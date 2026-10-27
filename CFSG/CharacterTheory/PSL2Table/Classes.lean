module

public import CFSG.CharacterTheory.PSL2Table.Partition
public import CFSG.CharacterTheory.PSL2Table.TorusCharacters

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem isConj_of_mem_conjSet {H : Subgroup PSL(2, F)} {g : PSL(2, F)} (hg : g ∈ conjSet H) :
    ∃ x ∈ H, x ≠ 1 ∧ IsConj g x := by
  obtain ⟨hg1, k, hk⟩ := hg
  refine ⟨k * g * k⁻¹, hk, ?_, isConj_iff.mpr ⟨k, rfl⟩⟩
  intro h
  apply hg1
  have := congrArg (fun z => k⁻¹ * z * k) h
  simpa [mul_assoc] using this

theorem conj_cases (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F} (hν : ¬ IsSquare ν)
    (g : PSL(2, F)) :
    g = 1 ∨ IsConj g (mk (unip 1)) ∨ IsConj g (mk (unip ν)) ∨
      (∃ x ∈ splitTorus F, x ≠ 1 ∧ IsConj g x) ∨
      (∃ x ∈ nonsplitTorus ν, x ≠ 1 ∧ IsConj g x) := by
  have h2 := Ring.two_ne_zero hF
  rcases mem_conjSet_cases hF hq hν g with h | h | h | h
  · exact Or.inl h
  · obtain ⟨x, hx, hx1, hgx⟩ := isConj_of_mem_conjSet h
    obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
    have ht : t ≠ 0 := fun h => hx1 ((mk_unip_eq_one_iff h2 t).mpr h)
    by_cases hsq : IsSquare t
    · right; left
      exact hgx.trans ((isConj_unip_iff h2 ht one_ne_zero).mpr (by simpa using hsq))
    · right; right; left
      exact hgx.trans ((isConj_unip_iff h2 ht (ne_zero_of_not_isSquare hν)).mpr
        (isSquare_mul_of_not_isSquare hsq hν))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isConj_of_mem_conjSet h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isConj_of_mem_conjSet h))))

omit [Fintype F] [DecidableEq F] in
theorem not_isConj_unip_one_unip_nu (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    ¬ IsConj (mk (unip (1 : F))) (mk (unip ν)) := by
  rw [isConj_unip_iff (Ring.two_ne_zero hF) one_ne_zero (ne_zero_of_not_isSquare hν), one_mul]
  exact hν

omit [Fintype F] [DecidableEq F] in
theorem mem_conjSet_of_isConj {H : Subgroup PSL(2, F)} {g x : PSL(2, F)} (hx : x ∈ H)
    (hx1 : x ≠ 1) (hgx : IsConj g x) : g ∈ conjSet H := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgx
  refine ⟨fun h => hx1 ?_, c, by rw [hc]; exact hx⟩
  rw [← hc, h]
  group

omit [DecidableEq F] in
theorem not_isConj_families (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    (∀ u ∈ unipotent F, u ≠ 1 → ∀ x ∈ splitTorus F, x ≠ 1 → ¬ IsConj u x) ∧
    (∀ u ∈ unipotent F, u ≠ 1 → ∀ x ∈ nonsplitTorus ν, x ≠ 1 → ¬ IsConj u x) ∧
    (∀ x ∈ splitTorus F, x ≠ 1 → ∀ y ∈ nonsplitTorus ν, y ≠ 1 → ¬ IsConj x y) := by
  refine ⟨fun u hu hu1 x hx hx1 h => ?_, fun u hu hu1 x hx hx1 h => ?_,
    fun x hx hx1 y hy hy1 h => ?_⟩
  · exact disjoint_conjSet (coprime_card_unipotent_splitTorus hF) (mem_conjSet_of_mem hu hu1)
      (mem_conjSet_of_isConj hx hx1 h)
  · exact disjoint_conjSet (coprime_card_unipotent_nonsplitTorus hF hν)
      (mem_conjSet_of_mem hu hu1) (mem_conjSet_of_isConj hx hx1 h)
  · exact disjoint_conjSet (coprime_card_splitTorus_nonsplitTorus hF hν)
      (mem_conjSet_of_mem hx hx1) (mem_conjSet_of_isConj hy hy1 h)

omit [Fintype F] [DecidableEq F] in
theorem isConj_splitTorus_iff {x y : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1)
    (hy : y ∈ splitTorus F) : IsConj x y ↔ y = x ∨ y = x⁻¹ := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    rcases (splitTorus_conj_mem_iff hx hx1 c).mp (by rw [hc]; exact hy) with hc' | hc'
    · left
      rw [← hc, splitTorus_mul_comm hc' hx, mul_inv_cancel_right]
    · right
      obtain ⟨t, ht, rfl⟩ : ∃ t ∈ splitTorus F, c = splitWeyl F * t :=
        ⟨(splitWeyl F)⁻¹ * c, hc', by group⟩
      rw [← hc, _root_.mul_inv_rev, show splitWeyl F * t * x * (t⁻¹ * (splitWeyl F)⁻¹) =
        splitWeyl F * (t * x * t⁻¹) * (splitWeyl F)⁻¹ by group, splitTorus_mul_comm ht hx,
        mul_inv_cancel_right, splitWeyl_conj hx]
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · exact isConj_iff.mpr ⟨splitWeyl F, splitWeyl_conj hx⟩

omit [DecidableEq F] in
theorem isConj_nonsplitTorus_iff (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
    {x y : PSL(2, F)} (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) (hy : y ∈ nonsplitTorus ν) :
    IsConj x y ↔ y = x ∨ y = x⁻¹ := by
  obtain ⟨w, -, -, hinv, hTI⟩ := exists_nonsplitWeyl hF hν
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    rcases (hTI x hx hx1 c).mp (by rw [hc]; exact hy) with hc' | hc'
    · left
      rw [← hc, nonsplitTorus_mul_comm hc' hx, mul_inv_cancel_right]
    · right
      obtain ⟨t, ht, rfl⟩ : ∃ t ∈ nonsplitTorus ν, c = w * t := ⟨w⁻¹ * c, hc', by group⟩
      rw [← hc, _root_.mul_inv_rev, show w * t * x * (t⁻¹ * w⁻¹) = w * (t * x * t⁻¹) * w⁻¹ by
        group, nonsplitTorus_mul_comm ht hx, mul_inv_cancel_right, hinv x hx]
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · exact isConj_iff.mpr ⟨w, hinv x hx⟩

omit [DecidableEq F] in
theorem card_centralizer_unip (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) :
    Nat.card (Subgroup.centralizer {mk (unip t)} : Subgroup PSL(2, F)) = Fintype.card F := by
  rw [centralizer_mk_unip (Ring.two_ne_zero hF) ht, card_unipotent (Ring.two_ne_zero hF)]

theorem card_centralizer_splitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.centralizer {x} : Subgroup PSL(2, F)) =
      if x ^ 2 = 1 then 2 * Nat.card (splitTorus F) else Nat.card (splitTorus F) := by
  have hmem : ∀ g, g ∈ Subgroup.centralizer {x} ↔ g ∈ splitTorus F ∨
      ((splitWeyl F)⁻¹ * g ∈ splitTorus F ∧ x ^ 2 = 1) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have hconj : g * x * g⁻¹ = x := by rw [hg, mul_inv_cancel_right]
      rcases (splitTorus_conj_mem_iff hx hx1 g).mp (by rw [hconj]; exact hx) with h | h
      · exact Or.inl h
      · right
        refine ⟨h, ?_⟩
        obtain ⟨t, ht, rfl⟩ : ∃ t ∈ splitTorus F, g = splitWeyl F * t :=
          ⟨(splitWeyl F)⁻¹ * g, h, by group⟩
        have : splitWeyl F * t * x * (splitWeyl F * t)⁻¹ = x⁻¹ := by
          rw [_root_.mul_inv_rev, show splitWeyl F * t * x * (t⁻¹ * (splitWeyl F)⁻¹) =
            splitWeyl F * (t * x * t⁻¹) * (splitWeyl F)⁻¹ by group, splitTorus_mul_comm ht hx,
            mul_inv_cancel_right, splitWeyl_conj hx]
        rw [hconj] at this
        rw [sq]
        nth_rewrite 2 [this]
        exact mul_inv_cancel x
    · rintro (h | ⟨h, hx2⟩)
      · exact splitTorus_mul_comm h hx
      · obtain ⟨t, ht, rfl⟩ : ∃ t ∈ splitTorus F, g = splitWeyl F * t :=
          ⟨(splitWeyl F)⁻¹ * g, h, by group⟩
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
        have : splitWeyl F * t * x * (splitWeyl F * t)⁻¹ = x := by
          rw [_root_.mul_inv_rev, show splitWeyl F * t * x * (t⁻¹ * (splitWeyl F)⁻¹) =
            splitWeyl F * (t * x * t⁻¹) * (splitWeyl F)⁻¹ by group, splitTorus_mul_comm ht hx,
            mul_inv_cancel_right, splitWeyl_conj hx, hxinv]
        calc splitWeyl F * t * x = splitWeyl F * t * x * (splitWeyl F * t)⁻¹ * (splitWeyl F * t) :=
              by group
          _ = x * (splitWeyl F * t) := by rw [this]
  split_ifs with hx2
  · rw [← card_normalizer_splitTorus hF hq]
    have heq : Subgroup.centralizer {x} = Subgroup.normalizer (splitTorus F : Set PSL(2, F)) := by
      ext g
      rw [hmem, mem_normalizer_iff_of_TI splitWeyl_mul_self (fun y hy => splitWeyl_conj hy) hx
        (splitTorus_conj_mem_iff hx hx1)]
      simp [hx2]
    rw [heq]
  · have heq : Subgroup.centralizer {x} = splitTorus F := by
      ext g
      rw [hmem]
      simp [hx2]
    rw [heq]

theorem card_centralizer_nonsplitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.centralizer {x} : Subgroup PSL(2, F)) =
      if x ^ 2 = 1 then 2 * Nat.card (nonsplitTorus ν) else Nat.card (nonsplitTorus ν) := by
  obtain ⟨w, hw, hw2, hinv, hTI⟩ := exists_nonsplitWeyl hF hν
  have hmem : ∀ g, g ∈ Subgroup.centralizer {x} ↔ g ∈ nonsplitTorus ν ∨
      (w⁻¹ * g ∈ nonsplitTorus ν ∧ x ^ 2 = 1) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have hconj : g * x * g⁻¹ = x := by rw [hg, mul_inv_cancel_right]
      rcases (hTI x hx hx1 g).mp (by rw [hconj]; exact hx) with h | h
      · exact Or.inl h
      · right
        refine ⟨h, ?_⟩
        obtain ⟨t, ht, rfl⟩ : ∃ t ∈ nonsplitTorus ν, g = w * t := ⟨w⁻¹ * g, h, by group⟩
        have : w * t * x * (w * t)⁻¹ = x⁻¹ := by
          rw [_root_.mul_inv_rev, show w * t * x * (t⁻¹ * w⁻¹) = w * (t * x * t⁻¹) * w⁻¹ by
            group, nonsplitTorus_mul_comm ht hx, mul_inv_cancel_right, hinv x hx]
        rw [hconj] at this
        rw [sq]
        nth_rewrite 2 [this]
        exact mul_inv_cancel x
    · rintro (h | ⟨h, hx2⟩)
      · exact nonsplitTorus_mul_comm h hx
      · obtain ⟨t, ht, rfl⟩ : ∃ t ∈ nonsplitTorus ν, g = w * t := ⟨w⁻¹ * g, h, by group⟩
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
        have : w * t * x * (w * t)⁻¹ = x := by
          rw [_root_.mul_inv_rev, show w * t * x * (t⁻¹ * w⁻¹) = w * (t * x * t⁻¹) * w⁻¹ by
            group, nonsplitTorus_mul_comm ht hx, mul_inv_cancel_right, hinv x hx, hxinv]
        calc w * t * x = w * t * x * (w * t)⁻¹ * (w * t) := by group
          _ = x * (w * t) := by rw [this]
  split_ifs with hx2
  · rw [← card_normalizer_nonsplitTorus hF hq hν]
    have heq : Subgroup.centralizer {x} =
        Subgroup.normalizer (nonsplitTorus ν : Set PSL(2, F)) := by
      ext g
      rw [hmem, mem_normalizer_iff_of_TI hw2 hinv hx (hTI x hx hx1)]
      simp [hx2]
    rw [heq]
  · have heq : Subgroup.centralizer {x} = nonsplitTorus ν := by
      ext g
      rw [hmem]
      simp [hx2]
    rw [heq]

theorem exists_involution_splitTorus_iff (hF : ringChar F ≠ 2) :
    (∃ x ∈ splitTorus F, orderOf x = 2) ↔ IsSquare (-1 : F) := by
  have hcard := card_sq_eq_one_splitTorus hF (F := F)
  constructor
  · rintro ⟨x, hx, hord⟩
    by_contra hm
    rw [ite_eq_right hm, Nat.card_eq_one_iff_exists] at hcard
    obtain ⟨y, hy⟩ := hcard
    have hx2 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hord] at this
    have h1 := hy ⟨⟨x, hx⟩, Subtype.ext (by simpa using hx2)⟩
    have h2 := hy ⟨1, one_pow 2⟩
    have : (⟨x, hx⟩ : splitTorus F) = 1 := congrArg Subtype.val (h1.trans h2.symm)
    have : x = 1 := congrArg Subtype.val this
    rw [this, orderOf_one] at hord
    norm_num at hord
  · intro hm
    rw [ite_eq_left hm, Nat.card_eq_two_iff] at hcard
    obtain ⟨a, b, hab, -⟩ := hcard
    have hex : ∃ c : {t : splitTorus F // t ^ 2 = 1}, (c : splitTorus F) ≠ 1 := by
      by_cases ha : (a : splitTorus F) = 1
      · exact ⟨b, fun hb => hab (Subtype.ext (ha.trans hb.symm))⟩
      · exact ⟨a, ha⟩
    obtain ⟨⟨c, hc2⟩, hc1⟩ := hex
    refine ⟨c, c.2, ?_⟩
    have hc1' : (c : PSL(2, F)) ≠ 1 := fun h => hc1 (Subtype.ext h)
    apply orderOf_eq_prime
    · rw [← Subgroup.coe_pow, hc2, Subgroup.coe_one]
    · exact hc1'

theorem exists_involution_nonsplitTorus_iff (hF : ringChar F ≠ 2) {ν : F}
    (hν : ¬ IsSquare ν) : (∃ x ∈ nonsplitTorus ν, orderOf x = 2) ↔ ¬ IsSquare (-1 : F) := by
  have hcard := card_sq_eq_one_nonsplitTorus hF hν
  constructor
  · rintro ⟨x, hx, hord⟩ hm
    rw [ite_eq_left hm, Nat.card_eq_one_iff_exists] at hcard
    obtain ⟨y, hy⟩ := hcard
    have hx2 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hord] at this
    have h1 := hy ⟨⟨x, hx⟩, Subtype.ext (by simpa using hx2)⟩
    have h2 := hy ⟨1, one_pow 2⟩
    have : (⟨x, hx⟩ : nonsplitTorus ν) = 1 := congrArg Subtype.val (h1.trans h2.symm)
    have : x = 1 := congrArg Subtype.val this
    rw [this, orderOf_one] at hord
    norm_num at hord
  · intro hm
    rw [ite_eq_right hm, Nat.card_eq_two_iff] at hcard
    obtain ⟨a, b, hab, -⟩ := hcard
    have hex : ∃ c : {t : nonsplitTorus ν // t ^ 2 = 1}, (c : nonsplitTorus ν) ≠ 1 := by
      by_cases ha : (a : nonsplitTorus ν) = 1
      · exact ⟨b, fun hb => hab (Subtype.ext (ha.trans hb.symm))⟩
      · exact ⟨a, ha⟩
    obtain ⟨⟨c, hc2⟩, hc1⟩ := hex
    refine ⟨c, c.2, ?_⟩
    have hc1' : (c : PSL(2, F)) ≠ 1 := fun h => hc1 (Subtype.ext h)
    apply orderOf_eq_prime
    · rw [← Subgroup.coe_pow, hc2, Subgroup.coe_one]
    · exact hc1'

theorem involution_conj_torus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {g : PSL(2, F)} (hg : orderOf g = 2) :
    (IsSquare (-1 : F) → ∃ x ∈ splitTorus F, IsConj g x) ∧
      (¬ IsSquare (-1 : F) → ∃ x ∈ nonsplitTorus ν, IsConj g x) := by
  have h2 := Ring.two_ne_zero hF
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    norm_num at hg
  have hord : ∀ {x : PSL(2, F)}, IsConj g x → orderOf x = 2 := by
    intro x hgx
    obtain ⟨c, hc⟩ := isConj_iff.mp hgx
    rw [← hc]
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective g
    simpa [hg] using this
  rcases mem_conjSet_cases hF hq hν g with h | h | h | h
  · exact (hg1 h).elim
  · exfalso
    obtain ⟨x, hx, -, hgx⟩ := isConj_of_mem_conjSet h
    have hdvd := Subgroup.orderOf_dvd_natCard _ hx
    rw [hord hgx, card_unipotent h2] at hdvd
    have hodd := FiniteField.odd_card_of_char_ne_two hF
    omega
  · obtain ⟨x, hx, -, hgx⟩ := isConj_of_mem_conjSet h
    refine ⟨fun _ => ⟨x, hx, hgx⟩, fun hm => ?_⟩
    exact (hm ((exists_involution_splitTorus_iff hF).mp ⟨x, hx, hord hgx⟩)).elim
  · obtain ⟨x, hx, -, hgx⟩ := isConj_of_mem_conjSet h
    refine ⟨fun hm => ?_, fun _ => ⟨x, hx, hgx⟩⟩
    exact ((exists_involution_nonsplitTorus_iff hF hν).mp ⟨x, hx, hord hgx⟩ hm).elim

omit [Fintype F] [DecidableEq F] in
theorem splitTorus_isCyclic [Finite F] : IsCyclic (splitTorus F) := by
  let f : Fˣ →* splitTorus F :=
    { toFun := fun a => ⟨mk (diag a), mk_diag_mem_splitTorus a⟩
      map_one' := by
        apply Subtype.ext
        simp [diag_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        simp [diag_mul] }
  apply isCyclic_of_surjective f
  intro x
  obtain ⟨a, ha⟩ := (mem_splitTorus_iff_exists (x : PSL(2, F))).mp x.2
  exact ⟨a, Subtype.ext ha.symm⟩

end CFSG.PSL2Table
