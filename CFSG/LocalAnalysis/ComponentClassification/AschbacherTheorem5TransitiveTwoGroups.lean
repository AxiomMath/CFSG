module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupTwoGroup
public import CFSG.GroupTheory.QuaternionCentralizers
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

namespace TwoGroups

section General

variable {G : Type*} [Group G]

theorem mul_comm_of_sq_eq_one {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hinv : ∀ w : G, w ^ 2 = 1 → w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hw)
  calc x * y = (x * y)⁻¹ := (hinv _ hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv y hy, hinv x hx]

theorem isElemAbelian_of_sq {E : Subgroup G} (h : ∀ x ∈ E, x ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 E :=
  ⟨⟨⟨fun x y => Subtype.ext (mul_comm_of_sq_eq_one (h _ x.2) (h _ y.2)
    (h _ (E.mul_mem x.2 y.2)))⟩⟩, h⟩

theorem sq_eq_one_of_orderOf {t : G} (h : orderOf t = 2) : t ^ 2 = 1 := by
  rw [← h]
  exact pow_orderOf_eq_one t

theorem ne_one_of_orderOf {t : G} (h : orderOf t = 2) : t ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  exact absurd h (by norm_num)

theorem two_pow_sub_one {n : ℕ} (hn : 2 ≤ n) : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
  rw [← pow_succ']
  congr 1
  omega

theorem zmod_natCast_ne_zero {m : ℕ} [NeZero m] : (m : ZMod (2 * m)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have hm := NeZero.ne m
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h
  omega

theorem eq_of_card_four {R P : Subgroup G} (hPR : P ≤ R) (hR : Nat.card R = 4)
    (hPc : ¬ IsCyclic P) : P = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  have : Finite P := Finite.of_injective _ (Subgroup.inclusion_injective hPR)
  have hdvd : Nat.card P ∣ 4 := hR ▸ Subgroup.card_dvd_of_le hPR
  have hle : Nat.card P ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card P := Nat.card_pos
  interval_cases h : Nat.card P
  · rw [Subgroup.card_eq_one] at h
    subst h
    exact (hPc inferInstance).elim
  · exact absurd (isCyclic_of_prime_card h) hPc
  · norm_num at hdvd
  · exact Subgroup.eq_of_le_of_card_ge hPR (by rw [h, hR])

end General

section Embedding

variable {X : Type*} [Group X] {D : Type*} [Group D]

theorem exists_embedding {R : Subgroup X} (e : R ≃* D) :
    ∃ f : D →* X, Function.Injective f ∧ f.range = R := by
  refine ⟨R.subtype.comp e.symm.toMonoidHom, R.subtype_injective.comp e.symm.injective, ?_⟩
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    exact (e.symm d).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp⟩

theorem isCyclic_of_isCyclic_comap {f : D →* X} {P : Subgroup X} (hP : P ≤ f.range)
    (h : IsCyclic (P.comap f)) : IsCyclic P := by
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (P.comap f)).1 h
  refine (Subgroup.isCyclic_iff_exists_zpowers_eq_top P).2 ⟨f d, ?_⟩
  rw [← MonoidHom.map_zpowers, hd, Subgroup.map_comap_eq_self hP]

theorem normal_comap {f : D →* X} {P : Subgroup X} (hP : (P.subgroupOf f.range).Normal) :
    (P.comap f).Normal :=
  ⟨fun n hn g => by
    have := hP.conj_mem ⟨f n, n, rfl⟩ hn ⟨f g, g, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using this⟩

theorem commuting_noncyclic_eq_of_index_two {H : Subgroup D} {z : D} (hHc : IsCyclic H)
    (hind : H.index = 2) (hcent : ∀ x, x ∉ H → ∀ h ∈ H, x * h = h * x → h = 1 ∨ h = z)
    {f : D →* X} (hf : Function.Injective f) {P P' : Subgroup X} (hP : P ≤ f.range)
    (hP' : P' ≤ f.range) (hPc : ¬ IsCyclic P) (hP'c : ¬ IsCyclic P')
    (hcomm : ∀ x ∈ P, ∀ y ∈ P', x * y = y * x) : P = P' := by
  have hind' : (H.subgroupOf ⊤).index = 2 := (Subgroup.relIndex_top_right H).trans hind
  have hcent' : ∀ x ∈ (⊤ : Subgroup D), x ∉ H → ∀ h ∈ H, x * h = h * x → h = 1 ∨ h = z :=
    fun x _ => hcent x
  have hc : ¬ IsCyclic (P.comap f) := fun h => hPc (isCyclic_of_isCyclic_comap hP h)
  have hc' : ¬ IsCyclic (P'.comap f) := fun h => hP'c (isCyclic_of_isCyclic_comap hP' h)
  have h1 := AschbacherKnownGroup.TwoGroup.commuting_noncyclic_le hHc hind' hcent' le_top
    le_top hc hc' fun y₁ h₁ y₂ h₂ => hf (by rw [map_mul, map_mul]; exact hcomm _ h₁ _ h₂)
  have h2 := AschbacherKnownGroup.TwoGroup.commuting_noncyclic_le hHc hind' hcent' le_top
    le_top hc' hc fun y₁ h₁ y₂ h₂ => hf (by rw [map_mul, map_mul]; exact (hcomm _ h₂ _ h₁).symm)
  calc P = (P.comap f).map f := (Subgroup.map_comap_eq_self hP).symm
    _ = (P'.comap f).map f := by rw [le_antisymm h2 h1]
    _ = P' := Subgroup.map_comap_eq_self hP'

end Embedding

section Dihedral

open DihedralGroup

theorem mem_zpowers_r_one_iff {n : ℕ} [NeZero n] (g : DihedralGroup n) :
    g ∈ Subgroup.zpowers (r 1) ↔ ∃ j, g = r j := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, r_one_zpow k⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(j.val : ℤ), by rw [r_one_zpow, Int.cast_natCast, ZMod.natCast_zmod_val]⟩

theorem index_zpowers_r_one {n : ℕ} [NeZero n] :
    (Subgroup.zpowers (r 1 : DihedralGroup n)).index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨sr 0, fun h => ?_, fun b => ?_⟩
  · obtain ⟨j, hj⟩ := (mem_zpowers_r_one_iff _).1 h
    cases hj
  · cases b with
    | r j => exact Or.inr ((mem_zpowers_r_one_iff _).2 ⟨j, rfl⟩)
    | sr j => exact Or.inl ((mem_zpowers_r_one_iff _).2 ⟨0 - j, sr_mul_sr j 0⟩)

variable {m : ℕ} [NeZero m]

theorem mem_centralizer_sr_iff (i : ZMod (2 * m)) (g : DihedralGroup (2 * m)) :
    g ∈ Subgroup.centralizer {sr i} ↔
      g = r 0 ∨ g = r (m : ZMod (2 * m)) ∨ g = sr i ∨ g = sr (i + (m : ZMod (2 * m))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  cases g with
  | r j =>
    rw [r_mul_sr, sr_mul_r, sr.injEq]
    have h : i - j = i + j ↔ 2 * j = 0 :=
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
    rw [h, CFSG.GroupTheory.two_mul_eq_zero_iff_zmod]
    simp only [r.injEq, reduceCtorEq, or_false]
  | sr j =>
    rw [sr_mul_sr, sr_mul_sr, r.injEq]
    have h : i - j = j - i ↔ 2 * (j - i) = 0 :=
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
    rw [h, CFSG.GroupTheory.two_mul_eq_zero_iff_zmod, sub_eq_zero, sub_eq_iff_eq_add,
      add_comm (m : ZMod (2 * m))]
    simp only [sr.injEq, reduceCtorEq, false_or]

theorem card_centralizer_sr (i : ZMod (2 * m)) :
    Nat.card (Subgroup.centralizer {sr i} : Subgroup (DihedralGroup (2 * m))) = 4 := by
  have hm := zmod_natCast_ne_zero (m := m)
  set c : ZMod (2 * m) := (m : ZMod (2 * m))
  have hset : ((Subgroup.centralizer {sr i} : Subgroup (DihedralGroup (2 * m))) : Set _) =
      {r 0, r c, sr i, sr (i + c)} := by
    ext g
    rw [SetLike.mem_coe, mem_centralizer_sr_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Iff.rfl
  have h1 : r 0 ∉ ({r c, sr i, sr (i + c)} : Set (DihedralGroup (2 * m))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, r.injEq, reduceCtorEq, or_false]
    exact fun h => hm h.symm
  have h2 : r c ∉ ({sr i, sr (i + c)} : Set (DihedralGroup (2 * m))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq, or_self,
      not_false_eq_true]
  have h3 : sr i ≠ sr (i + c) := by
    rw [Ne, sr.injEq]
    intro h
    exact hm (by linear_combination -h)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem h1,
    Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]

theorem r_sq_eq_one_iff (j : ZMod (2 * m)) :
    (r j : DihedralGroup (2 * m)) ^ 2 = 1 ↔ j = 0 ∨ j = m := by
  rw [sq, r_mul_r, one_def, r.injEq, ← two_mul, CFSG.GroupTheory.two_mul_eq_zero_iff_zmod]

theorem sq_eq_one_of_mem_centralizer_sr {i : ZMod (2 * m)} {g : DihedralGroup (2 * m)}
    (hg : g ∈ Subgroup.centralizer {sr i}) : g ^ 2 = 1 := by
  rcases (mem_centralizer_sr_iff i g).1 hg with rfl | rfl | rfl | rfl
  · exact (r_sq_eq_one_iff 0).2 (Or.inl rfl)
  · exact (r_sq_eq_one_iff _).2 (Or.inr rfl)
  · rw [sq, sr_mul_self]
  · rw [sq, sr_mul_self]

theorem mul_comm_of_mem_centralizer_sr {i : ZMod (2 * m)} {g h : DihedralGroup (2 * m)}
    (hg : g ∈ Subgroup.centralizer {sr i}) (hh : h ∈ Subgroup.centralizer {sr i}) :
    g * h = h * g :=
  mul_comm_of_sq_eq_one (sq_eq_one_of_mem_centralizer_sr hg)
    (sq_eq_one_of_mem_centralizer_sr hh)
    (sq_eq_one_of_mem_centralizer_sr (Subgroup.mul_mem _ hg hh))

theorem exists_mem_centralizer_sr {d : DihedralGroup (2 * m)} (hd1 : d ≠ 1) (hd2 : d ^ 2 = 1) :
    ∃ i, d ∈ Subgroup.centralizer {sr i} := by
  cases d with
  | r j =>
    rcases (r_sq_eq_one_iff j).1 hd2 with rfl | rfl
    · exact absurd r_zero hd1
    · exact ⟨0, (mem_centralizer_sr_iff 0 _).2 (Or.inr (Or.inl rfl))⟩
  | sr i => exact ⟨i, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem exists_le_centralizer_sr {E : Subgroup (DihedralGroup (2 * m))}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h2 : ∀ x ∈ E, x ^ 2 = 1) :
    ∃ i, E ≤ Subgroup.centralizer {sr i} := by
  by_cases h : ∃ i, sr i ∈ E
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (hc g hg _ hi)⟩
  · push Not at h
    refine ⟨0, fun g hg => ?_⟩
    cases g with
    | r j =>
      rcases (r_sq_eq_one_iff j).1 (h2 _ hg) with rfl | rfl
      · exact (mem_centralizer_sr_iff 0 _).2 (Or.inl rfl)
      · exact (mem_centralizer_sr_iff 0 _).2 (Or.inr (Or.inl rfl))
    | sr i => exact absurd hg (h i)

theorem eq_of_comm_r {x h : DihedralGroup (2 * m)} (hx : x ∉ Subgroup.zpowers (r 1))
    (hh : h ∈ Subgroup.zpowers (r 1)) (hxh : x * h = h * x) : h = 1 ∨ h = r m := by
  obtain ⟨j, rfl⟩ := (mem_zpowers_r_one_iff h).1 hh
  cases x with
  | r i => exact absurd ((mem_zpowers_r_one_iff _).2 ⟨i, rfl⟩) hx
  | sr i =>
    rcases (mem_centralizer_sr_iff i (r j)).1
      (Subgroup.mem_centralizer_singleton_iff.2 hxh.symm) with h | h | h | h
    · exact Or.inl (h.trans r_zero)
    · exact Or.inr h
    · cases h
    · cases h

theorem eq_r_of_central (hm : 2 ≤ m) {z : DihedralGroup (2 * m)} (hz : z ≠ 1)
    (hzc : ∀ g, z * g = g * z) : z = r m := by
  have h1 : (1 : ZMod (2 * m)) ≠ 0 := by
    have : Fact (1 < 2 * m) := ⟨by omega⟩
    exact one_ne_zero
  have h1m : (1 : ZMod (2 * m)) ≠ m := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hv
    have : Fact (1 < 2 * m) := ⟨by omega⟩
    rw [ZMod.val_one] at hv
    omega
  have hr1 : ∀ j : ZMod (2 * m), (r 1 : DihedralGroup (2 * m)) ∉ Subgroup.centralizer {sr j} := by
    intro j h
    rcases (mem_centralizer_sr_iff j _).1 h with h | h | h | h
    · exact h1 (r.inj h)
    · exact h1m (r.inj h)
    · cases h
    · cases h
  rcases (mem_centralizer_sr_iff 0 z).1 (Subgroup.mem_centralizer_singleton_iff.2 (hzc _))
    with rfl | rfl | rfl | rfl
  · exact absurd r_zero hz
  · rfl
  · exact absurd (Subgroup.mem_centralizer_singleton_iff.2 (hzc (r 1)).symm) (hr1 0)
  · exact absurd (Subgroup.mem_centralizer_singleton_iff.2 (hzc (r 1)).symm) (hr1 _)

theorem r_mem_of_normal (hm : Even m) {P : Subgroup (DihedralGroup (2 * m))} (hPn : P.Normal)
    (hPc : ¬ IsCyclic P) : r (m : ZMod (2 * m)) ∈ P := by
  obtain ⟨g, hgP, hg⟩ : ∃ g ∈ P, g ∉ Subgroup.zpowers (r 1) := by
    by_contra h
    push Not at h
    exact hPc (Subgroup.isCyclic_of_le (H' := Subgroup.zpowers (r 1)) h)
  obtain ⟨i, rfl⟩ : ∃ i, g = sr i := by
    cases g with
    | r j => exact absurd ((mem_zpowers_r_one_iff _).2 ⟨j, rfl⟩) hg
    | sr i => exact ⟨i, rfl⟩
  have h2 : r 2 ∈ P := by
    have h := P.mul_mem (hPn.conj_mem _ hgP (r 1)) hgP
    rw [inv_r, r_mul_sr, sr_mul_r, sr_mul_sr] at h
    convert h using 2
    ring
  obtain ⟨k, hk⟩ := hm
  have h3 := P.pow_mem h2 k
  rw [r_pow] at h3
  have hk' : 2 * k = m := by omega
  have hmk : (m : ZMod (2 * m)) = 2 * k :=
    calc (m : ZMod (2 * m)) = ((2 * k : ℕ) : ZMod (2 * m)) := by rw [hk']
      _ = 2 * k := by norm_num
  rw [hmk]
  exact h3

end Dihedral

section Quaternion

open QuaternionGroup

variable {m : ℕ} [NeZero m]

theorem mem_zpowers_a_one_iff (g : QuaternionGroup m) :
    g ∈ Subgroup.zpowers (a 1) ↔ ∃ j, g = a j := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hg)
    exact ⟨k, a_one_pow k⟩
  · rintro ⟨j, rfl⟩
    exact Subgroup.mem_zpowers_iff.2
      ⟨(j.val : ℤ), by rw [zpow_natCast, a_one_pow, ZMod.natCast_zmod_val]⟩

theorem index_zpowers_a_one : (Subgroup.zpowers (a 1 : QuaternionGroup m)).index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨xa 0, fun h => ?_, fun b => ?_⟩
  · obtain ⟨j, hj⟩ := (mem_zpowers_a_one_iff _).1 h
    cases hj
  · cases b with
    | a j => exact Or.inr ((mem_zpowers_a_one_iff _).2 ⟨j, rfl⟩)
    | xa j => exact Or.inl ((mem_zpowers_a_one_iff _).2 ⟨_, xa_mul_xa j 0⟩)

theorem eq_of_comm_a {x h : QuaternionGroup m} (hx : x ∉ Subgroup.zpowers (a 1))
    (hh : h ∈ Subgroup.zpowers (a 1)) (hxh : x * h = h * x) : h = 1 ∨ h = a m := by
  obtain ⟨j, rfl⟩ := (mem_zpowers_a_one_iff h).1 hh
  cases x with
  | a i => exact absurd ((mem_zpowers_a_one_iff _).2 ⟨i, rfl⟩) hx
  | xa i =>
    rcases (CFSG.GroupTheory.a_mul_xa_eq_xa_mul_a_iff j i).1 hxh.symm with rfl | rfl
    · exact Or.inl a_zero
    · exact Or.inr rfl

theorem eq_a_of_sq_eq_one {q : QuaternionGroup m} (hq1 : q ≠ 1) (hq2 : q ^ 2 = 1) :
    q = a m := by
  cases q with
  | a j =>
    rw [sq, a_mul_a, one_def, a.injEq, ← two_mul,
      CFSG.GroupTheory.two_mul_eq_zero_iff_zmod] at hq2
    rcases hq2 with rfl | rfl
    · exact absurd a_zero hq1
    · rfl
  | xa i =>
    rw [xa_sq, one_def, a.injEq] at hq2
    exact absurd hq2 zmod_natCast_ne_zero

theorem a_mem_of_not_isCyclic {P : Subgroup (QuaternionGroup m)} (hPc : ¬ IsCyclic P) :
    a (m : ZMod (2 * m)) ∈ P := by
  obtain ⟨g, hgP, hg⟩ : ∃ g ∈ P, g ∉ Subgroup.zpowers (a 1) := by
    by_contra h
    push Not at h
    exact hPc (Subgroup.isCyclic_of_le (H' := Subgroup.zpowers (a 1)) h)
  cases g with
  | a j => exact absurd ((mem_zpowers_a_one_iff _).2 ⟨j, rfl⟩) hg
  | xa i =>
    have h := P.pow_mem hgP 2
    rwa [xa_sq] at h

end Quaternion

section Transport

variable {X : Type*} [Group X]

theorem dihedral_mem_of_normal {m : ℕ} [NeZero m] (hm : Even m)
    {f : DihedralGroup (2 * m) →* X} (hf : Function.Injective f) {P : Subgroup X} {z : X}
    (hzR : z ∈ f.range) (hz : z ≠ 1) (hzc : ∀ x ∈ f.range, z * x = x * z)
    (hPR : P ≤ f.range) (hPn : (P.subgroupOf f.range).Normal) (hPc : ¬ IsCyclic P) :
    z ∈ P := by
  obtain ⟨d, rfl⟩ := hzR
  have hm2 : 2 ≤ m := by
    obtain ⟨k, hk⟩ := hm
    have := NeZero.ne m
    omega
  have hd : d = DihedralGroup.r m := eq_r_of_central (z := d) hm2
    (fun h => hz (by rw [h, map_one]))
    (fun g => hf (by rw [map_mul, map_mul]; exact hzc _ ⟨g, rfl⟩))
  rw [hd]
  exact r_mem_of_normal hm (normal_comap hPn) fun h => hPc (isCyclic_of_isCyclic_comap hPR h)

theorem quaternion_mem_of_noncyclic {m : ℕ} [NeZero m] {f : QuaternionGroup m →* X}
    (hf : Function.Injective f) {P : Subgroup X} {z : X} (hzR : z ∈ f.range) (hz : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hPR : P ≤ f.range) (hPc : ¬ IsCyclic P) : z ∈ P := by
  obtain ⟨d, rfl⟩ := hzR
  have hd : d = QuaternionGroup.a m := eq_a_of_sq_eq_one (q := d)
    (fun h => hz (by rw [h, map_one]))
    (hf (by rw [map_pow, hz2, map_one]))
  rw [hd]
  exact a_mem_of_not_isCyclic fun h => hPc (isCyclic_of_isCyclic_comap hPR h)

theorem isElemAbelian_map_centralizer {m : ℕ} [NeZero m] {f : DihedralGroup (2 * m) →* X}
    (hf : Function.Injective f) (i : ZMod (2 * m)) :
    CFSG.Open.IsElemAbelian 2 ((Subgroup.centralizer {DihedralGroup.sr i}).map f) ∧
      Nat.card ((Subgroup.centralizer {DihedralGroup.sr i}).map f) = 4 := by
  refine ⟨isElemAbelian_of_sq ?_, by rw [Subgroup.card_map_of_injective hf, card_centralizer_sr]⟩
  rintro _ ⟨w, hw, rfl⟩
  rw [← map_pow, sq_eq_one_of_mem_centralizer_sr hw, map_one]

theorem dihedral_four {m : ℕ} [NeZero m] {f : DihedralGroup (2 * m) →* X}
    (hf : Function.Injective f) {a : X} (ha : a ∈ f.range) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    ∃ V : Subgroup X, V ≤ f.range ∧ a ∈ V ∧ (∀ v ∈ V, v * a = a * v) ∧
      CFSG.Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨d, rfl⟩ := ha
  obtain ⟨i, hi⟩ := exists_mem_centralizer_sr (d := d) (fun h => ha1 (by rw [h, map_one]))
    (hf (by rw [map_pow, ha2, map_one]))
  obtain ⟨hV, hcard⟩ := isElemAbelian_map_centralizer hf i
  refine ⟨_, Subgroup.map_le_range _ _, ⟨d, hi, rfl⟩, ?_, hV, hcard⟩
  rintro _ ⟨w, hw, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm_of_mem_centralizer_sr hw hi]

theorem pRank_range_dihedral [Finite X] {m : ℕ} [NeZero m] {f : DihedralGroup (2 * m) →* X}
    (hf : Function.Injective f) : CFSG.Open.pRank 2 f.range = 2 := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le one_lt_two fun E hE hEab => ?_
    have hc : ∀ x ∈ E.comap f, ∀ y ∈ E.comap f, x * y = y * x := fun x hx y hy =>
      hf (by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val (isMulCommutative_iff.mp hEab.1 ⟨f x, hx⟩ ⟨f y, hy⟩))
    obtain ⟨i, hi⟩ := exists_le_centralizer_sr hc fun x hx =>
      hf (by rw [map_pow, hEab.2 _ hx, map_one])
    rw [← Subgroup.map_comap_eq_self hE, Subgroup.card_map_of_injective hf]
    exact ((Subgroup.card_le_of_le hi).trans (card_centralizer_sr i).le).trans (by norm_num)
  · obtain ⟨hV, hcard⟩ := isElemAbelian_map_centralizer hf 0
    exact CFSG.SectionRank.le_pRank one_lt_two (Subgroup.map_le_range _ _) hV
      (hcard.trans (by norm_num))

theorem quaternion_eq_of_equiv {R : Subgroup X} {n : ℕ} (e : R ≃* QuaternionGroup (2 ^ (n - 2)))
    {t t' : X} (ht : t ∈ R) (ht' : t' ∈ R) (h1 : orderOf t = 2) (h2 : orderOf t' = 2) :
    t = t' := by
  obtain ⟨f, hf, rfl⟩ := exists_embedding e
  obtain ⟨d, rfl⟩ := ht
  obtain ⟨d', rfl⟩ := ht'
  rw [orderOf_injective f hf] at h1 h2
  rw [eq_a_of_sq_eq_one (ne_one_of_orderOf h1) (sq_eq_one_of_orderOf h1),
    eq_a_of_sq_eq_one (ne_one_of_orderOf h2) (sq_eq_one_of_orderOf h2)]

theorem not_twoRankAtLeastTwo [Finite X] {P : Subgroup X} (hr : CFSG.Open.pRank 2 P ≤ 1) :
    ¬ BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo P := by
  rintro ⟨E, hcard, hsq⟩
  have hE : CFSG.Open.IsElemAbelian 2 (E.map P.subtype) := by
    refine isElemAbelian_of_sq ?_
    rintro _ ⟨u, hu, rfl⟩
    have h := congrArg (fun w : E => ((w : P) : X)) (hsq ⟨u, hu⟩)
    simpa using h
  have := CFSG.SectionRank.le_pRank one_lt_two (Subgroup.map_subtype_le E) hE (k := 2)
    (((Subgroup.card_map_of_injective P.subtype_injective).trans hcard).trans (by norm_num))
  omega

theorem cyclic_or_quaternion [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P)
    (hr : CFSG.Open.pRank 2 P ≤ 1) :
    IsCyclic P ∨ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 (⊤ : Subgroup P) := hP.to_subgroup ⊤
  have hidx : ¬ 2 ∣ (⊤ : Subgroup P).index := by
    rw [Subgroup.index_top]
    norm_num
  let φ : P ≃* ((hS.toSylow hidx : Sylow 2 P) : Subgroup P) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hS hidx).symm)
  rcases BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank (not_twoRankAtLeastTwo hr)
    (hS.toSylow hidx) with h | ⟨r, hr3, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_injective φ.toMonoidHom φ.injective)
  · exact Or.inr ⟨r, hr3, ⟨φ.trans e⟩⟩

end Transport

section Perfect

theorem even_natCard_of_perfect (G : Type*) [Group G] [Finite G] [Group.IsPerfect G]
    [Nontrivial G] : Even (Nat.card G) := by
  by_contra hodd
  exact Group.IsPerfect.not_isSolvable G
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd))

theorem not_normalizer_le_centralizer {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [Nontrivial G] (Q : Sylow 2 G) :
    ¬ Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer (Q : Set G) := by
  intro hNC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative (MonoidHom.transferSylow Q hNC).range :=
    ⟨⟨fun x y => Subtype.ext (Subtype.ext (hNC (Subgroup.le_normalizer y.1.2) x.1 x.1.2))⟩⟩
  have : Group.IsPerfect (MonoidHom.transferSylow Q hNC).range :=
    Group.IsPerfect.range (MonoidHom.transferSylow Q hNC)
  have hker : (MonoidHom.transferSylow Q hNC).ker = ⊤ := by
    refine eq_top_iff.2 fun g _ => (MonoidHom.mem_ker).2 ?_
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨_, g, rfl⟩ : (MonoidHom.transferSylow Q hNC).range) 1)
  have hQ : Nat.card (Q : Subgroup G) = 1 := by
    rw [← (MonoidHom.ker_transferSylow_isComplement' Q hNC).symm.index_eq_card, hker,
      Subgroup.index_top]
  have h2 := Q.dvd_card_of_dvd_card (even_iff_two_dvd.1 (even_natCard_of_perfect G))
  rw [hQ] at h2
  exact absurd h2 (by norm_num)

end Perfect

end TwoGroups

theorem commuting_noncyclic_eq {X : Type} [Group X] {R P P' : Subgroup X}
    (hR : IsCyclic R ∨ AschbacherTheorem3.IsDihedralTwoGroup R ∨
      AschbacherTheorem3.IsQuaternionTwoGroup R)
    (hP : P ≤ R) (hP' : P' ≤ R) (hPc : ¬ IsCyclic P) (hP'c : ¬ IsCyclic P')
    (hcomm : ∀ x ∈ P, ∀ y ∈ P', x * y = y * x) : P = P' := by
  rcases hR with hR | ⟨n, hn, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
  · exact absurd (Subgroup.isCyclic_of_le hP) hPc
  · rw [TwoGroups.two_pow_sub_one hn] at e
    obtain ⟨f, hf, rfl⟩ := TwoGroups.exists_embedding e
    exact TwoGroups.commuting_noncyclic_eq_of_index_two inferInstance
      TwoGroups.index_zpowers_r_one (fun _ hx _ hh hxh => TwoGroups.eq_of_comm_r hx hh hxh) hf
      hP hP' hPc hP'c hcomm
  · obtain ⟨f, hf, rfl⟩ := TwoGroups.exists_embedding e
    exact TwoGroups.commuting_noncyclic_eq_of_index_two inferInstance
      TwoGroups.index_zpowers_a_one (fun _ hx _ hh hxh => TwoGroups.eq_of_comm_a hx hh hxh) hf
      hP hP' hPc hP'c hcomm

theorem mem_of_normal_noncyclic {X : Type} [Group X] {R P : Subgroup X}
    (hR : IsCyclic R ∨ AschbacherTheorem3.IsDihedralTwoGroup R ∨
      AschbacherTheorem3.IsQuaternionTwoGroup R)
    {z : X} (hzR : z ∈ R) (hz : z ≠ 1) (hz2 : z ^ 2 = 1) (hzc : ∀ x ∈ R, z * x = x * z)
    (hPR : P ≤ R) (hPn : (P.subgroupOf R).Normal) (hPc : ¬ IsCyclic P) : z ∈ P := by
  rcases hR with hR | ⟨n, hn, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
  · exact absurd (Subgroup.isCyclic_of_le hPR) hPc
  · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · have hcard : Nat.card R = 4 :=
        (Nat.card_congr e.toEquiv).trans (DihedralGroup.nat_card.trans (by norm_num))
      rw [TwoGroups.eq_of_card_four hPR hcard hPc]
      exact hzR
    · rw [TwoGroups.two_pow_sub_one hn] at e
      obtain ⟨f, hf, rfl⟩ := TwoGroups.exists_embedding e
      exact TwoGroups.dihedral_mem_of_normal (Nat.even_pow.2 ⟨even_two, by omega⟩) hf hzR hz
        hzc hPR hPn hPc
  · obtain ⟨f, hf, rfl⟩ := TwoGroups.exists_embedding e
    exact TwoGroups.quaternion_mem_of_noncyclic hf hzR hz hz2 hPR hPc

theorem dihedral_centralizer_four {X : Type} [Group X] {R : Subgroup X}
    (hR : AschbacherTheorem3.IsDihedralTwoGroup R) {a : X} (ha : a ∈ R) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) :
    ∃ V : Subgroup X, V ≤ R ∧ a ∈ V ∧ (∀ v ∈ V, v * a = a * v) ∧
      CFSG.Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hR
  rw [TwoGroups.two_pow_sub_one hn] at e
  obtain ⟨f, hf, rfl⟩ := TwoGroups.exists_embedding e
  exact TwoGroups.dihedral_four hf ha ha1 ha2

theorem dihedral_pRank_two {X : Type} [Group X] [Finite X] {R : Subgroup X}
    (hR : AschbacherTheorem3.IsDihedralTwoGroup R) : CFSG.Open.pRank 2 R = 2 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hR
  rw [TwoGroups.two_pow_sub_one hn] at e
  obtain ⟨f, hf, rfl⟩ := TwoGroups.exists_embedding e
  exact TwoGroups.pRank_range_dihedral hf

theorem quaternion_unique_involution {X : Type} [Group X] {R : Subgroup X}
    (hR : AschbacherTheorem3.IsQuaternionTwoGroup R) {t t' : X} (ht : t ∈ R) (ht' : t' ∈ R)
    (h1 : orderOf t = 2) (h2 : orderOf t' = 2) : t = t' := by
  obtain ⟨n, -, ⟨e⟩⟩ := hR
  exact TwoGroups.quaternion_eq_of_equiv e ht ht' h1 h2

theorem cyclic_or_quaternion_of_pRank_le_one {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (hr : CFSG.Open.pRank 2 P ≤ 1) :
    IsCyclic P ∨ AschbacherTheorem3.IsQuaternionTwoGroup P :=
  TwoGroups.cyclic_or_quaternion hP hr

theorem eq_of_pRank_le_one {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (hr : CFSG.Open.pRank 2 P ≤ 1) {t t' : X} (ht : t ∈ P) (ht' : t' ∈ P)
    (h1 : orderOf t = 2) (h2 : orderOf t' = 2) : t = t' := by
  rcases TwoGroups.cyclic_or_quaternion hP hr with hc | ⟨n, -, ⟨e⟩⟩
  · exact AschbacherKnownGroup.TwoGroup.involution_unique_of_isCyclic hc ht ht'
      (TwoGroups.sq_eq_one_of_orderOf h1) (TwoGroups.ne_one_of_orderOf h1)
      (TwoGroups.sq_eq_one_of_orderOf h2) (TwoGroups.ne_one_of_orderOf h2)
  · exact TwoGroups.quaternion_eq_of_equiv e ht ht' h1 h2

theorem sylow_not_cyclic_of_perfect {X : Type*} [Group X] [Finite X] {Y P : Subgroup X}
    (hYp : Group.IsPerfect Y) (hY : Y ≠ ⊥) (hP : CFSG.ABGLocalTools.IsSylowOf 2 P Y) :
    ¬ IsCyclic P := by
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hY
  intro hPc
  obtain ⟨Q, rfl⟩ := hP
  have hQc : IsCyclic (Q : Subgroup Y) := isCyclic_of_injective
    (Subgroup.equivMapOfInjective (Q : Subgroup Y) Y.subtype Y.subtype_injective).toMonoidHom
    (MulEquiv.injective _)
  have hmin : (Nat.card Y).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).2 (even_iff_two_dvd.1 (TwoGroups.even_natCard_of_perfect Y))
  exact TwoGroups.not_normalizer_le_centralizer Q (hQc.normalizer_le_centralizer hmin)

theorem sylow_not_le_centralizer_of_perfect {X : Type*} [Group X] [Finite X] {Y P : Subgroup X}
    (hYp : Group.IsPerfect Y) (hY : Y ≠ ⊥) (hP : CFSG.ABGLocalTools.IsSylowOf 2 P Y) :
    ¬ P ≤ Subgroup.centralizer (Y : Set X) := by
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hY
  intro hPC
  obtain ⟨Q, rfl⟩ := hP
  refine TwoGroups.not_normalizer_le_centralizer Q fun g _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hPC ⟨h, hh, rfl⟩) g g.2).symm

end CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
