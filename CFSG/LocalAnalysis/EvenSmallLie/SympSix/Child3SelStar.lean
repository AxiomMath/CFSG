module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup
open scoped commutatorElement

theorem mem_zpowers_iff_of_orderOf_eq_two {Y : Type} [Group Y] {a x : Y} (ha : orderOf a = 2) :
    x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  classical
  have hfin : IsOfFinOrder a := orderOf_pos_iff.1 (by rw [ha]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, ha]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (pow_zero a)
    · exact Or.inr (pow_one a)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero a⟩
    · exact ⟨1, by norm_num, pow_one x⟩

theorem card_centralizer_subtype {Y : Type} [Group Y] (X : Subgroup Y) (t : X) :
    Nat.card (centralizer ({t} : Set X)) = Nat.card ↥(X ⊓ centralizer ({(t : Y)} : Set Y)) := by
  have h : (centralizer ({t} : Set X)).map X.subtype = X ⊓ centralizer ({(t : Y)} : Set Y) := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, subtype_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by simpa using congrArg Subtype.val hx⟩
    · rintro ⟨hyX, hy⟩
      exact ⟨⟨y, hyX⟩, Subtype.ext (by simpa using hy), rfl⟩
  rw [← h, Subgroup.card_map_of_injective X.subtype_injective]

theorem card_centralizer_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (x : A) :
    Nat.card (centralizer ({e x} : Set B)) = Nat.card (centralizer ({x} : Set A)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)).symm
  simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem not_four_dvd_card_of_centralizer {X : Type} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2) (h : ¬ 4 ∣ Nat.card (centralizer ({t} : Set X))) :
    ¬ 4 ∣ Nat.card X := by
  intro h4
  have hpt : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := hpt.exists_le_sylow
  have htS : t ∈ (S : Subgroup X) := hS (mem_zpowers t)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  set C : Subgroup X := (S : Subgroup X) ⊓ centralizer ({t} : Set X) with hCdef
  have hCp : IsPGroup 2 C := S.isPGroup'.to_le inf_le_left
  obtain ⟨k, hk⟩ := hCp.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk2
    apply h
    have hdvd : Nat.card C ∣ Nat.card (centralizer ({t} : Set X)) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hk] at hdvd
    exact (pow_dvd_pow 2 (by omega : 2 ≤ k)).trans hdvd
  have htC : zpowers t ≤ C := by
    rw [zpowers_le]
    exact ⟨htS, mem_centralizer_singleton_iff.2 rfl⟩
  have hCeq : C = zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge htC ?_).symm
    rw [hk, Nat.card_zpowers, ht]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := pow_one 2
  have : Nontrivial (S : Subgroup X) := ⟨⟨⟨t, htS⟩, 1, fun h' => ht1 (congrArg Subtype.val h')⟩⟩
  have hZ := S.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : center (S : Subgroup X))
  have hzS : ((z : (S : Subgroup X)) : X) ∈ C := by
    refine mem_inf.2 ⟨(z : (S : Subgroup X)).2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_center_iff.1 z.2 ⟨t, htS⟩
    exact (congrArg Subtype.val this).symm
  rw [hCeq, mem_zpowers_iff_of_orderOf_eq_two ht] at hzS
  have hzt : ((z : (S : Subgroup X)) : X) = t := by
    refine hzS.resolve_left fun h' => hz1 ?_
    exact Subtype.ext (Subtype.ext h')
  have hSC : (S : Subgroup X) ≤ C := by
    intro s hs
    refine mem_inf.2 ⟨hs, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_center_iff.1 z.2 ⟨s, hs⟩
    have h' := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h'
    rw [hzt] at h'
    exact h'
  have hcardS : Nat.card (S : Subgroup X) ≤ 2 := by
    have := Subgroup.card_le_of_le hSC
    rwa [hCeq, Nat.card_zpowers, ht] at this
  have hfac : 2 ≤ (Nat.card X).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 (by simpa using h4)
  rw [S.card_eq_multiplicity] at hcardS
  have : 2 ^ 2 ≤ 2 ^ (Nat.card X).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  omega

theorem not_four_dvd_card_of_inf_centralizer {Y : Type} [Group Y] [Finite Y] (X : Subgroup Y)
    {t : Y} (htX : t ∈ X) (ht : orderOf t = 2)
    (h : ¬ 4 ∣ Nat.card ↥(X ⊓ centralizer ({t} : Set Y))) : ¬ 4 ∣ Nat.card X := by
  refine not_four_dvd_card_of_centralizer (t := ⟨t, htX⟩) ?_ ?_
  · rw [Subgroup.orderOf_mk, ht]
  · rwa [card_centralizer_subtype]

theorem odd_card_of_forall_mul_self {G : Type} [Group G] [Finite G]
    (h : ∀ g : G, g * g = 1 → g = 1) : Odd (Nat.card G) := by
  rcases Nat.even_or_odd (Nat.card G) with he | ho
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 he)
    have h1 := h g (by rw [← pow_two, ← hg, pow_orderOf_eq_one])
    rw [h1, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · exact ho

@[expose] def glThree : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide +kernel,
    by decide +kernel⟩

@[expose] def glSeven : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], !![1, 1, 0; 0, 0, 1; 1, 0, 0], by decide +kernel,
    by decide +kernel⟩

theorem val_glThree :
    (glThree : Matrix (Fin 3) (Fin 3) (ZMod 2)) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem val_glSeven :
    (glSeven : Matrix (Fin 3) (Fin 3) (ZMod 2)) = !![0, 0, 1; 1, 0, 1; 0, 1, 0] := rfl

theorem orderOf_glThree : orderOf glThree = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, val_glThree, Units.val_one]
    decide +kernel
  · intro h
    have h' := congrArg Units.val h
    rw [val_glThree, Units.val_one] at h'
    exact absurd h' (by decide +kernel)

theorem orderOf_glSeven : orderOf glSeven = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, val_glSeven, Units.val_one]
    decide +kernel
  · intro h
    have h' := congrArg Units.val h
    rw [val_glSeven, Units.val_one] at h'
    exact absurd h' (by decide +kernel)

theorem matrix_comm_glThree : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    M * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = !![0, 0, 1; 1, 0, 0; 0, 1, 0] * M → M * M = 1 →
      M = 1 := by
  decide +kernel

theorem matrix_comm_glSeven : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    M * !![0, 0, 1; 1, 0, 1; 0, 1, 0] = !![0, 0, 1; 1, 0, 1; 0, 1, 0] * M → M * M = 1 →
      M = 1 := by
  decide +kernel

theorem odd_card_centralizer_of_matrix {A : GL (Fin 3) (ZMod 2)}
    (hA : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M * (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M → M * M = 1 → M = 1) :
    Odd (Nat.card (centralizer ({A} : Set (GL (Fin 3) (ZMod 2))))) := by
  apply odd_card_of_forall_mul_self
  rintro ⟨g, hg⟩ hgg
  rw [mem_centralizer_singleton_iff] at hg
  have h1 := hA (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (by
      rw [← Units.val_mul, ← Units.val_mul, hg])
    (by
      have := congrArg (fun x : centralizer ({A} : Set (GL (Fin 3) (ZMod 2))) =>
        ((x : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) hgg
      simpa using this)
  exact Subtype.ext (Units.ext (by simpa using h1))

theorem odd_card_centralizer_glThree :
    Odd (Nat.card (centralizer ({glThree} : Set (GL (Fin 3) (ZMod 2))))) :=
  odd_card_centralizer_of_matrix (by rw [val_glThree]; exact matrix_comm_glThree)

theorem odd_card_centralizer_glSeven :
    Odd (Nat.card (centralizer ({glSeven} : Set (GL (Fin 3) (ZMod 2))))) :=
  odd_card_centralizer_of_matrix (by rw [val_glSeven]; exact matrix_comm_glSeven)

namespace GL3Source

variable {Y : Type} [Group Y] {D : Subgroup Y} {a : Y} {J : Subgroup Y}

theorem mem_centralizer_J (h : GL3Source D a J) : a ∈ centralizer (J : Set Y) :=
  mem_centralizer_iff.2 fun _ hj => mem_centralizer_singleton_iff.1 (h.le_centralizer hj)

theorem zpowers_le_normalizer_of_le (h : GL3Source D a J) {H : Subgroup Y} (hH : H ≤ J) :
    zpowers a ≤ normalizer (H : Set Y) :=
  zpowers_le.2 (centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _ hj => mem_centralizer_singleton_iff.1 (h.le_centralizer (hH hj))))

theorem exists_of_mem_centralizer (h : GL3Source D a J) {x : Y}
    (hx : x ∈ centralizer ({a} : Set Y)) : ∃ k ∈ zpowers a, ∃ j ∈ J, k * j = x := by
  rw [← h.sup_eq] at hx
  have hx' : x ∈ ((zpowers a ⊔ J : Subgroup Y) : Set Y) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ (h.zpowers_le_normalizer_of_le le_rfl)] at hx'
  obtain ⟨k, hk, j, hj, rfl⟩ := hx'
  exact ⟨k, hk, j, hj, rfl⟩

theorem mem_centralizer_of_mem (h : GL3Source D a J) {g : Y} (hg : g ∈ J) :
    a ∈ centralizer ({g} : Set Y) :=
  mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (h.le_centralizer hg)).symm

theorem centralizer_inf_centralizer (h : GL3Source D a J) {g : Y} (hg : g ∈ J) :
    centralizer ({g} : Set Y) ⊓ centralizer ({a} : Set Y) =
      zpowers a ⊔ (J ⊓ centralizer ({g} : Set Y)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxg, hxa⟩ := mem_inf.1 hx
    obtain ⟨k, hk, j, hj, rfl⟩ := h.exists_of_mem_centralizer hxa
    have hkg : k ∈ centralizer ({g} : Set Y) := (zpowers_le.2 (h.mem_centralizer_of_mem hg)) hk
    have hjg : j ∈ centralizer ({g} : Set Y) := by
      have := (centralizer ({g} : Set Y)).mul_mem ((centralizer ({g} : Set Y)).inv_mem hkg) hxg
      simpa using this
    exact mul_mem_sup hk (mem_inf.2 ⟨hj, hjg⟩)
  · refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact mem_inf.2 ⟨h.mem_centralizer_of_mem hg, mem_centralizer_singleton_iff.2 rfl⟩
    · exact le_inf inf_le_right (inf_le_left.trans h.le_centralizer)

theorem card_centralizer_inf_centralizer (h : GL3Source D a J) {g : Y} (hg : g ∈ J) :
    Nat.card ↥(centralizer ({g} : Set Y) ⊓ centralizer ({a} : Set Y)) =
      Nat.card ↥(J ⊓ centralizer ({g} : Set Y)) * 2 := by
  rw [h.centralizer_inf_centralizer hg, sup_comm,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (h.zpowers_le_normalizer_of_le inf_le_left), Nat.card_zpowers, h.orderOf_eq]
  rw [disjoint_iff, eq_bot_iff, ← h.inf_eq, inf_comm]
  exact inf_le_inf_left _ inf_le_left

theorem not_four_dvd_card_centralizer [Finite Y] (h : GL3Source D a J) {g : Y} (hg : g ∈ J)
    (hodd : Odd (Nat.card ↥(J ⊓ centralizer ({g} : Set Y)))) :
    ¬ 4 ∣ Nat.card (centralizer ({g} : Set Y)) := by
  refine not_four_dvd_card_of_inf_centralizer _ (h.mem_centralizer_of_mem hg) h.orderOf_eq ?_
  rw [h.card_centralizer_inf_centralizer hg]
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ := hodd
  omega

theorem odd_card_inf_centralizer_of_not_mem [Finite Y] (h : GL3Source D a J) (ha : a ∉ D)
    {g : Y} (hg : g ∈ J) (hodd : Odd (Nat.card ↥(J ⊓ centralizer ({g} : Set Y)))) :
    Odd (Nat.card ↥(D ⊓ centralizer ({g} : Set Y))) := by
  have hD := h.normal
  have haC := h.mem_centralizer_of_mem hg
  have hnorm : zpowers a ≤ normalizer ((D ⊓ centralizer ({g} : Set Y) : Subgroup Y) : Set Y) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxD, hxC⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨hD.conj_mem x hxD a, mul_mem (mul_mem haC hxC) (inv_mem haC)⟩
    · intro hx
      obtain ⟨hxD, hxC⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨?_, ?_⟩
      · have := hD.conj_mem _ hxD a⁻¹
        simpa [mul_assoc] using this
      · have := mul_mem (mul_mem (inv_mem haC) hxC) haC
        simpa [mul_assoc] using this
  have hdisj : Disjoint (D ⊓ centralizer ({g} : Set Y)) (zpowers a) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxa⟩ := mem_inf.1 hx
    rcases (mem_zpowers_iff_of_orderOf_eq_two h.orderOf_eq).1 hxa with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.1 hxH).1 ha
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj
  have hle : (D ⊓ centralizer ({g} : Set Y)) ⊔ zpowers a ≤ centralizer ({g} : Set Y) :=
    sup_le inf_le_right (zpowers_le.2 haC)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard, Nat.card_zpowers, h.orderOf_eq] at hdvd
  have h4 := h.not_four_dvd_card_centralizer hg hodd
  rcases Nat.even_or_odd (Nat.card ↥(D ⊓ centralizer ({g} : Set Y))) with ⟨m, hm⟩ | ho
  · exact absurd ((show 4 ∣ Nat.card ↥(D ⊓ centralizer ({g} : Set Y)) * 2 from
      ⟨m, by omega⟩).trans hdvd) h4
  · exact ho

theorem exists_odd (h : GL3Source D a J) {q : ℕ} (hq : q = 3 ∨ q = 7) :
    ∃ g ∈ J, orderOf g = q ∧ Odd (Nat.card ↥(J ⊓ centralizer ({g} : Set Y))) := by
  obtain ⟨ψ⟩ := h.gl3
  obtain ⟨M, hMq, hModd⟩ : ∃ M : GL (Fin 3) (ZMod 2), orderOf M = q ∧
      Odd (Nat.card (centralizer ({M} : Set (GL (Fin 3) (ZMod 2))))) := by
    rcases hq with rfl | rfl
    · exact ⟨glThree, orderOf_glThree, odd_card_centralizer_glThree⟩
    · exact ⟨glSeven, orderOf_glSeven, odd_card_centralizer_glSeven⟩
  refine ⟨(ψ.symm M : J), (ψ.symm M).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hMq]
  · rw [← card_centralizer_subtype J (ψ.symm M), card_centralizer_mulEquiv ψ.symm M]
    exact hModd

theorem exists_star [Finite Y] (h : GL3Source D a J) {T : Type} [Group T] (e : D ≃* T) {q : ℕ}
    (hq : q = 3 ∨ q = 7) : ∃ x : T, orderOf x = q ∧
      ¬ 4 ∣ Nat.card (centralizer ({x} : Set T)) ∧
      (a ∉ D → Odd (Nat.card (centralizer ({x} : Set T)))) := by
  obtain ⟨g, hgJ, hgq, hodd⟩ := h.exists_odd hq
  refine ⟨e ⟨g, h.le hgJ⟩, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hgq]
  · rw [card_centralizer_mulEquiv, card_centralizer_subtype]
    intro h4
    exact h.not_four_dvd_card_centralizer hgJ hodd
      (h4.trans (Subgroup.card_dvd_of_le inf_le_right))
  · intro ha
    rw [card_centralizer_mulEquiv, card_centralizer_subtype]
    exact h.odd_card_inf_centralizer_of_not_mem ha hgJ hodd

theorem mem_of_e3 [Finite Y] (h : GL3Source D a J) {T : Type} [Group T] (e : D ≃* T)
    (he : ∀ x : T, orderOf x = 3 → 2 ∣ Nat.card (centralizer ({x} : Set T))) : a ∈ D := by
  by_contra ha
  obtain ⟨x, hx, -, hodd⟩ := h.exists_star e (Or.inl rfl)
  exact (Nat.not_even_iff_odd.2 (hodd ha)) (even_iff_two_dvd.2 (he x hx))

end GL3Source

theorem false_of_k3 {T : Type} [Group T]
    (hk : ∀ x : T, orderOf x = 3 → 4 ∣ Nat.card (centralizer ({x} : Set T))) :
    ExcludedSource T := by
  intro Y _ _ D a J h ⟨e⟩
  obtain ⟨x, hx, h4, -⟩ := h.exists_star e (Or.inl rfl)
  exact h4 (hk x hx)

theorem glThree_mul_glSeven_ne : glThree * glSeven ≠ glSeven * glThree := by
  intro h
  have h' := congrArg Units.val h
  rw [Units.val_mul, Units.val_mul, val_glThree, val_glSeven] at h'
  exact absurd h' (by decide +kernel)

theorem isQuasisimple_of_isSimpleGroup {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ x y : X, x * y ≠ y * x) : CFSG.IsQuasisimple X := by
  have := hs
  obtain ⟨x, y, hxy⟩ := hnab
  have hc : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exact absurd (mem_center_iff.1 (h ▸ mem_top y) x) hxy
  let e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hcomm : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      apply hxy
      have hmem : ⁅x, y⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
      rw [h, mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
      exact hmem
    · exact h
  refine ⟨Group.isPerfect_def.mpr hcomm, e.isSimpleGroup, ?_⟩
  exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by simpa using h))⟩

theorem isSimpleGroup_and_nonab_of_GL {X : Type} [Group X] (ψ : X ≃* GL (Fin 3) (ZMod 2)) :
    IsSimpleGroup X ∧ ∃ x y : X, x * y ≠ y * x := by
  have :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
  refine ⟨ψ.isSimpleGroup, ψ.symm glThree, ψ.symm glSeven, fun h => ?_⟩
  apply glThree_mul_glSeven_ne
  simpa using congrArg ψ h

namespace GL3Source

variable {Y : Type} [Group Y] {D : Subgroup Y} {a : Y} {J : Subgroup Y}

theorem exists_component_of_mem (h : GL3Source D a J) (ha : a ∈ D) {T : Type} [Group T]
    (e : D ≃* T) :
    ∃ u : T, orderOf u = 2 ∧ ∃ B : Subgroup (centralizer ({u} : Set T)), CFSG.IsComponent B := by
  obtain ⟨ψ⟩ := h.gl3
  set u : T := e ⟨a, ha⟩ with hu
  set JT : Subgroup T := (J.subgroupOf D).map e.toMonoidHom with hJT
  have hJTu : JT ≤ centralizer ({u} : Set T) := by
    rintro x ⟨j, hj, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, hu, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 (h.le_centralizer (mem_subgroupOf.1 hj))
  have hconj : ∀ c ∈ centralizer ({u} : Set T), ∀ x ∈ JT, c * x * c⁻¹ ∈ JT := by
    intro c hc x hx
    obtain ⟨j, hj, rfl⟩ := hx
    set d : D := e.symm c with hd
    have hcd : c = e d := by rw [hd, MulEquiv.apply_symm_apply]
    have hdC : (d : Y) ∈ centralizer ({a} : Set Y) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [hcd, hu, ← map_mul, ← map_mul] at hc
      exact congrArg Subtype.val (e.injective hc)
    obtain ⟨k, hk, j₀, hj₀, hkj⟩ := h.exists_of_mem_centralizer hdC
    have hkC : k ∈ centralizer (J : Set Y) :=
      (zpowers_le.2 h.mem_centralizer_J) hk
    have hmem : (d : Y) * (j : Y) * (d : Y)⁻¹ ∈ J := by
      rw [← hkj]
      have hj' : (j : Y) ∈ J := mem_subgroupOf.1 hj
      have h1 : j₀ * (j : Y) * j₀⁻¹ ∈ J := mul_mem (mul_mem hj₀ hj') (inv_mem hj₀)
      have h2 := mem_centralizer_iff.1 hkC _ h1
      have h3 : k * j₀ * (j : Y) * (k * j₀)⁻¹ = j₀ * (j : Y) * j₀⁻¹ :=
        calc k * j₀ * (j : Y) * (k * j₀)⁻¹ = (k * (j₀ * (j : Y) * j₀⁻¹)) * k⁻¹ := by group
          _ = (j₀ * (j : Y) * j₀⁻¹ * k) * k⁻¹ := by rw [h2]
          _ = j₀ * (j : Y) * j₀⁻¹ := by group
      rw [h3]
      exact h1
    refine ⟨d * j * d⁻¹, mem_subgroupOf.2 (by simpa using hmem), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hcd]
  have hnorm : centralizer ({u} : Set T) ≤ normalizer (JT : Set T) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj c hc x, fun hx => ?_⟩
    have := hconj c⁻¹ (inv_mem hc) _ hx
    simpa [mul_assoc] using this
  refine ⟨u, ?_, JT.subgroupOf (centralizer ({u} : Set T)), ?_, ?_⟩
  · rw [hu, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h.orderOf_eq]
  ·
    let χ : ↥(JT.subgroupOf (centralizer ({u} : Set T))) ≃* GL (Fin 3) (ZMod 2) :=
      ((Subgroup.subgroupOfEquivOfLe hJTu).trans
        ((J.subgroupOf D).equivMapOfInjective e.toMonoidHom e.injective).symm).trans
        ((Subgroup.subgroupOfEquivOfLe h.le).trans ψ)
    obtain ⟨hs, hnab⟩ := isSimpleGroup_and_nonab_of_GL χ
    exact isQuasisimple_of_isSimpleGroup hs hnab
  ·
    exact ((normal_subgroupOf_iff_le_normalizer hJTu).2 hnorm).isSubnormal

end GL3Source

end CFSG.EvenSmallLie.Child3
