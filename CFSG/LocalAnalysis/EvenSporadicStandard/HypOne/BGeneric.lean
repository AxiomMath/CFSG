module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.ComponentClassification.M12Cover

structure FourType (T : Type*) [Group T] : Prop where
  pow_four : ∀ t : T, t ^ 4 = 1
  exists_sq : ∃ t : T, t ^ 2 ≠ 1
  sq_unique : ∀ s t : T, s ^ 2 ≠ 1 → t ^ 2 ≠ 1 → s ^ 2 = t ^ 2
  card_sq_le : Nat.card {t : T // t ^ 2 ≠ 1} ≤ 4
  card_ge : 3 ≤ Nat.card T
  card_le : Nat.card T ≤ 8
  isPGroup : IsPGroup 2 T

theorem fourType_z4 : FourType (Multiplicative (ZMod 4)) where
  pow_four := by decide
  exists_sq := by decide
  sq_unique := by decide
  card_sq_le := by rw [card_sq_ne_one_four]; norm_num
  card_ge := by simp
  card_le := by simp
  isPGroup := IsPGroup.of_card (n := 2) (by simp)

theorem fourType_z2z4 : FourType (Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) where
  pow_four := by decide
  exists_sq := by decide
  sq_unique := by decide
  card_sq_le := by rw [card_sq_ne_one_two_four]
  card_ge := by simp
  card_le := by simp
  isPGroup := IsPGroup.of_card (n := 3) (by simp)

section Roots

variable {C : Type*} [Group C]

theorem FourType.exists_normal_root {T : Type*} [Group T] [Finite T] (hT : FourType T)
    {N : Subgroup C} (hN : N.Normal) (e : N ≃* T) :
    ∃ n : C, n ^ 2 ≠ 1 ∧ n ^ 4 = 1 ∧ (∀ c : C, c * n ^ 2 * c⁻¹ = n ^ 2) ∧
      Nat.card {y : C // IsConj n y} ≤ 4 := by
  obtain ⟨t₀, ht₀⟩ := hT.exists_sq
  set m₀ : N := e.symm t₀ with hm₀
  set n : C := (m₀ : C) with hn
  have hm₀2 : m₀ ^ 2 ≠ 1 := by
    intro h
    apply ht₀
    have := congrArg e h
    rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
  have hn2 : n ^ 2 ≠ 1 := by
    intro h
    apply hm₀2
    exact Subtype.ext (by simpa using h)
  have hn4 : n ^ 4 = 1 := by
    have h4 : m₀ ^ 4 = 1 := by
      have := congrArg e.symm (hT.pow_four t₀)
      rwa [map_pow, map_one] at this
    have := congrArg Subtype.val h4
    simpa using this
  have hconj : ∀ c : C, c * n * c⁻¹ ∈ N := fun c => hN.conj_mem n m₀.2 c
  have hsq : ∀ c : C, (c * n * c⁻¹) ^ 2 ≠ 1 := by
    intro c h
    apply hn2
    have : c * n ^ 2 * c⁻¹ = 1 := by rw [← conj_pow]; exact h
    simpa using this
  have hsq' : ∀ c : C, (c * n * c⁻¹) ^ 2 = n ^ 2 := by
    intro c
    have h1 := hT.sq_unique (e ⟨c * n * c⁻¹, hconj c⟩) t₀ (by
      intro h
      apply hsq c
      have := congrArg e.symm h
      rw [map_pow, MulEquiv.symm_apply_apply, map_one] at this
      simpa using congrArg Subtype.val this) ht₀
    have h2 := congrArg e.symm h1
    rw [map_pow, MulEquiv.symm_apply_apply, map_pow] at h2
    simpa using congrArg Subtype.val h2
  refine ⟨n, hn2, hn4, fun c => ?_, ?_⟩
  · have := hsq' c
    rwa [conj_pow] at this
  · have hfin : Finite {t : T // t ^ 2 ≠ 1} := inferInstance
    refine le_trans (Nat.card_le_card_of_injective
      (fun y : {y : C // IsConj n y} => (⟨e ⟨y.1, ?_⟩, ?_⟩ : {t : T // t ^ 2 ≠ 1})) ?_) hT.card_sq_le
    · obtain ⟨c, hc⟩ := isConj_iff.1 y.2
      rw [← hc]
      exact hconj c
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 y.2
      apply hsq c
      have := congrArg e.symm h
      rw [map_pow, MulEquiv.symm_apply_apply, map_one] at this
      have h' : y.1 ^ 2 = 1 := by simpa using congrArg Subtype.val this
      rw [hc]
      exact h'
    · intro a b hab
      have h1 := e.injective (congrArg Subtype.val hab)
      have h3 : (a : C) = b := congrArg (Subtype.val : N → C) h1
      exact Subtype.ext h3

theorem noNormalFour_of_root_class_large (w : C)
    (hcen : ∀ z : C, z * z = 1 → (∀ y : C, z * y = y * z) → z = 1 ∨ z = w)
    (hroot : ∀ n : C, n * n = w → 5 ≤ Nat.card {y : C // IsConj n y}) : NoNormalFour C := by
  have key : ∀ (T : Type) [Group T] [Finite T], FourType T → ∀ N : Subgroup C, N.Normal →
      IsEmpty (N ≃* T) := by
    intro T _ _ hT N hN
    refine ⟨fun e => ?_⟩
    obtain ⟨n, hn2, hn4, hcentral, hcard⟩ := hT.exists_normal_root hN e
    have hu : n ^ 2 * n ^ 2 = 1 := by rw [← pow_add]; exact hn4
    have hu' := hcen (n ^ 2) hu (fun y => by
      have := hcentral y
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm)
    have hnw : n * n = w := by
      rcases hu' with h | h
      · exact absurd h hn2
      · rwa [pow_two] at h
    have := hroot n hnw
    omega
  intro N hN
  exact ⟨key _ fourType_z4 N hN, key _ fourType_z2z4 N hN⟩

end Roots

section Perfect

variable {G : Type*} [Group G] [Finite G]

theorem isPerfect_centralizes_of_card_conj_le (L : Subgroup G) (hL : Group.IsPerfect L) (n : G)
    (hn : Nat.card {y : G // IsConj n y} ≤ 4) : ∀ l ∈ L, l * n * l⁻¹ = n := by
  classical
  let _ : MulAction L G := MulAction.compHom G
    (((MulAut.toPerm G).comp (MulAut.conj : G →* MulAut G)).comp L.subtype)
  have hsmul : ∀ (l : L) (y : G), l • y = (l : G) * y * (l : G)⁻¹ := fun l y => rfl
  have horb : Nat.card (MulAction.orbit L n) ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun y : MulAction.orbit L n => (⟨y.1, ?_⟩ : {y : G // IsConj n y})) ?_) hn
    · obtain ⟨l, hl⟩ := y.2
      have h : (y : G) = l • n := hl.symm
      rw [h, hsmul]
      exact isConj_iff.2 ⟨l, rfl⟩
    · intro a b hab
      have h3 : (a : G) = b := congrArg (Subtype.val : {y : G // IsConj n y} → G) hab
      exact Subtype.ext h3
  let φ := MulAction.toPermHom L (MulAction.orbit L n)
  have : Group.IsSolvable (Equiv.Perm (MulAction.orbit L n)) := Equiv.Perm.isSolvable horb
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  intro l hl
  have h1 : φ ⟨l, hl⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨φ ⟨l, hl⟩, ⟨l, hl⟩, rfl⟩ : φ.range) 1)
  have h2 := congrArg
    (fun τ : Equiv.Perm (MulAction.orbit L n) => (τ ⟨n, MulAction.mem_orbit_self n⟩ : G)) h1
  simpa [φ, hsmul] using h2

end Perfect

theorem noNormalFour_of_perfect_index_two {E : Type*} [Group E] [Finite E]
    (hperf : Group.IsPerfect (commutator E)) (hidx : (commutator E).index = 2)
    (hZL : ∀ z ∈ commutator E, (∀ l ∈ commutator E, z * l = l * z) → z * z = 1)
    (hZE : ∀ z : E, (∀ y : E, z * y = y * z) → z * z = 1) : NoNormalFour E := by
  have key : ∀ (T : Type) [Group T] [Finite T], FourType T → ∀ N : Subgroup E, N.Normal →
      IsEmpty (N ≃* T) := by
    intro T _ _ hT N hN
    refine ⟨fun e => ?_⟩
    obtain ⟨n, hn2, -, -, hcard⟩ := hT.exists_normal_root hN e
    have hc := isPerfect_centralizes_of_card_conj_le (commutator E) hperf n hcard
    have hnn : n * n ≠ 1 := by rwa [pow_two] at hn2
    by_cases hnL : n ∈ commutator E
    · apply hnn
      refine hZL n hnL fun l hl => ?_
      have := hc l hl
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · apply hnn
      refine hZE n fun y => ?_
      by_cases hyL : y ∈ commutator E
      · have := hc y hyL
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      · have hmem : n⁻¹ * y ∈ commutator E := by
          rw [mul_mem_iff_of_index_two hidx]
          exact ⟨fun h => absurd (inv_mem_iff.1 h) hnL, fun h => absurd h hyL⟩
        have h1 := hc _ hmem
        rw [mul_inv_eq_iff_eq_mul] at h1
        calc n * y = n * (n * (n⁻¹ * y)) := by group
          _ = n * ((n⁻¹ * y) * n) := by rw [h1]
          _ = (n * (n⁻¹ * y)) * n := by group
          _ = y * n := by group
  intro N hN
  exact ⟨key _ fourType_z4 N hN, key _ fourType_z2z4 N hN⟩

theorem noNormalFour_of_invariant_subgroups {G : Type*} [Group G] [Finite G] (J Q : Subgroup G)
    (hQJ : Q ≤ J) (x : G) (hQcard : 8 < Nat.card Q) (hJ2 : ¬ IsPGroup 2 J)
    (hx : Nat.card (zpowers x) ≤ 2) (hQ2 : IsPGroup 2 Q)
    (hQn : ∀ h ∈ J, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hinv : ∀ R : Subgroup G, R ≤ Q → (∀ h ∈ J, ∀ r ∈ R, h * r * h⁻¹ ∈ R) →
      R = ⊥ ∨ R = zpowers x ∨ R = Q)
    (hnorm : ∀ R : Subgroup G, Q ≤ R → R ≤ J → (∀ h ∈ J, ∀ r ∈ R, h * r * h⁻¹ ∈ R) →
      R = Q ∨ R = J) : NoNormalFour J := by
  have key : ∀ (T : Type) [Group T] [Finite T], FourType T → ∀ N : Subgroup J, N.Normal →
      IsEmpty (N ≃* T) := by
    intro T _ _ hT N hN
    refine ⟨fun e => ?_⟩
    set N' : Subgroup G := N.map J.subtype with hN'
    have hN'J : N' ≤ J := Subgroup.map_subtype_le N
    have hcardN' : Nat.card N' = Nat.card T := by
      rw [hN', Subgroup.card_map_of_injective J.subtype_injective]
      exact Nat.card_congr e.toEquiv
    have hN'inv : ∀ h ∈ J, ∀ r ∈ N', h * r * h⁻¹ ∈ N' := by
      rintro h hh _ ⟨m, hm, rfl⟩
      exact ⟨⟨h, hh⟩ * m * ⟨h, hh⟩⁻¹, hN.conj_mem m hm ⟨h, hh⟩, rfl⟩
    obtain ⟨k, hk⟩ := hT.isPGroup.exists_card_eq
    have hN'2 : IsPGroup 2 N' := IsPGroup.of_card (n := k) (by rw [hcardN', hk])
    have hnormQ : ∀ h ∈ J, h ∈ normalizer (Q : Set G) := by
      intro h hh
      rw [mem_normalizer_iff]
      intro q
      refine ⟨fun hq => hQn h hh q hq, fun hq => ?_⟩
      have h1 := hQn h⁻¹ (J.inv_mem hh) _ hq
      have h2 : h⁻¹ * (h * q * h⁻¹) * h⁻¹⁻¹ = q := by group
      rwa [h2] at h1
    have hRinv : ∀ h ∈ J, ∀ r ∈ N' ⊔ Q, h * r * h⁻¹ ∈ N' ⊔ Q := by
      intro h hh r hr
      have hmap : (N' ⊔ Q).map (MulAut.conj h).toMonoidHom ≤ N' ⊔ Q := by
        rw [Subgroup.map_sup]
        refine sup_le_sup ?_ ?_
        · rintro _ ⟨a, ha, rfl⟩
          exact hN'inv h hh a ha
        · rintro _ ⟨a, ha, rfl⟩
          exact hQn h hh a ha
      exact hmap ⟨r, hr, rfl⟩
    rcases hnorm (N' ⊔ Q) le_sup_right (sup_le hN'J hQJ) hRinv with h | h
    ·
      have hle : N' ≤ Q := by
        have := le_sup_left (a := N') (b := Q)
        rwa [h] at this
      rcases hinv N' hle hN'inv with h1 | h1 | h1
      · have := hT.card_ge
        rw [← hcardN', h1, Subgroup.card_bot] at this
        omega
      · have := hT.card_ge
        rw [← hcardN', h1] at this
        omega
      · have := hT.card_le
        rw [← hcardN', h1] at this
        omega
    · have hsup : IsPGroup 2 (N' ⊔ Q : Subgroup G) :=
        IsPGroup.to_sup_of_normal_right' hN'2 hQ2 (fun r hr => hnormQ r (hN'J hr))
      rw [h] at hsup
      exact hJ2 hsup
  intro N hN
  exact ⟨key _ fourType_z4 N hN, key _ fourType_z2z4 N hN⟩

theorem noNormalFour_of_mulEquiv {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    (h : NoNormalFour A) : NoNormalFour A' := by
  intro N hN
  have hN' : (N.comap e.toMonoidHom).Normal := hN.comap _
  have eN : N.comap e.toMonoidHom ≃* N :=
    (e.subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective e.surjective N))
  obtain ⟨h1, h2⟩ := h _ hN'
  exact ⟨⟨fun f => h1.false (eN.trans f)⟩, ⟨fun f => h2.false (eN.trans f)⟩⟩

theorem noNormalFour_centralizer_of_isConj {Y : Type*} [Group Y] {y y' : Y} (h : IsConj y y')
    (hy : NoNormalFour (centralizer ({y} : Set Y))) :
    NoNormalFour (centralizer ({y'} : Set Y)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e := centralizerEquiv (MulAut.conj c) y
  have hcy : (MulAut.conj c) y = y' := by
    rw [MulAut.conj_apply, hc]
  rw [hcy] at e
  exact noNormalFour_of_mulEquiv e hy

theorem noNormalFour_centralizer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {x : X} {y : Y} (hxy : e x = y) (hx : NoNormalFour (centralizer ({x} : Set X))) :
    NoNormalFour (centralizer ({y} : Set Y)) := by
  subst hxy
  exact noNormalFour_of_mulEquiv (centralizerEquiv e x) hx

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
