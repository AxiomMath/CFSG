module

public import CFSG.LocalAnalysis.GH72.Sec4CStruct
public import CFSG.LocalAnalysis.GH72.DDStructure
public import CFSG.LocalAnalysis.GH72.G3b

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement

namespace G4c

open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff comm_of_mul_self)

section Basic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_map_le {g : G} {K : Subgroup G} (h1 : K.map (cj g) ≤ K)
    (h2 : K.map (cj g⁻¹) ≤ K) : g ∈ normalizer (K : Set G) := by
  refine mem_normalizer_of_map_cj_eq (le_antisymm h1 ?_)
  have h := map_mono (f := cj g) h2
  rwa [map_cj_inv_cj] at h

omit [Finite G] in
theorem le_normalizer_O_sup {H L D : Subgroup G} (hLH : L ≤ H)
    (hLD : ⁅L, D⁆ ≤ O H) : L ≤ normalizer ((O H ⊔ D : Subgroup G) : Set G) := by
  intro m hm
  have key : ∀ m ∈ L, (O H ⊔ D).map (cj m) ≤ O H ⊔ D := by
    intro m hm
    rw [map_cj_sup, map_cj_eq_of_mem_normalizer (le_normalizer_O H (hLH hm))]
    refine sup_le le_sup_left ?_
    rintro _ ⟨d, hd, rfl⟩
    have hc : ⁅m, d⁆ ∈ O H := hLD (commutator_mem_commutator hm hd)
    have : cj m d = ⁅m, d⁆ * d := by
      rw [cj_apply, commutatorElement_def]
      group
    rw [this]
    exact mul_mem_sup hc hd
  exact mem_normalizer_of_map_le (key m hm) (key m⁻¹ (inv_mem hm))

theorem le_O_of_sup_eq {H L D E : Subgroup G} (hH : O2 H = (L ⊓ O2 H) ⊔ O H) (hDH : D ≤ H)
    (hD : Odd (Nat.card D)) (hDE : D ≤ E) (hE : Odd (Nat.card E))
    (hLE : L ⊓ O2 H ≤ normalizer (E : Set G)) : D ≤ O H := by
  set K := O2 H with hK
  set L' := L ⊓ K with hL'
  have hDK : D ≤ K := le_O2_of_odd hDH hD
  have hOK : O H ≤ K := O_le_O2 H
  have hL'K : L' ≤ K := inf_le_right
  have hKH : K ≤ H := O2_le H
  have hOKO : O K ≤ O H := O_le_O hKH (le_normalizer_O2 H)
  have hcrit : ∀ Q : Subgroup G, Q ≤ K → Odd (Nat.card Q) → L' ≤ normalizer
      ((O H ⊔ Q : Subgroup G) : Set G) → Q ≤ O H := by
    intro Q hQK hQ hL'Q
    have hnorm : K ≤ normalizer ((O H ⊔ Q : Subgroup G) : Set G) := by
      rw [show K = L' ⊔ O H from hH]
      exact sup_le hL'Q (le_sup_left.trans le_normalizer)
    have hodd : Odd (Nat.card (O H ⊔ Q : Subgroup G)) :=
      odd_card_sup (odd_card_O H) hQ ((hQK.trans hKH).trans (le_normalizer_O H))
    have hle : O H ⊔ Q ≤ O K := le_O_of_le_normalizer (sup_le hOK hQK) hnorm hodd
    exact le_sup_right.trans (hle.trans hOKO)
  have hD₁E : ⁅D, L'⁆ ≤ E :=
    (commutator_mono hDE le_rfl).trans (commutator_le_left_of_le_normalizer hLE)
  have hD₁O : ⁅D, L'⁆ ≤ O H := by
    refine hcrit _ (commutator_le_of_le hDK hL'K) (odd_card_of_le hD₁E hE) ?_
    exact le_trans (le_inf ((hL'K.trans hKH).trans (le_normalizer_O H))
      (le_normalizer_commutator_right D L')) (inf_normalizer_le_normalizer_sup _ _)
  refine hcrit D hDK hD (le_normalizer_O_sup (hL'K.trans hKH) ?_)
  rwa [commutator_comm]

theorem le_O_of_hasNormalTwoComplement {K D : Subgroup G} (hK : HasNormalTwoComplement K)
    (hDK : D ≤ K) (hD : Odd (Nat.card D)) : D ≤ O K := by
  obtain ⟨N, hNK, hNn, hNodd, n, hidx⟩ := hK
  have hKN : K ≤ normalizer (N : Set G) := (normal_subgroupOf_iff_le_normalizer hNK).mp hNn
  have hDN : D ≤ N := (le_O2_of_odd hDK hD).trans (O2_le_of_relIndex hNK hKN hidx)
  exact hDN.trans (le_O_of_le_normalizer hNK hKN hNodd)

theorem le_O_C_of_map_le {g x z : G} (hg : g * x * g⁻¹ = z) {K : Subgroup G}
    (h : K.map (cj g) ≤ O (C z)) : K ≤ O (C x) := by
  have hCx : (C x).map (cj g) = C z := by rw [map_cj_C, hg]
  rw [← hCx, ← map_cj_O] at h
  exact (map_le_map_iff_of_injective (cj_injective g)).mp h

theorem le_O_C_of_isConj {a b : G} (hab : IsConj a b) (hb : HasNormalTwoComplement (C b))
    {D : Subgroup G} (hDa : D ≤ C a) (hD : Odd (Nat.card D)) : D ≤ O (C a) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hCa : (C a).map (cj g) = C b := by rw [map_cj_C, hg]
  exact le_O_C_of_map_le hg
    (le_O_of_hasNormalTwoComplement hb (hCa ▸ map_mono hDa) (by rwa [card_map_cj]))

theorem cover_of_conj {x z g : G} (hg : g * x * g⁻¹ = z)
    (hz : ∀ K D : Subgroup G, K ≤ C z → ⁅O2 (C z), O2 (C z)⁆ ≤ K ⊔ O (C z) → D ≤ C z →
      Odd (Nat.card D) → K ≤ normalizer (D : Set G) → D ≤ O (C z))
    {K D : Subgroup G} (hKH : K ≤ C x) (hcov : ⁅O2 (C x), O2 (C x)⁆ ≤ K ⊔ O (C x))
    (hDH : D ≤ C x) (hD : Odd (Nat.card D)) (hKD : K ≤ normalizer (D : Set G)) :
    D ≤ O (C x) := by
  have hCx : (C x).map (cj g) = C z := by rw [map_cj_C, hg]
  refine le_O_C_of_map_le hg (hz (K.map (cj g)) (D.map (cj g)) (hCx ▸ map_mono hKH) ?_
    (hCx ▸ map_mono hDH) (by rwa [card_map_cj]) (map_cj_le_normalizer hKD))
  rw [← hCx, ← map_cj_O2, ← map_cj_commutator, ← map_cj_O, ← map_cj_sup]
  exact map_mono hcov

theorem inf_le_O_of_covers {H Cx M M₀ : Subgroup G}
    (hz : ∀ K D : Subgroup G, K ≤ Cx → ⁅O2 Cx, O2 Cx⁆ ≤ K ⊔ O Cx → D ≤ Cx →
      Odd (Nat.card D) → K ≤ normalizer (D : Set G) → D ≤ O Cx)
    (hMC : M ≤ Cx) (hM₀ : M₀ ≤ M)
    (h5 : ⁅O2 Cx, O2 Cx⁆ ⊔ O Cx = (M₀ ⊓ ⁅O2 Cx, O2 Cx⁆) ⊔ O Cx)
    (hcov : M₀ ≤ (H ⊓ M₀) ⊔ O M) : O H ⊓ Cx ≤ O Cx := by
  have hL : ⁅O2 Cx, O2 Cx⁆ ≤ (M₀ ⊓ ⁅O2 Cx, O2 Cx⁆) ⊔ O Cx :=
    (le_sup_left : _ ≤ ⁅O2 Cx, O2 Cx⁆ ⊔ O Cx).trans h5.le
  have hOM : O M ≤ O Cx :=
    hz _ _ (inf_le_right.trans (commutator_le_of_le (O2_le _) (O2_le _))) hL
      ((O_le M).trans hMC) (odd_card_O M) (inf_le_left.trans (hM₀.trans (le_normalizer_O M)))
  have hcov2 : ⁅O2 Cx, O2 Cx⁆ ≤ (H ⊓ M₀) ⊔ O Cx :=
    hL.trans (sup_le (inf_le_left.trans (hcov.trans (sup_le_sup_left hOM _))) le_sup_right)
  exact hz _ _ (inf_le_right.trans (hM₀.trans hMC)) hcov2 inf_le_right
    (odd_card_of_le inf_le_left (odd_card_O H))
    (le_trans (le_inf (inf_le_left.trans (le_normalizer_O H))
      (inf_le_right.trans ((hM₀.trans hMC).trans le_normalizer))) inf_normalizer_le_normalizer_inf)

omit [Finite G] in
theorem isKleinFour_map_cj {V : Subgroup G} (hV : IsKleinFour V) (g : G) :
    IsKleinFour (V.map (cj g)) := by
  let e : V ≃* V.map (cj g) := V.equivMapOfInjective (cj g) (cj_injective g)
  exact ⟨by rw [← Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

theorem isSimpleGroup_of_isL2OrA7' {L : Type*} [Group L] {qmin : ℕ} (hq : 5 ≤ qmin)
    (h : IsL2OrA7 L qmin) : IsSimpleGroup L := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, k, _, hp2, hpk, ⟨e⟩⟩
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  · have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hpk
      omega
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [GaloisField.card p k hk]; omega)
    exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance

theorem isL2PGL2OrA7OrV4_of_isL2OrA7 {L : Type*} [Group L] {qmin : ℕ} (hq : 5 ≤ qmin)
    (h : IsL2OrA7 L qmin) : IsL2PGL2OrA7OrV4 L := by
  left
  rcases h with h | ⟨p, k, hp, hp2, hpk, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, k, hp, hp2, hq.trans hpk, e⟩

theorem eq_bot_of_le_of_isSimpleGroup {X : Type*} [Group X] [Finite X] {L P N : Subgroup X}
    (hL : IsSimpleGroup L) (hPL : P ≤ L) (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (hNL : N ≤ L)
    (hLN : L ≤ normalizer (N : Set X)) (hN : Odd (Nat.card N)) : N = ⊥ := by
  have : (N.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLN
  rcases hL.eq_bot_or_eq_top_of_normal (N.subgroupOf L) with h | h
  · rwa [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hNL] at h
  · rw [subgroupOf_eq_top] at h
    have hNL' : N = L := le_antisymm hNL h
    have := inf_eq_bot_of_odd_of_isPGroup hN hP
    rw [hNL', inf_eq_right.mpr hPL] at this
    exact absurd this hP1

theorem bar_ne_bot {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) {z : G} (hz : z ∈ P)
    (hz2 : orderOf z = 2) : bar H P ≠ ⊥ := by
  intro h
  rw [bar_eq_bot_iff hPH] at h
  have h1 := inf_eq_bot_of_odd_of_isPGroup (odd_card_O H) hP
  rw [inf_eq_right.mpr h] at h1
  have hz1 : z = 1 := by
    rw [← mem_bot, ← h1]
    exact hz
  rw [hz1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

omit [Finite G] in
theorem map_cj_map_cj (g h : G) (K : Subgroup G) :
    (K.map (cj h)).map (cj g) = K.map (cj (g * h)) := by
  rw [map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, cj_apply, mul_inv_rev, mul_assoc]

end Basic

section Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

theorem mem_X {a : G} : a ∈ 𝔖.X A ↔ a ∈ A ∧ a ∈ 𝔖.S₁ := Iff.rfl

theorem mem_Y {a : G} : a ∈ 𝔖.Y A ↔ a ∈ A ∧ a ∈ 𝔖.S₂ := Iff.rfl

theorem S_eq : (𝔖.S : Subgroup G) = 𝔖.S₁ ⊔ 𝔖.S₂ := 𝔖.decomp.sup_eq.symm

theorem isPGroup_S₁ : IsPGroup 2 𝔖.S₁ := 𝔖.S.isPGroup'.to_le 𝔖.decomp.le_left

theorem isPGroup_S₂ : IsPGroup 2 𝔖.S₂ := 𝔖.S.isPGroup'.to_le 𝔖.decomp.le_right

theorem S₂_le_C_z₁ : 𝔖.S₂ ≤ C 𝔖.z₁ := fun _ hs =>
  mem_centralizer_singleton_iff.mpr (𝔖.decomp.comm 𝔖.hz₁.1 hs).symm

theorem S₁_le_C_z₂ : 𝔖.S₁ ≤ C 𝔖.z₂ := fun _ hs =>
  mem_centralizer_singleton_iff.mpr (𝔖.decomp.comm hs 𝔖.hz₂.1)

theorem S_le_C_z₁ : (𝔖.S : Subgroup G) ≤ C 𝔖.z₁ := by
  rw [S_eq]
  exact sup_le 𝔖.hz₁.2.2 (S₂_le_C_z₁ 𝔖)

theorem S_le_C_z₂ : (𝔖.S : Subgroup G) ≤ C 𝔖.z₂ := by
  rw [S_eq]
  exact sup_le (S₁_le_C_z₂ 𝔖) 𝔖.hz₂.2.2

theorem z₁z₂_mem : 𝔖.z₁ * 𝔖.z₂ ∈ 𝔖.S₁ ⊔ 𝔖.S₂ ∧ 𝔖.z₁ * 𝔖.z₂ ∉ 𝔖.S₁ ∧ 𝔖.z₁ * 𝔖.z₂ ∉ 𝔖.S₂ ∧
    orderOf (𝔖.z₁ * 𝔖.z₂) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₁, ho₁, -⟩ := 𝔖.hz₁
  obtain ⟨h₂, ho₂, -⟩ := 𝔖.hz₂
  have hne : ∀ {z : G}, z ∈ 𝔖.S₁ → z ∈ 𝔖.S₂ → orderOf z = 2 → False := by
    intro z hz₁ hz₂ hz
    have : z ∈ 𝔖.S₁ ⊓ 𝔖.S₂ := ⟨hz₁, hz₂⟩
    rw [𝔖.decomp.inf_eq, mem_bot] at this
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hn₁ : 𝔖.z₁ * 𝔖.z₂ ∉ 𝔖.S₁ := fun h =>
    hne (by simpa using 𝔖.S₁.mul_mem (𝔖.S₁.inv_mem h₁) h) h₂ ho₂
  have hn₂ : 𝔖.z₁ * 𝔖.z₂ ∉ 𝔖.S₂ := fun h =>
    hne h₁ (by simpa using 𝔖.S₂.mul_mem h (𝔖.S₂.inv_mem h₂)) ho₁
  refine ⟨mul_mem_sup h₁ h₂, hn₁, hn₂, orderOf_eq_prime ?_ fun h => hn₁ (h ▸ one_mem _)⟩
  have hs : ∀ {z : G}, orderOf z = 2 → z * z = 1 := fun hz => by
    rw [← pow_two, ← hz, pow_orderOf_eq_one]
  rw [pow_two]
  exact (𝔖.decomp.mul_self_iff h₁ h₂).mpr ⟨hs ho₁, hs ho₂⟩

variable {𝔖}

theorem X_le_A : 𝔖.X A ≤ A := inf_le_left

theorem X_le_S₁ : 𝔖.X A ≤ 𝔖.S₁ := inf_le_right

theorem Y_le_A : 𝔖.Y A ≤ A := inf_le_left

theorem Y_le_S₂ : 𝔖.Y A ≤ 𝔖.S₂ := inf_le_right

theorem M_le_C {x : G} (hx : x ∈ 𝔖.X A) : 𝔖.M A ≤ C x :=
  centralizer_le (Set.singleton_subset_iff.mpr hx)

theorem N_le_C {y : G} (hy : y ∈ 𝔖.Y A) : 𝔖.N A ≤ C y :=
  centralizer_le (Set.singleton_subset_iff.mpr hy)

theorem M₀_le_M : 𝔖.M₀ A ≤ 𝔖.M A := sup_le (commutator_le_of_le (O2_le _) (O2_le _)) (O_le _)

theorem N₀_le_N : 𝔖.N₀ A ≤ 𝔖.N A := sup_le (commutator_le_of_le (O2_le _) (O2_le _)) (O_le _)

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

omit [Finite G] in
include hA in
theorem orderOf_eq_two {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact isElemAbelian_two_iff.1 hA.1 a ha) ha1

include hAS hA in
theorem isKleinFour_X : IsKleinFour (𝔖.X A) := (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.1

include hAS hA in
theorem isKleinFour_Y : IsKleinFour (𝔖.Y A) := (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.2.1

include hAS hA in
theorem isConj_z₁z₂ {a : G} (ha : a ∈ A) (haX : a ∉ 𝔖.X A) (haY : a ∉ 𝔖.Y A) :
    IsConj a (𝔖.z₁ * 𝔖.z₂) := by
  obtain ⟨hm, h1, h2, ho⟩ := z₁z₂_mem 𝔖
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact haX (one_mem _)
  exact 𝔖.fusion.conj₃ a (S_eq 𝔖 ▸ hAS ha) _ hm (fun h => haX ((mem_X 𝔖).mpr ⟨ha, h⟩))
    (fun h => haY ((mem_Y 𝔖).mpr ⟨ha, h⟩)) h1 h2 (orderOf_eq_two hA ha ha1) ho

include hA in
theorem exists_conj_align {x z : G} (hxA : x ∈ A) (hxz : IsConj x z)
    (hSz : (𝔖.S : Subgroup G) ≤ C z) :
    ∃ g : G, g * x * g⁻¹ = z ∧ (𝔖.X A).map (cj g) ≤ 𝔖.S₁ ∧ (𝔖.Y A).map (cj g) ≤ 𝔖.S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hxz
  have hAx : A ≤ C x := fun a ha => mem_centralizer_singleton_iff.mpr
    (comm_of_mul_self (isElemAbelian_two_iff.1 hA.1) ha hxA)
  have hAc : A.map (cj c) ≤ C z := by
    rw [← hc, ← map_cj_C]
    exact map_mono hAx
  have hA2 : IsPGroup 2 (A.map (cj c)) :=
    IsPGroup.of_card (n := 4) (by rw [card_map_cj, hA.2]; norm_num)
  obtain ⟨d, hd, hdA⟩ := exists_mem_map_cj_le 𝔖.S hSz hAc hA2
  rw [map_cj_map_cj] at hdA
  have hT : ∀ T : Subgroup G, T ≤ A → T.map (cj (d * c)) ≤ 𝔖.S := fun T hT =>
    (map_mono hT).trans hdA
  have hinv : ∀ {T : Subgroup G} {R : Subgroup G}, T ≤ A →
      (∀ t ∈ T, orderOf t = 2 → (d * c) * t * (d * c)⁻¹ ∈ R) → T.map (cj (d * c)) ≤ R := by
    intro T R hTA h
    rintro _ ⟨t, ht, rfl⟩
    rw [cj_apply]
    by_cases ht1 : t = 1
    · rw [ht1, mul_one, mul_inv_cancel]
      exact one_mem _
    · exact h t ht (orderOf_eq_two hA (hTA ht) ht1)
  refine ⟨d * c, ?_, hinv X_le_A ?_, hinv Y_le_A ?_⟩
  · rw [show d * c * x * (d * c)⁻¹ = d * (c * x * c⁻¹) * d⁻¹ by group, hc,
      mem_centralizer_singleton_iff.mp hd, mul_inv_cancel_right]
  · exact (𝔖.toSec3Setting.lemma_3_12 𝔖.fusion (𝔖.X A) (d * c) (hT _ X_le_A)).1 X_le_S₁
  · exact (𝔖.toSec3Setting.lemma_3_12 𝔖.fusion (𝔖.Y A) (d * c) (hT _ Y_le_A)).2 Y_le_S₂

end Setting

end G4c

namespace Sec4Setting

open G4c

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

include hAS hA in
theorem lemma_4_10_of (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y))) :
    (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
    (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)) := by
  refine ⟨fun x hx _ a ha haY => ?_, fun y hy _ a ha haX => ?_⟩
  · by_cases haX : a ∈ 𝔖.X A
    · have ha1 : a ≠ 1 := by
        rintro rfl
        exact haY (one_mem _)
      exact le_O_of_sup_eq (h47.2.2.2.2.1 a haX ha1) inf_le_right
        (odd_card_of_le inf_le_left (odd_card_O _)) inf_le_left (odd_card_O _)
        (inf_le_left.trans ((O2_le _).trans ((M_le_C hx).trans (le_normalizer_O _))))
    · exact le_O_C_of_isConj (isConj_z₁z₂ hAS hA ha haX haY) h317 inf_le_right
        (odd_card_of_le inf_le_left (odd_card_O _))
  · by_cases haY : a ∈ 𝔖.Y A
    · have ha1 : a ≠ 1 := by
        rintro rfl
        exact haX (one_mem _)
      exact le_O_of_sup_eq (h48.2.2.2.2.1 a haY ha1) inf_le_right
        (odd_card_of_le inf_le_left (odd_card_O _)) inf_le_left (odd_card_O _)
        (inf_le_left.trans ((O2_le _).trans ((N_le_C hy).trans (le_normalizer_O _))))
    · exact le_O_C_of_isConj (isConj_z₁z₂ hAS hA ha haX haY) h317 inf_le_right
        (odd_card_of_le inf_le_left (odd_card_O _))

include hAS hA in
theorem lemma_4_11_of
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
        V ≤ normalizer (K : Set X) → IsCyclic K) :
    (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
    (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)) := by
  obtain ⟨⟨H₁, -, hRF₁', hFR₁, hTL₁, hL₁⟩, ⟨K₁, -, hRF₂', hFR₂, hTL₂, hL₂⟩⟩ := h315
  refine ⟨fun x hx hx1 D hDx hD hAD => ?_, fun y hy hy1 D hDy hD hAD => ?_⟩
  · obtain ⟨g, hg, hXg, hYg⟩ := exists_conj_align hA ((mem_X 𝔖).mp hx).1
      (𝔖.fusion.conj₁ x ((mem_X 𝔖).mp hx).2 _ 𝔖.hz₁.1
        (orderOf_eq_two hA ((mem_X 𝔖).mp hx).1 hx1) 𝔖.hz₁.2.1) (S_le_C_z₁ 𝔖)
    have hCx : (C x).map (cj g) = C 𝔖.z₁ := by rw [map_cj_C, hg]
    have hDg : D.map (cj g) ≤ C 𝔖.z₁ := hCx ▸ map_mono hDx
    have hDo : Odd (Nat.card (D.map (cj g))) := by rwa [card_map_cj]
    have h1 := commutator_le_O_of_le_R (isPGroup_S₁ 𝔖) hRF₁' hFR₁ hXg 𝔖.hz₁.2.2 hDg hDo
      (map_cj_le_normalizer (X_le_A.trans hAD))
    have h2 := commutator_commutator_le_O hRF₁' hFR₁ hTL₁ hYg (S₂_le_C_z₁ 𝔖) hDg hDo
      (map_cj_le_normalizer (Y_le_A.trans hAD)) fun K hK hKo hYK =>
        hP2b5 (isL2PGL2OrA7OrV4_of_isL2OrA7 (by norm_num) hL₁)
          (isKleinFour_bar (hYg.trans (S₂_le_C_z₁ 𝔖)) (isKleinFour_map_cj (isKleinFour_Y hAS hA) g))
          ((bar_mono hYg).trans hTL₁) hK hKo hYK
    refine le_O_C_of_map_le hg ?_
    simp only [map_cj_sup, map_cj_commutator]
    exact sup_le h1 h2
  · obtain ⟨g, hg, hXg, hYg⟩ := exists_conj_align hA ((mem_Y 𝔖).mp hy).1
      (𝔖.fusion.conj₂ y ((mem_Y 𝔖).mp hy).2 _ 𝔖.hz₂.1
        (orderOf_eq_two hA ((mem_Y 𝔖).mp hy).1 hy1) 𝔖.hz₂.2.1) (S_le_C_z₂ 𝔖)
    have hCy : (C y).map (cj g) = C 𝔖.z₂ := by rw [map_cj_C, hg]
    have hDg : D.map (cj g) ≤ C 𝔖.z₂ := hCy ▸ map_mono hDy
    have hDo : Odd (Nat.card (D.map (cj g))) := by rwa [card_map_cj]
    have h1 := commutator_le_O_of_le_R (isPGroup_S₂ 𝔖) hRF₂' hFR₂ hYg 𝔖.hz₂.2.2 hDg hDo
      (map_cj_le_normalizer (Y_le_A.trans hAD))
    have h2 := commutator_commutator_le_O hRF₂' hFR₂ hTL₂ hXg (S₁_le_C_z₂ 𝔖) hDg hDo
      (map_cj_le_normalizer (X_le_A.trans hAD)) fun K hK hKo hXK => by
        rcases hL₂ with hL₂ | hL₂
        · exact hP2b5 (isL2PGL2OrA7OrV4_of_isL2OrA7 le_rfl hL₂)
            (isKleinFour_bar (hXg.trans (S₁_le_C_z₂ 𝔖))
              (isKleinFour_map_cj (isKleinFour_X hAS hA) g))
            ((bar_mono hXg).trans hTL₂) hK hKo hXK
        · have hbot := inf_eq_bot_of_odd_of_isPGroup hKo
            (isPGroup_bar (H := C 𝔖.z₂) (isPGroup_S₁ 𝔖))
          rw [inf_eq_left.mpr (hK.trans hL₂.le)] at hbot
          rw [hbot]
          infer_instance
    refine le_O_C_of_map_le hg ?_
    simp only [map_cj_sup, map_cj_commutator]
    exact sup_le h1 h2

include hA in
theorem lemma_4_13_of
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (H : Subgroup G) (_hH : H ≠ ⊤) :
    (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
    (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)) := by
  obtain ⟨⟨H₁, hRF₁, hRF₁', hFR₁, hTL₁, hL₁⟩, ⟨K₁, hRF₂, hRF₂', hFR₂, hTL₂, hL₂⟩⟩ := h315
  have hz₁ : ∀ K D : Subgroup G, K ≤ C 𝔖.z₁ → ⁅O2 (C 𝔖.z₁), O2 (C 𝔖.z₁)⁆ ≤ K ⊔ O (C 𝔖.z₁) →
      D ≤ C 𝔖.z₁ → Odd (Nat.card D) → K ≤ normalizer (D : Set G) → D ≤ O (C 𝔖.z₁) :=
    fun K D => le_O_of_covers 𝔖.S (S_eq 𝔖) (S_le_C_z₁ 𝔖) (isPGroup_S₁ 𝔖) hRF₁ hRF₁' hFR₁ hTL₁
      (fun N hN hLN hNo => eq_bot_of_le_of_isSimpleGroup
        (isSimpleGroup_of_isL2OrA7' (by norm_num) hL₁) hTL₁ (isPGroup_bar (isPGroup_S₂ 𝔖))
        (bar_ne_bot (S₂_le_C_z₁ 𝔖) (isPGroup_S₂ 𝔖) 𝔖.hz₂.1 𝔖.hz₂.2.1) hN hLN hNo)
      (K := K) (D := D)
  have hz₂ : ∀ K D : Subgroup G, K ≤ C 𝔖.z₂ → ⁅O2 (C 𝔖.z₂), O2 (C 𝔖.z₂)⁆ ≤ K ⊔ O (C 𝔖.z₂) →
      D ≤ C 𝔖.z₂ → Odd (Nat.card D) → K ≤ normalizer (D : Set G) → D ≤ O (C 𝔖.z₂) := by
    refine fun K D => le_O_of_covers 𝔖.S ((S_eq 𝔖).trans (sup_comm _ _)) (S_le_C_z₂ 𝔖)
      (isPGroup_S₂ 𝔖) hRF₂ hRF₂' hFR₂ hTL₂ (fun N hN hLN hNo => ?_) (K := K) (D := D)
    rcases hL₂ with hL₂ | hL₂
    · exact eq_bot_of_le_of_isSimpleGroup (isSimpleGroup_of_isL2OrA7' le_rfl hL₂) hTL₂
        (isPGroup_bar (isPGroup_S₁ 𝔖))
        (bar_ne_bot (S₁_le_C_z₂ 𝔖) (isPGroup_S₁ 𝔖) 𝔖.hz₁.1 𝔖.hz₁.2.1) hN hLN hNo
    · have hbot := inf_eq_bot_of_odd_of_isPGroup hNo
        (isPGroup_bar (H := C 𝔖.z₂) (isPGroup_S₁ 𝔖))
      rwa [inf_eq_left.mpr (hN.trans hL₂.le)] at hbot
  refine ⟨fun hcov x hx hx1 _ => ?_, fun hcov y hy hy1 _ => ?_⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp (𝔖.fusion.conj₁ x ((mem_X 𝔖).mp hx).2 _ 𝔖.hz₁.1
      (orderOf_eq_two hA ((mem_X 𝔖).mp hx).1 hx1) 𝔖.hz₁.2.1)
    exact inf_le_O_of_covers (fun K D => cover_of_conj hg hz₁ (K := K) (D := D)) (M_le_C hx)
      M₀_le_M (h47.2.2.2.2.2 x hx hx1) hcov
  · obtain ⟨g, hg⟩ := isConj_iff.mp (𝔖.fusion.conj₂ y ((mem_Y 𝔖).mp hy).2 _ 𝔖.hz₂.1
      (orderOf_eq_two hA ((mem_Y 𝔖).mp hy).1 hy1) 𝔖.hz₂.2.1)
    exact inf_le_O_of_covers (fun K D => cover_of_conj hg hz₂ (K := K) (D := D)) (N_le_C hy)
      N₀_le_N (h48.2.2.2.2.2 y hy hy1) hcov

end Sec4Setting

end CFSG.GH72
