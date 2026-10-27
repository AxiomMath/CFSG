module

public import CFSG.GH74.GLS.LU.Local.Assembly
public import CFSG.GH74.GLS.LU.Local.A3T

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
  CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

theorem exists_mulEquiv_SL2 {G : Type} [Group G] {X : Subgroup G} {q : ℕ}
    (h : HasSL2Model ↥X (fun r => r = q)) (K : Type) [Field K] [Finite K] (hK : Nat.card K = q) :
    Nonempty (SL(2, K) ≃* ↥X) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card K = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF]
  let φ : K ≃+* F := FiniteField.ringEquivOfCardEq hcard
  exact ⟨((CFSG.ClassicalModels.specialLinearFieldEquiv φ (Fin 2)).trans
    (specialLinearGroupEquivStatedSL 2 F)).trans e.symm⟩

theorem exists_mulEquiv_cj {G : Type} [Group G] {X : Subgroup G} {K : Type} [Field K]
    (h : Nonempty (SL(2, K) ≃* ↥X)) (g : G) : Nonempty (SL(2, K) ≃* ↥(cj X g)) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans ((MulAut.conj g⁻¹).subgroupMap X)⟩

theorem isCentralInvolutionIn_cj {G : Type} [Group G] {X : Subgroup G} {z : G}
    (hz : IsCentralInvolutionIn z X) (g : G) : IsCentralInvolutionIn (g⁻¹ * z * g) (cj X g) := by
  obtain ⟨hzX, hz2, hzc⟩ := hz
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_cj]; simpa [mul_assoc] using hzX
  · have h1 := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective z
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    rw [h1]; exact hz2
  · intro x hx
    rw [mem_cj] at hx
    have := hzc _ hx
    calc x * (g⁻¹ * z * g) = g⁻¹ * ((g * x * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * z * g) * x := by group

@[expose] def A3CoreLin (G : Type) [Group G] (p f : ℕ) (z : G) (K₁ K₂ : Subgroup G) (u : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (u' h : G) (L : Subgroup G),
    Nat.card K = p ^ f ∧ (u' = u ∨ u' = u * z) ∧ h⁻¹ * z * h = u' ∧ (L = cj K₁ h ∨ L = cj K₂ h) ∧
    (∃ α : SL(3, K) →* G, α.ker ≤ Subgroup.center SL(3, K) ∧ α.range = K₁ ⊔ L) ∧
    (∃ α : SL(3, K) →* G, α.ker ≤ Subgroup.center SL(3, K) ∧ α.range = L ⊔ K₂)

@[expose] def A3CoreUni (G : Type) [Group G] (p f : ℕ) (z : G) (K₁ K₂ : Subgroup G) (u : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F) (_ : Finite F)
    (u' h : G) (L : Subgroup G),
    Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ (u' = u ∨ u' = u * z) ∧ h⁻¹ * z * h = u' ∧
    (L = cj K₁ h ∨ L = cj K₂ h) ∧
    (∃ α : ↥(StatedSU 3 (p ^ f) K) →* G, α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) K) ∧
      α.range = K₁ ⊔ L) ∧
    (∃ α : ↥(StatedSU 3 (p ^ f) K) →* G, α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) K) ∧
      α.range = L ⊔ K₂)

@[expose] def A3Hyp (G : Type) [Group G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G)
    (t u : G) : Prop :=
  LUComps G (p ^ f) z K₁ K₂ ∧ LUSyl G z S K₁ K₂ t u ∧ MaxOverCentralizerPSp4 z p f ∧
    LU61 G z S K₁ K₂ t u ∧
    ∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
      ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y

@[expose] def LUA3Lin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    p ^ f ≠ 5 → ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
      A3Hyp G p f z S K₁ K₂ t u → LUEps G (p ^ f) 1 z K₁ u → A3CoreLin G p f z K₁ K₂ u

@[expose] def LUA3Uni : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
      A3Hyp G p f z S K₁ K₂ t u → LUEps G (p ^ f) (-1) z K₁ u → A3CoreUni G p f z K₁ K₂ u

@[expose] def LUA3Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    p ^ f = 5 → ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
      A3Hyp G p f z S K₁ K₂ t u → LUEps G (p ^ f) 1 z K₁ u → A3CoreLin G p f z K₁ K₂ u

theorem a3_sl2 {G : Type} [Group G] {q : ℕ} {z : G} {K₁ K₂ : Subgroup G} (hc : LUComps G q z K₁ K₂)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q) {h : G} {L : Subgroup G}
    (hL : L = cj K₁ h ∨ L = cj K₂ h) :
    ∀ i : Fin 3, Nonempty (SL(2, K) ≃* ↥(![K₁, L, K₂] i)) := by
  intro i
  fin_cases i
  · exact exists_mulEquiv_SL2 hc.sl₁ K hK
  · rcases hL with rfl | rfl
    · exact exists_mulEquiv_cj (exists_mulEquiv_SL2 hc.sl₁ K hK) h
    · exact exists_mulEquiv_cj (exists_mulEquiv_SL2 hc.sl₂ K hK) h
  · exact exists_mulEquiv_SL2 hc.sl₂ K hK

theorem a3_common {G : Type} [Group G] [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
    {t u : G} (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {u' h : G} {L : Subgroup G}
    (hu' : u' = u ∨ u' = u * z) (hh : h⁻¹ * z * h = u') (hL : L = cj K₁ h ∨ L = cj K₂ h) :
    IsCentralInvolutionIn z K₁ ∧ IsCentralInvolutionIn z K₂ ∧ IsCentralInvolutionIn u' L ∧ z ≠ u' ∧
      z * u' = u' * z := by
  have hz1 : IsCentralInvolutionIn z K₁ := ⟨hc.z_mem₁, hs.z_inv, fun k hk => hc.cz₁ hk⟩
  have hz2 : IsCentralInvolutionIn z K₂ := ⟨hc.z_mem₂, hs.z_inv, fun k hk => hc.cz₂ hk⟩
  have hzu : u * z = z * u := hs.comm_z hs.u_mem
  refine ⟨hz1, hz2, ?_, ?_, ?_⟩
  · rw [← hh]
    rcases hL with rfl | rfl
    · exact isCentralInvolutionIn_cj hz1 h
    · exact isCentralInvolutionIn_cj hz2 h
  · rcases hu' with rfl | rfl
    · exact hs.u_ne.symm
    · intro hzz
      have h1 : u = 1 := by
        have : u * z = 1 * z := by rw [one_mul]; exact hzz.symm
        exact mul_right_cancel this
      have h2 := hs.u_ord
      rw [h1, orderOf_one] at h2
      omega
  · rcases hu' with rfl | rfl
    · exact hzu.symm
    · calc z * (u * z) = (z * u) * z := by group
        _ = (u * z) * z := by rw [hzu]

theorem luA3Leaf_of_cores (hLin : LUA3Lin) (hUni : LUA3Uni) (hFive : LUA3Five) : LUA3Leaf := by
  intro G _ _ hG p f hp hp2 hq z S K₁ K₂ t u hc hs h6A h61 hgen
  have hH : A3Hyp G p f z S K₁ K₂ t u := ⟨hc, hs, h6A, h61, hgen⟩
  constructor
  · intro he
    have hcore : A3CoreLin G p f z K₁ K₂ u := by
      by_cases h5 : p ^ f = 5
      · exact hFive G hG p f hp hp2 hq h5 z S K₁ K₂ t u hH he
      · exact hLin G hG p f hp hp2 hq h5 z S K₁ K₂ t u hH he
    obtain ⟨K, hK, hKf, u', h, L, hKc, hu', hh, hLc, hα, hβ⟩ := hcore
    obtain ⟨hz1, hz2, hu'L, hzu, hcomm⟩ := a3_common hc hs hu' hh hLc
    have hN : IsLinearA3Neighborhood K z u' ![K₁, L, K₂] :=
      ⟨a3_sl2 hc K hKc hLc, hz1, hz2, hu'L, hzu, hcomm, hc.comm, hα, hβ⟩
    have := he.A0_cyc
    obtain ⟨T, hT, hTp, hTc⟩ := exists_T_of_nbhd_lin hp hp2 (by omega) hKc hc hs hN
    refine ⟨K, hK, hKf, u', ![K₁, L, K₂], h, hKc, hu', rfl, rfl, hh, hLc, hN, T, ?_, hTp, hTc⟩
    rw [iSup_vec_three]; exact hT
  · intro he
    have hcore := hUni G hG p f hp hp2 hq z S K₁ K₂ t u hH he
    obtain ⟨K, hK, hKf, hKp, F, hF, hFf, u', h, L, hKc, hFc, hu', hh, hLc, hα, hβ⟩ := hcore
    obtain ⟨hz1, hz2, hu'L, hzu, hcomm⟩ := a3_common hc hs hu' hh hLc
    have hN : IsUnitaryA3Neighborhood (p ^ f) K F z u' ![K₁, L, K₂] :=
      ⟨a3_sl2 hc F hFc hLc, hz1, hz2, hu'L, hzu, hcomm, hc.comm, hα, hβ⟩
    have := he.A0_cyc
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨T, hT, hTp, hTc⟩ := exists_T_of_nbhd_uni hp2 hq hKc hFc hc hs hN
    refine ⟨K, hK, hKf, hKp, F, hF, hFf, u', ![K₁, L, K₂], h, hKc, hFc, hu', rfl, rfl, hh, hLc, hN, T, ?_,
      hTp, hTc⟩
    rw [iSup_vec_three]; exact hT

theorem luLocalLeaf_of_cores
    (hLin : LUA3Lin) (hUni : LUA3Uni) (hFive : LUA3Five) : LULocalLeaf :=
  luLocalLeaf_of_A3 (luA3Leaf_of_cores hLin hUni hFive)

theorem luNeighborhood_of_cores
    (hM : LUModelLeaf) (hLin : LUA3Lin) (hUni : LUA3Uni)
    (hFive : LUA3Five) (h6A : LUMax6A) : LUNeighborhood :=
  luNeighborhood_of_A3 hM (luA3Leaf_of_cores hLin hUni hFive) h6A

end CFSG.GH74.GLS.LU.Local
