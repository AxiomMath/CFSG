module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo

section Transfer

variable {G : Type} [Group G] {Y P : Subgroup G} {K : Type} [Field K]
  {π : adjointGroup .G2 K →* ↥Y}

@[expose] noncomputable def g2Transfer (hπ : Function.Bijective π) :
    ↥(Subgroup.normalizer (Y : Set G)) →* MulAut (adjointGroup .G2 K) :=
  (MulAut.congr (MulEquiv.ofBijective π hπ).symm).toMonoidHom.comp Y.normalizerMonoidHom

theorem apply_g2Transfer (hπ : Function.Bijective π)
    (β : ↥(Subgroup.normalizer (Y : Set G))) (c : adjointGroup .G2 K) :
    π (g2Transfer hπ β c) = Y.normalizerMonoidHom β (π c) := by
  set ψ : adjointGroup .G2 K ≃* ↥Y := MulEquiv.ofBijective π hπ
  change ψ (ψ.symm (Y.normalizerMonoidHom β (ψ c))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem g2Transfer_mem (hπ : Function.Bijective π) {β : ↥(Subgroup.normalizer (Y : Set G))}
    (hβ : (β : G) ∈ Subgroup.normalizer (P : Set G)) {a : adjointGroup .G2 K}
    (ha : a ∈ (P.subgroupOf Y).comap π) : g2Transfer hπ β a ∈ (P.subgroupOf Y).comap π := by
  rw [Subgroup.mem_comap, apply_g2Transfer, Subgroup.mem_subgroupOf,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp hβ _).mp ha

theorem centralizes_of_g2Transfer_eq_one (hπ : Function.Bijective π)
    {β : ↥(Subgroup.normalizer (Y : Set G))} (hβ : g2Transfer hπ β = 1) :
    ∀ y ∈ Y, (β : G) * y = y * β := by
  intro y hy
  have hγ : Y.normalizerMonoidHom β = 1 := by
    apply (MulAut.congr (MulEquiv.ofBijective π hπ).symm).injective
    rw [map_one]
    exact hβ
  have h3 := congrArg (fun γ : MulAut ↥Y => ((γ ⟨y, hy⟩ : ↥Y) : G)) hγ
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
  calc (β : G) * y = (β : G) * y * (β : G)⁻¹ * (β : G) := by group
    _ = y * β := by rw [h3]

end Transfer


section TransferWCent

variable {G : Type} [Group G] [Finite G] {Y P : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {π : adjointGroup .G2 K →* ↥Y}

theorem g2Transfer_mul_inv_mem_pCoreOf (hπ : Function.Bijective π) (hPY : P ≤ Y)
    (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ (P.subgroupOf Y).comap π)
    {i : Fin (Tag.rank .G2)} (hI : negIndices (g2Datum K) ((P.subgroupOf Y).comap π) = {i})
    (h4 : 4 ≤ Nat.card K) {β : ↥(Subgroup.normalizer (Y : Set G))}
    (hβ : (β : G) ∈ Subgroup.normalizer (P : Set G)) (hWβ : WCent P β)
    {s : adjointGroup .G2 K} (hs : s ∈ rankOne (g2Datum K).rootGroup i) :
    g2Transfer hπ β s * s⁻¹ ∈ pCoreOf 2 ((P.subgroupOf Y).comap π) := by
  have hsA : s ∈ (P.subgroupOf Y).comap π :=
    rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl) hs
  have hmem := toHat_rankOne_mem_wSup hπ hPY hBA hI h4 hs hsA
  have hw := hWβ _ (toP hπ hPY ⟨s, hsA⟩).2 hmem
  have hsA' : g2Transfer hπ β s * s⁻¹ ∈ (P.subgroupOf Y).comap π :=
    Subgroup.mul_mem _ (g2Transfer_mem hπ hβ hsA) (Subgroup.inv_mem _ hsA)
  refine mem_pCoreOf_of_toP hπ hPY (a := ⟨_, hsA'⟩) ?_
  have hval : ((toP hπ hPY ⟨_, hsA'⟩ : ↥P) : G) =
      (β : G) * ((toP hπ hPY ⟨s, hsA⟩ : ↥P) : G) * (β : G)⁻¹ *
        ((toP hπ hPY ⟨s, hsA⟩ : ↥P) : G)⁻¹ := by
    rw [coe_toP, coe_toP, map_mul, map_inv, apply_g2Transfer, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
  obtain ⟨o, ho, hoe⟩ := hw
  have : toP hπ hPY ⟨_, hsA'⟩ = o := Subtype.ext (by rw [hval]; exact hoe.symm)
  rw [this]
  exact ho

end TransferWCent

theorem exists_g2_cover (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G] [Finite G]
    {Y P : Subgroup G} (hY : Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥)
    (hF : IsLieOf IdxG2 (↥Y ⧸ Subgroup.center ↥Y)) (hpar : IsParabolicTwo Y P) (hne : P ≠ Y)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) :
    ∃ (f : ℕ) (_ : 2 ≤ f) (π : adjointGroup .G2 (GaloisField 2 f) →* ↥Y),
      Function.Bijective π ∧
      borel (g2Datum (GaloisField 2 f)) (torus (τ := .G2) (GaloisField 2 f)) ≤
        (P.subgroupOf Y).comap π ∧
      ∃ i : Fin (Tag.rank .G2),
        negIndices (g2Datum (GaloisField 2 f)) ((P.subgroupOf Y).comap π) = {i} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := Lin.odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2_of_isLieOf hGA hY hodd hF
  obtain ⟨π, hQ, hBA, i, hI⟩ := exists_node_of_parabolic e hpar hne hna
  refine ⟨f, hf, π, ⟨?_, hQ.surj⟩, hBA, i, hI⟩
  rw [injective_iff_map_eq_one]
  intro z hz
  have hc := hQ.ker_central z hz
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.G2) (K := GaloisField 2 f),
    Subgroup.mem_bot] at hc
  exact hc

theorem exists_g2_model (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G] [Finite G]
    {Y P : Subgroup G} (hY : Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥)
    (hF : IsLieOf IdxG2 (↥Y ⧸ Subgroup.center ↥Y)) (hpar : IsParabolicTwo Y P) (hne : P ≠ Y)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) :
    ∃ (f : ℕ) (_ : 2 ≤ f) (A : Subgroup (adjointGroup .G2 (GaloisField 2 f)))
      (i : Fin (Tag.rank .G2))
      (aut : ↥(Subgroup.normalizer (Y : Set G)) →* MulAut (adjointGroup .G2 (GaloisField 2 f))),
      borel (g2Datum (GaloisField 2 f)) (torus (τ := .G2) (GaloisField 2 f)) ≤ A ∧
      negIndices (g2Datum (GaloisField 2 f)) A = {i} ∧
      (∀ β : ↥(Subgroup.normalizer (Y : Set G)), (β : G) ∈ Subgroup.normalizer (P : Set G) →
        ∀ a ∈ A, aut β a ∈ A) ∧
      (∀ β : ↥(Subgroup.normalizer (Y : Set G)), (β : G) ∈ Subgroup.normalizer (P : Set G) →
        WCent P β → ∀ s ∈ rankOne (g2Datum (GaloisField 2 f)).rootGroup i,
          aut β s * s⁻¹ ∈ pCoreOf 2 A) ∧
      (∀ β : ↥(Subgroup.normalizer (Y : Set G)), aut β = 1 → ∀ y ∈ Y, (β : G) * y = y * β) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, π, hπ, hBA, i, hI⟩ := exists_g2_cover hGA hY h2 hF hpar hne hna
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact ⟨f, hf, _, i, g2Transfer hπ, hBA, hI, fun β hβ a ha => g2Transfer_mem hπ hβ ha,
    fun β hβ hWβ s hs => g2Transfer_mul_inv_mem_pCoreOf hπ hpar.1 hBA hI h4 hβ hWβ hs,
    fun β hβ => centralizes_of_g2Transfer_eq_one hπ hβ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo
