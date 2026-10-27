module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415SimpleInputs
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PN

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem orderOf_z₁F : orderOf (betaBar z₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({z₁} : Set X)))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine orderOf_mk_eq_two hodd ?_
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime hD.fd.sq_z₁ hD.z₁_ne_one

theorem list_of_alpha [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (h34 : Harris81Lemma34Input) (hin : Harris36SimpleInput)
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    (hM : IsComponent (layer (MBar z₁))) (hEs : IsSimpleGroup ↥(layer (MBar z₁)))
    (hF : IsOfType (HarrisF p) ↥(layer (MBar z₁)))
    (hlt : barOf (centralizer {z₁}) K₂ < layer (MBar z₁)) :
    Nonempty (↥(layer (MBar z₁)) ≃* Blueprint.NativeSporadic.J2) ∨
      Nonempty (↥(layer (MBar z₁)) ≃* Blueprint.NativeSporadic.J3) ∨
      Blueprint.LieModel ↥(layer (MBar z₁)) .PSL 3 2 2 ∨
      Blueprint.LieModel ↥(layer (MBar z₁)) .PSL 3 p (f / 2) ∨
      Blueprint.LieModel ↥(layer (MBar z₁)) .PSU 3 p (f / 2) ∨
      Blueprint.LieModel ↥(layer (MBar z₁)) .PSL 2 p (2 * (f / 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hαE, hKα⟩ := hD.lieModel_layerIn_alpha hnab hK hSch hFC hKC h34 hnβ hM hEs hF hlt
  have hq : IsQuasisimple ↥(layer (MBar z₁)) := hM.1
  have hEnab : ∃ a b : ↥(layer (MBar z₁)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hZ : center ↥(layer (MBar z₁)) = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hEnab).2
  let e : ↥(layer (MBar z₁)) ⧸ center ↥(layer (MBar z₁)) ≃* ↥(layer (MBar z₁)) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have h47 : ∀ k : ℕ, 1 ≤ k → ¬ Blueprint.LieModel ↥(layer (MBar z₁)) .PSL 4 p k ∧
      ¬ Blueprint.LieModel ↥(layer (MBar z₁)) .PSU 4 p k := by
    intro k hk
    obtain ⟨h1, h2⟩ := hD.not_lieModel_L4U4 hnβ hM k hk
    exact ⟨fun h => h1 (GSThmB.OddQuot.lieModel_of_equiv e.symm h),
      fun h => h2 (GSThmB.OddQuot.lieModel_of_equiv e.symm h)⟩
  have hα2 : (QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (QuotientGroup.mk ⟨α, hD.alpha_mem_F⟩ : MBar z₁)
    rwa [hD.orderOf_alphaF] at h1
  have hz₁2 : betaBar z₁ ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (betaBar z₁)
    rwa [hD.orderOf_z₁F] at h1
  have hz₁1 : betaBar z₁ ≠ 1 := by
    intro h1
    have h2 := hD.orderOf_z₁F
    rw [h1, orderOf_one] at h2
    norm_num at h2
  exact (HarrisEnd.list_of_simple hin hα2 hαE (betaBar_mem_center z₁) hz₁2 hz₁1
    hD.hs.prime_p hD.hs.p_ne_two hD.hs.one_le_half hD.hs.sixteen_dvd hF h47 hKα
    (fun _ hP hP2 => hD.exists_closure_four_alphaF hP hP2)).2

theorem beta_facts {M : Subgroup (MBar z₁)} (hM : IsComponent M) (hMeq : layer (MBar z₁) = M)
    (hlt : barOf (centralizer {z₁}) K₂ < M)
    (hKpc : IsPComponent 2 ((barOf (centralizer {z₁}) K₂).subgroupOf (M ⊓ centralizer
      {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁)})))
    (hsyl : IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) M)
    (hcard : Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) ≤
      (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁} ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).relIndex
        (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) *
      Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M ⊓
        centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
          hD.beta_mem_F⟩ : MBar z₁)}))
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁) :
    orderOf (MulAut.conjNormal (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
        hD.beta_mem_F⟩ : MBar z₁) : MulAut ↥(layer (MBar z₁))) = 2 ∧
      IsTwoComponentIn ((barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁)))
        (fixedPoints (MulAut.conjNormal (QuotientGroup.mk
          ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁) :
            MulAut ↥(layer (MBar z₁)))) ∧
      Blueprint.LieModel
        (↥((barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁))) ⧸
          pPrimeCore 2 ↥((barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁))))
        .PSL 2 p (f / 2) ∧
      twoPart (⊤ : Subgroup ↥(layer (MBar z₁))) ≤
        2 * twoPart (fixedPoints (MulAut.conjNormal (QuotientGroup.mk
          ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁) :
            MulAut ↥(layer (MBar z₁)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hMeq
  have hq : IsQuasisimple ↥(layer (MBar z₁)) := hM.1
  obtain ⟨hKC, -, -⟩ := L415.isPComponent_barOf hD.beta_mem_F hD.orderOf_beta
    hD.fd.isTwoComponentIn_K₂
  have hKM := hlt.le
  have hKfix : (barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁)) ≤
      fixedPoints (MulAut.conjNormal (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
        hD.beta_mem_F⟩ : MBar z₁) : MulAut ↥(layer (MBar z₁))) := by
    rw [L415.fixedPoints_conjNormal]
    intro x hx
    exact ⟨x.2, hKC hx⟩
  refine ⟨L415.orderOf_conjNormal hq hD.betaF_mul_betaF hlt hKpc (by
      obtain ⟨k, hk, hkz⟩ := hD.exists_not_comm_z₂F
      exact ⟨k, hk, _, hD.z₂F_mem, hkz⟩), ?_, ?_,
    L415.twoPart_top_le hsyl (hcard.trans (Nat.mul_le_mul_right _
      (hD.relIndex_W₀F_le_two hnβ)))⟩
  · rw [L415.isTwoComponentIn_fixedPoints_iff _ hKfix, subgroupOf_map_subtype,
      inf_of_le_left hKM]
    exact hKpc
  · obtain ⟨e⟩ := hD.nonempty_K₂F_equiv
    exact lieModel_psl2_of_mulEquiv ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hKM)).trans e) (hD.hs.lieModel_KBar hD.h412)

theorem not_small_types (hSm : Harris415SmallTypesIndexFact)
    {M : Subgroup (MBar z₁)} (hM : IsComponent M) (hMeq : layer (MBar z₁) = M)
    (hlt : barOf (centralizer {z₁}) K₂ < M)
    (hKpc : IsPComponent 2 ((barOf (centralizer {z₁}) K₂).subgroupOf (M ⊓ centralizer
      {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁)})))
    (hsyl : IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) M)
    (hcard : Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) ≤
      (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁} ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).relIndex
        (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) *
      Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M ⊓
        centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
          hD.beta_mem_F⟩ : MBar z₁)}))
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁) :
    ¬ (Nonempty (↥(layer (MBar z₁)) ≃* Blueprint.NativeSporadic.J2) ∨
      Nonempty (↥(layer (MBar z₁)) ≃* Blueprint.NativeSporadic.J3) ∨
      Blueprint.LieModel ↥(layer (MBar z₁)) .PSL 3 2 2) := by
  intro hY
  obtain ⟨hτ, hKc, hKL, hbound⟩ := hD.beta_facts hM hMeq hlt hKpc hsyl hcard hnβ
  have h1 := hSm _ hY _ hτ _ hKc p (f / 2) hD.hs.prime_p hD.hs.p_ne_two hD.hs.one_le_half
    hD.hs.sixteen_dvd hKL
  have hpos : 0 < twoPart (fixedPoints (MulAut.conjNormal (QuotientGroup.mk
      ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁) :
        MulAut ↥(layer (MBar z₁)))) := pow_pos two_pos _
  omega

end Data415B

end CFSG.ComponentClassification.HarrisLit
