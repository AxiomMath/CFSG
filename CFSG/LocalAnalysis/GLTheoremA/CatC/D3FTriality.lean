module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FStable
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeIso
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.ComponentClassification.CatalogueBOrthogonalPointData
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d3f_congr_conj {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (x : G) :
    MulAut.congr θ (MulAut.conj x) = MulAut.conj (θ x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem d3f_isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G ≃* H) {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 3 A) : CFSG.Open.IsElemAbelian 3 (A.map f.toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
    obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    change f a' * f b' = f b' * f a'
    rw [← map_mul, ← map_mul, d3f_commute hA ha' hb']
  · rintro _ ⟨x, hx, rfl⟩
    change f x ^ 3 = 1
    rw [← map_pow, hA.2 x hx, map_one]

theorem charP_three_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 3 ^ n) :
    CharP K 3 := by
  have hn : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card K = 1 := by simpa using hK
    have := Finite.one_lt_card (α := K)
    omega
  have := Fintype.ofFinite K
  obtain ⟨m, hr, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at hK
  have hdvd : 3 ∣ ringChar K ^ (m : ℕ) := hK ▸ dvd_pow_self 3 hn
  have h3 : ringChar K = 3 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp (Nat.prime_three.dvd_of_dvd_pow hdvd)).symm
  exact h3 ▸ ringChar.charP K


theorem d3TrialityCentRank_holds : D3TrialityCentRank := by
  intro K _ _ n hK t ht3 htE A hA hfix
  haveI := charP_three_of_card hK
  let φ : D4Model K ≃* ↥(adjointGroup Tag.D4 K) :=
    (coordinatePlusWitnessEquiv K (isoAdj K).symm).symm
  set α : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.congr φ t with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ht3, map_one]
  have hαnot : α ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    rintro ⟨y, hy⟩
    apply htE
    have h1 : t = MulAut.conj (φ.symm y) := by
      apply (MulAut.congr φ).injective
      rw [← hα, ← hy, d3f_congr_conj, MulEquiv.apply_symm_apply]
    rw [h1]
    exact CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _
  have hA' := d3f_isElemAbelian_map φ hA
  have hfix' : ∀ a ∈ A.map φ.toMonoidHom, α a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change α (φ a) = φ a
    rw [hα, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfix a ha]
  have hcard : Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective φ.injective
  have h := chev_card_le α hα3 hαnot _ hA' hfix'
  rw [hcard] at h
  calc Nat.card A ≤ Nat.card K ^ 4 := h
    _ = 3 ^ (4 * n) := by rw [hK, ← pow_mul]; ring_nf

end CFSG.LocalAnalysis.GLTheoremA
