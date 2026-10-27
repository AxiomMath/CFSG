module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.RootCharHom
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.TwE6Step3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.E7ThreePerX
public import CFSG.RankThree.PartOne.KE.E7ThreeStab

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Matrix

set_option linter.unusedSectionVars false


section Psi


variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

@[expose] def psiC (g0 : ModGL .E7 L) (c : adjointGroup .E7 K) :
    adjointGroup .E7 K →* ModGL .E7 L :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp ((adjEmb .E7 K L).comp (MulAut.conj c).toMonoidHom)

theorem psiC_apply (g0 : ModGL .E7 L) (c x : adjointGroup .E7 K) :
    psiC g0 c x = g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0 := by
  simp [psiC, MulAut.conj_apply]

theorem psiC_injective (g0 : ModGL .E7 L) (c : adjointGroup .E7 K) :
    Function.Injective (psiC g0 c) := by
  intro x y h
  have h1 : adjEmb .E7 K L (c * x * c⁻¹) = adjEmb .E7 K L (c * y * c⁻¹) := by
    have : g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0 = g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * g0 := by
      simpa [psiC_apply] using h
    exact mul_left_cancel (mul_right_cancel this)
  have h2 := adjEmb_injective h1
  have h3 : c⁻¹ * (c * x * c⁻¹) * c = c⁻¹ * (c * y * c⁻¹) * c := by rw [h2]
  simpa [mul_assoc] using h3

end Psi


section Orbit


theorem mem_hyperClosure_of_kernel_orbit (hLay : E7ThreeLayers)
    {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1)
    {c : adjointGroup .E7 K} {E : Subgroup (adjointGroup .E7 K)} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {y : adjointGroup .E7 K} (hy : y ∈ E) (hy1 : y ≠ 1) (σ : Fin Tag.E7.rank → ℤ)
    (hσ : ∀ b : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 b = psiC F.g0 c y →
      ∀ α ∈ rootCharKernel b, ∃ j : ℕ, α = ((((-1 : ℤ) • e7T3W) ^ j) *ᵥ σ))
    {k : adjointGroup .E7 K} (hk : k * y = y * k) : k ∈ hyperClosure p ⊤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def ℓ f x
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hstab := e7T3_stabHyp F hK hp hp3 hε hpf
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    simpa [psiC_apply] using hT y hy
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_three_prelim F hp hyo c hhy
  obtain ⟨ι₀, P, ψ, -, hψinj, hψ, hψHQ, -⟩ := e7_three_perx hLay F hf hK hp hp3 hε hpf hstab hyo c
    hhy hb hap hb1 hbh
  have hbE : ∀ e : E, ∃ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b = (psiC F.g0 c).comp E.subtype e := by
    intro e
    have h := hT e e.2
    rw [F.hT] at h
    obtain ⟨b, -, hb⟩ := h
    exact ⟨b, hb⟩
  obtain ⟨χ, hχ⟩ := exists_rootCharHom ((psiC F.g0 c).comp E.subtype) hbE σ
  obtain ⟨e, hey, hχe⟩ := CFSG.HardMathSupport.Lang.TwE6Step3.exists_mem_ker_not_mem_zpowers hE hEc χ hy
  have hee : (e : adjointGroup .E7 K) ∈ E := e.2
  have hTe := hT e e.2
  have hTe' := hTe
  rw [F.hT] at hTe'
  obtain ⟨be, hbeF, hbe⟩ := hTe'
  have hbe' : rootDiagUnit .E7 be = (psiC F.g0 c).comp E.subtype e := hbe
  have hσe : rootChar be σ = 1 := by
    rw [← hχ e be hbe']
    exact hχe
  have hsub : rootCharKernel b ⊆ rootCharKernel be := by
    intro α hα
    refine ⟨hα.1, ?_⟩
    obtain ⟨j, rfl⟩ := hσ b (by rw [hbh, psiC_apply]) α hα
    rw [rootChar_pow_mulVec_of_mem_fixedCharTuples (hFr := hFr) hbeF j σ, hσe, one_pow]
  have hbeT : rootDiagUnit .E7 be ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hbe']; exact hTe
  have hcent : torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b) ≤
      Subgroup.centralizer {rootDiagUnit .E7 be} := by
    refine sup_le ?_ (rootSpan_le_centralizer be hsub)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact torusGroup_comm hx (mem_twistedTorusOf.1 hbeT).1
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk : psiC F.g0 c k ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b) := by
    have h := hψHQ ⟨k, hkC⟩
    rw [hψ] at h
    simpa [psiC_apply] using h
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hcent hψk)
  rw [hbe'] at hc
  have hke : k * e = e * k := by
    apply psiC_injective F.g0 c
    rw [map_mul, map_mul]
    exact hc
  exact CFSG.HardMathSupport.Lang.TwE6Step3.mem_hyperClosure_of_commute_pair hE hEc hy hee hy1 hey hk
    hke

end Orbit

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
