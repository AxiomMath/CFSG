module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftCore
public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftCentralizer

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open Matrix CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.TorusSplitting

variable {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {F : Type} [Field F] {Sigma : Subgroup (F ≃+* F)} {b : Fˣ}
  {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}
  {h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)}
  {J : Subgroup (involutionCentralizer n S e)} [J.Normal]
  (hJR : J ⊓ centralizerOddCore n S e = ⊥)
  (hJmem : ∀ j ∈ J, liftMap n hn S e Ψ h j ∈ modelLayer F b n hn Sigma hSigma)
  (y₀ : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
  (hy : liftMap n hn S e Ψ h (nModel n hn S e (Original.x2 (2 ^ n))) =
    modelInl F b n hn Sigma hSigma y₀)
  (hMD : (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)).range ⊓
    Subgroup.centralizer {y₀} =
      (OddFieldTorus.torus F).map
        (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)))
  (WF : Subgroup (SpecialLinearGroup (Fin 2) F))
  (hWF : ∀ g, g ∈ WF ↔ g ∈ OddFieldTorus.torus F ∧ Odd (orderOf g))

include hJR hJmem hy hMD hWF in
theorem oddTorus_le_centralizer_four :
    oddTorus n hn S e Ψ h J WF ≤ Subgroup.centralizer (Subgroup.closure
      {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) := by
  intro g hg
  have hmem := (mem_oddTorus_iff hn hJR hJmem y₀ hy hMD WF hWF g).mp hg
  obtain ⟨⟨j, hj, rfl⟩, hcy, -⟩ := hmem
  exact (mem_centralizer_four_iff hn S e j).mpr (Subtype.ext hcy)

include hJR hJmem hy hMD hWF in
theorem oddTorus_normalized : ∀ c ∈ Subgroup.centralizer (Subgroup.closure
      {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G),
    ∀ g ∈ oddTorus n hn S e Ψ h J WF, c * g * c⁻¹ ∈ oddTorus n hn S e Ψ h J WF := by
  intro c hc g hg
  have hmem := (mem_oddTorus_iff hn hJR hJmem y₀ hy hMD WF hWF g).mp hg
  obtain ⟨⟨j, hj, rfl⟩, hcy, hodd⟩ := hmem
  have hcN : c ∈ involutionCentralizer n S e := centralizer_four_le n S e hc
  have hcy' : c * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * c :=
    (Subgroup.mem_centralizer_iff.mp hc _ (x2_mem_four n S e)).symm
  apply (mem_oddTorus_iff hn hJR hJmem y₀ hy hMD WF hWF _).mpr
  refine ⟨⟨⟨c, hcN⟩ * j * (⟨c, hcN⟩ : involutionCentralizer n S e)⁻¹,
    (inferInstance : J.Normal).conj_mem j hj _, rfl⟩, ?_, ?_⟩
  · set y := wreathModelHom S e (Original.x2 (2 ^ n))
    change c * (j : G) * c⁻¹ * y = y * (c * (j : G) * c⁻¹)
    have hcy'' : c⁻¹ * y = y * c⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcy', mul_assoc, mul_inv_cancel, mul_one]
    calc c * (j : G) * c⁻¹ * y = c * (j : G) * (c⁻¹ * y) := by group
      _ = c * ((j : G) * y) * c⁻¹ := by rw [hcy'']; group
      _ = c * (y * (j : G)) * c⁻¹ := by
        rw [show (j : G) * y = y * (j : G) from hcy]
      _ = (c * y) * (j : G) * c⁻¹ := by group
      _ = y * (c * (j : G) * c⁻¹) := by rw [hcy']; group
  · change Odd (orderOf (MulAut.conj c (j : G)))
    rw [MulEquiv.orderOf_eq]
    exact hodd

include hJR hJmem hy hMD hWF in
theorem oddTorus_odd [Finite G] : Odd (Nat.card (oddTorus n hn S e Ψ h J WF)) := by
  apply ReducedInvolution.odd_card_of_forall_odd_orderOf
  intro g
  rw [← Subgroup.orderOf_coe]
  exact ((mem_oddTorus_iff hn hJR hJmem y₀ hy hMD WF hWF g).mp g.2).2.2

include hJR hJmem hy hMD hWF in
theorem oddTorus_le_torusCore [Finite G] : oddTorus n hn S e Ψ h J WF ≤ torusCore n S e :=
  le_ambientOddCore (oddTorus_le_centralizer_four hn hJR hJmem y₀ hy hMD WF hWF)
    (oddTorus_normalized hn hJR hJmem y₀ hy hMD WF hWF)
    (oddTorus_odd hn hJR hJmem y₀ hy hMD WF hWF)

omit [J.Normal] in
theorem oddTorus_inf_torusFixedCore [Finite G] (hJR : J ⊓ centralizerOddCore n S e = ⊥) :
    oddTorus n hn S e Ψ h J WF ⊓ torusFixedCore n S e = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨j, -, rfl⟩, ⟨⟨r, hr, hrj⟩, -⟩⟩
  have hjr : (j : involutionCentralizer n S e) = r := Subtype.ext hrj.symm
  have hm : (j : involutionCentralizer n S e) ∈ J ⊓ centralizerOddCore n S e :=
    ⟨j.2, hjr ▸ hr⟩
  rw [hJR, Subgroup.mem_bot] at hm
  change ((j : involutionCentralizer n S e) : G) ∈ (⊥ : Subgroup G)
  rw [hm]
  exact Subgroup.one_mem _

theorem oddTorus_comm_torusFixedCore [Finite G] (hJR : J ⊓ centralizerOddCore n S e = ⊥) :
    ∀ g ∈ oddTorus n hn S e Ψ h J WF, ∀ z ∈ torusFixedCore n S e, g * z = z * g := by
  rintro g ⟨j, -, rfl⟩ z ⟨⟨r, hr, rfl⟩, -⟩
  exact congrArg Subtype.val (commute_of_inf_eq_bot hJR j.2 hr)

end CFSG.Wreathed.NormalComponentLift
