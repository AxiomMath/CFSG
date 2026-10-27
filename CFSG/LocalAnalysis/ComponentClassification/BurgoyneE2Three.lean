module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Core

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {τ : Tag} {K : Type} [Field K]

theorem units_sq_eq_one_of_card_three [Finite K] (h3 : Nat.card K = 3) (t : Kˣ) : t ^ 2 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card Kˣ = 2 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h3]
  rw [← hcard]
  exact pow_card_eq_one


theorem sq_eq_one_of_mem_torusGroup_three [Finite K] (h3 : Nat.card K = 3) {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : h ^ 2 = 1 := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, t⟩, rfl⟩ := hx
    change torusElt τ K i t ^ 2 = 1
    rw [sq, ← torusElt_mul, ← sq, units_sq_eq_one_of_card_three h3, torusElt_one]
  | one => rw [one_pow]
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (mul_comm_of_mem_torusGroup hx hy) 2, ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

theorem sq_eq_one_of_mem_center_componentRootSpan_three [Finite K] (h3 : Nat.card K = 3)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} {z : componentRootSpan K χ i}
    (hz : z ∈ center (componentRootSpan K χ i)) : (z : ModGL τ K) ^ 2 = 1 :=
  sq_eq_one_of_mem_torusGroup_three h3 (componentTorus_le_torusGroup K χ i
    (CFSG.LieType.HighestRoot.coe_mem_componentTorus_of_mem_center hz))

theorem sq_eq_one_of_commute_componentRootSpan_three [Finite K] (h3 : Nat.card K = 3)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {n : ModGL τ K} (hn : n ∈ rootSpan τ K (kernelRoots χ))
    (hc : ∀ i, ∀ s ∈ componentRootSpan K χ i, n * s = s * n) : n ^ 2 = 1 := by
  classical
  obtain ⟨-, -, -, -, ⟨μ, hμ1, hμs, -⟩, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
  obtain ⟨f, hf⟩ := hμs ⟨n, hn⟩
  have hμ : ∀ g, (μ g : ModGL τ K) = ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) :=
    fun _ => rfl
  have hfc : ∀ i, f i ∈ center (componentRootSpan K χ i) := by
    intro i
    rw [Subgroup.mem_center_iff]
    intro x
    set g := f * (Pi.mulSingle i (f i))⁻¹ with hg_def
    have hg : g * Pi.mulSingle i x = Pi.mulSingle i x * g := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hg_def]
      · simp [hg_def, Pi.mulSingle_eq_of_ne hj]
    have hfg : f = g * Pi.mulSingle i (f i) := by
      rw [hg_def, inv_mul_cancel_right]
    have e1 : (μ g : ModGL τ K) * x = x * μ g := by
      have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hg
      simpa only [map_mul, Subgroup.coe_mul, hμ1] using h1
    have e3 : n = (μ g : ModGL τ K) * (f i : ModGL τ K) := by
      have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hfg
      simp only [map_mul, Subgroup.coe_mul, hμ1, hf] at h1
      exact h1
    have e2 : n * x = x * n := hc i x x.2
    rw [e3] at e2
    refine Subtype.ext ?_
    change (x : ModGL τ K) * f i = f i * x
    have e4 : (μ g : ModGL τ K) * (f i * x) = (μ g : ModGL τ K) * (x * f i) := by
      calc (μ g : ModGL τ K) * (f i * x) = (μ g : ModGL τ K) * f i * x := by group
        _ = x * ((μ g : ModGL τ K) * f i) := e2
        _ = (μ g : ModGL τ K) * (x * f i) := by rw [← mul_assoc, ← e1, mul_assoc]
    exact (mul_left_cancel e4).symm
  have hff : f ^ 2 = 1 := by
    funext i
    refine Subtype.ext ?_
    rw [Pi.pow_apply, Pi.one_apply, Subgroup.coe_pow, Subgroup.coe_one]
    exact sq_eq_one_of_mem_center_componentRootSpan_three h3 (hfc i)
  have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hff
  simpa only [map_pow, map_one, hf, Subgroup.coe_pow, Subgroup.coe_one] using h1

theorem pPrimeCore_toralCentralizer_eq_bot_three [Finite K] (h3 : Nat.card K = 3)
    (hK : ringChar K ≠ 2) {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) :
    pPrimeCore 2 (toralCentralizer τ K b) = ⊥ := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have hT : ∀ (i : Fin τ.rank) (t : Kˣ),
      torusElt τ K i t ^ 2 ∈ rootSpan τ K (rootCharKernel b) := by
    intro i t
    rw [sq, ← torusElt_mul, ← sq, units_sq_eq_one_of_card_three h3, torusElt_one]
    exact one_mem _
  set χ := maskChar (signTupleBits b) with hχ_def
  have hKer : rootCharKernel b = kernelRoots χ := rootCharKernel_eq_kernelRoots hK hb
  set X := toralCentralizer τ K b with hX
  set S := rootSpan τ K (rootCharKernel b) with hS
  have hSX : S ≤ X := rootSpan_rootCharKernel_le_toralCentralizer b
  obtain ⟨-, -, -, hnorm, -, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
  have hSiS : ∀ i, componentRootSpan K χ i ≤ S := fun i => by
    rw [hS, hKer]
    exact (hnorm i).1
  rw [pPrimeCore_eq_bot_iff]
  intro N hNn hNodd
  set N₀ := N.map X.subtype with hN₀
  have hN₀odd : ∀ n ∈ N₀, Odd (orderOf n) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact Nat.coprime_two_left.mp (hNodd.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hm))
  have hN₀X : N₀ ≤ X := Subgroup.map_subtype_le N
  have hN₀S : N₀ ≤ S := fun n hn => mem_rootSpan_of_odd hK hb hT (hN₀X hn) (hN₀odd n hn)
  have hN₀conj : ∀ x ∈ X, ∀ n ∈ N₀, x * n * x⁻¹ ∈ N₀ := by
    rintro x hx _ ⟨m, hm, rfl⟩
    exact ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, hNn.conj_mem m hm _, rfl⟩
  have hNi : ∀ i, ∀ z ∈ N₀, z ∈ componentRootSpan K χ i → z = 1 := by
    intro i z hzN hzi
    set Si := componentRootSpan K χ i
    let D : Subgroup Si := N₀.comap Si.subtype
    have hDn : D.Normal := ⟨fun d hd s => by
      change (s : ModGL τ K) * d * (s : ModGL τ K)⁻¹ ∈ N₀
      exact hN₀conj _ (hSX (hSiS i s.2)) _ hd⟩
    have hDodd : Nat.Coprime 2 (Nat.card D) := by
      rw [← Subgroup.card_map_of_injective Si.subtype_injective]
      have hle : D.map Si.subtype ≤ N₀ := Subgroup.map_comap_le _ _
      have hcard : Nat.card N₀ = Nat.card N :=
        Subgroup.card_map_of_injective X.subtype_injective
      exact (hcard ▸ hNodd).coprime_dvd_right (Subgroup.card_dvd_of_le hle)
    have hz : (⟨z, hzi⟩ : Si) ∈ center Si :=
      le_center_of_odd_normal_componentRootSpan hK χ i D hDodd (show z ∈ N₀ from hzN)
    have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_center_componentRootSpan_three h3 hz
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have hodd := hN₀odd z hzN
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  have hNc : ∀ n ∈ N₀, ∀ i, ∀ s ∈ componentRootSpan K χ i, n * s = s * n := by
    intro n hn i s hs
    have h1 : n * s * n⁻¹ * s⁻¹ ∈ N₀ := by
      have := mul_mem hn (hN₀conj s (hSX (hSiS i hs)) _ (inv_mem hn))
      rwa [show n * (s * n⁻¹ * s⁻¹) = n * s * n⁻¹ * s⁻¹ by group] at this
    have h2' : n * s * n⁻¹ * s⁻¹ ∈ componentRootSpan K χ i := by
      have hnS : n ∈ rootSpan τ K (kernelRoots χ) := hKer ▸ hN₀S hn
      have hsS : s ∈ rootSpan τ K (kernelRoots χ) := (hnorm i).1 hs
      have h3 := (hnorm i).2.conj_mem ⟨s, hsS⟩ hs ⟨n, hnS⟩
      exact mul_mem h3 (inv_mem hs)
    have h4 := hNi i _ h1 h2'
    calc n * s = n * s * n⁻¹ * s⁻¹ * (s * n) := by group
      _ = s * n := by rw [h4, one_mul]
  rw [eq_bot_iff]
  intro m hm
  have hmN₀ : (m : ModGL τ K) ∈ N₀ := ⟨m, hm, rfl⟩
  have hm2 : (m : ModGL τ K) ^ 2 = 1 :=
    sq_eq_one_of_commute_componentRootSpan_three h3 (hKer ▸ hN₀S hmN₀) (hNc _ hmN₀)
  have hdvd : orderOf (m : ModGL τ K) ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
  have hodd := hN₀odd _ hmN₀
  rw [Subgroup.mem_bot]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact Subtype.ext (orderOf_eq_one_iff.1 h1)
  · rw [h1] at hodd
    exact absurd hodd (by decide)

theorem burgCoreFor_E7_t7_three [Finite K] (h3 : Nat.card K = 3) :
    BurgCoreFor (rootDiagAut .E7 K (bitsTuple e7BitsSix)) := by
  have hK2 : ringChar K ≠ 2 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact h3)
    rw [ringChar.eq K 3]
    decide
  exact burgCoreFor_rootDiagAut_E7 (pPrimeCore_toralCentralizer_eq_bot_three h3 hK2
    (bitsTuple_mem _)) (k := e7Node 0)
    (by simp [bitsTuple, show e7BitsSix (e7Node 0) = false from by decide])

end CFSG.ComponentClassification.Burgoyne.E2
