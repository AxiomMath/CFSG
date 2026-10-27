module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Comp
public import CFSG.LieType.HighestRoot.CentChevalleyToral

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem exists_mul_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {H S : Subgroup G}
    (hHS : H ≤ normalizer (S : Set G)) {m : G} (hm : m ∈ H ⊔ S) :
    ∃ h ∈ H, ∃ s ∈ S, m = h * s := by
  rw [← Subgroup.closure_eq H, ← Subgroup.closure_eq S, ← Subgroup.closure_union] at hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem S, (mul_one x).symm⟩
    · exact ⟨1, one_mem H, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, one_mem H, 1, one_mem S, (mul_one 1).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨h₁, hh₁, s₁, hs₁, rfl⟩ := ihx
    obtain ⟨h₂, hh₂, s₂, hs₂, rfl⟩ := ihy
    refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, h₂⁻¹ * s₁ * h₂ * s₂, mul_mem ?_ hs₂, by group⟩
    have := (Subgroup.mem_normalizer_iff.1 (hHS (inv_mem hh₂)) s₁).1 hs₁
    rwa [inv_inv] at this
  | inv x _ ihx =>
    obtain ⟨h, hh, s, hs, rfl⟩ := ihx
    refine ⟨h⁻¹, inv_mem hh, h * s⁻¹ * h⁻¹, ?_, by group⟩
    exact (Subgroup.mem_normalizer_iff.1 (hHS hh) _).1 (inv_mem hs)

theorem mem_rootSpan_of_odd
    (hK : ringChar K ≠ 2) {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hT : ∀ (i : Fin τ.rank) (t : Kˣ), torusElt τ K i t ^ 2 ∈ rootSpan τ K (rootCharKernel b))
    {x : ModGL τ K} (hx : x ∈ toralCentralizer τ K b) (hodd : Odd (orderOf x)) :
    x ∈ rootSpan τ K (rootCharKernel b) := by
  set S := rootSpan τ K (rootCharKernel b)
  have hHN : torusGroup τ K ≤ normalizer (S : Set (ModGL τ K)) :=
    (torusGroup_le_toralCentralizer b).trans (toralCentralizer_le_normalizer_rootSpan b)
  have hT2 : ∀ h ∈ torusGroup τ K, h ^ 2 ∈ S := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨i, t⟩, rfl⟩ := hx
      exact hT i t
    | one => rw [one_pow]; exact one_mem S
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (mul_comm_of_mem_torusGroup hx hy) 2)]
      exact mul_mem ihx ihy
    | inv x _ ihx =>
      rw [inv_pow]
      exact inv_mem ihx
  obtain ⟨h, hh, s, hs, hm⟩ := exists_mul_of_mem_sup_of_le_normalizer hHN
    (CFSG.LieType.HighestRoot.sq_mem_toralRootGroup hK hb hx)
  have h4 : x ^ 4 ∈ S := by
    have e : x ^ 4 = h ^ 2 * (h⁻¹ * s * h) * s := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hm, sq]
      group
    rw [e]
    refine mul_mem (mul_mem (hT2 h hh) ?_) hs
    have := (Subgroup.mem_normalizer_iff.1 (hHN (inv_mem hh)) s).1 hs
    rwa [inv_inv] at this
  refine mem_of_pow_mem_of_coprime ?_ h4
  exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)

theorem pPrimeCore_toralCentralizer_eq_bot
    [Finite K] (hK : ringChar K ≠ 2) {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1)
    (h2 : ∀ j : Fin τ.rank,
      (2 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ AddSubgroup.closure (rootCharKernel b))
    (hT : ∀ (i : Fin τ.rank) (t : Kˣ), torusElt τ K i t ^ 2 ∈ rootSpan τ K (rootCharKernel b)) :
    pPrimeCore 2 (toralCentralizer τ K b) = ⊥ := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set χ := maskChar (signTupleBits b) with hχ_def
  have hKer : rootCharKernel b = kernelRoots χ := rootCharKernel_eq_kernelRoots hK hb
  rw [hKer] at h2
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
    have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_center_componentRootSpan h2 hz
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
    sq_eq_one_of_commute_componentRootSpan h2 (hKer ▸ hN₀S hmN₀) (hNc _ hmN₀)
  have hdvd : orderOf (m : ModGL τ K) ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
  have hodd := hN₀odd _ hmN₀
  rw [Subgroup.mem_bot]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact Subtype.ext (orderOf_eq_one_iff.1 h1)
  · rw [h1] at hodd
    exact absurd hodd (by decide)

end CFSG.ComponentClassification.CatLeafProof
