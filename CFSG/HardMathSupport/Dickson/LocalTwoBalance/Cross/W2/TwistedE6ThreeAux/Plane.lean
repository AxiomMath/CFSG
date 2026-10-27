module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Normal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.A2A2
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Cover
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenCenter

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω}

section Plane

variable (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
  (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
  (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
  (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)

include hℓ hf hK hσ hFr hp hp3 hpq hg hgn

theorem plane_data (c₀ : twistedE6RootGroup K σ) (A₀ : Subgroup (twistedE6RootGroup K σ))
    (hA₀card : Nat.card A₀ = p ^ 2) (hA₀exp : ∀ e ∈ A₀, e ^ p = 1)
    (hc₀ : ∀ e ∈ A₀, frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g) :
    (∀ y ∈ phi3TorusTorsion Ω Fr p, ∃ e ∈ A₀, frameEmb K σ Ω g c₀ e = y) ∧
      (∀ e ∈ A₀, e ≠ 1 → orderOf (frameEmb K σ Ω g c₀ e) = p) ∧
      ∃ e ∈ A₀, e ≠ 1 ∧ ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 supportA2A2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hψinj := frameEmb_injective (g := g) c₀
  obtain ⟨-, -, hplanes⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨hplane, L, hL, -, -, hmeet⟩ := hplanes
  have hĀle : A₀.map (frameEmb K σ Ω g c₀) ≤ phi3TStar K σ.toRingHom Ω Fr g := by
    rintro _ ⟨e, he, rfl⟩
    exact hc₀ e he
  have hĀexp : ∀ y ∈ A₀.map (frameEmb K σ Ω g c₀), y ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hA₀exp e he, map_one]
  have hĀcard : Nat.card (A₀.map (frameEmb K σ Ω g c₀)) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hψinj]
    exact hA₀card
  have hĀeq : A₀.map (frameEmb K σ Ω g c₀) = phi3TorusTorsion Ω Fr p :=
    hplane _ hĀle hĀexp hĀcard
  refine ⟨fun y hy => ?_, fun e he he1 => ?_, ?_⟩
  · rw [← hĀeq] at hy
    obtain ⟨e, he, rfl⟩ := hy
    exact ⟨e, he, rfl⟩
  · rw [orderOf_frameEmb]
    exact orderOf_eq_prime (hA₀exp e he) he1
  · obtain ⟨u, huĀ, huL, hu1⟩ := hmeet _ hĀle hĀexp hĀcard 0
    obtain ⟨e, he, rfl⟩ := huĀ
    exact ⟨e, he, fun h => hu1 (by rw [h, map_one]), (hL 0).2.2 _ huL hu1⟩

variable (c₀ : twistedE6RootGroup K σ)

theorem not_graph_actor (e : twistedE6RootGroup K σ)
    (hy : frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g)
    (hyp : orderOf (frameEmb K σ Ω g c₀ e) = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 supportA2A2)
    {η : MulAut (twistedE6RootGroup K σ)} (hηe : η e = e)
    (hηl : ∀ u, frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e) → η u = u)
    {a : ModGL Tag.E6 Ω} (haC : a ∈ adjointGroup Tag.E6 Ω)
    (hae : ∀ u : twistedE6RootGroup K σ, twE6Emb K σ Ω (η u) =
      a * diagE6 Ω ^ 1 * twE6Emb K σ Ω u * (diagE6 Ω ^ 1)⁻¹ * a⁻¹) : False := by
  classical
  obtain ⟨G₃, hG₃⟩ : ∃ G₃ : ModGL Tag.E6 Ω, G₃ = g⁻¹ * twE6Emb K σ Ω c₀ * a *
      (diagE6 Ω * ((twE6Emb K σ Ω c₀)⁻¹ * g) * (diagE6 Ω)⁻¹) := ⟨_, rfl⟩
  have hG₃adj : G₃ ∈ adjointGroup Tag.E6 Ω := by
    rw [hG₃]
    exact mul_mem (mul_mem (mul_mem (inv_mem hg) (twE6Emb_mem c₀)) haC)
      (E6GraphLevi.diagramMap_conj_mem_adjointGroup'
        (mul_mem (inv_mem (twE6Emb_mem c₀)) hg))
  have hconj : ∀ r : twistedE6RootGroup K σ, (G₃ * diagE6 Ω) * frameEmb K σ Ω g c₀ r *
      (G₃ * diagE6 Ω)⁻¹ = frameEmb K σ Ω g c₀ (η r) := by
    intro r
    have h1 : (G₃ * diagE6 Ω) * frameEmb K σ Ω g c₀ r * (G₃ * diagE6 Ω)⁻¹ =
        g⁻¹ * twE6Emb K σ Ω c₀ * ((a * diagE6 Ω) * twE6Emb K σ Ω r * (a * diagE6 Ω)⁻¹) *
          (twE6Emb K σ Ω c₀)⁻¹ * g := by
      rw [hG₃, frameEmb_apply]
      simp only [map_mul, map_inv]
      group
    have h2 : twE6Emb K σ Ω (η r) = (a * diagE6 Ω) * twE6Emb K σ Ω r * (a * diagE6 Ω)⁻¹ := by
      rw [hae r, pow_one]
      group
    rw [h1, ← h2, frameEmb_apply]
    simp only [map_mul, map_inv]
    group
  have hfix : (G₃ * diagE6 Ω) * frameEmb K σ Ω g c₀ e * (G₃ * diagE6 Ω)⁻¹ =
      frameEmb K σ Ω g c₀ e := by
    rw [hconj e, hηe]
  refine KETw3.phi3_graph_contra (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq
    hy.1 hyp hA2A2 hG₃adj hfix (fun u hu => ?_)
  have hCs := layer_le_CStar hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp (Or.inr hA2A2) hu
  rw [← range_frameEmb (g := g) c₀] at hCs
  obtain ⟨r, rfl⟩ := hCs
  rw [hconj r, hηl r hu]

theorem eq_one_of_actor (A₀ : Subgroup (twistedE6RootGroup K σ))
    (hA₀card : Nat.card A₀ = p ^ 2) (hA₀exp : ∀ e ∈ A₀, e ^ p = 1)
    (hc₀ : ∀ e ∈ A₀, frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g)
    {η : MulAut (twistedE6RootGroup K σ)}
    (hfix : ∀ e ∈ A₀, e ≠ 1 →
      ((∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 support13) ∨
        ∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) =
            parabolicRoots Tag.E6 supportA2A2) →
      η e = e ∧ ∀ u, frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e) → η u = u)
    {a : ModGL Tag.E6 Ω} (haC : a ∈ adjointGroup Tag.E6 Ω)
    (hae : ∀ u : twistedE6RootGroup K σ,
      twE6Emb K σ Ω (η u) = a * twE6Emb K σ Ω u * a⁻¹) : η = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hlift, hord, e_b, he_b, he_b1, hA2A2⟩ :=
    plane_data hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ A₀ hA₀card hA₀exp hc₀
  obtain ⟨a_g, ha_g⟩ : ∃ a_g : ModGL Tag.E6 Ω,
      a_g = g⁻¹ * twE6Emb K σ Ω c₀ * a * (twE6Emb K σ Ω c₀)⁻¹ * g := ⟨_, rfl⟩
  have hag_adj : a_g ∈ adjointGroup Tag.E6 Ω := by
    rw [ha_g]
    exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hg) (twE6Emb_mem c₀)) haC)
      (inv_mem (twE6Emb_mem c₀))) hg
  have hconj : ∀ r : twistedE6RootGroup K σ,
      a_g * frameEmb K σ Ω g c₀ r * a_g⁻¹ = frameEmb K σ Ω g c₀ (η r) := by
    intro r
    have h1 : frameEmb K σ Ω g c₀ (η r) =
        g⁻¹ * twE6Emb K σ Ω c₀ * twE6Emb K σ Ω (η r) * (twE6Emb K σ Ω c₀)⁻¹ * g := by
      rw [frameEmb_apply]
      simp only [map_mul, map_inv]
      group
    rw [h1, hae r, ha_g, frameEmb_apply]
    simp only [map_mul, map_inv]
    group
  have hcomm : ∀ e ∈ A₀, e ≠ 1 →
      ((∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 support13) ∨
        ∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) =
            parabolicRoots Tag.E6 supportA2A2) →
      a_g * frameEmb K σ Ω g c₀ e = frameEmb K σ Ω g c₀ e * a_g ∧
        ∀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e), a_g * u = u * a_g := by
    intro e he he1 htype
    obtain ⟨hηe, hηl⟩ := hfix e he he1 htype
    refine ⟨?_, fun u hu => ?_⟩
    · have := hconj e
      rw [hηe] at this
      exact (mul_inv_eq_iff_eq_mul.1 this)
    · have hCs := layer_le_CStar hℓ hf hK hσ hFr hp hp3 hpq hg hgn (hc₀ e he) (hord e he he1)
        htype hu
      rw [← range_frameEmb (g := g) c₀] at hCs
      obtain ⟨r, rfl⟩ := hCs
      have := hconj r
      rw [hηl r hu] at this
      exact (mul_inv_eq_iff_eq_mul.1 this)
  have hag_torus : a_g ∈ torusGroup Tag.E6 Ω := by
    obtain ⟨hcy, hcP⟩ := hcomm e_b he_b he_b1 (Or.inr hA2A2)
    exact mem_torus_of_commute_A2A2 hℓ hf hK hσ hFr hp hp3 hpq hg hgn (hc₀ e_b he_b)
      (hord e_b he_b he_b1) hA2A2 hag_adj hcy hcP
  have hroot : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ∀ c : Ω,
      a_g * pinnedX Tag.E6 Ω α c = pinnedX Tag.E6 Ω α c * a_g := by
    intro α hα c
    obtain ⟨y, hyT, hy1, hαy⟩ := exists_mem_torsion_kernel hℓ hf hK hσ hFr hp hp3 hpq hα
    obtain ⟨e, he, rfl⟩ := hlift y hyT
    have he1 : e ≠ 1 := fun h => hy1 (by rw [h, map_one])
    have hy := hc₀ e he
    have hyp := hord e he he1
    have htype := type_of_mem_kernel hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp hαy
    obtain ⟨-, hcP⟩ := hcomm e he he1 htype
    rcases htype with hA2 | hA2A2'
    · exact phi3_A2_commute_roots hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp hA2 hag_torus hcP α
        hαy c
    · exact phi3_A2A2_commute_roots hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp hA2A2' hag_torus hcP
        α hαy c
  have hχ : ∀ i : Fin Tag.E6.rank, torusRootChar a_g (Pi.single i 1) = 1 := by
    intro i
    have hα : IsRoot Tag.E6 (Pi.single i 1) := isRoot_single Tag.E6 i
    have e := conj_pinnedX_of_mem_torusGroup hag_torus hα 1
    rw [hroot _ hα 1, mul_inv_cancel_right, mul_one] at e
    exact (pinnedX_injective Tag.E6 Ω _ e).symm
  have hag1 : a_g = 1 := CFSG.RankThree.Lattice.eq_one_of_torusRootChar_single hag_torus hχ
  refine MulEquiv.ext fun r => ?_
  have h1 := hconj r
  rw [hag1, one_mul, inv_one, mul_one] at h1
  exact (frameEmb_injective (g := g) c₀ h1).symm

theorem eq_one_of_fixes (A₀ : Subgroup (twistedE6RootGroup K σ))
    (hA₀card : Nat.card A₀ = p ^ 2) (hA₀exp : ∀ e ∈ A₀, e ^ p = 1)
    (hc₀ : ∀ e ∈ A₀, frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g)
    {η : MulAut (twistedE6RootGroup K σ)}
    (hfix : ∀ e ∈ A₀, e ≠ 1 →
      ((∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 support13) ∨
        ∃ w : WeylGroup Tag.E6,
          (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) =
            parabolicRoots Tag.E6 supportA2A2) →
      η e = e ∧ ∀ u, frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e) → η u = u) :
    η = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hlift, hord, e_b, he_b, he_b1, hA2A2⟩ :=
    plane_data hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ A₀ hA₀card hA₀exp hc₀
  obtain ⟨y_a, hy_aT, hy_a1, hA2_a⟩ := exists_A2_in_torsion hℓ hf hK hσ hFr hp hp3 hpq hg hgn
  obtain ⟨e_a, he_a, rfl⟩ := hlift y_a hy_aT
  have he_a1 : e_a ≠ 1 := fun h => hy_a1 (by rw [h, map_one])
  obtain ⟨-, hηla⟩ := hfix e_a he_a he_a1 (Or.inl hA2_a)
  obtain ⟨a, haC, ε, hε, hae⟩ := normal_form_A2 hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ e_a
    (hc₀ e_a he_a) (hord e_a he_a he_a1) hA2_a hηla
  interval_cases ε
  · exact eq_one_of_actor hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ A₀ hA₀card hA₀exp hc₀ hfix haC
      (fun u => by simpa using hae u)
  · exfalso
    obtain ⟨hηeb, hηlb⟩ := hfix e_b he_b he_b1 (Or.inr hA2A2)
    exact not_graph_actor hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ e_b (hc₀ e_b he_b)
      (hord e_b he_b he_b1) hA2A2 hηeb hηlb haC hae

end Plane

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
