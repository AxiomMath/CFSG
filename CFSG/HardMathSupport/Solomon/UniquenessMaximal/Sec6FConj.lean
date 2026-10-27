module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FM1

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem dQ_gLBConj (g : G) (K : Subgroup G) : dQ (GLBConj g K) = GLBConj g (dQ K) := by
  ext z
  rw [mem_dQ, mem_gLBConj, mem_dQ, glaPPrimeCoreOf_gLBConj, normalizer_gLBConj,
    normalizer_gLBConj, mem_gLBConj, mem_gLBConj]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h y hy
    have := h (g⁻¹ * y * g) (by rw [mem_gLBConj]; simpa [mul_assoc] using hy)
    rw [mem_gLBConj] at this
    simpa [mul_assoc] using this
  · intro h y hy
    rw [mem_gLBConj]
    have := h (g * y * g⁻¹) (mem_gLBConj.1 hy)
    simpa [mul_assoc] using this

omit [Finite G] in
theorem gLBConj_inv_centralizer_singleton (g x : G) :
    GLBConj g⁻¹ (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext w
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : (g⁻¹ * w * g⁻¹⁻¹) * x = x * (g⁻¹ * w * g⁻¹⁻¹) := h
    calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * w := by group
  · intro h
    have h1 : w * (g * x * g⁻¹) = g * x * g⁻¹ * w := h
    calc (g⁻¹ * w * g⁻¹⁻¹) * x = g⁻¹ * (w * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * w) * g := by rw [h1]
      _ = x * (g⁻¹ * w * g⁻¹⁻¹) := by group

omit [Finite G] in
theorem mem_dQ_of_centralizes {K : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hxC : K ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ dQ K := by
  have hcomm : ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ = 1 := by
    intro y hy
    have := Subgroup.mem_centralizer_singleton_iff.1 (hxC hy)
    rw [this]; group
  refine mem_dQ.2 ⟨hxN, ?_, fun y hy => by rw [hcomm y hy]; exact one_mem _⟩
  have hOK : GLAPPrimeCoreOf 3 K ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hx : ∀ u ∈ K, x * u * x⁻¹ = u := by
    intro u hu
    have := Subgroup.mem_centralizer_singleton_iff.1 (hxC hu)
    rw [← this]; group
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [hx u (hOK hu)]; exact hu
  · intro hu
    have huK : u ∈ K := (Subgroup.mem_normalizer_iff.1 hxN u).2 (hOK hu)
    rwa [hx u huK] at hu

theorem conj_hsl {B K : Subgroup G} (hS : GLStanding G 4 3) {x g : G} (hx : x ∈ B)
    (hcomp : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) (hg : g ∈ Subgroup.normalizer (B : Set G))
    (hKM : ¬ K ≤ GLBCore 3 3 B) (hB1 : IsBOneMax 3 B)
    (hSL : IsSLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)) (hcard : Nat.card ↥(B ⊓ dQ K) = 9) :
    GLAPComponent 3 (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) (GLBConj g⁻¹ K) ∧
      B ≤ Subgroup.normalizer ((GLBConj g⁻¹ K : Subgroup G) : Set G) ∧
      ¬ GLBConj g⁻¹ K ≤ GLBCore 3 3 B ∧
      IsSLThreeFour (↥(GLBConj g⁻¹ K) ⧸ GLAPPrimeCore 3 ↥(GLBConj g⁻¹ K)) ∧
      Nat.card ↥(B ⊓ dQ (GLBConj g⁻¹ K)) = 9 ∧ g * x * g⁻¹ ∈ dQ (GLBConj g⁻¹ K) := by
  have hgB : ∀ b : G, b ∈ B ↔ g * b * g⁻¹ ∈ B := fun b => Subgroup.mem_normalizer_iff.1 hg b
  have hBg : GLBConj g B = B := by
    ext z
    rw [mem_gLBConj]
    exact (hgB z).symm
  have hBg' : GLBConj g⁻¹ B = B := by
    ext z
    rw [mem_gLBConj]
    have := hgB (g⁻¹ * z * g⁻¹⁻¹)
    simp only [inv_inv] at this ⊢
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at this
    exact this
  have h3 : 3 ≤ Open.pRank 3 B :=
    (three_le_pRank_sub_one hS hB1).trans ((Nat.sub_le _ _).trans
      (pRank_le_open_pRank hS.prime.one_lt B))
  have hgM : g ∈ GLBCore 3 3 B := normalizer_le_glbCore le_rfl h3 hg
  have hBcard : B ⊓ dQ (GLBConj g⁻¹ K) = GLBConj g⁻¹ (B ⊓ dQ K) := by
    rw [dQ_gLBConj]
    unfold GLBConj
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹⁻¹).injective]
    have := hBg'
    unfold GLBConj at this
    rw [this]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← gLBConj_inv_centralizer_singleton]
    exact glaPComponent_gLBConj hcomp g⁻¹
  · intro b hb
    rw [normalizer_gLBConj, mem_gLBConj]
    apply hBN
    exact (hgB (g⁻¹ * b * g⁻¹⁻¹)).2 (by simpa [mul_assoc] using hb)
  · intro hle
    apply hKM
    intro k hk
    have hy : g * k * g⁻¹ ∈ GLBConj g⁻¹ K := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hk
    have := hle hy
    have h2 := mul_mem (mul_mem (inv_mem hgM) this) hgM
    simpa [mul_assoc] using h2
  · obtain ⟨F, hF, hFin, hc, ⟨e⟩⟩ := hSL
    exact ⟨F, hF, hFin, hc, ⟨(conjQuotEquiv 3 g⁻¹ K).symm.trans e⟩⟩
  · rw [hBcard]
    unfold GLBConj
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective]
    exact hcard
  · rw [dQ_gLBConj, mem_gLBConj]
    have hxd : x ∈ dQ K := mem_dQ_of_centralizes (hBN hx) hcomp.1
    simpa [mul_assoc] using hxd

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
