module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4T
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isUniqueInvolution_of_isSylow2In (hL : TightLargeHypR r n Y R S t) {M T : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) (hT : IsSylow2In T M) {z : Y}
    (hz : IsUniqueInvolution M z) : IsUniqueInvolution T z := by
  have h := TightLargeHypR.typeRFam hL
  have h8 := Sec6Gen.eight_le_of_mem_RSet h.hyp (mem_RSet_of_isSylow2In hM hT)
  exact ⟨T3.mem_of_isPGroup hz hT.1 hT.2.1 (by omega), hz.ne_one, hz.sq,
    fun y hy hy2 => hz.unique y (hT.1 hy) hy2⟩

theorem exists_e4FrameAt (hL : TightLargeHypR 3 n Y R S t) (hcase : LinkE4 R t)
    (hA : ¬ TriNbrAll R t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) :
    ∃ (K' : Subgroup Y) (x y x' : Y), E4FrameAt R t J K' u x y x' := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨K', hK'K, hK'J⟩ := exists_commonNbr_of_linkE4 hL hcase hJ
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK'K.1
  have hz'tu : z' = t * u := noGNbr_of_linkE4 hL hcase hA hJ K' hK'K hK'J u z' hu hz'
  rw [hz'tu] at hz'
  obtain ⟨T₀, T, T', hT₀, hT, hT', c01, c02, c12⟩ :=
    exists_commuting_sylow_triple hL hJ hK'K hK'J hu hz'
  obtain ⟨e₀⟩ := h.quat _ hK₀ T₀ hT₀
  obtain ⟨e₁⟩ := h.quat _ hJ.1 T hT
  obtain ⟨e₂⟩ := h.quat _ hK'K.1 T' hT'
  have ht₀ := isUniqueInvolution_of_isSylow2In hL hK₀ hT₀ ht
  have hu₁ := isUniqueInvolution_of_isSylow2In hL hJ.1 hT hu
  have htu₂ := isUniqueInvolution_of_isSylow2In hL hK'K.1 hT' hz'
  obtain ⟨x, hxT, hxx⟩ := q8_exists_sq e₀ ht₀
  obtain ⟨y, hyT, hyy⟩ := q8_exists_sq e₁ hu₁
  obtain ⟨x', hx'T, hx'x'⟩ := q8_exists_sq e₂ htu₂
  obtain ⟨⟨a, haT, hax⟩, ⟨b₀, hb₀T, hnc⟩⟩ := q8_exists_inv e₀ ht₀ hxT hxx
  obtain ⟨⟨b, hbT, hby⟩, -⟩ := q8_exists_inv e₁ hu₁ hyT hyy
  have cxy : x * y = y * x := c01 x hxT y hyT
  have cxx' : x * x' = x' * x := c02 x hxT x' hx'T
  have cyx' : y * x' = x' * y := c12 y hyT x' hx'T
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  refine ⟨K', x, y, x', ⟨hJ, hu, hK'K, hK'J, hz', hT₀.1 hxT, hT.1 hyT, hT'.1 hx'T, hxx, hyy, hx'x',
    cxy, cxx', cyx', ?_, ⟨a, hax, c01 a haT y hyT, c02 a haT x' hx'T⟩,
    ⟨b, hby, (c01 x hxT b hbT).symm, c12 b hbT x' hx'T⟩⟩⟩
  intro hs
  apply hnc
  have hb₀t : b₀ * t = t * b₀ := by
    have h1 := ht₀.conj_eq (conjSub_eq_self_of_mem hb₀T)
    calc b₀ * t = b₀ * t * b₀⁻¹ * b₀ := by group
      _ = t * b₀ := by rw [h1]
  have hb₀u : b₀ * u = u * b₀ := c01 b₀ hb₀T u hu₁.mem
  have hb₀s : b₀ * (x * y * x') = x * y * x' * b₀ := by
    rcases T3CII.closure_pair_cases ht.sq hu.sq ctu hs with e | e | e | e <;> rw [e]
    · group
    · exact hb₀t
    · exact hb₀u
    · rw [← mul_assoc, hb₀t, mul_assoc, hb₀u, ← mul_assoc]
  have hb₀y : Commute b₀ y := c01 b₀ hb₀T y hyT
  have hb₀x' : Commute b₀ x' := c02 b₀ hb₀T x' hx'T
  have hb₀s' : Commute b₀ (x * y * x') := hb₀s
  have h1 := (hb₀s'.mul_right hb₀x'.inv_right).mul_right hb₀y.inv_right
  rw [show x * y * x' * x'⁻¹ * y⁻¹ = x by group] at h1
  exact h1.eq

variable {n : ℕ}

theorem tightE4FrameR_three : TightE4FrameR 3 n := by
  intro Y _ _ R S t hL hc hcase hA J hJ u hu
  exact exists_e4FrameAt hL hcase hA hJ hu

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
