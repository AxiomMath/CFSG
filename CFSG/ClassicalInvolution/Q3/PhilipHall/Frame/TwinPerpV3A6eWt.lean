module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eSides

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

structure Frame4 {Y : Type} [Group Y] (K K' K₃ K₄ W' : Subgroup Y) (t b₁ b₂ b₃ b₄ y' : Y) : Prop where
  h₁ : b₁ ∈ K ⊓ W'
  h₂ : b₂ ∈ K' ⊓ W'
  h₃ : b₃ ∈ K₃ ⊓ W'
  h₄ : b₄ ∈ K₄ ⊓ W'
  o₁ : orderOf b₁ = 4
  o₂ : orderOf b₂ = 4
  o₃ : orderOf b₃ = 4
  o₄ : orderOf b₄ = 4
  hy : y' * t * y'⁻¹ = b₁ * b₂ * b₃ * b₄

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem mem_tG_W' (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y) {W' : Subgroup Y}
    (hW' : W' ∈ WSet Ω[R]) (htW' : t ∈ W') {b₁ b₂ b₃ b₄ y' : Y}
    (fr : Frame4 K K' K₃ K₄ W' t b₁ b₂ b₃ b₄ y') {w : Y} (hwW : w ∈ W') {g : Y}
    (hg : g * t * g⁻¹ = w) :
    w = t ∨ w = y' * t * y'⁻¹ ∨ w = t * (y' * t * y'⁻¹) := by
  have hStd := C.H.ex.1
  have hF := C.H.ex.2.1
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  have hP := hC.partIHypG
  have hQ8 := A6Gen.q8Omega_of_hyp C.H
  have hKD' : K ∈ DSet Ω[R] W' := twin_mem_DSet hP (C.H.ex.2.2.2.1) hW' htW' hd.mem hd.hz
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := C.H.ex.2.2.2.1
  have htt : t * t = 1 := hd.hz.sq
  have htr : ∀ K₁ ∈ Ω[R], ∀ J ∈ Ω[R], ∃ x : Y, conjSub x K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hnab : ¬ ∀ x y : ↥(muGroup Ω[R] W'), x * y = y * x := fun hc =>
    TL4.not_comm_of_muIsoWylD4_gen (hStd.wyl W' hW') fun x hx y hy =>
      congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨S₀, hWS₀, hWC, -⟩ := A6Gen.exists_weaklyClosed_conj_of_nonab hP htr hW' hnab
  have hWab : ∀ {v : Y}, v ∈ W' → v ∈ Subgroup.centralizer (W' : Set Y) := fun hv =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Q3CL.Thompson.commutes_of_mem_WSet hP.hyp hW' x hx _ hv
  obtain ⟨m, hmN, hm⟩ := Sec7.control_centralizer_of_weaklyClosed
    (S₀.isPGroup'.to_le hWS₀) hWC (hWab htW') (g := g) (by rw [hg]; exact hWab hwW)
  rw [hg] at hm
  set J := conjSub m K with hJdef
  have hJΩ : J ∈ Ω[R] := hΩ.conjInvariant m K hd.mem
  have hJz : IsUniqueInvolution J w := by
    have := A6jB.isUniqueInvolution_conjSub hd.hz m
    rwa [hm] at this
  have hJD : J ∈ DSet Ω[R] W' := by
    have := hQ8.conjSub_mem_DSet hKD' m
    rwa [mem_normalizer_iff_conjSub_eq.mp hmN] at this
  by_cases htw : J ∈ twinSet Ω[R] K
  · left
    exact (hJz.eq (Asc77.isUniqueInvolution_of_mem_twinSet hd.hz htw))
  right
  set M : Fin 4 → Subgroup Y := ![K, K', K₃, K₄] with hM
  have hmemM : ∀ i, M i ∈ twinSet Ω[R] K := by
    intro i
    fin_cases i
    exacts [mem_twinSet_self hd.mem hd.hz, hd.hK', hd.hK₃, hF.1]
  have hinj : Function.Injective M := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hM] at hij ⊢ <;>
      first
      | exact (hd.hne hij.symm).elim
      | exact (hd.hne hij).elim
      | exact (hd.hK₃K hij.symm).elim
      | exact (hd.hK₃K hij).elim
      | exact (hd.hK₃K' hij.symm).elim
      | exact (hd.hK₃K' hij).elim
      | exact (hF.2.1 hij.symm).elim
      | exact (hF.2.1 hij).elim
      | exact (hF.2.2.1 hij.symm).elim
      | exact (hF.2.2.1 hij).elim
      | exact (hF.2.2.2.1 hij.symm).elim
      | exact (hF.2.2.2.1 hij).elim
  have hsurj : ∀ L ∈ twinSet Ω[R] K, ∃ i, M i = L := by
    intro L hL
    rcases twinSet_four hStd hF L hL with h | h | h | h
    exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩, ⟨3, h.symm⟩]
  have hJne : J ≠ M 0 := fun e => htw (by rw [e]; exact hmemM 0)
  have hJnot : M 0 ∉ omegaNbr Ω[R] J := by
    intro hnb
    have h1 := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJΩ hd.mem hnb
    have h2 : J ∈ KPerp Ω[R] K := Set.mem_insert_of_mem _ h1
    rw [kPerp_datum hStd.perp hd.mem hd.hz] at h2
    exact htw h2
  obtain ⟨e⟩ := members_q8_of_isPGroup hStd.perp h2g J hJΩ
  obtain ⟨v, hvJ, hvW, hvv⟩ := WF.exists_gen_sq hΩ hW' hJΩ hJD (h2g J hJΩ) (WF.q8Facts_of_iso hJz e)
  obtain ⟨k, hk, hprod⟩ := A6Wt.frame_prod_of_exit C.H.ex hinj hmemM hsurj hW' htW' hJΩ hJD hJz hJne
    hJnot ⟨hvJ, hvW⟩ hvv
  have hcyc : ∀ {L : Subgroup Y}, L ∈ DSet Ω[R] W' → L ∈ Ω[R] → IsCyclic ↥(L ⊓ W') := fun hLD hL =>
    (Q3CL.Thompson.inf_W_of_mem_D hd.hyp hW' hLD hL
      ⟨le_rfl, h2g _ hL, fun _ hV' _ h => le_antisymm hV' h⟩).2.2.1
  have hMD : ∀ i, M i ∈ DSet Ω[R] W' := fun i =>
    twin_mem_DSet hP h2g hW' htW' (hmemM i).1 (Asc77.isUniqueInvolution_of_mem_twinSet hd.hz (hmemM i))
  have hord4 : ∀ i, orderOf (k i) = 4 := by
    intro i
    have hk2 : k i ^ 2 = t := by rw [sq]; exact (hk i).2
    have hne : ¬ k i ^ 2 ^ 1 = 1 := by
      rw [pow_one, hk2]; exact hd.hz.ne_one
    have hfin : k i ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hk2, sq, htt]
    exact orderOf_eq_prime_pow hne hfin
  have ha : ∀ i, ![b₁, b₂, b₃, b₄] i ∈ M i ⊓ W' ∧ orderOf (![b₁, b₂, b₃, b₄] i) = 4 := by
    intro i
    fin_cases i
    exacts [⟨fr.h₁, fr.o₁⟩, ⟨fr.h₂, fr.o₂⟩, ⟨fr.h₃, fr.o₃⟩, ⟨fr.h₄, fr.o₄⟩]
  have hsq : ∀ i, ![b₁, b₂, b₃, b₄] i * ![b₁, b₂, b₃, b₄] i = t := fun i =>
    Asc77.sq_eq_of_orderOf_four (Asc77.isUniqueInvolution_of_mem_twinSet hd.hz (hmemM i))
      (ha i).1.1 (ha i).2
  have hcase : ∀ i, k i = ![b₁, b₂, b₃, b₄] i ∨ k i = ![b₁, b₂, b₃, b₄] i * t := by
    intro i
    rcases Asc77.eq_or_eq_inv_of_orderOf_four_of_cyclic (hcyc (hMD i) (hmemM i).1) (ha i).1 (hk i).1
      (ha i).2 (hord4 i) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h]
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, hsq i, htt]
  have hcomm : ∀ i, ![b₁, b₂, b₃, b₄] i * t = t * ![b₁, b₂, b₃, b₄] i := by
    intro i
    rw [← hsq i, mul_assoc]
  have hτ : y' * t * y'⁻¹ = b₁ * b₂ * b₃ * b₄ := fr.hy
  rcases A6Wt.prod4_of_cases htt (hcomm 0) (hcomm 1) (hcomm 2) (hcomm 3) (hcase 0) (hcase 1) (hcase 2)
    (hcase 3) with h | h
  · left
    rw [← hprod, hτ]
    simpa using h
  · right
    rw [← hprod, hτ]
    simpa using h


end A6eCtx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
