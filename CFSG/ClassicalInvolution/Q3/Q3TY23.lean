module

public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.RouteD.TWT8Spin
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWT8 CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.ModelFacts.OrthAut
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame


section Recognition

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}

theorem exists_spin_pair3_frame (hQ : Q.Nondegenerate) {m : ℕ}
    (hm : 4 ≤ m) (F₀ : HypFrame Q m) (hdim : 9 ≤ Module.finrank (GaloisField 3 1) V)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField 3 1) V))
    {R₀ R₁ : Subgroup (spinGroup Q)} (hR₀ : R₀ ∈ 𝓕) (hR₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₀ R₁) :
    ∃ x : spinGroup Q,
      R₀ = ((rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom) := by
  classical
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  let L : ℕ → Subgroup (V ≃ₗ[GaloisField 3 1]
      V) :=
    fun a => (if a = 0 then R₀ else R₁).map (spinAction Q)
  have hL0 : L 0 = R₀.map (spinAction Q) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction Q) := by simp [L]
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let i : ℕ → (V ≃ₗ[GaloisField 3 1]
      V) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental Q (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  have hadjV : ModelAdj (scalars (GaloisField 3 1) V)
      (R₀.map (spinAction Q))
      (R₁.map (spinAction Q)) := cq.modelAdj hR₀ hR₁ hadj
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hi₀ hi₁ hadjV
  have hVchain : VChain Q 2 L i := by
    refine ⟨hi, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => by omega⟩
    · have : a = 0 := by omega
      subst this
      simpa [i] using cm
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using N
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using C
    · have : a = 0 := by omega
      subst this
      obtain ⟨W, hW⟩ := hlin
      have := hasSingularVector_of_linearPair3 hi₀ hi₁ cm N C
        ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
      simpa [i] using this
  obtain ⟨pp, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hVchain (le_refl 2)
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ F₀ (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 F₀ a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction Q) := by
    intro a ha
    have := La_range_eq_of_pairs F₀ (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  refine ⟨x, ?_, ?_⟩
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₀)
      (rootSL2_map_conj_pow3 F₀ 0 1 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₁)
      (rootSL2_map_conj_pow3 F₀ 1 2 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL1]; exact hnode 1 (by omega))

end Recognition

section Lift

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}

theorem bridgeSpin_of_omega3 (hodd : Odd (Nat.card (GaloisField 3 1)))
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField 3 1) V))
    {T₁ T₂ : Subgroup (spinGroup Q)} (h₁ : T₁ ∈ 𝓕) (h₂ : T₂ ∈ 𝓕)
    (hb : BridgeOmega Q (T₁.map (spinAction Q)) (T₂.map (spinAction Q))) :
    T₁ ≠ T₂ ∧ ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ := by
  obtain ⟨-, -, hne, hnc, hnorm⟩ := hb
  refine ⟨fun h => hne (by rw [h]), fun h => hnc ((cq.commutes_iff h₁).mpr h), ?_⟩
  intro r hr y hy
  have hinv : InvOf (T₂.map (spinAction Q)) (spinAction Q r) := cq.invOf h₂ hr
  obtain ⟨i₂, hi₂⟩ := cq.map_mem T₂ h₂
  have hπr : spinAction Q r = i₂ := IsFundamental.eq_of_orderOf_eq_two hodd hi₂ hinv.1 hinv.2
  have hmem := hnorm i₂ hi₂
  rw [Subgroup.mem_normalizer_iff] at hmem
  have hmap : (T₁.map (MulAut.conj r).toMonoidHom).map (spinAction Q) = T₁.map (spinAction Q) := by
    ext s
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
      obtain ⟨y'', hy'', hy''e⟩ := (hmem (spinAction Q y')).mp ⟨y', hy', rfl⟩
      refine ⟨y'', hy'', ?_⟩
      rw [hy''e]
      show _ = spinAction Q (r * y' * r⁻¹)
      rw [map_mul, map_mul, map_inv, hπr]
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨y'', hy'', hy''e⟩ := (hmem (i₂⁻¹ * spinAction Q y' * i₂)).mpr (by
        have : i₂ * (i₂⁻¹ * spinAction Q y' * i₂) * i₂⁻¹ = spinAction Q y' := by group
        rw [this]
        exact ⟨y', hy', rfl⟩)
      refine ⟨(MulAut.conj r).toMonoidHom y'', ⟨y'', hy'', rfl⟩, ?_⟩
      show spinAction Q (r * y'' * r⁻¹) = spinAction Q y'
      rw [map_mul, map_mul, map_inv, hπr, hy''e]
      group
  have heq := eq_of_map_eq_of_pow3 (spinAction Q) cq.ker_le cq.cop
    ((cq.pow3 T₁ h₁).map (MulAut.conj r).toMonoidHom) (cq.pow3 T₁ h₁) hmap
  rw [← heq]
  exact ⟨y, hy, rfl⟩

end Lift

section Frames

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V} {m : ℕ}

theorem spinAction_mem_O3 (x : spinGroup Q) :
    spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v

theorem exists_bridge_spin_of_frames3 (hodd : Odd (Nat.card (GaloisField 3 1))) (F₀ : HypFrame Q m)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField 3 1) V))
    (h0 : 0 < m) (h1 : 1 < m) (h2 : 2 < m) {x₀ : spinGroup Q} {R₀ R₁ : Subgroup (spinGroup Q)}
    (hR₀ : R₀ = (rootSL2 F₀ 0 1 h0 h1 (by omega) true false).map (MulAut.conj x₀).toMonoidHom)
    (hR₁ : R₁ = (rootSL2 F₀ 1 2 h1 h2 (by omega) true false).map (MulAut.conj x₀).toMonoidHom)
    {F₁ F₂ : OFrame Q} (hbr : BridgeOmega Q F₁.La.range F₂.La.range)
    {W : Submodule (GaloisField 3 1) V} (hW₁ : F₁.span ≤ W) (hW₂ : F₂.span ≤ W)
    (hWo : ∀ a : Fin m, a.val < 3 → ∀ x ∈ hypPlane (imgPair F₀ a (spinAction_mem_O x₀)),
      ∀ y ∈ W, polar Q x y = 0) :
    ∃ T₁ ∈ 𝓕, ∃ T₂ ∈ 𝓕, Commutes T₁ R₀ ∧ Commutes T₁ R₁ ∧ Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧
      T₁ ≠ T₂ ∧ ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ := by
  classical
  have hg := spinAction_mem_O3 (Q := Q) x₀
  let a0 : Fin m := ⟨0, h0⟩
  let a1 : Fin m := ⟨1, h1⟩
  let a2 : Fin m := ⟨2, h2⟩
  have o01 : (imgPair F₀ a0 hg).Orth (swapPair (imgPair F₀ a1 hg)) :=
    orth_swapPair (imgPair_orth F₀ hg (by simp [a0, a1, Fin.ext_iff]))
  have o12 : (imgPair F₀ a1 hg).Orth (swapPair (imgPair F₀ a2 hg)) :=
    orth_swapPair (imgPair_orth F₀ hg (by simp [a1, a2, Fin.ext_iff]))
  have hC₀ : (mkFrame (imgPair F₀ a0 hg) (swapPair (imgPair F₀ a1 hg)) o01).La.range =
      R₀.map (spinAction Q) := by
    rw [hR₀]
    exact La_range_eq_of_pairs F₀ h0 h1 (by omega) true false x₀ o01 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  have hC₁ : (mkFrame (imgPair F₀ a1 hg) (swapPair (imgPair F₀ a2 hg)) o12).La.range =
      R₁.map (spinAction Q) := by
    rw [hR₁]
    exact La_range_eq_of_pairs F₀ h1 h2 (by omega) true false x₀ o12 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  have hco : ∀ (F : OFrame Q), F.span ≤ W → ∀ (a b : Fin m)
      (hab : (imgPair F₀ a hg).Orth (swapPair (imgPair F₀ b hg))), a.val < 3 → b.val < 3 →
      Commutes F.La.range
        (mkFrame (imgPair F₀ a hg) (swapPair (imgPair F₀ b hg)) hab).La.range := by
    intro F hF a b hab ha hb
    have hspan : (mkFrame (imgPair F₀ a hg) (swapPair (imgPair F₀ b hg)) hab).span =
        hypPlane (imgPair F₀ a hg) ⊔ hypPlane (imgPair F₀ b hg) := by
      rw [frame_span_eq]
      show hypPlane (imgPair F₀ a hg) ⊔ hypPlane (swapPair (imgPair F₀ b hg)) = _
      rw [hypPlane_swapPair]
    refine commutes_of_span_orth F _ fun x hx y hy => ?_
    rw [hspan] at hy
    have hxW := hF hx
    exact polar_zero_of_mem_sup (A := W)
      (fun x' hx' y' hy' => by rw [polar_comm]; exact hWo a ha y' hy' x' hx')
      (fun x' hx' y' hy' => by rw [polar_comm]; exact hWo b hb y' hy' x' hx') x hxW y hy
  obtain ⟨T₁, hT₁, hT₁e⟩ := cq.surj _ hbr.1
  obtain ⟨T₂, hT₂, hT₂e⟩ := cq.surj _ hbr.2.1
  refine ⟨T₁, hT₁, T₂, hT₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (cq.commutes_iff hT₁).mp ?_
    rw [hT₁e, ← hC₀]
    exact hco F₁ hW₁ a0 a1 o01 (by simp [a0]) (by simp [a1])
  · refine (cq.commutes_iff hT₁).mp ?_
    rw [hT₁e, ← hC₁]
    exact hco F₁ hW₁ a1 a2 o12 (by simp [a1]) (by simp [a2])
  · refine (cq.commutes_iff hT₂).mp ?_
    rw [hT₂e, ← hC₀]
    exact hco F₂ hW₂ a0 a1 o01 (by simp [a0]) (by simp [a1])
  · refine (cq.commutes_iff hT₂).mp ?_
    rw [hT₂e, ← hC₁]
    exact hco F₂ hW₂ a1 a2 o12 (by simp [a1]) (by simp [a2])
  · exact (bridgeSpin_of_omega3 hodd cq hT₁ hT₂ (by rw [hT₁e, hT₂e]; exact hbr)).1
  · exact (bridgeSpin_of_omega3 hodd cq hT₁ hT₂ (by rw [hT₁e, hT₂e]; exact hbr)).2.1
  · exact (bridgeSpin_of_omega3 hodd cq hT₁ hT₂ (by rw [hT₁e, hT₂e]; exact hbr)).2.2

end Frames

section Models

theorem exists_bridge_spin_plus3
    {R₀ R₁ : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1)))}
    (h₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (h₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₀ R₁) :
    ∃ T₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)),
      ∃ T₂ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)),
        Commutes T₁ R₀ ∧ Commutes T₁ R₁ ∧ Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧ T₁ ≠ T₂ ∧
        ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ := by
  classical
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have cq := centralQuot3_plus (m := 6) (by norm_num)
  have hQ : (quadPlus 6 (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 6 _)
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus]
    norm_num
  set F₀ : HypFrame (quadPlus 6 (GaloisField 3 1)) 6 :=
    plusFrame 6 (GaloisField 3 1) (by norm_num : 3 ≤ 6) with hF₀
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair3_frame hQ (m := 6) (by norm_num) F₀ hdim cq h₀ h₁
    hadj hlin
  have hg := spinAction_mem_O3 (Q := quadPlus 6 (GaloisField 3 1)) x₀
  have hc : ∀ a b : Fin 6, a ≠ b → (imgPair F₀ a hg).Orth (imgPair F₀ b hg) :=
    fun a b hab => imgPair_orth F₀ hg hab
  obtain ⟨hbr, hs₁, hs₂⟩ := bridgeOmega_of_pairs hodd (imgPair F₀ 3 hg) (imgPair F₀ 4 hg)
    (imgPair F₀ 5 hg) (hc 3 4 (by decide)) (hc 3 5 (by decide)) (hc 4 5 (by decide))
  refine exists_bridge_spin_of_frames3 hodd F₀ cq (by norm_num) (by norm_num) (by norm_num) hx0 hx1
    hbr (W := hypPlane (imgPair F₀ 3 hg) ⊔ hypPlane (imgPair F₀ 4 hg) ⊔ hypPlane (imgPair F₀ 5 hg))
    ?_ ?_ ?_
  · rw [hs₁]
    exact le_sup_left
  · rw [hs₂]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  · intro a ha x hx y hy
    have h3 : a ≠ 3 := fun h => by simp [h] at ha
    have h4 : a ≠ 4 := fun h => by simp [h] at ha
    have h5 : a ≠ 5 := fun h => by simp [h] at ha
    exact polar_zero_of_mem_sup (A := hypPlane (imgPair F₀ a hg))
      (polar_zero_of_mem_sup (polar_hypPlane_of_orth (hc a 3 h3))
        (polar_hypPlane_of_orth (hc a 4 h4))) (polar_hypPlane_of_orth (hc a 5 h5)) x hx y hy

end Models

end CFSG.ClassicalInvolution.Q3.Q3TY
