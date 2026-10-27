module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11L
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11M
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFForm

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem false_of_conj_eight_eleven
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {a g : X} (hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hs2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1)
    (hs8 : (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 8) {x : X} (hxM : x ∈ M)
    (hxo : x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X))) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, le_normalizer hxM⟩).support.card = 4)
    (hxf : FourForm (ρ ⟨g⁻¹ * a * g, hHN hs⟩) (ρ ⟨x, le_normalizer hxM⟩)) {y : X}
    (hy2 : y * y = 1) (hyx' : y * (g * x * g⁻¹) = g * x * g⁻¹ * y)
    (hyo : y ∈ oddGen (centralizer ({g * x * g⁻¹} : Set X) ⊓ centralizer ({a} : Set X)))
    (hko : y * (g * x * g⁻¹) ∈ oddGen (centralizer ({a} : Set X) ⊓
      (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)))
    (hCk : centralizer ({y * (g * x * g⁻¹)} : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCx : centralizer ({x} : Set X) ≤ H := hA x hxM hx2 hx4
  have hxs : x * (g⁻¹ * a * g) = g⁻¹ * a * g * x :=
    mem_centralizer_singleton_iff.mp (oddGen_le _ hxo)
  have hygo : g⁻¹ * y * g ∈
      oddGen (centralizer ({x} : Set X) ⊓ centralizer ({g⁻¹ * a * g} : Set X)) := by
    have h1 := conj_mem_oddGen_inf_centralizer (g := g⁻¹) hyo
    rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  have hygC := oddGen_le _ hygo
  have hygH : g⁻¹ * y * g ∈ H := hCx hygC.1
  have hCN : centralizer ({x} : Set X) ⊓ centralizer ({g⁻¹ * a * g} : Set X) ≤
      normalizer (M : Set X) := inf_le_left.trans (hCx.trans hHN)
  have hsxN : g⁻¹ * a * g * x ∈ normalizer (M : Set X) := mul_mem (hHN hs) (le_normalizer hxM)
  have hsx2 : g⁻¹ * a * g * x * (g⁻¹ * a * g * x) = 1 := by
    calc _ = g⁻¹ * a * g * (x * (g⁻¹ * a * g)) * x := by group
      _ = g⁻¹ * a * g * (g⁻¹ * a * g * x) * x := by rw [hxs]
      _ = g⁻¹ * a * g * (g⁻¹ * a * g) * (x * x) := by group
      _ = 1 := by rw [hs2, hx2, one_mul]
  have hρsx : ρ ⟨g⁻¹ * a * g * x, hsxN⟩ =
      ρ ⟨g⁻¹ * a * g, hHN hs⟩ * ρ ⟨x, le_normalizer hxM⟩ := by
    rw [← map_mul]
    rfl
  have hσ2 : ρ ⟨g⁻¹ * a * g, hHN hs⟩ * ρ ⟨g⁻¹ * a * g, hHN hs⟩ = 1 := by
    rw [← map_mul]
    convert map_one ρ
    exact Subtype.ext hs2
  obtain ⟨i, hi, i', hi', hii', hσi', hδ⟩ : ∃ i ∈ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support,
      ∃ i' ∈ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support, i' ≠ i ∧ i' ≠ ρ ⟨g⁻¹ * a * g, hHN hs⟩ i ∧
        ρ ⟨x, le_normalizer hxM⟩ = swap i (ρ ⟨g⁻¹ * a * g, hHN hs⟩ i) *
          swap i' (ρ ⟨g⁻¹ * a * g, hHN hs⟩ i') := by
    rcases hxf with ⟨-, h⟩ | ⟨h6, -⟩
    · exact h
    · omega
  obtain ⟨hδsub, hsub⟩ := support_mul_subset_of_swap_mul_swap hσ2 hi hi' hii' hσi'
  rw [← hδ] at hδsub hsub
  have hsx4 : (ρ ⟨g⁻¹ * a * g * x, hsxN⟩).support.card ≤ 4 := by
    rw [hρsx]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hδsub, hs8, hx4] at h1
    omega
  have hCsx : centralizer ({x} : Set X) ⊓ centralizer ({g⁻¹ * a * g} : Set X) ≤
      centralizer ({g⁻¹ * a * g * x} : Set X) := by
    rintro z ⟨hzx, hzs⟩
    have h1 := mem_centralizer_singleton_iff.mp hzx
    have h2 := mem_centralizer_singleton_iff.mp hzs
    rw [mem_centralizer_singleton_iff]
    calc z * (g⁻¹ * a * g * x) = z * (g⁻¹ * a * g) * x := by group
      _ = g⁻¹ * a * g * z * x := by rw [h2]
      _ = g⁻¹ * a * g * (z * x) := by group
      _ = g⁻¹ * a * g * (x * z) := by rw [h1]
      _ = g⁻¹ * a * g * x * z := by group
  obtain ⟨b₁, hb₁, hb₁eq⟩ := rho_mem_fixAlt_of_mem_oddGen (le_normalizer hxM) hx2 hx4.le hCN
    inf_le_left hygo (hHN hygH)
  obtain ⟨b₂, hb₂, hb₂eq⟩ := rho_mem_fixAlt_of_mem_oddGen hsxN hsx2 hsx4 hCN hCsx hygo
    (hHN hygH)
  have hb₁' : (b₁ : Perm (Fin 11)) = ρ ⟨g⁻¹ * y * g, hHN hygH⟩ := hb₁eq
  have hb₂' : (b₂ : Perm (Fin 11)) = ρ ⟨g⁻¹ * y * g, hHN hygH⟩ := hb₂eq
  have hsupp : (ρ ⟨g⁻¹ * y * g, hHN hygH⟩).support ⊆ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).supportᶜ := by
    intro v hv
    have hv1 := mem_fixAlt.mp hb₁ (show v ∈ (b₁ : Perm (Fin 11)).support by rw [hb₁']; exact hv)
    have hv2 := mem_fixAlt.mp hb₂ (show v ∈ (b₂ : Perm (Fin 11)).support by rw [hb₂']; exact hv)
    rw [Finset.mem_compl, Perm.notMem_support] at hv1 hv2 ⊢
    rw [hρsx, Perm.mul_apply, hv1] at hv2
    exact hv2
  have hyg2 : g⁻¹ * y * g * (g⁻¹ * y * g) = 1 := by
    calc _ = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy2]; group
  have hρyg2 : ρ ⟨g⁻¹ * y * g, hHN hygH⟩ * ρ ⟨g⁻¹ * y * g, hHN hygH⟩ = 1 := by
    rw [← map_mul]
    convert map_one ρ
    exact Subtype.ext hyg2
  have hygA : ρ ⟨g⁻¹ * y * g, hHN hygH⟩ ∈ alternatingGroup (Fin 11) := by
    rw [← hb₁']
    exact b₁.2
  have h3 : (ρ ⟨g⁻¹ * y * g, hHN hygH⟩).support.card ≤ 3 := by
    have h1 := Finset.card_le_card hsupp
    rwa [Finset.card_compl, Fintype.card_fin, hs8] at h1
  have hρyg := eq_one_of_card_support_le_three hρyg2 hygA h3
  have hwH : g⁻¹ * y * g * x ∈ H := mul_mem hygH (hMH hxM)
  have hxyg : g⁻¹ * y * g * x = x * (g⁻¹ * y * g) := mem_centralizer_singleton_iff.mp hygC.1
  have hw2 : g⁻¹ * y * g * x * (g⁻¹ * y * g * x) = 1 := by
    calc _ = g⁻¹ * y * g * (x * (g⁻¹ * y * g)) * x := by group
      _ = g⁻¹ * y * g * (g⁻¹ * y * g * x) * x := by rw [← hxyg]
      _ = g⁻¹ * y * g * (g⁻¹ * y * g) * (x * x) := by group
      _ = 1 := by rw [hyg2, hx2, one_mul]
  have hρw : ρ ⟨g⁻¹ * y * g * x, hHN hwH⟩ = ρ ⟨x, le_normalizer hxM⟩ := by
    have h1 : ρ ⟨g⁻¹ * y * g * x, hHN hwH⟩ =
        ρ ⟨g⁻¹ * y * g, hHN hygH⟩ * ρ ⟨x, le_normalizer hxM⟩ := by
      rw [← map_mul]
      rfl
    rw [h1, hρyg, one_mul]
  have hw4 : (ρ ⟨g⁻¹ * y * g * x, hHN hwH⟩).support.card = 4 := by rw [hρw]; exact hx4
  have hw1 : ρ ⟨g⁻¹ * y * g * x, hHN hwH⟩ ≠ 1 := by
    intro h1
    rw [h1, Perm.support_one, Finset.card_empty] at hw4
    omega
  have hCw := S.centralizer_le_of_four_eleven h33 h35 hT13 hML hSch hPump hN1 hMH hMpc hJM hHN
    hsup hρ hA hwH hw2 hw4
  have hkC := oddGen_le _ hko
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc _ = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hk2 : y * (g * x * g⁻¹) * (y * (g * x * g⁻¹)) = 1 := by
    calc _ = y * (g * x * g⁻¹ * y) * (g * x * g⁻¹) := by group
      _ = y * (y * (g * x * g⁻¹)) * (g * x * g⁻¹) := by rw [← hyx']
      _ = y * y * (g * x * g⁻¹ * (g * x * g⁻¹)) := by group
      _ = 1 := by rw [hy2, hx'2, one_mul]
  obtain ⟨L, hLM, hLC, -, hLperf, ⟨θL, hθL⟩, -⟩ := exists_layer_of_kernel hMH hMpc θ hkC.2.1
    hkC.2.2 (isPGroup_zpowers_of_mul_self hk2) hCk
  set Lw := L.map (MulAut.conj g⁻¹).toMonoidHom with hLwdef
  have hLwC : Lw ≤ centralizer ({g⁻¹ * y * g * x} : Set X) := by
    have h1 := map_conj_centralizer_singleton g⁻¹ (y * (g * x * g⁻¹))
    rw [inv_inv, show g⁻¹ * (y * (g * x * g⁻¹)) * g = g⁻¹ * y * g * x by group] at h1
    rw [hLwdef, ← h1]
    exact map_mono hLC
  have hLwH : Lw ≤ H := hLwC.trans hCw
  have hLwperf : ⁅Lw, Lw⁆ = Lw := by rw [hLwdef, ← map_commutator, hLperf]
  let θLw : ↥Lw ⧸ pPrimeCore 2 ↥Lw ≃* alternatingGroup (Fin 11) :=
    (Sol78.coreQuotCongr (L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)).symm.trans θL
  have hLwK := le_coreActionKernel_of_le_centralizer_of_ne_one hρ (by norm_num) (hHN hwH) hw1
    (hLwH.trans hHN) hLwC θLw hLwperf
  obtain ⟨ρa, hρa⟩ := exists_isPermAction (M := L) (by norm_num) (by norm_num) θL
  obtain ⟨δ, hδA, hδ2, hδ4, -, -⟩ := exists_four_of_fix (1 : Perm (Fin 11))
    (by rw [Perm.support_one, Finset.card_empty]; norm_num)
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hδ4
    omega
  obtain ⟨f, hfL, -, hf2, hρaf⟩ := hρa.exists_involution_lift (by norm_num) (one_mem _)
    (one_mul 1) hδA hδ2 hδ1 (by rw [show (⟨1, one_mem _⟩ : ↥(normalizer (L : Set X))) = 1 from
      rfl, map_one, mul_one, one_mul])
  have hfM : f ∈ M := hLM hfL
  have hρf : ρ ⟨f, le_normalizer hfM⟩ = δ := by
    rw [hρ.apply_of_mem (by norm_num) ⟨f, hfM⟩, ← hθL f hfL hfM, ← hρaf]
    exact (hρa.apply_of_mem (by norm_num) ⟨f, hfL⟩).symm
  have hf4 : (ρ ⟨f, le_normalizer hfM⟩).support.card = 4 := by rw [hρf]; exact hδ4
  have hTg : (zpowers f).map (MulAut.conj g⁻¹).toMonoidHom ≤ Lw :=
    map_mono (zpowers_le.mpr hfL)
  exact S.false_of_conj_le_coreActionKernel_of_sup_zpowers h33 h35 hT13 hML hSch hMH hMpc hHN
    hsup hρ hfM (le_normalizer hfM) hf2 hf4 (hA f hfM hf2 hf4) (hTg.trans hLwH) (hTg.trans hLwK)

end Sig36

end CFSG.ComponentClassification.SolMax
