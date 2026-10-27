module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11I
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCI

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem conj_mem_oddGen_inf_centralizer {u v g y : X}
    (hy : y ∈ oddGen (centralizer ({u} : Set X) ⊓ centralizer ({v} : Set X))) :
    g * y * g⁻¹ ∈
      oddGen (centralizer ({g * u * g⁻¹} : Set X) ⊓ centralizer ({g * v * g⁻¹} : Set X)) := by
  change y ∈ Subgroup.closure _ at hy
  induction hy using closure_induction with
  | mem z hz =>
    refine mem_oddGen ⟨mem_centralizer_conj_iff.mp hz.1.1, mem_centralizer_conj_iff.mp hz.1.2⟩ ?_
    rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, MulEquiv.orderOf_eq]
    exact hz.2
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul y z _ _ hy hz =>
    have h : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [h]
    exact mul_mem hy hz
  | inv y _ hy =>
    have h : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem hy

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem centralizer_le_of_four_eleven
    (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {w : X} (hwH : w ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hw2 : w * w = 1)
    (hw4 : (ρ ⟨w, hHN hwH⟩).support.card = 4) :
    centralizer ({w} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  obtain ⟨S₀, hS₀H, hS₀C, -, hS₀card⟩ := S.card_two_eq_of_sup h33 h35 hT13 hML hSch hMH hMpc
    hHN θ hsup
  obtain ⟨h, hhH, hhS⟩ := exists_conj_mem_of_card_eq_of_le hS₀H hS₀card hwH hw2
  set c := h * w * h⁻¹ with hcdef
  have hcH : c ∈ H := mul_mem (mul_mem hhH hwH) (inv_mem hhH)
  have hc2 : c * c = 1 := by
    calc c * c = h * (w * w) * h⁻¹ := by rw [hcdef]; group
      _ = 1 := by rw [hw2]; group
  have hct : c ∈ centralizer ({t} : Set X) := hS₀C hhS
  have hc4 : (ρ ⟨c, hHN hcH⟩).support.card = 4 := by
    have h1 : (⟨c, hHN hcH⟩ : ↥(normalizer (M : Set X))) =
        ⟨h, hHN hhH⟩ * ⟨w, hHN hwH⟩ * (⟨h, hHN hhH⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, Perm.card_support_conj, hw4]
  have hcJ : c ∈ normalizer (J : Set X) := S.centralizer_le_normalizer hT13 hML hSch hct
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  have hcJ4 : (ρJ ⟨c, hcJ⟩).support.card = 4 := by
    rw [← card_support_rho_eq_rhoJ (by norm_num) hJM hsup hρ hρJ hcJ (hHN hcH)]
    exact hc4
  obtain ⟨L₀, F, -, -, -, hL₀C, -, hFL₀, hFJ, hF4, hFsq, ⟨DF, hDF, hFs⟩, -, -⟩ :=
    S.exists_fixed_layer_seven_of_four hρJ hcJ hc2 hcJ4
  have hFc : F ≤ centralizer ({c} : Set X) := hFL₀.trans (hL₀C.trans inf_le_right)
  have hFel : CFSG.Open.IsElemAbelian 2 F := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun u hu => by rw [sq]; exact hFsq u hu⟩
    have hu := hFsq _ u.2
    have hv := hFsq _ v.2
    have huv : (u : X) * v * ((u : X) * v) = 1 := hFsq _ (mul_mem u.2 v.2)
    change (u : X) * v = v * u
    calc (u : X) * v = ((u : X) * v)⁻¹ := (inv_eq_of_mul_eq_one_right huv).symm
      _ = (v : X)⁻¹ * (u : X)⁻¹ := mul_inv_rev _ _
      _ = v * u := by rw [inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hu]
  set Oc := (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype
    with hOcdef
  have hOcodd : Nat.Coprime 2 (Nat.card Oc) := by
    rw [hOcdef, card_map_of_injective (centralizer ({c} : Set X)).subtype_injective]
    exact pPrimeCore_coprime_card
  have hFOc : F ≤ normalizer (Oc : Set X) := fun f hf =>
    le_normalizer_pPrimeCore (le_normalizer (hFc hf))
  have hOC : Oc ≤ H := by
    have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
      Nat.prime_two F Oc hFel (by rw [hF4]; norm_num) hFOc hOcodd
    rw [← hgen]
    refine iSup₂_le fun T hT => ?_
    obtain ⟨hTF, hTcard⟩ := hT
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
    obtain ⟨⟨v, hvT⟩, hv1⟩ := exists_ne (1 : T)
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hvF := hTF hvT
    have hv2 : v * v = 1 := hFsq v hvF
    have hv4 : (ρ ⟨v, le_normalizer (hJM (hFJ hvF))⟩).support.card = 4 := by
      have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ (hFJ hvF)
      rw [card_support_coreImage_of_four e (hFJ hvF) hv2 hv1' hDF
        (fun ω hω => hFs ⟨v, hFJ hvF⟩ hvF ω hω)] at h1
      exact h1
    exact inf_le_right.trans ((centralizer_le (Set.singleton_subset_iff.mpr hvT)).trans
      (hA v (hJM (hFJ hvF)) hv2 hv4))
  have hCc : centralizer ({c} : Set X) ≤ H := S.centralizer_le_of_four_of_oddCore h33 h35 hT13
    hML hSch hPump hN1 hMH hMpc hJM hHN hsup hρ hcH hc2 hct hc4 hOC
  intro z hz
  have h1 : h * z * h⁻¹ ∈ centralizer ({c} : Set X) := mem_centralizer_conj_iff.mp hz
  have h2 : z = h⁻¹ * (h * z * h⁻¹) * h := by group
  rw [h2]
  exact mul_mem (mul_mem (inv_mem hhH) (hCc h1)) hhH

end Sig36

end CFSG.ComponentClassification.SolMax
