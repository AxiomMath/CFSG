module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DExt
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem IsLThreeEps.of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsLThreeEps Y) : IsLThreeEps Y' := by
  rcases h with ⟨K, hK, hf, hc, ⟨f⟩⟩ | ⟨K, hK, hf, q, hc, hq, ⟨f⟩⟩
  · exact Or.inl ⟨K, hK, hf, hc, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨K, hK, hf, q, hc, hq, ⟨e.symm.trans f⟩⟩

section Cover

variable {G : Type} [Group G] [Finite G]

theorem isLThreeEps_barOf_congr {H H' : Subgroup G} (h : H = H')
    (h1 : IsLThreeEps (barOf 3 H)) : IsLThreeEps (barOf 3 H') := by
  subst h; exact h1

theorem barOf_equiv_of_cover {X J : Subgroup G} (hJX : J ≤ X)
    (hcov : X ≤ J ⊔ GLAPPrimeCoreOf 3 X) : Nonempty (barOf 3 J ≃* barOf 3 X) := by
  set φ : ↥J →* barOf 3 X :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Subgroup.inclusion hJX) with hφ
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with | H k => ?_
    have hk : (k : G) ∈ J ⊔ GLAPPrimeCoreOf 3 X := hcov k.2
    have hsup : (J.subgroupOf X ⊔ GLAPPrimeCore 3 ↥X).map X.subtype = J ⊔ GLAPPrimeCoreOf 3 X := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJX]
      rfl
    have hk' : k ∈ J.subgroupOf X ⊔ GLAPPrimeCore 3 ↥X := by
      rw [← Subgroup.mem_map_iff_mem X.subtype_injective, hsup]
      exact hk
    obtain ⟨j, hj, n, hn, hjn⟩ := Subgroup.mem_sup_of_normal_right.1 hk'
    refine ⟨⟨(j : G), hj⟩, ?_⟩
    have hinc : Subgroup.inclusion hJX ⟨(j : G), hj⟩ = j := rfl
    show (QuotientGroup.mk (Subgroup.inclusion hJX ⟨(j : G), hj⟩) : barOf 3 X) = QuotientGroup.mk k
    rw [hinc, ← hjn]
    simp [(QuotientGroup.eq_one_iff n).2 hn]
  have hker : φ.ker = GLAPPrimeCore 3 ↥J := by
    apply le_antisymm
    · set M : Subgroup ↥J := φ.ker with hM
      have hMn : M.Normal := MonoidHom.normal_ker φ
      have hMle : M.map (Subgroup.inclusion hJX) ≤ GLAPPrimeCore 3 ↥X := by
        rintro _ ⟨k, hk, rfl⟩
        exact (QuotientGroup.eq_one_iff _).1 hk
      have hcard : Nat.Coprime 3 (Nat.card M) := by
        have h2 : Nat.card (M.map (Subgroup.inclusion hJX)) = Nat.card M :=
          Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJX)
        have h3 := Subgroup.card_dvd_of_le hMle
        rw [h2] at h3
        exact (coprime_card_gLAPPrimeCore_aux 3 ↥X).coprime_dvd_right h3
      exact le_sSup ⟨hMn, hcard⟩
    · intro k hk
      have hN : ((GLAPPrimeCore 3 ↥J).map φ).Normal :=
        Subgroup.Normal.map inferInstance φ hsurj
      have hcard : Nat.Coprime 3 (Nat.card ((GLAPPrimeCore 3 ↥J).map φ)) :=
        (coprime_card_gLAPPrimeCore_aux 3 ↥J).coprime_dvd_right (Subgroup.card_map_dvd _ φ)
      have hle : (GLAPPrimeCore 3 ↥J).map φ ≤ GLAPPrimeCore 3 (barOf 3 X) :=
        le_sSup ⟨hN, hcard⟩
      rw [glaPPrimeCore_quotient_eq_bot Nat.prime_three, le_bot_iff] at hle
      have : φ k ∈ (GLAPPrimeCore 3 ↥J).map φ := ⟨k, hk, rfl⟩
      rw [hle, Subgroup.mem_bot] at this
      exact this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

end Cover

@[expose] def InputJLayerType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsExtremalType (barOf 3 K) → g ^ 3 = 1 →
    InducesFieldAut 3 K g →
      CLay K g = ⊥ ∨ IsLThreeEps (barOf 3 (CLay K g))

theorem inputJLayerType_of_inputs (V : InndiagVocab) (iT : InputL3T) (iF : InputL3fix V) :
    InputJLayerType := by
  intro G _ _ K g hq hext hg3 hfld
  by_cases hT : TrivOn K g
  · obtain ⟨-, hcov⟩ := iT G K g hq hg3 hT
    refine Or.inr ?_
    have hle : CLay K g ≤ K :=
      (sSup_le fun _ hL => hL.1 : GLAPLayer 3 (K ⊓ Cs g) ≤ K ⊓ Cs g).trans inf_le_left
    obtain ⟨e⟩ := barOf_equiv_of_cover hle hcov
    exact IsLThreeEps.of_mulEquiv e.symm (IsExtremalType.isLThreeEps hext)
  · have hraw : ∃ r : ℕ, ((r % 3 = 1 ∧ IsPSLn 3 r (barOf 3 K)) ∨ (r % 3 = 2 ∧ IsPSUn 3 r (barOf 3 K))) := by
      rcases hext with ⟨F, hF, hfin, h1, he⟩ | ⟨F, hF, hfin, q, h1, h2, -, he⟩
      · exact ⟨Nat.card F, Or.inl ⟨h1, F, hF, hfin, rfl, he⟩⟩
      · exact ⟨q, Or.inr ⟨h2, F, hF, hfin, h1, he⟩⟩
    obtain ⟨r, hr⟩ := hraw
    have hr' : IsL3Raw r (barOf 3 K) := by
      rcases hr with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨-, r0, hr0, h⟩ := iF G K g r hq hr' hg3 hfld hT
    rcases h with ⟨-, -, hl, hu⟩ | ⟨hbot, -, -⟩
    · refine Or.inr ?_
      have hmod : r0 ^ 3 % 3 = r0 % 3 := by
        have : r0 % 3 < 3 := Nat.mod_lt _ (by norm_num)
        rw [Nat.pow_mod]
        interval_cases h : r0 % 3 <;> simp
      rcases hr with ⟨h3, hPSL⟩ | ⟨h3, hPSU⟩
      · obtain ⟨F, hF, hfin, hcF, ⟨e⟩⟩ := hl hPSL
        refine Or.inl ⟨F, hF, hfin, ?_, ⟨e⟩⟩
        rw [hcF]
        rw [hr0] at h3
        omega
      · obtain ⟨F, hF, hfin, hcF, ⟨e⟩⟩ := hu hPSU
        refine Or.inr ⟨F, hF, hfin, r0, hcF, ?_, ⟨e⟩⟩
        rw [hr0] at h3
        omega
    · exact Or.inl hbot

theorem inputKType_of_inputs (iL3 : InputL3U3Facts) (h514 : Lemma514) (hJ : InputJLayerType) :
    InputKType := by
  intro G _ _ m hS hC B hB b L A hw x hxA hx1
  have hx : ExtCtx B b L A := exists_extCtx hS hC hB hw
  have hb3 : b ^ 3 = 1 := hx.Bel.2 b hx.b_mem
  by_cases hxb : x ∈ Subgroup.zpowers b
  · have hCen := centralizer_eq_of_mem_zpowers hb3 hx.b_ne hxb hx1
    exact isLThreeEps_barOf_congr (kOf_eq_L iL3 hx hCen).symm
      (IsExtremalType.isLThreeEps hx.ext_type)
  · have hxB : x ∈ B := hx.AB hxA
    have hx3 : x ^ 3 = 1 := hx.Bel.2 x hxB
    have hcov : kOf L A x ≤ jLayerOf L A ⊔ GLAPPrimeCoreOf 3 (kOf L A x) :=
      (h514 G m hS hC B hB b L A hw x hxA hx1).2 hxb
    obtain ⟨e⟩ := barOf_equiv_of_cover (jOf_le_kOf' L A x) hcov
    have hcomm : x * b = b * x := ea_comm hx.Bel hxB hx.b_mem
    have hne : Subgroup.zpowers x ≠ Subgroup.zpowers b := by
      intro h; apply hxb; rw [← h]; exact Subgroup.mem_zpowers x
    have h9 := card_zpowers_sup hcomm hx3 hb3 hx1 hx.b_ne hne
    have hAeq : Subgroup.zpowers x ⊔ Subgroup.zpowers b = A :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 hxA)
        (Subgroup.zpowers_le.2 hx.b_A)) (by rw [h9, hx.Ac])
    have hLC : L ⊓ Subgroup.centralizer ({x} : Set G) = L ⊓ Subgroup.centralizer (A : Set G) := by
      ext g
      constructor
      · rintro ⟨hgL, hgx⟩
        have hgb : g * b = b * g :=
          Subgroup.mem_centralizer_singleton_iff.1 (hx.L_comp.1 hgL)
        have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hgx
        have hle : A ≤ Subgroup.centralizer ({g} : Set G) := by
          rw [← hAeq]
          exact sup_le (zpowers_le_cent hgx'.symm) (zpowers_le_cent hgb.symm)
        refine ⟨hgL, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz))
      · rintro ⟨hgL, hgA⟩
        exact ⟨hgL, Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hgA x hxA).symm⟩
    have hq : CFSG.Open.IsQuasisimple (barOf 3 L) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hx.L_comp
    have hJeq : jLayerOf L A = CLay L x := by
      unfold jLayerOf CLay
      rw [hLC]
    have hlay := hJ G L x hq hx.ext_type hx3 (hx.field x hxA)
    rcases hlay with hbot | hty
    · exfalso
      have hF : B ⊓ L ≤ ⊥ := by
        rw [← hbot, ← hJeq]; exact hx.FJ
      have h1 : Nat.card ↥(B ⊓ L) = 1 := by
        rw [eq_bot_iff.2 hF]; exact Subgroup.card_bot
      rw [hx.Fc] at h1
      omega
    · exact IsLThreeEps.of_mulEquiv e (isLThreeEps_barOf_congr hJeq.symm hty)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
