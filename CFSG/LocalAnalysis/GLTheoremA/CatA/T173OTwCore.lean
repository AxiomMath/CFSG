module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OUniFull
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OTwSU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniComp
public import CFSG.HardMathSupport.Timmesfeld.Proving.ComponentCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X CFSG.LocalAnalysis.GLTheoremA.T173A
open CFSG.SeitzReduction.TwistedE6Pilot CFSG.LieType.Chevalley.E6GraphLevi

section Certificates


theorem exists_unitary_frame_su6Levi {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    {σ : K →+* K} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {K' : Type} [Field K'] [Finite K'] (hK'card : Nat.card K' = (2 ^ f) ^ 2)
    (e₀ : ↥(su6Levi σ) ≃* UniPSU f 6 K')
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hA : IsElemAbelian p A) :
    ∃ (ψ : ↥(su6Levi σ) ≃* UniPSU f 6 K') (A_GL : Subgroup (GL (Fin 6) K')),
      UniArith p f 6 K' ∧ UniDiagFrame p f 6 K' ψ (A.subgroupOf (su6Levi σ)) A_GL := by
  have hf1 : 1 ≤ f := by omega
  have hp6 : ¬ p ∣ 6 := by
    intro h
    have h' : p ∣ 2 * 3 := by rwa [show 2 * 3 = 6 by norm_num]
    rcases hp.dvd_mul.mp h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
      omega
    · have := Nat.le_of_dvd (by norm_num : 0 < 3) h3
      omega
  have hUni : UniArith p f 6 K' :=
    ⟨hp, hpq, hp6, hK'card, hf1, by norm_num, by norm_num⟩
  obtain ⟨ψ, A_GL, hfr⟩ := uni_exists_frame hUni e₀ (hA.subgroupOf (su6Levi σ))
  exact ⟨ψ, A_GL, hUni, hfr⟩

theorem exists_component_block_su6Levi {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    {σ : K →+* K} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {K' : Type} [Field K'] [Finite K'] (hK'card : Nat.card K' = (2 ^ f) ^ 2)
    (e₀ : ↥(su6Levi σ) ≃* UniPSU f 6 K')
    {A Kb : Subgroup (ModGL TwistTag.E6.tag K)} (hAD : A ≤ su6Levi σ)
    (hA : IsElemAbelian p A) {d : ModGL TwistTag.E6.tag K} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hK' : IsComponentOf Kb
      (Subgroup.centralizer ({d} : Set (ModGL TwistTag.E6.tag K)) ⊓ su6Levi σ)) :
    ∃ (ψ : ↥(su6Levi σ) ≃* UniPSU f 6 K') (A_GL : Subgroup (GL (Fin 6) K'))
      (I : Finset (Fin 6)),
      UniArith p f 6 K' ∧ UniDiagFrame p f 6 K' ψ (A.subgroupOf (su6Levi σ)) A_GL ∧
        2 ≤ I.card ∧
        ((Kb.subgroupOf (su6Levi σ)).map ψ.toMonoidHom : Set (UniPSU f 6 K')) =
          UniBlockImage f 6 K' I := by
  let S : Subgroup (ModGL TwistTag.E6.tag K) := su6Levi σ
  let Q := ↥S
  let Bbar : Subgroup Q := A.subgroupOf S
  obtain ⟨ψ, A_GL, hUni, hfr⟩ := exists_unitary_frame_su6Levi hf hp hp5 hpq hK'card e₀ hA
  have hdS : d ∈ S := hAD hdA
  have hKS : Kb ≤ S := hK'.1.trans inf_le_right
  have hcent_eq : Subgroup.centralizer ({⟨d, hdS⟩} : Set Q) =
      (Subgroup.centralizer ({d} : Set (ModGL TwistTag.E6.tag K)) ⊓ S).subgroupOf S := by
    rw [← Subgroup.map_subtype_inj (H := S)]
    rw [CFSG.LocalAnalysis.ComponentInitial.map_subtype_centralizer_singleton]
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [inf_assoc, inf_idem]
  have hKbarAss : CFSG.Assembly.IsComponentOf (Kb.subgroupOf S)
      (Subgroup.centralizer ({⟨d, hdS⟩} : Set Q)) := by
    rw [hcent_eq,
      ← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff S.subtype_injective]
    rw [Subgroup.subgroupOf_map_subtype (Kb) S]
    rw [Subgroup.subgroupOf_map_subtype
      (Subgroup.centralizer ({d} : Set (ModGL TwistTag.E6.tag K)) ⊓ S) S]
    rw [inf_eq_left.mpr hKS, inf_assoc, inf_idem]
    exact CFSG.Assembly.isComponentOf_iff_open.mpr hK'
  have hKbar : IsComponentOf (Kb.subgroupOf S)
      (Subgroup.centralizer ({⟨d, hdS⟩} : Set Q)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hKbarAss
  have hdM : (⟨d, hdS⟩ : Q) ∈ Bbar := hdA
  have hdQ1 : (⟨d, hdS⟩ : Q) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  obtain ⟨I, hI, hKI⟩ := uni_component_support hUni hfr hdM hdQ1 hKbar
  exact ⟨ψ, A_GL, I, hUni, hfr, hI, hKI⟩

private theorem exists_split_su6Levi_in_model {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    {σ : K →+* K} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {K' : Type} [Field K'] [Finite K'] (hK'card : Nat.card K' = (2 ^ f) ^ 2)
    (e₀ : ↥(su6Levi σ) ≃* UniPSU f 6 K')
    {A Kb : Subgroup (ModGL TwistTag.E6.tag K)} (hAD : A ≤ su6Levi σ)
    (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ 5)
    {d : ModGL TwistTag.E6.tag K} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hK' : IsComponentOf Kb
      (Subgroup.centralizer ({d} : Set (ModGL TwistTag.E6.tag K)) ⊓ su6Levi σ)) :
    ∃ U : Subgroup ↥(su6Levi σ), U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ Kb.subgroupOf (su6Levi σ) ∧
      A.subgroupOf (su6Levi σ) =
        (A.subgroupOf (su6Levi σ) ⊓ Kb.subgroupOf (su6Levi σ)) ⊔
          (A.subgroupOf (su6Levi σ) ⊓ Subgroup.normalizer (U : Set ↥(su6Levi σ))) := by
  obtain ⟨ψ, A_GL, I, hUni, hfr, hI, hKI⟩ :=
    exists_component_block_su6Levi hf hp hp5 hpq hK'card e₀ hAD hA hdA hd1 hK'
  have hcardB : Nat.card (A.subgroupOf (su6Levi σ)) = p ^ (6 - 1) := by
    rw [show 6 - 1 = 5 by norm_num, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv
  obtain ⟨U, hUne, hU2, hUK, hUsplit⟩ := uni_split_of_full hUni hfr hcardB hI hKI
  exact ⟨U, hUne, hU2, hUK, hUsplit⟩

private theorem exists_split_map_back_su6Levi {K : Type} [Field K] {σ : K →+* K}
    {A Kb : Subgroup (ModGL TwistTag.E6.tag K)} (hAD : A ≤ su6Levi σ)
    (hKS : Kb ≤ su6Levi σ) {U : Subgroup ↥(su6Levi σ)} (hUne : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hUK : U ≤ Kb.subgroupOf (su6Levi σ))
    (hUsplit : A.subgroupOf (su6Levi σ) =
      (A.subgroupOf (su6Levi σ) ⊓ Kb.subgroupOf (su6Levi σ)) ⊔
        (A.subgroupOf (su6Levi σ) ⊓ Subgroup.normalizer (U : Set ↥(su6Levi σ)))) :
    ∃ T : Subgroup (ModGL TwistTag.E6.tag K), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ Kb ∧
      A = (A ⊓ Kb) ⊔ (A ⊓ Subgroup.normalizer (T : Set (ModGL TwistTag.E6.tag K))) := by
  refine ⟨U.map (su6Levi σ).subtype, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hUne
    rw [← Subgroup.map_subtype_inj (H := su6Levi σ), hbot, Subgroup.map_bot]
  · exact hU2.map (su6Levi σ).subtype
  · calc U.map (su6Levi σ).subtype ≤
        (Kb.subgroupOf (su6Levi σ)).map (su6Levi σ).subtype := Subgroup.map_mono hUK
      _ = Kb := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKS]
  · have hTsub : U.map (su6Levi σ).subtype ≤ su6Levi σ := Subgroup.map_subtype_le U
    have hTsub_eq : (U.map (su6Levi σ).subtype).subgroupOf (su6Levi σ) = U := by
      simpa only [Subgroup.comap_subtype] using
        Subgroup.comap_map_eq_self_of_injective (su6Levi σ).subtype_injective U
    have hNQ : Subgroup.normalizer (U : Set ↥(su6Levi σ)) =
        (Subgroup.normalizer (U.map (su6Levi σ).subtype :
          Set (ModGL TwistTag.E6.tag K))).subgroupOf (su6Levi σ) := by
      rw [Subgroup.subgroupOf_normalizer_eq hTsub, hTsub_eq]
    have hmap := congrArg (Subgroup.map (su6Levi σ).subtype) hUsplit
    rw [Subgroup.map_sup,
      Subgroup.map_inf (A.subgroupOf (su6Levi σ)) (Kb.subgroupOf (su6Levi σ))
        (su6Levi σ).subtype (su6Levi σ).subtype_injective,
      Subgroup.map_inf (A.subgroupOf (su6Levi σ))
        (Subgroup.normalizer (U : Set ↥(su6Levi σ)))
        (su6Levi σ).subtype (su6Levi σ).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAD, Subgroup.map_subgroupOf_eq_of_le hKS,
      hNQ, Subgroup.subgroupOf_map_subtype] at hmap
    rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hAD)] at hmap
    exact hmap

theorem split_of_le_su6Levi {f : ℕ} (hf : 2 ≤ f) {k K : Type} [Field k] [Field K]
    [Algebra k K] [Finite K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) {A Kb : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAD : A ≤ su6Levi σ) (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ 5)
    {d : ModGL TwistTag.E6.tag K} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hK' : IsComponentOf Kb
      (Subgroup.centralizer ({d} : Set (ModGL TwistTag.E6.tag K)) ⊓ su6Levi σ)) :
    ∃ T : Subgroup (ModGL TwistTag.E6.tag K), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ Kb ∧
      A = (A ⊓ Kb) ⊔ (A ⊓ Subgroup.normalizer (T : Set (ModGL TwistTag.E6.tag K))) := by
  classical
  have hf1 : 1 ≤ f := by omega
  obtain ⟨-, -, -, -, -, hModel, -⟩ := su6Levi_facts hf1 hk hK hσ
  obtain ⟨-, ⟨K', hK'field, hK'fin, hK'card, ⟨e₀⟩⟩⟩ := hModel
  letI : Field K' := hK'field
  letI : Finite K' := hK'fin
  have hKS : Kb ≤ su6Levi σ := hK'.1.trans inf_le_right
  obtain ⟨U, hUne, hU2, hUK, hUsplit⟩ :=
    exists_split_su6Levi_in_model hf hp hp5 hpq hK'card e₀ hAD hA hcard hdA hd1 hK'
  exact exists_split_map_back_su6Levi hAD hKS hUne hU2 hUK hUsplit

private theorem isComponentOf_stdLayer_map {F : Type} [Field F] {σ : F ≃+* F}
    {p : ℕ} {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hKD : (stdLayer d).map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom)
    (hd : IsStdElt p A d) :
    IsComponentOf ((stdLayer d).map (twistedE6RootGroup F σ).subtype)
      (Subgroup.centralizer
        ({((d : ↥(twistedE6RootGroup F σ)) : ModGL TwistTag.E6.tag F)} :
          Set (ModGL TwistTag.E6.tag F)) ⊓ su6Levi σ.toRingHom) := by
  let C0 : Subgroup (ModGL TwistTag.E6.tag F) := twistedE6RootGroup F σ
  let S : Subgroup (ModGL TwistTag.E6.tag F) := su6Levi σ.toRingHom
  have hSC0 : S ≤ C0 := su6Levi_le_graphFixedRootGroup σ.toRingHom
  have hcompM : IsComponentOf ((stdLayer d).map C0.subtype)
      (C0 ⊓ Subgroup.centralizer ({((d : ↥C0) : ModGL TwistTag.E6.tag F)} :
        Set (ModGL TwistTag.E6.tag F))) := by
    have hcompA : CFSG.Assembly.IsComponentOf (stdLayer d)
        (Subgroup.centralizer ({d} : Set ↥C0)) :=
      CFSG.Assembly.isComponentOf_iff_open.mpr hd.2.2.2.1
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := C0.subtype) C0.subtype_injective).mpr hcompA
    rw [CFSG.LocalAnalysis.ComponentInitial.map_subtype_centralizer_singleton] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hcompS : IsComponentOf ((stdLayer d).map C0.subtype)
      ((C0 ⊓ Subgroup.centralizer ({((d : ↥C0) : ModGL TwistTag.E6.tag F)} :
        Set (ModGL TwistTag.E6.tag F))) ⊓ S) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isComponentOf_inf_of_le hcompM hKD
  have hcompS' : IsComponentOf ((stdLayer d).map C0.subtype)
      (Subgroup.centralizer ({((d : ↥C0) : ModGL TwistTag.E6.tag F)} :
        Set (ModGL TwistTag.E6.tag F)) ⊓ S) := by
    have h := hcompS
    rw [inf_assoc, inf_eq_right.mpr (le_trans inf_le_right hSC0)] at h
    exact h
  exact hcompS'

private theorem exists_split_map_twistedE6 {f : ℕ} (hf : 2 ≤ f) {k F : Type} [Field k]
    [Field F] [Algebra k F] [Finite F] (hk : Nat.card k = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(twistedE6RootGroup F σ)} (hA : IsElemAbelian p A)
    (hcard : Nat.card A = p ^ 5) {d : ↥(twistedE6RootGroup F σ)} (hd : IsStdElt p A d)
    (hAD : A.map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom)
    (hKD : (stdLayer d).map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom) :
    ∃ T : Subgroup (ModGL TwistTag.E6.tag F), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      T ≤ (stdLayer d).map (twistedE6RootGroup F σ).subtype ∧
      A.map (twistedE6RootGroup F σ).subtype =
        (A.map (twistedE6RootGroup F σ).subtype ⊓
            (stdLayer d).map (twistedE6RootGroup F σ).subtype) ⊔
          (A.map (twistedE6RootGroup F σ).subtype ⊓
            Subgroup.normalizer (T : Set (ModGL TwistTag.E6.tag F))) := by
  have hKcomp := isComponentOf_stdLayer_map hKD hd
  have hA' : IsElemAbelian p (A.map (twistedE6RootGroup F σ).subtype) :=
    hA.map (twistedE6RootGroup F σ).subtype
  have hcard' : Nat.card (A.map (twistedE6RootGroup F σ).subtype) = p ^ 5 := by
    rw [Subgroup.card_map_of_injective (twistedE6RootGroup F σ).subtype_injective, hcard]
  have hdA' : ((d : ↥(twistedE6RootGroup F σ)) : ModGL TwistTag.E6.tag F) ∈
      A.map (twistedE6RootGroup F σ).subtype :=
    Subgroup.mem_map_of_mem (twistedE6RootGroup F σ).subtype hd.1
  have hd1' : ((d : ↥(twistedE6RootGroup F σ)) : ModGL TwistTag.E6.tag F) ≠ 1 := by
    intro h
    exact hd.2.1 (Subtype.ext h)
  exact split_of_le_su6Levi (σ := σ.toRingHom) hf hk hF hσ hp hp5 hpq hAD hA' hcard' hdA' hd1'
    hKcomp

private theorem exists_split_pullback_twistedE6 {F : Type} [Field F]
    {σ : F ≃+* F} {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hKD : (stdLayer d).map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom)
    {T : Subgroup (ModGL TwistTag.E6.tag F)} (hTne : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTK : T ≤ (stdLayer d).map (twistedE6RootGroup F σ).subtype)
    (hTsplit : A.map (twistedE6RootGroup F σ).subtype =
      (A.map (twistedE6RootGroup F σ).subtype ⊓
          (stdLayer d).map (twistedE6RootGroup F σ).subtype) ⊔
        (A.map (twistedE6RootGroup F σ).subtype ⊓
          Subgroup.normalizer (T : Set (ModGL TwistTag.E6.tag F)))) :
    ∃ T0 : Subgroup ↥(twistedE6RootGroup F σ), T0 ≠ ⊥ ∧ IsPGroup 2 T0 ∧ T0 ≤ stdLayer d ∧
      A = (A ⊓ stdLayer d) ⊔
        (A ⊓ Subgroup.normalizer (T0 : Set ↥(twistedE6RootGroup F σ))) := by
  let C0 : Subgroup (ModGL TwistTag.E6.tag F) := twistedE6RootGroup F σ
  have hSC0 : su6Levi σ.toRingHom ≤ C0 := su6Levi_le_graphFixedRootGroup σ.toRingHom
  have hTC0 : T ≤ C0 := hTK.trans (hKD.trans hSC0)
  have hT0map : (T.subgroupOf C0).map C0.subtype = T :=
    Subgroup.map_subgroupOf_eq_of_le hTC0
  have hT0ne : T.subgroupOf C0 ≠ ⊥ := by
    intro hbot
    apply hTne
    rw [← hT0map, hbot, Subgroup.map_bot]
  have hT02 : IsPGroup 2 (T.subgroupOf C0) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTC0).symm
  have hT0K : T.subgroupOf C0 ≤ stdLayer d := by
    have h : ((stdLayer d).map C0.subtype).subgroupOf C0 = stdLayer d :=
      Subgroup.comap_map_eq_self_of_injective C0.subtype_injective (stdLayer d)
    exact (Subgroup.subgroupOf_mono C0 hTK).trans (le_of_eq h)
  have hsplit0 : A = (A ⊓ stdLayer d) ⊔
      (A ⊓ Subgroup.normalizer ((T.subgroupOf C0) : Set ↥C0)) := by
    rw [← Subgroup.map_subtype_inj (H := C0)]
    rw [Subgroup.map_sup,
      Subgroup.map_inf A (stdLayer d) C0.subtype C0.subtype_injective,
      Subgroup.map_inf A (Subgroup.normalizer ((T.subgroupOf C0) : Set ↥C0))
        C0.subtype C0.subtype_injective,
      (Subgroup.subgroupOf_normalizer_eq hTC0).symm, Subgroup.subgroupOf_map_subtype]
    rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left (Subgroup.map_subtype_le A))]
    exact hTsplit
  exact ⟨T.subgroupOf C0, hT0ne, hT02, hT0K, hsplit0⟩

private theorem exists_order_p_centralizer_su6Levi {f : ℕ} (hf : 2 ≤ f) {k F : Type}
    [Field k] [Field F] [Algebra k F] [Finite F] (hk : Nat.card k = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hAD : A.map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom)
    (hKD : (stdLayer d).map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom) :
    ∃ y : ↥(twistedE6RootGroup F σ),
      y ∈ Subgroup.centralizer (A : Set ↥(twistedE6RootGroup F σ)) ∧
        y ∈ Subgroup.centralizer (stdLayer d : Set ↥(twistedE6RootGroup F σ)) ∧
          y ^ p = 1 ∧ y ∉ A := by
  let C0 : Subgroup (ModGL TwistTag.E6.tag F) := twistedE6RootGroup F σ
  obtain ⟨y, hyC0, hyS, hyp, hyS'⟩ :=
    exists_pow_eq_one_centralizer_su6Levi (σ := σ.toRingHom) (by omega : 1 ≤ f) hk hF hσ hp hpq
  let y0 : ↥C0 := ⟨y, hyC0⟩
  have hy0A : y0 ∈ Subgroup.centralizer (A : Set ↥C0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyS (a : ModGL TwistTag.E6.tag F)
      (hAD (Subgroup.mem_map_of_mem C0.subtype ha))
  have hy0K : y0 ∈ Subgroup.centralizer ((stdLayer d) : Set ↥C0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyS (x : ModGL TwistTag.E6.tag F)
      (hKD (Subgroup.mem_map_of_mem C0.subtype hx))
  have hy0p : y0 ^ p = 1 := Subtype.ext (by simpa using hyp)
  have hy0notA : y0 ∉ A := by
    intro h
    apply hyS'
    exact hAD (Subgroup.mem_map_of_mem C0.subtype h)
  exact ⟨y0, hy0A, hy0K, hy0p, hy0notA⟩

theorem stdExtendsN_of_le_su6Levi {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ 5) (hd : IsStdElt p A d)
    (hAD : A.map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom)
    (hKD : (stdLayer d).map (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom) :
    StdExtendsN p A d := by
  classical
  have hf1 : 1 ≤ f := by omega
  obtain ⟨k, hkfield, hkalg, hkcard⟩ := exists_subfield_twE6 hf1 hF
  letI : Field k := hkfield
  letI : Algebra k F := hkalg
  obtain ⟨T, hTne, hT2, hTK, hTsplit⟩ :=
    exists_split_map_twistedE6 hf hkcard hF σ hσ hp hp5 hpq hA hcard hd hAD hKD
  obtain ⟨T0, hT0ne, hT02, hT0K, hsplit0⟩ :=
    exists_split_pullback_twistedE6 hKD hTne hT2 hTK hTsplit
  obtain ⟨y0, hy0A, hy0K, hy0p, hy0notA⟩ :=
    exists_order_p_centralizer_su6Levi hf hkcard hF σ hσ hp hpq hAD hKD
  exact ⟨⟨T0, hT0ne, hT02, hT0K, hsplit0⟩, ⟨y0, hy0A, hy0K, hy0p, hy0notA⟩⟩

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
