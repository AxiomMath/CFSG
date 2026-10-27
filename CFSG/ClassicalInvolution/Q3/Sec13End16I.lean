module

public import CFSG.ClassicalInvolution.Q3.Sec13End16H
public import CFSG.ClassicalInvolution.Q3.Sec13EndPolar16B

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

private theorem e16i_map_conjSub' {X Q : Type*} [Group X] [Group Q] (φ : X →* Q) (x : X)
    (M : Subgroup X) : (conjSub x M).map φ = conjSub (φ x) (M.map φ) := by
  ext q
  simp only [Subgroup.mem_map, mem_conjSub_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨x⁻¹ * y * x, hy, by simp only [map_mul, map_inv]⟩
  · rintro ⟨m, hm, hmq⟩
    refine ⟨x * m * x⁻¹, ?_, ?_⟩
    · rw [show x⁻¹ * (x * m * x⁻¹) * x = m by group]
      exact hm
    · rw [map_mul, map_mul, map_inv, hmq]
      group

private theorem e16i_map_conjSub {X : Subgroup G} {L : Subgroup G} {n : ℕ}
    (φ : ↥X →* AE.AEQ n) (x : ↥X) :
    ((conjSub (x : G) L).subgroupOf X).map φ = conjSub (φ x) ((L.subgroupOf X).map φ) := by
  rw [← conjSub_subgroupOf X x L]
  exact e16i_map_conjSub' φ x (L.subgroupOf X)

private theorem e16i_conjSub_eq_self {Q : Type*} [Group Q] {M : Subgroup Q} {q : Q}
    (hq : q⁻¹ = q) (hM : ∀ x ∈ M, q * x * q⁻¹ ∈ M) : conjSub q M = M := by
  have hqq : q * q = 1 := by
    have := mul_inv_cancel q
    rwa [hq] at this
  ext m
  rw [mem_conjSub_iff, hq]
  constructor
  · intro hm
    have h1 := hM _ hm
    rw [hq, show q * (q * m * q) * q = m by
      rw [show q * (q * m * q) * q = (q * q) * m * (q * q) by group, hqq, one_mul, mul_one]] at h1
    exact h1
  · intro hm
    have h1 := hM m hm
    rwa [hq] at h1

private theorem e16i_zBar_normalizes {n : ℕ} (hn : 5 ≤ n) {α β : Finset (Fin n)}
    (hα : α.card = 4) (hβ : β.card = 4) (hαβ : (α ∩ β).card = 2) (b : Bool) :
    ∀ x ∈ AE.memBar α hα b, AE.zBar β hβ * x * (AE.zBar β hβ)⁻¹ ∈ AE.memBar α hα b := by
  rw [TC.Thin.zBar_eq_vbar_indv β hβ]
  refine (AE.vec_normalizes_memBar_iff hn α hα b (TC.Thin.indv β)).mpr ?_
  unfold TC.Thin.indv
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, hαβ]
  rfl

private theorem e16i_exists_inter {n : ℕ} (hn : 6 ≤ n) {α : Finset (Fin n)} (hα : α.card = 4) :
    ∃ β : Finset (Fin n), ∃ hβ : β.card = 4, (α ∩ β).card = 2 := by
  obtain ⟨S, hSα, hS⟩ := Finset.exists_subset_card_eq (s := α) (n := 2) (by omega)
  obtain ⟨T, hTα, hT⟩ := Finset.exists_subset_card_eq (s := αᶜ) (n := 2) (by
    rw [Finset.card_compl, Fintype.card_fin, hα]; omega)
  have hdisj : Disjoint S T :=
    Finset.disjoint_of_subset_left hSα (Finset.disjoint_of_subset_right hTα disjoint_compl_right)
  have hβ : (S ∪ T).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj, hS, hT]
  refine ⟨S ∪ T, hβ, ?_⟩
  have hI : α ∩ (S ∪ T) = S := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hi, hi'⟩
      rcases hi' with hi' | hi'
      · exact hi'
      · exact absurd hi (Finset.mem_compl.mp (hTα hi'))
    · intro hi
      exact ⟨hSα hi, Or.inl hi⟩
  rw [hI, hS]

private theorem e16i_e64_inter {α : Finset (Fin 7)} (hα : α ∈ AE.e64Sets) :
    ∃ β ∈ AE.e64Sets, ∃ hβ : β.card = 4, (α ∩ β).card = 2 := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  have hex : ∀ ℓ ∈ AE.fanoLines, ∃ m ∈ AE.fanoLines, m ≠ ℓ := by decide +kernel
  have hint : ∀ ℓ ∈ AE.fanoLines, ∀ m ∈ AE.fanoLines, ℓ ≠ m → (ℓᶜ ∩ mᶜ).card = 2 := by
    decide +kernel
  obtain ⟨m, hm, hmℓ⟩ := hex ℓ hℓ
  refine ⟨mᶜ, ⟨m, hm, rfl⟩, AE.fanoLines_compl_card m hm, ?_⟩
  exact hint ℓ hℓ m hm (Ne.symm hmℓ)

private theorem e16i_map_injective {Ω : Set (Subgroup G)} (h : StarHyp Ω) {P : Set (Subgroup G)}
    (hP : P ⊆ Ω) {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan P)) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (he : (L.subgroupOf (pSpan P)).map φ = (L'.subgroupOf (pSpan P)).map φ) : L = L' := by
  by_contra hne
  have key : ∀ l' ∈ L', ∃ l ∈ L, ∃ c : G, (∀ y ∈ pSpan P, c * y = y * c) ∧ l' = l * c := by
    intro l' hl'
    have hx : φ ⟨l', le_pSpan hL' hl'⟩ ∈ (L.subgroupOf (pSpan P)).map φ := by
      rw [he]
      exact ⟨⟨l', le_pSpan hL' hl'⟩, Subgroup.mem_subgroupOf.mpr hl', rfl⟩
    obtain ⟨w, hw, hwe⟩ := hx
    have hk : w⁻¹ * ⟨l', le_pSpan hL' hl'⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
    refine ⟨(w : G), Subgroup.mem_subgroupOf.mp hw, (w : G)⁻¹ * l',
      fun y hy => ?_, (mul_inv_cancel_left _ _).symm⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp (hker hk) ⟨y, hy⟩)).symm
  have hN : L' ≤ Subgroup.normalizer (L : Set G) := by
    intro l' hl'
    obtain ⟨l, hl, c, hc, rfl⟩ := key l' hl'
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer hl)
      (Subgroup.centralizer_le_normalizer _ ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hc x (le_pSpan hL hx)).symm
  have hL2 := h.thmD.two L (hP hL)
  have hL'2 := h.thmD.two L' (hP hL')
  obtain ⟨S, hS⟩ := (hL'2.to_sup_of_normal_right' hL2 hN).exists_le_sylow
  have hcomm : Commutes L L' := Q3CP.l67Gen G Ω h.thmD.hyp S L
    (TC.mem_RSet_of_isPGroup (hP hL) hL2) L' (TC.mem_RSet_of_isPGroup (hP hL') hL'2)
    (le_sup_right.trans hS) (le_sup_left.trans hS) hne
  obtain ⟨v, hv, hvc⟩ := Sec6Gen.exists_noncentral h.thmD.hyp (hP hL') le_rfl hL'2
    (by rw [h.thmD.card L' (hP hL')]; norm_num)
  refine hvc fun w hw => ?_
  obtain ⟨l, hl, c, hc, rfl⟩ := key w hw
  calc v * (l * c) = v * l * c := (mul_assoc _ _ _).symm
    _ = l * v * c := by rw [hcomm l hl v hv]
    _ = l * (v * c) := mul_assoc _ _ _
    _ = l * (c * v) := by rw [hc v (le_pSpan hL' hv)]
    _ = l * c * v := (mul_assoc _ _ _).symm

private theorem e16i_core {Ω : Set (Subgroup G)} (h : EndHyp Ω) (h9 : Perp9 Ω)
    {P : Set (Subgroup G)} (hP : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≠ 8)
    (φ : ↥(pSpan P) →* AE.AEQ n) (hker : φ.ker ≤ Subgroup.center ↥(pSpan P))
    {J R : Subgroup G} (hJ : J ∈ P) (hR : R ∈ P)
    {α β : Finset (Fin n)} {hα : α.card = 4} {hβ : β.card = 4} {b b' : Bool}
    (hJlab : (J.subgroupOf (pSpan P)).map φ = AE.memBar α hα b)
    (hRlab : (R.subgroupOf (pSpan P)).map φ = AE.memBar β hβ b')
    (hαβ : (α ∩ β).card = 2) :
    R ∈ omegaStarNbr Ω J ∧ R ∉ twinSet Ω J := by
  have hJΩ : J ∈ Ω := hP hJ
  have hRΩ : R ∈ Ω := hP hR
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hRΩ
  have hzP : z ∈ pSpan P := le_pSpan hR hz.mem
  have hzR : φ ⟨z, hzP⟩ = AE.zBar β hβ :=
    TC.Thin.phi_map_eq_zBar φ hn5 hR (EndHyp.card_eq_eight h hRΩ) hRlab hz
  have hzinv : (AE.zBar β hβ)⁻¹ = AE.zBar β hβ :=
    inv_eq_of_mul_eq_one_right (AE.zBar_mul_self β hβ)
  have hconjP : conjSub z J ∈ P := hinv J hJ z hzP
  have himg : ((conjSub z J).subgroupOf (pSpan P)).map φ = (J.subgroupOf (pSpan P)).map φ := by
    have hm := e16i_map_conjSub (L := J) φ ⟨z, hzP⟩
    dsimp only at hm
    rw [hm, hJlab, hzR]
    exact e16i_conjSub_eq_self hzinv (e16i_zBar_normalizes hn5 hα hβ hαβ b)
  have hJeq : conjSub z J = J := e16i_map_injective h.toStarHyp hP φ hker hconjP hJ himg
  have hzN : z ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hJeq
  have hnot : R ∉ twinSet Ω J := by
    rintro ⟨-, z', hzJ, hzR'⟩
    have h1 := TC.Thin.phi_map_eq_zBar φ hn5 hJ (EndHyp.card_eq_eight h hJΩ) hJlab hzJ
    have h2 := TC.Thin.phi_map_eq_zBar φ hn5 hR (EndHyp.card_eq_eight h hRΩ) hRlab hzR'
    have hαβeq : α = β := AE.eq_of_zBar_eq hn8 (h1.symm.trans h2)
    subst hαβeq
    rw [Finset.inter_self] at hαβ
    omega
  rcases EndHyp.mem_omegaStarNbr_or_twinSet h h9 hJΩ hRΩ hz hzN with hstar | htw
  · exact ⟨hstar, hnot⟩
  · exact absurd htw hnot

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem sectionOutcomeRestricted_centMembers_u
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    SectionOutcomeRestricted (centMembers Ω u) := by
  have hK' : K' ∈ Ω := by
    have hm : K' ∈ twinSet Ω K := by rw [c.twin.twin]; simp
    exact hm.1
  have hR : conjSub g K ∈ centMembers Ω u :=
    Generic.mem_centMembers.mpr ⟨h.thmD.hyp.conjInvariant g K c.twin.mem,
      (conjSub_le_centralizer_u c h h9).1⟩
  have hR' : conjSub g K' ∈ centMembers Ω u :=
    Generic.mem_centMembers.mpr ⟨h.thmD.hyp.conjInvariant g K' hK',
      (conjSub_le_centralizer_u c h h9).2⟩
  have hs : TwinSit Ω (conjSub g K) (conjSub g K') (u * e) := by
    have := TwinSit.conj c.twin h.thmD.hyp.conjInvariant g
    rwa [c.data.hgt] at this
  rcases EndHyp.centMembers_cases h h9 c.data.hu1 hs hR hR' with h1 | h1
  · exact absurd h1 (centMembers_u_ne_pair c h h9 h13)
  · exact h1.2

private theorem e16ia_mem_map_iff {Γ : Type} [Group Γ] (σ : Γ ≃* Γ) {K : Subgroup Γ} {x : Γ} :
    x ∈ K.map σ.toMonoidHom ↔ σ.symm x ∈ K :=
  Subgroup.mem_map_equiv

private theorem e16ia_mem_map_symm_iff {Γ : Type} [Group Γ] (σ : Γ ≃* Γ) {K : Subgroup Γ}
    {x : Γ} : x ∈ K.map σ.symm.toMonoidHom ↔ σ x ∈ K :=
  Subgroup.mem_map_equiv

private theorem e16ia_map_map_symm {Γ : Type} [Group Γ] (σ : Γ ≃* Γ) (K : Subgroup Γ) :
    (K.map σ.toMonoidHom).map σ.symm.toMonoidHom = K := by
  ext x
  rw [e16ia_mem_map_symm_iff, e16ia_mem_map_iff, MulEquiv.symm_apply_apply]

private theorem e16ia_map_symm_map {Γ : Type} [Group Γ] (σ : Γ ≃* Γ) (K : Subgroup Γ) :
    (K.map σ.symm.toMonoidHom).map σ.toMonoidHom = K := by
  ext x
  rw [e16ia_mem_map_iff, e16ia_mem_map_symm_iff, MulEquiv.apply_symm_apply]

section AutTransport

variable {Γ : Type} [Group Γ]

private theorem e16ia_RSet_map {𝓕 : Set (Subgroup Γ)} (σ : Γ ≃* Γ)
    (hσ : ∀ L ∈ 𝓕, L.map σ.toMonoidHom ∈ 𝓕) {R : Subgroup Γ} (hR : R ∈ RSet 𝓕) :
    R.map σ.toMonoidHom ∈ RSet 𝓕 := by
  obtain ⟨J, hJ, hRJ, hR2, hmax⟩ := mem_RSet_iff.mp hR
  refine mem_RSet_iff.mpr ⟨J.map σ.toMonoidHom, hσ J hJ, Subgroup.map_mono hRJ, hR2.map _, ?_⟩
  intro R' hR'J hR'2 hle
  have hR''J : R'.map σ.symm.toMonoidHom ≤ J := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have := hR'J hv
    rw [e16ia_mem_map_iff] at this
    exact this
  have hRR'' : R ≤ R'.map σ.symm.toMonoidHom := by
    intro x hx
    rw [e16ia_mem_map_symm_iff]
    exact hle (Subgroup.mem_map_of_mem _ hx)
  have h1 := hmax (R'.map σ.symm.toMonoidHom) hR''J (hR'2.map _) hRR''
  calc R' = (R'.map σ.symm.toMonoidHom).map σ.toMonoidHom := (e16ia_map_symm_map σ R').symm
    _ = R.map σ.toMonoidHom := by rw [h1]

private theorem e16ia_USet_map {𝓕 : Set (Subgroup Γ)} (σ : Γ ≃* Γ)
    (hσ : ∀ L ∈ 𝓕, L.map σ.toMonoidHom ∈ 𝓕) {U : Subgroup Γ} (hU : U ∈ USet 𝓕) :
    U.map σ.toMonoidHom ∈ USet 𝓕 := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  refine ⟨R.map σ.toMonoidHom, e16ia_RSet_map σ hσ hR, Subgroup.map_mono hUR, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U σ.toMonoidHom σ.injective)).mp hcyc
  · rw [Subgroup.relIndex_map_map_of_injective _ _ σ.injective]
    exact hidx

private theorem e16ia_inDistinct_image {𝓕 : Set (Subgroup Γ)} (σ : Γ ≃* Γ)
    (hσ' : ∀ L ∈ 𝓕, L.map σ.symm.toMonoidHom ∈ 𝓕) {η : Set (Subgroup Γ)}
    (h : InDistinctMembers 𝓕 η) :
    InDistinctMembers 𝓕 ((fun U : Subgroup Γ => U.map σ.toMonoidHom) '' η) := by
  rintro _ ⟨U, hU, rfl⟩ _ ⟨U', hU', rfl⟩ hne J hJ ⟨h1, h2⟩
  have hne' : U ≠ U' := fun h' => hne (by rw [h'])
  refine h U hU U' hU' hne' (J.map σ.symm.toMonoidHom) (hσ' J hJ) ⟨?_, ?_⟩
  · intro x hx
    rw [e16ia_mem_map_symm_iff]
    exact h1 (Subgroup.mem_map_of_mem _ hx)
  · intro x hx
    rw [e16ia_mem_map_symm_iff]
    exact h2 (Subgroup.mem_map_of_mem _ hx)

private theorem e16ia_etaSet_map {𝓕 : Set (Subgroup Γ)} (σ : Γ ≃* Γ)
    (hσ : ∀ L ∈ 𝓕, L.map σ.toMonoidHom ∈ 𝓕) (hσ' : ∀ L ∈ 𝓕, L.map σ.symm.toMonoidHom ∈ 𝓕)
    {S : Subgroup Γ} {η : Set (Subgroup Γ)} (h : η ∈ etaSet 𝓕 S) :
    (fun U : Subgroup Γ => U.map σ.toMonoidHom) '' η ∈ etaSet 𝓕 (S.map σ.toMonoidHom) := by
  have hinj : Function.Injective (fun U : Subgroup Γ => U.map σ.toMonoidHom) := by
    intro U V hUV
    have := congrArg (fun K : Subgroup Γ => K.map σ.symm.toMonoidHom) hUV
    simpa only [e16ia_map_map_symm] using this
  have hinj' : Function.Injective (fun U : Subgroup Γ => U.map σ.symm.toMonoidHom) := by
    intro U V hUV
    have := congrArg (fun K : Subgroup Γ => K.map σ.toMonoidHom) hUV
    simpa only [e16ia_map_symm_map] using this
  refine ⟨?_, e16ia_inDistinct_image σ hσ' h.2.1, fun η' hη' hd => ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨e16ia_USet_map σ hσ (h.1 hU).1, Subgroup.map_mono (h.1 hU).2⟩
  · have hη'' : (fun U : Subgroup Γ => U.map σ.symm.toMonoidHom) '' η' ⊆
        {U | U ∈ USet 𝓕 ∧ U ≤ S} := by
      rintro _ ⟨V, hV, rfl⟩
      obtain ⟨hVU, hVS⟩ := hη' hV
      refine ⟨e16ia_USet_map σ.symm hσ' hVU, ?_⟩
      calc V.map σ.symm.toMonoidHom ≤ (S.map σ.toMonoidHom).map σ.symm.toMonoidHom :=
            Subgroup.map_mono hVS
        _ = S := e16ia_map_map_symm σ S
    have hσσ : ∀ L ∈ 𝓕, L.map σ.symm.symm.toMonoidHom ∈ 𝓕 := hσ
    have hd'' := e16ia_inDistinct_image σ.symm hσσ hd
    have hle := h.2.2 _ hη'' hd''
    rw [Set.ncard_image_of_injective η' hinj'] at hle
    rw [Set.ncard_image_of_injective η hinj]
    exact hle

private theorem e16ia_etaG_map {𝓕 : Set (Subgroup Γ)} (σ : Γ ≃* Γ)
    (hσ : ∀ L ∈ 𝓕, L.map σ.toMonoidHom ∈ 𝓕) (hσ' : ∀ L ∈ 𝓕, L.map σ.symm.toMonoidHom ∈ 𝓕)
    {η : Set (Subgroup Γ)} (h : η ∈ etaG 𝓕) :
    (fun U : Subgroup Γ => U.map σ.toMonoidHom) '' η ∈ etaG 𝓕 := by
  obtain ⟨S, hS, hinv⟩ := h
  let S' : Sylow 2 Γ :=
    { toSubgroup := S.map σ.toMonoidHom
      isPGroup' := S.isPGroup'.map _
      is_maximal' := by
        intro Q hQ hle
        have h1 : (S : Subgroup Γ) ≤ Q.map σ.symm.toMonoidHom := by
          intro x hx
          rw [e16ia_mem_map_symm_iff]
          exact hle (Subgroup.mem_map_of_mem _ hx)
        have h2 := S.is_maximal' (hQ.map _) h1
        rw [← e16ia_map_symm_map σ Q, h2] }
  refine ⟨S', e16ia_etaSet_map σ hσ hσ' hS, ?_⟩
  rintro s' hs' _ ⟨U, hU, rfl⟩
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
  refine ⟨conjSub s U, hinv s hs U hU, ?_⟩
  simp only [conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private theorem e16ia_WSet_map {𝓕 : Set (Subgroup Γ)} (σ : Γ ≃* Γ)
    (hσ : ∀ L ∈ 𝓕, L.map σ.toMonoidHom ∈ 𝓕) (hσ' : ∀ L ∈ 𝓕, L.map σ.symm.toMonoidHom ∈ 𝓕)
    {W : Subgroup Γ} (hW : W ∈ WSet 𝓕) : W.map σ.toMonoidHom ∈ WSet 𝓕 := by
  obtain ⟨η, hη, rfl⟩ := hW
  refine ⟨_, e16ia_etaG_map σ hσ hσ' hη, ?_⟩
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun U hU => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_biSup (fun V : Subgroup Γ => V) (Set.mem_image_of_mem _ hU)
  · refine iSup₂_le fun V hV => ?_
    obtain ⟨U, hU, rfl⟩ := hV
    exact Subgroup.map_mono (le_biSup (fun V : Subgroup Γ => V) hU)

end AutTransport

private def e16ia_conjEquiv {Γ : Type} [Group Γ] (Y : Subgroup Γ) (g : Γ)
    (hY : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) (hY' : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) : Y ≃* Y where
  toFun x := ⟨g * x * g⁻¹, hY x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, hY' x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x₁ x₂ := Subtype.ext (by simp [mul_assoc])

private theorem e16ia_map_subgroupOf_conj {Γ : Type} [Group Γ] {Y : Subgroup Γ} {g : Γ}
    (hY : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) (hY' : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) (L : Subgroup Γ) :
    (L.subgroupOf Y).map (e16ia_conjEquiv Y g hY hY').toMonoidHom =
      (conjSub g L).subgroupOf Y := by
  ext x
  rw [e16ia_mem_map_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSub_iff]
  rfl

private theorem e16ia_map_subgroupOf_conj_symm {Γ : Type} [Group Γ] {Y : Subgroup Γ} {g : Γ}
    (hY : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) (hY' : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) (L : Subgroup Γ) :
    (L.subgroupOf Y).map (e16ia_conjEquiv Y g hY hY').symm.toMonoidHom =
      (conjSub g⁻¹ L).subgroupOf Y := by
  ext x
  rw [e16ia_mem_map_symm_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSub_iff,
    inv_inv]
  rfl

private theorem e16ia_restrict_family_conj {Γ : Type} [Group Γ] {P : Set (Subgroup Γ)}
    {Y : Subgroup Γ} (hLY : ∀ L ∈ P, L ≤ Y) {g : Γ} (hg : ∀ L ∈ P, conjSub g L ∈ P)
    (hg' : ∀ L ∈ P, conjSub g⁻¹ L ∈ P) (hY : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y)
    (hY' : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) :
    (∀ L ∈ restrictFamily P Y,
        L.map (e16ia_conjEquiv Y g hY hY').toMonoidHom ∈ restrictFamily P Y) ∧
    (∀ L ∈ restrictFamily P Y,
        L.map (e16ia_conjEquiv Y g hY hY').symm.toMonoidHom ∈ restrictFamily P Y) := by
  constructor
  · rintro _ ⟨L, hL, -, rfl⟩
    exact ⟨conjSub g L, hg L hL, hLY _ (hg L hL), e16ia_map_subgroupOf_conj hY hY' L⟩
  · rintro _ ⟨L, hL, -, rfl⟩
    exact ⟨conjSub g⁻¹ L, hg' L hL, hLY _ (hg' L hL), e16ia_map_subgroupOf_conj_symm hY hY' L⟩

private theorem e16ia_map_conjEquiv_subtype {Γ : Type} [Group Γ] (Y : Subgroup Γ) (g : Γ)
    (hY : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) (hY' : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) (K : Subgroup Y) :
    (K.map (e16ia_conjEquiv Y g hY hY').toMonoidHom).map Y.subtype =
      conjSub g (K.map Y.subtype) := by
  simp only [conjSub, Subgroup.map_map]
  congr 1

private theorem e16ia_inv_comm {Γ : Type} [Group Γ] {u g₀ : Γ} (hg : g₀ * u = u * g₀) :
    g₀⁻¹ * u = u * g₀⁻¹ := by
  calc g₀⁻¹ * u = g₀⁻¹ * (u * g₀) * g₀⁻¹ := by group
    _ = g₀⁻¹ * (g₀ * u) * g₀⁻¹ := by rw [hg]
    _ = u * g₀⁻¹ := by group

private theorem e16ia_conjSub_pSpan_le {Γ : Type} [Group Γ] {P : Set (Subgroup Γ)} {g₀ : Γ}
    (hP : ∀ L ∈ P, conjSub g₀ L ∈ P) : conjSub g₀ (pSpan P) ≤ pSpan P := by
  unfold pSpan
  rw [conjSub_iSup₂]
  exact iSup₂_le fun L hL => le_pSpan (hP L hL)

private theorem e16ia_conjSub_centMembers {Γ : Type} [Group Γ] [Finite Γ] {Ω : Set (Subgroup Γ)}
    (h : EndHyp Ω) {u g₀ : Γ} (hg : g₀ * u = u * g₀) {L : Subgroup Γ}
    (hL : L ∈ centMembers Ω u) : conjSub g₀ L ∈ centMembers Ω u := by
  have hg' : g₀⁻¹ * u = u * g₀⁻¹ := e16ia_inv_comm hg
  refine Generic.mem_centMembers.mpr
    ⟨h.thmD.hyp.conjInvariant g₀ L (Generic.mem_centMembers.mp hL).1, ?_⟩
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [mem_conjSub_iff] at hx
  have hl := Subgroup.mem_centralizer_singleton_iff.mp ((Generic.mem_centMembers.mp hL).2 hx)
  set l := g₀⁻¹ * x * g₀ with hl_def
  have hx' : x = g₀ * l * g₀⁻¹ := by rw [hl_def]; group
  rw [hx']
  calc g₀ * l * g₀⁻¹ * u = g₀ * l * (g₀⁻¹ * u) := by group
    _ = g₀ * l * (u * g₀⁻¹) := by rw [hg']
    _ = g₀ * (l * u) * g₀⁻¹ := by group
    _ = g₀ * (u * l) * g₀⁻¹ := by rw [hl]
    _ = (g₀ * u) * l * g₀⁻¹ := by group
    _ = (u * g₀) * l * g₀⁻¹ := by rw [hg]
    _ = u * (g₀ * l * g₀⁻¹) := by group

private theorem e16ia_inv_memAt (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool) {v : AE.Wr 6}
    (hv : v ∈ AE.memAt α hα b) (hsq : v * v = 1) : v = 1 ∨ v = AE.zOf (AE.emb α hα) := by
  cases b with
  | false => exact AE.eq_of_mem_memKStar_mul_self (AE.emb α hα) v hv hsq
  | true => exact AE.eq_of_mem_memK_mul_self (AE.emb α hα) v hv hsq

private theorem e16ia_yOf_conj_memAt (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool)
    {v : AE.Wr 6} (hv : v ∈ AE.memAt α hα b) :
    AE.yOf (AE.emb α hα) * v * (AE.yOf (AE.emb α hα))⁻¹ ∈ AE.memAt α hα b := by
  cases b with
  | false => exact AE.yOf_conj_mem_memKStar _ v hv
  | true => exact AE.yOf_conj_mem_memK _ v hv

private theorem e16ia_fix_kList : ∀ a ∈ AE.kList,
    AE.yQ * a = a * AE.yQ → a = 1 ∨ a = AE.zQ := by decide +kernel

private theorem e16ia_fix_kStarList : ∀ a ∈ AE.kStarList,
    AE.yQ * a = a * AE.yQ → a = 1 ∨ a = AE.zQ := by decide +kernel

private theorem e16ia_centralizer_memAt (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool)
    {v : AE.Wr 6} (hv : v ∈ AE.memAt α hα b)
    (hc : AE.yOf (AE.emb α hα) * v = v * AE.yOf (AE.emb α hα)) :
    v = 1 ∨ v = AE.zOf (AE.emb α hα) := by
  cases b with
  | false =>
    change v ∈ AE.memKStar (AE.emb α hα) at hv
    unfold AE.memKStar at hv
    obtain ⟨a, ha, rfl⟩ := hv
    unfold AE.yOf at hc
    rw [← map_mul, ← map_mul] at hc
    have hya := AE.embed_injective _ hc
    rcases e16ia_fix_kStarList a (AE.mem_kQStar.mp ha) hya with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  | true =>
    change v ∈ AE.memK (AE.emb α hα) at hv
    unfold AE.memK at hv
    obtain ⟨a, ha, rfl⟩ := hv
    unfold AE.yOf at hc
    rw [← map_mul, ← map_mul] at hc
    have hya := AE.embed_injective _ hc
    rcases e16ia_fix_kList a (AE.mem_kQ.mp ha) hya with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl

private theorem e16ia_cube {Γ : Type} [Group Γ] (y a : Γ) (hy : y * y * y = 1)
    (ha : orderOf a = 4) (hmem : y * a * y⁻¹ ∈ Subgroup.zpowers a) : y * a = a * y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have ha4 : a ^ (4 : ℕ) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hmod : a ^ (k % 4) = y * a * y⁻¹ := by
    rw [← hk]
    have := zpow_mod_orderOf a k
    rw [ha] at this
    exact_mod_cast this
  have hr0 : 0 ≤ k % 4 := Int.emod_nonneg _ (by norm_num)
  have hr1 : k % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = k % 4 := ⟨_, rfl⟩
  rw [← hm] at hmod hr0 hr1
  have hsq_contra : a * a = 1 → False := fun hsq => by
    have hsq2 : a ^ 2 = 1 := by rw [pow_two]; exact hsq
    have hdvd := orderOf_dvd_of_pow_eq_one hsq2
    rw [ha] at hdvd
    norm_num at hdvd
  interval_cases m
  ·
    rw [zpow_zero] at hmod
    have h1 : a = 1 := conj_eq_one_iff.mp hmod.symm
    rw [h1, orderOf_one] at ha
    norm_num at ha
  · rw [zpow_one] at hmod
    calc y * a = (y * a * y⁻¹) * y := by group
      _ = a * y := by rw [← hmod]
  ·
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at hmod
    have h1 : y * a ^ 2 * y⁻¹ = 1 := by
      rw [← conj_pow, ← hmod, ← pow_mul]
      exact ha4
    exact (hsq_contra (by rw [← pow_two]; exact conj_eq_one_iff.mp h1)).elim
  ·
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at hmod
    have h3 : a ^ 3 * a = 1 := by rw [← pow_succ]; exact ha4
    have hinv3 : a ^ 3 = a⁻¹ := eq_inv_of_mul_eq_one_left h3
    have c1 : y * a * y⁻¹ = a⁻¹ := by rw [← hmod, hinv3]
    have c2 : y * a⁻¹ * y⁻¹ = a := by
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e, c1, inv_inv]
    have s3 : y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ = a⁻¹ := by rw [c1, c2, c1]
    have s3' : y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ = a := by
      have e : y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * a * (y * y * y)⁻¹ := by
        group
      rw [e, hy, inv_one, mul_one, one_mul]
    have hainv : a⁻¹ = a := s3.symm.trans s3'
    exact (hsq_contra (mul_eq_one_iff_eq_inv.mpr hainv.symm)).elim

theorem false_of_uniqueW_Y (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hW : ∃ W₀ : Subgroup G,
      WIn (centMembers Ω u) (pSpan (centMembers Ω u)) = {W₀}) : False := by
  obtain ⟨W₀, hW₀⟩ := hW
  have hKΩ : K ∈ Ω := c.twin.mem
  have hJΩ : conjSub g K ∈ Ω := h.thmD.hyp.conjInvariant g K hKΩ
  have hJP : conjSub g K ∈ centMembers Ω u :=
    Generic.mem_centMembers.mpr ⟨hJΩ, (conjSub_le_centralizer_u c h h9).1⟩
  have htz : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := c.twin.isInv.conj g
  have heW : e ∈ W := by
    have h1 : e ∈ Subgroup.closure ({e} : Set G) := Subgroup.subset_closure rfl
    rw [c.data.he] at h1
    exact (Subgroup.mem_inf.mp h1).1
  have htW : g * z * g⁻¹ ∈ W := by
    rw [c.data.hgt]
    exact W.mul_mem c.data.huW heW
  have hJe : conjSub g K ∈ centMembers Ω e :=
    c.dSet_subset_centMembers h (h.mem_dSet_of_mem c.data.hW hJΩ htz htW)
  have htJ : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub c.twin.isInv.mem
  have hu : u = (g * z * g⁻¹) * e := by
    rw [c.data.hgt, mul_assoc, c.data.he2, mul_one]
  set P := centMembers Ω u with hPdef
  set Y := pSpan P with hYdef
  set J := conjSub g K with hJdef
  set t := g * z * g⁻¹ with htdef
  obtain ⟨I, ψ, -, -, hlab, ⟨heX, hψe⟩, -⟩ := exists_equiv_X c h h9 h13
  obtain ⟨α, hα, b, hJlab⟩ := I.label J hJe
  have hJψ := hlab J hJe α hα b hJlab
  have hchar : ∀ w : ↥(pSpan (centMembers Ω e)),
      (w : G) ∈ J ↔ ((ψ w : ↥(AE.aeSub 6)) : AE.Wr 6) ∈ AE.memAt α hα b := by
    intro w
    constructor
    · intro hw
      rw [← hJψ]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw))
    · intro hw
      rw [← hJψ, Subgroup.mem_map] at hw
      obtain ⟨v, hv, hvw⟩ := hw
      obtain ⟨x, hx, hxv⟩ := Subgroup.mem_map.mp hv
      have hxw : x = w := ψ.injective (hxv.trans (Subtype.ext hvw))
      rw [← hxw]
      exact Subgroup.mem_subgroupOf.mp hx
  have htX : t ∈ pSpan (centMembers Ω e) := le_pSpan hJe htJ
  set tX : ↥(pSpan (centMembers Ω e)) := ⟨t, htX⟩ with htXdef
  have hψt : ((ψ tX : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
    have hmem : ((ψ tX : ↥(AE.aeSub 6)) : AE.Wr 6) ∈ AE.memAt α hα b := (hchar tX).mp htJ
    have htt : tX * tX = 1 := Subtype.ext htz.sq
    have hψsq : ψ tX * ψ tX = 1 := by rw [← map_mul, htt, map_one]
    have hsq : ((ψ tX : ↥(AE.aeSub 6)) : AE.Wr 6) * ((ψ tX : ↥(AE.aeSub 6)) : AE.Wr 6) = 1 := by
      have := congrArg Subtype.val hψsq
      simpa using this
    have hne : ((ψ tX : ↥(AE.aeSub 6)) : AE.Wr 6) ≠ 1 := by
      intro h1
      have h2 : ψ tX = 1 := Subtype.ext h1
      have h3 : tX = 1 := ψ.injective (by rw [h2, map_one])
      exact htz.ne_one (congrArg Subtype.val h3)
    exact (e16ia_inv_memAt α hα b hmem hsq).resolve_left hne
  set eX : ↥(pSpan (centMembers Ω e)) := ⟨e, heX⟩ with heXdef
  have hψe' : ((ψ eX : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.Wr.allOnes 6 := hψe
  let yA : ↥(AE.aeSub 6) := ⟨AE.yOf (AE.emb α hα), AE.yOf_mem_aeSub _⟩
  set yX : ↥(pSpan (centMembers Ω e)) := ψ.symm yA with hyXdef
  have hψy : ((ψ yX : ↥(AE.aeSub 6)) : AE.Wr 6) = AE.yOf (AE.emb α hα) := by
    rw [hyXdef, MulEquiv.apply_symm_apply]
  have hyt : yX * tX = tX * yX := by
    apply ψ.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, hψy, hψt]
    exact AE.yOf_comm_zOf _
  have hye : yX * eX = eX * yX := by
    apply ψ.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, hψy, hψe']
    exact (AE.Wr.allOnes_comm _).symm
  have hyG_t : (yX : G) * t = t * yX := congrArg Subtype.val hyt
  have hyG_e : (yX : G) * e = e * yX := congrArg Subtype.val hye
  have hyG_u : (yX : G) * u = u * yX := by
    rw [hu]
    calc (yX : G) * (t * e) = ((yX : G) * t) * e := (mul_assoc _ _ _).symm
      _ = (t * (yX : G)) * e := by rw [hyG_t]
      _ = t * ((yX : G) * e) := mul_assoc _ _ _
      _ = t * (e * (yX : G)) := by rw [hyG_e]
      _ = (t * e) * (yX : G) := (mul_assoc _ _ _).symm
  have hyG3 : (yX : G) * yX * yX = 1 := by
    have h1 : yX * yX * yX = 1 := by
      apply ψ.injective
      apply Subtype.ext
      simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, hψy]
      exact AE.yOf_pow_three _
    exact congrArg Subtype.val h1
  have hJnorm : ∀ j ∈ J, (yX : G) * j * (yX : G)⁻¹ ∈ J := by
    intro j hj
    have hjX : j ∈ pSpan (centMembers Ω e) := le_pSpan hJe hj
    have h1 : ((ψ ⟨j, hjX⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) ∈ AE.memAt α hα b := (hchar ⟨j, hjX⟩).mp hj
    have h2 := e16ia_yOf_conj_memAt α hα b h1
    have h3 : ((yX * ⟨j, hjX⟩ * yX⁻¹ : ↥(pSpan (centMembers Ω e))) : G) ∈ J := by
      apply (hchar _).mpr
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψy]
      exact h2
    exact h3
  have hPΩ : ∀ L ∈ P, L ∈ Ω := fun L hL => (Generic.mem_centMembers.mp hL).1
  have hLY : ∀ L ∈ P, L ≤ Y := fun L hL => le_pSpan hL
  have hPy : ∀ L ∈ P, conjSub (yX : G) L ∈ P :=
    fun L hL => e16ia_conjSub_centMembers h hyG_u hL
  have hPy' : ∀ L ∈ P, conjSub (yX : G)⁻¹ L ∈ P :=
    fun L hL => e16ia_conjSub_centMembers h (e16ia_inv_comm hyG_u) hL
  have hYy : conjSub (yX : G) Y ≤ Y := e16ia_conjSub_pSpan_le hPy
  have hYy' : conjSub (yX : G)⁻¹ Y ≤ Y := e16ia_conjSub_pSpan_le hPy'
  have hY1 : ∀ x ∈ Y, (yX : G) * x * (yX : G)⁻¹ ∈ Y := fun x hx => hYy (conj_mem_conjSub hx)
  have hY2 : ∀ x ∈ Y, (yX : G)⁻¹ * x * (yX : G) ∈ Y := by
    intro x hx
    have h1 := hYy' (conj_mem_conjSub (n := (yX : G)⁻¹) hx)
    rwa [inv_inv] at h1
  obtain ⟨hσF, hσF'⟩ := e16ia_restrict_family_conj hLY hPy hPy' hY1 hY2
  have hW₀mem : W₀ ∈ WIn P Y := by rw [hW₀]; exact Set.mem_singleton W₀
  obtain ⟨Wq, hWq, hWqW⟩ := hW₀mem
  have hWqW' : Wq.map Y.subtype = W₀ := hWqW
  have hWσ : Wq.map (e16ia_conjEquiv Y (yX : G) hY1 hY2).toMonoidHom ∈ WSet (restrictFamily P Y) :=
    e16ia_WSet_map _ hσF hσF' hWq
  have hWσW : ((Wq.map (e16ia_conjEquiv Y (yX : G) hY1 hY2).toMonoidHom).map Y.subtype) = W₀ := by
    have hmem : ((Wq.map (e16ia_conjEquiv Y (yX : G) hY1 hY2).toMonoidHom).map Y.subtype) ∈
        WIn P Y := ⟨_, hWσ, rfl⟩
    rw [hW₀] at hmem
    exact hmem
  have hconjW : conjSub (yX : G) W₀ = W₀ := by
    calc conjSub (yX : G) W₀ = conjSub (yX : G) (Wq.map Y.subtype) := by rw [hWqW']
      _ = ((Wq.map (e16ia_conjEquiv Y (yX : G) hY1 hY2).toMonoidHom).map Y.subtype) :=
          (e16ia_map_conjEquiv_subtype Y (yX : G) hY1 hY2 Wq).symm
      _ = W₀ := hWσW
  have h2P : ∀ L ∈ P,
      Subgroup.closure {x : G | x ∈ L ∧ IsPGroup 2 (Subgroup.zpowers x)} = L := by
    intro L hL
    apply le_antisymm
    · exact Subgroup.closure_le _ |>.mpr fun x hx => hx.1
    · intro x hx
      exact Subgroup.subset_closure
        ⟨hx, (h.thmD.two L (hPΩ L hL)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  have hQ : HypOmegaGen (restrictFamily P Y) :=
    TL4.hypOmegaGen_restrict_of Y hLY
      (fun n hn L hL => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hn)
      (fun L hL => h.thmD.hyp.omega1 L (hPΩ L hL)) h2P
      (fun K hK J' hJ' => h.thmD.hyp.omega3 K (hPΩ K hK) J' (hPΩ J' hJ'))
      (fun K hK J' hJ' hne => h.thmD.hyp.omega4 K (hPΩ K hK) J' (hPΩ J' hJ') hne)
      (fun K hK J' hJ' hne => h.thmD.hyp.omega5 K (hPΩ K hK) J' (hPΩ J' hJ') hne)
  have hJY : J ≤ Y := le_pSpan hJP
  have hJ'Q : J.subgroupOf Y ∈ restrictFamily P Y := ⟨J, hJP, hJY, rfl⟩
  have hJ'2 : IsPGroup 2 (J.subgroupOf Y) := (h.thmD.two J hJΩ).comap_subtype
  obtain ⟨S₁, hS₁⟩ := hJ'2.exists_le_sylow
  obtain ⟨η₁, hη₁, hinv₁⟩ := Sec6Gen.exists_invariant_mem_etaSet hQ S₁
  have hηG : η₁ ∈ etaG (restrictFamily P Y) := ⟨S₁, hη₁, hinv₁⟩
  have hηle : ∀ V ∈ η₁, V ≤ (S₁ : Subgroup Y) := fun V hV => (hη₁.1 hV).2
  have hJcard : Nat.card ↥(J.subgroupOf Y) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv, h.card_eq_eight hJΩ]
  have h611 := Sec6Gen.l6_11Gen ↥Y (restrictFamily P Y) hQ S₁ η₁ hηG hηle (J.subgroupOf Y) hJ'Q
    (by rw [inf_eq_left.mpr hS₁, hJcard]; norm_num)
  have hW₁ : (⨆ V ∈ η₁, V) ∈ WSet (restrictFamily P Y) := ⟨η₁, hηG, rfl⟩
  have hW₁W : (⨆ V ∈ η₁, V).map Y.subtype = W₀ := by
    have hmem : (⨆ V ∈ η₁, V).map Y.subtype ∈ WIn P Y := ⟨_, hW₁, rfl⟩
    rw [hW₀] at hmem
    exact hmem
  have hU₀ : J.subgroupOf Y ⊓ (⨆ V ∈ η₁, V) ∈ USet (restrictFamily P Y) := (hη₁.1 h611).1
  obtain ⟨R₀, -, J₀, hJ₀, hRJ₀, -, hcyc, hcardR, -⟩ := Sec6Gen.exists_data_of_mem_USet hQ hU₀
  have hR₀8 : Nat.card ↥R₀ = 8 := by
    obtain ⟨L, hL, -, hJ₀eq⟩ := hJ₀
    subst hJ₀eq
    have h2L : IsPGroup 2 (L.subgroupOf Y) := (h.thmD.two L (hPΩ L hL)).comap_subtype
    have hRL : L.subgroupOf Y = R₀ := hRJ₀.2.2 _ le_rfl h2L hRJ₀.1
    rw [← hRL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hLY L hL)).toEquiv,
      h.card_eq_eight (hPΩ L hL)]
  have hU₀card : Nat.card ↥(J.subgroupOf Y ⊓ (⨆ V ∈ η₁, V)) = 4 := by omega
  have hCeq : (J.subgroupOf Y ⊓ (⨆ V ∈ η₁, V)).map Y.subtype = J ⊓ W₀ := by
    rw [Subgroup.map_inf_eq _ _ _ Y.subtype_injective, Subgroup.subgroupOf_map_subtype, hW₁W,
      inf_eq_left.mpr hJY]
  have hequiv := Subgroup.equivMapOfInjective (J.subgroupOf Y ⊓ (⨆ V ∈ η₁, V)) Y.subtype
    Y.subtype_injective
  have hCcyc : IsCyclic ↥(J ⊓ W₀) := by
    rw [← hCeq]
    exact (MulEquiv.isCyclic hequiv).mp hcyc
  have hC4 : Nat.card ↥(J ⊓ W₀) = 4 := by
    rw [← hCeq, ← Nat.card_congr hequiv.toEquiv]
    exact hU₀card
  haveI := hCcyc
  obtain ⟨a', ha'⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(J ⊓ W₀))
  rw [hC4] at ha'
  obtain ⟨a, ha_def⟩ : ∃ a : G, a = (a' : G) := ⟨_, rfl⟩
  have ha4 : orderOf a = 4 := by rw [ha_def, Subgroup.orderOf_coe, ha']
  have haJ : a ∈ J := by rw [ha_def]; exact (Subgroup.mem_inf.mp a'.2).1
  have haW : a ∈ W₀ := by rw [ha_def]; exact (Subgroup.mem_inf.mp a'.2).2
  have hzp : Subgroup.zpowers a = J ⊓ W₀ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨haJ, haW⟩
    · rw [hC4, Nat.card_zpowers, ha4]
  have hyCa : (yX : G) * a * (yX : G)⁻¹ ∈ Subgroup.zpowers a := by
    rw [hzp]
    refine Subgroup.mem_inf.mpr ⟨hJnorm a haJ, ?_⟩
    have h1 := conj_mem_conjSub (n := (yX : G)) haW
    rw [hconjW] at h1
    exact h1
  have hcomm : (yX : G) * a = a * (yX : G) := e16ia_cube (yX : G) a hyG3 ha4 hyCa
  have haX : a ∈ pSpan (centMembers Ω e) := le_pSpan hJe haJ
  set aX : ↥(pSpan (centMembers Ω e)) := ⟨a, haX⟩ with haXdef
  have hcomm_ψ : AE.yOf (AE.emb α hα) * ((ψ aX : ↥(AE.aeSub 6)) : AE.Wr 6) =
      ((ψ aX : ↥(AE.aeSub 6)) : AE.Wr 6) * AE.yOf (AE.emb α hα) := by
    have h1 : yX * aX = aX * yX := Subtype.ext hcomm
    have h2 := congrArg (fun v : ↥(pSpan (centMembers Ω e)) =>
      ((ψ v : ↥(AE.aeSub 6)) : AE.Wr 6)) h1
    simp only [map_mul, Subgroup.coe_mul, hψy] at h2
    exact h2
  rcases e16ia_centralizer_memAt α hα b ((hchar aX).mp haJ) hcomm_ψ with h1 | h1
  · have h2 : ψ aX = 1 := Subtype.ext h1
    have h3 : aX = 1 := ψ.injective (by rw [h2, map_one])
    have h4 : a = 1 := congrArg Subtype.val h3
    rw [h4, orderOf_one] at ha4
    norm_num at ha4
  · have h2 : aX = tX := ψ.injective (Subtype.ext (h1.trans hψt.symm))
    have h3 : a = t := congrArg Subtype.val h2
    have hsq : a * a = 1 := by rw [h3]; exact htz.sq
    have hsq2 : a ^ 2 = 1 := by rw [pow_two]; exact hsq
    have hdvd := orderOf_dvd_of_pow_eq_one hsq2
    rw [ha4] at hdvd
    norm_num at hdvd

theorem exists_adjacent_Y (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hn : (∃ n : ℕ, 6 ≤ n ∧ n ≤ 7 ∧ Nonempty (AEIdent (centMembers Ω u) n)) ∨
      Nonempty (AEIdentOn (centMembers Ω u) 7 AE.e64Sets AE.e64Sub)) :
    ∃ R ∈ centMembers Ω u, R ∈ omegaStarNbr Ω (conjSub g K) ∧
      R ∉ twinSet Ω (conjSub g K) := by
  have hJP : conjSub g K ∈ centMembers Ω u :=
    Generic.mem_centMembers.mpr ⟨h.thmD.hyp.conjInvariant g K c.twin.mem,
      (conjSub_le_centralizer_u c h h9).1⟩
  have hinv : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u :=
    fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx
  have hPΩ : centMembers Ω u ⊆ Ω := fun L hL => (Generic.mem_centMembers.mp hL).1
  rcases hn with ⟨n, hn6, hn7, hI⟩ | hI
  · obtain ⟨I⟩ := hI
    obtain ⟨α, hα, b, hJlab⟩ := I.label _ hJP
    obtain ⟨β, hβ, hαβ⟩ := e16i_exists_inter hn6 hα
    obtain ⟨R, hR, hRlab⟩ := I.label_surj β hβ b
    exact ⟨R, hR, e16i_core h h9 hPΩ hinv (by omega) (by omega) I.φ I.ker_le hJP hR hJlab
      hRlab hαβ⟩
  · obtain ⟨I⟩ := hI
    obtain ⟨α, hα𝒜, hα, b, hJlab⟩ := I.label _ hJP
    obtain ⟨β, hβ𝒜, hβ, hαβ⟩ := e16i_e64_inter hα𝒜
    obtain ⟨R, hR, hRlab⟩ := I.label_surj β hβ𝒜 hβ b
    exact ⟨R, hR, e16i_core h h9 hPΩ hinv (by norm_num) (by norm_num) I.φ I.ker_le hJP hR
      hJlab hRlab hαβ⟩

theorem exists_section_le_centMembers_u
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hn : (∃ n : ℕ, 6 ≤ n ∧ n ≤ 7 ∧ Nonempty (AEIdent (centMembers Ω u) n)) ∨
      Nonempty (AEIdentOn (centMembers Ω u) 7 AE.e64Sets AE.e64Sub)) :
    ∃ (W' : Subgroup G) (u' e' g' : G),
      Sit16 Ω (conjSub g K) (conjSub g K') W' (u * e) u' e' g' ∧
        centMembers Ω e' ⊆ centMembers Ω u ∧ e' ≠ e := by
  obtain ⟨R, hRu, hRω, hRtw⟩ := exists_adjacent_Y c h h9 h13 hn
  obtain ⟨W', u', e', g', c', hRW', -⟩ :=
    exists_frame_of_omegaStarNbr (conj_frame c h h9) h h9 hRω
  have h13' : zGroup Ω ≠ eGroup Ω (conjSub g K) :=
    EndHyp.zGroup_ne_eGroup_conj h c.twin.mem h13 g
  have hJW' : conjSub g K ∈ DSet Ω W' :=
    h.mem_dSet_of_mem c'.data.hW c'.twin.mem c'.twin.isInv c'.data.hzW
  have hlam := lambdaW_eq_of_mem c' h h9 h13' hJW' hRW' hRtw
  have hlamc := lambdaW_eq_centralizer c' h h9 h13'
  have hJu : ∀ m ∈ conjSub g K, m * u = u * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mp ((conjSub_le_centralizer_u c h h9).1 hm)
  have hRu' : ∀ m ∈ R, m * u = u * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mp ((Generic.mem_centMembers.mp hRu).2 hm)
  have hu_lam : u ∈ lambdaW Ω W' := by
    rw [hlam]
    exact ⟨⟨(u_mem_zGroup c h h9 h13).1, Subgroup.mem_centralizer_iff.mpr hJu⟩,
      Subgroup.mem_centralizer_iff.mpr hRu'⟩
  rw [hlamc] at hu_lam
  have hX : u ∈ Subgroup.centralizer ((pSpan (centMembers Ω e') : Subgroup G) : Set G) :=
    hu_lam.2
  have hsub : centMembers Ω e' ⊆ centMembers Ω u := by
    intro L hL
    refine Generic.mem_centMembers.mpr ⟨(Generic.mem_centMembers.mp hL).1, ?_⟩
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hX m (le_pSpan hL hm))
  refine ⟨W', u', e', g', c', hsub, fun hee => ?_⟩
  apply not_mem_centMembers_u c h h9 h13
  apply hsub
  rw [hee]
  exact dSet_subset_centMembers c h
    (h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW)

theorem false_of_e64_Y (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hn : Nonempty (AEIdentOn (centMembers Ω u) 7 AE.e64Sets AE.e64Sub)) : False := by
  obtain ⟨W', u', e', g', c', hsub, -⟩ :=
    exists_section_le_centMembers_u c h h9 h13 (Or.inr hn)
  have h13' : zGroup Ω ≠ eGroup Ω (conjSub g K) :=
    EndHyp.zGroup_ne_eGroup_conj h c.twin.mem h13 g
  obtain ⟨I, -⟩ := exists_equiv_X c' h h9 h13'
  have h6 : (centMembers Ω e').ncard = 30 := by
    have := EndHyp.ncard_eq_of_aeIdent h (fun L hL => (Generic.mem_centMembers.mp hL).1)
      (fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx)
      (EndHyp.oddCore_centMembers_eq_bot h h9 c'.twin h13' (u_mem_zGroup c' h h9 h13').2
        c'.data.he1)
      (by norm_num) (by norm_num) I
    rw [this]
    rfl
  obtain ⟨I7⟩ := hn
  have h14 : (centMembers Ω u).ncard = 14 :=
    EndHyp.ncard_eq_fourteen_of_e64 h (fun L hL => (Generic.mem_centMembers.mp hL).1)
      (fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx)
      (EndHyp.oddCore_centMembers_eq_bot h h9 c.twin h13 (u_mem_zGroup c h h9 h13).1
        c.data.hu1) I7
  have hle := Set.ncard_le_ncard hsub
  omega

private def e16ib_ind (α : Finset (Fin 6)) : Fin 6 → ZMod 2 :=
  fun i => if i ∈ α then 1 else 0

private theorem e16ib_zOf_eq (α : Finset (Fin 6)) (hα : α.card = 4) :
    AE.zOf (AE.emb α hα) = AE.Wr.ofVec (e16ib_ind α) := by
  refine AE.Wr.ext (funext fun i => ?_) ?_
  · rw [AE.zOf_vec_apply]
    simp [e16ib_ind, AE.range_emb, AE.Wr.ofVec]
  · rw [AE.zOf_perm]
    rfl

private theorem e16ib_ofVec_mul (v w : Fin 6 → ZMod 2) :
    AE.Wr.ofVec v * AE.Wr.ofVec w = AE.Wr.ofVec (v + w) := by
  refine AE.Wr.ext ?_ ?_
  · funext i
    simp only [AE.Wr.ofVec, AE.Wr.mul_vec, Pi.add_apply]
    rfl
  · simp [AE.Wr.ofVec, AE.Wr.mul_perm]

private theorem e16ib_ind_add (α β : Finset (Fin 6)) :
    e16ib_ind β + e16ib_ind α = e16ib_ind (symmDiff α β) := by
  funext i
  simp only [e16ib_ind, Pi.add_apply, Finset.mem_symmDiff]
  by_cases hα : i ∈ α <;> by_cases hβ : i ∈ β <;> simp [hα, hβ] <;> decide

private theorem e16ib_sum_ind (γ α : Finset (Fin 6)) :
    ∑ i ∈ γ, e16ib_ind α i = ((γ ∩ α).card : ZMod 2) := by
  simp only [e16ib_ind]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]

private theorem e16ib_c0 : ∀ α β : Finset (Fin 6), α.card = 4 → β.card = 4 →
    2 ≤ (α ∩ β).card ∧ ((α ∩ β).card = 4 → α = β) := by
  decide +kernel

private theorem e16ib_c1 : ∀ β : Finset (Fin 6), β.card = 4 →
    (Finset.univ.filter fun α : Finset (Fin 6) => α.card = 4 ∧ (α ∩ β).card = 2).card = 6 := by
  decide +kernel

private theorem e16ib_c2 :
    ∀ β ∈ (Finset.univ : Finset (Finset (Fin 6))).filter (fun β => β.card = 4),
    ∀ α ∈ (Finset.univ : Finset (Finset (Fin 6))).filter
      (fun α => α.card = 4 ∧ (α ∩ β).card = 2),
    ∀ γ ∈ (Finset.univ : Finset (Finset (Fin 6))).filter
      (fun γ => γ.card = 4 ∧ (γ ∩ β).card = 2),
    α ≠ γ → γ ≠ symmDiff α β → (α ∩ γ).card % 2 = 1 := by
  decide +kernel

private theorem e16ib_c3 : ∀ α β : Finset (Fin 6), α.card = 4 → β.card = 4 →
    (α ∩ β).card = 2 → (symmDiff α β).card = 4 ∧ (symmDiff α β ∩ β).card = 2 := by
  decide +kernel

private theorem e16ib_inv_eq {e₀ : G} (I : AEIdent (centMembers Ω e₀) 6)
    (ψ : ↥(pSpan (centMembers Ω e₀)) ≃* ↥(AE.aeSub 6))
    (hmem : ∀ L ∈ centMembers Ω e₀, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (centMembers Ω e₀))).map I.φ = AE.memBar α hα b →
        ((L.subgroupOf (pSpan (centMembers Ω e₀))).map ψ.toMonoidHom).map (AE.aeSub 6).subtype =
          AE.memAt α hα b)
    {L : Subgroup G} (hL : L ∈ centMembers Ω e₀) {α : Finset (Fin 6)} {hα : α.card = 4}
    {b : Bool} (hLα : (L.subgroupOf (pSpan (centMembers Ω e₀))).map I.φ = AE.memBar α hα b)
    {r : G} (hr : r ∈ pSpan (centMembers Ω e₀)) (hLr : IsUniqueInvolution L r) :
    (ψ ⟨r, hr⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
  have hmemS : (ψ ⟨r, hr⟩ : AE.Wr 6) ∈ AE.memAt α hα b := by
    rw [← hmem L hL α hα b hLα]
    refine Subgroup.mem_map.mpr ⟨ψ ⟨r, hr⟩, Subgroup.mem_map.mpr ⟨⟨r, hr⟩, ?_, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hLr.mem
  have hsq : (ψ ⟨r, hr⟩ : AE.Wr 6) * (ψ ⟨r, hr⟩ : AE.Wr 6) = 1 := by
    have h1 : ψ ⟨r, hr⟩ * ψ ⟨r, hr⟩ = 1 := by
      rw [← map_mul]
      have h2 : (⟨r, hr⟩ : pSpan (centMembers Ω e₀)) * ⟨r, hr⟩ = 1 :=
        Subtype.ext (by simp [hLr.sq])
      rw [h2, map_one]
    exact congrArg Subtype.val h1
  rcases AE.eq_of_mem_memAt_mul_self hmemS hsq with h3 | h3
  · exfalso
    have h4 : ψ ⟨r, hr⟩ = 1 := Subtype.ext h3
    have h5 : (⟨r, hr⟩ : pSpan (centMembers Ω e₀)) = 1 := ψ.injective (by rw [h4, map_one])
    exact hLr.ne_one (congrArg Subtype.val h5)
  · exact h3

private theorem e16ib_link {e₀ : G} (hS : StarHyp Ω) (I : AEIdent (centMembers Ω e₀) 6)
    (hinv : ∀ L ∈ centMembers Ω e₀, ∀ x ∈ pSpan (centMembers Ω e₀),
      conjSub x L ∈ centMembers Ω e₀)
    (hΩ : centMembers Ω e₀ ⊆ Ω) {L : Subgroup G} (hL : L ∈ centMembers Ω e₀)
    {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hLα : (L.subgroupOf (pSpan (centMembers Ω e₀))).map I.φ = AE.memBar α hα b)
    {w : G} (hw : w ∈ pSpan (centMembers Ω e₀)) :
    w ∈ Subgroup.normalizer (L : Set G) ↔
      ∀ x ∈ AE.memBar α hα b, I.φ ⟨w, hw⟩ * x * (I.φ ⟨w, hw⟩)⁻¹ ∈ AE.memBar α hα b := by
  constructor
  · intro hn x hx
    rw [← hLα] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨w, hw⟩ * y * (⟨w, hw⟩)⁻¹, ?_, ?_⟩
    · apply Subgroup.mem_subgroupOf.mpr
      exact (Subgroup.mem_normalizer_iff.mp hn (y : G)).mp (Subgroup.mem_subgroupOf.mp hy)
    · simp only [map_mul, map_inv]
  · intro H
    have hL' : conjSub w L ∈ centMembers Ω e₀ := hinv L hL w hw
    have hsub : (AE.memBar α hα b).map (MulAut.conj (I.φ ⟨w, hw⟩)).toMonoidHom ≤
        AE.memBar α hα b := by
      rintro _ ⟨m, hm, rfl⟩
      exact H m hm
    have heq2 : (AE.memBar α hα b).map (MulAut.conj (I.φ ⟨w, hw⟩)).toMonoidHom =
        AE.memBar α hα b :=
      Subgroup.eq_of_le_of_card_ge hsub (le_of_eq
        (Subgroup.card_map_of_injective (f := (MulAut.conj (I.φ ⟨w, hw⟩)).toMonoidHom)
          (MulAut.conj (I.φ ⟨w, hw⟩)).injective).symm)
    have himg : ((conjSub w L).subgroupOf (pSpan (centMembers Ω e₀))).map I.φ =
        AE.memBar α hα b := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        have hyL : w⁻¹ * (y : G) * w ∈ L := by
          have := Subgroup.mem_subgroupOf.mp hy
          rwa [mem_conjSub_iff] at this
        have hℓX : w⁻¹ * (y : G) * w ∈ pSpan (centMembers Ω e₀) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) y.2) hw
        set ℓ : ↥(pSpan (centMembers Ω e₀)) := ⟨w⁻¹ * (y : G) * w, hℓX⟩ with hℓ
        have hℓmem : I.φ ℓ ∈ AE.memBar α hα b := by
          rw [← hLα]
          exact ⟨ℓ, Subgroup.mem_subgroupOf.mpr hyL, rfl⟩
        have hy_eq : (⟨w, hw⟩ : ↥(pSpan (centMembers Ω e₀))) * ℓ * (⟨w, hw⟩)⁻¹ = y :=
          Subtype.ext (by simp [hℓ, mul_assoc])
        have := H (I.φ ℓ) hℓmem
        rw [← hy_eq]
        simpa only [map_mul, map_inv] using this
      · intro x hx
        have hx' : x ∈ (AE.memBar α hα b).map (MulAut.conj (I.φ ⟨w, hw⟩)).toMonoidHom := by
          rw [heq2]
          exact hx
        obtain ⟨m, hm, hmx⟩ := hx'
        rw [← hLα] at hm
        obtain ⟨ℓ, hℓ, rfl⟩ := hm
        refine ⟨⟨w, hw⟩ * ℓ * (⟨w, hw⟩)⁻¹, ?_, ?_⟩
        · apply Subgroup.mem_subgroupOf.mpr
          have hcoe : ((⟨w, hw⟩ * ℓ * (⟨w, hw⟩ : ↥(pSpan (centMembers Ω e₀)))⁻¹ :
              ↥(pSpan (centMembers Ω e₀))) : G) = w * (ℓ : G) * w⁻¹ := rfl
          rw [hcoe, mem_conjSub_iff]
          have hk : w⁻¹ * (w * (ℓ : G) * w⁻¹) * w = (ℓ : G) := by group
          rw [hk]
          exact Subgroup.mem_subgroupOf.mp hℓ
        · simp only [map_mul, map_inv]
          exact hmx.symm ▸ rfl
    have heq : conjSub w L = L :=
      StarHyp.aeIdent_map_injective hS hΩ I hL' hL (himg.trans hLα.symm)
    rw [Subgroup.mem_normalizer_iff]
    intro g'
    have key : w * g' * w⁻¹ ∈ conjSub w L ↔ g' ∈ L := by
      rw [mem_conjSub_iff]
      have hk : w⁻¹ * (w * g' * w⁻¹) * w = g' := by group
      rw [hk]
    rw [heq] at key
    exact key.symm

private theorem e16ib_bcrit {e₀ : G} (hS : StarHyp Ω) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) (I : AEIdent (centMembers Ω e₀) 6)
    (ψ : ↥(pSpan (centMembers Ω e₀)) ≃* ↥(AE.aeSub 6))
    (hcov : ∀ x, AE.mkQ 6 (ψ x : AE.Wr 6) = I.φ x)
    (hD : ∀ x : ↥(pSpan (centMembers Ω e₀)), (x : G) ∈ zGroup Ω ↔ (ψ x : AE.Wr 6).perm = 1)
    (hinv : ∀ L ∈ centMembers Ω e₀, ∀ x ∈ pSpan (centMembers Ω e₀),
      conjSub x L ∈ centMembers Ω e₀)
    {M : Subgroup G} (hM : M ∈ centMembers Ω e₀) {γ : Finset (Fin 6)} {hγ : γ.card = 4}
    {b : Bool} (hMγ : (M.subgroupOf (pSpan (centMembers Ω e₀))).map I.φ = AE.memBar γ hγ b)
    {w y : zGroup Ω} (hw : (w : G) ∈ pSpan (centMembers Ω e₀))
    (hy : IsUniqueInvolution M y.1) :
    bf w y = 0 ↔ ∑ i ∈ γ, (ψ ⟨w.1, hw⟩ : AE.Wr 6).vec i = 0 := by
  have hΩ : centMembers Ω e₀ ⊆ Ω := fun L hL => hL.1
  rw [hbf.spec M hM.1 y hy w, e16ib_link hS I hinv hΩ hM hMγ hw]
  have hperm : (ψ ⟨w.1, hw⟩ : AE.Wr 6).perm = 1 := (hD ⟨w.1, hw⟩).mp w.2
  have hv : (ψ ⟨w.1, hw⟩ : AE.Wr 6) = AE.Wr.ofVec (ψ ⟨w.1, hw⟩ : AE.Wr 6).vec := by
    refine AE.Wr.ext rfl ?_
    exact hperm
  have hI : I.φ ⟨w.1, hw⟩ = AE.mkQ 6 (AE.Wr.ofVec (ψ ⟨w.1, hw⟩ : AE.Wr 6).vec) := by
    rw [← hcov, ← hv]
  rw [hI]
  exact AE.vec_normalizes_memBar_iff (by norm_num) γ hγ b _

private abbrev e16ib_pts (bf : zGroup Ω → zGroup Ω → ZMod 2) (t₀ : G) (ht₀ : t₀ ∈ zGroup Ω)
    (e₀ : G) : Set (zGroup Ω) :=
  {x | (x ∈ zPoints Ω ∧ x ≠ ⟨t₀, ht₀⟩ ∧ bf ⟨t₀, ht₀⟩ x = 0) ∧
    ∃ M ∈ centMembers Ω e₀, IsUniqueInvolution M x.1}

private theorem e16ib_residue {K₀ K₀' W₀ : Subgroup G}
    {z₀ u₀ e₀ g₀ : G} (c₀ : Sit16 Ω K₀ K₀' W₀ z₀ u₀ e₀ g₀) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13₀ : zGroup Ω ≠ eGroup Ω K₀) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) {J₀ : Subgroup G} (hJ₀ : J₀ ∈ centMembers Ω e₀) {t₀ : G}
    (hJt : IsUniqueInvolution J₀ t₀) (ht₀ : t₀ ∈ zGroup Ω) :
    (e16ib_pts bf t₀ ht₀ e₀).ncard = 6 ∧
      (∀ x ∈ e16ib_pts bf t₀ ht₀ e₀, (⟨t₀, ht₀⟩ : zGroup Ω) * x ∈ e16ib_pts bf t₀ ht₀ e₀) ∧
      (∀ x ∈ e16ib_pts bf t₀ ht₀ e₀, ∀ y ∈ e16ib_pts bf t₀ ht₀ e₀, y ≠ x →
        y ≠ (⟨t₀, ht₀⟩ : zGroup Ω) * x → bf x y = 1) := by
  classical
  obtain ⟨I, ψ, -, hcov, hmem, -, hD⟩ := exists_equiv_X c₀ h h9 h13₀
  have hS : StarHyp Ω := h.toStarHyp
  have hΩ : centMembers Ω e₀ ⊆ Ω := fun L hL => hL.1
  have hinv : ∀ L ∈ centMembers Ω e₀, ∀ x ∈ pSpan (centMembers Ω e₀),
      conjSub x L ∈ centMembers Ω e₀ :=
    fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx
  have htp : t₀ ∈ pSpan (centMembers Ω e₀) := le_pSpan hJ₀ hJt.mem
  obtain ⟨β, hβ, bJ, hJβ⟩ := I.label J₀ hJ₀
  have hψt : (ψ ⟨t₀, htp⟩ : AE.Wr 6) = AE.zOf (AE.emb β hβ) :=
    e16ib_inv_eq I ψ hmem hJ₀ hJβ htp hJt
  have hvt : (ψ ⟨t₀, htp⟩ : AE.Wr 6).vec = e16ib_ind β := by
    rw [hψt, e16ib_zOf_eq β hβ]
    rfl
  have hsum : ∀ α : Finset (Fin 6),
      ∑ i ∈ α, (ψ ⟨t₀, htp⟩ : AE.Wr 6).vec i = ((α ∩ β).card : ZMod 2) := by
    intro α
    rw [hvt]
    exact e16ib_sum_ind α β
  have hYex : ∀ (α : Finset (Fin 6)) (hα : α.card = 4), ∃ y : zGroup Ω,
      (∃ M ∈ centMembers Ω e₀, IsUniqueInvolution M y.1 ∧
        (M.subgroupOf (pSpan (centMembers Ω e₀))).map I.φ = AE.memBar α hα true) ∧
      ∀ hy : y.1 ∈ pSpan (centMembers Ω e₀),
        (ψ ⟨y.1, hy⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
    intro α hα
    obtain ⟨M, hM, hMα⟩ := I.label_surj α hα true
    obtain ⟨r, hr⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hM.1
    refine ⟨⟨r, Subgroup.subset_closure ⟨M, hM.1, hr⟩⟩, ⟨M, hM, hr, hMα⟩, fun hy => ?_⟩
    exact e16ib_inv_eq I ψ hmem hM hMα hy hr
  choose! Yf hYf using hYex
  have hYmem : ∀ (α : Finset (Fin 6)) (hα : α.card = 4),
      (Yf α).1 ∈ pSpan (centMembers Ω e₀) := by
    intro α hα
    obtain ⟨⟨M, hM, hr, -⟩, -⟩ := hYf α hα
    exact le_pSpan hM hr.mem
  have hYψ : ∀ (α : Finset (Fin 6)) (hα : α.card = 4),
      (ψ ⟨(Yf α).1, hYmem α hα⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
    intro α hα
    exact (hYf α hα).2 _
  have hYzP : ∀ (α : Finset (Fin 6)) (hα : α.card = 4), Yf α ∈ zPoints Ω := by
    intro α hα
    obtain ⟨⟨M, hM, hr, -⟩, -⟩ := hYf α hα
    exact ⟨M, hM.1, hr⟩
  have hpinj : ∀ (x y : G) (hx : x ∈ pSpan (centMembers Ω e₀))
      (hy : y ∈ pSpan (centMembers Ω e₀)),
      (ψ ⟨x, hx⟩ : AE.Wr 6) = ψ ⟨y, hy⟩ → x = y := by
    intro x y hx hy hxy
    exact congrArg Subtype.val (ψ.injective (Subtype.ext hxy))
  have hzinj : ∀ (α β' : Finset (Fin 6)) (hα : α.card = 4) (hβ' : β'.card = 4),
      AE.zOf (AE.emb α hα) = AE.zOf (AE.emb β' hβ') → α = β' := by
    intro α β' hα hβ' heq
    have h1 := AE.range_eq_of_zOf_eq heq
    rw [AE.range_emb, AE.range_emb] at h1
    exact Finset.coe_injective h1
  have hkey : ∀ (x y : G) (hx : x ∈ pSpan (centMembers Ω e₀))
      (hy : y ∈ pSpan (centMembers Ω e₀)), x = y →
      (ψ ⟨x, hx⟩ : AE.Wr 6) = ψ ⟨y, hy⟩ := by
    rintro x y hx hy rfl
    rfl
  set Lb : Finset (Finset (Fin 6)) :=
    (Finset.univ : Finset (Finset (Fin 6))).filter
      (fun α : Finset (Fin 6) => α.card = 4 ∧ (α ∩ β).card = 2) with hLb
  have hLbcard : Lb.card = 6 := e16ib_c1 β hβ
  have hLbmem : ∀ α : Finset (Fin 6), α ∈ Lb ↔ α.card = 4 ∧ (α ∩ β).card = 2 := by
    intro α
    simp [hLb]
  have hYinj : Set.InjOn Yf ↑Lb := by
    intro α hα α' hα' heq
    obtain ⟨h4, -⟩ := (hLbmem α).mp (Finset.mem_coe.mp hα)
    obtain ⟨h4', -⟩ := (hLbmem α').mp (Finset.mem_coe.mp hα')
    have h1 := hkey _ _ (hYmem α h4) (hYmem α' h4') (congrArg Subtype.val heq)
    rw [hYψ α h4, hYψ α' h4'] at h1
    exact hzinj α α' h4 h4' h1
  have hP1 : e16ib_pts bf t₀ ht₀ e₀ = Yf '' ↑Lb := by
    ext x
    constructor
    · rintro ⟨⟨hxz, hxt, hbx⟩, M, hM, hxM⟩
      obtain ⟨α, hα, b', hMα⟩ := I.label M hM
      have hxp : x.1 ∈ pSpan (centMembers Ω e₀) := le_pSpan hM hxM.mem
      have hψx : (ψ ⟨x.1, hxp⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) :=
        e16ib_inv_eq I ψ hmem hM hMα hxp hxM
      have hcrit := e16ib_bcrit (w := ⟨t₀, ht₀⟩) (y := x) hS hbf I ψ hcov hD hinv hM hMα
        htp hxM
      have hz0 : ((α ∩ β).card : ZMod 2) = 0 := by
        rw [← hsum α]
        exact hcrit.mp hbx
      have hev : Even (α ∩ β).card := ZMod.natCast_eq_zero_iff_even.mp hz0
      obtain ⟨hc2, hc4⟩ := e16ib_c0 α β hα hβ
      have hle : (α ∩ β).card ≤ 4 := hα ▸ Finset.card_le_card Finset.inter_subset_left
      have hcard2 : (α ∩ β).card = 2 := by
        obtain ⟨k, hk⟩ := hev
        rcases (show (α ∩ β).card = 2 ∨ (α ∩ β).card = 4 by omega) with h2 | h4
        · exact h2
        · exfalso
          have hαβ : α = β := hc4 h4
          subst hαβ
          apply hxt
          have h1 : x.1 = t₀ := hpinj x.1 t₀ hxp htp (by rw [hψx, hψt])
          exact Subtype.ext h1
      have hαL : α ∈ Lb := (hLbmem α).mpr ⟨hα, hcard2⟩
      refine ⟨α, Finset.mem_coe.mpr hαL, ?_⟩
      apply Subtype.ext
      exact hpinj _ _ (hYmem α hα) hxp (by rw [hYψ α hα, hψx])
    · rintro ⟨α, hαL, rfl⟩
      obtain ⟨hα, hαβ⟩ := (hLbmem α).mp (Finset.mem_coe.mp hαL)
      obtain ⟨⟨M, hM, hr, hMα⟩, -⟩ := hYf α hα
      refine ⟨⟨hYzP α hα, ?_, ?_⟩, M, hM, hr⟩
      · intro heq
        have h1 : (Yf α).1 = t₀ := congrArg Subtype.val heq
        have h2 : (ψ ⟨(Yf α).1, hYmem α hα⟩ : AE.Wr 6) = (ψ ⟨t₀, htp⟩ : AE.Wr 6) :=
          hkey _ _ (hYmem α hα) htp h1
        rw [hYψ α hα, hψt] at h2
        have hαβ' : α = β := hzinj α β hα hβ h2
        subst hαβ'
        rw [Finset.inter_self, hα] at hαβ
        exact absurd hαβ (by decide)
      · have hcr := (e16ib_bcrit (w := ⟨t₀, ht₀⟩) (y := Yf α) hS hbf I ψ hcov hD hinv hM
          hMα htp hr).mpr
        apply hcr
        show ∑ i ∈ α, (ψ ⟨t₀, htp⟩ : AE.Wr 6).vec i = 0
        rw [hsum α, hαβ]
        decide
  have hmulY : ∀ (α : Finset (Fin 6)) (hαL : α ∈ Lb),
      (⟨t₀, ht₀⟩ : zGroup Ω) * Yf α = Yf (symmDiff α β) := by
    intro α hαL
    obtain ⟨hα, hαβ⟩ := (hLbmem α).mp hαL
    obtain ⟨hσ4, hσβ⟩ := e16ib_c3 α β hα hβ hαβ
    have hpa : (Yf α).1 ∈ pSpan (centMembers Ω e₀) := hYmem α hα
    have hmul : t₀ * (Yf α).1 ∈ pSpan (centMembers Ω e₀) := Subgroup.mul_mem _ htp hpa
    have hσp : (Yf (symmDiff α β)).1 ∈ pSpan (centMembers Ω e₀) := hYmem _ hσ4
    have hψm : (ψ ⟨t₀ * (Yf α).1, hmul⟩ : AE.Wr 6) =
        AE.zOf (AE.emb β hβ) * AE.zOf (AE.emb α hα) := by
      have hsplit : ψ ⟨t₀ * (Yf α).1, hmul⟩ = ψ ⟨t₀, htp⟩ * ψ ⟨(Yf α).1, hpa⟩ := by
        rw [← map_mul]
        rfl
      rw [hsplit, Subgroup.coe_mul, hψt, hYψ α hα]
    have hfin : (ψ ⟨t₀ * (Yf α).1, hmul⟩ : AE.Wr 6) =
        (ψ ⟨(Yf (symmDiff α β)).1, hσp⟩ : AE.Wr 6) := by
      rw [hψm, hYψ _ hσ4, e16ib_zOf_eq β hβ, e16ib_zOf_eq α hα, e16ib_zOf_eq _ hσ4,
        e16ib_ofVec_mul, e16ib_ind_add]
    apply Subtype.ext
    exact hpinj _ _ hmul hσp hfin
  have hclos : ∀ x ∈ e16ib_pts bf t₀ ht₀ e₀,
      (⟨t₀, ht₀⟩ : zGroup Ω) * x ∈ e16ib_pts bf t₀ ht₀ e₀ := by
    intro x hx
    rw [hP1] at hx ⊢
    obtain ⟨α, hαL, rfl⟩ := hx
    refine ⟨symmDiff α β, ?_, (hmulY α hαL).symm⟩
    rw [Finset.mem_coe, hLbmem]
    obtain ⟨hα, hαβ⟩ := (hLbmem α).mp (Finset.mem_coe.mp hαL)
    obtain ⟨hσ4, hσβ⟩ := e16ib_c3 α β hα hβ hαβ
    exact ⟨hσ4, hσβ⟩
  have hnp : ∀ x ∈ e16ib_pts bf t₀ ht₀ e₀, ∀ y ∈ e16ib_pts bf t₀ ht₀ e₀,
      y ≠ x → y ≠ (⟨t₀, ht₀⟩ : zGroup Ω) * x → bf x y = 1 := by
    intro x hx y hy hyx hyt
    rw [hP1] at hx hy
    obtain ⟨α, hαL, rfl⟩ := hx
    obtain ⟨γ, hγL, rfl⟩ := hy
    obtain ⟨hα, hαβ⟩ := (hLbmem α).mp (Finset.mem_coe.mp hαL)
    obtain ⟨hγ, hγβ⟩ := (hLbmem γ).mp (Finset.mem_coe.mp hγL)
    have hne1 : γ ≠ α := fun h' => hyx (by rw [h'])
    have hne2 : γ ≠ symmDiff α β := by
      intro h'
      apply hyt
      rw [hmulY α hαL, h']
    have hc := e16ib_c2 β (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ⟩) α
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα, hαβ⟩) γ
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hγ, hγβ⟩) (Ne.symm hne1) hne2
    obtain ⟨⟨M, hM, hr, hMγ⟩, -⟩ := hYf γ hγ
    have h0 : ¬ (bf (Yf α) (Yf γ) = 0) := by
      intro h0
      have h1 := (e16ib_bcrit hS hbf I ψ hcov hD hinv hM hMγ (hYmem α hα) hr).mp h0
      rw [hYψ α hα, e16ib_zOf_eq α hα] at h1
      have h2 : (AE.Wr.ofVec (e16ib_ind α)).vec = e16ib_ind α := rfl
      rw [h2, e16ib_sum_ind] at h1
      have hev : Even (γ ∩ α).card := ZMod.natCast_eq_zero_iff_even.mp h1
      rw [Finset.inter_comm] at hev
      rw [Nat.even_iff] at hev
      omega
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (bf (Yf α) (Yf γ)) with h | h
    · exact absurd h h0
    · exact h
  refine ⟨?_, hclos, hnp⟩
  rw [hP1, Set.InjOn.ncard_image hYinj, Set.ncard_coe_finset, hLbcard]

private theorem e16ib_cent_of_le {L : Subgroup G} {a : G}
    (hL : L ≤ Subgroup.centralizer ({a} : Set G)) : a ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact Subgroup.mem_centralizer_singleton_iff.mp (hL hj)

private theorem e16ib_ncard30 {K₀ K₀' W₀ : Subgroup G}
    {z₀ u₀ e₀ g₀ : G} (c₀ : Sit16 Ω K₀ K₀' W₀ z₀ u₀ e₀ g₀) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13₀ : zGroup Ω ≠ eGroup Ω K₀) : (centMembers Ω e₀).ncard = 30 := by
  obtain ⟨I, -⟩ := exists_equiv_X c₀ h h9 h13₀
  have := EndHyp.ncard_eq_of_aeIdent h (fun L hL => (Generic.mem_centMembers.mp hL).1)
    (fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx)
    (EndHyp.oddCore_centMembers_eq_bot h h9 c₀.twin h13₀ (u_mem_zGroup c₀ h h9 h13₀).2
      c₀.data.he1)
    (by norm_num) (by norm_num) I
  rw [this]
  rfl

private theorem e16ib_twin_mem {K₀ K₀' W₀ : Subgroup G}
    {z₀ u₀ e₀ g₀ : G} (c₀ : Sit16 Ω K₀ K₀' W₀ z₀ u₀ e₀ g₀) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13₀ : zGroup Ω ≠ eGroup Ω K₀) {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ centMembers Ω e₀)
    (hM₂ : M₂ ∈ Ω) {x : G} (hx₁ : IsUniqueInvolution M₁ x) (hx₂ : IsUniqueInvolution M₂ x) :
    M₂ ∈ centMembers Ω e₀ := by
  classical
  obtain ⟨I, ψ, -, hcov, hmem, -, hD⟩ := exists_equiv_X c₀ h h9 h13₀
  have hxp : x ∈ pSpan (centMembers Ω e₀) := le_pSpan hM₁ hx₁.mem
  obtain ⟨α, hα, b, hM₁α⟩ := I.label M₁ hM₁
  obtain ⟨N, hN, hNα⟩ := I.label_surj α hα (!b)
  obtain ⟨y, hy⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hN.1
  have hyp : y ∈ pSpan (centMembers Ω e₀) := le_pSpan hN hy.mem
  have hψx := e16ib_inv_eq I ψ hmem hM₁ hM₁α hxp hx₁
  have hψy := e16ib_inv_eq I ψ hmem hN hNα hyp hy
  have hxy : x = y := by
    have h1 := ψ.injective (Subtype.ext (hψx.trans hψy.symm))
    exact congrArg Subtype.val h1
  have hy' : IsUniqueInvolution N x := by
    rw [hxy]
    exact hy
  have hNM : N ≠ M₁ := by
    intro hNM1
    have h1 : AE.memBar α hα (!b) = AE.memBar α hα b := by
      rw [← hNα, hNM1, hM₁α]
    cases b
    · exact AE.memBar_true_ne_false (by norm_num) α hα (by simpa using h1)
    · exact AE.memBar_true_ne_false (by norm_num) α hα (by simpa using h1.symm)
  obtain ⟨L', -, hL'⟩ := h.twinSet_pair c₀.twin hM₁.1
  have hN_tw : N ∈ twinSet Ω M₁ := ⟨hN.1, x, hx₁, hy'⟩
  have hM₂_tw : M₂ ∈ twinSet Ω M₁ := ⟨hM₂, x, hx₁, hx₂⟩
  rw [hL'] at hN_tw hM₂_tw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN_tw hM₂_tw
  have hNL : N = L' := hN_tw.resolve_left hNM
  rcases hM₂_tw with h2 | h2
  · rw [h2]
    exact hM₁
  · rw [h2, ← hNL]
    exact hN

private theorem e16ib_frame_false {W' : Subgroup G} {u' e' g' : G}
    (c : Sit16 Ω K K' W z u e g)
    (c' : Sit16 Ω (conjSub g K) (conjSub g K') W' (u * e) u' e' g')
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (h13' : zGroup Ω ≠ eGroup Ω (conjSub g K)) (hee : e' ≠ e)
    (hJe' : conjSub g K ∈ centMembers Ω e')
    {R : Subgroup G} (hR : R ∈ Ω) (hRe : R ∈ centMembers Ω e) (hRe' : R ∈ centMembers Ω e')
    {x : G} (hRx : IsUniqueInvolution R x) (hxt : x ≠ u * e)
    (hadj : x ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G)) : False := by
  have hJΩ : conjSub g K ∈ Ω := (c.conjSub_mem h h9).2.1.1
  have hJt : IsUniqueInvolution (conjSub g K) (u * e) := (c.conjSub_mem h h9).2.2.2
  have hJD : conjSub g K ∈ DSet Ω W := (c.conjSub_mem h h9).1
  have hJe : conjSub g K ∈ centMembers Ω e := dSet_subset_centMembers c h hJD
  have hRω : R ∈ omegaStarNbr Ω (conjSub g K) := by
    rcases EndHyp.mem_omegaStarNbr_or_twinSet h h9 hJΩ hR hRx hadj with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨-, z', hz'J, hz'R⟩ := h1
      exact hxt ((hRx.eq hz'R).trans (hJt.eq hz'J).symm)
  obtain ⟨W₁, u₁, e₁, g₁, c₁, hR₁, -⟩ :=
    exists_frame_of_omegaStarNbr (conj_frame c h h9) h h9 hRω
  have h13J : zGroup Ω ≠ eGroup Ω (conjSub g K) := h13'
  have hJ₁ : conjSub g K ∈ DSet Ω W₁ :=
    h.mem_dSet_of_mem c₁.data.hW c₁.twin.mem c₁.twin.isInv c₁.data.hzW
  have hne : R ∉ twinSet Ω (conjSub g K) := by
    intro h1
    obtain ⟨-, z', hz'J, hz'R⟩ := h1
    exact hxt ((hRx.eq hz'R).trans (hJt.eq hz'J).symm)
  have hlam1 := lambdaW_eq_of_mem c₁ h h9 h13J hJ₁ hR₁ hne
  have hlamc1 := lambdaW_eq_centralizer c₁ h h9 h13J
  have heD : e ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).2
  have heΛ : e ∈ lambdaW Ω W₁ := by
    rw [hlam1]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨heD, e16ib_cent_of_le hJe.2⟩,
      e16ib_cent_of_le hRe.2⟩
  have he'Λ : e' ∈ lambdaW Ω W₁ := by
    rw [hlam1]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(u_mem_zGroup c' h h9 h13').2,
      e16ib_cent_of_le hJe'.2⟩, e16ib_cent_of_le hRe'.2⟩
  rw [hlamc1] at heΛ he'Λ
  have hsub1 : centMembers Ω e₁ ⊆ centMembers Ω e := by
    intro L hL
    refine ⟨hL.1, ?_⟩
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heΛ).2 m (le_pSpan hL hm))
  have hsub2 : centMembers Ω e₁ ⊆ centMembers Ω e' := by
    intro L hL
    refine ⟨hL.1, ?_⟩
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp he'Λ).2 m (le_pSpan hL hm))
  have h30₁ := e16ib_ncard30 c₁ h h9 h13J
  have h30 := e16ib_ncard30 c h h9 h13
  have h30' := e16ib_ncard30 c' h h9 h13'
  have heq1 : centMembers Ω e₁ = centMembers Ω e :=
    Set.eq_of_subset_of_ncard_le hsub1 (by omega) (Set.toFinite _)
  have heq2 : centMembers Ω e₁ = centMembers Ω e' :=
    Set.eq_of_subset_of_ncard_le hsub2 (by omega) (Set.toFinite _)
  have hD1 : DSet Ω W₁ ⊆ centMembers Ω e := by
    intro R' hR'
    rw [← heq1]
    exact dSet_subset_centMembers c₁ h hR'
  have hD2 : DSet Ω W₁ ⊆ centMembers Ω e' := by
    intro R' hR'
    rw [← heq2]
    exact dSet_subset_centMembers c₁ h hR'
  have he1 : e₁ = e := eq_of_dSet_subset_centMembers c c₁ h h9 h13 hD1
  have he2 : e₁ = e' := eq_of_dSet_subset_centMembers c' c₁ h h9 h13' hD2
  exact hee (he2.symm.trans he1)

theorem false_of_aeIdent_six_Y (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hn : Nonempty (AEIdent (centMembers Ω u) 6)) : False := by
  classical
  have huD : u ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).1
  have heD : e ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).2
  have htD : u * e ∈ zGroup Ω := Subgroup.mul_mem _ huD heD
  have hJΩ : conjSub g K ∈ Ω := (c.conjSub_mem h h9).2.1.1
  have hJD : conjSub g K ∈ DSet Ω W := (c.conjSub_mem h h9).1
  have hJt : IsUniqueInvolution (conjSub g K) (u * e) := (c.conjSub_mem h h9).2.2.2
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    (c.conjSub_le_centralizer_u h h9).1
  have hJe : conjSub g K ∈ centMembers Ω e := dSet_subset_centMembers c h hJD
  have hJP : conjSub g K ∈ centMembers Ω u := ⟨hJΩ, hJu⟩
  have hdz : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have hu2 : u * u = 1 := h.zGroup_mul_self h9 u huD
  obtain ⟨W', u', e', g', c', hsub, hee⟩ :=
    exists_section_le_centMembers_u c h h9 h13 (Or.inl ⟨6, by norm_num, by norm_num, hn⟩)
  have h13' : zGroup Ω ≠ eGroup Ω (conjSub g K) :=
    EndHyp.zGroup_ne_eGroup_conj h c.twin.mem h13 g
  have hn30 : (centMembers Ω u).ncard = 30 := by
    obtain ⟨I⟩ := hn
    have := EndHyp.ncard_eq_of_aeIdent h (fun L hL => hL.1)
      (fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx)
      (EndHyp.oddCore_centMembers_eq_bot h h9 c.twin h13 huD c.data.hu1) (by norm_num)
      (by norm_num) I
    rw [this]
    rfl
  have h30' := e16ib_ncard30 c' h h9 h13'
  have hPeq : centMembers Ω e' = centMembers Ω u :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hJe' : conjSub g K ∈ centMembers Ω e' := by
    rw [hPeq]
    exact hJP
  have hO : classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥ :=
    EndHyp.oddCore_centMembers_eq_bot h h9 c.twin h13 huD c.data.hu1
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hinvP : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u :=
    fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx
  have hA : ∀ d ∈ lambdaW Ω W, (∀ L ∈ centMembers Ω u, conjSub d L ∈ centMembers Ω u) ∧
      ∀ L ∈ centMembers Ω u, ∀ r : G, IsUniqueInvolution L r → d * r = r * d := by
    intro d hd
    have hdD : d ∈ zGroup Ω := (Subgroup.mem_inf.mp hd).1
    have hdu : d * u = u * d := hdz d hdD u huD
    refine ⟨fun L hL => ?_, fun L hL r hr => ?_⟩
    · have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩ.conjInvariant hL
        (n := d)
      rwa [show d * u * d⁻¹ = u by rw [hdu, mul_inv_cancel_right]] at hc
    · have hrD : r ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL.1, hr⟩
      exact hdz d hdD r hrD
  have hAL : ∀ a ∈ lambdaW Ω W, ∀ l ∈ conjSub g K, a * l = l * a := by
    intro a ha l hl
    have haJ : a ∈ Subgroup.centralizer ((conjSub g K : Subgroup G) : Set G) := by
      rw [lambdaW_eq c h h9 h13] at ha
      exact (Subgroup.mem_inf.mp ha).2
    exact (Subgroup.mem_centralizer_iff.mp haJ l hl).symm
  obtain ⟨I⟩ := hn
  have hbound := natCard_le_of_aeIdent hΩ h.thmD.two (fun L hL => hL.1) hinvP
    (by norm_num) (by norm_num) I (I.toLabel.isPGroup_ker hO) hA hJP hAL
  have hsub0 : lambdaW Ω W ⊓
      Subgroup.centralizer ((pSpan (centMembers Ω u) : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxL : x ∈ lambdaW Ω W := (Subgroup.mem_inf.mp hx).1
    have hxY : x ∈ Subgroup.centralizer ((pSpan (centMembers Ω u) : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hx).2
    have hxX : x ∈ Subgroup.centralizer ((pSpan (centMembers Ω e) : Subgroup G) : Set G) := by
      rw [lambdaW_eq_centralizer c h h9 h13] at hxL
      exact (Subgroup.mem_inf.mp hxL).2
    have hXY : pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) ≤
        Subgroup.centralizer ({x} : Set G) := by
      apply sup_le
      · exact fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxX s hs)
      · exact fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxY s hs)
    rw [pSpan_sup_eq_top_of_X c h h9 h13] at hXY
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g'
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hXY (Subgroup.mem_top g')))
    rw [h.center] at hxc
    exact hxc
  have hcard1 : Nat.card ↥(lambdaW Ω W ⊓
      Subgroup.centralizer ((pSpan (centMembers Ω u) : Subgroup G) : Set G)) = 1 := by
    rw [hsub0, Subgroup.card_bot]
  have hle4 : Nat.card ↥(lambdaW Ω W) ≤ 4 := by
    rw [hcard1] at hbound
    simpa using hbound
  obtain ⟨ε, hε, hDε, -⟩ := c.natCard_zGroup_eq_sixteen_mul h h9 h13
  have hE : ¬ eGroup Ω K ≤ K ⊔ K' := fun hle =>
    (c.mul_mem_eGroup h h9).2 (hle (c.mul_mem_eGroup h h9).1)
  have h64 := EndHyp.sixtyFour_le_natCard_zGroup h h9 c.twin h13 hE
  obtain ⟨m, hm⟩ := EndHyp.natCard_zGroup_eq_four_pow h h9 c.twin h13
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hε
  have hD128 : Nat.card (zGroup Ω) ≤ 128 := by
    rw [hDε]
    rcases hε with rfl | rfl <;> omega
  have hD64 : Nat.card (zGroup Ω) = 64 := by
    rw [hm] at h64 hD128 ⊢
    have hm3 : m < 4 := by
      by_contra hcon
      have hcon' : 4 ≤ m := by omega
      have h256 : 256 ≤ 4 ^ m := by
        calc (256 : ℕ) = 4 ^ 4 := by norm_num
          _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hcon'
      omega
    interval_cases m
    · exact absurd h64 (by norm_num)
    · exact absurd h64 (by norm_num)
    · exact absurd h64 (by norm_num)
    · norm_num
  obtain ⟨bf, hbf⟩ := EndHyp.exists_endForm h h9 c.twin h13
  haveI : Fact (EndHyp Ω) := ⟨h⟩
  haveI : Fact (Perp9 Ω) := ⟨h9⟩
  obtain ⟨a, hS⟩ := EndHyp.exists_pointSet c.twin h13 hbf
  have hB : Polar.SympForm bf := hbf.sympForm
  have hres := e16ib_residue c h h9 h13 hbf hJe hJt htD
  have hres' := e16ib_residue c' h h9 h13' hbf hJe' hJt htD
  have hdisj : Disjoint (e16ib_pts bf (u * e) htD e) (e16ib_pts bf (u * e) htD e') := by
    rw [Set.disjoint_left]
    rintro x ⟨⟨hxz, hxt, hbx⟩, M₁, hM₁, hxM₁⟩ ⟨-, M₂, hM₂, hxM₂⟩
    have hM₂e : M₂ ∈ centMembers Ω e :=
      e16ib_twin_mem c h h9 h13 hM₁ hM₂.1 hxM₁ hxM₂
    have hxt' : x.1 ≠ u * e := fun h1 => hxt (Subtype.ext h1)
    have hadj : x.1 ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
      (hbf.spec (conjSub g K) hJΩ (⟨u * e, htD⟩ : zGroup Ω) hJt x).mp
        ((hbf.symm x _).trans hbx)
    exact e16ib_frame_false c c' h h9 h13 h13' hee hJe' hM₂.1 hM₂e hM₂ hxM₂ hxt' hadj
  have hzero : ∀ j ∈ Polar.nbr bf (zPoints Ω) (⟨u * e, htD⟩ : zGroup Ω),
      bf (⟨e, heD⟩ : zGroup Ω) j = 0 ↔
        j ∈ e16ib_pts bf (u * e) htD e ∪ e16ib_pts bf (u * e) htD e' := by
    intro j hj
    have hjz : j ∈ zPoints Ω := hj.1
    have hjt : j ≠ (⟨u * e, htD⟩ : zGroup Ω) := hj.2.1
    have hBtj : bf (⟨u * e, htD⟩ : zGroup Ω) j = 0 := hj.2.2
    constructor
    · intro hBej
      obtain ⟨M, hMΩ, hMj⟩ := id hjz
      have hrM : (u * e) ∈ Subgroup.normalizer (M : Set G) :=
        (hbf.spec M hMΩ j hMj (⟨u * e, htD⟩ : zGroup Ω)).mp hBtj
      have hcM : e ∈ Subgroup.normalizer (M : Set G) :=
        (hbf.spec M hMΩ j hMj (⟨e, heD⟩ : zGroup Ω)).mp hBej
      have hcR : conjSub g K ≤ Subgroup.centralizer ({e} : Set G) := hJe.2
      rcases EndHyp.centralizer_or_mul h h9 c.twin h13 hJΩ hMΩ hJt hMj heD hcR hrM hcM with
        hMe | hMu
      · exact Or.inl ⟨⟨hjz, hjt, hBtj⟩, M, ⟨hMΩ, hMe⟩, hMj⟩
      · have hcomm : e * u = u * e := hdz e heD u huD
        have hee2 : e * e = 1 := h.zGroup_mul_self h9 e heD
        have heu : e * (u * e) = u := by
          calc e * (u * e) = (e * u) * e := (mul_assoc _ _ _).symm
            _ = (u * e) * e := by rw [hcomm]
            _ = u := by rw [mul_assoc, hee2, mul_one]
        rw [heu] at hMu
        exact Or.inr ⟨⟨hjz, hjt, hBtj⟩, M, (by rw [hPeq]; exact ⟨hMΩ, hMu⟩), hMj⟩
    · intro hj'
      rcases hj' with ⟨-, M, hM, hMj⟩ | ⟨-, M, hM, hMj⟩
      · exact (hbf.spec M hM.1 j hMj (⟨e, heD⟩ : zGroup Ω)).mpr
          (Subgroup.centralizer_le_normalizer _ (e16ib_cent_of_le hM.2))
      · have hM' : M ∈ centMembers Ω u := by
          rw [← hPeq]
          exact hM
        have hBu : bf (⟨u, huD⟩ : zGroup Ω) j = 0 :=
          (hbf.spec M hM'.1 j hMj (⟨u, huD⟩ : zGroup Ω)).mpr
            (Subgroup.centralizer_le_normalizer _ (e16ib_cent_of_le hM'.2))
        have hsplit : (⟨e, heD⟩ : zGroup Ω) = (⟨u, huD⟩ : zGroup Ω) * (⟨u * e, htD⟩ : zGroup Ω) :=
          Subtype.ext (by
            show e = u * (u * e)
            rw [← mul_assoc, hu2, one_mul])
        rw [hsplit, hbf.mul_left, hBu, hBtj, add_zero]
  exact Polar.false_of_two_sections (t := (⟨u * e, htD⟩ : zGroup Ω))
    (e := (⟨e, heD⟩ : zGroup Ω)) hB hS hD64
    ⟨conjSub g K, hJΩ, hJt⟩
    ((hbf.spec (conjSub g K) hJΩ (⟨u * e, htD⟩ : zGroup Ω) hJt (⟨e, heD⟩ : zGroup Ω)).mpr
      (Subgroup.centralizer_le_normalizer _ (e16ib_cent_of_le hJe.2)))
    (fun x hx => hx.1) (fun x hx => hx.1) hres.1 hres'.1 hdisj hres.2.1 hres'.2.1 hres.2.2
    hres'.2.2 hzero

section E16ic

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

private theorem e16ic_ofVec_add {n : ℕ} (v w : Fin n → ZMod 2) :
    Wr.ofVec (v + w) = Wr.ofVec v * Wr.ofVec w := by
  refine Wr.ext ?_ ?_
  · funext i
    simp only [Wr.ofVec, Wr.mul_vec, Pi.add_apply]
    rfl
  · simp [Wr.ofVec, Wr.mul_perm]

private theorem e16ic_ofVec_zero {n : ℕ} : Wr.ofVec (0 : Fin n → ZMod 2) = 1 := rfl

private theorem e16ic_mkQ_ofVec_add_one {n : ℕ} (v : Fin n → ZMod 2) :
    mkQ n (Wr.ofVec (v + fun _ => 1)) = mkQ n (Wr.ofVec v) := by
  rw [e16ic_ofVec_add, map_mul]
  have h1 : mkQ n (Wr.ofVec fun _ => 1) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (mem_piSub.mpr (Or.inr rfl))
  rw [h1, mul_one]

private theorem e16ic_ofVec_inv {n : ℕ} (v : Fin n → ZMod 2) :
    (Wr.ofVec v)⁻¹ = Wr.ofVec v := by
  refine Wr.ext ?_ ?_
  · funext i
    simp only [Wr.ofVec, Wr.inv_vec]
    rfl
  · simp [Wr.ofVec, Wr.inv_perm]

private theorem e16ic_zmod2_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  revert x y; decide

private theorem e16ic_ofVec_eq_one {n : ℕ} (x : Fin n → ZMod 2) :
    Wr.ofVec x = 1 ↔ x = 0 :=
  ⟨fun h => congrArg Wr.vec h, fun h => by subst h; rfl⟩

private theorem e16ic_ofVec_eq_allOnes {n : ℕ} (x : Fin n → ZMod 2) :
    Wr.ofVec x = allOnes n ↔ x = fun _ => 1 :=
  ⟨fun h => congrArg Wr.vec h, fun h => by subst h; rfl⟩

private theorem e16ic_mkQ_eq_iff_add {n : ℕ} (v w : Fin n → ZMod 2) :
    mkQ n (Wr.ofVec v) = mkQ n (Wr.ofVec w) ↔ v + w = 0 ∨ v + w = fun _ => 1 := by
  have key : (Wr.ofVec v)⁻¹ * Wr.ofVec w = Wr.ofVec (v + w) := by
    rw [e16ic_ofVec_inv, e16ic_ofVec_add]
  rw [mkQ_eq_iff, key, e16ic_ofVec_eq_one, e16ic_ofVec_eq_allOnes]

private theorem e16ic_mkQ_eq_one {n : ℕ} (v : Fin n → ZMod 2) :
    mkQ n (Wr.ofVec v) = 1 ↔ v = 0 ∨ v = fun _ => 1 := by
  show (QuotientGroup.mk (Wr.ofVec v) : AEQ n) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_piSub, e16ic_ofVec_eq_one, e16ic_ofVec_eq_allOnes]


private theorem e16ic_eq_one_of_comm (x : AEQ 7)
    (hx : ∀ y ∈ (aeSub 7).map (mkQ 7), x * y = y * x) : x = 1 := by
  have hvec : ∀ f : Fin 7 → ZMod 2, ∑ i, f i = 0 →
      x * mkQ 7 (Wr.ofVec f) = mkQ 7 (Wr.ofVec f) * x := by
    intro f hf
    refine hx _ ⟨Wr.ofVec f, ?_, rfl⟩
    exact (mem_aeSub).mpr ⟨hf, by simp [Wr.ofVec]⟩
  obtain ⟨v, rfl⟩ := AE.eq_vec_of_comm_vectors (n := 7) (by norm_num) hvec
  have hmemBar : ∀ (α : Finset (Fin 7)) (h : α.card = 4) (b : Bool),
      ∀ y ∈ memBar α h b, mkQ 7 (Wr.ofVec v) * y = y * mkQ 7 (Wr.ofVec v) := by
    intro α h b y hy
    refine hx y ?_
    have hsub : memAt α h b ≤ aeSub 7 := by
      cases b
      · exact memKStar_le_aeSub _
      · exact memK_le_aeSub _
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a, hsub ha, rfl⟩
  have hconst : ∀ i j : Fin 7, v i = v j := by
    intro i j
    obtain ⟨α, hij, -, hcard⟩ := Finset.exists_subsuperset_card_eq (s := {i, j})
      (t := (Finset.univ : Finset (Fin 7))) (n := 4) (Finset.subset_univ _)
      (Finset.card_le_two.trans (by norm_num)) (by simp)
    have h := (AE.vec_centralizes_memBar_iff (n := 7) (by norm_num) α hcard true v).mp
      (hmemBar α hcard true)
    exact h i (hij (by simp)) j (hij (by simp))
  have hc : v = 0 ∨ v = fun _ => 1 := by
    have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases this (v 0) with h0 | h1
    · left
      funext i
      rw [hconst i 0, h0]; rfl
    · right
      funext i
      rw [hconst i 0, h1]
  rw [e16ic_mkQ_eq_one]
  exact hc

private theorem e16ic_zBar_eq {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) :
    zBar α h = mkQ n (Wr.ofVec (fun x => if x ∈ α then 1 else 0)) := by
  unfold zBar
  congr 1
  refine Wr.ext ?_ ?_
  · funext x
    simp only [Wr.ofVec]
    rw [zOf_vec_apply]
    by_cases hx : x ∈ α
    · have hr : x ∈ Set.range (emb α h) := by rw [range_emb]; exact hx
      simp [hr, hx]
    · have hr : x ∉ Set.range (emb α h) := by rw [range_emb]; exact hx
      simp [hr, hx]
  · rw [zOf_perm]
    rfl

private theorem e16ic_even_decomp : ∀ f : Fin 7 → ZMod 2, (∑ i, f i = 0) → ∀ x : Fin 7,
    f x = ∑ i ∈ Finset.univ.filter (fun i => i ≠ 0 ∧ f i = 1),
      ((if x = 0 then 1 else 0) + (if x = i then 1 else 0) : ZMod 2) := by
  decide +kernel

private def e16ic_Kz : Subgroup (AEQ 7) :=
  Subgroup.closure {x | ∃ (α : Finset (Fin 7)) (h : α.card = 4), x = zBar α h}

private def e16ic_g (i : Fin 7) : Fin 7 → ZMod 2 :=
  fun x => (if x = 0 then 1 else 0) + (if x = i then 1 else 0)

private theorem e16ic_g_mem (i : Fin 7) (hi : i ≠ 0) :
    mkQ 7 (Wr.ofVec (e16ic_g i)) ∈ e16ic_Kz := by
  have hc2 : ({0, i} : Finset (Fin 7)).card = 2 := Finset.card_pair (Ne.symm hi)
  have hc5 : 3 ≤ (Finset.univ \ ({0, i} : Finset (Fin 7))).card := by
    rw [Finset.card_univ_diff, Fintype.card_fin, hc2]
    norm_num
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hc5
  have hT0 : (0 : Fin 7) ∉ T := fun h => by
    have := hT h; simp at this
  have hTi : i ∉ T := fun h => by
    have := hT h; simp at this
  have hα : (insert 0 T).card = 4 := by
    rw [Finset.card_insert_of_notMem hT0, hTc]
  have hβ : (insert i T).card = 4 := by
    rw [Finset.card_insert_of_notMem hTi, hTc]
  have hsum : e16ic_g i = fun x => (if x ∈ insert 0 T then 1 else 0) +
      (if x ∈ insert i T then 1 else 0) := by
    funext x
    unfold e16ic_g
    by_cases hx : x ∈ T
    · have h1 : x ≠ 0 := fun h => hT0 (h ▸ hx)
      have h2 : x ≠ i := fun h => hTi (h ▸ hx)
      simp [hx, h1, h2]
      decide
    · simp [hx]
  have hmul : mkQ 7 (Wr.ofVec (e16ic_g i)) =
      zBar (insert 0 T) hα * zBar (insert i T) hβ := by
    rw [e16ic_zBar_eq, e16ic_zBar_eq, ← map_mul, ← e16ic_ofVec_add, hsum]
    rfl
  rw [hmul]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hα, rfl⟩)
    (Subgroup.subset_closure ⟨_, hβ, rfl⟩)

private theorem e16ic_sum_mem : ∀ S : Finset (Fin 7), (∀ i ∈ S, i ≠ 0) →
    mkQ 7 (Wr.ofVec (∑ i ∈ S, e16ic_g i)) ∈ e16ic_Kz := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.sum_empty, e16ic_ofVec_zero, map_one]
    exact Subgroup.one_mem _
  | insert j S hjS ih =>
    intro hS
    rw [Finset.sum_insert hjS, e16ic_ofVec_add, map_mul]
    exact Subgroup.mul_mem _ (e16ic_g_mem j (hS j (Finset.mem_insert_self _ _)))
      (ih fun i hi => hS i (Finset.mem_insert_of_mem hi))

private theorem e16ic_even_mem (f : Fin 7 → ZMod 2) (hf : ∑ i, f i = 0) :
    mkQ 7 (Wr.ofVec f) ∈ e16ic_Kz := by
  have hfun : f = ∑ i ∈ Finset.univ.filter (fun i => i ≠ 0 ∧ f i = 1), e16ic_g i := by
    funext x
    rw [Finset.sum_apply, e16ic_even_decomp f hf x]
    rfl
  have heq : mkQ 7 (Wr.ofVec f) =
      mkQ 7 (Wr.ofVec (∑ i ∈ Finset.univ.filter (fun i => i ≠ 0 ∧ f i = 1), e16ic_g i)) := by
    rw [← hfun]
  rw [heq]
  exact e16ic_sum_mem _ fun i hi => (Finset.mem_filter.mp hi).2.1

private theorem e16ic_even_inj (f g : Fin 7 → ZMod 2) (hf : ∑ i, f i = 0) (hg : ∑ i, g i = 0)
    (h : mkQ 7 (Wr.ofVec f) = mkQ 7 (Wr.ofVec g)) : f = g := by
  rcases (e16ic_mkQ_eq_iff_add f g).mp h with h0 | h1
  · funext x
    exact e16ic_zmod2_add_eq_zero (congrFun h0 x)
  · exfalso
    have hs : ∑ i, (f i + g i) = ∑ i : Fin 7, (1 : ZMod 2) :=
      Finset.sum_congr rfl (fun i _ => congrFun h1 i)
    rw [Finset.sum_add_distrib, hf, hg, zero_add] at hs
    revert hs
    decide

private theorem e16ic_preimage_even {G : Type} [Group G] (Y S : Subgroup G) (φ : ↥Y →* AEQ 7)
    (hS : S ≤ Y)
    (hz : ∀ (α : Finset (Fin 7)) (h : α.card = 4), ∃ x ∈ S, ∃ hx : x ∈ Y,
      φ ⟨x, hx⟩ = zBar α h)
    (f : Fin 7 → ZMod 2) (hf : ∑ i, f i = 0) :
    ∃ x ∈ S, ∃ hx : x ∈ Y, φ ⟨x, hx⟩ = mkQ 7 (Wr.ofVec f) := by
  have hKT : e16ic_Kz ≤ (S.subgroupOf Y).map φ := by
    unfold e16ic_Kz
    rw [Subgroup.closure_le]
    rintro _ ⟨α, h, rfl⟩
    obtain ⟨x, hxS, hxY, hx⟩ := hz α h
    exact Subgroup.mem_map.mpr ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hxS, hx⟩
  obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.mp (hKT (e16ic_even_mem f hf))
  exact ⟨a.1, Subgroup.mem_subgroupOf.mp ha, a.2, by rw [← hfa]⟩

private theorem e16ic_card_even :
    Nat.card {f : Fin 7 → ZMod 2 // ∑ i, f i = 0} = 64 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem e16ic_card_ge {G : Type} [Group G] [Finite G] (Y S : Subgroup G)
    (φ : ↥Y →* AEQ 7) (hS : S ≤ Y)
    (hz : ∀ (α : Finset (Fin 7)) (h : α.card = 4), ∃ x ∈ S, ∃ hx : x ∈ Y,
      φ ⟨x, hx⟩ = zBar α h) :
    64 ≤ Nat.card ↥S := by
  classical
  have hex := fun f : {f : Fin 7 → ZMod 2 // ∑ i, f i = 0} =>
    e16ic_preimage_even Y S φ hS hz f.1 f.2
  choose x hxS hxY hxφ using hex
  have hinj : Function.Injective (fun f : {f : Fin 7 → ZMod 2 // ∑ i, f i = 0} =>
      (⟨x f, hxS f⟩ : ↥S)) := by
    intro f g hfg
    have hxfg : x f = x g := congrArg Subtype.val hfg
    have hpt : (⟨x f, hxY f⟩ : ↥Y) = ⟨x g, hxY g⟩ := Subtype.ext hxfg
    have hcl : mkQ 7 (Wr.ofVec f.1) = mkQ 7 (Wr.ofVec g.1) := by
      rw [← hxφ f, ← hxφ g, hpt]
    apply Subtype.ext
    exact e16ic_even_inj f.1 g.1 f.2 g.2 hcl
  have := Nat.card_le_card_of_injective _ hinj
  rw [e16ic_card_even] at this
  exact this

private theorem e16ic_aeCoverHyp {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (h : EndHyp Ω) {u : G} (I : AEIdent (centMembers Ω u) 7)
    (hO : classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥)
    (hinv : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u)
    (htrans : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      ∃ x ∈ pSpan (centMembers Ω u), conjSub x L = L')
    {J J' : Subgroup G} {t : G} (hJ : J ∈ centMembers Ω u) (hJ' : J' ∈ centMembers Ω u)
    (hJt : IsUniqueInvolution J t) (hJ't : IsUniqueInvolution J' t) (hne : J ≠ J') :
    TL4.AECoverHyp I := by
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ hL => hL.1
  have hΩ := h.thmD.hyp
  have h2 := h.thmD.two
  have hk : IsPGroup 2 I.φ.ker := I.isPGroup_ker hO
  have hinj : ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      (L.subgroupOf (pSpan (centMembers Ω u))).map I.φ =
        (L'.subgroupOf (pSpan (centMembers Ω u))).map I.φ → L = L' :=
    fun L hL L' hL' he => StarHyp.aeIdent_map_injective h.toStarHyp hPΩ I hL hL' he
  obtain ⟨δ, hδ, c, hlab⟩ := I.label J hJ
  obtain ⟨δ', hδ', c', hlab'⟩ := I.label J' hJ'
  have e1 := I.map_eq_zBar (by norm_num) hJ (h.card_eq_eight hJ.1) hlab hJt
  have e2 := I.map_eq_zBar (by norm_num) hJ' (h.card_eq_eight hJ'.1) hlab' hJ't
  have hδδ : δ = δ' := AE.eq_of_zBar_eq (by norm_num) (e1.symm.trans e2)
  subst hδδ
  have hcc : c' = !c := by
    by_contra hc
    have hcc' : c' = c := by cases c <;> cases c' <;> simp_all
    subst hcc'
    exact hne (hinj J hJ J' hJ' (hlab.trans hlab'.symm))
  subst hcc
  refine
    { ker_two := hk
      card := fun L hL => h.card_eq_eight hL.1
      conj_mem := hinv
      label_inj := hinj
      twin_comm := ?_
      twin_z := I.twin_z_of_trans (by norm_num) (by norm_num) hinv hinj htrans hJ hJ' hlab hlab'
        (fun v v' hv hv' => (hJt.eq hv).symm.trans (hJ't.eq hv')) }
  intro α hα L hL L' hL' hl hl'
  refine aeIdent_comm_of_map_comm hΩ h2 hPΩ I hk hL hL' ?_ ?_
  · intro e
    subst e
    rw [hl] at hl'
    exact AE.memBar_true_ne_false (by norm_num) α hα hl'
  · rw [hl, hl']
    exact memBar_twin_comm α hα true

private theorem e16ic_eq_one_of_central {G : Type} [Group G] {Ω : Set (Subgroup G)} {u : G}
    (I : AEIdent (centMembers Ω u) 7) (hker : I.φ.ker = ⊥) {x : G}
    (hx : x ∈ pSpan (centMembers Ω u))
    (hcomm : ∀ y ∈ pSpan (centMembers Ω u), x * y = y * x) : x = 1 := by
  have hw : I.φ ⟨x, hx⟩ = 1 := by
    apply e16ic_eq_one_of_comm
    intro y hy
    rw [← I.range_eq] at hy
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
    show I.φ ⟨x, hx⟩ * I.φ z = I.φ z * I.φ ⟨x, hx⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm z.1 z.2)
  have hmem : (⟨x, hx⟩ : ↥(pSpan (centMembers Ω u))) ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, hw]
  rw [hker, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem e16ic_false_of_card_zGroup {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (h : EndHyp Ω) {u : G} (I : AEIdent (centMembers Ω u) 7)
    (hker : I.φ.ker = ⊥) (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hD : Nat.card (zGroup Ω) = 64) :
    False := by
  set S : Subgroup G :=
    Subgroup.closure {x | ∃ M ∈ centMembers Ω u, IsUniqueInvolution M x} with hSdef
  have hSD : S ≤ zGroup Ω :=
    Subgroup.closure_mono (fun x hx => by
      obtain ⟨M, hM, hMx⟩ := hx
      exact ⟨M, hM.1, hMx⟩)
  have hSY : S ≤ pSpan (centMembers Ω u) := by
    rw [hSdef, Subgroup.closure_le]
    rintro x ⟨M, hM, hMx⟩
    exact le_pSpan hM hMx.mem
  have hz : ∀ (α : Finset (Fin 7)) (hα : α.card = 4), ∃ x ∈ S,
      ∃ hx : x ∈ pSpan (centMembers Ω u), I.φ ⟨x, hx⟩ = zBar α hα := by
    intro α hα
    obtain ⟨M, hM, hlab⟩ := I.label_surj α hα true
    obtain ⟨⟨z, hz⟩, -⟩ := h.thmD.hyp.omega1 M hM.1
    exact ⟨z, Subgroup.subset_closure ⟨M, hM, hz⟩, le_pSpan hM hz.mem,
      I.map_eq_zBar (by norm_num) hM (h.card_eq_eight hM.1) hlab hz⟩
  have h64 := e16ic_card_ge (pSpan (centMembers Ω u)) S I.φ hSY hz
  have hSeq : S = zGroup Ω :=
    Subgroup.eq_of_le_of_card_ge hSD (by rw [hD]; exact h64)
  have huS : u ∈ pSpan (centMembers Ω u) := by
    have : u ∈ S := hSeq ▸ hu
    exact hSY this
  have hY : pSpan (centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hcomm : ∀ y ∈ pSpan (centMembers Ω u), u * y = y * u := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hY hy)).symm
  exact hu1 (e16ic_eq_one_of_central I hker huS hcomm)

private def e16ic_w (p q : Fin 6) (s t : ZMod 2) : Fin 6 → ZMod 2 :=
  fun x => (if x = p then s else 0) + (if x = q then t else 0)

private theorem e16ic_transfer {n : ℕ} (v w : Fin n → ZMod 2)
    (h : v + w = 0 ∨ v + w = fun _ => 1) (x y : Fin n) : v x + w x = v y + w y := by
  rcases h with h | h
  · have hx := congrFun h x
    have hy := congrFun h y
    simp only [Pi.add_apply, Pi.zero_apply] at hx hy
    rw [hx, hy]
  · have hx := congrFun h x
    have hy := congrFun h y
    simp only [Pi.add_apply] at hx hy
    rw [hx, hy]

private theorem e16ic_norm {γ : Finset (Fin 6)} (hγ : γ.card = 4) {p q : Fin 6} (hpq : p ≠ q)
    (hc : γᶜ = {p, q}) (v : Fin 6 → ZMod 2) (hv : ∀ i ∈ γ, ∀ j ∈ γ, v i = v j) :
    ∃ s t : ZMod 2, mkQ 6 (Wr.ofVec v) = mkQ 6 (Wr.ofVec (e16ic_w p q s t)) := by
  obtain ⟨i0, hi0⟩ : γ.Nonempty := Finset.card_pos.mp (by omega)
  have hpγ : p ∉ γ := by
    intro h
    have hp : p ∈ γᶜ := by rw [hc]; simp
    exact (Finset.mem_compl.mp hp) h
  have hqγ : q ∉ γ := by
    intro h
    have hq : q ∈ γᶜ := by rw [hc]; simp
    exact (Finset.mem_compl.mp hq) h
  have hout : ∀ x, x ∉ γ → x = p ∨ x = q := by
    intro x hx
    have hx' : x ∈ γᶜ := Finset.mem_compl.mpr hx
    rw [hc] at hx'
    simpa using hx'
  set c0 := v i0 with hc0
  have hc2 : ∀ c : ZMod 2, c + c = 0 := by decide
  have hkey : v + (fun _ => c0) = e16ic_w p q (v p + c0) (v q + c0) := by
    funext x
    by_cases hx : x ∈ γ
    · have hxp : x ≠ p := fun h => hpγ (h ▸ hx)
      have hxq : x ≠ q := fun h => hqγ (h ▸ hx)
      have hvx : v x = c0 := hv x hx i0 hi0
      simp only [Pi.add_apply, e16ic_w, if_neg hxp, if_neg hxq, hvx, add_zero]
      exact hc2 c0
    · rcases hout x hx with h | h
      · rw [h]
        simp [e16ic_w, hpq]
      · rw [h]
        simp [e16ic_w, hpq.symm]
  have hcc : c0 = 0 ∨ c0 = 1 := by
    have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    exact this c0
  refine ⟨v p + c0, v q + c0, ?_⟩
  rw [← hkey]
  rcases hcc with h0 | h1
  · rw [h0]
    congr 2
    funext x
    simp
  · rw [h1]
    rw [show (fun _ : Fin 6 => (1 : ZMod 2)) = fun _ => 1 from rfl, e16ic_mkQ_ofVec_add_one]

private theorem e16ic_exists_avoid (p q : Fin 6) (hpq : p ≠ q) :
    ∃ α : Finset (Fin 6), α.card = 4 ∧ p ∉ α ∧ q ∈ α := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k : Fin 6, k ≠ p ∧ k ≠ q := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (Fin 6)) ⊆ {p, q} := by
      intro x _
      by_cases hx : x = p
      · simp [hx]
      · simp [hcon x hx]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_pair hpq, Finset.card_univ, Fintype.card_fin] at h1
    omega
  refine ⟨Finset.univ \ {p, k}, ?_, ?_, ?_⟩
  · rw [Finset.card_univ_diff, Fintype.card_fin, Finset.card_pair (Ne.symm hk1)]
  · simp
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    exact ⟨fun h => hpq h.symm, fun h => hk2 h.symm⟩

private theorem e16ic_exists_ne {α : Finset (Fin 6)} (hα : α.card = 4) (a : Fin 6) :
    ∃ j ∈ α, j ≠ a := by
  by_contra hcon
  push_neg at hcon
  have hsub : α ⊆ {a} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
  have := Finset.card_le_card hsub
  rw [hα, Finset.card_singleton] at this
  omega

private theorem e16ic_exists_alpha {A : Type} [Group A] [Finite A] (F : A →* AEQ 6)
    (hinj : Function.Injective F) {p q : Fin 6} (hpq : p ≠ q)
    (hF : ∀ a : A, ∃ s t : ZMod 2, F a = mkQ 6 (Wr.ofVec (e16ic_w p q s t)))
    (hcard : 4 ≤ Nat.card A) (u : A) (hu : F u ≠ 1) :
    ∃ n : A, n ≠ 1 ∧ ∃ α : Finset (Fin 6), ∃ _hα : α.card = 4,
      (∀ v : Fin 6 → ZMod 2, F n = mkQ 6 (Wr.ofVec v) → ∀ i ∈ α, ∀ j ∈ α, v i = v j) ∧
      (∀ v : Fin 6 → ZMod 2, F u = mkQ 6 (Wr.ofVec v) → ¬ ∀ i ∈ α, ∀ j ∈ α, v i = v j) := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let V : Finset (AEQ 6) := Finset.univ.image
    (fun st : ZMod 2 × ZMod 2 => mkQ 6 (Wr.ofVec (e16ic_w p q st.1 st.2)))
  have hV : V.card ≤ 4 := by
    refine (Finset.card_image_le).trans ?_
    simp
  let S : Finset (AEQ 6) := Finset.univ.image F
  have hSV : S ⊆ V := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s, t, hst⟩ := hF a
    exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_univ _, hst.symm⟩
  have hScard : S.card = Nat.card A := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  have hSeq : S = V := Finset.eq_of_subset_of_card_le hSV (by omega)
  have hsurj : ∀ s t : ZMod 2, ∃ a : A, F a = mkQ 6 (Wr.ofVec (e16ic_w p q s t)) := by
    intro s t
    have hmem : mkQ 6 (Wr.ofVec (e16ic_w p q s t)) ∈ S := by
      rw [hSeq]
      exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_univ _, rfl⟩
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
    exact ⟨a, ha⟩
  obtain ⟨su, tu, hu_eq⟩ := hF u
  have hnz : ¬ (su = 0 ∧ tu = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hu
    rw [hu_eq, e16ic_mkQ_eq_one]
    left
    funext x
    simp [e16ic_w]
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hcase tu with htu | htu
  ·
    subst htu
    have hsu : su = 1 := by
      rcases hcase su with h | h
      · exact absurd ⟨h, rfl⟩ hnz
      · exact h
    subst hsu
    obtain ⟨α, hα, hqα, hpα⟩ := e16ic_exists_avoid q p hpq.symm
    obtain ⟨n, hn⟩ := hsurj 0 1
    obtain ⟨j, hjα, hjp⟩ := e16ic_exists_ne hα p
    have hjq : j ≠ q := fun h => hqα (h ▸ hjα)
    refine ⟨n, ?_, α, hα, ?_, ?_⟩
    · intro hn1
      rw [hn1, map_one, eq_comm, e16ic_mkQ_eq_one] at hn
      rcases hn with h0 | h1
      · have := congrFun h0 q
        simp [e16ic_w] at this
      · have := congrFun h1 j
        simp [e16ic_w, hjp, hjq] at this
    · intro v hv i hi i' hi'
      have h := (e16ic_mkQ_eq_iff_add v _).mp (hv.symm.trans hn)
      have hev := e16ic_transfer v (e16ic_w p q 0 1) h i i'
      have hwi : e16ic_w p q 0 1 i = 0 := by
        simp [e16ic_w, (show i ≠ q from fun h => hqα (h ▸ hi))]
      have hwi' : e16ic_w p q 0 1 i' = 0 := by
        simp [e16ic_w, (show i' ≠ q from fun h => hqα (h ▸ hi'))]
      rw [hwi, hwi', add_zero, add_zero] at hev
      exact hev
    · intro v hv hconst
      have h := (e16ic_mkQ_eq_iff_add v _).mp (hv.symm.trans hu_eq)
      have hev := e16ic_transfer v (e16ic_w p q 1 0) h p j
      have hwp : e16ic_w p q 1 0 p = 1 := by simp [e16ic_w, hpq]
      have hwj : e16ic_w p q 1 0 j = 0 := by simp [e16ic_w, hjp, hjq]
      rw [hwp, hwj, hconst p hpα j hjα, add_zero] at hev
      simp at hev
  ·
    subst htu
    obtain ⟨α, hα, hpα, hqα⟩ := e16ic_exists_avoid p q hpq
    obtain ⟨n, hn⟩ := hsurj 1 0
    obtain ⟨j, hjα, hjq⟩ := e16ic_exists_ne hα q
    have hjp : j ≠ p := fun h => hpα (h ▸ hjα)
    refine ⟨n, ?_, α, hα, ?_, ?_⟩
    · intro hn1
      rw [hn1, map_one, eq_comm, e16ic_mkQ_eq_one] at hn
      rcases hn with h0 | h1
      · have := congrFun h0 p
        simp [e16ic_w] at this
      · have := congrFun h1 j
        simp [e16ic_w, hjp, hjq] at this
    · intro v hv i hi i' hi'
      have h := (e16ic_mkQ_eq_iff_add v _).mp (hv.symm.trans hn)
      have hev := e16ic_transfer v (e16ic_w p q 1 0) h i i'
      have hwi : e16ic_w p q 1 0 i = 0 := by
        simp [e16ic_w, (show i ≠ p from fun h => hpα (h ▸ hi))]
      have hwi' : e16ic_w p q 1 0 i' = 0 := by
        simp [e16ic_w, (show i' ≠ p from fun h => hpα (h ▸ hi'))]
      rw [hwi, hwi', add_zero, add_zero] at hev
      exact hev
    · intro v hv hconst
      have h := (e16ic_mkQ_eq_iff_add v _).mp (hv.symm.trans hu_eq)
      have hev := e16ic_transfer v (e16ic_w p q su 1) h q j
      have hwq : e16ic_w p q su 1 q = 1 := by simp [e16ic_w, hpq.symm]
      have hwj : e16ic_w p q su 1 j = 0 := by simp [e16ic_w, hjp, hjq]
      rw [hwq, hwj, hconst q hqα j hjα, add_zero] at hev
      simp at hev

private theorem e16ic_card_range_le {D : Type} [Group D] [Finite D] (f : D →* AEQ 7)
    (hf : ∀ a : D, ∃ v : Fin 7 → ZMod 2, f a = mkQ 7 (Wr.ofVec v)) :
    Nat.card f.range ≤ 64 := by
  classical
  let T : Finset (AEQ 7) := (Finset.univ.filter
    (fun v : Fin 7 → ZMod 2 => ∑ i, v i = 0)).image (fun v => mkQ 7 (Wr.ofVec v))
  have hT : T.card ≤ 64 := by
    refine Finset.card_image_le.trans ?_
    rw [show (Finset.univ.filter (fun v : Fin 7 → ZMod 2 => ∑ i, v i = 0)).card = 64 from by
      decide +kernel]
  have hsub : (f.range : Set (AEQ 7)) ⊆ (T : Set (AEQ 7)) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨v, hv⟩ := hf a
    rw [hv]
    by_cases h0 : ∑ i, v i = 0
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, by simp [h0], rfl⟩)
    · have hsum : ∑ i, (v i + 1) = 0 := by
        rw [Finset.sum_add_distrib]
        have h1 : ∑ i : Fin 7, (1 : ZMod 2) = 1 := by decide
        rw [h1]
        have hz : ∀ c : ZMod 2, c ≠ 0 → c + 1 = 0 := by decide
        exact hz _ h0
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨fun i => v i + 1, by simp [hsum], ?_⟩)
      exact e16ic_mkQ_ofVec_add_one v
  calc Nat.card f.range = Nat.card (f.range : Set (AEQ 7)) := rfl
    _ ≤ Nat.card (T : Set (AEQ 7)) := Nat.card_mono (Set.toFinite _) hsub
    _ = T.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ ≤ 64 := hT

private theorem e16ic_card_le_ker_mul {D : Type} [Group D] [Finite D] (f : D →* AEQ 7)
    (hf : ∀ a : D, ∃ v : Fin 7 → ZMod 2, f a = mkQ 7 (Wr.ofVec v)) :
    Nat.card D ≤ 64 * Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.ker
  have h2 := Subgroup.index_ker f
  rw [h2] at h1
  rw [← h1, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (e16ic_card_range_le f hf)

private theorem e16ic_card_le_four {A : Type} [Group A] [Finite A] (F : A →* AEQ 6)
    (hinj : Function.Injective F) {p q : Fin 6} (hpq : p ≠ q)
    (hF : ∀ a : A, ∃ s t : ZMod 2, F a = mkQ 6 (Wr.ofVec (e16ic_w p q s t))) :
    Nat.card A ≤ 4 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let V : Finset (AEQ 6) := Finset.univ.image
    (fun st : ZMod 2 × ZMod 2 => mkQ 6 (Wr.ofVec (e16ic_w p q st.1 st.2)))
  have hV : V.card ≤ 4 := by
    refine (Finset.card_image_le).trans ?_
    simp
  let S : Finset (AEQ 6) := Finset.univ.image F
  have hSV : S ⊆ V := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s, t, hst⟩ := hF a
    exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_univ _, hst.symm⟩
  have hScard : S.card = Nat.card A := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  have := Finset.card_le_card hSV
  rw [hScard] at this
  omega

theorem false_of_aeIdent_seven_Y (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (hn : Nonempty (AEIdent (centMembers Ω u) 7)) : False := by
  obtain ⟨I⟩ := hn
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have h2 : ∀ L ∈ Ω, IsPGroup 2 L := h.thmD.two
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  have hu : u ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).1
  have he : e ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).2
  have hu1 : u ≠ 1 := c.data.hu1
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ hL => hL.1
  have hO : classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥ :=
    EndHyp.oddCore_centMembers_eq_bot h h9 c.twin h13 hu hu1
  have hinv : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u :=
    fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx
  have htrans := centMembers_u_oneClass c h h9 h13
  have hY : pSpan (centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hs : TwinSit Ω (conjSub g K) (conjSub g K') (u * e) := by
    have := TwinSit.conj c.twin hΩc g
    rwa [c.data.hgt] at this
  have hJ : conjSub g K ∈ centMembers Ω u :=
    ⟨((c.conjSub_mem h h9).2.1).1, (c.conjSub_le_centralizer_u h h9).1⟩
  have hJ' : conjSub g K' ∈ centMembers Ω u :=
    ⟨hs.mem_twin.1, (c.conjSub_le_centralizer_u h h9).2⟩
  have hne : conjSub g K ≠ conjSub g K' := fun heq => c.twin.ne (conjSub_injective g heq)
  have hH := e16ic_aeCoverHyp h I hO hinv htrans hJ hJ' hs.isInv hs.mem_twin.2 hne
  have hker : I.φ.ker = ⊥ :=
    TL4.aeCoverOddKer_proved G (centMembers Ω u) 7 I (by norm_num) (by decide) hH
  have hD64 : Nat.card (zGroup Ω) ≠ 64 := fun hD => e16ic_false_of_card_zGroup h I hker hu hu1 hD
  have hE : ¬ eGroup Ω K ≤ K ⊔ K' := fun hle =>
    (c.mul_mem_eGroup h h9).2 (hle (c.mul_mem_eGroup h h9).1)
  have h64 : 64 ≤ Nat.card (zGroup Ω) := EndHyp.sixtyFour_le_natCard_zGroup h h9 c.twin h13 hE
  obtain ⟨m, hm⟩ := h.natCard_zGroup_eq_four_pow h9 c.twin h13
  have hAD : ∀ d ∈ zGroup Ω, (∀ L ∈ centMembers Ω u, conjSub d L ∈ centMembers Ω u) ∧
      ∀ L ∈ centMembers Ω u, ∀ r : G, IsUniqueInvolution L r → d * r = r * d := by
    intro d hd
    refine ⟨fun L hL => ?_, fun L hL r hr => ?_⟩
    · have hdu : d * u = u * d := h.zGroup_comm h9 d hd u hu
      have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩc hL (n := d)
      rwa [show d * u * d⁻¹ = u by rw [hdu, mul_inv_cancel_right]] at hc
    · have hrD : r ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL.1, hr⟩
      exact h.zGroup_comm h9 d hd r hrD
  obtain ⟨fP, hfP, hfPker⟩ := exists_vecHom_of_aeIdent hΩ h2 hPΩ hinv (by norm_num)
    (by norm_num) I (I.isPGroup_ker hO) (zGroup Ω) hAD
  have hfPform : ∀ a : ↥(zGroup Ω), ∃ v : Fin 7 → ZMod 2, fP a = mkQ 7 (Wr.ofVec v) :=
    fun a => (hfP a).imp fun v hv => hv.1
  have hcardD : Nat.card (zGroup Ω) ≤ 64 * Nat.card fP.ker := e16ic_card_le_ker_mul fP hfPform
  set N : Subgroup G := zGroup Ω ⊓ Subgroup.centralizer ((pSpan (centMembers Ω u) : Subgroup G) :
    Set G) with hNdef
  have hmemN : ∀ a : G, a ∈ N ↔ a ∈ zGroup Ω ∧ ∀ x ∈ pSpan (centMembers Ω u), a * x = x * a := by
    intro a
    rw [hNdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (h2 x hx).symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (h2 x hx).symm⟩
  have hkerN_mem : ∀ a : fP.ker, (a.1 : G) ∈ N := by
    intro a
    rw [hmemN]
    refine ⟨(a.1).2, ?_⟩
    have ha : fP a.1 = 1 := a.2
    exact fun x hx => ((hfPker a.1).mp ha) x hx
  have hkerN : Nat.card fP.ker ≤ Nat.card N := by
    refine Nat.card_le_card_of_injective (fun a => (⟨(a.1 : G), hkerN_mem a⟩ : ↥N)) ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨IX, -, hIX, -, -, -, -⟩ := exists_equiv_X c h h9 h13
  have hPeΩ : centMembers Ω e ⊆ Ω := fun _ hL => hL.1
  have hcomm_e : ∀ x ∈ pSpan (centMembers Ω e), x * e = e * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun L hL => hL.2) hx)
  have hinvE : ∀ L ∈ centMembers Ω e, ∀ x ∈ pSpan (centMembers Ω e),
      conjSub x L ∈ centMembers Ω e := by
    intro L hL x hx
    have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩc hL (n := x)
    rwa [show x * e * x⁻¹ = e by rw [hcomm_e x hx, mul_inv_cancel_right]] at hc
  have hAN : ∀ d ∈ N, (∀ L ∈ centMembers Ω e, conjSub d L ∈ centMembers Ω e) ∧
      ∀ L ∈ centMembers Ω e, ∀ r : G, IsUniqueInvolution L r → d * r = r * d := by
    intro d hd
    have hdD : d ∈ zGroup Ω := ((hmemN d).mp hd).1
    have hde : d * e = e * d := h.zGroup_comm h9 d hdD e he
    refine ⟨fun L hL => ?_, fun L hL r hr => ?_⟩
    · have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩc hL (n := d)
      rwa [show d * e * d⁻¹ = e by rw [hde, mul_inv_cancel_right]] at hc
    · have hrD : r ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL.1, hr⟩
      exact h.zGroup_comm h9 d hdD r hrD
  obtain ⟨fX, hfX, hfXker⟩ := exists_vecHom_of_aeIdent hΩ h2 hPeΩ hinvE (by norm_num)
    (by norm_num) IX hIX.ker_two N hAN
  have hJe : conjSub g K ∈ centMembers Ω e := dSet_subset_centMembers c h (c.conjSub_mem h h9).1
  obtain ⟨γ, hγ, bJ, hlabJ⟩ := IX.label _ hJe
  have hcentJ : ∀ a : G, a ∈ N → ∀ l ∈ conjSub g K, a * l = l * a := fun a ha l hl =>
    ((hmemN a).mp ha).2 l (le_pSpan hJ hl)
  have hFconst : ∀ a : ↥N, ∃ v : Fin 6 → ZMod 2, fX a = mkQ 6 (Wr.ofVec v) ∧
      ∀ i ∈ γ, ∀ j ∈ γ, v i = v j := by
    intro a
    obtain ⟨v, hv, hiff⟩ := hfX a
    exact ⟨v, hv, ((hiff (conjSub g K) hJe γ hγ bJ hlabJ).2).mp (hcentJ a a.2)⟩
  have hkerfX : ∀ a : ↥N, fX a = 1 → (a : G) = 1 := by
    intro a ha
    have hcentX := (hfXker a).mp ha
    have hcentY := ((hmemN a).mp a.2).2
    have hXY : pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) ≤
        Subgroup.centralizer ({(a : G)} : Set G) := by
      apply sup_le
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentX x hx).symm
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentY x hx).symm
    rw [pSpan_sup_eq_top_of_X c h h9 h13] at hXY
    have hxc : (a : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXY (Subgroup.mem_top g'))
    rw [h.center] at hxc
    exact Subgroup.mem_bot.mp hxc
  have hFinj : Function.Injective fX := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hkerfX a ha)
  have hcompl : γᶜ.card = 2 := by
    rw [Finset.card_compl, hγ]
    simp
  obtain ⟨p, q, hpq, hpqc⟩ := Finset.card_eq_two.mp hcompl
  have hFform : ∀ a : ↥N, ∃ s t : ZMod 2, fX a = mkQ 6 (Wr.ofVec (e16ic_w p q s t)) := by
    intro a
    obtain ⟨v, hv, hconst⟩ := hFconst a
    obtain ⟨s, t, hst⟩ := e16ic_norm hγ hpq hpqc v hconst
    exact ⟨s, t, hv.trans hst⟩
  have hcard4 : Nat.card N ≤ 4 := e16ic_card_le_four fX hFinj hpq hFform
  have hD256 : Nat.card (zGroup Ω) ≤ 256 := by omega
  have hD : Nat.card (zGroup Ω) = 256 := by
    have hm4 : m ≤ 4 := by
      by_contra hc
      push_neg at hc
      have : 4 ^ 5 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hc
      omega
    interval_cases m <;> omega
  have hN4 : 4 ≤ Nat.card N := by omega
  have huN : u ∈ N := (hmemN u).mpr ⟨hu, fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp
    (hY hx)).symm⟩
  have hu' : fX ⟨u, huN⟩ ≠ 1 := fun h1 => hu1 (hkerfX ⟨u, huN⟩ h1)
  obtain ⟨n, hn1, α, hα, hnconst, huncon⟩ :=
    e16ic_exists_alpha fX hFinj hpq hFform hN4 ⟨u, huN⟩ hu'
  obtain ⟨M, hM, hlabM⟩ := IX.label_surj α hα true
  obtain ⟨vn, hvn, hivn⟩ := hfX n
  have hnM : ∀ l ∈ M, (n : G) * l = l * (n : G) :=
    ((hivn M hM α hα true hlabM).2).mpr (hnconst vn hvn)
  have hMu : M ∉ centMembers Ω u := by
    intro hMP
    obtain ⟨vu, hvu, hiu⟩ := hfX ⟨u, huN⟩
    have hcu : ∀ l ∈ M, u * l = l * u := fun l hl =>
      ((Generic.mem_centMembers_iff_commute.mp hMP).2 l hl).symm
    exact huncon vu hvu (((hiu M hM α hα true hlabM).2).mp hcu)
  have hPcard : (centMembers Ω u).ncard = 70 := by
    rw [EndHyp.ncard_eq_of_aeIdent h hPΩ hinv hO (by norm_num) (by norm_num) I]
    norm_num [Nat.choose]
  have hsub : insert M (centMembers Ω u) ⊆ centMembers Ω (n : G) := by
    intro L hL
    rcases hL with rfl | hL
    · exact Generic.mem_centMembers_iff_commute.mpr ⟨hM.1, fun l hl => (hnM l hl).symm⟩
    · exact Generic.mem_centMembers_iff_commute.mpr
        ⟨hPΩ hL, fun l hl => (((hmemN (n : G)).mp n.2).2 l (le_pSpan hL hl)).symm⟩
  have hcardM : 71 ≤ (centMembers Ω (n : G)).ncard := by
    have h1 : (insert M (centMembers Ω u)).ncard = 71 := by
      rw [Set.ncard_insert_of_notMem hMu (Set.toFinite _), hPcard]
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hnne1 : (n : G) ≠ 1 := fun h1 => hn1 (Subtype.ext h1)
  have hJn : conjSub g K ∈ centMembers Ω (n : G) :=
    Generic.mem_centMembers_iff_commute.mpr
      ⟨hJ.1, fun l hl => (((hmemN (n : G)).mp n.2).2 l (le_pSpan hJ hl)).symm⟩
  have hJ'n : conjSub g K' ∈ centMembers Ω (n : G) :=
    Generic.mem_centMembers_iff_commute.mpr
      ⟨hJ'.1, fun l hl => (((hmemN (n : G)).mp n.2).2 l (le_pSpan hJ' hl)).symm⟩
  have hne2 : centMembers Ω (n : G) ≠ {conjSub g K, conjSub g K'} := fun heq => by
    rw [heq, Set.ncard_pair hne] at hcardM
    omega
  rcases EndHyp.centMembers_cases h h9 hnne1 hs hJn hJ'n with hpair | ⟨-, hOR⟩
  · rw [hpair, Set.ncard_pair hne] at hcardM
    omega
  · have hO_n : classicalInvolutionOddCore ↥(pSpan (centMembers Ω (n : G))) = ⊥ :=
      EndHyp.oddCore_centMembers_eq_bot h h9 c.twin h13 ((hmemN n).mp n.2).1 hnne1
    have hinv_n : ∀ L ∈ centMembers Ω (n : G), ∀ x ∈ pSpan (centMembers Ω (n : G)),
        conjSub x L ∈ centMembers Ω (n : G) :=
      fun L hL x hx => StarHyp.conjSub_mem_centMembers h.toStarHyp hL hx
    have hΩn : centMembers Ω (n : G) ⊆ Ω := fun _ hL => hL.1
    rcases hOR with ⟨W₀, hW⟩ | ⟨m', hm5, hm7, ⟨I'⟩⟩ | ⟨I'⟩
    · have := EndHyp.ncard_eq_six_of_uniqueW h h9 hnne1 hs hJn hJ'n hne2 ⟨W₀, hW⟩
      omega
    · have hc := EndHyp.ncard_eq_of_aeIdent h hΩn hinv_n hO_n hm5 (by omega) I'
      have hch : m'.choose 4 ≤ 35 := by
        interval_cases m' <;> decide
      omega
    · obtain ⟨I''⟩ := I'
      have := EndHyp.ncard_eq_fourteen_of_e64 h hΩn hinv_n hO_n I''
      omega

end E16ic

theorem exists_aeIdent_five_Y (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    Nonempty (AEIdent (centMembers Ω u) 5) := by
  rcases sectionOutcomeRestricted_centMembers_u c h h9 h13 with ⟨W₀, hW⟩ | ⟨n, hn5, hn7, hn⟩ | hn
  · exact (false_of_uniqueW_Y c h h9 h13 ⟨W₀, hW⟩).elim
  · interval_cases n
    · exact hn
    · exact (false_of_aeIdent_six_Y c h h9 h13 hn).elim
    · exact (false_of_aeIdent_seven_Y c h h9 h13 hn).elim
  · exact (false_of_e64_Y c h h9 h13 hn).elim

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
