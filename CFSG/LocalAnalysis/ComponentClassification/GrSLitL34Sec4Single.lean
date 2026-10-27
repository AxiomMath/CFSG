module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputsHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsSingle
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46W
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrDihedralWitness

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem subgroupOf_map_subtype_eq' {M : Subgroup X} (L : Subgroup M) :
    (L.map M.subtype).subgroupOf M = L := by
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]

omit [Finite X] in
theorem self_le_normalizer_oddIn (M : Subgroup X) :
    M ≤ normalizer ((oddIn M : Subgroup X) : Set X) :=
  fun m hm => mem_normalizer_iff.mpr fun y => ⟨fun hy => conj_mem_oddIn hm hy, fun hy => by
    have := conj_mem_oddIn (inv_mem hm) hy
    rwa [show m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y by group] at this⟩

theorem conj_mem_oddIn_of_mem_normalizer {K : Subgroup X} {g o : X}
    (hg : g ∈ normalizer (K : Set X)) (ho : o ∈ oddIn K) : g * o * g⁻¹ ∈ oddIn K := by
  set K₁ : Subgroup X := K ⊔ zpowers g with hK₁
  have hKK₁ : K ≤ K₁ := le_sup_left
  have hK₁N : K₁ ≤ normalizer (K : Set X) := sup_le le_normalizer (zpowers_le.mpr hg)
  have h1 : oddIn K ≤ oddIn K₁ := map_pPrimeCore_le_of_le_normalizer hKK₁ hK₁N
  have h2 : g * o * g⁻¹ ∈ oddIn K₁ := conj_mem_oddIn (mem_sup_right (mem_zpowers g)) (h1 ho)
  have h3 : g * o * g⁻¹ ∈ K := (mem_normalizer_iff.mp hg o).mp (map_subtype_le _ ho)
  exact GrS5.inf_oddIn_le_oddIn hKK₁ (mem_inf.mpr ⟨h2, h3⟩)

theorem not_odd_card_of_isPComponent {C J : Subgroup X} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : ¬ Odd (Nat.card J) := by
  intro hodd
  apply not_le_coreActionKernel_self hJC hJ
  have htop : (⊤ : Subgroup J) ≤ pPrimeCore 2 J :=
    le_pPrimeCore_of_normal_of_odd inferInstance (by rwa [card_top])
  intro g hg
  refine mem_coreActionKernel.mpr ⟨le_normalizer hg, fun j hj => ?_⟩
  exact ⟨⟨j⁻¹ * g⁻¹ * j * g, mul_mem (mul_mem (mul_mem (inv_mem hj) (inv_mem hg)) hj) hg⟩,
    htop (mem_top _), rfl⟩

omit [Finite X] in
theorem isPerfect_subgroupOf {J M : Subgroup X} (hJM : J ≤ M) (hJ : ⁅J, J⁆ = J) :
    Group.IsPerfect ↥(J.subgroupOf M) := by
  have h2 : Group.IsPerfect ↥J := (Subgroup.isPerfect_iff (H := J)).mpr hJ
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hJM).symm.surjective

theorem le_normalizer_of_isPComponent {J H : Subgroup X}
    (hT : ∀ g : X, ¬ ⁅J, conjugate J g⁆ ≤ oddIn J ⊓ oddIn (conjugate J g))
    (hJH : J ≤ H) (hJ : IsPComponent 2 (J.subgroupOf H)) : H ≤ normalizer (J : Set X) := by
  intro c hc
  apply UnbalancedLayer.mem_normalizer_of_conjugate_eq
  by_contra hne
  exact hT c (GrS5.commutator_le_inf_oddIn hJH (conjugate_le_of_mem hJH hc) hJ
    (isPComponent_conjugate_subgroupOf hc hJ) fun h => hne h.symm)

theorem oddIn_le_normalizer_of_isPComponent {K M : Subgroup X} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) : oddIn M ≤ normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact mem_normalizer_of_subgroupOf hKM (pPrimeCore_le_normalizer hK hm)

theorem le_of_sup_oddIn_eq {J K M : Subgroup X} (hJM : J ≤ M) (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) (hJ : ⁅J, J⁆ = J)
    (hsup : J ⊔ oddIn M = K ⊔ oddIn M) : J ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Odd (Nat.card (pPrimeCore 2 M)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hTKR : J.subgroupOf M ≤ K.subgroupOf M ⊔ pPrimeCore 2 M := by
    intro y hy
    have hy' : (y : X) ∈ K ⊔ oddIn M := hsup ▸ mem_sup_left hy
    have h1 : y ∈ (K ⊔ oddIn M).subgroupOf M := hy'
    unfold oddIn at h1
    rwa [subgroupOf_sup hKM (map_subtype_le _), subgroupOf_map_subtype_eq'] at h1
  intro j hj
  exact le_of_perfect_le_sup_of_odd hR (pPrimeCore_le_normalizer hK)
    (isPerfect_subgroupOf hJM hJ) hTKR (show (⟨j, hJM hj⟩ : M) ∈ J.subgroupOf M from hj)

theorem eq_sup_oddIn_of_sup_eq {J K M : Subgroup X} (hJK : J ≤ K) (hKM : K ≤ M)
    (hsup : J ⊔ oddIn M = K ⊔ oddIn M) : K = J ⊔ oddIn K := by
  refine le_antisymm (fun k hk => ?_) (sup_le hJK (map_subtype_le _))
  have hk' : k ∈ J ⊔ oddIn M := hsup ▸ mem_sup_left hk
  have hJN : J ≤ normalizer ((oddIn M : Subgroup X) : Set X) :=
    (hJK.trans hKM).trans (self_le_normalizer_oddIn M)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hJN] at hk'
  obtain ⟨j, hj, o, ho, rfl⟩ := hk'
  have hoK : o ∈ K := by
    have h1 := mul_mem (inv_mem (hJK hj)) hk
    rwa [inv_mul_cancel_left] at h1
  exact mul_mem_sup hj (GrS5.inf_oddIn_le_oddIn hKM (mem_inf.mpr ⟨ho, hoK⟩))

theorem oddIn_le_oddIn_of_eq_sup {J K : Subgroup X} (hJK : J ≤ K) (hKJ : K = J ⊔ oddIn K) :
    oddIn J ≤ oddIn K := by
  set N : Subgroup X := oddIn J ⊔ oddIn K with hN
  have hOJK : oddIn J ≤ K := (map_subtype_le _).trans hJK
  have hNK : N ≤ K := sup_le hOJK (map_subtype_le _)
  have hJN : J ≤ normalizer (N : Set X) := by
    intro j hj
    rw [mem_normalizer_iff_map_conj_eq, hN, Subgroup.map_sup]
    have h1 := mem_normalizer_iff_map_conj_eq.mp (self_le_normalizer_oddIn J hj)
    have h2 := mem_normalizer_iff_map_conj_eq.mp (self_le_normalizer_oddIn K (hJK hj))
    rw [h1, h2]
  have hON : oddIn K ≤ normalizer (N : Set X) := by
    have hmap : ∀ o ∈ oddIn K, N.map (MulAut.conj o).toMonoidHom ≤ N := by
      intro o ho
      rw [hN, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        have hxK : x ∈ K := hOJK hx
        have hc : o * (x * o⁻¹ * x⁻¹) ∈ oddIn K := mul_mem ho (conj_mem_oddIn hxK (inv_mem ho))
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show o * x * o⁻¹ = (o * (x * o⁻¹ * x⁻¹)) * x by group]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
      · rintro _ ⟨x, hx, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right (conj_mem_oddIn (map_subtype_le _ ho) hx)
    intro o ho
    rw [mem_normalizer_iff_map_conj_eq]
    exact eq_of_le_of_card_ge (hmap o ho)
      (by rw [card_map_of_injective (MulAut.conj o).injective])
  have hKN : K ≤ normalizer (N : Set X) := by
    rw [hKJ]
    exact sup_le hJN hON
  have hoddJ : Odd (Nat.card (oddIn J)) := odd_card_map_pPrimeCore J
  have hoddK : Odd (Nat.card (oddIn K)) := odd_card_map_pPrimeCore K
  have hcard := card_sup_mul_inf_eq_mul_of_normalizes
    (hOJK.trans (self_le_normalizer_oddIn K))
  have hoddN : Odd (Nat.card N) :=
    Odd.of_dvd_nat (hoddJ.mul hoddK) (Dvd.intro _ hcard)
  have hNn : (N.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hNodd : Odd (Nat.card (N.subgroupOf K)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNK).toEquiv]
  have hle := le_pPrimeCore_of_normal_of_odd hNn hNodd
  intro x hx
  have hxN : x ∈ N := mem_sup_left hx
  exact ⟨⟨x, hNK hxN⟩, hle (show (⟨x, hNK hxN⟩ : K) ∈ N.subgroupOf K from hxN), rfl⟩

theorem fstar_facts_of_gsMaximalSetting {a : X} {J : Subgroup X} (h : GSMaximalSetting X a J) :
    IsSimpleGroup (GeneralizedFitting.subgroup X) ∧
      (∃ u v : GeneralizedFitting.subgroup X, u * v ≠ v * u) ∧
      ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup X) := by
  have : IsSimpleGroup X := h.simple
  have htop : GeneralizedFitting.subgroup X = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  refine ⟨eF.isSimpleGroup, ?_, fun hL => h.notU (Or.inl hL)⟩
  obtain ⟨u, v, huv⟩ := h.nonabelian
  exact ⟨eF.symm u, eF.symm v, fun h' => huv (eF.symm.injective (by rw [map_mul, map_mul, h']))⟩

theorem iSup_conjugate_le_of_gsMaximalSetting (hMax : MaximalTwoComponentInput) {a : X}
    {J : Subgroup X} (h : GSMaximalSetting X a J) :
    (⨆ (g : X) (_ : conjugate J g ≤ centralizer ({a} : Set X)), conjugate J g) ≤
      oddIn (centralizer ({a} : Set X)) ⊔ J := by
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts_of_gsMaximalSetting h
  have : IsSimpleGroup X := h.simple
  exact (hMax X hsF hnF hoF h.kProper J h.maximal (by have := h.rank; omega) h.not_sp4 h.type a
    h.orderOf_eq h.le_centralizer).1

theorem not_commutator_le_of_gsMaximalSetting (hMax : MaximalTwoComponentInput) {a : X}
    {J : Subgroup X} (h : GSMaximalSetting X a J) (g : X) :
    ¬ ⁅J, conjugate J g⁆ ≤ oddIn J ⊓ oddIn (conjugate J g) := by
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts_of_gsMaximalSetting h
  have : IsSimpleGroup X := h.simple
  exact (hMax X hsF hnF hoF h.kProper J h.maximal (by have := h.rank; omega) h.not_sp4 h.type a
    h.orderOf_eq h.le_centralizer).2 h.rank g

theorem not_commutator_le_of_gsMaximalSetting_he (hMax : MaximalTwoComponentInputHe) {a : X}
    {J : Subgroup X} (h : GSMaximalSetting X a J) (hHe : IsHeldType (J ⧸ Open.fusionZStar J))
    (g : X) : ¬ ⁅J, conjugate J g⁆ ≤ oddIn J ⊓ oddIn (conjugate J g) := by
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts_of_gsMaximalSetting h
  have : IsSimpleGroup X := h.simple
  exact (hMax X hsF hnF hoF h.kProper J h.maximal (by have := h.rank; omega) h.not_sp4 hHe a
    h.orderOf_eq h.le_centralizer).2 h.rank g

theorem commutator_eq_self_of_gsMaximalSetting {a : X} {J : Subgroup X}
    (h : GSMaximalSetting X a J) : ⁅J, J⁆ = J :=
  GSThmB.commutator_eq_self_of_isPComponent h.le_centralizer h.isPComponent

theorem centralizer_le_normalizer_of_gsMaximalSetting (hMax : MaximalTwoComponentInput) {a : X}
    {J : Subgroup X} (h : GSMaximalSetting X a J) :
    centralizer ({a} : Set X) ≤ normalizer (J : Set X) :=
  le_normalizer_of_isPComponent (not_commutator_le_of_gsMaximalSetting hMax h) h.le_centralizer
    h.isPComponent

theorem centralizer_le_normalizer_of_gsMaximalSetting_he (hMax : MaximalTwoComponentInputHe)
    {a : X} {J : Subgroup X} (h : GSMaximalSetting X a J)
    (hHe : IsHeldType (J ⧸ Open.fusionZStar J)) :
    centralizer ({a} : Set X) ≤ normalizer (J : Set X) :=
  le_normalizer_of_isPComponent (not_commutator_le_of_gsMaximalSetting_he hMax h hHe)
    h.le_centralizer h.isPComponent

theorem conjugate_eq_of_le_centralizer (hMax : MaximalTwoComponentInput) {a : X}
    {J : Subgroup X} (h : GSMaximalSetting X a J) {g : X}
    (hg : conjugate J g ≤ centralizer ({a} : Set X)) : conjugate J g = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := centralizer ({a} : Set X) with hC
  have hle : conjugate J g ≤ oddIn C ⊔ J :=
    (le_iSup₂_of_le g hg le_rfl).trans (iSup_conjugate_le_of_gsMaximalSetting hMax h)
  have hJ := commutator_eq_self_of_gsMaximalSetting h
  have hJg : ⁅conjugate J g, conjugate J g⁆ = conjugate J g := by
    show ⁅J.map _, J.map _⁆ = J.map _
    rw [← map_commutator, hJ]
  have hR : Odd (Nat.card (pPrimeCore 2 C)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hTKR : (conjugate J g).subgroupOf C ≤ J.subgroupOf C ⊔ pPrimeCore 2 C := by
    intro y hy
    have h1 : y ∈ (oddIn C ⊔ J).subgroupOf C := hle hy
    unfold oddIn at h1
    rwa [subgroupOf_sup (map_subtype_le _) h.le_centralizer, subgroupOf_map_subtype_eq',
      sup_comm] at h1
  have h1 := le_of_perfect_le_sup_of_odd hR (pPrimeCore_le_normalizer h.isPComponent)
    (isPerfect_subgroupOf hg hJg) hTKR
  have hle' : conjugate J g ≤ J := fun y hy =>
    h1 (show (⟨y, hg hy⟩ : C) ∈ (conjugate J g).subgroupOf C from hy)
  exact eq_of_le_of_card_ge hle' (card_map_of_injective (MulAut.conj g⁻¹).injective).ge

section Setting

variable {a : X} {J W K : Subgroup X}

theorem centralizer_le_of_singleComponentSetting (hMax : MaximalTwoComponentInput)
    (hs : SingleComponentSetting X a J W K) :
    centralizer ({a} : Set X) ≤ normalizer (W : Set X) :=
  (centralizer_le_normalizer_of_gsMaximalSetting hMax hs.toGSMaximalSetting).trans
    hs.normalizer_le

theorem centralizer_le_of_singleComponentSetting_he (hMax : MaximalTwoComponentInputHe)
    (hs : SingleComponentSetting X a J W K) (hHe : IsHeldType (J ⧸ Open.fusionZStar J)) :
    centralizer ({a} : Set X) ≤ normalizer (W : Set X) :=
  (centralizer_le_normalizer_of_gsMaximalSetting_he hMax hs.toGSMaximalSetting hHe).trans
    hs.normalizer_le

theorem le_normalizer_of_singleComponentSetting (hs : SingleComponentSetting X a J W K) :
    J ≤ normalizer (W : Set X) :=
  le_normalizer.trans hs.normalizer_le

theorem le_of_singleComponentSetting (hs : SingleComponentSetting X a J W K) : J ≤ K :=
  le_of_sup_oddIn_eq (le_normalizer_of_singleComponentSetting hs) hs.le_normalizer
    hs.isPComponent_K (commutator_eq_self_of_gsMaximalSetting hs.toGSMaximalSetting) hs.sup_eq

theorem eq_sup_oddIn_of_singleComponentSetting (hs : SingleComponentSetting X a J W K) :
    K = J ⊔ oddIn K :=
  eq_sup_oddIn_of_sup_eq (le_of_singleComponentSetting hs) hs.le_normalizer hs.sup_eq

theorem oddIn_eq_inf_of_singleComponentSetting (hs : SingleComponentSetting X a J W K) :
    oddIn J = J ⊓ oddIn (normalizer (W : Set X)) := by
  have hJK := le_of_singleComponentSetting hs
  refine le_antisymm (le_inf (map_subtype_le _) ((oddIn_le_oddIn_of_eq_sup hJK
    (eq_sup_oddIn_of_singleComponentSetting hs)).trans
    (GSLit.map_pPrimeCore_le_of_isPComponent hs.le_normalizer hs.isPComponent_K))) ?_
  rw [inf_comm]
  exact GrS5.inf_oddIn_le_oddIn (le_normalizer_of_singleComponentSetting hs)

theorem mem_coreActionKernel_of_singleComponentSetting_of_mem
    (hs : SingleComponentSetting X a J W K) (haM : a ∈ normalizer (W : Set X)) :
    a ∈ coreActionKernel K := by
  have h := hs.toGSMaximalSetting
  have hJK := le_of_singleComponentSetting hs
  have hKM := hs.le_normalizer
  have hKa : conjugate K a = K := by
    by_contra hne
    have hc := GrS5.commutator_le_inf_oddIn hKM (conjugate_le_of_mem hKM haM) hs.isPComponent_K
      (isPComponent_conjugate_subgroupOf haM hs.isPComponent_K) fun e => hne e.symm
    have hJK' : J ≤ conjugate K a := fun y hy => by
      have hya : y * a = a * y := mem_centralizer_singleton_iff.mp (h.le_centralizer hy)
      rw [UnbalancedLayer.mem_conjugate_iff, ← hya, mul_inv_cancel_right]
      exact hJK hy
    have hJO : J ≤ oddIn K := by
      rw [← commutator_eq_self_of_gsMaximalSetting h]
      exact (commutator_mono hJK hJK').trans (hc.trans inf_le_left)
    exact not_odd_card_of_isPComponent h.le_centralizer h.isPComponent
      (Odd.of_dvd_nat (odd_card_map_pPrimeCore K) (card_dvd_of_le hJO))
  have haN : a ∈ normalizer (K : Set X) := UnbalancedLayer.mem_normalizer_of_conjugate_eq hKa
  refine mem_coreActionKernel.mpr ⟨haN, fun k hk => ?_⟩
  have hset : ((K : Subgroup X) : Set X) = (J : Set X) * (oddIn K : Set X) := by
    conv_lhs => rw [eq_sup_oddIn_of_singleComponentSetting hs]
    exact coe_mul_of_left_le_normalizer_right _ _ (hJK.trans (self_le_normalizer_oddIn K))
  have hk' : k ∈ (J : Set X) * (oddIn K : Set X) := hset ▸ hk
  obtain ⟨j, hj, o, ho, rfl⟩ := hk'
  beta_reduce
  have hc : Commute j a⁻¹ :=
    Commute.inv_right (mem_centralizer_singleton_iff.mp (h.le_centralizer hj))
  have e : (j * o)⁻¹ * a⁻¹ * (j * o) * a = o⁻¹ * (a⁻¹ * o * a⁻¹⁻¹) := by
    calc (j * o)⁻¹ * a⁻¹ * (j * o) * a = o⁻¹ * j⁻¹ * (a⁻¹ * j) * o * a := by group
      _ = o⁻¹ * j⁻¹ * (j * a⁻¹) * o * a := by rw [← hc.eq]
      _ = o⁻¹ * (a⁻¹ * o * a⁻¹⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem ho) (conj_mem_oddIn_of_mem_normalizer (inv_mem haN) ho)

theorem mem_coreActionKernel_of_singleComponentSetting (hMax : MaximalTwoComponentInput)
    (hs : SingleComponentSetting X a J W K) : a ∈ coreActionKernel K :=
  mem_coreActionKernel_of_singleComponentSetting_of_mem hs
    (centralizer_le_of_singleComponentSetting hMax hs (mem_centralizer_singleton_iff.mpr rfl))

theorem mem_coreActionKernel_of_singleComponentSetting_he (hMax : MaximalTwoComponentInputHe)
    (hs : SingleComponentSetting X a J W K) (hHe : IsHeldType (J ⧸ Open.fusionZStar J)) :
    a ∈ coreActionKernel K :=
  mem_coreActionKernel_of_singleComponentSetting_of_mem hs
    (centralizer_le_of_singleComponentSetting_he hMax hs hHe
      (mem_centralizer_singleton_iff.mpr rfl))

theorem normalizer_eq_of_eq (hMax : MaximalTwoComponentInput)
    (hs : SingleComponentSetting X a J W K) (hKJ : K = J) :
    normalizer (W : Set X) = normalizer (J : Set X) := by
  refine le_antisymm ?_ hs.normalizer_le
  have hJM : J ≤ normalizer (W : Set X) := by rw [← hKJ]; exact hs.le_normalizer
  have hJc : IsPComponent 2 (J.subgroupOf (normalizer (W : Set X))) := by
    rw [← hKJ]; exact hs.isPComponent_K
  exact le_normalizer_of_isPComponent
    (not_commutator_le_of_gsMaximalSetting hMax hs.toGSMaximalSetting) hJM hJc

end Setting

end CFSG.ComponentClassification.GrSLit.GrS4
