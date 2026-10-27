module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Diag
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple

public section

namespace CFSG.ComponentClassification.GSThmB.CF23Diag

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4
open scoped commutatorElement

theorem eq_top_or_le_center_of_isSubnormal {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    {U : Subgroup Q} (hU : U.IsSubnormal) : U = ⊤ ∨ U ≤ center Q := by
  exact CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQ hU

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem D_le_JB : h.D ≤ GSLit.fixedLayer h.J h.B := by
  rw [GSLit.fixedLayer_eq_closure h.isQuasisimple_J h.B_le_coreActionKernel h.isPGroup_B]
  intro d hd
  refine subset_closure ⟨mem_inf.mpr ⟨h.D_le_J hd, ?_⟩,
    h.orderOf_eq_two_pow_of_mem_S (h.D_le_S hd)⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact (h.D_comm_P hd (h.B_le_P hb)).symm

theorem JB_le_X : GSLit.fixedLayer h.J h.B ≤
    centralizer ({h.a} : Set H) ⊓ centralizer (h.B : Set H) :=
  le_inf (fixedLayer_le_centralizer_a h) ((GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_right)

theorem isPerfect_JB : Group.IsPerfect ↥(GSLit.fixedLayer h.J h.B) :=
  B5a.isPerfect_of_isPComponent_subgroupOf (JB_le_X h) (B5a.isPComponent_fixedLayer h)

noncomputable abbrev psiJB : ↥(GSLit.fixedLayer h.J h.B) →* Vbar h :=
  (psi h).comp (inclusion (B5a.fixedLayer_le_V h))

theorem not_top_le_oddJB : ¬ (⊤ : Subgroup ↥(GSLit.fixedLayer h.J h.B)) ≤
    pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) := by
  intro htop
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  have := LocalCores.isQuasisimple_nontrivial h.isQuasisimple_J
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (OddBar h.J)
  apply hxy
  obtain ⟨x', rfl⟩ := e.surjective x
  obtain ⟨y', rfl⟩ := e.surjective y
  congr 1
  obtain ⟨x'', rfl⟩ := QuotientGroup.mk_surjective x'
  obtain ⟨y'', rfl⟩ := QuotientGroup.mk_surjective y'
  rw [QuotientGroup.eq]
  exact htop trivial

theorem false_of_range_le_center (hc : (psiJB h).range ≤ center (Vbar h)) : False := by
  have hP := isPerfect_JB h
  have hbot : (psiJB h).range = ⊥ := by
    rw [MonoidHom.range_eq_map,
      ← Group.IsPerfect.commutator_eq_top (G := ↥(GSLit.fixedLayer h.J h.B)),
      _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      commutator_eq_bot_iff_le_centralizer]
    exact hc.trans (center_le_centralizer _)
  apply not_top_le_oddJB h
  intro j _
  apply ker_psi_le h (B5a.fixedLayer_le_V h)
  have hj : psiJB h j ∈ (psiJB h).range := ⟨j, rfl⟩
  rw [hbot] at hj
  exact hj

variable (hKa : conjugate h.K h.a ≠ h.K)

include hKa in
theorem range_psiJB_le : (psiJB h).range ≤ (delta h hKa).range := by
  have hP := isPerfect_JB h
  have hdec : ∀ j : ↥(GSLit.fixedLayer h.J h.B), ∃ k : ↥h.K, ∃ c ∈ center (Vbar h),
      psiJB h j = delta h hKa k * c := fun j =>
    exists_delta_mul_center h hKa _ (by
      have hja : (j : H) * h.a = h.a * j :=
        mem_centralizer_singleton_iff.mp (fixedLayer_le_centralizer_a h j.2)
      show h.a⁻¹ * (j : H) * h.a = j
      rw [mul_assoc, hja, inv_mul_cancel_left])
  rw [MonoidHom.range_eq_map,
    ← Group.IsPerfect.commutator_eq_top (G := ↥(GSLit.fixedLayer h.J h.B)),
    _root_.commutator_def, map_commutator, commutator_le]
  rintro _ ⟨j₁, -, rfl⟩ _ ⟨j₂, -, rfl⟩
  obtain ⟨k₁, c₁, hc₁, e₁⟩ := hdec j₁
  obtain ⟨k₂, c₂, hc₂, e₂⟩ := hdec j₂
  rw [e₁, e₂, SectionRank.commutatorElement_mul_mem_center _ _ hc₁ hc₂, ← map_commutatorElement]
  exact ⟨_, rfl⟩

theorem exists_comm_lift (g : ↥h.V) (hg : sigmaBar h (psi h g) = psi h g) :
    ∃ v : ↥h.V, (v : H) * h.a = h.a * v ∧ psi h v = psi h g := by
  set o : ↥h.V := (sigmaV h g)⁻¹ * g with ho
  have ho1 : psi h o = 1 := by
    rw [ho, map_mul, map_inv, ← sigmaBar_psi, hg, inv_mul_cancel]
  have hoO : (o : H) ∈ oddCoreIn h.V := (psi_eq_one_iff h o).1 ho1
  have hoe : (o : H) = h.a⁻¹ * (g : H)⁻¹ * h.a * g := by
    rw [ho, Subgroup.coe_mul, Subgroup.coe_inv, coe_sigmaV]
    group
  have ha2 := a_sq h
  have hao' : h.a * (o : H) = (g : H)⁻¹ * h.a * g := by
    rw [hoe]
    group
  have hao : h.a * o * (h.a * o) = 1 := by
    rw [hao']
    calc (g : H)⁻¹ * h.a * g * ((g : H)⁻¹ * h.a * g) = (g : H)⁻¹ * (h.a * h.a) * g := by group
      _ = 1 := by rw [ha2]; group
  obtain ⟨n, hn⟩ := exists_zpow_conj_eq_of_odd ha2 hao (odd_orderOf_of_mem_oddCoreIn hoO)
  refine ⟨g * o ^ n, ?_, ?_⟩
  · have e : ((g : H) * (o : H) ^ n)⁻¹ * h.a * ((g : H) * (o : H) ^ n) = h.a := by
      calc ((g : H) * (o : H) ^ n)⁻¹ * h.a * ((g : H) * (o : H) ^ n) =
          ((o : H) ^ n)⁻¹ * ((g : H)⁻¹ * h.a * g) * (o : H) ^ n := by group
        _ = ((o : H) ^ n)⁻¹ * (h.a * o) * (o : H) ^ n := by rw [hao']
        _ = h.a := hn
    rw [Subgroup.coe_mul, Subgroup.coe_zpow]
    calc (g : H) * (o : H) ^ n * h.a = (g : H) * (o : H) ^ n *
        (((g : H) * (o : H) ^ n)⁻¹ * h.a * ((g : H) * (o : H) ^ n)) := by rw [e]
      _ = h.a * ((g : H) * (o : H) ^ n) := by group
  · rw [map_mul, map_zpow, ho1, one_zpow, mul_one]

include hKa in
theorem exists_comm_delta (k : ↥h.K) :
    ∃ v : ↥h.V, (v : H) * h.a = h.a * v ∧ psi h v = delta h hKa k := by
  have hg : psi h ((⟨k, h.K_le_V k.2⟩ : ↥h.V) * sigmaV h ⟨k, h.K_le_V k.2⟩) = delta h hKa k := by
    rw [map_mul, ← sigmaBar_psi, delta_eq]
  have hfix : sigmaBar h (delta h hKa k) = delta h hKa k := by
    rw [delta_eq, map_mul, sigmaBar_sigmaBar, sigmaBar_K h k.2]
    exact (psi_comm h hKa k.2 (conjA_mem_Ka h k.2)).symm
  rw [← hg] at hfix ⊢
  exact exists_comm_lift h _ hfix

abbrev CVa : Subgroup ↥h.V := (centralizer ({h.a} : Set H)).comap h.V.subtype

noncomputable abbrev Ybar : Subgroup (Vbar h) := (CVa h).map (psi h)

include hKa in
theorem range_delta_le_Ybar : (delta h hKa).range ≤ Ybar h := by
  rintro _ ⟨k, rfl⟩
  obtain ⟨v, hva, hv⟩ := exists_comm_delta h hKa k
  exact ⟨v, mem_centralizer_singleton_iff.mpr hva, hv⟩

theorem isSubnormal_psiJB : ((psiJB h).range.subgroupOf (Ybar h)).IsSubnormal := by
  have hsn : ((GSLit.fixedLayer h.J h.B).subgroupOf
      (centralizer ({h.a} : Set H) ⊓ centralizer (h.B : Set H))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := B5a.isPComponent_fixedLayer h
    exact hs
  let ι₁ : ↥(CVa h) →* ↥(centralizer ({h.a} : Set H) ⊓ centralizer (h.B : Set H)) :=
    { toFun := fun c => ⟨((c : ↥h.V) : H), mem_inf.mpr ⟨c.2, B5a.V_le_centralizer h (c : ↥h.V).2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ψY : ↥(CVa h) →* ↥(Ybar h) :=
    ((psi h).comp (CVa h).subtype).codRestrict (Ybar h) (fun c => ⟨c, c.2, rfl⟩)
  have hψY : Function.Surjective ψY := by
    rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  have h1 := (hsn.comap ι₁).map hψY
  have e : (psiJB h).range.subgroupOf (Ybar h) =
      (((GSLit.fixedLayer h.J h.B).subgroupOf
        (centralizer ({h.a} : Set H) ⊓ centralizer (h.B : Set H))).comap ι₁).map ψY := by
    ext ⟨y, hy⟩
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨inclusion (B5a.fixedLayer_le_V h) j, fixedLayer_le_centralizer_a h j.2⟩, j.2, rfl⟩
    · rintro ⟨c, hc, hce⟩
      refine ⟨⟨((c : ↥h.V) : H), hc⟩, ?_⟩
      have := congrArg Subtype.val hce
      exact this
  rw [e]
  exact h1

include hKa in
theorem range_delta_le_psiJB : (delta h hKa).range ≤ (psiJB h).range := by
  have hY := range_delta_le_Ybar h hKa
  let δY : ↥h.K →* ↥(Ybar h) := (delta h hKa).codRestrict (Ybar h) (fun k => hY ⟨k, rfl⟩)
  set U : Subgroup ↥h.K := ((psiJB h).range.subgroupOf (Ybar h)).comap δY with hU
  have hU' : (U.map (QuotientGroup.mk' (pPrimeCore 2 ↥h.K))).IsSubnormal :=
    ((isSubnormal_psiJB h).comap δY).map (QuotientGroup.mk'_surjective _)
  have hmemU : ∀ k : ↥h.K, k ∈ U ↔ delta h hKa k ∈ (psiJB h).range := fun k => Iff.rfl
  rcases eq_top_or_le_center_of_isSubnormal h.isQuasisimple_K hU' with htop | hZ
  · rintro _ ⟨k, rfl⟩
    have hk : (k : OddBar h.K) ∈ U.map (QuotientGroup.mk' (pPrimeCore 2 ↥h.K)) := by
      rw [htop]
      trivial
    obtain ⟨u, hu, hue⟩ := hk
    have e : delta h hKa k = delta h hKa u := by
      rw [← deltaBar_mk, ← deltaBar_mk]
      exact congrArg (deltaBar h hKa) hue.symm
    rw [e]
    exact (hmemU u).1 hu
  · exfalso
    refine false_of_range_le_center h ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := range_psiJB_le h hKa ⟨j, rfl⟩
    have hkU : k ∈ U := (hmemU k).2 (by rw [hk]; exact ⟨j, rfl⟩)
    rw [← hk]
    exact delta_mem_center h hKa (hZ ⟨k, hkU, rfl⟩)

include hKa in
theorem oddJB_le_ker : pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) ≤ (psiJB h).ker := by
  set N : Subgroup (Vbar h) := (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map (psiJB h) with hN
  set M : Subgroup (OddBar h.K) := N.comap (deltaBar h hKa) with hM
  have hrange : ∀ g : OddBar h.K, ∃ j, psiJB h j = deltaBar h hKa g := fun g =>
    range_delta_le_psiJB h hKa (by rw [← range_deltaBar]; exact ⟨g, rfl⟩)
  have hMn : M.Normal := ⟨fun m hm g => by
    obtain ⟨j, hj⟩ := hrange g
    obtain ⟨o, ho, hoe⟩ := hm
    show deltaBar h hKa (g * m * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv, ← hj, ← hoe, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, (pPrimeCore_normal (p := 2)).conj_mem o ho j, rfl⟩⟩
  rcases LocalCores.quasisimple_normal_subgroups h.isQuasisimple_K hMn with htop | hZ
  · exfalso
    apply not_top_le_oddJB h
    intro j _
    obtain ⟨k, hk⟩ := range_psiJB_le h hKa ⟨j, rfl⟩
    have hkM : (k : OddBar h.K) ∈ M := by
      rw [htop]
      trivial
    obtain ⟨o, ho, hoe⟩ := hkM
    have h1 : o⁻¹ * j ∈ pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) := by
      apply ker_psi_le h (B5a.fixedLayer_le_V h)
      show psiJB h (o⁻¹ * j) = 1
      rw [map_mul, map_inv, hoe, deltaBar_mk, hk, inv_mul_cancel]
    have h2 := mul_mem ho h1
    rwa [mul_inv_cancel_left] at h2
  · intro o ho
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := range_psiJB_le h hKa ⟨o, rfl⟩
    have hkM : (k : OddBar h.K) ∈ M := by
      show deltaBar h hKa k ∈ N
      rw [deltaBar_mk, hk]
      exact ⟨o, ho, rfl⟩
    have hc : psiJB h o ∈ center (Vbar h) := by
      rw [← hk]
      exact delta_mem_center h hKa (hZ hkM)
    have hodd : Odd (orderOf o) := by
      have := odd_orderOf_of_mem_oddCoreIn (K := GSLit.fixedLayer h.J h.B) ⟨o, ho, rfl⟩
      rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at this
    exact eq_one_of_mem_center_of_odd hc (Odd.of_dvd_nat hodd (orderOf_map_dvd _ _))

end CFSG.ComponentClassification.GSThmB.CF23Diag
