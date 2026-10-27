module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictionsFull
public import CFSG.Milestones.CL_LIT_Aschbacher_proper_two_generated_core
public import CFSG.Milestones.LR_nonabelian_simple_two_rank_lower_bound
public import CFSG.Goldschmidt.Steps.GSz8MultBasic

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ProperTwoGeneratedCore CFSG.ProperTwoGeneratedCore.Lemma37

section Quasisimple

variable {J : Type} [Group J] [Finite J]

theorem nonempty_sz_of_twoPointCyclic
    (hperf : commutator J = ⊤) [hs : IsSimpleGroup (J ⧸ center J)]
    (hnab : ∃ a b : J ⧸ center J, a * b ≠ b * a) (hZ2 : IsPGroup 2 (center J))
    (hZcyc : IsCyclic (center J)) (hZne : center J ≠ ⊥)
    (hZinv : ∀ c ∈ center J, ∀ d ∈ center J, orderOf c = 2 → orderOf d = 2 → c = d)
    {a b : J} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) {T : Sylow 2 J}
    {B : Subgroup J} (hTB : (T : Subgroup J) ≤ B) (hB : B ≠ ⊤)
    (hcyc : ∀ g : J, g ∉ B → ∀ Q : Subgroup J, IsPGroup 2 Q →
      (∀ p ∈ Q, p ∈ B ∧ g⁻¹ * p * g ∈ B) → IsCyclic Q) :
    Nonempty (J ⧸ center J ≃* Open.Sz 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (QuotientGroup.mk' (center J)) := QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (center J)).ker = center J := QuotientGroup.ker_mk' _
  have hkerB : (QuotientGroup.mk' (center J)).ker ≤ B := by
    rw [hker]
    exact (hZ2.le_sylow_of_normal T).trans hTB
  have hker2 : IsPGroup 2 (QuotientGroup.mk' (center J)).ker := by
    rw [hker]
    exact hZ2
  let Ts : Sylow 2 (J ⧸ center J) := T.mapSurjective hπ
  have hTsB : (Ts : Subgroup (J ⧸ center J)) ≤ B.map (QuotientGroup.mk' (center J)) := by
    rw [Sylow.coe_mapSurjective]
    exact map_mono hTB
  have hΓ2 : Open.properTwoGenCoreGamma (Ts : Subgroup (J ⧸ center J)) 2 ≠ ⊤ := fun h =>
    CyclicCase.map_ne_top_of_ker_le _ hkerB hB (top_le_iff.mp
      (h ▸ CyclicCase.gamma_two_le_map_of_cyclic _ hπ hkerB hker2 hcyc Ts hTsB))
  have hev : Even (Nat.card (J ⧸ center J)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hmem : ∀ x : J, orderOf x = 2 → x ∈ center J := by
      intro x hx
      have h1 : orderOf (QuotientGroup.mk' (center J) x) ∣ 2 := by
        rw [← hx]
        exact orderOf_map_dvd _ x
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      · have h2 := orderOf_dvd_natCard (QuotientGroup.mk' (center J) x)
        rw [h] at h2
        exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
    exact hab (hZinv a (hmem a ha) b (hmem b hb) ha hb)
  have h2 : 2 ≤ Open.twoRank (J ⧸ center J) :=
    Milestones.lr_nonabelian_simple_two_rank_lower_bound _ hnab hev
  have hne2 : Open.twoRank (J ⧸ center J) ≠ 2 := fun h =>
    hab (rankTwoCoverStatement J hperf hZ2 hZne hZcyc hs h a b ha hb)
  have h3 : 3 ≤ Open.pRank 2 (Ts : Subgroup (J ⧸ center J)) := by
    rw [sylow_two_rank_eq]
    omega
  rcases Milestones.cl_lit_aschbacher_proper_two_generated_core _ hnab Ts h3 hΓ2 with
    hΓ1 | hJ1
  · rcases CoverExcl.bender_cover_quotient_of_isCyclic hperf hZ2 hZcyc hZne hnab
        (CyclicCase.isBenderGroup_of_gamma_one_ne_top Ts h2 hΓ1) with he | he
    · obtain ⟨e⟩ := he
      exact absurd (GH74.twoRank_eq_of_mulEquiv_psl2Model (by norm_num) e) (by omega)
    · obtain ⟨e⟩ := he
      exact ⟨e.trans (MulEquiv.subgroupCongr (GH74.Bender.szModel_eq_sz 1))⟩
  · obtain ⟨eJ⟩ := hJ1
    exact absurd (center_eq_bot_of_quotient_jOne hperf eJ) hZne

theorem card_center_eq_two_of_twoPoint (hZ2 : IsPGroup 2 (center J)) (hZne : center J ≠ ⊥)
    {T : Sylow 2 J} {B : Subgroup J} (hTB : (T : Subgroup J) ≤ B)
    (hΓ : Open.properTwoGenCoreGamma (T : Subgroup J) 2 ≤ B) {g : J} (hg : g ∉ B)
    {Q : Subgroup J} (hQ2 : IsPGroup 2 Q) (hQB : ∀ p ∈ Q, p ∈ B ∧ g⁻¹ * p * g ∈ B)
    (hQc : ¬ IsCyclic Q) : Nat.card (center J) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZB : center J ≤ B := (hZ2.le_sylow_of_normal T).trans hTB
  have hW2 : IsPGroup 2 (Q ⊔ center J : Subgroup J) := hQ2.to_sup_of_normal_right hZ2
  have hWB : Q ⊔ center J ≤ B ⊓ B.conjBy g := by
    refine sup_le (fun p hp => ⟨(hQB p hp).1, mem_map.mpr ⟨g⁻¹ * p * g, (hQB p hp).2, ?_⟩⟩)
      (fun c hc => ⟨hZB hc, mem_map.mpr ⟨c, hZB hc, ?_⟩⟩)
    · change g * (g⁻¹ * p * g) * g⁻¹ = p
      group
    · change g * c * g⁻¹ = c
      rw [mem_center_iff.mp hc g, mul_inv_cancel_right]
  have hlt := conjugate_intersection_rank_lt T B (k := 2) (by norm_num) hTB hΓ g⁻¹
    (fun h => hg (by simpa using inv_mem h))
  rw [inv_inv] at hlt
  have hWr : Open.twoRank (Q ⊔ center J : Subgroup J) ≤ 1 := by
    rw [Open.twoRank, ← RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
      one_lt_two]
    have := SectionRank.pRank_mono one_lt_two hWB
    omega
  have hWc : ¬ IsCyclic (Q ⊔ center J : Subgroup J) := fun h =>
    hQc (@Subgroup.isCyclic_of_le _ _ _ _ (le_sup_left : Q ≤ Q ⊔ center J) h)
  have hZW := card_center_eq_two_of_not_isCyclic hW2 hWr hWc
  have hle : (center J).subgroupOf (Q ⊔ center J) ≤ center (Q ⊔ center J : Subgroup J) :=
    fun c hc => mem_center_iff.mpr fun w => Subtype.ext (mem_center_iff.mp hc w)
  have h1 : Nat.card (center J) ≤ 2 := by
    rw [← hZW, ← Nat.card_congr (subgroupOfEquivOfLe (le_sup_right :
      center J ≤ Q ⊔ center J)).toEquiv]
    exact Subgroup.card_le_of_le hle
  have h2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZne
  omega

theorem card_center_eq_two_of_sz (hperf : commutator J = ⊤)
    [IsSimpleGroup (J ⧸ center J)] (hZcyc : IsCyclic (center J)) (hZne : center J ≠ ⊥)
    (e : J ⧸ center J ≃* Open.Sz 1) : Nat.card (center J) = 2 := by
  have h1 := CyclicCase.card_le_two_of_isElemAbelian_of_isCyclic
    (Goldschmidt.GSz8Mult.isElemAbelian_center ⟨hperf, inferInstance⟩ e) hZcyc
  have h2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZne
  omega

end Quasisimple

variable {X : Type} [Group X] [Finite X]

theorem component_quasi_of_mem
    (hodd : pPrimeCore 2 X = ⊥) {u : X} (huZ : u ∈ center X) (hu : orderOf u = 2)
    (huO : u ∈ CFSG.pCore 2 X) (hrk : Open.pRank 2 (CFSG.pCore 2 X) = 1) (P : Sylow 2 X)
    {Y : Subgroup X} (hY : Y ≠ ⊤) (hPY : (P : Subgroup X) ≤ Y)
    (hcore : Open.properTwoGenCoreGamma (P : Subgroup X) 2 ≤ Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (huL : u ∈ L) (hL2 : 2 ≤ Open.pRank 2 L) :
    L.Normal ∧ Open.pRank 2 (centralizer (L : Set X)) ≤ 1 ∧ commutator L = ⊤ ∧
      Nat.card (center L) = 2 ∧
      (Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (L ⧸ center L ≃* Open.Sz 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc := (CFSG.isComponent_iff_open L).mp hL
  obtain ⟨-, hres, -, -⟩ := proper_full_core_component_number_restrictions P Y hY hPY hcore
  have hchar : L.Characteristic := proper_full_core_high_rank_component_characteristic P Y hY
    hPY hcore L hLc hL2
  have hLn : L.Normal := inferInstance
  obtain ⟨T, hTmap, hΓT, hBlt, hCL⟩ : ∃ T : Sylow 2 L,
      (T : Subgroup L).map L.subtype = (P : Subgroup X) ⊓ L ∧
      Open.properTwoGenCoreGamma (T : Subgroup L) 2 ≤ Y.subgroupOf L ∧ Y.subgroupOf L < ⊤ ∧
      Open.pRank 2 (centralizer (L : Set X)) ≤ 1 := by
    obtain ⟨hchar', hT⟩ := hres L hLc hL2
    exact ⟨_, hT⟩
  have hTB : (T : Subgroup L) ≤ Y.subgroupOf L := fun x hx => by
    have h1 : (x : X) ∈ (T : Subgroup L).map L.subtype := mem_map_of_mem _ hx
    rw [hTmap] at h1
    exact hPY h1.1
  have hperf : commutator L = ⊤ := hL.1.1.commutator_eq_top
  have hs : IsSimpleGroup (L ⧸ center L) := hL.1.2.1
  have hnab := hL.1.2.2
  obtain ⟨hZ2, hZO⟩ := Assembly.component_center_le_twoCore hodd hL
  have hZu : ∀ c ∈ center L, orderOf c = 2 → (c : X) = u := fun c hc hc2 =>
    Assembly.eq_of_mem_twoCore_of_rank_one huZ hu huO hrk (hZO (mem_map_of_mem _ hc))
      (by rwa [Subgroup.orderOf_coe])
  have hZinv : ∀ c ∈ center L, ∀ d ∈ center L, orderOf c = 2 → orderOf d = 2 → c = d :=
    fun c hc d hd hc2 hd2 => Subtype.ext ((hZu c hc hc2).trans (hZu d hd hd2).symm)
  have hZne : center L ≠ ⊥ := by
    intro h
    have hmem : (⟨u, huL⟩ : L) ∈ center L :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp huZ g)
    rw [h, mem_bot] at hmem
    have h1 : u = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hu
    omega
  have hZcyc : IsCyclic (center L) := ABGLocalTools.isCyclic_of_isPGroup_two_of_comm hZ2
    (fun c d => Subtype.ext (mem_center_iff.mp c.2 d).symm)
    (fun c d hc hd => Subtype.ext (hZinv c c.2 d d.2 (by rwa [Subgroup.orderOf_coe])
      (by rwa [Subgroup.orderOf_coe])))
  by_cases hcyc : ∀ g : L, g ∉ Y.subgroupOf L → ∀ Q : Subgroup L, IsPGroup 2 Q →
      (∀ p ∈ Q, p ∈ Y.subgroupOf L ∧ g⁻¹ * p * g ∈ Y.subgroupOf L) → IsCyclic Q
  · obtain ⟨a, haL, b, hbL, ha2, hb2, hab, -⟩ :=
      Assembly.exists_commuting_involutions_of_two_le_pRank hL2
    obtain ⟨e⟩ := nonempty_sz_of_twoPointCyclic hperf hnab hZ2 hZcyc hZne hZinv
      (a := ⟨a, haL⟩) (b := ⟨b, hbL⟩) (by rwa [Subgroup.orderOf_mk])
      (by rwa [Subgroup.orderOf_mk]) (fun h => hab (congrArg Subtype.val h)) hTB hBlt.ne hcyc
    exact ⟨hLn, hCL, hperf, card_center_eq_two_of_sz hperf hZcyc hZne e, Or.inr ⟨e⟩⟩
  · push Not at hcyc
    obtain ⟨g, hgB, Q, hQ2, hQB, hQc⟩ := hcyc
    have hZ : Nat.card (center L) = 2 :=
      card_center_eq_two_of_twoPoint hZ2 hZne hTB hΓT hgB hQ2 hQB hQc
    have IH : CanonicalBelow (Nat.card L) := fun K _ _ _ _ hnab' S h3 hΓ =>
      Milestones.cl_lit_aschbacher_proper_two_generated_core K hnab' S h3 hΓ
    have h2L : 2 ≤ Open.twoRank L := by
      rw [Open.twoRank, ← RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
        one_lt_two]
      exact hL2
    rcases quasisimpleQuaternionCoreClassificationBelow L IH hL.1.1 hs hZ h2L T _ hTB hBlt.ne
        hΓT ⟨g, hgB, Q, hQ2, hQc, hQB⟩ with he | he
    · exact ⟨hLn, hCL, hperf, hZ, Or.inl he⟩
    · obtain ⟨e⟩ := he
      exact ⟨hLn, hCL, hperf, hZ,
        Or.inr ⟨e.trans (MulEquiv.subgroupCongr (GH74.Bender.szModel_eq_sz 1))⟩⟩

end CFSG.ComponentClassification.Foote5
