module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneAbelianTwo
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.GlueLib
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section Abs

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_lt {T Ta : Subgroup G} (hTa : IsPGroup 2 ↥Ta) (hlt : T < Ta) :
    ∃ x ∈ Ta, x ∉ T ∧ x ∈ normalizer (T : Set G) := by
  have hnil : Group.IsNilpotent ↥Ta := hTa.isNilpotent
  have hTle : T ≤ Ta := hlt.le
  have hH : T.subgroupOf Ta < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply (not_le_of_gt hlt)
    intro x hx
    have : (⟨x, hx⟩ : ↥Ta) ∈ T.subgroupOf Ta := by rw [htop]; exact mem_top _
    exact this
  have hn := Group.normalizerCondition_of_isNilpotent (G := ↥Ta) (T.subgroupOf Ta) hH
  obtain ⟨y, hyn, hyH⟩ := IsConcreteLE.exists_of_lt hn
  refine ⟨y.1, y.2, fun h => hyH h, ?_⟩
  rw [mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact (mem_normalizer_iff.1 hyn ⟨t, hTle ht⟩).1 ht
  · intro hxt
    have htTa : t ∈ Ta := by
      have h1 : (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G) ∈ Ta :=
        mul_mem (mul_mem (inv_mem y.2) (hTle hxt)) y.2
      simpa [mul_assoc] using h1
    exact (mem_normalizer_iff.1 hyn ⟨t, htTa⟩).2 hxt

theorem lemma63_abs {z a : G} {S : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hzS : z ∈ S)
    (hzc : ∀ s ∈ S, z * s = s * z) (haS : a ∈ S)
    (hextC : M.Syl2In (S ⊓ centralizer ({a} : Set G))
      (centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G)))
    (h62 : ∀ t ∈ S, t * a = a * t → (∀ s ∈ S, s * a = a * s → s * t = t * s) → IsConj z t →
      t = z) :
    M.Syl2In (S ⊓ centralizer ({a} : Set G)) (centralizer ({a} : Set G)) ∧
    ∀ g : G, g⁻¹ * a * g ∈ S →
      conjugate (S ⊓ centralizer ({a} : Set G)) g = S ⊓ centralizer ({g⁻¹ * a * g} : Set G) →
        g ∈ centralizer ({z} : Set G) := by
  have hT2 : IsPGroup 2 ↥(S ⊓ centralizer ({a} : Set G)) := hS2.to_inf_left
  have hzT : z ∈ S ⊓ centralizer ({a} : Set G) :=
    ⟨hzS, Subgroup.mem_centralizer_singleton_iff.2 (hzc a haS)⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨Ta, hTa, hTTa⟩ := M.exists_syl2In_ge hT2 (inf_le_right : S ⊓ centralizer ({a} : Set G) ≤ _)
    by_cases heq : S ⊓ centralizer ({a} : Set G) = Ta
    · rw [heq]; exact hTa
    · exfalso
      have hlt : S ⊓ centralizer ({a} : Set G) < Ta := lt_of_le_of_ne hTTa heq
      obtain ⟨x, hxTa, hxT, hxn⟩ := exists_mem_normalizer_of_lt hTa.2.1 hlt
      have hxmem := mem_normalizer_iff.1 hxn
      have hzt : x * z * x⁻¹ ∈ S ⊓ centralizer ({a} : Set G) := (hxmem z).1 hzT
      have hcent : ∀ s ∈ S ⊓ centralizer ({a} : Set G), s * (x * z * x⁻¹) = (x * z * x⁻¹) * s := by
        intro s hs
        have hs' : x⁻¹ * s * x ∈ S ⊓ centralizer ({a} : Set G) := by
          refine (hxmem (x⁻¹ * s * x)).2 ?_
          have e : x * (x⁻¹ * s * x) * x⁻¹ = s := by group
          rw [e]; exact hs
        have h1 := hzc _ hs'.1
        calc s * (x * z * x⁻¹) = x * ((x⁻¹ * s * x) * z) * x⁻¹ := by group
          _ = x * (z * (x⁻¹ * s * x)) * x⁻¹ := by rw [h1]
          _ = (x * z * x⁻¹) * s := by group
      have h6 := h62 (x * z * x⁻¹) hzt.1 (Subgroup.mem_centralizer_singleton_iff.1 hzt.2)
        (fun s hs hsa => hcent s ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 hsa⟩)
        (isConj_iff.2 ⟨x, rfl⟩)
      have hxz : x * z = z * x := by
        calc x * z = (x * z * x⁻¹) * x := by group
          _ = z * x := by rw [h6]
      have hxC : x ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxz
      have hQ2 : IsPGroup 2 ↥(S ⊓ centralizer ({a} : Set G) ⊔ zpowers x) :=
        hTa.2.1.to_le (sup_le hTTa (zpowers_le.2 hxTa))
      have hQle : S ⊓ centralizer ({a} : Set G) ⊔ zpowers x ≤
          centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G) :=
        sup_le hextC.1 (zpowers_le.2 ⟨hxC, hTa.1 hxTa⟩)
      have := hextC.eq_of_le hQ2 le_sup_left hQle
      apply hxT
      rw [← this]
      exact mem_sup_right (mem_zpowers x)
  · intro g hbS hcon
    have hzb : z ∈ S ⊓ centralizer ({g⁻¹ * a * g} : Set G) :=
      ⟨hzS, Subgroup.mem_centralizer_singleton_iff.2 (hzc _ hbS)⟩
    have hcon' : M.cj (S ⊓ centralizer ({a} : Set G)) g = S ⊓ centralizer ({g⁻¹ * a * g} : Set G) := by
      rw [cj_eq_conjugate]; exact hcon
    have hz1 : g * z * g⁻¹ ∈ S ⊓ centralizer ({a} : Set G) := by
      rw [← hcon'] at hzb
      exact M.mem_cj.1 hzb
    have hcent : ∀ s ∈ S ⊓ centralizer ({a} : Set G), s * (g * z * g⁻¹) = (g * z * g⁻¹) * s := by
      intro s hs
      have hs' : g⁻¹ * s * g ∈ S ⊓ centralizer ({g⁻¹ * a * g} : Set G) := by
        rw [← hcon', M.mem_cj]
        have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
        rw [e]; exact hs
      have h1 := hzc _ hs'.1
      calc s * (g * z * g⁻¹) = g * ((g⁻¹ * s * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
        _ = (g * z * g⁻¹) * s := by group
    have h6 := h62 (g * z * g⁻¹) hz1.1 (Subgroup.mem_centralizer_singleton_iff.1 hz1.2)
      (fun s hs hsa => hcent s ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 hsa⟩)
      (isConj_iff.2 ⟨g, rfl⟩)
    apply Subgroup.mem_centralizer_singleton_iff.2
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h6]

theorem exists_Q_cyclic {S E : Subgroup G} {a : G} (hS2 : IsPGroup 2 ↥S) (hES : E ≤ S)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ E) (haS : a ∈ S) (haE : a ∉ E) :
    ∃ Q : Subgroup G, E ≤ Q ∧ Q ≤ S ∧ a ∉ Q ∧ (∀ t ∈ S, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) ∧
      ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q := by
  classical
  have hne : E ∈ {Q : Subgroup G | E ≤ Q ∧ Q ≤ S ∧ a ∉ Q} := ⟨le_rfl, hES, haE⟩
  obtain ⟨Q, ⟨hEQ, hQS, haQ⟩, hmax⟩ :=
    Set.Finite.exists_maximalFor (id : Subgroup G → Subgroup G)
      {Q : Subgroup G | E ≤ Q ∧ Q ≤ S ∧ a ∉ Q} (Set.toFinite _) ⟨E, hne⟩
  have hnorm : ∀ t ∈ S, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    have h1 : ⁅t, q⁆ ∈ E := hcomm t ht q (hQS hq)
    have e : t * q * t⁻¹ = ⁅t, q⁆ * q := by simp only [commutatorElement_def]; group
    rw [e]; exact mul_mem (hEQ h1) hq
  refine ⟨Q, hEQ, hQS, haQ, hnorm, ?_⟩
  set Qs : Subgroup ↥S := Q.subgroupOf S with hQs
  have hQsn : Qs.Normal := ⟨fun n hn g => by
    rw [hQs, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm (g : G) g.2 (n : G) hn⟩
  have hqc : ∀ x y : ↥S ⧸ Qs, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | _ s => ?_
    induction y using QuotientGroup.induction_on with | _ s' => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [hQs, Subgroup.mem_subgroupOf]
    have h1 := hEQ (hcomm _ (S.inv_mem s'.2) _ (S.inv_mem s.2))
    have e : (((s * s')⁻¹ * (s' * s) : ↥S) : G) = ⁅(s' : G)⁻¹, (s : G)⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]; exact h1
  let _ : CommGroup (↥S ⧸ Qs) := { (inferInstance : Group (↥S ⧸ Qs)) with mul_comm := hqc }
  have hp2 : IsPGroup 2 (↥S ⧸ Qs) := hS2.to_quotient Qs
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      (↥S ⧸ Qs) := by
    have key : ∀ w : CFSG.DisconnectedInvolutionGraph.Helpers.Involution (↥S ⧸ Qs),
        (w : ↥S ⧸ Qs) = ((⟨a, haS⟩ : ↥S) : ↥S ⧸ Qs) := by
      intro w
      obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (w : ↥S ⧸ Qs)
      have hw : orderOf (w : ↥S ⧸ Qs) = 2 := w.2
      have hsq : (w : ↥S ⧸ Qs) * w = 1 := R1.sq_one_of_orderOf_two hw
      have hw1 : (w : ↥S ⧸ Qs) ≠ 1 := ne_one_of_orderOf_eq_two hw
      have hsQ : (s : G) ∉ Q := by
        intro h
        apply hw1
        rw [← hs]
        exact (QuotientGroup.eq_one_iff s).2 (by rw [hQs, Subgroup.mem_subgroupOf]; exact h)
      have hss : (s : G) * s ∈ Q := by
        have h1 : ((s * s : ↥S) : ↥S ⧸ Qs) = 1 := by rw [QuotientGroup.mk_mul, hs]; exact hsq
        have h2 := (QuotientGroup.eq_one_iff (s * s)).1 h1
        rw [hQs, Subgroup.mem_subgroupOf] at h2
        exact h2
      have hnorms : zpowers (s : G) ≤ normalizer (Q : Set G) := by
        refine zpowers_le.2 (M.mem_normalizer_of_both (fun x hx => hnorm s s.2 x hx) (fun x hx => ?_))
        have := hnorm (s : G)⁻¹ (S.inv_mem s.2) x hx
        simpa using this
      have haQ' : a ∈ Q ⊔ zpowers (s : G) := by
        by_contra hnot
        have hmem : (Q ⊔ zpowers (s : G)) ∈ {Q : Subgroup G | E ≤ Q ∧ Q ≤ S ∧ a ∉ Q} :=
          ⟨hEQ.trans le_sup_left, sup_le hQS (zpowers_le.2 s.2), hnot⟩
        have := (hmax hmem le_sup_left)
        apply hsQ
        exact this (mem_sup_right (mem_zpowers _))
      rw [sup_comm] at haQ'
      obtain ⟨b, hb, q, hq, hab⟩ := M.mem_sup_of_le_normalizer hnorms haQ'
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      have hs2 : (s : G) ^ (2 : ℤ) ∈ Q := by rw [zpow_two]; exact hss
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · exfalso
        apply haQ
        have h1 : (s : G) ^ (2 * m) ∈ Q := by
          rw [zpow_mul]
          exact Q.zpow_mem hs2 m
        rw [hab]; exact mul_mem h1 hq
      · have hu : ((s : G) ^ (2 : ℤ)) ^ m ∈ Q := Q.zpow_mem hs2 m
        have e : (s : G) ^ (2 * m + 1) = ((s : G) ^ (2 : ℤ)) ^ m * s := by
          rw [zpow_add_one, zpow_mul]
        rw [← hs]
        rw [QuotientGroup.eq]
        rw [hQs, Subgroup.mem_subgroupOf]
        have h1 : (s : G)⁻¹ * a = ((s : G)⁻¹ * ((s : G) ^ (2 : ℤ)) ^ m * s) * q := by
          rw [hab, e]; group
        show (s : G)⁻¹ * a ∈ Q
        rw [h1]
        refine mul_mem ?_ hq
        have := hnorm (s : G)⁻¹ (S.inv_mem s.2) _ hu
        simpa using this
    intro w1 w2 _
    apply Subtype.ext
    rw [key w1, key w2]
  have hcyc : IsCyclic (↥S ⧸ Qs) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_abelian_two_group_cyclic (↥S ⧸ Qs) hp2 hrank
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨b, b.2, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg (QuotientGroup.mk (⟨t, ht⟩ : ↥S)))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, hQs, Subgroup.mem_subgroupOf] at hk
  simpa using hk

theorem ctrl_contra {z a : G} {S : Subgroup G} (hsimple : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hStop : M.Syl2In S ⊤) (hSC : S ≤ centralizer ({z} : Set G))
    (haS : a ∈ S) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hanot : a ∉ commBar z)
    (hext : M.Syl2In (S ⊓ centralizer ({a} : Set G)) (centralizer ({a} : Set G)))
    (hctrl : ∀ g : G, g⁻¹ * a * g ∈ S →
      conjugate (S ⊓ centralizer ({a} : Set G)) g = S ⊓ centralizer ({g⁻¹ * a * g} : Set G) →
        g ∈ centralizer ({z} : Set G)) : False := by
  set E : Subgroup G := S ⊓ commBar z with hE
  have hES : E ≤ S := inf_le_left
  have hcomm : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ E := by
    intro s hs s' hs'
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hs hs') (S.inv_mem hs)) (S.inv_mem hs')
    · exact mem_sup_left (Subgroup.commutator_mem_commutator (hSC hs) (hSC hs'))
  have haE : a ∉ E := fun h => hanot h.2
  obtain ⟨Q, hEQ, hQS, haQ, hnorm, hcyc⟩ := exists_Q_cyclic hStop.2.1 hES hcomm haS haE
  have key : ∀ y : G, (∃ g : G, g⁻¹ * a * g = y) → y ∈ S →
      CFSG.GH74.GLS.Stage1.Thm6.Sec12.IsExtremal S y → a⁻¹ * y ∈ E := by
    intro y ⟨g, hg⟩ hyS hyext
    subst hg
    have hT1 : M.Syl2In (M.cj (S ⊓ centralizer ({a} : Set G)) g)
        (centralizer ({g⁻¹ * a * g} : Set G)) := by
      have := M.syl2In_cj hext g
      rwa [M.cj_centralizer] at this
    obtain ⟨c, hc, hcT⟩ := hT1.exists_conj hyext
    have hcy : c * (g⁻¹ * a * g) = (g⁻¹ * a * g) * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hg'a : (g * c)⁻¹ * a * (g * c) = g⁻¹ * a * g := by
      calc (g * c)⁻¹ * a * (g * c) = c⁻¹ * (g⁻¹ * a * g) * c := by group
        _ = g⁻¹ * a * g := by
          rw [show c⁻¹ * (g⁻¹ * a * g) * c = c⁻¹ * (c * (g⁻¹ * a * g)) by rw [hcy]; group]
          group
    have hconj : conjugate (S ⊓ centralizer ({a} : Set G)) (g * c) =
        S ⊓ centralizer ({(g * c)⁻¹ * a * (g * c)} : Set G) := by
      rw [hg'a, ← cj_eq_conjugate, ← M.cj_cj, hcT]
    have hCg : g * c ∈ centralizer ({z} : Set G) :=
      hctrl (g * c) (by rw [hg'a]; exact hyS) hconj
    have hzc : (g * c) * z = z * (g * c) := Subgroup.mem_centralizer_singleton_iff.1 hCg
    have hmem : a⁻¹ * (g⁻¹ * a * g) ∈ ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ := by
      rw [← hg'a]
      have e : a⁻¹ * ((g * c)⁻¹ * a * (g * c)) = ⁅a⁻¹, (g * c)⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((centralizer ({z} : Set G)).inv_mem (hSC haS))
        ((centralizer ({z} : Set G)).inv_mem hCg)
    exact ⟨S.mul_mem (S.inv_mem haS) hyS, mem_sup_left hmem⟩
  obtain ⟨g, hg, hgext⟩ := CFSG.GH74.GLS.Stage1.Thm6.Sec12b.transfer_conj
    CFSG.GH74.GLS.Stage1.Thm6.Sec12.ig_15_15 hsimple hnab hStop hQS hnorm
    (fun h => haQ (h ▸ haS)) hcyc haS haQ
    (fun v hv hvQ => by
      have hv1 : v ≠ 1 := fun e => hvQ (e ▸ Q.one_mem)
      have h1 : orderOf v ≠ 1 := fun e => hv1 (orderOf_eq_one_iff.1 e)
      have h2 := orderOf_pos v
      rw [R1.orderOf_two_of_sq_one ha2 ha1]; omega)
    (fun y hyS hy hyext => Or.inr (hEQ (key y hy hyS hyext)))
  have hyS : g⁻¹ * a * g ∈ S := hQS hg
  have h1 := hEQ (key _ ⟨g, rfl⟩ hyS hgext)
  apply haQ
  have e : a = (g⁻¹ * a * g) * (a⁻¹ * (g⁻¹ * a * g))⁻¹ := by group
  rw [e]
  exact Q.mul_mem hg (Q.inv_mem h1)

end Abs

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
