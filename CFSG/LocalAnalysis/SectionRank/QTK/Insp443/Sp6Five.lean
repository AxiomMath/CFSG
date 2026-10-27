module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Sp6E32
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermCands
public import Certificates.Certificate725105
public import Certificates.Certificate725106

public section

namespace CFSG.SectionRank.QTK.Insp443.Sp6

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native


theorem orb_facts (h : chkOrb () = true) :
    tabsOK 36 [x5T, x7T] = true ∧ siftOK x5T = true ∧ siftOK x7T = true ∧
      ordTest 36 5 x5T = true ∧ ordTest 36 7 x7T = true ∧ candsOK 36 cands5 = true ∧
      candsOK 36 cands7 = true ∧ (cands5.all fun c => c.all siftOK) = true ∧
      (cands7.all fun c => c.all siftOK) = true ∧
      orbCheck 36 5 (orderTables co3Sp36Chain 2) (powTabs 36 x5T 5) cands5 = true ∧
      orbCheck 36 7 (orderTables co3Sp36Chain 2) (powTabs 36 x7T 7) cands7 = true := by
  rw [orderTables_eq_invs]
  simpa only [chkOrb, Bool.and_eq_true, and_assoc] using h

theorem p5_facts (h : chkP5 () = true) :
    sixCheckE 36 (cands5.getD 1 []) ds1 hs1 a1T g1T h1T = true ∧ siftOK a1T = true ∧
      siftOK g1T = true ∧ siftOK h1T = true ∧
    sixCheckE 36 (cands5.getD 3 []) ds3 hs3 a3T g3T h3T = true ∧ siftOK a3T = true ∧
      siftOK g3T = true ∧ siftOK h3T = true ∧
    sixCheckE 36 (cands5.getD 4 []) ds4 hs4 a4T g4T h4T = true ∧ siftOK a4T = true ∧
      siftOK g4T = true ∧ siftOK h4T = true ∧
    subOK 36 (cands5.getD 0 []) (cands5.getD 1 []) = true ∧
    subOK 36 (cands5.getD 1 []) (cands5.getD 1 []) = true ∧
    subOK 36 (cands5.getD 2 []) (cands5.getD 3 []) = true ∧
    subOK 36 (cands5.getD 3 []) (cands5.getD 3 []) = true ∧
    subOK 36 (cands5.getD 4 []) (cands5.getD 4 []) = true ∧
    subOK 36 (cands5.getD 5 []) (cands5.getD 4 []) = true ∧
    spanEq 36 (cands5.getD 0 []) (ds1.getD 0 []) = true ∧
    spanEq 36 (cands5.getD 2 []) (ds3.getD 0 []) = true ∧
    spanEq 36 (cands5.getD 5 []) (ds4.getD 0 []) = true ∧
    countProducts 36 (anyTest (tests5 (spanTabs 36 (cands5.getD 1 []))
      (spanTabs 36 (cands5.getD 3 [])) (spanTabs 36 (cands5.getD 4 []))))
      (levelTables co3Sp36Chain) (idT 36) = 0 := by
  rw [levelTables_eq_lv]
  simpa only [chkP5, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem exists_x5 (h : chkOrb () = true) :
    ∃ x : co3X36, Rep 36 x5T (x : Perm (Fin 36)) ∧ orderOf x = 5 := by
  obtain ⟨ht, h5, -, ho5, -⟩ := orb_facts h
  simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at ht
  have hrep := rep_tabPerm ht.1
  refine ⟨⟨_, mem_of_siftOK hrep h5⟩, hrep, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact (ordTest_iff perm_faithful hrep (by norm_num)).mp ho5

theorem exists_x7 (h : chkOrb () = true) :
    ∃ x : co3X36, Rep 36 x7T (x : Perm (Fin 36)) ∧ orderOf x = 7 := by
  obtain ⟨ht, -, h7, -, ho7, -⟩ := orb_facts h
  simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at ht
  have hrep := rep_tabPerm ht.2
  refine ⟨⟨_, mem_of_siftOK hrep h7⟩, hrep, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact (ordTest_iff perm_faithful hrep (by norm_num)).mp ho7

theorem permB_mem {bs : List Table} (ht : tabsOK 36 bs = true) (hs : bs.all siftOK = true)
    (i : Fin bs.length) : permB 36 bs i ∈ co3X36 := by
  unfold tabsOK at ht
  rw [List.all_eq_true] at ht hs
  exact mem_of_siftOK (rep_tabPerm (ht _ (List.getElem_mem i.2))) (hs _ (List.getElem_mem i.2))

theorem ds_facts {ws : List Table} {ds : List (List Table)} {hs : List Table} {aT gT hT : Table}
    (hc : sixCheckE 36 ws ds hs aT gT hT = true) :
    tabsOK 36 ws = true ∧ ebasisOK 36 ws = true ∧ ds.length = 6 ∧
      ∀ r < 6, tabsOK 36 (ds.getD r []) = true := by
  simp only [sixCheckE, Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.not_eq_true',
    List.all_eq_true] at hc
  obtain ⟨hwt, hwe, -, hdl, hdall, -⟩ := hc
  exact ⟨hwt, hwe, hdl, fun r hr => (hdall _ (getD_mem (by rw [hdl]; exact hr))).1⟩

theorem no_viol {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    {t : Table → Bool} (ht : t ∈ tests) {P : Perm (Fin 36) → Prop}
    (htP : ∀ T g, Rep 36 T g → (t T = true ↔ P g)) : ∀ x : co3X36, ¬ P x := by
  classical
  exact forall_of_tests_count hn36 co3Sp36Chain valid hcnt ht htP

theorem cent_of_test {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    {us ws : List Table} (ht : centTestS 36 us (spanTabs 36 ws) ∈ tests)
    (hus : tabsOK 36 us = true) (hws : tabsOK 36 ws = true) (hwb : EBasis (permB 36 ws)) :
    ∀ x : co3X36, ¬ ((∀ i, (x : Perm (Fin 36)) * permB 36 us i = permB 36 us i * x) ∧
      (x : Perm (Fin 36)) ∉ eSub hwb) :=
  no_viol (P := fun g => (∀ i, g * permB 36 us i = permB 36 us i * g) ∧ g ∉ eSub hwb) hcnt ht
    fun _ _ hT => centTest_iff hn36 hwb (forall₂_permB hus) (forall₂_permB hws) hT

theorem six_of_test {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    {ws : List Table} {ds : List (List Table)}
    (ht : sixTestS 36 ws (spanTabs 36 ws) ds (ds.map (spanTabs 36)) ∈ tests)
    (hws : tabsOK 36 ws = true) (hwb : EBasis (permB 36 ws)) (hds : ds.length = 6)
    (hdt : ∀ r < 6, tabsOK 36 (ds.getD r []) = true) :
    ∀ x : co3X36, ¬ ((x : Perm (Fin 36)) ∈ eNorm hwb ∧
      (¬ (∀ r < 6, ∃ s < 6, ConjInto (x : Perm (Fin 36)) (dB 36 ds r) (dB 36 ds s)) ∨
        ((∀ r < 6, ConjInto (x : Perm (Fin 36)) (dB 36 ds r) (dB 36 ds r)) ∧
          (x : Perm (Fin 36)) ∉ eSub hwb))) :=
  no_viol (P := fun g => g ∈ eNorm hwb ∧
      (¬ (∀ r < 6, ∃ s < 6, ConjInto g (dB 36 ds r) (dB 36 ds s)) ∨
        ((∀ r < 6, ConjInto g (dB 36 ds r) (dB 36 ds r)) ∧ g ∉ eSub hwb))) hcnt ht
    fun _ _ hT => sixTest_iff hn36 hwb (forall₂_permB hws) hds hdt hT

theorem conclK_cand {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK)
    {ws : List Table} {ds : List (List Table)} {hs : List Table} {aT gT hT : Table}
    (hc : sixCheckE 36 ws ds hs aT gT hT = true) (haS : siftOK aT = true)
    (hgS : siftOK gT = true) (hhS : siftOK hT = true) (hwS : ws.all siftOK = true)
    {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    (hmW : centTestS 36 ws (spanTabs 36 ws) ∈ tests)
    (hmS : sixTestS 36 ws (spanTabs 36 ws) ds (ds.map (spanTabs 36)) ∈ tests)
    {us : List Table} (hsub : subOK 36 us ws = true)
    (hmU : centTestS 36 us (spanTabs 36 ws) ∈ tests)
    (hUW : us = ws ∨ (us.length + 1 = ws.length ∧ spanEq 36 us (ds.getD 0 []) = true))
    {U : Subgroup co3X36}
    (hU : U.map co3X36.subtype = Subgroup.closure {g | g ∈ us.map (tabPerm 36)})
    (hUV : U ≤ V) : ConclK co3X36 L V MK := by
  obtain ⟨hwt, hwe, hdl, hdt⟩ := ds_facts hc
  have hsub' := hsub
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsub'
  obtain ⟨⟨⟨⟨⟨hut, hue⟩, -⟩, -⟩, huW⟩, -⟩ := hsub'
  have hub : EBasis (permB 36 us) := ebasis_permB hn36 hut hue
  have hwb : EBasis (permB 36 ws) := ebasis_permB hn36 hwt hwe
  have hwH : ∀ i, permB 36 ws i ∈ co3X36 := permB_mem hwt hwS
  obtain ⟨huH, rfl⟩ := eq_eSub_of_map_eq_closure hub hU
  have hC := cent_of_test hcnt hmW hwt hwt hwb
  have hS := six_of_test hcnt hmS hwt hwb hdl hdt
  have hCU := cent_of_test hcnt hmU hut hwt hwb
  have hUle : eSub hub ≤ eSub hwb :=
    eSub_le_of_inSpan hn36 hub hwb (forall₂_permB hut) (forall₂_permB hwt) fun b hb => huW b hb
  have hVW : V ≤ eSub (liftB_basis hwH hwb) := by
    intro v hv
    have hvc : v ∈ Subgroup.centralizer (eSub (liftB_basis huH hub) : Set co3X36) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨u, hUV hu⟩ ⟨v, hv⟩)
    rw [mem_centralizer_liftB_iff huH hub] at hvc
    by_contra hvW
    exact hCU v ⟨hvc, fun hm => hvW ((mem_eSub_liftB_iff hwH hwb v).mpr hm)⟩
  rcases hUW with rfl | ⟨hl, hspan⟩
  · exact conclK_e32 h hc haS hgS hhS hwb hwH hC hS (le_antisymm hVW hUV)
  · have hcard : Nat.card (eSub (liftB_basis hwH hwb)) =
        2 * Nat.card (eSub (liftB_basis huH hub)) := by
      rw [card_eSub, card_eSub, ← hl, pow_succ, mul_comm]
    rcases eq_or_eq_of_le_of_card hUV hVW hcard with hV | hV
    · exact (false_e16 h hc hgS hhS hwb hwH hS hub huH hCU hsub (r := 0) (by norm_num) hspan
        hV).elim
    · exact conclK_e32 h hc haS hgS hhS hwb hwH hC hS hV

theorem conclK_five (hOrb : chkOrb () = true) (h5 : chkP5 () = true)
    {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK) {x : co3X36}
    (hxT : Rep 36 x5T (x : Perm (Fin 36))) (hx : orderOf x = 5) {y t : co3X36} (hy : y ∈ L)
    (hyx : y ∈ Subgroup.zpowers x) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) :
    ConclK co3X36 L V MK := by
  obtain ⟨-, -, -, -, -, hc5, -, hs5, -, ho5, -⟩ := orb_facts hOrb
  obtain ⟨ht2, hcomm⟩ := h.bad_facts hy ht hyt
  obtain ⟨cg, hcg, hU⟩ :=
    orbSub_mem_cands hn36 valid (by norm_num) hxT hx hc5 ho5 hyx ht2 hyt hcomm
  have hUV : orbSub y t ≤ V := orbSub_le (h.le_normalizer hy) ht
  obtain ⟨k, hk, rfl⟩ := exists_index_of_mem_candPerms hcg
  obtain ⟨hc1, ha1, hg1, hh1, hc3, ha3, hg3, hh3, hc4, ha4, hg4, hh4, hs0, hs1, hs2, hs3, hs4,
    hs5', he0, he2, he5, hcnt⟩ := p5_facts h5
  have hlen : cands5.length = 6 := rfl
  have hsift : ∀ k < 6, (cands5.getD k []).all siftOK = true := fun k hk =>
    List.all_eq_true.mp hs5 _ (getD_mem (by rw [hlen]; exact hk))
  have hk6 : k < 6 := by rwa [hlen] at hk
  interval_cases k
  · exact conclK_cand h hc1 ha1 hg1 hh1 (hsift 1 (by norm_num)) hcnt (by simp [tests5])
      (by simp [tests5]) hs0 (by simp [tests5]) (Or.inr ⟨rfl, he0⟩) hU hUV
  · exact conclK_cand h hc1 ha1 hg1 hh1 (hsift 1 (by norm_num)) hcnt (by simp [tests5])
      (by simp [tests5]) hs1 (by simp [tests5]) (Or.inl rfl) hU hUV
  · exact conclK_cand h hc3 ha3 hg3 hh3 (hsift 3 (by norm_num)) hcnt (by simp [tests5])
      (by simp [tests5]) hs2 (by simp [tests5]) (Or.inr ⟨rfl, he2⟩) hU hUV
  · exact conclK_cand h hc3 ha3 hg3 hh3 (hsift 3 (by norm_num)) hcnt (by simp [tests5])
      (by simp [tests5]) hs3 (by simp [tests5]) (Or.inl rfl) hU hUV
  · exact conclK_cand h hc4 ha4 hg4 hh4 (hsift 4 (by norm_num)) hcnt (by simp [tests5])
      (by simp [tests5]) hs4 (by simp [tests5]) (Or.inl rfl) hU hUV
  · exact conclK_cand h hc4 ha4 hg4 hh4 (hsift 4 (by norm_num)) hcnt (by simp [tests5])
      (by simp [tests5]) hs5' (by simp [tests5]) (Or.inr ⟨rfl, he5⟩) hU hUV

section Cert


theorem exists_x5_of_cert : ∃ x : co3X36, Rep 36 x5T (x : Perm (Fin 36)) ∧ orderOf x = 5 :=
  exists_x5 Certificates.certificate725105

theorem conclK_five_of_cert {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK) {x : co3X36}
    (hxT : Rep 36 x5T (x : Perm (Fin 36))) (hx : orderOf x = 5) {y t : co3X36} (hy : y ∈ L)
    (hyx : y ∈ Subgroup.zpowers x) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) :
    ConclK co3X36 L V MK :=
  conclK_five Certificates.certificate725105 Certificates.certificate725106 h hxT hx
    hy hyx ht hyt

end Cert

end CFSG.SectionRank.QTK.Insp443.Sp6

end
