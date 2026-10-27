module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.L52Model
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.E16Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.E64Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Perm3
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.E8Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermCands
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermScan
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CFSG.SectionRank.QTK.Insp443.L52

open Equiv CFSG.Open CFSG.Certificates CFSG.Literature.GL52 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem le_or_le_of_forall_mem_or {G : Type*} [Group G] {V Z W : Subgroup G}
    (h : ∀ v ∈ V, v ∈ Z ∨ v ∈ W) : V ≤ Z ∨ V ≤ W := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨a, haV, haZ⟩ := SetLike.not_le_iff_exists.mp hne.1
  obtain ⟨b, hbV, hbW⟩ := SetLike.not_le_iff_exists.mp hne.2
  have haW : a ∈ W := (h a haV).resolve_left haZ
  have hbZ : b ∈ Z := (h b hbV).resolve_right hbW
  rcases h (a * b) (V.mul_mem haV hbV) with hab | hab
  · exact haZ (by simpa using Z.mul_mem hab (Z.inv_mem hbZ))
  · exact hbW (by simpa using W.mul_mem (W.inv_mem haW) hab)

theorem prime_eq_of_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 9999360) :
    p = 5 ∨ p = 7 ∨ p = 31 := by
  have h' : p ∣ 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1))

theorem permBk_append {n : ℕ} {as bs : List Table} (ha : as.length = 3) :
    Fin.append (permBk n 3 as) (permBk n 3 bs) = permBk n 6 (as ++ bs) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    unfold permBk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, Fin.coe_castAdd,
      List.getElem?_append_left (by rw [ha]; exact j.2)]
  · rw [Fin.append_right]
    unfold permBk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, Fin.coe_natAdd,
      List.getElem?_append_right (by rw [ha]; omega), ha, Nat.add_sub_cancel_left]

theorem permBk_diagT {n : ℕ} {as bs : List Table} (hat : tabsOK n as = true)
    (hbt : tabsOK n bs = true) (hdt : tabsOK n (diagT n as bs) = true) (ha : as.length = 3)
    (hb : bs.length = 3) (i : Fin 3) :
    permBk n 3 (diagT n as bs) i = permBk n 3 as i * permBk n 3 bs i := by
  have hl : (diagT n as bs).length = 3 := by
    unfold diagT
    rw [List.length_zipWith, ha, hb, Nat.min_self]
  have hd : (diagT n as bs).getD i #[] = compT n (as.getD i #[]) (bs.getD i #[]) := by
    unfold diagT
    rw [List.getD_eq_getElem _ _ (by rw [List.length_zipWith, ha, hb, Nat.min_self]; exact i.2),
      List.getElem_zipWith, List.getD_eq_getElem _ _ (by rw [ha]; exact i.2),
      List.getD_eq_getElem _ _ (by rw [hb]; exact i.2)]
  have h1 := rep_getD_of_forall₂ (forall₂_permBk hdt hl) i
  rw [hd] at h1
  exact rep_eq h1 (Rep.compT (rep_getD_of_forall₂ (forall₂_permBk hat ha) i)
    (rep_getD_of_forall₂ (forall₂_permBk hbt hb) i))


theorem e16_facts (hP : chkP52 () = true) {z : ℕ} (hz : z < 7) :
    (e16.getD z []).length = 4 ∧ tabsOK 31 (e16.getD z []) = true ∧
      ebasisOK 31 (e16.getD z []) = true := by
  have hok := (p_facts hP).1 z hz
  simp only [e16OK, subOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hl, ⟨⟨⟨⟨⟨ht, he⟩, -⟩, -⟩, -⟩, -⟩⟩ := hok
  exact ⟨hl, ht, he⟩

theorem e64_facts (hP : chkP52 () = true) {w : ℕ} (hw : w < 2) :
    (e64a0.getD w []).length = 3 ∧ (e64a1.getD w []).length = 3 ∧ tabsOK 31 (wB w) = true ∧
      ebasisOK 31 (wB w) = true ∧
      ∀ A ∈ aB w, tabsOK 31 A = true ∧ ebasisOK 31 A = true := by
  have hok := (p_facts hP).2.1 w hw
  simp only [e64OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨hl0, hl1⟩, hsubW⟩, hsubA⟩ := hok
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsubW
  obtain ⟨⟨⟨⟨⟨hwt, hwe⟩, -⟩, -⟩, -⟩, -⟩ := hsubW
  refine ⟨hl0, hl1, hwt, hwe, fun A hA => ?_⟩
  have h1 := hsubA A hA
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨hat, hae⟩, -⟩, -⟩, -⟩, -⟩ := h1
  exact ⟨hat, hae⟩

theorem length_wB (hP : chkP52 () = true) {w : ℕ} (hw : w < 2) : (wB w).length = 6 := by
  obtain ⟨hl0, hl1, -⟩ := e64_facts hP hw
  unfold wB
  rw [List.length_append, hl0, hl1]

theorem conclK_e16 (hP : chkP52 () = true) {L V MK : Subgroup glCert.originalSubgroup}
    (h : KConfig glCert.originalSubgroup L V MK) {z : ℕ} (hz : z < 7)
    (hzH : ∀ i, permBk 31 4 (e16.getD z []) i ∈ glCert.originalSubgroup)
    (hzb : EBasis (permBk 31 4 (e16.getD z []))) (hZV : eSub (liftB_basis hzH hzb) ≤ V) :
    ConclK glCert.originalSubgroup L V MK := by
  obtain ⟨hzl, hzt, -⟩ := e16_facts hP hz
  obtain ⟨-, -, -, hcntN, hcnt⟩ := p_facts hP
  have hzs := forall₂_permBk hzt hzl
  have hcent : Subgroup.centralizer (eSub (liftB_basis hzH hzb) : Set glCert.originalSubgroup) ≤
      eSub (liftB_basis hzH hzb) := fun x hx => by
    rw [mem_centralizer_liftB_iff hzH hzb] at hx
    exact (mem_eSub_liftB_iff hzH hzb x).mpr
      (cent_of_scan hn31 glCert glCert_valid hcnt hzb hzs hzs (mem_tests_e16 hz) x hx)
  have hcardN : Nat.card (eNorm (liftB_basis hzH hzb)) = 322560 := by
    rw [card_eNorm_liftB hn31 glCert glCert_valid hzH hzb hzs]
    have h1 := hcntN z hz
    rwa [getD_map_lt (spanTabs 31) (by rw [length_e16]; exact hz) [] []] at h1
  exact KConfig.conclK_of_e16 (liftB_basis hzH hzb) h hcardN hcent hZV

theorem conclK_e16cand (hP : chkP52 () = true) {L V MK : Subgroup glCert.originalSubgroup}
    (h : KConfig glCert.originalSubgroup L V MK) {z : ℕ} (hz : z < 7)
    {U : Subgroup glCert.originalSubgroup}
    (hU : U.map glCert.originalSubgroup.subtype =
      Subgroup.closure {g | g ∈ (e16.getD z []).map (tabPerm 31)}) (hUV : U ≤ V) :
    ConclK glCert.originalSubgroup L V MK := by
  obtain ⟨hzl, hzt, hze⟩ := e16_facts hP hz
  have hzb := ebasis_permBk hn31 hzt hze hzl
  obtain ⟨hzH, rfl⟩ := eq_eSub_of_map_eq_closure' hzb (closure_map_tabPerm_k hzl hzb) hU
  exact conclK_e16 hP h hz hzH hzb hUV

theorem conclK_e64 (hO : chkOrb52 () = true) (hP : chkP52 () = true)
    {L V MK : Subgroup glCert.originalSubgroup} (h : KConfig glCert.originalSubgroup L V MK)
    {w : ℕ} (hw : w < 2) (hwH : ∀ i, permBk 31 6 (wB w) i ∈ glCert.originalSubgroup)
    (hwb : EBasis (permBk 31 6 (wB w))) (hV : V = eSub (liftB_basis hwH hwb)) :
    ConclK glCert.originalSubgroup L V MK := by
  obtain ⟨hl0, hl1, hwt, -, hA⟩ := e64_facts hP hw
  obtain ⟨-, -, -, -, hcnt⟩ := p_facts hP
  have hal : ∀ i : Fin 3, ((aB w).getD i []).length = 3 := by
    intro i
    fin_cases i
    · exact hl0
    · exact hl1
    · show (diagT 31 (e64a0.getD w []) (e64a1.getD w [])).length = 3
      unfold diagT
      rw [List.length_zipWith, hl0, hl1, Nat.min_self]
  have haOK : ∀ i : Fin 3,
      tabsOK 31 ((aB w).getD i []) = true ∧ ebasisOK 31 ((aB w).getD i []) = true :=
    fun i => hA _ (getD_mem (by show (i : ℕ) < 3; exact i.2))
  let a : Fin 3 → Fin 3 → Perm (Fin 31) := fun i => permBk 31 3 ((aB w).getD i [])
  have hab : ∀ i, EBasis (a i) := fun i => ebasis_permBk hn31 (haOK i).1 (haOK i).2 (hal i)
  have has : ∀ i : Fin 3, List.Forall₂ (Rep 31) ((aB w).getD i []) (List.ofFn (a i)) :=
    fun i => forall₂_permBk (haOK i).1 (hal i)
  have haH : ∀ i r, a i r ∈ glCert.originalSubgroup :=
    fun i => permBk_mem hO (aB_sub_memL hw i.2) (hal i)
  have hwl := length_wB hP hw
  have hsw := forall₂_permBk hwt hwl
  have happ : Fin.append (a 0) (a 1) = permBk 31 6 (wB w) := permBk_append hl0
  have hdiag : ∀ r, a 2 r = a 0 r * a 1 r :=
    permBk_diagT (haOK 0).1 (haOK 1).1 (haOK 2).1 (hal 0) (hal 1)
  have hwP : EBasis (Fin.append (a 0) (a 1)) := by
    rw [happ]
    exact hwb
  have ha₀ : EBasis (liftB (a 0) (haH 0)) := liftB_basis (haH 0) (hab 0)
  have ha₁ : EBasis (liftB (a 1) (haH 1)) := liftB_basis (haH 1) (hab 1)
  have happX : Fin.append (liftB (a 0) (haH 0)) (liftB (a 1) (haH 1)) =
      liftB (permBk 31 6 (wB w)) hwH := by
    funext i
    apply Subtype.ext
    rw [coe_liftB, ← happ]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left, Fin.append_left, coe_liftB]
    · rw [Fin.append_right, Fin.append_right, coe_liftB]
  have hwX : EBasis (Fin.append (liftB (a 0) (haH 0)) (liftB (a 1) (haH 1))) := by
    rw [happX]
    exact liftB_basis hwH hwb
  have hdiagX : (fun i => liftB (a 0) (haH 0) i * liftB (a 1) (haH 1) i) = liftB (a 2) (haH 2) := by
    funext i
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_liftB, coe_liftB, coe_liftB, hdiag]
  have ha₂ : EBasis fun i => liftB (a 0) (haH 0) i * liftB (a 1) (haH 1) i := by
    rw [hdiagX]
    exact liftB_basis (haH 2) (hab 2)
  have hWeq : eSub hwX = eSub (liftB_basis hwH hwb) := eSub_congr _ _ happX
  have hV' : V = eSub hwX := hV.trans hWeq.symm
  let A : Fin 3 → Subgroup glCert.originalSubgroup := fun i => eSub (liftB_basis (haH i) (hab i))
  have hperm : ∀ g ∈ Subgroup.normalizer (eSub hwX : Set glCert.originalSubgroup), ∀ i, ∃ j,
      (A i).map (MulAut.conj g).toMonoidHom = A j := by
    intro g hg i
    rw [hWeq, mem_normalizer_liftB_iff hwH hwb] at hg
    obtain ⟨j, hj⟩ := perm3_of_scan hn31 glCert glCert_valid hcnt hwb hsw has
      (mem_tests_perm3 hw) rfl g hg i
    exact ⟨j, map_conj_liftB (haH i) (hab i) (haH j) (hab j) g hj⟩
  have hne01 : eSub (hab 0) ≠ eSub (hab 1) := by
    intro he
    apply a1_not_mem_a0 (hab 0) (hab 1) hwP 0
    rw [he]
    exact mem_eSub (hab 1) 0
  have hne02 : eSub (hab 0) ≠ eSub (hab 2) := by
    intro he
    apply a1_not_mem_a0 (hab 0) (hab 1) hwP 0
    have h1 : a 0 0 * a 1 0 ∈ eSub (hab 0) := by
      rw [he, ← hdiag]
      exact mem_eSub (hab 2) 0
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_eSub (hab 0) 0)) h1
    rwa [inv_mul_cancel_left] at h2
  have hne12 : eSub (hab 1) ≠ eSub (hab 2) := by
    intro he
    apply a0_not_mem_a1 (hab 0) (hab 1) hwP 0
    have h1 : a 0 0 * a 1 0 ∈ eSub (hab 1) := by
      rw [he, ← hdiag]
      exact mem_eSub (hab 2) 0
    have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (mem_eSub (hab 1) 0))
    rwa [mul_inv_cancel_right] at h2
  have hinj : Function.Injective A := by
    intro i j hij
    have h1 : eSub (hab i) = eSub (hab j) := by
      rw [← eSub_liftB_map (haH i) (hab i), ← eSub_liftB_map (haH j) (hab j)]
      exact congrArg (fun K => K.map glCert.originalSubgroup.subtype) hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h1 hne01
    · exact absurd h1 hne02
    · exact absurd h1.symm hne01
    · rfl
    · exact absurd h1 hne12
    · exact absurd h1.symm hne02
    · exact absurd h1.symm hne12
    · rfl
  have hLW : L ≤ Subgroup.normalizer (eSub hwX : Set glCert.originalSubgroup) :=
    hV' ▸ h.le_normalizer
  have hL0 : L ≤ eNorm ha₀ := le_normalizer_of_perm3 hinj hperm hLW h.perfect 0
  have hL1 : L ≤ eNorm ha₁ := le_normalizer_of_perm3 hinj hperm hLW h.perfect 1
  have hA2 : A 2 = eSub ha₂ := eSub_congr _ _ hdiagX.symm
  have hL2 : L ≤ eNorm ha₂ := by
    have h1 := le_normalizer_of_perm3 hinj hperm hLW h.perfect 2
    rwa [hA2] at h1
  have hC0 : Subgroup.centralizer (eSub ha₀ : Set glCert.originalSubgroup) ⊓ eNorm ha₁ ≤
      eSub hwX := by
    intro g hg
    obtain ⟨hg0, hg1⟩ := Subgroup.mem_inf.mp hg
    rw [hWeq, mem_eSub_liftB_iff hwH hwb]
    rw [mem_centralizer_liftB_iff (haH 0) (hab 0)] at hg0
    have hg1' := (mem_normalizer_liftB_iff (haH 1) (hab 1) g).mp hg1
    exact cn_of_scan hn31 glCert glCert_valid hcnt (hab 1) hwb (has 0) (has 1) hsw
      (mem_tests_cn hw) g hg0 hg1'
  exact KConfig.conclK_of_e64 ha₀ ha₁ hwX ha₂ h hV' hL0 hL1 hL2 hC0

theorem conclK_e8 {L MK : Subgroup glCert.originalSubgroup} {us : List Table}
    (huH : ∀ i, permBk 31 3 us i ∈ glCert.originalSubgroup) (hub : EBasis (permBk 31 3 us))
    (h : KConfig glCert.originalSubgroup L (eSub (liftB_basis huH hub)) MK)
    (hC : ∀ y : glCert.originalSubgroup,
      (∀ i, (y : Perm (Fin 31)) * permBk 31 3 us i = permBk 31 3 us i * y) →
        (y : Perm (Fin 31)) ^ 128 = 1) :
    ConclK glCert.originalSubgroup L (eSub (liftB_basis huH hub)) MK := by
  refine KConfig.conclK_of_e8 (liftB_basis huH hub) h fun g => ⟨7, ?_⟩
  have h1 := hC g ((mem_centralizer_liftB_iff huH hub g).mp g.2)
  apply Subtype.ext
  apply Subtype.ext
  simpa using h1

theorem comm_of_le {V : Subgroup glCert.originalSubgroup} (hV : IsElemAbelian 2 V)
    {us : List Table} (huH : ∀ i, permBk 31 3 us i ∈ glCert.originalSubgroup)
    (hub : EBasis (permBk 31 3 us)) (hUV : eSub (liftB_basis huH hub) ≤ V)
    {v : glCert.originalSubgroup} (hv : v ∈ V) (i : Fin 3) :
    (v : Perm (Fin 31)) * permBk 31 3 us i = permBk 31 3 us i * v := by
  have h1 := congrArg Subtype.val (congrArg Subtype.val
    (hV.1.is_comm.comm ⟨v, hv⟩ ⟨_, hUV (mem_eSub (liftB_basis huH hub) i)⟩))
  simpa [coe_liftB] using h1

theorem conclK_typeB (hO : chkOrb52 () = true) (hP : chkP52 () = true)
    {L V MK : Subgroup glCert.originalSubgroup} (h : KConfig glCert.originalSubgroup L V MK)
    {x : glCert.originalSubgroup} (hxT : Rep 31 x7T (x : Perm (Fin 31))) (hxL : x ∈ L)
    {k z w : ℕ} (hk : k < 24) (hz : z < 7) (hw : w < 2) (hkd : kind7.getD k (3, 0, 0) = (1, z, w))
    (hl : (cands7.getD k []).length = 3)
    (hsubZ : subOK 31 (cands7.getD k []) (e16.getD z []) = true)
    (hsubW : subOK 31 (cands7.getD k []) (wB w) = true)
    (hirr : irrOK 31 7 x7T (invT 31 x7T) (cands7.getD k []) (wB w) = true)
    {U : Subgroup glCert.originalSubgroup}
    (hU : U.map glCert.originalSubgroup.subtype =
      Subgroup.closure {g | g ∈ (cands7.getD k []).map (tabPerm 31)}) (hUV : U ≤ V) :
    ConclK glCert.originalSubgroup L V MK := by
  obtain ⟨-, -, -, -, hcnt⟩ := p_facts hP
  obtain ⟨hzl, -, -⟩ := e16_facts hP hz
  have hwl := length_wB hP hw
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsubZ hsubW
  obtain ⟨⟨⟨⟨⟨hut, hue⟩, hzt⟩, hze⟩, -⟩, -⟩ := hsubZ
  obtain ⟨⟨⟨⟨-, hwt⟩, hwe⟩, -⟩, -⟩ := hsubW
  have hub := ebasis_permBk hn31 hut hue hl
  have hzb := ebasis_permBk hn31 hzt hze hzl
  have hwb := ebasis_permBk hn31 hwt hwe hwl
  have hus := forall₂_permBk hut hl
  have hzs := forall₂_permBk hzt hzl
  have hws := forall₂_permBk hwt hwl
  obtain ⟨huH, rfl⟩ := eq_eSub_of_map_eq_closure' hub (closure_map_tabPerm_k hl hub) hU
  have hzH := permBk_mem hO (e16_sub_memL hz) hzl
  have hwH := permBk_mem hO (wB_sub_memL hw) hwl
  have hxi : Rep 31 (invT 31 x7T) (x : Perm (Fin 31))⁻¹ := rep_invT_of_rep hn31 hxT
  have hxV := h.le_normalizer hxL
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcs : ∀ ab ∈ x7Pairs (invT 31 x7T), ∃ c : Perm (Fin 31),
      (∃ j : ℕ, c = (x : Perm (Fin 31)) ^ j) ∧ Rep 31 ab.1 c ∧ Rep 31 ab.2 c⁻¹ := by
    intro ab hab
    unfold x7Pairs at hab
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hab
    refine ⟨(x : Perm (Fin 31)) ^ j, ⟨j, rfl⟩, Rep.powT hn31 hxT j, ?_⟩
    rw [← inv_pow]
    exact Rep.powT hn31 hxi j
  have hZW : ∀ v ∈ V, v ∈ eSub (liftB_basis hzH hzb) ∨ v ∈ eSub (liftB_basis hwH hwb) := by
    intro v hv
    have hvc : ∀ c : Perm (Fin 31), (∃ j : ℕ, c = (x : Perm (Fin 31)) ^ j) →
        (v : Perm (Fin 31)) * (c * v * c⁻¹) = c * v * c⁻¹ * v := by
      rintro c ⟨j, rfl⟩
      have hmem : x ^ j * v * (x ^ j)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxV j) v).mp hv
      have h1 := congrArg Subtype.val (hcomm v hv _ hmem)
      simpa using h1
    rcases s_of_scan hn31 glCert glCert_valid hcnt hzb hwb hus hzs hws hcs
        (mem_tests_s hk hz hw hkd) v (comm_of_le h.elemAbelian huH hub hUV hv) hvc with h1 | h1
    · exact Or.inl ((mem_eSub_liftB_iff hzH hzb v).mpr h1)
    · exact Or.inr ((mem_eSub_liftB_iff hwH hwb v).mpr h1)
  have hC2 : ∀ y : glCert.originalSubgroup,
      (∀ i, (y : Perm (Fin 31)) * permBk 31 3 (cands7.getD k []) i =
        permBk 31 3 (cands7.getD k []) i * y) → (y : Perm (Fin 31)) ^ 128 = 1 :=
    fun y hy => pow_of_scan hn31 glCert glCert_valid hcnt hus (mem_tests_c2 hk hkd) y hy
  rcases le_or_le_of_forall_mem_or hZW with hVZ | hVW
  · have hcard : Nat.card (eSub (liftB_basis hzH hzb)) =
        2 * Nat.card (eSub (liftB_basis huH hub)) := by
      rw [card_eSub, card_eSub]
      norm_num
    rcases eq_or_eq_of_le_of_card hUV hVZ hcard with hV | hV
    · subst hV
      exact conclK_e8 huH hub h hC2
    · exact conclK_e16 hP h hz hzH hzb hV.ge
  · rcases eq_or_eq_of_irrOK hn31 (liftB_basis huH hub) (liftB_basis hwH hwb)
        (forall₂_liftB huH hus) (forall₂_liftB hwH hws) hxT hxi hirr hUV hVW hxV with hV | hV
    · subst hV
      exact conclK_e8 huH hub h hC2
    · exact conclK_e64 hO hP h hw hwH hwb hV

theorem conclK_typeC (hO : chkOrb52 () = true) (hP : chkP52 () = true)
    {L V MK : Subgroup glCert.originalSubgroup} (h : KConfig glCert.originalSubgroup L V MK)
    {x : glCert.originalSubgroup} (hxT : Rep 31 x7T (x : Perm (Fin 31))) (hxL : x ∈ L)
    {k z w : ℕ} (hk : k < 24) (hw : w < 2) (hkd : kind7.getD k (3, 0, 0) = (2, z, w))
    (hl : (cands7.getD k []).length = 3)
    (hsubW : subOK 31 (cands7.getD k []) (wB w) = true)
    (hirr : irrOK 31 7 x7T (invT 31 x7T) (cands7.getD k []) (wB w) = true)
    {U : Subgroup glCert.originalSubgroup}
    (hU : U.map glCert.originalSubgroup.subtype =
      Subgroup.closure {g | g ∈ (cands7.getD k []).map (tabPerm 31)}) (hUV : U ≤ V) :
    ConclK glCert.originalSubgroup L V MK := by
  obtain ⟨-, -, -, -, hcnt⟩ := p_facts hP
  have hwl := length_wB hP hw
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsubW
  obtain ⟨⟨⟨⟨⟨hut, hue⟩, hwt⟩, hwe⟩, -⟩, -⟩ := hsubW
  have hub := ebasis_permBk hn31 hut hue hl
  have hwb := ebasis_permBk hn31 hwt hwe hwl
  have hus := forall₂_permBk hut hl
  have hws := forall₂_permBk hwt hwl
  obtain ⟨huH, rfl⟩ := eq_eSub_of_map_eq_closure' hub (closure_map_tabPerm_k hl hub) hU
  have hwH := permBk_mem hO (wB_sub_memL hw) hwl
  have hxi : Rep 31 (invT 31 x7T) (x : Perm (Fin 31))⁻¹ := rep_invT_of_rep hn31 hxT
  have hxV := h.le_normalizer hxL
  have hCU : ∀ y : glCert.originalSubgroup,
      (∀ i, (y : Perm (Fin 31)) * permBk 31 3 (cands7.getD k []) i =
        permBk 31 3 (cands7.getD k []) i * y) → (y : Perm (Fin 31)) ∈ eSub hwb :=
    fun y hy => cent_of_scan hn31 glCert glCert_valid hcnt hwb hus hws (mem_tests_cent hk hw hkd) y hy
  have hVW : V ≤ eSub (liftB_basis hwH hwb) := fun v hv =>
    (mem_eSub_liftB_iff hwH hwb v).mpr (hCU v (comm_of_le h.elemAbelian huH hub hUV hv))
  have hC2 : ∀ y : glCert.originalSubgroup,
      (∀ i, (y : Perm (Fin 31)) * permBk 31 3 (cands7.getD k []) i =
        permBk 31 3 (cands7.getD k []) i * y) → (y : Perm (Fin 31)) ^ 128 = 1 := fun y hy => by
    have h1 := eSub_sq hwb _ (hCU y hy)
    calc (y : Perm (Fin 31)) ^ 128 = ((y : Perm (Fin 31)) * y) ^ 64 := by
          rw [← pow_two, ← pow_mul]
      _ = 1 := by rw [h1, one_pow]
  rcases eq_or_eq_of_irrOK hn31 (liftB_basis huH hub) (liftB_basis hwH hwb)
      (forall₂_liftB huH hus) (forall₂_liftB hwH hws) hxT hxi hirr hUV hVW hxV with hV | hV
  · subst hV
    exact conclK_e8 huH hub h hC2
  · exact conclK_e64 hO hP h hw hwH hwb hV

end CFSG.SectionRank.QTK.Insp443.L52

end
