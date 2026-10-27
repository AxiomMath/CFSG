module

public import Certificates.Data.Kernel.U42Syl.Defs
public import CFSG.Certificates.Kernel.Sp62W.Sound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTab
public import CFSG.Quasithin.H13.L32NKGSp6Group

public section

namespace CFSG.KC.U42Syl

open CFSG.KD.U42Syl CFSG.KD.Sp62W CFSG.KC.Mat8P CFSG.KGroups.Sp6 CFSG.Quasithin.H13
  CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

@[expose] def RepN (g : H6) (X : ℕ) : Prop := ∃ c, validB c = true ∧ Rep g c ∧ numC c = X

theorem RepN.mul {g h : H6} {X Y : ℕ} (hg : RepN g X) (hh : RepN h Y) :
    RepN (g * h) (mulP X Y) := by
  obtain ⟨c, hc, hgc, rfl⟩ := hg
  obtain ⟨d, hd, hhd, rfl⟩ := hh
  exact ⟨mulC c d, CFSG.KC.Sp62W.validB_mulC hc hd, hgc.mul hhd,
    CFSG.KC.Sp62W.numC_mulC hc hd⟩

theorem numC_oneC : numC oneC = oneP := by decide

theorem RepN.one : RepN 1 oneP := ⟨oneC, by decide, Rep.one, numC_oneC⟩

theorem RepN.eq {g h : H6} {X : ℕ} (hg : RepN g X) (hh : RepN h X) : g = h := by
  obtain ⟨c, hc, hgc, rfl⟩ := hg
  obtain ⟨d, hd, hhd, e⟩ := hh
  obtain rfl := CFSG.KC.Sp62W.numC_inj hd hc e
  exact hgc.eq hhd

theorem RepN.code_eq {g : H6} {X Y : ℕ} (hX : RepN g X) (hY : RepN g Y) : X = Y := by
  obtain ⟨c, -, hgc, rfl⟩ := hX
  obtain ⟨d, -, hgd, rfl⟩ := hY
  rw [(hgc.eq_iff hgd).1 rfl]

@[expose] noncomputable def kc (g : H6) : ℕ := numC (KGSp6.colsOf (mat6 g))

theorem repN_kc (g : H6) : RepN g (kc g) :=
  ⟨_, validB_iff.2 (KGSp6.validC_colsOf _), ⟨KGSp6.validC_colsOf _, (KGSp6.decodeC_colsOf _).symm⟩,
    rfl⟩

theorem RepN.kc_eq {g : H6} {X : ℕ} (h : RepN g X) : kc g = X := (repN_kc g).code_eq h

theorem repN_elt {c : List ℕ} (h : isoB c = true) : RepN (elt c) (numC c) := by
  refine ⟨c, ?_, rep_elt h, rfl⟩
  unfold isoB at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem lk_eq (d : ℕ) : ∀ (L : List ℕ) (j : ℕ), lk d L j = L.getD j d
  | [], j => by rw [List.getD_nil]; rfl
  | a :: L, 0 => by rw [List.getD_cons_zero]; rfl
  | a :: L, j + 1 => by rw [List.getD_cons_succ, ← lk_eq d L j]; rfl

theorem alph_of_mem {A : List ℕ} {H : Subgroup H6} (hA : ∀ X ∈ A, ∃ g ∈ H, RepN g X) (j : ℕ) :
    ∃ g ∈ H, RepN g (lk oneP A j) := by
  rw [lk_eq]
  by_cases hj : j < A.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hA _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨1, H.one_mem, RepN.one⟩

theorem wvP_rep {A : List ℕ} {H : Subgroup H6} (hA : ∀ X ∈ A, ∃ g ∈ H, RepN g X) :
    ∀ w : List ℕ, ∃ g ∈ H, RepN g (wvP A w)
  | [] => ⟨1, H.one_mem, RepN.one⟩
  | j :: w => by
    obtain ⟨g, hg, hr⟩ := wvP_rep hA w
    obtain ⟨a, ha, hra⟩ := alph_of_mem hA j
    have e : wvP A (j :: w) = mulP (lk oneP A j) (wvP A w) := rfl
    rw [e]
    exact ⟨a * g, H.mul_mem ha hg, hra.mul hr⟩

theorem gens_rep {gens : List (List ℕ)} (hiso : gens.all isoB = true) :
    ∀ X ∈ gens.map numC, ∃ g ∈ Hgen gens, RepN g X := by
  intro X hX
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hX
  exact ⟨elt c, elt_mem_Hgen hc, repN_elt (List.all_eq_true.1 hiso c hc)⟩

theorem words_rep {gens : List (List ℕ)} (hiso : gens.all isoB = true) {W : List (List ℕ)} :
    ∀ X ∈ W.map (wvP (gens.map numC)), ∃ g ∈ Hgen gens, RepN g X := by
  intro X hX
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hX
  exact wvP_rep (gens_rep hiso) w

theorem powP_rep {g : H6} {X : ℕ} (h : RepN g X) : ∀ k : ℕ, RepN (g ^ (k + 1)) (powP X k)
  | 0 => by
    have e : powP X 0 = X := rfl
    rw [e, zero_add, pow_one]
    exact h
  | k + 1 => by
    have e : powP X (k + 1) = mulP (powP X k) X := rfl
    rw [e, pow_succ]
    exact (powP_rep h k).mul h

theorem all2_lk {f : ℕ → ℕ → Bool} {d : ℕ} (hd : f d d = true) :
    ∀ (L L' : List ℕ), all2 f L L' = true → ∀ j, f (lk d L j) (lk d L' j) = true
  | [], L', h, j => by
    have e : L' = [] := List.isEmpty_iff.1 h
    subst e
    exact hd
  | a :: L, [], h, _ => absurd (h : false = true) Bool.false_ne_true
  | a :: L, b :: L', h, j => by
    have h' : (f a b && all2 f L L') = true := h
    rw [Bool.and_eq_true] at h'
    cases j with
    | zero => exact h'.1
    | succ j => exact all2_lk hd L L' h'.2 j

theorem gensT_iso : gensT.all isoB = true := by decide

theorem gensV_iso : gensV.all isoB = true := by decide

theorem mulP_oneP : mulP oneP oneP = oneP := by decide

theorem tab_facts {TW TWI : List (List ℕ)} {TT TI : List ℕ}
    (h : tabK (gensT.map numC) TW TWI TT TI = true) (j : ℕ) :
    ∃ s ∈ Hgen gensT, RepN s (lk oneP TT j) ∧ RepN s⁻¹ (lk oneP TI j) := by
  simp only [tabK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hT, hI⟩, hinv⟩ := h
  have hAT : ∀ X ∈ TT, ∃ g ∈ Hgen gensT, RepN g X := by
    rw [hT]
    exact words_rep gensT_iso
  have hAI : ∀ X ∈ TI, ∃ g ∈ Hgen gensT, RepN g X := by
    rw [hI]
    exact words_rep gensT_iso
  obtain ⟨s, hs, hrs⟩ := alph_of_mem hAT j
  obtain ⟨t, -, hrt⟩ := alph_of_mem hAI j
  have h0 : Nat.beq (mulP (lk oneP TT j) (lk oneP TI j)) oneP = true :=
    all2_lk (f := fun s t => Nat.beq (mulP s t) oneP) (d := oneP) (by decide) TT TI hinv j
  have h1 := Nat.eq_of_beq_eq_true h0
  have hst : s * t = 1 := by
    have := hrs.mul hrt
    rw [h1] at this
    exact this.eq RepN.one
  refine ⟨s, hs, hrs, ?_⟩
  rw [eq_inv_of_mul_eq_one_right hst] at hrt
  exact hrt

theorem rep_facts {RW AW BW : List (List ℕ)} {RT : List ℕ}
    (h : repK (gensT.map numC) (gensV.map numC) (numC cA) (numC cB) RW RT AW BW = true)
    {i : ℕ} (hi : i < 16) :
    ∃ r ∈ Hgen gensV, RepN r (lk oneP RT i) ∧ r ≠ 1 ∧ r ^ 5 = 1 ∧
      Hgen gensV ≤ Hgen gensT ⊔ Subgroup.zpowers r := by
  simp only [repK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hR, -⟩, -⟩, -⟩, hall⟩ := h
  have hAR : ∀ X ∈ RT, ∃ g ∈ Hgen gensV, RepN g X := by
    rw [hR]
    exact words_rep gensV_iso
  obtain ⟨r, hr, hrr⟩ := alph_of_mem hAR i
  have hb := hall i hi
  unfold repB at hb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hne0, h50⟩, ha0⟩, hbw0⟩ := hb
  have hne : lk oneP RT i ≠ oneP := fun h => by
    rw [h] at hne0
    exact absurd hne0 (by decide)
  have h5 := Nat.eq_of_beq_eq_true h50
  have ha := Nat.eq_of_beq_eq_true ha0
  have hbw := Nat.eq_of_beq_eq_true hbw0
  refine ⟨r, hr, hrr, fun h1 => hne ?_, ?_, ?_⟩
  · rw [h1] at hrr
    exact hrr.code_eq RepN.one
  · have := powP_rep hrr 4
    rw [h5] at this
    exact this.eq RepN.one
  · let H := Hgen gensT ⊔ Subgroup.zpowers r
    have hA : ∀ X ∈ gensT.map numC ++ [lk oneP RT i], ∃ g ∈ H, RepN g X := by
      intro X hX
      rcases List.mem_append.1 hX with hX | hX
      · obtain ⟨g, hg, hrg⟩ := gens_rep gensT_iso X hX
        exact ⟨g, Subgroup.mem_sup_left hg, hrg⟩
      · rw [List.mem_singleton.1 hX]
        exact ⟨r, Subgroup.mem_sup_right (Subgroup.mem_zpowers r), hrr⟩
    have hmem : ∀ c ∈ gensV, elt c ∈ H := by
      intro c hc
      have hc' : c = cA ∨ c = cB := by simpa [gensV] using hc
      have hiso : isoB c = true := List.all_eq_true.1 gensV_iso c hc
      rcases hc' with rfl | rfl
      · obtain ⟨g, hg, hrg⟩ := wvP_rep hA (AW.getD i [])
        rw [ha] at hrg
        rwa [← hrg.eq (repN_elt hiso)]
      · obtain ⟨g, hg, hrg⟩ := wvP_rep hA (BW.getD i [])
        rw [hbw] at hrg
        rwa [← hrg.eq (repN_elt hiso)]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact hmem c hc

theorem orderOf_five {G : Type*} [Group G] {x : G} (h5 : x ^ 5 = 1) (h1 : x ≠ 1) :
    orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h5 h1

theorem rec_facts {TW TWI RW AW BW : List (List ℕ)} {TT TI RT : List ℕ}
    (htab : tabK (gensT.map numC) TW TWI TT TI = true)
    (hrep : repK (gensT.map numC) (gensV.map numC) (numC cA) (numC cB) RW RT AW BW = true)
    (e : ℕ) :
    ∃ s ∈ Hgen gensT, ∃ r ∈ Hgen gensV, ∃ k < 4, r ^ 5 = 1 ∧ r ≠ 1 ∧
      Hgen gensV ≤ Hgen gensT ⊔ Subgroup.zpowers r ∧
      RepN (s * r ^ (k + 1) * s⁻¹) (xOf TT TI RT e) := by
  have hi : Nat.land (Nat.shiftRight e 2) 15 < 16 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hk : Nat.land e 3 < 4 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  obtain ⟨s, hs, hrs, hrsi⟩ := tab_facts htab (Nat.shiftRight e 6)
  obtain ⟨r, hr, hrr, hr1, hr5, hV⟩ := rep_facts hrep hi
  exact ⟨s, hs, r, hr, Nat.land e 3, hk, hr5, hr1, hV,
    (hrs.mul (powP_rep hrr (Nat.land e 3))).mul hrsi⟩

theorem orderOf_conj_pow {s r : H6} {k : ℕ} (hk : k < 4) (hr5 : r ^ 5 = 1) (hr1 : r ≠ 1) :
    orderOf (s * r ^ (k + 1) * s⁻¹) = 5 := by
  have hor : orderOf r = 5 := orderOf_five hr5 hr1
  refine orderOf_five ?_ ?_
  · rw [conj_pow, ← pow_mul, mul_comm (k + 1) 5, pow_mul, hr5, one_pow, mul_one, mul_inv_cancel]
  · intro h
    have h' : r ^ (k + 1) = 1 := by
      have := congrArg (fun y => s⁻¹ * y * s) h
      simpa [mul_assoc] using this
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hor] at this
    have := Nat.le_of_dvd (by omega) this
    omega

theorem canon_kc {g : H6} {X : ℕ} (hX : RepN g X) (h : canonB X = true) :
    kc g < kc (g ^ 2) ∧ kc g < kc (g ^ 3) ∧ kc g < kc (g ^ 4) := by
  simp only [canonB, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h2, h3⟩, h4⟩ := h
  have r2 := hX.mul hX
  have r3 := r2.mul hX
  have r4 := r2.mul r2
  rw [hX.kc_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_two, r2.kc_eq]
    exact h2
  · rw [pow_succ, pow_two, r3.kc_eq]
    exact h3
  · rw [(by norm_num : (4 : ℕ) = 2 + 2), pow_add, pow_two, r4.kc_eq]
    exact h4

theorem exists_pow_lt {x y : H6} (hx : orderOf x = 5) (h : y ∈ Subgroup.zpowers x) :
    ∃ j < 5, x ^ j = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  have h1 : k % (5 : ℤ) < 5 := Int.emod_lt_of_pos k (by norm_num)
  have h2 : 0 ≤ k % (5 : ℤ) := Int.emod_nonneg k (by norm_num)
  refine ⟨(k % (5 : ℤ)).toNat, by omega, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg h2]
  have := zpow_mod_orderOf x k
  rw [hx] at this
  exact_mod_cast this

theorem canon_lt {g : H6} (hc : kc g < kc (g ^ 2) ∧ kc g < kc (g ^ 3) ∧ kc g < kc (g ^ 4))
    {j : ℕ} (h2 : 2 ≤ j) (h5 : j < 5) : kc g < kc (g ^ j) := by
  interval_cases j
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2

theorem canon_unique {g h : H6} (hg : orderOf g = 5) (hh : orderOf h = 5)
    (cg : kc g < kc (g ^ 2) ∧ kc g < kc (g ^ 3) ∧ kc g < kc (g ^ 4))
    (ch : kc h < kc (h ^ 2) ∧ kc h < kc (h ^ 3) ∧ kc h < kc (h ^ 4))
    (e : Subgroup.zpowers g = Subgroup.zpowers h) : g = h := by
  have hmh : h ∈ Subgroup.zpowers g := by
    rw [e]
    exact Subgroup.mem_zpowers h
  have hmg : g ∈ Subgroup.zpowers h := by
    rw [← e]
    exact Subgroup.mem_zpowers g
  obtain ⟨j, hj, rfl⟩ := exists_pow_lt hg hmh
  obtain ⟨l, hl, hl'⟩ := exists_pow_lt hh hmg
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_one] at hh
    omega
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hl'
    rw [← hl', orderOf_one] at hg
    omega
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · obtain rfl : j = 1 := by omega
    exact (pow_one g).symm
  rcases Nat.lt_or_ge l 2 with hl2 | hl2
  · obtain rfl : l = 1 := by omega
    rw [pow_one] at hl'
    exact hl'.symm
  have a := canon_lt cg hj2 hj
  have b := canon_lt ch hl2 hl
  rw [hl'] at b
  omega

theorem card_sylow_dvd_cofactor {G : Type*} [Group G] [Finite G] {p N : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p * N) (hpN : ¬ p ∣ N) : Nat.card (Sylow p G) ∣ N := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hP : Nat.card P = p := by
    rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hp.out.ne_zero
      (by rintro rfl; simp at hpN)]
    rw [Finsupp.add_apply, hp.out.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hpN, add_zero, pow_one]
  have hidx : P.index = N := by
    have := P.card_mul_index
    rw [hP, hG] at this
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos this
  rw [← hidx]
  exact P.card_dvd_index

theorem card_sylow_five_le {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 25920) :
    Nat.card (Sylow 5 G) ≤ 1296 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := card_sylow_dvd_cofactor (p := 5) (N := 5184) (by rw [hG]) (by norm_num)
  have hm := card_sylow_modEq_one 5 G
  unfold Nat.ModEq at hm
  rcases Nat.lt_or_ge c 4 with h4 | h4
  · interval_cases c <;> omega
  · nlinarith

noncomputable def sylowOf {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] (S : Subgroup G)
    [Finite S] {N : ℕ} (hS : Nat.card S = p * N) (hpN : ¬ p ∣ N) (y : G) (hy : y ∈ S)
    (hyp : orderOf y = p) : Sylow p S :=
  Sylow.ofCard (Subgroup.zpowers (⟨y, hy⟩ : S)) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyp, hS,
      Nat.factorization_mul hp.out.ne_zero (by rintro rfl; simp at hpN), Finsupp.add_apply,
      hp.out.factorization_self, Nat.factorization_eq_zero_of_not_dvd hpN, add_zero, pow_one])

theorem zpowers_eq_of_sylowOf_eq {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    [Finite S] {N : ℕ} {hS : Nat.card S = p * N} {hpN : ¬ p ∣ N} {y z : G} {hy : y ∈ S}
    {hz : z ∈ S} {hyp : orderOf y = p} {hzp : orderOf z = p}
    (h : sylowOf S hS hpN y hy hyp = sylowOf S hS hpN z hz hzp) :
    Subgroup.zpowers y = Subgroup.zpowers z := by
  have e : Subgroup.zpowers (⟨y, hy⟩ : S) = Subgroup.zpowers (⟨z, hz⟩ : S) := by
    have e0 := congrArg (fun P : Sylow p S => (P : Subgroup S)) h
    simpa only [sylowOf, Sylow.coe_ofCard] using e0
  have := congrArg (Subgroup.map S.subtype) e
  rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this

theorem exists_zpowers_eq_of_list {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (S : Subgroup G)
    [Finite S] {N : ℕ} (hS : Nat.card S = p * N) (hpN : ¬ p ∣ N) (L : List G)
    (hLS : ∀ X ∈ L, X ∈ S ∧ orderOf X = p)
    (hnd : L.Pairwise fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y)
    (hcard : Nat.card (Sylow p S) ≤ L.length) {x : G} (hx : x ∈ S) (hxp : orderOf x = p) :
    ∃ X ∈ L, Subgroup.zpowers X = Subgroup.zpowers x := by
  have hmem : ∀ i : Fin L.length, L[i] ∈ L := fun i => List.getElem_mem i.2
  let f : Fin L.length → Sylow p S := fun i =>
    sylowOf S hS hpN L[i] (hLS _ (hmem i)).1 (hLS _ (hmem i)).2
  have hinj : Function.Injective f := by
    intro i j hij
    have e := zpowers_eq_of_sylowOf_eq hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact (List.pairwise_iff_getElem.1 hnd i j i.2 j.2 hlt) e
    · exact (List.pairwise_iff_getElem.1 hnd j i j.2 i.2 hlt) e.symm
  have hbij := hinj.bijective_of_nat_card_le (by simpa using hcard)
  obtain ⟨i, hi⟩ := hbij.2 (sylowOf S hS hpN x hx hxp)
  exact ⟨L[i], hmem i, zpowers_eq_of_sylowOf_eq hi⟩

theorem recB_append {TT TI RT : List ℕ} {L₂ : List ℕ} {q r : ℕ} (h₂ : recB TT TI RT L₂ q r = true) :
    ∀ (L₁ : List ℕ) (p : ℕ), recB TT TI RT L₁ p q = true → recB TT TI RT (L₁ ++ L₂) p r = true
  | [], p, h => by
    have e : p = q := Nat.eq_of_beq_eq_true h
    subst e
    exact h₂
  | e :: L₁, p, h => by
    have h' : (Nat.blt p (xOf TT TI RT e) && canonB (xOf TT TI RT e) &&
        recB TT TI RT L₁ (xOf TT TI RT e) q) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    have : (Nat.blt p (xOf TT TI RT e) && canonB (xOf TT TI RT e) &&
        recB TT TI RT (L₁ ++ L₂) (xOf TT TI RT e) r) = true := by
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨h'.1, recB_append h₂ L₁ _ h'.2⟩
    exact this

theorem recB_sound {TT TI RT : List ℕ} :
    ∀ (L : List ℕ) (p q : ℕ), recB TT TI RT L p q = true →
      (∀ e ∈ L, canonB (xOf TT TI RT e) = true ∧ p < xOf TT TI RT e) ∧
      (L.map (xOf TT TI RT)).Pairwise (· < ·)
  | [], _, _, _ => ⟨by simp, List.Pairwise.nil⟩
  | e :: L, p, q, h => by
    have h' : (Nat.blt p (xOf TT TI RT e) && canonB (xOf TT TI RT e) &&
        recB TT TI RT L (xOf TT TI RT e) q) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨hp, hc⟩, hL⟩ := h'
    obtain ⟨ih1, ih2⟩ := recB_sound L _ q hL
    refine ⟨?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact ⟨hc, hp⟩
      · exact ⟨(ih1 e' he').1, lt_trans hp (ih1 e' he').2⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih2⟩
      intro y hy
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 hy
      exact (ih1 e' he').2

@[expose] noncomputable def eltN (X : ℕ) : H6 :=
  open Classical in if h : ∃ g, RepN g X then h.choose else 1

theorem repN_eltN {g : H6} {X : ℕ} (h : RepN g X) : RepN (eltN X) X := by
  have hx : ∃ g, RepN g X := ⟨g, h⟩
  rw [eltN, dif_pos hx]
  exact hx.choose_spec

theorem order5_cover_of_checks {TW TWI RW AW BW : List (List ℕ)} {TT TI RT REC : List ℕ} {K : ℕ}
    (htab : tabK (gensT.map numC) TW TWI TT TI = true)
    (hrep : repK (gensT.map numC) (gensV.map numC) (numC cA) (numC cB) RW RT AW BW = true)
    (hrec : recB TT TI RT REC 0 K = true) (hlen : REC.length = 1296)
    (hV : Nat.card (Hgen gensV) = 25920) (hTV : Hgen gensT ≤ Hgen gensV)
    {x : H6} (hx : x ∈ Hgen gensV) (hx1 : x ≠ 1) (hx5 : x ^ 5 = 1) :
    Hgen gensV ≤ Hgen gensT ⊔ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (Hgen gensV) := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  obtain ⟨hcan, hsort⟩ := recB_sound REC 0 K hrec
  have hfacts : ∀ e, ∃ s ∈ Hgen gensT, ∃ r ∈ Hgen gensV, ∃ k < 4, r ^ 5 = 1 ∧ r ≠ 1 ∧
      Hgen gensV ≤ Hgen gensT ⊔ Subgroup.zpowers r ∧
      eltN (xOf TT TI RT e) = s * r ^ (k + 1) * s⁻¹ := by
    intro e
    obtain ⟨s, hs, r, hr, k, hk, hr5, hr1, hVr, hR⟩ := rec_facts htab hrep e
    exact ⟨s, hs, r, hr, k, hk, hr5, hr1, hVr, (repN_eltN hR).eq hR⟩
  have hord : ∀ e, eltN (xOf TT TI RT e) ∈ Hgen gensV ∧ orderOf (eltN (xOf TT TI RT e)) = 5 := by
    intro e
    obtain ⟨s, hs, r, hr, k, hk, hr5, hr1, -, he⟩ := hfacts e
    rw [he]
    exact ⟨mul_mem (mul_mem (hTV hs) (pow_mem hr _)) (inv_mem (hTV hs)),
      orderOf_conj_pow hk hr5 hr1⟩
  have hcode : ∀ e, RepN (eltN (xOf TT TI RT e)) (xOf TT TI RT e) := by
    intro e
    obtain ⟨_, _, _, _, _, _, _, _, _, hR⟩ := rec_facts htab hrep e
    exact repN_eltN hR
  have hLS : ∀ X ∈ REC.map fun e => eltN (xOf TT TI RT e), X ∈ Hgen gensV ∧ orderOf X = 5 := by
    intro X hX
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hX
    exact hord e
  have hnd : (REC.map fun e => eltN (xOf TT TI RT e)).Pairwise
      fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y := by
    rw [List.pairwise_map] at hsort ⊢
    refine hsort.imp_of_mem ?_
    intro e e' he he' hlt heq
    have hgg := canon_unique (hord e).2 (hord e').2 (canon_kc (hcode e) (hcan e he).1)
      (canon_kc (hcode e') (hcan e' he').1) heq
    have h1 := (hcode e).kc_eq
    have h2 := (hcode e').kc_eq
    rw [hgg] at h1
    omega
  obtain ⟨X, hXL, hXx⟩ := exists_zpowers_eq_of_list (p := 5) (N := 5184) (Hgen gensV)
    (by rw [hV]) (by norm_num) _ hLS hnd
    (by rw [List.length_map, hlen]; exact card_sylow_five_le hV) hx (orderOf_five hx5 hx1)
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hXL
  obtain ⟨s, hs, r, hr, k, hk, hr5, hr1, hVr, he⟩ := hfacts e
  have hXmem : s * r ^ (k + 1) * s⁻¹ ∈ Subgroup.zpowers x := by
    rw [← he, ← hXx]
    exact Subgroup.mem_zpowers _
  let H := Hgen gensT ⊔ Subgroup.zpowers x
  have hrk : r ^ (k + 1) ∈ H := by
    have e1 : r ^ (k + 1) = s⁻¹ * (s * r ^ (k + 1) * s⁻¹) * s := by group
    rw [e1]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem hs)) (Subgroup.mem_sup_right hXmem))
      (Subgroup.mem_sup_left hs)
  have hrH : r ∈ H := by
    have hor : orderOf r = 5 := orderOf_five hr5 hr1
    have hm' : (k + 1) * (k + 1) ^ 3 % 5 = 1 := by interval_cases k <;> norm_num
    have hm : (r ^ (k + 1)) ^ ((k + 1) ^ 3) = r := by
      rw [← pow_mul, ← pow_mod_orderOf r ((k + 1) * (k + 1) ^ 3), hor, hm', pow_one]
    rw [← hm]
    exact pow_mem hrk _
  exact hVr.trans (sup_le le_sup_left ((Subgroup.zpowers_le).2 hrH))

end CFSG.KC.U42Syl
