module

public import Certificates.Data.Kernel.L52Insp443.Sub
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv
public import CFSG.Certificates.Kernel.L52Insp443.OrbSound

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Literature.GL52 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Sporadic.Schreier.Native

@[expose] noncomputable def maskG : List ℕ → ℕ → G
  | [], _ => 1
  | b :: bs, m => (if m % 2 = 1 then gD b else 1) * maskG bs (m / 2)

theorem maskK_cons (b : ℕ) (bs : List ℕ) (m : ℕ) :
    maskK (b :: bs) m = if m % 2 = 1 then mmulK b (maskK bs (m / 2)) else maskK bs (m / 2) := by
  change Bool.rec (motive := fun _ => ℕ) (maskK bs (Nat.div m 2)) (mmulK b (maskK bs (Nat.div m 2)))
    (Nat.beq (Nat.mod m 2) 1) = _
  by_cases h : m % 2 = 1
  · have hb : Nat.beq (Nat.mod m 2) 1 = true := by
      rw [Nat.beq_eq]
      exact h
    rw [if_pos h, hb]
    rfl
  · have hb : Nat.beq (Nat.mod m 2) 1 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact h (Nat.eq_of_beq_eq_true e)
    rw [if_neg h, hb]
    rfl

theorem mcode_maskG : ∀ {cs : List ℕ}, (∀ c ∈ cs, unitK c = true) → ∀ m,
    mcode ((maskG cs m : G) : Mat) = maskK cs m
  | [], _, m => by
    rw [maskG.eq_1, kG_one]
    rfl
  | b :: bs, hu, m => by
    have ih := mcode_maskG (fun c hc => hu c (List.mem_cons_of_mem b hc)) (m / 2)
    rw [maskG.eq_2, maskK_cons]
    by_cases h : m % 2 = 1
    · rw [if_pos h, if_pos h, kG_mul, mcode_gD (hu b List.mem_cons_self), ih]
    · rw [if_neg h, if_neg h, one_mul, ih]

theorem rep_maskProd : ∀ {cs : List ℕ} {Ts : List Table},
    List.Forall₂ (Rep 31) Ts (cs.map fun c => glPerm (gD c)) → ∀ m,
      Rep 31 (maskProd 31 Ts m) (glPerm (maskG cs m))
  | [], [], _, m => by
    rw [maskG.eq_1, map_one]
    exact Rep.idT hn31
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: bs, T :: Ts, h, m => by
    rw [List.map_cons, List.forall₂_cons] at h
    rw [maskG.eq_2, map_mul]
    unfold maskProd
    refine Rep.compT ?_ (rep_maskProd h.2 (m / 2))
    by_cases hm : m % 2 = 1
    · rw [if_pos hm, if_pos hm]
      exact h.1
    · rw [if_neg hm, if_neg hm, map_one]
      exact Rep.idT hn31

theorem length_of_f2 {cs : List ℕ} {Ts : List Table}
    (h : List.Forall₂ (Rep 31) Ts (cs.map fun c => glPerm (gD c))) : Ts.length = cs.length := by
  rw [h.length_eq, List.length_map]

theorem all_of_f2 {p : Table → Bool} {φ : ℕ → Equiv.Perm (Fin 31)} :
    ∀ {Ts : List Table} {bs : List ℕ}, List.Forall₂ (Rep 31) Ts (bs.map φ) →
      (∀ T b, b ∈ bs → Rep 31 T (φ b) → p T = true) → Ts.all p = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | T :: Ts, b :: bs, h, hp => by
    rw [List.map_cons, List.forall₂_cons] at h
    rw [List.all_cons, Bool.and_eq_true]
    exact ⟨hp T b List.mem_cons_self h.1,
      all_of_f2 h.2 fun T' b' hb' hr => hp T' b' (List.mem_cons_of_mem b hb') hr⟩

theorem gD_comm {b c : ℕ} (hb : unitK b = true) (hc : unitK c = true)
    (h : mmulK b c = mmulK c b) : gD b * gD c = gD c * gD b := by
  apply kG_inj
  change mcode ((gD b * gD c : G) : Mat) = mcode ((gD c * gD b : G) : Mat)
  rw [kG_mul, kG_mul, mcode_gD hb, mcode_gD hc, h]

theorem gD_sq {b : ℕ} (hb : unitK b = true) (h : mmulK b b = idK) : gD b * gD b = 1 := by
  apply kG_inj
  change mcode ((gD b * gD b : G) : Mat) = mcode ((1 : G) : Mat)
  rw [kG_mul, mcode_gD hb, h, kG_one]

theorem eq_gD_of_code {g : G} {b : ℕ} (hb : unitK b = true) (h : mcode (g : Mat) = b) :
    g = gD b := by
  apply kG_inj
  change mcode (g : Mat) = mcode ((gD b : G) : Mat)
  rw [mcode_gD hb, h]

theorem tabsOK_of {Ts : List Table} {cs : List ℕ}
    (h : List.Forall₂ (Rep 31) Ts (cs.map fun c => glPerm (gD c))) : tabsOK 31 Ts = true := by
  unfold tabsOK
  refine all_of_f2 h fun T b _ hT => ?_
  have hR := rep_invT_of_rep hn31 hT
  unfold tabOK
  refine allIn_eq_true.mpr fun i _ hi => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hT i hi]
  refine ⟨idx_lt _ hi, ?_⟩
  rw [hR _ (idx_lt _ hi), idx_inv_idx]

theorem ebasisOK_of {cs : List ℕ} {Ts : List Table}
    (hT : List.Forall₂ (Rep 31) Ts (cs.map fun c => glPerm (gD c)))
    (hu : ∀ c ∈ cs, unitK c = true) (h : ebasK cs = true) : ebasisOK 31 Ts = true := by
  obtain ⟨h1, h2⟩ := and2 h
  obtain ⟨h2, h3⟩ := and2 h2
  have hnz := (recAnd_iff (fun m => CFSG.KC.Ord.orB (Nat.beq m 0) (CFSG.KC.Ord.notB (Nat.beq (maskK cs m) idK)))
    (Nat.pow 2 cs.length)).mp h3
  unfold ebasisOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨all_of_f2 hT fun T b hb hr => ?_, all_of_f2 hT fun T b hb hr => ?_⟩, ?_⟩
  · refine (tblEq_iff_eq (Rep.compT hr hr) (Rep.idT hn31)).mpr ?_
    rw [← map_mul, gD_sq (hu b hb) (Nat.eq_of_beq_eq_true ((allK_iff _ _).mp h1 b hb)), map_one]
  · refine all_of_f2 hT fun T' c hc hr' => ?_
    change tblEq 31 (compT 31 T T') (compT 31 T' T) = true
    refine (tblEq_iff_eq (Rep.compT hr hr') (Rep.compT hr' hr)).mpr ?_
    rw [← map_mul, ← map_mul, gD_comm (hu b hb) (hu c hc)
      ((commK_iff b c).mp ((allK_iff _ _).mp ((allK_iff _ _).mp h2 b hb) c hc))]
  · rw [List.all_eq_true]
    intro m hm
    rw [List.mem_range, length_of_f2 hT] at hm
    rw [Bool.or_eq_true, beq_iff_eq]
    rcases orB_true.mp (hnz m hm) with h0 | h0
    · exact Or.inl (Nat.eq_of_beq_eq_true h0)
    · refine Or.inr ?_
      rw [Bool.not_eq_true']
      rw [Bool.eq_false_iff]
      intro he
      have e := (tblEq_iff_eq (rep_maskProd hT m) (Rep.idT hn31)).mp he
      rw [← map_one glPerm] at e
      have e' : mcode ((maskG cs m : G) : Mat) = mcode ((1 : G) : Mat) :=
        congrArg (fun g : G => mcode (g : Mat)) (glPerm_injective e)
      rw [mcode_maskG hu, kG_one] at e'
      rw [notB_true, e', Nat.beq_refl] at h0
      exact Bool.false_ne_true h0.symm

theorem inSp_of_memK {u : ℕ} {U : Table} {ws : List ℕ} {Ws : List Table}
    (hU : Rep 31 U (glPerm (gD u))) (hu : unitK u = true)
    (hW : List.Forall₂ (Rep 31) Ws (ws.map fun c => glPerm (gD c)))
    (hwu : ∀ c ∈ ws, unitK c = true) (h : memK u (spanK ws) = true) :
    inSp 31 (spanTabs 31 Ws) U = true :=
  inSp_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one kG_mul kG_inj gD hn31 glPerm
    (fun c hc => mcode_gD (hwu c hc)) hW (x := gD u)
    (by rw [mcode_gD hu]; exact (memK_iff _ _).mp h) hU

theorem subOK_of {us ws : List ℕ} {Us Ws : List Table}
    (hU : List.Forall₂ (Rep 31) Us (us.map fun c => glPerm (gD c))) (huu : ∀ c ∈ us, unitK c = true)
    (hW : List.Forall₂ (Rep 31) Ws (ws.map fun c => glPerm (gD c))) (hwu : ∀ c ∈ ws, unitK c = true)
    (h : subKOK us ws = true) : subOK 31 Us Ws = true := by
  obtain ⟨h1, h2⟩ := and2 h
  obtain ⟨h2, h3⟩ := and2 h2
  obtain ⟨h3, h4⟩ := and2 h3
  simp only [subOK, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨tabsOK_of hU, ebasisOK_of hU huu h1⟩, tabsOK_of hW⟩, ebasisOK_of hW hwu h2⟩, ?_⟩, ?_⟩
  · exact all_of_f2 hU fun T b hb hr =>
      inSp_of_memK hr (huu b hb) hW hwu ((allK_iff _ _).mp h3 b hb)
  · refine all_of_f2 hW fun T b hb hr => ?_
    unfold commAllT
    refine all_of_f2 hU fun T' c hc hr' => ?_
    refine (CFSG.SectionRank.QTK.Insp443.PermKit.commT2_iff hr hr').mpr ?_
    rw [← map_mul, ← map_mul, gD_comm (hwu b hb) (huu c hc)
      ((commK_iff b c).mp ((allK_iff _ _).mp ((allK_iff _ _).mp h4 b hb) c hc))]

theorem hits_facts {L : List ℕ} : ∀ {ws rs : List ℕ}, hitsK L ws rs = true →
    ∀ b ∈ ws, ∃ r < 2 ^ L.length, maskK L r = b
  | [], _, _ => by simp
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | b :: ws, r :: rs, h => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt r (Nat.pow 2 (List.length L))) (Nat.beq (maskK L r) b))
      (hitsK L ws rs) = true at h
    obtain ⟨hab, h2⟩ := and2 h
    obtain ⟨hA, hB⟩ := and2 hab
    have hr : r < 2 ^ L.length := by
      rw [Nat.blt_eq] at hA
      exact hA
    have hb : maskK L r = b := Nat.eq_of_beq_eq_true hB
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · exact ⟨r, hr, hb.trans hc.symm⟩
    · exact hits_facts h2 c hc

theorem f2_orb {x y : G} {X XI Wt : Table} (hX : Rep 31 X (glPerm x))
    (hXI : Rep 31 XI (glPerm x⁻¹)) (hW : Rep 31 Wt (glPerm y)) :
    ∀ L : List ℕ, List.Forall₂ (Rep 31)
      (L.map fun j => conjTab 31 (powT 31 j X) (powT 31 j XI) Wt)
      ((List.zipWith (fun p q => mmulK (mmulK p (mcode (y : Mat))) q)
        (L.map fun j => mcode ((x ^ j : G) : Mat)) (L.map fun j => mcode ((x⁻¹ ^ j : G) : Mat))).map
          fun c => glPerm (gD c)) ∧
      ∀ c ∈ List.zipWith (fun p q => mmulK (mmulK p (mcode (y : Mat))) q)
        (L.map fun j => mcode ((x ^ j : G) : Mat)) (L.map fun j => mcode ((x⁻¹ ^ j : G) : Mat)),
          unitK c = true
  | [] => by simp
  | j :: L => by
    obtain ⟨ih1, ih2⟩ := f2_orb hX hXI hW L
    rw [List.map_cons, List.map_cons, List.map_cons, List.zipWith_cons_cons, List.map_cons,
      List.forall₂_cons, code3, gD_mcode]
    refine ⟨⟨?_, ih1⟩, fun c hc => ?_⟩
    · unfold conjTab
      rw [map_mul, map_mul, map_pow, map_pow]
      exact Rep.compT (Rep.compT (Rep.powT hn31 hX j) hW) (Rep.powT hn31 hXI j)
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact unitK_mcode _
      · exact ih2 c hc

theorem list_eq_map_range {L : List ℕ} {f : ℕ → ℕ} (hl : L.length = 7)
    (h : ∀ j < 7, L.getD j 0 = f j) : L = (List.range 7).map f := by
  apply List.ext_getElem (by rw [hl, List.length_map, List.length_range])
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, ← h j (by omega), List.getD_eq_getElem _ _ h1]

theorem irrOK_of {us ws ps qs : List ℕ} {R : List (List ℕ)} {Us Ws : List Table}
    (hU : List.Forall₂ (Rep 31) Us (us.map fun c => glPerm (gD c))) (huu : ∀ c ∈ us, unitK c = true)
    (hW : List.Forall₂ (Rep 31) Ws (ws.map fun c => glPerm (gD c))) (hwu : ∀ c ∈ ws, unitK c = true)
    {x : G} {X XI : Table} (hX : Rep 31 X (glPerm x)) (hXI : Rep 31 XI (glPerm x⁻¹))
    (hpl : ps.length = 7) (hql : qs.length = 7) (hps : ∀ j < 7, ps.getD j 0 = mcode ((x ^ j : G) : Mat))
    (hqs : ∀ j < 7, qs.getD j 0 = mcode ((x⁻¹ ^ j : G) : Mat))
    (h : irrK ps qs us ws R = true) : irrOK 31 7 X XI Us Ws = true := by
  have hm := (recAnd_iff (fun m => letB (maskK ws m) fun c => CFSG.KC.Ord.orB (memK c (spanK us))
      (hitsK (List.append us (orbK ps qs c)) ws (nthL R m))) (Nat.pow 2 ws.length)).mp h
  rw [list_eq_map_range hpl hps, list_eq_map_range hql hqs] at hm
  simp only [irrOK]
  rw [List.all_eq_true]
  intro w hw
  unfold spanTabs at hw
  obtain ⟨m, hmr, rfl⟩ := List.mem_map.mp hw
  rw [List.mem_range, length_of_f2 hW] at hmr
  have hcm := hm m hmr
  simp only [letB_l52] at hcm
  have hrw := rep_maskProd hW m
  rw [Bool.or_eq_true]
  rcases orB_true.mp hcm with h1 | h1
  · refine Or.inl ?_
    exact inSp_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one kG_mul kG_inj gD hn31 glPerm
      (fun c hc => mcode_gD (huu c hc)) hU (x := maskG ws m)
      (by rw [mcode_maskG hwu]; exact (memK_iff _ _).mp h1) hrw
  · refine Or.inr ?_
    rw [← mcode_maskG hwu m] at h1
    obtain ⟨ho1, ho2⟩ := f2_orb hX hXI hrw (List.range 7)
    have hL : List.Forall₂ (Rep 31) (Us ++ orbTabs 31 7 X XI (maskProd 31 Ws m))
        ((List.append us (orbK ((List.range 7).map fun j => mcode ((x ^ j : G) : Mat))
          ((List.range 7).map fun j => mcode ((x⁻¹ ^ j : G) : Mat))
            (mcode ((maskG ws m : G) : Mat)))).map fun c => glPerm (gD c)) := by
      rw [List.append_eq, List.map_append]
      exact List.rel_append hU ho1
    have hLu : ∀ c ∈ List.append us (orbK ((List.range 7).map fun j => mcode ((x ^ j : G) : Mat))
        ((List.range 7).map fun j => mcode ((x⁻¹ ^ j : G) : Mat))
          (mcode ((maskG ws m : G) : Mat))), unitK c = true := by
      intro c hc
      rw [List.append_eq, List.mem_append] at hc
      rcases hc with hc | hc
      · exact huu c hc
      · exact ho2 c hc
    have hfacts := hits_facts h1
    refine all_of_f2 hW fun T b hb hr => ?_
    obtain ⟨r, hr1, hr2⟩ := hfacts b hb
    unfold inSp spanTabs
    rw [List.any_eq_true]
    refine ⟨maskProd 31 _ r, List.mem_map.mpr ⟨r, List.mem_range.mpr ?_, rfl⟩, ?_⟩
    · rw [length_of_f2 hL]
      exact hr1
    · refine (tblEq_iff_eq (rep_maskProd hL r) hr).mpr ?_
      rw [eq_gD_of_code (hwu b hb) ((mcode_maskG hLu r).trans hr2)]

end CFSG.KC.L52I

end
