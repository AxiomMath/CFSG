module

public import CFSG.Certificates.Kernel.Q47KSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.HeSylKSound
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.Q47KOSound
import CFSG.Certificates.Kernel.Q47KRunSound
import CFSG.Certificates.Kernel.Q47KGlue
import CFSG.Certificates.Kernel.FusYKSound

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Q47
open CFSG.KLie.CT (anyN andB orB notB)

variable {n w : Nat}

theorem ord3_eq {t : Nat} (ht : PP 64 7 t) :
    (eqA 64 (powN 64 (unpack 64 7 t) 3) (idA 64) && !(eqA 64 (unpack 64 7 t) (idA 64))) = ord3 t := by
  rw [HeAutK.powN_PP ht 3, eqA_id_PP (HeAutK.pw_PP ht 3), eqA_id_PP ht]
  unfold ord3
  rw [andB_eq, notB_eq]

theorem runK_facts {gs : List (Array Nat)} {G : Nat → Nat} {fuel m : Nat} (b : Bound 64 7 gs G)
    (hl : (runK 64 7 gs.length G fuel).length = m) (hm : m ≤ fuel) (hf : fuel ≤ 4000) :
    (∀ y ∈ runK 64 7 gs.length G fuel, PP 64 7 y) ∧
      eltsN 64 gs = (runK 64 7 gs.length G fuel).map (unpack 64 7) ∧ enumCheckN 64 gs m = true := by
  obtain ⟨h1, h2, h3⟩ := runK_sound hsz64 rfl (fun k hk => b k hk) (by rw [hl]; exact hm) hf
  rw [hl] at h3
  exact ⟨h1, h2, h3⟩

theorem cls_sound {trans : List (List (Array Nat))} {OP : List Nat}
    (hO : oAllG trans = OP.map (unpack 64 7)) (hOP : ∀ t ∈ OP, PP 64 7 t)
    {D Eb K1 K2 : List (Array Nat)} {GD GE G1 G2 : Nat → Nat}
    (bD : Bound 64 7 D GD) (bE : Bound 64 7 Eb GE) (b1 : Bound 64 7 K1 G1) (b2 : Bound 64 7 K2 G2)
    (hE : (runK 64 7 Eb.length GE 100).length = 4) (h1 : (runK 64 7 K1.length G1 100).length = 24)
    (h2 : (runK 64 7 K2.length G2 100).length = 24)
    (hD1 : ∀ k < D.length, memK (runK 64 7 K1.length G1 100) (GD k) = true)
    (hD2 : ∀ k < D.length, memK (runK 64 7 K2.length G2 100) (GD k) = true)
    (hc : ∀ t ∈ OP, ord3 t = true → clsAt Eb.length GE (runK 64 7 Eb.length GE 100)
      (runK 64 7 K1.length G1 100) (runK 64 7 K2.length G2 100) D.length GD t = true) :
    classCheckG trans D Eb K1 K2 = true := by
  obtain ⟨pE, eE, cE⟩ := runK_facts bE hE (by decide) (by decide)
  obtain ⟨p1, e1, c1⟩ := runK_facts b1 h1 (by decide) (by decide)
  obtain ⟨p2, e2, c2⟩ := runK_facts b2 h2 (by decide) (by decide)
  have pD : ∀ k < D.length, PP 64 7 (GD k) := fun k hk => PP_bound hsz64 bD hk
  have pG : ∀ k < Eb.length, PP 64 7 (GE k) := fun k hk => PP_bound hsz64 bE hk
  unfold classCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨cE, c1⟩, c2⟩, ?_⟩, ?_⟩, ?_⟩
  · refine all_bound bD fun k hk => ?_
    rw [e1, FusYK.inLN_memK (pD k hk) p1]
    exact hD1 k hk
  · refine all_bound bD fun k hk => ?_
    rw [e2, FusYK.inLN_memK (pD k hk) p2]
    exact hD2 k hk
  · unfold oOrd3G
    rw [hO, List.filter_map, List.all_map, List.all_eq_true]
    intro t ht
    obtain ⟨htO, hf⟩ := List.mem_filter.1 ht
    have pt := hOP t htO
    simp only [Function.comp_apply] at hf
    rw [ord3_eq pt] at hf
    have h := hc t htO hf
    unfold clsAt at h
    simp only [Function.comp_apply]
    rw [e1, e2, FusYK.inLN_memK pt p1, FusYK.inLN_memK pt p2, eE]
    have eall : (Eb.all fun e => inLN 64 ((runK 64 7 Eb.length GE 100).map (unpack 64 7))
        (conjA 64 (unpack 64 7 t) e)) =
        allN Eb.length fun e => memK (runK 64 7 Eb.length GE 100) (conj 64 7 t (GE e)) := by
      rw [list_of_bound bE, List.all_map, List.length_map, List.length_range, allN_eq']
      refine HexaK.all_congr_mem fun k hk => ?_
      have pk := pG k (List.mem_range.1 hk)
      simp only [Function.comp_apply]
      rw [conjA_PP pt pk, FusYK.inLN_memK (pt.conjK pk) pE]
    rw [eall]
    simp only [orB_eq, notB_eq, Bool.or_eq_true] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · refine Or.inr ?_
      have hl := Nat.eq_of_beq_eq_true h
      have bt : Bound 64 7 [unpack 64 7 t] (fun _ => t) := fun k hk => by
        have : k = 0 := by simpa using hk
        subst this
        exact ⟨rfl, permOK_PP pt⟩
      obtain ⟨-, -, cW⟩ := runK_sound (gs := D ++ [unpack 64 7 t])
        (G := fun k => nIf(Nat.blt k D.length, GD k, t)) (fuel := 200) hsz64
        (by rw [List.length_append, List.length_singleton])
        (fun k hk => FusYK.bound_append bD bt k (by simpa using hk))
        (by rw [hl]; decide) (by decide)
      rwa [hl] at cW

theorem rep_sound {form : Array Nat} {Qg reps : List (Array Nat)} {z : Array Nat} {REP : Nat → Nat}
    {NQ PZ : Nat} {TQ : Nat → Nat} (hsz : szOK n w = true) (hl : reps.length = 64)
    (bR : Bound n w reps REP) (hz : z = unpack n w PZ) (pz : PP n w PZ)
    (hQ : eltsN n Qg = (List.range NQ).map fun i => unpack n w (TQ i)) (pQ : ∀ i < NQ, PP n w (TQ i))
    (h : repK n w REP NQ TQ PZ form = true) : repCheckG form n Qg reps z = true := by
  have pR : ∀ v < 64, PP n w (REP v) := fun v hv => PP_bound hsz bR (by omega)
  have gR : ∀ v < 64, reps[v]! = unpack n w (REP v) := fun v hv => (bR v (by omega)).1
  unfold repK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨r1, r2, r3, r4, r5⟩ := h
  subst hz
  unfold repCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨by rw [hl]; rfl, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [gR 0 (by decide), eqA_id_PP (pR 0 (by decide))]
    exact r1
  · rw [hQ, list_of_bound bR, hl, List.all_map, List.all_eq_true]
    intro v hv
    simp only [Function.comp_apply]
    rw [inLN_eq (pR v (List.mem_range.1 hv)) pQ]
    exact CFSG.KC.Pack.allN_spec r2 v (List.mem_range.1 hv)
  · rw [List.all_eq_true]
    intro u hu
    rw [List.all_eq_true]
    intro v hv
    have hu' := List.mem_range.1 hu
    have hv' := List.mem_range.1 hv
    have huv : u ^^^ v < 64 := Nat.xor_lt_two_pow (n := 6) hu' hv'
    have hr := CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec r3 u hu') v hv'
    rw [strictB_eq', orB_eq] at hr
    rw [gR u hu', gR v hv', gR _ huv, mulN_PP (pR u hu') (pR v hv'),
      eqA_PP ((pR u hu').mul (pR v hv')) (pR _ huv), mulN_PP (pR _ huv) pz,
      eqA_PP ((pR u hu').mul (pR v hv')) ((pR _ huv).mul pz)]
    exact hr
  · rw [hQ, List.all_map, List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    have pk := pQ k hk'
    have hr := CFSG.KC.Pack.allN_spec r4 k hk'
    rw [strictB_eq', anyN_eq] at hr
    simp only [Function.comp_apply]
    rw [← hr]
    refine HexaK.any_congr_mem fun v hv => ?_
    have hv' := List.mem_range.1 hv
    rw [gR v hv', eqA_PP pk (pR v hv'), mulN_PP (pR v hv') pz, eqA_PP pk ((pR v hv').mul pz), orB_eq]
    rfl
  · rw [List.all_eq_true]
    intro v hv
    have hv' := List.mem_range.1 hv
    have hr := CFSG.KC.Pack.allN_spec r5 v hv'
    rw [strictB_eq', orB_eq] at hr
    rw [gR v hv', mulN_PP (pR v hv') (pR v hv'), eqA_id_PP ((pR v hv').mul (pR v hv')),
      eqA_PP ((pR v hv').mul (pR v hv')) pz, beq_nat, beq_nat]
    exact hr

theorem imgs_sound {reps gs ds : List (Array Nat)} {z : Array Nat} {REP G Dm : Nat → Nat} {PZ : Nat}
    (bR : ∀ v < 64, reps[v]! = unpack n w (REP v) ∧ PP n w (REP v))
    (hz : z = unpack n w PZ) (pz : PP n w PZ)
    (hg : ∀ k < gs.length, gs[k]! = unpack n w (G k) ∧ PP n w (G k)) (bD : Bound 64 7 ds Dm)
    (hlen : gs.length = ds.length) (h : imgK n w REP PZ gs.length G Dm = true) :
    imgsOK n reps z gs ds = true := by
  subst hz
  unfold imgsOK
  rw [Bool.and_eq_true, hlen]
  refine ⟨beq_self_eq_true _, ?_⟩
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  have hkg : k < gs.length := by omega
  have pd : PP 64 7 (Dm k) := PP_bound hsz64 bD hk'
  have hi := CFSG.KC.Pack.allN_spec h k hkg
  unfold imgOK
  rw [Bool.and_eq_true, (bD k hk').1, (hg k hkg).1]
  refine ⟨validA_unpack (bD k hk').2, ?_⟩
  rw [allN_eq'] at hi
  rw [← hi]
  refine HexaK.all_congr_mem fun v hv => ?_
  have hv' := List.mem_range.1 hv
  have pgk := (hg k hkg).2
  have hdv := pd.2.1 v hv'
  rw [strictB_eq', strictB_eq', unpack_get64 hv', (bR _ hdv).1, (bR v hv').1,
    conjA_PP pgk (bR v hv').2, eqA_PP (pgk.conjK (bR v hv').2) (bR _ hdv).2,
    mulN_PP (bR _ hdv).2 pz, eqA_PP (pgk.conjK (bR v hv').2) ((bR _ hdv).2.mul pz), orB_eq]
  rfl

theorem pin_get {gs : List (Array Nat)} {g : Nat} {G : Nat → Nat} {N : Nat} {T E S : Nat → Nat}
    (p : Pin n w gs g G N T E S) : ∀ k < gs.length, gs[k]! = unpack n w (G k) ∧ PP n w (G k) := by
  intro k hk
  have hl := len_pin p
  exact ⟨(bnd_pin p k hk).1, PP_gen p.ok p.perm k (hl ▸ hk)⟩

theorem model_sound {d : QD} {m : MD} {k : ModelK} {GY : Nat → Nat} {OP : List Nat}
    (h : ModelOK d n w m k GY) (hdir : modelDirectG d m = true) (bY : Bound 64 7 d.yg GY)
    (hyl : d.yg.length = 2) (hAddC : ∀ c < 4, addK (k.CP c) = true)
    (hO : oAllG d.trans = OP.map (unpack 64 7)) (hOP : ∀ t ∈ OP, PP 64 7 t)
    (hcls : ∀ t ∈ OP, ord3 t = true →
      clsC (clsOf m k false) t = true ∧ clsC (clsOf m k true) t = true) :
    modelCheckG d n m = true := by
  have hsz : szOK n w = true := by
    have hk := h.pX.ok
    unfold bfsK at hk
    simp only [bAnd_iff] at hk
    exact hk.1
  unfold modelDirectG at hdir
  simp only [Bool.and_eq_true, beq_iff_eq] at hdir
  obtain ⟨⟨⟨⟨⟨⟨⟨hrl, hke⟩, hkf⟩, hcl⟩, hcf⟩, hnd⟩, heb⟩, hfb⟩ := hdir
  have hr := h.runs
  unfold runsB at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩ := hr
  have hm := h.model
  unfold modelB modelYK at hm
  simp only [andB_eq, Bool.and_eq_true] at hm
  obtain ⟨y1, y2, y3, y4, y5⟩ := hm
  have hi := h.img
  simp only [Bool.and_eq_true] at hi
  obtain ⟨⟨i1, i2⟩, i3⟩ := hi
  have pz : PP n w k.PZ := PP_of_permOK hsz h.z.2
  have bRp : ∀ v < 64, m.reps[v]! = unpack n w (k.REP v) ∧ PP n w (k.REP v) := fun v hv =>
    ⟨(h.reps v (by omega)).1, PP_bound hsz h.reps (by omega)⟩
  have eX := eltsN_eq h.pX.size h.pX.bind h.pX.ok h.pX.fuel
  have eQ := eltsN_eq h.pQ.size h.pQ.bind h.pQ.ok h.pQ.fuel
  have eE := eltsN_eq h.pE.size h.pE.bind h.pE.ok h.pE.fuel
  have eF := eltsN_eq h.pF.size h.pF.bind h.pF.ok h.pF.fuel
  have sX := PP_pts h.pX.ok h.pX.perm
  have sQ := PP_pts h.pQ.ok h.pQ.perm
  have sE := PP_pts h.pE.ok h.pE.perm
  have sF := PP_pts h.pF.ok h.pF.perm
  have gNE := PP_gen h.pNE.ok h.pNE.perm
  have gE := PP_gen h.pE.ok h.pE.perm
  have gF := PP_gen h.pF.ok h.pF.perm
  have pY : ∀ y < 2, PP 64 7 (GY y) := fun y hy => PP_bound hsz64 bY (by omega)
  have hd : (default : List (Array ℕ)) = [] := rfl
  have kl : ∀ i < 2, kListG m i = m.ke.getD i [] ∧ kListG m (2 + i) = m.kf.getD i [] := by
    intro i hi
    unfold kListG
    rw [decide_eq_true hi, decide_eq_false (by omega : ¬ 2 + i < 2), Nat.add_sub_cancel_left]
    exact ⟨rfl, rfl⟩
  have bK : ∀ i < 2, Bound 64 7 (m.ke.getD i []) (k.GK i) ∧ Bound 64 7 (m.kf.getD i []) (k.GK (2 + i)) := by
    intro i hi
    have a := h.ks i (by omega)
    have b := h.ks (2 + i) (by omega)
    rw [(kl i hi).1] at a
    rw [(kl i hi).2] at b
    exact ⟨a, b⟩
  have rK : ∀ i < 2, (runK 64 7 (m.ke.getD i []).length (k.GK i) 100).length = 24 ∧
      (runK 64 7 (m.kf.getD i []).length (k.GK (2 + i)) 100).length = 24 := by
    intro i hi
    have a := CFSG.KC.Pack.allN_spec r4 i (by omega)
    have b := CFSG.KC.Pack.allN_spec r4 (2 + i) (by omega)
    unfold kPts at a b
    rw [(kl i hi).1] at a
    rw [(kl i hi).2] at b
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩
  have yK : ∀ i < 2, (∀ j < m.d.length, memK (runK 64 7 (m.ke.getD i []).length (k.GK i) 100) (k.GD j) = true) ∧
      (∀ j < m.d.length, memK (runK 64 7 (m.kf.getD i []).length (k.GK (2 + i)) 100) (k.GD j) = true) := by
    intro i hi
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have a := CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec y4 i (by omega)) j hj
      unfold kPts at a
      rwa [(kl i hi).1] at a
    · have b := CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec y4 (2 + i) (by omega)) j hj
      unfold kPts at b
      rwa [(kl i hi).2] at b
  have k0 : m.ke[0]! = m.ke.getD 0 [] := by rw [FusYK.getElem!_getD, hd]
  have k1 : m.ke[1]! = m.ke.getD 1 [] := by rw [FusYK.getElem!_getD, hd]
  have k2 : m.kf[0]! = m.kf.getD 0 [] := by rw [FusYK.getElem!_getD, hd]
  have k3 : m.kf[1]! = m.kf.getD 1 [] := by rw [FusYK.getElem!_getD, hd]
  unfold modelCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, by rw [hke]; rfl⟩, by rw [hkf]; rfl⟩,
    ?_⟩, ?_⟩, by rw [hcl]; rfl⟩, ?_⟩, ?_⟩
  · exact rep_sound hsz hrl h.reps h.z.1 pz eQ sQ h.rep
  · have := enumCheckN_of h.pNE.size h.pNE.bind h.pNE.perm h.pNE.ok h.pNE.fuel
    rwa [h.sNE] at this
  · refine all_bound (bnd_pin h.pNE) fun j hj => ?_
    rw [eX, inLN_eq (gNE j hj) sX]
    exact CFSG.KC.Pack.allN_spec y1 j hj
  · refine all_bound (bnd_pin h.pNE) fun j hj => all_bound (bnd_pin h.pE) fun q hq => ?_
    rw [eE, conjA_PP (gNE j hj) (gE q hq), inLN_eq ((gNE j hj).conjK (gE q hq)) sE]
    exact CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec y2 j hj) q hq
  · refine all_bound (bnd_pin h.pNE) fun j hj => all_bound (bnd_pin h.pF) fun q hq => ?_
    rw [eF, conjA_PP (gNE j hj) (gF q hq), inLN_eq ((gNE j hj).conjK (gF q hq)) sF]
    exact CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec y3 j hj) q hq
  · exact imgs_sound bRp h.z.1 pz (pin_get h.pNE) h.dB hnd i1
  · exact imgs_sound bRp h.z.1 pz (pin_get h.pE) h.eb heb i2
  · exact imgs_sound bRp h.z.1 pz (pin_get h.pF) h.fb hfb i3
  · exact (runK_facts h.dB (Nat.eq_of_beq_eq_true r1) (by decide) (by decide)).2.2
  · rw [k0, k1]
    refine cls_sound hO hOP h.dB h.eb (bK 0 (by decide)).1 (bK 1 (by decide)).1
      (Nat.eq_of_beq_eq_true r2) (rK 0 (by decide)).1 (rK 1 (by decide)).1 (yK 0 (by decide)).1
      (yK 1 (by decide)).1 fun t ht h3 => ?_
    have e := (hcls t ht h3).1
    unfold clsC clsOf at e
    dsimp only at e
    exact e
  · rw [k2, k3]
    refine cls_sound hO hOP h.dB h.fb (bK 0 (by decide)).2 (bK 1 (by decide)).2
      (Nat.eq_of_beq_eq_true r3) (rK 0 (by decide)).2 (rK 1 (by decide)).2 (yK 0 (by decide)).2
      (yK 1 (by decide)).2 fun t ht h3 => ?_
    have e := (hcls t ht h3).2
    unfold clsC clsOf at e
    dsimp only at e
    exact e
  · refine isom_all h.c (fun c hc => hAddC c (by omega)) fun c hc => ?_
    rw [List.all_eq_true] at hcf
    have := hcf _ (List.getElem_mem hc)
    rwa [← getElem!_pos m.c c hc, (h.c c hc).1] at this
  · refine List.all_eq_true.2 fun i hi => List.all_eq_true.2 fun j hj => ?_
    have hi2 := List.mem_range.1 hi
    have hj2 := List.mem_range.1 hj
    have hc := CFSG.KC.Pack.allN_spec r5 (2 * i + j) (by omega)
    have e1 : (2 * i + j) / 2 = i := by omega
    have e2 : (2 * i + j) % 2 = j := by omega
    have bA := (bK i hi2).1
    have bB := (bK j hj2).2
    have hkef : kefPts m k (2 * i + j) = runK 64 7 ((m.ke.getD i []).length + (m.kf.getD j []).length)
        (fun t => nIf(Nat.blt t (m.ke.getD i []).length, k.GK i t,
          k.GK (2 + j) (t - (m.ke.getD i []).length))) 200 := by
      unfold kefPts kefG
      rw [e1, e2]
    have hl2 : (kefPts m k (2 * i + j)).length = 168 := Nat.eq_of_beq_eq_true hc
    obtain ⟨pK, eK, cK⟩ := runK_sound (gs := m.ke.getD i [] ++ m.kf.getD j [])
      (G := fun t => nIf(Nat.blt t (m.ke.getD i []).length, k.GK i t,
        k.GK (2 + j) (t - (m.ke.getD i []).length))) (fuel := 200) hsz64
      (List.length_append ..)
      (fun t ht => FusYK.bound_append bA bB t (by rw [List.length_append]; exact ht))
      (by rw [← hkef, hl2]; decide) (by decide)
    rw [← hkef] at pK eK cK
    rw [hl2] at cK
    rw [FusYK.getElem!_getD m.ke, FusYK.getElem!_getD m.kf, hd, Bool.and_eq_true]
    refine ⟨cK, all_bound bY fun y hy => ?_⟩
    have pc : PP 64 7 (k.CP (2 * i + j)) := PP_bound hsz64 h.c (by omega)
    rw [eK, (h.c (2 * i + j) (by omega)).1, conjA_PP pc (pY y (by omega)),
      FusYK.inLN_memK (pc.conjK (pY y (by omega))) pK]
    exact CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec y5 (2 * i + j) (by omega)) y (by omega)

end CFSG.KC.Q47K

end
