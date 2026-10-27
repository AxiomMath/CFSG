module

public import CFSG.Certificates.Kernel.KGC31PSound
public import CFSG.Certificates.Kernel.PermCent.ConjInv

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
open CFSG.KC.Child3 (tabP)
open CFSG.Certificates.Kernel.PkCV.ConjInv (all_congr_mem)

section Grp

variable {G : Type} [Group G] [DecidableEq G]

@[expose] def gmask : List G → Nat → G
  | [], _ => 1
  | b :: bs, m => (if m % 2 = 1 then b else 1) * gmask bs (m / 2)

@[expose] def gspan (bs : List G) : List G := (List.range (2 ^ bs.length)).map (gmask bs)

@[expose] def gorb (m : Nat) (g t : G) : List G :=
  (List.range m).map fun j => g ^ j * t * (g ^ j)⁻¹

@[expose] def gorbIs (orb bs : List G) : Bool :=
  (orb.all fun o => decide (o ∈ gspan bs)) && bs.all fun b => decide (b ∈ gspan orb)

@[expose] def gbad (m : Nat) (g t : G) : Bool :=
  !(decide (g * t * g⁻¹ = t)) && (gorb m g t).all fun c => decide (t * c = c * t)

theorem mem_gspan (bs : List G) (s : G) :
    s ∈ gspan bs ↔ ∃ S : List G, S.Sublist bs ∧ S.prod = s := by
  induction bs generalizing s with
  | nil =>
    simp only [gspan, List.length_nil, pow_zero, List.mem_map, List.mem_range, List.sublist_nil]
    constructor
    · rintro ⟨m, -, rfl⟩
      exact ⟨[], rfl, by simp [gmask]⟩
    · rintro ⟨S, rfl, rfl⟩
      exact ⟨0, by omega, by simp [gmask]⟩
  | cons b bs ih =>
    simp only [gspan, List.mem_map, List.mem_range, List.length_cons, pow_succ] at ih ⊢
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨S, hS, e⟩ := (ih (gmask bs (m / 2))).1 ⟨m / 2, by omega, rfl⟩
      rw [gmask]
      split
      · exact ⟨b :: S, hS.cons₂ b, by rw [List.prod_cons, e]⟩
      · exact ⟨S, hS.cons b, by rw [one_mul, e]⟩
    · rintro ⟨S, hS, rfl⟩
      rcases List.sublist_cons_iff.1 hS with hS | ⟨r, rfl, hr⟩
      · obtain ⟨m, hm, e⟩ := (ih S.prod).2 ⟨S, hS, rfl⟩
        have h2 : 2 * m / 2 = m := by omega
        refine ⟨2 * m, by omega, ?_⟩
        rw [gmask, if_neg (by omega), one_mul, h2, e]
      · obtain ⟨m, hm, e⟩ := (ih r.prod).2 ⟨r, hr, rfl⟩
        have h2 : (2 * m + 1) / 2 = m := by omega
        refine ⟨2 * m + 1, by omega, ?_⟩
        rw [gmask, if_pos (by omega), h2, e, List.prod_cons]

theorem pairwise_commute {S : List G} (h : ∀ a ∈ S, ∀ b ∈ S, Commute a b) :
    S.Pairwise Commute := by
  induction S with
  | nil => exact List.Pairwise.nil
  | cons x S ih =>
    exact List.Pairwise.cons (fun b hb => h x List.mem_cons_self b (List.mem_cons_of_mem _ hb))
      (ih fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

theorem mem_gspan_perm {L L' : List G} (hp : L.Perm L') (hc : ∀ a ∈ L, ∀ b ∈ L, Commute a b)
    {s : G} : s ∈ gspan L → s ∈ gspan L' := by
  rw [mem_gspan, mem_gspan]
  rintro ⟨S, hS, rfl⟩
  obtain ⟨S', hS', hsub⟩ := hp.subperm_left.1 hS.subperm
  refine ⟨S', hsub, hS'.prod_eq' (pairwise_commute fun a ha b hb => ?_)⟩
  exact hc a (hp.mem_iff.2 (hsub.subset ha)) b (hp.mem_iff.2 (hsub.subset hb))

theorem gorbIs_perm {O O' : List G} (hp : O.Perm O') (hc : ∀ a ∈ O, ∀ b ∈ O, Commute a b)
    (B : List G) : gorbIs O' B = gorbIs O B := by
  have hc' : ∀ a ∈ O', ∀ b ∈ O', Commute a b := fun a ha b hb =>
    hc a (hp.mem_iff.2 ha) b (hp.mem_iff.2 hb)
  have e : ∀ s, s ∈ gspan O' ↔ s ∈ gspan O := fun s =>
    ⟨mem_gspan_perm hp.symm hc', mem_gspan_perm hp hc⟩
  rw [gorbIs, gorbIs, all_congr_mem (fun x => (hp.mem_iff (a := x)).symm)]
  simp only [e]

theorem range_mul_mod_perm {a p : Nat} (hp : 1 < p) (hc : Nat.Coprime a p) :
    ((List.range p).map fun j => a * j % p).Perm (List.range p) := by
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hp
  have h1 : ∀ x, b * (a * x % p) % p = x % p := fun x => by
    rw [Nat.mul_mod_mod, ← mul_assoc, Nat.mul_mod, mul_comm b a, hb, one_mul, Nat.mod_mod]
  have h2 : ∀ x, a * (b * x % p) % p = x % p := fun x => by
    rw [Nat.mul_mod_mod, ← mul_assoc, Nat.mul_mod, hb, one_mul, Nat.mod_mod]
  rw [List.perm_ext_iff_of_nodup ?_ List.nodup_range]
  · intro k
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, -, rfl⟩
      exact Nat.mod_lt _ (by omega)
    · intro hk
      exact ⟨b * k % p, Nat.mod_lt _ (by omega), by rw [h2, Nat.mod_eq_of_lt hk]⟩
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro i hi j hj e
    rw [List.mem_range] at hi hj
    have := h1 i
    rw [e, h1, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact this.symm

theorem pow_mod_eq {g : G} {p : Nat} (hg : g ^ p = 1) (k : Nat) : g ^ k = g ^ (k % p) := by
  conv_lhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hg, one_pow, mul_one]

theorem gorb_pow_perm {g t : G} {p a : Nat} (hg : g ^ p = 1) (hp : 1 < p)
    (hc : Nat.Coprime a p) : (gorb p (g ^ a) t).Perm (gorb p g t) := by
  have e : gorb p (g ^ a) t =
      ((List.range p).map fun j => a * j % p).map fun j => g ^ j * t * (g ^ j)⁻¹ := by
    rw [gorb, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp, ← pow_mul]
    rw [pow_mod_eq hg (a * j)]
  rw [e, gorb]
  exact (range_mul_mod_perm hp hc).map _

theorem conj_eq_iff_pow {g t : G} {p a : Nat} (hg : g ^ p = 1) (hp : 1 < p)
    (hc : Nat.Coprime a p) : g ^ a * t * (g ^ a)⁻¹ = t ↔ g * t * g⁻¹ = t := by
  have key : ∀ x : G, x * t * x⁻¹ = t ↔ Commute x t := fun x => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Iff.rfl
  rw [key, key]
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hp
  constructor
  · intro h
    have h' := h.pow_left b
    rwa [← pow_mul, pow_mod_eq hg, hb, pow_one] at h'
  · intro h
    exact h.pow_left a

theorem gbad_pow {g t : G} {p a : Nat} (hg : g ^ p = 1) (hp : 1 < p) (hc : Nat.Coprime a p) :
    gbad p (g ^ a) t = gbad p g t := by
  rw [gbad, gbad, all_congr_mem (fun x => (gorb_pow_perm (t := t) hg hp hc).mem_iff (a := x))]
  simp only [conj_eq_iff_pow hg hp hc]

theorem gorb_comm {g t : G} {p : Nat} (h : gbad p g t = true) :
    ∀ c ∈ gorb p g t, ∀ d ∈ gorb p g t, Commute c d := by
  rw [gbad, Bool.and_eq_true, List.all_eq_true] at h
  have hk : ∀ k < p, t * (g ^ k * t * (g ^ k)⁻¹) = g ^ k * t * (g ^ k)⁻¹ * t := fun k hk =>
    of_decide_eq_true (h.2 _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  have cc : ∀ i k, k < p →
      Commute (g ^ i * t * (g ^ i)⁻¹) (g ^ (i + k) * t * (g ^ (i + k))⁻¹) := by
    intro i k hkp
    have e : g ^ (i + k) * t * (g ^ (i + k))⁻¹ = g ^ i * (g ^ k * t * (g ^ k)⁻¹) * (g ^ i)⁻¹ := by
      simp only [pow_add, mul_inv_rev, mul_assoc]
    rw [e]
    have h0 : Commute t (g ^ k * t * (g ^ k)⁻¹) := hk k hkp
    have hm := h0.map (MulAut.conj (g ^ i))
    simpa only [MulAut.conj_apply] using hm
  intro c hc d hd
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hd
  rw [List.mem_range] at hi hj
  rcases le_total i j with hij | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact cc i k (by omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact (cc j k (by omega)).symm

theorem gone_pow {g t : G} {p a : Nat} (hg : g ^ p = 1) (hp : 1 < p) (hc : Nat.Coprime a p)
    (C : List (List G)) :
    (!(gbad p (g ^ a) t) || C.any (gorbIs (gorb p (g ^ a) t))) =
      (!(gbad p g t) || C.any (gorbIs (gorb p g t))) := by
  rw [gbad_pow hg hp hc]
  cases h : gbad p g t
  · rfl
  · simp only [Bool.not_true, Bool.false_or]
    exact any_congr' (f := gorbIs (gorb p (g ^ a) t)) (g := gorbIs (gorb p g t))
      fun B _ => gorbIs_perm (gorb_pow_perm hg hp hc).symm (gorb_comm h) B

theorem gbad_one (m : Nat) (t : G) : gbad m 1 t = false := by
  simp [gbad]

end Grp

variable {n w : Nat}

theorem sg_pc {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    sg n w (pc n w a b) = sg n w a * sg n w b := sg_pcomp ha hb

theorem sg_ppw {x : Nat} (hx : PP n w x) : ∀ e, sg n w (ppw n w x e) = sg n w x ^ e
  | 0 => by rw [ppw, sg_id hx.sz, pow_zero]
  | e + 1 => by rw [ppw, sg_pc hx (PP_ppw hx e), sg_ppw hx e, pow_succ']

theorem sg_pinv' {x : Nat} (hx : PP n w x) : sg n w (pinv n w x) = (sg n w x)⁻¹ := sg_pinv hx

theorem sg_pcj {x xi t : Nat} (hx : PP n w x) (hxi : PP n w xi) (ht : PP n w t) :
    sg n w (pcj n w x xi t) = sg n w x * sg n w t * sg n w xi := by
  rw [pcj, sg_pc (hx.pc ht) hxi, sg_pc hx ht]

theorem sg_pmask (hsz : szOK n w = true) :
    ∀ (bs : List Nat), (∀ b ∈ bs, PP n w b) →
      ∀ m, sg n w (pmask n w bs m) = gmask (bs.map (sg n w)) m
  | [], _, _ => by rw [pmask, sg_id hsz]; rfl
  | b :: bs, h, m => by
    have hbs : ∀ c ∈ bs, PP n w c := fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hb : PP n w b := h b List.mem_cons_self
    rw [pmask, List.map_cons, gmask]
    by_cases hm : m % 2 = 1
    · rw [if_pos hm, if_pos hm, sg_pc hb (PP_pmask hsz bs hbs _), sg_pmask hsz bs hbs]
    · rw [if_neg hm, if_neg hm, sg_pc (PP.id hsz) (PP_pmask hsz bs hbs _),
        sg_pmask hsz bs hbs, sg_id hsz]

theorem pspan_map (hsz : szOK n w = true) {bs : List Nat} (h : ∀ b ∈ bs, PP n w b) :
    (pspan n w bs).map (sg n w) = gspan (bs.map (sg n w)) := by
  rw [pspan, gspan, List.length_map, List.map_map]
  exact List.map_congr_left fun m _ => sg_pmask hsz bs h m

theorem any_beq {o : Nat} {L : List Nat} (ho : PP n w o) (hL : ∀ s ∈ L, PP n w s) :
    L.any (Nat.beq o) = decide (sg n w o ∈ L.map (sg n w)) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, List.mem_map]
  constructor
  · rintro ⟨s, hs, e⟩
    exact ⟨s, hs, ((PP_eq_iff ho (hL s hs)).1 (Nat.eq_of_beq_eq_true e)).symm⟩
  · rintro ⟨s, hs, e⟩
    exact ⟨s, hs, Nat.beq_eq.mpr ((PP_eq_iff ho (hL s hs)).2 e.symm)⟩

theorem porbIs_eq (hsz : szOK n w = true) {orb bs : List Nat} (ho : ∀ o ∈ orb, PP n w o)
    (hb : ∀ b ∈ bs, PP n w b) :
    porbIs n w orb bs = gorbIs (orb.map (sg n w)) (bs.map (sg n w)) := by
  rw [porbIs, gorbIs, List.all_map, List.all_map]
  congr 1
  · refine all_congr' fun o hoo => ?_
    rw [any_beq (ho o hoo) (PP_pspan hsz hb), pspan_map hsz hb]
    rfl
  · refine all_congr' fun b hbb => ?_
    rw [any_beq (hb b hbb) (PP_pspan hsz ho), pspan_map hsz ho]
    rfl

theorem porbTabs_map {m x t : Nat} (hx : PP n w x) (ht : PP n w t) :
    (porbTabs n w m x (pinv n w x) t).map (sg n w) = gorb m (sg n w x) (sg n w t) := by
  rw [porbTabs, gorb, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp]
  rw [sg_pcj (PP_ppw hx j) (PP_ppw hx.pinv j) ht, sg_ppw hx, sg_ppw hx.pinv, sg_pinv' hx, inv_pow]

theorem pbadAct_eq {m x t : Nat} (hx : PP n w x) (ht : PP n w t) :
    pbadAct n w m x (pinv n w x) t = gbad m (sg n w x) (sg n w t) := by
  have hxi := hx.pinv
  rw [pbadAct, gbad, beq_PP (PP_pcj hx hxi ht) ht, sg_pcj hx hxi ht, sg_pinv' hx, gorb,
    List.all_map]
  congr 1
  refine all_congr' fun j _ => ?_
  have hc := PP_pcj (PP_ppw hx j) (PP_ppw hxi j) ht
  rw [beq_PP (ht.pc hc) (hc.pc ht), sg_pc ht hc, sg_pc hc ht,
    sg_pcj (PP_ppw hx j) (PP_ppw hxi j) ht, sg_ppw hx, sg_ppw hxi, sg_pinv' hx, inv_pow]
  rfl

theorem porbOne_eq (hsz : szOK n w = true) {m x t : Nat} {cands : List (List Nat)}
    (hx : PP n w x) (ht : PP n w t) (hc : ∀ c ∈ cands, ∀ b ∈ c, PP n w b) :
    porbOne n w m x cands t = (!(gbad m (sg n w x) (sg n w t)) ||
      (cands.map (List.map (sg n w))).any (gorbIs (gorb m (sg n w x) (sg n w t)))) := by
  rw [porbOne, pbadAct_eq hx ht, List.any_map]
  congr 1
  refine any_congr' fun c hcc => ?_
  rw [porbIs_eq hsz (PP_porbTabs hx hx.pinv ht) (hc c hcc), porbTabs_map hx ht]
  rfl

theorem pactOne_eq {m x t : Nat} (hx : PP n w x) (ht : PP n w t) :
    pactOne n w m x t = !(gbad m (sg n w x) (sg n w t)) := by
  rw [pactOne, pbadAct_eq hx ht]

theorem sg_pow_of_pord {p x : Nat} (hx : PP n w x) (h : pord n w p x = true) :
    sg n w x ^ p = 1 := by
  rw [pord, Bool.and_eq_true] at h
  rw [← sg_ppw hx, Nat.eq_of_beq_eq_true h.1, sg_id hx.sz]

theorem porbOne_pow (hsz : szOK n w = true) {p a x t : Nat} {cands : List (List Nat)}
    (hx : PP n w x) (ht : PP n w t) (hc : ∀ c ∈ cands, ∀ b ∈ c, PP n w b)
    (hg : sg n w x ^ p = 1) (hp : 1 < p) (hco : Nat.Coprime a p) :
    porbOne n w p (ppw n w x a) cands t = porbOne n w p x cands t := by
  rw [porbOne_eq hsz (PP_ppw hx a) ht hc, porbOne_eq hsz hx ht hc, sg_ppw hx a]
  exact gone_pow hg hp hco _

theorem pactOne_pow {p a x t : Nat} (hx : PP n w x) (ht : PP n w t) (hg : sg n w x ^ p = 1)
    (hp : 1 < p) (hco : Nat.Coprime a p) : pactOne n w p (ppw n w x a) t = pactOne n w p x t := by
  rw [pactOne_eq (PP_ppw hx a) ht, pactOne_eq hx ht, sg_ppw hx a, gbad_pow hg hp hco]

theorem porbOne_zero (hsz : szOK n w = true) {m x t : Nat} {cands : List (List Nat)}
    (hx : PP n w x) (ht : PP n w t) (hc : ∀ c ∈ cands, ∀ b ∈ c, PP n w b) :
    porbOne n w m (ppw n w x 0) cands t = true := by
  rw [porbOne_eq hsz (PP_ppw hx 0) ht hc, sg_ppw hx 0, pow_zero, gbad_one]
  rfl

theorem pactOne_zero {m x t : Nat} (hx : PP n w x) (ht : PP n w t) :
    pactOne n w m (ppw n w x 0) t = true := by
  rw [pactOne_eq (PP_ppw hx 0) ht, sg_ppw hx 0, pow_zero, gbad_one]
  rfl

theorem range_all_eq {p : Nat} (hp : 1 < p) {f : Nat → Bool} {b : Bool} (h0 : f 0 = true)
    (h : ∀ a < p, 0 < a → f a = b) : (List.range p).all f = b := by
  rw [Bool.eq_iff_iff, List.all_eq_true]
  constructor
  · intro H
    rw [← h 1 hp (by omega)]
    exact H 1 (List.mem_range.2 hp)
  · intro hb a ha
    rw [List.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · exact h0
    · rw [h a ha ha0]
      exact hb

theorem orbCheck_powTabs (hsz : szOK n w = true) {p X : Nat} (hX : PP n w X) (hp : p.Prime)
    (hord : pord n w p X = true) {cands : List (List Nat)} (hc : ∀ c ∈ cands, ∀ b ∈ c, PP n w b)
    {invs : List Table} (hI : ∀ t ∈ invs, ∃ u, PP n w u ∧ t = tabP n w u) :
    orbCheck n p invs (powTabs n (tabP n w X) p) (cands.map (List.map (tabP n w))) =
      orbCheck n p invs [tabP n w X] (cands.map (List.map (tabP n w))) := by
  have hg := sg_pow_of_pord hX hord
  have h1 := hp.one_lt
  have hY : ∀ {Y Y' : Nat}, PP n w Y → PP n w Y' →
      (∀ u, PP n w u → porbOne n w p Y cands u = porbOne n w p Y' cands u) →
      (invs.all fun t => !(badAct n p (tabP n w Y) (invT n (tabP n w Y)) t) ||
        (cands.map (List.map (tabP n w))).any
          (orbIs n (orbTabs n p (tabP n w Y) (invT n (tabP n w Y)) t))) =
      (invs.all fun t => !(badAct n p (tabP n w Y') (invT n (tabP n w Y')) t) ||
        (cands.map (List.map (tabP n w))).any
          (orbIs n (orbTabs n p (tabP n w Y') (invT n (tabP n w Y')) t))) := by
    intro Y Y' hy hy' H
    refine all_congr' fun t ht => ?_
    obtain ⟨u, hu, rfl⟩ := hI t ht
    rw [orbOne_tabP hsz hy hu hc, orbOne_tabP hsz hy' hu hc, H u hu]
  rw [orbCheck, orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP hX,
    Bool.true_and, powTabs, List.all_map]
  refine range_all_eq h1 ?_ fun a hap ha0 => ?_
  · simp only [Function.comp_apply, powT_tabP hX, invOK_tabP (PP_ppw hX 0), Bool.true_and]
    rw [List.all_eq_true]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := hI t ht
    rw [orbOne_tabP hsz (PP_ppw hX 0) hu hc]
    exact porbOne_zero hsz hX hu hc
  · simp only [Function.comp_apply, powT_tabP hX, invOK_tabP (PP_ppw hX a), Bool.true_and]
    exact hY (PP_ppw hX a) hX fun u hu =>
      porbOne_pow hsz hX hu hc hg h1 (Nat.coprime_of_lt_prime ha0.ne' hap hp).symm

theorem actCheck_powTabs {p X : Nat} (hX : PP n w X) (hp : p.Prime) (hord : pord n w p X = true)
    {invs : List Table} (hI : ∀ t ∈ invs, ∃ u, PP n w u ∧ t = tabP n w u) :
    actCheck n p invs (powTabs n (tabP n w X) p) = actCheck n p invs [tabP n w X] := by
  have hg := sg_pow_of_pord hX hord
  have h1 := hp.one_lt
  rw [actCheck, actCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP hX,
    Bool.true_and, powTabs, List.all_map]
  refine range_all_eq h1 ?_ fun a hap ha0 => ?_
  · simp only [Function.comp_apply, powT_tabP hX, invOK_tabP (PP_ppw hX 0), Bool.true_and]
    rw [List.all_eq_true]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := hI t ht
    rw [actOne_tabP (PP_ppw hX 0) hu]
    exact pactOne_zero hX hu
  · simp only [Function.comp_apply, powT_tabP hX, invOK_tabP (PP_ppw hX a), Bool.true_and]
    refine all_congr' fun t ht => ?_
    obtain ⟨u, hu, rfl⟩ := hI t ht
    rw [actOne_tabP (PP_ppw hX a) hu, actOne_tabP hX hu]
    exact pactOne_pow hX hu hg h1 (Nat.coprime_of_lt_prime ha0.ne' hap hp).symm

end CFSG.KC.KGC31P

end
