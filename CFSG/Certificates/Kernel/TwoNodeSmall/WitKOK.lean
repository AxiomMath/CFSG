module

public import CFSG.Certificates.Kernel.TwoNodeSmall.PosBKOK

public section

namespace CFSG.TwoNodeSmall.WitK.OK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.LaneSound CFSG.TwoNodeSmall.PosBK
  CFSG.TwoNodeSmall.PosBK.OKS

open CFSG.TwoNodeSmall.ExclK (pkrP)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {P : Pt}

theorem packR3 (hp : P.p = 3) (r : Refl) : packR P r = (pk P.D r.h, pkr P.D r.f) := by
  unfold packR
  rw [hp]
  rfl

theorem conjW (hp : P.p = 3) (hD : P.D ≤ 10) (g r : Refl) :
    (red (Nat.mul 3 (ones P.D)) (Nat.add (packR P r).1 (Nat.mul (Nat.mod (Nat.sub 3
        (dotK (Nat.mul 16 (Nat.sub P.D 1)) (packR P g).2 (packR P r).1)) 3) (packR P g).1)),
      red (Nat.mul 3 (ones P.D)) (Nat.add (packR P r).2 (Nat.mul (Nat.mod (Nat.sub 3
        (dotK (Nat.mul 16 (Nat.sub P.D 1)) (packR P r).2 (packR P g).1)) 3) (packR P g).2))) =
      packR P (conjR P g r) := by
  rw [packR3 hp, packR3 hp, packR3 hp]
  refine Prod.ext ?_ ?_
  · exact appKW_pk hp hD g.h g.f r.h
  · exact conjFW_pkr hp hD g.h g.f r.f

theorem cloK_cons (m3 sh n : Nat) (G C : List (Nat × Nat)) (e : Nat × Nat × Nat × Nat)
    (es : List (Nat × Nat × Nat × Nat)) (i cur : Nat) (suf : List (Nat × Nat)) :
    cloK m3 sh n G C (e :: es) i cur suf =
      (Nat.blt e.2.1 i && Nat.ble cur e.2.1 && Nat.blt e.1 n &&
      Nat.beq e.2.2.1 (red m3 (Nat.add ((dropK (Nat.sub e.2.1 cur) suf).headD (0, 0)).1
        (Nat.mul (Nat.mod (Nat.sub 3 (dotK sh (nthK (0, 0) G e.1).2
          ((dropK (Nat.sub e.2.1 cur) suf).headD (0, 0)).1)) 3) (nthK (0, 0) G e.1).1))) &&
      Nat.beq e.2.2.2 (red m3 (Nat.add ((dropK (Nat.sub e.2.1 cur) suf).headD (0, 0)).2
        (Nat.mul (Nat.mod (Nat.sub 3 (dotK sh ((dropK (Nat.sub e.2.1 cur) suf).headD (0, 0)).2
          (nthK (0, 0) G e.1).1)) 3) (nthK (0, 0) G e.1).2))) &&
      cloK m3 sh n G C es (Nat.succ i) e.2.1 (dropK (Nat.sub e.2.1 cur) suf)) := rfl

theorem cloK_spec [Fact P.p.Prime] (hp : P.p = 3) (hD : P.D ≤ 10) (C C' : List (Nat × Nat)) :
    ∀ (clo : List (Nat × Nat × Nat × Nat)) (acc : List CE) (cur : Nat) (rest : List (Nat × Nat)),
      cloK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) P.gens.length
        (P.gens.map (packR P)) C' clo acc.length cur (C.drop cur) = true →
      cur ≤ acc.length → acc.map (fun x => packR P x.1) = C.take acc.length →
      C.drop acc.length = clo.map ent ++ rest → (∀ x ∈ acc, Sem P x) →
      (cloD P acc clo).map (fun x => packR P x.1) = C.take (acc.length + clo.length) ∧
        ∀ x ∈ cloD P acc clo, Sem P x
  | [], acc, _, _, _, _, hacc, _, hs => by
    refine ⟨?_, hs⟩
    simpa [cloD] using hacc
  | e :: es, acc, cur, rest, h, hcur, hacc, hdrop, hs => by
    rw [cloK_cons] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨⟨hq, hcq⟩, hj⟩, hc1⟩, hc2⟩, hrest⟩ := h
    have hlen : acc.length ≤ C.length := by
      have := congrArg List.length hacc
      simp only [List.length_map, List.length_take] at this
      omega
    have hsuf : dropK (Nat.sub e.2.1 cur) (C.drop cur) = C.drop e.2.1 := by
      rw [dropK_eq', List.drop_drop]
      congr 1
      change cur + (e.2.1 - cur) = e.2.1
      omega
    rw [hsuf] at hc1 hc2 hrest
    have hCq : (C.drop e.2.1).headD (0, 0) = packR P (acc.getD e.2.1 dfl).1 := by
      rw [headD_drop]
      have hqC : e.2.1 < C.length := by omega
      rw [List.getD_eq_getElem _ _ hqC, List.getD_eq_getElem _ _ hq]
      have := congrArg (fun l => l[e.2.1]?) hacc
      simp only [List.getElem?_map, List.getElem?_eq_getElem hq, List.getElem?_take,
        if_pos hq, List.getElem?_eq_getElem hqC,
        Option.map_some, Option.some.injEq] at this
      exact this.symm
    have hGj : nthK (0, 0) (P.gens.map (packR P)) e.1 = packR P (P.gens.getD e.1 ⟨[], []⟩) := by
      rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj]
    rw [hCq, hGj] at hc1 hc2
    have hcw := conjW hp hD (P.gens.getD e.1 ⟨[], []⟩) (acc.getD e.2.1 dfl).1
    have hc1' := hc1.trans (congrArg Prod.fst hcw)
    have hc2' := hc2.trans (congrArg Prod.snd hcw)
    have hent : ent e = packR P (stepC P acc e).1 := by
      simp only [ent, stepC, Prod.ext_iff]
      exact ⟨hc1', hc2'⟩
    have hsem : Sem P (stepC P acc e) := by
      have hx : Sem P (acc.getD e.2.1 dfl) := by
        rw [List.getD_eq_getElem _ _ hq]; exact hs _ (List.getElem_mem hq)
      exact sem_step hx hj
    have hacc' : (acc ++ [stepC P acc e]).map (fun x => packR P x.1) =
        C.take (acc ++ [stepC P acc e]).length := by
      rw [List.map_append, hacc, List.length_append, List.length_singleton, List.take_succ]
      have h0 : C[acc.length]? = some (ent e) := by
        have := congrArg (fun l => l[0]?) hdrop
        simpa using this
      rw [h0]
      simp [hent]
    have hdrop' : C.drop (acc ++ [stepC P acc e]).length = es.map ent ++ rest := by
      rw [List.length_append, List.length_singleton, ← List.drop_drop, hdrop]
      simp
    have hs' : ∀ x ∈ acc ++ [stepC P acc e], Sem P x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hs x hx
      · rw [List.mem_singleton.mp hx]; exact hsem
    have hl : (acc ++ [stepC P acc e]).length = Nat.succ acc.length := by simp
    rw [← hl] at hrest
    have := cloK_spec hp hD C C' es (acc ++ [stepC P acc e]) e.2.1 rest hrest (by simp; omega)
      hacc' hdrop' hs'
    have hl2 : (acc ++ [stepC P acc e]).length + es.length = acc.length + (e :: es).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [cloD]
    refine ⟨?_, this.2⟩
    rw [this.1, hl2]

theorem clo_specW [Fact P.p.Prime] (hp : P.p = 3) (hD : P.D ≤ 10)
    (clo : List (Nat × Nat × Nat × Nat)) (C' : List (Nat × Nat))
    (h : cloK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) P.gens.length
      (P.gens.map (packR P)) C' clo P.gens.length 0 (P.gens.map (packR P) ++ clo.map ent) = true) :
    (cloD P (baseD P) clo).map (fun x => packR P x.1) = P.gens.map (packR P) ++ clo.map ent ∧
      ∀ x ∈ cloD P (baseD P) clo, Sem P x := by
  have e1 : (baseD P).length = P.gens.length := by simp [baseD]
  have hclo' : cloK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) P.gens.length
      (P.gens.map (packR P)) C' clo (baseD P).length 0
      ((P.gens.map (packR P) ++ clo.map ent).drop 0) = true := by
    rw [e1, List.drop_zero]
    exact h
  have hacc : (baseD P).map (fun x => packR P x.1) =
      (P.gens.map (packR P) ++ clo.map ent).take (baseD P).length := by
    rw [e1, List.take_left' (by simp)]
    apply List.ext_getElem (by simp [baseD])
    intro i h1 h2
    simp only [baseD, List.length_map, List.length_range] at h1
    simp [baseD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  have hdrop : (P.gens.map (packR P) ++ clo.map ent).drop (baseD P).length =
      clo.map ent ++ [] := by
    rw [e1, List.append_nil, List.drop_left' (by simp)]
  obtain ⟨hDl, hsem⟩ := cloK_spec hp hD _ C' clo (baseD P) 0 [] hclo' (Nat.zero_le _) hacc hdrop
    sem_base
  refine ⟨?_, hsem⟩
  rw [hDl, List.take_of_length_le]
  simp [e1]

theorem natrecW (b : Nat → Bool) : ∀ D,
    Nat.rec (motive := fun _ => Bool) true (fun j ih => b j && ih) D = true → ∀ j < D, b j = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | D + 1, h, j, hj => by
    change (b D && Nat.rec (motive := fun _ => Bool) true (fun j ih => b j && ih) D) = true at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_or_ge j D with hjD | hjD
    · exact natrecW b D h.2 j hjD
    · obtain rfl : j = D := by omega
      exact h.1

theorem nthK_mapW {α β : Type} (d : β) (f : α → β) {l : List α} {k : Nat} (hk : k < l.length) :
    nthK d (l.map f) k = f l[k] := by
  rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

theorem gensK_eqW (hp : P.p = 3) : gensK P = P.gens.map (packR P) := by
  unfold gensK
  apply List.map_congr_left
  intro g _
  rw [packR3 hp]

theorem vec_congr_refl [Fact P.p.Prime] (r : Refl) {w w' : Vec} (h : P.vec w = P.vec w') :
    P.vec (P.applyRefl r w) = P.vec (P.applyRefl r w') := by
  rw [vec_refl, vec_refl, h]

theorem ent_of_vec [Fact P.p.Prime] {a b : Vec} (h : P.vec a = P.vec b) {j : Nat} (hj : j < P.D) :
    P.ent a j = P.ent b j := by
  have := congrFun h ⟨j, hj⟩
  simp only [Pt.vec] at this
  rw [ZMod.natCast_eq_natCast_iff'] at this
  exact this

theorem ent_of_vecEq {a b : Vec} (h : P.vecEq a b = true) {j : Nat} (hj : j < P.D) :
    P.ent a j = P.ent b j := by
  unfold Pt.vecEq at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.mp (h j (List.mem_range.mpr hj))

theorem pk_nil (D : Nat) : pk D [] = 0 := by
  rw [pk_eq]
  exact fw_eq_zero _ _ (fun j _ => by simp [ln])

theorem wordOK_app (a b : Word) : P.wordOK (a ++ b) = (P.wordOK a && P.wordOK b) := by
  simp only [Pt.wordOK, List.all_append]

theorem pkr_nil (D : Nat) : pkr D [] = 0 := by
  rw [pkr_eq]
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [rv_succ_last, ih]
    simp [ln]

theorem vecNZ_of_pk (hp : P.p = 3) {u : Vec} (h : (pk P.D u == 0) = false) : P.vecNZ u = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  unfold Pt.vecNZ at hc
  rw [List.any_eq_false] at hc
  have hv : P.vecEq u [] = true := by
    unfold Pt.vecEq
    rw [List.all_eq_true]
    intro j hj
    have := hc j hj
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
    rw [this]
    simp [Pt.ent]
  rw [← pk_inj hp, pk_nil] at hv
  rw [hv] at h
  exact absurd h (by decide)

theorem vecNZ_of_pkr (hp : P.p = 3) {u : Vec} (h : (pkr P.D u == 0) = false) :
    P.vecNZ u = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  unfold Pt.vecNZ at hc
  rw [List.any_eq_false] at hc
  have hv : P.vecEq u [] = true := by
    unfold Pt.vecEq
    rw [List.all_eq_true]
    intro j hj
    have := hc j hj
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
    rw [this]
    simp [Pt.ent]
  rw [← pkr_inj hp, pkr_nil] at hv
  rw [hv] at h
  exact absurd h (by decide)

theorem WF_of_gens (hp : P.p = 3) (hD : P.D ≤ 10) [Fact P.p.Prime]
    (h : (P.gens.map (packR P)).all (fun g => Nat.beq (dotK (Nat.mul 16 (Nat.sub P.D 1)) g.2 g.1) 2)
      = true) : P.WF ∧ wfCheck P = true := by
  rw [List.all_eq_true] at h
  have h2 : ∀ g ∈ P.gens, P.dotv g.f g.h = 2 := by
    intro g hg
    have := h _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [packR3 hp, Nat.beq_eq, dotKW_pk hp hD] at this
    exact this
  refine ⟨fun g hg => ?_, ?_⟩
  · rw [← Pt.dotv_spec, h2 g hg]
    rfl
  · unfold wfCheck
    rw [List.all_eq_true]
    intro g hg
    rw [h2 g hg, hp]
    rfl

theorem chk_common {P : Pt} {k : Nat} (hk : k ≠ 0) {sm : List Nat}
    {clo : List (Nat × Nat × Nat × Nat)} {lv : List (Nat × List Nat × List Nat)}
    {ex : List (List Nat)} (h : chkPt P (k, sm, clo, lv, ex) = true) :
    ∃ (hp : P.p = 3) (hD : P.D ≤ 10) (_ : 1 ≤ P.D) (_ : Fact P.p.Prime), P.WF ∧ wfCheck P = true ∧
      ∃ Dl : List CE, (∀ x ∈ Dl, Sem P x) ∧ Dl.length = P.gens.length + clo.length ∧
        P.gens.map (packR P) ++ clo.map ent = Dl.map (fun x => packR P x.1) ∧
        (bif Nat.beq k 1 then tK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) Dl.length
            (Dl.map fun x => packR P x.1) sm
          else bif Nat.beq k 2 then Nat.blt P.bound (chainK P.D (Nat.mul 3 (ones P.D))
            (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) Dl.length (Dl.map fun x => packR P x.1) lv 0 1)
          else bif Nat.beq k 3 then wK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1))
            (yK P.D) Dl.length (P.gens.map (packR P)) (Dl.map fun x => packR P x.1) sm ex lv
          else false) = true := by
  have hk0 : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun h' => hk (Nat.eq_of_beq_eq_true h')
  unfold chkPt at h
  simp only [hk0, cond_false, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨hp, hD1⟩, hD⟩, ⟨hG, hclo⟩, hkind⟩ := h
  have hfact : Fact P.p.Prime := ⟨by rw [hp]; norm_num⟩
  rw [gensK_eqW hp] at hG hclo hkind
  obtain ⟨hWF, hwf⟩ := WF_of_gens hp hD hG
  have hclo' : cloK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) P.gens.length
      (P.gens.map (packR P)) (P.gens.map (packR P) ++ clo.map ent) clo P.gens.length 0
      (P.gens.map (packR P) ++ clo.map ent) = true := by
    rw [List.length_map] at hclo
    exact hclo
  obtain ⟨hDl, hsem⟩ := clo_specW hp hD clo _ hclo'
  have hlen : (cloD P (baseD P) clo).length = P.gens.length + clo.length := by
    have := congrArg List.length hDl
    simp only [List.length_map, List.length_append] at this
    exact this
  refine ⟨hp, hD, hD1, hfact, hWF, hwf, cloD P (baseD P) clo, hsem, hlen, hDl.symm, ?_⟩
  have e1 : (P.gens.map (packR P) ++ clo.map fun e => (e.2.2.1, e.2.2.2)) =
      (cloD P (baseD P) clo).map (fun x => packR P x.1) := hDl.symm
  have e2 : Nat.add (P.gens.map (packR P)).length clo.length = (cloD P (baseD P) clo).length := by
    rw [hlen, List.length_map]
    rfl
  rw [e1, e2] at hkind
  exact hkind

@[expose] def tWord (a b : Word) (sq : Nat) : Word := bif Nat.beq sq 0 then a ++ b else a ++ b ++ a ++ b

theorem tK_verify [Fact P.p.Prime] (hp : P.p = 3) (hD : P.D ≤ 10) (hwf : P.WF) {Dl : List CE}
    (hs : ∀ x ∈ Dl, Sem P x) {sm : List Nat}
    (h : tK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) Dl.length
      (Dl.map fun x => packR P x.1) sm = true) : ∃ t, verifyT P t = true := by
  unfold tK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hs0, ht0⟩, hsq⟩, hU⟩, hΦ⟩, hd⟩, hcols⟩ := h
  set s := nthK 0 sm 0
  set t := nthK 0 sm 1
  set sq := nthK 0 sm 2
  set u := dropK 3 sm
  set φ := dropK (Nat.add 3 P.D) sm
  have hS := hs _ (List.getElem_mem hs0)
  have hT := hs _ (List.getElem_mem ht0)
  rw [nthK_mapW _ _ hs0, nthK_mapW _ _ ht0] at hcols
  refine ⟨⟨tWord (sw Dl[s]) (sw Dl[t]) sq, u, φ⟩, ?_⟩
  unfold verifyT
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, vecNZ_of_pk hp hU⟩, vecNZ_of_pkr hp hΦ⟩, ?_⟩, ?_⟩
  · have h1 := sw_ok hS
    have h2 := sw_ok hT
    unfold tWord
    cases Nat.beq sq 0 <;> simp only [cond_false, cond_true, wordOK_app, h1, h2, Bool.and_self]
  · rw [← dotKW_pk hp hD]
    exact hd
  · intro i hi j hj
    rw [List.mem_range] at hi hj
    have hc := natrecW _ P.D hcols i hi
    simp only [Nat.beq_eq] at hc
    rw [shiftLeft_unit P hi, packR3 hp, packR3 hp, appKW_pk hp hD, appKW_pk hp hD,
      redW_eq, red_fw_add 3 (Or.inl rfl) P.D (Nat.mod (nthK 0 φ i) 3)
        (Nat.le_of_lt_succ (Nat.mod_lt (nthK 0 φ i) (by norm_num)))] at hc
    have hw : P.vec (P.applyWord (tWord (sw Dl[s]) (sw Dl[t]) sq) (P.unit i)) =
        P.vec (bif Nat.beq sq 0 then P.applyRefl Dl[s].1 (P.applyRefl Dl[t].1 (P.unit i))
          else P.applyRefl Dl[s].1 (P.applyRefl Dl[t].1
            (P.applyRefl Dl[s].1 (P.applyRefl Dl[t].1 (P.unit i))))) := by
      unfold tWord
      cases Nat.beq sq 0
      · simp only [cond_false, applyWord_append]
        rw [sw_act hwf hS, vec_congr_refl _ (sw_act hwf hT _), vec_congr_refl _ (vec_congr_refl _
          (sw_act hwf hS _)), vec_congr_refl _ (vec_congr_refl _ (vec_congr_refl _
            (sw_act hwf hT _)))]
      · simp only [cond_true, applyWord_append]
        rw [sw_act hwf hS, vec_congr_refl _ (sw_act hwf hT _)]
    rw [ent_of_vec hw hj]
    have key : ∀ g : Vec, pk P.D g = fw P.D (fun l => (ln (P.unit i) l + nthK 0 φ i % 3 * ln u l) % 3) →
        P.ent g j = ((if i = j then 1 else 0) + P.ent φ i * P.ent u j) % P.p := by
      intro g hg
      have e : fw P.D (fun l => (ln (P.unit i) l + nthK 0 φ i % 3 * ln u l) % 3) =
          pk P.D ((List.range P.D).map fun l => (ln (P.unit i) l + nthK 0 φ i % 3 * ln u l) % 3) := by
        rw [pk_eq]
        unfold fw
        apply enc_map_congr
        intro l hl
        rw [List.mem_range] at hl
        simp [ln, List.getD_eq_getElem?_getD, hl]
      rw [e, pk_inj hp] at hg
      rw [ent_of_vecEq hg hj]
      simp only [Pt.ent, hp, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
        Option.map_some, Option.getD_some, ln, Pt.unit, nthK_eq']
      by_cases hij : i = j
      · subst hij
        simp only [if_pos rfl]
        omega
      · rw [if_neg (Ne.symm hij), if_neg hij]
        simp only [Nat.zero_mod, Nat.zero_add, Nat.mod_mod, Nat.mul_mod (List.getD φ i 0 % 3)]
    cases hb : Nat.beq sq 0
    · rw [hb] at hc
      simp only [cond_false] at hc
      rw [appKW_pk hp hD, appKW_pk hp hD] at hc
      exact key _ hc
    · rw [hb] at hc
      simp only [cond_true] at hc
      exact key _ hc

theorem minor_aux : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ d < 3, d ≠ 0 → (a * d) % 3 = (c * b) % 3 →
    a = ((c * d) % 3 * b) % 3 := by
  intro a ha b hb c hc d hd h0 h
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> omega

theorem kK_verify (hp : P.p = 3) (hD : P.D ≤ 10) {w : Vec}
    (h : kK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) P.nFrame (gensK P) (pk P.D P.x)
      (pk P.D w) = true) : verifyK P w = true := by
  unfold kK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hX : pk P.D P.x ≠ 0 := fun e => by rw [e] at h2; exact absurd h2 (by decide)
  have hW : pk P.D w ≠ 0 := fun e => by rw [e] at h3; exact absurd h3 (by decide)
  have hWX : pk P.D w ≠ pk P.D P.x := fun e => by
    rw [e, Nat.beq_refl] at h4
    exact absurd h4 (by decide)
  have hW2 : pk P.D w ≠ red (Nat.mul 3 (ones P.D)) (Nat.add (pk P.D P.x) (pk P.D P.x)) :=
    fun e => by
      rw [e, Nat.beq_refl] at h5
      exact absurd h5 (by decide)
  unfold verifyK
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at h1 ⊢
    intro g hg
    have := h1 (pk P.D g.h, pkr P.D g.f) (by
      unfold gensK
      rw [← List.map_take]
      exact List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [Nat.beq_eq, dotKW_pk hp hD] at this
    rw [beq_iff_eq]
    exact this
  by_contra hc
  have hm : ∀ i < P.D, ∀ j < P.D, (P.ent w i * P.ent P.x j) % 3 = (P.ent w j * P.ent P.x i) % 3 := by
    intro i hi j hj
    by_contra hne
    apply hc
    rw [List.any_eq_true]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [List.any_eq_true]
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [hp]
    simpa using hne
  have hx0 : ∃ j0 < P.D, ln P.x j0 ≠ 0 := by
    by_contra hn
    simp only [not_exists, not_and, Decidable.not_not] at hn
    apply hX
    rw [pk_eq]
    exact fw_eq_zero _ _ hn
  obtain ⟨j0, hj0, hx0⟩ := hx0
  have hcoord : ∀ i < P.D, ln w i = ((ln w j0 * ln P.x j0) % 3 * ln P.x i) % 3 := by
    intro i hi
    have := hm i hi j0 hj0
    simp only [Pt.ent, hp] at this
    exact minor_aux _ (by have := ln_le w i; omega) _ (by have := ln_le P.x i; omega) _
      (by have := ln_le w j0; omega) _ (by have := ln_le P.x j0; omega) hx0 this
  have hWeq : pk P.D w = fw P.D (fun i => ((ln w j0 * ln P.x j0) % 3 * ln P.x i) % 3) := by
    rw [pk_eq]
    unfold fw
    apply enc_map_congr
    intro i hi
    exact hcoord i (List.mem_range.mp hi)
  have hl : (ln w j0 * ln P.x j0) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize (ln w j0 * ln P.x j0) % 3 = l at hWeq hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · apply hW
    rw [hWeq]
    exact fw_eq_zero _ _ (fun j _ => by simp)
  · apply hWX
    rw [hWeq, pk_eq]
    unfold fw
    apply enc_map_congr
    intro i _
    have := ln_le P.x i
    omega
  · apply hW2
    have e2 : Nat.add (pk P.D P.x) (pk P.D P.x) = Nat.add (pk P.D P.x) (Nat.mul 1 (pk P.D P.x)) :=
      congrArg (Nat.add (pk P.D P.x)) (Nat.one_mul _).symm
    rw [redW_eq, hWeq, e2, red_fw_add 3 (Or.inl rfl) P.D 1 (by norm_num)]
    unfold fw
    apply enc_map_congr
    intro i _
    omega

theorem kidsK_nil (m3 sh y V m : Nat) (st : List Nat × Nat × Nat × Bool) :
    kidsK m3 sh y V [] m st = (st.1, st.2.1, st.2.2.1, st.2.2.2 && Nat.beq m 0) := rfl

theorem kidsK_cons (m3 sh y V : Nat) (r : Nat × Nat) (rs : List (Nat × Nat)) (m : Nat)
    (st : List Nat × Nat × Nat × Bool) :
    kidsK m3 sh y V (r :: rs) m st =
      bif Nat.beq m 0 then st
      else bif Nat.beq (Nat.land m 1) 0 then kidsK m3 sh y V rs (Nat.shiftRight m 1) st
      else kidsK m3 sh y V rs (Nat.shiftRight m 1)
        (appK m3 sh r V :: st.1, Nat.lor st.2.1 (Nat.shiftLeft 1 (codeK y sh (appK m3 sh r V))),
          Nat.succ st.2.2.1, st.2.2.2 && clearB st.2.1 (codeK y sh (appK m3 sh r V))) := rfl

theorem kidsK_false (m3 sh y V : Nat) : ∀ (rs : List (Nat × Nat)) (m : Nat)
    (st : List Nat × Nat × Nat × Bool), st.2.2.2 = false →
      (kidsK m3 sh y V rs m st).2.2.2 = false
  | [], m, st, h => by simp [kidsK_nil, h]
  | r :: rs, m, st, h => by
    rw [kidsK_cons]
    cases Nat.beq m 0
    · cases Nat.beq (Nat.land m 1) 0
      · exact kidsK_false m3 sh y V rs _ _ (by simp [h])
      · exact kidsK_false m3 sh y V rs _ st h
    · exact h

structure TInvW (P : Pt) (Sv : List Refl) (root : Vec) (T : List TE) (np : Nat)
    (fr bk : List Nat) (bs cnt : Nat) : Prop where
  q1 : (T.drop np).map (fun e => pk P.D e.1) = fr ++ bk.reverse
  q2 : cnt = T.length
  q3 : (T.map fun e => P.code e.1).Nodup
  q4 : ∀ e ∈ T, bs.testBit (P.code e.1) = true
  q5 : ∀ i (hi : i < T.length), 0 < i → T[i].2.1 < i ∧ T[i].2.2 < Sv.length ∧
    T[i].1 = P.applyRefl (Sv.getD T[i].2.2 ⟨[], []⟩) (T.getD T[i].2.1 dt).1
  q6 : T.head? = some (root, 0, 0)
  q7 : np ≤ T.length

structure TFinW (P : Pt) (Sv : List Refl) (root : Vec) (T : List TE) : Prop where
  q3 : (T.map fun e => P.code e.1).Nodup
  q5 : ∀ i (hi : i < T.length), 0 < i → T[i].2.1 < i ∧ T[i].2.2 < Sv.length ∧
    T[i].1 = P.applyRefl (Sv.getD T[i].2.2 ⟨[], []⟩) (T.getD T[i].2.1 dt).1
  q6 : T.head? = some (root, 0, 0)

theorem pop_specW {Sv : List Refl} {root : Vec} {T : List TE} {np : Nat}
    {fr bk : List Nat} {bs cnt : Nat} (h : TInvW P Sv root T np fr bk bs cnt)
    (hp : (popK fr bk).2.2.2 = true) :
    np < T.length ∧ (popK fr bk).1 = pk P.D (T.getD np dt).1 ∧
      TInvW P Sv root T (np + 1) (popK fr bk).2.1 (popK fr bk).2.2.1 bs cnt := by
  have q1 := h.q1
  cases fr with
  | cons x xs =>
    rw [popK_cons]
    rw [List.cons_append] at q1
    obtain ⟨hlt, hx, hr⟩ := drop_map_cons q1
    exact ⟨hlt, hx.symm, ⟨hr, h.q2, h.q3, h.q4, h.q5, h.q6, hlt⟩⟩
  | nil =>
    rw [popK_nil] at hp ⊢
    rw [List.nil_append] at q1
    cases hb : bk.reverse with
    | nil => rw [hb] at hp; cases hp
    | cons x xs =>
      rw [hb] at q1
      obtain ⟨hlt, hx, hr⟩ := drop_map_cons q1
      refine ⟨hlt, hx.symm, ⟨?_, h.q2, h.q3, h.q4, h.q5, h.q6, hlt⟩⟩
      rw [hr]
      simp

theorem kids_specW (hp : P.p = 3) (hD : P.D ≤ 10) {Sv : List Refl} {root : Vec}
    {np par : Nat} {fr : List Nat} {V : Vec} :
    ∀ (rs : List Refl) (k m : Nat) (bk : List Nat) (bs cnt : Nat) (fl : Bool) (T : List TE),
      Sv.drop k = rs → par < T.length → (T.getD par dt).1 = V →
      TInvW P Sv root T np fr bk bs cnt →
      (kidsK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (pk P.D V)
        (rs.map (packR P)) m (bk, bs, cnt, fl)).2.2.2 = true →
      ∃ T', (∃ new, T' = T ++ new) ∧
        TInvW P Sv root T' np fr
          (kidsK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (pk P.D V)
            (rs.map (packR P)) m (bk, bs, cnt, fl)).1
          (kidsK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (pk P.D V)
            (rs.map (packR P)) m (bk, bs, cnt, fl)).2.1
          (kidsK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (pk P.D V)
            (rs.map (packR P)) m (bk, bs, cnt, fl)).2.2.1
  | [], k, m, bk, bs, cnt, fl, T, _, _, _, hI, _ => by
    rw [List.map_nil, kidsK_nil]
    exact ⟨T, ⟨[], by simp⟩, hI⟩
  | r :: rs, k, m, bk, bs, cnt, fl, T, hk, hpar, hV, hI, hfl => by
    have hk' : Sv.drop (k + 1) = rs := by rw [← List.tail_drop, hk]; rfl
    have hkl : k < Sv.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hk
      cases hk
    have hSk : Sv.getD k ⟨[], []⟩ = r := by
      rw [← headD_drop, hk]
      rfl
    rw [List.map_cons, kidsK_cons] at hfl ⊢
    cases hm : Nat.beq m 0
    · rw [hm] at hfl
      simp only [cond_false] at hfl ⊢
      cases hb : Nat.beq (Nat.land m 1) 0
      · rw [hb] at hfl
        simp only [cond_false] at hfl ⊢
        have hw : appK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (packR P r) (pk P.D V) =
            pk P.D (P.applyRefl r V) := by
          rw [packR3 hp]
          exact appKW_pk hp hD r.h r.f V
        have hcode : codeK (yK P.D) (Nat.mul 16 (Nat.sub P.D 1)) (pk P.D (P.applyRefl r V)) =
            P.code (P.applyRefl r V) := codeK_pk hp hD _
        rw [hw, hcode] at hfl ⊢
        set c := P.code (P.applyRefl r V) with hcdef
        have hin : (fl && clearB bs c) = true := by
          by_contra hc
          rw [Bool.not_eq_true] at hc
          rw [kidsK_false _ _ _ _ (rs.map (packR P)) _ _ hc] at hfl
          cases hfl
        have hcl : bs.testBit c = false := clearB_spec (Bool.and_eq_true _ _ ▸ hin).2
        let e : TE := (P.applyRefl r V, par, k)
        have hI' : TInvW P Sv root (T ++ [e]) np fr (pk P.D (P.applyRefl r V) :: bk)
            (Nat.lor bs (Nat.shiftLeft 1 c)) (Nat.succ cnt) := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [List.drop_append_of_le_length hI.q7, List.map_append, hI.q1]
            simp [e]
          · rw [hI.q2]; simp
          · rw [List.map_append, List.nodup_append]
            refine ⟨hI.q3, by simp, ?_⟩
            intro a ha b hb hab
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
            have := hI.q4 x hx
            rw [hab, hb] at this
            simp only [e] at this
            rw [← hcdef, hcl] at this
            cases this
          · intro x hx
            rw [testBit_lor_one]
            rcases List.mem_append.mp hx with hx | hx
            · rw [hI.q4 x hx]; rfl
            · rw [List.mem_singleton.mp hx]; simp [e, hcdef]
          · intro i hi hi0
            rw [List.length_append, List.length_singleton] at hi
            rcases Nat.lt_or_ge i T.length with hiT | hiT
            · obtain ⟨a1, a2, a3⟩ := hI.q5 i hiT hi0
              rw [List.getElem_append_left hiT, getD_append_left _ _ _ (by omega)]
              exact ⟨a1, a2, a3⟩
            · have hiE : i = T.length := by omega
              subst hiE
              rw [List.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero, e]
              refine ⟨hpar, hkl, ?_⟩
              rw [getD_append_left _ _ _ hpar, hV, hSk]
          · obtain ⟨t, ht⟩ : ∃ t, T = (root, 0, 0) :: t := by
              have := hI.q6
              cases T with
              | nil => cases this
              | cons a t => exact ⟨t, by simp at this; rw [this]⟩
            rw [ht]
            rfl
          · simp only [List.length_append]
            have := hI.q7
            omega
        have hpar' : par < (T ++ [e]).length := by
          rw [List.length_append]
          omega
        obtain ⟨T', ⟨new, hT'⟩, hI''⟩ := kids_specW hp hD rs (k + 1) _ _ _ _ _ (T ++ [e]) hk'
          hpar' (by rw [getD_append_left _ _ _ hpar, hV]) hI' hfl
        exact ⟨T', ⟨e :: new, by rw [hT']; simp⟩, hI''⟩
      · rw [hb] at hfl
        simp only [cond_true] at hfl ⊢
        exact kids_specW hp hD rs (k + 1) _ bk bs cnt fl T hk' hpar hV hI hfl
    · simp only [cond_true]
      exact ⟨T, ⟨[], by simp⟩, hI⟩

@[expose] noncomputable def tloopW (m3 sh y : Nat) (S : List (Nat × Nat)) (ms : List Nat) :
    List Nat × List Nat × Nat × Nat × Bool → Nat :=
  List.rec (motive := fun _ => List Nat × List Nat × Nat × Nat × Bool → Nat)
    (fun st => bif st.2.2.2.2 then st.2.2.2.1 else 0)
    (fun m _ ih st =>
      let p := popK st.1 st.2.1
      let r := kidsK m3 sh y p.1 S m (p.2.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 && p.2.2.2)
      ih (p.2.1, r.1, r.2.1, r.2.2.1, r.2.2.2))
    ms

theorem treeK_eq (m3 sh y : Nat) (S : List (Nat × Nat)) (root : Nat) (ms : List Nat) :
    treeK m3 sh y S root ms =
      tloopW m3 sh y S ms ([root], [], Nat.shiftLeft 1 (codeK y sh root), 1, true) := rfl

theorem tloopW_nil (m3 sh y : Nat) (S : List (Nat × Nat)) (st) :
    tloopW m3 sh y S [] st = bif st.2.2.2.2 then st.2.2.2.1 else 0 := rfl

theorem tloopW_cons (m3 sh y : Nat) (S : List (Nat × Nat)) (m : Nat) (ms : List Nat) (st) :
    tloopW m3 sh y S (m :: ms) st = tloopW m3 sh y S ms ((popK st.1 st.2.1).2.1,
      (kidsK m3 sh y (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).1,
      (kidsK m3 sh y (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.1,
      (kidsK m3 sh y (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.2.1,
      (kidsK m3 sh y (popK st.1 st.2.1).1 S m ((popK st.1 st.2.1).2.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.2.2) := rfl

theorem tloopW_false (m3 sh y : Nat) (S : List (Nat × Nat)) :
    ∀ (ms : List Nat) (st : List Nat × List Nat × Nat × Nat × Bool), st.2.2.2.2 = false →
      tloopW m3 sh y S ms st = 0
  | [], st, h => by rw [tloopW_nil, h]; rfl
  | m :: ms, st, h => by
    rw [tloopW_cons]
    apply tloopW_false m3 sh y S ms
    exact kidsK_false m3 sh y _ S m _ (by simp [h])

theorem tloop_specW (hp : P.p = 3) (hD : P.D ≤ 10) {Sv : List Refl} {root : Vec} :
    ∀ (ms : List Nat) (st : List Nat × List Nat × Nat × Nat × Bool) (T : List TE) (np : Nat),
      TInvW P Sv root T np st.1 st.2.1 st.2.2.1 st.2.2.2.1 →
      tloopW (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (Sv.map (packR P)) ms st
        ≠ 0 →
      ∃ T', TFinW P Sv root T' ∧ tloopW (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1))
        (yK P.D) (Sv.map (packR P)) ms st = T'.length
  | [], st, T, np, hI, h => by
    rw [tloopW_nil] at h ⊢
    cases hf : st.2.2.2.2
    · rw [hf] at h; exact absurd rfl h
    · exact ⟨T, ⟨hI.q3, hI.q5, hI.q6⟩, by rw [cond_true, hI.q2]⟩
  | m :: ms, st, T, np, hI, h => by
    rw [tloopW_cons] at h ⊢
    have hk : (kidsK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D)
        (popK st.1 st.2.1).1 (Sv.map (packR P)) m ((popK st.1 st.2.1).2.2.1,
        st.2.2.1, st.2.2.2.1, st.2.2.2.2 && (popK st.1 st.2.1).2.2.2)).2.2.2 = true := by
      by_contra hc
      rw [Bool.not_eq_true] at hc
      exact h (tloopW_false _ _ _ _ ms _ hc)
    have hin : (st.2.2.2.2 && (popK st.1 st.2.1).2.2.2) = true := by
      by_contra hc
      rw [Bool.not_eq_true] at hc
      rw [kidsK_false _ _ _ _ _ m _ hc] at hk
      cases hk
    have hpop := (Bool.and_eq_true _ _ ▸ hin).2
    obtain ⟨hlt, hx, hI1⟩ := pop_specW hI hpop
    rw [hx] at hk h ⊢
    obtain ⟨T1, _, hI2⟩ := kids_specW hp hD Sv 0 m _ _ _ _ T (List.drop_zero) hlt rfl hI1 hk
    exact tloop_specW hp hD ms _ T1 (np + 1) hI2 h

theorem treeK_spec (hp : P.p = 3) (hD : P.D ≤ 10) {Sv : List Refl} {b : Nat} (hb : b < P.D)
    {ms : List Nat}
    (h : treeK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (Sv.map (packR P))
      (Nat.shiftLeft 1 (Nat.mul 16 b)) ms ≠ 0) :
    ∃ T, TFinW P Sv (P.unit b) T ∧
      treeK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (Sv.map (packR P))
        (Nat.shiftLeft 1 (Nat.mul 16 b)) ms = T.length := by
  rw [treeK_eq] at h ⊢
  rw [shiftLeft_unit P hb, codeK_pk hp hD] at h ⊢
  refine tloop_specW hp hD ms _ [(P.unit b, 0, 0)] 0 ⟨by simp, rfl, by simp, ?_, ?_, rfl, by simp⟩ h
  · intro e he
    rw [List.mem_singleton.mp he]
    change (1 <<< _).testBit _ = true
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    exact decide_eq_true rfl
  · intro i hi hi0
    simp at hi
    omega

theorem levelOK_ofW [Fact P.p.Prime] (hwf : P.WF) {Dl : List CE}
    (hs : ∀ x ∈ Dl, Sem P x) {bs : List Nat} (hbs : ∀ b ∈ bs, b < P.D) {b : Nat} {idx : List Nat}
    (hidx : ∀ i ∈ idx, i < Dl.length)
    (hfix : ∀ i ∈ idx, ∀ c ∈ bs, (Dl.getD i dfl).1.f.getD c 0 % P.p = 0) {T : List TE}
    (hT : TFinW P (idx.map fun i => (Dl.getD i dfl).1) (P.unit b) T) :
    P.levelOK (bs.map P.unit) (lev P Dl b idx T) = true := by
  have hsem : ∀ i ∈ idx, Sem P (Dl.getD i dfl) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (hidx i hi)]
    exact hs _ (List.getElem_mem _)
  unfold Pt.levelOK
  simp only [lev, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro s hs'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs'
    exact sw_ok (hsem i hi)
  · intro s hs' v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    apply vecEq_of_vec
    rw [sw_act hwf (hsem i hi)]
    exact vec_of_vecEq P (refl_fix _ (hbs c hc) (hfix i hi c hc))
  · obtain ⟨t, rfl⟩ : ∃ t, T = (P.unit b, 0, 0) :: t := by
      have := hT.q6
      cases T with
      | nil => cases this
      | cons a t => exact ⟨t, by simp at this; rw [this]⟩
    exact vecEq_rfl P _
  · intro x hx
    obtain ⟨hlt, hxe⟩ := List.mem_zipIdx' hx
    rcases Nat.eq_zero_or_pos x.2 with h0 | h0
    · simp [h0]
    · obtain ⟨a1, a2, a3⟩ := hT.q5 x.2 hlt h0
      simp only [List.length_map] at a2
      rw [hxe]
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, List.length_map]
      refine Or.inr ⟨⟨a1, a2⟩, ?_⟩
      have e1 : (idx.map fun i => (Dl.getD i dfl).1).getD T[x.2].2.2 ⟨[], []⟩ =
          (Dl.getD idx[T[x.2].2.2] dfl).1 := by
        rw [List.getD_eq_getElem _ _ (by simpa using a2), List.getElem_map]
      have e2 : (idx.map fun i => sw (Dl.getD i dfl)).getD T[x.2].2.2 [] =
          sw (Dl.getD idx[T[x.2].2.2] dfl) := by
        rw [List.getD_eq_getElem _ _ (by simpa using a2), List.getElem_map]
      rw [a3, e1, e2]
      apply vecEq_of_vec
      rw [sw_act hwf (hsem _ (List.getElem_mem _))]
      rfl
  · rw [beq_iff_eq, eraseDups_of_nodup _ hT.q3, List.length_map]

theorem chainK_cons (D m3 sh y nC : Nat) (C : List (Nat × Nat)) (L : Nat × List Nat × List Nat)
    (lv : List (Nat × List Nat × List Nat)) (E prod : Nat) :
    chainK D m3 sh y nC C (L :: lv) E prod =
      bif Nat.blt L.1 D && sortedLt nC L.2.1 0 &&
          (selK L.2.1 0 C).all (fun r => Nat.beq (Nat.land r.2 E) 0) &&
          !(Nat.beq (treeK m3 sh y (selK L.2.1 0 C) (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2) 0) then
        chainK D m3 sh y nC C lv (Nat.lor E (Nat.shiftLeft 65535 (Nat.mul 16 (Nat.sub (Nat.sub D 1)
          L.1)))) (Nat.mul prod (treeK m3 sh y (selK L.2.1 0 C) (Nat.shiftLeft 1 (Nat.mul 16 L.1))
            L.2.2))
      else 0 := rfl

theorem chainK_spec [Fact P.p.Prime] (hp : P.p = 3) (hD : P.D ≤ 10) (hwf : P.WF) (Dl : List CE)
    (hs : ∀ x ∈ Dl, Sem P x) :
    ∀ (lv : List (Nat × List Nat × List Nat)) (bs : List Nat) (E prod : Nat),
      (∀ b ∈ bs, b < P.D) →
      (∀ f : Vec, Nat.land (pkrP P.p P.D f) E = 0 → ∀ b ∈ bs, f.getD b 0 % P.p = 0) →
      chainK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) Dl.length
        (Dl.map fun x => packR P x.1) lv E prod ≠ 0 →
      ∃ Ls : List Level, P.chainProd (bs.map P.unit) Ls prod =
        some (chainK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) Dl.length
          (Dl.map fun x => packR P x.1) lv E prod)
  | [], bs, E, prod, _, _, _ => ⟨[], rfl⟩
  | L :: lv, bs, E, prod, hbs, hE, h => by
    have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
    have hp' : P.p < 65536 := by omega
    rw [chainK_cons] at h ⊢
    set C := Dl.map fun x => packR P x.1 with hC
    cases hc : (Nat.blt L.1 P.D && sortedLt Dl.length L.2.1 0 &&
          (selK L.2.1 0 C).all (fun r => Nat.beq (Nat.land r.2 E) 0) &&
          !(Nat.beq (treeK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D)
            (selK L.2.1 0 C) (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2) 0))
    · rw [hc] at h
      exact absurd rfl h
    rw [hc] at h
    simp only [cond_true] at h ⊢
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', List.all_eq_true, Nat.beq_eq] at hc
    obtain ⟨⟨⟨hb, hsort⟩, hall⟩, ht0⟩ := hc
    have ht : treeK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) (selK L.2.1 0 C)
        (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2 ≠ 0 := by
      intro h0
      rw [h0] at ht0
      simp at ht0
    obtain ⟨hsel, hidx⟩ := selK_spec C Dl.length L.2.1 0 hsort
    rw [List.drop_zero] at hsel
    have hSv : selK L.2.1 0 C = (L.2.1.map fun i => (Dl.getD i dfl).1).map (packR P) := by
      rw [hsel, List.map_map]
      apply List.map_congr_left
      intro i hi
      rw [hC, List.getD_eq_getElem _ _ (by simpa using hidx i hi), List.getElem_map]
      simp only [Function.comp_apply]
      rw [List.getD_eq_getElem _ _ (hidx i hi)]
    rw [hSv] at ht h ⊢
    rw [hSv] at hall
    obtain ⟨T, hT, htl⟩ := treeK_spec hp hD hb ht
    have hfix : ∀ i ∈ L.2.1, ∀ c ∈ bs, (Dl.getD i dfl).1.f.getD c 0 % P.p = 0 := by
      intro i hi c hc
      have := hall _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, rfl⟩)
      exact hE _ this c hc
    have hE' : ∀ f : Vec, Nat.land (pkrP P.p P.D f)
        (Nat.lor E (Nat.shiftLeft 65535 (Nat.mul 16 (Nat.sub (Nat.sub P.D 1) L.1)))) = 0 →
        ∀ c ∈ bs ++ [L.1], f.getD c 0 % P.p = 0 := by
      intro f hf c hc
      obtain ⟨h1, h2⟩ := land_lor_zero hf
      rcases List.mem_append.mp hc with hc | hc
      · exact hE f h1 c hc
      · rw [List.mem_singleton.mp hc]
        exact mask_md hp0 hp' hb f h2
    have hbs' : ∀ c ∈ bs ++ [L.1], c < P.D := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hbs c hc
      · rw [List.mem_singleton.mp hc]; exact hb
    obtain ⟨Ls, hLs⟩ := chainK_spec hp hD hwf Dl hs lv (bs ++ [L.1]) _ _ hbs' hE' h
    refine ⟨lev P Dl L.1 L.2.1 T :: Ls, ?_⟩
    rw [Pt.chainProd, if_pos (levelOK_ofW hwf hs hbs hidx hfix hT)]
    rw [List.map_append, List.map_singleton] at hLs
    change P.chainProd (bs.map P.unit ++ [P.unit L.1]) Ls (prod * T.length) = _
    rw [← htl]
    exact hLs

theorem order_verify {sm : List Nat} {clo : List (Nat × Nat × Nat × Nat)}
    {lv : List (Nat × List Nat × List Nat)} {ex : List (List Nat)}
    (h : chkPt P (2, sm, clo, lv, ex) = true) : ∃ o, verify P (.order o) = true := by
  obtain ⟨hp, hD, -, hfact, hWF, hwf, Dl, hs, -, -, hk⟩ := chk_common (by norm_num) h
  change Nat.blt P.bound (chainK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D)
    Dl.length (Dl.map fun x => packR P x.1) lv 0 1) = true at hk
  rw [Nat.blt_eq] at hk
  obtain ⟨Ls, hLs⟩ := chainK_spec hp hD hWF Dl hs lv [] 0 1 (by simp) (by simp) (by omega)
  refine ⟨⟨Ls⟩, ?_⟩
  change (wfCheck P && verifyO P ⟨Ls⟩ P.bound) = true
  rw [hwf, Bool.true_and]
  unfold verifyO
  rw [List.map_nil] at hLs
  change (match P.chainProd [] Ls 1 with
    | some n => decide (P.bound < n) | none => false) = true
  rw [hLs]
  exact decide_eq_true hk

theorem wordK_spec (hp : P.p = 3) (hD : P.D ≤ 10) (Sv : List Refl) :
    ∀ (w : List Nat), (∀ l ∈ w, l < Sv.length) → ∀ v : Vec,
      wordK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (Sv.map (packR P)) w (pk P.D v) =
        pk P.D (wv P Sv w v)
  | [], _, v => rfl
  | l :: w, hw, v => by
    have hl := hw l (by simp)
    change appK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (nthK (0, 0) (Sv.map (packR P)) l)
      (wordK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (Sv.map (packR P)) w (pk P.D v)) =
      pk P.D (P.applyRefl (Sv.getD l ⟨[], []⟩) (wv P Sv w v))
    rw [wordK_spec hp hD Sv w (fun x hx => hw x (by simp [hx])) v, nthK_eq',
      List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getD_eq_getElem _ _ hl,
      packR3 hp]
    exact appKW_pk hp hD _ _ _

theorem exprCols_spec (m3 sh : Nat) (S : List (Nat × Nat)) (w : List Nat) (r : Nat × Nat) :
    ∀ k, exprCols m3 sh S w r k = true → ∀ j < k,
      wordK m3 sh S w (Nat.shiftLeft 1 (Nat.mul 16 j)) = appK m3 sh r (Nat.shiftLeft 1 (Nat.mul 16 j))
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, h, j, hj => by
    change (Nat.beq (wordK m3 sh S w (Nat.shiftLeft 1 (Nat.mul 16 k)))
      (appK m3 sh r (Nat.shiftLeft 1 (Nat.mul 16 k))) && exprCols m3 sh S w r k) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact exprCols_spec m3 sh S w r k h.2 j hj
    · exact h.1

theorem nbeqW (x y : Nat) : Nat.beq x y = (x == y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem pair_condW (x a b : Nat)
    (h : (bif Nat.beq x 2 then Nat.beq a 0 && Nat.beq b 0 else Nat.beq (Nat.mod (Nat.mul a b) 3) 1)
      = true) : (if x == 2 then a == 0 && b == 0 else (a * b) % 3 == 1) = true := by
  rw [nbeqW, nbeqW, nbeqW, nbeqW] at h
  cases hx : x == 2
  · rw [hx] at h
    exact h
  · rw [hx] at h
    exact h

theorem weyl_verify {sm : List Nat} {clo : List (Nat × Nat × Nat × Nat)}
    {lv : List (Nat × List Nat × List Nat)} {ex : List (List Nat)}
    (h : chkPt P (3, sm, clo, lv, ex) = true) : ∃ c, verify P (.weyl c) = true := by
  obtain ⟨hp, hD, -, hfact, hWF, hwf, Dl, hsem, -, -, hk⟩ := chk_common (by norm_num) h
  change wK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) Dl.length
    (P.gens.map (packR P)) (Dl.map fun x => packR P x.1) sm ex lv = true at hk
  have hp0 : 0 < P.p := (Fact.out : P.p.Prime).pos
  unfold wK at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨k2, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := hk
  have hsig : ∀ i ∈ sm, i < Dl.length := by
    intro i hi
    have := List.all_eq_true.mp k3 i hi
    rwa [Nat.blt_eq] at this
  have hsigl : sm.length = 8 := Nat.eq_of_beq_eq_true k2
  let xs := sm.map fun i => Dl.getD i dfl
  have hxs : ∀ x ∈ xs, Sem P x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [List.getD_eq_getElem _ _ (hsig i hi)]
    exact hsem _ (List.getElem_mem _)
  have hxl : xs.length = 8 := by simp [xs, hsigl]
  have hSK : sm.map (nthK (0, 0) (Dl.map fun x => packR P x.1)) = (xs.map (·.1)).map (packR P) := by
    simp only [xs, List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hsig i hi), List.getElem_map,
      Function.comp_apply, Function.comp_apply, List.getD_eq_getElem _ _ (hsig i hi)]
  rw [hSK] at k4 k5 k7
  set Sv := xs.map (·.1) with hSv
  have hSvl : Sv.length = 8 := by simp [hSv, hxl]
  have k8' : 696729599 < chainK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D)
      Dl.length (Dl.map fun x => packR P x.1) lv 0 1 := by
    rwa [Nat.blt_eq] at k8
  obtain ⟨Ls, hLs⟩ := chainK_spec hp hD hWF Dl hsem lv [] 0 1 (by simp) (by simp) (by omega)
  simp only [List.map_nil] at hLs
  have hgetx : ∀ i (hi : i < xs.length), P.vec (P.sigmaVecs xs[i].2.1 xs[i].2.2).1 =
      P.vec (Sv.getD i ⟨[], []⟩).h ∧ P.vec (P.sigmaVecs xs[i].2.1 xs[i].2.2).2 =
      P.vec (Sv.getD i ⟨[], []⟩).f := by
    intro i hi
    have e : Sv.getD i ⟨[], []⟩ = xs[i].1 := by
      simp [hSv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [e]
    exact sig_vecs (hxs _ (List.getElem_mem _))
  refine ⟨⟨4, xs.map (fun x => (x.2.1, x.2.2)), ex, ⟨Ls⟩⟩, ?_⟩
  change (wfCheck P && verifyW P _) = true
  rw [hwf, Bool.true_and]
  unfold verifyW
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨rfl, ?_⟩, ?_⟩, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩, ?_⟩
  · rw [beq_iff_eq, List.length_map]
    exact hxl
  · rw [List.all_eq_true]
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    have := hxs x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨this.1, this.2.1⟩
  · rw [List.all_eq_true]
    intro cb hcb
    simp only [List.map_map, List.mem_map] at hcb
    obtain ⟨x, hx, rfl⟩ := hcb
    have hsx := sig_vecs (hxs x hx)
    have h2 := List.all_eq_true.mp k4 (packR P x.1)
      (List.mem_map.mpr ⟨x.1, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩)
    rw [Nat.beq_eq, packR3 hp, dotKW_pk hp hD] at h2
    rw [beq_iff_eq, Function.comp_apply, dotv_congr hsx.2 hsx.1, h2, hp]
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    have k5ij := List.all_eq_true.mp (List.all_eq_true.mp k5 i hi) j hj
    rw [List.mem_range] at hi hj
    rw [Bool.or_eq_true] at k5ij ⊢
    rcases k5ij with k | k
    · left
      rw [Nat.beq_eq] at k
      rw [k, beq_self_eq_true]
    · right
      have hiS : i < Sv.length := by omega
      have hjS : j < Sv.length := by omega
      have hl : (xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2) =
          xs.map fun x => P.sigmaVecs x.2.1 x.2.2 := by
        rw [List.map_map]
        rfl
      have hgi : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).getD i
          ([], []) = P.sigmaVecs xs[i].2.1 xs[i].2.2 := by
        rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
      have hgj : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).getD j
          ([], []) = P.sigmaVecs xs[j].2.1 xs[j].2.2 := by
        rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
      have hnK : ∀ l (hl : l < Sv.length), nthK (0, 0) (Sv.map (packR P)) l =
          packR P (Sv.getD l ⟨[], []⟩) := by
        intro l hl
        rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
          List.getD_eq_getElem _ _ hl]
      have ha : dotK (Nat.mul 16 (Nat.sub P.D 1)) (nthK (0, 0) (Sv.map (packR P)) i).2
          (nthK (0, 0) (Sv.map (packR P)) j).1 =
          P.dotv (P.sigmaVecs xs[i].2.1 xs[i].2.2).2 (P.sigmaVecs xs[j].2.1 xs[j].2.2).1 := by
        rw [hnK i hiS, hnK j hjS, packR3 hp, packR3 hp, dotKW_pk hp hD,
          dotv_congr (hgetx i (by omega)).2 (hgetx j (by omega)).1]
      have hb : dotK (Nat.mul 16 (Nat.sub P.D 1)) (nthK (0, 0) (Sv.map (packR P)) j).2
          (nthK (0, 0) (Sv.map (packR P)) i).1 =
          P.dotv (P.sigmaVecs xs[j].2.1 xs[j].2.2).2 (P.sigmaVecs xs[i].2.1 xs[i].2.2).1 := by
        rw [hnK i hiS, hnK j hjS, packR3 hp, packR3 hp, dotKW_pk hp hD,
          dotv_congr (hgetx j (by omega)).2 (hgetx i (by omega)).1]
      unfold pairOK at k
      rw [ha, hb] at k
      have hpc := pair_condW _ _ _ k
      simp only [hgi, hgj, hp]
      exact hpc
  · rw [beq_iff_eq]
    have := Nat.eq_of_beq_eq_true k6
    rwa [List.length_map] at this
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨w, r⟩ := x
    have hm : (w, packR P r) ∈ ex.zip (P.gens.map (packR P)) := by
      rw [List.zip_map_right]
      exact List.mem_map.mpr ⟨(w, r), hx, rfl⟩
    have h7 := List.all_eq_true.mp k7 _ hm
    simp only [Bool.and_eq_true] at h7
    obtain ⟨hw, he⟩ := h7
    have hw' : ∀ l ∈ w, l < 8 := by
      intro l hl
      have := List.all_eq_true.mp hw l hl
      rwa [Nat.blt_eq] at this
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨hw', fun j hj => ?_⟩
    rw [List.mem_range] at hj
    have hej := exprCols_spec _ _ _ w _ P.D he j hj
    rw [shiftLeft_unit P hj, wordK_spec hp hD Sv w (fun l hl => hSvl ▸ hw' l hl), packR3 hp,
      appKW_pk hp hD] at hej
    have hv := vec_of_vecEq P ((pk_inj hp _ _).mp hej)
    apply vecEq_of_vec
    have hSMl : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).length =
        8 := by simp [hxl]
    have hSM : ∀ l (hl : l < ((xs.map fun x => (x.2.1, x.2.2)).map
        (fun s => P.sigmaVecs s.1 s.2)).length),
        P.vec ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2))[l].1 =
          P.vec (Sv.getD l ⟨[], []⟩).h ∧
        P.vec ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2))[l].2 =
          P.vec (Sv.getD l ⟨[], []⟩).f := by
      intro l hl
      simp only [List.getElem_map]
      exact hgetx l (by simpa using hl)
    rw [sigmaWord_spec _ Sv hSM w (fun l hl => hSMl ▸ hw' l hl) (P.unit j), hv]
  · unfold verifyO
    rw [hLs]
    exact decide_eq_true k8'

end CFSG.TwoNodeSmall.WitK.OK

end
