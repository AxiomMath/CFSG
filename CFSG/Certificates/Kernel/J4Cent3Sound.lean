module

public import Certificates.Data.Kernel.J4Cent3
public import CFSG.Certificates.Kernel.J4FiveSound

public section

namespace CFSG.KC.J4Cent3

open CFSG.KC.J4Count CFSG.KC.J4Q CFSG.KC.Loop CFSG.KC.J4Five Equiv

theorem allN_spec' {f : Nat → Bool} {n : Nat} (h : allN n f = true) : ∀ i < n, f i = true :=
  CFSG.KC.J4Five.allN_spec h

variable {B P : List Nat}

theorem oct6OK_spec {z Fl Tl : List Nat} (h : oct6OK B P z Fl Tl = true) {k : Nat} (hk : k < 6) :
    pcN (octM z Fl Tl k) 24 = 8 ∧ inC B P (octM z Fl Tl k) = true ∧
      ∀ s < 4096, pcN (combo B s) 24 = 8 →
        combo B s &&& maskL (Fl.eraseIdx k) = maskL (Fl.eraseIdx k) → combo B s = octM z Fl Tl k := by
  have e := allN_spec' h k hk
  beta_reduce at e
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at e
  obtain ⟨⟨h8, hC⟩, hall⟩ := e
  refine ⟨Nat.eq_of_beq_eq_true h8, hC, fun s hs h8' hF => ?_⟩
  have k' := all64_spec hall s (by omega)
  beta_reduce at k'
  rw [strictB_eq] at k'
  rw [orB_eq_or, Bool.or_eq_true, notB_eq, andB_eq, h8', Nat.beq_refl] at k'
  have hF' : Nat.beq (Nat.land (combo B s) (maskL (Fl.eraseIdx k))) (maskL (Fl.eraseIdx k)) =
      true := by
    change Nat.beq (combo B s &&& maskL (Fl.eraseIdx k)) _ = true
    rw [hF]
    exact Nat.beq_refl _
  rw [hF'] at k'
  rcases k' with k' | k'
  · exact absurd k' (by decide)
  · exact Nat.eq_of_beq_eq_true k'

theorem testBit_octM (z Fl Tl : List Nat) (k x : Nat) :
    (octM z Fl Tl k).testBit x = true ↔ x ∈ Fl.eraseIdx k ∨ x ∈ orb3 z (getN 0 Tl k) := by
  change (maskL (Fl.eraseIdx k) ||| maskL (orb3 z (getN 0 Tl k))).testBit x = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true, testBit_maskL, testBit_maskL]

theorem crd16OK_spec {z crd L : List Nat} (h : crd16OK z crd L = true) :
    ∀ x < 24, getN 0 crd x % 16 < 12 ∧
      zPow z (getN 0 crd x / 16) (getN 0 L (getN 0 crd x % 16)) = x := by
  intro x hx
  have k := allN_spec' h x hx
  change andB (Nat.blt (getN 0 crd x % 16) 12)
    (Nat.beq (zPow z (getN 0 crd x / 16) (getN 0 L (getN 0 crd x % 16))) x) = true at k
  rw [andB_eq, Bool.and_eq_true] at k
  exact ⟨Nat.le_of_ble_eq_true k.1, Nat.eq_of_beq_eq_true k.2⟩

theorem bld16_eq {z crd L : List Nat} {ξ h : Perm (Fin 24)} (hz : ∀ i < 24, pf ξ i = getN 0 z i)
    (hcrd : crd16OK z crd L = true) (hlen : L.length = 12) (hlt : ∀ x ∈ L, x < 24)
    (hc : Commute h ξ) {x : Nat} (hx : x < 24) : bld16 z crd (L.map (pf h)) x = pf h x := by
  obtain ⟨hi, hxe⟩ := crd16OK_spec hcrd x hx
  have hmem := getN_mem' (l := L) (i := getN 0 crd x % 16) (by omega)
  have hL := hlt _ hmem
  change zPow z (getN 0 crd x / 16) (getN 0 (L.map (pf h)) (getN 0 crd x % 16)) = _
  rw [getN_map _ (by omega), zPow_pf hz _ (pf_lt _ hL), ← pf_mul _ _ hL,
    ((hc.pow_right (getN 0 crd x / 16)).eq).symm, pf_mul _ _ hL, ← zPow_pf hz _ hL, hxe]

theorem mem_prodL {AL : List (List Nat)} {l : List Nat}
    (h : List.Forall₂ (fun x A => x ∈ A) l AL) : l ∈ prodL AL := by
  induction h with
  | nil => exact List.mem_singleton_self _
  | cons hx _ ih =>
    rw [prodL, List.mem_flatMap]
    exact ⟨_, hx, List.mem_map.2 ⟨_, ih, rfl⟩⟩

theorem swap_cases {g : Perm (Fin 24)} {f0 f1 f2 f3 f4 f5 : Nat}
    (hlt : f0 < 24 ∧ f1 < 24 ∧ f2 < 24 ∧ f3 < 24 ∧ f4 < 24 ∧ f5 < 24)
    (hd : f0 ≠ f4 ∧ f1 ≠ f4 ∧ f2 ≠ f4 ∧ f3 ≠ f4 ∧ f0 ≠ f5 ∧ f1 ≠ f5 ∧ f2 ≠ f5 ∧ f3 ≠ f5 ∧ f4 ≠ f5)
    (h0 : pf g f0 = f0) (h1 : pf g f1 = f1) (h2 : pf g f2 = f2) (h3 : pf g f3 = f3)
    (m4 : pf g f4 ∈ [f0, f1, f2, f3, f4, f5]) (m5 : pf g f5 ∈ [f0, f1, f2, f3, f4, f5]) :
    (pf g f4 = f4 ∧ pf g f5 = f5) ∨ (pf g f4 = f5 ∧ pf g f5 = f4) := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := hlt
  have inj := pf_inj g
  have c : ∀ a, a < 24 → a ≠ f0 → a ≠ f1 → a ≠ f2 → a ≠ f3 → pf g a ∈ [f0, f1, f2, f3, f4, f5] →
      pf g a = f4 ∨ pf g a = f5 := by
    intro a ha n0 n1 n2 n3 m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with e | e | e | e | e | e
    · exact absurd (inj a ha f0 l0 (e.trans h0.symm)) n0
    · exact absurd (inj a ha f1 l1 (e.trans h1.symm)) n1
    · exact absurd (inj a ha f2 l2 (e.trans h2.symm)) n2
    · exact absurd (inj a ha f3 l3 (e.trans h3.symm)) n3
    · exact Or.inl e
    · exact Or.inr e
  obtain ⟨d04, d14, d24, d34, d05, d15, d25, d35, d45⟩ := hd
  have c4 := c f4 l4 (Ne.symm d04) (Ne.symm d14) (Ne.symm d24) (Ne.symm d34) m4
  have c5 := c f5 l5 (Ne.symm d05) (Ne.symm d15) (Ne.symm d25) (Ne.symm d35) m5
  have hne : pf g f4 ≠ pf g f5 := fun e => d45 (inj f4 l4 f5 l5 e)
  rcases c4 with e4 | e4 <;> rcases c5 with e5 | e5
  · exact absurd (e4.trans e5.symm) hne
  · exact Or.inl ⟨e4, e5⟩
  · exact Or.inr ⟨e4, e5⟩
  · exact absurd (e4.trans e5.symm) hne

theorem card_cent3_le (G : Subgroup (Perm (Fin 24))) {n : Nat} {z crd : List Nat}
    {f0 f1 f2 f3 f4 f5 t0 t1 t2 t3 t4 t5 : Nat} {Fl Tl : List Nat}
    (hFl : Fl = [f0, f1, f2, f3, f4, f5]) (hTl : Tl = [t0, t1, t2, t3, t4, t5])
    (hlen : P.length = B.length) (hB : B.length = 12) (hinv : invOK B P = true)
    (hG : ∀ g ∈ G, genOK B P (pf g) = true)
    {ξ : Perm (Fin 24)} (hξ : ξ ∈ G) (hz : ∀ i < 24, pf ξ i = getN 0 z i)
    (hfix : fixOK z Fl = true) (hoct : oct6OK B P z Fl Tl = true)
    (hcrd : crd16OK z crd (Fl ++ Tl) = true) (hcand : cand3N B P z crd Fl Tl = n)
    (hd : distB (Fl ++ Tl) = true) (hlt : ∀ x ∈ Fl ++ Tl, x < 24) :
    Nat.card ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24)))) ≤ 360 * (3 * n) := by
  classical
  subst hFl hTl
  simp only [List.cons_append, List.nil_append] at hcrd hd hlt
  have hinv' : ∀ m < 2 ^ B.length, decode P (combo B m) = m := fun m hm =>
    invOK_spec hinv m (by rw [hB] at hm; norm_num at hm; omega)
  have hlt' := hlt
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt'
  obtain ⟨l0, l1, l2, l3, l4, l5, u0, u1, u2, u3, u4, u5⟩ := hlt'
  set Fl : List Nat := [f0, f1, f2, f3, f4, f5] with hFl
  set Tl : List Nat := [t0, t1, t2, t3, t4, t5] with hTl
  set L : List Nat := [f0, f1, f2, f3, f4, f5, t0, t1, t2, t3, t4, t5] with hL
  have hLe : L = Fl ++ Tl := rfl
  have hnd : (Fl ++ Tl).Nodup := hLe ▸ distB_spec hd
  have hne : ∀ i j : Nat, (hi : i < 12) → (hj : j < 12) → i ≠ j → L[i] ≠ L[j] :=
    fun i j hi hj hij e => hij ((List.Nodup.getElem_inj_iff (hLe ▸ hnd)).1 e)
  have hdisj : ∀ x ∈ Tl, x ∉ Fl := fun x hx hx' => List.disjoint_of_nodup_append hnd hx' hx
  have hFl24 : ∀ x ∈ Fl, x < 24 := fun x hx => hlt x (hLe ▸ List.mem_append_left Tl hx)
  have hTl24' : ∀ x ∈ Tl, x < 24 := fun x hx => hlt x (hLe ▸ List.mem_append_right Fl hx)
  have hF : ∀ x < 24, (pf ξ x = x ↔ x ∈ Fl) := fun x hx => by
    rw [hz x hx]
    exact (fixOK_spec hfix x hx).2
  have hFg : ∀ g : Perm (Fin 24), Commute g ξ → ∀ x ∈ Fl, pf g x ∈ Fl := by
    intro g hc x hx
    have hx24 := hFl24 x hx
    rw [← hF _ (pf_lt g hx24), ← pf_mul _ _ hx24, ← hc.eq, pf_mul _ _ hx24, (hF x hx24).2 hx]
  have hNF : ∀ g : Perm (Fin 24), Commute g ξ → ∀ x < 24, x ∉ Fl → pf g x ∉ Fl := by
    intro g hc x hx hxF hm
    have e1 := (hF _ (pf_lt g hx)).2 hm
    rw [← pf_mul _ _ hx, ← hc.eq, pf_mul _ _ hx] at e1
    exact hxF ((hF x hx).1 (pf_inj g _ (pf_lt ξ hx) _ hx e1))
  have g0 : getN 0 Tl 0 = t0 := rfl
  have g1 : getN 0 Tl 1 = t1 := rfl
  have g2 : getN 0 Tl 2 = t2 := rfl
  have g3 : getN 0 Tl 3 = t3 := rfl
  have g4 : getN 0 Tl 4 = t4 := rfl
  have g5 : getN 0 Tl 5 = t5 := rfl
  have e0 : getN 0 Fl 0 = f0 := rfl
  have e1 : getN 0 Fl 1 = f1 := rfl
  have e2 : getN 0 Fl 2 = f2 := rfl
  have e3 : getN 0 Fl 3 = f3 := rfl
  have e4 : getN 0 Fl 4 = f4 := rfl
  have e5 : getN 0 Fl 5 = f5 := rfl
  have hTl24 : ∀ k < 6, getN 0 Tl k < 24 ∧ getN 0 Tl k ∉ Fl := fun k hk =>
    have hm : getN 0 Tl k ∈ Tl := getN_mem' (l := Tl) (by rw [hTl]; simpa using hk)
    ⟨hTl24' _ hm, hdisj _ hm⟩
  have hoctI : ∀ g ∈ G, ∀ k < 6, ∀ k' < 6, Fl.eraseIdx k' ⊆ (Fl.eraseIdx k).map (pf g) →
      imgF (pf g) (octM z Fl Tl k) = octM z Fl Tl k' := by
    intro g hgG k hk k' hk' hsub
    obtain ⟨h8, hC, -⟩ := oct6OK_spec hoct hk
    obtain ⟨-, -, huniq⟩ := oct6OK_spec hoct hk'
    have hinC := inC_img hlen hinv' (pf_inj g) (hG g hgG) hC
    obtain ⟨s, hs, hsa⟩ := (inC_iff hlen hinv' _).1 hinC
    have hs' : s < 4096 := by rw [hB] at hs; norm_num at hs; omega
    have h8' : pcN (combo B s) 24 = 8 := by
      rw [hsa, pc_imgF (fun i hi => pf_lt g hi) (pf_inj g), h8]
    have hland : combo B s &&& maskL (Fl.eraseIdx k') = maskL (Fl.eraseIdx k') := by
      apply Nat.eq_of_testBit_eq
      intro y
      rw [Nat.testBit_and]
      cases hy : (maskL (Fl.eraseIdx k')).testBit y
      · simp
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hsub ((testBit_maskL _ _).1 hy))
        have hx24 := hFl24 x (List.mem_of_mem_eraseIdx hx)
        have hxO : (octM z Fl Tl k).testBit x = true := (testBit_octM _ _ _ _ _).2 (Or.inl hx)
        rw [hsa, testBit_imgF_app (pf_inj g) hx24, hxO]
        rfl
    rw [← hsa]
    exact huniq s hs' h8' hland
  have hTk : ∀ g ∈ G, Commute g ξ → ∀ k < 6, ∀ k' < 6,
      Fl.eraseIdx k' ⊆ (Fl.eraseIdx k).map (pf g) → pf g (getN 0 Tl k) ∈ orb3 z (getN 0 Tl k') := by
    intro g hgG hc k hk k' hk' hsub
    have e := hoctI g hgG k hk k' hk' hsub
    obtain ⟨ht24, htF⟩ := hTl24 k hk
    have hb : (octM z Fl Tl k).testBit (getN 0 Tl k) = true :=
      (testBit_octM _ _ _ _ _).2 (Or.inr List.mem_cons_self)
    have hb' := testBit_imgF_app (pf_inj g) ht24 (octM z Fl Tl k)
    rw [e, hb, testBit_octM] at hb'
    rcases hb' with h | h
    · exact absurd (List.mem_of_mem_eraseIdx h) (hNF g hc _ ht24 htF)
    · exact h
  set C := G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24))) with hCdef
  have hcomm : ∀ g : ↥C, Commute (g : Perm (Fin 24)) ξ := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
  have hmemG : ∀ g : ↥C, (g : Perm (Fin 24)) ∈ G := fun g => (Subgroup.mem_inf.1 g.2).1
  have hFlen : Fl.length = 6 := by rw [hFl]; rfl
  let b : Fin 4 → Fin 24 := fun i =>
    ⟨Fl[i.val]'(by rw [hFlen]; omega), hFl24 _ (List.getElem_mem _)⟩
  have hfixb : ∀ g : ↥(MulAction.stabilizer ↥C b), pf (g : Perm (Fin 24)) f0 = f0 ∧
      pf (g : Perm (Fin 24)) f1 = f1 ∧ pf (g : Perm (Fin 24)) f2 = f2 ∧
      pf (g : Perm (Fin 24)) f3 = f3 := by
    intro g
    have hg : (g : ↥C) • b = b := g.2
    have e : ∀ i : Fin 4, ((g : ↥C) : Perm (Fin 24)) (b i) = b i := fun i => congrFun hg i
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pf_fin' _ l0]; exact congrArg Fin.val (e 0)
    · rw [pf_fin' _ l1]; exact congrArg Fin.val (e 1)
    · rw [pf_fin' _ l2]; exact congrArg Fin.val (e 2)
    · rw [pf_fin' _ l3]; exact congrArg Fin.val (e 3)
  have hswap : ∀ h : Perm (Fin 24), Commute h ξ → pf h f0 = f0 → pf h f1 = f1 → pf h f2 = f2 →
      pf h f3 = f3 → (pf h f4 = f4 ∧ pf h f5 = f5) ∨ (pf h f4 = f5 ∧ pf h f5 = f4) := by
    intro h hc h0 h1 h2 h3
    exact swap_cases ⟨l0, l1, l2, l3, l4, l5⟩
      ⟨hne 0 4 (by decide) (by decide) (by decide), hne 1 4 (by decide) (by decide) (by decide),
        hne 2 4 (by decide) (by decide) (by decide), hne 3 4 (by decide) (by decide) (by decide),
        hne 0 5 (by decide) (by decide) (by decide), hne 1 5 (by decide) (by decide) (by decide),
        hne 2 5 (by decide) (by decide) (by decide), hne 3 5 (by decide) (by decide) (by decide),
        hne 4 5 (by decide) (by decide) (by decide)⟩ h0 h1 h2 h3
      (hFg h hc f4 (by simp [hFl])) (hFg h hc f5 (by simp [hFl]))
  have hsubk : ∀ h : Perm (Fin 24), Commute h ξ → pf h f0 = f0 → pf h f1 = f1 →
      pf h f2 = f2 → pf h f3 = f3 → ∀ k < 4,
      Fl.eraseIdx k ⊆ (Fl.eraseIdx k).map (pf h) := by
    intro h hc h0 h1 h2 h3 k hk
    rcases hswap h hc h0 h1 h2 h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;>
      interval_cases k <;>
      · intro y hy
        simp only [hFl, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.map_cons,
          List.map_nil, List.mem_cons, List.not_mem_nil, or_false, h0, h1, h2, h3, h4, h5] at hy ⊢
        omega
  have hsub45 : ∀ h : Perm (Fin 24), Commute h ξ → pf h f0 = f0 → pf h f1 = f1 →
      pf h f2 = f2 → pf h f3 = f3 → ∀ k, 4 ≤ k → k < 6 →
      ∃ k', 4 ≤ k' ∧ k' < 6 ∧ Fl.eraseIdx k' ⊆ (Fl.eraseIdx k).map (pf h) := by
    intro h hc h0 h1 h2 h3 k hk4 hk6
    rcases hswap h hc h0 h1 h2 h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · refine ⟨k, hk4, hk6, ?_⟩
      interval_cases k <;>
      · intro y hy
        simp only [hFl, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.map_cons,
          List.map_nil, List.mem_cons, List.not_mem_nil, or_false, h0, h1, h2, h3, h4, h5] at hy ⊢
        omega
    · refine ⟨9 - k, by omega, by omega, ?_⟩
      interval_cases k <;>
      · intro y hy
        simp only [hFl, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.map_cons,
          List.map_nil, List.mem_cons, List.not_mem_nil, or_false, h0, h1, h2, h3, h4, h5,
          show 9 - 4 = 5 from rfl, show 9 - 5 = 4 from rfl] at hy ⊢
        omega
  have key : ∀ g : ↥(MulAction.stabilizer ↥C b), ∃ j : Fin 3,
      pf ((ξ ^ (j : Nat))⁻¹ * ((g : ↥C) : Perm (Fin 24))) t0 = t0 := by
    intro g
    obtain ⟨h0, h1, h2, h3⟩ := hfixb g
    have hm := hTk _ (hmemG g) (hcomm g) 0 (by norm_num) 0 (by norm_num)
      (hsubk _ (hcomm g) h0 h1 h2 h3 0 (by norm_num))
    rw [g0, orb3] at hm
    have hz0 : ∀ j : Nat, zPow z j t0 = pf (ξ ^ j) t0 := fun j => zPow_pf hz j u0
    have hj : ∃ j : Fin 3, pf ((g : ↥C) : Perm (Fin 24)) t0 = zPow z j t0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e | e | e
      · exact ⟨0, e⟩
      · exact ⟨1, e⟩
      · exact ⟨2, e⟩
    obtain ⟨j, hj⟩ := hj
    refine ⟨j, ?_⟩
    rw [pf_mul _ _ u0, hj, hz0, pf_inv_pf _ u0]
  choose Jf hJ using key
  have hpw : ∀ j : Nat, ∀ x ∈ Fl, pf (ξ ^ j)⁻¹ x = x := by
    intro j x hx
    have hx24 := hFl24 x hx
    have e : pf (ξ ^ j) x = x := by
      induction j with
      | zero => rw [pow_zero, pf_one hx24]
      | succ j ih => rw [pow_succ', pf_mul _ _ hx24, ih, (hF x hx24).2 hx]
    calc pf (ξ ^ j)⁻¹ x = pf (ξ ^ j)⁻¹ (pf (ξ ^ j) x) := by rw [e]
      _ = x := pf_inv_pf _ hx24
  let hN : ↥(MulAction.stabilizer ↥C b) → Perm (Fin 24) := fun g =>
    (ξ ^ (Jf g : Nat))⁻¹ * ((g : ↥C) : Perm (Fin 24))
  have hNG : ∀ g, hN g ∈ G := fun g => G.mul_mem (G.inv_mem (G.pow_mem hξ _)) (hmemG g)
  have hNc : ∀ g, Commute (hN g) ξ := fun g =>
    ((Commute.refl ξ).pow_left _).inv_left.mul_left (hcomm g)
  have hNf : ∀ g, pf (hN g) f0 = f0 ∧ pf (hN g) f1 = f1 ∧ pf (hN g) f2 = f2 ∧ pf (hN g) f3 = f3 := by
    intro g
    obtain ⟨h0, h1, h2, h3⟩ := hfixb g
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pf_mul _ _ l0, h0]
      exact hpw _ _ (by rw [hFl]; exact List.mem_cons_self)
    · rw [pf_mul _ _ l1, h1]
      exact hpw _ _ (by rw [hFl]; simp)
    · rw [pf_mul _ _ l2, h2]
      exact hpw _ _ (by rw [hFl]; simp)
    · rw [pf_mul _ _ l3, h3]
      exact hpw _ _ (by rw [hFl]; simp)
  set Lst := (cands3 z Fl Tl).filter fun c => genOK B P (bld16 z crd c) with hLst
  have hmemL : ∀ g, L.map (pf (hN g)) ∈ Lst := by
    intro g
    obtain ⟨h0, h1, h2, h3⟩ := hNf g
    have ht0 : pf (hN g) t0 = t0 := hJ g
    rw [hLst, List.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [cands3]
      apply mem_prodL
      have m1 := hTk _ (hNG g) (hNc g) 1 (by norm_num) 1 (by norm_num)
        (hsubk _ (hNc g) h0 h1 h2 h3 1 (by norm_num))
      have m2 := hTk _ (hNG g) (hNc g) 2 (by norm_num) 2 (by norm_num)
        (hsubk _ (hNc g) h0 h1 h2 h3 2 (by norm_num))
      have m3 := hTk _ (hNG g) (hNc g) 3 (by norm_num) 3 (by norm_num)
        (hsubk _ (hNc g) h0 h1 h2 h3 3 (by norm_num))
      have m45 : ∀ k, 4 ≤ k → k < 6 → pf (hN g) (getN 0 Tl k) ∈
          orb3 z (getN 0 Tl 4) ++ orb3 z (getN 0 Tl 5) := by
        intro k hk4 hk6
        obtain ⟨k', hk'4, hk'6, hs⟩ := hsub45 _ (hNc g) h0 h1 h2 h3 k hk4 hk6
        have m := hTk _ (hNG g) (hNc g) k hk6 k' hk'6 hs
        rw [List.mem_append]
        interval_cases k'
        · exact Or.inl m
        · exact Or.inr m
      have m4 := m45 4 (by norm_num) (by norm_num)
      have m5 := m45 5 (by norm_num) (by norm_num)
      have hs := hswap _ (hNc g) h0 h1 h2 h3
      rw [allow3, e0, e1, e2, e3, e4, e5, g0, g1, g2, g3, g4, g5]
      rw [g1] at m1
      rw [g2] at m2
      rw [g3] at m3
      rw [g4, g5] at m4 m5
      simp only [hL, List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff,
        and_true,
        List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨h0, h1, h2, h3, by omega, by omega, ht0, m1, m2, m3, m4, m5⟩
    · rw [genOK_congr (g := pf (hN g))
        (fun x hx => bld16_eq hz hcrd (by simp [hL]) hlt (hNc g) hx)]
      exact hG _ (hNG g)
  have hinj : ∀ h h' : Perm (Fin 24), Commute h ξ → Commute h' ξ →
      L.map (pf h) = L.map (pf h') → h = h' := by
    intro h h' hc hc' e
    refine pf_ext fun x hx => ?_
    rw [← bld16_eq hz hcrd (by simp [hL]) hlt hc hx, ← bld16_eq hz hcrd (by simp [hL]) hlt hc' hx, e]
  let Φ : ↥(MulAction.stabilizer ↥C b) → Fin 3 × ↥Lst.toFinset :=
    fun g => (Jf g, ⟨L.map (pf (hN g)), List.mem_toFinset.2 (hmemL g)⟩)
  have hΦ : Function.Injective Φ := by
    intro g g' e
    have e1 : Jf g = Jf g' := congrArg Prod.fst e
    have e2 := congrArg (fun p => (p.2 : List Nat)) e
    simp only [Φ] at e2
    have e3 := hinj _ _ (hNc g) (hNc g') e2
    simp only [hN] at e3
    rw [e1] at e3
    exact Subtype.ext (Subtype.ext (mul_left_cancel e3))
  have hstab : Nat.card ↥(MulAction.stabilizer ↥C b) ≤ 3 * n := by
    calc Nat.card ↥(MulAction.stabilizer ↥C b) ≤ Nat.card (Fin 3 × ↥Lst.toFinset) :=
          Nat.card_le_card_of_injective Φ hΦ
      _ = 3 * Lst.toFinset.card := by
          rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
            Fintype.card_coe]
      _ ≤ 3 * Lst.length := Nat.mul_le_mul_left _ (List.toFinset_card_le _)
      _ = 3 * n := by rw [← hcand]; rfl
  let SF := {x : Fin 24 // (x : Nat) ∈ Fl}
  have hFnd : Fl.Nodup := (List.nodup_append.1 hnd).1
  have hSF : Fintype.card SF = 6 := by
    let φ : Fin 6 → SF := fun i =>
      ⟨⟨Fl[i.val]'(by rw [hFl]; simp), hFl24 _ (List.getElem_mem _)⟩, List.getElem_mem _⟩
    have hφ : Function.Bijective φ := by
      refine ⟨fun i j e => ?_, fun x => ?_⟩
      · have e' : Fl[i.val]'(by rw [hFl]; simp) = Fl[j.val]'(by rw [hFl]; simp) :=
          congrArg Fin.val (congrArg Subtype.val e)
        exact Fin.ext ((List.Nodup.getElem_inj_iff hFnd).1 e')
      · obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 x.2
        refine ⟨⟨k, by rw [hFl] at hk; simpa using hk⟩, Subtype.ext (Fin.ext ?_)⟩
        exact e
    rw [← Fintype.card_of_bijective hφ, Fintype.card_fin]
  have hb : Function.Injective b := by
    intro i j e
    exact Fin.ext ((List.Nodup.getElem_inj_iff hFnd).1 (congrArg Fin.val e))
  have horb : MulAction.orbit ↥C b ⊆ Set.range (fun e : Fin 4 ↪ SF => fun i => (e i).1) := by
    rintro _ ⟨g, rfl⟩
    have hmem : ∀ i, ((g : Perm (Fin 24)) (b i) : Nat) ∈ Fl := fun i => by
      rw [← pf_fin]
      exact hFg _ (hcomm g) _ (List.getElem_mem _)
    refine ⟨⟨fun i => ⟨(g : Perm (Fin 24)) (b i), hmem i⟩, fun i j e => ?_⟩, ?_⟩
    · have e' := congrArg Subtype.val e
      exact hb ((g : Perm (Fin 24)).injective e')
    · funext i
      rfl
  have horb' : (MulAction.orbit ↥C b).ncard ≤ 360 := by
    calc (MulAction.orbit ↥C b).ncard
        ≤ (Set.range (fun e : Fin 4 ↪ SF => fun i => (e i).1)).ncard :=
          Set.ncard_le_ncard horb (Set.finite_range _)
      _ = Nat.card (Set.range (fun e : Fin 4 ↪ SF => fun i => (e i).1)) :=
          (Nat.card_coe_set_eq _).symm
      _ ≤ Nat.card (Fin 4 ↪ SF) := Finite.card_range_le _
      _ = 360 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, hSF, Fintype.card_fin]
          rfl
  have e := Subgroup.card_mul_index (MulAction.stabilizer ↥C b)
  rw [MulAction.index_stabilizer] at e
  rw [← e]
  calc Nat.card ↥(MulAction.stabilizer ↥C b) * (MulAction.orbit ↥C b).ncard
      ≤ (3 * n) * 360 := Nat.mul_le_mul hstab horb'
    _ = 360 * (3 * n) := Nat.mul_comm _ _

end CFSG.KC.J4Cent3

end
