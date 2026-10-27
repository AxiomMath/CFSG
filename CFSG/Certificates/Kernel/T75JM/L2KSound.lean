module

public import Certificates.Data.Kernel.T75JM.L2K
public import CFSG.Certificates.Kernel.T75JM.PCheckKSound

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable

variable {L : Int → Nat}

theorem ap_compT (X Y : Table) {x : Nat} (hx : x < 22) : ap (compT 22 X Y) x = ap X (ap Y x) := by
  unfold Native.compT
  rw [ap_ofFn _ hx]
  rfl

theorem n0Tab_append' (hL : LetterRd L) (u v : List (Fin 6 × Bool)) :
    compT 22 (n0Tab u) (n0Tab v) = n0Tab (u ++ v) := by
  refine beq_iff_eq.1 (beq_of_ap (compT_size _ _) (size_n0Tab hL _) fun x hx => ?_)
  rw [ap_compT _ _ hx, ap_pw hL v hx, ap_pw hL u (fd_pw_lt hL v hx), ap_pw hL _ hx,
    fd_pw_append hL _ _ hx]

theorem idT_eq (hL : LetterRd L) : idT 22 = n0Tab [] := by
  refine beq_iff_eq.1 (beq_of_ap (idT_size 22) (size_n0Tab hL _) fun x hx => ?_)
  rw [ap_idT (by norm_num) hx, ap_pw hL _ hx]
  exact (CFSG.KC.N0K.hid x hx).symm

theorem eqWd_iff (w w' : List (Fin 6 × Bool)) :
    eqWd L w w' = true ↔ ∀ x < 22, fd 5 (pw L w) x = fd 5 (pw L w') x := by
  unfold eqWd eqP
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    exact Nat.eq_of_beq_eq_true (h x (List.mem_range.2 hx))
  · intro h x hx
    have e := h x (List.mem_range.1 hx)
    rw [fdN_eq, fdN_eq, e]
    exact Nat.beq_refl _

theorem beq_n0Tab (hL : LetterRd L) (w w' : List (Fin 6 × Bool)) :
    (n0Tab w == n0Tab w') = eqWd L w w' := by
  rw [Bool.eq_iff_iff, beq_iff_eq, eqWd_iff]
  constructor
  · intro h x hx
    rw [← ap_pw hL w hx, ← ap_pw hL w' hx, h]
  · intro h
    refine beq_iff_eq.1 (beq_of_ap (size_n0Tab hL w) (size_n0Tab hL w') fun x hx => ?_)
    rw [ap_pw hL w hx, ap_pw hL w' hx]
    exact h x hx

theorem contains_map_n0Tab (hL : LetterRd L) {α : Type} (l : List α) (f : α → List (Fin 6 × Bool))
    (w : List (Fin 6 × Bool)) :
    (l.map fun k => n0Tab (f k)).contains (n0Tab w) = l.any fun k => eqWd L w (f k) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.contains_cons, List.any_cons, ih, beq_n0Tab hL]

theorem tTabs_K (hL : LetterRd L) (w : List (Fin 6 × Bool)) :
    tTabs.contains (n0Tab w) = inT L w :=
  contains_map_n0Tab hL _ _ w

theorem bTabs_K (hL : LetterRd L) (w : List (Fin 6 × Bool)) :
    bTabs.contains (n0Tab w) = inB L w := by
  unfold bTabs inB tb0 tb1 tb01
  rw [idT_eq hL]
  simp only [List.contains_cons, List.contains_nil, beq_n0Tab hL]

theorem normB_K (hL : LetterRd L) (x xi : List (Fin 6 × Bool)) :
    normB (n0Tab x) (n0Tab xi) = normBK L x xi := by
  unfold normB normL normBK tConj tb0 tb1
  simp only [n0Tab_append' hL, bTabs_K hL]

theorem evalT_n0 (hL : LetterRd L) (f : Fin 2 → List (Fin 6 × Bool)) (w : List (Fin 2)) :
    evalT (fun i => n0Tab (f i)) w = n0Tab ((w.map f).flatten) := by
  have key : ∀ (w : List (Fin 2)) (u : List (Fin 6 × Bool)),
      w.foldl (fun acc k => compT 22 acc (n0Tab (f k))) (n0Tab u) =
        n0Tab (u ++ (w.map f).flatten) := by
    intro w
    induction w with
    | nil => intro u; simp
    | cons k w ih =>
      intro u
      rw [List.foldl_cons, n0Tab_append' hL, ih, List.map_cons, List.flatten_cons,
        List.append_assoc]
  unfold evalT
  rw [idT_eq hL, key, List.nil_append]

theorem evalT_tdd (hL : LetterRd L) (w : List (Fin 2)) : evalT tdd w = n0Tab (dEvalW w) :=
  evalT_n0 hL dGen w

theorem evalT_tth (hL : LetterRd L) (w : List (Fin 2)) : evalT tth w = n0Tab (thEvalW w) :=
  evalT_n0 hL dTheta w

theorem tCheck_of (hL : LetterRd L) (h : tK L = true) : tCheck = true := by
  unfold tK at h
  rw [withL_eq] at h
  unfold tCheck
  simp only [beq_n0Tab hL]
  exact h

theorem bCheck_of (hL : LetterRd L) (h : bK L = true) : bCheck = true := by
  unfold bK at h
  rw [withL_eq] at h
  unfold bCheck commTab tb0 tb1 tb01
  simp only [n0Tab_append' hL, idT_eq hL, beq_n0Tab hL, tTabs_K hL]
  exact h

theorem aRelCheck_of (hL : LetterRd L) (h : aRelK L = true) : alphaRelCheck = true := by
  unfold aRelK at h
  rw [withL_eq] at h
  unfold alphaRelCheck
  simp only [idT_eq hL, beq_n0Tab hL]
  exact h

theorem aTCheck_of (hL : LetterRd L) (h : aTK L = true) : alphaTCheck = true := by
  unfold aTK at h
  rw [withL_eq] at h
  unfold alphaTCheck
  simp only [tTabs_K hL]
  exact h

theorem dMemCheck_of (hL : LetterRd L) (h : dMemK L = true) : dMemCheck = true := by
  unfold dMemK at h
  rw [withL_eq] at h
  unfold dMemCheck tdd tth
  simp only [normB_K hL]
  exact h

theorem dRelCheck_of (hL : LetterRd L) (h : dRelK L = true) : dRelCheck = true := by
  unfold dRelK at h
  rw [withL_eq] at h
  unfold dRelCheck
  simp only [evalT_tdd hL, idT_eq hL, beq_n0Tab hL]
  exact h

theorem abCheck_of (hL : LetterRd L) (h : abK L = true) : abWordsCheck = true := by
  unfold abK at h
  rw [withL_eq] at h
  unfold abWordsCheck
  simp only [evalT_tdd hL, normB_K hL, idT_eq hL, beq_n0Tab hL, tTabs_K hL, bTabs_K hL]
  exact h

theorem thSqCheck_of (hL : LetterRd L) (h : thSqK L = true) : thetaSqCheck = true := by
  unfold thSqK at h
  rw [withL_eq] at h
  unfold thetaSqCheck
  simp only [evalT_tdd hL, evalT_tth hL]
  unfold tdd tth
  simp only [beq_n0Tab hL]
  exact h

theorem idx_pw {h1 : n0InvCheck = true} {h2 : n0RelCheck = true} (hL : LetterRd L)
    (w : List (Fin 6 × Bool)) {x : Nat} (hx : x < 22) :
    idx 22 (phiK h1 h2 (n0 w)) x = fd 5 (pw L w) x :=
  idx_phiK hL w hx

theorem n0_eq_of_eqWd (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) {w w' : List (Fin 6 × Bool)} (h : eqWd L w w' = true) : n0 w = n0 w' := by
  have h2 := n0RelCheck_of hL (n0kOk_parts hok).1
  refine phiK_injective (h2 := h2) hL h1 hok (eq_of_idx fun x hx => ?_)
  rw [idx_pw hL w hx, idx_pw hL w' hx]
  exact (eqWd_iff w w').1 h x hx

theorem inT_spec (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) {w : List (Fin 6 × Bool)} (h : inT L w = true) :
    ∃ l < 16, n0 w = n0 (tw l) := by
  obtain ⟨l, hl, e⟩ := List.any_eq_true.1 h
  exact ⟨l, List.mem_range.1 hl, n0_eq_of_eqWd hL h1 hok e⟩

theorem mem_letters6 (p : Fin 6 × Bool) : p ∈ letters6 := by
  obtain ⟨i, b⟩ := p
  fin_cases i <;> cases b <;> decide

theorem normal_of (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) (h : normalK L = true) :
    ∀ n : N0, ∀ k < 16, ∃ l < 16, n * n0 (tw k) * n⁻¹ = n0 (tw l) := by
  unfold normalK at h
  rw [withL_eq] at h
  have step : ∀ p : Fin 6 × Bool, ∀ k < 16, ∃ l < 16, n0 [p] * n0 (tw k) * (n0 [p])⁻¹ = n0 (tw l) := by
    intro p k hk
    have hp := List.all_eq_true.1 (List.all_eq_true.1 h p (mem_letters6 p)) k (List.mem_range.2 hk)
    obtain ⟨l, hl, e⟩ := inT_spec hL h1 hok hp
    refine ⟨l, hl, ?_⟩
    have hinv : (n0 [p])⁻¹ = n0 [(p.1, !p.2)] := by
      rw [← n0_invWord]
      simp [CFSG.CGT.T75JM.invWord]
    rw [hinv, ← n0_append, ← n0_append]
    exact e
  have key : ∀ w : List (Fin 6 × Bool), ∀ k < 16, ∃ l < 16, n0 w * n0 (tw k) * (n0 w)⁻¹ = n0 (tw l) := by
    intro w
    induction w with
    | nil => intro k hk; exact ⟨k, hk, by simp [n0_nil]⟩
    | cons p w ih =>
      intro k hk
      obtain ⟨l, hl, e⟩ := ih k hk
      obtain ⟨m, hm, e'⟩ := step p l hl
      refine ⟨m, hm, ?_⟩
      have hc : p :: w = [p] ++ w := rfl
      rw [hc, n0_append, ← e', ← e]
      group
  intro n k hk
  obtain ⟨a, -, k', -, rfl⟩ := n0K_surj hL h1 hok n
  exact key _ k hk

theorem substWord_append (u v : W6) : substWord (u ++ v) = substWord u ++ substWord v := by
  simp [substWord, List.flatMap_append]

theorem substWord_lift (w : W6) :
    FreeGroup.lift (fun i => n0 (alphaImg i)) (FreeGroup.mk w) = n0 (substWord w) := by
  induction w with
  | nil => simp [substWord, n0_nil, FreeGroup.lift_mk]
  | cons p w ih =>
    have e1 : FreeGroup.lift (fun i => n0 (alphaImg i)) (FreeGroup.mk (p :: w)) =
        (cond p.2 (n0 (alphaImg p.1)) (n0 (alphaImg p.1))⁻¹) *
          FreeGroup.lift (fun i => n0 (alphaImg i)) (FreeGroup.mk w) := by
      rw [FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_cons, List.prod_cons]
    have e2 : substWord (p :: w) =
        (if p.2 then alphaImg p.1 else invWord (alphaImg p.1)) ++ substWord w := by
      simp [substWord]
    rw [e1, ih, e2, n0_append]
    obtain ⟨i, b⟩ := p
    cases b <;> simp [n0_invWord]

theorem a6W_eq (a : Nat) : a6W a = a6Wl (a6Words.getD a []) := rfl

theorem alphaInj_of (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) (h : alphaK L = true) :
    ∀ w w' : List (Fin 6 × Bool), n0 (substWord w) = n0 (substWord w') → n0 w = n0 w' := by
  have h2 := n0RelCheck_of hL (n0kOk_parts hok).1
  unfold alphaK at h
  rw [withL_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hrel, hfix⟩, hA⟩, hT⟩ := h
  have hrel' : ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ rels6.map FreeGroup.mk},
      FreeGroup.lift (fun i => n0 (alphaImg i)) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [substWord_lift, ← n0_nil]
    exact n0_eq_of_eqWd hL h1 hok (List.all_eq_true.1 hrel w hw)
  let φ : N0 →* N0 := PresentedGroup.toGroup hrel'
  have hφ : ∀ w, φ (n0 w) = n0 (substWord w) := by
    intro w
    have hcomp : φ.comp (PresentedGroup.mk _) = FreeGroup.lift fun i => n0 (alphaImg i) := by
      apply FreeGroup.ext_hom
      intro i
      simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact PresentedGroup.toGroup.of _
    rw [← substWord_lift]
    exact congrArg (fun f => f (FreeGroup.mk w)) hcomp
  have hfix' : ∀ k < 16, ∀ p ∈ hexad, fd 5 (pw L (substWord (tw k))) p = p := by
    intro k hk p hp
    exact Nat.eq_of_beq_eq_true
      (List.all_eq_true.1 (List.all_eq_true.1 hfix k (List.mem_range.2 hk)) p hp)
  have hinj : Function.Injective φ := by
    intro g g' e
    obtain ⟨a, ha, k, hk, rfl⟩ := n0K_surj hL h1 hok g
    obtain ⟨b, hb, l, hl, rfl⟩ := n0K_surj hL h1 hok g'
    rw [hφ, hφ, substWord_append, substWord_append, n0_append, n0_append] at e
    have hH : ∀ p ∈ hexad, fd 5 (pw L (substWord (a6W a))) p = fd 5 (pw L (substWord (a6W b))) p := by
      intro p hp
      have hp22 : p < 22 := by simp [hexad] at hp; omega
      have := congrArg (fun g => idx 22 (phiK h1 h2 g) p) e
      simp only [map_mul, idx_mul] at this
      rw [idx_pw hL (substWord (tw k)) hp22, hfix' k hk p hp,
        idx_pw hL (substWord (tw l)) hp22, hfix' l hl p hp, idx_pw hL (substWord (a6W a)) hp22,
        idx_pw hL (substWord (a6W b)) hp22] at this
      exact this
    have hab : a = b := by
      refine eq_of_nodupA (f := fun u => keyL hexad (pw L (substWord (a6Wl u)))) hA ha hb
        (keyP_congr hexad fun p hp => ?_)
      rw [fdN_eq, fdN_eq, ← a6W_eq, ← a6W_eq]
      exact hH p hp
    subst hab
    have e' := mul_left_cancel e
    have hT' : ∀ p ∈ List.range 22,
        fdN 5 (pw L (substWord (tw k))) p = fdN 5 (pw L (substWord (tw l))) p := by
      intro p hp
      have hp22 := List.mem_range.1 hp
      rw [fdN_eq, fdN_eq, ← idx_pw (h1 := h1) (h2 := h2) hL _ hp22,
        ← idx_pw (h1 := h1) (h2 := h2) hL _ hp22, e']
    have hkl : k = l := eq_of_nodupN (f := fun k => keyL (List.range 22) (pw L (substWord (tw k))))
      hT hk hl (keyP_congr _ hT')
    subst hkl
    rfl
  intro w w' e
  rw [← hφ, ← hφ] at e
  exact hinj e

theorem idx_elem {h1 : n0InvCheck = true} {h2 : n0RelCheck = true} (hL : LetterRd L) (a : Nat)
    {k : Nat} (hk : k < 16) {x : Nat} (hx : x < 22) :
    idx 22 (phiK h1 h2 (n0 (a6W a ++ tw k))) x = fd 5 (ak L a) (fd 5 (tk L k) x) := by
  rw [idx_phiK_elem hL a hk hx, fd_pcomp (by norm_num) 5 _ _ hx]

theorem conjAt_of (hL : LetterRd L) (h1 : n0InvCheck = true) (h2 : n0RelCheck = true) {a k : Nat}
    (hk : k < 16) {v y : List (Fin 6 × Bool)}
    (e : n0 (a6W a ++ tw k) * n0 v = n0 y * n0 (a6W a ++ tw k)) :
    conjAt (ak L a) (tk L k) (pw L v) (pw L y) = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  have hx' := List.mem_range.1 hx
  have e1 := congrArg (fun g => idx 22 (phiK h1 h2 g) x) e
  simp only [map_mul, idx_mul] at e1
  have hv : fd 5 (pw L v) x < 22 := fd_pw_lt hL _ hx'
  have hz : fd 5 (ak L a) (fd 5 (tk L k) x) < 22 := by
    rw [← idx_elem (h1 := h1) (h2 := h2) hL a hk hx']
    exact idx_lt _ hx'
  rw [idx_elem hL a hk hx', idx_pw hL _ hx', idx_elem hL a hk hv, idx_pw hL _ hz] at e1
  rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq, e1]
  exact Nat.beq_refl _

theorem center_of (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) (h : centerK L = true) :
    ∀ z : N0, (∀ i : Fin 2, z * n0 (bGen i) * z⁻¹ = 1 ∨ z * n0 (bGen i) * z⁻¹ = n0 (bGen 0) ∨
      z * n0 (bGen i) * z⁻¹ = n0 (bGen 1) ∨
      z * n0 (bGen i) * z⁻¹ = n0 (bGen 0) * n0 (bGen 1)) →
    (∀ i : Fin 2, z * n0 (dGen i) = n0 (dGen i) * z) → z = 1 := by
  have h2 := n0RelCheck_of hL (n0kOk_parts hok).1
  unfold centerK at h
  rw [withL_eq] at h
  simp only [sB_eq] at h
  unfold centerE at h
  refine n0K_forall hL h1 hok _ fun a ha k hk => ?_
  intro hB hD
  have hg := allAT_spec h ha hk
  have hcz : ∀ {v y : List (Fin 6 × Bool)}, n0 (a6W a ++ tw k) * n0 v * (n0 (a6W a ++ tw k))⁻¹ =
      n0 y → conjAt (ak L a) (tk L k) (pw L v) (pw L y) = true := by
    intro v y e
    refine conjAt_of hL h1 h2 hk ?_
    rw [← e]
    group
  have hcom : ((List.range 22).all fun x => comAt (ak L a) (tk L k) (pw L (dGen 0)) x &&
      comAt (ak L a) (tk L k) (pw L (dGen 1)) x) = true := by
    have c0 := conjAt_of hL h1 h2 hk (hD 0)
    have c1 := conjAt_of hL h1 h2 hk (hD 1)
    refine List.all_eq_true.2 fun x hx => ?_
    rw [Bool.and_eq_true]
    exact ⟨List.all_eq_true.1 c0 x hx, List.all_eq_true.1 c1 x hx⟩
  have hY : ∀ i : Fin 2, ∃ Y ∈ [idn, pw L (bGen 0), pw L (bGen 1), pw L (bGen 0 ++ bGen 1)],
      conjAt (ak L a) (tk L k) (pw L (bGen i)) Y = true := by
    intro i
    rcases hB i with e | e | e | e
    · exact ⟨pw L [], List.mem_cons_self, hcz (by rw [e, n0_nil])⟩
    · exact ⟨pw L (bGen 0), by simp, hcz e⟩
    · exact ⟨pw L (bGen 1), by simp, hcz e⟩
    · exact ⟨pw L (bGen 0 ++ bGen 1), by simp,
        hcz (y := bGen 0 ++ bGen 1) (by rw [e, n0_append])⟩
  have hnb : ([pw L (bGen 0), pw L (bGen 1)].all fun P =>
      [idn, pw L (bGen 0), pw L (bGen 1), pw L (bGen 0 ++ bGen 1)].any fun Y =>
        conjAt (ak L a) (tk L k) P Y) = true := by
    refine List.all_eq_true.2 fun P hP => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · obtain ⟨Y, hYm, hc⟩ := hY 0
      exact List.any_eq_true.2 ⟨Y, hYm, hc⟩
    · obtain ⟨Y, hYm, hc⟩ := hY 1
      exact List.any_eq_true.2 ⟨Y, hYm, hc⟩
  rw [hcom, hnb] at hg
  simp only [Bool.not_true, Bool.false_or] at hg
  refine phiK_injective (h2 := h2) hL h1 hok (eq_of_idx fun x hx => ?_)
  have hx' := List.all_eq_true.1 hg x (List.mem_range.2 hx)
  rw [idx_elem hL a hk hx, map_one, idx_one]
  exact (Nat.eq_of_beq_eq_true hx').trans (CFSG.KC.N0K.hid x hx)

end CFSG.KC.N0K

end
