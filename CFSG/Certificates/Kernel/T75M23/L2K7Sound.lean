module

public import Certificates.Data.Kernel.T75M23.L2K7
public import CFSG.Certificates.Kernel.T75M23.P7KSound

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable

variable {L : Int → Nat}

theorem ap_compT (X Y : Table) {x : Nat} (hx : x < 23) : ap (compT 23 X Y) x = ap X (ap Y x) := by
  unfold Native.compT
  rw [ap_ofFn _ hx]
  rfl

theorem n7Tab_append' (hL : LetterRd L) (u v : List (Fin 6 × Bool)) :
    compT 23 (n7Tab u) (n7Tab v) = n7Tab (u ++ v) := by
  refine beq_iff_eq.1 (beq_of_ap (compT_size _ _) (size_n7Tab hL _) fun x hx => ?_)
  rw [ap_compT _ _ hx, ap_pw hL v hx, ap_pw hL u (fd_pw_lt hL v hx), ap_pw hL _ hx,
    fd_pw_append hL _ _ hx]

theorem idT_eq (hL : LetterRd L) : idT 23 = n7Tab [] := by
  refine beq_iff_eq.1 (beq_of_ap (idT_size 23) (size_n7Tab hL _) fun x hx => ?_)
  rw [ap_idT (by norm_num) hx, ap_pw hL _ hx]
  exact (hid x hx).symm

theorem eqWd_iff (w w' : List (Fin 6 × Bool)) :
    eqWd L w w' = true ↔ ∀ x < 23, fd 5 (pw L w) x = fd 5 (pw L w') x := by
  unfold eqWd eqP
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    exact Nat.eq_of_beq_eq_true (h x (List.mem_range.2 hx))
  · intro h x hx
    have e := h x (List.mem_range.1 hx)
    rw [fdN_eq, fdN_eq, e]
    exact Nat.beq_refl _

theorem beq_n7Tab (hL : LetterRd L) (w w' : List (Fin 6 × Bool)) :
    (n7Tab w == n7Tab w') = eqWd L w w' := by
  rw [Bool.eq_iff_iff, beq_iff_eq, eqWd_iff]
  constructor
  · intro h x hx
    rw [← ap_pw hL w hx, ← ap_pw hL w' hx, h]
  · intro h
    refine beq_iff_eq.1 (beq_of_ap (size_n7Tab hL w) (size_n7Tab hL w') fun x hx => ?_)
    rw [ap_pw hL w hx, ap_pw hL w' hx]
    exact h x hx

theorem contains_map_n7Tab (hL : LetterRd L) {α : Type} (l : List α)
    (f : α → List (Fin 6 × Bool)) (w : List (Fin 6 × Bool)) :
    (l.map fun k => n7Tab (f k)).contains (n7Tab w) = l.any fun k => eqWd L w (f k) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.contains_cons, List.any_cons, ih, beq_n7Tab hL]

theorem tTabs_K (hL : LetterRd L) (w : List (Fin 6 × Bool)) :
    tTabs7.contains (n7Tab w) = inT L w :=
  contains_map_n7Tab hL _ _ w

theorem tTabs7_all (f : Table → Bool) :
    tTabs7.all f = (List.range 16).all fun l => f (n7Tab (tw7 l)) := by
  unfold tTabs7
  rw [List.all_map]
  rfl

theorem bTabs_K (hL : LetterRd L) (w : List (Fin 6 × Bool)) :
    bTabs7.contains (n7Tab w) = inB L w := by
  unfold bTabs7 inB bt0 bt1 bt01
  rw [idT_eq hL]
  simp only [List.contains_cons, List.contains_nil, beq_n7Tab hL]

theorem normB_K (hL : LetterRd L) (x xi : List (Fin 6 × Bool)) :
    normB7 (n7Tab x) (n7Tab xi) = normBK L x xi := by
  unfold normB7 normL7 normBK tConj7 bt0 bt1
  simp only [n7Tab_append' hL, bTabs_K hL]

theorem evalT_n7 (hL : LetterRd L) (f : Fin 3 → List (Fin 6 × Bool)) (w : List (Fin 3)) :
    evalT7 (fun i => n7Tab (f i)) w = n7Tab ((w.map f).flatten) := by
  have key : ∀ (w : List (Fin 3)) (u : List (Fin 6 × Bool)),
      w.foldl (fun acc k => compT 23 acc (n7Tab (f k))) (n7Tab u) =
        n7Tab (u ++ (w.map f).flatten) := by
    intro w
    induction w with
    | nil => intro u; simp
    | cons k w ih =>
      intro u
      rw [List.foldl_cons, n7Tab_append' hL, ih, List.map_cons, List.flatten_cons,
        List.append_assoc]
  unfold evalT7
  rw [idT_eq hL, key, List.nil_append]

theorem evalT_tdd (hL : LetterRd L) (w : List (Fin 3)) : evalT7 tdd7 w = n7Tab (dEvalW7 w) :=
  evalT_n7 hL dGen7 w

theorem evalT_tth (hL : LetterRd L) (k : Fin 2) (w : List (Fin 3)) :
    evalT7 (tth7 k) w = n7Tab (thEvalW7 k w) :=
  evalT_n7 hL (thetaW7 k) w

theorem tCheck7_of (hL : LetterRd L) (h : tK L = true) : tCheck7 = true := by
  unfold tK at h
  rw [withL_eq] at h
  unfold tCheck7
  simp only [beq_n7Tab hL]
  exact h

theorem bCheck7_of (hL : LetterRd L) (h : bK L = true) : bCheck7 = true := by
  unfold bK at h
  rw [withL_eq] at h
  unfold bCheck7 commTab7 bt0 bt1 bt01
  simp only [n7Tab_append' hL, idT_eq hL, beq_n7Tab hL, tTabs_K hL]
  exact h

theorem normalCheck7_of (hL : LetterRd L) (h : normalK L = true) : normalCheck7 = true := by
  unfold normalK at h
  rw [withL_eq] at h
  unfold normalCheck7
  simp only [tTabs7_all]
  unfold tConj7 genTab7
  simp only [n7Tab_append' hL, tTabs_K hL]
  exact h

theorem dMemCheck7_of (hL : LetterRd L) (h : dMemK L = true) : dMemCheck7 = true := by
  unfold dMemK at h
  rw [withL_eq] at h
  unfold dMemCheck7 tdd7 tth7 td0_7
  simp only [normB_K hL]
  exact h

theorem dRelCheck7_of (hL : LetterRd L) (h : dRelK L = true) : dRelCheck7 = true := by
  unfold dRelK at h
  rw [withL_eq] at h
  unfold dRelCheck7
  simp only [evalT_tdd hL, idT_eq hL, beq_n7Tab hL]
  exact h

theorem abCheck7_of (hL : LetterRd L) (h : abK L = true) : abWordsCheck7 = true := by
  unfold abK at h
  rw [withL_eq] at h
  unfold abWordsCheck7
  simp only [evalT_tdd hL, normB_K hL, idT_eq hL, beq_n7Tab hL, tTabs_K hL, bTabs_K hL]
  exact h

theorem thSqCheck7_of (hL : LetterRd L) (h : thSqK L = true) : thetaSqCheck7 = true := by
  unfold thSqK at h
  rw [withL_eq] at h
  unfold thetaSqCheck7
  simp only [evalT_tdd hL, evalT_tth hL]
  unfold tth7 td0_7 tdd7 tConj7
  simp only [n7Tab_append' hL, beq_n7Tab hL]
  exact h

theorem idxK_pw {h1 : n7InvCheck = true} {h2 : n7RelCheck = true} (hL : LetterRd L)
    (w : List (Fin 6 × Bool)) {x : Nat} (hx : x < 23) :
    idx 23 (phiK h1 h2 (n7 w)) x = fd 5 (pw L w) x := by
  rw [phiK_n7]
  exact idx_img h1 hL w hx

theorem idxK_elem {h1 : n7InvCheck = true} {h2 : n7RelCheck = true} (hL : LetterRd L) (a : Nat)
    {k : Nat} (hk : k < 16) {x : Nat} (hx : x < 23) :
    idx 23 (phiK h1 h2 (n7 (a7W a ++ tw7 k))) x = fd 5 (ak L a) (fd 5 (tk L k) x) := by
  rw [phiK_n7, idx_elem h1 hL a hk hx, fd_pcomp (by norm_num) 5 _ _ hx]

theorem conjAt_of (hL : LetterRd L) (h1 : n7InvCheck = true) (h2 : n7RelCheck = true)
    {a k : Nat} (hk : k < 16) {v y : List (Fin 6 × Bool)}
    (e : n7 (a7W a ++ tw7 k) * n7 v = n7 y * n7 (a7W a ++ tw7 k)) :
    conjAt (ak L a) (tk L k) (pw L v) (pw L y) = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  have hx' := List.mem_range.1 hx
  have e1 := congrArg (fun g => idx 23 (phiK h1 h2 g) x) e
  simp only [map_mul, idx_mul] at e1
  have hv : fd 5 (pw L v) x < 23 := fd_pw_lt hL _ hx'
  have hz : fd 5 (ak L a) (fd 5 (tk L k) x) < 23 := by
    rw [← idxK_elem (h1 := h1) (h2 := h2) hL a hk hx']
    exact idx_lt _ hx'
  rw [idxK_elem hL a hk hx', idxK_pw hL _ hx', idxK_elem hL a hk hv, idxK_pw hL _ hz] at e1
  rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq, e1]
  exact Nat.beq_refl _

theorem center_of (hL : LetterRd L) (h1 : n7InvCheck = true)
    (h2 : n7RelCheck = true) (hok : n7kOk L = true) (h : centerK L = true) :
    ∀ z : N7, (∀ i : Fin 2, z * n7 (bGen7 i) * z⁻¹ = 1 ∨ z * n7 (bGen7 i) * z⁻¹ = n7 (bGen7 0) ∨
      z * n7 (bGen7 i) * z⁻¹ = n7 (bGen7 1) ∨
      z * n7 (bGen7 i) * z⁻¹ = n7 (bGen7 0) * n7 (bGen7 1)) →
    (∀ i : Fin 3, z * n7 (dGen7 i) = n7 (dGen7 i) * z) → z = 1 := by
  unfold centerK at h
  rw [withL_eq] at h
  simp only [sB_eq] at h
  unfold centerE at h
  refine n7K_forall hL h1 h2 hok _ fun a ha k hk => ?_
  intro hB hD
  have hg := allAT_spec h ha hk
  have hcz : ∀ {v y : List (Fin 6 × Bool)}, n7 (a7W a ++ tw7 k) * n7 v * (n7 (a7W a ++ tw7 k))⁻¹ =
      n7 y → conjAt (ak L a) (tk L k) (pw L v) (pw L y) = true := by
    intro v y e
    refine conjAt_of hL h1 h2 hk ?_
    rw [← e]
    group
  have hcom : ((List.range 23).all fun x => comAt (ak L a) (tk L k) (pw L (dGen7 0)) x &&
      comAt (ak L a) (tk L k) (pw L (dGen7 1)) x &&
      comAt (ak L a) (tk L k) (pw L (dGen7 2)) x) = true := by
    have c0 := conjAt_of hL h1 h2 hk (hD 0)
    have c1 := conjAt_of hL h1 h2 hk (hD 1)
    have c2 := conjAt_of hL h1 h2 hk (hD 2)
    refine List.all_eq_true.2 fun x hx => ?_
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨List.all_eq_true.1 c0 x hx, List.all_eq_true.1 c1 x hx⟩, List.all_eq_true.1 c2 x hx⟩
  have hY : ∀ i : Fin 2, ∃ Y ∈ [idn, pw L (bGen7 0), pw L (bGen7 1), pw L (bGen7 0 ++ bGen7 1)],
      conjAt (ak L a) (tk L k) (pw L (bGen7 i)) Y = true := by
    intro i
    rcases hB i with e | e | e | e
    · exact ⟨pw L [], List.mem_cons_self, hcz (by rw [e, n7_nil])⟩
    · exact ⟨pw L (bGen7 0), by simp, hcz e⟩
    · exact ⟨pw L (bGen7 1), by simp, hcz e⟩
    · exact ⟨pw L (bGen7 0 ++ bGen7 1), by simp,
        hcz (y := bGen7 0 ++ bGen7 1) (by rw [e, n7_append])⟩
  have hnb : ([pw L (bGen7 0), pw L (bGen7 1)].all fun P =>
      [idn, pw L (bGen7 0), pw L (bGen7 1), pw L (bGen7 0 ++ bGen7 1)].any fun Y =>
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
  refine phiK_injective hL h1 h2 hok (eq_of_idx fun x hx => ?_)
  have hx' := List.all_eq_true.1 hg x (List.mem_range.2 hx)
  rw [idxK_elem hL a hk hx, map_one, idx_one]
  exact (Nat.eq_of_beq_eq_true hx').trans (hid x hx)

end CFSG.KC.N7K

end
