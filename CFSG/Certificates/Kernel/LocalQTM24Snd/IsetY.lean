module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Tr
public import CFSG.Certificates.Kernel.LocalQTM24Snd.TrHash
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.KC.LQT.W CFSG.KC.LQT.M24

variable {n : ℕ}

private theorem aux_isety_eqL_iff : ∀ (l m : List ℕ),
    CFSG.KC.LQT.Syl.eqL l m = true ↔ l = m
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => by simp only [reduceCtorEq, iff_false]; exact Bool.false_ne_true
  | _ :: _, [] => by simp only [reduceCtorEq, iff_false]; exact Bool.false_ne_true
  | x :: t, y :: u => by
    change CFSG.KC.Ord.andB (Nat.beq x y) (CFSG.KC.LQT.Syl.eqL t u) = true ↔ _
    rw [CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.beq_iff, aux_isety_eqL_iff t u, List.cons.injEq]

private theorem aux_isety_anyLs_iff (l : List (List ℕ)) (f : List ℕ → Bool) :
    CFSG.KC.LQT.M24.anyLs l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil =>
    constructor
    · intro h
      exact absurd (show false = true from h) Bool.false_ne_true
    · rintro ⟨x, hx, _⟩
      cases hx
  | cons a l ih =>
    have h0 : CFSG.KC.LQT.M24.anyLs (a :: l) f =
        CFSG.KC.Ord.orB (f a) (CFSG.KC.LQT.M24.anyLs l f) := rfl
    rw [h0, CFSG.KC.LQT.P.orB_iff, ih]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨a, List.mem_cons.2 (Or.inl rfl), h⟩
      · exact ⟨x, List.mem_cons.2 (Or.inr hx), h⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact Or.inl h
      · exact Or.inr ⟨x, hx', h⟩

private theorem aux_isety_evalWK (hn : n ≤ 32) (gs : List (Perm (Fin n))) (w : List ℕ) :
    CFSG.KC.LQT.W.evalWK n (gs.map CFSG.KC.LQT.W.codeP) w =
      CFSG.KC.LQT.P.code (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs w) :=
  CFSG.KC.LQT.LK.evalWK_code hn gs w

private theorem aux_isety_conjX (x σ : Perm (Fin n)) (i j k : ℕ) (hi : i = k) (hj : j = 5 - k) :
    CFSG.QuasithinUnique.A5.Kc3Cert.conjX (RN.enc x) (RN.enc σ) k =
      RN.enc (x ^ i * σ * x ^ j) := by
  subst hi hj
  unfold CFSG.QuasithinUnique.A5.Kc3Cert.conjX
  rw [← CFSG.QuasithinUnique.A5.Kc3Cert.enc_pow (rawIsEnc n) x,
    ← CFSG.QuasithinUnique.A5.Kc3Cert.enc_pow (rawIsEnc n) x, RN.enc_mul, RN.enc_mul]

private theorem aux_isety_ne (x σ : Perm (Fin n)) (i j k : ℕ) (hi : i = k) (hj : j = 5 - k)
    (hq : ¬ σ * (x ^ i * σ * x ^ j) = (x ^ i * σ * x ^ j) * σ) :
    (RN.enc σ * CFSG.QuasithinUnique.A5.Kc3Cert.conjX (RN.enc x) (RN.enc σ) k !=
      CFSG.QuasithinUnique.A5.Kc3Cert.conjX (RN.enc x) (RN.enc σ) k * RN.enc σ) = true := by
  rw [aux_isety_conjX x σ i j k hi hj, bne_iff_ne]
  intro heq
  exact hq (RN.enc_inj (by simpa only [RN.enc_mul] using heq))

private theorem aux_isety_ne5 (x σ : Perm (Fin n))
    (hq : ¬ σ * (x ^ 1 * σ * x ^ 4) * (x ^ 2 * σ * x ^ 3) * (x ^ 3 * σ * x ^ 2) *
      (x ^ 4 * σ * x ^ 1) = 1) :
    (RN.enc σ * CFSG.QuasithinUnique.A5.Kc3Cert.conjX (RN.enc x) (RN.enc σ) 1 *
      CFSG.QuasithinUnique.A5.Kc3Cert.conjX (RN.enc x) (RN.enc σ) 2 *
      CFSG.QuasithinUnique.A5.Kc3Cert.conjX (RN.enc x) (RN.enc σ) 3 *
      CFSG.QuasithinUnique.A5.Kc3Cert.conjX (RN.enc x) (RN.enc σ) 4 != 1) = true := by
  rw [aux_isety_conjX x σ 1 4 1 rfl rfl, aux_isety_conjX x σ 2 3 2 rfl rfl,
    aux_isety_conjX x σ 3 2 3 rfl rfl, aux_isety_conjX x σ 4 1 4 rfl rfl, bne_iff_ne]
  intro heq
  apply hq
  apply RN.enc_inj
  rw [RN.enc_one]
  simpa only [RN.enc_mul] using heq

theorem getK_map_pow (X : ℕ) (k : ℕ) (hk : k < 6) :
    CFSG.KC.LQT.S.getK (List.map (CFSG.KC.LQT.P.pow n X) [0, 1, 2, 3, 4, 5]) k =
      CFSG.KC.LQT.P.pow n X k := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
    omega
  all_goals rfl

theorem allZ_mem_right {α β : Type} {l : List α} {m : List β} {f : α → β → Bool}
    (h : allZ l m f = true) : ∀ y ∈ m, ∃ x ∈ l, f x y = true := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => intro y hy; cases hy
    | cons b m' => exact absurd (show false = true from h) Bool.false_ne_true
  | cons a l ih =>
    cases m with
    | nil => exact absurd (show false = true from h) Bool.false_ne_true
    | cons b m' =>
      have h' : CFSG.KC.Ord.andB (f a b) (allZ l m' f) = true := h
      obtain ⟨hab, hrest⟩ := (CFSG.KC.LQT.P.andB_iff).1 h'
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact ⟨a, List.mem_cons.2 (Or.inl rfl), hab⟩
      · obtain ⟨x, hx, hf⟩ := ih (m := m') hrest y hy'
        exact ⟨x, List.mem_cons.2 (Or.inr hx), hf⟩

theorem esK_mem (hn : n ≤ 32) (gs : List (Perm (Fin n))) (c : ECert) (El : List ℕ)
    (h : esK n (gs.map codeP) c.eW El = true) :
    ∀ τ : Perm (Fin n), (P.code τ ∈ El ↔ RN.enc τ ∈ c.Es (gs.map RN.enc)) := by
  intro τ
  have hg : List.map (CFSG.KC.LQT.W.evalWK n (gs.map CFSG.KC.LQT.W.codeP)) c.eW =
      (c.eW.map (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs)).map
        CFSG.KC.LQT.P.code := by
    rw [List.map_map]
    exact List.map_congr_left fun w _ => aux_isety_evalWK hn gs w
  have hEs : c.Es (gs.map RN.enc) =
      CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.bfsSet
        ((c.eW.map (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs)).map RN.enc) 16 := by
    unfold ECert.Es ECert.eR
    congr 1
    rw [List.map_map]
    exact List.map_congr_left fun w _ =>
      (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.enc_evalW
        (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.rawIsEnc n) gs w).symm
  unfold esK at h
  simp only [bfsC_eq] at h
  rw [hg] at h
  have hE := (aux_isety_eqL_iff _ _).1 h
  have hR := (rounds_code_iff hn
    (c.eW.map (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs)) 16).1 τ
  have hB := (bfsSet_enc_iff
    (c.eW.map (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs)) 16).1 τ
  rw [hEs, ← hE]
  exact hR.trans hB.symm

private theorem aux_isety_in (hn : n ≤ 32) (gs : List (Perm (Fin n))) (c : ECert) (El : List ℕ)
    (σ : Perm (Fin n)) (hf : esK n (gs.map CFSG.KC.LQT.W.codeP) c.eW El = true)
    (hmem : CFSG.KC.LQT.P.code σ ∈ El) :
    (c.Es (gs.map RN.enc)).contains (RN.enc σ) = true :=
  Std.HashSet.mem_iff_contains.1 ((esK_mem hn gs c El hf σ).1 hmem)

private theorem aux_isety_cases (hn : n ≤ 32) (x₀ σ : Perm (Fin n)) (Els : List (List ℕ))
    (h : CFSG.KC.LQT.M24.ycK n
      (List.map (CFSG.KC.LQT.P.pow n (CFSG.KC.LQT.P.code x₀)) [0, 1, 2, 3, 4, 5])
      Els (CFSG.KC.LQT.P.code σ) = true) :
    (∃ El ∈ Els, CFSG.KC.LQT.S.memL (CFSG.KC.LQT.P.code σ) El = true) ∨
      ¬ σ * (x₀ ^ 1 * σ * x₀ ^ 4) = (x₀ ^ 1 * σ * x₀ ^ 4) * σ ∨
      ¬ σ * (x₀ ^ 2 * σ * x₀ ^ 3) = (x₀ ^ 2 * σ * x₀ ^ 3) * σ ∨
      ¬ σ * (x₀ ^ 3 * σ * x₀ ^ 2) = (x₀ ^ 3 * σ * x₀ ^ 2) * σ ∨
      ¬ σ * (x₀ ^ 4 * σ * x₀ ^ 1) = (x₀ ^ 4 * σ * x₀ ^ 1) * σ ∨
      ¬ σ * (x₀ ^ 1 * σ * x₀ ^ 4) * (x₀ ^ 2 * σ * x₀ ^ 3) * (x₀ ^ 3 * σ * x₀ ^ 2) *
        (x₀ ^ 4 * σ * x₀ ^ 1) = 1 := by
  unfold CFSG.KC.LQT.M24.ycK at h
  have g1 := getK_map_pow (n := n) (CFSG.KC.LQT.P.code x₀) 1 (by norm_num)
  have g2 := getK_map_pow (n := n) (CFSG.KC.LQT.P.code x₀) 2 (by norm_num)
  have g3 := getK_map_pow (n := n) (CFSG.KC.LQT.P.code x₀) 3 (by norm_num)
  have g4 := getK_map_pow (n := n) (CFSG.KC.LQT.P.code x₀) 4 (by norm_num)
  simp only [g1, g2, g3, g4, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.orB_iff,
    CFSG.KC.LQT.P.notB_iff, CFSG.KC.LQT.P.code_pow hn, CFSG.KC.LQT.P.code_mul hn,
    CFSG.KC.LQT.P.code_one, CFSG.KC.LQT.P.comm_code hn, CFSG.KC.LQT.P.beq_iff,
    CFSG.KC.LQT.P.code_eq_iff hn] at h
  rcases h with h | h | h | h | h | h
  · exact Or.inl ((aux_isety_anyLs_iff _ _).1 h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem ycK_sound (hn : n ≤ 32) (gs : List (Perm (Fin n))) (xW : List ℕ)
    (c1 c2 c3 c4 c5 : ECert) (Els : List (List ℕ))
    (hes : allZ [c1.eW, c2.eW, c3.eW, c4.eW, c5.eW] Els (esK n (gs.map codeP)) = true)
    (σ : Perm (Fin n))
    (h : ycK n (List.map (CFSG.KC.LQT.P.pow n (evalWK n (gs.map codeP) xW)) [0, 1, 2, 3, 4, 5])
      Els (P.code σ) = true) :
    yCheck (evalW (gs.map RN.enc) xW) (c1.Es (gs.map RN.enc)) (c2.Es (gs.map RN.enc))
      (c3.Es (gs.map RN.enc)) (c4.Es (gs.map RN.enc)) (c5.Es (gs.map RN.enc)) (RN.enc σ) =
        true := by
  have hX : evalWK n (gs.map CFSG.KC.LQT.W.codeP) xW =
      CFSG.KC.LQT.P.code (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs xW) :=
    aux_isety_evalWK hn gs xW
  have hE : CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW (gs.map RN.enc) xW =
      RN.enc (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs xW) :=
    (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.enc_evalW
      (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.rawIsEnc n) gs xW).symm
  rw [hX] at h
  rw [hE]
  generalize CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW gs xW = x₀ at h ⊢
  rcases aux_isety_cases hn x₀ σ Els h with ⟨El, hEl, hm⟩ | h1 | h2 | h3 | h4 | h5
  · have hmem : CFSG.KC.LQT.P.code σ ∈ El := (CFSG.KC.LQT.S.memL_iff _ _).1 hm
    obtain ⟨x, hx, hf⟩ := allZ_mem_right hes El hEl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have hc := aux_isety_in hn gs c1 El σ hf hmem
      simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hc, Bool.true_or, Bool.or_true]
    · have hc := aux_isety_in hn gs c2 El σ hf hmem
      simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hc, Bool.true_or, Bool.or_true]
    · have hc := aux_isety_in hn gs c3 El σ hf hmem
      simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hc, Bool.true_or, Bool.or_true]
    · have hc := aux_isety_in hn gs c4 El σ hf hmem
      simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hc, Bool.true_or, Bool.or_true]
    · have hc := aux_isety_in hn gs c5 El σ hf hmem
      simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hc, Bool.true_or, Bool.or_true]
  · have hd := aux_isety_ne x₀ σ 1 4 1 rfl rfl h1
    simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hd, Bool.or_true, Bool.true_or]
  · have hd := aux_isety_ne x₀ σ 2 3 2 rfl rfl h2
    simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hd, Bool.or_true, Bool.true_or]
  · have hd := aux_isety_ne x₀ σ 3 2 3 rfl rfl h3
    simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hd, Bool.or_true, Bool.true_or]
  · have hd := aux_isety_ne x₀ σ 4 1 4 rfl rfl h4
    simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hd, Bool.or_true, Bool.true_or]
  · have hd := aux_isety_ne5 x₀ σ h5
    simp only [CFSG.QuasithinUnique.A5.Kc3Cert.yCheck, hd, Bool.or_true, Bool.true_or]

end CFSG.KC.LQT.M24Snd

end
