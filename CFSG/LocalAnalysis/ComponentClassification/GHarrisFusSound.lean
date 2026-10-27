module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert

namespace SCert


theorem SE.enc_lt (s : SE) : s.enc < 512 := by
  have h1 := s.d.isLt
  have h2 := ZMod.val_lt s.v0
  have h3 := ZMod.val_lt s.v1
  have h4 := ZMod.val_lt s.v2
  unfold SE.enc
  omega

theorem SE.zmod4_cast (k : ℕ) (v : ZMod 4) : ((4 * k + v.val : ℕ) : ZMod 4) = v := by
  rw [Nat.cast_add, Nat.cast_mul, show ((4 : ℕ) : ZMod 4) = 0 from rfl, zero_mul, zero_add,
    ZMod.natCast_zmod_val]

theorem SE.dec_enc (s : SE) : SE.dec s.enc = s := by
  obtain ⟨d, v0, v1, v2⟩ := s
  have h1 := d.isLt
  have h2 := ZMod.val_lt v0
  have h3 := ZMod.val_lt v1
  have h4 := ZMod.val_lt v2
  simp only [SE.dec, SE.enc]
  congr 1
  · ext
    simp only [Fin.val_ofNat]
    omega
  · rw [show (d.val * 64 + v0.val * 16 + v1.val * 4 + v2.val) / 16 = 4 * d.val + v0.val by omega]
    exact SE.zmod4_cast _ _
  · rw [show (d.val * 64 + v0.val * 16 + v1.val * 4 + v2.val) / 4 =
      4 * (4 * d.val + v0.val) + v1.val by omega]
    exact SE.zmod4_cast _ _
  · rw [show d.val * 64 + v0.val * 16 + v1.val * 4 + v2.val =
      4 * (16 * d.val + 4 * v0.val + v1.val) + v2.val by omega]
    exact SE.zmod4_cast _ _

theorem SE.fmul_mulArr (a b : SE) : SE.fmul SE.mulArr a b = a * b := by
  have ha := SE.enc_lt a
  have hb := SE.enc_lt b
  have hi : a.enc * 512 + b.enc < 262144 := by omega
  unfold SE.fmul SE.mulArr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, dite_true, Option.getD_some]
  rw [show (a.enc * 512 + b.enc) / 512 = a.enc by omega,
    show (a.enc * 512 + b.enc) % 512 = b.enc by omega, SE.dec_enc, SE.dec_enc]

theorem SE.mem_allList (s : SE) : s ∈ SE.allList := by
  obtain ⟨d, a, b, c⟩ := s
  unfold SE.allList
  exact List.mem_flatMap.mpr ⟨d, List.mem_finRange d, List.mem_flatMap.mpr ⟨a,
    List.mem_finRange (n := 4) a, List.mem_flatMap.mpr ⟨b, List.mem_finRange (n := 4) b,
      List.mem_map.mpr ⟨c, List.mem_finRange (n := 4) c, rfl⟩⟩⟩⟩

theorem Fus.checkList_sound {L : List Fus.Data} (h : Fus.checkList L = true) {A : Fus.Data}
    (hA : A ∈ L) : A.checkM (· * ·) = true := by
  have hf : SE.fmul SE.mulArr = (· * ·) := funext fun a => funext fun b => SE.fmul_mulArr a b
  unfold Fus.checkList at h
  simp only [hf, List.all_eq_true] at h
  exact h A hA

theorem Fus.Data.pairOk_congr (mul : SE → SE → SE) (A : Fus.Data) {q q' : Array SE} {i j : ℕ}
    (hi : q.getD i 1 = q'.getD i 1) (hj : q.getD j 1 = q'.getD j 1) :
    A.pairOk mul q i j = A.pairOk mul q' i j := by
  simp only [Fus.Data.pairOk, Fus.pat, hi, hj]

theorem Fus.Data.outB_of_checkM {A : Fus.Data} (h : A.checkM (· * ·) = true) {q1 q2 q3 : SE}
    (h1 : Fus.isInv (· * ·) q1 = true) (h2 : Fus.isInv (· * ·) q2 = true)
    (h3 : Fus.isInv (· * ·) q3 = true)
    (hp : ∀ i j, i < 4 → j < 4 → A.pairOk (· * ·) #[A.target, q1, q2, q3] i j = true)
    (hc : A.condB (· * ·) #[A.target, q1, q2, q3] = true) :
    A.outB (· * ·) #[A.target, q1, q2, q3] = true := by
  unfold Fus.Data.checkM at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hm : ∀ s : SE, Fus.isInv (· * ·) s = true →
      s ∈ SE.allList.filter (Fus.isInv (· * ·)) :=
    fun s hs => List.mem_filter.mpr ⟨SE.mem_allList s, hs⟩
  have e01 : A.pairOk (· * ·) #[A.target, q1, 1, 1] 0 1 = true := by
    rw [← Fus.Data.pairOk_congr _ A (i := 0) (j := 1) (q := #[A.target, q1, q2, q3])
      (q' := #[A.target, q1, 1, 1]) rfl rfl]
    exact hp 0 1 (by norm_num) (by norm_num)
  have e02 : A.pairOk (· * ·) #[A.target, q1, q2, 1] 0 2 = true := by
    rw [← Fus.Data.pairOk_congr _ A (i := 0) (j := 2) (q := #[A.target, q1, q2, q3])
      (q' := #[A.target, q1, q2, 1]) rfl rfl]
    exact hp 0 2 (by norm_num) (by norm_num)
  have e12 : A.pairOk (· * ·) #[A.target, q1, q2, 1] 1 2 = true := by
    rw [← Fus.Data.pairOk_congr _ A (i := 1) (j := 2) (q := #[A.target, q1, q2, q3])
      (q' := #[A.target, q1, q2, 1]) rfl rfl]
    exact hp 1 2 (by norm_num) (by norm_num)
  have l1 := h.2 q1 (hm q1 h1)
  rw [e01, Bool.not_true, Bool.false_or, List.all_eq_true] at l1
  have l2 := l1 q2 (hm q2 h2)
  rw [e02, e12, Bool.and_true, Bool.not_true, Bool.false_or, List.all_eq_true] at l2
  have l3 := l2 q3 (hm q3 h3)
  rw [hp 0 3 (by norm_num) (by norm_num), hp 1 3 (by norm_num) (by norm_num),
    hp 2 3 (by norm_num) (by norm_num), hc] at l3
  simpa using l3


theorem Fus.evalW_foldl (q : Array SE) (w : List ℕ) (acc : SE) :
    w.foldl (fun a i => a * q.getD i 1) acc = acc * Fus.evalW (· * ·) q w := by
  induction w generalizing acc with
  | nil => simp [Fus.evalW]
  | cons i w ih =>
    simp only [List.foldl_cons, Fus.evalW]
    rw [ih, ih (1 * q.getD i 1)]
    group

theorem Fus.evalW_cons (q : Array SE) (i : ℕ) (w : List ℕ) :
    Fus.evalW (· * ·) q (i :: w) = q.getD i 1 * Fus.evalW (· * ·) q w := by
  have h := Fus.evalW_foldl q w (1 * q.getD i 1)
  rw [one_mul] at h
  rw [← h]
  show List.foldl (fun acc i => acc * q.getD i 1) 1 (i :: w) = _
  rw [List.foldl_cons, one_mul]

theorem Fus.evalW_hom (q q' : Array SE) (ψ : SE → SE) (P : SE → Prop)
    (hP1 : P 1) (hPmul : ∀ a b, P a → P b → P (a * b))
    (hψ : ∀ a b, P a → P b → ψ (a * b) = ψ a * ψ b) (hψ1 : ψ 1 = 1)
    (hq : ∀ i < 4, P (q.getD i 1) ∧ ψ (q.getD i 1) = q'.getD i 1)
    (w : List ℕ) (hw : ∀ i ∈ w, i < 4) :
    P (Fus.evalW (· * ·) q w) ∧ ψ (Fus.evalW (· * ·) q w) = Fus.evalW (· * ·) q' w := by
  induction w with
  | nil => exact ⟨hP1, hψ1⟩
  | cons i w ih =>
    have hi := hq i (hw i List.mem_cons_self)
    obtain ⟨h1, h2⟩ := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [Fus.evalW_cons, Fus.evalW_cons]
    exact ⟨hPmul _ _ hi.1 h1, by rw [hψ _ _ hi.1 h1, hi.2, h2]⟩

structure Fus.Data.TableFacts (A : Fus.Data) : Prop where
  gens_size : A.gens.size = 4
  words_lt : ∀ k < 32, ∀ i ∈ A.words.getD k [], i < 4
  mi_lt : ∀ k < 32, ∀ i < 4, A.mi k i < 32
  gen0 : A.gens.getD 0 1 = A.source
  gens_inv : ∀ i < 4, Fus.isInv (· * ·) (A.gens.getD i 1) = true
  gens_comm : ∀ i < 4, A.gens.getD i 1 * A.source = A.source * A.gens.getD i 1
  elt_mul : ∀ k < 32, ∀ i < 4, A.elt (· * ·) (A.mi k i) = A.elt (· * ·) k * A.gens.getD i 1
  words0 : A.words.getD 0 [0] = []
  elt_ne : ∀ k < 32, k ≠ 0 → A.elt (· * ·) k ≠ 1
  zIdx_lt : A.zIdx < 32
  elt_z : A.elt (· * ·) A.zIdx = SE.gen 0

theorem Fus.Data.tableFacts {A : Fus.Data} (h : A.tableOk (· * ·) = true) :
    Fus.Data.TableFacts A := by
  unfold Fus.Data.tableOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg4, hw32⟩, hm32⟩, hmrows⟩, hwl⟩, hz⟩, hg0⟩, hgens⟩, hmul⟩, hw0⟩, hne⟩, hez⟩ :=
    h
  refine ⟨hg4, ?_, ?_, hg0, fun i hi => (hgens i hi).1, fun i hi => (hgens i hi).2, hmul, hw0,
    ?_, hz, hez⟩
  · intro k hk i hi
    have hk' : k < A.words.size := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk', Option.getD_some] at hi
    exact hwl k hk' i hi
  · intro k hk i hi
    unfold Fus.Data.mi
    have hk' : k < A.mulIdx.size := by omega
    have hr := hmrows k hk'
    have hi' : i < A.mulIdx[k].size := by omega
    have e1 : A.mulIdx.getD k #[] = A.mulIdx[k] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk', Option.getD_some]
    rw [e1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
    exact hr.2 i hi'
  · intro k hk hk0
    rcases hne k hk with h | h
    · exact absurd h hk0
    · exact h



theorem SE.cls_spec (h : SE.clsOk = true) {s : SE} (hs : SE.isInvB s = true) :
    SE.clsTab s < 9 ∧ ∃ c : SE, c⁻¹ * s * c = SE.invRep (Fin.ofNat 9 (SE.clsTab s)) := by
  unfold SE.clsOk at h
  rw [List.all_eq_true] at h
  have h1 := h s (by
    obtain ⟨d, a, b, c⟩ := s
    unfold SE.allList
    exact List.mem_flatMap.mpr ⟨d, List.mem_finRange d, List.mem_flatMap.mpr ⟨a,
      List.mem_finRange (n := 4) a, List.mem_flatMap.mpr ⟨b, List.mem_finRange (n := 4) b,
        List.mem_map.mpr ⟨c, List.mem_finRange (n := 4) c, rfl⟩⟩⟩⟩)
  generalize SE.clsTab s = n at h1 ⊢
  rcases Bool.or_eq_true_iff.mp h1 with h' | h'
  · rw [hs] at h'
    exact absurd h' Bool.false_ne_true
  · obtain ⟨hlt, hany⟩ := Bool.and_eq_true_iff.mp h'
    obtain ⟨c, -, hc⟩ := List.any_eq_true.mp hany
    exact ⟨of_decide_eq_true hlt, c, beq_iff_eq.mp hc⟩


end SCert

variable {G : Type} [Group G] (D : GHSylow G)

open Classical in
noncomputable def GHSylow.conjM (g : G) (s : SE) : SE :=
  if h : g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G) then Classical.choose (D.exists_toG h) else 1

theorem GHSylow.toG_conjM {g : G} {s : SE} (h : g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G)) :
    D.toG (D.conjM g s) = g⁻¹ * D.toG s * g := by
  unfold GHSylow.conjM
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec (D.exists_toG h)

theorem GHSylow.conjM_mul {g : G} {a b : SE} (ha : g⁻¹ * D.toG a * g ∈ (D.S : Subgroup G))
    (hb : g⁻¹ * D.toG b * g ∈ (D.S : Subgroup G)) :
    D.conjM g (a * b) = D.conjM g a * D.conjM g b := by
  have hab : g⁻¹ * D.toG (a * b) * g ∈ (D.S : Subgroup G) := by
    rw [map_mul, show g⁻¹ * (D.toG a * D.toG b) * g = (g⁻¹ * D.toG a * g) * (g⁻¹ * D.toG b * g) by
      group]
    exact mul_mem ha hb
  apply D.toG_injective
  rw [map_mul, D.toG_conjM hab, D.toG_conjM ha, D.toG_conjM hb, map_mul]
  group

theorem GHSylow.conjM_one (g : G) : D.conjM g 1 = 1 := by
  apply D.toG_injective
  rw [D.toG_conjM (by rw [map_one]; simp), map_one]
  group

theorem GHSylow.conjM_injective {g : G} {a b : SE} (ha : g⁻¹ * D.toG a * g ∈ (D.S : Subgroup G))
    (hb : g⁻¹ * D.toG b * g ∈ (D.S : Subgroup G)) (h : D.conjM g a = D.conjM g b) : a = b := by
  have h' := congrArg D.toG h
  rw [D.toG_conjM ha, D.toG_conjM hb] at h'
  apply D.toG_injective
  simpa using h'


noncomputable abbrev GHSylow.fusQ (A : Fus.Data) (g : G) : Array SE :=
  #[A.target, D.conjM g (A.gens.getD 1 1), D.conjM g (A.gens.getD 2 1),
    D.conjM g (A.gens.getD 3 1)]

theorem GHSylow.fus_img {A : Fus.Data} (hA : A.checkM (· * ·) = true) {g : G}
    (hgu : g⁻¹ * D.toG A.source * g = D.toG A.target)
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G)) :
    ∀ k < 32, (A.elt (· * ·) k) * A.source = A.source * A.elt (· * ·) k ∧
      D.conjM g (A.elt (· * ·) k) = A.img (· * ·) (D.fusQ A g) k := by
  have hT := Fus.Data.tableFacts (Bool.and_eq_true_iff.mp (by
    unfold Fus.Data.checkM at hA; exact hA)).1
  have hP1 : (1 : SE) * A.source = A.source * 1 := by group
  have hPmul : ∀ a b : SE, a * A.source = A.source * a → b * A.source = A.source * b →
      a * b * A.source = A.source * (a * b) := by
    intro a b ha hb
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  have hq : ∀ i < 4, A.gens.getD i 1 * A.source = A.source * A.gens.getD i 1 ∧
      D.conjM g (A.gens.getD i 1) = (D.fusQ A g).getD i 1 := by
    intro i hi
    refine ⟨hT.gens_comm i hi, ?_⟩
    interval_cases i
    · rw [hT.gen0]
      apply D.toG_injective
      rw [D.toG_conjM (hgC _ (by group)), hgu]
      rfl
    · rfl
    · rfl
    · rfl
  intro k hk
  have := Fus.evalW_hom A.gens (D.fusQ A g) (D.conjM g) (fun s => s * A.source = A.source * s)
    hP1 hPmul (fun a b ha hb => D.conjM_mul (hgC a ha) (hgC b hb)) (D.conjM_one g) hq
    (A.words.getD k []) (hT.words_lt k hk)
  exact this


theorem arr_range_getD (f : ℕ → SE) {k : ℕ} (hk : k < 32) :
    ((List.range 32).toArray.map f).getD k 1 = f k := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_range hk]
  rfl

theorem GHSylow.fusQ_getD {A : Fus.Data} (hA : A.checkM (· * ·) = true) {g : G}
    (hgu : g⁻¹ * D.toG A.source * g = D.toG A.target)
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    {i : ℕ} (hi : i < 4) : (D.fusQ A g).getD i 1 = D.conjM g (A.gens.getD i 1) := by
  have hT := Fus.Data.tableFacts (Bool.and_eq_true_iff.mp (by
    unfold Fus.Data.checkM at hA; exact hA)).1
  interval_cases i
  · rw [hT.gen0]
    apply D.toG_injective
    rw [D.toG_conjM (hgC _ (by group)), hgu]
    rfl
  · rfl
  · rfl
  · rfl

theorem GHSylow.conjM_beq {A : Fus.Data} {g : G}
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    {a b : SE} (ha : a * A.source = A.source * a) (hb : b * A.source = A.source * b) :
    (D.conjM g a == D.conjM g b) = (a == b) := by
  by_cases h : a = b
  · rw [h]; simp
  · have h' : D.conjM g a ≠ D.conjM g b := fun e => h (D.conjM_injective (hgC a ha) (hgC b hb) e)
    simp [h, h']

theorem GHSylow.conjM_beq_one {A : Fus.Data} {g : G}
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    {a : SE} (ha : a * A.source = A.source * a) : (D.conjM g a == 1) = (a == 1) := by
  have h := D.conjM_beq hgC ha (b := 1) (by group)
  rwa [D.conjM_one] at h


@[expose] def GHSylow.FusN (i j : ℕ) : Prop :=
  ∃ g : G, g⁻¹ * D.toG (SE.invRep (Fin.ofNat 9 i)) * g = D.toG (SE.invRep (Fin.ofNat 9 j))

theorem GHSylow.fusN_of_conj (hcls : SE.clsOk = true) {c d : SE} (hc : SE.isInvB c = true)
    (hd : SE.isInvB d = true) {g : G} (hg : g⁻¹ * D.toG c * g = D.toG d) :
    D.FusN (SE.clsTab c) (SE.clsTab d) := by
  obtain ⟨-, x, hx⟩ := SE.cls_spec hcls hc
  obtain ⟨-, y, hy⟩ := SE.cls_spec hcls hd
  refine ⟨(D.toG x)⁻¹ * g * D.toG y, ?_⟩
  rw [← hx, ← hy]
  simp only [map_mul, map_inv]
  rw [← hg]
  group

theorem GHSylow.pairOk_fusQ {A : Fus.Data} (hA : A.checkM (· * ·) = true) {g : G}
    (hgu : g⁻¹ * D.toG A.source * g = D.toG A.target)
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    {i j : ℕ} (hi : i < 4) (hj : j < 4) : A.pairOk (· * ·) (D.fusQ A g) i j = true := by
  have hT := Fus.Data.tableFacts (Bool.and_eq_true_iff.mp (by
    unfold Fus.Data.checkM at hA; exact hA)).1
  have hPmul : ∀ a b : SE, a * A.source = A.source * a → b * A.source = A.source * b →
      a * b * A.source = A.source * (a * b) := by
    intro a b ha hb
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  set a := A.gens.getD i 1
  set b := A.gens.getD j 1
  have ha := hT.gens_comm i hi
  have hb := hT.gens_comm j hj
  have hab := hPmul a b ha hb
  have hba := hPmul b a hb ha
  have hab2 := hPmul _ _ hab hab
  have hab4 := hPmul _ _ hab2 hab2
  have m := fun x y hx hy => D.conjM_mul (g := g) (hgC x hx) (hgC y hy)
  unfold Fus.Data.pairOk Fus.pat
  rw [D.fusQ_getD hA hgu hgC hi, D.fusQ_getD hA hgu hgC hj]
  simp only []
  rw [← m a b ha hb, ← m b a hb ha, ← m _ _ hab hab, ← m _ _ hab2 hab2,
    D.conjM_beq_one hgC hab, D.conjM_beq_one hgC hab2, D.conjM_beq_one hgC hab4,
    D.conjM_beq hgC hab hba]
  exact beq_self_eq_true _


theorem GHSylow.isInv_conjM {A : Fus.Data} {g : G}
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    {s : SE} (hs : s * A.source = A.source * s) (h : Fus.isInv (· * ·) s = true) :
    Fus.isInv (· * ·) (D.conjM g s) = true := by
  have hss : s * s * A.source = A.source * (s * s) := by
    rw [mul_assoc, hs, ← mul_assoc, hs, mul_assoc]
  change (D.conjM g s * D.conjM g s == 1 && D.conjM g s != 1) = true
  change (s * s == 1 && s != 1) = true at h
  rw [← D.conjM_mul (hgC _ hs) (hgC _ hs), D.conjM_beq_one hgC hss, bne, D.conjM_beq_one hgC hs]
  exact h

theorem GHSylow.fus_good {A : Fus.Data} (hA : A.checkM (· * ·) = true) (hcls : SE.clsOk = true)
    {g : G} (hgu : g⁻¹ * D.toG A.source * g = D.toG A.target)
    (hgC : ∀ s : SE, s * A.source = A.source * s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G))
    (hbad : ∀ p ∈ A.badPairs, ¬ D.FusN p.1 p.2)
    (hE : A.useE = true → g⁻¹ * D.z * g = D.z → ∀ s : SE, s * A.source = A.source * s →
      (SE.predE s ↔ SE.predE (D.conjM g s)))
    (hF : A.useF = true → g⁻¹ * D.z * g = D.z → ∀ s : SE, s * A.source = A.source * s →
      (SE.predF s ↔ SE.predF (D.conjM g s))) :
    A.good (· * ·) (D.fusQ A g) = true := by
  have hT := Fus.Data.tableFacts (Bool.and_eq_true_iff.mp (by
    unfold Fus.Data.checkM at hA; exact hA)).1
  have himg := D.fus_img hA hgu hgC
  have hinv : ∀ i, i < 4 → Fus.isInv (· * ·) (D.conjM g (A.gens.getD i 1)) = true := fun i hi =>
    D.isInv_conjM hgC (hT.gens_comm i hi) (hT.gens_inv i hi)
  have hcond : A.condB (· * ·) (D.fusQ A g) = true := by
    unfold Fus.Data.condB
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, Bool.or_eq_true,
      bne_iff_ne]
    refine ⟨fun k hk i hi => ?_, fun k hk => ?_⟩
    · rw [arr_range_getD _ (hT.mi_lt k hk i hi), arr_range_getD _ hk,
        ← (himg _ (hT.mi_lt k hk i hi)).2, ← (himg k hk).2, hT.elt_mul k hk i hi,
        D.fusQ_getD hA hgu hgC hi, D.conjM_mul (hgC _ (himg k hk).1) (hgC _ (hT.gens_comm i hi))]
    · by_cases hk0 : k = 0
      · left; simp [hk0]
      · right
        rw [arr_range_getD _ hk, ← (himg k hk).2]
        intro h1
        apply hT.elt_ne k hk hk0
        apply D.conjM_injective (hgC _ (himg k hk).1) (hgC 1 (by group))
        rw [h1, D.conjM_one]
  have hout := Fus.Data.outB_of_checkM hA (hinv 1 (by norm_num)) (hinv 2 (by norm_num))
    (hinv 3 (by norm_num)) (fun i j hi hj => D.pairOk_fusQ hA hgu hgC hi hj) hcond
  change A.outB (· * ·) (D.fusQ A g) = true at hout
  unfold Fus.Data.outB at hout
  simp only [Bool.or_eq_true] at hout
  have hz' : A.fixZ (· * ·) (D.fusQ A g) = true → g⁻¹ * D.z * g = D.z := by
    intro hz
    unfold Fus.Data.fixZ at hz
    have h1 := (himg _ hT.zIdx_lt).2
    rw [beq_iff_eq.mp hz, hT.elt_z] at h1
    have h2 := D.toG_conjM (g := g) (hgC _ (himg _ hT.zIdx_lt).1)
    rw [hT.elt_z, h1] at h2
    exact h2.symm
  rcases hout with ((hb | he) | hf) | hg
  · exfalso
    unfold Fus.Data.badB at hb
    obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp hb
    rw [List.mem_range] at hk
    obtain ⟨hkinv, hkb⟩ := Bool.and_eq_true_iff.mp hk'
    have hcI : SE.isInvB (A.elt (· * ·) k) = true := hkinv
    have hdI : SE.isInvB (A.img (· * ·) (D.fusQ A g) k) = true := by
      rw [← (himg k hk).2]
      exact D.isInv_conjM hgC (himg k hk).1 hkinv
    have hfus := D.fusN_of_conj hcls hcI hdI (by
      rw [← (himg k hk).2, D.toG_conjM (hgC _ (himg k hk).1)])
    generalize SE.clsTab (A.elt (· * ·) k) = cc at hkb hfus
    generalize SE.clsTab (A.img (· * ·) (D.fusQ A g) k) = dd at hkb hfus
    exact hbad (cc, dd) (List.contains_iff_mem.mp hkb) hfus
  · exfalso
    unfold Fus.Data.badEB at he
    obtain ⟨hud, hk⟩ := Bool.and_eq_true_iff.mp he
    obtain ⟨hu, hz⟩ := Bool.and_eq_true_iff.mp hud
    obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp hk
    rw [List.mem_range] at hk
    have := hE hu (hz' hz) _ (himg k hk).1
    rw [(himg k hk).2] at this
    simp [this] at hk'
  · exfalso
    unfold Fus.Data.badFB at hf
    obtain ⟨hud, hk⟩ := Bool.and_eq_true_iff.mp hf
    obtain ⟨hu, hz⟩ := Bool.and_eq_true_iff.mp hud
    obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp hk
    rw [List.mem_range] at hk
    have := hF hu (hz' hz) _ (himg k hk).1
    rw [(himg k hk).2] at this
    simp [this] at hk'
  · exact hg


end CFSG.ComponentClassification.GHarris
