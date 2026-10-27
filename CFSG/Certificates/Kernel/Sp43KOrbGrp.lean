module

public import Certificates.Data.Kernel.Sp43KCase
public import CFSG.Certificates.Kernel.Sp43KGrpFacts

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43 Subgroup

theorem getD_chunk {α : Type*} (L : List α) (d : α) {i s m : ℕ} (h1 : s ≤ i) (h2 : i < s + m) :
    ((L.drop s).take m).getD (i - s) d = L.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt
    (by omega), List.getElem?_drop, Nat.add_sub_cancel' h1]

private theorem oOne_parts {n₁ n₁' n₂ n₂' k M r X N T D t : ℕ} {q : ℕ × ℕ}
    (h : oOne n₁ n₁' n₂ n₂' k M r X N T D t q = true) :
    (fldT D t = 0 ∧ q.1 < k ∧ fldT M q.1 = fldT T t) ∨
      (fldT D t = 1 ∧ q.1 < r ∧ fldT X q.1 = fldT T t) ∨
      (2 ≤ fldT D t ∧ q.1 < N ∧ 1 ≤ fldT D q.1 ∧ fldT D q.1 < fldT D t ∧
        (fldT T t = conjT n₁ n₁' (fldT T q.1) ∨ fldT T t = conjT n₂ n₂' (fldT T q.1))) := by
  unfold oOne at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  · refine Or.inr (Or.inr ⟨h1, h2, h3, h4, ?_⟩)
    split_ifs at h5
    · exact Or.inl h5
    · exact Or.inr h5

theorem orb_spec {n₁ n₁' n₂ n₂' k M r X N T D : ℕ} {R : ℕ → ℕ × ℕ} {H : Subgroup G}
    (h : ∀ t < N, oOne n₁ n₁' n₂ n₂' k M r X N T D t (R t) = true)
    (hM : ∀ x < k, InG (fldT M x) ∧ ofT (fldT M x) ∈ H) (hX : ∀ x < r, InG (fldT X x))
    (h1 : InG n₁) (h1' : InG n₁') (h2 : InG n₂) (h2' : InG n₂') (e1 : mulT n₁ n₁' = oneT)
    (e2 : mulT n₂ n₂' = oneT) :
    ∀ t < N, InG (fldT T t) ∧ (fldT D t = 0 → ofT (fldT T t) ∈ H) ∧
      (1 ≤ fldT D t → ∃ rr < r, ∃ n ∈ sub2T n₁ n₂, ofT (fldT T t) = n * ofT (fldT X rr) * n⁻¹) := by
  suffices H' : ∀ d, ∀ t < N, fldT D t = d → InG (fldT T t) ∧ (d = 0 → ofT (fldT T t) ∈ H) ∧
      (1 ≤ d → ∃ rr < r, ∃ n ∈ sub2T n₁ n₂, ofT (fldT T t) = n * ofT (fldT X rr) * n⁻¹) from
    fun t ht => by simpa using H' _ t ht rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro t ht hd
    rcases oOne_parts (h t ht) with ⟨h0, hx, he⟩ | ⟨h0, hx, he⟩ | ⟨h0, hp, hp1, hpd, he⟩
    · rw [← he]
      exact ⟨(hM _ hx).1, fun _ => (hM _ hx).2, fun h' => by omega⟩
    · rw [← he]
      refine ⟨hX _ hx, fun h' => by omega, fun _ => ⟨_, hx, 1, Subgroup.one_mem _, by group⟩⟩
    · obtain ⟨hpG, -, hrep⟩ := ih _ (by omega) _ hp rfl
      obtain ⟨rr, hrr, n, hn, en⟩ := hrep hp1
      have key : ∀ {m m' : ℕ}, InG m → InG m' → mulT m m' = oneT → ofT m ∈ sub2T n₁ n₂ →
          fldT T t = conjT m m' (fldT T (R t).1) →
          InG (fldT T t) ∧ (d = 0 → ofT (fldT T t) ∈ H) ∧
            (1 ≤ d → ∃ rr < r, ∃ n ∈ sub2T n₁ n₂,
              ofT (fldT T t) = n * ofT (fldT X rr) * n⁻¹) := by
        intro m m' hm hm' emm hmS e
        rw [e]
        refine ⟨inG_conjT hm hm' hpG, fun h' => by omega, fun _ => ⟨rr, hrr, ofT m * n,
          Subgroup.mul_mem _ hmS hn, ?_⟩⟩
        rw [ofT_conjT hm hm' hpG emm, en]
        group
      rcases he with e | e
      · exact key h1 h1' e1 (Subgroup.subset_closure (by simp)) e
      · exact key h2 h2' e2 (Subgroup.subset_closure (by simp)) e

private theorem conj_pow (S : Set G) (g : G) (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    ∀ (k : ℕ), ∀ s ∈ S, g ^ k * s * (g ^ k)⁻¹ ∈ S := by
  intro k
  induction k with
  | zero => intro s hs; simpa using hs
  | succ k ih =>
    intro s hs
    have e : g ^ (k + 1) * s * (g ^ (k + 1))⁻¹ = g * (g ^ k * s * (g ^ k)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h _ (ih s hs)

theorem conj_closed (S : Set G) {a b : G} (ha : ∀ s ∈ S, a * s * a⁻¹ ∈ S)
    (hb : ∀ s ∈ S, b * s * b⁻¹ ∈ S) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set G), ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => intro s hs; simpa using hs
  | mul x y _ _ hx hy =>
    intro s hs
    have e : x * y * s * (x * y)⁻¹ = x * (y * s * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy s hs)
  | inv x _ hx =>
    have hpos : 0 < Nat.card G := Nat.card_pos
    have h1 : x * x ^ (Nat.card G - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_card_eq_one']
    rw [inv_eq_of_mul_eq_one_right h1]
    exact conj_pow S x hx _

theorem powT_spec {c : ℕ} (hc : InG c) : ∀ e : ℕ, InG (powT c e) ∧ ofT (powT c e) = ofT c ^ e
  | 0 => ⟨inG_oneT, by rw [pow_zero, ← ofT_oneT]; rfl⟩
  | e + 1 => by
    have eq : powT c (e + 1) = mulT (powT c e) c := rfl
    obtain ⟨h1, h2⟩ := powT_spec hc e
    rw [eq, ofT_mulT h1 hc, h2, pow_succ]
    exact ⟨inG_mulT h1 hc, rfl⟩

theorem evGo_mem {a b x : ℕ} {K : Subgroup G} (ha : InG a ∧ ofT a ∈ K) (hb : InG b ∧ ofT b ∈ K)
    (hx : InG x ∧ ofT x ∈ K) :
    ∀ (w : List (ℕ × ℕ)) (acc : ℕ), InG acc → ofT acc ∈ K → lettersOK w = true →
      InG (evGo a b x w acc) ∧ ofT (evGo a b x w acc) ∈ K
  | [], _, h1, h2, _ => ⟨h1, h2⟩
  | le :: w, acc, h1, h2, hw => by
    have e : evGo a b x (le :: w) acc = evGo a b x w (mulT acc (powT (letT a b x le.1) le.2)) :=
      rfl
    have hw' : (decide (le.1 < 3) && lettersOK w) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have hl : InG (letT a b x le.1) ∧ ofT (letT a b x le.1) ∈ K := by
      unfold letT
      split_ifs
      · exact ha
      · exact hb
      · exact hx
    obtain ⟨hp1, hp2⟩ := powT_spec hl.1 le.2
    rw [e]
    refine evGo_mem ha hb hx w _ (inG_mulT h1 hp1) ?_ hw'.2
    rw [ofT_mulT h1 hp1, hp2]
    exact K.mul_mem h2 (K.pow_mem hl.2 _)

theorem case_join {a b x g g' h₁ h₂ : ℕ} {w₁ w₂ : List (ℕ × ℕ)} (ha : InG a) (hb : InG b)
    (hx : InG x) (hg : InG g) (hg' : InG g') (hh1 : InG h₁) (hh2 : InG h₂)
    (hgg : mulT g g' = oneT) (ma : ofT (conjT g g' a) ∈ sub2T h₁ h₂)
    (mb : ofT (conjT g g' b) ∈ sub2T h₁ h₂) (mx : ofT (conjT g g' x) ∈ sub2T h₁ h₂)
    (hw1 : lettersOK w₁ = true) (hw2 : lettersOK w₂ = true)
    (e1 : evGo a b x w₁ oneT = conjT g' g h₁) (e2 : evGo a b x w₂ oneT = conjT g' g h₂) :
    sub2T a b ⊔ zpowers (ofT x) =
      (sub2T h₁ h₂).map (MulAut.conj (ofT g)⁻¹).toMonoidHom := by
  have hginv : ofT g' = (ofT g)⁻¹ := ofT_inv_of_mulT hg hg' hgg
  refine le_antisymm ?_ ?_
  · have key : ∀ k : ℕ, InG k → ofT (conjT g g' k) ∈ sub2T h₁ h₂ →
        ofT k ∈ (sub2T h₁ h₂).map (MulAut.conj (ofT g)⁻¹).toMonoidHom := by
      intro k hk hm
      rw [ofT_conjT hg hg' hk hgg] at hm
      refine ⟨_, hm, ?_⟩
      simp [mul_assoc]
    refine sup_le ?_ ?_
    · rw [sub2T, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact key _ ha ma
      · exact key _ hb mb
    · rw [Subgroup.zpowers_le]
      exact key _ hx mx
  · set K := sub2T a b ⊔ zpowers (ofT x)
    have hK : (InG a ∧ ofT a ∈ K) ∧ (InG b ∧ ofT b ∈ K) ∧ (InG x ∧ ofT x ∈ K) :=
      ⟨⟨ha, (le_sup_left : sub2T a b ≤ K) (Subgroup.subset_closure (by simp))⟩,
        ⟨hb, (le_sup_left : sub2T a b ≤ K) (Subgroup.subset_closure (by simp))⟩,
        ⟨hx, (le_sup_right : zpowers (ofT x) ≤ K) (Subgroup.mem_zpowers _)⟩⟩
    have hev : ∀ w, lettersOK w = true → ofT (evGo a b x w oneT) ∈ K := fun w hw =>
      (evGo_mem hK.1 hK.2.1 hK.2.2 w oneT inG_oneT (by rw [ofT_oneT]; exact K.one_mem) hw).2
    have hconj : ∀ h : ℕ, InG h → ofT (conjT g' g h) =
        (MulAut.conj (ofT g)⁻¹).toMonoidHom (ofT h) := by
      intro h hh
      unfold conjT
      rw [ofT_mulT (inG_mulT hg' hh) hg, ofT_mulT hg' hh, hginv]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    rw [sub2T, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · rw [← hconj _ hh1, ← e1]
      exact hev _ hw1
    · rw [← hconj _ hh2, ← e2]
      exact hev _ hw2

end CFSG.KC.Sp43K

end
