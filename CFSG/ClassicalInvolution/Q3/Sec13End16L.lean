module

public import CFSG.ClassicalInvolution.Q3.Sec13End16K
import CFSG.ClassicalInvolution.Q3.Sec13RecogQ8
public import CFSG.ClassicalInvolution.Q3.Sec13RecogS

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3

variable {G : Type} [Group G] [Finite G]

private theorem e16l_add_add_self (x y : ZMod 2) : x + y + x = y := by
  revert x y; decide

private theorem e16l_ofVec_vec {n : ℕ} (v : Fin n → ZMod 2) : (ofVec v).vec = v := rfl

private theorem e16l_ofVec_perm {n : ℕ} (v : Fin n → ZMod 2) : (ofVec v).perm = 1 := rfl

private theorem e16l_conj_ofVec {n : ℕ} (a : Wr n) (v : Fin n → ZMod 2) :
    a * ofVec v * a⁻¹ = ofVec (fun i => v (a.perm.symm i)) := by
  refine Wr.ext ?_ ?_
  · funext i
    simp only [mul_vec, inv_vec, e16l_ofVec_vec, mul_perm, e16l_ofVec_perm, mul_one,
      Equiv.apply_symm_apply]
    exact e16l_add_add_self _ _
  · simp [mul_perm, inv_perm, e16l_ofVec_perm]

private def e16l_w {n : ℕ} (l : Fin n) : Fin n → ZMod 2 := fun i => if i = l then 0 else 1

private theorem e16l_conj_w {n : ℕ} (a : Wr n) (l : Fin n) :
    a * ofVec (e16l_w l) * a⁻¹ = ofVec (e16l_w (a.perm l)) := by
  rw [e16l_conj_ofVec]
  congr 1
  funext i
  simp only [e16l_w, Equiv.symm_apply_eq]

private theorem e16l_perm_fix {n : ℕ} (a : Wr n) (l : Fin n)
    (h : a * ofVec (e16l_w l) * a⁻¹ = ofVec (e16l_w l)) : a.perm l = l := by
  rw [e16l_conj_w] at h
  have hv : e16l_w (a.perm l) = e16l_w l := congrArg Wr.vec h
  by_contra hne
  have := congrFun hv (a.perm l)
  simp [e16l_w, hne] at this

private theorem e16l_wsum_ofVec {n : ℕ} (v : Fin n → ZMod 2) : wsum (ofVec v) = ∑ i, v i := rfl

private theorem e16l_wsum_allOnes : wsum (allOnes 7) = 1 := by decide

private theorem e16l_zmod_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x + 1 = 0 := by
  revert x; decide

private theorem e16l_lift_unique {a b : Wr 7} (ha : wsum a = 0) (hb : wsum b = 0)
    (h : mkQ 7 a = mkQ 7 b) : a = b := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact inv_mul_eq_one.mp h1
  · exfalso
    have h2 : wsum (a⁻¹ * b) = 0 := by
      rw [wsum_mul, wsum_inv, ha, hb, add_zero]
    rw [h1, e16l_wsum_allOnes] at h2
    exact absurd h2 (by decide)

private theorem e16l_lift_exists (q : AEQ 7) : ∃ a : Wr 7, wsum a = 0 ∧ mkQ 7 a = q := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  by_cases ha : wsum a = 0
  · exact ⟨a, ha, rfl⟩
  · refine ⟨a * allOnes 7, ?_, ?_⟩
    · rw [wsum_mul, e16l_wsum_allOnes]
      exact e16l_zmod_ne_zero _ ha
    · show mkQ 7 (a * allOnes 7) = mkQ 7 a
      rw [mkQ_eq_iff]
      right
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_eq_of_mul_eq_one_right (allOnes_mul_self 7)

private noncomputable def e16l_lift7 : AEQ 7 →* Wr 7 where
  toFun q := (e16l_lift_exists q).choose
  map_one' := by
    refine e16l_lift_unique (e16l_lift_exists 1).choose_spec.1 wsum_one ?_
    rw [(e16l_lift_exists 1).choose_spec.2, map_one]
  map_mul' p q := by
    refine e16l_lift_unique (a := (e16l_lift_exists (p * q)).choose)
      (b := (e16l_lift_exists p).choose * (e16l_lift_exists q).choose)
      (e16l_lift_exists (p * q)).choose_spec.1 ?_ ?_
    · rw [wsum_mul, (e16l_lift_exists p).choose_spec.1, (e16l_lift_exists q).choose_spec.1,
        add_zero]
    · rw [map_mul, (e16l_lift_exists (p * q)).choose_spec.2,
        (e16l_lift_exists p).choose_spec.2, (e16l_lift_exists q).choose_spec.2]

private theorem e16l_lift7_mkQ (q : AEQ 7) : mkQ 7 (e16l_lift7 q) = q :=
  (e16l_lift_exists q).choose_spec.2

private theorem e16l_lift7_wsum (q : AEQ 7) : wsum (e16l_lift7 q) = 0 :=
  (e16l_lift_exists q).choose_spec.1

private theorem e16l_lift7_eq {q : AEQ 7} {a : Wr 7} (ha : wsum a = 0) (h : mkQ 7 a = q) :
    e16l_lift7 q = a :=
  e16l_lift_unique (e16l_lift7_wsum q) ha (by rw [e16l_lift7_mkQ, h])

private theorem e16l_exists_embed {n : ℕ} {ι : Fin 4 ↪ Fin n} {w : Wr n}
    (hw : SupportedOn w (Set.range ι)) : ∃ w0 : Wr 4, embed ι w0 = w := by
  classical
  have hmap : ∀ i : Fin 4, ∃ j : Fin 4, w.perm (ι i) = ι j := by
    intro i
    by_cases hi : w.perm (ι i) ∈ Set.range ι
    · obtain ⟨j, hj⟩ := hi
      exact ⟨j, hj.symm⟩
    · exfalso
      have h1 : w.perm (w.perm (ι i)) = w.perm (ι i) := (hw _ hi).2
      exact hi ⟨i, (w.perm.injective h1).symm⟩
  choose p0 hp0 using hmap
  have hinj : Function.Injective p0 := by
    intro i i' hii
    apply ι.injective
    apply w.perm.injective
    rw [hp0, hp0, hii]
  let e0 : Equiv.Perm (Fin 4) := Equiv.ofBijective p0 (Function.Injective.bijective_of_finite hinj)
  refine ⟨⟨fun k => w.vec (ι k), e0⟩, ?_⟩
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · by_cases hx : x ∈ Set.range ι
    · obtain ⟨k, rfl⟩ := hx
      rw [AE.embed_vec, AE.embedVec_apply]
    · rw [AE.embed_vec, AE.embedVec_of_not_mem ι _ hx]
      exact ((hw x hx).1).symm
  · by_cases hx : x ∈ Set.range ι
    · obtain ⟨k, rfl⟩ := hx
      rw [AE.embed_perm, AE.embedPerm_apply]
      exact (hp0 k).symm
    · rw [AE.embed_perm, AE.embedPerm_of_not_mem ι _ hx]
      exact ((hw x hx).2).symm

private theorem e16l_cand_mem : ∀ w0 : Wr 4, w0.perm * w0.perm = 1 →
    (∀ k, w0.vec k + w0.vec (w0.perm.symm k) = 1) → w0 ∈ kList ∨ w0 ∈ kStarList := by
  decide +kernel

private theorem e16l_zQ_vec : ∀ k : Fin 4, zQ.vec k = 1 := by decide

private theorem e16l_mem_memBar {α : Finset (Fin 7)} {h : α.card = 4} {a : Wr 7} {w0 : Wr 4}
    (hw : embed (AE.emb α h) w0 = a) (hsq : w0 * w0 = zQ) :
    mkQ 7 a ∈ AE.memBar α h true ∨ mkQ 7 a ∈ AE.memBar α h false := by
  have hperm : w0.perm * w0.perm = 1 := by
    have h1 := congrArg Wr.perm hsq
    rwa [mul_perm, show zQ.perm = 1 from rfl] at h1
  have hvec : ∀ k, w0.vec k + w0.vec (w0.perm.symm k) = 1 := by
    intro k
    have h1 := congrArg (fun x : Wr 4 => x.vec k) hsq
    simp only [mul_vec] at h1
    rw [h1]
    exact e16l_zQ_vec k
  have hmem := e16l_cand_mem w0 hperm hvec
  subst hw
  rcases hmem with hk | hk
  · exact Or.inl (TL4.AECov.mkQ_embed_mem_memBar α h true hk)
  · exact Or.inr (TL4.AECov.mkQ_embed_mem_memBar α h false hk)



section E16LB

open QuaternionGroup

private def e16l_cls : QuaternionGroup 2 → ZMod 2 × ZMod 2
  | .a k => (if k = 1 ∨ k = 3 then 1 else 0, 0)
  | .xa k => (if k = 1 ∨ k = 3 then 1 else 0, 1)

private def e16l_lin (cu cv p : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  (p.1 * cu.1 + p.2 * cv.1, p.1 * cu.2 + p.2 * cv.2)

private theorem e16l_cls_mul : ∀ g h : QuaternionGroup 2,
    e16l_cls (g * h) = e16l_cls g + e16l_cls h := by decide

private theorem e16l_fiber : ∀ g h : QuaternionGroup 2,
    e16l_cls h = e16l_cls g → h = g ∨ h = g * a 2 := by decide

private theorem e16l_gen : ∀ g : QuaternionGroup 2,
    ∃ n : Fin 4, ∃ m : Fin 2, g = a 1 ^ (n : ℕ) * xa 0 ^ (m : ℕ) := by decide

private theorem e16l_mat : ∀ cu cv : ZMod 2 × ZMod 2,
    e16l_lin cu cv (e16l_lin cu cv (e16l_lin cu cv (1, 0))) = (1, 0) →
    e16l_lin cu cv (e16l_lin cu cv (e16l_lin cu cv (0, 1))) = (0, 1) →
    (cu = (1, 0) ∧ cv = (0, 1)) ∨ (cu = (0, 1) ∧ cv = (1, 1)) ∨ (cu = (1, 1) ∧ cv = (1, 0)) := by
  decide

private theorem e16l_a2_sq : a 2 * a 2 = (1 : QuaternionGroup 2) := by decide

private theorem e16l_a2_ne_one : (a 2 : QuaternionGroup 2) ≠ 1 := by decide

private theorem e16l_cls_a1 : e16l_cls (a 1) = (1, 0) := by decide

private theorem e16l_cls_x0 : e16l_cls (xa 0) = (0, 1) := by decide

private theorem e16l_lin_add (cu cv p q : ZMod 2 × ZMod 2) :
    e16l_lin cu cv (p + q) = e16l_lin cu cv p + e16l_lin cu cv q := by
  simp only [e16l_lin, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  congr 1 <;> ring

private theorem e16l_hom_pow {A : Type*} [AddCommGroup A] (H : QuaternionGroup 2 → A)
    (hH : ∀ g h, H (g * h) = H g + H h) (g : QuaternionGroup 2) (k : ℕ) :
    H (g ^ k) = k • H g := by
  have h1 : H 1 = 0 := by
    have := hH 1 1
    rw [mul_one] at this
    simpa using this
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [pow_succ, hH, ih, succ_nsmul]

private theorem e16l_eq_of_gen {A : Type*} [AddCommGroup A] (F G : QuaternionGroup 2 → A)
    (hF : ∀ g h, F (g * h) = F g + F h) (hG : ∀ g h, G (g * h) = G g + G h)
    (h1 : F (a 1) = G (a 1)) (h2 : F (xa 0) = G (xa 0)) : ∀ g, F g = G g := by
  intro g
  obtain ⟨n, m, rfl⟩ := e16l_gen g
  rw [hF, hG, e16l_hom_pow F hF, e16l_hom_pow F hF, e16l_hom_pow G hG, e16l_hom_pow G hG,
    h1, h2]

private theorem e16l_q8_group {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (θ : QuaternionGroup 2 →* QuaternionGroup 2)
    (h3 : ∀ g, θ (θ (θ g)) = g) (hne : ∃ g, θ g ≠ g)
    (f : QuaternionGroup 2 → A) (hf : ∀ g h, f (g * h) = f g + f h)
    (hθf : ∀ g, f (θ g) = f g) : ∀ g, f g = 0 := by
  have hA : ∀ g, e16l_cls (θ g) = e16l_lin (e16l_cls (θ (a 1))) (e16l_cls (θ (xa 0)))
      (e16l_cls g) := by
    intro g
    refine e16l_eq_of_gen (fun g => e16l_cls (θ g))
      (fun g => e16l_lin (e16l_cls (θ (a 1))) (e16l_cls (θ (xa 0))) (e16l_cls g))
      ?_ ?_ ?_ ?_ g
    · intro g h
      simp only [map_mul, e16l_cls_mul, e16l_lin_add]
    · intro g h
      simp only [e16l_cls_mul, e16l_lin_add]
    · simp only [e16l_cls_a1, e16l_lin]
      simp
    · simp only [e16l_cls_x0, e16l_lin]
      simp
  have hM : ∀ g, e16l_lin (e16l_cls (θ (a 1))) (e16l_cls (θ (xa 0)))
      (e16l_lin (e16l_cls (θ (a 1))) (e16l_cls (θ (xa 0)))
        (e16l_lin (e16l_cls (θ (a 1))) (e16l_cls (θ (xa 0))) (e16l_cls g))) = e16l_cls g := by
    intro g
    rw [← hA, ← hA, ← hA, h3]
  have hcase := e16l_mat (e16l_cls (θ (a 1))) (e16l_cls (θ (xa 0)))
    (by rw [← e16l_cls_a1, hM]) (by rw [← e16l_cls_x0, hM])
  have hF : ∀ g, f g = (e16l_cls g).1 • f (a 1) + (e16l_cls g).2 • f (xa 0) := by
    intro g
    refine e16l_eq_of_gen f
      (fun g => (e16l_cls g).1 • f (a 1) + (e16l_cls g).2 • f (xa 0)) hf ?_ ?_ ?_ g
    · intro g h
      rw [e16l_cls_mul]
      simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
    · simp [e16l_cls_a1]
    · simp [e16l_cls_x0]
  have hu : (e16l_cls (θ (a 1))).1 • f (a 1) + (e16l_cls (θ (a 1))).2 • f (xa 0) = f (a 1) := by
    rw [← hF, hθf]
  have hv : (e16l_cls (θ (xa 0))).1 • f (a 1) + (e16l_cls (θ (xa 0))).2 • f (xa 0)
      = f (xa 0) := by
    rw [← hF, hθf]
  have hfin : f (a 1) = 0 → f (xa 0) = 0 → ∀ g, f g = 0 := by
    intro h1 h2 g
    rw [hF g, h1, h2]
    simp
  rcases hcase with ⟨hu1, hv1⟩ | ⟨hu1, hv1⟩ | ⟨hu1, hv1⟩
  ·
    exfalso
    have hcls : ∀ g, e16l_cls (θ g) = e16l_cls g := by
      intro g
      rw [hA, hu1, hv1]
      simp [e16l_lin]
    have hfib : ∀ g, θ g = g ∨ θ g = g * a 2 := fun g => e16l_fiber g (θ g) (hcls g)
    have ha2 : θ (a 2) = a 2 := by
      rcases hfib (a 2) with h | h
      · exact h
      · exfalso
        have h1 : θ (θ (θ (a 2))) = a 2 := h3 _
        rw [h, e16l_a2_sq, map_one, map_one] at h1
        exact e16l_a2_ne_one h1.symm
    have hsq : ∀ g, θ (θ g) = g := by
      intro g
      rcases hfib g with h | h
      · rw [h, h]
      · rw [h, map_mul, ha2, h, mul_assoc, e16l_a2_sq, mul_one]
    have hid : ∀ g, θ g = g := fun g => by
      have h1 := hsq (θ g)
      rw [h3 g] at h1
      exact h1.symm
    obtain ⟨g, hg⟩ := hne
    exact hg (hid g)
  ·
    rw [hu1] at hu
    rw [hv1] at hv
    simp at hu hv
    exact hfin hv (hu.trans hv)
  ·
    rw [hu1] at hu
    rw [hv1] at hv
    simp at hu hv
    exact hfin (hv.trans hu) hu


end E16LB

private theorem e16l_three_fix (s : Equiv.Perm (Fin 7)) {p q : Fin 7} (hpq : p ≠ q)
    (hsp : s p = p ∨ s p = q) (hsq : s q = p ∨ s q = q) {N : ℕ} (hN : Odd N)
    (hsN : s ^ N = 1) : s p = p ∧ s q = q := by
  rcases hsp with hp | hp
  · rcases hsq with hq | hq
    · exact absurd (s.injective (hq.trans hp.symm)).symm hpq
    · exact ⟨hp, hq⟩
  · rcases hsq with hq | hq
    · exfalso
      obtain ⟨t, rfl⟩ := hN
      have hs2 : (s ^ 2) p = p := by rw [sq, Equiv.Perm.mul_apply, hp, hq]
      have h2 : ∀ r : ℕ, (s ^ (2 * r + 1)) p = s p := by
        intro r
        induction r with
        | zero => simp
        | succ r ih =>
          rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by ring, pow_add, Equiv.Perm.mul_apply,
            hs2, ih]
      have h3 := h2 t
      rw [hsN, Equiv.Perm.one_apply, hp] at h3
      exact hpq h3
    · exact absurd (s.injective (hp.trans hq.symm)) hpq

private theorem e16l_set_fix (s : Equiv.Perm (Fin 7)) {S : Finset (Fin 7)} (hS3 : S.card = 3)
    (hsS : ∀ l ∈ S, s l ∈ S) {m : Fin 7} (hmS : m ∈ S) (hsm : s m = m) {N : ℕ} (hN : Odd N)
    (hsN : s ^ N = 1) : ∀ l ∈ S, s l = l := by
  obtain ⟨x, y, w, hxy, hxw, hyw, rfl⟩ := Finset.card_eq_three.mp hS3
  have hnm : ∀ p, p ≠ m → s p ≠ m := fun p hp hsp => hp (s.injective (hsp.trans hsm.symm))
  have hmem : ∀ p, s p ∈ ({x, y, w} : Finset (Fin 7)) ↔ (s p = x ∨ s p = y ∨ s p = w) := by
    intro p
    simp [Finset.mem_insert]
  rcases Finset.mem_insert.mp hmS with rfl | hmS'
  ·
    have hy : s y = y ∨ s y = w := by
      rcases (hmem y).mp (hsS y (by simp)) with h | h | h
      · exact absurd h (hnm _ (Ne.symm hxy))
      · exact Or.inl h
      · exact Or.inr h
    have hw : s w = y ∨ s w = w := by
      rcases (hmem w).mp (hsS w (by simp)) with h | h | h
      · exact absurd h (hnm _ (Ne.symm hxw))
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨h1, h2⟩ := e16l_three_fix s hyw hy hw hN hsN
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact hsm
    · exact h1
    · exact h2
  rcases Finset.mem_insert.mp hmS' with rfl | hmS''
  ·
    have hx : s x = x ∨ s x = w := by
      rcases (hmem x).mp (hsS x (by simp)) with h | h | h
      · exact Or.inl h
      · exact absurd h (hnm _ hxy)
      · exact Or.inr h
    have hw : s w = x ∨ s w = w := by
      rcases (hmem w).mp (hsS w (by simp)) with h | h | h
      · exact Or.inl h
      · exact absurd h (hnm _ (Ne.symm hyw))
      · exact Or.inr h
    obtain ⟨h1, h2⟩ := e16l_three_fix s hxw hx hw hN hsN
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact h1
    · exact hsm
    · exact h2
  ·
    rw [Finset.mem_singleton] at hmS''
    subst hmS''
    have hx : s x = x ∨ s x = y := by
      rcases (hmem x).mp (hsS x (by simp)) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hnm _ hxw)
    have hy : s y = x ∨ s y = y := by
      rcases (hmem y).mp (hsS y (by simp)) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hnm _ hyw)
    obtain ⟨h1, h2⟩ := e16l_three_fix s hxy hx hy hN hsN
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact hsm

private theorem e16l_conj_vec_fix {n : ℕ} (A B : Wr n) (i : Fin n) (hA : A.perm i = i)
    (hB : B.perm i = i) : (A * B * A⁻¹).vec i = B.vec i := by
  have hA' : A.perm.symm i = i := by
    rw [Equiv.symm_apply_eq]
    exact hA.symm
  have hAB : (A * B).perm.symm i = i := by
    rw [mul_perm, Equiv.symm_apply_eq, Equiv.Perm.mul_apply, hB, hA]
  rw [mul_vec, inv_vec, hAB, hA, mul_vec, hA']
  exact e16l_add_add_self _ _

private theorem e16l_prod_perm {G' : Type*} [Group G'] (f : Fin 7 → G')
    (hc : ∀ i j, f i * f j = f j * f i) (σ : Equiv.Perm (Fin 7)) :
    (List.ofFn (f ∘ σ)).prod = (List.ofFn f).prod := by
  apply List.Perm.prod_eq' (Equiv.Perm.ofFn_comp_perm σ f)
  rw [List.pairwise_ofFn]
  intro i j _
  exact hc _ _

private theorem e16l_add_self_zmod (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

private theorem e16l_w_even (l : Fin 7) : ∑ i, e16l_w l i = 0 := by
  fin_cases l <;> decide

private theorem e16l_sum_single (l : Fin 7) :
    ∑ i, (Pi.single l (1 : ZMod 2) : Fin 7 → ZMod 2) i = 1 := by
  rw [Finset.sum_pi_single']
  simp

private theorem e16l_q8_class : ∀ q : QuaternionGroup 2,
    q = 1 ∨ q = QuaternionGroup.a 2 ∨ q * q = QuaternionGroup.a 2 := by
  decide

private theorem e16l_a2_ne_one' : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide

private theorem e16l_pow_fix (s : Equiv.Perm (Fin 7)) (S : Finset (Fin 7))
    (hs : ∀ l ∈ S, s l = l) (n : ℕ) : ∀ l ∈ S, (s ^ n) l = l := by
  intro l hl
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, hs l hl]; exact ih

private theorem e16l_aux {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {z u e g : G}
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) {H : Subgroup G}
    {σ : H →* Equiv.Perm (Fin 7)} {β : Multiplicative (Fin 7 → ZMod 2) →* G}
    (hS : AESplitHyp (zGroup Ω) H σ β) (hA : σ.range = alternatingGroup (Fin 7))
    (hβ : ∀ i, ∃ x : G, β (Multiplicative.ofAdd (Pi.single i 1)) = x * e * x⁻¹)
    (hpts : ∃ (pt : Fin 7 → G) (σK : G →* Equiv.Perm (Fin 7)),
      Function.Injective pt ∧ (∀ i, pt i ∈ zGroup Ω) ∧ pt 0 = e ∧
      (∀ i, ∃ x : G, pt i = x * e * x⁻¹) ∧ (List.ofFn pt).prod = 1 ∧
      Subgroup.closure (Set.range pt) = zGroup Ω ∧
      (∀ (x : G) (i : Fin 7), x * pt i * x⁻¹ = pt (σK x i)) ∧
      σK.ker = Subgroup.centralizer (zGroup Ω : Set G) ∧ σK.range = alternatingGroup (Fin 7) ∧
      (∀ M ∈ Ω, ∀ b : G, IsUniqueInvolution M b →
        ∃ i j k : Fin 7, i < j ∧ j < k ∧ b = pt i * pt j * pt k ∧
          ∀ l : Fin 7, (l = i ∨ l = j ∨ l = k) ↔ M ≤ Subgroup.centralizer ({pt l} : Set G)))
    (hthree : ∃ x : G, x ∈ pSpan (Generic.centMembers Ω e) ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
      (∃ a : ℕ, x ^ 3 ^ a = 1) ∧ (∃ k ∈ K, x * k ≠ k * x)) :
    ∃ K₀ ∈ Ω, ∃ (α : Finset (Fin 7)) (hα : α.card = 4) (b : Bool) (φ : G →* AE.AEQ 7),
      (∀ f : Multiplicative (Fin 7 → ZMod 2), ∑ i, f.toAdd i = 0 →
        φ (β f) = AE.mkQ 7 (AE.Wr.ofVec f.toAdd)) ∧
      (∀ x : H, φ x = AE.mkQ 7 (AE.Wr.ofPerm (σ x))) ∧ K₀.map φ = AE.memBar α hα b := by
  classical
  have hK : K ∈ Ω := c.twin.mem
  have hKinv : IsUniqueInvolution K z := c.twin.isInv
  have hK8 : Nat.card K = 8 := h.card_eq_eight hK
  have hKz : z ≠ 1 := hKinv.ne_one
  have hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have heK : ∀ k ∈ K, k * e = e * k := by
    intro k hk
    have he := (Sit16.e_mem_centralizer c h).1
    rw [Subgroup.mem_centralizer_iff] at he
    exact he k hk
  obtain ⟨pt, σK, hpinj, hptD, hpt0, -, hprod, -, hact, -, -, htriple⟩ := hpts
  choose xl hxl using hβ
  obtain ⟨P, hP⟩ : ∃ P : Fin 7 → G, ∀ l, P l = β (Multiplicative.ofAdd (Pi.single l 1)) :=
    ⟨fun l => β (Multiplicative.ofAdd (Pi.single l 1)), fun _ => rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : Fin 7 → Fin 7, ∀ l, τ l = σK (xl l) 0 :=
    ⟨fun l => σK (xl l) 0, fun _ => rfl⟩
  have hτP : ∀ l, pt (τ l) = P l := by
    intro l
    rw [hτdef, ← hact, hpt0, hP, hxl l]
  have hPsq : ∀ l, P l * P l = 1 := by
    intro l
    have h0 : (Pi.single l (1 : ZMod 2) + Pi.single l 1 : Fin 7 → ZMod 2) = 0 := by
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact e16l_add_self_zmod _
    rw [hP, ← map_mul, ← ofAdd_add, h0, ofAdd_zero, map_one]
  have hPinj : ∀ l m, P l = P m → l = m := by
    intro l m hlm
    by_contra hne
    have hone : β (Multiplicative.ofAdd (Pi.single l 1 + Pi.single m 1)) = 1 := by
      rw [ofAdd_add, map_mul, ← hP l, ← hP m, hlm]
      exact hPsq m
    have hsum : ∑ i, (Pi.single l (1 : ZMod 2) + Pi.single m 1 : Fin 7 → ZMod 2) i = 0 := by
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, e16l_sum_single, e16l_sum_single]
      decide
    rcases (hS.eq_one_iff _ (by simpa using hsum)).mp hone with h1 | h1
    · have := congrFun h1 l
      simp [Pi.single_apply, hne] at this
    · obtain ⟨i, hil, him⟩ : ∃ i : Fin 7, i ≠ l ∧ i ≠ m := by
        have key : ∀ l' m' : Fin 7, l' ≠ m' → ∃ i : Fin 7, i ≠ l' ∧ i ≠ m' := by decide
        exact key l m hne
      have := congrFun h1 i
      simp [Pi.single_apply, hil, him] at this
  have hτinj : Function.Injective τ := fun l m hlm => hPinj l m (by rw [← hτP l, ← hτP m, hlm])
  have hτsurj : Function.Surjective τ := Finite.surjective_of_injective hτinj
  let τe : Equiv.Perm (Fin 7) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  have hτe : ∀ l, τe l = τ l := fun l => rfl
  have hβπ : β (Multiplicative.ofAdd (fun _ : Fin 7 => (1 : ZMod 2))) = 1 := by
    have hsplit : Multiplicative.ofAdd (fun _ : Fin 7 => (1 : ZMod 2)) =
        Multiplicative.ofAdd (Pi.single 0 1) * Multiplicative.ofAdd (Pi.single 1 1) *
        Multiplicative.ofAdd (Pi.single 2 1) * Multiplicative.ofAdd (Pi.single 3 1) *
        Multiplicative.ofAdd (Pi.single 4 1) * Multiplicative.ofAdd (Pi.single 5 1) *
        Multiplicative.ofAdd (Pi.single 6 1) := by
      simp only [← ofAdd_add]
      congr 1
      decide
    rw [hsplit, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
    simp only [← hP]
    have hc : ∀ i j, pt i * pt j = pt j * pt i := fun i j => hcomm _ (hptD i) _ (hptD j)
    have h1 := e16l_prod_perm pt hc τe
    have h2 : (List.ofFn (pt ∘ τe)).prod = P 0 * P 1 * P 2 * P 3 * P 4 * P 5 * P 6 := by
      simp [List.ofFn_succ, Function.comp_def, hτe, hτP, mul_assoc]
    rw [h2, hprod] at h1
    exact h1
  obtain ⟨i, j, k, hij, hjk, hzijk, hiff⟩ := htriple K hK z hKinv
  obtain ⟨a1, ha1⟩ := hτsurj i
  obtain ⟨b1, hb1⟩ := hτsurj j
  obtain ⟨c1, hc1⟩ := hτsurj k
  have hzP : z = P a1 * P b1 * P c1 := by
    rw [hzijk, ← hτP a1, ← hτP b1, ← hτP c1, ha1, hb1, hc1]
  have hmemP : ∀ l, K ≤ Subgroup.centralizer ({P l} : Set G) ↔
      (l = a1 ∨ l = b1 ∨ l = c1) := by
    intro l
    have := hiff (τ l)
    rw [hτP l, ← ha1, ← hb1, ← hc1, hτinj.eq_iff, hτinj.eq_iff, hτinj.eq_iff] at this
    exact this.symm
  obtain ⟨Sset, hSdef⟩ : ∃ S : Finset (Fin 7), S = {a1, b1, c1} := ⟨_, rfl⟩
  have hmemS : ∀ l, l ∈ Sset ↔ K ≤ Subgroup.centralizer ({P l} : Set G) := by
    intro l
    rw [hmemP, hSdef]
    simp
  have hab : a1 ≠ b1 := fun h' => hij.ne (by rw [← ha1, ← hb1, h'])
  have hac : a1 ≠ c1 := fun h' => (lt_trans hij hjk).ne (by rw [← ha1, ← hc1, h'])
  have hbc : b1 ≠ c1 := fun h' => hjk.ne (by rw [← hb1, ← hc1, h'])
  have hScard : Sset.card = 3 := by
    rw [hSdef, Finset.card_eq_three]
    exact ⟨a1, b1, c1, hab, hac, hbc, rfl⟩
  have hγcard : (Sset)ᶜ.card = 4 := by
    rw [Finset.card_compl, hScard]
    rfl
  obtain ⟨vγ, hvγ⟩ : ∃ v : Fin 7 → ZMod 2, v = fun i => Pi.single a1 (1 : ZMod 2) i +
      Pi.single b1 1 i + Pi.single c1 1 i + 1 := ⟨_, rfl⟩
  have hvγ_even : ∑ i, vγ i = 0 := by
    simp only [hvγ, Pi.add_apply]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      e16l_sum_single, e16l_sum_single, e16l_sum_single]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide
  have hzβ : z = β (Multiplicative.ofAdd vγ) := by
    have hfun : Multiplicative.ofAdd vγ = Multiplicative.ofAdd (Pi.single a1 1) *
        Multiplicative.ofAdd (Pi.single b1 1) * Multiplicative.ofAdd (Pi.single c1 1) *
        Multiplicative.ofAdd (fun _ : Fin 7 => (1 : ZMod 2)) := by
      rw [hvγ]
      simp only [← ofAdd_add]
      rfl
    rw [hfun, map_mul, map_mul, map_mul, hβπ, mul_one, hzP, hP, hP, hP]
  have hγmem : ∀ i, i ∈ (Sset)ᶜ ↔ i ≠ a1 ∧ i ≠ b1 ∧ i ≠ c1 := by
    intro i
    rw [Finset.mem_compl, hSdef]
    simp
  have hvγ_range : ∀ i, vγ i = if i ∈ Set.range (AE.emb (Sset)ᶜ hγcard) then 1 else 0 := by
    intro i
    simp only [hvγ, AE.range_emb, Finset.mem_coe, hγmem]
    by_cases h1 : i = a1 <;> by_cases h2 : i = b1 <;> by_cases h3 : i = c1 <;>
      simp [Pi.single_apply, h1, h2, h3, hab, hac, hbc, Ne.symm hab, Ne.symm hac,
        Ne.symm hbc] <;> decide
  obtain ⟨φ, hφinj, -, hφβ, hφH⟩ := hS.exists_hom_aeModel hA
  obtain ⟨L, hLdef⟩ : ∃ L : G →* AE.Wr 7, L = e16l_lift7.comp φ := ⟨_, rfl⟩
  have hLmk : ∀ g, AE.mkQ 7 (L g) = φ g := by
    intro g
    rw [hLdef]
    exact e16l_lift7_mkQ (φ g)
  have hLinj : Function.Injective L := by
    intro g g' hgg
    apply hφinj
    rw [← hLmk g, ← hLmk g', hgg]
  have hLβ : ∀ f : Multiplicative (Fin 7 → ZMod 2), ∑ i, f.toAdd i = 0 →
      L (β f) = AE.Wr.ofVec f.toAdd := by
    intro f hf
    rw [hLdef]
    show e16l_lift7 (φ (β f)) = _
    exact e16l_lift7_eq ((e16l_wsum_ofVec _).trans hf) (hφβ f hf).symm
  have hPw : ∀ l, P l = β (Multiplicative.ofAdd (e16l_w l)) := by
    intro l
    have hfun : Multiplicative.ofAdd (e16l_w l) = Multiplicative.ofAdd (Pi.single l 1) *
        Multiplicative.ofAdd (fun _ : Fin 7 => (1 : ZMod 2)) := by
      rw [← ofAdd_add]
      congr 1
      funext i
      by_cases hi : i = l
      · subst hi
        simp [e16l_w] <;> decide
      · simp [e16l_w, hi, Pi.single_apply]
    rw [hP, hfun, map_mul, hβπ, mul_one]
  have hLP : ∀ l, L (P l) = AE.Wr.ofVec (e16l_w l) := by
    intro l
    rw [hPw l, hLβ (Multiplicative.ofAdd (e16l_w l)) (e16l_w_even l)]
    rfl
  have hconjP : ∀ g l, g * P l * g⁻¹ = P ((L g).perm l) := by
    intro g l
    apply hLinj
    rw [map_mul, map_mul, map_inv, hLP, e16l_conj_w, hLP]
  have hKfix : ∀ k ∈ K, ∀ l ∈ Sset, (L k).perm l = l := by
    intro k hk l hl
    have hc : k * P l = P l * k := Subgroup.mem_centralizer_singleton_iff.mp ((hmemS l).mp hl hk)
    apply hPinj
    rw [← hconjP k l, hc, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨x, hxpS, hxN, ⟨aa, haa⟩, ⟨k0, hk0, hxk0⟩⟩ := hthree
  have hxC : x * e = e * x := by
    have hle : pSpan (Generic.centMembers Ω e) ≤ Subgroup.centralizer ({e} : Set G) :=
      pSpan_le (fun L' hL' => hL'.2)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hxpS)
  obtain ⟨m, hm⟩ := hτsurj 0
  have hPm : P m = e := by rw [← hτP m, hm, hpt0]
  have hmS : m ∈ Sset := (hmemS m).mpr fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [hPm]; exact heK k hk)
  have hxm : (L x).perm m = m := by
    apply hPinj
    rw [← hconjP x m, hPm, hxC, mul_inv_cancel_right]
  have hxS : ∀ l ∈ Sset, (L x).perm l ∈ Sset := by
    intro l hl
    rw [hmemS] at hl ⊢
    intro k hk
    have hk' : x⁻¹ * k * x ∈ K := by
      refine (Subgroup.mem_normalizer_iff.mp hxN _).mpr ?_
      have : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
      rw [this]
      exact hk
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hl hk')
    rw [Subgroup.mem_centralizer_singleton_iff, ← hconjP x l]
    calc k * (x * P l * x⁻¹) = x * ((x⁻¹ * k * x) * P l) * x⁻¹ := by group
      _ = x * (P l * (x⁻¹ * k * x)) * x⁻¹ := by rw [hc]
      _ = (x * P l * x⁻¹) * k := by group
  have hpow3 : ∀ n : ℕ, (L x ^ n).perm = (L x).perm ^ n := fun n => map_pow (AE.permHom 7) (L x) n
  have hsN : (L x).perm ^ 3 ^ aa = 1 := by
    have h1 : L x ^ 3 ^ aa = 1 := by rw [← map_pow, haa, map_one]
    have h2 : (L x ^ 3 ^ aa).perm = 1 := by simp [h1, one_perm]
    rw [hpow3] at h2
    exact h2
  have hfixS : ∀ l ∈ Sset, (L x).perm l = l :=
    e16l_set_fix (L x).perm hScard hxS hmS hxm (Odd.pow (by decide)) hsN
  have hex : ∃ j : ℕ, ∀ k ∈ K, x ^ 3 ^ j * k * (x ^ 3 ^ j)⁻¹ = k := by
    refine ⟨aa, fun k _ => ?_⟩
    rw [haa, one_mul, inv_one, mul_one]
  have hj0ne : Nat.find hex ≠ 0 := by
    intro h0
    have h1 := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at h1
    apply hxk0
    have h2 := h1 k0 hk0
    calc x * k0 = x * k0 * x⁻¹ * x := by group
      _ = k0 * x := by rw [h2]
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero hj0ne
  have hnotj : ¬ ∀ k ∈ K, x ^ 3 ^ j * k * (x ^ 3 ^ j)⁻¹ = k := fun hP' =>
    Nat.find_min hex (by omega) hP'
  have hcube : ∀ k ∈ K, (x ^ 3 ^ j) ^ 3 * k * ((x ^ 3 ^ j) ^ 3)⁻¹ = k := by
    intro k hk
    have h1 := Nat.find_spec hex k hk
    rw [hj, pow_succ, pow_mul] at h1
    exact h1
  have hnorm_pow : ∀ n : ℕ, ∀ k ∈ K, x ^ 3 ^ n * k * (x ^ 3 ^ n)⁻¹ ∈ K := by
    intro n k hk
    have hxn : x ^ 3 ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hxN _
    exact (Subgroup.mem_normalizer_iff.mp hxn k).mp hk
  obtain ⟨y, hydef⟩ : ∃ y : G, y = x ^ 3 ^ j := ⟨_, rfl⟩
  have hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K := fun k hk => by rw [hydef]; exact hnorm_pow j k hk
  have hy3 : ∀ k ∈ K, y * (y * (y * k * y⁻¹) * y⁻¹) * y⁻¹ = k := by
    intro k hk
    have h1 := hcube k hk
    rw [hydef]
    calc x ^ 3 ^ j * (x ^ 3 ^ j * (x ^ 3 ^ j * k * (x ^ 3 ^ j)⁻¹) * (x ^ 3 ^ j)⁻¹) *
          (x ^ 3 ^ j)⁻¹ = (x ^ 3 ^ j) ^ 3 * k * ((x ^ 3 ^ j) ^ 3)⁻¹ := by group
      _ = k := h1
  have hynon : ∃ k ∈ K, y * k * y⁻¹ ≠ k := by
    push_neg at hnotj
    obtain ⟨k, hk, hne⟩ := hnotj
    exact ⟨k, hk, by rw [hydef]; exact hne⟩
  have hLy : L y = (L x) ^ 3 ^ j := by rw [hydef, map_pow]
  have hyfix : ∀ l ∈ Sset, (L y).perm l = l := by
    intro l hl
    rw [hLy, hpow3]
    exact e16l_pow_fix (L x).perm Sset hfixS _ l hl
  obtain ⟨fS, hfS⟩ : ∃ fS : G → Fin 7 → ZMod 2,
      ∀ g i, fS g i = if i ∈ Sset then (L g).vec i else 0 := ⟨_, fun _ _ => rfl⟩
  have hfS_mul : ∀ k ∈ K, ∀ k' ∈ K, fS (k * k') = fS k + fS k' := by
    intro k hk k' hk'
    funext i
    rw [Pi.add_apply, hfS, hfS, hfS, map_mul]
    split_ifs with hi
    · have hsymm : (L k).perm.symm i = i := by
        rw [Equiv.symm_apply_eq]
        exact (hKfix k hk i hi).symm
      rw [mul_vec, hsymm]
    · simp
  have hfS_conj : ∀ k ∈ K, fS (y * k * y⁻¹) = fS k := by
    intro k hk
    funext i
    rw [hfS, hfS]
    split_ifs with hi
    · have h1 : L (y * k * y⁻¹) = L y * L k * (L y)⁻¹ := by rw [map_mul, map_mul, map_inv]
      rw [h1]
      exact e16l_conj_vec_fix (L y) (L k) i (hyfix i hi) (hKfix k hk i hi)
    · rfl
  obtain ⟨kk, hkk1, ⟨e8⟩⟩ := h.isQuatSub_of_mem hK
  have hkk : kk = 1 := by
    haveI : NeZero (2 ^ kk) := ⟨by positivity⟩
    have h1 : Nat.card K = 4 * 2 ^ kk := by
      rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h2 : 2 ^ kk = 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h2)
  subst hkk
  let e : K ≃* QuaternionGroup 2 := e8
  let θK : K →* K :=
    { toFun := fun k => ⟨y * k * y⁻¹, hyK k k.2⟩
      map_one' := Subtype.ext (by simp only [Subgroup.coe_mk, OneMemClass.coe_one]; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mk, Subgroup.coe_mul]; group) }
  have hθK3 : ∀ k : K, θK (θK (θK k)) = k := fun k => Subtype.ext (hy3 k k.2)
  let θQ : QuaternionGroup 2 →* QuaternionGroup 2 :=
    e.toMonoidHom.comp (θK.comp e.symm.toMonoidHom)
  have h3Q : ∀ q, θQ (θQ (θQ q)) = q := by
    intro q
    show e (θK (e.symm (e (θK (e.symm (e (θK (e.symm q)))))))) = q
    simp only [MulEquiv.symm_apply_apply]
    rw [hθK3]
    simp
  have hneQ : ∃ q, θQ q ≠ q := by
    obtain ⟨k, hk, hyk⟩ := hynon
    refine ⟨e ⟨k, hk⟩, fun heq => hyk ?_⟩
    have h1 : θQ (e ⟨k, hk⟩) = e (θK ⟨k, hk⟩) := by simp [θQ]
    rw [h1] at heq
    have h2 := e.injective heq
    exact congrArg Subtype.val h2
  let fQ : QuaternionGroup 2 → (Fin 7 → ZMod 2) := fun q => fS (e.symm q : G)
  have hfQ : ∀ q q', fQ (q * q') = fQ q + fQ q' := by
    intro q q'
    simp only [fQ, map_mul, Subgroup.coe_mul]
    exact hfS_mul _ (e.symm q).2 _ (e.symm q').2
  have hθfQ : ∀ q, fQ (θQ q) = fQ q := by
    intro q
    have h1 : ((e.symm (θQ q) : K) : G) = y * ((e.symm q : K) : G) * y⁻¹ := by
      simp [θQ, θK]
    simp only [fQ]
    rw [h1]
    exact hfS_conj _ (e.symm q).2
  have hQ0 := e16l_q8_group θQ h3Q hneQ fQ hfQ hθfQ
  have hvan : ∀ k ∈ K, ∀ i ∈ Sset, (L k).vec i = 0 := by
    intro k hk i hi
    have h1 := hQ0 (e ⟨k, hk⟩)
    have h2 : fS k = 0 := by simpa [fQ] using h1
    have h3 := congrFun h2 i
    rw [hfS, if_pos hi] at h3
    exact h3
  have hsupp : ∀ k ∈ K, AE.SupportedOn (L k) (Set.range (AE.emb (Sset)ᶜ hγcard)) := by
    intro k hk i hi
    rw [AE.range_emb, Finset.mem_coe] at hi
    have hiS : i ∈ Sset := by
      by_contra hc
      exact hi (Finset.mem_compl.mpr hc)
    exact ⟨hvan k hk i hiS, hKfix k hk i hiS⟩
  have hLz : L z = AE.zOf (AE.emb (Sset)ᶜ hγcard) := by
    have hz' : L z = AE.Wr.ofVec vγ := by
      rw [hzβ]
      exact hLβ (Multiplicative.ofAdd vγ) hvγ_even
    rw [hz']
    refine AE.Wr.ext (funext fun i => ?_) ?_
    · show vγ i = (AE.zOf (AE.emb (Sset)ᶜ hγcard)).vec i
      rw [hvγ_range i, AE.zOf_vec_apply]
    · show (AE.Wr.ofVec vγ).perm = (AE.zOf (AE.emb (Sset)ᶜ hγcard)).perm
      rw [AE.zOf_perm]
      rfl
  have hz1 : e ⟨z, hKinv.mem⟩ = QuaternionGroup.a 2 := by
    rcases e16l_q8_class (e ⟨z, hKinv.mem⟩) with h2 | h2 | h2
    · have hz0 : z = 1 := congrArg Subtype.val (e.injective (h2.trans (map_one e).symm))
      exact absurd hz0 hKz
    · exact h2
    · have hsq : (⟨z, hKinv.mem⟩ * ⟨z, hKinv.mem⟩ : K) = 1 := Subtype.ext hKinv.sq
      rw [← map_mul, hsq, map_one] at h2
      exact absurd h2.symm e16l_a2_ne_one'
  have hmemK : ∀ k ∈ K, AE.mkQ 7 (L k) ∈ AE.memBar (Sset)ᶜ hγcard true ∨
      AE.mkQ 7 (L k) ∈ AE.memBar (Sset)ᶜ hγcard false := by
    intro k hk
    rcases e16l_q8_class (e ⟨k, hk⟩) with h1 | h1 | h1
    ·
      left
      have hk1 : k = 1 := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
      rw [hk1, map_one, map_one]
      exact Subgroup.one_mem _
    ·
      left
      have hkz : k = z := congrArg Subtype.val (e.injective (h1.trans hz1.symm))
      rw [hkz, hLz]
      exact TL4.AECov.mkQ_embed_mem_memBar _ _ true (AE.mem_kQ.mp AE.zQ_mem_kQ)
    ·
      have hkk'' : (⟨k, hk⟩ * ⟨k, hk⟩ : K) = ⟨z, hKinv.mem⟩ :=
        e.injective (by rw [map_mul, h1, hz1])
      have hkk' : k * k = z := congrArg Subtype.val hkk''
      obtain ⟨w0, hw0⟩ := e16l_exists_embed (hsupp k hk)
      have hw : AE.embed (AE.emb (Sset)ᶜ hγcard) (w0 * w0) =
          AE.embed (AE.emb (Sset)ᶜ hγcard) AE.zQ := by
        rw [map_mul, hw0, ← map_mul L, hkk', hLz]
        rfl
      exact e16l_mem_memBar hw0 (AE.embed_injective _ hw)
  have hle : K.map φ ≤ AE.memBar (Sset)ᶜ hγcard true ⊔ AE.memBar (Sset)ᶜ hγcard false := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← hLmk k]
    rcases hmemK k hk with h1 | h1
    · exact Subgroup.mem_sup_left h1
    · exact Subgroup.mem_sup_right h1
  have hcardK : Nat.card (K.map φ) = 8 := by
    rw [Subgroup.card_map_of_injective hφinj, hK8]
  have hw : IsUniqueInvolution (K.map φ) (φ z) := by
    refine ⟨Subgroup.mem_map_of_mem φ hKinv.mem, ?_, ?_, ?_⟩
    · intro h1
      apply hKz
      apply hφinj
      rw [h1, map_one]
    · rw [← map_mul, hKinv.sq, map_one]
    · rintro _ ⟨k, hk, rfl⟩ hyy
      have hkk1 : k * k = 1 := hφinj (by rw [map_mul, map_one]; exact hyy)
      rcases hKinv.unique k hk hkk1 with h1 | h1
      · left
        rw [h1, map_one]
      · right
        rw [h1]
  rcases eq_memBar_of_le_sup_memBar (by norm_num) hle hcardK hw with h1 | h1
  · exact ⟨K, hK, (Sset)ᶜ, hγcard, true, φ, hφβ, hφH, h1⟩
  · exact ⟨K, hK, (Sset)ᶜ, hγcard, false, φ, hφβ, hφH, h1⟩



namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem exists_member_seven_of_points (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {H : Subgroup G}
    {σ : H →* Equiv.Perm (Fin 7)} {β : Multiplicative (Fin 7 → ZMod 2) →* G}
    (hS : AESplitHyp (zGroup Ω) H σ β) (hA : σ.range = alternatingGroup (Fin 7))
    (hβ : ∀ i, ∃ x : G, β (Multiplicative.ofAdd (Pi.single i 1)) = x * e * x⁻¹) :
    ∃ K₀ ∈ Ω, ∃ (α : Finset (Fin 7)) (hα : α.card = 4) (b : Bool) (φ : G →* AE.AEQ 7),
      (∀ f : Multiplicative (Fin 7 → ZMod 2), ∑ i, f.toAdd i = 0 →
        φ (β f) = AE.mkQ 7 (AE.Wr.ofVec f.toAdd)) ∧
      (∀ x : H, φ x = AE.mkQ 7 (AE.Wr.ofPerm (σ x))) ∧ K₀.map φ = AE.memBar α hα b := by
  exact e16l_aux c h h9 hS hA hβ (exists_points_sigma c h h9 h13)
    (exists_three_element_of_frame c h h9 h13)

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
