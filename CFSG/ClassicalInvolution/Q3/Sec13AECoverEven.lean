module

public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Q3.TL4AECoverF
public import CFSG.ClassicalInvolution.Q3.TL4AECoverL
import CFSG.ClassicalInvolution.Q3.TL4AECoverG
import CFSG.ClassicalInvolution.Q3.TL3T48

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4.AECov (ePt ofVec_add conj_ePt conjSub_memBar_of_perm_eq_one)

namespace EvenCov

section Model

variable {n : ℕ}

theorem single_add_self (p : Fin n) :
    (Pi.single p 1 : Fin n → ZMod 2) + Pi.single p 1 = 0 := by
  rw [← Pi.single_add, show (1 + 1 : ZMod 2) = 0 from rfl, Pi.single_zero]

theorem ePt_mul_self (p : Fin n) : ePt n p * ePt n p = 1 := by
  rw [ePt, ← map_mul, ← ofVec_add, single_add_self]
  rfl

theorem ePt_comm (p q : Fin n) : ePt n p * ePt n q = ePt n q * ePt n p := by
  rw [ePt, ePt, ← map_mul, ← map_mul, ← ofVec_add, ← ofVec_add, add_comm]

theorem conj_ePt_mul (g : AEQ n) (p q : Fin n) :
    g * (ePt n p * ePt n q) * g⁻¹ = ePt n (permQ n g p) * ePt n (permQ n g q) := by
  rw [← conj_ePt g p, ← conj_ePt g q]
  group

theorem ePt_pair_mul (p q r : Fin n) :
    ePt n p * ePt n q * (ePt n q * ePt n r) = ePt n p * ePt n r := by
  rw [mul_assoc, ← mul_assoc (ePt n q), ePt_mul_self, one_mul]

theorem zBar_eq_ePt (α : Finset (Fin n)) (h : α.card = 4) :
    zBar α h = ePt n (emb α h 0) * ePt n (emb α h 1) *
      (ePt n (emb α h 2) * ePt n (emb α h 3)) := by
  classical
  simp only [ePt, ← map_mul, ← ofVec_add]
  rw [zBar]
  congr 1
  refine Wr.ext (funext fun x => ?_) (zOf_perm _)
  rw [zOf_vec_apply]
  show _ = (Pi.single (emb α h 0) 1 + Pi.single (emb α h 1) 1 +
    (Pi.single (emb α h 2) 1 + Pi.single (emb α h 3) 1) : Fin n → ZMod 2) x
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hx : x ∈ Set.range (emb α h)
  · obtain ⟨i, rfl⟩ := hx
    simp only [Set.mem_range_self, ite_true, (emb α h).injective.eq_iff]
    fin_cases i <;> decide
  · have hne : ∀ j, x ≠ emb α h j := fun j hj => hx ⟨j, hj.symm⟩
    simp only [hx, ite_false, hne, add_zero]

theorem loc_pair : ∀ i j : Fin 4, i ≠ j → ∃ a ∈ kList, ∃ b ∈ kStarList,
    a * b = ofVec (Pi.single i 1 + Pi.single j 1) := by
  decide +kernel

theorem embed_ofVec (ι : Fin 4 ↪ Fin n) (v : Fin 4 → ZMod 2) :
    embed ι (ofVec v) = ofVec (embedVec ι v) :=
  Wr.ext rfl (embedPerm_one ι)

theorem embedVec_pair (ι : Fin 4 ↪ Fin n) (i j : Fin 4) :
    embedVec ι (Pi.single i 1 + Pi.single j 1) = Pi.single (ι i) 1 + Pi.single (ι j) 1 := by
  classical
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i', rfl⟩ := hx
    rw [embedVec_apply]
    simp only [Pi.add_apply, Pi.single_apply, ι.injective.eq_iff]
  · rw [embedVec_of_not_mem ι _ hx]
    have hne : ∀ j, x ≠ ι j := fun j hj => hx ⟨j, hj.symm⟩
    simp only [Pi.add_apply, Pi.single_apply, hne, ite_false, add_zero]

theorem exists_pair_mem_twin {α : Finset (Fin n)} (h : α.card = 4) {p q : Fin n}
    (hp : p ∈ α) (hq : q ∈ α) (hpq : p ≠ q) :
    ∃ a ∈ memBar α h true, ∃ b ∈ memBar α h false, a * b = ePt n p * ePt n q := by
  have hr : ∀ x ∈ α, ∃ i, emb α h i = x := fun x hx => by
    rw [← Set.mem_range, range_emb]
    exact hx
  obtain ⟨i, rfl⟩ := hr p hp
  obtain ⟨j, rfl⟩ := hr q hq
  have hij : i ≠ j := fun e => hpq (by rw [e])
  obtain ⟨a, ha, b, hb, hab⟩ := loc_pair i j hij
  refine ⟨mkQ n (embed (emb α h) a), ⟨embed (emb α h) a, ⟨a, ha, rfl⟩, rfl⟩,
    mkQ n (embed (emb α h) b), ⟨embed (emb α h) b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
  rw [← map_mul, ← map_mul, hab, embed_ofVec, embedVec_pair, ofVec_add, map_mul]
  rfl

theorem conjSub_memBar (g : AEQ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ c : Bool, conjSub g (memBar α h b) =
      memBar (α.map (permQ n g).toEmbedding) (by rw [Finset.card_map]; exact h) c := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
  have hw : (w : AEQ n) = mkQ n (ofVec w.vec) * mkQ n (ofPerm w.perm) := by
    rw [← map_mul, ofVec_mul_ofPerm]
    rfl
  obtain ⟨b', hb'⟩ := exists_conj_ofPerm_memBar w.perm α h b
  rw [hw, conjSub_mul]
  have e : conjSub (mkQ n (ofPerm w.perm)) (memBar α h b) =
      memBar (α.map w.perm.toEmbedding) (by rw [Finset.card_map]; exact h) b' := hb'
  rw [e]
  rcases conjSub_memBar_of_perm_eq_one (w := ofVec w.vec) rfl (α.map w.perm.toEmbedding)
    (by rw [Finset.card_map]; exact h) b' with h1 | h1
  · exact ⟨true, h1⟩
  · exact ⟨false, h1⟩

theorem memAt_comm_yOf (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) {m : Wr n}
    (hm : m ∈ memAt α h b) : ∃ m₁ ∈ memAt α h b, ∃ m₂ ∈ memAt α h b,
      m = (m₁ * yOf (emb α h) * m₁⁻¹ * (yOf (emb α h))⁻¹) *
        (m₂ * yOf (emb α h) * m₂⁻¹ * (yOf (emb α h))⁻¹) := by
  have key : ∀ a ∈ (bif b then kList else kStarList), ∃ k₁ ∈ (bif b then kList else kStarList),
      ∃ k₂ ∈ (bif b then kList else kStarList),
        a = (k₁ * yQ * k₁⁻¹ * yQ⁻¹) * (k₂ * yQ * k₂⁻¹ * yQ⁻¹) := by
    cases b
    · exact TL4.kStarList_comm_yQ
    · exact TL4.kList_comm_yQ
  have hmem : ∀ c ∈ (bif b then kList else kStarList), embed (emb α h) c ∈ memAt α h b :=
    fun c hc => by cases b <;> exact ⟨c, hc, rfl⟩
  have hm' : m ∈ (bif b then kQ else kQStar).map (embed (emb α h)) := by cases b <;> exact hm
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hm'
  obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := key a (by cases b <;> exact ha)
  refine ⟨_, hmem k₁ hk₁, _, hmem k₂ hk₂, ?_⟩
  rw [he]
  simp only [map_mul, map_inv]
  rfl

end Model

section TLift

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ} (I : AEIdent P k)

noncomputable def tw (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) : Subgroup G :=
  (I.label_surj α h b).choose

theorem tw_mem (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) : tw I α h b ∈ P :=
  (I.label_surj α h b).choose_spec.1

theorem tw_label (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    ((tw I α h b).subgroupOf (pSpan P)).map I.φ = memBar α h b :=
  (I.label_surj α h b).choose_spec.2

@[expose] def IsTL (α : Finset (Fin k)) (h : α.card = 4) (x : ↥(pSpan P)) (e : AEQ k) : Prop :=
  (∃ l ∈ tw I α h true, ∃ l' ∈ tw I α h false, (x : G) = l * l') ∧ I.φ x = e

variable {I}

theorem eq_tw (hH : TL4.AECoverHyp I) {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin k)}
    {h : α.card = 4} {b : Bool} (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h b) :
    L = tw I α h b :=
  hH.label_inj L hL _ (tw_mem I α h b) (hlab.trans (tw_label I α h b).symm)

theorem tw_comm (hH : TL4.AECoverHyp I) (α : Finset (Fin k)) (h : α.card = 4) :
    ∀ x ∈ tw I α h true, ∀ y ∈ tw I α h false, x * y = y * x :=
  hH.twin_comm α h _ (tw_mem I α h true) _ (tw_mem I α h false) (tw_label I α h true)
    (tw_label I α h false)

theorem tw_injOn (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {α : Finset (Fin k)} {h : α.card = 4}
    {b : Bool} {l₁ l₂ : G} (h₁ : l₁ ∈ tw I α h b) (h₂ : l₂ ∈ tw I α h b)
    (he : I.φ ⟨l₁, le_pSpan (tw_mem I α h b) h₁⟩ = I.φ ⟨l₂, le_pSpan (tw_mem I α h b) h₂⟩) :
    l₁ = l₂ :=
  I.injOn hk (tw_mem I α h b) (hH.card _ (tw_mem I α h b)) (tw_label I α h b) h₁ h₂ he

theorem exists_tw_inv (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) (α : Finset (Fin k))
    (h : α.card = 4) : ∃ u : G, IsUniqueInvolution (tw I α h true) u ∧
      IsUniqueInvolution (tw I α h false) u ∧ ∃ hu : u ∈ pSpan P, I.φ ⟨u, hu⟩ = zBar α h := by
  obtain ⟨u, hu, hue⟩ := TL4.AECov.exists_isUniqueInvolution I hk (tw_mem I α h true)
    (hH.card _ (tw_mem I α h true)) (tw_label I α h true)
  obtain ⟨u', hu', -⟩ := TL4.AECov.exists_isUniqueInvolution I hk (tw_mem I α h false)
    (hH.card _ (tw_mem I α h false)) (tw_label I α h false)
  have huu : u = u' := hH.twin_z α h _ (tw_mem I α h true) _ (tw_mem I α h false)
    (tw_label I α h true) (tw_label I α h false) u u' hu hu'
  subst huu
  exact ⟨u, hu, hu', _, hue⟩

theorem IsTL.congr_set {α β : Finset (Fin k)} (hαβ : α = β) {h : α.card = 4}
    {h' : β.card = 4} {x : ↥(pSpan P)} {e : AEQ k} (hx : IsTL I α h x e) : IsTL I β h' x e := by
  subst hαβ
  exact hx

theorem IsTL.mul (hH : TL4.AECoverHyp I) {α : Finset (Fin k)} {h : α.card = 4}
    {x y : ↥(pSpan P)} {e f : AEQ k} (hx : IsTL I α h x e) (hy : IsTL I α h y f) :
    IsTL I α h (x * y) (e * f) := by
  obtain ⟨⟨l₁, hl₁, l₁', hl₁', hx⟩, hxe⟩ := hx
  obtain ⟨⟨l₂, hl₂, l₂', hl₂', hy⟩, hye⟩ := hy
  refine ⟨⟨l₁ * l₂, (tw I α h true).mul_mem hl₁ hl₂, l₁' * l₂',
    (tw I α h false).mul_mem hl₁' hl₂', ?_⟩, by rw [map_mul, hxe, hye]⟩
  rw [Subgroup.coe_mul, hx, hy]
  have hc := tw_comm hH α h l₂ hl₂ l₁' hl₁'
  calc l₁ * l₁' * (l₂ * l₂') = l₁ * (l₁' * l₂) * l₂' := by group
    _ = l₁ * (l₂ * l₁') * l₂' := by rw [hc]
    _ = l₁ * l₂ * (l₁' * l₂') := by group

theorem exists_isTL {α : Finset (Fin k)} {h : α.card = 4} {a b : AEQ k}
    (ha : a ∈ memBar α h true) (hb : b ∈ memBar α h false) : ∃ x, IsTL I α h x (a * b) := by
  rw [← tw_label I α h true] at ha
  rw [← tw_label I α h false] at hb
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map (tw_mem I α h true) ha
  obtain ⟨l', hl', rfl⟩ := I.exists_of_mem_map (tw_mem I α h false) hb
  exact ⟨⟨l, le_pSpan (tw_mem I α h true) hl⟩ * ⟨l', le_pSpan (tw_mem I α h false) hl'⟩,
    ⟨l, hl, l', hl', rfl⟩, map_mul _ _ _⟩

theorem IsTL.unique (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {α : Finset (Fin k)} {h : α.card = 4}
    {x y : ↥(pSpan P)} {e : AEQ k} (hx : IsTL I α h x e) (hy : IsTL I α h y e) : x = y := by
  obtain ⟨⟨l₁, hl₁, l₁', hl₁', hx⟩, hxe⟩ := hx
  obtain ⟨⟨l₂, hl₂, l₂', hl₂', hy⟩, hye⟩ := hy
  obtain ⟨u, hu, hu', huX, hue⟩ := exists_tw_inv hH hk α h
  have hLP := le_pSpan (tw_mem I α h true)
  have hL'P := le_pSpan (tw_mem I α h false)
  have hm₁ : l₂⁻¹ * l₁ ∈ tw I α h true := (tw I α h true).mul_mem ((tw I α h true).inv_mem hl₂) hl₁
  have hm₂ : l₂' * l₁'⁻¹ ∈ tw I α h false :=
    (tw I α h false).mul_mem hl₂' ((tw I α h false).inv_mem hl₁')
  have hx' : x = ⟨l₁, hLP hl₁⟩ * ⟨l₁', hL'P hl₁'⟩ := Subtype.ext hx
  have hy' : y = ⟨l₂, hLP hl₂⟩ * ⟨l₂', hL'P hl₂'⟩ := Subtype.ext hy
  have e₁ : I.φ ⟨l₁, hLP hl₁⟩ * I.φ ⟨l₁', hL'P hl₁'⟩ =
      I.φ ⟨l₂, hLP hl₂⟩ * I.φ ⟨l₂', hL'P hl₂'⟩ := by
    rw [← map_mul, ← map_mul, ← hx', ← hy', hxe, hye]
  have haa : I.φ ⟨l₂⁻¹ * l₁, hLP hm₁⟩ = I.φ ⟨l₂' * l₁'⁻¹, hL'P hm₂⟩ := by
    have ea : (⟨l₂⁻¹ * l₁, hLP hm₁⟩ : ↥(pSpan P)) = (⟨l₂, hLP hl₂⟩)⁻¹ * ⟨l₁, hLP hl₁⟩ := rfl
    have ea' : (⟨l₂' * l₁'⁻¹, hL'P hm₂⟩ : ↥(pSpan P)) = ⟨l₂', hL'P hl₂'⟩ * (⟨l₁', hL'P hl₁'⟩)⁻¹ :=
      rfl
    rw [ea, ea', map_mul, map_inv, map_mul, map_inv]
    calc (I.φ ⟨l₂, hLP hl₂⟩)⁻¹ * I.φ ⟨l₁, hLP hl₁⟩
        = (I.φ ⟨l₂, hLP hl₂⟩)⁻¹ * (I.φ ⟨l₁, hLP hl₁⟩ * I.φ ⟨l₁', hL'P hl₁'⟩) *
          (I.φ ⟨l₁', hL'P hl₁'⟩)⁻¹ := by group
      _ = (I.φ ⟨l₂, hLP hl₂⟩)⁻¹ * (I.φ ⟨l₂, hLP hl₂⟩ * I.φ ⟨l₂', hL'P hl₂'⟩) *
          (I.φ ⟨l₁', hL'P hl₁'⟩)⁻¹ := by rw [e₁]
      _ = I.φ ⟨l₂', hL'P hl₂'⟩ * (I.φ ⟨l₁', hL'P hl₁'⟩)⁻¹ := by group
  have ha₁ : I.φ ⟨l₂⁻¹ * l₁, hLP hm₁⟩ ∈ memBar α h true := by
    rw [← tw_label I α h true]
    exact I.mem_map (tw_mem I α h true) hm₁
  have ha₂ : I.φ ⟨l₂⁻¹ * l₁, hLP hm₁⟩ ∈ memBar α h false := by
    rw [haa, ← tw_label I α h false]
    exact I.mem_map (tw_mem I α h false) hm₂
  apply Subtype.ext
  rw [hx, hy]
  rcases inf_memBar_true_false hk ha₁ ha₂ with h1 | h1
  · have e₂ : l₂⁻¹ * l₁ = 1 := tw_injOn hH hk hm₁ (tw I α h true).one_mem
      (h1.trans (map_one I.φ).symm)
    have e₃ : l₂' * l₁'⁻¹ = 1 := tw_injOn hH hk hm₂ (tw I α h false).one_mem
      ((haa.symm.trans h1).trans (map_one I.φ).symm)
    rw [inv_mul_eq_one] at e₂
    rw [mul_inv_eq_one] at e₃
    rw [e₂, e₃]
  · have e₂ : l₂⁻¹ * l₁ = u := tw_injOn hH hk hm₁ hu.mem (h1.trans hue.symm)
    have e₃ : l₂' * l₁'⁻¹ = u := tw_injOn hH hk hm₂ hu'.mem ((haa.symm.trans h1).trans hue.symm)
    have f₁ : l₁ = l₂ * u := by rw [← e₂]; group
    have f₂ : l₂' = u * l₁' := by rw [← e₃]; group
    rw [f₁, f₂]
    group

theorem mem_mul_of_mem_tw (hH : TL4.AECoverHyp I) {α : Finset (Fin k)} {h : α.card = 4}
    {c₁ c₂ : Bool} {a a' : G} (ha : a ∈ tw I α h c₁) (ha' : a' ∈ tw I α h c₂) :
    ∃ l ∈ tw I α h true, ∃ l' ∈ tw I α h false, a * a' = l * l' := by
  cases c₁ <;> cases c₂
  · exact ⟨1, (tw I α h true).one_mem, a * a', (tw I α h false).mul_mem ha ha', by rw [one_mul]⟩
  · exact ⟨a', ha', a, ha, (tw_comm hH α h a' ha' a ha).symm⟩
  · exact ⟨a, ha, a', ha', rfl⟩
  · exact ⟨a * a', (tw I α h true).mul_mem ha ha', 1, (tw I α h false).one_mem, by rw [mul_one]⟩

theorem conjSub_tw (hH : TL4.AECoverHyp I) (g : ↥(pSpan P)) (α : Finset (Fin k))
    (h : α.card = 4) (b : Bool) : ∃ c : Bool, conjSub (g : G) (tw I α h b) =
      tw I (α.map (permQ k (I.φ g)).toEmbedding) (by rw [Finset.card_map]; exact h) c := by
  obtain ⟨c, hc⟩ := conjSub_memBar (I.φ g) α h b
  refine ⟨c, eq_tw hH (hH.conj_mem _ (tw_mem I α h b) g g.2) ?_⟩
  rw [TL4.AECov.map_conjSub_eq I _ g, tw_label, hc]

theorem IsTL.conj (hH : TL4.AECoverHyp I) {α : Finset (Fin k)} {h : α.card = 4}
    {x : ↥(pSpan P)} {e : AEQ k} (hx : IsTL I α h x e) (g : ↥(pSpan P)) :
    IsTL I (α.map (permQ k (I.φ g)).toEmbedding) (by rw [Finset.card_map]; exact h)
      (g * x * g⁻¹) (I.φ g * e * (I.φ g)⁻¹) := by
  obtain ⟨⟨l, hl, l', hl', hx⟩, hxe⟩ := hx
  refine ⟨?_, by rw [map_mul, map_mul, map_inv, hxe]⟩
  have hβ : (α.map (permQ k (I.φ g)).toEmbedding).card = 4 := by rw [Finset.card_map]; exact h
  obtain ⟨c₁, hc₁⟩ := conjSub_tw hH g α h true
  obtain ⟨c₂, hc₂⟩ := conjSub_tw hH g α h false
  have h1 : (g : G) * l * (g : G)⁻¹ ∈ tw I (α.map (permQ k (I.φ g)).toEmbedding) hβ c₁ := by
    rw [← hc₁]
    exact conj_mem_conjSub hl
  have h2 : (g : G) * l' * (g : G)⁻¹ ∈ tw I (α.map (permQ k (I.φ g)).toEmbedding) hβ c₂ := by
    rw [← hc₂]
    exact conj_mem_conjSub hl'
  have e : ((g * x * g⁻¹ : ↥(pSpan P)) : G) =
      ((g : G) * l * (g : G)⁻¹) * ((g : G) * l' * (g : G)⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
    group
  rw [e]
  exact mem_mul_of_mem_tw hH h1 h2

end TLift

section Pairs

theorem eq_of_conj_rel {X : Type*} [Group X] {g a b a' b' ζ : X} (hζ : ∀ y, ζ * y = y * ζ)
    (ha' : a' = a * ζ) (h1 : g * a * g⁻¹ = b) (h2 : g * b * g⁻¹ = a * b)
    (h1' : g * a' * g⁻¹ = b') (h2' : g * b' * g⁻¹ = a' * b') : a = a' := by
  have hgζ : g * ζ * g⁻¹ = ζ := by rw [← hζ g, mul_inv_cancel_right]
  have hb' : b' = b * ζ := by
    rw [← h1', ha', ← h1]
    calc g * (a * ζ) * g⁻¹ = g * a * g⁻¹ * (g * ζ * g⁻¹) := by group
      _ = g * a * g⁻¹ * ζ := by rw [hgζ]
  have key : a * b * ζ * ζ = a * b * ζ * 1 := by
    calc a * b * ζ * ζ = a * (b * ζ) * ζ := by group
      _ = a * (ζ * b) * ζ := by rw [hζ b]
      _ = a * ζ * (b * ζ) := by group
      _ = a' * b' := by rw [ha', hb']
      _ = g * b' * g⁻¹ := h2'.symm
      _ = g * b * g⁻¹ * (g * ζ * g⁻¹) := by rw [hb']; group
      _ = a * b * ζ * 1 := by rw [h2, hgζ, mul_one]
  rw [ha', mul_left_cancel key, mul_one]

theorem swap_mem {k : ℕ} {β : Finset (Fin k)} {a b x : Fin k} (ha : a ∈ β) (hb : b ∈ β)
    (hx : x ∈ β) : Equiv.swap a b x ∈ β := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

theorem map_swap_mul_swap {k : ℕ} {β : Finset (Fin k)} {p q r : Fin k} (hp : p ∈ β)
    (hq : q ∈ β) (hr : r ∈ β) : β.map (Equiv.swap p r * Equiv.swap p q).toEmbedding = β := by
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (by rw [Finset.card_map])
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  exact swap_mem hp hr (swap_mem hp hq hy)

theorem exists_third {k : ℕ} {α : Finset (Fin k)} (h : α.card = 4) (p q : Fin k) :
    ∃ r ∈ α, r ≠ p ∧ r ≠ q := by
  classical
  obtain ⟨r, hr, hrq⟩ := Finset.exists_mem_ne (s := α.erase p)
    (lt_of_lt_of_le (by omega) Finset.pred_card_le_card_erase) q
  exact ⟨r, Finset.mem_of_mem_erase hr, Finset.ne_of_mem_erase hr, hrq⟩

theorem exists_four_superset {k : ℕ} (hk : 4 ≤ k) (s : Finset (Fin k)) (hs : s.card ≤ 4) :
    ∃ α : Finset (Fin k), s ⊆ α ∧ α.card = 4 := by
  obtain ⟨α, hsα, -, hα⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hs
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hk)
  exact ⟨α, hsα, hα⟩

theorem mem_emb {k : ℕ} (α : Finset (Fin k)) (h : α.card = 4) (i : Fin 4) : emb α h i ∈ α := by
  have := Set.mem_range_self (f := emb α h) i
  rwa [range_emb] at this

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ} {I : AEIdent P k}

theorem isTL_pair_eq_of_three (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {p q r : Fin k} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) {α α' : Finset (Fin k)} {h : α.card = 4} {h' : α'.card = 4}
    (hp : p ∈ α) (hq : q ∈ α) (hr : r ∈ α) (hp' : p ∈ α') (hq' : q ∈ α') (hr' : r ∈ α')
    {x x' : ↥(pSpan P)} (hx : IsTL I α h x (ePt k p * ePt k q))
    (hx' : IsTL I α' h' x' (ePt k p * ePt k q)) : x = x' := by
  set σ : Equiv.Perm (Fin k) := Equiv.swap p r * Equiv.swap p q with hσ
  have hσA : σ ∈ alternatingGroup (Fin k) := by
    rw [Equiv.Perm.mem_alternatingGroup, hσ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpr,
      Equiv.Perm.sign_swap hpq]
    decide
  have hσp : σ p = q := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hpq.symm hqr]
  have hσq : σ q = r := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have hσr : σ r = p := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpr.symm hqr.symm,
      Equiv.swap_apply_right]
  obtain ⟨g, hg⟩ : mkQ k (ofPerm σ) ∈ I.φ.range := by
    rw [I.range_eq]
    exact mem_aeModel_ofPerm hσA
  have hgσ : permQ k (I.φ g) = σ := by rw [hg]; rfl
  have hconj : ∀ {β : Finset (Fin k)} {hβ : β.card = 4} {y : ↥(pSpan P)} {s t : Fin k},
      p ∈ β → q ∈ β → r ∈ β → IsTL I β hβ y (ePt k s * ePt k t) →
      IsTL I β hβ (g * y * g⁻¹) (ePt k (σ s) * ePt k (σ t)) := by
    intro β hβ y s t hpβ hqβ hrβ hy
    have h1 := (hy.conj hH g).congr_set (h' := hβ)
      (by rw [hgσ]; exact map_swap_mul_swap hpβ hqβ hrβ)
    rwa [conj_ePt_mul, hgσ] at h1
  have hpair : ∀ {β : Finset (Fin k)} (hβ : β.card = 4), q ∈ β → r ∈ β →
      ∃ b, IsTL I β hβ b (ePt k q * ePt k r) := by
    intro β hβ hqβ hrβ
    obtain ⟨a₁, ha₁, a₂, ha₂, he⟩ := exists_pair_mem_twin hβ hqβ hrβ hqr
    rw [← he]
    exact exists_isTL ha₁ ha₂
  have hrel : ∀ {β : Finset (Fin k)} {hβ : β.card = 4} {y b : ↥(pSpan P)}, p ∈ β → q ∈ β →
      r ∈ β → IsTL I β hβ y (ePt k p * ePt k q) → IsTL I β hβ b (ePt k q * ePt k r) →
      g * y * g⁻¹ = b ∧ g * b * g⁻¹ = y * b := by
    intro β hβ y b hpβ hqβ hrβ hy hb
    refine ⟨(hconj hpβ hqβ hrβ hy).unique hH hk ?_, (hconj hpβ hqβ hrβ hb).unique hH hk ?_⟩
    · rw [hσp, hσq]
      exact hb
    · rw [hσq, hσr, ← ePt_comm, ← ePt_pair_mul p q r]
      exact hy.mul hH hb
  obtain ⟨b, hb⟩ := hpair h hq hr
  obtain ⟨b', hb'⟩ := hpair h' hq' hr'
  obtain ⟨h1, h2⟩ := hrel hp hq hr hx hb
  obtain ⟨h1', h2'⟩ := hrel hp' hq' hr' hx' hb'
  have hζ : x⁻¹ * x' ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx.2, hx'.2, inv_mul_cancel]
  exact eq_of_conj_rel (fun y => (Subgroup.mem_center_iff.mp (I.ker_le hζ) y).symm)
    (by group) h1 h2 h1' h2'

theorem isTL_pair_eq (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {p q : Fin k} (hpq : p ≠ q)
    {α α' : Finset (Fin k)} {h : α.card = 4} {h' : α'.card = 4} (hp : p ∈ α) (hq : q ∈ α)
    (hp' : p ∈ α') (hq' : q ∈ α') {x x' : ↥(pSpan P)} (hx : IsTL I α h x (ePt k p * ePt k q))
    (hx' : IsTL I α' h' x' (ePt k p * ePt k q)) : x = x' := by
  classical
  obtain ⟨r, hr, hrp, hrq⟩ := exists_third h p q
  obtain ⟨r', hr', hr'p, hr'q⟩ := exists_third h' p q
  by_cases hrα' : r ∈ α'
  · exact isTL_pair_eq_of_three hH hk hpq hrp.symm hrq.symm hp hq hr hp' hq' hrα' hx hx'
  have hrr' : r ≠ r' := fun e => hrα' (by rw [e]; exact hr')
  have hβ : ({p, q, r, r'} : Finset (Fin k)).card = 4 :=
    Finset.card_eq_four.mpr ⟨p, q, r, r', hpq, hrp.symm, hr'p.symm, hrq.symm, hr'q.symm, hrr', rfl⟩
  have hpβ : p ∈ ({p, q, r, r'} : Finset (Fin k)) := by simp
  have hqβ : q ∈ ({p, q, r, r'} : Finset (Fin k)) := by simp
  have hrβ : r ∈ ({p, q, r, r'} : Finset (Fin k)) := by simp
  have hr'β : r' ∈ ({p, q, r, r'} : Finset (Fin k)) := by simp
  obtain ⟨y, hy⟩ : ∃ y, IsTL I {p, q, r, r'} hβ y (ePt k p * ePt k q) := by
    obtain ⟨a₁, ha₁, a₂, ha₂, he⟩ := exists_pair_mem_twin hβ hpβ hqβ hpq
    rw [← he]
    exact exists_isTL ha₁ ha₂
  exact (isTL_pair_eq_of_three hH hk hpq hrp.symm hrq.symm hp hq hr hpβ hqβ hrβ hx hy).trans
    (isTL_pair_eq_of_three hH hk hpq hr'p.symm hr'q.symm hpβ hqβ hr'β hp' hq' hr' hy hx')

theorem IsTL.transport (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {p q : Fin k} (hpq : p ≠ q)
    {α β : Finset (Fin k)} {h : α.card = 4} (hβ : β.card = 4) (hp : p ∈ α) (hq : q ∈ α)
    (hpβ : p ∈ β) (hqβ : q ∈ β) {x : ↥(pSpan P)} (hx : IsTL I α h x (ePt k p * ePt k q)) :
    IsTL I β hβ x (ePt k p * ePt k q) := by
  obtain ⟨a₁, ha₁, a₂, ha₂, he⟩ := exists_pair_mem_twin hβ hpβ hqβ hpq
  obtain ⟨y, hy⟩ := exists_isTL (I := I) ha₁ ha₂
  rw [he] at hy
  rwa [isTL_pair_eq hH hk hpq hp hq hpβ hqβ hx hy]

theorem exists_pairLift (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {p q : Fin k} (hpq : p ≠ q) :
    ∃ x : ↥(pSpan P), ∀ (α : Finset (Fin k)) (h : α.card = 4), p ∈ α → q ∈ α →
      IsTL I α h x (ePt k p * ePt k q) := by
  classical
  obtain ⟨α₀, hs, h₀⟩ := exists_four_superset (by omega) {p, q}
    (le_trans Finset.card_le_two (by norm_num))
  have hp₀ : p ∈ α₀ := hs (by simp)
  have hq₀ : q ∈ α₀ := hs (by simp)
  obtain ⟨a₁, ha₁, a₂, ha₂, he⟩ := exists_pair_mem_twin h₀ hp₀ hq₀ hpq
  obtain ⟨x, hx⟩ := exists_isTL (I := I) ha₁ ha₂
  rw [he] at hx
  exact ⟨x, fun α h hp hq => hx.transport hH hk hpq h hp₀ hq₀ hp hq⟩

theorem exists_pointLift (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) (p₀ : Fin k) :
    ∃ u : Fin k → ↥(pSpan P), u p₀ = 1 ∧ ∀ p q : Fin k, p ≠ q →
      ∀ (α : Finset (Fin k)) (h : α.card = 4), p ∈ α → q ∈ α →
        IsTL I α h (u p * u q) (ePt k p * ePt k q) := by
  classical
  choose x hx using fun p (hp : p ≠ p₀) => exists_pairLift (I := I) hH hk (Ne.symm hp)
  refine ⟨fun p => if hp : p = p₀ then 1 else x p hp, by simp, ?_⟩
  intro p q hpq α h hpα hqα
  by_cases hp : p = p₀
  · have hq : q ≠ p₀ := fun e => hpq (hp.trans e.symm)
    simp only [dif_pos hp, dif_neg hq, one_mul]
    rw [hp]
    exact hx q hq α h (hp ▸ hpα) hqα
  by_cases hq : q = p₀
  · simp only [dif_neg hp, dif_pos hq, mul_one]
    rw [hq, ePt_comm]
    exact hx p hp α h (hq ▸ hqα) hpα
  simp only [dif_neg hp, dif_neg hq]
  obtain ⟨β, hs, hβ⟩ := exists_four_superset (by omega) {p₀, p, q}
    (le_trans Finset.card_le_three (by norm_num))
  have hp₀β : p₀ ∈ β := hs (by simp)
  have hpβ : p ∈ β := hs (by simp)
  have hqβ : q ∈ β := hs (by simp)
  have hxy := (hx p hp β hβ hp₀β hpβ).mul hH (hx q hq β hβ hp₀β hqβ)
  rw [ePt_comm p₀ p, ePt_pair_mul] at hxy
  exact hxy.transport hH hk hpq h hpβ hqβ hpα hqα

theorem inv_eq_pointLift (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {u : Fin k → ↥(pSpan P)}
    (hu : ∀ p q : Fin k, p ≠ q → ∀ (α : Finset (Fin k)) (h : α.card = 4), p ∈ α → q ∈ α →
      IsTL I α h (u p * u q) (ePt k p * ePt k q))
    {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin k)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h b) {z : G}
    (hz : IsUniqueInvolution L z) :
    (⟨z, le_pSpan hL hz.mem⟩ : ↥(pSpan P)) =
      u (emb α h 0) * u (emb α h 1) * (u (emb α h 2) * u (emb α h 3)) := by
  have hLe := eq_tw hH hL hlab
  have hzT : IsTL I α h ⟨z, le_pSpan hL hz.mem⟩ (zBar α h) := by
    refine ⟨?_, I.map_eq_zBar hk hL (hH.card L hL) hlab hz⟩
    have hzm : z ∈ tw I α h b := by rw [← hLe]; exact hz.mem
    cases b
    · exact ⟨1, (tw I α h true).one_mem, z, hzm, (one_mul z).symm⟩
    · exact ⟨z, hzm, 1, (tw I α h false).one_mem, (mul_one z).symm⟩
  have hne : ∀ {i j : Fin 4}, i ≠ j → emb α h i ≠ emb α h j :=
    fun hij e => hij ((emb α h).injective e)
  have h01 := hu _ _ (hne (by decide : (0 : Fin 4) ≠ 1)) α h (mem_emb α h 0) (mem_emb α h 1)
  have h23 := hu _ _ (hne (by decide : (2 : Fin 4) ≠ 3)) α h (mem_emb α h 2) (mem_emb α h 3)
  have h0123 := h01.mul hH h23
  rw [← zBar_eq_ePt] at h0123
  exact hzT.unique hH hk h0123

theorem conj_pointLift (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) {p₀ : Fin k}
    {u : Fin k → ↥(pSpan P)} (hu1 : u p₀ = 1)
    (hu : ∀ p q : Fin k, p ≠ q → ∀ (α : Finset (Fin k)) (h : α.card = 4), p ∈ α → q ∈ α →
      IsTL I α h (u p * u q) (ePt k p * ePt k q))
    (hsq : ∀ p, u p * u p = 1) (g : ↥(pSpan P)) (p : Fin k) :
    g * u p * g⁻¹ = u (permQ k (I.φ g) p₀) * u (permQ k (I.φ g) p) := by
  classical
  by_cases hp : p = p₀
  · rw [hp, hu1, mul_one, mul_inv_cancel, hsq]
  obtain ⟨α, hs, hα⟩ := exists_four_superset (by omega) {p₀, p}
    (le_trans Finset.card_le_two (by norm_num))
  have hp₀α : p₀ ∈ α := hs (by simp)
  have hpα : p ∈ α := hs (by simp)
  have h1 := hu p₀ p (Ne.symm hp) α hα hp₀α hpα
  rw [hu1, one_mul] at h1
  have h2 := h1.conj hH g
  rw [conj_ePt_mul] at h2
  exact h2.unique hH hk (hu _ _ ((permQ k (I.φ g)).injective.ne (Ne.symm hp)) _ _
    (Finset.mem_map_of_mem _ hp₀α) (Finset.mem_map_of_mem _ hpα))

end Pairs

section SV

open CFSG.ClassicalInvolution.Q3.TL4.AECov (sv pow_val_add mkQ_ofVec_pow ofVec_zero)

variable {A : Type*} [CommGroup A] {k : ℕ} (u : Fin k → A)

theorem sv_single (a : Fin k) : sv u (Pi.single a 1) = u a := by
  classical
  rw [sv, Finset.prod_eq_single a
    (fun p _ hp => by rw [Pi.single_eq_of_ne hp, ZMod.val_zero, pow_zero])
    (fun h => absurd (Finset.mem_univ a) h), Pi.single_eq_same]
  exact pow_one (u a)

theorem prod_pow_val {t : A} (ht : t * t = 1) (v : Fin k → ZMod 2) (S : Finset (Fin k)) :
    ∏ p ∈ S, t ^ (v p).val = t ^ (∑ p ∈ S, v p).val := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pow_val_add ht]

theorem sv_conj (c : A →* A) (σ : Equiv.Perm (Fin k)) {t : A} (ht : t * t = 1)
    (hc : ∀ p, c (u p) = t * u (σ p)) {v : Fin k → ZMod 2} (hv : ∑ i, v i = 0) :
    c (sv u v) = sv u fun q => v (σ.symm q) := by
  rw [sv, map_prod]
  simp only [map_pow, hc, mul_pow, Finset.prod_mul_distrib]
  rw [prod_pow_val ht, hv, ZMod.val_zero, pow_zero, one_mul, sv]
  exact Fintype.prod_equiv σ _ _ fun p => by rw [Equiv.symm_apply_apply]

theorem f_prod_vec (f : A →* AEQ k) (w : Fin k → Fin k → ZMod 2)
    (hf : ∀ p, f (u p) = mkQ k (ofVec (w p))) (v : Fin k → ZMod 2) (S : Finset (Fin k)) :
    f (∏ p ∈ S, u p ^ (v p).val) = mkQ k (ofVec (∑ p ∈ S, (v p).val • w p)) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, map_one, ofVec_zero, map_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, ih, map_pow, hf, mkQ_ofVec_pow,
      ← map_mul, ← ofVec_add]

theorem f_sv_pair (f : A →* AEQ k) (p₀ : Fin k) (hf : ∀ p, f (u p) = ePt k p₀ * ePt k p)
    {v : Fin k → ZMod 2} (hv : ∑ i, v i = 0) : f (sv u v) = mkQ k (ofVec v) := by
  classical
  have hf' : ∀ p, f (u p) = mkQ k (ofVec (Pi.single p₀ 1 + Pi.single p 1)) := fun p => by
    rw [hf, ePt, ePt, ← map_mul, ← ofVec_add]
  rw [sv, f_prod_vec u f _ hf' v Finset.univ]
  congr 2
  have key : ∀ p, (v p).val • (Pi.single p₀ 1 + Pi.single p 1 : Fin k → ZMod 2) =
      v p • (Pi.single p₀ 1 + Pi.single p 1) := fun p => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
  simp only [key, smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, hv, zero_smul, zero_add]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_single_four (a b c d : Fin k) :
    ∑ i, (Pi.single a 1 + Pi.single b 1 + (Pi.single c 1 + Pi.single d 1) :
      Fin k → ZMod 2) i = 0 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  decide

end SV

section Members

theorem comm_mul_central_left {W : Type*} [Group W] (x y c : W) (hc : ∀ g, c * g = g * c) :
    (x * c) * y * (x * c)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  calc (x * c) * y * (x * c)⁻¹ * y⁻¹ = x * (c * y) * c⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * c) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [hc y]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_mul_central_right {W : Type*} [Group W] (x y d : W) (hd : ∀ g, d * g = g * d) :
    x * (y * d) * x⁻¹ * (y * d)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  calc x * (y * d) * x⁻¹ * (y * d)⁻¹ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [hd x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem eq_or_eq_mul_allOnes {n : ℕ} {a b : Wr n} (h : mkQ n a = mkQ n b) :
    b = a ∨ b = a * allOnes n := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact Or.inl (inv_mul_eq_one.mp h1).symm
  · exact Or.inr (by rw [← h1]; group)

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ} {I : AEIdent P k}

theorem map_member_eq (hH : TL4.AECoverHyp I) (ψ : ↥(pSpan P) ≃* ↥(aeSub k))
    (hψ : ∀ x, mkQ k (ψ x : Wr k) = I.φ x) {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin k)}
    {h : α.card = 4} {b : Bool} (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h b) :
    ((L.subgroupOf (pSpan P)).map ψ.toMonoidHom).map (aeSub k).subtype = memAt α h b := by
  set H := ((L.subgroupOf (pSpan P)).map ψ.toMonoidHom).map (aeSub k).subtype with hHdef
  have hπ : ∀ g : Wr k, allOnes k * g = g * allOnes k := allOnes_comm
  have hlift : ∀ m ∈ memAt α h b, ∃ w ∈ H, w = m ∨ w = m * allOnes k := by
    intro m hm
    have hmb : mkQ k m ∈ (L.subgroupOf (pSpan P)).map I.φ := by
      rw [hlab]
      exact ⟨m, hm, rfl⟩
    obtain ⟨l, hl, hle⟩ := I.exists_of_mem_map hL hmb
    refine ⟨(ψ ⟨l, le_pSpan hL hl⟩ : Wr k), ⟨ψ ⟨l, le_pSpan hL hl⟩,
      ⟨⟨l, le_pSpan hL hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, rfl⟩, ?_⟩
    exact eq_or_eq_mul_allOnes ((hψ _).trans hle).symm
  obtain ⟨y, hy⟩ : yBar α h ∈ I.φ.range := by
    rw [I.range_eq]
    exact yBar_mem α h
  have hyL : conjSub (y : G) L = L := by
    refine hH.label_inj _ (hH.conj_mem L hL y y.2) L hL ?_
    rw [TL4.AECov.map_conjSub_eq, hy, hlab, TL4.AECov.conjSub_yBar_memBar]
  have hyH : ∀ w ∈ H, (ψ y : Wr k) * w * (ψ y : Wr k)⁻¹ ∈ H := by
    rintro _ ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩, rfl⟩
    have hl' : l ∈ L := Subgroup.mem_subgroupOf.mp hl
    have h1 : (y : G) * l * (y : G)⁻¹ ∈ L := by
      rw [← hyL]
      exact conj_mem_conjSub hl'
    refine ⟨ψ (y * ⟨l, hlX⟩ * y⁻¹), ⟨y * ⟨l, hlX⟩ * y⁻¹, Subgroup.mem_subgroupOf.mpr h1, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hyo := eq_or_eq_mul_allOnes (a := yOf (emb α h)) (b := (ψ y : Wr k))
    (by rw [hψ, hy]; rfl)
  have hcomm : ∀ m ∈ memAt α h b, m * yOf (emb α h) * m⁻¹ * (yOf (emb α h))⁻¹ ∈ H := by
    intro m hm
    obtain ⟨w, hw, hwm⟩ := hlift m hm
    have h1 : w * (ψ y : Wr k) * w⁻¹ * (ψ y : Wr k)⁻¹ ∈ H := by
      have := H.mul_mem hw (hyH _ (H.inv_mem hw))
      simpa [mul_assoc] using this
    have e : w * (ψ y : Wr k) * w⁻¹ * (ψ y : Wr k)⁻¹ =
        m * yOf (emb α h) * m⁻¹ * (yOf (emb α h))⁻¹ := by
      rcases hwm with rfl | rfl <;> rcases hyo with h2 | h2 <;> rw [h2]
      · exact comm_mul_central_right _ _ _ hπ
      · exact comm_mul_central_left _ _ _ hπ
      · rw [comm_mul_central_left _ _ _ hπ, comm_mul_central_right _ _ _ hπ]
    rwa [e] at h1
  have hle : memAt α h b ≤ H := fun m hm => by
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := memAt_comm_yOf α h b hm
    exact H.mul_mem (hcomm m₁ hm₁) (hcomm m₂ hm₂)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hHdef, Subgroup.card_map_of_injective (aeSub k).subtype_injective,
    Subgroup.card_map_of_injective ψ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).toEquiv, hH.card L hL,
    natCard_memAt]

end Members

section Elem

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ} {I : AEIdent P k}

theorem ker_permHom_elem (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) :
    (∀ a ∈ (TL4.AECov.permHom I).ker, ∀ b ∈ (TL4.AECov.permHom I).ker,
      a * b = b * a ∧ a * a = 1) ∧ (TL4.AECov.permHom I).ker ≤ TL4.AECov.zSpan P := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u := fun L hL L' hL' u u' hu hu' =>
    TL4.AECov.comm_of_isUniqueInvolution I hk hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL'
      hu hu'
  have hW := TL4.AECov.zSpan_elem hcomm
  have hUW := TL4.AECov.ker_permHom_le_zSpan I (by omega) hH.card hH.conj_mem hH.label_inj
    hH.ker_two (TL4.AECov.zSpan_normal hH.conj_mem) hW
  exact ⟨fun a ha b hb => hW a (hUW ha) b (hUW hb), hUW⟩

theorem ker_le_zSpan (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) : I.φ.ker ≤ TL4.AECov.zSpan P := by
  intro z hz
  refine (ker_permHom_elem hH hk).2 ?_
  rw [TL4.AECov.mem_ker_permHom, MonoidHom.mem_ker.mp hz, map_one]

theorem ker_eq_center (hk : 5 ≤ k) (I : AEIdent P k) :
    I.φ.ker = Subgroup.center ↥(pSpan P) := by
  refine le_antisymm I.ker_le fun z hz => ?_
  rw [MonoidHom.mem_ker]
  refine aeModel_center hk _ (TL4.AECov.mem_aeModel I z) fun m hm => ?_
  have hm' : m ∈ I.φ.range := by
    rw [I.range_eq]
    exact hm
  obtain ⟨x, rfl⟩ := hm'
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz x).symm]

end Elem

section Iso

open CFSG.ClassicalInvolution.Q3.TL4.AECov (sv sv_add sv_zero)

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ} {I : AEIdent P k}

theorem exists_vecLift (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) :
    ∃ Φ : (Fin k → ZMod 2) → ↥(pSpan P), (∀ v w, Φ (v + w) = Φ v * Φ w) ∧
      (∀ v, Φ v ∈ (TL4.AECov.permHom I).ker) ∧
      (∀ v, ∑ i, v i = 0 → I.φ (Φ v) = mkQ k (ofVec v)) ∧
      (∀ x ∈ TL4.AECov.zSpan P, ∃ v : Fin k → ZMod 2, ∑ i, v i = 0 ∧ x = Φ v) ∧
      ∀ (g : ↥(pSpan P)) (v : Fin k → ZMod 2), ∑ i, v i = 0 →
        g * Φ v * g⁻¹ = Φ fun q => v ((permQ k (I.φ g)).symm q) := by
  classical
  obtain ⟨hU, -⟩ := ker_permHom_elem hH hk
  set U := (TL4.AECov.permHom I).ker with hUdef
  set p₀ : Fin k := ⟨0, by omega⟩ with hp₀
  obtain ⟨u, hu1, hu⟩ := exists_pointLift hH hk p₀
  have huφ : ∀ p, I.φ (u p) = ePt k p₀ * ePt k p := by
    intro p
    by_cases hp : p = p₀
    · rw [hp, hu1, map_one, ePt_mul_self]
    obtain ⟨α, hs, hα⟩ := exists_four_superset (by omega) {p₀, p}
      (le_trans Finset.card_le_two (by norm_num))
    have h1 := (hu p₀ p (Ne.symm hp) α hα (hs (by simp)) (hs (by simp))).2
    rwa [hu1, one_mul] at h1
  have huU : ∀ p, u p ∈ U := fun p => by
    rw [hUdef, TL4.AECov.mem_ker_permHom, huφ, map_mul]
    rfl
  have hsq : ∀ p, u p * u p = 1 := fun p => (hU _ (huU p) _ (huU p)).2
  letI : CommGroup ↥U :=
    { (inferInstance : Group ↥U) with mul_comm := fun a b => Subtype.ext (hU a a.2 b b.2).1 }
  set uA : Fin k → ↥U := fun p => ⟨u p, huU p⟩ with huA
  have hu2 : ∀ p, uA p * uA p = 1 := fun p => Subtype.ext (hsq p)
  set Φ : (Fin k → ZMod 2) → ↥(pSpan P) := fun v => ((sv uA v : ↥U) : ↥(pSpan P)) with hΦ
  have hΦU : ∀ v, Φ v ∈ U := fun v => (sv uA v).2
  have hΦadd : ∀ v w, Φ (v + w) = Φ v * Φ w := fun v w => by
    rw [hΦ]
    dsimp only
    rw [sv_add uA hu2]
    rfl
  have hΦsingle : ∀ a, Φ (Pi.single a 1) = u a := fun a => by
    rw [hΦ]
    dsimp only
    rw [sv_single uA a]
  have hWs : ∀ x ∈ TL4.AECov.zSpan P, ∃ v : Fin k → ZMod 2, ∑ i, v i = 0 ∧ x = Φ v := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨L, hL, hxL⟩ := hx
      obtain ⟨α, h, b, hlab⟩ := I.label L hL
      have e := inv_eq_pointLift hH hk hu hL hlab hxL
      refine ⟨Pi.single (emb α h 0) 1 + Pi.single (emb α h 1) 1 +
        (Pi.single (emb α h 2) 1 + Pi.single (emb α h 3) 1), sum_single_four _ _ _ _, ?_⟩
      rw [hΦadd, hΦadd, hΦadd, hΦsingle, hΦsingle, hΦsingle, hΦsingle]
      exact (Subtype.coe_eta x _).symm.trans e
    | one => exact ⟨0, by simp, by rw [hΦ]; dsimp only; rw [sv_zero]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨v, hv, rfl⟩ := ihx
      obtain ⟨w, hw, rfl⟩ := ihy
      exact ⟨v + w, by simp only [Pi.add_apply]; rw [Finset.sum_add_distrib, hv, hw, add_zero],
        (hΦadd v w).symm⟩
    | inv x _ ih =>
      obtain ⟨v, hv, rfl⟩ := ih
      exact ⟨v, hv, inv_eq_of_mul_eq_one_right (hU _ (hΦU v) _ (hΦU v)).2⟩
  have hconj : ∀ (g : ↥(pSpan P)) (v : Fin k → ZMod 2), ∑ i, v i = 0 →
      g * Φ v * g⁻¹ = Φ fun q => v ((permQ k (I.φ g)).symm q) := by
    intro g v hv
    set c : ↥U →* ↥U := (MulAut.conjNormal g).toMonoidHom with hc
    have hcu : ∀ p, c (uA p) = uA (permQ k (I.φ g) p₀) * uA (permQ k (I.φ g) p) := fun p =>
      Subtype.ext (conj_pointLift hH hk hu1 hu hsq g p)
    exact congrArg Subtype.val (sv_conj uA c (permQ k (I.φ g)) (hu2 _) hcu hv)
  exact ⟨Φ, hΦadd, hΦU, fun v hv => f_sv_pair uA (I.φ.comp U.subtype) p₀ huφ hv, hWs, hconj⟩

theorem exists_aeSub_equiv (hH : TL4.AECoverHyp I) (hk : 5 ≤ k)
    {Φ : (Fin k → ZMod 2) → ↥(pSpan P)} (hΦadd : ∀ v w, Φ (v + w) = Φ v * Φ w)
    (hΦφ : ∀ v, ∑ i, v i = 0 → I.φ (Φ v) = mkQ k (ofVec v))
    (hWs : ∀ x ∈ TL4.AECov.zSpan P, ∃ v : Fin k → ZMod 2, ∑ i, v i = 0 ∧ x = Φ v)
    (hconj : ∀ (g : ↥(pSpan P)) (v : Fin k → ZMod 2), ∑ i, v i = 0 →
      g * Φ v * g⁻¹ = Φ fun q => v ((permQ k (I.φ g)).symm q))
    (hπ1 : (Φ fun _ => 1) ≠ 1) :
    ∃ ψ : ↥(pSpan P) ≃* ↥(aeSub k), ∀ x, mkQ k (ψ x : Wr k) = I.φ x := by
  obtain ⟨-, hUW⟩ := ker_permHom_elem hH hk
  have hΦ0 : Φ 0 = 1 := by
    have h := hΦadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  obtain ⟨s, hs⟩ := AEIdent.exists_section hk I hH.ker_two hH.card
    (fun L hL => by
      obtain ⟨α, h, b, hlab⟩ := I.label L hL
      obtain ⟨z, hz, -⟩ := TL4.AECov.exists_isUniqueInvolution I hk hL (hH.card L hL) hlab
      exact ⟨z, hz⟩)
    (fun L hL L' hL' α hα h1 h2 => ⟨hH.twin_comm α hα L hL L' hL' h1 h2,
      hH.twin_z α hα L hL L' hL' h1 h2⟩)
    hH.label_inj hH.conj_mem
  have hsσ : ∀ σ : alternatingGroup (Fin k), permQ k (I.φ (s σ)) = σ := fun σ => by
    rw [hs]
    rfl
  have hperm : ∀ a : ↥(aeSub k), (a : Wr k).perm ∈ alternatingGroup (Fin k) := fun a =>
    Equiv.Perm.mem_alternatingGroup.mpr a.2.2
  let χ : ↥(aeSub k) →* ↥(pSpan P) :=
    { toFun := fun a => Φ (a : Wr k).vec * s ⟨(a : Wr k).perm, hperm a⟩
      map_one' := by
        show Φ 0 * s 1 = 1
        rw [map_one, mul_one, hΦ0]
      map_mul' := fun a b => by
        show Φ ((a : Wr k) * b).vec * s (⟨(a : Wr k).perm, hperm a⟩ * ⟨(b : Wr k).perm, hperm b⟩) =
          Φ (a : Wr k).vec * s ⟨(a : Wr k).perm, hperm a⟩ *
            (Φ (b : Wr k).vec * s ⟨(b : Wr k).perm, hperm b⟩)
        have hvec : ((a : Wr k) * b).vec =
            (a : Wr k).vec + fun i => (b : Wr k).vec ((a : Wr k).perm.symm i) := rfl
        have hc := hconj (s ⟨(a : Wr k).perm, hperm a⟩) (b : Wr k).vec b.2.1
        rw [hsσ] at hc
        rw [hvec, hΦadd, map_mul, ← hc]
        group }
  have hφχ : ∀ a, I.φ (χ a) = mkQ k (a : Wr k) := fun a => by
    show I.φ (Φ (a : Wr k).vec * s ⟨(a : Wr k).perm, hperm a⟩) = _
    rw [map_mul, hΦφ _ a.2.1, hs, ← map_mul]
    exact congrArg (mkQ k) (ofVec_mul_ofPerm (a : Wr k))
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : mkQ k (a : Wr k) = 1 := by rw [← hφχ, ha, map_one]
    have h2 : (a : Wr k) ∈ piSub k := (QuotientGroup.eq_one_iff (N := piSub k) _).mp h1
    rcases mem_piSub.mp h2 with h3 | h3
    · exact Subtype.ext h3
    · exfalso
      apply hπ1
      have hv : (a : Wr k).vec = fun _ => 1 := congrArg Wr.vec h3
      have hp : (⟨(a : Wr k).perm, hperm a⟩ : alternatingGroup (Fin k)) = 1 :=
        Subtype.ext (congrArg Wr.perm h3)
      have e : χ a = Φ fun _ => 1 := by
        show Φ (a : Wr k).vec * s ⟨(a : Wr k).perm, hperm a⟩ = _
        rw [hv, hp, map_one, mul_one]
      rw [← e, ha]
  have hsurj : Function.Surjective χ := by
    intro x
    set σ := TL4.AECov.permHom I x with hσ
    have hσs : TL4.AECov.permHom I (s σ) = σ := Subtype.ext (by
      rw [TL4.AECov.coe_permHom, hsσ])
    have hx' : x * (s σ)⁻¹ ∈ (TL4.AECov.permHom I).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσs, mul_inv_cancel]
    obtain ⟨v, hv, hxv⟩ := hWs _ (hUW hx')
    refine ⟨⟨⟨v, σ⟩, hv, Equiv.Perm.mem_alternatingGroup.mp σ.2⟩, ?_⟩
    show Φ v * s σ = x
    rw [← hxv, inv_mul_cancel_right]
  refine ⟨(MulEquiv.ofBijective χ ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
  have e : χ ((MulEquiv.ofBijective χ ⟨hinj, hsurj⟩).symm x) = x :=
    (MulEquiv.ofBijective χ ⟨hinj, hsurj⟩).apply_symm_apply x
  rw [← hφχ, e]

end Iso

end EvenCov

open EvenCov

theorem aeCover_ker {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ}
    {I : AEIdent P k} (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) :
    Nat.card I.φ.ker ≤ 2 ∧
      (I.φ.ker = ⊥ ∨ ∃ ψ : ↥(pSpan P) ≃* ↥(aeSub k),
        (∀ x, mkQ k (ψ x : Wr k) = I.φ x) ∧
        ∀ L ∈ P, ∀ (α : Finset (Fin k)) (h : α.card = 4) (b : Bool),
          (L.subgroupOf (pSpan P)).map I.φ = memBar α h b →
          ((L.subgroupOf (pSpan P)).map ψ.toMonoidHom).map (aeSub k).subtype = memAt α h b) := by
  obtain ⟨hU, -⟩ := ker_permHom_elem hH hk
  obtain ⟨Φ, hΦadd, hΦU, hΦφ, hWs, hconj⟩ := exists_vecLift hH hk
  have hker : ∀ z ∈ I.φ.ker, z = 1 ∨ z = Φ fun _ => 1 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hWs z (ker_le_zSpan hH hk hz)
    have h1 : mkQ k (ofVec v) = 1 := by rw [← hΦφ v hv]; exact hz
    have h2 : ofVec v ∈ piSub k := (QuotientGroup.eq_one_iff (N := piSub k) (ofVec v)).mp h1
    rcases mem_piSub.mp h2 with h3 | h3
    · left
      have hv0 : v = 0 := congrArg Wr.vec h3
      have h := hΦadd 0 0
      rw [add_zero] at h
      rw [hv0]
      exact mul_left_cancel (h.symm.trans (mul_one _).symm)
    · right
      have hv1 : v = fun _ => 1 := congrArg Wr.vec h3
      rw [hv1]
  have hcard : Nat.card I.φ.ker ≤ 2 := by
    have hle : I.φ.ker ≤ Subgroup.zpowers (Φ fun _ => 1) := by
      intro z hz
      rcases hker z hz with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have h2 : (Φ fun _ => 1) ^ 2 = 1 := by
      rw [sq]
      exact (hU _ (hΦU fun _ => 1) _ (hΦU fun _ => 1)).2
    calc Nat.card I.φ.ker ≤ Nat.card (Subgroup.zpowers (Φ fun _ => 1)) :=
          Subgroup.card_le_of_le hle
      _ = orderOf (Φ fun _ => 1) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) h2
  refine ⟨hcard, ?_⟩
  by_cases hbot : I.φ.ker = ⊥
  · exact Or.inl hbot
  right
  have hπ1 : (Φ fun _ => 1) ≠ 1 := by
    obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    rcases hker z z.2 with h1 | h1
    · exact absurd (Subtype.ext h1) hz
    · rw [← h1]
      exact fun h => hz (Subtype.ext h)
  obtain ⟨ψ, hψ⟩ := exists_aeSub_equiv hH hk hΦadd hΦφ hWs hconj hπ1
  exact ⟨ψ, hψ, fun L hL α h b hlab => map_member_eq hH ψ hψ hL hlab⟩

theorem aeCoverEvenKer_proved :
    ∀ (G : Type) [Group G] [Finite G] (P : Set (Subgroup G)) (k : ℕ) (I : AEIdent P k),
      5 ≤ k → Even k → TL4.AECoverHyp I →
        Nat.card I.φ.ker ≤ 2 ∧
        (I.φ.ker = ⊥ ∨ ∃ ψ : ↥(pSpan P) ≃* ↥(aeSub k),
          (∀ x, mkQ k (ψ x : Wr k) = I.φ x) ∧
          ∀ L ∈ P, ∀ (α : Finset (Fin k)) (h : α.card = 4) (b : Bool),
            (L.subgroupOf (pSpan P)).map I.φ = memBar α h b →
            ((L.subgroupOf (pSpan P)).map ψ.toMonoidHom).map (aeSub k).subtype = memAt α h b) :=
  fun _ _ _ _ _ _ hk _ hH => aeCover_ker hH hk

end CFSG.ClassicalInvolution.Q3.Sec13
