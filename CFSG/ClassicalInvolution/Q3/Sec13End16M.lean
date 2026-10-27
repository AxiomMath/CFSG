module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

private theorem e16m_ofVec_eq_one (u : Fin n → ZMod 2) : Wr.ofVec u = 1 ↔ u = 0 :=
  ⟨fun h => congrArg Wr.vec h, fun h => by subst h; rfl⟩

private theorem e16m_ofVec_eq_allOnes (u : Fin n → ZMod 2) :
    Wr.ofVec u = Wr.allOnes n ↔ u = fun _ => 1 :=
  ⟨fun h => congrArg Wr.vec h, fun h => by subst h; rfl⟩

private theorem e16m_conj_ofVec (v : Fin n → ZMod 2) (E : Wr n) :
    Wr.ofVec v * E * (Wr.ofVec v)⁻¹ = Wr.ofVec (fun x => v x + v (E.perm.symm x)) * E := by
  refine Wr.ext (funext fun x => ?_) ?_
  · simp [mul_vec, inv_vec, mul_perm, Wr.ofVec, one_perm]
    ring
  · simp [mul_perm, inv_perm, Wr.ofVec, one_perm]

private theorem e16m_comm_iff (v : Fin n → ZMod 2) (E : Wr n) :
    mkQ n (Wr.ofVec v) * mkQ n E = mkQ n E * mkQ n (Wr.ofVec v) ↔
      (fun x => v x + v (E.perm.symm x)) = 0 ∨ (fun x => v x + v (E.perm.symm x)) = fun _ => 1 := by
  rw [← mul_inv_eq_iff_eq_mul, ← map_inv, ← map_mul, ← map_mul, e16m_conj_ofVec, map_mul,
    mul_eq_right]
  change (QuotientGroup.mk (Wr.ofVec _) : AEQ n) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_piSub, e16m_ofVec_eq_one, e16m_ofVec_eq_allOnes]

private theorem e16m_exists_notMem (s : Finset (Fin n)) (hs : s.card < n) : ∃ x, x ∉ s := by
  by_contra hne
  have : s = Finset.univ := Finset.eq_univ_of_forall fun x => by
    by_contra hx
    exact hne ⟨x, hx⟩
  rw [this, Finset.card_univ, Fintype.card_fin] at hs
  omega

private theorem e16m_mem_of_range {α : Finset (Fin n)} {h : α.card = 4} {x : Fin n}
    (hx : x ∈ Set.range (emb α h)) : x ∈ α := by
  rw [range_emb] at hx
  exact hx

private theorem e16m_range_of_mem {α : Finset (Fin n)} {h : α.card = 4} {x : Fin n}
    (hx : x ∈ α) : x ∈ Set.range (emb α h) := by
  rw [range_emb]
  exact hx

private theorem e16m_memAt_form {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : Wr n}
    (ha : a ∈ memAt α h b) : ∃ k : Wr 4, (k ∈ kList ∨ k ∈ kStarList) ∧ a = embed (emb α h) k := by
  cases b
  · obtain ⟨k, hk, rfl⟩ := ha
    exact ⟨k, Or.inr hk, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := ha
    exact ⟨k, Or.inl hk, rfl⟩

private theorem e16m_exists_perm (α : Finset (Fin n)) (h : α.card = 4) (b : Bool)
    {d : Equiv.Perm (Fin 4)} (hd : d ∈ [d₁, d₂, d₃]) :
    ∃ a ∈ memAt α h b, a.perm = embedPerm (emb α h) d := by
  cases b
  · obtain ⟨k, hk, hkd⟩ := exists_mem_kQStar_perm d hd
    exact ⟨embed (emb α h) k, ⟨k, mem_kQStar.mpr hk, rfl⟩, by rw [embed_perm, hkd]⟩
  · obtain ⟨k, hk, hkd⟩ := exists_mem_kQ_perm d hd
    exact ⟨embed (emb α h) k, ⟨k, mem_kQ.mpr hk, rfl⟩, by rw [embed_perm, hkd]⟩

private theorem e16m_sum_emb (α : Finset (Fin n)) (h : α.card = 4) (v : Fin n → ZMod 2) :
    ∑ i ∈ α, v i = ∑ i : Fin 4, v (emb α h i) := by
  have hα : Finset.univ.map (emb α h) = α :=
    Finset.coe_injective ((range_eq_finset _).symm.trans (range_emb α h))
  have h1 : ∑ x ∈ Finset.univ.map (emb α h), v x = ∑ i : Fin 4, v (emb α h i) :=
    Finset.sum_map _ _ _
  rw [hα] at h1
  exact h1

private theorem e16m_perm_const_kList : ∀ k ∈ kList, ∀ w : Fin 4 → ZMod 2, ∑ i, w i = 0 →
    ∀ i j : Fin 4, w i + w (k.perm.symm i) = w j + w (k.perm.symm j) := by
  decide +kernel

private theorem e16m_perm_const_kStarList : ∀ k ∈ kStarList, ∀ w : Fin 4 → ZMod 2,
    ∑ i, w i = 0 → ∀ i j : Fin 4, w i + w (k.perm.symm i) = w j + w (k.perm.symm j) := by
  decide +kernel

private theorem e16m_vec_const_kList : ∀ k ∈ kList, k.perm = 1 → ∀ i j : Fin 4,
    k.vec i = k.vec j := by
  decide +kernel

private theorem e16m_vec_const_kStarList : ∀ k ∈ kStarList, k.perm = 1 → ∀ i j : Fin 4,
    k.vec i = k.vec j := by
  decide +kernel

private theorem e16m_zmod2_key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem e16m_zmod2_eq : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide

private theorem e16m_ofVec_mem {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    {u : Fin n → ZMod 2} (hsupp : ∀ x, x ∉ Set.range (emb α h) → u x = 0)
    (hconst : ∀ i j : Fin 4, u (emb α h i) = u (emb α h j)) : Wr.ofVec u ∈ memAt α h b := by
  rcases e16m_zmod2_key (u (emb α h 0)) with h0 | h1
  · have hu : u = 0 := funext fun x => by
      by_cases hx : x ∈ Set.range (emb α h)
      · obtain ⟨i, rfl⟩ := hx
        rw [hconst i 0, h0]
        rfl
      · exact hsupp x hx
    rw [hu]
    have h1' : Wr.ofVec (0 : Fin n → ZMod 2) = 1 := rfl
    rw [h1']
    exact Subgroup.one_mem _
  · have hu : u = (zOf (emb α h)).vec := funext fun x => by
      rw [zOf_vec_apply]
      by_cases hx : x ∈ Set.range (emb α h)
      · obtain ⟨i, rfl⟩ := hx
        rw [if_pos (Set.mem_range_self i), hconst i 0, h1]
      · rw [if_neg hx]
        exact hsupp x hx
    have hz : Wr.ofVec u = zOf (emb α h) := by
      rw [hu]
      exact Wr.ext rfl (zOf_perm _).symm
    rw [hz]
    exact zOf_mem_memAt α h b

private theorem e16m_const_of_ofVec_mem {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    {u : Fin n → ZMod 2} (hu : Wr.ofVec u ∈ memAt α h b) (i j : Fin 4) :
    u (emb α h i) = u (emb α h j) := by
  obtain ⟨k, hk, hke⟩ := e16m_memAt_form hu
  have hp : embedPerm (emb α h) k.perm = 1 := by
    rw [← embed_perm, ← hke]
    rfl
  have hk1 : k.perm = 1 := Equiv.ext fun x => by
    have hx := congrArg (fun σ : Equiv.Perm (Fin n) => σ (emb α h x)) hp
    simp only [embedPerm_apply, Equiv.Perm.one_apply] at hx
    rw [Equiv.Perm.one_apply]
    exact (emb α h).injective hx
  have hval : ∀ x : Fin 4, u (emb α h x) = k.vec x := fun x => by
    show (Wr.ofVec u).vec (emb α h x) = k.vec x
    rw [hke, embed_vec, embedVec_apply]
  rw [hval i, hval j]
  rcases hk with hk | hk
  · exact e16m_vec_const_kList k hk hk1 i j
  · exact e16m_vec_const_kStarList k hk hk1 i j

private theorem e16m_u_const {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : Wr n}
    (ha : a ∈ memAt α h b) (v : Fin n → ZMod 2) (hsum : ∑ i ∈ α, v i = 0) (i j : Fin 4) :
    v (emb α h i) + v (a.perm.symm (emb α h i)) =
      v (emb α h j) + v (a.perm.symm (emb α h j)) := by
  obtain ⟨k, hk, rfl⟩ := e16m_memAt_form ha
  rw [embed_perm, embedPerm_symm_apply, embedPerm_symm_apply]
  have hw : ∑ x, v (emb α h x) = 0 := by
    rw [← e16m_sum_emb α h v]
    exact hsum
  rcases hk with hk | hk
  · exact e16m_perm_const_kList k hk (fun x => v (emb α h x)) hw i j
  · exact e16m_perm_const_kStarList k hk (fun x => v (emb α h x)) hw i j

private theorem e16m_supp_mul {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {a : Wr n}
    (ha : a ∈ memAt α h b) (u : Fin n → ZMod 2) (hsupp : ∀ x, x ∉ Set.range (emb α h) → u x = 0) :
    SupportedOn (Wr.ofVec u * a) (Set.range (emb α h)) := by
  intro x hx
  have hs := supportedOn_of_mem_memAt ha x hx
  refine ⟨?_, ?_⟩
  · rw [mul_vec]
    have h1s : (1 : Equiv.Perm (Fin n)).symm x = x := rfl
    show u x + a.vec ((1 : Equiv.Perm (Fin n)).symm x) = 0
    rw [h1s, hsupp x hx, hs.1, add_zero]
  · rw [mul_perm]
    simp [Wr.ofVec, hs.2]

private theorem e16m_sum4 : ∀ A B C D : ZMod 2, A + B = C + D → A + B + C + D = 0 := by
  decide

private theorem e16m_rel_of_centralizes (v : Fin n → ZMod 2) {α : Finset (Fin n)}
    {h : α.card = 4} {b : Bool}
    (H : ∀ x ∈ memBar α h b, mkQ n (Wr.ofVec v) * x = x * mkQ n (Wr.ofVec v))
    {d : Equiv.Perm (Fin 4)} (hd : d ∈ [d₁, d₂, d₃]) {x₀ : Fin n}
    (hx₀ : x₀ ∉ Set.range (emb α h)) :
    ∀ i : Fin 4, v (emb α h i) = v (emb α h (d.symm i)) := by
  obtain ⟨a, ha, hap⟩ := e16m_exists_perm α h b hd
  have hcomm := H (mkQ n a) ⟨a, ha, rfl⟩
  rcases (e16m_comm_iff v a).mp hcomm with h0 | h1
  · intro i
    have hi := congrFun h0 (emb α h i)
    simp only [Pi.zero_apply] at hi
    rw [hap, embedPerm_symm_apply] at hi
    exact e16m_zmod2_eq _ _ hi
  · exfalso
    have hi := congrFun h1 x₀
    rw [SupportedOn.perm_symm (supportedOn_of_mem_memAt ha) hx₀, Wr.zmod_two_add_self] at hi
    exact absurd hi (by decide)

theorem vec_normalizes_memBar_iff (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool)
    (v : Fin n → ZMod 2) :
    (∀ x ∈ memBar α h b, mkQ n (Wr.ofVec v) * x * (mkQ n (Wr.ofVec v))⁻¹ ∈ memBar α h b) ↔
      ∑ i ∈ α, v i = 0 := by
  have hconj : ∀ a : Wr n, mkQ n (Wr.ofVec v) * mkQ n a * (mkQ n (Wr.ofVec v))⁻¹ =
      mkQ n (Wr.ofVec (fun x => v x + v (a.perm.symm x)) * a) := by
    intro a
    rw [← map_inv, ← map_mul, ← map_mul, e16m_conj_ofVec]
  constructor
  · intro H
    obtain ⟨a, ha, hap⟩ := e16m_exists_perm α h b (d := d₁) (by simp)
    have hH := H (mkQ n a) ⟨a, ha, rfl⟩
    rw [hconj] at hH
    obtain ⟨a', ha', hEq⟩ := hH
    have hsupp : ∀ x, x ∉ Set.range (emb α h) → (fun y => v y + v (a.perm.symm y)) x = 0 := by
      intro x hx
      show v x + v (a.perm.symm x) = 0
      rw [SupportedOn.perm_symm (supportedOn_of_mem_memAt ha) hx, Wr.zmod_two_add_self]
    have heq := mkQ_inj_of_supportedOn hn (supportedOn_of_mem_memAt ha')
      (e16m_supp_mul ha _ hsupp) hEq
    have hmem : Wr.ofVec (fun x => v x + v (a.perm.symm x)) ∈ memAt α h b := by
      have h2 := Subgroup.mul_mem _ (heq ▸ ha' : Wr.ofVec _ * a ∈ memAt α h b)
        (Subgroup.inv_mem _ ha)
      simpa using h2
    have hc := e16m_const_of_ofVec_mem hmem 0 2
    rw [hap, embedPerm_symm_apply, embedPerm_symm_apply] at hc
    have e1 : d₁.symm 0 = 1 := by decide
    have e2 : d₁.symm 2 = 3 := by decide
    rw [e1, e2] at hc
    rw [e16m_sum_emb α h v, Fin.sum_univ_four]
    exact e16m_sum4 _ _ _ _ hc
  · intro hsum x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hu : Wr.ofVec (fun y => v y + v (a.perm.symm y)) ∈ memAt α h b := by
      apply e16m_ofVec_mem
      · intro y hy
        show v y + v (a.perm.symm y) = 0
        rw [SupportedOn.perm_symm (supportedOn_of_mem_memAt ha) hy, Wr.zmod_two_add_self]
      · intro i j
        exact e16m_u_const ha v hsum i j
    rw [hconj]
    exact ⟨_, Subgroup.mul_mem _ hu ha, rfl⟩

theorem vec_centralizes_memBar_iff (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool)
    (v : Fin n → ZMod 2) :
    (∀ x ∈ memBar α h b, mkQ n (Wr.ofVec v) * x = x * mkQ n (Wr.ofVec v)) ↔
      ∀ i ∈ α, ∀ j ∈ α, v i = v j := by
  constructor
  · intro H
    obtain ⟨x₀, hx₀⟩ := e16m_exists_notMem α (by omega)
    have hx₀r : x₀ ∉ Set.range (emb α h) := fun hr => hx₀ (e16m_mem_of_range hr)
    have r1 := e16m_rel_of_centralizes v H (d := d₁) (by simp) hx₀r
    have r2 := e16m_rel_of_centralizes v H (d := d₂) (by simp) hx₀r
    have e1 : d₁.symm 0 = 1 := by decide
    have e2 : d₁.symm 2 = 3 := by decide
    have e3 : d₂.symm 0 = 2 := by decide
    have e4 : d₂.symm 1 = 3 := by decide
    have k01 : v (emb α h 0) = v (emb α h 1) := by
      have := r1 0
      rwa [e1] at this
    have k23 : v (emb α h 2) = v (emb α h 3) := by
      have := r1 2
      rwa [e2] at this
    have k02 : v (emb α h 0) = v (emb α h 2) := by
      have := r2 0
      rwa [e3] at this
    have k13 : v (emb α h 1) = v (emb α h 3) := by
      have := r2 1
      rwa [e4] at this
    have hall : ∀ i : Fin 4, v (emb α h i) = v (emb α h 0) := by
      intro i
      fin_cases i
      · rfl
      · exact k01.symm
      · exact k02.symm
      · exact k23.symm.trans k02.symm
    intro i hi j hj
    obtain ⟨i', rfl⟩ := e16m_range_of_mem (h := h) hi
    obtain ⟨j', rfl⟩ := e16m_range_of_mem (h := h) hj
    exact (hall i').trans (hall j').symm
  · intro hv x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [e16m_comm_iff]
    left
    funext y
    show v y + v (a.perm.symm y) = 0
    by_cases hy : y ∈ Set.range (emb α h)
    · obtain ⟨i, rfl⟩ := hy
      have hm : a.perm.symm (emb α h i) ∈ Set.range (emb α h) :=
        (supportedOn_of_mem_memAt ha).perm_mem (Set.mem_range_self i)
      rw [hv _ (e16m_mem_of_range (Set.mem_range_self i)) _ (e16m_mem_of_range hm),
        Wr.zmod_two_add_self]
    · rw [SupportedOn.perm_symm (supportedOn_of_mem_memAt ha) hy, Wr.zmod_two_add_self]

theorem eq_vec_of_comm_vectors (hn : 5 ≤ n) {x : AEQ n}
    (hx : ∀ f : Fin n → ZMod 2, ∑ i, f i = 0 → x * mkQ n (Wr.ofVec f) = mkQ n (Wr.ofVec f) * x) :
    ∃ v : Fin n → ZMod 2, x = mkQ n (Wr.ofVec v) := by
  obtain ⟨⟨w, σ⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hfix : ∀ i, σ i = i := by
    intro i
    obtain ⟨j, hj⟩ := e16m_exists_notMem ({i, σ i} : Finset (Fin n)) (by
      have := Finset.card_le_two (a := i) (b := σ i)
      omega)
    have hji : j ≠ i := fun e => hj (by simp [e])
    have hjσ : j ≠ σ i := fun e => hj (by simp [e])
    let f : Fin n → ZMod 2 := fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)
    have hsum : ∑ k, f k = 0 := by
      simp only [f, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      decide
    have hc := (e16m_comm_iff f ⟨w, σ⟩).mp (hx f hsum).symm
    obtain ⟨x₀, hx₀⟩ := e16m_exists_notMem ({i, j, σ i, σ j} : Finset (Fin n)) (by
      have := Finset.card_le_four (a := i) (b := j) (c := σ i) (d := σ j)
      omega)
    have hx₀' : x₀ ≠ i ∧ x₀ ≠ j ∧ x₀ ≠ σ i ∧ x₀ ≠ σ j := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx₀
      exact hx₀
    have hu0 : ∀ y, f y + f (σ.symm y) = 0 := by
      rcases hc with h0 | h1
      · intro y
        exact congrFun h0 y
      · exfalso
        have h1x := congrFun h1 x₀
        have hs1 : σ.symm x₀ ≠ i := fun e => hx₀'.2.2.1 (by rw [← e, Equiv.apply_symm_apply])
        have hs2 : σ.symm x₀ ≠ j := fun e => hx₀'.2.2.2 (by rw [← e, Equiv.apply_symm_apply])
        have f0 : f x₀ = 0 := by simp [f, hx₀'.1, hx₀'.2.1]
        have f1 : f (σ.symm x₀) = 0 := by simp [f, hs1, hs2]
        simp only [f0, f1] at h1x
        exact absurd h1x (by decide)
    by_contra hne
    have h1 : f (σ i) = 0 := by simp [f, hne, hjσ.symm]
    have h2 : f (σ.symm (σ i)) = 1 := by simp [f, hji.symm]
    have := hu0 (σ i)
    rw [h1, h2] at this
    exact absurd this (by decide)
  have hperm : σ = 1 := Equiv.ext hfix
  subst hperm
  exact ⟨w, rfl⟩

theorem const_eq_of_syntheme {p₁ p₂ : Finset (Fin 6)} (h₁ : p₁.card = 2) (h₂ : p₂.card = 2)
    (hd : Disjoint p₁ p₂) (v : Fin 6 → ZMod 2) (hv₁ : ∀ i ∈ p₁ᶜ, ∀ j ∈ p₁ᶜ, v i = v j)
    (hv₂ : ∀ i ∈ p₂ᶜ, ∀ j ∈ p₂ᶜ, v i = v j) : v = 0 ∨ v = fun _ => 1 := by
  have hcard : (p₁ ∪ p₂).card = 4 := by
    rw [Finset.card_union_of_disjoint hd, h₁, h₂]
  obtain ⟨m, hm⟩ := e16m_exists_notMem (p₁ ∪ p₂) (by omega)
  have hm1 : m ∉ p₁ := fun h => hm (Finset.mem_union_left _ h)
  have hm2 : m ∉ p₂ := fun h => hm (Finset.mem_union_right _ h)
  have hconst : ∀ i, v i = v m := by
    intro i
    by_cases hi1 : i ∈ p₁
    · by_cases hi2 : i ∈ p₂
      · exact absurd hi2 (Finset.disjoint_left.mp hd hi1)
      · exact hv₂ i (by simpa using hi2) m (by simpa using hm2)
    · exact hv₁ i (by simpa using hi1) m (by simpa using hm1)
  have hvm : v = fun _ => v m := funext hconst
  rcases e16m_zmod2_key (v m) with h0 | h1
  · left
    rw [hvm, h0]
    rfl
  · right
    rw [hvm, h1]

theorem card_vec_const (hn : 4 ≤ n) (γ : Finset (Fin n)) (hγ : γ.card = 4) :
    Nat.card {v : Fin n → ZMod 2 // ∀ i ∈ γ, ∀ j ∈ γ, v i = v j} = 2 ^ (n - 3) := by
  classical
  obtain ⟨g, hg⟩ : γ.Nonempty := Finset.card_pos.mp (by omega)
  let e : {v : Fin n → ZMod 2 // ∀ i ∈ γ, ∀ j ∈ γ, v i = v j} ≃
      ZMod 2 × ({x : Fin n // x ∉ γ} → ZMod 2) :=
    { toFun := fun v => (v.1 g, fun x => v.1 x.1)
      invFun := fun p => ⟨fun x => if hx : x ∈ γ then p.1 else p.2 ⟨x, hx⟩, fun i hi j hj => by
          simp [hi, hj]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ γ
        · simp only [dif_pos hx]
          exact v.2 g hg x hx
        · simp only [dif_neg hx]
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · simp [hg]
        · funext x
          simp [x.2] }
  have hcompl : Nat.card {x : Fin n // x ∉ γ} = n - 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_coe, hγ]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_zmod, hcompl]
  have hn3 : n - 3 = (n - 4) + 1 := by omega
  rw [hn3, pow_succ, mul_comm]

theorem count_weight4 (h : Fin 6 → ZMod 2) :
    (h = 0 ∨ h = fun _ => 1) ∧ (Finset.univ.filter fun α : Finset (Fin 6) =>
        α.card = 4 ∧ ∑ i ∈ α, h i = 0).card = 15 ∨
      (¬ (h = 0 ∨ h = fun _ => 1)) ∧
        ((Finset.univ.filter fun α : Finset (Fin 6) => α.card = 4 ∧ ∑ i ∈ α, h i = 0).card = 5 ∨
          (Finset.univ.filter fun α : Finset (Fin 6) => α.card = 4 ∧ ∑ i ∈ α, h i = 0).card = 7 ∨
          (Finset.univ.filter fun α : Finset (Fin 6) => α.card = 4 ∧ ∑ i ∈ α, h i = 0).card = 9) ∧
        ((Finset.univ.filter fun α : Finset (Fin 6) => α.card = 4 ∧ ∑ i ∈ α, h i = 0).card = 5 →
          ∑ i, h i = 1) := by
  revert h
  decide +kernel

end CFSG.ClassicalInvolution.Q3.AE
