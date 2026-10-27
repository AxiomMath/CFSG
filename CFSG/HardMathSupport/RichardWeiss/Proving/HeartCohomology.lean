module

public import CFSG.HardMathSupport.RichardWeiss.Proving.PermCohomology
public import CFSG.HardMathSupport.RichardWeiss.Proving.HeartFixed

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  Equiv Equiv.Perm

variable {n : ℕ}

@[expose] def sVec (a : Fin n) : evenWeight n →+ ({x : Fin n // x ≠ a} → ZMod 2) where
  toFun x := fun y => (x : Fin n → ZMod 2) y + (x : Fin n → ZMod 2) a
  map_zero' := by funext y; simp
  map_add' x x' := by
    funext y
    simp only [AddSubgroup.coe_add, Pi.add_apply]
    ring

theorem sVec_eq_zero_of_mem_ones (a : Fin n) {x : evenWeight n} (hx : x ∈ evenWeightOnes n) :
    sVec a x = 0 := by
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
  funext y
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  simp only [sVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hc, Pi.zero_apply]
  exact h2 c

@[expose] noncomputable def sH (a : Fin n) : altHeart n →+ ({x : Fin n // x ≠ a} → ZMod 2) :=
  QuotientAddGroup.lift (evenWeightOnes n) (sVec a) fun _ hx => sVec_eq_zero_of_mem_ones a hx

theorem sH_mk (a : Fin n) (x : evenWeight n) : sH a (x : altHeart n) = sVec a x := rfl

theorem sH_altAct_ofSubtype (a : Fin n) (σ : Perm {x : Fin n // x ≠ a}) (h : altHeart n) :
    sH a (altAct (Perm.ofSubtype σ) h) = vecAct σ (sH a h) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  funext y
  rw [altAct_mk, sH_mk, sH_mk]
  have h1 : ((Perm.ofSubtype σ)⁻¹) (y : Fin n) = (σ.symm y : Fin n) := by
    rw [← map_inv, Perm.ofSubtype_apply_coe]; rfl
  have h2 : ((Perm.ofSubtype σ)⁻¹) a = a := by
    rw [← map_inv]; exact Perm.ofSubtype_apply_of_not_mem _ (by simp)
  simp only [sVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, evenWeightPerm_apply, vecAct_apply, h1,
    h2]

@[expose] def uVec (a : Fin n) (v : {x : Fin n // x ≠ a} → ZMod 2) : Fin n → ZMod 2 :=
  fun y => if h : y = a then ∑ z, v z else v ⟨y, h⟩

theorem uVec_a (a : Fin n) (v : {x : Fin n // x ≠ a} → ZMod 2) : uVec a v a = ∑ z, v z := by
  simp [uVec]

theorem uVec_ne (a : Fin n) (v : {x : Fin n // x ≠ a} → ZMod 2) (z : {x : Fin n // x ≠ a}) :
    uVec a v z = v z := by
  simp [uVec, z.2]

theorem uVec_sum (a : Fin n) (v : {x : Fin n // x ≠ a} → ZMod 2) : ∑ y, uVec a v y = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ a, uVec_a]
  simp only [uVec_ne]
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  exact h2 _

@[expose] def uEW (a : Fin n) (v : {x : Fin n // x ≠ a} → ZMod 2) : evenWeight n :=
  ⟨uVec a v, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    exact uVec_sum a v⟩

theorem uVec_add (a : Fin n) (v w : {x : Fin n // x ≠ a} → ZMod 2) :
    uVec a (v + w) = uVec a v + uVec a w := by
  funext y
  by_cases h : y = a
  · subst h
    simp only [uVec_a, Pi.add_apply, Finset.sum_add_distrib]
  · have hy : (⟨y, h⟩ : {x : Fin n // x ≠ a}) = ⟨y, h⟩ := rfl
    simp only [Pi.add_apply, uVec, h, dite_false]

theorem uEW_zero (a : Fin n) : uEW a 0 = 0 := by
  apply Subtype.ext
  funext y
  by_cases h : y = a
  · subst h; simp [uEW, uVec]
  · simp [uEW, uVec, h]

theorem uEW_add (a : Fin n) (v w : {x : Fin n // x ≠ a} → ZMod 2) :
    uEW a (v + w) = uEW a v + uEW a w := Subtype.ext (uVec_add a v w)

@[expose] noncomputable def iHom (a : Fin n) :
    ({x : Fin n // x ≠ a} → ZMod 2) →+ altHeart n where
  toFun v := ((uEW a v : evenWeight n) : altHeart n)
  map_zero' := by rw [uEW_zero]; rfl
  map_add' v w := by rw [uEW_add]; rfl

theorem altAct_iHom (a : Fin n) (σ : Perm {x : Fin n // x ≠ a})
    (v : {x : Fin n // x ≠ a} → ZMod 2) :
    altAct (Perm.ofSubtype σ) (iHom a v) = iHom a (vecAct σ v) := by
  show altAct _ ((uEW a v : evenWeight n) : altHeart n) = ((uEW a (vecAct σ v) : evenWeight n) :
    altHeart n)
  rw [altAct_mk]
  congr 1
  apply Subtype.ext
  funext y
  rw [evenWeightPerm_apply]
  by_cases hy : y = a
  · subst hy
    have h2 : ((Perm.ofSubtype σ)⁻¹) y = y := by
      rw [← map_inv]; exact Perm.ofSubtype_apply_of_not_mem _ (by simp)
    show uVec y v (((Perm.ofSubtype σ)⁻¹) y) = uVec y (vecAct σ v) y
    rw [h2, uVec_a, uVec_a]
    exact (Equiv.sum_comp σ.symm v).symm
  · have h1 : ((Perm.ofSubtype σ)⁻¹) y = (σ.symm ⟨y, hy⟩ : Fin n) := by
      rw [← map_inv]
      exact Perm.ofSubtype_apply_coe (σ⁻¹) ⟨y, hy⟩
    show uVec a v (((Perm.ofSubtype σ)⁻¹) y) = uVec a (vecAct σ v) y
    rw [h1]
    have := uVec_ne a v (σ.symm ⟨y, hy⟩)
    rw [this]
    have := uVec_ne a (vecAct σ v) ⟨y, hy⟩
    rw [this]
    rfl

theorem card_subtype_ne_cast (hev : Even n) (a : Fin n) :
    ((Fintype.card {x : Fin n // x ≠ a} : ℕ) : ZMod 2) = 1 := by
  have h := Fintype.card_subtype_compl (fun x : Fin n => x = a)
  have hc : Fintype.card {x : Fin n // x = a} = 1 := Fintype.card_subtype_eq a
  have hn : Fintype.card {x : Fin n // x ≠ a} + 1 = n := by
    have := Fintype.card_subtype_compl (fun x : Fin n => x = a)
    simp only [hc, Fintype.card_fin] at this
    have hpos : 0 < n := Fin.pos a
    simp only [ne_eq] at this ⊢
    omega
  obtain ⟨k, hk⟩ := hev
  have h2 : ((Fintype.card {x : Fin n // x ≠ a} : ℕ) : ZMod 2) + 1 = 0 := by
    have : ((Fintype.card {x : Fin n // x ≠ a} + 1 : ℕ) : ZMod 2) = 0 := by
      rw [hn, hk]; push_cast; exact CharTwo.add_self_eq_zero _
    simpa using this
  have h3 : ∀ c : ZMod 2, c + 1 = 0 → c = 1 := by decide
  exact h3 _ h2

theorem iHom_sH (hev : Even n) (a : Fin n) (h : altHeart n) : iHom a (sH a h) = h := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
  rw [sH_mk]
  show ((uEW a (sVec a x) : evenWeight n) : altHeart n) = (x : altHeart n)
  rw [QuotientAddGroup.eq]
  apply mem_evenWeightOnes_of_forall_eq (c := (x : Fin n → ZMod 2) a)
  intro i
  have hx : ∑ y, (x : Fin n → ZMod 2) y = 0 := by
    have := x.2
    simpa [evenWeight] using this
  have hcard := card_subtype_ne_cast hev a
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne (fun y => (x : Fin n → ZMod 2) y) a
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  by_cases hi : i = a
  · subst hi
    have hsum : ∑ z : {y : Fin n // y ≠ i}, ((sVec i x) z) = 0 := by
      simp only [sVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      rw [hx] at hsplit
      have h3 : ∀ p q : ZMod 2, 0 = p + q → q + p * 1 = 0 := by decide
      have := h3 _ _ hsplit
      simpa [add_comm] using this
    show -(uVec i (sVec i x) i) + (x : Fin n → ZMod 2) i = (x : Fin n → ZMod 2) i
    rw [uVec_a, hsum]
    have h6 : ∀ c : ZMod 2, -(0 : ZMod 2) + c = c := by decide
    exact h6 _
  · show -(uVec a (sVec a x) i) + (x : Fin n → ZMod 2) i = (x : Fin n → ZMod 2) a
    have := uVec_ne a (sVec a x) ⟨i, hi⟩
    show -(uVec a (sVec a x) i) + (x : Fin n → ZMod 2) i = _
    have h4 : uVec a (sVec a x) i = (x : Fin n → ZMod 2) i + (x : Fin n → ZMod 2) a := this
    rw [h4]
    have h5 : ∀ p q : ZMod 2, -(p + q) + p = q := by decide
    exact h5 _ _

theorem cocycle_heart_stab (hn : 4 ≤ n) (hev : Even n) (a : Fin n)
    (f : alternatingGroup (Fin n) → altHeart n)
    (hf : ∀ g h, f (g * h) = f g + altAct (g : Perm (Fin n)) (f h)) :
    ∃ w : altHeart n, ∀ g : alternatingGroup (Fin n), (g : Perm (Fin n)) a = a →
      f g = altAct (g : Perm (Fin n)) w - w := by
  classical
  have hmem : ∀ σ : alternatingGroup {x : Fin n // x ≠ a},
      Perm.ofSubtype (σ : Perm {x : Fin n // x ≠ a}) ∈ alternatingGroup (Fin n) := fun σ =>
    mem_alternatingGroup.2 (by rw [Perm.sign_ofSubtype]; exact mem_alternatingGroup.1 σ.2)
  let gσ : alternatingGroup {x : Fin n // x ≠ a} → alternatingGroup (Fin n) := fun σ =>
    ⟨Perm.ofSubtype (σ : Perm {x : Fin n // x ≠ a}), hmem σ⟩
  let F : alternatingGroup {x : Fin n // x ≠ a} → ({x : Fin n // x ≠ a} → ZMod 2) :=
    fun σ => sH a (f (gσ σ))
  have hF : ∀ σ τ, F (σ * τ) = F σ + vecAct (σ : Perm {x : Fin n // x ≠ a}) (F τ) := by
    intro σ τ
    have hm : gσ (σ * τ) = gσ σ * gσ τ := Subtype.ext (map_mul _ _ _)
    show sH a (f (gσ (σ * τ))) = sH a (f (gσ σ)) + vecAct _ (sH a (f (gσ τ)))
    rw [hm, hf, map_add]
    congr 1
    exact sH_altAct_ofSubtype a _ _
  have hcard : 3 ≤ Fintype.card {x : Fin n // x ≠ a} := by
    have h := Fintype.card_subtype_compl (fun x : Fin n => x = a)
    have hc : Fintype.card {x : Fin n // x = a} = 1 := Fintype.card_subtype_eq a
    simp only [hc, Fintype.card_fin] at h
    simp only [ne_eq]
    omega
  obtain ⟨p', hp'⟩ := cocycle_vec_coboundary hcard F hF
  refine ⟨iHom a p', ?_⟩
  intro g hga
  have h₁ : ∀ x : Fin n, (fun y => y ≠ a) ((g : Perm (Fin n)) x) ↔ (fun y => y ≠ a) x := by
    intro x
    constructor
    · intro h hx; apply h; rw [hx, hga]
    · intro h hx; apply h; apply (g : Perm (Fin n)).injective; rw [hx, hga]
  have h₂ : ∀ x : Fin n, (g : Perm (Fin n)) x ≠ x → (fun y => y ≠ a) x := by
    intro x hx hxa; apply hx; rw [hxa, hga]
  let σ0 : Perm {x : Fin n // x ≠ a} := (g : Perm (Fin n)).subtypePerm (p := fun y => y ≠ a) h₁
  have hsign : Perm.sign σ0 = 1 := by
    rw [Perm.sign_subtypePerm _ h₁ h₂]; exact mem_alternatingGroup.1 g.2
  have hσ0 : σ0 ∈ alternatingGroup {x : Fin n // x ≠ a} := mem_alternatingGroup.2 hsign
  have hg : gσ ⟨σ0, hσ0⟩ = g := Subtype.ext (Perm.ofSubtype_subtypePerm h₁ h₂)
  have e := hp' ⟨σ0, hσ0⟩
  have e2 : f g = iHom a (F ⟨σ0, hσ0⟩) := by
    show f g = iHom a (sH a (f (gσ ⟨σ0, hσ0⟩)))
    rw [hg, iHom_sH hev]
  rw [e2, e, map_sub, ← altAct_iHom]
  have : (Perm.ofSubtype σ0) = (g : Perm (Fin n)) := Perm.ofSubtype_subtypePerm h₁ h₂
  rw [this]

theorem altHeart_add_comm (a b : altHeart n) : a + b = b + a := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm]

section Decomp

noncomputable instance altHeartAddCommGroup : AddCommGroup (altHeart n) :=
  { (inferInstance : AddGroup (altHeart n)) with
    add_comm := fun x y => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm] }

open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem exists_notMem_fin (s : Finset (Fin n)) (h : s.card < n) : ∃ k, k ∉ s := by
  obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
    (by simpa using h)
  exact ⟨e, he⟩

theorem pairEW_self_altHeart (k : Fin n) : (pairEW k k : altHeart n) = 0 := by
  have h : pairEW k k = 0 := Subtype.ext <| funext fun p => by
    rw [pairEW_apply]
    have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
    exact h2 _
  rw [h, QuotientAddGroup.mk_zero]

theorem altAct_pairEW (g : Perm (Fin n)) (a j : Fin n) :
    altAct g (pairEW a j : altHeart n) = (pairEW (g a) (g j) : altHeart n) := by
  rw [altAct_mk, evenWeightPerm_pairEW]

theorem exists_alt_stab_apply (hn : 4 ≤ n) {a j k : Fin n} (hj : j ≠ a) (hk : k ≠ a) :
    ∃ g : alternatingGroup (Fin n), (g : Perm (Fin n)) a = a ∧ (g : Perm (Fin n)) j = k := by
  classical
  by_cases hjk : j = k
  · exact ⟨1, rfl, by simp [hjk]⟩
  · obtain ⟨c, hc⟩ := exists_notMem_fin ({a, j, k} : Finset (Fin n))
      (lt_of_le_of_lt (Finset.card_le_three) (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨hca, hcj, hck⟩ := hc
    refine ⟨⟨swap j k * swap k c, ?_⟩, ?_, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hjk, Perm.sign_swap (Ne.symm hck)]
      decide
    · change (swap j k) ((swap k c) a) = a
      rw [swap_apply_of_ne_of_ne (Ne.symm hk) (fun h => hca h.symm),
        swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hk)]
    · change (swap j k) ((swap k c) j) = k
      rw [swap_apply_of_ne_of_ne hjk (fun h => hcj h.symm), swap_apply_left]

theorem cocycle_heart_decomp (hn : 6 ≤ n) (hev : Even n) (a : Fin n)
    (f : alternatingGroup (Fin n) → altHeart n)
    (hf : ∀ g h, f (g * h) = f g + altAct (g : Perm (Fin n)) (f h)) :
    ∃ (w : altHeart n) (β : Bool), ∀ g : alternatingGroup (Fin n),
      f g = (if β then (pairEW ((g : Perm (Fin n)) a) a : altHeart n) else 0) +
        (altAct (g : Perm (Fin n)) w - w) := by
  classical
  have hfixed : ∀ j : Fin n, a ≠ j → ∀ x : altHeart n,
      (∀ σ : Perm (Fin n), σ.IsThreeCycle → (∀ y, σ y ≠ y → y ≠ a ∧ y ≠ j) → altAct σ x = x) →
      ∃ b : Bool, x = if b then (pairEW a j : altHeart n) else 0 := by
    intro j hj x hx
    rcases altHeart_fixed_form hn hev a j hj x hx with h | h
    · exact ⟨false, by simp [h]⟩
    · exact ⟨true, by simp [h]⟩
  obtain ⟨w₁, hw₁⟩ := cocycle_heart_stab (by omega) hev a f hf
  let f' : alternatingGroup (Fin n) → altHeart n := fun g =>
    f g - (altAct (g : Perm (Fin n)) w₁ - w₁)
  have hf' : ∀ g h, f' (g * h) = f' g + altAct (g : Perm (Fin n)) (f' h) := by
    intro g h
    simp only [f']
    rw [hf]
    have hgh : ((g * h : alternatingGroup (Fin n)) : Perm (Fin n)) = (g : Perm (Fin n)) * h := rfl
    rw [hgh, altAct_mul, map_sub, map_sub]
    abel
  have hstab : ∀ g : alternatingGroup (Fin n), (g : Perm (Fin n)) a = a → f' g = 0 := by
    intro g hg
    simp only [f']
    rw [hw₁ g hg, sub_self]
  have hn3 : 3 ≤ Fintype.card (Fin n) := by simpa using (by omega : 3 ≤ n)
  choose r hr using fun i => exists_alt_apply hn3 a i
  let φ : Fin n → altHeart n := fun j => f' (r j)
  have hφa : φ a = 0 := hstab (r a) (hr a)
  have hfg : ∀ g : alternatingGroup (Fin n), f' g = φ ((g : Perm (Fin n)) a) := by
    intro g
    let τ : alternatingGroup (Fin n) := (r ((g : Perm (Fin n)) a))⁻¹ * g
    have hτa : (τ : Perm (Fin n)) a = a := by
      have h := hr ((g : Perm (Fin n)) a)
      change ((r ((g : Perm (Fin n)) a) : Perm (Fin n))⁻¹) ((g : Perm (Fin n)) a) = a
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact h.symm
    have hg : g = r ((g : Perm (Fin n)) a) * τ := by simp [τ]
    have h0 := hstab τ hτa
    conv_lhs => rw [hg, hf', h0]
    simp [φ]
  have hstar : ∀ (g : alternatingGroup (Fin n)) (j : Fin n),
      φ ((g : Perm (Fin n)) j) = φ ((g : Perm (Fin n)) a) + altAct (g : Perm (Fin n)) (φ j) := by
    intro g j
    have h1 := hf' g (r j)
    have h2 := hfg (g * r j)
    have h3 := hfg g
    have hgr : ((g * r j : alternatingGroup (Fin n)) : Perm (Fin n)) a =
        (g : Perm (Fin n)) j := by
      change (g : Perm (Fin n)) ((r j : Perm (Fin n)) a) = _
      rw [hr j]
    rw [hgr] at h2
    rw [← h2, h1, h3]
  have hfixj : ∀ j : Fin n, j ≠ a → ∃ b : Bool, φ j = if b then (pairEW a j : altHeart n) else 0 := by
    intro j hj
    refine hfixed j (Ne.symm hj) (φ j) ?_
    intro σ h3 hs
    have hσa : σ a = a := by
      by_contra h; exact (hs a h).1 rfl
    have hσj : σ j = j := by
      by_contra h; exact (hs j h).2 rfl
    have hmem : σ ∈ alternatingGroup (Fin n) := mem_alternatingGroup.2 h3.sign
    have e := hstar ⟨σ, hmem⟩ j
    have e1 : ((⟨σ, hmem⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) j = j := hσj
    have e2 : ((⟨σ, hmem⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) a = a := hσa
    rw [e1, e2, hφa, zero_add] at e
    exact e.symm
  have hb : ∀ j : Fin n, ∃ b : Bool, j ≠ a →
      φ j = if b then (pairEW a j : altHeart n) else 0 := by
    intro j
    by_cases h : j = a
    · exact ⟨false, fun h' => absurd h h'⟩
    · obtain ⟨b, hb⟩ := hfixj j h
      exact ⟨b, fun _ => hb⟩
  choose b hb using hb
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, j₀ ≠ a := by
    obtain ⟨e, he⟩ := exists_notMem_fin ({a} : Finset (Fin n)) (by simp; omega)
    exact ⟨e, by simpa using he⟩
  have hconst : ∀ j : Fin n, j ≠ a → b j = b j₀ := by
    intro j hj
    obtain ⟨g, hga, hgj⟩ := exists_alt_stab_apply (by omega) hj₀ hj
    have e := hstar g j₀
    rw [hgj, hga, hφa, zero_add, hb j hj, hb j₀ hj₀] at e
    have hne := pairEW_ne_zero_altHeart (by omega : 3 ≤ n) (Ne.symm hj)
    have e' : (if b j then (pairEW a j : altHeart n) else 0) =
        if b j₀ then (pairEW a j : altHeart n) else 0 := by
      rw [e]
      cases hbb : b j₀
      · simp only [Bool.false_eq_true, ite_false, map_zero]
      · simp only [ite_true]
        rw [altAct_pairEW, hga, hgj]
    have key : ∀ (P : altHeart n) (p q : Bool), (if p then P else 0) = (if q then P else 0) →
        P ≠ 0 → p = q := by
      intro P p q h hP
      cases p <;> cases q
      · rfl
      · simp only [Bool.false_eq_true, ite_false, ite_true] at h
        exact absurd h.symm hP
      · simp only [Bool.false_eq_true, ite_false, ite_true] at h
        exact absurd h hP
      · rfl
    exact key _ _ _ e' hne
  refine ⟨w₁, b j₀, fun g => ?_⟩
  have hφ : φ ((g : Perm (Fin n)) a) =
      if b j₀ then (pairEW ((g : Perm (Fin n)) a) a : altHeart n) else 0 := by
    by_cases h : (g : Perm (Fin n)) a = a
    · rw [h, hφa, pairEW_self_altHeart]; simp
    · rw [hb _ h, hconst _ h, pairEW_comm]
  have := hfg g
  rw [hφ] at this
  simp only [f'] at this
  exact sub_eq_iff_eq_add.mp this

end Decomp

end CFSG.HardMathSupport.RichardWeiss.Proving
