module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section Form

@[expose] def form (u v : Fin n ⊕ Fin n → K) : K := u ⬝ᵥ (gram K n *ᵥ v)

theorem gram_mulVec (v : Fin n ⊕ Fin n → K) :
    gram K n *ᵥ v = fun a => sgn K a * v (par a) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, gram_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (par a)]
  simp

theorem form_apply (u v : Fin n ⊕ Fin n → K) :
    form u v = ∑ a, u a * (sgn K a * v (par a)) := by
  rw [form, gram_mulVec]
  rfl

theorem form_mulVec (x : StatedSp n K) (u v : Fin n ⊕ Fin n → K) :
    form (mat n K x *ᵥ u) (mat n K x *ᵥ v) = form u v := by
  have h := mat_transpose_mul_gram_mul x
  unfold form
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h]

theorem form_antisymm (u v : Fin n ⊕ Fin n → K) : form v u = -form u v := by
  rw [form_apply, form_apply, ← (Equiv.sumComm (Fin n) (Fin n)).sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : (Equiv.sumComm (Fin n) (Fin n)) b = par b := rfl
  have h2 : sgn K (par b) = -sgn K b := by cases b <;> simp
  rw [h1, par_par, h2]
  ring

theorem form_single_right (v : Fin n ⊕ Fin n → K) (b : Fin n ⊕ Fin n) :
    form v (Pi.single b 1) = v (par b) * sgn K (par b) := by
  rw [form_apply, Finset.sum_eq_single (par b)]
  · simp
  · intro a _ ha
    have : par a ≠ b := fun h => ha (by rw [← h, par_par])
    simp [this]
  · simp

theorem form_eq_zero_of_supp {S : Set (Fin n ⊕ Fin n)} (hS : ParClosed S)
    {u v : Fin n ⊕ Fin n → K} (hu : ∀ a ∈ S, u a = 0) (hv : ∀ a ∉ S, v a = 0) :
    form u v = 0 := by
  rw [form_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a ∈ S
  · rw [hu a ha, zero_mul]
  · have : par a ∉ S := fun h => ha (by simpa using hS _ h)
    rw [hv _ this, mul_zero, mul_zero]

theorem mem_fixSpace_longInv_iff_forall_form (h2 : (2 : K) ≠ 0) (k : Fin n)
    {v : Fin n ⊕ Fin n → K} :
    v ∈ fixSpace (longInv K n k) ↔ ∀ u ∈ minusSpace (longInv K n k), form v u = 0 := by
  constructor
  · intro hv u hu
    exact form_eq_zero_of_supp (parClosed_coords k) ((mem_fixSpace_longInv h2 k).1 hv)
      (fun a ha => (mem_minusSpace_longInv h2 k).1 hu a ha)
  · intro h
    rw [mem_fixSpace_longInv h2]
    have hu : ∀ b ∈ coords k, (Pi.single b (1 : K) : Fin n ⊕ Fin n → K) ∈
        minusSpace (longInv K n k) := fun b hb => by
      rw [mem_minusSpace_longInv h2]
      intro u hu
      have : u ≠ b := fun e => hu (e ▸ hb)
      simp [this]
    intro t ht
    have h1 := h _ (hu (par t) (parClosed_coords k t ht))
    rw [form_single_right, par_par] at h1
    exact (mul_eq_zero.1 h1).resolve_right (sgn_ne_zero _)

theorem mulVec_inj (g : StatedSp n K) {a b : Fin n ⊕ Fin n → K}
    (h : mat n K g *ᵥ a = mat n K g *ᵥ b) : a = b :=
  calc a = mat n K g⁻¹ *ᵥ (mat n K g *ᵥ a) := (mulVec_inv_mulVec g a).symm
    _ = mat n K g⁻¹ *ᵥ (mat n K g *ᵥ b) := by rw [h]
    _ = b := mulVec_inv_mulVec g b

theorem mulVec_conj_apply (g c : StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    mat n K (g⁻¹ * c * g) *ᵥ (mat n K g⁻¹ *ᵥ v) = mat n K g⁻¹ *ᵥ (mat n K c *ᵥ v) := by
  have h1 : mat n K g * mat n K g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  simp only [map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, Matrix.mul_one]

end Form

section Geometry

variable {L : Subgroup (StatedSp n K)} {i : StatedSp n K}

theorem IsLongRootSp2.mem_fixSpace_iff (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i)
    {v : Fin n ⊕ Fin n → K} :
    v ∈ fixSpace i ↔ ∀ u ∈ minusSpace i, form v u = 0 := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  rw [mem_fixSpace_conj, mem_fixSpace_longInv_iff_forall_form h2]
  constructor
  · intro hv u hu
    calc form v u = form (mat n K g⁻¹ *ᵥ v) (mat n K g⁻¹ *ᵥ u) := (form_mulVec g⁻¹ v u).symm
      _ = 0 := hv _ (mem_minusSpace_conj.1 hu)
  · intro hv u' hu'
    have hu : mat n K g *ᵥ u' ∈ minusSpace (g * longInv K n k * g⁻¹) :=
      mem_minusSpace_conj.2 (by rwa [mulVec_inv_mulVec])
    calc form (mat n K g⁻¹ *ᵥ v) u'
        = form (mat n K g *ᵥ (mat n K g⁻¹ *ᵥ v)) (mat n K g *ᵥ u') := (form_mulVec g _ _).symm
      _ = form v (mat n K g *ᵥ u') := by rw [mulVec_mulVec_inv]
      _ = 0 := hv _ hu

theorem IsLongRootSp2.mul_self (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) : i * i = 1 := by
  have := pow_orderOf_eq_one i
  rwa [(h.isClassicalSL2 h2).orderOf_eq_two, sq] at this

theorem IsLongRootSp2.eq_of_minusSpace_eq (h2 : (2 : K) ≠ 0) {L₁ L₂ : Subgroup (StatedSp n K)}
    {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁) (h₂ : IsLongRootSp2 L₂ i₂)
    (h : minusSpace i₁ = minusSpace i₂) : i₁ = i₂ := by
  have hfix : fixSpace i₁ = fixSpace i₂ := by
    ext v
    rw [h₁.mem_fixSpace_iff h2, h₂.mem_fixSpace_iff h2, h]
  have hL : L₁ = L₂ := by
    rw [h₁.eq_longRootGroup h2, h₂.eq_longRootGroup h2, longRootGroup, longRootGroup, hfix]
  exact h₁.involution_unique h2 (by rw [hL]; exact h₂)

end Geometry

section Commuting

variable {L : Subgroup (StatedSp n K)} {i : StatedSp n K}

theorem dichotomy_longInv (h2 : (2 : K) ≠ 0) (k : Fin n) {c : StatedSp n K}
    (hc : c * longInv K n k = longInv K n k * c) (hsq : c * c = 1) :
    (∀ v ∈ minusSpace (longInv K n k), mat n K c *ᵥ v = v) ∨
      ∀ v ∈ minusSpace (longInv K n k), mat n K c *ᵥ v = -v := by
  have h := isLongRootSp2_standard (K := K) (n := n) k
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute_longInv h2 k hc
  have hab : Commute a b := h.commute_of_mem_complGroup h2 ha hb
  have h1 : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab.eq]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hsq
  have haa : a * a = 1 := by
    refine Subgroup.disjoint_def.1 (h.disjoint_complGroup h2) (mul_mem ha ha) ?_
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (mul_mem hb hb)
  have ha' : a ∈ (longBlock K n k).range := ha
  obtain ⟨A, rfl⟩ := ha'
  have hAA : A * A = 1 := longBlock_injective k (by rw [map_mul, map_one]; exact haa)
  by_cases hA : A = 1
  · subst hA
    left
    intro v hv
    rw [map_one, one_mul]
    exact hb v hv
  · right
    have hord : orderOf A = 2 := orderOf_eq_prime (by rwa [sq]) hA
    have hA' : A = -1 := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 A).1 hord
    have hAi : longBlock K n k A = longInv K n k := by rw [hA']; rfl
    intro v hv
    rw [hAi, map_mul, ← Matrix.mulVec_mulVec, hb v hv]
    exact mem_minusSpace.1 hv

theorem IsLongRootSp2.dichotomy (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) {c : StatedSp n K}
    (hc : c * i = i * c) (hsq : c * c = 1) :
    (∀ v ∈ minusSpace i, mat n K c *ᵥ v = v) ∨ ∀ v ∈ minusSpace i, mat n K c *ᵥ v = -v := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  have hc' : g⁻¹ * c * g * longInv K n k = longInv K n k * (g⁻¹ * c * g) :=
    Subgroup.mem_centralizer_singleton_iff.1
      (mem_centralizer_conj.1 (Subgroup.mem_centralizer_singleton_iff.2 hc))
  have hsq' : g⁻¹ * c * g * (g⁻¹ * c * g) = 1 := by
    calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [hsq]; group
  rcases dichotomy_longInv h2 k hc' hsq' with h1 | h1
  · left
    intro v hv
    have := h1 _ (mem_minusSpace_conj.1 hv)
    rw [mulVec_conj_apply] at this
    exact mulVec_inj g⁻¹ this
  · right
    intro v hv
    have := h1 _ (mem_minusSpace_conj.1 hv)
    rw [mulVec_conj_apply, ← Matrix.mulVec_neg] at this
    exact mulVec_inj g⁻¹ this

theorem IsLongRootSp2.cases_of_commute (h2 : (2 : K) ≠ 0) {L₁ L₂ : Subgroup (StatedSp n K)}
    {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁) (h₂ : IsLongRootSp2 L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    (∀ v ∈ minusSpace i₂, v ∈ fixSpace i₁) ∨ ∀ v ∈ minusSpace i₁, v ∈ fixSpace i₂ := by
  rcases h₂.dichotomy h2 hc.eq (h₁.mul_self h2) with hA | hA
  · exact Or.inl fun v hv => mem_fixSpace.2 (hA v hv)
  · rcases h₁.dichotomy h2 hc.symm.eq (h₂.mul_self h2) with hB | hB
    · exact Or.inr fun v hv => mem_fixSpace.2 (hB v hv)
    · exfalso
      refine hne (h₁.eq_of_minusSpace_eq h2 h₂ ?_)
      ext v
      exact ⟨fun hv => mem_minusSpace.2 (hB v hv), fun hv => mem_minusSpace.2 (hA v hv)⟩

theorem IsLongRootSp2.form_eq_zero_of_commute (h2 : (2 : K) ≠ 0) {L₁ L₂ : Subgroup (StatedSp n K)}
    {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁) (h₂ : IsLongRootSp2 L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) {u v : Fin n ⊕ Fin n → K} (hu : u ∈ minusSpace i₁)
    (hv : v ∈ minusSpace i₂) : form u v = 0 := by
  rcases h₁.cases_of_commute h2 h₂ hc hne with hA | hB
  · have := (h₁.mem_fixSpace_iff h2).1 (hA v hv) u hu
    rw [← neg_neg (form u v), ← form_antisymm u v, this, neg_zero]
  · exact (h₂.mem_fixSpace_iff h2).1 (hB u hu) v hv

theorem IsLongRootSp2.commute_of_commute (h2 : (2 : K) ≠ 0) {L₁ L₂ : Subgroup (StatedSp n K)}
    {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁) (h₂ : IsLongRootSp2 L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  intro x hx y hy
  rcases h₁.cases_of_commute h2 h₂ hc hne with hA | hB
  · have hxc : x ∈ complGroup i₂ := fun v hv => (h₁.mem_iff h2).1 hx v (hA v hv)
    exact (h₂.commute_of_mem_complGroup h2 hy hxc).symm.eq
  · have hyc : y ∈ complGroup i₁ := fun v hv => (h₂.mem_iff h2).1 hy v (hB v hv)
    exact (h₁.commute_of_mem_complGroup h2 hx hyc).eq

theorem IsLongRootSp2.commute_iff (h2 : (2 : K) ≠ 0) {L₁ L₂ : Subgroup (StatedSp n K)}
    {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁) (h₂ : IsLongRootSp2 L₂ i₂) :
    Commute i₁ i₂ ↔
      i₁ = i₂ ∨ ∀ u ∈ minusSpace i₁, ∀ v ∈ minusSpace i₂, form u v = 0 := by
  constructor
  · intro hc
    by_cases hne : i₁ = i₂
    · exact Or.inl hne
    · exact Or.inr fun u hu v hv => h₁.form_eq_zero_of_commute h2 h₂ hc hne hu hv
  · rintro (rfl | h)
    · exact Commute.refl _
    · have hfix : ∀ v ∈ minusSpace i₂, v ∈ fixSpace i₁ := fun v hv =>
        (h₁.mem_fixSpace_iff h2).2 fun u hu => by
          rw [form_antisymm, h u hu v hv, neg_zero]
      have hmem : i₁ ∈ complGroup i₂ := fun v hv =>
        (h₁.mem_iff h2).1 (h₁.isClassicalSL2 h2).mem v (hfix v hv)
      exact (h₂.commute_of_mem_complGroup h2 (h₂.isClassicalSL2 h2).mem hmem).symm

theorem IsLongRootSp2.commute_iff_minusSpace (h2 : (2 : K) ≠ 0) {L₁ L₂ : Subgroup (StatedSp n K)}
    {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁) (h₂ : IsLongRootSp2 L₂ i₂) :
    Commute i₁ i₂ ↔ minusSpace i₁ = minusSpace i₂ ∨
      ∀ u ∈ minusSpace i₁, ∀ v ∈ minusSpace i₂, form u v = 0 := by
  rw [h₁.commute_iff h2 h₂]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (h₁.eq_of_minusSpace_eq h2 h₂ h)
    · exact Or.inr h

theorem IsLongRootSp2.commute_iff_forall_commute (h2 : (2 : K) ≠ 0)
    {L₁ L₂ : Subgroup (StatedSp n K)} {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁)
    (h₂ : IsLongRootSp2 L₂ i₂) (hne : i₁ ≠ i₂) :
    Commute i₁ i₂ ↔ ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x :=
  ⟨fun hc => h₁.commute_of_commute h2 h₂ hc hne, fun h =>
    h _ (h₁.isClassicalSL2 h2).mem _ (h₂.isClassicalSL2 h2).mem⟩

end Commuting

section Frame

theorem IsLongRootSp2.mem_centralizer_of_commute (h2 : (2 : K) ≠ 0)
    {L₁ L₂ : Subgroup (StatedSp n K)} {i₁ i₂ : StatedSp n K} (h₁ : IsLongRootSp2 L₁ i₁)
    (h₂ : IsLongRootSp2 L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    i₂ ∈ Subgroup.centralizer (L₁ : Set (StatedSp n K)) :=
  Subgroup.mem_centralizer_iff.2 fun x hx =>
    h₁.commute_of_commute h2 h₂ hc hne x hx i₂ (h₂.isClassicalSL2 h2).mem

theorem suppGroup_mono {S T : Set (Fin n ⊕ Fin n)} (h : S ⊆ T) :
    suppGroup S ≤ (suppGroup T : Subgroup (StatedSp n K)) :=
  fun _ hx r t hrt => hx r t fun h' => hrt ⟨h h'.1, h h'.2⟩

theorem coords_subset_compl {k l : Fin n} (hkl : k ≠ l) : coords k ⊆ (coords l)ᶜ := by
  intro a ha hl
  rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 hl with h | h <;>
    first | exact hkl (Sum.inl_injective h) | exact hkl (Sum.inr_injective h) | cases h

theorem commute_longRootSp2 {k l : Fin n} (hkl : k ≠ l) {x y : StatedSp n K}
    (hx : x ∈ longRootSp2 K n k) (hy : y ∈ longRootSp2 K n l) : Commute x y := by
  rw [longRootSp2_eq_suppGroup] at hx hy
  exact (commute_suppGroup_compl hy (suppGroup_mono (coords_subset_compl hkl) hx)).symm

theorem longInv_commute_longRootSp2 (h2 : (2 : K) ≠ 0) (k l : Fin n) {x : StatedSp n K}
    (hx : x ∈ longRootSp2 K n l) : Commute (longInv K n k) x := by
  by_cases hkl : k = l
  · subst hkl
    exact (Subgroup.mem_centralizer_singleton_iff.1
      ((isClassicalSL2_longRootSp2 h2 k).le_centralizer hx) : Commute x (longInv K n k)).symm
  · exact commute_longRootSp2 hkl (longInv_mem_longRootSp2 k) hx

theorem longInv_ne_of_ne (h2 : (2 : K) ≠ 0) {k l : Fin n} (hkl : k ≠ l) :
    longInv K n k ≠ longInv K n l := by
  intro h
  have h1 : (Pi.single (Sum.inl k) (1 : K) : Fin n ⊕ Fin n → K) ∈ minusSpace (longInv K n k) := by
    rw [mem_minusSpace_longInv h2]
    intro u hu
    have : u ≠ Sum.inl k := fun e => hu (e ▸ inl_mem_coords k)
    simp [this]
  have h3 : (Pi.single (Sum.inl k) (1 : K) : Fin n ⊕ Fin n → K) ∈ fixSpace (longInv K n l) := by
    rw [mem_fixSpace_longInv h2]
    intro u hu
    have : u ≠ Sum.inl k := fun e => by
      rw [e] at hu
      exact coords_subset_compl hkl (inl_mem_coords k) hu
    simp [this]
  rw [← h] at h3
  have := congrFun (h3.symm.trans (mem_minusSpace.1 h1)) (Sum.inl k)
  simp at this
  exact h2 (by linear_combination this)

end Frame

end CFSG.ClassicalInvolution.Models.SymplecticPairs
