module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Uniqueness.SU.KI7d

open Equiv Subgroup

variable {G : Type*} [Group G]

theorem comm_of_inverted (Y : Subgroup G) (a : G) (hinv : ∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) :
    ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁ := by
  intro y₁ h₁ y₂ h₂
  have h12 := hinv (y₁ * y₂) (Y.mul_mem h₁ h₂)
  have e1 := hinv y₁ h₁
  have e2 := hinv y₂ h₂
  have : (y₁ * y₂)⁻¹ = y₁⁻¹ * y₂⁻¹ := by
    rw [← h12, ← e1, ← e2]; group
  have h3 : y₂⁻¹ * y₁⁻¹ = y₁⁻¹ * y₂⁻¹ := by rw [← mul_inv_rev]; exact this
  have h4 := congrArg (fun x => x⁻¹) h3
  simp only [mul_inv_rev, inv_inv] at h4
  exact h4


section PermSection

variable {n : ℕ} (Y : Subgroup (Perm (Fin n)))

def stabY (ω : Fin n) : Subgroup ↥Y := MulAction.stabilizer ↥Y ω

variable {Y}

theorem mem_stabY {ω : Fin n} {y : ↥Y} : y ∈ stabY Y ω ↔ (y : Perm (Fin n)) ω = ω :=
  MulAction.mem_stabilizer_iff.trans Iff.rfl

theorem stabY_smul (hY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁) (ω : Fin n) (y : ↥Y) :
    stabY Y ((y : Perm (Fin n)) ω) = stabY Y ω := by
  ext z
  rw [mem_stabY, mem_stabY]
  have hc : (z : Perm (Fin n)) * y = y * z := hY _ z.2 _ y.2
  have key : ∀ x : Fin n, (z : Perm (Fin n)) ((y : Perm (Fin n)) x) =
      (y : Perm (Fin n)) ((z : Perm (Fin n)) x) := fun x => by
    have := congrArg (fun f : Perm (Fin n) => f x) hc
    simpa [Perm.mul_apply] using this
  constructor
  · intro h
    rw [key] at h
    exact (y : Perm (Fin n)).injective h
  · intro h
    rw [key, h]

theorem stabY_apply (a : Perm (Fin n)) (ha2 : a * a = 1)
    (hinv : ∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) (ω : Fin n) : stabY Y (a ω) = stabY Y ω := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haa : ∀ x : Fin n, a (a x) = x := fun x => by
    have := congrArg (fun f : Perm (Fin n) => f x) ha2
    simpa [Perm.mul_apply] using this
  ext z
  rw [mem_stabY, mem_stabY]
  have h1 : ∀ x : Fin n, a ((z : Perm (Fin n)) (a x)) = (z : Perm (Fin n))⁻¹ x := fun x => by
    have := congrArg (fun f : Perm (Fin n) => f x) (hinv z z.2)
    simpa [Perm.mul_apply, ha] using this
  constructor
  · intro h
    have h2 : (z : Perm (Fin n))⁻¹ ω = ω := by
      rw [← h1 ω, h, haa]
    exact (Perm.inv_eq_iff_eq.mp h2).symm
  · intro h
    have h2 : (z : Perm (Fin n))⁻¹ ω = ω := Perm.inv_eq_iff_eq.mpr h.symm
    have h3 : a ((z : Perm (Fin n)) (a ω)) = ω := by rw [h1 ω]; exact h2
    have h4 := congrArg a h3
    rwa [haa] at h4

theorem iInf_stabY : (⨅ ω : Fin n, stabY Y ω) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_iInf] at hz
  have : (z : Perm (Fin n)) = 1 := by
    refine Equiv.ext fun ω => ?_
    exact mem_stabY.mp (hz ω)
  exact Subgroup.mem_bot.mpr (Subtype.ext this)


open Classical in
noncomputable def stabSet (Y : Subgroup (Perm (Fin n))) : Finset (Subgroup ↥Y) :=
  Finset.univ.image (stabY Y)

theorem stabY_mem_stabSet (ω : Fin n) : stabY Y ω ∈ stabSet Y := by
  classical
  unfold stabSet
  exact Finset.mem_image_of_mem _ (Finset.mem_univ ω)

open Classical in
theorem fiber_card_ge (hY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁) (ω : Fin n) :
    (stabY Y ω).index ≤ (Finset.univ.filter (fun x => stabY Y x = stabY Y ω)).card := by
  have hsub : (MulAction.orbit ↥Y ω) ⊆
      ↑(Finset.univ.filter (fun x => stabY Y x = stabY Y ω)) := by
    rintro _ ⟨y, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact stabY_smul hY ω y
  calc (stabY Y ω).index = (MulAction.orbit ↥Y ω).ncard := MulAction.index_stabilizer ↥Y ω
    _ ≤ _ := by
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rwa [Set.ncard_coe_finset] at this

open Classical in
theorem sum_index_le (hY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁) :
    ∑ S ∈ stabSet Y, S.index ≤ n := by
  have h := Finset.card_eq_sum_card_image (stabY Y) (Finset.univ : Finset (Fin n))
  rw [Finset.card_univ, Fintype.card_fin] at h
  refine le_of_le_of_eq ?_ h.symm
  apply Finset.sum_le_sum
  intro S hS
  obtain ⟨ω, -, rfl⟩ := Finset.mem_image.mp hS
  exact fiber_card_ge hY ω

open Classical in
theorem card_le_prod_index :
    Nat.card ↥Y ≤ ∏ S ∈ stabSet Y, S.index := by
  have hbot : (⨅ S : {S // S ∈ stabSet Y}, (S : Subgroup ↥Y)) = ⊥ := by
    rw [eq_bot_iff, ← iInf_stabY (Y := Y)]
    exact le_iInf fun ω => iInf_le_of_le ⟨stabY Y ω, stabY_mem_stabSet ω⟩ le_rfl
  have h := Subgroup.index_iInf_le (fun S : {S // S ∈ stabSet Y} => (S : Subgroup ↥Y))
  rw [hbot, Subgroup.index_bot] at h
  rwa [Finset.prod_coe_sort (stabSet Y) (fun S => S.index)] at h

end PermSection


section Extract

theorem extract_three {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ x ∈ s, f x = 1 ∨ f x = 3 ∨ f x = 9 ∨ f x = 27)
    (hprod : 27 ≤ ∏ x ∈ s, f x) (hsum : ∑ x ∈ s, f x ≤ 10) :
    ∃ x y z, x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ f x = 3 ∧ f y = 3 ∧ f z = 3 ∧
      ∀ w ∈ s, w ≠ x → w ≠ y → w ≠ z → f w = 1 := by
  set t := s.filter (fun x => f x ≠ 1) with ht
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hprodt : ∏ x ∈ t, f x = ∏ x ∈ s, f x := Finset.prod_filter_ne_one s
  have hsumt : ∑ x ∈ t, f x ≤ 10 :=
    (Finset.sum_le_sum_of_subset hts).trans hsum
  have hft : ∀ x ∈ t, f x = 3 ∨ f x = 9 ∨ f x = 27 := by
    intro x hx
    have hxs := (Finset.mem_filter.mp hx).1
    have hx1 := (Finset.mem_filter.mp hx).2
    rcases hf x hxs with h | h | h | h
    · exact absurd h hx1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hge : ∀ x ∈ t, 3 ≤ f x := fun x hx => by rcases hft x hx with h | h | h <;> omega
  have hcard : 3 * t.card ≤ 10 := by
    have h' : t.card * 3 ≤ ∑ x ∈ t, f x := by
      simpa [smul_eq_mul] using Finset.card_nsmul_le_sum t f 3 hge
    omega
  have hcard' : t.card ≤ 3 := by omega
  rw [← hprodt] at hprod
  have hcases : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 ∨ t.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · rw [Finset.card_eq_zero] at h0
    rw [h0] at hprod
    simp at hprod
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    rw [hx] at hprod hsumt hft
    simp only [Finset.prod_singleton, Finset.sum_singleton] at hprod hsumt
    have := hft x (Finset.mem_singleton_self x)
    omega
  · obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp h2
    rw [hxy'] at hprod hsumt hft
    rw [Finset.prod_pair hxy] at hprod
    rw [Finset.sum_pair hxy] at hsumt
    have hx := hft x (Finset.mem_insert_self _ _)
    have hy := hft y (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hprod hsumt <;>
      omega
  · obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.mp h3
    have hxt : x ∈ t := by rw [hxyz]; simp
    have hyt : y ∈ t := by rw [hxyz]; simp
    have hzt : z ∈ t := by rw [hxyz]; simp
    rw [hxyz] at hsumt
    rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz] at hsumt
    have hx := hft x hxt
    have hy := hft y hyt
    have hz := hft z hzt
    have hx3 : f x = 3 := by rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;>
      rcases hz with h'' | h'' | h'' <;> omega
    have hy3 : f y = 3 := by rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;>
      rcases hz with h'' | h'' | h'' <;> omega
    have hz3 : f z = 3 := by rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;>
      rcases hz with h'' | h'' | h'' <;> omega
    refine ⟨x, y, z, hts hxt, hts hyt, hts hzt, hxy, hxz, hyz, hx3, hy3, hz3, ?_⟩
    intro w hw hwx hwy hwz
    by_contra hw1
    have hwt : w ∈ t := Finset.mem_filter.mpr ⟨hw, hw1⟩
    rw [hxyz] at hwt
    simp at hwt
    rcases hwt with h | h | h <;> contradiction

end Extract


section Triple

variable {n : ℕ} {Y : Subgroup (Perm (Fin n))}

theorem normal_of_comm (hY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁) (S : Subgroup ↥Y) :
    S.Normal := by
  refine ⟨fun m hm g => ?_⟩
  have h : g * m * g⁻¹ = m := by
    apply Subtype.ext
    have h1 := hY (g : Perm (Fin n)) g.2 (m : Perm (Fin n)) m.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1]; group
  rw [h]; exact hm

open Classical in
theorem fiber_triple (hY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁) {S : Subgroup ↥Y}
    (hS : S.index = 3) {ω₀ : Fin n} (h₀ : stabY Y ω₀ = S)
    (hcard : (Finset.univ.filter (fun ω => stabY Y ω = S)).card < 6) :
    ∃ y : ↥Y, y ∉ S ∧ Finset.univ.filter (fun ω => stabY Y ω = S) =
        {ω₀, (y : Perm (Fin n)) ω₀, (y : Perm (Fin n)) ((y : Perm (Fin n)) ω₀)} ∧
      (y : Perm (Fin n)) ω₀ ≠ ω₀ ∧ (y : Perm (Fin n)) ((y : Perm (Fin n)) ω₀) ≠ ω₀ ∧
      (y : Perm (Fin n)) ((y : Perm (Fin n)) ((y : Perm (Fin n)) ω₀)) = ω₀ := by
  classical
  have hS1 : S ≠ ⊤ := fun h => by rw [h, Subgroup.index_top] at hS; omega
  obtain ⟨y, hy⟩ : ∃ y : ↥Y, y ∉ S := by
    by_contra h
    push Not at h
    exact hS1 (eq_top_iff.mpr fun x _ => h x)
  have hSn : S.Normal := normal_of_comm hY S
  have hy3 : y ^ 3 ∈ S := by
    have := Subgroup.pow_index_mem S y
    rwa [hS] at this
  have hy2 : y ^ 2 ∉ S := by
    intro h2
    apply hy
    have : y = y ^ 3 * (y ^ 2)⁻¹ := by group
    rw [this]
    exact S.mul_mem hy3 (S.inv_mem h2)
  set A := Finset.univ.filter (fun ω => stabY Y ω = S) with hA
  have hmemA : ∀ ω, ω ∈ A ↔ stabY Y ω = S := fun ω => by simp [hA]
  have hyA : ∀ ω ∈ A, (y : Perm (Fin n)) ω ∈ A := fun ω hω => by
    rw [hmemA] at hω ⊢
    rw [stabY_smul hY ω y, hω]
  have hne1 : ∀ ω ∈ A, (y : Perm (Fin n)) ω ≠ ω := fun ω hω h => by
    rw [hmemA] at hω
    exact hy (hω ▸ mem_stabY.mpr h)
  have hne2 : ∀ ω ∈ A, (y : Perm (Fin n)) ((y : Perm (Fin n)) ω) ≠ ω := fun ω hω h => by
    rw [hmemA] at hω
    apply hy2
    rw [← hω]
    refine mem_stabY.mpr ?_
    simpa [pow_two] using h
  have heq3 : ∀ ω ∈ A, (y : Perm (Fin n)) ((y : Perm (Fin n)) ((y : Perm (Fin n)) ω)) = ω :=
    fun ω hω => by
      rw [hmemA] at hω
      have := mem_stabY.mp (hω ▸ hy3 : y ^ 3 ∈ stabY Y ω)
      simpa [pow_succ, Perm.mul_apply] using this
  set t : Fin n → Finset (Fin n) := fun ω =>
    {ω, (y : Perm (Fin n)) ω, (y : Perm (Fin n)) ((y : Perm (Fin n)) ω)} with ht
  have htA : ∀ ω ∈ A, t ω ⊆ A := fun ω hω => by
    intro x hx
    simp only [ht, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hω
    · exact hyA _ hω
    · exact hyA _ (hyA _ hω)
  have htcard : ∀ ω ∈ A, (t ω).card = 3 := fun ω hω => by
    have h1 := hne1 ω hω
    have h2 := hne2 ω hω
    have h3 : (y : Perm (Fin n)) ((y : Perm (Fin n)) ω) ≠ (y : Perm (Fin n)) ω := fun h =>
      h1 ((y : Perm (Fin n)).injective h)
    simp only [ht]
    rw [Finset.card_insert_of_notMem, Finset.card_pair h3.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
  have htt : ∀ ω ∈ A, ∀ x ∈ t ω, t x = t ω := fun ω hω x hx => by
    simp only [ht, Finset.mem_insert, Finset.mem_singleton] at hx
    have h3 := heq3 ω hω
    rcases hx with rfl | rfl | rfl
    · rfl
    · simp only [ht, h3]
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · simp only [ht]
      have : (y : Perm (Fin n)) ((y : Perm (Fin n)) ((y : Perm (Fin n)) ((y : Perm (Fin n)) ω)))
          = (y : Perm (Fin n)) ω := by rw [h3]
      rw [this, h3]
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  have hω₀A : ω₀ ∈ A := (hmemA ω₀).mpr h₀
  refine ⟨y, hy, ?_, hne1 ω₀ hω₀A, hne2 ω₀ hω₀A, heq3 ω₀ hω₀A⟩
  refine (Finset.eq_of_subset_of_card_le (htA ω₀ hω₀A) ?_).symm
  by_contra hlt
  push Not at hlt
  rw [htcard ω₀ hω₀A] at hlt
  obtain ⟨ω', hω'A, hω'⟩ : ∃ ω' ∈ A, ω' ∉ t ω₀ := by
    by_contra hh
    push Not at hh
    have hsub' : A ⊆ t ω₀ := hh
    have := Finset.card_le_card hsub'
    rw [htcard ω₀ hω₀A] at this
    omega
  have hdisj : Disjoint (t ω₀) (t ω') := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    apply hω'
    have e1 := htt ω₀ hω₀A x hx1
    have e2 := htt ω' hω'A x hx2
    have hω'mem : ω' ∈ t ω' := by simp [ht]
    rw [← e2, e1] at hω'mem
    exact hω'mem
  have hsub : t ω₀ ∪ t ω' ⊆ A := Finset.union_subset (htA ω₀ hω₀A) (htA ω' hω'A)
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, htcard ω₀ hω₀A, htcard ω' hω'A] at this
  omega

end Triple


section SwapTriple

theorem swap_on_triple {n : ℕ} (y a : Perm (Fin n)) (ω₀ : Fin n)
    (h1 : y ω₀ ≠ ω₀) (h2 : y (y ω₀) ≠ ω₀) (h3 : y (y (y ω₀)) = ω₀)
    (hay : a * y * a⁻¹ = y⁻¹) (haO : a ω₀ = ω₀ ∨ a ω₀ = y ω₀ ∨ a ω₀ = y (y ω₀)) :
    ∃ p q : Fin n, p ≠ q ∧ (p = ω₀ ∨ p = y ω₀ ∨ p = y (y ω₀)) ∧
      (q = ω₀ ∨ q = y ω₀ ∨ q = y (y ω₀)) ∧ a ω₀ = swap p q ω₀ ∧
      a (y ω₀) = swap p q (y ω₀) ∧ a (y (y ω₀)) = swap p q (y (y ω₀)) := by
  have hay' : ∀ x : Fin n, a (y x) = y⁻¹ (a x) := fun x => by
    have : a * y = y⁻¹ * a := mul_inv_eq_iff_eq_mul.mp hay
    simpa [Perm.mul_apply] using congrArg (fun f : Perm (Fin n) => f x) this
  have hinv0 : y⁻¹ ω₀ = y (y ω₀) := Perm.inv_eq_iff_eq.mpr h3.symm
  have hinv1 : y⁻¹ (y ω₀) = ω₀ := by simp
  have hinv2 : y⁻¹ (y (y ω₀)) = y ω₀ := by simp
  have d01 : y ω₀ ≠ y (y ω₀) := fun h => h1 (y.injective h).symm
  have d02 : ω₀ ≠ y (y ω₀) := fun h => h2 h.symm
  have d10 : y ω₀ ≠ ω₀ := h1
  rcases haO with h | h | h
  ·
    refine ⟨y ω₀, y (y ω₀), d01, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), ?_, ?_, ?_⟩
    · rw [h, swap_apply_of_ne_of_ne d10.symm d02]
    · have : a (y ω₀) = y (y ω₀) := by rw [hay', h, hinv0]
      rw [this, swap_apply_left]
    · have e1 : a (y ω₀) = y (y ω₀) := by rw [hay', h, hinv0]
      have : a (y (y ω₀)) = y ω₀ := by rw [hay', e1, hinv2]
      rw [this, swap_apply_right]
  ·
    refine ⟨ω₀, y ω₀, d10.symm, Or.inl rfl, Or.inr (Or.inl rfl), ?_, ?_, ?_⟩
    · rw [h, swap_apply_left]
    · have : a (y ω₀) = ω₀ := by rw [hay', h, hinv1]
      rw [this, swap_apply_right]
    · have e1 : a (y ω₀) = ω₀ := by rw [hay', h, hinv1]
      have : a (y (y ω₀)) = y (y ω₀) := by rw [hay', e1, hinv0]
      rw [this, swap_apply_of_ne_of_ne h2 d01.symm]
  ·
    refine ⟨ω₀, y (y ω₀), d02, Or.inl rfl, Or.inr (Or.inr rfl), ?_, ?_, ?_⟩
    · rw [h, swap_apply_left]
    · have : a (y ω₀) = y ω₀ := by rw [hay', h, hinv2]
      rw [this, swap_apply_of_ne_of_ne d10 d01]
    · have e1 : a (y ω₀) = y ω₀ := by rw [hay', h, hinv2]
      have : a (y (y ω₀)) = ω₀ := by rw [hay', e1, hinv1]
      rw [this, swap_apply_right]

end SwapTriple


section OrbitData

variable {n : ℕ} {Y : Subgroup (Perm (Fin n))}

open Classical in
noncomputable def fib (Y : Subgroup (Perm (Fin n))) (S : Subgroup ↥Y) : Finset (Fin n) :=
  Finset.univ.filter (fun ω => stabY Y ω = S)

theorem mem_fib {S : Subgroup ↥Y} {ω : Fin n} : ω ∈ fib Y S ↔ stabY Y ω = S := by
  classical
  simp [fib]

theorem orbit_data (hY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁) (a : Perm (Fin n))
    (ha2 : a * a = 1) (hinv : ∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) {S : Subgroup ↥Y} (hS : S.index = 3)
    {ω₀ : Fin n} (h₀ : stabY Y ω₀ = S) (hcard : (fib Y S).card < 6) :
    (fib Y S).card = 3 ∧ ∃ p q : Fin n, p ≠ q ∧ p ∈ fib Y S ∧ q ∈ fib Y S ∧
      ∀ ω ∈ fib Y S, a ω = swap p q ω := by
  classical
  obtain ⟨y, hyS, hfib, h1, h2, h3⟩ := fiber_triple hY hS h₀ (by simpa [fib] using hcard)
  have hfib' : fib Y S =
      {ω₀, (y : Perm (Fin n)) ω₀, (y : Perm (Fin n)) ((y : Perm (Fin n)) ω₀)} := by
    simpa [fib] using hfib
  have hω₀ : ω₀ ∈ fib Y S := mem_fib.mpr h₀
  have hay : a * (y : Perm (Fin n)) * a⁻¹ = (y : Perm (Fin n))⁻¹ := hinv y y.2
  have haO : a ω₀ = ω₀ ∨ a ω₀ = (y : Perm (Fin n)) ω₀ ∨
      a ω₀ = (y : Perm (Fin n)) ((y : Perm (Fin n)) ω₀) := by
    have : a ω₀ ∈ fib Y S := by rw [mem_fib, stabY_apply a ha2 hinv ω₀, h₀]
    rw [hfib'] at this
    simpa using this
  obtain ⟨p, q, hpq, hp, hq, e0, e1, e2⟩ := swap_on_triple (y : Perm (Fin n)) a ω₀ h1 h2 h3 hay haO
  have hpA : p ∈ fib Y S := by rw [hfib']; simpa using hp
  have hqA : q ∈ fib Y S := by rw [hfib']; simpa using hq
  refine ⟨?_, p, q, hpq, hpA, hqA, ?_⟩
  · rw [hfib']
    have d1 : (y : Perm (Fin n)) ((y : Perm (Fin n)) ω₀) ≠ (y : Perm (Fin n)) ω₀ := fun h =>
      h1 ((y : Perm (Fin n)).injective h)
    rw [Finset.card_insert_of_notMem, Finset.card_pair d1.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
  · intro ω hω
    rw [hfib'] at hω
    simp only [Finset.mem_insert, Finset.mem_singleton] at hω
    rcases hω with rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2

end OrbitData


section Main

open Classical in
theorem no_inverted_subgroup_card_27 {n : ℕ} (hn : n = 9 ∨ n = 10)
    (Y : Subgroup (Perm (Fin n))) (hcard : Nat.card Y = 27)
    (a : Perm (Fin n)) (ha2 : a * a = 1) (ha : Perm.sign a = 1)
    (hinv : ∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) : False := by
  have hn10 : n ≤ 10 := by omega
  have hY := comm_of_inverted Y a hinv
  have haa : ∀ x : Fin n, a (a x) = x := fun x => by
    have := congrArg (fun f : Perm (Fin n) => f x) ha2
    simpa [Perm.mul_apply] using this
  have hdvd : ∀ S ∈ stabSet Y, S.index = 1 ∨ S.index = 3 ∨ S.index = 9 ∨ S.index = 27 := by
    intro S _
    have h27 : S.index ∣ 3 ^ 3 := by
      have := Subgroup.index_dvd_card S
      rw [hcard] at this
      simpa using this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h27
    interval_cases k <;> simp_all
  have hprod : 27 ≤ ∏ S ∈ stabSet Y, S.index := by
    have := card_le_prod_index (Y := Y)
    rwa [hcard] at this
  have hsum : ∑ S ∈ stabSet Y, S.index ≤ 10 := (sum_index_le hY).trans hn10
  obtain ⟨S₁, S₂, S₃, hS₁, hS₂, hS₃, h12, h13, h23, i₁, i₂, i₃, hrest⟩ :=
    extract_three (stabSet Y) (fun S => S.index) hdvd hprod hsum
  have hptS : ∀ S ∈ stabSet Y, ∃ ω, stabY Y ω = S := fun S hS => by
    obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hS
    exact ⟨ω, hω⟩
  obtain ⟨ω₁, hω₁⟩ := hptS S₁ hS₁
  obtain ⟨ω₂, hω₂⟩ := hptS S₂ hS₂
  obtain ⟨ω₃, hω₃⟩ := hptS S₃ hS₃
  have hge : ∀ (S : Subgroup ↥Y) (ω : Fin n), stabY Y ω = S → S.index = 3 → 3 ≤ (fib Y S).card :=
    fun S ω hω hi => by
      have := fiber_card_ge hY ω
      rw [hω] at this
      simpa [fib, hi] using this
  have g₁ := hge S₁ ω₁ hω₁ i₁
  have g₂ := hge S₂ ω₂ hω₂ i₂
  have g₃ := hge S₃ ω₃ hω₃ i₃
  have dis : ∀ {S T : Subgroup ↥Y}, S ≠ T → Disjoint (fib Y S) (fib Y T) := fun {S T} hST => by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hST ((mem_fib.mp hx).symm.trans (mem_fib.mp hx'))
  have hsum3 : (fib Y S₁).card + (fib Y S₂).card + (fib Y S₃).card ≤ n := by
    have hd12 := dis h12
    have hd123 : Disjoint (fib Y S₁ ∪ fib Y S₂) (fib Y S₃) := by
      rw [Finset.disjoint_union_left]
      exact ⟨dis h13, dis h23⟩
    have := Finset.card_le_univ (fib Y S₁ ∪ fib Y S₂ ∪ fib Y S₃)
    rw [Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12,
      Fintype.card_fin] at this
    exact this
  obtain ⟨c₁, p₁, q₁, hpq₁, hp₁, hq₁, hsw₁⟩ := orbit_data hY a ha2 hinv i₁ hω₁ (by omega)
  obtain ⟨c₂, p₂, q₂, hpq₂, hp₂, hq₂, hsw₂⟩ := orbit_data hY a ha2 hinv i₂ hω₂ (by omega)
  obtain ⟨c₃, p₃, q₃, hpq₃, hp₃, hq₃, hsw₃⟩ := orbit_data hY a ha2 hinv i₃ hω₃ (by omega)
  have hpres : ∀ (S : Subgroup ↥Y) (ω : Fin n), ω ∈ fib Y S → a ω ∈ fib Y S := fun S ω hω => by
    rw [mem_fib] at hω ⊢
    rw [stabY_apply a ha2 hinv ω, hω]
  have hrem : ∀ ω : Fin n, ω ∉ fib Y S₁ → ω ∉ fib Y S₂ → ω ∉ fib Y S₃ → a ω = ω := by
    intro ω h1 h2 h3
    set R : Finset (Fin n) := Finset.univ \ (fib Y S₁ ∪ fib Y S₂ ∪ fib Y S₃) with hR
    have hd12 := dis h12
    have hd123 : Disjoint (fib Y S₁ ∪ fib Y S₂) (fib Y S₃) := by
      rw [Finset.disjoint_union_left]
      exact ⟨dis h13, dis h23⟩
    have hRcard : R.card ≤ 1 := by
      rw [hR, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12]
      omega
    have hωR : ω ∈ R := by simp [hR, h1, h2, h3]
    have haR : a ω ∈ R := by
      simp only [hR, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
      refine ⟨⟨fun h => h1 ?_, fun h => h2 ?_⟩, fun h => h3 ?_⟩
      · have := hpres S₁ _ h; rwa [haa] at this
      · have := hpres S₂ _ h; rwa [haa] at this
      · have := hpres S₃ _ h; rwa [haa] at this
    exact (Finset.card_le_one.mp hRcard _ haR _ hωR)
  have nm : ∀ {S T : Subgroup ↥Y} {x : Fin n}, S ≠ T → x ∈ fib Y S → x ∉ fib Y T :=
    fun {S T x} hST hx hx' => Finset.disjoint_left.mp (dis hST) hx hx'
  have hdec : a = swap p₁ q₁ * swap p₂ q₂ * swap p₃ q₃ := by
    refine Equiv.ext fun ω => ?_
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hω1 : ω ∈ fib Y S₁
    · have a2 : ω ≠ p₂ := fun h => nm h12 hω1 (h ▸ hp₂)
      have b2 : ω ≠ q₂ := fun h => nm h12 hω1 (h ▸ hq₂)
      have a3 : ω ≠ p₃ := fun h => nm h13 hω1 (h ▸ hp₃)
      have b3 : ω ≠ q₃ := fun h => nm h13 hω1 (h ▸ hq₃)
      rw [swap_apply_of_ne_of_ne a3 b3, swap_apply_of_ne_of_ne a2 b2, ← hsw₁ ω hω1]
    by_cases hω2 : ω ∈ fib Y S₂
    · have a3 : ω ≠ p₃ := fun h => nm h23 hω2 (h ▸ hp₃)
      have b3 : ω ≠ q₃ := fun h => nm h23 hω2 (h ▸ hq₃)
      have hu : swap p₂ q₂ ω ∈ fib Y S₂ := hsw₂ ω hω2 ▸ hpres S₂ ω hω2
      have a1 : swap p₂ q₂ ω ≠ p₁ := fun h => nm (Ne.symm h12) hu (h ▸ hp₁)
      have b1 : swap p₂ q₂ ω ≠ q₁ := fun h => nm (Ne.symm h12) hu (h ▸ hq₁)
      rw [swap_apply_of_ne_of_ne a3 b3, swap_apply_of_ne_of_ne a1 b1, ← hsw₂ ω hω2]
    by_cases hω3 : ω ∈ fib Y S₃
    · have hu : swap p₃ q₃ ω ∈ fib Y S₃ := hsw₃ ω hω3 ▸ hpres S₃ ω hω3
      have a1 : swap p₃ q₃ ω ≠ p₁ := fun h => nm (Ne.symm h13) hu (h ▸ hp₁)
      have b1 : swap p₃ q₃ ω ≠ q₁ := fun h => nm (Ne.symm h13) hu (h ▸ hq₁)
      have a2 : swap p₃ q₃ ω ≠ p₂ := fun h => nm (Ne.symm h23) hu (h ▸ hp₂)
      have b2 : swap p₃ q₃ ω ≠ q₂ := fun h => nm (Ne.symm h23) hu (h ▸ hq₂)
      rw [swap_apply_of_ne_of_ne a2 b2, swap_apply_of_ne_of_ne a1 b1, ← hsw₃ ω hω3]
    · have a1 : ω ≠ p₁ := fun h => hω1 (h ▸ hp₁)
      have b1 : ω ≠ q₁ := fun h => hω1 (h ▸ hq₁)
      have a2 : ω ≠ p₂ := fun h => hω2 (h ▸ hp₂)
      have b2 : ω ≠ q₂ := fun h => hω2 (h ▸ hq₂)
      have a3 : ω ≠ p₃ := fun h => hω3 (h ▸ hp₃)
      have b3 : ω ≠ q₃ := fun h => hω3 (h ▸ hq₃)
      rw [swap_apply_of_ne_of_ne a3 b3, swap_apply_of_ne_of_ne a2 b2,
        swap_apply_of_ne_of_ne a1 b1, hrem ω hω1 hω2 hω3]
  have hsign : Perm.sign a = -1 := by
    rw [hdec, map_mul, map_mul, Perm.sign_swap hpq₁, Perm.sign_swap hpq₂, Perm.sign_swap hpq₃]
    decide
  rw [hsign] at ha
  exact absurd ha (by decide)

end Main


section Bound

open Classical in
theorem perm_bound {n : ℕ} (hn : n = 9 ∨ n = 10) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Y : Subgroup (Perm (Fin n))) (hY : IsPGroup p Y)
    (a : Perm (Fin n)) (ha2 : a * a = 1) (ha : Perm.sign a = 1)
    (hinv : ∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) :
    Nat.card Y ∣ 5 ^ (if n = 9 then 1 else 2) ∨ Nat.card Y ∣ 7 ∨ Nat.card Y ∣ 9 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hdvd : p ^ k ∣ n.factorial := by
    have h1 := Subgroup.card_subgroup_dvd_card Y
    rw [hk, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1
  by_cases hk0 : k = 0
  · right; left
    rw [hk, hk0]; simp
  have hpn : p ≤ n := (Nat.Prime.dvd_factorial hp).mp (dvd_trans (dvd_pow_self p hk0) hdvd)
  have hp10 : p ≤ 10 := by omega
  have hp3 : p = 3 ∨ p = 5 ∨ p = 7 := by
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)
  rcases hn with rfl | rfl
  · rcases hp3 with rfl | rfl | rfl
    ·
      right; right
      by_cases hk3 : k ≤ 2
      · rw [hk]
        interval_cases k <;> norm_num
      · exfalso
        have h27 : 3 ^ 3 ∣ Nat.card Y := by
          rw [hk]; exact pow_dvd_pow 3 (by omega)
        obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
        refine no_inverted_subgroup_card_27 (Or.inl rfl) (K.map Y.subtype) ?_ a ha2 ha ?_
        · rw [Subgroup.card_map_of_injective Y.subtype_injective, hK]; norm_num
        · rintro _ ⟨y, -, rfl⟩
          exact hinv y y.2
    ·
      left
      have hk1 : k ≤ 1 := by
        by_contra h
        have : 5 ^ 2 ∣ Nat.factorial 9 := dvd_trans (pow_dvd_pow 5 (by omega)) hdvd
        revert this; norm_num [Nat.factorial]
      rw [hk]
      interval_cases k <;> simp
    ·
      right; left
      have hk1 : k ≤ 1 := by
        by_contra h
        have : 7 ^ 2 ∣ Nat.factorial 9 := dvd_trans (pow_dvd_pow 7 (by omega)) hdvd
        revert this; norm_num [Nat.factorial]
      rw [hk]
      interval_cases k <;> simp
  · rcases hp3 with rfl | rfl | rfl
    · right; right
      by_cases hk3 : k ≤ 2
      · rw [hk]
        interval_cases k <;> norm_num
      · exfalso
        have h27 : 3 ^ 3 ∣ Nat.card Y := by
          rw [hk]; exact pow_dvd_pow 3 (by omega)
        obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
        refine no_inverted_subgroup_card_27 (Or.inr rfl) (K.map Y.subtype) ?_ a ha2 ha ?_
        · rw [Subgroup.card_map_of_injective Y.subtype_injective, hK]; norm_num
        · rintro _ ⟨y, -, rfl⟩
          exact hinv y y.2
    · left
      have hk1 : k ≤ 2 := by
        by_contra h
        have : 5 ^ 3 ∣ Nat.factorial 10 := dvd_trans (pow_dvd_pow 5 (by omega)) hdvd
        revert this; norm_num [Nat.factorial]
      rw [hk]
      interval_cases k <;> simp
    · right; left
      have hk1 : k ≤ 1 := by
        by_contra h
        have : 7 ^ 2 ∣ Nat.factorial 10 := dvd_trans (pow_dvd_pow 7 (by omega)) hdvd
        revert this; norm_num [Nat.factorial]
      rw [hk]
      interval_cases k <;> simp

end Bound


end CFSG.GH74.Uniqueness.SU.KI7d
