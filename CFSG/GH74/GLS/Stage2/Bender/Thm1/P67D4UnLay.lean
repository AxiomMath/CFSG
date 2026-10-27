module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPol

public section

open scoped Pointwise

namespace CFSG.GH74.BNPair

namespace RankTwoSystem

variable {X : Type*} [Group X] (D : RankTwoSystem X 3)

section Aux

private theorem intList_one_three' : intList 1 ((3 : ℕ) : ℤ) = [1, 2, 3] := by decide

private def oppConj (τ : X ≃* X) (w : X) : X ≃* X := τ.trans (MulAut.conj w⁻¹)

private theorem oppConj_apply (τ : X ≃* X) (w x : X) : oppConj τ w x = w⁻¹ * τ x * w := by
  simp [oppConj]

private theorem theta_eq (τ : X ≃* X) (w g x : X) :
    τ.trans (MulAut.conj g) x = (g * w) * oppConj τ w x * (g * w)⁻¹ := by
  rw [oppConj_apply]
  simp only [MulEquiv.trans_apply, MulAut.conj_apply]
  group

private theorem w₀_eq_mul : D.w₀ = D.w₁ * D.w₂ * D.w₁ := by
  simp only [w₀, altWord, one_mul]

private theorem w₀_inv_eq : D.w₀⁻¹ = D.w₀ := by
  have h1 : D.w₁⁻¹ = D.w₁ := inv_eq_of_mul_eq_one_right D.w₁_mul_self
  have h2 : D.w₂⁻¹ = D.w₂ := inv_eq_of_mul_eq_one_right D.w₂_mul_self
  rw [w₀_eq_mul, mul_inv_rev, mul_inv_rev, h1, h2, mul_assoc]

variable {D}

private theorem mk_inv_w₀ {w : D.N} (hw : (w : D.Weyl) = D.w₀) :
    ((w⁻¹ : D.N) : D.Weyl) = D.w₀ := by
  rw [QuotientGroup.mk_inv, hw, D.w₀_inv_eq]

private theorem oppConj_root {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {k q : ℤ} (hk : IsRoot 3 k) (hq : Rt 3 q = -k) {x : X}
    (hx : x ∈ D.root k) : oppConj τ (w : X) x ∈ D.root (Rt 3 (tauA 3 3 q)) := by
  have h1 : τ x ∈ D.root (Rt 3 q) := by
    rw [hq]
    exact hτ.mem_root k hk x hx
  have h2 := actsPos_altWord₁ (D := D) 3 (w⁻¹) (mk_inv_w₀ hw) q _ h1
  rw [oppConj_apply]
  simpa using h2

private theorem oppConj_root₁ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.root 1) :
    oppConj τ (w : X) x ∈ D.root 3 := by
  have h := oppConj_root hτ hw (k := 1) (q := 3) ⟨by norm_num, by norm_num⟩ (by decide) hx
  rwa [show Rt 3 (tauA 3 3 3) = 3 by decide] at h

private theorem oppConj_root₂ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.root 2) :
    oppConj τ (w : X) x ∈ D.root 2 := by
  have h := oppConj_root hτ hw (k := 2) (q := 4) ⟨by norm_num, by norm_num⟩ (by decide) hx
  rwa [show Rt 3 (tauA 3 3 4) = 2 by decide] at h

private theorem oppConj_root₃ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.root 3) :
    oppConj τ (w : X) x ∈ D.root 1 := by
  have h := oppConj_root hτ hw (k := 3) (q := 5) ⟨by norm_num, by norm_num⟩ (by decide) hx
  rwa [show Rt 3 (tauA 3 3 5) = 1 by decide] at h

variable (D)

private theorem exists_decomp {u : X} (hu : u ∈ D.U) :
    ∃ a ∈ D.root 1, ∃ b ∈ D.root 2, ∃ c ∈ D.root 3, u = a * (b * c) := by
  have hu' : u ∈ chainProd D.root (intList 1 ((3 : ℕ) : ℤ)) := by
    rw [← D.roots.carrier_eq]
    exact hu
  rw [intList_one_three', chainProd_cons, chainProd_cons, chainProd_singleton] at hu'
  obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.1 hu'
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.1 hy
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

private theorem mem_root₂_of_mem_mul {z : X} (h₁₂ : z ∈ (D.root 1 : Set X) * D.root 2)
    (h₂₃ : z ∈ (D.root 2 : Set X) * D.root 3) : z ∈ D.root 2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 h₁₂
  obtain ⟨c, hc, d, hd, e⟩ := Set.mem_mul.1 h₂₃
  replace ha : a ∈ D.root 1 := ha
  replace hb : b ∈ D.root 2 := hb
  replace hc : c ∈ D.root 2 := hc
  replace hd : d ∈ D.root 3 := hd
  have key := D.roots.unique (fun k => if k = 1 then a else if k = 2 then b else 1)
    (fun k => if k = 1 then 1 else if k = 2 then c else d) ?_ ?_ ?_ 1
    (by rw [intList_one_three']; decide)
  · have h1 : a = 1 := by simpa using key
    rw [h1, one_mul]
    exact hb
  · intro k hk
    rw [intList_one_three'] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp [ha, hb]
  · intro k hk
    rw [intList_one_three'] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp [hc, hd]
  · rw [intList_one_three']
    simp
    exact e.symm

private theorem exists_layers : ∃ V₁ V₂ : Subgroup X,
    (V₁ : Set X) = (D.root 1 : Set X) * D.root 2 ∧ (V₁ : Set X) = (D.root 2 : Set X) * D.root 1 ∧
    (V₂ : Set X) = (D.root 2 : Set X) * D.root 3 ∧
    (∀ b ∈ D.B, ∀ y ∈ V₁, b * y * b⁻¹ ∈ V₁) ∧ (∀ b ∈ D.B, ∀ y ∈ V₂, b * y * b⁻¹ ∈ V₂) ∧
    D.root 1 ≤ V₁ ∧ D.root 2 ≤ V₁ ∧ D.root 2 ≤ V₂ ∧ D.root 3 ≤ V₂ ∧
    ∀ z, z ∈ V₁ → z ∈ V₂ → z ∈ D.root 2 := by
  obtain ⟨V₁, hV₁c, -, -, hV₁n⟩ :=
    D.roots.subgroup 1 (((3 : ℕ) : ℤ) - 1) le_rfl (by norm_num) (by norm_num)
  obtain ⟨V₂, hV₂c, -, hV₂n, -⟩ :=
    D.roots.subgroup 2 ((3 : ℕ) : ℤ) (by norm_num) (by norm_num) le_rfl
  have h₁ : (V₁ : Set X) = (D.root 1 : Set X) * D.root 2 := by
    rw [hV₁c, show intList 1 (((3 : ℕ) : ℤ) - 1) = [1, 2] by decide, chainProd_cons,
      chainProd_singleton]
  have h₂ : (V₂ : Set X) = (D.root 2 : Set X) * D.root 3 := by
    rw [hV₂c, show intList 2 ((3 : ℕ) : ℤ) = [2, 3] by decide, chainProd_cons,
      chainProd_singleton]
  have h₁' : (V₁ : Set X) = (D.root 2 : Set X) * D.root 1 := by
    have := D.roots.reverse_eq 1 2 le_rfl (by norm_num) (by norm_num)
    rw [show intList 1 2 = [1, 2] by decide] at this
    have h21 : chainProd D.root (([1, 2] : List ℤ).reverse) = (D.root 2 : Set X) * D.root 1 := by
      show chainProd D.root [2, 1] = _
      rw [chainProd_cons, chainProd_singleton]
    rw [h₁, ← h21, ← this, chainProd_cons, chainProd_singleton]
  refine ⟨V₁, V₂, h₁, h₁', h₂, D.B_normalizes_V₂ hV₁c (hV₁n (by norm_num)),
    D.B_normalizes_V₁ hV₂c (hV₂n (by norm_num)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← SetLike.mem_coe, h₁]
    exact Set.mem_mul.2 ⟨x, hx, 1, (D.root 2).one_mem, mul_one x⟩
  · intro x hx
    rw [← SetLike.mem_coe, h₁]
    exact Set.mem_mul.2 ⟨1, (D.root 1).one_mem, x, hx, one_mul x⟩
  · intro x hx
    rw [← SetLike.mem_coe, h₂]
    exact Set.mem_mul.2 ⟨x, hx, 1, (D.root 3).one_mem, mul_one x⟩
  · intro x hx
    rw [← SetLike.mem_coe, h₂]
    exact Set.mem_mul.2 ⟨1, (D.root 2).one_mem, x, hx, one_mul x⟩
  · intro z hz₁ hz₂
    rw [← SetLike.mem_coe, h₁] at hz₁
    rw [← SetLike.mem_coe, h₂] at hz₂
    exact D.mem_root₂_of_mem_mul hz₁ hz₂

private theorem cross_mem_root₂ {a c : X} (ha : a ∈ D.root 1) (hc : c ∈ D.root 3) :
    a * c * a⁻¹ * c⁻¹ ∈ D.root 2 := by
  obtain ⟨V₁, V₂, -, -, -, n₁, n₂, l₁₁, -, -, l₃₂, inter⟩ := D.exists_layers
  have haB : a ∈ D.B := D.root_le_B (by norm_num) (by norm_num) ha
  have hcB : c ∈ D.B := D.root_le_B (by norm_num) (by norm_num) hc
  refine inter _ ?_ ?_
  · have h1 : c * a⁻¹ * c⁻¹ ∈ V₁ := n₁ c hcB _ (V₁.inv_mem (l₁₁ ha))
    have := V₁.mul_mem (l₁₁ ha) h1
    simpa only [mul_assoc] using this
  · have h1 : a * c * a⁻¹ ∈ V₂ := n₂ a haB c (l₃₂ hc)
    exact V₂.mul_mem h1 (V₂.inv_mem (l₃₂ hc))

private theorem conj_mem_root₂_aux {u y : X} (hu : u ∈ D.U) (hy : y ∈ D.root 2) :
    u * y * u⁻¹ ∈ D.root 2 := by
  obtain ⟨V₁, V₂, -, -, -, n₁, n₂, -, l₂₁, l₂₂, -, inter⟩ := D.exists_layers
  have huB : u ∈ D.B := D.U_le_B hu
  exact inter _ (n₁ u huB y (l₂₁ hy)) (n₂ u huB y (l₂₂ hy))

private theorem comm_iff_of_group {Q : Type*} [Group Q] (a b : Q) :
    a * b * a⁻¹ * b⁻¹ = 1 ↔ a * b = b * a :=
  commutatorElement_eq_one_iff_mul_comm

private theorem mk_mul_comm_iff {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ N ↔ (x : G ⧸ N) * y = y * x := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
  exact comm_iff_of_group _ _

private theorem mul_comm_four {G : Type*} [Group G] {a c a' c' : G} (h₁₁ : a * a' = a' * a)
    (h₃₃ : c * c' = c' * c) (h₁₃ : a * c' = c' * a) (h₃₁ : c * a' = a' * c) :
    a * c * (a' * c') = a' * c' * (a * c) := by
  calc a * c * (a' * c') = a * (c * a') * c' := by group
    _ = a * (a' * c) * c' := by rw [h₃₁]
    _ = (a * a') * (c * c') := by group
    _ = (a' * a) * (c' * c) := by rw [h₁₁, h₃₃]
    _ = a' * (a * c') * c := by group
    _ = a' * (c' * a) * c := by rw [h₁₃]
    _ = a' * c' * (a * c) := by group

end Aux

theorem commutator_mem_root₂ (h₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (h₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a) {u v : X} (hu : u ∈ D.U)
    (hv : v ∈ D.U) : u * v * u⁻¹ * v⁻¹ ∈ D.root 2 := by
  have hN : ((D.root 2).subgroupOf D.U).Normal :=
    (Subgroup.normal_subgroupOf_iff (D.root_le_U (by norm_num) (by norm_num))).2
      fun y g hy hg => D.conj_mem_root₂_aux hg hy
  have hcomm_of : ∀ (x y : X) (hx : x ∈ D.U) (hy : y ∈ D.U), x * y * x⁻¹ * y⁻¹ ∈ D.root 2 →
      ((⟨x, hx⟩ : D.U) : D.U ⧸ (D.root 2).subgroupOf D.U) * (⟨y, hy⟩ : D.U) =
        (⟨y, hy⟩ : D.U) * (⟨x, hx⟩ : D.U) :=
    fun x y hx hy h => (mk_mul_comm_iff _ ⟨x, hx⟩ ⟨y, hy⟩).1 (Subgroup.mem_subgroupOf.2 h)
  have key : ∀ x y : D.U,
      (x : D.U ⧸ (D.root 2).subgroupOf D.U) * (y : D.U) = (y : D.U) * (x : D.U) := by
    intro x y
    obtain ⟨a, ha, b, hb, c, hc, hx⟩ := D.exists_decomp x.2
    obtain ⟨a', ha', b', hb', c', hc', hy⟩ := D.exists_decomp y.2
    have haU : a ∈ D.U := D.root_le_U (by norm_num) (by norm_num) ha
    have hbU : b ∈ D.U := D.root_le_U (by norm_num) (by norm_num) hb
    have hcU : c ∈ D.U := D.root_le_U (by norm_num) (by norm_num) hc
    have haU' : a' ∈ D.U := D.root_le_U (by norm_num) (by norm_num) ha'
    have hbU' : b' ∈ D.U := D.root_le_U (by norm_num) (by norm_num) hb'
    have hcU' : c' ∈ D.U := D.root_le_U (by norm_num) (by norm_num) hc'
    have ex : x = ⟨a, haU⟩ * (⟨b, hbU⟩ * ⟨c, hcU⟩) := Subtype.ext hx
    have ey : y = ⟨a', haU'⟩ * (⟨b', hbU'⟩ * ⟨c', hcU'⟩) := Subtype.ext hy
    have hb1 : ((⟨b, hbU⟩ : D.U) : D.U ⧸ (D.root 2).subgroupOf D.U) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hb)
    have hb1' : ((⟨b', hbU'⟩ : D.U) : D.U ⧸ (D.root 2).subgroupOf D.U) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hb')
    rw [ex, ey, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, hb1, hb1', one_mul, one_mul]
    refine mul_comm_four ?_ ?_ ?_ ?_
    · refine hcomm_of a a' haU haU' ?_
      rw [h₁ a ha a' ha']
      simp
    · refine hcomm_of c c' hcU hcU' ?_
      rw [h₃ c hc c' hc']
      simp
    · exact hcomm_of a c' haU hcU' (D.cross_mem_root₂ ha hc')
    · exact (hcomm_of a' c haU' hcU (D.cross_mem_root₂ ha' hc)).symm
  exact Subgroup.mem_subgroupOf.1
    ((mk_mul_comm_iff ((D.root 2).subgroupOf D.U) ⟨u, hu⟩ ⟨v, hv⟩).2 (key ⟨u, hu⟩ ⟨v, hv⟩))

theorem conj_root₂_mem {u y : X} (hu : u ∈ D.U) (hy : y ∈ D.root 2) :
    u * y * u⁻¹ ∈ D.root 2 :=
  D.conj_mem_root₂_aux hu hy

variable {D}

theorem IsOpposition.theta_root₁ {τ : X ≃* X} (hτ : D.IsOpposition τ) {g : X}
    (hg : g * ((D.lift D.w₀ : D.N) : X) ∈ D.B) {y : X} (hy : y ∈ D.root 1) :
    ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, τ.trans (MulAut.conj g) y = b * z := by
  obtain ⟨_, V₂, -, -, h₂c, -, n₂, -, -, -, l₃₂, -⟩ := D.exists_layers
  have hz := oppConj_root₁ hτ (D.lift_mk D.w₀) hy
  have hmem : τ.trans (MulAut.conj g) y ∈ V₂ := by
    rw [theta_eq]
    exact n₂ _ hg _ (l₃₂ hz)
  rw [← SetLike.mem_coe, h₂c] at hmem
  obtain ⟨b, hb, z, hz', e⟩ := Set.mem_mul.1 hmem
  exact ⟨b, hb, z, hz', e.symm⟩

theorem IsOpposition.theta_root₃ {τ : X ≃* X} (hτ : D.IsOpposition τ) {g : X}
    (hg : g * ((D.lift D.w₀ : D.N) : X) ∈ D.B) {z : X} (hz : z ∈ D.root 3) :
    ∃ b ∈ D.root 2, ∃ y ∈ D.root 1, τ.trans (MulAut.conj g) z = b * y := by
  obtain ⟨V₁, _, -, h₁c, -, n₁, -, l₁₁, -, -, -, -⟩ := D.exists_layers
  have hy := oppConj_root₃ hτ (D.lift_mk D.w₀) hz
  have hmem : τ.trans (MulAut.conj g) z ∈ V₁ := by
    rw [theta_eq]
    exact n₁ _ hg _ (l₁₁ hy)
  rw [← SetLike.mem_coe, h₁c] at hmem
  obtain ⟨b, hb, y, hy', e⟩ := Set.mem_mul.1 hmem
  exact ⟨b, hb, y, hy', e.symm⟩

theorem IsOpposition.theta_root₂ {τ : X ≃* X} (hτ : D.IsOpposition τ) {g : X}
    (hg : g * ((D.lift D.w₀ : D.N) : X) ∈ D.B) {b : X} (hb : b ∈ D.root 2) :
    τ.trans (MulAut.conj g) b ∈ D.root 2 := by
  obtain ⟨V₁, V₂, -, -, -, n₁, n₂, -, l₂₁, l₂₂, -, inter⟩ := D.exists_layers
  have hb' := oppConj_root₂ hτ (D.lift_mk D.w₀) hb
  rw [theta_eq]
  exact inter _ (n₁ _ hg _ (l₂₁ hb')) (n₂ _ hg _ (l₂₂ hb'))

theorem IsOpposition.theta_sq [Finite X] {τ : X ≃* X} (hτ : D.IsOpposition τ) {e : X ≃* X}
    (hτe : ∀ y, τ (τ y) = e y) (he : ∀ b ∈ D.B, e b ∈ D.B) {g : X}
    (hg : g * ((D.lift D.w₀ : D.N) : X) ∈ D.B) :
    ∃ b₂ ∈ D.B, ∀ y, τ.trans (MulAut.conj g) (τ.trans (MulAut.conj g) y) = b₂ * e y * b₂⁻¹ := by
  have hsq : ∀ y, τ.trans (MulAut.conj g) (τ.trans (MulAut.conj g) y) =
      (g * τ g) * e y * (g * τ g)⁻¹ := by
    intro y
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv, hτe]
    group
  refine ⟨g * τ g, ?_, hsq⟩
  have hθ : ∀ b ∈ D.B, τ.trans (MulAut.conj g) b ∈ D.B := (hτ.isPolarity hg).mem_B
  have hN : Subgroup.normalizer (D.B : Set X) = D.B := by
    have h := D.isTits.normalizer_parabolic (J := ∅) (Finset.empty_subset _)
    simpa only [Finset.coe_empty, parabolic_empty] using h
  have he_surj : ∀ b ∈ D.B, ∃ b' ∈ D.B, e b' = b := by
    let f : D.B → D.B := fun b => ⟨e b, he b b.2⟩
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (e.injective (congrArg Subtype.val h))
    intro b hb
    obtain ⟨b', hb'⟩ := Finite.surjective_of_injective hf ⟨b, hb⟩
    exact ⟨b', b'.2, congrArg Subtype.val hb'⟩
  have hconj : ∀ b ∈ D.B, (g * τ g) * b * (g * τ g)⁻¹ ∈ D.B := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := he_surj b hb
    rw [← hsq]
    exact hθ _ (hθ _ hb')
  have hmem : g * τ g ∈ Subgroup.normalizer (D.B : Set X) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨hconj h, fun hh => ?_⟩
    let c : D.B → D.B := fun b => ⟨(g * τ g) * b * (g * τ g)⁻¹, hconj b b.2⟩
    have hc : Function.Injective c := fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [c, mul_left_inj, mul_right_inj] at h'
      exact Subtype.ext h'
    obtain ⟨b', hb'⟩ := Finite.surjective_of_injective hc ⟨_, hh⟩
    have h' := congrArg Subtype.val hb'
    simp only [c, mul_left_inj, mul_right_inj] at h'
    rw [← h']
    exact b'.2
  rwa [hN] at hmem

end RankTwoSystem

end CFSG.GH74.BNPair
