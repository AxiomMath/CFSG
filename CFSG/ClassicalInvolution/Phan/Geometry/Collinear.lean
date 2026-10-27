module

public import CFSG.ClassicalInvolution.Phan.Geometry.Count

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

section Collinear

@[expose] def IsCollinear (σ : K ≃+* K) (x y : Submodule K (Fin m → K)) : Prop :=
  x ≠ y ∧ Nondeg σ (x ⊔ y)

theorem IsCollinear.symm {x y : Submodule K (Fin m → K)} (h : IsCollinear σ x y) :
    IsCollinear σ y x :=
  ⟨h.1.symm, by rw [sup_comm]; exact h.2⟩

@[expose] def collGraph (σ : K ≃+* K) (W : Submodule K (Fin m → K)) :
    SimpleGraph ↥(nsPts σ W) where
  Adj x y := IsCollinear σ x.1 y.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {W : Submodule K (Fin m → K)}

theorem inf_eq_bot_of_ne_pts {x y : Submodule K (Fin m → K)} (hx : finrank K x = 1)
    (hy : finrank K y = 1) (hxy : x ≠ y) : x ⊓ y = ⊥ := by
  by_contra h
  have h0 : finrank K ↥(x ⊓ y) ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.mp h0)
  have hle : finrank K ↥(x ⊓ y) ≤ 1 := hx ▸ Submodule.finrank_mono inf_le_left
  have h1 : finrank K ↥(x ⊓ y) = 1 := by omega
  have e1 : x ⊓ y = x := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hx])
  have e2 : x ⊓ y = y := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hy])
  exact hxy (e1.symm.trans e2)

theorem finrank_sup_of_ne_pts {x y : Submodule K (Fin m → K)} (hx : finrank K x = 1)
    (hy : finrank K y = 1) (hxy : x ≠ y) : finrank K ↥(x ⊔ y) = 2 := by
  rw [finrank_sup_of_disjoint (disjoint_iff.mpr (inf_eq_bot_of_ne_pts hx hy hxy)), hx, hy]

section
variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem IsCollinear.of_orth {W W' x y : Submodule K (Fin m → K)} (hx : x ∈ nsPts σ W)
    (hy : y ∈ nsPts σ W') (hxy : Orth σ x y) : IsCollinear σ x y := by
  refine ⟨?_, Nondeg.sup_of_orth hσ hx.2.2 hy.2.2 hxy⟩
  rintro rfl
  obtain ⟨v, hv, -, rfl⟩ := mem_nsPts_iff.mp hx
  exact hv (hxy v (Submodule.mem_span_singleton_self v) v (Submodule.mem_span_singleton_self v))

omit hσ in
theorem isCollinear_of_le_plane {L x y : Submodule K (Fin m → K)} (hL : finrank K L = 2)
    (hnd : Nondeg σ L) (hx : x ∈ pts L) (hy : y ∈ pts L) (hxy : x ≠ y) : IsCollinear σ x y := by
  refine ⟨hxy, ?_⟩
  have h2 := finrank_sup_of_ne_pts hx.2 hy.2 hxy
  have : x ⊔ y = L := Submodule.eq_of_le_of_finrank_eq (sup_le hx.1 hy.1) (by rw [h2, hL])
  rw [this]
  exact hnd

end

end Collinear

section Gram

variable (hσ : IsUnitaryInvolution σ)

include hσ in
theorem isCollinear_span_iff {x₀ y₀ : Fin m → K} (hx : herm σ x₀ x₀ ≠ 0)
    (hy : herm σ y₀ y₀ ≠ 0) :
    IsCollinear σ (K ∙ x₀) (K ∙ y₀) ↔
      herm σ x₀ x₀ * herm σ y₀ y₀ - herm σ x₀ y₀ * herm σ y₀ x₀ ≠ 0 := by
  constructor
  · rintro ⟨hne, hnd⟩
    have hy' : y₀ ∉ K ∙ x₀ := not_mem_span_of_ne hy hne
    have h := (nondeg_span_pair_iff hσ hx hy').mp hnd
    rw [herm_projPerp_projPerp hσ hx] at h
    intro h0
    apply h
    field_simp
    linear_combination h0
  · intro hΔ
    have hy' : y₀ ∉ K ∙ x₀ := by
      rintro hmem
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hmem
      apply hΔ
      simp only [herm_smul_right, herm_smul_left]
      ring
    refine ⟨fun he => hy' (he ▸ Submodule.mem_span_singleton_self y₀), ?_⟩
    refine (nondeg_span_pair_iff hσ hx hy').mpr ?_
    rw [herm_projPerp_projPerp hσ hx]
    intro h0
    apply hΔ
    field_simp at h0
    linear_combination h0

include hσ in
theorem isCollinear_span_congr {x₀ y₀ e₀ : Fin m → K} (hx : herm σ x₀ x₀ ≠ 0)
    (hy : herm σ y₀ y₀ ≠ 0) (he : herm σ e₀ e₀ ≠ 0) (hxe : herm σ x₀ e₀ = herm σ y₀ e₀)
    (hxy : herm σ x₀ x₀ = herm σ y₀ y₀) :
    IsCollinear σ (K ∙ x₀) (K ∙ e₀) ↔ IsCollinear σ (K ∙ y₀) (K ∙ e₀) := by
  rw [isCollinear_span_iff hσ hx he, isCollinear_span_iff hσ hy he,
    herm_conj σ hσ.invol x₀ e₀, herm_conj σ hσ.invol y₀ e₀, hxe, hxy]

end Gram

section LineCount

variable (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)

include hσ hK in
theorem ncard_not_collinear_le_of_not_mem {L : Submodule K (Fin m → K)} (hL : finrank K L = 2)
    (hnd : Nondeg σ L) {a₀ : Fin m → K} (ha₀ : herm σ a₀ a₀ ≠ 0) (haL : a₀ ∉ L) :
    {x | x ∈ nsPts σ L ∧ ¬ Nondeg σ (K ∙ a₀ ⊔ x)}.ncard ≤ q + 1 := by
  set ρ := projPerp σ a₀ with hρ
  set T := L.map ρ with hT
  have hT2 : finrank K ↥T ≤ 2 := (Submodule.finrank_map_le ρ L).trans hL.le
  have hTne : ∃ v ∈ T, herm σ v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hpol : ∀ l ∈ L, ∀ l' ∈ L, herm σ (ρ l) (ρ l') = 0 := fun l hl l' hl' =>
      herm_eq_zero_of_forall_isotropic hσ (S := T) (fun v hv => hcon v hv)
        (Submodule.mem_map_of_mem hl) (Submodule.mem_map_of_mem hl')
    let φ : L →ₗ[K] K := (hermL σ a₀).comp L.subtype
    have hker : LinearMap.ker φ ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by rw [hL, finrank_self]; omega)
    obtain ⟨l₀, hl₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have h0 : herm σ a₀ l₀ = 0 := hl₀
    have h1 : herm σ l₀ a₀ = 0 := (herm_eq_zero_iff hσ _ _).mp h0
    have : (l₀ : Fin m → K) = 0 := by
      refine hnd l₀ l₀.2 fun l' hl' => ?_
      have := hpol l₀ l₀.2 l' hl'
      rw [herm_projPerp_projPerp hσ ha₀, h1, zero_mul, mul_zero, sub_zero] at this
      exact this
    exact hne (Subtype.ext this)
  set bad := {x | x ∈ nsPts σ L ∧ ¬ Nondeg σ (K ∙ a₀ ⊔ x)} with hbad
  have hspan : ∀ v : Fin m → K, Submodule.map ρ (K ∙ v) = K ∙ ρ v := fun v => by
    rw [Submodule.map_span, Set.image_singleton]
  have hnot : ∀ v ∈ L, v ≠ 0 → v ∉ K ∙ a₀ := by
    intro v hvL hv0 hvK
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvK
    have hc : c ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
    exact haL (by simpa [smul_smul, inv_mul_cancel₀ hc] using L.smul_mem c⁻¹ hvL)
  have hmaps : ∀ x ∈ bad, Submodule.map ρ x ∈ isoPts σ T := by
    rintro x ⟨hx, hxnd⟩
    obtain ⟨v, hv, hvL, rfl⟩ := mem_nsPts_iff.mp hx
    have hv0 : v ≠ 0 := fun h => hv (by rw [h]; simp)
    have hvK := hnot v hvL hv0
    have hzero : herm σ (ρ v) (ρ v) = 0 := by
      by_contra h
      exact hxnd ((nondeg_span_pair_iff hσ ha₀ hvK).mpr h)
    rw [hspan]
    exact span_singleton_mem_isoPts (fun h => hvK ((projPerp_eq_zero_iff ha₀).mp h)) hzero
      (Submodule.mem_map_of_mem hvL)
  have hinj : Set.InjOn (Submodule.map ρ) bad := by
    rintro x ⟨hx, -⟩ y ⟨hy, -⟩ hxy
    obtain ⟨v, hv, hvL, rfl⟩ := mem_nsPts_iff.mp hx
    obtain ⟨w, hw, hwL, rfl⟩ := mem_nsPts_iff.mp hy
    have hv0 : v ≠ 0 := fun h => hv (by rw [h]; simp)
    have hw0 : w ≠ 0 := fun h => hw (by rw [h]; simp)
    rw [hspan, hspan] at hxy
    have h1 : ρ w ∈ K ∙ ρ v := by rw [hxy]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    have h2 : ρ (w - c • v) = 0 := by rw [map_sub, map_smul, hc, sub_self]
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp ((projPerp_eq_zero_iff ha₀).mp h2)
    have hd0 : d = 0 := by
      by_contra hd0
      have : d • a₀ ∈ L := by
        rw [hd]
        exact L.sub_mem hwL (L.smul_mem c hvL)
      exact haL (by simpa [smul_smul, inv_mul_cancel₀ hd0] using L.smul_mem d⁻¹ this)
    rw [hd0, zero_smul, eq_comm, sub_eq_zero] at hd
    have hc0 : c ≠ 0 := by rintro rfl; exact hw0 (by rw [hd, zero_smul])
    rw [hd]
    exact (Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) v).symm
  calc bad.ncard ≤ (isoPts σ T).ncard :=
        Set.ncard_le_ncard_of_injOn (Submodule.map ρ) hmaps hinj (Set.toFinite _)
    _ ≤ q + 1 := ncard_isoPts_le hσ hK hT2 hTne

end LineCount

section LineCount2

variable (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)

include hσ hK in
theorem ncard_not_collinear_le {W L a : Submodule K (Fin m → K)} (hL : finrank K L = 2)
    (hnd : Nondeg σ L) (ha : a ∈ nsPts σ W) :
    {x | x ∈ nsPts σ L ∧ ¬ IsCollinear σ a x}.ncard ≤ q + 1 := by
  obtain ⟨a₀, ha₀, -, rfl⟩ := mem_nsPts_iff.mp ha
  by_cases haL : a₀ ∈ L
  · have hapt : K ∙ a₀ ∈ pts L :=
      span_singleton_mem_pts (fun h => ha₀ (by rw [h]; simp)) haL
    have hsub : {x | x ∈ nsPts σ L ∧ ¬ IsCollinear σ (K ∙ a₀) x} ⊆ {K ∙ a₀} := by
      rintro x ⟨hx, hxc⟩
      by_contra hne
      exact hxc (isCollinear_of_le_plane hL hnd hapt ⟨hx.1, hx.2.1⟩ (Ne.symm hne))
    calc _ ≤ ({K ∙ a₀} : Set (Submodule K (Fin m → K))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton _
      _ ≤ q + 1 := by omega
  · have hsub : {x | x ∈ nsPts σ L ∧ ¬ IsCollinear σ (K ∙ a₀) x} ⊆
        {x | x ∈ nsPts σ L ∧ ¬ Nondeg σ (K ∙ a₀ ⊔ x)} := by
      rintro x ⟨hx, hxc⟩
      refine ⟨hx, fun hn => hxc ⟨?_, hn⟩⟩
      rintro rfl
      exact haL (hx.1 (Submodule.mem_span_singleton_self a₀))
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (ncard_not_collinear_le_of_not_mem hσ hK hL hnd ha₀ haL)

include hσ hK in
theorem le_ncard_collinear {W L a : Submodule K (Fin m → K)} (hL : finrank K L = 2)
    (hnd : Nondeg σ L) (ha : a ∈ nsPts σ W) :
    q ^ 2 - 2 * q - 1 ≤ {x | x ∈ nsPts σ L ∧ IsCollinear σ a x}.ncard := by
  have hbad := ncard_not_collinear_le hσ hK hL hnd ha
  have hns := ncard_nsPts_of_nondeg_plane hσ hK hL hnd
  have hunion : nsPts σ L = {x | x ∈ nsPts σ L ∧ IsCollinear σ a x} ∪
      {x | x ∈ nsPts σ L ∧ ¬ IsCollinear σ a x} := by
    ext x
    constructor
    · intro hx
      by_cases h : IsCollinear σ a x
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hdisj : Disjoint {x | x ∈ nsPts σ L ∧ IsCollinear σ a x}
      {x | x ∈ nsPts σ L ∧ ¬ IsCollinear σ a x} := by
    rw [Set.disjoint_left]
    rintro x ⟨-, h⟩ ⟨-, h'⟩
    exact h' h
  rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at hns
  omega

end LineCount2

section Diameter

variable (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)

include hσ hK in
theorem isCollinear_or_exists_common {W : Submodule K (Fin m → K)} (hq : 3 ≤ q) (hW : Nondeg σ W)
    (h3 : 3 ≤ finrank K W) {a b : Submodule K (Fin m → K)} (ha : a ∈ nsPts σ W)
    (hb : b ∈ nsPts σ W) :
    IsCollinear σ a b ∨ ∃ c ∈ nsPts σ W, IsCollinear σ a c ∧ IsCollinear σ c b := by
  by_cases hab : IsCollinear σ a b
  · exact Or.inl hab
  refine Or.inr ?_
  obtain ⟨b₀, hb₀, hb₀W, rfl⟩ := mem_nsPts_iff.mp hb
  set U := W ⊓ perp σ (K ∙ b₀) with hU
  have hUnd : Nondeg σ U := Nondeg.inf_perp_span_singleton hσ hb₀W hb₀ hW
  have hUdim : finrank K W = finrank K ↥U + 1 := finrank_eq_inf_perp_add_one hσ hb₀W hb₀
  obtain ⟨L, hLU, hL2, hLnd⟩ := exists_nondeg_plane_le hσ hUnd (by omega)
  have hLW : L ≤ W := hLU.trans inf_le_left
  have hLb : ∀ u ∈ L, herm σ u b₀ = 0 := fun u hu =>
    mem_perp_span_singleton.mp (hLU hu).2
  obtain ⟨a₀, ha₀, ha₀W, rfl⟩ := mem_nsPts_iff.mp ha
  have haL : a₀ ∉ L := by
    intro haL
    refine hab (IsCollinear.of_orth hσ ha hb ?_)
    intro u hu v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have := hLb a₀ haL
    rw [herm_smul_left, herm_smul_right, this, mul_zero, mul_zero]
  have hcount := le_ncard_collinear hσ hK hL2 hLnd (span_singleton_mem_nsPts ha₀ ha₀W)
  have hpos : 0 < {x | x ∈ nsPts σ L ∧ IsCollinear σ (K ∙ a₀) x}.ncard := by
    have : 2 * q + 2 ≤ q ^ 2 := by nlinarith
    omega
  obtain ⟨c, hcL, hcol⟩ : ∃ c, c ∈ nsPts σ L ∧ IsCollinear σ (K ∙ a₀) c := by
    obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    exact ⟨c, hc⟩
  have hcW : c ∈ nsPts σ W := ⟨hcL.1.trans hLW, hcL.2.1, hcL.2.2⟩
  refine ⟨c, hcW, hcol, ?_⟩
  refine IsCollinear.of_orth hσ hcW hb ?_
  intro u hu v hv
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [herm_smul_right, hLb u (hcL.1 hu), mul_zero]

end Diameter

section Exists

variable (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)

include hσ hK in
theorem ncard_exists_not_collinear_le {W L : Submodule K (Fin m → K)} (hL : finrank K L = 2)
    (hnd : Nondeg σ L) (X : Finset (Submodule K (Fin m → K))) (hX : ∀ x ∈ X, x ∈ nsPts σ W) :
    {e | e ∈ nsPts σ L ∧ ∃ x ∈ X, ¬ IsCollinear σ x e}.ncard ≤ X.card * (q + 1) := by
  classical
  induction X using Finset.induction_on with
  | empty => simp
  | insert x X hxX ih =>
    have hx : x ∈ nsPts σ W := hX x (Finset.mem_insert_self x X)
    have ih' := ih fun y hy => hX y (Finset.mem_insert_of_mem hy)
    have hsub : {e | e ∈ nsPts σ L ∧ ∃ y ∈ insert x X, ¬ IsCollinear σ y e} ⊆
        {e | e ∈ nsPts σ L ∧ ¬ IsCollinear σ x e} ∪
          {e | e ∈ nsPts σ L ∧ ∃ y ∈ X, ¬ IsCollinear σ y e} := by
      rintro e ⟨he, y, hy, hyc⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inl ⟨he, hyc⟩
      · exact Or.inr ⟨he, y, hy, hyc⟩
    calc _ ≤ ({e | e ∈ nsPts σ L ∧ ¬ IsCollinear σ x e} ∪
          {e | e ∈ nsPts σ L ∧ ∃ y ∈ X, ¬ IsCollinear σ y e}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ (q + 1) + X.card * (q + 1) := add_le_add (ncard_not_collinear_le hσ hK hL hnd hx) ih'
      _ = (insert x X).card * (q + 1) := by
          rw [Finset.card_insert_of_notMem hxX]
          ring

include hσ hK in
theorem exists_collinear_all {W L : Submodule K (Fin m → K)} (hL : finrank K L = 2)
    (hnd : Nondeg σ L) (X : Finset (Submodule K (Fin m → K))) (hX : ∀ x ∈ X, x ∈ nsPts σ W)
    (hcard : X.card * (q + 1) < q ^ 2 - q) :
    ∃ e ∈ nsPts σ L, ∀ x ∈ X, IsCollinear σ x e := by
  by_contra! hcon
  have hbad := ncard_exists_not_collinear_le hσ hK hL hnd X hX
  have hns := ncard_nsPts_of_nondeg_plane hσ hK hL hnd
  have hsub : nsPts σ L ⊆ {e | e ∈ nsPts σ L ∧ ∃ x ∈ X, ¬ IsCollinear σ x e} := fun e he =>
    ⟨he, hcon e he⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end Exists

section Graph

variable (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)

omit [Finite K] in
theorem collGraph_adj {W : Submodule K (Fin m → K)} {x y : ↥(nsPts σ W)} :
    (collGraph σ W).Adj x y ↔ IsCollinear σ x.1 y.1 := Iff.rfl

include hσ hK in
theorem collGraph_edist_le_two (hq : 3 ≤ q) {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h3 : 3 ≤ finrank K W) (x y : ↥(nsPts σ W)) : (collGraph σ W).edist x y ≤ 2 := by
  by_cases hxy : x = y
  · subst hxy
    simp
  rcases isCollinear_or_exists_common hσ hK hq hW h3 x.2 y.2 with h | ⟨c, hc, hxc, hcy⟩
  · have hadj : (collGraph σ W).Adj x y := h
    calc (collGraph σ W).edist x y ≤ hadj.toWalk.length := SimpleGraph.edist_le _
      _ = 1 := by simp
      _ ≤ 2 := by norm_num
  · have h1 : (collGraph σ W).Adj x ⟨c, hc⟩ := hxc
    have h2 : (collGraph σ W).Adj ⟨c, hc⟩ y := hcy
    calc (collGraph σ W).edist x y ≤ (SimpleGraph.Walk.cons h1 h2.toWalk).length :=
        SimpleGraph.edist_le _
      _ = 2 := by simp

include hσ hK in
theorem collGraph_ediam_le_two (hq : 3 ≤ q) {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h3 : 3 ≤ finrank K W) : (collGraph σ W).ediam ≤ 2 :=
  SimpleGraph.ediam_le_of_edist_le (collGraph_edist_le_two hσ hK hq hW h3)

include hσ hK in
theorem collGraph_connected (hq : 3 ≤ q) {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h3 : 3 ≤ finrank K W) : (collGraph σ W).Connected := by
  have hne : (nsPts σ W).Nonempty :=
    nsPts_nonempty_of_nondeg hσ hW (fun h => by rw [h, finrank_bot] at h3; omega)
  have : Nonempty ↥(nsPts σ W) := hne.to_subtype
  refine ⟨fun x y => ?_⟩
  rw [← SimpleGraph.edist_ne_top_iff_reachable]
  exact ne_top_of_le_ne_top (by simp) (collGraph_edist_le_two hσ hK hq hW h3 x y)

end Graph

end CFSG.ClassicalInvolution.Phan
