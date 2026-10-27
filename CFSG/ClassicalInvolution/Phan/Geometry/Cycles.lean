module

public import CFSG.ClassicalInvolution.Phan.Geometry.Collinear

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

section Large

variable (hσ : IsUnitaryInvolution σ)

include hσ in
theorem inProperNondeg_of_five_le {W a b c : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h5 : 5 ≤ finrank K W) (ha : a ∈ nsPts σ W) (hb : b ∈ nsPts σ W) (hc : c ∈ nsPts σ W)
    (hab : IsCollinear σ a b) : InProperNondeg σ W {a, b, c} := by
  obtain ⟨c₀, hc₀, hc₀W, rfl⟩ := mem_nsPts_iff.mp hc
  have hP2 : finrank K ↥(a ⊔ b) = 2 := finrank_sup_of_ne_pts ha.2.1 hb.2.1 hab.1
  have hPW : a ⊔ b ≤ W := sup_le ha.1 hb.1
  have hPnd : Nondeg σ (a ⊔ b) := hab.2
  have hMnd : Nondeg σ (W ⊓ perp σ (a ⊔ b)) := Nondeg.inf_perp hσ hW hPnd hPW
  have hsplit : a ⊔ b ⊔ (W ⊓ perp σ (a ⊔ b)) = W := sup_inf_perp_of_nondeg hσ _ rfl hPnd hPW
  have hdim := finrank_eq_add_finrank_inf_perp hσ hPnd hPW
  obtain ⟨p, hp, m, hm, hcm⟩ := Submodule.mem_sup.mp (hsplit ▸ hc₀W)
  have hPM : Orth σ (a ⊔ b) (W ⊓ perp σ (a ⊔ b)) :=
    Orth.symm hσ fun u hu v hv => hu.2 v hv
  have hc₀' : c₀ = p + m := hcm.symm
  have haP : a ≤ a ⊔ b := le_sup_left
  have hbP : b ≤ a ⊔ b := le_sup_right
  by_cases hm0 : m = 0
  · refine ⟨a ⊔ b, hPW, hPnd, by omega, ?_⟩
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact haP
    · exact hbP
    · rw [Submodule.span_singleton_le_iff_mem, hc₀', hm0, add_zero]
      exact hp
  by_cases hmm : herm σ m m = 0
  ·
    obtain ⟨y, hyM, hy⟩ : ∃ y ∈ W ⊓ perp σ (a ⊔ b), herm σ m y ≠ 0 := by
      by_contra! hcon
      exact hm0 (hMnd m hm hcon)
    have hy'M : (herm σ m y)⁻¹ • y ∈ W ⊓ perp σ (a ⊔ b) := Submodule.smul_mem _ _ hyM
    have hmy' : herm σ m ((herm σ m y)⁻¹ • y) = 1 := by
      rw [herm_smul_right, inv_mul_cancel₀ hy]
    obtain ⟨t, ht⟩ := exists_isotropize hσ hmm hmy'
    have hfM : (herm σ m y)⁻¹ • y + t • m ∈ W ⊓ perp σ (a ⊔ b) :=
      Submodule.add_mem _ hy'M (Submodule.smul_mem _ _ hm)
    generalize hf : (herm σ m y)⁻¹ • y + t • m = f at ht hfM
    have hmf : herm σ m f = 1 := by
      rw [← hf, herm_add_right, hmy', herm_smul_right, hmm, mul_zero, add_zero]
    have hfm : herm σ f m = 1 := by rw [herm_conj σ hσ.invol m f, hmf, map_one]
    have hHnd : Nondeg σ (K ∙ m ⊔ K ∙ f) := by
      intro s hs hs'
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hs
      obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have h1 := hs' f (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f))
      have h2 := hs' m (Submodule.mem_sup_left (Submodule.mem_span_singleton_self m))
      simp only [herm_add_left, herm_smul_left, hmf, ht, hmm, hfm, mul_one, mul_zero, add_zero,
        zero_add] at h1 h2
      rw [(map_eq_zero_iff σ σ.injective).mp h1, (map_eq_zero_iff σ σ.injective).mp h2,
        zero_smul, zero_smul, add_zero]
    have hHM : K ∙ m ⊔ K ∙ f ≤ W ⊓ perp σ (a ⊔ b) :=
      sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hm)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hfM)
    refine ⟨a ⊔ b ⊔ (K ∙ m ⊔ K ∙ f), sup_le hPW (hHM.trans inf_le_left),
      Nondeg.sup_of_orth hσ hPnd hHnd (hPM.mono le_rfl hHM), ?_, ?_⟩
    · have h1 : finrank K ↥(a ⊔ b ⊔ (K ∙ m ⊔ K ∙ f)) ≤
          finrank K ↥(a ⊔ b) + finrank K ↥(K ∙ m ⊔ K ∙ f) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      have h2 : finrank K ↥(K ∙ m ⊔ K ∙ f) ≤ finrank K ↥(K ∙ m) + finrank K ↥(K ∙ f) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      have h3 := finrank_span_singleton_le_one (K := K) m
      have h4 := finrank_span_singleton_le_one (K := K) f
      omega
    · intro y hy
      rcases hy with rfl | rfl | rfl
      · exact le_sup_of_le_left haP
      · exact le_sup_of_le_left hbP
      · rw [Submodule.span_singleton_le_iff_mem, hc₀']
        exact Submodule.add_mem _ (Submodule.mem_sup_left hp)
          (Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.mem_span_singleton_self m)))
  ·
    have hmK : K ∙ m ≤ W ⊓ perp σ (a ⊔ b) := (Submodule.span_singleton_le_iff_mem _ _).mpr hm
    refine ⟨a ⊔ b ⊔ K ∙ m, sup_le hPW (hmK.trans inf_le_left),
      Nondeg.sup_of_orth hσ hPnd (nondeg_span_singleton hmm) (hPM.mono le_rfl hmK), ?_, ?_⟩
    · have h1 : finrank K ↥(a ⊔ b ⊔ K ∙ m) ≤ finrank K ↥(a ⊔ b) + finrank K ↥(K ∙ m) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      have h3 := finrank_span_singleton_le_one (K := K) m
      omega
    · intro y hy
      rcases hy with rfl | rfl | rfl
      · exact le_sup_of_le_left haP
      · exact le_sup_of_le_left hbP
      · rw [Submodule.span_singleton_le_iff_mem, hc₀']
        exact Submodule.add_mem _ (Submodule.mem_sup_left hp)
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self m))

end Large

section Triple

variable (hσ : IsUnitaryInvolution σ)

include hσ in
theorem inProperNondeg_triple {W : Submodule K (Fin m → K)} {x₀ c₀ : Fin m → K}
    (hx : herm σ x₀ x₀ ≠ 0) (hxW : x₀ ∈ W) (hcW : c₀ ∈ W) {e : Submodule K (Fin m → K)}
    (he : e ∈ nsPts σ W) (hxe : Orth σ e (K ∙ x₀))
    (hce : IsCollinear σ (K ∙ projPerp σ x₀ c₀) e) (h4 : 4 ≤ finrank K W) :
    InProperNondeg σ W {K ∙ x₀, K ∙ c₀, e} := by
  set ca := projPerp σ x₀ c₀ with hca
  have hcaW : ca ∈ W := by
    rw [hca, projPerp_apply]
    exact W.sub_mem hcW (W.smul_mem _ hxW)
  have hxca : Orth σ (K ∙ x₀) (K ∙ ca) :=
    orth_span_singleton_iff.mpr (herm_projPerp_right hσ hx c₀)
  have hxe' : Orth σ (K ∙ x₀) e := hxe.symm hσ
  have hle : K ∙ x₀ ⊔ (K ∙ ca ⊔ e) ≤ W :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hxW)
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hcaW) he.1)
  refine ⟨K ∙ x₀ ⊔ (K ∙ ca ⊔ e), hle, ?_, ?_, ?_⟩
  · exact Nondeg.sup_of_orth hσ (nondeg_span_singleton hx) hce.2 (Orth.sup_right hxca hxe')
  · have h1 : finrank K ↥(K ∙ x₀ ⊔ (K ∙ ca ⊔ e)) ≤
        finrank K ↥(K ∙ x₀) + finrank K ↥(K ∙ ca ⊔ e) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h2 : finrank K ↥(K ∙ ca ⊔ e) ≤ finrank K ↥(K ∙ ca) + finrank K ↥e :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h3 := finrank_span_singleton_le_one (K := K) x₀
    have h4' := finrank_span_singleton_le_one (K := K) ca
    have h5 := he.2.1
    omega
  · intro y hy
    rcases hy with rfl | rfl | rfl
    · exact le_sup_left
    · rw [Submodule.span_singleton_le_iff_mem]
      have : c₀ = ca + ((herm σ x₀ x₀)⁻¹ * herm σ x₀ c₀) • x₀ := by
        rw [hca, projPerp_apply]; abel
      rw [this]
      exact Submodule.add_mem _
        (Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · exact le_sup_of_le_right le_sup_right

end Triple

section Invariant

variable (hσ : IsUnitaryInvolution σ)

@[expose] def nu (σ : K ≃+* K) (x y : Fin m → K) : K :=
  herm σ x y * herm σ y x / (herm σ x x * herm σ y y)

theorem nu_comm (x y : Fin m → K) : nu σ x y = nu σ y x := by
  rw [nu, nu, mul_comm (herm σ x y), mul_comm (herm σ x x)]

include hσ in
theorem herm_projPerp_self {a₀ c₀ : Fin m → K} (ha : herm σ a₀ a₀ ≠ 0)
    (hc : herm σ c₀ c₀ ≠ 0) :
    herm σ (projPerp σ a₀ c₀) (projPerp σ a₀ c₀) = herm σ c₀ c₀ * (1 - nu σ a₀ c₀) := by
  rw [herm_projPerp_projPerp hσ ha, nu]
  field_simp

include hσ in
theorem nu_ne_one_of_isCollinear {x₀ y₀ : Fin m → K} (hx : herm σ x₀ x₀ ≠ 0)
    (hy : herm σ y₀ y₀ ≠ 0) (h : IsCollinear σ (K ∙ x₀) (K ∙ y₀)) : nu σ x₀ y₀ ≠ 1 := by
  rw [isCollinear_span_iff hσ hx hy] at h
  intro h1
  apply h
  rw [nu, div_eq_one_iff_eq (mul_ne_zero hx hy)] at h1
  linear_combination -h1

include hσ in
theorem nu_fixed (x y : Fin m → K) : σ (nu σ x y) = nu σ x y := by
  rw [nu, map_div₀, map_mul, map_mul, herm_conj σ hσ.invol x y, herm_self_fixed σ hσ.invol,
    herm_self_fixed σ hσ.invol, hσ.invol, mul_comm (herm σ x y)]

theorem herm_projPerp_of_orth {a₀ c₀ e₀ : Fin m → K} (hae : herm σ a₀ e₀ = 0) :
    herm σ (projPerp σ a₀ c₀) e₀ = herm σ c₀ e₀ := by
  rw [projPerp_apply, herm_sub_left, herm_smul_left, hae, mul_zero, sub_zero]

section Pigeon

variable [Finite K]

include hσ in
theorem eq_or_eq_zero_of_card_four (hK : Nat.card K = 4 ^ 2) {x y z : K} (hx : σ x = x)
    (hy : σ y = y) (hz : σ z = z) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hz1 : z ≠ 1) :
    x = 0 ∨ y = 0 ∨ z = 0 ∨ x = y ∨ y = z ∨ x = z := by
  by_contra! h
  obtain ⟨hx0, hy0, hz0, hxy, hyz, hxz⟩ := h
  have hF : ({c : K | σ c = c} : Set K).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact card_fixed_eq hσ hK
  have hU : ({c : K | σ c = c ∧ c ≠ 0 ∧ c ≠ 1} ∪ {0, 1} : Set K) = {c : K | σ c = c} := by
    ext c
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact h
      · rcases h with rfl | rfl
        · exact map_zero σ
        · exact map_one σ
    · intro h
      by_cases h0 : c = 0
      · exact Or.inr (Or.inl h0)
      · by_cases h1 : c = 1
        · exact Or.inr (Or.inr h1)
        · exact Or.inl ⟨h, h0, h1⟩
  have hD : Disjoint {c : K | σ c = c ∧ c ≠ 0 ∧ c ≠ 1} ({0, 1} : Set K) := by
    rw [Set.disjoint_left]
    rintro c ⟨-, h0, h1⟩ hc
    rcases hc with rfl | rfl
    · exact h0 rfl
    · exact h1 rfl
  rw [← hU, Set.ncard_union_eq hD (Set.toFinite _) (Set.toFinite _),
    Set.ncard_pair (zero_ne_one : (0 : K) ≠ 1)] at hF
  have hsub : ({x, y, z} : Set K) ⊆ {c : K | σ c = c ∧ c ≠ 0 ∧ c ≠ 1} := by
    intro c hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨hx, hx0, hx1⟩
    · exact ⟨hy, hy0, hy1⟩
    · exact ⟨hz, hz0, hz1⟩
  have h3 : ({x, y, z} : Set K).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end Pigeon

end Invariant

@[expose] def IsConePoint (σ : K ≃+* K) (W a b c e : Submodule K (Fin m → K)) : Prop :=
  e ∈ nsPts σ W ∧ IsCollinear σ a e ∧ IsCollinear σ b e ∧ IsCollinear σ c e ∧
    InProperNondeg σ W {a, b, e} ∧ InProperNondeg σ W {a, c, e} ∧ InProperNondeg σ W {b, c, e}

theorem IsConePoint.swap_left {W a b c e : Submodule K (Fin m → K)}
    (h : IsConePoint σ W a b c e) : IsConePoint σ W b a c e := by
  obtain ⟨he, hae, hbe, hce, h1, h2, h3⟩ := h
  refine ⟨he, hbe, hae, hce, ?_, h3, h2⟩
  rwa [Set.insert_comm] at h1

theorem IsConePoint.swap_right {W a b c e : Submodule K (Fin m → K)}
    (h : IsConePoint σ W a b c e) : IsConePoint σ W a c b e := by
  obtain ⟨he, hae, hbe, hce, h1, h2, h3⟩ := h
  refine ⟨he, hae, hce, hbe, h2, h1, ?_⟩
  rwa [Set.insert_comm] at h3

section CycleExistence

variable (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)

include hσ hK in
theorem exists_orth_collinear {W a b : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) (ha : a ∈ nsPts σ W) (hb : b ∈ nsPts σ W) (hab : IsCollinear σ a b)
    (X : Finset (Submodule K (Fin m → K))) (hX : ∀ x ∈ X, x ∈ nsPts σ W)
    (hcard : X.card * (q + 1) < q ^ 2 - q) :
    ∃ e ∈ nsPts σ W, Orth σ e a ∧ Orth σ e b ∧ ∀ x ∈ X, IsCollinear σ x e := by
  have hP2 : finrank K ↥(a ⊔ b) = 2 := finrank_sup_of_ne_pts ha.2.1 hb.2.1 hab.1
  have hPW : a ⊔ b ≤ W := sup_le ha.1 hb.1
  obtain ⟨L, hLW, hLnd, hL2, hLP⟩ := exists_nondeg_plane_orth hσ hW hab.2 hPW hP2 h4
  obtain ⟨e, heL, hXe⟩ := exists_collinear_all hσ hK hL2 hLnd X hX hcard
  refine ⟨e, ⟨heL.1.trans hLW, heL.2.1, heL.2.2⟩, ?_, ?_, hXe⟩
  · exact hLP.mono heL.1 le_sup_left
  · exact hLP.mono heL.1 le_sup_right

include hσ hK in
theorem exists_orth_collinear_two (hq : 4 ≤ q) {W a b c d : Submodule K (Fin m → K)}
    (hW : Nondeg σ W) (h4 : 4 ≤ finrank K W) (ha : a ∈ nsPts σ W) (hb : b ∈ nsPts σ W)
    (hab : IsCollinear σ a b) (hc : c ∈ nsPts σ W) (hd : d ∈ nsPts σ W) :
    ∃ e ∈ nsPts σ W, Orth σ e a ∧ Orth σ e b ∧ IsCollinear σ c e ∧ IsCollinear σ d e := by
  classical
  have hcard : ({c, d} : Finset (Submodule K (Fin m → K))).card * (q + 1) < q ^ 2 - q := by
    have h2 : ({c, d} : Finset (Submodule K (Fin m → K))).card ≤ 2 := Finset.card_le_two
    have : 2 * (q + 1) < q ^ 2 - q := by
      have : 3 * q + 3 ≤ q ^ 2 := by nlinarith
      omega
    calc _ ≤ 2 * (q + 1) := Nat.mul_le_mul_right _ h2
      _ < _ := this
  obtain ⟨e, he, hOa, hOb, hXe⟩ := exists_orth_collinear hσ hK hW h4 ha hb hab {c, d}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc
      · rw [Finset.mem_singleton.mp hx]; exact hd) hcard
  exact ⟨e, he, hOa, hOb, hXe c (by simp), hXe d (by simp)⟩

include hσ hK in
theorem exists_orth_collinear_one (hq : 3 ≤ q) {W a c d : Submodule K (Fin m → K)}
    (hW : Nondeg σ W) (h4 : 4 ≤ finrank K W) (hc : c ∈ nsPts σ W) (hd : d ∈ nsPts σ W)
    (hcd : IsCollinear σ c d) (ha : a ∈ nsPts σ W) :
    ∃ f ∈ nsPts σ W, Orth σ f c ∧ Orth σ f d ∧ IsCollinear σ a f := by
  classical
  have hcard : ({a} : Finset (Submodule K (Fin m → K))).card * (q + 1) < q ^ 2 - q := by
    have : 2 * q + 2 ≤ q ^ 2 := by nlinarith
    rw [Finset.card_singleton]
    omega
  obtain ⟨f, hf, hOc, hOd, hXf⟩ := exists_orth_collinear hσ hK hW h4 hc hd hcd {a}
    (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]; exact ha) hcard
  exact ⟨f, hf, hOc, hOd, hXf a (by simp)⟩

omit [Finite K] in
include hσ in
theorem isConePoint_of_collinear {W : Submodule K (Fin m → K)} (h4 : 4 ≤ finrank K W)
    {a₀ b₀ c₀ : Fin m → K} (ha₀ : herm σ a₀ a₀ ≠ 0) (hb₀ : herm σ b₀ b₀ ≠ 0)
    (ha₀W : a₀ ∈ W) (hb₀W : b₀ ∈ W) (hc₀W : c₀ ∈ W) (hab : IsCollinear σ (K ∙ a₀) (K ∙ b₀))
    {e : Submodule K (Fin m → K)} (he : e ∈ nsPts σ W) (hOa : Orth σ e (K ∙ a₀))
    (hOb : Orth σ e (K ∙ b₀)) (hce : IsCollinear σ (K ∙ c₀) e)
    (hcae : IsCollinear σ (K ∙ projPerp σ a₀ c₀) e)
    (hcbe : IsCollinear σ (K ∙ projPerp σ b₀ c₀) e) :
    IsConePoint σ W (K ∙ a₀) (K ∙ b₀) (K ∙ c₀) e := by
  have ha : K ∙ a₀ ∈ nsPts σ W := span_singleton_mem_nsPts ha₀ ha₀W
  have hb : K ∙ b₀ ∈ nsPts σ W := span_singleton_mem_nsPts hb₀ hb₀W
  refine ⟨he, IsCollinear.of_orth hσ ha he (hOa.symm hσ),
    IsCollinear.of_orth hσ hb he (hOb.symm hσ), hce, ?_,
    inProperNondeg_triple hσ ha₀ ha₀W hc₀W he hOa hcae h4,
    inProperNondeg_triple hσ hb₀ hb₀W hc₀W he hOb hcbe h4⟩
  refine ⟨K ∙ a₀ ⊔ K ∙ b₀ ⊔ e, sup_le (sup_le ha.1 hb.1) he.1,
    Nondeg.sup_of_orth hσ hab.2 he.2.2 (Orth.sup_left (hOa.symm hσ) (hOb.symm hσ)), ?_, ?_⟩
  · have h1 : finrank K ↥(K ∙ a₀ ⊔ K ∙ b₀ ⊔ e) ≤ finrank K ↥(K ∙ a₀ ⊔ K ∙ b₀) + finrank K ↥e :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h2 : finrank K ↥(K ∙ a₀ ⊔ K ∙ b₀) = 2 := finrank_sup_of_ne_pts ha.2.1 hb.2.1 hab.1
    have h5 := he.2.1
    omega
  · intro y hy
    rcases hy with rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right

include hσ hK in
theorem exists_cone_point_triangle (hq : 5 ≤ q) {W a b c : Submodule K (Fin m → K)}
    (hW : Nondeg σ W) (h4 : 4 ≤ finrank K W) (ha : a ∈ nsPts σ W) (hb : b ∈ nsPts σ W)
    (hc : c ∈ nsPts σ W) (hab : IsCollinear σ a b) (hac : IsCollinear σ a c)
    (hbc : IsCollinear σ b c) : ∃ e, IsConePoint σ W a b c e := by
  classical
  obtain ⟨a₀, ha₀, ha₀W, rfl⟩ := mem_nsPts_iff.mp ha
  obtain ⟨b₀, hb₀, hb₀W, rfl⟩ := mem_nsPts_iff.mp hb
  obtain ⟨c₀, hc₀, hc₀W, rfl⟩ := mem_nsPts_iff.mp hc
  have hca : herm σ (projPerp σ a₀ c₀) (projPerp σ a₀ c₀) ≠ 0 :=
    (nondeg_span_pair_iff hσ ha₀ (not_mem_span_of_ne hc₀ hac.1)).mp hac.2
  have hcb : herm σ (projPerp σ b₀ c₀) (projPerp σ b₀ c₀) ≠ 0 :=
    (nondeg_span_pair_iff hσ hb₀ (not_mem_span_of_ne hc₀ hbc.1)).mp hbc.2
  have hcaW : projPerp σ a₀ c₀ ∈ W := by
    rw [projPerp_apply]; exact W.sub_mem hc₀W (W.smul_mem _ ha₀W)
  have hcbW : projPerp σ b₀ c₀ ∈ W := by
    rw [projPerp_apply]; exact W.sub_mem hc₀W (W.smul_mem _ hb₀W)
  have hXW : ∀ x ∈ ({K ∙ c₀, K ∙ projPerp σ a₀ c₀, K ∙ projPerp σ b₀ c₀} :
      Finset (Submodule K (Fin m → K))), x ∈ nsPts σ W := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hc
    · exact span_singleton_mem_nsPts hca hcaW
    · exact span_singleton_mem_nsPts hcb hcbW
  have hcard : ({K ∙ c₀, K ∙ projPerp σ a₀ c₀, K ∙ projPerp σ b₀ c₀} :
      Finset (Submodule K (Fin m → K))).card * (q + 1) < q ^ 2 - q := by
    have h3 : ({K ∙ c₀, K ∙ projPerp σ a₀ c₀, K ∙ projPerp σ b₀ c₀} :
        Finset (Submodule K (Fin m → K))).card ≤ 3 := Finset.card_le_three
    have : 3 * (q + 1) < q ^ 2 - q := by
      have : 4 * q + 4 ≤ q ^ 2 := by nlinarith
      omega
    calc _ ≤ 3 * (q + 1) := Nat.mul_le_mul_right _ h3
      _ < _ := this
  obtain ⟨e, he, hOa, hOb, hXe⟩ := exists_orth_collinear hσ hK hW h4 ha hb hab _ hXW hcard
  exact ⟨e, isConePoint_of_collinear hσ h4 ha₀ hb₀ ha₀W hb₀W hc₀W hab he hOa hOb
    (hXe _ (by simp)) (hXe _ (by simp)) (hXe _ (by simp))⟩

include hσ hK in
theorem exists_cone_point_of_repeat (hq : 4 ≤ q) {W : Submodule K (Fin m → K)} (hW : Nondeg σ W)
    (h4 : 4 ≤ finrank K W) {a₀ b₀ c₀ : Fin m → K} (ha₀ : herm σ a₀ a₀ ≠ 0)
    (hb₀ : herm σ b₀ b₀ ≠ 0) (hc₀ : herm σ c₀ c₀ ≠ 0) (ha₀W : a₀ ∈ W) (hb₀W : b₀ ∈ W)
    (hc₀W : c₀ ∈ W) (hab : IsCollinear σ (K ∙ a₀) (K ∙ b₀))
    (hac : IsCollinear σ (K ∙ a₀) (K ∙ c₀)) (hbc : IsCollinear σ (K ∙ b₀) (K ∙ c₀))
    (hrep : nu σ a₀ c₀ = 0 ∨ nu σ b₀ c₀ = 0 ∨ nu σ a₀ c₀ = nu σ b₀ c₀) :
    ∃ e, IsConePoint σ W (K ∙ a₀) (K ∙ b₀) (K ∙ c₀) e := by
  classical
  have ha : K ∙ a₀ ∈ nsPts σ W := span_singleton_mem_nsPts ha₀ ha₀W
  have hb : K ∙ b₀ ∈ nsPts σ W := span_singleton_mem_nsPts hb₀ hb₀W
  have hc : K ∙ c₀ ∈ nsPts σ W := span_singleton_mem_nsPts hc₀ hc₀W
  have hca : herm σ (projPerp σ a₀ c₀) (projPerp σ a₀ c₀) ≠ 0 :=
    (nondeg_span_pair_iff hσ ha₀ (not_mem_span_of_ne hc₀ hac.1)).mp hac.2
  have hcb : herm σ (projPerp σ b₀ c₀) (projPerp σ b₀ c₀) ≠ 0 :=
    (nondeg_span_pair_iff hσ hb₀ (not_mem_span_of_ne hc₀ hbc.1)).mp hbc.2
  have hcaW : projPerp σ a₀ c₀ ∈ W := by
    rw [projPerp_apply]; exact W.sub_mem hc₀W (W.smul_mem _ ha₀W)
  have hcbW : projPerp σ b₀ c₀ ∈ W := by
    rw [projPerp_apply]; exact W.sub_mem hc₀W (W.smul_mem _ hb₀W)
  have hnca : K ∙ projPerp σ a₀ c₀ ∈ nsPts σ W := span_singleton_mem_nsPts hca hcaW
  have hncb : K ∙ projPerp σ b₀ c₀ ∈ nsPts σ W := span_singleton_mem_nsPts hcb hcbW
  have hg₂ := herm_projPerp_self hσ ha₀ hc₀ (a₀ := a₀) (c₀ := c₀)
  have hg₃ := herm_projPerp_self hσ hb₀ hc₀ (a₀ := b₀) (c₀ := c₀)
  have hcard : ∀ X : Finset (Submodule K (Fin m → K)), X.card ≤ 2 →
      X.card * (q + 1) < q ^ 2 - q := by
    intro X hX
    have : 2 * (q + 1) < q ^ 2 - q := by
      have : 3 * q + 3 ≤ q ^ 2 := by nlinarith
      omega
    calc _ ≤ 2 * (q + 1) := Nat.mul_le_mul_right _ hX
      _ < _ := this
  have horth : ∀ e₀ : Fin m → K, herm σ e₀ a₀ = 0 → herm σ e₀ b₀ = 0 →
      herm σ (projPerp σ a₀ c₀) e₀ = herm σ c₀ e₀ ∧ herm σ (projPerp σ b₀ c₀) e₀ = herm σ c₀ e₀ :=
    fun e₀ h1 h2 => ⟨herm_projPerp_of_orth ((herm_eq_zero_iff hσ _ _).mp h1),
      herm_projPerp_of_orth ((herm_eq_zero_iff hσ _ _).mp h2)⟩
  rcases hrep with hz | hy | hzy
  ·
    have hgg : herm σ (projPerp σ a₀ c₀) (projPerp σ a₀ c₀) = herm σ c₀ c₀ := by
      rw [hg₂, hz, sub_zero, mul_one]
    obtain ⟨e, he, hOa, hOb, hXe⟩ := exists_orth_collinear hσ hK hW h4 ha hb hab
      {K ∙ projPerp σ a₀ c₀, K ∙ projPerp σ b₀ c₀}
      (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hnca
        · rw [Finset.mem_singleton.mp hx]; exact hncb)
      (hcard _ Finset.card_le_two)
    obtain ⟨e₀, he₀, he₀W, rfl⟩ := mem_nsPts_iff.mp he
    obtain ⟨h1, h2⟩ := horth e₀ (orth_span_singleton_iff.mp (hOa)) (orth_span_singleton_iff.mp hOb)
    have hcae := hXe (K ∙ projPerp σ a₀ c₀) (by simp)
    have hcbe := hXe (K ∙ projPerp σ b₀ c₀) (by simp)
    have hce : IsCollinear σ (K ∙ c₀) (K ∙ e₀) :=
      (isCollinear_span_congr hσ hca hc₀ he₀ h1 hgg).mp hcae
    exact ⟨K ∙ e₀, isConePoint_of_collinear hσ h4 ha₀ hb₀ ha₀W hb₀W hc₀W hab he hOa hOb hce
      hcae hcbe⟩
  ·
    have hgg : herm σ (projPerp σ b₀ c₀) (projPerp σ b₀ c₀) = herm σ c₀ c₀ := by
      rw [hg₃, hy, sub_zero, mul_one]
    obtain ⟨e, he, hOa, hOb, hXe⟩ := exists_orth_collinear hσ hK hW h4 ha hb hab
      {K ∙ projPerp σ a₀ c₀, K ∙ projPerp σ b₀ c₀}
      (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hnca
        · rw [Finset.mem_singleton.mp hx]; exact hncb)
      (hcard _ Finset.card_le_two)
    obtain ⟨e₀, he₀, he₀W, rfl⟩ := mem_nsPts_iff.mp he
    obtain ⟨h1, h2⟩ := horth e₀ (orth_span_singleton_iff.mp (hOa)) (orth_span_singleton_iff.mp hOb)
    have hcae := hXe (K ∙ projPerp σ a₀ c₀) (by simp)
    have hcbe := hXe (K ∙ projPerp σ b₀ c₀) (by simp)
    have hce : IsCollinear σ (K ∙ c₀) (K ∙ e₀) :=
      (isCollinear_span_congr hσ hcb hc₀ he₀ h2 hgg).mp hcbe
    exact ⟨K ∙ e₀, isConePoint_of_collinear hσ h4 ha₀ hb₀ ha₀W hb₀W hc₀W hab he hOa hOb hce
      hcae hcbe⟩
  ·
    have hgg : herm σ (projPerp σ a₀ c₀) (projPerp σ a₀ c₀) =
        herm σ (projPerp σ b₀ c₀) (projPerp σ b₀ c₀) := by
      rw [hg₂, hg₃, hzy]
    obtain ⟨e, he, hOa, hOb, hXe⟩ := exists_orth_collinear hσ hK hW h4 ha hb hab
      {K ∙ c₀, K ∙ projPerp σ a₀ c₀}
      (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hc
        · rw [Finset.mem_singleton.mp hx]; exact hnca)
      (hcard _ Finset.card_le_two)
    obtain ⟨e₀, he₀, he₀W, rfl⟩ := mem_nsPts_iff.mp he
    obtain ⟨h1, h2⟩ := horth e₀ (orth_span_singleton_iff.mp (hOa)) (orth_span_singleton_iff.mp hOb)
    have hce := hXe (K ∙ c₀) (by simp)
    have hcae := hXe (K ∙ projPerp σ a₀ c₀) (by simp)
    have hcbe : IsCollinear σ (K ∙ projPerp σ b₀ c₀) (K ∙ e₀) :=
      (isCollinear_span_congr hσ hca hcb he₀ (h1.trans h2.symm) hgg).mp hcae
    exact ⟨K ∙ e₀, isConePoint_of_collinear hσ h4 ha₀ hb₀ ha₀W hb₀W hc₀W hab he hOa hOb hce
      hcae hcbe⟩

include hσ hK in
theorem exists_cone_point_triangle_of_four_le (hq : 4 ≤ q) {W a b c : Submodule K (Fin m → K)}
    (hW : Nondeg σ W) (h4 : 4 ≤ finrank K W) (ha : a ∈ nsPts σ W) (hb : b ∈ nsPts σ W)
    (hc : c ∈ nsPts σ W) (hab : IsCollinear σ a b) (hac : IsCollinear σ a c)
    (hbc : IsCollinear σ b c) : ∃ e, IsConePoint σ W a b c e := by
  rcases Nat.lt_or_ge q 5 with hlt | h5
  swap
  · exact exists_cone_point_triangle hσ hK h5 hW h4 ha hb hc hab hac hbc
  have hq4 : q = 4 := by omega
  subst hq4
  obtain ⟨a₀, ha₀, ha₀W, rfl⟩ := mem_nsPts_iff.mp ha
  obtain ⟨b₀, hb₀, hb₀W, rfl⟩ := mem_nsPts_iff.mp hb
  obtain ⟨c₀, hc₀, hc₀W, rfl⟩ := mem_nsPts_iff.mp hc
  have hpig := eq_or_eq_zero_of_card_four hσ hK (nu_fixed hσ a₀ b₀) (nu_fixed hσ b₀ c₀)
    (nu_fixed hσ a₀ c₀) (nu_ne_one_of_isCollinear hσ ha₀ hb₀ hab)
    (nu_ne_one_of_isCollinear hσ hb₀ hc₀ hbc) (nu_ne_one_of_isCollinear hσ ha₀ hc₀ hac)
  have hapex_a : (nu σ b₀ a₀ = 0 ∨ nu σ c₀ a₀ = 0 ∨ nu σ b₀ a₀ = nu σ c₀ a₀) →
      ∃ e, IsConePoint σ W (K ∙ a₀) (K ∙ b₀) (K ∙ c₀) e := fun hrep => by
    obtain ⟨e, he⟩ := exists_cone_point_of_repeat hσ hK hq hW h4 hb₀ hc₀ ha₀ hb₀W hc₀W ha₀W hbc
      hab.symm hac.symm hrep
    exact ⟨e, he.swap_right.swap_left⟩
  have hapex_b : (nu σ a₀ b₀ = 0 ∨ nu σ c₀ b₀ = 0 ∨ nu σ a₀ b₀ = nu σ c₀ b₀) →
      ∃ e, IsConePoint σ W (K ∙ a₀) (K ∙ b₀) (K ∙ c₀) e := fun hrep => by
    obtain ⟨e, he⟩ := exists_cone_point_of_repeat hσ hK hq hW h4 ha₀ hc₀ hb₀ ha₀W hc₀W hb₀W hac
      hab hbc.symm hrep
    exact ⟨e, he.swap_right⟩
  have hapex_c : (nu σ a₀ c₀ = 0 ∨ nu σ b₀ c₀ = 0 ∨ nu σ a₀ c₀ = nu σ b₀ c₀) →
      ∃ e, IsConePoint σ W (K ∙ a₀) (K ∙ b₀) (K ∙ c₀) e := fun hrep =>
    exists_cone_point_of_repeat hσ hK hq hW h4 ha₀ hb₀ hc₀ ha₀W hb₀W hc₀W hab hac hbc hrep
  rcases hpig with hx | hy | hz | hxy | hyz | hxz
  · exact hapex_a (Or.inl (by rw [nu_comm]; exact hx))
  · exact hapex_c (Or.inr (Or.inl hy))
  · exact hapex_c (Or.inl hz)
  · exact hapex_b (Or.inr (Or.inr (by rw [nu_comm c₀ b₀]; exact hxy)))
  · exact hapex_c (Or.inr (Or.inr hyz.symm))
  · exact hapex_a (Or.inr (Or.inr (by rw [nu_comm b₀ a₀, nu_comm c₀ a₀]; exact hxz)))

end CycleExistence

end CFSG.ClassicalInvolution.Phan
