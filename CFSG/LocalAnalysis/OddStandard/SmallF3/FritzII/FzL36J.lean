module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36Hom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzJ36
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

private lemma fzl_conj_sq (g a : G) : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by
  have h : g⁻¹ * a * g = g⁻¹ * a * (g⁻¹)⁻¹ := by rw [inv_inv]
  rw [h, conj_pow, inv_inv]

private lemma fzl_q8Hom_a1 {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.a 1) = p := by
  change zmod4Pow p (1 : ZMod 4) = p
  rw [zmod4Pow, show (1 : ZMod 4).val = 1 from rfl, pow_one]

private lemma fzl_q8Hom_a2 {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.a 2) = p ^ 2 := by
  change zmod4Pow p (2 : ZMod 4) = p ^ 2
  rw [zmod4Pow, show (2 : ZMod 4).val = 2 from rfl]

private lemma fzl_q8Hom_xa0 {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.xa 0) = q := by
  change q * zmod4Pow p (0 : ZMod 4) = q
  rw [zmod4Pow_zero, mul_one]

private lemma fzl_mul_t_sq {G : Type} [Group G] [Finite G] {t x₁ x₂ lam : G} {L S : Subgroup G}
    {rho : G} (h : Ctx0 t L S x₁ x₂ lam rho) : (x₁ * t) ^ 2 = x₁ ^ 2 := by
  have hc : Commute t x₁ := (fz_commute_t h).1
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp h.hyp.ord_t).1
  rw [(hc.symm).mul_pow 2, ht2, mul_one]

private lemma fzl_mul_t_sq₂ {G : Type} [Group G] [Finite G] {t x₁ x₂ lam : G} {L S : Subgroup G}
    {rho : G} (h : Ctx0 t L S x₁ x₂ lam rho) : (x₂ * t) ^ 2 = x₂ ^ 2 := by
  have hc : Commute t x₂ := (fz_commute_t h).2
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp h.hyp.ord_t).1
  rw [(hc.symm).mul_pow 2, ht2, mul_one]

private lemma fzl_x2sq {G : Type} [Group G] [Finite G] {t x₁ x₂ lam : G} {L S : Subgroup G}
    {rho : G} (h : Ctx0 t L S x₁ x₂ lam rho) :
    x₂ ^ 2 = (x₁ ^ 2)⁻¹ * (x₁ * x₂) ^ 2 := by
  have hcomm : Commute x₁ x₂ := h.wreath.comm
  rw [hcomm.mul_pow 2, ← mul_assoc, inv_mul_cancel, one_mul]

@[expose] def FzJ (T : Subgroup G) (u : G) : Prop :=
  ∃ y ∈ T ⊓ centralizer ({u} : Set G), ∃ v ∈ T ⊓ centralizer ({u} : Set G),
    ∃ w ∈ T ⊓ centralizer ({u} : Set G),
      y ^ 2 ≠ 1 ∧ y ^ 2 ≠ u ^ 2 ∧ v ^ 2 = u ^ 2 ∧ w ^ 2 = u ^ 2 ∧ w * v * w⁻¹ = v⁻¹ ∧
        y * v = v * y ∧ y * w = w * y

theorem fzl_J_conj {T : Subgroup G} {u x g : G} (hg : g⁻¹ * u * g = x)
    (hC : ∀ c ∈ T ⊓ centralizer ({u} : Set G), g⁻¹ * c * g ∈ T ⊓ centralizer ({x} : Set G))
    (hJ : FzJ T u) : FzJ T x := by
  obtain ⟨y, hy, v, hv, w, hw, hy1, hyu, hv2, hw2, hwv, hyv, hyw⟩ := hJ
  refine ⟨g⁻¹ * y * g, hC y hy, g⁻¹ * v * g, hC v hv, g⁻¹ * w * g, hC w hw,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hy1
    have h' : g * (g⁻¹ * y ^ 2 * g) * g⁻¹ = 1 := by
      rw [← fzl_conj_sq g y, h, mul_one, mul_inv_cancel]
    rwa [show g * (g⁻¹ * y ^ 2 * g) * g⁻¹ = y ^ 2 by group] at h'
  · rw [← hg]
    intro h
    have h' : y ^ 2 = u ^ 2 := by
      have h2 : g * (g⁻¹ * y ^ 2 * g) * g⁻¹ = g * (g⁻¹ * u ^ 2 * g) * g⁻¹ := by
        rw [← fzl_conj_sq g y, ← fzl_conj_sq g u, h]
      rwa [show g * (g⁻¹ * y ^ 2 * g) * g⁻¹ = y ^ 2 by group,
        show g * (g⁻¹ * u ^ 2 * g) * g⁻¹ = u ^ 2 by group] at h2
    exact hyu h'
  · rw [← hg, fzl_conj_sq g v, fzl_conj_sq g u, hv2]
  · rw [← hg, fzl_conj_sq g w, fzl_conj_sq g u, hw2]
  · have h2 : g⁻¹ * (w * v * w⁻¹) * g = g⁻¹ * v⁻¹ * g := by rw [hwv]
    rwa [show g⁻¹ * (w * v * w⁻¹) * g
        = (g⁻¹ * w * g) * (g⁻¹ * v * g) * (g⁻¹ * w * g)⁻¹ by group,
      show g⁻¹ * v⁻¹ * g = (g⁻¹ * v * g)⁻¹ by group] at h2
  · have h2 : g⁻¹ * (y * v) * g = g⁻¹ * (v * y) * g := by rw [hyv]
    rwa [show g⁻¹ * (y * v) * g = (g⁻¹ * y * g) * (g⁻¹ * v * g) by group,
      show g⁻¹ * (v * y) * g = (g⁻¹ * v * g) * (g⁻¹ * y * g) by group] at h2
  · have h2 : g⁻¹ * (y * w) * g = g⁻¹ * (w * y) * g := by rw [hyw]
    rwa [show g⁻¹ * (y * w) * g = (g⁻¹ * y * g) * (g⁻¹ * w * g) by group,
      show g⁻¹ * (w * y) * g = (g⁻¹ * w * g) * (g⁻¹ * y * g) by group] at h2

variable [Finite G] {t : G} {L S T₂ : Subgroup G} {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}

theorem fzl_J_holds (hset : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) {u : G}
    (hu : u ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂) (hu2 : u ^ 2 = (x₁ * x₂) ^ 2)
    (hn : ¬ ∃ r ∈ fzR3 t x₁ x₂ a₃₂, ∃ ε ∈ fourGrp x₁ x₂, u = r * ε) : FzJ T₂ u := by
  have hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ := hset.shape
  have hctx0 : Ctx0 t L S x₁ x₂ lam rho := hset.ctx.toCtx0
  obtain ⟨π, hπ1, hπ2, hπ3, _hπlam, hπrange, hπker⟩ := fzl_model_hom hsh
  have hgen : ∀ e ∈ ({x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂} : Set G),
      e ∈ (π.comp (SemidirectProduct.inl : N3 →* Model)).range := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨(QuaternionGroup.a 1, 1, 1), ?_⟩
      exact (hπ1 (QuaternionGroup.a 1)).trans (fzl_q8Hom_a1 hsh.quat₁)
    · refine ⟨(QuaternionGroup.xa 0, 1, 1), ?_⟩
      exact (hπ1 (QuaternionGroup.xa 0)).trans (fzl_q8Hom_xa0 hsh.quat₁)
    · refine ⟨(1, QuaternionGroup.a 1, 1), ?_⟩
      exact (hπ2 (QuaternionGroup.a 1)).trans (fzl_q8Hom_a1 hsh.quat₂)
    · refine ⟨(1, QuaternionGroup.xa 0, 1), ?_⟩
      exact (hπ2 (QuaternionGroup.xa 0)).trans (fzl_q8Hom_xa0 hsh.quat₂)
    · refine ⟨(1, 1, QuaternionGroup.a 1), ?_⟩
      exact (hπ3 (QuaternionGroup.a 1)).trans (fzl_q8Hom_a1 hsh.quat₃)
    · refine ⟨(1, 1, QuaternionGroup.xa 0), ?_⟩
      exact (hπ3 (QuaternionGroup.xa 0)).trans (fzl_q8Hom_xa0 hsh.quat₃)
  obtain ⟨n, hπu⟩ := MonoidHom.mem_range.mp
    ((by rw [fzR6, Subgroup.closure_le]; exact hgen : fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ≤
      (π.comp (SemidirectProduct.inl : N3 →* Model)).range) hu)
  have hπu' : π (⟨n, 1⟩ : Model) = u := hπu
  have hπxt : π xt = (x₁ * x₂)⁻¹ * t :=
    (hπ3 (QuaternionGroup.a 1)).trans (fzl_q8Hom_a1 hsh.quat₃)
  have hR3le : fzR3 t x₁ x₂ a₃₂ ≤ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [fzR3, fourGrp]
    refine fz_closure_le_centralizer ?_
    intro c hc d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · rw [hc, hd, ← fzl_mul_t_sq hctx0]
      exact ((hsh.comm₁₃ (x₁ * t) (by simp) ((x₁ * x₂)⁻¹ * t) (by simp)).pow_left 2).eq
    · rw [hc, hd, ← fz_sq_a31 hctx0]
      exact ((Commute.refl ((x₁ * x₂)⁻¹ * t)).pow_left 2).eq
    · rw [hc, hd, ← fzl_mul_t_sq hctx0]
      exact ((hsh.comm₁₃ (x₁ * t) (by simp) a₃₂ (by simp)).pow_left 2).eq
    · rw [hc, hd, ← fz_sq_a31 hctx0]
      exact hsh.quat₃.mul_comm_sq.symm
  have hP36 : P36 n := by
    refine ⟨?_, ?_⟩
    · apply (hπker _ _).mp
      rw [map_mul, map_mul, hπu', hπxt, ← pow_two, ← pow_two, hu2, fz_sq_a31 hctx0]
    · rintro ⟨q, i, j, hKE⟩
      have hr_mem : q8Hom hsh.quat₃ q ∈ fzR3 t x₁ x₂ a₃₂ := by
        rw [fzR3, ← fz_q8_range hsh.quat₃]
        exact MonoidHom.mem_range.mpr ⟨q, rfl⟩
      have hx2sq : x₂ ^ 2 = (x₁ ^ 2)⁻¹ * (x₁ * x₂) ^ 2 := fzl_x2sq hctx0
      have hx1sq_mem : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
      have hx2sq_mem : x₂ ^ 2 ∈ fourGrp x₁ x₂ := by
        rw [hx2sq]
        exact mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp))
      have hε_mem : (x₁ ^ 2) ^ (i : ℕ) * (x₂ ^ 2) ^ (j : ℕ) ∈ fourGrp x₁ x₂ :=
        mul_mem (Subgroup.pow_mem _ hx1sq_mem (i : ℕ))
          (Subgroup.pow_mem _ hx2sq_mem (j : ℕ))
      have hcomm : ((x₁ ^ 2) ^ (i : ℕ) * (x₂ ^ 2) ^ (j : ℕ)) * q8Hom hsh.quat₃ q
          = q8Hom hsh.quat₃ q * ((x₁ ^ 2) ^ (i : ℕ) * (x₂ ^ 2) ^ (j : ℕ)) :=
        Subgroup.mem_centralizer_iff.mp (hR3le hr_mem) _ hε_mem
      have h1i : q8Hom hsh.quat₁ ((QuaternionGroup.a 2 : Q8) ^ (i : ℕ))
          = (x₁ ^ 2) ^ (i : ℕ) := by
        rw [map_pow, fzl_q8Hom_a2, fzl_mul_t_sq hctx0]
      have h2j : q8Hom hsh.quat₂ ((QuaternionGroup.a 2 : Q8) ^ (j : ℕ))
          = (x₂ ^ 2) ^ (j : ℕ) := by
        rw [map_pow, fzl_q8Hom_a2, fzl_mul_t_sq₂ hctx0]
      have hsplit : (⟨(QuaternionGroup.a 2 ^ (i : ℕ), QuaternionGroup.a 2 ^ (j : ℕ), q),
          1⟩ : Model) =
          (⟨(QuaternionGroup.a 2 ^ (i : ℕ), 1, 1), 1⟩ : Model)
            * (⟨(1, QuaternionGroup.a 2 ^ (j : ℕ), 1), 1⟩ : Model)
            * (⟨(1, 1, q), 1⟩ : Model) := by
        ext <;> simp
      have hval : π (⟨(QuaternionGroup.a 2 ^ (i : ℕ), QuaternionGroup.a 2 ^ (j : ℕ), q),
          1⟩ : Model) =
          ((x₁ ^ 2) ^ (i : ℕ) * (x₂ ^ 2) ^ (j : ℕ)) * q8Hom hsh.quat₃ q := by
        rw [hsplit, map_mul, map_mul, hπ1, hπ2, hπ3, h1i, h2j]
      have hu_eq : u = ((x₁ ^ 2) ^ (i : ℕ) * (x₂ ^ 2) ^ (j : ℕ)) * q8Hom hsh.quat₃ q := by
        rw [← hπu', (hπker (⟨n, 1⟩ : Model)
          (⟨(QuaternionGroup.a 2 ^ (i : ℕ), QuaternionGroup.a 2 ^ (j : ℕ), q), 1⟩ :
            Model)).mpr hKE, hval]
      exact hn ⟨q8Hom hsh.quat₃ q, hr_mem,
        (x₁ ^ 2) ^ (i : ℕ) * (x₂ ^ 2) ^ (j : ℕ), hε_mem, by rw [hu_eq, hcomm]⟩
  have hMJ : MJ (⟨n, 1⟩ : Model) := JHolds n hP36
  obtain ⟨ny, nv, nw, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hMJ
  rw [← hπu']
  refine ⟨π ny, ⟨?_, ?_⟩, π nv, ⟨?_, ?_⟩, π nw, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hπrange]
    exact MonoidHom.mem_range.mpr ⟨ny, rfl⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using (hπker (ny * ⟨n, 1⟩) (⟨n, 1⟩ * ny)).mpr h1)
  · rw [← hπrange]
    exact MonoidHom.mem_range.mpr ⟨nv, rfl⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using (hπker (nv * ⟨n, 1⟩) (⟨n, 1⟩ * nv)).mpr h2)
  · rw [← hπrange]
    exact MonoidHom.mem_range.mpr ⟨nw, rfl⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using (hπker (nw * ⟨n, 1⟩) (⟨n, 1⟩ * nw)).mpr h3)
  · intro h
    exact h4 ((hπker (ny * ny) 1).mp (by simpa only [map_mul, map_one, pow_two] using h))
  · intro h
    apply h5
    apply (hπker (ny * ny) (⟨n, 1⟩ * ⟨n, 1⟩)).mp
    simpa only [map_mul, pow_two] using h
  · have h := (hπker (nv * nv) (⟨n, 1⟩ * ⟨n, 1⟩)).mpr h6
    simpa only [map_mul, pow_two] using h
  · have h := (hπker (nw * nw) (⟨n, 1⟩ * ⟨n, 1⟩)).mpr h7
    simpa only [map_mul, pow_two] using h
  · have h := (hπker (nw * nv * nw⁻¹) (nv⁻¹)).mpr h8
    simpa only [map_mul, map_inv] using h
  · have h := (hπker (ny * nv) (nv * ny)).mpr h9
    simpa only [map_mul] using h
  · have h := (hπker (ny * nw) (nw * ny)).mpr h10
    simpa only [map_mul] using h

end CFSG.OddStandard.SmallF3.FritzII
