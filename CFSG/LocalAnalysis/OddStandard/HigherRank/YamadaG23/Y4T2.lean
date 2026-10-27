module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Ctx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31CenT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GZ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_T2_isPGroup (c : Ctx4 s e) : IsPGroup 2 ↥s.T₂ :=
  (f3_c9 c.toF33).2.1

theorem y4_T2_le_X (c : Ctx4 s e) : s.T₂ ≤ s.X :=
  (f3_c9 c.toF33).1

theorem y4_T_le_T2 (s : Setting3 G L) : s.T ≤ s.T₂ := le_sup_left

theorem y4_C2_le_T2 (s : Setting3 G L) : s.C₂ ≤ s.T₂ := le_sup_right

theorem y4_T2_normV (c : Ctx4 s e) :
    ∀ x ∈ s.T₂, ∀ v ∈ cen s.fr.B, x * v * x⁻¹ ∈ cen s.fr.B :=
  fun x hx v hv => f3_X_norm_V c.toF33 x (y4_T2_le_X c hx) v hv

theorem y4_T2_le_normV (c : Ctx4 s e) : s.T₂ ≤ normalizer (cen s.fr.B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => y4_T2_normV c x hx v hv, fun hv => ?_⟩
  have h := y4_T2_normV c x⁻¹ (inv_mem hx) _ hv
  have e : x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v := by group
  rwa [e] at h

theorem y4_T2_inf_H (c : Ctx4 s e) : s.H ⊓ s.T₂ = s.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  symm
  exact sylowIn_eq_of_le s.sylow_T ((y4_T2_isPGroup c).to_le inf_le_right) inf_le_left
    (le_inf s.sylow_T.1 (y4_T_le_T2 s))

theorem y4_T2_comm_t (c : Ctx4 s e) {x : G} (hx : x ∈ s.T₂) (h : x * s.t = s.t * x) :
    x ∈ s.T := by
  rw [← y4_T2_inf_H c]
  exact ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff.mp hy]; exact h.symm, hx⟩

theorem y4_cenB_eq (c : Ctx4 s e) : cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} :=
  c.hLF.fact14.2.2.1.1

theorem y4_exists_psi (c : Ctx4 s e) :
    ∃ x ∈ s.C₂, ⁅x, s.t⁆ ∈ cen s.fr.B ∧ ⁅x, s.t⁆ ≠ 1 ∧ ⁅x, s.t⁆ ≠ s.fr.z := by
  obtain ⟨f, hf, hsurj, -⟩ := f3_phiHom c.toF33
  obtain ⟨w, hw, -, hw1, -, hwz, -⟩ := f3_V_elems c.toF33
  obtain ⟨x, hx⟩ := hsurj ⟨w, hw⟩
  refine ⟨x, x.2, ?_⟩
  have h : ((f x : ↥(cen s.fr.B)) : G) = ⁅(x : G), s.t⁆ := by
    rw [hf x, commutatorElement_def]
  rw [hx] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [← h]; exact hw
  · rw [← h]; exact hw1
  · rw [← h]; exact hwz


theorem y4_mem_normalizer_of_conj_mem {H : Subgroup G} {x : G}
    (h : ∀ u ∈ H, x * u * x⁻¹ ∈ H) : x ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  let f : H → H := fun u => ⟨x * u * x⁻¹, h u u.2⟩
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : x * (u : G) * x⁻¹ = x * (v : G) * x⁻¹ := congrArg Subtype.val huv
    exact Subtype.ext (by simpa using h1)
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hf ⟨x * y * x⁻¹, hy⟩
  have h1 : x * (u : G) * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hu
  have h2 : (u : G) = y := by simpa using h1
  exact h2 ▸ u.2

theorem y4_z_mem_T2 (s : Setting3 G L) : s.fr.z ∈ s.T₂ := y4_T_le_T2 s (s3_z_mem_T s)

theorem y4_t_mem_T2 (s : Setting3 G L) : s.t ∈ s.T₂ := y4_T_le_T2 s (s3_t_mem_T s)

theorem y4_S_le_T2 (s : Setting3 G L) : s.fr.S ≤ s.T₂ := (s3_S_le_T s).trans (y4_T_le_T2 s)

theorem y4_A_le_T2 (s : Setting3 G L) : s.fr.A ≤ s.T₂ := (s3_A_le_T s).trans (y4_T_le_T2 s)

theorem y4_z_ne_one (c : Ctx4 s e) : s.fr.z ≠ 1 := by
  intro h
  have := s3_z_order s c.hA
  rw [h, orderOf_one] at this
  norm_num at this

theorem y4_z_sq (c : Ctx4 s e) : s.fr.z ^ 2 = 1 := c.hRel.z_sq

theorem y4_z_comm_S (c : Ctx4 s e) {x : G} (hx : x ∈ s.fr.S) : x * s.fr.z = s.fr.z * x := by
  have hz : s.fr.z ∈ cen s.fr.S := by
    rw [c.hA.cen_S]; exact Subgroup.mem_zpowers _
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hx

theorem y4_C2_cent_V (c : Ctx4 s e) {x v : G} (hx : x ∈ s.C₂) (hv : v ∈ cen s.fr.B) :
    x * v * x⁻¹ = v := by
  have h := (Subgroup.mem_inf.mp (f3_C₂_le_Y c.toF33 hx)).2
  have h2 := Subgroup.mem_centralizer_iff.mp h v hv
  calc x * v * x⁻¹ = (x * v) * x⁻¹ := rfl
    _ = (v * x) * x⁻¹ := by rw [← h2]
    _ = v := by group

theorem y4_comm_t_mem_V (c : Ctx4 s e) {x : G} (hx : x ∈ s.C₂) : ⁅x, s.t⁆ ∈ cen s.fr.B := by
  obtain ⟨f, hf, -, -⟩ := f3_phiHom c.toF33
  have h : ((f ⟨x, hx⟩ : ↥(cen s.fr.B)) : G) = ⁅x, s.t⁆ := by
    rw [hf ⟨x, hx⟩, commutatorElement_def]
  rw [← h]
  exact (f ⟨x, hx⟩).2

theorem y4_conj_t (x : G) (t : G) : x * t * x⁻¹ = ⁅x, t⁆ * t := by
  rw [commutatorElement_def]; group

theorem y4_w_mem_V (c : Ctx4 s e) : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := by
  rw [y4_cenB_eq c]; exact Subgroup.subset_closure (by simp)

theorem y4_z_mem_V (c : Ctx4 s e) : s.fr.z ∈ cen s.fr.B := by
  rw [y4_cenB_eq c]; exact Subgroup.subset_closure (by simp)

theorem y4_w_ne_one (c : Ctx4 s e) : s.fr.b₁ * s.fr.b₂ ≠ 1 := by
  intro h
  have hb : s.fr.b₁ = s.fr.b₂⁻¹ := eq_inv_of_mul_eq_one_left h
  have hc : Commute s.fr.a₁ s.fr.b₂ := commutatorElement_eq_one_iff_commute.mp c.hRel.a1b2
  have h1 : ⁅s.fr.a₁, s.fr.b₁⁆ = 1 := by
    rw [hb]; exact commutatorElement_eq_one_iff_commute.mpr hc.inv_right
  rw [c.hRel.comm1] at h1
  exact y4_z_ne_one c h1

theorem y4_w_ne_z (c : Ctx4 s e) : s.fr.b₁ * s.fr.b₂ ≠ s.fr.z := by
  intro h
  have hb : s.fr.b₁ = s.fr.z * s.fr.b₂⁻¹ := by rw [← h]; group
  have hc : Commute s.fr.a₁ s.fr.b₂ := commutatorElement_eq_one_iff_commute.mp c.hRel.a1b2
  have hza : Commute s.fr.a₁ s.fr.z := y4_z_comm_S c (Subgroup.subset_closure (by simp))
  have h1 : ⁅s.fr.a₁, s.fr.b₁⁆ = 1 := by
    rw [hb]; exact commutatorElement_eq_one_iff_commute.mpr (hza.mul_right hc.inv_right)
  rw [c.hRel.comm1] at h1
  exact y4_z_ne_one c h1

theorem y4_V_enum (c : Ctx4 s e) {v : G} (hv : v ∈ cen s.fr.B) :
    v = 1 ∨ v = s.fr.z ∨ v = s.fr.b₁ * s.fr.b₂ ∨ v = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  obtain ⟨w, hw, hzV, hw1, hz1, hwz, hwsq, hzsq, hwzc, henum⟩ := f3_V_elems c.toF33
  have hzz : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hzsq
  have hww : w * w = 1 := by rw [← pow_two]; exact hwsq
  rcases henum _ (y4_w_mem_V c) with h | h | h | h
  · exact absurd h (y4_w_ne_one c)
  · exact absurd h (y4_w_ne_z c)
  · rw [← h] at henum; exact henum v hv
  ·
    have hw' : w = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
      rw [h]; calc w = (s.fr.z * s.fr.z) * w := by rw [hzz, one_mul]
        _ = s.fr.z * (s.fr.z * w) := by rw [mul_assoc]
    rcases henum v hv with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (h'.trans hw')))
    · exact Or.inr (Or.inr (Or.inl (h'.trans h.symm)))

theorem y4_V_sq (c : Ctx4 s e) {v : G} (hv : v ∈ cen s.fr.B) : v ^ 2 = 1 := by
  obtain ⟨w, hw, hzV, hw1, hz1, hwz, hwsq, hzsq, hwzc, henum⟩ := f3_V_elems c.toF33
  rcases henum v hv with rfl | rfl | rfl | rfl
  · simp
  · exact hzsq
  · exact hwsq
  · have : (s.fr.z * w) ^ 2 = s.fr.z ^ 2 * w ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc s.fr.z * w * (s.fr.z * w) = s.fr.z * (w * s.fr.z) * w := by group
        _ = s.fr.z * (s.fr.z * w) * w := by rw [hwzc]
        _ = s.fr.z * s.fr.z * (w * w) := by group
    rw [this, hzsq, hwsq, one_mul]

theorem y4_V_comm (c : Ctx4 s e) {u v : G} (hu : u ∈ cen s.fr.B) (hv : v ∈ cen s.fr.B) :
    u * v = v * u := by
  have hv' : v ∈ s.fr.B := s3_cenB_le_B s hv
  have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 v hv'
  exact this.symm


theorem y4_sq_one_mem_V (c : Ctx4 s e) {a : G}
    (ha : a ∈ closure ({s.fr.b₁, s.fr.b₂} : Set G)) (h2 : a ^ 2 = 1) : a ∈ cen s.fr.B := by
  have h14 := c.hLF.fact14
  have h1 : zSeries 2 s.fr.S = closure {s.fr.b₁, s.fr.b₂} := h14.1.2.1.trans h14.1.2.2.1
  have h3 : cen s.fr.B = omega1 (zSeries 2 s.fr.S) := h14.2.2.1.2.1
  rw [h3]
  exact Subgroup.subset_closure ⟨by rw [h1]; exact ha, h2⟩

theorem y4_zt_comm_T (c : Ctx4 s e) {u x : G} (hu : u ∈ zt s) (hx : x ∈ s.T) :
    u * x = x * u := by
  have h := (Subgroup.mem_inf.mp (s3_zt_le_cen_T s c.hS c.hZ hu)).2
  exact (Subgroup.mem_centralizer_iff.mp h x hx).symm

theorem y4_zt_sq (c : Ctx4 s e) {u : G} (hu : u ∈ zt s) : u ^ 2 = 1 := by
  have hzt : s.fr.z * s.t = s.t * s.fr.z := y4_zt_comm_T c (u := s.fr.z) (x := s.t)
    (Subgroup.subset_closure (by simp)) (s3_t_mem_T s)
  have htt : s.t ^ 2 = 1 := by
    have := pow_orderOf_eq_one s.t
    rwa [s.t_order] at this
  have hzz : s.fr.z ^ 2 = 1 := c.hRel.z_sq
  rcases (s3_mem_zt_iff s c.hA).mp hu with rfl | rfl | rfl | rfl
  · simp
  · exact hzz
  · exact htt
  · have hzz' : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hzz
    have htt' : s.t * s.t = 1 := by rw [← pow_two]; exact htt
    rw [pow_two]
    calc s.fr.z * s.t * (s.fr.z * s.t) = s.fr.z * (s.t * s.fr.z) * s.t := by group
      _ = s.fr.z * (s.fr.z * s.t) * s.t := by rw [← hzt]
      _ = (s.fr.z * s.fr.z) * (s.t * s.t) := by group
      _ = 1 := by rw [hzz', htt', one_mul]


@[expose] def y4Zt (c : Ctx4 s e) : Subgroup G :=
  y4Zmod s.T₂ (cen s.fr.B) (y4_T2_le_normV c)

theorem y4_mem_Zt (c : Ctx4 s e) (x : G) :
    x ∈ y4Zt c ↔ x ∈ s.T₂ ∧ ∀ y ∈ s.T₂, ⁅x, y⁆ ∈ cen s.fr.B :=
  y4_mem_Zmod (y4_T2_le_normV c) x

@[expose] def y4Zt' (c : Ctx4 s e) : Subgroup G :=
  y4Zt c ⊓ centralizer (cen s.fr.B : Set G)

theorem y4_mem_Zt' (c : Ctx4 s e) (x : G) :
    x ∈ y4Zt' c ↔ (x ∈ s.T₂ ∧ ∀ y ∈ s.T₂, ⁅x, y⁆ ∈ cen s.fr.B) ∧
      ∀ v ∈ cen s.fr.B, v * x = x * v := by
  rw [y4Zt', Subgroup.mem_inf, y4_mem_Zt, Subgroup.mem_centralizer_iff]
  rfl

end CFSG.OddStandard.HigherRank.YamadaG23
