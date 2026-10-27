module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GCentA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Z2a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private lemma y4_mem_zpowers_z_iff (c : Ctx4 s e) {x : G} :
    x ∈ zpowers s.fr.z ↔ x = 1 ∨ x = s.fr.z := by
  have hz := s3_z_order s c.hA
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hmod := zpow_mod_orderOf s.fr.z k
    rw [hz] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← hk, ← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
      simp
    · right
      rw [← hk, ← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
      simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

private lemma y4_commutator_mul_eq {c u y : G} (h : u * y = y * u) :
    ⁅c, y⁆ = ⁅c * u, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def,
    show c * u * y = c * y * u by rw [mul_assoc, h, ← mul_assoc]]
  group

private lemma y4_conj_mem_pair (c : Ctx4 s e) {v y : G} (hv : v ∈ cen s.fr.B) (hy : y ∈ s.T₂) :
    y * v * y⁻¹ = v ∨ y * v * y⁻¹ = s.fr.z * v := by
  have hzy : y * s.fr.z * y⁻¹ = s.fr.z := f3_T2_fix_z c.toF33 y hy
  have hwV : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := y4_w_mem_V c
  have hconjw : y * (s.fr.b₁ * s.fr.b₂) * y⁻¹ ∈ cen s.fr.B :=
    y4_T2_normV c y hy _ hwV
  have hwcase : y * (s.fr.b₁ * s.fr.b₂) * y⁻¹ = s.fr.b₁ * s.fr.b₂ ∨
      y * (s.fr.b₁ * s.fr.b₂) * y⁻¹ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
    rcases y4_V_enum c hconjw with h | h | h | h
    · exfalso
      have hh := congrArg (fun t => y⁻¹ * t * y) h
      rw [show y⁻¹ * (y * (s.fr.b₁ * s.fr.b₂) * y⁻¹) * y = s.fr.b₁ * s.fr.b₂ by group]
        at hh
      exact y4_w_ne_one c (by simpa using hh)
    · exfalso
      have hz' : y⁻¹ * s.fr.z * y = s.fr.z := by
        have hh := congrArg (fun t => y⁻¹ * t * y) hzy
        rw [show y⁻¹ * (y * s.fr.z * y⁻¹) * y = s.fr.z by group] at hh
        exact hh.symm
      have hh := congrArg (fun t => y⁻¹ * t * y) h
      rw [show y⁻¹ * (y * (s.fr.b₁ * s.fr.b₂) * y⁻¹) * y = s.fr.b₁ * s.fr.b₂ by group,
        hz'] at hh
      exact y4_w_ne_z c hh
    · exact Or.inl h
    · exact Or.inr h
  rcases y4_V_enum c hv with rfl | rfl | rfl | rfl
  · simp
  · exact Or.inl hzy
  · exact hwcase
  · have h1 : y * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * y⁻¹ =
        s.fr.z * (y * (s.fr.b₁ * s.fr.b₂) * y⁻¹) := by
      rw [show y * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * y⁻¹ =
        (y * s.fr.z * y⁻¹) * (y * (s.fr.b₁ * s.fr.b₂) * y⁻¹) by group, hzy]
    rw [h1]
    rcases hwcase with h | h
    · left; rw [h]
    · right; rw [h]

private lemma y4_commutator_mem_Z (c : Ctx4 s e) {v y : G} (hv : v ∈ cen s.fr.B) (hy : y ∈ s.T₂) :
    ⁅v, y⁆ ∈ zpowers s.fr.z := by
  have hvv : v * v = 1 := by simpa [pow_two] using y4_V_sq c hv
  have hvz : v * s.fr.z = s.fr.z * v := y4_V_comm c hv (y4_z_mem_V c)
  have hcomm : ⁅v, y⁆ = v * (y * v * y⁻¹) := by
    rw [commutatorElement_def, show v⁻¹ = v from inv_eq_of_mul_eq_one_right hvv]
    group
  rcases y4_conj_mem_pair c hv hy with h | h
  · rw [hcomm, h, hvv]; exact Subgroup.one_mem _
  · rw [hcomm, h]
    have hz : v * (s.fr.z * v) = s.fr.z := by
      calc v * (s.fr.z * v) = (v * s.fr.z) * v := by group
        _ = (s.fr.z * v) * v := by rw [hvz]
        _ = s.fr.z := by rw [mul_assoc, hvv, mul_one]
    rw [hz]; exact Subgroup.mem_zpowers _

theorem y4_V_le_Z2 (c : Ctx4 s e) : cen s.fr.B ≤ zSeries 2 s.T₂ := by
  intro v hv
  rw [y4_mem_zSeries_succ]
  refine ⟨y4_S_le_T2 s (s3_B_le_S s (s3_cenB_le_B s hv)), fun y hy => ?_⟩
  rw [y4_zSeries_one, y4_cenT2_eq c]
  exact y4_commutator_mem_Z c hv hy

theorem y4_Z2_decomp (c : Ctx4 s e) {x : G} (hx : x ∈ zSeries 2 s.T₂) :
    ∃ a ∈ closure ({s.fr.b₁, s.fr.b₂} : Set G), ∃ u ∈ zt s, x = a * u := by
  have hxcomm : ∀ y ∈ s.T₂, ⁅x, y⁆ ∈ zpowers s.fr.z := by
    intro y hy
    have h := (y4_mem_zSeries_succ 1 s.T₂ x).mp hx |>.2 y hy
    rwa [y4_zSeries_one, y4_cenT2_eq c] at h
  have hz_comm : ∀ a ∈ s.fr.S, ⁅s.fr.z, a⁆ = 1 := fun a ha =>
    commutatorElement_eq_one_iff_commute.mpr (y4_z_comm_S c ha).symm
  have hy : ∀ a ∈ ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂} : Set G),
      ⁅x, a⁆ = 1 ∨ ⁅x, a⁆ = s.fr.z := by
    intro a ha
    exact (y4_mem_zpowers_z_iff c).mp (hxcomm a (y4_A_le_T2 s (Subgroup.subset_closure ha)))
  obtain ⟨c₀, hc₀A, hc₀cent⟩ := y4_central_aut (y4_z_sq c)
    (hz_comm s.fr.a₁ (Subgroup.subset_closure (by simp)))
    (hz_comm s.fr.b₁ (Subgroup.subset_closure (by simp)))
    (hz_comm s.fr.a₂ (Subgroup.subset_closure (by simp)))
    (hz_comm s.fr.b₂ (Subgroup.subset_closure (by simp)))
    c.hRel.comm1 c.hRel.comm2 c.hRel.a1a2 c.hRel.a1b2 c.hRel.b1a2 c.hRel.b1b2 hy
  let u : G := c₀⁻¹ * x
  have huT1 : u ∈ e.T₁ := e.T₁.mul_mem (e.T₁.inv_mem (c.h32.1.1 hc₀A)) (y4_Z2_le_T1 c hx)
  have huC0 : u ∈ C0 e := Subgroup.mem_inf.mpr ⟨huT1, hc₀cent⟩
  have huzt : u ∈ zt s := c.hBr ▸ huC0
  have hc₀S : c₀ ∈ s.fr.S := s3_A_le_S s hc₀A
  have hc₀Z2 : c₀ ∈ zSeries 2 s.fr.S := by
    rw [y4_mem_zSeries_succ]
    refine ⟨hc₀S, fun y hy => ?_⟩
    rw [y4_zSeries_one, c.hA.cen_S]
    have hx_eq : x = c₀ * u := by rw [show u = c₀⁻¹ * x from rfl]; group
    have hcommuy : u * y = y * u := y4_zt_comm_T c huzt (s3_S_le_T s hy)
    rw [y4_commutator_mul_eq hcommuy, ← hx_eq]
    exact hxcomm y (y4_S_le_T2 s hy)
  have hc₀b : c₀ ∈ closure ({s.fr.b₁, s.fr.b₂} : Set G) := by
    have h : zSeries 2 s.fr.S = closure ({s.fr.b₁, s.fr.b₂} : Set G) :=
      c.hLF.fact14.1.2.1.trans c.hLF.fact14.1.2.2.1
    rwa [← h]
  exact ⟨c₀, hc₀b, u, huzt, by rw [show u = c₀⁻¹ * x from rfl]; group⟩

private lemma y4_V_mul_comm (c : Ctx4 s e) {x y z : G}
    (hx : x ∈ cen s.fr.B) (hy : y ∈ cen s.fr.B) (hz : z ∈ cen s.fr.B) :
    x * (y * z) = z * (x * y) := by
  calc x * (y * z) = (x * y) * z := by group
    _ = (y * x) * z := by rw [y4_V_comm c hx hy]
    _ = y * (x * z) := by group
    _ = y * (z * x) := by rw [y4_V_comm c hx hz]
    _ = (y * z) * x := by group
    _ = (z * y) * x := by rw [y4_V_comm c hy hz]
    _ = z * (y * x) := by group
    _ = z * (x * y) := by rw [y4_V_comm c hx hy]

private lemma y4_eps_t_contra (c : Ctx4 s e) {a ε : G} (haV : a ∈ cen s.fr.B)
    (hε : ε = 1 ∨ ε = s.fr.z) (hyZ : a * (ε * s.t) ∈ zSeries 2 s.T₂) : False := by
  obtain ⟨x₁, hx₁, hψV, hψ1, hψz⟩ := y4_exists_psi c
  have hx₁T2 : x₁ ∈ s.T₂ := y4_C2_le_T2 s hx₁
  have hεV : ε ∈ cen s.fr.B := by
    rcases hε with rfl | rfl
    · exact Subgroup.one_mem _
    · exact y4_z_mem_V c
  have hycomm : ⁅a * (ε * s.t), x₁⁆ ∈ zpowers s.fr.z := by
    have h := (y4_mem_zSeries_succ 1 s.T₂ (a * (ε * s.t))).mp hyZ |>.2 x₁ hx₁T2
    rwa [y4_zSeries_one, y4_cenT2_eq c] at h
  have hxy : ⁅x₁, a * (ε * s.t)⁆ ∈ zpowers s.fr.z := by
    have h := (zpowers s.fr.z).inv_mem hycomm
    rwa [commutatorElement_inv] at h
  have hxa : x₁ * a * x₁⁻¹ = a := y4_C2_cent_V c hx₁ haV
  have hxε : x₁ * ε * x₁⁻¹ = ε := by
    rcases hε with rfl | rfl
    · simp
    · exact y4_C2_cent_V c hx₁ (y4_z_mem_V c)
  have hVcomm : a * (ε * ⁅x₁, s.t⁆) = ⁅x₁, s.t⁆ * (a * ε) :=
    y4_V_mul_comm c haV hεV hψV
  have hconj : x₁ * (a * (ε * s.t)) * x₁⁻¹ = ⁅x₁, s.t⁆ * (a * (ε * s.t)) := by
    rw [show x₁ * (a * (ε * s.t)) * x₁⁻¹
        = (x₁ * a * x₁⁻¹) * (x₁ * ε * x₁⁻¹) * (x₁ * s.t * x₁⁻¹) by group,
      hxa, hxε, y4_conj_t x₁ s.t]
    rw [show a * ε * (⁅x₁, s.t⁆ * s.t) = (a * (ε * ⁅x₁, s.t⁆)) * s.t by group,
      show ⁅x₁, s.t⁆ * (a * (ε * s.t)) = (⁅x₁, s.t⁆ * (a * ε)) * s.t by group,
      hVcomm]
  have hψeq : ⁅x₁, a * (ε * s.t)⁆ = ⁅x₁, s.t⁆ := by
    rw [commutatorElement_def, hconj]
    group
  rw [hψeq] at hxy
  rcases (y4_mem_zpowers_z_iff c).mp hxy with h | h
  · exact hψ1 h
  · exact hψz h

theorem y4_omega1_Z2 (c : Ctx4 s e) : omega1 (zSeries 2 s.T₂) = cen s.fr.B := by
  apply le_antisymm
  · rw [omega1, Subgroup.closure_le]
    rintro y ⟨hyZ, hy2⟩
    obtain ⟨a, ha, u, hu, rfl⟩ := y4_Z2_decomp c hyZ
    have hbA : closure ({s.fr.b₁, s.fr.b₂} : Set G) ≤ s.fr.A := by
      apply Subgroup.closure_mono
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      tauto
    have haS : a ∈ s.fr.S := s3_A_le_S s (hbA ha)
    have hcomm : Commute a u := (y4_zt_comm_T c hu (s3_S_le_T s haS)).symm
    have hu2 : u ^ 2 = 1 := y4_zt_sq c hu
    have ha2 : a ^ 2 = 1 := by
      have h : a ^ 2 * u ^ 2 = 1 := by rw [← hcomm.mul_pow 2]; exact hy2
      rwa [hu2, mul_one] at h
    have haV : a ∈ cen s.fr.B := y4_sq_one_mem_V c ha ha2
    rcases (s3_mem_zt_iff s c.hA).mp hu with rfl | rfl | rfl | rfl
    · simpa using haV
    · exact (cen s.fr.B).mul_mem haV (y4_z_mem_V c)
    · exact False.elim (y4_eps_t_contra c haV (Or.inl rfl) (by simpa using hyZ))
    · exact False.elim (y4_eps_t_contra c haV (Or.inr rfl) hyZ)
  · intro v hv
    rw [omega1]
    exact Subgroup.subset_closure ⟨y4_V_le_Z2 c hv, y4_V_sq c hv⟩

end CFSG.OddStandard.HigherRank.YamadaG23
