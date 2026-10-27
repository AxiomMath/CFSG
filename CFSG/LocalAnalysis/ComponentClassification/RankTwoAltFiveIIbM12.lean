module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbQ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFivePoints
public import CFSG.GH74.M12.AscFinal

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup

namespace IIbM12

open CFSG.Certificates.ExtraspecialNF

variable {G : Type*} [Group G]

theorem ptOf_zpow_mul {z : G} (k : ℕ) (u : G) : ptOf z (z ^ k * u) = ptOf z u := by
  apply le_antisymm
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    exact mul_mem (pow_mem (mem_sup_left (mem_zpowers z)) k) (mem_sup_right (mem_zpowers u))
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have hm : z ^ k * u ∈ ptOf z (z ^ k * u) := mem_sup_right (mem_zpowers _)
    have hz : z ∈ ptOf z (z ^ k * u) := mem_sup_left (mem_zpowers z)
    have := mul_mem (inv_mem (pow_mem hz k)) hm
    rwa [inv_mul_cancel_left] at this

structure CentHyp (C : Subgroup G) (z₀ v t a c₁ s : G) : Prop where
  d8 : D8D8 z₀ v t a c₁
  le_cent : C ≤ centralizer ({z₀} : Set G)
  Q_le : Qd z₀ v t a c₁ ≤ C
  E₁_normal : ∀ g ∈ C, g * v * g⁻¹ ∈ E₁d z₀ v c₁ ∧ g * c₁ * g⁻¹ ∈ E₁d z₀ v c₁
  cent_E₁ : ∀ g ∈ C, g * v = v * g → g * c₁ = c₁ * g → g ∈ E₁d z₀ v c₁
  card : Nat.card C = 192
  s_mem : s ∈ C
  s_sq : s * s = 1
  s_v : s * v = v * s
  s_a : s * a * s⁻¹ = v * a ∨ s * a * s⁻¹ = v * a * z₀
  s_c : s * c₁ * s⁻¹ = v * c₁ ∨ s * c₁ * s⁻¹ = v * c₁ * z₀
  s_t : s * t * s⁻¹ = v * t * a * c₁ ∨ s * t * s⁻¹ = v * t * a * c₁ * z₀

namespace CentHyp

variable [Finite G] {C : Subgroup G} {z₀ v t a c₁ s : G} (hC : CentHyp C z₀ v t a c₁ s)
include hC

omit [Finite G] in
theorem z_comm {g : G} (hg : g ∈ C) : g * z₀ = z₀ * g :=
  mem_centralizer_singleton_iff.mp (hC.le_cent hg)

omit [Finite G] in
theorem conj_z {g : G} (hg : g ∈ C) : g * z₀ * g⁻¹ = z₀ := by
  rw [hC.z_comm hg, mul_inv_cancel_right]

theorem le_normalizer_E₁ : C ≤ normalizer (E₁d z₀ v c₁ : Set G) := by
  intro g hg
  have hle : (E₁d z₀ v c₁).map (MulAut.conj g).toMonoidHom ≤ E₁d z₀ v c₁ := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SetLike.mem_coe]
    rcases hx with rfl | rfl | rfl
    · rw [hC.conj_z hg]
      exact D8D8.z_mem_E₁
    · exact (hC.E₁_normal g hg).1
    · exact (hC.E₁_normal g hg).2
  exact mem_normalizer_iff_map_conj_eq.mpr
    (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective]))

@[expose] def rho : ↥C →* Equiv.Perm (points (E₁d z₀ v c₁) z₀) :=
  ptAction hC.le_normalizer_E₁ hC.le_cent

omit [Finite G] in
theorem not_mem_zpowers_of_hasVec {x : G} {w : Fin 4 → ZMod 2}
    (hx : D8D8.HasVec z₀ v t a c₁ x w) (hw : w ≠ 0) : x ∉ zpowers z₀ := fun hm =>
  hw ((hC.d8.hasVec_mem_zpowers_iff hx).mp hm)

omit [Finite G] in
theorem ptOf_mem {u : G} (hu : u ∈ E₁d z₀ v c₁) (hu' : u ∉ zpowers z₀) :
    ptOf z₀ u ∈ points (E₁d z₀ v c₁) z₀ :=
  ptOf_mem_points D8D8.z_mem_E₁ hu hC.d8.z_sq hC.d8.z_ne_one (hC.d8.mul_self_of_mem_E₁ hu)
    (hC.d8.comm_of_mem_E₁ D8D8.z_mem_E₁ hu) hu'

omit [Finite G] in
theorem hasVec_vc : D8D8.HasVec z₀ v t a c₁ (v * c₁) ![1, 0, 0, 1] :=
  (hC.d8.hasVec_mul D8D8.hasVec_v D8D8.hasVec_c).congr (by decide)

omit [Finite G] hC in
theorem vc_mem_E₁ : v * c₁ ∈ E₁d z₀ v c₁ := mul_mem D8D8.v_mem_E₁ D8D8.c_mem_E₁

@[expose] def pt : Fin 3 → points (E₁d z₀ v c₁) z₀ :=
  ![⟨ptOf z₀ v, hC.ptOf_mem D8D8.v_mem_E₁
      (hC.not_mem_zpowers_of_hasVec D8D8.hasVec_v (by decide))⟩,
    ⟨ptOf z₀ c₁, hC.ptOf_mem D8D8.c_mem_E₁
      (hC.not_mem_zpowers_of_hasVec D8D8.hasVec_c (by decide))⟩,
    ⟨ptOf z₀ (v * c₁), hC.ptOf_mem vc_mem_E₁
      (hC.not_mem_zpowers_of_hasVec hC.hasVec_vc (by decide))⟩]

theorem pt_surjective : Function.Surjective hC.pt := by
  intro U
  obtain ⟨hUE, hzU, hU4, -⟩ := U.2
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ (U : Subgroup G), u ∉ zpowers z₀ := by
    by_contra hno
    push Not at hno
    have h1 := card_le_of_le (show (U : Subgroup G) ≤ zpowers z₀ from hno)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hU4, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hC.d8.z_sq) hC.d8.z_ne_one]
      at h1
    omega
  have hUpt := eq_ptOf_of_mem_points U.2 hC.d8.z_sq hC.d8.z_ne_one huU hu
  obtain ⟨b, w, hw, rfl⟩ := hC.d8.mem_E₁_iff.mp (hUE huU)
  have hw0 : w ≠ 0 := fun e => hu ((hC.d8.nf_mem_zpowers_iff b w).mpr e)
  rw [nf_eq_zpow_mul, ptOf_zpow_mul] at hUpt
  rcases inWE_cases w hw with rfl | rfl | rfl | rfl
  · exact absurd rfl hw0
  · exact ⟨0, Subtype.ext (by rw [hUpt, ← D8D8.v_eq_nf]; rfl)⟩
  · exact ⟨1, Subtype.ext (by rw [hUpt, ← D8D8.c_eq_nf]; rfl)⟩
  · exact ⟨2, Subtype.ext (by rw [hUpt, ← hC.d8.vc_eq_nf]; rfl)⟩

omit [Finite G] in
theorem pt_injective : Function.Injective hC.pt := by
  have hv := hC.d8.hasVec_mul D8D8.hasVec_z D8D8.hasVec_v
  have hc := hC.d8.hasVec_mul D8D8.hasVec_z D8D8.hasVec_c
  have hvc := hC.d8.hasVec_mul D8D8.hasVec_z hC.hasVec_vc
  have key : ∀ {x y : G} {wx wy : Fin 4 → ZMod 2}, D8D8.HasVec z₀ v t a c₁ x wx →
      D8D8.HasVec z₀ v t a c₁ y wy → x * x = 1 → z₀ * x = x * z₀ → wy ≠ 0 → wy ≠ wx →
      wy ≠ 0 + wx → y ∉ ptOf z₀ x := by
    intro x y wx wy hx hy hx2 hzx hy0 hyx hyzx hm
    rcases (mem_ptOf hC.d8.z_sq hx2 hzx).mp hm with e | e | e | e
    · exact hy0 (hC.d8.hasVec_unique hy (e ▸ (⟨0, nf_zero_zero _ _⟩ :
        D8D8.HasVec z₀ v t a c₁ 1 0)))
    · exact hy0 (hC.d8.hasVec_unique hy (e ▸ D8D8.hasVec_z))
    · exact hyx (hC.d8.hasVec_unique hy (e ▸ hx))
    · exact hyzx (hC.d8.hasVec_unique hy (e ▸ hC.d8.hasVec_mul D8D8.hasVec_z hx))
  have hv2 := hC.d8.v_sq
  have hc2 := hC.d8.c_sq
  have hvc2 : v * c₁ * (v * c₁) = 1 := hC.d8.mul_self_of_mem_E₁ vc_mem_E₁
  have hzv := hC.d8.z_v
  have hzc := hC.d8.z_c
  have hzvc : z₀ * (v * c₁) = v * c₁ * z₀ := by rw [← mul_assoc, hzv, mul_assoc, hzc, mul_assoc]
  intro i j e
  have e' : ((hC.pt i : points _ _) : Subgroup G) = (hC.pt j : Subgroup G) := congrArg _ e
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exfalso
  · exact key D8D8.hasVec_v D8D8.hasVec_c hv2 hzv (by decide) (by decide) (by decide)
      ((show ptOf z₀ v = ptOf z₀ c₁ from e') ▸ mem_sup_right (mem_zpowers c₁))
  · exact key D8D8.hasVec_v hC.hasVec_vc hv2 hzv (by decide) (by decide) (by decide)
      ((show ptOf z₀ v = ptOf z₀ (v * c₁) from e') ▸ mem_sup_right (mem_zpowers (v * c₁)))
  · exact key D8D8.hasVec_c D8D8.hasVec_v hc2 hzc (by decide) (by decide) (by decide)
      ((show ptOf z₀ c₁ = ptOf z₀ v from e') ▸ mem_sup_right (mem_zpowers v))
  · exact key D8D8.hasVec_c hC.hasVec_vc hc2 hzc (by decide) (by decide) (by decide)
      ((show ptOf z₀ c₁ = ptOf z₀ (v * c₁) from e') ▸ mem_sup_right (mem_zpowers (v * c₁)))
  · exact key hC.hasVec_vc D8D8.hasVec_v hvc2 hzvc (by decide) (by decide) (by decide)
      ((show ptOf z₀ (v * c₁) = ptOf z₀ v from e') ▸ mem_sup_right (mem_zpowers v))
  · exact key hC.hasVec_vc D8D8.hasVec_c hvc2 hzvc (by decide) (by decide) (by decide)
      ((show ptOf z₀ (v * c₁) = ptOf z₀ c₁ from e') ▸ mem_sup_right (mem_zpowers c₁))

@[expose] noncomputable def ptEquiv : Fin 3 ≃ points (E₁d z₀ v c₁) z₀ :=
  Equiv.ofBijective hC.pt ⟨hC.pt_injective, hC.pt_surjective⟩

theorem rho_apply (g : ↥C) (U : points (E₁d z₀ v c₁) z₀) :
    ((hC.rho g U : points (E₁d z₀ v c₁) z₀) : Subgroup G) =
      (U : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom :=
  rfl

theorem rho_eq_one_of_mem_Q {g : ↥C} (hg : (g : G) ∈ Qd z₀ v t a c₁) : hC.rho g = 1 := by
  refine Equiv.ext fun U => Subtype.ext ?_
  rw [rho_apply, Equiv.Perm.one_apply]
  obtain ⟨hUE, hzU, -, -⟩ := U.2
  have hzU' : zpowers z₀ ≤ (U : Subgroup G) := zpowers_le.mpr hzU
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro hy
    have hc := hzU' (hC.d8.commutator_mem hg (hC.d8.E₁_le_Q (hUE hy)))
    have := mul_mem hc hy
    rwa [show (g : G) * ((g : G)⁻¹ * y * g) * (g : G)⁻¹ * ((g : G)⁻¹ * y * g)⁻¹ *
      ((g : G)⁻¹ * y * g) = y by group] at this
  · intro hy
    have hc := hzU' (hC.d8.commutator_mem (inv_mem hg) (hC.d8.E₁_le_Q (hUE hy)))
    have := mul_mem hc hy
    rwa [inv_inv, show (g : G)⁻¹ * y * g * y⁻¹ * y = (g : G)⁻¹ * y * g by group] at this

omit [Finite G] in
theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hC.d8.t_sq

omit [Finite G] in
theorem conj_t_v : t * v * t⁻¹ = z₀ * v := by
  rw [hC.t_inv, mul_assoc, hC.d8.v_t, ← mul_assoc, ← mul_assoc, hC.d8.t_sq, one_mul,
    hC.d8.z_v]

omit [Finite G] in
theorem conj_t_c : t * c₁ * t⁻¹ = c₁ := by
  rw [hC.d8.t_c, mul_inv_cancel_right]

omit [Finite G] in
theorem conj_a_v : a * v * a⁻¹ = v := by
  rw [← hC.d8.v_a, mul_inv_cancel_right]

omit [Finite G] in
theorem conj_a_c : a * c₁ * a⁻¹ = z₀ * c₁ := by
  rw [hC.d8.a_c, show c₁ * a * z₀ * a⁻¹ = c₁ * (a * z₀ * a⁻¹) by group, ← hC.d8.z_a,
    mul_inv_cancel_right, hC.d8.z_c]

omit [Finite G] in
theorem hzc : ∀ q ∈ E₁d z₀ v c₁, z₀ * q = q * z₀ := fun _ hq =>
  hC.d8.comm_of_mem_E₁ D8D8.z_mem_E₁ hq

omit [Finite G] in
theorem v_not_mem : v ∉ zpowers z₀ :=
  hC.not_mem_zpowers_of_hasVec D8D8.hasVec_v (by decide)

omit [Finite G] in
theorem c_not_mem : c₁ ∉ zpowers z₀ :=
  hC.not_mem_zpowers_of_hasVec D8D8.hasVec_c (by decide)

theorem conj_v_of_rho {g : ↥C} (hg : hC.rho g = 1) :
    (g : G) * v * (g : G)⁻¹ = v ∨ (g : G) * v * (g : G)⁻¹ = z₀ * v :=
  conj_eq_or_of_ptAction_eq_one D8D8.z_mem_E₁ hC.d8.z_sq hC.d8.z_ne_one hC.hzc
    hC.le_normalizer_E₁ hC.le_cent hg D8D8.v_mem_E₁ hC.d8.v_sq hC.v_not_mem

theorem conj_c_of_rho {g : ↥C} (hg : hC.rho g = 1) :
    (g : G) * c₁ * (g : G)⁻¹ = c₁ ∨ (g : G) * c₁ * (g : G)⁻¹ = z₀ * c₁ :=
  conj_eq_or_of_ptAction_eq_one D8D8.z_mem_E₁ hC.d8.z_sq hC.d8.z_ne_one hC.hzc
    hC.le_normalizer_E₁ hC.le_cent hg D8D8.c_mem_E₁ hC.d8.c_sq hC.c_not_mem

theorem mem_Q_of_rho_eq_one {g : ↥C} (hg : hC.rho g = 1) : (g : G) ∈ Qd z₀ v t a c₁ := by
  have hzv := hC.d8.z_v
  obtain ⟨q, hqQ, hqv, hqc⟩ : ∃ q ∈ Qd z₀ v t a c₁, q * v * q⁻¹ = (g : G) * v * (g : G)⁻¹ ∧
      q * c₁ * q⁻¹ = (g : G) * c₁ * (g : G)⁻¹ := by
    rcases hC.conj_v_of_rho hg with hv | hv <;> rcases hC.conj_c_of_rho hg with hc | hc
    · exact ⟨1, one_mem _, by rw [hv]; group, by rw [hc]; group⟩
    · exact ⟨a, D8D8.a_mem_Q, by rw [hv, hC.conj_a_v], by rw [hc, hC.conj_a_c]⟩
    · exact ⟨t, D8D8.t_mem_Q, by rw [hv, hC.conj_t_v], by rw [hc, hC.conj_t_c]⟩
    · refine ⟨t * a, mul_mem D8D8.t_mem_Q D8D8.a_mem_Q, ?_, ?_⟩
      · rw [hv, show t * a * v * (t * a)⁻¹ = t * (a * v * a⁻¹) * t⁻¹ by group, hC.conj_a_v,
          hC.conj_t_v]
      · rw [hc, show t * a * c₁ * (t * a)⁻¹ = t * (a * c₁ * a⁻¹) * t⁻¹ by group, hC.conj_a_c,
          show t * (z₀ * c₁) * t⁻¹ = (t * z₀ * t⁻¹) * (t * c₁ * t⁻¹) by group, hC.conj_t_c,
          ← hC.d8.z_t, mul_inv_cancel_right]
  have hqC : q ∈ C := hC.Q_le hqQ
  have hcomm : ∀ {y : G}, q * y * q⁻¹ = (g : G) * y * (g : G)⁻¹ →
      q⁻¹ * g * y = y * (q⁻¹ * g) := by
    intro y hy
    have : (g : G) * y = q * y * q⁻¹ * g := by rw [hy]; group
    calc q⁻¹ * g * y = q⁻¹ * ((g : G) * y) := by group
      _ = y * (q⁻¹ * g) := by rw [this]; group
  have hE := hC.cent_E₁ _ (mul_mem (inv_mem hqC) g.2) (hcomm hqv) (hcomm hqc)
  have := mul_mem hqQ (hC.d8.E₁_le_Q hE)
  rwa [mul_inv_cancel_left] at this

theorem ker_rho : hC.rho.ker = (Qd z₀ v t a c₁).subgroupOf C := by
  ext g
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  exact ⟨hC.mem_Q_of_rho_eq_one, hC.rho_eq_one_of_mem_Q⟩

omit [Finite G] in
theorem card_Q_subgroupOf : Nat.card ((Qd z₀ v t a c₁).subgroupOf C) = 32 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe hC.Q_le).toEquiv, hC.d8.card_Q]

theorem card_points : Nat.card (points (E₁d z₀ v c₁) z₀) = 3 := by
  rw [← Nat.card_congr hC.ptEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem rho_surjective : Function.Surjective hC.rho := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup hC.rho.ker
  have h2 : Nat.card hC.rho.ker = 32 := by rw [hC.ker_rho]; exact hC.card_Q_subgroupOf
  rw [hC.card, h2, Nat.card_congr (QuotientGroup.quotientKerEquivRange hC.rho).toEquiv] at h1
  have h6 : Nat.card hC.rho.range = 6 := by omega
  have hP : Nat.card (Equiv.Perm (points (E₁d z₀ v c₁) z₀)) = 6 := by
    rw [Nat.card_perm, hC.card_points]
    rfl
  have : Finite (points (E₁d z₀ v c₁) z₀) :=
    Nat.finite_of_card_ne_zero (by rw [hC.card_points]; norm_num)
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ (h6.trans hP.symm)

@[expose] noncomputable def psi : ↥C →* Equiv.Perm (Fin 3) :=
  (Equiv.permCongrHom hC.ptEquiv.symm).toMonoidHom.comp hC.rho

theorem psi_surjective : Function.Surjective hC.psi :=
  (Equiv.permCongrHom hC.ptEquiv.symm).surjective.comp hC.rho_surjective

theorem ker_psi : hC.psi.ker = (Qd z₀ v t a c₁).subgroupOf C := by
  rw [psi, MonoidHom.ker_comp_of_injective hC.rho _ (Equiv.permCongrHom _).injective,
    hC.ker_rho]

omit [Finite G] in
theorem isPGroup_Q : IsPGroup 2 (Qd z₀ v t a c₁) :=
  IsPGroup.of_card (n := 5) (by rw [hC.d8.card_Q]; rfl)

theorem pCore_eq : CFSG.pCore 2 ↥C = (Qd z₀ v t a c₁).subgroupOf C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine sSup_le fun M ⟨hMn, hM2⟩ => ?_
    have : (M.map hC.psi).Normal := hMn.map hC.psi hC.psi_surjective
    have hbot := CFSG.GH74.M12.Hyp.eq_bot_of_normal_isPGroup_perm_three (M.map hC.psi)
      (hM2.map _)
    rw [← hC.ker_psi]
    intro m hm
    have : hC.psi m ∈ M.map hC.psi := mem_map_of_mem _ hm
    rwa [hbot, mem_bot] at this
  · refine le_sSup ⟨?_, ?_⟩
    · rw [← hC.ker_psi]
      exact MonoidHom.normal_ker _
    · exact hC.isPGroup_Q.comap_subtype

theorem le_normalizer_Q : C ≤ normalizer (Qd z₀ v t a c₁ : Set G) := by
  intro g hg
  have hn : ((Qd z₀ v t a c₁).subgroupOf C).Normal := hC.ker_psi ▸ MonoidHom.normal_ker _
  have hle : (Qd z₀ v t a c₁).map (MulAut.conj g).toMonoidHom ≤ Qd z₀ v t a c₁ := by
    rintro _ ⟨q, hq, rfl⟩
    have h1 := hn.conj_mem ⟨q, hC.Q_le hq⟩ (mem_subgroupOf.mpr hq) ⟨g, hg⟩
    exact mem_subgroupOf.mp h1
  exact mem_normalizer_iff_map_conj_eq.mpr
    (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective]))

omit [Finite G] in
theorem map_conj_K₁_eq {g : G} (hg : g ∈ normalizer (Qd z₀ v t a c₁ : Set G))
    {w : Fin 4 → ZMod 2} (hw : D8D8.HasVec z₀ v t a c₁ (g * (v * t) * g⁻¹) w) (hw1 : inW₁ w) :
    hC.d8.K₁.map (MulAut.conj g).toMonoidHom = hC.d8.K₁ := by
  have hle : hC.d8.K₁.map (MulAut.conj g).toMonoidHom ≤ Qd z₀ v t a c₁ := by
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_normalizer_iff.mp hg k).mp (hC.d8.K₁_le_Q hk)
  obtain ⟨e⟩ := hC.d8.K₁_quaternion
  rcases hC.d8.eq_K₁_or_K₂ hle
      ⟨(hC.d8.K₁.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e⟩ with h1 | h2
  · exact h1
  · exfalso
    have hm : g * (v * t) * g⁻¹ ∈ hC.d8.K₂ := h2 ▸ ⟨v * t, hC.d8.vt_mem_K₁, rfl⟩
    obtain ⟨w', hw', hxw'⟩ := hC.d8.mem_K₂_iff.mp hm
    rw [← hC.d8.hasVec_unique hw hxw'] at hw'
    have key : ∀ w : Fin 4 → ZMod 2, inW₁ w → inW₂ w → w = 0 := by decide
    have hz := (hC.d8.hasVec_mem_zpowers_iff hw).mpr (key w hw1 hw')
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hC.d8.z_sq hz with e | e
    · have : v * t = 1 := by
        have := congrArg (fun x => g⁻¹ * x * g) e
        simpa [mul_assoc] using this
      have hvt := hC.d8.hasVec_mul D8D8.hasVec_v D8D8.hasVec_t
      rw [this] at hvt
      exact absurd (hC.d8.hasVec_unique hvt ⟨0, nf_zero_zero _ _⟩) (by decide)
    · have hsq : (v * t) * (v * t) = z₀ := by
        rw [hC.d8.hasVec_sq (hC.d8.hasVec_mul D8D8.hasVec_v D8D8.hasVec_t),
          show qf cMat (![1, 0, 0, 0] + ![0, 1, 0, 0]) = 1 by decide, val_one_two, pow_one]
      have h3 : g * ((v * t) * (v * t)) * g⁻¹ = 1 := by
        rw [show g * ((v * t) * (v * t)) * g⁻¹ = (g * (v * t) * g⁻¹) * (g * (v * t) * g⁻¹) by
          group, e, hC.d8.z_sq]
      rw [hsq] at h3
      apply hC.d8.z_ne_one
      have := congrArg (fun x => g⁻¹ * x * g) h3
      simpa [mul_assoc] using this

omit [Finite G] in
theorem hasVec_conj_of_comm {g x : G} {w : Fin 4 → ZMod 2} (hx : D8D8.HasVec z₀ v t a c₁ x w)
    (hgQ : g ∈ Qd z₀ v t a c₁) : D8D8.HasVec z₀ v t a c₁ (g * x * g⁻¹) w := by
  have hc := hC.d8.commutator_mem hgQ hx.mem_Q
  obtain ⟨b, hb⟩ := (mem_zpowers_iff_exists hC.d8.rel).mp hc
  have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
  rw [e, ← hb, ← nf_zero_vec z₀ ![v, t, a, c₁] b]
  exact (hC.d8.hasVec_mul ⟨b, rfl⟩ hx).congr (zero_add w)

theorem map_conj_s_K₁ : hC.d8.K₁.map (MulAut.conj s).toMonoidHom = hC.d8.K₁ := by
  have hsv : s * v * s⁻¹ = v := by rw [hC.s_v, mul_inv_cancel_right]
  have e : s * (v * t) * s⁻¹ = (s * v * s⁻¹) * (s * t * s⁻¹) := by group
  have hvt : D8D8.HasVec z₀ v t a c₁ (v * t * a * c₁) ![1, 1, 1, 1] :=
    (hC.d8.hasVec_mul (hC.d8.hasVec_mul (hC.d8.hasVec_mul D8D8.hasVec_v D8D8.hasVec_t)
      D8D8.hasVec_a) D8D8.hasVec_c).congr (by decide)
  have hst : D8D8.HasVec z₀ v t a c₁ (s * t * s⁻¹) ![1, 1, 1, 1] := by
    rcases hC.s_t with h1 | h1 <;> rw [h1]
    · exact hvt
    · exact (hC.d8.hasVec_mul hvt D8D8.hasVec_z).congr (by decide)
  refine hC.map_conj_K₁_eq (hC.le_normalizer_Q hC.s_mem) ?_ (w := ![0, 1, 1, 1]) (by decide)
  rw [e, hsv]
  exact (hC.d8.hasVec_mul D8D8.hasVec_v hst).congr (by decide)

theorem map_conj_Q_K₁ {g : G} (hg : g ∈ Qd z₀ v t a c₁) :
    hC.d8.K₁.map (MulAut.conj g).toMonoidHom = hC.d8.K₁ :=
  hC.map_conj_K₁_eq (hC.le_normalizer_Q (hC.Q_le hg))
    (hC.hasVec_conj_of_comm (hC.d8.hasVec_mul D8D8.hasVec_v D8D8.hasVec_t) hg) (by decide)

omit [Finite G] in
theorem not_mem_Q_of_orderOf_three {x : G} (hx : orderOf x = 3) : x ∉ Qd z₀ v t a c₁ := by
  intro hxQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hC.isPGroup_Q ⟨x, hxQ⟩
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  rw [hx] at h1
  have h2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
  omega

theorem psi_ne_one_of_not_mem_Q {g : ↥C} (hg : (g : G) ∉ Qd z₀ v t a c₁) : hC.psi g ≠ 1 := by
  intro h1
  apply hg
  have : g ∈ hC.psi.ker := h1
  rw [hC.ker_psi] at this
  exact this

theorem K₁_normal : (hC.d8.K₁.subgroupOf C).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Nm : Subgroup ↥C := (normalizer (hC.d8.K₁ : Set G)).subgroupOf C with hNm
  have hmem : ∀ g : ↥C, hC.d8.K₁.map (MulAut.conj (g : G)).toMonoidHom = hC.d8.K₁ → g ∈ Nm :=
    fun g e => mem_subgroupOf.mpr (mem_normalizer_iff_map_conj_eq.mpr e)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 (by rw [hC.card]; norm_num)
  have hyG : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyN : y ∈ Nm := hmem y (hC.d8.map_conj_K₁_of_pow_three (hC.le_normalizer_Q y.2)
    (by rw [← hyG]; exact pow_orderOf_eq_one _))
  have hsN : (⟨s, hC.s_mem⟩ : ↥C) ∈ Nm := hmem _ hC.map_conj_s_K₁
  have hs1 : hC.psi ⟨s, hC.s_mem⟩ ≠ 1 := by
    refine hC.psi_ne_one_of_not_mem_Q fun hsQ => ?_
    have hc := hC.d8.commutator_mem D8D8.c_mem_Q hsQ
    rcases hC.s_c with e | e
    · have hcv : c₁ * s * c₁⁻¹ * s⁻¹ = (s * c₁ * s⁻¹ * c₁⁻¹)⁻¹ := by group
      rw [hcv, e] at hc
      have := inv_mem hc
      rw [inv_inv, mul_inv_cancel_right] at this
      exact hC.v_not_mem this
    · have hcv : c₁ * s * c₁⁻¹ * s⁻¹ = (s * c₁ * s⁻¹ * c₁⁻¹)⁻¹ := by group
      rw [hcv, e] at hc
      have := inv_mem hc
      rw [inv_inv, show v * c₁ * z₀ * c₁⁻¹ = v * (c₁ * z₀ * c₁⁻¹) by group, ← hC.d8.z_c,
        mul_inv_cancel_right] at this
      exact hC.v_not_mem (by simpa using mul_mem this (inv_mem (mem_zpowers z₀)))
  have hs2 : hC.psi ⟨s, hC.s_mem⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨s, hC.s_mem⟩ : ↥C) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [sq, hC.s_sq]
    rw [this, map_one]
  have hy1 : hC.psi y ≠ 1 := hC.psi_ne_one_of_not_mem_Q (hC.not_mem_Q_of_orderOf_three hyG)
  have hy3 : hC.psi y ^ 3 = 1 := by
    have : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
    rw [← map_pow, this, map_one]
  have hNtop : Nm.map hC.psi = ⊤ := by
    have h2 : 2 ∣ Nat.card (Nm.map hC.psi) := by
      have ho : orderOf (⟨hC.psi ⟨s, hC.s_mem⟩, mem_map_of_mem _ hsN⟩ : Nm.map hC.psi) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime hs2 hs1
      have := orderOf_dvd_natCard
        (⟨hC.psi ⟨s, hC.s_mem⟩, mem_map_of_mem _ hsN⟩ : Nm.map hC.psi)
      rwa [ho] at this
    have h3 : 3 ∣ Nat.card (Nm.map hC.psi) := by
      have ho : orderOf (⟨hC.psi y, mem_map_of_mem _ hyN⟩ : Nm.map hC.psi) = 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime hy3 hy1
      have := orderOf_dvd_natCard (⟨hC.psi y, mem_map_of_mem _ hyN⟩ : Nm.map hC.psi)
      rwa [ho] at this
    have h6 : 6 ∣ Nat.card (Nm.map hC.psi) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    have hP : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm, Nat.card_fin]
      rfl
    have hle : Nat.card (Nm.map hC.psi) ≤ 6 := hP ▸ Subgroup.card_le_card_group (Nm.map hC.psi)
    have hpos := Nat.le_of_dvd Nat.card_pos h6
    exact Subgroup.eq_top_of_card_eq _ (by rw [hP]; omega)
  have hNm : Nm = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨n, hn, e⟩ : hC.psi g ∈ Nm.map hC.psi := hNtop ▸ mem_top _
    have hk : n⁻¹ * g ∈ hC.psi.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    rw [hC.ker_psi] at hk
    have hkN : n⁻¹ * g ∈ Nm := hmem _ (hC.map_conj_Q_K₁ (mem_subgroupOf.mp hk))
    have := mul_mem hn hkN
    rwa [mul_inv_cancel_left] at this
  constructor
  intro k hk g
  have hgN : g ∈ Nm := hNm ▸ mem_top g
  rw [mem_subgroupOf] at hk ⊢
  have := (mem_normalizer_iff.mp (mem_subgroupOf.mp hgN) (k : G)).mp hk
  simpa using this

theorem rho_apply_pt (g : ↥C) (i : Fin 3) :
    hC.rho g (hC.ptEquiv i) = hC.ptEquiv (hC.psi g i) := by
  simp [psi, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem centralizer_three {x : ↥C} (hx : orderOf x = 3) {q : ↥C}
    (hq : (q : G) ∈ Qd z₀ v t a c₁) (hxq : x * q = q * x) : (q : G) ∈ zpowers z₀ := by
  have perm3_fpf : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
      ∀ i j : Fin 3, j = i ∨ j = σ i ∨ j = σ (σ i) := by decide
  have perm3_nofix : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → ∀ i, σ i ≠ i := by decide
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  set σ := hC.psi x with hσ
  have hσ1 : σ ≠ 1 := hC.psi_ne_one_of_not_mem_Q (hC.not_mem_Q_of_orderOf_three hxG)
  have hσ3 : σ ^ 3 = 1 := by
    have : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
    rw [hσ, ← map_pow, this, map_one]
  have hxq' : (x : G) * q = q * x := congrArg Subtype.val hxq
  have hzq : (q : G) * z₀ = z₀ * q := hC.z_comm q.2
  have hzx : (x : G) * z₀ = z₀ * x := hC.z_comm x.2
  let Cq : points (E₁d z₀ v c₁) z₀ → Prop := fun U =>
    (U : Subgroup G) ≤ centralizer ({(q : G)} : Set G)
  have hinv : ∀ U, Cq U → Cq (hC.rho x U) := by
    intro U hU
    show (hC.rho x U : Subgroup G) ≤ _
    rw [rho_apply]
    rintro _ ⟨u, hu, rfl⟩
    have hqu : (q : G) * u = u * q := (mem_centralizer_iff.mp (hU hu)) _ rfl
    rw [mem_centralizer_iff]
    rintro _ rfl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hxi : (q : G) * (x : G)⁻¹ = (x : G)⁻¹ * q := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hxq', mul_inv_cancel_right]
    calc (q : G) * ((x : G) * u * (x : G)⁻¹) = (x : G) * ((q : G) * u) * (x : G)⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, ← hxq', mul_assoc (x : G) (q : G) u]
      _ = (x : G) * u * ((q : G) * (x : G)⁻¹) := by rw [hqu]; group
      _ = (x : G) * u * (x : G)⁻¹ * q := by rw [hxi]; group
  have hCq_pt : ∀ {e : G} (i : Fin 3), ((hC.pt i : points _ _) : Subgroup G) = ptOf z₀ e →
      (q : G) * e = e * q → Cq (hC.ptEquiv i) := by
    intro e i hi hqe
    show ((hC.pt i : points _ _) : Subgroup G) ≤ _
    rw [hi]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_iff]
      rintro _ rfl
      exact hzq
    · rw [mem_centralizer_iff]
      rintro _ rfl
      exact hqe
  have hcomm_of : ∀ {e : G}, (q : G) * e * (q : G)⁻¹ * e⁻¹ = 1 → (q : G) * e = e * q := by
    intro e he
    calc (q : G) * e = (q : G) * e * (q : G)⁻¹ * e⁻¹ * e * q := by group
      _ = e * q := by rw [he, one_mul]
  have hsome : ∃ i, Cq (hC.ptEquiv i) := by
    have hv := hC.d8.commutator_mem hq D8D8.v_mem_Q
    have hc := hC.d8.commutator_mem hq D8D8.c_mem_Q
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hC.d8.z_sq hv with ev | ev
    · exact ⟨0, hCq_pt 0 rfl (hcomm_of ev)⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hC.d8.z_sq hc with ec | ec
    · exact ⟨1, hCq_pt 1 rfl (hcomm_of ec)⟩
    refine ⟨2, hCq_pt 2 rfl (hcomm_of ?_)⟩
    have e1 : (q : G) * v * (q : G)⁻¹ = z₀ * v := by
      rw [← ev]; group
    have e2 : (q : G) * c₁ * (q : G)⁻¹ = z₀ * c₁ := by
      rw [← ec]; group
    calc (q : G) * (v * c₁) * (q : G)⁻¹ * (v * c₁)⁻¹ =
        ((q : G) * v * (q : G)⁻¹) * ((q : G) * c₁ * (q : G)⁻¹) * (v * c₁)⁻¹ := by group
      _ = z₀ * v * (z₀ * c₁) * (v * c₁)⁻¹ := by rw [e1, e2]
      _ = v * (z₀ * z₀) * c₁ * (v * c₁)⁻¹ := by
          rw [show z₀ * v * (z₀ * c₁) = (z₀ * v) * z₀ * c₁ by group, hC.d8.z_v]; group
      _ = 1 := by rw [hC.d8.z_sq]; group
  obtain ⟨i₀, hi₀⟩ := hsome
  have hall : ∀ j, Cq (hC.ptEquiv j) := by
    intro j
    rcases perm3_fpf σ hσ3 hσ1 i₀ j with rfl | rfl | rfl
    · exact hi₀
    · rw [← rho_apply_pt]
      exact hinv _ hi₀
    · rw [← rho_apply_pt, ← rho_apply_pt]
      exact hinv _ (hinv _ hi₀)
  have hqv : (q : G) * v = v * q := by
    have h0 : v ∈ ((hC.pt 0 : points _ _) : Subgroup G) := mem_sup_right (mem_zpowers v)
    exact ((mem_centralizer_iff.mp (hall 0 h0)) _ rfl)
  have hqc : (q : G) * c₁ = c₁ * q := by
    have h1 : c₁ ∈ ((hC.pt 1 : points _ _) : Subgroup G) := mem_sup_right (mem_zpowers c₁)
    exact ((mem_centralizer_iff.mp (hall 1 h1)) _ rfl)
  have hqE : (q : G) ∈ E₁d z₀ v c₁ := hC.cent_E₁ q q.2 hqv hqc
  by_contra hnz
  set U' : points (E₁d z₀ v c₁) z₀ := ⟨ptOf z₀ q, hC.ptOf_mem hqE hnz⟩ with hU'
  have hfix : hC.rho x U' = U' := by
    apply Subtype.ext
    rw [rho_apply, hU']
    show (zpowers z₀ ⊔ zpowers (q : G)).map (MulAut.conj (x : G)).toMonoidHom =
      zpowers z₀ ⊔ zpowers (q : G)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hzx, hxq', mul_inv_cancel_right, mul_inv_cancel_right]
  obtain ⟨i, hi⟩ := hC.ptEquiv.surjective U'
  refine perm3_nofix σ hσ3 hσ1 i (hC.ptEquiv.injective ?_)
  rw [← rho_apply_pt, hi, hfix]

@[expose] def zC : ↥C := ⟨z₀, hC.Q_le D8D8.z_mem_Q⟩

theorem localHyp : CFSG.GH74.M12.Hyp.LocalHyp ↥C hC.zC where
  card_eq := hC.card
  card_core := by rw [hC.pCore_eq]; exact hC.card_Q_subgroupOf
  extraspecial := by
    rw [hC.pCore_eq]
    exact CFSG.GH74.M12.Hyp.isExtraspecial_of_mulEquiv (subgroupOfEquivOfLe hC.Q_le).symm
      hC.d8.isExtraspecial_Q
  quotient_S3 := ⟨(QuotientGroup.quotientMulEquivOfEq (hC.pCore_eq.trans hC.ker_psi.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective hC.psi hC.psi_surjective)⟩
  centralizer_X := by
    intro x hx q hq hxq
    rw [hC.pCore_eq, mem_subgroupOf] at hq
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hC.centralizer_three hx hq hxq)
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [zC] using hk)⟩

theorem q8 : ∃ K ∈ CFSG.GH74.M12.q8Subgroups (CFSG.pCore 2 ↥C), K.Normal := by
  have hK₁C : hC.d8.K₁ ≤ C := hC.d8.K₁_le_Q.trans hC.Q_le
  obtain ⟨e⟩ := hC.d8.K₁_quaternion
  refine ⟨hC.d8.K₁.subgroupOf C, ⟨?_, ⟨(subgroupOfEquivOfLe hK₁C).trans e⟩⟩, hC.K₁_normal⟩
  rw [hC.pCore_eq]
  intro x hx
  exact mem_subgroupOf.mpr (hC.d8.K₁_le_Q (mem_subgroupOf.mp hx))

end CentHyp

@[expose] def centEquiv (X : Subgroup G) {z : G} (hz : z ∈ X) :
    ↥(X ⊓ centralizer ({z} : Set G)) ≃* ↥(centralizer ({(⟨z, hz⟩ : X)} : Set X)) where
  toFun g := ⟨⟨g, g.2.1⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp g.2.2))⟩
  invFun g := ⟨g.1.1, g.1.2, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp g.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end IIbM12

end CFSG.ComponentClassification.RankTwoAltFive

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup IIbM12

variable {G : Type} [Group G] [Finite G]

structure IIbCz0 (X : Subgroup G) (z₀ v a c₁ t s : G) : Prop where
  d8 : D8D8 z₀ v t a c₁
  z₀_mem : z₀ ∈ X
  v_mem : v ∈ X
  a_mem : a ∈ X
  c₁_mem : c₁ ∈ X
  t_mem : t ∈ X
  s_mem : s ∈ X
  s_sq : s * s = 1
  s_z₀ : s * z₀ = z₀ * s
  s_v : s * v = v * s
  s_a : s * a * s⁻¹ = v * a ∨ s * a * s⁻¹ = v * a * z₀
  s_c₁ : s * c₁ * s⁻¹ = v * c₁ ∨ s * c₁ * s⁻¹ = v * c₁ * z₀
  s_t : s * t * s⁻¹ = v * t * a * c₁ ∨ s * t * s⁻¹ = v * t * a * c₁ * z₀
  fusion : ∃ g ∈ X, g * z₀ * g⁻¹ = v
  E₁_normal : ∀ g ∈ X, g * z₀ = z₀ * g →
    g * v * g⁻¹ ∈ closure ({z₀, v, c₁} : Set G) ∧ g * c₁ * g⁻¹ ∈ closure ({z₀, v, c₁} : Set G)
  centralizer_E₁ : ∀ g ∈ X, g * z₀ = z₀ * g → g * v = v * g → g * c₁ = c₁ * g →
    g ∈ closure ({z₀, v, c₁} : Set G)
  card : Nat.card ↥(X ⊓ centralizer ({z₀} : Set G)) = 192

namespace IIbCz0

variable {X : Subgroup G} {z₀ v a c₁ t s : G} (h : IIbCz0 X z₀ v a c₁ t s)
include h

omit [Finite G] in
theorem centHyp : CentHyp (X ⊓ centralizer ({z₀} : Set G)) z₀ v t a c₁ s where
  d8 := h.d8
  le_cent := inf_le_right
  Q_le := by
    rw [closure_le]
    rintro x (rfl | ⟨i, rfl⟩)
    · exact ⟨h.z₀_mem, mem_centralizer_singleton_iff.mpr rfl⟩
    · fin_cases i
      · exact ⟨h.v_mem, mem_centralizer_singleton_iff.mpr h.d8.z_v.symm⟩
      · exact ⟨h.t_mem, mem_centralizer_singleton_iff.mpr h.d8.z_t.symm⟩
      · exact ⟨h.a_mem, mem_centralizer_singleton_iff.mpr h.d8.z_a.symm⟩
      · exact ⟨h.c₁_mem, mem_centralizer_singleton_iff.mpr h.d8.z_c.symm⟩
  E₁_normal g hg := h.E₁_normal g hg.1 (mem_centralizer_singleton_iff.mp hg.2)
  cent_E₁ g hg hv hc := h.centralizer_E₁ g hg.1 (mem_centralizer_singleton_iff.mp hg.2) hv hc
  card := h.card
  s_mem := ⟨h.s_mem, mem_centralizer_singleton_iff.mpr h.s_z₀⟩
  s_sq := h.s_sq
  s_v := h.s_v
  s_a := h.s_a
  s_c := h.s_c₁
  s_t := h.s_t

theorem asc03Hyp : CFSG.GH74.M12.Asc03Hyp ↥X ⟨z₀, h.z₀_mem⟩ ∧
    ∃ K ∈ CFSG.GH74.M12.q8Subgroups
      (CFSG.pCore 2 ↥(centralizer ({(⟨z₀, h.z₀_mem⟩ : X)} : Set X))), K.Normal := by
  have hC := h.centHyp
  set e := centEquiv X h.z₀_mem with he
  have hze : e hC.zC = CFSG.GH74.M12.Hyp.zElt' (⟨z₀, h.z₀_mem⟩ : X) := rfl
  have hloc := hC.localHyp.of_mulEquiv e hze
  have hord : orderOf (⟨z₀, h.z₀_mem⟩ : X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact h.d8.z_sq) h.d8.z_ne_one
  refine ⟨CFSG.GH74.M12.Hyp.asc03Hyp_of_local _ hord hloc ?_,
    CFSG.GH74.M12.Hyp.exists_q8_normal_of_mulEquiv e hC.q8⟩
  obtain ⟨g, hgX, hgv⟩ := h.fusion
  have hvQ : v ∈ Qd z₀ v t a c₁ := D8D8.v_mem_Q
  have hvC : v ∈ X ⊓ centralizer ({z₀} : Set G) := hC.Q_le hvQ
  have hvp : (⟨v, hvC⟩ : ↥(X ⊓ centralizer ({z₀} : Set G))) ∈
      CFSG.pCore 2 ↥(X ⊓ centralizer ({z₀} : Set G)) := by
    rw [hC.pCore_eq]
    exact mem_subgroupOf.mpr hvQ
  have hvp' : e ⟨v, hvC⟩ ∈ CFSG.pCore 2 ↥(centralizer ({(⟨z₀, h.z₀_mem⟩ : X)} : Set X)) := by
    rw [← CFSG.pCore_map_iso 2 e]
    exact mem_map_of_mem _ hvp
  refine ⟨⟨g, hgX⟩, ?_, e ⟨v, hvC⟩, hvp', Subtype.ext ?_⟩
  · intro e'
    have e'' : g * z₀ * g⁻¹ = z₀ := congrArg Subtype.val e'
    rw [hgv] at e''
    have hv : D8D8.HasVec z₀ v t a c₁ v ![1, 0, 0, 0] := D8D8.hasVec_v
    have hz : D8D8.HasVec z₀ v t a c₁ v 0 := by
      obtain ⟨b, hb⟩ := (D8D8.hasVec_z : D8D8.HasVec z₀ v t a c₁ z₀ 0)
      exact ⟨b, hb.trans e''.symm⟩
    exact absurd (h.d8.hasVec_unique hv hz) (by decide)
  · exact hgv.symm

theorem isSporadic_M12
    (hX : IsSimpleGroup ↥X) :
    CFSG.Blueprint.NativeSporadic.IsSporadic ↥X .M12 :=
  CFSG.GH74.M12.s_asc03_simple ↥X hX _ h.asc03Hyp.1 h.asc03Hyp.2

end IIbCz0

end CFSG.ComponentClassification.RankTwoAltFive
