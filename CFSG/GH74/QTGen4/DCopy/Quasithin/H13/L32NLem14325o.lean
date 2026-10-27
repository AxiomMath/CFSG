module

public import CFSG.Quasithin.H13.L32NLem14325o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch10.SecF

namespace L14325

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace CtxI.TransData

variable {C : CtxI G T L V V₂ g D} {x c : G} (X : TransData C x c)
include X

theorem false_F4 (h64 : G64.LemmaG64) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) : False := by
  have := L14332.finite_linearEquiv D
  obtain ⟨_, S⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 C.ctx.hyp C.ctx.plane
  have hU : conjClosure V₂ (l32nH T V) = fsuU T V := (lemma12_8_8_six_F4 h1222 C.ctx.setting).symm
  have hT : QuasithinUnique.IsSylowTwoOf T (l32nH T V) :=
    C.ctx.hyp.isSylowTwoOf_l32nH_F4 (stmtL32NModule_of_inputs_F4 h1332 h1334)
  have hVZ : V ⊓ centerOf (fsuU T V) = fsuV1 T V := lemma12_8_8_three_F4 h1222 h12213 C.ctx.setting
  have hE : ∀ k ∈ l32nH T V, ∀ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨k, hkN⟩ = 1 → ∀ u ∈ fsuU T V, k * u * k⁻¹ * u⁻¹ ∈ nK T V g :=
    fun k hkH hkN h1 u hu => X.cHat_U h64 hT hU ((L14332.rho_eq_one_iff_mem hkH hkN).mp h1) hu

  obtain ⟨z, a, b, hz, hz1, haV₂, ha1, hbV, hbV₂⟩ := S.exists_basis_F4
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := C.ctx.plane.2 hz
  have haV : a ∈ V := C.ctx.plane.1.1 haV₂
  obtain ⟨r, hrL, hr3, hrz, hra, hrb⟩ := S.exists_rot_F4 hzV haV hbV
    (fun h => ha1 (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => ha1 (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ haV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ haV₂))
  have hrH : r ∈ l32nH T V := S.mem_g1_F4 hz hz1 hrz
  have hrL₁ : r ∈ lOne L (fsuV1 T V) := by
    rw [lOne_eq_L₁Of]
    exact Subgroup.subset_closure ⟨⟨hrL, hrH⟩, 3, by decide, hr3⟩
  have hrN : r ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V hrH
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = D.ρ ⟨r, hrN⟩ := ⟨_, rfl⟩

  have hγ1 : γ ≠ 1 := by
    intro h1
    have hra' := hE r hrH hrN (hγ ▸ h1) a (C.ctx.V_U haV)
    rw [hra] at hra'
    have hba : b * a⁻¹ ∈ fsuV1 T V := by
      rw [← hVZ]
      exact ⟨V.mul_mem hbV (V.inv_mem haV), hra'.1⟩
    apply hbV₂
    have : b * a⁻¹ * a ∈ V₂ := V₂.mul_mem (C.ctx.plane.2 hba) haV₂
    rwa [inv_mul_cancel_right] at this
  have hγ3 : γ ^ 3 = 1 := by
    rw [hγ, ← map_pow]
    have : (⟨r, hrN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hr3)
    rw [this, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hγL : γ ∈ D.img (lOne L (fsuV1 T V)) := hγ ▸ L128A.HatU.rho_mem_img D hrL₁ hrN
  have hL₁ : D.img (lOne L (fsuV1 T V)) = Subgroup.zpowers γ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hγL) ?_).symm
    rw [Nat.card_zpowers, hord]
    exact Nat.le_of_dvd (by norm_num) (L14332.card_img_lOne_dvd_three_F4 S C.hi)

  have hxdich : ∀ h ∈ l32nH T V, ∃ k ∈ l32nH T V,
      (∀ u ∈ fsuU T V, k * u * k⁻¹ * u⁻¹ ∈ nK T V g) ∧
      (h⁻¹ * r * h = k * r ∨ h⁻¹ * r * h = k * r⁻¹) := by
    intro h hh
    have hhN := L14332.l32nH_le_normalizer_fsuU T V hh
    have hyH : h⁻¹ * r * h ∈ l32nH T V := mul_mem (mul_mem (inv_mem hh) hrH) hh
    have hyN := L14332.l32nH_le_normalizer_fsuU T V hyH
    have hρy : D.ρ ⟨h⁻¹ * r * h, hyN⟩ = (D.ρ ⟨h, hhN⟩)⁻¹ * γ * (D.ρ ⟨h, hhN⟩)⁻¹⁻¹ := by
      rw [inv_inv, hγ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hyL : D.ρ ⟨h⁻¹ * r * h, hyN⟩ ∈ Subgroup.zpowers γ := by
      rw [← hL₁, hρy]
      exact (Subgroup.mem_normalizer_iff.mp (C.l1_normal ((D.img (l32nH T V)).inv_mem
        (L128A.HatU.rho_mem_img D hh hhN))) γ).mp hγL
    have hy1 : D.ρ ⟨h⁻¹ * r * h, hyN⟩ ≠ 1 := by
      intro h1
      rw [hρy, inv_inv] at h1
      apply hγ1
      calc γ = D.ρ ⟨h, hhN⟩ * ((D.ρ ⟨h, hhN⟩)⁻¹ * γ * D.ρ ⟨h, hhN⟩) * (D.ρ ⟨h, hhN⟩)⁻¹ := by
            group
        _ = 1 := by rw [h1]; group
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hyL
    obtain ⟨j, hj, hjy⟩ := hyL
    rw [Finset.mem_range] at hj
    have hk1 : h⁻¹ * r * h * r⁻¹ ∈ l32nH T V := mul_mem hyH (inv_mem hrH)
    have hk2 : h⁻¹ * r * h * r ∈ l32nH T V := mul_mem hyH hrH
    interval_cases j
    · exact absurd (hjy.symm.trans (pow_zero γ)) hy1
    · refine ⟨h⁻¹ * r * h * r⁻¹, hk1,
        hE _ hk1 (L14332.l32nH_le_normalizer_fsuU T V hk1) ?_, Or.inl (by group)⟩
      have e : (⟨h⁻¹ * r * h * r⁻¹, L14332.l32nH_le_normalizer_fsuU T V hk1⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h⁻¹ * r * h, hyN⟩ * ⟨r, hrN⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, ← hγ, ← hjy, pow_one, mul_inv_cancel]
    · refine ⟨h⁻¹ * r * h * r, hk2,
        hE _ hk2 (L14332.l32nH_le_normalizer_fsuU T V hk2) ?_, Or.inr (by group)⟩
      have e : (⟨h⁻¹ * r * h * r, L14332.l32nH_le_normalizer_fsuU T V hk2⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h⁻¹ * r * h, hyN⟩ * ⟨r, hrN⟩ := rfl
      rw [e, map_mul, ← hγ, ← hjy, ← pow_succ]
      exact hγ3

  have hidx : (fsuV1 T V).relIndex V₂ = 2 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V₂)
    rw [inf_eq_left.mpr C.ctx.plane.2, C.ctx.card_V1, C.ctx.plane.1.2.1] at this
    omega
  have hV₂c : ∀ v ∈ V₂, v ∈ fsuV1 T V ∨ ∃ c' ∈ fsuV1 T V, v = a * c' := by
    intro v hv
    by_cases hv1 : v ∈ fsuV1 T V
    · exact Or.inl hv1
    right
    have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a⁻¹, V₂.inv_mem haV₂⟩)
      (b := ⟨v, hv⟩)).mpr (iff_of_false (fun hm => ha1 (by
        have := (fsuV1 T V).inv_mem (Subgroup.mem_subgroupOf.mp hm)
        rwa [inv_inv] at this)) (fun hm => hv1 (Subgroup.mem_subgroupOf.mp hm)))
    exact ⟨a⁻¹ * v, Subgroup.mem_subgroupOf.mp hm, by group⟩
  have hV : ∀ v ∈ V₂, v * (r * v * r⁻¹) * (r * r * v * (r * r)⁻¹) ∈ nK T V g := by
    intro v hv
    refine C.V1_le_nK ?_
    rcases hV₂c v hv with hv1 | ⟨c', hc', rfl⟩
    · rw [C.H_V1 hrH hv1, C.H_V1 ((l32nH T V).mul_mem hrH hrH) hv1,
        S.mul_self_V_F4 (Subgroup.mem_inf.mp hv1).1, one_mul]
      exact hv1
    · have hcV : c' ∈ V := (Subgroup.mem_inf.mp hc').1
      have hrc := C.H_V1 hrH hc'
      have e1 : r * (a * c') * r⁻¹ = b * c' := by
        rw [show r * (a * c') * r⁻¹ = (r * a * r⁻¹) * (r * c' * r⁻¹) by group, hra, hrc]
      have e2 : r * r * (a * c') * (r * r)⁻¹ = a * b * c' := by
        rw [show r * r * (a * c') * (r * r)⁻¹ = r * (r * (a * c') * r⁻¹) * r⁻¹ by group, e1,
          show r * (b * c') * r⁻¹ = (r * b * r⁻¹) * (r * c' * r⁻¹) by group, hrb, hrc]
      have hcb : c' * b = b * c' := S.comm_V_F4 hcV hbV
      have e3 : a * c' * (b * c') * (a * b * c') = c' := by
        calc a * c' * (b * c') * (a * b * c') = a * (c' * b) * c' * (a * b * c') := by group
          _ = a * (b * c') * c' * (a * b * c') := by rw [hcb]
          _ = a * b * (c' * c') * (a * b * c') := by group
          _ = a * b * (a * b) * c' := by rw [S.mul_self_V_F4 hcV, mul_one]; group
          _ = c' := by rw [S.mul_self_V_F4 (mul_mem haV hbV), one_mul]
      rw [e1, e2, e3]
      exact hc'

  have hLK : ∀ δ ∈ D.img (lOne L (fsuV1 T V)), δ ∈ D.img (kI T V g) → δ = 1 := by
    intro δ hδL hδK
    by_contra hδ1
    apply C.not_lOne_le
    rw [hL₁, Subgroup.zpowers_le]
    rw [hL₁] at hδL
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδL
    have hδ3 : (γ ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hγ3, one_zpow]
    have hoδ : orderOf (γ ^ k) = 3 := orderOf_eq_prime hδ3 hδ1
    have heq : Subgroup.zpowers (γ ^ k) = Subgroup.zpowers γ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers γ k))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hoδ, hord])
    have hγδ : γ ∈ Subgroup.zpowers (γ ^ k) := heq ▸ Subgroup.mem_zpowers γ
    exact Subgroup.zpowers_le.mpr hδK hγδ

  have hrP : r ∈ Subgroup.centralizer (vP T V c : Set G) := by
    refine X.cent_of_comm hrH fun h' hh' => ?_
    have hx'K := X.conj_x_mem hh'
    have hrx'K : r * (h' * x * h'⁻¹) * r⁻¹ ∈ kI T V g :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_kI hrH) _).mp hx'K
    have hqK : r * (h' * x * h'⁻¹) * r⁻¹ * (h' * x * h'⁻¹)⁻¹ ∈ kI T V g :=
      (kI T V g).mul_mem hrx'K ((kI T V g).inv_mem hx'K)
    refine X.cent_of_hat h64 hqK ?_
    have hqN := L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hqK)
    refine (L14332.rho_eq_one_iff_mem (D := D) (C.kI_le hqK) hqN).mp ?_
    have hx'N := L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hx'K)
    have hρq : D.ρ ⟨_, hqN⟩ = γ * D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ * γ⁻¹ *
        (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩)⁻¹ := by
      have e1 : (⟨r * (h' * x * h'⁻¹) * r⁻¹ * (h' * x * h'⁻¹)⁻¹, hqN⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) =
          ⟨r, hrN⟩ * ⟨h' * x * h'⁻¹, hx'N⟩ * ⟨r, hrN⟩⁻¹ * ⟨h' * x * h'⁻¹, hx'N⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, ← hγ]
    rw [hρq]
    have hκK := L128A.HatU.rho_mem_img D hx'K hx'N
    have hκH : D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ ∈ D.img (l32nH T V) :=
      L128A.HatU.rho_mem_img D (C.kI_le hx'K) hx'N
    have hγH : γ ∈ D.img (l32nH T V) := by
      rw [hγ]
      exact L128A.HatU.rho_mem_img D hrH hrN
    refine hLK _ ?_ ?_
    · have h1 := (Subgroup.mem_normalizer_iff.mp (C.l1_normal hκH) _).mp
        ((D.img (lOne L (fsuV1 T V))).inv_mem hγL)
      have h2 := (D.img (lOne L (fsuV1 T V))).mul_mem hγL h1
      have e2 : γ * (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ * γ⁻¹ * (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩)⁻¹) =
          γ * D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ * γ⁻¹ * (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩)⁻¹ := by group
      rwa [e2] at h2
    · exact (D.img (kI T V g)).mul_mem (C.img_kI_normal hγH hκK)
        ((D.img (kI T V g)).inv_mem hκK)

  have hrc : r * c * r⁻¹ * c⁻¹ = 1 := by
    have := Subgroup.mem_centralizer_iff.mp hrP c (c_mem_vP c)
    calc r * c * r⁻¹ * c⁻¹ = c * r * r⁻¹ * c⁻¹ := by rw [this]
      _ = 1 := by group
  have hcN := mem_of_norm' (N₀ := nK T V g) (V₂ := V₂) C.ctx.U_le
    (L14332.l32nH_le_normalizer_fsuU T V) (fun h hh n hn => conj_mem_nK hh hn)
    (fun u hu v hv => C.V1_le_nK (C.comm u hu v hv)) hU hrH hr3 hxdich hV
    (C.ctx.vH_le X.c_mem).1 (by rw [hrc]; exact one_mem _)
    (by rw [C.vH_sq X.c_mem]; exact one_mem _)
  exact X.c_ne (X.eq_one_of_cent h64 (c_mem_vP c) fun k hk => by
    have := Subgroup.mem_centralizer_iff.mp hcN.2 k hk
    calc k * c * k⁻¹ = c * k * k⁻¹ := by rw [this]
      _ = c := by group)

end CtxI.TransData

theorem Ctx14325.not_case_i_F4 (C : Ctx14325 G T L V V₂ g D) (h64 : G64.LemmaG64)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hi : Case14323i T L V g D) : False := by
  obtain ⟨x, c, X⟩ := (exists_ctxI_F4 h1332 h1334 h1222 h12213 h12810 C hd hi).exists_transData
  exact X.false_F4 h64 h1332 h1334 h1222 h12213

end L14325

end CFSG.Quasithin.H13
