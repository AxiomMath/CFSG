module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAQ
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM3
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8ACase

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7 Sec8

theorem card_H8 : Nat.card H8 = 32 := by
  have hbij : Function.Bijective
      (fun q : (ZMod 8)ˣ × ZMod 8 => (⟨aff8 q.1 q.2, aff8_mem_H8 _ _⟩ : H8)) := by
    refine ⟨fun q q' h => ?_, fun ⟨g, hg⟩ => ?_⟩
    · have h' := aff8_injective (congrArg Subtype.val h)
      exact Prod.ext h'.1 h'.2
    · obtain ⟨u, b, rfl⟩ := hg
      exact ⟨(u, b), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

omit [Finite X] in
include C in
theorem card_T_le : Nat.card A.T ≤ 64 := by
  rw [A.card_T_eq, C.card_K]
  have := Subgroup.card_le_of_le A.range_le_H8
  rw [card_H8] at this
  omega

theorem dc_t (e : Bool) (c₂ : MA) : dc e c₂ MA.t = MA.t := (dAct_gens _ _ _).2.2.2.2.2.1

theorem dc_y (e : Bool) (c₂ : MA) : dc e c₂ MA.y = MA.u := (dAct_gens _ _ _).2.2.2.2.1

theorem dc_k (e : Bool) (c₂ : MA) : dc e c₂ MA.k = MA.z * MA.k := (dAct_gens _ _ _).2.2.2.2.2.2

theorem dc_z (e : Bool) (c₂ : MA) : dc e c₂ MA.z = MA.z := (dAct_gens _ _ _).2.2.2.1

namespace AD

namespace TD

variable {H : AD S T₁} (T : H.TD)

theorem ι_tE_inv : (H.ι (tE T.e))⁻¹ = H.ι (tE T.e) := by rw [← map_inv, tE_inv]

theorem conj_inv {a : MA} (ha : MA.inT1 a = true) :
    H.ι (dci T.e T.c₂ a) = T.d⁻¹ * H.ι a * T.d := by
  have h1 := T.conj a ha
  have e1 : H.ι (tE T.e) = (T.d * T.d)⁻¹ := by rw [T.sq, T.ι_tE_inv]
  have e2 : H.ι (tE T.e) = T.d * T.d := T.sq.symm
  rw [dci, map_mul, map_mul, h1]
  nth_rewrite 1 [e1]
  rw [e2]
  group

theorem d_conj_t : T.d * t * T.d⁻¹ = t := by
  have h := T.conj MA.t (by decide +kernel)
  rw [dc_t, H.ι_t] at h
  exact h.symm

theorem d_comm_t : T.d * t = t * T.d := by
  calc T.d * t = (T.d * t * T.d⁻¹) * T.d := by group
    _ = t * T.d := by rw [T.d_conj_t]

@[expose] noncomputable def p : X := T.d * H.ι MA.w₂ * T.d⁻¹

theorem p_mul_p : T.p * T.p = 1 := by
  rw [p, show T.d * H.ι MA.w₂ * T.d⁻¹ * (T.d * H.ι MA.w₂ * T.d⁻¹) =
    T.d * (H.ι MA.w₂ * H.ι MA.w₂) * T.d⁻¹ by group, H.w₂_mul_w₂]; group

theorem p_inv : T.p⁻¹ = T.p := inv_eq_of_mul_eq_one_right T.p_mul_p

theorem p_conj_ι {a : MA} (ha : MA.inT1 a = true) :
    T.p * H.ι a * T.p⁻¹ = H.ι (pAct T.e T.c₂ a) := by
  have h1 := T.conj_inv ha
  have h2 : MA.inT1 (MA.w₂ * dci T.e T.c₂ a * MA.w₂⁻¹) = true :=
    MA.T1_normal _ _ (dci_T1 T.e T.c₂ T.hc₂ a)
  rw [pAct, T.conj _ h2, map_mul, map_mul, map_inv, h1, p]
  group

theorem p_conj_t : T.p * t * T.p⁻¹ = H.ι (MA.t * MA.u) := by
  have h := T.p_conj_ι (a := MA.t) (by decide +kernel)
  rwa [H.ι_t, (actsW_pAct T.e T.c₂ T.hc₂).1] at h

theorem p_not_mem_S₁ : T.p ∉ H.G.D₁.S₁ := by
  intro h
  obtain ⟨s, hs⟩ := H.mem_range_of_mem_S₁ h
  apply MA.not_conj_t_tu s
  apply H.ι_injective
  rw [map_mul, map_mul, map_inv, hs, H.ι_t, T.p_conj_t]

theorem d_conj_p : T.d * T.p * T.d⁻¹ = H.ι (tE T.e * MA.w₂ * tE T.e) := by
  rw [p, map_mul, map_mul]
  nth_rewrite 2 [← T.ι_tE_inv]
  rw [← T.sq]
  group

@[expose] noncomputable def R₂ : Subgroup X := H.G.D₁.S₁ ⊔ zpowers T.p

theorem S₁_le_R₂ : H.G.D₁.S₁ ≤ T.R₂ := le_sup_left

theorem p_mem_R₂ : T.p ∈ T.R₂ := mem_sup_right (mem_zpowers _)

theorem ι_mem_R₂ (a : MA) : H.ι a ∈ T.R₂ := T.S₁_le_R₂ (H.ι_mem_S₁ a)

theorem p_mem_normalizer : T.p ∈ normalizer (H.G.D₁.S₁ : Set X) := T.hp

theorem p_sq : T.p ^ 2 = 1 := by rw [pow_two, T.p_mul_p]

theorem isPGroup_R₂ : IsPGroup 2 T.R₂ :=
  IsPGroup.to_sup_of_normal_left' H.G.D₁.isPGroup_S₁
    (isPGroup_zpowers_of_pow (a := 1) (by rw [pow_one]; exact T.p_sq))
    (zpowers_le.mpr T.p_mem_normalizer)

theorem mem_R₂ {g : X} (hg : g ∈ T.R₂) : g ∈ H.G.D₁.S₁ ∨ g * T.p⁻¹ ∈ H.G.D₁.S₁ :=
  Sec7.mem_or_of_mem_sup_zpowers T.p_mem_normalizer (by rw [T.p_sq]; exact one_mem _) hg

theorem mem_S₁_of_comm_t {g : X} (hg : g ∈ T.R₂) (hgt : g * t = t * g) :
    g ∈ H.G.D₁.S₁ := by
  rcases T.mem_R₂ hg with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs⟩ := H.mem_range_of_mem_S₁ h
    have hg' : g = H.ι s * T.p := by rw [hs]; group
    apply (not_conj_tu_zt s).1
    apply H.ι_injective
    rw [map_mul, map_mul, map_inv, ← T.p_conj_t, H.ι_t]
    calc H.ι s * (T.p * t * T.p⁻¹) * (H.ι s)⁻¹ = g * t * g⁻¹ := by rw [hg']; group
      _ = t := by rw [hgt, mul_inv_cancel_right]

theorem d_mem_normalizer_R₂ : T.d ∈ normalizer (T.R₂ : Set X) := by
  refine mem_normalizer_of_conj_le fun g hg => ?_
  have hle : T.R₂ ≤ T.R₂.comap (MulAut.conj T.d).toMonoidHom := by
    refine sup_le ?_ (zpowers_le.mpr ?_)
    · rw [← H.range_ι, MonoidHom.range_eq_map, ← map_le_iff_le_comap, map_map,
        ← MonoidHom.range_eq_map]
      refine MA.range_le _ fun a ha => ?_
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      simp only [MA.gens, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact T.p_mem_R₂
      all_goals rw [← T.conj _ (by decide +kernel)]; exact T.ι_mem_R₂ _
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [T.d_conj_p]; exact T.ι_mem_R₂ _
  exact hle hg

theorem d_sq_mem_R₂ : T.d * T.d ∈ T.R₂ := by rw [T.sq]; exact T.ι_mem_R₂ _

theorem d_not_mem_R₂ : T.d ∉ T.R₂ := by
  intro h
  obtain ⟨s, hs⟩ := H.mem_range_of_mem_S₁ (T.mem_S₁_of_comm_t h T.d_comm_t)
  have hst : s * MA.t = MA.t * s := by
    apply H.ι_injective
    rw [map_mul, map_mul, hs, H.ι_t, T.d_comm_t]
  apply not_conj_y_u s hst
  apply H.ι_injective
  have h1 := T.conj MA.y (by decide +kernel)
  rw [dc_y] at h1
  rw [map_mul, map_mul, map_inv, hs, ← h1]

@[expose] noncomputable def T₂ : Subgroup X := T.R₂ ⊔ zpowers T.d

theorem R₂_le_T₂ : T.R₂ ≤ T.T₂ := le_sup_left

theorem d_mem_T₂ : T.d ∈ T.T₂ := mem_sup_right (mem_zpowers _)

theorem d_pow_four : T.d ^ 4 = 1 := by
  calc T.d ^ 4 = (T.d * T.d) * (T.d * T.d) := by
        rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one]; group
    _ = 1 := by rw [T.sq, ← map_mul, tE_mul_tE, map_one]

theorem isPGroup_T₂ : IsPGroup 2 T.T₂ :=
  IsPGroup.to_sup_of_normal_left' T.isPGroup_R₂
    (isPGroup_zpowers_of_pow (a := 2) (by rw [show (2 : ℕ) ^ 2 = 4 from rfl]; exact
      T.d_pow_four))
    (zpowers_le.mpr T.d_mem_normalizer_R₂)

theorem mem_T₂ {g : X} (hg : g ∈ T.T₂) : g ∈ T.R₂ ∨ g * T.d⁻¹ ∈ T.R₂ :=
  Sec7.mem_or_of_mem_sup_zpowers T.d_mem_normalizer_R₂ (by rw [pow_two]; exact T.d_sq_mem_R₂) hg

@[expose] noncomputable def Tp : Subgroup X := Ct.map H.ι ⊔ zpowers T.d

theorem ι_Ct_le_S₁ : Ct.map H.ι ≤ H.G.D₁.S₁ := by
  rintro _ ⟨a, -, rfl⟩; exact H.ι_mem_S₁ a

theorem d_mem_normalizer_Ct : T.d ∈ normalizer ((Ct.map H.ι : Subgroup X) : Set X) := by
  refine mem_normalizer_of_conj_le fun g hg => ?_
  obtain ⟨a, ha, rfl⟩ := hg
  have haT : MA.inT1 a = true := Ct_T1 a (mem_Ct.mp ha)
  rw [← T.conj a haT]
  refine ⟨_, mem_Ct.mpr ?_, rfl⟩
  apply H.ι_injective
  rw [map_mul, map_mul, T.conj a haT, H.ι_t]
  have hat : H.ι a * t = t * H.ι a := by
    have h1 := congrArg H.ι (mem_Ct.mp ha)
    rwa [map_mul, map_mul, H.ι_t] at h1
  calc T.d * H.ι a * T.d⁻¹ * t = T.d * (H.ι a * (T.d⁻¹ * t * T.d)) * T.d⁻¹ := by group
    _ = T.d * (H.ι a * t) * T.d⁻¹ := by
        rw [show T.d⁻¹ * t * T.d = t by
          calc T.d⁻¹ * t * T.d = T.d⁻¹ * (T.d * t * T.d⁻¹) * T.d := by rw [T.d_conj_t]
            _ = t := by group]
    _ = t * (T.d * H.ι a * T.d⁻¹) := by
        rw [hat, show T.d * (t * H.ι a) * T.d⁻¹ = (T.d * t * T.d⁻¹) * (T.d * H.ι a * T.d⁻¹) by
          group, T.d_conj_t]

theorem Tp_le_T₂ : T.Tp ≤ T.T₂ :=
  sup_le ((ι_Ct_le_S₁ (H := H)).trans (T.S₁_le_R₂.trans T.R₂_le_T₂)) (zpowers_le.mpr T.d_mem_T₂)

theorem Tp_le_centralizer : T.Tp ≤ centralizer ({t} : Set X) := by
  refine sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr T.d_comm_t))
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h1 := congrArg H.ι (mem_Ct.mp ha)
  rwa [map_mul, map_mul, H.ι_t] at h1

theorem d_not_mem_Ct : T.d ∉ Ct.map H.ι := fun h =>
  T.d_not_mem_R₂ (T.S₁_le_R₂ ((ι_Ct_le_S₁ (H := H)) h))

theorem d_sq_mem_Ct : T.d * T.d ∈ Ct.map H.ι := by
  rw [T.sq]
  refine ⟨_, mem_Ct.mpr ?_, rfl⟩
  cases T.e <;> decide +kernel

theorem card_Tp : Nat.card T.Tp = 64 := by
  rw [Tp, Sec8.card_sup_zpowers T.d_mem_normalizer_Ct T.d_sq_mem_Ct T.d_not_mem_Ct,
    card_map_of_injective H.ι_injective, card_Ct]

theorem card_T_le_Tp : Nat.card A.T ≤ Nat.card T.Tp := by
  rw [T.card_Tp]; exact card_T_le (C := C)

theorem mem_Tp_of_comm_t {g : X} (hg : g ∈ T.T₂) (hgt : g * t = t * g) : g ∈ T.Tp := by
  have hCt : ∀ r ∈ T.R₂, r * t = t * r → r ∈ Ct.map H.ι := fun r hr hrt => by
    obtain ⟨s, rfl⟩ := H.mem_range_of_mem_S₁ (T.mem_S₁_of_comm_t hr hrt)
    refine ⟨s, mem_Ct.mpr ?_, rfl⟩
    apply H.ι_injective
    rw [map_mul, map_mul, H.ι_t, hrt]
  rcases T.mem_T₂ hg with h | h
  · exact mem_sup_left (hCt g h hgt)
  · have hgd : (g * T.d⁻¹) * t = t * (g * T.d⁻¹) := by
      have h1 : T.d⁻¹ * t = t * T.d⁻¹ := by
        calc T.d⁻¹ * t = T.d⁻¹ * (t * T.d) * T.d⁻¹ := by group
          _ = T.d⁻¹ * (T.d * t) * T.d⁻¹ := by rw [T.d_comm_t]
          _ = t * T.d⁻¹ := by group
      rw [mul_assoc, h1, ← mul_assoc, hgt, mul_assoc]
    rw [show g = (g * T.d⁻¹) * T.d by group]
    exact mul_mem (mem_sup_left (hCt _ h hgd)) (mem_sup_right (mem_zpowers _))

end TD

end AD

end KD8ab

end CFSG.ComponentClassification.HSFLit
