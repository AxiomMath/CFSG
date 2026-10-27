module

public import CFSG.LargeExtraspecial.S97RXRho
public import CFSG.LargeExtraspecial.S9SevenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k : G}
  {m : S.M} {O : Subgroup S.O}

theorem H97.cubic (X : S9.Hyp97 S k m O) {x₁ x₂ x₃ : S.O} (h₁ : x₁ ∈ S.Lbar k)
    (h₂ : x₂ ∈ S.Lbar k) (h₃ : x₃ ∈ S.Lbar k) {v : S.Qt} (hv : v ∈ S9.Ut S k (S9.X97 S k m)) :
    (x₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((x₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) - ((x₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) -
      ((x₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) -
        ((x₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) = 0 := by
  have hiso : ∀ u ∈ S9.Ut S k (S9.X97 S k m), ∀ w ∈ S9.Ut S k (S9.X97 S k m),
      QuadraticMap.polar S.q u w = 0 := fun u hu w hw =>
    S9.polar_eq_zero_of_mem_Ut X.hyp4 X.cons le_sup_left X.le X.normal X.isPGroup
      X.inf_ne_bot hu hw
  have hw₁ := S9.apply_sub_mem_Ut_inf_clSub X.hyp4 X.cons le_sup_left hiso h₃ hv
  have hw₂ := S6.Lbar_apply_sub_mem_span' X.hyp4.conj_mem (Submodule.mem_inf.mp hw₁).2 h₂
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw₂
  rw [← hc, map_smul, fix_of_mem_normalizer X.hyp4 (le_normalizer h₁), sub_self]

namespace Pair111

variable (P : Pair111 S g A h k ((m : G) * k)) (hE : Ebar S k ((m : G) * k) ≠ ⊥)
  (hodd : Odd (Nat.card (center (S9.Q97 S k m))))
include P hE hodd

theorem pi97_eq_one_of_fix (hsimp : IsSimpleGroup (Lam97 S k m)) {x : ↥(S9.X97 S k m)}
    (hx : ∀ u ∈ S9.Ut S k (S9.X97 S k m), ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) :
    pi97 S k m x = 1 := by
  have X := P.hyp97 hE
  set K := (ptFix S (S9.Ut S k (S9.X97 S k m))).subgroupOf (S9.X97 S k m) with hK
  have hKn : K.Normal := Pair111.normal_ptFix_Ut (S := S) (k := k) (k' := (m : G) * k)
  have hKm : (K.map (pi97 S k m)).Normal := hKn.map _ pi97_surjective
  have hxK : x ∈ K := mem_subgroupOf.mpr (mem_ptFix.mpr hx)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimp _ hKm with h0 | htop
  · have h1 : pi97 S k m x ∈ K.map (pi97 S k m) := mem_map_of_mem _ hxK
    rw [h0] at h1
    exact h1
  exfalso
  have hall : ∀ y : ↥(S9.X97 S k m), ∀ u ∈ S9.Ut S k (S9.X97 S k m),
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    intro y u hu
    have hy : pi97 S k m y ∈ K.map (pi97 S k m) := htop ▸ mem_top _
    obtain ⟨κ, hκ, hκy⟩ := hy
    have h1 : pi97 S k m (κ⁻¹ * y) = 1 := by
      simp only [map_mul, map_inv, hκy, inv_mul_cancel]
    have h2 := H97.fix_of_pi97_eq_one X hodd h1 hu
    have h3 := mem_ptFix.mp (mem_subgroupOf.mp hκ) u hu
    have e : (y : S.O) = (κ : S.O) * ((κ⁻¹ * y : ↥(S9.X97 S k m)) : S.O) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e, coe_mul_apply, h2, h3]
  have haF : S.cl (k * S.z * k⁻¹) ∈ fixSub S (S.Lbar ((m : G) * k)) :=
    (mem_fixSub S).mpr fun l hl => hall ⟨l, mem_sup_right hl⟩ _ (S9.cl_mem_Ut _)
  rw [P.hy'.hyp4.fixSub_eq, mem_span_cl_iff] at haF
  rcases haF with h0 | h1
  · exact cl_conj_z_ne_zero S P.memQ P.ne h0
  · exact P.cl_ne h1

theorem modCfg_inj (hsimp : IsSimpleGroup (Lam97 S k m)) :
    Function.Injective (H97.rhoLam97 (P.hyp97 hE) hodd) := by
  refine (injective_iff_map_eq_one _).mpr fun c hc => ?_
  obtain ⟨x, rfl⟩ := pi97_surjective c
  have hc' : rhoX97 S k m x = 1 := hc
  exact P.pi97_eq_one_of_fix hE hodd hsimp ((rhoX97_eq_one_iff x).mp hc')

theorem modCfg_stab (u y : Lam97 S k m) :
    H97.rhoLam97 (P.hyp97 hE) hodd u (H97.rhoLam97 (P.hyp97 hE) hodd y
        (⟨S.cl (k * S.z * k⁻¹), S9.cl_mem_Ut _⟩ : ↥(S9.Ut S k (S9.X97 S k m)))) =
      H97.rhoLam97 (P.hyp97 hE) hodd y
        (⟨S.cl (k * S.z * k⁻¹), S9.cl_mem_Ut _⟩ : ↥(S9.Ut S k (S9.X97 S k m))) ↔
      u ∈ normalizer (conjSubgroup y (T97 S k m k) : Set (Lam97 S k m)) := by
  obtain ⟨u', rfl⟩ := pi97_surjective u
  obtain ⟨y', rfl⟩ := pi97_surjective y
  exact Subtype.ext_iff.trans (H97.fix_iff (P.hyp97 hE) hodd u' y')

theorem modCfg_fix0 (v : ↥(S9.Ut S k (S9.X97 S k m)))
    (hv : ∀ u : Lam97 S k m, H97.rhoLam97 (P.hyp97 hE) hodd u v = v) : v = 0 := by
  have hfa : (v : S.Qt) ∈ fixSub S (S.Lbar k) := (mem_fixSub S).mpr fun l hl =>
    congrArg Subtype.val (hv (pi97 S k m ⟨l, mem_sup_left hl⟩))
  have hfb : (v : S.Qt) ∈ fixSub S (S.Lbar ((m : G) * k)) := (mem_fixSub S).mpr fun l hl =>
    congrArg Subtype.val (hv (pi97 S k m ⟨l, mem_sup_right hl⟩))
  rw [P.hy.hyp4.fixSub_eq, mem_span_cl_iff] at hfa
  rw [P.hy'.hyp4.fixSub_eq, mem_span_cl_iff] at hfb
  refine Subtype.ext ?_
  rcases hfa with h0 | h1
  · exact h0
  rcases hfb with h0 | h2
  · exact h0
  exact absurd (h1.symm.trans h2) P.cl_ne

omit P hE hodd in
theorem cubic_of_lift (X : S9.Hyp97 S k m O)
    {f₁ f₂ f₃ : ↥(S9.Ut S k (S9.X97 S k m)) ≃ₗ[ZMod 2] ↥(S9.Ut S k (S9.X97 S k m))}
    (h₁ : ∃ x ∈ S.Lbar k, ∀ v, (f₁ v : S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    (h₂ : ∃ x ∈ S.Lbar k, ∀ v, (f₂ v : S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    (h₃ : ∃ x ∈ S.Lbar k, ∀ v, (f₃ v : S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    (v : ↥(S9.Ut S k (S9.X97 S k m))) :
    f₁ (f₂ (f₃ v - v) - (f₃ v - v)) - (f₂ (f₃ v - v) - (f₃ v - v)) = 0 := by
  obtain ⟨x₁, hx₁, e₁⟩ := h₁
  obtain ⟨x₂, hx₂, e₂⟩ := h₂
  obtain ⟨x₃, hx₃, e₃⟩ := h₃
  refine Subtype.ext ?_
  simp only [Submodule.coe_sub, e₁, e₂, e₃, ZeroMemClass.coe_zero]
  exact H97.cubic X hx₁ hx₂ hx₃ v.2

omit P hE in
theorem lift_of_mem_T97 (X : S9.Hyp97 S k m O) {t : Lam97 S k m} (ht : t ∈ T97 S k m k) :
    ∃ x ∈ S.Lbar k, ∀ v, (H97.rhoLam97 X hodd t v : S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_T97 ht
  exact ⟨x, hx, fun v => rfl⟩

theorem modCfg (hsimp : IsSimpleGroup (Lam97 S k m)) :
    ModCfg (H97.rhoLam97 (P.hyp97 hE) hodd) (T97 S k m k)
      (⟨S.cl (k * S.z * k⁻¹), S9.cl_mem_Ut _⟩ : ↥(S9.Ut S k (S9.X97 S k m))) where
  inj := P.modCfg_inj hE hodd hsimp
  comm := fun _ hx _ hy => elemAbelian_mul_comm (isElemAbelian_T97 P.hy.hyp4) hx hy
  sq := fun _ hx => mul_self_of_mem_T97 P.hy.hyp4 hx
  ne_zero := fun h0 => cl_conj_z_ne_zero S P.memQ P.ne (congrArg Subtype.val h0)
  stab := P.modCfg_stab hE hodd
  fix0 := P.modCfg_fix0 hE hodd
  cubic := fun _ h₁ _ h₂ _ h₃ v => cubic_of_lift (P.hyp97 hE)
    (lift_of_mem_T97 hodd (P.hyp97 hE) h₁) (lift_of_mem_T97 hodd (P.hyp97 hE) h₂)
    (lift_of_mem_T97 hodd (P.hyp97 hE) h₃) v

omit hodd in
theorem two_pow_finrank_le' :
    2 ^ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) ≤ 4 * Nat.card (S9.Tj97 S k m k) ^ 2 := by
  have X := P.hyp97 hE
  have h1 := S9.card_mul_card_mul_two_pow_finrank_Ut_le X.hyp4 X.cons m X.le X.normal
    X.isPGroup X.inf_ne_bot
  rw [P.inf_O2Sub_eq, P.inf_O2Sub_eq', ← P.card_Ebar_eq] at h1
  have h2 := X.card_Tj97_mul (j := k) le_sup_left
  rw [P.inf_O2Sub_eq, P.hy.cons.card_Lbar] at h2
  have hn : 1 ≤ S.width := by have := P.hy.hyp4.two_lt_width; omega
  have hw : 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hw, ← h2] at h1
  set e := Nat.card (Ebar S k ((m : G) * k))
  set t := Nat.card (S9.Tj97 S k m k)
  have he : 0 < e := Nat.card_pos
  have h3 : e * e * 2 ^ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) ≤ e * e * (4 * t ^ 2) := by
    calc e * e * 2 ^ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) ≤ 2 * (t * e) * (2 * (t * e)) :=
          h1
      _ = e * e * (4 * t ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (Nat.mul_pos he he)

theorem two_pow_finrank_le :
    2 ^ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) ≤ 4 * Nat.card (T97 S k m k) ^ 2 := by
  rw [H97.card_T97 hodd P.hy.hyp4]
  exact P.two_pow_finrank_le' hE

theorem exists_lift_normalizer {c : Lam97 S k m}
    (hc : c ∈ normalizer (T97 S k m k : Set (Lam97 S k m))) :
    ∃ y : ↥(S9.X97 S k m), pi97 S k m y = c ∧ (y : S.O) ∈ normalizer (S.Lbar k : Set S.O) := by
  obtain ⟨y, rfl⟩ := pi97_surjective c
  exact ⟨y, rfl, (H97.pi97_mem_normalizer_iff (P.hyp97 hE) hodd le_sup_left P.hy.hyp4 P.hy.cons
    y).mp hc⟩

omit P hE hodd in
theorem exists_ne_ne_of_three {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (h3 : 3 ≤ Nat.card T) (t : K) : ∃ t' ∈ T, t' ≠ 1 ∧ t' ≠ t := by
  by_contra hcon
  push Not at hcon
  have hsub : (T : Set K) ⊆ {1, t} := fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hcon x hx h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, t} : Set K).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  have h3' : Nat.card T = (T : Set K).ncard := Nat.card_coe_set_eq _
  omega

theorem exists_move (htr : ∀ x ∈ T97 S k m k, x ≠ 1 → ∀ y ∈ T97 S k m k, y ≠ 1 →
      ∃ c ∈ normalizer (T97 S k m k : Set (Lam97 S k m)), c * x * c⁻¹ = y)
    (h3 : 3 ≤ Nat.card (T97 S k m k)) {l : S.O} (hl : l ∈ S.Lbar k)
    (hlE : l ∉ Ebar S k ((m : G) * k)) :
    ∃ y ∈ S9.X97 S k m, y ∈ normalizer (S.Lbar k : Set S.O) ∧
      l⁻¹ * (y * l * y⁻¹) ∉ Ebar S k ((m : G) * k) := by
  have X := P.hyp97 hE
  have hlO : l ∉ O2Sub (S9.X97 S k m) := fun h0 => hlE (P.inf_O2Sub_eq ▸ ⟨hl, h0⟩)
  have ht1 : pi97 S k m ⟨l, mem_sup_left hl⟩ ≠ 1 := fun h0 =>
    hlO ((H97.pi97_eq_one_iff X hodd P.hy.hyp4 (x := ⟨l, mem_sup_left hl⟩) hl).mp h0)
  obtain ⟨t', ht', ht'1, ht'l⟩ := exists_ne_ne_of_three h3 (pi97 S k m ⟨l, mem_sup_left hl⟩)
  obtain ⟨c, hcN, hc⟩ := htr _ (pi97_mem_T97 (x := ⟨l, mem_sup_left hl⟩) hl) ht1 t' ht' ht'1
  obtain ⟨y, rfl, hyN⟩ := P.exists_lift_normalizer hE hodd hcN
  refine ⟨y, y.2, hyN, fun hmem => ht'l ?_⟩
  rw [← P.inf_O2Sub_eq] at hmem
  have hz := (mem_inf.mp hmem).1
  have hO := (mem_inf.mp hmem).2
  have h1 := (H97.pi97_eq_one_iff X hodd P.hy.hyp4
    (x := (⟨l, mem_sup_left hl⟩ : ↥(S9.X97 S k m))⁻¹ * (y * ⟨l, mem_sup_left hl⟩ * y⁻¹))
    (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hz)).mpr
    (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hO)
  simp only [map_mul, map_inv] at h1
  exact hc.symm.trans (inv_mul_eq_one.mp h1).symm

end Pair111

end CFSG.LargeExtraspecial.S11
