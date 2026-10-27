module

public import CFSG.Fischer.Classification.Recognition.R3Order
public import CFSG.Assembly.Defs

public section

namespace CFSG.LargeExtraspecial.S12InspF3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem eq_top_of_invariant (hf : IsF3Form f) (hm : 4 ≤ m)
    {U : Submodule (ZMod 3) (Fin m → ZMod 3)}
    (hU : ∀ g ∈ F3.reflGroup f, ∀ x ∈ U, F3.act g x ∈ U) (hU0 : U ≠ ⊥) : U = ⊤ := by
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).1 hU0
  obtain ⟨w, hw, hxw⟩ : ∃ w, f w w = 1 ∧ f x w ≠ 0 := by
    by_contra! h
    exact hx0 (F3.eq_zero_of_forall_norm_one hf (by omega) h)
  have hwU : w ∈ U := by
    have h1 := hU _ (F3.refl_mem_reflGroup w) x hxU
    rw [F3.act_refl hw] at h1
    have h2 : f x w • w ∈ U := by
      have := U.sub_mem h1 hxU
      rwa [add_sub_cancel_left] at this
    have := U.smul_mem (f x w)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hxw, one_smul] at this
  have hall : ∀ w', f w' w' = 1 → w' ∈ U := fun w' hw' => by
    obtain ⟨g, hg, hgw⟩ := Recognition.R3.exists_mem_act_eq hf hm hw hw'
    rw [← hgw]
    exact hU g hg w hwU
  have hnd : f.Nondegenerate :=
    ⟨fun x hx => hf.nondeg x hx, fun y hy => hf.nondeg y fun x => by rw [hf.symm]; exact hy x⟩
  have horth : f.orthogonal U = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    refine F3.eq_zero_of_forall_norm_one hf (by omega) fun u hu => ?_
    rw [hf.symm]
    exact LinearMap.BilinForm.mem_orthogonal_iff.1 hy u (hall u hu)
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [horth, finrank_bot] at h1
  have h2 := Submodule.finrank_le U
  exact Submodule.eq_top_of_finrank_eq (by omega)

theorem neg_one_pow_ne_one (hm : 1 ≤ m) {k : ℕ} (hk : Odd k) :
    (-1 : GL (Fin m) (ZMod 3)) ^ k ≠ 1 := by
  rw [hk.neg_one_pow]
  intro h
  have := congrArg (fun g : GL (Fin m) (ZMod 3) => F3.act g (Pi.single ⟨0, by omega⟩ 1)) h
  simp only [F3.act_neg_one, F3.act_one] at this
  have h0 := congrFun this ⟨0, by omega⟩
  simp only [Pi.neg_apply, Pi.single_eq_same] at h0
  exact absurd h0 (by decide)

theorem normal_three_eq_bot (hf : IsF3Form f) (hm : 4 ≤ m) (N : Subgroup (R3 f))
    (hN : N.Normal) (h3 : IsPGroup 3 N) : N = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := F3.reflGroup f with hRdef
  set π : R →* R3 f := QuotientGroup.mk' (Subgroup.center R) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hZ : ∀ z : R, z ∈ Subgroup.center R → (z : GL (Fin m) (ZMod 3)) = 1 ∨
      (z : GL (Fin m) (ZMod 3)) = -1 := fun z hz => F3.coe_eq_of_mem_center hf hm hz
  have hker : ∀ z : R, π z = 1 ↔ z ∈ Subgroup.center R := fun z => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set Ñ := N.comap π with hÑdef
  let φ : Ñ →* N := (π.comp Ñ.subtype).codRestrict N fun x => x.2
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hπs x
    exact ⟨⟨y, hx⟩, rfl⟩
  have hφ : ∀ x : Ñ, ((φ x : N) : R3 f) = π x := fun x => rfl
  obtain ⟨P⟩ : Nonempty (Sylow 3 Ñ) := inferInstance
  have hPN : (P : Subgroup Ñ).map φ = ⊤ := by
    obtain ⟨j, hj⟩ := h3.index ((P : Subgroup Ñ).map φ)
    have hdvd : ((P : Subgroup Ñ).map φ).index ∣ (P : Subgroup Ñ).index := by
      rw [← Subgroup.index_comap_of_surjective _ hφs]
      exact Subgroup.index_dvd_of_le (Subgroup.le_comap_map _ _)
    have hnd := P.not_dvd_index
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact Subgroup.index_eq_one.mp hj
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero j)).trans (hj ▸ hdvd)) hnd
  have hP3 : ∀ p ∈ (P : Subgroup Ñ), ∃ k, p ^ 3 ^ k = 1 := fun p hp => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hcent : ∀ {z : R}, z ∈ Subgroup.center R → ∀ {k : ℕ}, z ^ 3 ^ k = 1 → z = 1 := by
    intro z hz k hk
    rcases hZ z hz with h | h
    · exact Subtype.ext h
    · exfalso
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_pow, h, OneMemClass.coe_one] at this
      exact neg_one_pow_ne_one (by omega) (Odd.pow (by decide : Odd 3)) this
  set PR : Subgroup R := (P : Subgroup Ñ).map Ñ.subtype with hPRdef
  have hPR : ∀ g : R, ∀ q ∈ PR, g * q * g⁻¹ ∈ PR := by
    rintro g _ ⟨p, hp, rfl⟩
    have hq : g * (p : R) * g⁻¹ ∈ Ñ := by
      show π (g * p * g⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hN.conj_mem _ p.2 _
    have hφq : φ ⟨_, hq⟩ ∈ (P : Subgroup Ñ).map φ := by rw [hPN]; trivial
    obtain ⟨p', hp', hpq⟩ := hφq
    set z : R := (p' : R)⁻¹ * (g * p * g⁻¹) with hzdef
    have hzc : z ∈ Subgroup.center R := by
      rw [← hker, hzdef, map_mul, map_inv]
      have := congrArg Subtype.val hpq
      rw [hφ, hφ] at this
      rw [show π (g * p * g⁻¹) = π p' from this.symm, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hP3 p hp
    obtain ⟨k', hk'⟩ := hP3 p' hp'
    have hz1 : z = 1 := by
      refine hcent hzc (k := k + k') ?_
      have hzcomm : ∀ y : R, z * y = y * z := fun y =>
        (Subgroup.mem_center_iff.mp hzc y).symm
      have hqpow : (g * (p : R) * g⁻¹) ^ 3 ^ (k + k') = 1 := by
        rw [conj_pow, pow_add, pow_mul, show ((p : R) ^ 3 ^ k) = 1 from
          congrArg Subtype.val hk, one_pow, mul_one, mul_inv_cancel]
      have hp'pow : (p' : R) ^ 3 ^ (k + k') = 1 := by
        rw [pow_add, mul_comm, pow_mul, show ((p' : R) ^ 3 ^ k') = 1 from
          congrArg Subtype.val hk', one_pow]
      have hdecomp : g * (p : R) * g⁻¹ = p' * z := by rw [hzdef, mul_inv_cancel_left]
      have := hqpow
      rw [hdecomp, (Commute.symm (hzcomm _)).mul_pow, hp'pow, one_mul] at this
      exact this
    refine ⟨p', hp', ?_⟩
    rw [hzdef] at hz1
    exact inv_mul_eq_one.mp hz1
  let A : MulAction PR (Fin m → ZMod 3) :=
    { smul := fun p x => F3.act ((p : R) : GL (Fin m) (ZMod 3)) x
      one_smul := fun x => F3.act_one x
      mul_smul := fun p q x => F3.act_mul _ _ x }
  have hPR3 : IsPGroup 3 PR := (P.isPGroup').map Ñ.subtype
  have hfixU : ∃ U : Submodule (ZMod 3) (Fin m → ZMod 3),
      ∀ x, x ∈ U ↔ ∀ p ∈ PR, F3.act ((p : R) : GL (Fin m) (ZMod 3)) x = x :=
    ⟨{ carrier := {x | ∀ p ∈ PR, F3.act ((p : R) : GL (Fin m) (ZMod 3)) x = x}
       add_mem' := fun {x y} hx hy p hp => by rw [F3.act_add, hx p hp, hy p hp]
       zero_mem' := fun p _ => F3.act_zero _
       smul_mem' := fun c x hx p hp => by rw [F3.act_smul, hx p hp] }, fun x => Iff.rfl⟩
  obtain ⟨U, hU⟩ := hfixU
  have hUinv : ∀ g ∈ F3.reflGroup f, ∀ x ∈ U, F3.act g x ∈ U := by
    intro g hg x hx
    rw [hU] at hx ⊢
    intro p hp
    have h1 := hx _ (hPR ⟨g, hg⟩⁻¹ p hp)
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, F3.act_mul] at h1
    calc F3.act ((p : R) : GL (Fin m) (ZMod 3)) (F3.act g x) =
        F3.act g (F3.act g⁻¹ (F3.act ((p : R) : GL (Fin m) (ZMod 3)) (F3.act g x))) :=
          (F3.act_act_inv _ _).symm
      _ = F3.act g x := by rw [h1]
  have hU0 : U ≠ ⊥ := by
    have hmod := hPR3.card_modEq_card_fixedPoints (Fin m → ZMod 3)
    have hcard : Nat.card (Fin m → ZMod 3) = 3 ^ m := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard] at hmod
    have h0fix : (0 : Fin m → ZMod 3) ∈ MulAction.fixedPoints PR (Fin m → ZMod 3) :=
      fun p => F3.act_zero _
    obtain ⟨x, hxfix, hx0⟩ : ∃ x ∈ MulAction.fixedPoints PR (Fin m → ZMod 3), x ≠ 0 := by
      by_contra h
      push Not at h
      have h1 : Nat.card (MulAction.fixedPoints PR (Fin m → ZMod 3)) ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr
          ⟨fun p q => Subtype.ext ((h p p.2).trans (h q q.2).symm)⟩
      have h2 : 0 < Nat.card (MulAction.fixedPoints PR (Fin m → ZMod 3)) :=
        Nat.card_pos_iff.mpr ⟨⟨⟨0, h0fix⟩⟩, inferInstance⟩
      have h3m : (3 : ℕ) ^ m % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      unfold Nat.ModEq at hmod
      omega
    rw [Submodule.ne_bot_iff]
    exact ⟨x, (hU x).2 fun p hp => hxfix ⟨p, hp⟩, hx0⟩
  have htop := eq_top_of_invariant hf hm hUinv hU0
  have hPR1 : PR = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    refine Subtype.ext (F3.gl_ext fun x => ?_)
    rw [OneMemClass.coe_one, F3.act_one]
    exact (hU x).1 (htop ▸ Submodule.mem_top) p hp
  have hP1 : (P : Subgroup Ñ) = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    have : (p : R) ∈ PR := ⟨p, hp, rfl⟩
    rw [hPR1, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  rw [hP1, Subgroup.map_bot] at hPN
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) := trivial
  rw [← hPN, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

end CFSG.LargeExtraspecial.S12InspF3
