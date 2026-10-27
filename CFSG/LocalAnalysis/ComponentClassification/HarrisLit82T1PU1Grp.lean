module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.Fischer.Classification.Recognition.PSU6

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.LieType.Universal.Spin (upperSL2 lowerSL2 coe_upperSL2 coe_lowerSL2)
open scoped MatrixGroups commutatorElement

section SL2

variable {K : Type*} [Field K]

theorem coe_upperSL2_mul_lowerSL2_mul_upperSL2 (a b c : K) :
    ((upperSL2 a * lowerSL2 b * upperSL2 c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![1 + a * b, a + c + a * b * c; b, 1 + b * c] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2,
    coe_lowerSL2, coe_upperSL2, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem commutatorElement_upperSL2_lowerSL2_eq_neg_one {d x y : K} (hd : d ≠ 0) (hy : y ≠ 0)
    (hxy : x ^ 2 + y ^ 2 = -1) :
    ⁅upperSL2 d * lowerSL2 (-d⁻¹) * upperSL2 d,
      upperSL2 ((x - 1) * d / y) * lowerSL2 (y / d) * upperSL2 ((-x - 1) * d / y)⁆ = -1 := by
  obtain ⟨i, hi⟩ : ∃ i : SL(2, K), i = upperSL2 d * lowerSL2 (-d⁻¹) * upperSL2 d := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : SL(2, K),
      j = upperSL2 ((x - 1) * d / y) * lowerSL2 (y / d) * upperSL2 ((-x - 1) * d / y) :=
    ⟨_, rfl⟩
  rw [← hi, ← hj]
  have e1 : (1 : K) + d * -d⁻¹ = 0 := by rw [mul_neg, mul_inv_cancel₀ hd]; ring
  have e2 : d + d + d * -d⁻¹ * d = d := by rw [mul_neg, mul_inv_cancel₀ hd]; ring
  have hi' : (i : Matrix (Fin 2) (Fin 2) K) = !![0, d; -d⁻¹, 0] := by
    rw [hi, coe_upperSL2_mul_lowerSL2_mul_upperSL2, e1, e2, mul_comm (-d⁻¹) d, e1]
  have g1 : (x - 1) * d / y * (y / d) = x - 1 := by field_simp
  have g2 : y / d * ((-x - 1) * d / y) = -x - 1 := by field_simp
  have f1 : (1 : K) + (x - 1) * d / y * (y / d) = x := by rw [g1]; ring
  have f2 : (1 : K) + y / d * ((-x - 1) * d / y) = -x := by rw [g2]; ring
  have f3 : (x - 1) * d / y + (-x - 1) * d / y + (x - 1) * d / y * (y / d) * ((-x - 1) * d / y) =
      d * y := by
    have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy
    rw [g1]
    linear_combination (-d * y⁻¹) * hxy + (d * y) * hyy
  have hj' : (j : Matrix (Fin 2) (Fin 2) K) = !![x, d * y; y / d, -x] := by
    rw [hj, coe_upperSL2_mul_lowerSL2_mul_upperSL2, f1, f2, f3]
  have hij : i * j = -1 * (j * i) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hi', hj', Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext a b
    fin_cases a <;> fin_cases b <;> simp <;> field_simp
  rw [commutatorElement_def, hij]
  group

theorem exists_sq_add_sq_eq_neg_one {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ x y : F, y ≠ 0 ∧ x ^ 2 + y ^ 2 = -1 := by
  have := Fintype.ofFinite F
  have hF : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨s, t, hst⟩ :=
    CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hF one_ne_zero one_ne_zero (-1 : F)
  simp only [one_mul] at hst
  by_cases ht : t = 0
  · refine ⟨0, s, fun hs => ?_, by rw [← hst, ht]; ring⟩
    rw [hs, ht] at hst
    have : (1 : F) = 0 := by linear_combination hst
    exact one_ne_zero this
  · exact ⟨s, t, ht, hst⟩

end SL2

section Lift

variable {S G : Type*} [Group S] [Group G] (π : S →* G) {E : Subgroup G}

theorem commutator_self_le (H : Subgroup S) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem map_commutator_comap_of_le (hEr : E ≤ π.range) :
    (⁅E.comap π, E.comap π⁆).map π = ⁅E, E⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_of_le_right hEr]

theorem commutator_comap_eq_of_le (hE : ⁅E, E⁆ = E) (hEr : E ≤ π.range)
    (hker : π.ker ≤ ⁅E.comap π, E.comap π⁆) : ⁅E.comap π, E.comap π⁆ = E.comap π := by
  refine le_antisymm (commutator_self_le _) fun j hj => ?_
  have h1 : π j ∈ (⁅E.comap π, E.comap π⁆).map π := by
    rw [map_commutator_comap_of_le π hEr, hE]
    exact hj
  obtain ⟨c, hc, hcj⟩ := Subgroup.mem_map.mp h1
  have h2 : c⁻¹ * j ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcj, inv_mul_cancel]
  have := mul_mem hc (hker h2)
  rwa [mul_inv_cancel_left] at this

theorem isQuasisimple_of_openQuasisimple {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

@[expose] def comapRestrict (E : Subgroup G) : ↥(E.comap π) →* ↥E :=
  (π.comp (E.comap π).subtype).codRestrict E fun x => x.2

theorem coe_comapRestrict (E : Subgroup G) (x : ↥(E.comap π)) :
    (comapRestrict π E x : G) = π x :=
  rfl

theorem comapRestrict_surjective (hEr : E ≤ π.range) :
    Function.Surjective (comapRestrict π E) := by
  rintro ⟨g, hg⟩
  obtain ⟨s, rfl⟩ := hEr hg
  exact ⟨⟨s, hg⟩, rfl⟩

theorem isQuasisimple_comap_of_le (hE : IsQuasisimple ↥E) (hEr : E ≤ π.range)
    (hcen : π.ker ≤ center S) (hker : π.ker ≤ ⁅E.comap π, E.comap π⁆) :
    IsQuasisimple ↥(E.comap π) := by
  have hEp : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp hE.1
  have hJp : Group.IsPerfect ↥(E.comap π) :=
    Subgroup.isPerfect_iff.mpr (commutator_comap_eq_of_le π hEp hEr hker)
  have hfker : (comapRestrict π E).ker ≤ center ↥(E.comap π) := by
    intro x hx
    have hx' : (x : S) ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← coe_comapRestrict, MonoidHom.mem_ker.mp hx, OneMemClass.coe_one]
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hcen hx') y)
  exact (LocalCores.isQuasisimple_iff_of_surjective hJp (comapRestrict π E)
    (comapRestrict_surjective π hEr) hfker).mpr hE

theorem pPrimeCore_comap_eq_bot [Finite S] (hq : IsQuasisimple ↥(E.comap π))
    (hEr : E ≤ π.range) (hZ : ∀ g ∈ E, (∀ h ∈ E, g * h = h * g) → g * g = 1)
    (hker : ∀ s ∈ π.ker, s * s = 1) {z : S} (hz : z ∈ E.comap π) (hz1 : z ≠ 1)
    (hzz : z * z = 1) : pPrimeCore 2 ↥(E.comap π) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := pPrimeCore_coprime_card (p := 2) (G := ↥(E.comap π))
  rcases LocalCores.quasisimple_normal_subgroups hq
      (pPrimeCore_normal (p := 2) (G := ↥(E.comap π))) with htop | hle
  · exfalso
    rw [htop, Subgroup.card_top] at hc
    have hz2 : orderOf (⟨z, hz⟩ : ↥(E.comap π)) = 2 := by
      refine orderOf_eq_prime ?_ fun h => hz1 (congrArg Subtype.val h)
      exact Subtype.ext (by simp [pow_two, hzz])
    have h2 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(E.comap π))
    rw [hz2] at h2
    exact absurd (Nat.Coprime.eq_one_of_dvd hc h2) (by norm_num)
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have hxc := Subgroup.mem_center_iff.mp (hle hx)
    have hπx : π x * π x = 1 := by
      refine hZ _ x.2 fun h hh => ?_
      obtain ⟨s, rfl⟩ := hEr hh
      have := congrArg (fun y : ↥(E.comap π) => π y) (hxc ⟨s, hh⟩)
      simp only [Subgroup.coe_mul, map_mul] at this
      exact this.symm
    have hx4 : x ^ 4 = 1 := by
      have hk : (x : S) * x ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, hπx]
      have h1 := hker _ hk
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← h1]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have hdvd4 : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have hodd : Nat.Coprime 2 (orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥(E.comap π)))) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) hc
    rw [Subgroup.orderOf_mk] at hodd
    have h1 : orderOf x = 1 := by
      have hc4 : Nat.Coprime (orderOf x) 4 := by
        have := (Nat.Coprime.pow_left 2 hodd).symm
        simpa using this
      exact Nat.Coprime.eq_one_of_dvd hc4 hdvd4
    exact orderOf_eq_one_iff.mp h1

theorem apply_eq_of_map_apply_eq (hcen : π.ker ≤ center S) {J : Subgroup S} (hJ : ⁅J, J⁆ = J)
    (α : MulAut S) (hα : ∀ s ∈ J, π (α s) = π s) : ∀ s ∈ J, α s = s := by
  have hc : ∀ s ∈ J, ∃ c ∈ center S, α s = s * c := fun s hs =>
    ⟨s⁻¹ * α s, hcen (by rw [MonoidHom.mem_ker, map_mul, map_inv, hα s hs, inv_mul_cancel]),
      by rw [mul_inv_cancel_left]⟩
  have hle : ⁅J, J⁆ ≤ fixedSubgroup α := Subgroup.commutator_le.mpr fun a ha b hb => by
    obtain ⟨c, hcZ, hac⟩ := hc a ha
    obtain ⟨d, hdZ, hbd⟩ := hc b hb
    have hc' := Subgroup.mem_center_iff.mp hcZ
    have hd' := Subgroup.mem_center_iff.mp hdZ
    rw [mem_fixedSubgroup, map_commutatorElement, hac, hbd, commutatorElement_def,
      commutatorElement_def]
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * (c * (b * d) * c⁻¹) * a⁻¹ * (b * d)⁻¹ := by group
      _ = a * (b * d) * a⁻¹ * (b * d)⁻¹ := by rw [← hc' (b * d), mul_inv_cancel_right]
      _ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [← hd' a⁻¹, mul_inv_cancel_right]
  intro s hs
  rw [← hJ] at hs
  exact hle hs

theorem eq_conj_of_map_apply_eq [hS : Group.IsPerfect S] (hcen : π.ker ≤ center S)
    (α : MulAut S) (x : S) (hα : ∀ s, π (α s) = π (x * s * x⁻¹)) : α = MulAut.conj x := by
  have htop : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = (⊤ : Subgroup S) := by
    rw [← commutator_def]
    exact hS.commutator_eq_top
  have h := apply_eq_of_map_apply_eq π hcen htop (MulAut.conj x⁻¹ * α) fun s _ => by
    rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, hα]
    simp only [map_mul, map_inv, inv_inv]
    group
  ext s
  have hs := h s (Subgroup.mem_top s)
  rw [MulAut.mul_apply, MulAut.conj_apply, inv_inv] at hs
  rw [MulAut.conj_apply]
  calc α s = x * (x⁻¹ * α s * x) * x⁻¹ := by group
    _ = x * s * x⁻¹ := by rw [hs]

end Lift

section Components

theorem isTwoComponentIn_of_normal_of_pPrimeCore {X : Type*} [Group X] {J C : Subgroup X}
    (hJC : J ≤ C) (hn : (J.subgroupOf C).Normal) (hq : IsQuasisimple ↥J)
    (hO : pPrimeCore 2 ↥J = ⊥) : IsTwoComponentIn J C :=
  ⟨hJC, hn.isSubnormal, hq.1, LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩

theorem not_isSLTwoOver_of_sq_dvd {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {q : ℕ} (hq : 2 ≤ q) (hdvd : q ^ 2 ∣ Nat.card Y) :
    ¬ IsSLTwoOver q (Y ⧸ pPrimeCore 2 Y) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  have h1 : Nat.card Y = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, ← Nat.card_congr e.toEquiv,
      Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hO).trans
        QuotientGroup.quotientBot).toEquiv]
  rw [Nat.card_eq_fintype_card (α := F), hF] at h1
  rw [h1, pow_two] at hdvd
  have h2 : q ∣ q ^ 2 - 1 := by
    rw [pow_two]
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
  have h3 : q ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub (dvd_pow_self q two_ne_zero) h2
  have h4 : q ^ 2 - (q ^ 2 - 1) = 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  rw [h4] at h3
  have := Nat.le_of_dvd one_pos h3
  omega

end Components

section RootGroup

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem card_dvd_of_eichler_mem {A : Type*} [AddCommGroup A] (ρ : A →+ V)
    (hρ : Function.Injective ρ) {u f : V} (hu : Q u = 0) (huf : polar Q u f ≠ 0)
    (hρu : ∀ a, polar Q u (ρ a) = 0) (hρf : ∀ a, polar Q f (ρ a) = 0)
    {E : Subgroup (V ≃ₗ[K] V)} (hE : ∀ a, eichler Q u (ρ a) ∈ E) :
    Nat.card A ∣ Nat.card E := by
  let φ : Multiplicative A →* ↥E :=
    { toFun := fun a => ⟨eichler Q u (ρ a.toAdd), hE _⟩
      map_one' := Subtype.ext (by
        change eichler Q u (ρ 0) = 1
        rw [map_zero, eichler_zero_right])
      map_mul' := fun a b => Subtype.ext (by
        change eichler Q u (ρ (a.toAdd + b.toAdd)) =
          eichler Q u (ρ a.toAdd) * eichler Q u (ρ b.toAdd)
        rw [map_add, eichler_mul (hρu _) (hρu _)]) }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : eichler Q u (ρ a.toAdd) = 1 := congrArg Subtype.val ha
    have hfu : polar Q f u ≠ 0 := by rwa [polar_comm]
    have hwf : polar Q f (ρ a.toAdd) = 0 := hρf _
    have h2 := LinearEquiv.congr_fun h1 f
    rw [eichler_apply hu (hρu _), hwf, zero_add] at h2
    change f + polar Q f u • ρ a.toAdd - (Q (ρ a.toAdd) * polar Q f u) • u = f at h2
    have h3 : polar Q f u • (ρ a.toAdd - Q (ρ a.toAdd) • u) = 0 := by
      linear_combination (norm := module) h2
    have h4 : ρ a.toAdd = Q (ρ a.toAdd) • u :=
      sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_left hfu)
    have h5 : Q (ρ a.toAdd) = 0 := by
      have := hwf
      rw [h4, polar_smul_right, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_right hfu
    rw [h5, zero_smul] at h4
    have : a.toAdd = 0 := hρ (by rw [h4, map_zero])
    simpa using this
  have := Subgroup.card_dvd_of_injective φ hφ
  rwa [Nat.card_congr Multiplicative.toAdd] at this

end RootGroup

end CFSG.ComponentClassification.HarrisLit.T1
