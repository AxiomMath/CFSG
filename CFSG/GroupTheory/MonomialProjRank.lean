module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePermCount
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePermOrb
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore
open Equiv MulAction
open scoped commutatorElement

private theorem pow_card_mul_prod_pow_mul_le {ι : Type*} [Fintype ι] {r : ℕ} (hr : 3 ≤ r)
    (b : ι → ℕ) (i₀ : ι) :
    r ^ (b i₀) * ∏ i, (r * r ^ (b i)) ≤ r ^ (∑ i, r ^ (b i)) := by
  classical
  have hterm : ∀ a, 2 * a + 1 ≤ r ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      nlinarith
  have hb_le : b i₀ ≤ ∑ i, b i :=
    Finset.single_le_sum (f := b) (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)
  have hsum2 : ∑ i, (2 * b i + 1) = 2 * ∑ i, b i + Fintype.card ι := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
    simp
  have hexp : b i₀ + (Fintype.card ι + ∑ i, b i) ≤ ∑ i, r ^ b i := by
    have h1 : b i₀ + (Fintype.card ι + ∑ i, b i) ≤ ∑ i, (2 * b i + 1) := by
      rw [hsum2]
      omega
    exact h1.trans (Finset.sum_le_sum fun i _ => hterm (b i))
  have hprod : ∏ i, (r * r ^ b i) = r ^ (∑ i, (1 + b i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ,
      ← pow_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    simp
  have hexp' : b i₀ + ∑ i, (1 + b i) ≤ ∑ i, r ^ b i := by
    have h : ∑ i, (1 + b i) = Fintype.card ι + ∑ i, b i := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      simp
    rw [h]
    exact hexp
  calc r ^ (b i₀) * ∏ i, (r * r ^ b i) = r ^ (b i₀ + ∑ i, (1 + b i)) := by
        rw [hprod, ← pow_add]
    _ ≤ r ^ (∑ i, r ^ b i) := Nat.pow_le_pow_right (by omega) hexp'


private theorem pmb_card_proj_bound {r m : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hm : 1 ≤ m)
    (B : Subgroup (Equiv.Perm (Fin m))) (hBp : ∀ b ∈ B, b ^ r = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    Nat.card B * Nat.card {u : Fin m → ZMod r //
      u ⟨0, hm⟩ = 0 ∧ ∀ b ∈ B, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} ≤ r ^ (m - 1) := by
  classical
  have hp : r.Prime := Fact.out
  have hr1 : r ≠ 1 := hp.ne_one
  have hr3 : 3 ≤ r := by have := hp.two_le; omega
  let x₀ : Fin m := ⟨0, hm⟩
  haveI : FaithfulSMul B (Fin m) :=
    ⟨fun {g h} hgh => Subtype.ext (Equiv.ext hgh)⟩
  have hG : IsPGroup r B := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hBp g g.2)⟩
  let A : Type := {u : Fin m → ZMod r //
    ∀ g : B, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c}
  let U : Type := {u : Fin m → ZMod r //
    u x₀ = 0 ∧ ∀ g : B, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c}
  have hAeq : Nat.card A = r * Nat.card U := by
    let cst : ZMod r → (Fin m → ZMod r) := fun a _ => a
    let cstA : ZMod r → A := fun a => ⟨cst a, fun g => ⟨0, fun x => by simp [cst]⟩⟩
    let subA : A → A → A := fun u v =>
      ⟨u.1 - v.1, fun g => by
        obtain ⟨cu, hcu⟩ := u.2 g
        obtain ⟨cv, hcv⟩ := v.2 g
        exact ⟨cu - cv, fun x => by
          simp only [Pi.sub_apply, ← hcu x, ← hcv x]
          ring⟩⟩
    let addA : A → A → A := fun u v =>
      ⟨u.1 + v.1, fun g => by
        obtain ⟨cu, hcu⟩ := u.2 g
        obtain ⟨cv, hcv⟩ := v.2 g
        exact ⟨cu + cv, fun x => by
          simp only [Pi.add_apply, ← hcu x, ← hcv x]
          ring⟩⟩
    let normU : A → U := fun u =>
      ⟨u.1 - cst (u.1 x₀), ⟨by simp [cst], (subA u (cstA (u.1 x₀))).2⟩⟩
    let e : A ≃ ZMod r × U :=
      { toFun := fun u => (u.1 x₀, normU u)
        invFun := fun p => addA ⟨p.2.1, p.2.2.2⟩ (cstA p.1)
        left_inv := by
          intro u
          apply Subtype.ext
          funext x
          simp [cst, cstA, addA, subA, normU]
        right_inv := by
          intro p
          apply Prod.ext
          · simp [cst, cstA, addA, normU, p.2.2.1]
          · apply Subtype.ext
            funext x
            simp [cst, cstA, addA, subA, normU, p.2.2.1] }
    calc Nat.card A = Nat.card (ZMod r × U) := Nat.card_congr e
      _ = r * Nat.card U := by rw [Nat.card_prod, Nat.card_zmod]
  let n : MulAction.orbitRel.Quotient B (Fin m) → ℕ :=
    fun ω => Nat.card (MulAction.orbit B ω.out)
  let t : ℕ := Nat.card (MulAction.orbitRel.Quotient B (Fin m))
  have hsum : ∑ ω, n ω = m := by
    rw [CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pmb_sum_card_orbit (G := B) (X := Fin m),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hprod : Nat.card B ≤ ∏ ω, n ω :=
    CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pmb_card_le_prod_card_orbit
      (G := B) (X := Fin m) (hc := fun g h => Subtype.ext (hBc g g.2 h h.2))
  have ht : 0 < t := by
    haveI : Nonempty (MulAction.orbitRel.Quotient B (Fin m)) := ⟨Quotient.mk'' x₀⟩
    exact Nat.card_pos
  have hpow_t : r ^ t = r * r ^ (t - 1) := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    rw [pow_succ']
  have hpow_m : r ^ m = r * r ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ']
  have hprodconst : (∏ ω : MulAction.orbitRel.Quotient B (Fin m), r) = r ^ t := by
    rw [Finset.prod_const, Finset.card_univ]
    rw [show t = Fintype.card (MulAction.orbitRel.Quotient B (Fin m)) by
      exact Nat.card_eq_fintype_card]
  have hUcard : Nat.card U = Nat.card {u : Fin m → ZMod r //
      u ⟨0, hm⟩ = 0 ∧ ∀ b ∈ B, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    exact and_congr_right fun _ =>
      ⟨fun h b hb => h ⟨b, hb⟩, fun h g => h g.1 g.2⟩
  by_cases hfix : (MulAction.fixedPoints B (Fin m)).Nonempty
  · obtain ⟨x, hx⟩ := hfix
    have hx1 : Nat.card (MulAction.orbit B x) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hx
    have hA_le : Nat.card A ≤ r ^ t := by
      have h := CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pmb_card_affine_le
        (G := B) (X := Fin m) (r := r) hG x
      rw [hx1, mul_one] at h
      exact h
    have hU_le : Nat.card U ≤ r ^ (t - 1) := by
      have h1 : r * Nat.card U ≤ r * r ^ (t - 1) := by
        calc r * Nat.card U = Nat.card A := hAeq.symm
          _ ≤ r ^ t := hA_le
          _ = r * r ^ (t - 1) := hpow_t
      exact Nat.le_of_mul_le_mul_left h1 hp.pos
    have hmain : r * (Nat.card U * Nat.card B) ≤ r * r ^ (m - 1) := by
      calc r * (Nat.card U * Nat.card B) = (r * Nat.card U) * Nat.card B := by ring
        _ ≤ (r * r ^ (t - 1)) * Nat.card B :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left r hU_le)
        _ = r ^ t * Nat.card B := by rw [hpow_t]
        _ ≤ r ^ t * ∏ ω, n ω := Nat.mul_le_mul_left _ hprod
        _ = (∏ ω, r) * ∏ ω, n ω := by rw [hprodconst]
        _ = ∏ ω, (r * n ω) := (Finset.prod_mul_distrib).symm
        _ ≤ r ^ m := by
            have := CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pmb_prod_mul_le_pow (r := r) hr1 n
            rwa [hsum] at this
        _ = r * r ^ (m - 1) := hpow_m
    have h := Nat.le_of_mul_le_mul_left hmain hp.pos
    rw [hUcard] at h
    simpa [Nat.mul_comm] using h
  · choose b n_b using fun (ω : MulAction.orbitRel.Quotient B (Fin m)) =>
      hG.card_orbit ω.out
    let ω₀ : MulAction.orbitRel.Quotient B (Fin m) := Quotient.mk'' x₀
    have hA_le : Nat.card A ≤ r ^ t * n ω₀ :=
      CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pmb_card_affine_le
        (G := B) (X := Fin m) (r := r) hG ω₀.out
    have hU_le : Nat.card U ≤ r ^ (t - 1) * n ω₀ := by
      have h1 : r * Nat.card U ≤ r * (r ^ (t - 1) * n ω₀) := by
        calc r * Nat.card U = Nat.card A := hAeq.symm
          _ ≤ r ^ t * n ω₀ := hA_le
          _ = r * (r ^ (t - 1) * n ω₀) := by rw [hpow_t]; ring
      exact Nat.le_of_mul_le_mul_left h1 hp.pos
    have harith : n ω₀ * ∏ ω, (r * n ω) ≤ r ^ m := by
      have h := pow_card_mul_prod_pow_mul_le (r := r) hr3 b ω₀
      simp only [← n_b] at h
      rwa [hsum] at h
    have hmain : r * (Nat.card U * Nat.card B) ≤ r * r ^ (m - 1) := by
      calc r * (Nat.card U * Nat.card B) = (r * Nat.card U) * Nat.card B := by ring
        _ ≤ (r * (r ^ (t - 1) * n ω₀)) * Nat.card B :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left r hU_le)
        _ = n ω₀ * (r ^ t * Nat.card B) := by rw [hpow_t]; ring
        _ ≤ n ω₀ * (r ^ t * ∏ ω, n ω) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hprod)
        _ = n ω₀ * ((∏ ω, r) * ∏ ω, n ω) := by rw [hprodconst]
        _ = n ω₀ * ∏ ω, (r * n ω) := by rw [Finset.prod_mul_distrib]
        _ ≤ r ^ m := harith
        _ = r * r ^ (m - 1) := hpow_m
    have h := Nat.le_of_mul_le_mul_left hmain hp.pos
    rw [hUcard] at h
    simpa [Nat.mul_comm] using h


theorem card_le_pow_sub_one_mul_card_inf_scalars_mon
    {r m : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    {C : Type} [CommGroup C] [Finite C] [Nontrivial C] (hCc : IsCyclic C)
    (hCr : IsPGroup r C) (hm : 1 ≤ m) (P : Subgroup (Mon C m))
    (hpow : ∀ x ∈ P, x ^ r ∈ (monScalar C m).range)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ (monScalar C m).range) :
    Nat.card P ≤ r ^ (m - 1) * Nat.card ↥(P ⊓ (monScalar C m).range) := by
  classical
  have hp : r.Prime := hr.out
  let S := (monScalar C m).range
  let i0 : Fin m := ⟨0, hm⟩
  let π' : P →* Perm (Fin m) := monPerm.comp P.subtype
  let T := π'.ker
  let B := π'.range
  let T' : Subgroup (Mon C m) := T.map P.subtype
  have hT'eq : T' = P ⊓ monPerm.ker := by
    ext y
    simp only [T', T, Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply,
      Subgroup.coe_subtype, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hyP, hyker⟩
      exact ⟨⟨y, hyP⟩, hyker, rfl⟩
  have hT'leP : T' ≤ P := by rw [hT'eq]; exact inf_le_left
  have hT'right : ∀ y ∈ T', y.right = 1 := by
    intro y hy
    have hy' : y ∈ P ⊓ monPerm.ker := by rwa [← hT'eq]
    exact MonoidHom.mem_ker.1 hy'.2
  have hSle : S ≤ monPerm.ker := by
    intro z hz
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hz
    rw [MonoidHom.mem_ker]
    exact monPerm_monScalar c
  have hT'inter : T' ⊓ S = P ⊓ S := by
    rw [hT'eq, inf_assoc, inf_eq_right.mpr hSle]
  have hcardT : Nat.card T = Nat.card T' :=
    (Subgroup.card_map_of_injective P.subtype_injective).symm
  have hcardP : Nat.card P = Nat.card T' * Nat.card B := by
    rw [← hcardT]
    exact (Subgroup.card_ker_mul_card_range π').symm
  have hBp : ∀ b ∈ B, b ^ r = 1 := by
    intro b hb
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hb
    have h1 : (x : Mon C m) ^ r ∈ S := hpow x x.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 h1
    have h2 : monPerm ((x : Mon C m) ^ r) = 1 := by
      rw [← hz]
      exact monPerm_monScalar z
    calc b ^ r = (π' x) ^ r := by rw [hx]
      _ = π' (x ^ r) := (map_pow π' x r).symm
      _ = monPerm ((x : Mon C m) ^ r) := rfl
      _ = 1 := h2
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hb
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hb'
    have h1 : ⁅(x : Mon C m), (y : Mon C m)⁆ ∈ S := hcomm x x.2 y y.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 h1
    have h2 : monPerm ⁅(x : Mon C m), (y : Mon C m)⁆ = 1 := by
      rw [← hz]
      exact monPerm_monScalar z
    have hcomm' : ⁅π' x, π' y⁆ = 1 := by
      rw [← map_commutatorElement]
      exact h2
    rw [commutatorElement_eq_one_iff_mul_comm] at hcomm'
    calc b * b' = π' x * π' y := by rw [hx, hy]
      _ = π' y * π' x := hcomm'
      _ = b' * b := by rw [hx, hy]
  have hBpg : IsPGroup r B := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hBp g g.2)⟩
  have hpowD : ∀ x : T', ∀ i, x.1.left i ^ r = x.1.left i0 ^ r := by
    intro x i
    have hmem : x.1 ^ r ∈ S := hpow x.1 (hT'leP x.2)
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hmem
    have hxeq : x.1 = monT x.1.left := eq_monT_of_right_eq_one (hT'right x.1 x.2)
    have h1 : monT (x.1.left ^ r) = monScalar C m z := by
      change SemidirectProduct.inl (x.1.left ^ r) = monScalar C m z
      rw [map_pow, show SemidirectProduct.inl (x.1.left) = x.1 from hxeq.symm]
      exact hz.symm
    rw [monScalar_apply] at h1
    have h2 : x.1.left ^ r = fun _ => z := monT_injective h1
    have h2i : x.1.left i ^ r = z := congrFun h2 i
    have h2i0 : x.1.left i0 ^ r = z := congrFun h2 i0
    rw [h2i, h2i0]
  let ξ : T' →* (Fin m → C) :=
    { toFun := fun y i => y.1.left i / y.1.left i0
      map_one' := by ext i; simp
      map_mul' := by
        intro x y
        have hx : x.1.right = 1 := hT'right x.1 x.2
        ext i
        have hmul : ((x * y).1 : Mon C m).left = x.1.left * y.1.left := by
          change (x.1 * y.1).left = x.1.left * y.1.left
          rw [SemidirectProduct.mul_left, hx]
          simp
        change ((x * y).1 : Mon C m).left i / ((x * y).1 : Mon C m).left i0 =
          (x.1.left i / x.1.left i0) * (y.1.left i / y.1.left i0)
        rw [hmul]
        simp only [Pi.mul_apply, div_eq_mul_inv]
        rw [mul_inv_rev]
        ac_rfl }
  have hξtor : ∀ y : T', ∀ i, (ξ y i) ^ r = 1 := by
    intro y i
    change (y.1.left i / y.1.left i0) ^ r = 1
    rw [div_pow, hpowD y i, hpowD y i0]
    simp [div_eq_mul_inv]
  let U : Set (Fin m → ZMod r) :=
    {u | u i0 = 0 ∧ ∀ b ∈ B, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c}
  have hU : Nat.card B * Nat.card U ≤ r ^ (m - 1) :=
    pmb_card_proj_bound (r := r) hr2 hm B hBp hBc
  have hξrange_tor : ∀ y : ξ.range, ∀ i, (y.1 i) ^ r = 1 := by
    intro y i
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 y.2
    rw [← hx]
    exact hξtor x i
  have htorsionLog_one : torsionLog hCr
      (1 : (powMonoidHom r : C →* C).ker) = 0 := by
    have h := torsionLog_mul hCr (1 : (powMonoidHom r : C →* C).ker) 1
    rw [mul_one] at h
    have h' : torsionLog hCr 1 + 0 =
        torsionLog hCr 1 + torsionLog hCr 1 := by
      rw [add_zero]
      exact h
    exact (add_left_cancel h').symm
  have hΨmem : ∀ y : ξ.range, (fun i =>
      torsionLog hCr ⟨y.1 i, by
        rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact hξrange_tor y i⟩) ∈ U := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hw
    dsimp only [U]
    constructor
    · have hξi0 : ξ x i0 = 1 := by simp [ξ]
      change torsionLog hCr ⟨ξ x i0, _⟩ = 0
      convert htorsionLog_one using 2
      exact Subtype.ext hξi0
    · intro b hb
      obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hb
      let xl : Fin m → C := (x.1).left
      let pr : Perm (Fin m) := (p.1).right
      have hpx : pr = b := hp
      have hxeq : x.1 = monT xl := eq_monT_of_right_eq_one (hT'right x.1 x.2)
      have hcommP : ⁅(p.1 : Mon C m), x.1⁆ ∈ S := by
        exact hcomm p p.2 x.1 (hT'leP x.2)
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hcommP
      have hcommz : (xl ∘ pr.symm) * xl⁻¹ = fun _ => z := by
        have h2 : ⁅(p.1 : Mon C m), monT xl⁆ = monScalar C m z := by
          rw [hxeq] at hz
          exact hz.symm
        rw [mon_comm_monT p.1 xl, monScalar_apply] at h2
        exact monT_injective h2
      have hzmem : z ∈ (powMonoidHom r : C →* C).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply]
        have h1 := congrFun hcommz (pr.symm i0)
        rw [← h1]
        simp only [Pi.mul_apply, Pi.inv_apply, Function.comp_apply]
        rw [← div_eq_mul_inv, div_pow, hpowD x (pr.symm (pr.symm i0)),
          hpowD x (pr.symm i0)]
        simp [div_eq_mul_inv]
      refine ⟨torsionLog hCr ⟨z, hzmem⟩, fun i => ?_⟩
      have hb_eq : b⁻¹ i = pr.symm i := by rw [← hpx]; rfl
      have hzrel : ξ x (pr.symm i) = z * ξ x i := by
        have hzi := congrFun hcommz i
        change xl (pr.symm i) / xl i0 = z * (xl i / xl i0)
        rw [← hzi]
        change xl (pr.symm i) / xl i0 =
          (xl (pr.symm i) * (xl i)⁻¹) * (xl i / xl i0)
        generalize ha : xl (pr.symm i) = a
        generalize hb : xl i = bb
        generalize hc : xl i0 = cc
        change a / cc = (a * bb⁻¹) * (bb / cc)
        have key : ∀ x y z : C, x * y⁻¹ * (y * z⁻¹) = x * z⁻¹ := by
          intro x y z
          group
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact (key a bb cc).symm
      have h1 : (⟨ξ x (b⁻¹ i), by
            rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact hξtor x (b⁻¹ i)⟩ :
            (powMonoidHom r : C →* C).ker) =
          ⟨z, hzmem⟩ * ⟨ξ x i, by
            rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact hξtor x i⟩ := by
        apply Subtype.ext
        rw [hb_eq]
        exact hzrel
      have h2 := congrArg (torsionLog hCr) h1
      rw [torsionLog_mul] at h2
      change torsionLog hCr ⟨ξ x (b⁻¹ i), _⟩ -
        torsionLog hCr ⟨ξ x i, _⟩ = torsionLog hCr ⟨z, hzmem⟩
      rw [h2]
      abel
  let Ψ : ξ.range → U := fun y => ⟨_, hΨmem y⟩
  have hΨinj : Function.Injective Ψ := by
    intro y y' h
    apply Subtype.ext
    funext i
    have h1 : torsionLog hCr ⟨y.1 i, _⟩ = torsionLog hCr ⟨y'.1 i, _⟩ :=
      congrFun (congrArg Subtype.val h) i
    exact congrArg Subtype.val (torsionLog_injective hCr h1)
  let diag : T' →* Mon C m :=
    { toFun := fun y => monT y.1.left
      map_one' := by
        change monT (1 : Fin m → C) = 1
        exact map_one _
      map_mul' := by
        intro x y
        have hx : x.1.right = 1 := hT'right x.1 x.2
        rw [← monT_mul]
        congr 1
        change (x.1 * y.1).left = x.1.left * y.1.left
        rw [SemidirectProduct.mul_left, hx]
        simp }
  have hdiag_inj : Function.Injective diag := by
    intro x y h
    have h1 : x.1.left = y.1.left := monT_injective h
    apply Subtype.ext
    rw [eq_monT_of_right_eq_one (hT'right x.1 x.2),
      eq_monT_of_right_eq_one (hT'right y.1 y.2), h1]
  have hdiag_map : ξ.ker.map diag = T' ⊓ S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ξ x = 1 := MonoidHom.mem_ker.1 hx
      have hconst : x.1.left = fun _ => x.1.left i0 := by
        funext i
        have h := congrFun hx' i
        change x.1.left i / x.1.left i0 = 1 at h
        rwa [div_eq_one] at h
      refine ⟨?_, ?_⟩
      · change monT x.1.left ∈ T'
        rw [show monT x.1.left = x.1 from
          (eq_monT_of_right_eq_one (hT'right x.1 x.2)).symm]
        exact x.2
      · change monT x.1.left ∈ S
        rw [hconst, ← monScalar_apply]
        exact MonoidHom.mem_range.2 ⟨_, rfl⟩
    · rintro ⟨hzT, hzS⟩
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hzS
      refine ⟨⟨monT (fun _ => c), ?_⟩, ?_, ?_⟩
      · rw [← monScalar_apply]
        show monScalar C m c ∈ T'
        rw [hc]
        exact hzT
      · ext i
        change c / c = 1
        simp
      · show monT (fun _ => c) = z
        rw [← monScalar_apply]
        exact hc
  have hξker : Nat.card ξ.ker = Nat.card ↥(P ⊓ S) := by
    rw [← hT'inter]
    rw [← Subgroup.card_map_of_injective (K := ξ.ker) hdiag_inj, hdiag_map]
  have hξrange : Nat.card ξ.range ≤ Nat.card U :=
    Nat.card_le_card_of_injective Ψ hΨinj
  have hξcard : Nat.card T' = Nat.card ξ.ker * Nat.card ξ.range :=
    (Subgroup.card_ker_mul_card_range ξ).symm
  calc Nat.card P = Nat.card T' * Nat.card B := hcardP
    _ = (Nat.card ξ.ker * Nat.card ξ.range) * Nat.card B := by rw [hξcard]
    _ ≤ (Nat.card ↥(P ⊓ S) * Nat.card U) * Nat.card B := by
        rw [hξker]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hξrange)
    _ = Nat.card ↥(P ⊓ S) * (Nat.card U * Nat.card B) := by ring
    _ ≤ Nat.card ↥(P ⊓ S) * r ^ (m - 1) := by
        exact Nat.mul_le_mul_left _ (by rw [Nat.mul_comm]; exact hU)
    _ = r ^ (m - 1) * Nat.card ↥(P ⊓ S) := by rw [Nat.mul_comm]


private theorem mem_scalars_of_monEmb_mem_center
    {C : Type} [CommGroup C] {F : Type} [Field F] (e : C →* Fˣ)
    (he : Function.Injective e) {m : ℕ} (hm : 1 ≤ m) {y : Mon C m}
    (hy : monEmb (F := F) e m y ∈ Subgroup.center (GL (Fin m) F)) :
    y ∈ (monScalar C m).range := by
  classical
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hy
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hy
  have hent : ∀ i, y.right⁻¹ i = i := by
    intro i
    have h := congrFun (congrFun (congrArg (fun A : GL (Fin m) F =>
      (A : Matrix (Fin m) (Fin m) F)) hu) i) i
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      coe_monEmb_apply] at h
    simp only [Matrix.diagonal_apply_eq] at h
    by_contra hne
    rw [if_neg hne] at h
    exact u.ne_zero h
  have hent_eq : ∀ i, e (y.left i) = u := by
    intro i
    have h := congrFun (congrFun (congrArg (fun A : GL (Fin m) F =>
      (A : Matrix (Fin m) (Fin m) F)) hu) i) i
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      coe_monEmb_apply, if_pos (hent i)] at h
    exact Units.ext (by simpa only [Matrix.diagonal_apply_eq] using h.symm)
  have hright : y.right = 1 := by
    have h : y.right⁻¹ = 1 := Equiv.ext hent
    exact inv_eq_one.mp h
  let i0 : Fin m := ⟨0, hm⟩
  refine MonoidHom.mem_range.2 ⟨y.left i0, ?_⟩
  have hconst : y.left = fun _ => y.left i0 := by
    funext i
    apply he
    rw [hent_eq i, hent_eq i0]
  rw [eq_monT_of_right_eq_one hright, monScalar_apply]
  congr 1
  exact hconst.symm

theorem card_le_pow_sub_one_mul_card_inf_scalars_GL
    {F : Type} [Field F] [Finite F] {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrF : r ∣ Nat.card F - 1) (R : Subgroup (GL (Fin m) F)) (hR : IsPGroup r R)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ Subgroup.center (GL (Fin m) F))
    (hpow : ∀ x ∈ R, x ^ r ∈ Subgroup.center (GL (Fin m) F)) :
    Nat.card R ≤ r ^ (m - 1) *
      Nat.card ↥(R ⊓ Subgroup.center (GL (Fin m) F)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : Subsingleton (GL (Fin 0) F) := by
      rw [← not_nontrivial_iff_subsingleton]
      rintro ⟨A, B, hAB⟩
      apply hAB
      apply Units.ext
      ext i
      exact Fin.elim0 i
    have hRbot : R = ⊥ := Subgroup.eq_bot_of_subsingleton R
    have hSbot : (R ⊓ Subgroup.center (GL (Fin 0) F)) = ⊥ := by
      rw [hRbot, bot_inf_eq]
    rw [hRbot, Subgroup.card_bot]
    simp
  · haveI : Fact r.Prime := ⟨hr⟩
    haveI : Fintype F := Fintype.ofFinite F
    have hcardF : r ∣ Fintype.card F - 1 := by rwa [Nat.card_eq_fintype_card] at hrF
    obtain ⟨g, hg⟩ := exists_conj_monomial_GL (F := F) (r := r) (m := m) hr2 hcardF hm R hR
    let e : unitsPPart F r →* Fˣ := (unitsPPart F r).subtype
    have he : Function.Injective e := Subgroup.subtype_injective _
    let H : Subgroup (GL (Fin m) F) := R.map (MulAut.conj g).toMonoidHom
    have hHle : H ≤ (monEmb (F := F) e m).range := by
      rintro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact hg x hx
    let P : Subgroup (Mon (unitsPPart F r) m) := H.comap (monEmb (F := F) e m)
    have hPmap : P.map (monEmb (F := F) e m) = H := by
      change (H.comap (monEmb (F := F) e m)).map (monEmb (F := F) e m) = H
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hHle]
    have hPcard : Nat.card P = Nat.card H := by
      rw [← Subgroup.card_map_of_injective (K := P) (monEmb_injective (F := F) he m), hPmap]
    have hHR : Nat.card H = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    haveI : Nontrivial (unitsPPart F r) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [card_unitsPPart F r]
      have hF2 : 1 < Fintype.card F := Fintype.one_lt_card
      have hpad : 1 ≤ padicValNat r (Fintype.card F - 1) :=
        one_le_padicValNat_of_dvd (by omega) hcardF
      exact Nat.one_lt_pow (by omega) hr.one_lt
    have hpowP : ∀ y ∈ P, y ^ r ∈ (monScalar (unitsPPart F r) m).range := by
      intro y hy
      have hyH : monEmb (F := F) e m y ∈ H := hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hyH
      have hxr : x ^ r ∈ Subgroup.center (GL (Fin m) F) := hpow x hx
      have hSconj : (MulAut.conj g x) ^ r ∈ Subgroup.center (GL (Fin m) F) := by
        rw [← map_pow (MulAut.conj g) x r]
        exact Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center (GL (Fin m) F)).Normal) (x ^ r) hxr g
      have hmon : monEmb (F := F) e m (y ^ r) ∈ Subgroup.center (GL (Fin m) F) := by
        rw [map_pow (monEmb (F := F) e m) y r, ← hxy]
        exact hSconj
      exact mem_scalars_of_monEmb_mem_center e he hm hmon
    have hcommP : ∀ y ∈ P, ∀ z ∈ P,
        ⁅y, z⁆ ∈ (monScalar (unitsPPart F r) m).range := by
      intro y hy z hz
      have hyH : monEmb (F := F) e m y ∈ H := hy
      have hzH : monEmb (F := F) e m z ∈ H := hz
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hyH
      obtain ⟨x', hx', hx'y⟩ := Subgroup.mem_map.1 hzH
      have hxr : ⁅x, x'⁆ ∈ Subgroup.center (GL (Fin m) F) := hcomm x hx x' hx'
      have hSconj : (MulAut.conj g ⁅x, x'⁆) ∈ Subgroup.center (GL (Fin m) F) :=
        Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center (GL (Fin m) F)).Normal) ⁅x, x'⁆ hxr g
      have hconj : ⁅(MulAut.conj g) x, (MulAut.conj g) x'⁆ =
          (MulAut.conj g) ⁅x, x'⁆ :=
        (map_commutatorElement (MulAut.conj g) x x').symm
      have hmon : monEmb (F := F) e m ⁅y, z⁆ ∈ Subgroup.center (GL (Fin m) F) := by
        rw [map_commutatorElement, ← hxy, ← hx'y]
        change ⁅(MulAut.conj g) x, (MulAut.conj g) x'⁆ ∈
          Subgroup.center (GL (Fin m) F)
        rw [hconj]
        exact hSconj
      exact mem_scalars_of_monEmb_mem_center e he hm hmon
    have hmon := card_le_pow_sub_one_mul_card_inf_scalars_mon (r := r) (m := m) hr2
      (unitsPPart_isCyclic F r) (unitsPPart_isPGroup F r) hm P hpowP hcommP
    have hSmap : (P ⊓ (monScalar (unitsPPart F r) m).range).map (monEmb (F := F) e m) =
        H ⊓ Subgroup.center (GL (Fin m) F) := by
      ext z
      constructor
      · rintro ⟨y, ⟨hyP, hyS⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [← hPmap]
          exact Subgroup.mem_map_of_mem _ hyP
        · obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hyS
          rw [monEmb_monScalar, Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact MonoidHom.mem_range.2 ⟨e c, rfl⟩
      · rintro ⟨hzH, hzS⟩
        have hzP : z ∈ P.map (monEmb (F := F) e m) := by rwa [hPmap]
        obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.1 hzP
        have hyS : y ∈ (monScalar (unitsPPart F r) m).range :=
          mem_scalars_of_monEmb_mem_center e he hm hzS
        exact ⟨y, ⟨hyP, hyS⟩, rfl⟩
    have hScard : Nat.card ↥(P ⊓ (monScalar (unitsPPart F r) m).range) =
        Nat.card ↥(H ⊓ Subgroup.center (GL (Fin m) F)) := by
      rw [← hSmap, Subgroup.card_map_of_injective (K := P ⊓ _) (monEmb_injective (F := F) he m)]
    have hHcard : Nat.card ↥(H ⊓ Subgroup.center (GL (Fin m) F)) =
        Nat.card ↥(R ⊓ Subgroup.center (GL (Fin m) F)) := by
      have hHsinf : H ⊓ Subgroup.center (GL (Fin m) F) =
          (R ⊓ Subgroup.center (GL (Fin m) F)).map (MulAut.conj g).toMonoidHom := by
        dsimp only [H]
        ext z
        constructor
        · rintro ⟨hzH, hzS⟩
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hzH
          have hxS : x ∈ Subgroup.center (GL (Fin m) F) := by
            have h := Subgroup.Normal.conj_mem
              (inferInstance : (Subgroup.center (GL (Fin m) F)).Normal)
              ((MulAut.conj g) x) hzS g⁻¹
            have hx' : g⁻¹ * ((MulAut.conj g) x) * g⁻¹⁻¹ = x := by
              rw [inv_inv, MulAut.conj_apply]
              group
            rwa [hx'] at h
          exact ⟨x, ⟨hx, hxS⟩, rfl⟩
        · rintro ⟨x, ⟨hx, hxS⟩, rfl⟩
          exact ⟨Subgroup.mem_map_of_mem _ hx,
            Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center (GL (Fin m) F)).Normal) x hxS g⟩
      rw [hHsinf, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    calc Nat.card R = Nat.card H := hHR.symm
      _ = Nat.card P := hPcard.symm
      _ ≤ r ^ (m - 1) * Nat.card ↥(P ⊓ (monScalar (unitsPPart F r) m).range) := hmon
      _ = r ^ (m - 1) * Nat.card ↥(H ⊓ Subgroup.center (GL (Fin m) F)) := by rw [hScard]
      _ = r ^ (m - 1) * Nat.card ↥(R ⊓ Subgroup.center (GL (Fin m) F)) := by rw [hHcard]

end CFSG.GroupTheory
