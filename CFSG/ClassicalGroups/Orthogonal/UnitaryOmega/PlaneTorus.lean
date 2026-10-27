module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.KLinearOmega
import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders

section Mul

variable {F K : Type} [Field F] [Field K] [Algebra F K]

@[expose] noncomputable def planeMul {m : ℕ} (u : Fin m → Kˣ) : (Fin m → K) ≃ₗ[F] (Fin m → K) where
  toFun x i := (u i : K) * x i
  invFun x i := (((u i)⁻¹ : Kˣ) : K) * x i
  map_add' x y := by
    funext i
    exact mul_add _ _ _
  map_smul' c x := by
    funext i
    exact mul_smul_comm c (u i : K) (x i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

theorem planeMul_apply {m : ℕ} (u : Fin m → Kˣ) (x : Fin m → K) (i : Fin m) :
    planeMul (F := F) u x i = (u i : K) * x i := rfl

@[expose] noncomputable def planeDiag (m : ℕ) :
    (Fin m → Kˣ) →* (((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) where
  toFun u := hypExt (planeMul u)
  map_one' := LinearEquiv.ext fun v => Prod.ext rfl (funext fun i => by
    show ((1 : Fin m → Kˣ) i : K) * v.2 i = v.2 i
    simp)
  map_mul' u w := LinearEquiv.ext fun v => Prod.ext rfl (funext fun i => by
    show ((u * w) i : K) * v.2 i = (u i : K) * ((w i : K) * v.2 i)
    rw [Pi.mul_apply, Units.val_mul, mul_assoc])

theorem planeDiag_apply (m : ℕ) (u : Fin m → Kˣ) (v : (F × F) × (Fin m → K)) :
    planeDiag m u v = (v.1, fun i => (u i : K) * v.2 i) := rfl

theorem zmodHom_pow_eq_one_of_dvd {M : Type*} [Monoid M] {p N : ℕ} (hpN : p ∣ N)
    (χ : Multiplicative (ZMod p) →* M) (a : Multiplicative (ZMod p)) : χ a ^ N = 1 := by
  obtain ⟨k, rfl⟩ := hpN
  have ha : a ^ p = 1 := by
    change Multiplicative.ofAdd (p • Multiplicative.toAdd a) = Multiplicative.ofAdd 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [pow_mul, ← map_pow, ha, map_one, one_pow]

end Mul

section Char

variable {K : Type} [Field K] [Finite K] {f : ℕ}

theorem exists_injective_unitChar {p : ℕ} [Fact p.Prime] (hK : UnitaryFieldData 2 f K)
    (hpq : p ∣ 2 ^ f + 1) : ∃ χ : Multiplicative (ZMod p) →* Kˣ, Function.Injective χ := by
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK.card]
    have hfac : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      rw [show 2 ^ (2 * f) = (2 ^ f) ^ 2 by rw [← pow_mul]; congr 1; omega]
      rw [← Nat.sq_sub_sq, one_pow]
    rw [hfac]
    exact dvd_mul_of_dvd_left hpq _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvd
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hgne : g ≠ 1 := by
    intro h
    have h1 : orderOf g = 1 := by rw [h, orderOf_one]
    rw [hg] at h1
    exact (Fact.out : p.Prime).ne_one h1
  let χ : Multiplicative (ZMod p) →* Kˣ :=
    AddMonoidHom.toMultiplicativeLeft ((ZMod.lift p)
      ⟨zmultiplesHom (Additive Kˣ) (Additive.ofMul g), by
        rw [zmultiplesHom_apply]
        show ((p : ℕ) : ℤ) • Additive.ofMul g = 0
        rw [natCast_zsmul, ← ofMul_pow, hgp]
        rfl⟩)
  have hχ1 : χ (Multiplicative.ofAdd (1 : ZMod p)) = g := by
    rw [show χ = AddMonoidHom.toMultiplicativeLeft ((ZMod.lift p)
      ⟨zmultiplesHom (Additive Kˣ) (Additive.ofMul g), by
        rw [zmultiplesHom_apply]
        show ((p : ℕ) : ℤ) • Additive.ofMul g = 0
        rw [natCast_zsmul, ← ofMul_pow, hgp]
        rfl⟩) from rfl]
    rw [AddMonoidHom.toMultiplicativeLeft_apply_apply]
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) = (1 : ZMod p) from rfl]
    rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) by norm_num, ZMod.lift_coe,
      zmultiplesHom_apply]
    simp
  have hker : χ.ker = ⊥ := by
    have hdvdker : Nat.card χ.ker ∣ p := by
      simpa using Subgroup.card_subgroup_dvd_card χ.ker
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvdker with h1 | hp
    · exact Subgroup.eq_bot_of_card_eq χ.ker h1
    · exfalso
      have htop : χ.ker = ⊤ := by
        refine Subgroup.eq_top_of_card_eq χ.ker ?_
        rw [hp]
        exact ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)).symm
      have hmem : Multiplicative.ofAdd (1 : ZMod p) ∈ χ.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hχ1] at hmem
      exact hgne hmem
  exact ⟨χ, MonoidHom.ker_eq_bot_iff χ |>.mp hker⟩

end Char

section Omega

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

include E in
theorem card_base_eq_two_pow (hK : UnitaryFieldData 2 f K) : Nat.card F = 2 ^ f := by
  have : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have h1 : Nat.card K = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), E.finrank_eq]
  have h : Nat.card F ^ 2 = (2 ^ f) ^ 2 := by
    rw [← h1, hK.card, ← pow_mul, mul_comm]
  exact Nat.pow_left_injective (by norm_num) h

theorem planeDiag_mem_normOmega {m : ℕ} (hm : 2 ≤ m) {u : Fin m → Kˣ}
    (hu : ∀ i, u i ^ (2 ^ f + 1) = 1) : planeDiag m u ∈ normOmega E m := by
  have hg : planeMul (F := F) u ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E m) := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    apply (algebraMap F K).injective
    rw [algebraMap_Qn, algebraMap_Qn]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hval : (u i : K) ^ (2 ^ f + 1) = 1 := by
      have h := congrArg Units.val (hu i)
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
    have hnorm : (u i : K) * unitaryInvolution K 2 f (u i : K) = 1 := by
      rw [unitaryInvolution_apply, ← pow_succ']
      exact hval
    rw [planeMul_apply, map_mul]
    calc
      (u i * x i) * (unitaryInvolution K 2 f (u i) * unitaryInvolution K 2 f (x i))
          = ((u i) * unitaryInvolution K 2 f (u i)) *
              (x i * unitaryInvolution K 2 f (x i)) := by ring
      _ = x i * unitaryInvolution K 2 f (x i) := by rw [hnorm, one_mul]
  have hlin : ∀ (c : K) (x : Fin m → K),
      planeMul (F := F) u (c • x) = c • planeMul (F := F) u x := by
    intro c x
    funext i
    rw [planeMul_apply, Pi.smul_apply, Pi.smul_apply, planeMul_apply, smul_eq_mul, smul_eq_mul]
    ring
  exact hypExt_mem_orthDerived_of_kLinear E hm hg hlin

@[expose] noncomputable def normPlaneTorus {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) : (Fin m → Multiplicative (ZMod p)) →* normOmega E m :=
  ((planeDiag m).comp (χ.compLeft (Fin m))).codRestrict (normOmega E m) fun t =>
    planeDiag_mem_normOmega E hm fun i => zmodHom_pow_eq_one_of_dvd hpq χ (t i)

theorem normPlaneTorus_apply {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) (t : Fin m → Multiplicative (ZMod p))
    (v : (F × F) × (Fin m → K)) :
    ((normPlaneTorus E hm hpq χ t : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
      (v.1, fun i => (χ (t i) : K) * v.2 i) := rfl

theorem normPlaneTorus_injective {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ) :
    Function.Injective (normPlaneTorus E hm hpq χ) := by
  intro t s hts
  funext i
  have hv := congrArg (fun e : normOmega E m =>
    (e : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
      ((0, 0), Pi.single i 1)) hts
  rw [normPlaneTorus_apply E hm hpq χ t,
    normPlaneTorus_apply E hm hpq χ s] at hv
  have h := congrFun (congrArg Prod.snd hv) i
  simp only [Pi.single_eq_same, mul_one] at h
  exact hχ (Units.ext h)

theorem center_normOmega_eq_bot {m : ℕ} (hm : 2 ≤ m) : Subgroup.center (normOmega E m) = ⊥ := by
  have hFinF : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have hCharF : CharP F 2 :=
    RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have hFinK : Module.Finite F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have hFinPair : Module.Finite F (F × F) :=
    @Module.Finite.prod F F F _ _ _ _ _
      (Module.Finite.self F) (Module.Finite.self F)
  have hFinPi : Module.Finite F (Fin m → K) :=
    @Module.Finite.pi F _ (Fin m) (fun _ => K) _ _ _ (fun _ => hFinK)
  have hFinV : Module.Finite F ((F × F) × (Fin m → K)) :=
    @Module.Finite.prod F (F × F) (Fin m → K) _ _ _ _ _ hFinPair hFinPi
  have hNontr : Nontrivial ((F × F) × (Fin m → K)) :=
    ⟨⟨((1, 0), 0), ((0, 0), 0), by simp⟩⟩
  exact @CFSG.RankThree.PartOne.center_orthDerived_eq_bot F _ hCharF
    ((F × F) × (Fin m → K)) _ _ hFinV (normHypForm E m) hFinF hNontr
    (normHypForm_polarBilin_nondegenerate E m) (exists_totallySingular_three_hypSum E hm)

theorem normOmega_map_conj {m : ℕ}
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)) :
    (normOmega E m).map (MulAut.conj g).toMonoidHom = normOmega E m := by
  have hH : (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)).map
        (MulAut.conj g).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) := by
    apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      exact mul_mem (mul_mem hg hh) (inv_mem hg)
    · intro h hh
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * h * g, mul_mem (mul_mem (inv_mem hg) hh) hg, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [show normOmega E m = ⁅TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m),
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)⁆ from rfl,
    Subgroup.map_commutator, hH]

@[expose] noncomputable def normOmegaConj {m : ℕ}
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)) :
    MulAut (normOmega E m) :=
  ((MulAut.conj g).subgroupMap (normOmega E m)).trans
    (MulEquiv.subgroupCongr (by
      rw [← MulEquiv.toMonoidHom_eq_coe]
      exact normOmega_map_conj E hg))

theorem normOmegaConj_apply {m : ℕ}
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)) (s : normOmega E m) :
    ((normOmegaConj E hg s : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) =
      g * (s : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹ := rfl

@[expose] noncomputable def planeBar {m : ℕ} (S : Finset (Fin m)) :
    (Fin m → K) ≃ₗ[F] (Fin m → K) where
  toFun x i := if i ∈ S then unitaryInvolution K 2 f (x i) else x i
  invFun x i := if i ∈ S then unitaryInvolution K 2 f (x i) else x i
  map_add' x y := by
    funext i
    by_cases hi : i ∈ S <;> simp [hi]
  map_smul' c x := by
    funext i
    by_cases hi : i ∈ S
    · simp only [hi, if_true, Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, map_mul, E.fix]
    · simp [hi]
  left_inv x := by
    funext i
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      exact E.isUnitary.invol (x i)
    · simp [hi]
  right_inv x := by
    funext i
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      exact E.isUnitary.invol (x i)
    · simp [hi]

@[expose] noncomputable def normBar {m : ℕ} (S : Finset (Fin m)) :
    ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) :=
  hypExt (planeBar E S)

private theorem planeBar_apply {m : ℕ} (S : Finset (Fin m)) (x : Fin m → K) (i : Fin m) :
    planeBar E S x i = if i ∈ S then unitaryInvolution K 2 f (x i) else x i := rfl

theorem normBar_mem_orthogonalGroup {m : ℕ} (S : Finset (Fin m)) :
    normBar E S ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) := by
  change hypExt (planeBar E S) ∈
    TauCeti.QuadraticMap.orthogonalGroup (hypSum (Qn E m))
  refine hypExt_mem (Q' := Qn E m) ?_
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  apply (algebraMap F K).injective
  rw [algebraMap_Qn, algebraMap_Qn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [planeBar_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, E.isUnitary.invol]
    exact mul_comm _ _
  · rw [if_neg hi]

private theorem normBar_apply {m : ℕ} (S : Finset (Fin m))
    (v : (F × F) × (Fin m → K)) :
    normBar E S v =
      (v.1, fun i => if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i) := rfl

private theorem normBar_mul_self {m : ℕ} (S : Finset (Fin m)) :
    normBar E S * normBar E S = 1 := by
  apply LinearEquiv.ext
  intro v
  change normBar E S (normBar E S v) = v
  rw [normBar_apply, normBar_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  show (if i ∈ S then unitaryInvolution K 2 f
        (if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i) else
        (if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i)) = v.2 i
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi, E.isUnitary.invol]
  · rw [if_neg hi, if_neg hi]

private theorem unitaryInvolution_unitChar_eq_inv {p : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) (a : Multiplicative (ZMod p)) :
    unitaryInvolution K 2 f (χ a : K) = ((χ a : K))⁻¹ := by
  have h := zmodHom_pow_eq_one_of_dvd hpq χ a
  have hval : (χ a : K) ^ (2 ^ f + 1) = 1 := by
    have h' := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h'
  have hmul : (χ a : K) * unitaryInvolution K 2 f (χ a : K) = 1 := by
    rw [unitaryInvolution_apply, ← pow_succ']
    exact hval
  exact eq_inv_of_mul_eq_one_right hmul

theorem normOmegaConj_normBar_normPlaneTorus {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) (S : Finset (Fin m))
    (t : Fin m → Multiplicative (ZMod p)) :
    normOmegaConj E (normBar_mem_orthogonalGroup E S) (normPlaneTorus E hm hpq χ t) =
      normPlaneTorus E hm hpq χ (fun i => if i ∈ S then (t i)⁻¹ else t i) := by
  have hinv : (normBar E S)⁻¹ = normBar E S :=
    inv_eq_of_mul_eq_one_left (normBar_mul_self E S)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [normOmegaConj_apply, hinv]
  change (normBar E S * (normPlaneTorus E hm hpq χ t : normOmega E m) * normBar E S) v =
    ((normPlaneTorus E hm hpq χ (fun i => if i ∈ S then (t i)⁻¹ else t i) :
      normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [show normBar E S v =
      (v.1, fun i => if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i) from
    normBar_apply E S v]
  rw [show ((normPlaneTorus E hm hpq χ t : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (v.1, fun i => if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i) =
      (v.1, fun i => (χ (t i) : K) *
        (if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i)) from
    normPlaneTorus_apply E hm hpq χ t _]
  rw [show normBar E S (v.1, fun i => (χ (t i) : K) *
        (if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i)) =
      (v.1, fun i => if i ∈ S then unitaryInvolution K 2 f ((χ (t i) : K) *
        (if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i)) else
          (χ (t i) : K) *
            (if i ∈ S then unitaryInvolution K 2 f (v.2 i) else v.2 i)) from
    normBar_apply E S _]
  rw [show ((normPlaneTorus E hm hpq χ (fun i => if i ∈ S then (t i)⁻¹ else t i) :
        normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) v =
      (v.1, fun i => (χ (if i ∈ S then (t i)⁻¹ else t i) : K) * v.2 i) from
    normPlaneTorus_apply E hm hpq χ _ v]
  refine Prod.ext rfl (funext fun i => ?_)
  by_cases hi : i ∈ S
  · simp only [if_pos hi]
    rw [map_mul, unitaryInvolution_unitChar_eq_inv hpq χ (t i), E.isUnitary.invol, map_inv,
      Units.val_inv_eq_inv_val]
  · simp only [if_neg hi]

end Omega

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
