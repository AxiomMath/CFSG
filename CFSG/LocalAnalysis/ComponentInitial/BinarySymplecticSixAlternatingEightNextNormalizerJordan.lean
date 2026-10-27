module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightNextNormalizerKernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

theorem eq_sum_single (u : Fin 3 → ZMod 2) :
    u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
  funext j
  fin_cases j <;> simp

theorem symThreeDiag_add (B B' : binarySymMatrices 3) :
    symThreeDiag ((B + B' : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
        symThreeDiag (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  funext k
  rfl

theorem symThreeDiag_altLabel (v : Fin 3 → ZMod 2) :
    symThreeDiag ((DegreeEight.altLabel v : binarySymMatrices 3) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 :=
  BinarySymThreeOrbit.mem_altSym_iff.1 (altLabel_mem_altSym v)

@[expose] def altDiag : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) →+ binarySymMatrices 3 where
  toFun p := DegreeEight.altLabel p.1 + symThreeDiagSection p.2
  map_zero' := by
    rw [Prod.fst_zero, Prod.snd_zero, DegreeEight.altLabel_zero, map_zero, add_zero]
  map_add' p q := by
    rw [Prod.fst_add, Prod.snd_add, altLabel_add, map_add]
    abel

theorem altDiag_apply (v w : Fin 3 → ZMod 2) :
    altDiag (v, w) = DegreeEight.altLabel v + symThreeDiagSection w :=
  rfl

theorem symThreeDiag_altDiag (v w : Fin 3 → ZMod 2) :
    symThreeDiag ((altDiag (v, w) : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      w := by
  rw [altDiag_apply, symThreeDiag_add, symThreeDiag_altLabel, symThreeDiag_diagSection, zero_add]

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf

include hzC hsup hinf hz hb hnd hV he halt in
theorem exists_jordan {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂lab : ∀ B ∈ BinarySymThreeOrbit.altSym, ∃ c ∈ C₂,
      z⁻¹ * c⁻¹ * z * c = (θ₂).symm (Multiplicative.ofAdd (B, 0))) :
    ∃ Ψ : Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) ≃* C₂,
      (∀ u v w, z * (Ψ (Multiplicative.ofAdd (u, v, w)) : G) * z⁻¹ =
        Ψ (Multiplicative.ofAdd (u, u + v, w))) ∧
      (∀ u v w, (Ψ (Multiplicative.ofAdd (u, v, w)) : G) ∈ 𝒜 ↔ u = 0) ∧
      ∀ u v w, (Ψ (Multiplicative.ofAdd (u, v, w)) : G) ∈
        tauSet φ e (fun B => ∀ i, B i i = 0) ↔ u = 0 ∧ w = 0 := by
  classical
  obtain ⟨ν, -, hν1, -, hν3, -, -, -, -, -, -⟩ :=
    exists_nu_sigma hzC hsup hinf hz hb hnd hV φ he halt
  have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
  have hz2 := z_mul_self hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have := hC₂e.toIsMulCommutative
  let _ : CommGroup C₂ :=
    { (inferInstance : Group C₂) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_isElementaryAbelian hC₂e a.2 b.2) }
  set νC : C₂ →* Multiplicative ↥BinarySymThreeOrbit.altSym := ν.comp (inclusion hC₂D) with hνC
  set lab : C₂ → binarySymMatrices 3 := fun c =>
    ((Multiplicative.toAdd (νC c) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3) with hlab
  have hlab_mul : ∀ c c' : C₂, lab (c * c') = lab c + lab c' := fun c c' => by
    simp only [hlab, map_mul, toAdd_mul, AddSubgroup.coe_add]
  have hνc : ∀ c : C₂, z⁻¹ * (c : G)⁻¹ * z * c = tauHom φ he (Multiplicative.ofAdd (lab c)) :=
    fun c => hν1 ⟨c, hC₂D c.2⟩
  have hlab_eq_zero : ∀ c : C₂, lab c = 0 ↔ (c : G) ∈ 𝒜 := by
    intro c
    constructor
    · intro h
      have h1 : (⟨c, hC₂D c.2⟩ : 𝒟) ∈ ν.ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective (Subtype.ext h)
      rw [hν3, mem_subgroupOf] at h1
      exact hC₂R.le (mem_inf.2 ⟨c.2, h1⟩)
    · intro h
      have h1 : (⟨c, hC₂D c.2⟩ : 𝒟) ∈ ν.ker := by
        rw [hν3, mem_subgroupOf]
        exact mem_sup_left h
      rw [MonoidHom.mem_ker] at h1
      change ((Multiplicative.toAdd (ν ⟨c, hC₂D c.2⟩) : ↥BinarySymThreeOrbit.altSym) :
        binarySymMatrices 3) = 0
      rw [h1]
      rfl
  have hzc : ∀ c : C₂, z * (c : G) * z⁻¹ = c * tauHom φ he (Multiplicative.ofAdd (lab c)) := by
    intro c
    have h1 := hνc c
    have htz : tauHom φ he (Multiplicative.ofAdd (lab c)) * z =
        z * tauHom φ he (Multiplicative.ofAdd (lab c)) :=
      RadicalLabels.mul_comm_z hzC (tauHom_mem φ he _)
    calc z * (c : G) * z⁻¹ = c * (z * (z⁻¹ * (c : G)⁻¹ * z * c)) * z⁻¹ := by group
      _ = c * (z * tauHom φ he (Multiplicative.ofAdd (lab c))) * z⁻¹ := by rw [h1]
      _ = c * (tauHom φ he (Multiplicative.ofAdd (lab c)) * z) * z⁻¹ := by rw [htz]
      _ = c * tauHom φ he (Multiplicative.ofAdd (lab c)) := by group
  have hlift : ∀ i : Fin 3, ∃ c : C₂, lab c = DegreeEight.altLabel (Pi.single i 1) := by
    intro i
    obtain ⟨c, hc, hcB⟩ := hC₂lab _ (altLabel_mem_altSym (Pi.single i 1))
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one] at hcB
    have h1 := hνc ⟨c, hc⟩
    rw [show z⁻¹ * ((⟨c, hc⟩ : C₂) : G)⁻¹ * z * ((⟨c, hc⟩ : C₂) : G) = z⁻¹ * c⁻¹ * z * c from rfl,
      hcB] at h1
    exact (Multiplicative.ofAdd.injective (tauHom_injective φ he h1)).symm
  choose x hx using hlift
  have hx2 : ∀ i, x i ^ 2 = 1 := fun i => by
    rw [sq]
    exact Subtype.ext (mul_self_of_isElementaryAbelian hC₂e (x i).2)
  let sC : Multiplicative (Fin 3 → ZMod 2) →* C₂ :=
    MonoidHom.mk' (fun u => x 0 ^ (Multiplicative.toAdd u 0).val *
      x 1 ^ (Multiplicative.toAdd u 1).val * x 2 ^ (Multiplicative.toAdd u 2).val) fun u u' => by
        simp only [toAdd_mul, Pi.add_apply]
        rw [OddQuadraticFive.pow_val_add_of_sq (hx2 0), OddQuadraticFive.pow_val_add_of_sq (hx2 1),
          OddQuadraticFive.pow_val_add_of_sq (hx2 2)]
        ac_rfl
  have hsC : ∀ u, sC (Multiplicative.ofAdd u) =
      x 0 ^ (u 0).val * x 1 ^ (u 1).val * x 2 ^ (u 2).val := fun u => rfl
  have hlab_pow : ∀ (c : C₂) (n : ℕ), lab (c ^ n) = n • lab c := by
    intro c n
    induction n with
    | zero => simp [hlab]
    | succ n ih => rw [pow_succ, hlab_mul, ih, succ_nsmul]
  have hlab_s : ∀ u, lab (sC (Multiplicative.ofAdd u)) = DegreeEight.altLabel u := by
    intro u
    rw [hsC, hlab_mul, hlab_mul, hlab_pow, hlab_pow, hlab_pow, hx, hx, hx,
      OddQuadraticFive.val_nsmul_eq_smul, OddQuadraticFive.val_nsmul_eq_smul,
      OddQuadraticFive.val_nsmul_eq_smul, ← altLabel_smul, ← altLabel_smul, ← altLabel_smul,
      ← altLabel_add, ← altLabel_add, ← eq_sum_single]
  have htmem : ∀ p : Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)),
      ((tauHom φ he).comp (AddMonoidHom.toMultiplicative altDiag)) p ∈ C₂ := fun p =>
    hAC₂ ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩)
  let tA : Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) →* C₂ :=
    ((tauHom φ he).comp (AddMonoidHom.toMultiplicative altDiag)).codRestrict C₂ htmem
  have htA : ∀ v w, (tA (Multiplicative.ofAdd (v, w)) : G) =
      tauHom φ he (Multiplicative.ofAdd (altDiag (v, w))) := fun v w => rfl
  have htA_mem : ∀ v w, (tA (Multiplicative.ofAdd (v, w)) : G) ∈ 𝒜 := fun v w =>
    (mem_pullSub_iff φ he).2 ⟨_, (htA v w).symm⟩
  have hlab_t : ∀ v w, lab (tA (Multiplicative.ofAdd (v, w))) = 0 := fun v w =>
    (hlab_eq_zero _).2 (htA_mem v w)
  let p₁ : Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) →*
      Multiplicative (Fin 3 → ZMod 2) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.fst _ _)
  let p₂ : Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) →*
      Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.snd _ _)
  let Ψ₀ := sC.comp p₁ * tA.comp p₂
  have hΨ₀ : ∀ u v w, Ψ₀ (Multiplicative.ofAdd (u, v, w)) =
      sC (Multiplicative.ofAdd u) * tA (Multiplicative.ofAdd (v, w)) := fun u v w => rfl
  have hlabΨ : ∀ u v w, lab (Ψ₀ (Multiplicative.ofAdd (u, v, w))) = DegreeEight.altLabel u := by
    intro u v w
    rw [hΨ₀, hlab_mul, hlab_s, hlab_t, add_zero]
  have hinj : Function.Injective Ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨⟨u, v, w⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = q := ⟨Multiplicative.toAdd q, rfl⟩
    have hu : u = 0 := by
      have h1 := hlabΨ u v w
      rw [hq, show lab 1 = 0 by simp [hlab]] at h1
      apply DegreeEight.altLabel_injective
      rw [← h1, DegreeEight.altLabel_zero]
    subst hu
    rw [hΨ₀, show sC (Multiplicative.ofAdd 0) = 1 from map_one sC, one_mul] at hq
    have h1 := congrArg Subtype.val hq
    rw [htA] at h1
    have h2 : altDiag (v, w) = 0 := by
      have h3 := tauHom_injective φ he (h1.trans (map_one (tauHom φ he)).symm)
      exact Multiplicative.ofAdd.injective h3
    have hw : w = 0 := by
      have h3 := symThreeDiag_altDiag v w
      rw [h2] at h3
      exact h3.symm
    subst hw
    have hv : v = 0 := by
      rw [altDiag_apply, map_zero, add_zero] at h2
      apply DegreeEight.altLabel_injective
      rw [h2, DegreeEight.altLabel_zero]
    subst hv
    rfl
  have hbij : Function.Bijective Ψ₀ := hinj.bijective_of_nat_card_le (by
    rw [hC₂c, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod,
      natCard_vecThree])
  refine ⟨MulEquiv.ofBijective Ψ₀ hbij, fun u v w => ?_, fun u v w => ?_, fun u v w => ?_⟩
  ·
    change z * (Ψ₀ (Multiplicative.ofAdd (u, v, w)) : G) * z⁻¹ =
      Ψ₀ (Multiplicative.ofAdd (u, u + v, w))
    rw [hΨ₀, hΨ₀, Subgroup.coe_mul, Subgroup.coe_mul]
    have h1 : z * (tA (Multiplicative.ofAdd (v, w)) : G) * z⁻¹ =
        tA (Multiplicative.ofAdd (v, w)) := by
      rw [← RadicalLabels.mul_comm_z hzC (pullSub_le φ _ (htA_mem v w)), mul_inv_cancel_right]
    calc z * ((sC (Multiplicative.ofAdd u) : G) * tA (Multiplicative.ofAdd (v, w))) * z⁻¹ =
        (z * (sC (Multiplicative.ofAdd u) : G) * z⁻¹) *
          (z * (tA (Multiplicative.ofAdd (v, w)) : G) * z⁻¹) := by group
      _ = (sC (Multiplicative.ofAdd u) : G) * tauHom φ he (Multiplicative.ofAdd
            (DegreeEight.altLabel u)) * tA (Multiplicative.ofAdd (v, w)) := by
          rw [hzc, hlab_s, h1]
      _ = (sC (Multiplicative.ofAdd u) : G) * tA (Multiplicative.ofAdd (u + v, w)) := by
          rw [htA, htA, mul_assoc, ← map_mul, ← ofAdd_add, altDiag_apply, altDiag_apply,
            altLabel_add, add_assoc]
  ·
    change (Ψ₀ (Multiplicative.ofAdd (u, v, w)) : G) ∈ 𝒜 ↔ u = 0
    rw [← hlab_eq_zero, hlabΨ]
    constructor
    · intro h
      apply DegreeEight.altLabel_injective
      rw [h, DegreeEight.altLabel_zero]
    · intro h
      rw [h, DegreeEight.altLabel_zero]
  ·
    change (Ψ₀ (Multiplicative.ofAdd (u, v, w)) : G) ∈ tauSet φ e (fun B => ∀ i, B i i = 0) ↔
      u = 0 ∧ w = 0
    constructor
    · intro h
      have hA : (Ψ₀ (Multiplicative.ofAdd (u, v, w)) : G) ∈ 𝒜 := by
        obtain ⟨B, -, hB⟩ := (mem_tauSet_iff φ he).1 h
        exact (mem_pullSub_iff φ he).2 ⟨B, hB⟩
      have hu : u = 0 := by
        rw [← hlab_eq_zero, hlabΨ] at hA
        apply DegreeEight.altLabel_injective
        rw [hA, DegreeEight.altLabel_zero]
      subst hu
      refine ⟨rfl, ?_⟩
      rw [hΨ₀, show sC (Multiplicative.ofAdd 0) = 1 from map_one sC, one_mul, htA] at h
      obtain ⟨B, hB, hBe⟩ := (mem_tauSet_iff φ he).1 h
      have h1 := Multiplicative.ofAdd.injective (tauHom_injective φ he hBe)
      have h2 : symThreeDiag ((Multiplicative.toAdd B : binarySymMatrices 3) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := funext hB
      rw [← symThreeDiag_altDiag v w]
      rw [show Multiplicative.toAdd B = altDiag (v, w) from h1] at h2
      exact h2
    · rintro ⟨rfl, rfl⟩
      rw [hΨ₀, show sC (Multiplicative.ofAdd 0) = 1 from map_one sC, one_mul, htA]
      refine (mem_tauSet_iff φ he).2 ⟨Multiplicative.ofAdd (altDiag (v, 0)), fun i => ?_, rfl⟩
      have h1 := symThreeDiag_altDiag v 0
      exact congrFun h1 i

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
