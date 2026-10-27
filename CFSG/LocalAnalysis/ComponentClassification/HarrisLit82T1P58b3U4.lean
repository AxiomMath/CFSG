module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3U4Key
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3U4Blk
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3SL4
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LSU

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix CFSG Subgroup Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd signMat compInd_compl
  commute_compInd_compl commute_signMat_iff)
open scoped MatrixGroups

namespace P58b3

theorem oddAutInner_of_PSU_four {X : Type} [Group X] (hX : IsQuasisimple X)
    (hm : Blueprint.LieModel (X ⧸ center X) .PSU 4 3 1) : OddAutInner X := by
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have h := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound _ 4 3 1
    hcl).2.2.1
  norm_num at h
  exact oddAutInner_of_card_outer_dvd hX.1 (m := 3) (by rw [h]; norm_num)

variable {F : Type} [Field F] (hu : UnitaryFieldData 3 1 F)

include hu in
theorem scalar_pow_four {n : ℕ} (hn : 1 ≤ n) {z : StatedSU n (3 ^ 1) F} {ω : F}
    (hz : ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = ω • 1) : ω ^ 4 = 1 := by
  have hbar : ∀ x : F, hu.bar x = x ^ 3 := fun x => by rw [hu.bar_apply, pow_one]
  have hU := ((mem_unitarySU_iff hu).1 z.2).2
  rw [hz, Matrix.map_smul' _ _ _ (map_mul hu.bar), Matrix.map_one _ (map_zero _) (map_one _),
    transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hU
  have e := congrFun (congrFun hU ⟨0, hn⟩) ⟨0, hn⟩
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hbar] at e
  linear_combination e

theorem false_of_su4 {X : Type} [Group X] [Finite X] (α : StatedSU 4 (3 ^ 1) F →* X)
    (hαs : Function.Surjective α)
    (hαZ : ∀ z, α z ∈ center X → projH (StatedSU 4 (3 ^ 1) F) z = 1) {t : X}
    {J : Finset (Fin 4)} (hJ : J.card = 2)
    (hf : ∀ y, t * α y * t⁻¹ = α (uLift hu (uSign hu J) 1 y)) {Q : Subgroup X}
    (hQ : IsSolvableTwoComponentIn Q (centralizer {t})) {c : X} (hcQ : c ∈ Q)
    (hcZ : c ∈ center X) (hc2 : c * c = 1) (hc1 : c ≠ 1) : False := by
  classical
  have := hu.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hu.charP
  have h2 : (2 : F) ≠ 0 := P58b3L.two_ne_zero_of_three hu
  set F₀ := CFSG.LieType.Steinberg.fixedSubfield F 3 1 with hF₀def
  have hF₀ : Nat.card F₀ = 3 := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hu.card_eq_sq, pow_one]
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hJ
  have hJc2 : ({a, b} : Finset (Fin 4))ᶜ.card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hJ]
  obtain ⟨c₀, d₀, hcd, hJc⟩ := Finset.card_eq_two.mp hJc2
  obtain ⟨e₁⟩ := nonempty_uBlock_pair_equiv hu hab
  obtain ⟨e₂'⟩ := nonempty_uBlock_pair_equiv hu hcd
  set e₂ : uBlock 3 1 F ({a, b} : Finset (Fin 4))ᶜ ≃* SL(2, F₀) :=
    (MulEquiv.subgroupCongr (congrArg (uBlock 3 1 F) hJc)).trans e₂' with he₂
  set ρ₁ : SL(2, F₀) →* X :=
    α.comp ((uBlock 3 1 F {a, b}).subtype.comp e₁.symm.toMonoidHom) with hρ₁
  set ρ₂ : SL(2, F₀) →* X :=
    α.comp ((uBlock 3 1 F ({a, b} : Finset (Fin 4))ᶜ).subtype.comp e₂.symm.toMonoidHom) with hρ₂
  have hρ₁a : ∀ A, ρ₁ A = α (e₁.symm A) := fun _ => rfl
  have hρ₂a : ∀ B, ρ₂ B = α (e₂.symm B) := fun _ => rfl
  have hscal : ∀ z, α z ∈ center X → ∃ ζ : Fˣ,
      ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (ζ : F) • 1 := fun z hz =>
    P58b3L.exists_scalar_of_projH (hαZ z hz)
  have hscal_comm : ∀ (z w : StatedSU 4 (3 ^ 1) F) (ζ : Fˣ),
      ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (ζ : F) • 1 → z * w = w * z := by
    intro z w ζ hz
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hz, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  set Fx : Subgroup (StatedSU 4 (3 ^ 1) F) :=
    MonoidHom.eqLocus (uLift hu (uSign hu {a, b}) 1) (MonoidHom.id _) with hFx
  have hmemFx : ∀ g, g ∈ Fx ↔ compInd F {a, b} * ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * compInd F {a, b} := fun g =>
    uLift_sign_eq_iff hu h2 {a, b} g
  set C' : Subgroup X := Fx.map α with hC'
  have hC'C : C' ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hf y
    have hy' : uLift hu (uSign hu {a, b}) 1 y = y := hy
    rw [hy'] at h1
    calc α y * t = t * α y * t⁻¹ * t := by rw [h1]
      _ = t * α y := by group
  have hsq : ∀ y, α y ∈ centralizer ({t} : Set X) → y * y ∈ Fx := by
    intro y hy
    have h1 : α (uLift hu (uSign hu {a, b}) 1 y) = α y := by
      rw [← hf y]
      rw [mem_centralizer_singleton_iff] at hy
      rw [← hy, mul_inv_cancel_right]
    set z := uLift hu (uSign hu {a, b}) 1 y * y⁻¹ with hzdef
    have hzc : α z ∈ center X := by
      rw [hzdef, map_mul, h1, map_inv, mul_inv_cancel]
      exact one_mem _
    obtain ⟨ζ, hζ⟩ := hscal z hzc
    have hzcomm : ∀ w, z * w = w * z := fun w => hscal_comm z w ζ hζ
    have hzfix : uLift hu (uSign hu {a, b}) 1 z = z := by
      apply Subtype.ext
      rw [P58b3L.coe_uLift_one]
      have hzG : (z : GL (Fin 4) F) = GeneralLinearGroup.scalar (Fin 4) ζ := by
        apply Units.ext
        rw [hζ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
      rw [hzG]
      have hsc : ∀ x : GL (Fin 4) F, GeneralLinearGroup.scalar (Fin 4) ζ * x =
          x * GeneralLinearGroup.scalar (Fin 4) ζ := fun x => by
        ext i j
        simp [GeneralLinearGroup.scalar, mul_comm]
      rw [mul_assoc, hsc, ← mul_assoc, mul_inv_cancel, one_mul]
    have hyz : uLift hu (uSign hu {a, b}) 1 y = z * y := by rw [hzdef, inv_mul_cancel_right]
    have hzz : z * z = 1 := by
      have hinv := P58b3L.uLift_sign_involutive hu {a, b} y
      rw [hyz, map_mul, hzfix, hyz] at hinv
      calc z * z = z * (z * y) * y⁻¹ := by group
        _ = 1 := by rw [hinv, mul_inv_cancel]
    show uLift hu (uSign hu {a, b}) 1 (y * y) = y * y
    rw [map_mul, hyz]
    calc z * y * (z * y) = z * (y * z) * y := by group
      _ = z * (z * y) * y := by rw [hzcomm y]
      _ = (z * z) * (y * y) := by group
      _ = y * y := by rw [hzz, one_mul]
  have hodd : ∀ x ∈ centralizer ({t} : Set X), Odd (orderOf x) → x ∈ C' := by
    intro x hx hxo
    obtain ⟨y, rfl⟩ := hαs x
    obtain ⟨m, hm⟩ := hxo
    refine ⟨(y * y) ^ (m + 1), pow_mem (hsq y hx) _, ?_⟩
    rw [map_pow, map_mul, ← pow_two, ← pow_mul]
    calc α y ^ (2 * (m + 1)) = α y ^ (2 * m + 1) * α y := by
          rw [← pow_succ]; congr 1
      _ = α y := by rw [← hm, pow_orderOf_eq_one, one_mul]
  have hQC' : Q ≤ C' := by
    refine (OddGen.le_closure (oddGen_of_coreQuot hQ.2.2.2)).trans ?_
    rw [closure_le]
    rintro x ⟨hxQ, hxo⟩
    exact hodd x (hQ.1 hxQ) hxo
  have hQs' : (Q.subgroupOf C').IsSubnormal :=
    F3L57.isSubnormal_subgroupOf_of_le hC'C hQ.2.1
  have hJ₁fix : ∀ g ∈ uBlock 3 1 F {a, b}, g ∈ Fx := fun g hg =>
    (hmemFx g).mpr (commute_compInd_of_mem_uBlock hg)
  have hJ₂fix : ∀ g ∈ uBlock 3 1 F ({a, b} : Finset (Fin 4))ᶜ, g ∈ Fx := fun g hg =>
    (hmemFx g).mpr (commute_compInd_of_or' (Or.inr rfl) (commute_compInd_of_mem_uBlock hg))
  have hR₁ : ρ₁.range ≤ C' := by
    rintro _ ⟨A, rfl⟩
    exact ⟨_, hJ₁fix _ (e₁.symm A).2, rfl⟩
  have hR₂ : ρ₂.range ≤ C' := by
    rintro _ ⟨B, rfl⟩
    exact ⟨_, hJ₂fix _ (e₂.symm B).2, rfl⟩
  have hC'mem : ∀ x ∈ C', ∃ g ∈ Fx, α g = x := fun x hx => hx
  have hconj : ∀ (I : Finset (Fin 4)), (I = {a, b} ∨ I = ({a, b} : Finset (Fin 4))ᶜ) →
      ∀ g ∈ Fx, ∀ w ∈ uBlock 3 1 F I, g * w * g⁻¹ ∈ uBlock 3 1 F I := by
    intro I hI g hg w hw
    refine conj_mem_uBlock (D := ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
      (Di := (((g⁻¹ : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
      ?_ ?_ (commute_compInd_of_or hI ((hmemFx g).mp hg)) hw ?_
    · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  have hN₁ : (ρ₁.range.subgroupOf C').Normal := by
    rw [normal_subgroupOf_iff hR₁]
    rintro _ x ⟨A, rfl⟩ hx
    obtain ⟨g, hg, rfl⟩ := hC'mem x hx
    have hw := hconj {a, b} (Or.inl rfl) g hg _ (e₁.symm A).2
    refine ⟨e₁ ⟨_, hw⟩, ?_⟩
    rw [hρ₁a, MulEquiv.symm_apply_apply]
    change α (g * e₁.symm A * g⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rfl
  have hN₂ : (ρ₂.range.subgroupOf C').Normal := by
    rw [normal_subgroupOf_iff hR₂]
    rintro _ x ⟨B, rfl⟩ hx
    obtain ⟨g, hg, rfl⟩ := hC'mem x hx
    have hw := hconj _ (Or.inr rfl) g hg _ (e₂.symm B).2
    refine ⟨e₂ ⟨_, hw⟩, ?_⟩
    rw [hρ₂a, MulEquiv.symm_apply_apply]
    change α (g * e₂.symm B * g⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rfl
  have hdisj : Disjoint ({a, b} : Finset (Fin 4)) ({a, b} : Finset (Fin 4))ᶜ :=
    disjoint_compl_right
  have hcommS : ∀ A B, (e₁.symm A : StatedSU 4 (3 ^ 1) F) * e₂.symm B =
      e₂.symm B * e₁.symm A := fun A B =>
    Burgoyne.B.uBlock_commute_of_disjoint hdisj (e₁.symm A).2 (e₂.symm B).2
  have hcomm : ∀ A B, ρ₁ A * ρ₂ B = ρ₂ B * ρ₁ A := by
    intro A B
    rw [hρ₁a, hρ₂a, ← map_mul, ← map_mul, hcommS]
  have hcen : ∀ {I : Finset (Fin 4)} (e : uBlock 3 1 F I ≃* SL(2, F₀)) (w : uBlock 3 1 F I),
      (∀ v : uBlock 3 1 F I, w * v = v * w) → e w = 1 ∨ e w = -1 := by
    intro I e w hw
    refine (CFSG.ClassicalInvolution.mem_center_sl2_iff (e w)).mp ?_
    rw [← Subgroup.map_center_eq e]
    exact ⟨w, mem_center_iff.2 fun v => (hw v).symm, rfl⟩
  have hinfC : ∀ A B, ρ₁ A = ρ₂ B → ∃ ζ : Fˣ,
      (((e₁.symm A : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (ζ : F) • (((e₂.symm B : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) := by
    intro A B h
    rw [hρ₁a, hρ₂a] at h
    have hz : α ((e₁.symm A : StatedSU 4 (3 ^ 1) F) *
        ((e₂.symm B : StatedSU 4 (3 ^ 1) F))⁻¹) ∈ center X := by
      rw [map_mul, h, map_inv, mul_inv_cancel]
      exact one_mem _
    obtain ⟨ζ, hζ⟩ := hscal _ hz
    refine ⟨ζ, ?_⟩
    calc (((e₁.symm A : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        = (((((e₁.symm A : StatedSU 4 (3 ^ 1) F) * ((e₂.symm B : StatedSU 4 (3 ^ 1) F))⁻¹) *
            (e₂.symm B : StatedSU 4 (3 ^ 1) F) : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) := by rw [inv_mul_cancel_right]
      _ = (((((e₁.symm A : StatedSU 4 (3 ^ 1) F) * ((e₂.symm B : StatedSU 4 (3 ^ 1) F))⁻¹ :
            StatedSU 4 (3 ^ 1) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (((e₂.symm B : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          rw [Subgroup.coe_mul, Units.val_mul]
      _ = (ζ : F) • (((e₂.symm B : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) := by rw [hζ, Matrix.smul_mul, Matrix.one_mul]
  have hinf₁ : ∀ A B, ρ₁ A = ρ₂ B → A = 1 ∨ A = -1 := by
    intro A B h
    obtain ⟨ζ, hζ⟩ := hinfC A B h
    have := hcen e₁ (e₁.symm A) fun v => by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
        Units.val_mul, hζ, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      have hc := Burgoyne.B.uBlock_commute_of_disjoint hdisj v.2 (e₂.symm B).2
      have := congrArg (fun x : StatedSU 4 (3 ^ 1) F => ((x : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F)) hc
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this.symm
    simpa using this
  have hinf₂ : ∀ A B, ρ₁ A = ρ₂ B → B = 1 ∨ B = -1 := by
    intro A B h
    obtain ⟨ζ, hζ⟩ := hinfC A B h
    have hζ' : (((e₂.symm B : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((ζ⁻¹ : Fˣ) : F) • (((e₁.symm A : StatedSU 4 (3 ^ 1) F) : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) := by
      rw [hζ, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    have := hcen e₂ (e₂.symm B) fun v => by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
        Units.val_mul, hζ', Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      have hc := Burgoyne.B.uBlock_commute_of_disjoint hdisj (e₁.symm A).2 v.2
      have := congrArg (fun x : StatedSU 4 (3 ^ 1) F => ((x : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F)) hc
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this
    simpa using this
  have hdec : ∀ x ∈ C', x ^ 3 = 1 → ∃ A B, x = ρ₁ A * ρ₂ B := by
    intro x hx hx3
    obtain ⟨g, hg, rfl⟩ := hC'mem x hx
    have hg3 : α (g ^ 3) ∈ center X := by
      rw [map_pow, hx3]
      exact one_mem _
    obtain ⟨ω, hω⟩ := hscal _ hg3
    have hω4 := scalar_pow_four hu (by norm_num) hω
    have hg12 : (g ^ 4) ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [← pow_mul, show 4 * 3 = 3 * 4 by rfl, pow_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val,
        hω, smul_pow, one_pow, hω4, one_smul, Subgroup.coe_one, Units.val_one]
    have hg4 : g ^ 4 ∈ Fx := pow_mem hg 4
    obtain ⟨g₁, hg₁, g₂, hg₂, hg₁₂⟩ :=
      exists_uBlock_mul_of_pow_three hu ((hmemFx _).mp hg4) hg12
    refine ⟨e₁ ⟨g₁, hg₁⟩, e₂ ⟨g₂, hg₂⟩, ?_⟩
    rw [hρ₁a, hρ₂a, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, ← map_mul]
    change α g = α (g₁ * g₂)
    rw [← hg₁₂, map_pow]
    calc α g = α g ^ 3 * α g := by rw [hx3, one_mul]
      _ = α g ^ 4 := by rw [← pow_succ]
  have hneg₁ : e₁.symm (-1) = ⟨uPairSign hu hab, uPairSign_mem hu hab⟩ := by
    apply e₁.injective
    rw [MulEquiv.apply_symm_apply]
    exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [uPairSign_eq_neg_one hu h2 hab e₁, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one]
  have hneg₂ : (e₂.symm (-1) : StatedSU 4 (3 ^ 1) F) = uPairSign hu hcd := by
    have h : e₂'.symm (-1) = ⟨uPairSign hu hcd, uPairSign_mem hu hcd⟩ := by
      apply e₂'.injective
      rw [MulEquiv.apply_symm_apply]
      exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
        rw [uPairSign_eq_neg_one hu h2 hcd e₂', Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_one]
    rw [he₂, MulEquiv.symm_trans_apply, h]
    rfl
  have hZ₁ : ∀ x ∈ C', ρ₁ (-1) * x = x * ρ₁ (-1) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hC'mem x hx
    rw [hρ₁a, hneg₁, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    change signMat F {a, b} * _ = _ * signMat F {a, b}
    exact (commute_signMat_iff h2 _ _).mpr ((hmemFx g).mp hg)
  have hZ₂ : ∀ x ∈ C', ρ₂ (-1) * x = x * ρ₂ (-1) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hC'mem x hx
    rw [hρ₂a, hneg₂, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    change signMat F {c₀, d₀} * _ = _ * signMat F {c₀, d₀}
    refine (commute_signMat_iff h2 _ _).mpr ?_
    rw [← hJc]
    exact commute_compInd_compl ((hmemFx g).mp hg)
  have hnsc : ∀ {u v : Fin 4} (huv : u ≠ v), ∀ k : Fin 4, k ∉ ({u, v} : Finset (Fin 4)) →
      c ≠ α (uPairSign hu huv) := by
    intro u v huv k hk h
    rw [h] at hcZ
    obtain ⟨ζ, hζ⟩ := hscal _ hcZ
    have e1 := congrFun (congrFun hζ u) u
    have e2 := congrFun (congrFun hζ k) k
    rw [coe_uPairSign, signMat, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq,
      smul_eq_mul, mul_one] at e1 e2
    have hu' : u ∈ ({u, v} : Finset (Fin 4)) := by simp
    simp only [hu', hk, ↓reduceIte] at e1 e2
    exact h2 (by linear_combination e2 - e1)
  have hnot₂ : ∃ k : Fin 4, k ∉ ({c₀, d₀} : Finset (Fin 4)) := ⟨a, by
    rw [← hJc]
    simp⟩
  have hnot₁ : ∃ k : Fin 4, k ∉ ({a, b} : Finset (Fin 4)) := ⟨c₀, by
    have : c₀ ∈ ({a, b} : Finset (Fin 4))ᶜ := by rw [hJc]; simp
    simpa using this⟩
  have hc₁ : c ≠ ρ₁ (-1) := by
    obtain ⟨k, hk⟩ := hnot₁
    rw [hρ₁a, hneg₁]
    exact hnsc hab k hk
  have hc₂ : c ≠ ρ₂ (-1) := by
    obtain ⟨k, hk⟩ := hnot₂
    rw [hρ₂a, hneg₂]
    exact hnsc hcd k hk
  have hinjI : ∀ {I : Finset (Fin 4)} (k : Fin 4), k ∉ I →
      Function.Injective (α.comp (uBlock 3 1 F I).subtype) := by
    intro I k hk
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    have hwz : α w ∈ center X := by
      rw [show α (w : StatedSU 4 (3 ^ 1) F) = 1 from hw]
      exact one_mem _
    have h1 := eq_one_of_mem_uBlock_scalars hk w.2
      ((QuotientGroup.eq_one_iff _).mp (hαZ _ hwz))
    exact (mem_bot).mpr (Subtype.ext h1)
  have hρ₁i : Function.Injective ρ₁ := by
    obtain ⟨k, hk⟩ := hnot₁
    exact (hinjI k hk).comp e₁.symm.injective
  have hρ₂i : Function.Injective ρ₂ := by
    obtain ⟨k, hk⟩ := hnot₂
    have hk' : k ∉ ({a, b} : Finset (Fin 4))ᶜ := by rw [hJc]; exact hk
    exact (hinjI k hk').comp e₂.symm.injective
  exact false_of_two_sl_central hF₀ ρ₁ ρ₂ hρ₁i hρ₂i hR₁ hR₂ hN₁ hN₂ hcomm hinf₁ hinf₂ hdec hZ₁ hZ₂
    hQC' hQs' hQ.2.2.2 hcQ (fun y _ => (mem_center_iff.mp hcZ y).symm) hc2 hc1 hc₁ hc₂

theorem harris82Lemma58bThreeRowAt_PSU_four : Harris82Lemma58bThreeRowAt .PSU 4 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ _ K hL₁ _ hz₁L _ he₁ hKc hO₁ _ hN hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  obtain ⟨F, _, hu, α, hαs, hαZ⟩ := P58b3L.exists_su_cover hX hO (by norm_num) hmX
  obtain ⟨H, J, hf⟩ := P58b3L.exists_sign_lift hu (by norm_num) α hαs (fun z => (hαZ z).1)
    (P58b3L.mk_ne_one hz₁ hz₁K) (P58b3L.mk_mem_center hKc.1 hz₁K) (P58b3L.mk_mul_self hz₂ hz₂K)
  have hα's : Function.Surjective (α.comp (uLift hu H 1)) :=
    hαs.comp (P58b3L.uLift_one_surjective hu H)
  have hα'Z : ∀ z, (α.comp (uLift hu H 1)) z ∈ center (↥K ⧸ pPrimeCore 2 ↥K) →
      projH (StatedSU 4 (3 ^ 1) F) z = 1 := fun z hz =>
    P58b3L.projH_eq_one_of_uLift hu H ((hαZ (uLift hu H 1 z)).1 hz)
  by_cases hbig : ∃ I : Finset (Fin 4), (I = J ∨ I = Jᶜ) ∧ 3 ≤ I.card
  · obtain ⟨I, hI, h3I⟩ := hbig
    obtain ⟨Q, hQt, hQsub, -, hQsolv, a, ha, b, hb, -, -, hab⟩ :=
      P58b3L.exists_quat_config hz₁ hz₂ hL₁ hz₁L he₁ hKc.1 hO₁ hz₁K hz₂K
    exact P58b3L.false_of_su_block hu (α.comp (uLift hu H 1)) hα's hα'Z hI h3I hf hQt hQsub
      hQsolv ha hb (P58b3L.mk_ne_one hz₁ hz₁K) (P58b3L.mk_mem_center hKc.1 hz₁K) hab
  · push Not at hbig
    have hsum : J.card + Jᶜ.card = 4 := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ J
      rw [Fintype.card_fin] at this
      omega
    have h1 := hbig J (Or.inl rfl)
    have h0 := hbig Jᶜ (Or.inr rfl)
    have hJ : J.card = 2 := by omega
    have hQ := lemma57_fourGroup_map_of_aut hz₂ hL₁ hKc.1 hO₁ hN hz₂K hz₁K
      (oddAutInner_of_PSU_four hX hmX)
    have hcQ : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈
        ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
      ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
    exact false_of_su4 hu (α.comp (uLift hu H 1)) hα's hα'Z hJ hf hQ hcQ
      (P58b3L.mk_mem_center hKc.1 hz₁K) (P58b3L.mk_mul_self hz₁ hz₁K)
      (P58b3L.mk_ne_one hz₁ hz₁K)

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
