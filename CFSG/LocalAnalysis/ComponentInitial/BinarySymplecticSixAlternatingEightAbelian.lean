module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightRadical

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Matrix DegreeEight
open scoped Pointwise BinarySymThreeOrbit commutatorElement

@[expose] def sevenDual : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 1; 1, 1, 0; 1, 0, 0]

theorem sevenDual_det : sevenDual.det = 1 := by
  decide +kernel

theorem orderSeven_mul_sevenDual : orderSeven * sevenDual = 1 := by
  decide +kernel

theorem coe_inv_glOfDet_orderSeven :
    (((glOfDet orderSeven orderSeven_det)⁻¹ : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = sevenDual := by
  have h : (glOfDet orderSeven orderSeven_det)⁻¹ = glOfDet sevenDual sevenDual_det :=
    inv_eq_of_mul_eq_one_right (Units.ext orderSeven_mul_sevenDual)
  rw [h, coe_glOfDet]
  decide +kernel

theorem sevenDual_add_injective : ∀ a : Fin 3 → ZMod 2, sevenDual *ᵥ a + a = 0 → a = 0 := by
  decide +kernel

theorem sevenDual_add_surjective :
    ∀ a : Fin 3 → ZMod 2, ∃ b : Fin 3 → ZMod 2, sevenDual *ᵥ b + b = a := by
  decide +kernel

@[expose] def altBilin (c₀₁ c₀₂ c₁₂ : Fin 3 → ZMod 2) (u v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  (u 0 * v 1 + u 1 * v 0) • c₀₁ + (u 0 * v 2 + u 2 * v 0) • c₀₂ + (u 1 * v 2 + u 2 * v 1) • c₁₂

theorem altBilin_sevenDual : ∀ c₀₁ c₀₂ c₁₂ : Fin 3 → ZMod 2,
    (∀ i j : Fin 3, altBilin c₀₁ c₀₂ c₁₂ (sevenDual *ᵥ bvec i) (sevenDual *ᵥ bvec j) =
      sevenDual *ᵥ altBilin c₀₁ c₀₂ c₁₂ (bvec i) (bvec j)) → c₀₁ = 0 ∧ c₀₂ = 0 ∧ c₁₂ = 0 := by
  decide +kernel

theorem eq_altBilin (t : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (h₁ : ∀ a a' w, t (a + a') w = t a w + t a' w) (h₂ : ∀ a w w', t a (w + w') = t a w + t a w')
    (h₀ : ∀ a, t a a = 0) (u v : Fin 3 → ZMod 2) :
    t u v = altBilin (t (bvec 0) (bvec 1)) (t (bvec 0) (bvec 2)) (t (bvec 1) (bvec 2)) u v := by
  have hsymm : ∀ a w, t w a = t a w := fun a w => by
    have h := h₀ (a + w)
    rw [h₁, h₂, h₂, h₀, h₀, zero_add, add_zero] at h
    funext k
    have hk := congrFun h k
    simp only [Pi.add_apply, Pi.zero_apply] at hk
    have h2 := symThree_zmod_add_self (t a w k)
    grind
  rw [bilin_expand t h₁ h₂ u v]
  simp only [Fin.sum_univ_three]
  rw [h₀ (bvec 0), h₀ (bvec 1), h₀ (bvec 2), hsymm (bvec 0) (bvec 1), hsymm (bvec 0) (bvec 2),
    hsymm (bvec 1) (bvec 2)]
  funext k
  simp only [altBilin, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero]
  ring

@[expose] def twistComm {G : Type*} [Group G] (n y : G) : G := n * y * n⁻¹ * y⁻¹

theorem card_mul_relIndex_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  rw [← Nat.card_congr (subgroupOfEquivOfLe h).toEquiv]
  exact (H.subgroupOf K).card_mul_index

namespace AltTranslationData

variable {G : Type*} [Group G] {R : Subgroup G}
  {θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)} {D S : Subgroup G}
  (H : AltTranslationData θ D S)
include H

theorem layerSub_top_le_D : BinarySymThreeOrbit.layerSub θ ⊤ ≤ D :=
  (BinarySymThreeOrbit.layerSub_le θ ⊤).trans H.le

theorem mul_comm_of_mem_A {a x : G} (ha : a ∈ BinarySymThreeOrbit.layerSub θ ⊤) (hx : x ∈ D) :
    x * a = a * x := by
  obtain ⟨B, -, rfl⟩ := ha
  have h := H.inv_conj_symm ⟨x, hx⟩ B 0
  rw [zero_smul, add_zero] at h
  calc x * θ.symm (.ofAdd (B, 0)) = x * (x⁻¹ * θ.symm (.ofAdd (B, 0)) * x) := by
        rw [show (x : G) = ((⟨x, hx⟩ : D) : G) from rfl, h]
    _ = θ.symm (.ofAdd (B, 0)) * x := by group

theorem commutator_mem_A {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    x * y * x⁻¹ * y⁻¹ ∈ BinarySymThreeOrbit.layerSub θ ⊤ := by
  have h : ⁅x, y⁆ ∈ ⁅D, D⁆ := commutator_mem_commutator hx hy
  rw [H.commutator_eq] at h
  exact (BinarySymThreeOrbit.layerSub_mono θ le_top) h

theorem lab_eq_zero_of_mem_R (d : D) (hd : (d : G) ∈ R) : H.lab d = 0 := by
  change symThreeOff ((H.T d (0, 1)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0
  rw [H.T_of_mem d hd]
  funext k
  fin_cases k <;> rfl

theorem mem_R_of_commute_z₀ (d : D)
    (h : (d : G) * θ.symm (.ofAdd (0, 1)) = θ.symm (.ofAdd (0, 1)) * d) : (d : G) ∈ R := by
  apply H.mem_of_zLabel d d.2
  have h1 := H.inv_conj_symm d 0 1
  rw [one_smul, zero_add, show (d : G)⁻¹ * θ.symm (.ofAdd (0, 1)) * d = θ.symm (.ofAdd (0, 1)) by
    rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]] at h1
  have h2 := congrArg Prod.fst (Multiplicative.ofAdd.injective (θ.symm.injective
    (Subtype.ext h1)))
  exact altLabel_injective (h2.symm.trans altLabel_zero.symm)

variable {n : G} (hn : n ∈ S)
  (hσ : ∀ X, conjLabel θ ⟨n, H.le_normalizer' hn⟩ X =
    (symThreeCongr (glOfDet orderSeven orderSeven_det) X.1, X.2))
include hn hσ

theorem lab_conj (y : D) :
    H.lab (H.conjD n (H.le_normalizer' hn) y) = sevenDual *ᵥ H.lab y := by
  rw [(H.conjD_levi n hn _ hσ y).1, coe_inv_glOfDet_orderSeven]

theorem conj_mem_A {a : G} (ha : a ∈ BinarySymThreeOrbit.layerSub θ ⊤) :
    n * a * n⁻¹ ∈ BinarySymThreeOrbit.layerSub θ ⊤ := by
  obtain ⟨B, -, rfl⟩ := ha
  rw [← conjLabel_spec θ ⟨n, H.le_normalizer' hn⟩, hσ]
  exact BinarySymThreeOrbit.symm_mem_layerSub θ (AddSubgroup.mem_top _)

omit hσ in
theorem twistComm_mem (y : D) : twistComm n y ∈ D :=
  mul_mem (H.normal n (H.le_normalizer' hn) y y.2) (inv_mem y.2)

theorem lab_twistComm (y : D) :
    H.lab ⟨twistComm n y, H.twistComm_mem hn y⟩ = sevenDual *ᵥ H.lab y + H.lab y := by
  have h : (⟨twistComm n y, H.twistComm_mem hn y⟩ : D) = H.conjD n (H.le_normalizer' hn) y * y⁻¹ :=
    rfl
  rw [h, H.lab_mul, H.lab_conj hn hσ, H.lab_inv]

@[expose] def complementSub : Subgroup G where
  carrier := {x | x ∈ D ∧ ∃ y ∈ D, x * (twistComm n y)⁻¹ ∈ BinarySymThreeOrbit.layerSub θ ⊤}
  one_mem' := ⟨one_mem D, 1, one_mem D, by simp [twistComm]⟩
  mul_mem' := by
    rintro x x' ⟨hx, y, hy, ha⟩ ⟨hx', y', hy', ha'⟩
    refine ⟨mul_mem hx hx', y * y', mul_mem hy hy', ?_⟩
    have hφ : twistComm n y ∈ D := H.twistComm_mem hn ⟨y, hy⟩
    have hYD : n * y * n⁻¹ ∈ D := H.normal n (H.le_normalizer' hn) y hy
    have hY'D : n * y' * n⁻¹ ∈ D := H.normal n (H.le_normalizer' hn) y' hy'
    have hwD : y'⁻¹ * y * y' ∈ D := mul_mem (mul_mem (inv_mem hy') hy) hy'
    have hc₁A := H.commutator_mem_A (inv_mem hy) (inv_mem hy')
    have hc₂A := H.commutator_mem_A (inv_mem hwD) hY'D
    have hcomm : twistComm n y * (x' * (twistComm n y')⁻¹) =
        (x' * (twistComm n y')⁻¹) * twistComm n y := H.mul_comm_of_mem_A ha' hφ
    have key : x * x' * (twistComm n (y * y'))⁻¹ =
        (x * (twistComm n y)⁻¹) * (x' * (twistComm n y')⁻¹) *
          (twistComm n y * twistComm n y' * (twistComm n (y * y'))⁻¹) := by
      calc x * x' * (twistComm n (y * y'))⁻¹ =
          (x * (twistComm n y)⁻¹) * (twistComm n y * (x' * (twistComm n y')⁻¹)) *
            twistComm n y' * (twistComm n (y * y'))⁻¹ := by group
        _ = _ := by rw [hcomm]; group
    have hprod : twistComm n y * twistComm n y' * (twistComm n (y * y'))⁻¹ =
        (n * y * n⁻¹) * ((y⁻¹ * y'⁻¹ * y⁻¹⁻¹ * y'⁻¹⁻¹) *
          ((y'⁻¹ * y * y')⁻¹ * (n * y' * n⁻¹) * (y'⁻¹ * y * y')⁻¹⁻¹ * (n * y' * n⁻¹)⁻¹)) *
            (n * y * n⁻¹)⁻¹ := by
      simp only [twistComm]
      group
    rw [key, hprod]
    refine mul_mem (mul_mem ha ha') ?_
    have hcen := H.mul_comm_of_mem_A (mul_mem hc₁A hc₂A) hYD
    rw [hcen, mul_inv_cancel_right]
    exact mul_mem hc₁A hc₂A
  inv_mem' := by
    rintro x ⟨hx, y, hy, ha⟩
    refine ⟨inv_mem hx, y⁻¹, inv_mem hy, ?_⟩
    have hφ : twistComm n y ∈ D := H.twistComm_mem hn ⟨y, hy⟩
    have hYD : n * y * n⁻¹ ∈ D := H.normal n (H.le_normalizer' hn) y hy
    have hc := H.commutator_mem_A (inv_mem hYD) hy
    have hcomm : (twistComm n y)⁻¹ * (x * (twistComm n y)⁻¹)⁻¹ =
        (x * (twistComm n y)⁻¹)⁻¹ * (twistComm n y)⁻¹ := H.mul_comm_of_mem_A (inv_mem ha)
          (inv_mem hφ)
    have key : x⁻¹ * (twistComm n y⁻¹)⁻¹ =
        (x * (twistComm n y)⁻¹)⁻¹ * ((n * y * n⁻¹)⁻¹ * y * (n * y * n⁻¹)⁻¹⁻¹ * y⁻¹)⁻¹ := by
      have h1 : x⁻¹ * (twistComm n y⁻¹)⁻¹ =
          (twistComm n y)⁻¹ * (x * (twistComm n y)⁻¹)⁻¹ * (twistComm n y⁻¹)⁻¹ := by group
      rw [h1, hcomm, mul_assoc]
      congr 1
      simp only [twistComm]
      group
    rw [key]
    exact mul_mem (inv_mem ha) (inv_mem hc)

omit hσ in
theorem complementSub_le : H.complementSub hn ≤ D := fun _ hx => hx.1

omit hσ in
theorem A_le_complementSub :
    BinarySymThreeOrbit.layerSub θ ⊤ ≤ H.complementSub hn := fun a ha =>
  ⟨H.layerSub_top_le_D ha, 1, one_mem D, by simpa [twistComm] using ha⟩

theorem lab_eq_of_mem_complementSub {x : G} (hx : x ∈ H.complementSub hn) :
    ∃ y : D, H.lab ⟨x, H.complementSub_le hn hx⟩ = sevenDual *ᵥ H.lab y + H.lab y := by
  obtain ⟨hxD, y, hy, ha⟩ := hx
  refine ⟨⟨y, hy⟩, ?_⟩
  have haD : (⟨x * (twistComm n y)⁻¹, H.layerSub_top_le_D ha⟩ : D) =
      ⟨x, hxD⟩ * (⟨twistComm n y, H.twistComm_mem hn ⟨y, hy⟩⟩ : D)⁻¹ := rfl
  have h0 := H.lab_eq_zero_of_mem_R ⟨_, H.layerSub_top_le_D ha⟩
    ((BinarySymThreeOrbit.layerSub_le θ ⊤) ha)
  rw [haD, H.lab_mul, H.lab_inv, H.lab_twistComm hn hσ ⟨y, hy⟩] at h0
  funext k
  have hk := congrFun h0 k
  simp only [Pi.add_apply, Pi.zero_apply] at hk
  have h2 := symThree_zmod_add_self (H.lab ⟨x, hxD⟩ k)
  simp only [Pi.add_apply]
  grind

theorem complementSub_inf_R :
    H.complementSub hn ⊓ R = BinarySymThreeOrbit.layerSub θ ⊤ := by
  apply le_antisymm
  · rintro x ⟨hxC, hxR⟩
    obtain ⟨hxD, y, hy, ha⟩ := hxC
    have hl : H.lab ⟨x, hxD⟩ = 0 := H.lab_eq_zero_of_mem_R _ hxR
    obtain ⟨y', hy'⟩ := H.lab_eq_of_mem_complementSub hn hσ ⟨hxD, y, hy, ha⟩
    have haD : (⟨x * (twistComm n y)⁻¹, H.layerSub_top_le_D ha⟩ : D) =
        ⟨x, hxD⟩ * (⟨twistComm n y, H.twistComm_mem hn ⟨y, hy⟩⟩ : D)⁻¹ := rfl
    have h0 := H.lab_eq_zero_of_mem_R ⟨_, H.layerSub_top_le_D ha⟩
      ((BinarySymThreeOrbit.layerSub_le θ ⊤) ha)
    rw [haD, H.lab_mul, H.lab_inv, H.lab_twistComm hn hσ ⟨y, hy⟩, hl, zero_add] at h0
    have hy0 := sevenDual_add_injective _ h0
    have hyR : y ∈ R := H.mem_of_zLabel y hy hy0
    have hφA : twistComm n y ∈ BinarySymThreeOrbit.layerSub θ ⊤ := by
      obtain ⟨⟨B, s⟩, hBs⟩ := BinarySymThreeOrbit.exists_symm θ hyR
      have h1 : n * y * n⁻¹ = θ.symm (.ofAdd (symThreeCongr (glOfDet orderSeven orderSeven_det)
          B, s)) := by
        rw [hBs, ← conjLabel_spec θ ⟨n, H.le_normalizer' hn⟩, hσ]
      change n * y * n⁻¹ * y⁻¹ ∈ _
      rw [h1, hBs, BinarySymThreeOrbit.symm_inv, BinarySymThreeOrbit.symm_mul_symm]
      refine BinarySymThreeOrbit.symm_mem_layerSub_iff θ |>.2 ⟨AddSubgroup.mem_top _, ?_⟩
      exact symThree_zmod_add_self s
    have h2 : x = (x * (twistComm n y)⁻¹) * twistComm n y := by group
    rw [h2]
    exact mul_mem ha hφA
  · exact le_inf (H.A_le_complementSub hn) (BinarySymThreeOrbit.layerSub_le θ ⊤)

theorem exists_mem_complementSub_lab (a : Fin 3 → ZMod 2) :
    ∃ (x : G) (hx : x ∈ H.complementSub hn), H.lab ⟨x, H.complementSub_le hn hx⟩ = a := by
  obtain ⟨b, hb⟩ := sevenDual_add_surjective a
  obtain ⟨y, hy, hly⟩ := H.zLabel_surj b
  refine ⟨twistComm n y, ⟨H.twistComm_mem hn ⟨y, hy⟩, y, hy, by simp⟩, ?_⟩
  rw [H.lab_twistComm hn hσ ⟨y, hy⟩, show H.lab ⟨y, hy⟩ = b from hly, hb]

theorem mem_A_of_lab_eq {x x' : G} (hx : x ∈ H.complementSub hn)
    (hx' : x' ∈ H.complementSub hn)
    (h : H.lab ⟨x, H.complementSub_le hn hx⟩ = H.lab ⟨x', H.complementSub_le hn hx'⟩) :
    x⁻¹ * x' ∈ BinarySymThreeOrbit.layerSub θ ⊤ := by
  rw [← H.complementSub_inf_R hn hσ]
  refine ⟨(H.complementSub hn).mul_mem ((H.complementSub hn).inv_mem hx) hx', ?_⟩
  have hD : x⁻¹ * x' ∈ D :=
    mul_mem (inv_mem (H.complementSub_le hn hx)) (H.complementSub_le hn hx')
  apply H.mem_of_zLabel _ hD
  change H.lab ⟨x⁻¹ * x', hD⟩ = 0
  rw [show (⟨x⁻¹ * x', hD⟩ : D) = (⟨x, H.complementSub_le hn hx⟩ : D)⁻¹ *
    ⟨x', H.complementSub_le hn hx'⟩ from rfl, H.lab_mul, H.lab_inv, h]
  funext k
  exact symThree_zmod_add_self _

theorem conj_mem_complementSub {x : G} (hx : x ∈ H.complementSub hn) :
    n * x * n⁻¹ ∈ H.complementSub hn := by
  obtain ⟨hxD, y, hy, ha⟩ := hx
  refine ⟨H.normal n (H.le_normalizer' hn) x hxD, n * y * n⁻¹,
    H.normal n (H.le_normalizer' hn) y hy, ?_⟩
  have h := H.conj_mem_A hn hσ ha
  convert h using 1
  simp only [twistComm]
  group

theorem complementSub_comm {x x' : G} (hx : x ∈ H.complementSub hn)
    (hx' : x' ∈ H.complementSub hn) : x * x' = x' * x := by
  classical
  choose xs hxs hlab using H.exists_mem_complementSub_lab hn hσ
  have hcI : ∀ {u v : G}, u ∈ D → v ∈ D →
      u * v * u⁻¹ * v⁻¹ ∈ BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym :=
    fun hu hv => by
      have h : ⁅_, _⁆ ∈ ⁅D, D⁆ := commutator_mem_commutator hu hv
      rwa [H.commutator_eq] at h
  have hc : ∀ a b : Fin 3 → ZMod 2, ∃ v : Fin 3 → ZMod 2,
      xs a * xs b * (xs a)⁻¹ * (xs b)⁻¹ = θ.symm (.ofAdd (altLabel v, 0)) := fun a b => by
    obtain ⟨B, hB, h⟩ := hcI (H.complementSub_le hn (hxs a)) (H.complementSub_le hn (hxs b))
    exact ⟨symThreeOff (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), by
      rw [h, ← eq_altLabel_of_diag_eq_zero (BinarySymThreeOrbit.mem_altSym_iff.1 hB)]⟩
  choose t ht using hc
  have hdep : ∀ {u u' v : G}, u ∈ D → v ∈ D →
      u⁻¹ * u' ∈ BinarySymThreeOrbit.layerSub θ ⊤ →
      u' * v * u'⁻¹ * v⁻¹ = u * v * u⁻¹ * v⁻¹ := fun {u u' v} hu hv ha => by
    have hu' : u' = u * (u⁻¹ * u') := by group
    have hcomm := H.mul_comm_of_mem_A ha hv
    rw [hu']
    calc u * (u⁻¹ * u') * v * (u * (u⁻¹ * u'))⁻¹ * v⁻¹ =
        u * (u⁻¹ * u' * v) * (u⁻¹ * u')⁻¹ * u⁻¹ * v⁻¹ := by group
      _ = u * v * u⁻¹ * v⁻¹ := by rw [← hcomm]; group
  have hdep' : ∀ {u v v' : G}, u ∈ D → v ∈ D →
      v⁻¹ * v' ∈ BinarySymThreeOrbit.layerSub θ ⊤ →
      u * v' * u⁻¹ * v'⁻¹ = u * v * u⁻¹ * v⁻¹ := fun {u v v'} hu hv ha => by
    have hv' : v' = v * (v⁻¹ * v') := by group
    have hcomm := H.mul_comm_of_mem_A ha hu
    rw [hv']
    calc u * (v * (v⁻¹ * v')) * u⁻¹ * (v * (v⁻¹ * v'))⁻¹ =
        u * v * ((v⁻¹ * v') * u⁻¹) * (v⁻¹ * v')⁻¹ * v⁻¹ := by group
      _ = u * v * u⁻¹ * v⁻¹ := by rw [← mul_comm_of_mem_A H ha (inv_mem hu)]; group
  have hA : ∀ {u : G} (hu : u ∈ H.complementSub hn),
      (xs (H.lab ⟨u, hu.1⟩))⁻¹ * u ∈ BinarySymThreeOrbit.layerSub θ ⊤ := fun hu =>
    H.mem_A_of_lab_eq hn hσ (hxs _) hu (hlab _)
  have hsymm_inj : ∀ v v' : Fin 3 → ZMod 2,
      (θ.symm (.ofAdd (altLabel v, 0)) : G) = θ.symm (.ofAdd (altLabel v', 0)) → v = v' :=
    fun v v' h => by
      have h1 := (BinarySymThreeOrbit.symm_inj θ).1 h
      exact altLabel_injective (congrArg Prod.fst h1)
  have hmulx : ∀ a a', (xs a * xs a') ∈ H.complementSub hn ∧
      H.lab ⟨xs a * xs a', (mul_mem (hxs a) (hxs a')).1⟩ = a + a' := fun a a' =>
    ⟨mul_mem (hxs a) (hxs a'), by
      have h : (⟨xs a * xs a', (mul_mem (hxs a) (hxs a')).1⟩ : D) =
          ⟨xs a, (H.complementSub_le hn (hxs a))⟩ * ⟨xs a', (H.complementSub_le hn (hxs a'))⟩ := rfl
      rw [h, H.lab_mul, hlab, hlab]⟩
  have h₁ : ∀ a a' b, t (a + a') b = t a b + t a' b := fun a a' b => by
    apply hsymm_inj
    rw [← ht, altLabel_add, show ((altLabel (t a b) + altLabel (t a' b), (0 : ZMod 2)) :
      binarySymMatrices 3 × ZMod 2) = (altLabel (t a b), 0) + (altLabel (t a' b), 0) by simp,
      ← BinarySymThreeOrbit.symm_mul_symm]
    rw [← ht, ← ht]
    have h1 := hdep (H.complementSub_le hn (hxs (a + a'))) (H.complementSub_le hn (hxs b))
      (H.mem_A_of_lab_eq hn hσ (hxs (a + a')) (hmulx a a').1
        ((hlab _).trans (hmulx a a').2.symm))
    rw [← h1]
    have hc'A := hcI (H.complementSub_le hn (hxs a')) (H.complementSub_le hn (hxs b)) |>
      (BinarySymThreeOrbit.layerSub_mono θ le_top)
    have hcA := hcI (H.complementSub_le hn (hxs a)) (H.complementSub_le hn (hxs b)) |>
      (BinarySymThreeOrbit.layerSub_mono θ le_top)
    have hcen := H.mul_comm_of_mem_A hc'A (H.complementSub_le hn (hxs a))
    have hcc := H.mul_comm_of_mem_A hc'A (H.layerSub_top_le_D hcA)
    calc xs a * xs a' * xs b * (xs a * xs a')⁻¹ * (xs b)⁻¹ =
        xs a * (xs a' * xs b * (xs a')⁻¹ * (xs b)⁻¹) * (xs a)⁻¹ *
          (xs a * xs b * (xs a)⁻¹ * (xs b)⁻¹) := by group
      _ = (xs a' * xs b * (xs a')⁻¹ * (xs b)⁻¹) * (xs a * xs b * (xs a)⁻¹ * (xs b)⁻¹) := by
        rw [hcen, mul_inv_cancel_right]
      _ = _ := hcc.symm
  have h₂ : ∀ a b b', t a (b + b') = t a b + t a b' := fun a b b' => by
    apply hsymm_inj
    rw [← ht, altLabel_add, show ((altLabel (t a b) + altLabel (t a b'), (0 : ZMod 2)) :
      binarySymMatrices 3 × ZMod 2) = (altLabel (t a b), 0) + (altLabel (t a b'), 0) by simp,
      ← BinarySymThreeOrbit.symm_mul_symm]
    rw [← ht, ← ht]
    have h1 := hdep' (H.complementSub_le hn (hxs a)) (H.complementSub_le hn (hxs (b + b')))
      (H.mem_A_of_lab_eq hn hσ (hxs (b + b')) (hmulx b b').1
        ((hlab _).trans (hmulx b b').2.symm))
    rw [← h1]
    have hcab' := hcI (H.complementSub_le hn (hxs a)) (H.complementSub_le hn (hxs b')) |>
      (BinarySymThreeOrbit.layerSub_mono θ le_top)
    have hcen := H.mul_comm_of_mem_A hcab' (H.complementSub_le hn (hxs b))
    calc xs a * (xs b * xs b') * (xs a)⁻¹ * (xs b * xs b')⁻¹ =
        (xs a * xs b * (xs a)⁻¹ * (xs b)⁻¹) * (xs b * (xs a * xs b' * (xs a)⁻¹ * (xs b')⁻¹) *
          (xs b)⁻¹) := by group
      _ = _ := by rw [hcen, mul_inv_cancel_right]
  have h₀ : ∀ a, t a a = 0 := fun a => by
    apply hsymm_inj
    rw [← ht, altLabel_zero, mul_inv_cancel_right, mul_inv_cancel, Prod.mk_zero_zero,
      ofAdd_zero, map_one, OneMemClass.coe_one]
  have hequiv : ∀ i j, altBilin (t (bvec 0) (bvec 1)) (t (bvec 0) (bvec 2)) (t (bvec 1) (bvec 2))
      (sevenDual *ᵥ bvec i) (sevenDual *ᵥ bvec j) = sevenDual *ᵥ altBilin (t (bvec 0) (bvec 1))
        (t (bvec 0) (bvec 2)) (t (bvec 1) (bvec 2)) (bvec i) (bvec j) := fun i j => by
    rw [← eq_altBilin t h₁ h₂ h₀, ← eq_altBilin t h₁ h₂ h₀]
    apply hsymm_inj
    have hc1 := H.conj_mem_complementSub hn hσ (hxs (bvec i))
    have hc2 := H.conj_mem_complementSub hn hσ (hxs (bvec j))
    have hl1 : H.lab ⟨n * xs (bvec i) * n⁻¹, (H.complementSub_le hn hc1)⟩ =
        sevenDual *ᵥ bvec i := by
      rw [show (⟨n * xs (bvec i) * n⁻¹, (H.complementSub_le hn hc1)⟩ : D) =
        H.conjD n (H.le_normalizer' hn) ⟨xs (bvec i), (H.complementSub_le hn (hxs _))⟩ from rfl,
        H.lab_conj hn hσ, hlab]
    have hl2 : H.lab ⟨n * xs (bvec j) * n⁻¹, (H.complementSub_le hn hc2)⟩ =
        sevenDual *ᵥ bvec j := by
      rw [show (⟨n * xs (bvec j) * n⁻¹, (H.complementSub_le hn hc2)⟩ : D) =
        H.conjD n (H.le_normalizer' hn) ⟨xs (bvec j), (H.complementSub_le hn (hxs _))⟩ from rfl,
        H.lab_conj hn hσ, hlab]
    rw [← ht]
    have e1 := hdep (u := xs (sevenDual *ᵥ bvec i)) (u' := n * xs (bvec i) * n⁻¹)
      (v := xs (sevenDual *ᵥ bvec j)) (H.complementSub_le hn (hxs _))
      (H.complementSub_le hn (hxs _))
      (H.mem_A_of_lab_eq hn hσ (hxs _) hc1 ((hlab _).trans hl1.symm))
    have e2 := hdep' (u := n * xs (bvec i) * n⁻¹) (v := xs (sevenDual *ᵥ bvec j))
      (v' := n * xs (bvec j) * n⁻¹) (H.complementSub_le hn hc1) (H.complementSub_le hn (hxs _))
      (H.mem_A_of_lab_eq hn hσ (hxs _) hc2 ((hlab _).trans hl2.symm))
    rw [← e1, ← e2]
    have h3 : n * xs (bvec i) * n⁻¹ * (n * xs (bvec j) * n⁻¹) * (n * xs (bvec i) * n⁻¹)⁻¹ *
        (n * xs (bvec j) * n⁻¹)⁻¹ =
        n * (xs (bvec i) * xs (bvec j) * (xs (bvec i))⁻¹ * (xs (bvec j))⁻¹) * n⁻¹ := by group
    rw [h3, ht, ← conjLabel_spec θ ⟨n, H.le_normalizer' hn⟩, hσ, symThreeCongr_altLabel,
      coe_inv_glOfDet_orderSeven]
  obtain ⟨h01, h02, h12⟩ := altBilin_sevenDual _ _ _ hequiv
  have ht0 : ∀ a b, t a b = 0 := fun a b => by
    rw [eq_altBilin t h₁ h₂ h₀, h01, h02, h12]
    funext k
    simp [altBilin]
  have e1 := hdep (u := xs (H.lab ⟨x, H.complementSub_le hn hx⟩)) (u' := x) (v := x')
    (H.complementSub_le hn (hxs _)) (H.complementSub_le hn hx') (hA hx)
  have e2 := hdep' (u := xs (H.lab ⟨x, H.complementSub_le hn hx⟩))
    (v := xs (H.lab ⟨x', H.complementSub_le hn hx'⟩)) (v' := x')
    (H.complementSub_le hn (hxs _)) (H.complementSub_le hn (hxs _)) (hA hx')
  have h := ht (H.lab ⟨x, H.complementSub_le hn hx⟩) (H.lab ⟨x', H.complementSub_le hn hx'⟩)
  rw [ht0, altLabel_zero, Prod.mk_zero_zero, ofAdd_zero, map_one, OneMemClass.coe_one,
    ← e2, ← e1] at h
  calc x * x' = x * x' * x⁻¹ * x'⁻¹ * (x' * x) := by group
    _ = x' * x := by rw [h, one_mul]

@[expose] def labHomC : H.complementSub hn →* Multiplicative (Fin 3 → ZMod 2) :=
  MonoidHom.mk' (fun c => Multiplicative.ofAdd (H.lab ⟨c, H.complementSub_le hn c.2⟩))
    fun c c' => by
      rw [← ofAdd_add, ← H.lab_mul]
      rfl

omit hσ in
theorem labHomC_apply (c : H.complementSub hn) :
    H.labHomC hn c = Multiplicative.ofAdd (H.lab ⟨c, H.complementSub_le hn c.2⟩) :=
  rfl

theorem labHomC_surjective : Function.Surjective (H.labHomC hn) := fun a => by
  obtain ⟨x, hx, hl⟩ := H.exists_mem_complementSub_lab hn hσ (Multiplicative.toAdd a)
  exact ⟨⟨x, hx⟩, by rw [labHomC_apply, hl, ofAdd_toAdd]⟩

theorem ker_labHomC :
    (H.labHomC hn).ker = (BinarySymThreeOrbit.layerSub θ ⊤).subgroupOf (H.complementSub hn) := by
  ext c
  rw [MonoidHom.mem_ker, labHomC_apply, mem_subgroupOf, ← H.complementSub_inf_R hn hσ]
  constructor
  · intro h
    refine ⟨c.2, H.mem_of_zLabel _ (H.complementSub_le hn c.2) ?_⟩
    exact Multiplicative.ofAdd.injective h
  · rintro ⟨-, hR⟩
    rw [H.lab_eq_zero_of_mem_R _ hR]
    rfl

theorem card_complementSub : Nat.card (H.complementSub hn) = 512 := by
  have h1 := (H.labHomC hn).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (H.labHomC_surjective hn hσ),
    Subgroup.card_top, H.ker_labHomC hn hσ,
    Nat.card_congr (subgroupOfEquivOfLe (H.A_le_complementSub hn)).toEquiv,
    BinarySymThreeOrbit.card_layerSub_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
  rw [← h1]
  norm_num

theorem mem_or_z₀_mul_mem {d : G} (hd : d ∈ D) :
    d ∈ H.complementSub hn ∨ (θ.symm (.ofAdd (0, 1)) : G) * d ∈ H.complementSub hn := by
  obtain ⟨c, hc, hl⟩ := H.exists_mem_complementSub_lab hn hσ (H.lab ⟨d, hd⟩)
  have hR : d * c⁻¹ ∈ R := by
    apply H.mem_of_zLabel _ (mul_mem hd (inv_mem (H.complementSub_le hn hc)))
    change H.lab ⟨d * c⁻¹, mul_mem hd (inv_mem (H.complementSub_le hn hc))⟩ = 0
    rw [show (⟨d * c⁻¹, mul_mem hd (inv_mem (H.complementSub_le hn hc))⟩ : D) =
      ⟨d, hd⟩ * (⟨c, H.complementSub_le hn hc⟩ : D)⁻¹ from rfl, H.lab_mul, H.lab_inv, hl]
    funext k
    exact symThree_zmod_add_self _
  obtain ⟨⟨B, s⟩, hBs⟩ := BinarySymThreeOrbit.exists_symm θ hR
  have hBc : (θ.symm (.ofAdd (B, 0)) : G) * c ∈ H.complementSub hn :=
    mul_mem (H.A_le_complementSub hn
      (BinarySymThreeOrbit.symm_mem_layerSub θ (AddSubgroup.mem_top B))) hc
  have hsplit : (θ.symm (.ofAdd (B, s)) : G) =
      θ.symm (.ofAdd (0, s)) * θ.symm (.ofAdd (B, 0)) := by
    rw [BinarySymThreeOrbit.symm_mul_symm]
    congr 3
    ext <;> simp
  have hd' : d = θ.symm (.ofAdd (0, s)) * (θ.symm (.ofAdd (B, 0)) * c) := by
    rw [← mul_assoc, ← hsplit, ← hBs]
    group
  rcases zmod_two_cases s with rfl | rfl
  · left
    rw [hd', Prod.mk_zero_zero, ofAdd_zero, map_one, OneMemClass.coe_one, one_mul]
    exact hBc
  · right
    rw [hd', ← mul_assoc, BinarySymThreeOrbit.symm_mul_symm]
    have h2 : ((0, 1) + (0, 1) : binarySymMatrices 3 × ZMod 2) = 0 :=
      BinarySymThreeOrbit.prod_add_self _
    rw [h2, ofAdd_zero, map_one, OneMemClass.coe_one, one_mul]
    exact hBc

theorem zpowers_mul_complementSub :
    ((zpowers (θ.symm (.ofAdd (0, 1)) : G) : Set G) * (H.complementSub hn : Set G)) = D := by
  ext d
  constructor
  · rintro ⟨t, ht, c, hc, rfl⟩
    exact mul_mem (zpowers_le.2 (H.le (θ.symm _).2) ht) (H.complementSub_le hn hc)
  · intro hd
    rcases H.mem_or_z₀_mul_mem hn hσ hd with h | h
    · exact ⟨1, one_mem _, d, h, one_mul d⟩
    · refine ⟨θ.symm (.ofAdd (0, 1)), mem_zpowers _, _, h, ?_⟩
      change (θ.symm (.ofAdd (0, 1)) : G) * ((θ.symm (.ofAdd (0, 1)) : G) * d) = d
      rw [← mul_assoc, BinarySymThreeOrbit.symm_mul_self, one_mul]

omit hn hσ in
theorem card_D : Nat.card D = 1024 := by
  let labD : D →* Multiplicative (Fin 3 → ZMod 2) :=
    MonoidHom.mk' (fun d => Multiplicative.ofAdd (H.lab d)) fun d d' => by
      rw [← ofAdd_add, ← H.lab_mul]
  have hsurj : Function.Surjective labD := fun a => by
    obtain ⟨d, hd, hl⟩ := H.zLabel_surj (Multiplicative.toAdd a)
    exact ⟨⟨d, hd⟩, by
      change Multiplicative.ofAdd (H.lab ⟨d, hd⟩) = a
      rw [show H.lab ⟨d, hd⟩ = _ from hl, ofAdd_toAdd]⟩
  have hker : labD.ker = R.subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change Multiplicative.ofAdd (H.lab d) = 1 ↔ _
    constructor
    · intro h
      exact H.mem_of_zLabel _ d.2 (Multiplicative.ofAdd.injective h)
    · intro hR
      rw [H.lab_eq_zero_of_mem_R d hR]
      rfl
  have h1 := labD.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, hker,
    Nat.card_congr (subgroupOfEquivOfLe H.le).toEquiv, BinarySymThreeOrbit.card_R θ,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    Fintype.card_fin] at h1
  rw [← h1]
  norm_num

theorem mem_A_iff_commute (c : G) (hc : c ∈ H.complementSub hn) :
    c * θ.symm (.ofAdd (0, 1)) = θ.symm (.ofAdd (0, 1)) * c ↔
      c ∈ BinarySymThreeOrbit.layerSub θ ⊤ := by
  constructor
  · intro h
    have hR := H.mem_R_of_commute_z₀ ⟨c, H.complementSub_le hn hc⟩ h
    rw [← H.complementSub_inf_R hn hσ]
    exact ⟨hc, hR⟩
  · intro hA
    exact (H.mul_comm_of_mem_A hA (H.le (θ.symm _).2)).symm

theorem commutators_z₀ :
    {x | ∃ c ∈ H.complementSub hn, c⁻¹ * (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * c *
      θ.symm (.ofAdd (0, 1)) = x} =
      (BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym : Set G) := by
  have key : ∀ c (hc : c ∈ H.complementSub hn), c⁻¹ * (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * c *
      θ.symm (.ofAdd (0, 1)) =
      θ.symm (.ofAdd (altLabel (H.lab ⟨c, H.complementSub_le hn hc⟩), 0)) := fun c hc => by
    have h : (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * c⁻¹ * θ.symm (.ofAdd (0, 1)) * c =
        θ.symm (.ofAdd (altLabel (H.lab ⟨c, H.complementSub_le hn hc⟩), 0)) :=
      H.commutator_z ⟨c, H.complementSub_le hn hc⟩
    rw [show c⁻¹ * (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * c * θ.symm (.ofAdd (0, 1)) =
      ((θ.symm (.ofAdd (0, 1)) : G)⁻¹ * c⁻¹ * θ.symm (.ofAdd (0, 1)) * c)⁻¹ by group, h,
      BinarySymThreeOrbit.symm_inv]
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [key c hc]
    exact BinarySymThreeOrbit.symm_mem_layerSub θ (altLabel_mem_altSym _)
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨c, hc, hl⟩ := H.exists_mem_complementSub_lab hn hσ
      (symThreeOff (B : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    refine ⟨c, hc, ?_⟩
    rw [key c hc, hl, ← eq_altLabel_of_diag_eq_zero (BinarySymThreeOrbit.mem_altSym_iff.1 hB)]

variable [Finite G] in
theorem eq_complementSub {F : Subgroup G} (hFD : F ≤ D)
    (hF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hcard : Nat.card F = 512) :
    F = H.complementSub hn := by
  by_contra hne
  have hFC : ¬ F ≤ H.complementSub hn := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, H.card_complementSub hn hσ]))
  obtain ⟨x, hxF, hxC⟩ := Set.not_subset.1 hFC
  have hzx := (H.mem_or_z₀_mul_mem hn hσ (hFD hxF)).resolve_left hxC
  set c := (θ.symm (.ofAdd (0, 1)) : G) * x with hc
  have hxc : x = θ.symm (.ofAdd (0, 1)) * c := by
    rw [hc, ← mul_assoc, BinarySymThreeOrbit.symm_mul_self, one_mul]
  have hinter : H.complementSub hn ⊓ F ≤ BinarySymThreeOrbit.layerSub θ ⊤ := by
    rintro f ⟨hfC, hfF⟩
    rw [← H.mem_A_iff_commute hn hσ f hfC]
    have hcomm := hF _ hxF f hfF
    have hcf := H.complementSub_comm hn hσ hzx hfC
    rw [hxc] at hcomm
    have h1 : (θ.symm (.ofAdd (0, 1)) : G) * f * c = f * θ.symm (.ofAdd (0, 1)) * c := by
      calc (θ.symm (.ofAdd (0, 1)) : G) * f * c = θ.symm (.ofAdd (0, 1)) * (f * c) := by group
        _ = θ.symm (.ofAdd (0, 1)) * (c * f) := by rw [hcf]
        _ = f * (θ.symm (.ofAdd (0, 1)) * c) := by rw [← hcomm]; group
        _ = f * θ.symm (.ofAdd (0, 1)) * c := by group
    exact (mul_right_cancel h1).symm
  have hle : Nat.card (H.complementSub hn ⊓ F : Subgroup G) ≤ 64 := by
    rw [← BinarySymThreeOrbit.card_layerSub_top θ]
    exact Subgroup.card_le_of_le hinter
  have hidxD : (H.complementSub hn).relIndex D = 2 := by
    have h := card_mul_relIndex_of_le (H.complementSub_le hn)
    rw [H.card_complementSub hn hσ, H.card_D] at h
    omega
  have hidx : (H.complementSub hn ⊓ F).relIndex F ≤ 2 := by
    have h1 := relIndex_inf_le (H := H.complementSub hn) (K := F) (L := F)
    rw [relIndex_self, mul_one] at h1
    refine h1.trans ?_
    rw [← hidxD]
    exact relIndex_le_of_le_right hFD (by rw [hidxD]; norm_num)
  have h := card_mul_relIndex_of_le (inf_le_right : H.complementSub hn ⊓ F ≤ F)
  rw [hcard] at h
  have : Nat.card (H.complementSub hn ⊓ F : Subgroup G) *
      (H.complementSub hn ⊓ F).relIndex F ≤ 64 * 2 := Nat.mul_le_mul hle hidx
  omega

variable [Finite G] in
theorem conj_mem_complementSub_of_mem_normalizer {g : G} (hg : g ∈ normalizer (R : Set G))
    {c : G} (hc : c ∈ H.complementSub hn) : g * c * g⁻¹ ∈ H.complementSub hn := by
  have hF := H.eq_complementSub hn hσ (F := (H.complementSub hn).map (MulAut.conj g).toMonoidHom)
    (by
      rintro _ ⟨c', hc', rfl⟩
      exact H.normal g hg c' (H.complementSub_le hn hc'))
    (by
      rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * c₁ * g⁻¹ * (g * c₂ * g⁻¹) = g * (c₁ * c₂) * g⁻¹ := by group
        _ = g * (c₂ * c₁) * g⁻¹ := by rw [H.complementSub_comm hn hσ hc₁ hc₂]
        _ = g * c₂ * g⁻¹ * (g * c₁ * g⁻¹) := by group)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      H.card_complementSub hn hσ])
  rw [← hF]
  exact ⟨c, hc, rfl⟩

end AltTranslationData

namespace AltTranslationData

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G}
  {θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)} {D S : Subgroup G}
  (H : AltTranslationData θ D S)
include H

theorem exists_unique_abelian :
    ∃ C : Subgroup G, C ≤ D ∧ (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧ Nat.card C = 512 ∧
      C ⊓ R = BinarySymThreeOrbit.layerSub θ ⊤ ∧
      ((zpowers (θ.symm (.ofAdd (0, 1)) : G) : Set G) * (C : Set G)) = D ∧
      (∀ F : Subgroup G, F ≤ D → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → Nat.card F = 512 →
        F = C) ∧
      (∀ g ∈ normalizer (R : Set G), ∀ c ∈ C, g * c * g⁻¹ ∈ C) ∧
      (∀ c ∈ C, c * θ.symm (.ofAdd (0, 1)) = θ.symm (.ofAdd (0, 1)) * c ↔
        c ∈ BinarySymThreeOrbit.layerSub θ ⊤) ∧
      {x | ∃ c ∈ C, c⁻¹ * (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * c * θ.symm (.ofAdd (0, 1)) = x} =
        (BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym : Set G) ∧
      ∀ B ∈ BinarySymThreeOrbit.altSym, ∃ c ∈ C,
        (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * c⁻¹ * θ.symm (.ofAdd (0, 1)) * c =
          θ.symm (.ofAdd (B, 0)) := by
  obtain ⟨n, hn, hσ⟩ := H.levi_surj (glOfDet orderSeven orderSeven_det)
  refine ⟨H.complementSub hn, H.complementSub_le hn,
    fun x hx y hy => H.complementSub_comm hn hσ hx hy, H.card_complementSub hn hσ,
    H.complementSub_inf_R hn hσ, H.zpowers_mul_complementSub hn hσ,
    fun F hFD hF hcard => H.eq_complementSub hn hσ hFD hF hcard,
    fun g hg c hc => H.conj_mem_complementSub_of_mem_normalizer hn hσ hg hc,
    fun c hc => H.mem_A_iff_commute hn hσ c hc, H.commutators_z₀ hn hσ, fun B hB => ?_⟩
  obtain ⟨c, hc, hl⟩ := H.exists_mem_complementSub_lab hn hσ
    (symThreeOff (B : Matrix (Fin 3) (Fin 3) (ZMod 2)))
  refine ⟨c, hc, ?_⟩
  have h := H.commutator_z ⟨c, H.complementSub_le hn hc⟩
  rw [show H.lab ⟨c, H.complementSub_le hn hc⟩ = _ from hl,
    ← eq_altLabel_of_diag_eq_zero (BinarySymThreeOrbit.mem_altSym_iff.1 hB)] at h
  exact h

end AltTranslationData

section Setting

open Module SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits
open LinearMap (BilinForm)

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒮" => (𝒩 ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf

include hzC hsup hinf hz hb hnd hV he in
theorem abelian_subgroup_structure
    (halt : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)) :
    ∃ C₂ : Subgroup G, C₂ ≤ 𝒟 ∧ (∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x) ∧ Nat.card C₂ = 512 ∧
      C₂ ⊓ ℛ = 𝒜 ∧ ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟 ∧
      (∀ F : Subgroup G, F ≤ 𝒟 → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → Nat.card F = 512 →
        F = C₂) ∧
      (∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂) ∧
      (∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) ∧
      {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
        (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G) ∧
      ∀ B ∈ BinarySymThreeOrbit.altSym, ∃ c ∈ C₂,
        z⁻¹ * c⁻¹ * z * c = (θ₂).symm (Multiplicative.ofAdd (B, 0)) := by
  have H := altTranslationData hzC hsup hinf hz hb hnd hV φ he halt
  have hz' := coe_radLabel_symm_z hzC hinf hz φ he
  have hA := layerSub_top_eq hzC hinf hz φ he
  obtain ⟨C, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := H.exists_unique_abelian
  rw [hz'] at h5 h8 h9 h10
  rw [hA] at h4 h8
  exact ⟨C, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
