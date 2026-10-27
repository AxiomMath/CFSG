module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightAction
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeAffineOrbitTwoGroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix MulAction SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits
  DegreeEight
open LinearMap (BilinForm)
open scoped Pointwise BinarySymThreeOrbit commutatorElement

namespace AltTranslationData

variable {G : Type*} [Group G] {R : Subgroup G}
  {θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)} {D S : Subgroup G}
  (H : AltTranslationData θ D S)
include H

omit H in
theorem altLabel_mem_altSym (v : Fin 3 → ZMod 2) : altLabel v ∈ BinarySymThreeOrbit.altSym :=
  BinarySymThreeOrbit.mem_altSym_iff.2 (diag_altLabel v)

theorem inv_conj_symm (d : D) (B : binarySymMatrices 3) (s : ZMod 2) :
    (d : G)⁻¹ * θ.symm (.ofAdd (B, s)) * d = θ.symm (.ofAdd (B + s • altLabel (H.lab d), s)) := by
  have h := conjLabel_spec θ ⟨(d : G)⁻¹, H.le_normalizer (inv_mem d.2)⟩ (B, s)
  have h1 : conjLabel θ ⟨(d : G)⁻¹, H.le_normalizer (inv_mem d.2)⟩ (B, s) =
      (B + s • altLabel (H.lab d), s) := by
    have := H.T_eq d⁻¹ B s
    rw [H.lab_inv] at this
    exact this
  rw [h1] at h
  rw [h]
  simp

theorem commutator_z (d : D) :
    (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * (d : G)⁻¹ * θ.symm (.ofAdd (0, 1)) * d =
      θ.symm (.ofAdd (altLabel (H.lab d), 0)) := by
  rw [mul_assoc _ _ (d : G), mul_assoc, ← mul_assoc ((d : G)⁻¹), H.inv_conj_symm, zero_add,
    one_smul, ← InvMemClass.coe_inv, ← map_inv, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_neg,
    ← ofAdd_add]
  congr 3
  ext
  · simp
  · simp only [Prod.snd_add, Prod.snd_neg]
    decide

theorem exists_nu : ∃ ν : D →* Multiplicative ↥BinarySymThreeOrbit.altSym,
    (∀ d : D, (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * (d : G)⁻¹ * θ.symm (.ofAdd (0, 1)) * d =
      θ.symm (.ofAdd (((Multiplicative.toAdd (ν d) : ↥BinarySymThreeOrbit.altSym) :
        binarySymMatrices 3), 0))) ∧
    Function.Surjective ν ∧ ν.ker = R.subgroupOf D ∧
    ∀ (d : D) (B : binarySymMatrices 3) (s : ZMod 2),
      (d : G)⁻¹ * θ.symm (.ofAdd (B, s)) * d =
        θ.symm (.ofAdd (B + s • ((Multiplicative.toAdd (ν d) : ↥BinarySymThreeOrbit.altSym) :
          binarySymMatrices 3), s)) := by
  refine ⟨MonoidHom.mk' (fun d => Multiplicative.ofAdd
      ⟨altLabel (H.lab d), altLabel_mem_altSym _⟩) fun d d' => ?_, fun d => ?_,
    fun B => ?_, ?_, fun d B s => ?_⟩
  · rw [H.lab_mul, ← ofAdd_add]
    congr 1
    exact Subtype.ext (altLabel_add _ _)
  · exact H.commutator_z d
  · obtain ⟨d, hd, hl⟩ := H.zLabel_surj (symThreeOff (((Multiplicative.toAdd B :
      ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    refine ⟨⟨d, hd⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change altLabel (H.lab ⟨d, hd⟩) =
      ((Multiplicative.toAdd B : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3)
    rw [show H.lab ⟨d, hd⟩ = _ from hl]
    exact (eq_altLabel_of_diag_eq_zero (BinarySymThreeOrbit.mem_altSym_iff.1
      (Multiplicative.toAdd B).2)).symm
  · ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change Multiplicative.ofAdd (⟨altLabel (H.lab d), _⟩ : ↥BinarySymThreeOrbit.altSym) = 1 ↔ _
    constructor
    · intro h
      apply H.mem_of_zLabel d d.2
      have h1 := congrArg (fun x => ((Multiplicative.toAdd x : ↥BinarySymThreeOrbit.altSym) :
        binarySymMatrices 3)) h
      simp only [toAdd_ofAdd, toAdd_one] at h1
      have h2 : altLabel (H.lab d) = altLabel 0 := by rw [altLabel_zero]; exact h1
      exact altLabel_injective h2
    · intro hR
      have h0 : H.lab d = 0 := by
        change symThreeOff ((H.T d (0, 1)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0
        rw [H.T_of_mem d hR]
        funext k
        fin_cases k <;> rfl
      rw [h0]
      apply Multiplicative.toAdd.injective
      exact Subtype.ext altLabel_zero
  · exact H.inv_conj_symm d B s

omit H in
theorem eq_symm_of_mem {x : G} (hx : x ∈ R) :
    x = θ.symm (.ofAdd (Multiplicative.toAdd (θ ⟨x, hx⟩))) := by
  rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem center_eq (hC : centralizer (R : Set G) = R) :
    (center D).map D.subtype = BinarySymThreeOrbit.layerSub θ ⊤ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxR : (x : G) ∈ R := by
      rw [← hC, mem_centralizer_iff]
      intro r hr
      have h := mem_center_iff.1 hx ⟨r, H.le hr⟩
      exact congrArg Subtype.val h
    obtain ⟨⟨B, s⟩, hBs⟩ : ∃ X, Multiplicative.toAdd (θ ⟨x, hxR⟩) = X := ⟨_, rfl⟩
    have hxe : (x : G) = θ.symm (.ofAdd (B, s)) := by
      rw [eq_symm_of_mem hxR, hBs]
    obtain ⟨d, hd, hl⟩ := H.zLabel_surj (bvec 0)
    have hcomm := mem_center_iff.1 hx ⟨d, hd⟩
    have h1 : (d : G)⁻¹ * x * d = x := by
      have := congrArg Subtype.val hcomm
      simp only [Subgroup.coe_mul] at this
      rw [mul_assoc, ← this]
      group
    rw [hxe, H.inv_conj_symm ⟨d, hd⟩] at h1
    have h2 := congrArg Prod.fst (Multiplicative.ofAdd.injective (θ.symm.injective
      (Subtype.ext h1)))
    simp only [add_eq_left] at h2
    rw [show H.lab ⟨d, hd⟩ = bvec 0 from hl] at h2
    have hs : s = 0 := by
      rcases zmod_two_cases s with rfl | rfl
      · rfl
      · rw [one_smul] at h2
        have h3 := congrArg (fun B : binarySymMatrices 3 =>
          ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2)) h2
        simp [altLabel, altMat, bvec] at h3
    show (x : G) ∈ _
    rw [hxe, hs]
    exact BinarySymThreeOrbit.symm_mem_layerSub θ (AddSubgroup.mem_top B)
  · rintro _ ⟨B, -, rfl⟩
    refine ⟨⟨θ.symm (.ofAdd (B, 0)), H.le (θ.symm _).2⟩, mem_center_iff.2 fun d => ?_, rfl⟩
    apply Subtype.ext
    have h := H.inv_conj_symm d B 0
    rw [zero_smul, add_zero] at h
    simp only [Subgroup.coe_mul]
    calc (d : G) * θ.symm (.ofAdd (B, 0)) = d * ((d : G)⁻¹ * θ.symm (.ofAdd (B, 0)) * d) := by
          rw [h]
      _ = θ.symm (.ofAdd (B, 0)) * d := by group

theorem sq_mem_R (d : D) : (d : G) ^ 2 ∈ R := by
  have h : H.lab (d * d) = 0 := by
    rw [H.lab_mul]
    funext k
    exact symThree_zmod_add_self _
  have h' := H.mem_of_zLabel _ (d * d).2 h
  rwa [sq]

abbrev sqLabel (d : D) : binarySymMatrices 3 × ZMod 2 :=
  Multiplicative.toAdd (θ ⟨(d : G) ^ 2, H.sq_mem_R d⟩)

theorem sqLabel_spec (d : D) : (θ.symm (.ofAdd (H.sqLabel d)) : G) = (d : G) ^ 2 := by
  rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem sqLabel_eq_of_symm (d : D) {X : binarySymMatrices 3 × ZMod 2}
    (h : (θ.symm (.ofAdd X) : G) = (d : G) ^ 2) : H.sqLabel d = X := by
  apply Multiplicative.ofAdd.injective
  apply θ.symm.injective
  apply Subtype.ext
  rw [H.sqLabel_spec, h]

theorem sqLabel_snd (d : D) (ha : H.lab d ≠ 0) : (H.sqLabel d).2 = 0 := by
  have h := H.inv_conj_symm d (H.sqLabel d).1 (H.sqLabel d).2
  rw [show ((H.sqLabel d).1, (H.sqLabel d).2) = H.sqLabel d from rfl, H.sqLabel_spec,
    show (d : G)⁻¹ * (d : G) ^ 2 * d = (d : G) ^ 2 by group, ← H.sqLabel_spec] at h
  have h2 := congrArg Prod.fst (Multiplicative.ofAdd.injective (θ.symm.injective
    (Subtype.ext h)))
  simp only [left_eq_add] at h2
  rcases zmod_two_cases (H.sqLabel d).2 with h3 | h3
  · exact h3
  · exfalso
    rw [h3, one_smul] at h2
    exact ha (altLabel_injective (h2.trans altLabel_zero.symm))

theorem diag_sqLabel_eq (d d' : D) (h : H.lab d = H.lab d') :
    symThreeDiag ((H.sqLabel d').1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      symThreeDiag ((H.sqLabel d).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  set r : D := d⁻¹ * d' with hr
  have hrR : (r : G) ∈ R := by
    apply H.mem_of_zLabel _ r.2
    change H.lab r = 0
    rw [hr, H.lab_mul, H.lab_inv, h]
    funext k
    exact symThree_zmod_add_self _
  obtain ⟨⟨Br, sr⟩, hBr⟩ := BinarySymThreeOrbit.exists_symm θ hrR
  have hd' : (d' : G) = d * r := by rw [hr]; simp
  have hsq : (d' : G) ^ 2 = (d : G) ^ 2 * ((d : G)⁻¹ * r * d) * r := by
    rw [hd', sq, sq]
    group
  rw [← H.sqLabel_spec d, hBr, H.inv_conj_symm, BinarySymThreeOrbit.symm_mul_symm,
    BinarySymThreeOrbit.symm_mul_symm] at hsq
  rw [H.sqLabel_eq_of_symm d' hsq.symm]
  have hsr : symThreeDiag ((sr • altLabel (H.lab d) : binarySymMatrices 3) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
    rcases zmod_two_cases sr with rfl | rfl
    · rw [zero_smul]
      rfl
    · rw [one_smul, diag_altLabel]
  simp only [Prod.fst_add, AddSubgroup.coe_add, symThreeDiag_add, hsr, add_zero]
  funext k
  simp only [Pi.add_apply]
  rw [add_assoc, symThree_zmod_add_self, add_zero]

theorem sq_mem (d : D) :
    (d : G) ^ 2 ∈ BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym := by
  by_cases ha : H.lab d = 0
  · have hR := H.mem_of_zLabel d d.2 ha
    obtain ⟨X, hX⟩ := BinarySymThreeOrbit.exists_symm θ hR
    rw [hX, sq, BinarySymThreeOrbit.symm_mul_self]
    exact one_mem _
  have hq : symThreeDiag ((H.sqLabel d).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
    apply eq_zero_of_forall_covec_stabilizer ha
    intro s hs hsa
    set σ := glOfDet s hs
    obtain ⟨n, hn, hσ⟩ := H.levi_surj σ
    obtain ⟨hl, -⟩ := H.conjD_levi n hn σ hσ d
    have hl' : H.lab (H.conjD n (H.le_normalizer' hn) d) = H.lab d := by
      rw [hl]
      conv_lhs => rw [← hsa]
      rw [mulVec_mulVec, ← transpose_mul, ← coe_glOfDet s hs, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, transpose_one, one_mulVec]
    have h1 := H.diag_sqLabel_eq d _ hl'.symm
    have h2 : H.sqLabel (H.conjD n (H.le_normalizer' hn) d) =
        conjLabel θ ⟨n, H.le_normalizer' hn⟩ (H.sqLabel d) := by
      apply H.sqLabel_eq_of_symm
      rw [conjLabel_spec, H.sqLabel_spec]
      change (n : G) * (d : G) ^ 2 * n⁻¹ = (n * d * n⁻¹) ^ 2
      simp only [sq]
      group
    rw [h2, hσ, symThreeDiag_coe_congr, coe_glOfDet] at h1
    exact h1
  have hX : (d : G) ^ 2 = θ.symm (.ofAdd ((H.sqLabel d).1, 0)) := by
    rw [← H.sqLabel_spec, ← H.sqLabel_snd d ha]
  rw [hX]
  exact BinarySymThreeOrbit.symm_mem_layerSub θ (BinarySymThreeOrbit.mem_altSym_iff.2 hq)

theorem closure_sq_le :
    closure {x | ∃ d ∈ D, d ^ 2 = x} ≤ BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym :=
  closure_le _ |>.2 fun _ ⟨d, hd, hx⟩ => hx ▸ H.sq_mem ⟨d, hd⟩

omit H in
theorem commutator_le_closure_sq : ⁅D, D⁆ ≤ closure {x | ∃ d ∈ D, d ^ 2 = x} := by
  rw [commutator_le]
  intro a ha c hc
  have h : ⁅a, c⁆ = a ^ 2 * (a⁻¹ * c) ^ 2 * c⁻¹ ^ 2 := by
    rw [commutatorElement_def]
    simp only [sq]
    group
  rw [h]
  exact mul_mem (mul_mem (subset_closure ⟨a, ha, rfl⟩)
    (subset_closure ⟨a⁻¹ * c, mul_mem (inv_mem ha) hc, rfl⟩))
    (subset_closure ⟨c⁻¹, inv_mem hc, rfl⟩)

theorem layerSub_altSym_le_commutator :
    BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym ≤ ⁅D, D⁆ := by
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨d, hd, hl⟩ := H.zLabel_surj (symThreeOff (B : Matrix (Fin 3) (Fin 3) (ZMod 2)))
  have h := H.commutator_z ⟨d, hd⟩
  rw [show H.lab ⟨d, hd⟩ = _ from hl, ← eq_altLabel_of_diag_eq_zero
    (BinarySymThreeOrbit.mem_altSym_iff.1 hB)] at h
  rw [← h]
  have hz : (θ.symm (.ofAdd (0, 1)) : G) ∈ D := H.le (θ.symm _).2
  have h2 : (θ.symm (.ofAdd (0, 1)) : G)⁻¹ * (d : G)⁻¹ * θ.symm (.ofAdd (0, 1)) * d =
      ⁅(θ.symm (.ofAdd (0, 1)) : G)⁻¹, d⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv]
  rw [h2]
  exact commutator_mem_commutator (inv_mem hz) (inv_mem hd)

theorem commutator_eq : ⁅D, D⁆ = BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym :=
  le_antisymm (commutator_le_closure_sq.trans H.closure_sq_le) H.layerSub_altSym_le_commutator

theorem closure_sq_eq :
    closure {x | ∃ d ∈ D, d ^ 2 = x} = BinarySymThreeOrbit.layerSub θ BinarySymThreeOrbit.altSym :=
  le_antisymm H.closure_sq_le (H.layerSub_altSym_le_commutator.trans commutator_le_closure_sq)

end AltTranslationData

section Setting

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

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem coe_radLabel_symm_apply (B : binarySymMatrices 3) (s : ZMod 2) :
    (((θ₂).symm (Multiplicative.ofAdd (B, s)) : ℛ) : G) =
      tauHom φ he (Multiplicative.ofAdd B) * RadicalLabels.zPow z s :=
  rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem mem_A_iff {x : G} :
    x ∈ 𝒜 ↔ ∃ B : binarySymMatrices 3, x = (θ₂).symm (Multiplicative.ofAdd (B, 0)) := by
  rw [mem_pullSub_iff φ he]
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨Multiplicative.toAdd B, (RadicalLabels.radHom_tau φ he hzC hz _).symm⟩
  · rintro ⟨B, rfl⟩
    exact ⟨Multiplicative.ofAdd B, (RadicalLabels.radHom_tau φ he hzC hz B).symm⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem z_mul_tauHom_altLabel (v : Fin 3 → ZMod 2) :
    z * tauHom φ he (Multiplicative.ofAdd (altLabel v)) =
      (θ₂).symm (Multiplicative.ofAdd (altLabel v, 1)) := by
  rw [coe_radLabel_symm_apply, RadicalLabels.zPow_one]
  exact (RadicalLabels.mul_comm_z hzC (tauHom_mem φ he _)).symm

include hzC hsup hinf hz hb hnd hV he in
theorem altTranslationData
    (halt : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)) :
    AltTranslationData θ₂ 𝒟 𝒮 := by
  classical
  have h8 : Nat.card (conjClass 𝒩 z) = 8 := by
    rw [halt, ← range_alt_labels φ he, Nat.card_range_of_injective (alt_labels_injective φ he)]
    simp
  obtain ⟨-, ℓ₁, -, hform, ρ, hρ, hKaff, -, hkerρ, -, -, D, hDdef, hDpcore, hcardD, hRD, hDM, -,
    -, -, -, -, -⟩ :=
    degree_eight_structure hzC hsup hinf hz hb hnd hV φ he 𝒩 inf_le_left le_rfl h8
  have hℓ₁ : ∀ v, (ℓ₁ v : G) = (θ₂).symm (Multiplicative.ofAdd (altLabel v, 1)) := by
    rcases hform with ⟨h1, -⟩ | ⟨-, hf⟩
    · exfalso
      have hv : (Pi.single 0 1 : Fin 3 → ZMod 2) ≠ 0 := fun h => by
        simpa using congrFun h 0
      have hx : z * tauHom φ he (Multiplicative.ofAdd (altLabel (Pi.single 0 1))) ∈
          z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) :=
        ⟨_, (mem_tauSet_iff φ he).2 ⟨_, (sym_rank_two_alternating_iff
          (altLabel (Pi.single 0 1))).2 ⟨_, hv, rfl⟩, rfl⟩, rfl⟩
      have hx' : z * tauHom φ he (Multiplicative.ofAdd (altLabel (Pi.single 0 1))) ∈
          conjClass 𝒩 z := by
        rw [halt]
        exact Or.inr hx
      rw [h1] at hx'
      rcases hx' with h | h
      · exact notMem_smul_tauSet φ he (P := fun B => B.rank = 2 ∧ ∀ i, B i i = 0) (by simp)
          (Set.mem_singleton_iff.1 h ▸ hx)
      · exact Set.disjoint_left.1 (Set.disjoint_smul_set.2 (disjoint_tauSet φ he
          fun B (h : B.rank = 1) h' => by rw [h] at h'; exact absurd h'.1 (by norm_num))) h hx
    · intro v
      obtain ⟨a, ha, hv, hmat⟩ := hf v
      rw [hv, RadicalLabels.eq_tauHom_of_toMatrix φ he ha (altLabel v) hmat,
        z_mul_tauHom_altLabel]
  have hDeq : 𝒟 = D := hDpcore.symm
  have hmemD : ∀ g : G, g ∈ 𝒟 ↔ ∃ h : g ∈ 𝒩, ∃ c, ∀ v, ρ ⟨g, h⟩ v = c + v := fun g => by
    rw [hDeq, hDdef]
    constructor
    · rintro ⟨m, ⟨c, hc⟩, rfl⟩
      exact ⟨m.2, c, hc⟩
    · rintro ⟨h, c, hc⟩
      exact ⟨⟨g, h⟩, ⟨c, hc⟩, rfl⟩
  have hDN : 𝒟 ≤ 𝒩 := map_subtype_le _
  have htr : ∀ (d : G) (hd : d ∈ 𝒟) (v : Fin 3 → ZMod 2),
      conjLabel θ₂ ⟨d, hDN hd⟩ (altLabel v, 1) =
        (altLabel (v + zLabel θ₂ ⟨d, hDN hd⟩), 1) := by
    intro d hd
    obtain ⟨hdN, c, hc⟩ := (hmemD d).1 hd
    have key : ∀ v, conjLabel θ₂ ⟨d, hDN hd⟩ (altLabel v, 1) = (altLabel (v + c), 1) := by
      intro v
      rw [conjLabel_eq_iff, ← hℓ₁, ← hℓ₁]
      have h := hρ ⟨d, hdN⟩ v
      rw [hc, add_comm] at h
      exact h.symm
    have hzl : zLabel θ₂ ⟨d, hDN hd⟩ = c := by
      have h := key 0
      rw [altLabel_zero, zero_add] at h
      change symThreeOff ((conjLabel θ₂ ⟨d, hDN hd⟩ (0, 1)).1 :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = c
      rw [h, symThreeOff_altLabel]
    intro v
    rw [hzl, key]
  obtain ⟨σ, hσs, -, -, hσ⟩ := exists_sigma hzC hsup hinf hb hnd hV φ he
  have hlevi : ∀ (n : 𝒮) (X : binarySymMatrices 3 × ZMod 2),
      conjLabel θ₂ ⟨n, (mem_inf.1 n.2).1⟩ X = (symThreeCongr (σ n) X.1, X.2) := by
    intro n X
    rw [conjLabel_eq_iff]
    exact RadicalLabels.conj_radHom_of_sigma φ he hzC hz (fun _ hx => (mem_inf.1 hx).2) σ hσ n
      X.1 X.2
  refine
    { comm := fun x hx y hy => mul_comm_of_mem_radical hzC hinf hz hb hnd hV φ he hx hy
      le_normalizer := hDN
      le_normalizer' := inf_le_left
      le := hDeq ▸ hRD
      normal := fun n hn d hd => ?_
      isPGroup := IsPGroup.of_card (n := 10) (by rw [hDeq, hcardD]; norm_num)
      translate := htr
      mem_of_zLabel := fun d hd h0 => ?_
      zLabel_surj := fun a => ?_
      levi := fun n hn => ⟨σ ⟨n, hn⟩, hlevi ⟨n, hn⟩⟩
      levi_surj := fun D₀ => ?_ }
  ·
    obtain ⟨d', hd', rfl⟩ := hd
    exact ⟨⟨n, hn⟩ * d' * ⟨n, hn⟩⁻¹,
      (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 𝒩).conj_mem d'
        hd' ⟨n, hn⟩, rfl⟩
  ·
    obtain ⟨hdN, c, hc⟩ := (hmemD d).1 hd
    have hc0 : c = 0 := by
      have h := htr d hd 0
      rw [h0] at h
      have h' : conjLabel θ₂ ⟨d, hDN hd⟩ (altLabel 0, 1) = (altLabel (0 + c), 1) := by
        rw [conjLabel_eq_iff, ← hℓ₁, ← hℓ₁]
        have h2 := hρ ⟨d, hdN⟩ 0
        rw [hc, add_comm] at h2
        exact h2.symm
      rw [h] at h'
      have h3 := altLabel_injective (congrArg Prod.fst h')
      rw [zero_add, zero_add] at h3
      exact h3.symm
    have h1 : ρ ⟨d, hdN⟩ = 1 := Equiv.ext fun v => by rw [hc, hc0, zero_add]; rfl
    have h2 : (⟨d, hdN⟩ : 𝒩) ∈ (ℛ).subgroupOf 𝒩 := hkerρ ▸ MonoidHom.mem_ker.2 h1
    exact mem_subgroupOf.1 h2
  ·
    obtain ⟨m, hm⟩ : Equiv.addLeft a ∈ ρ.range := by
      rw [hKaff]
      exact ⟨a, LinearEquiv.refl _ _, fun u => rfl⟩
    have hmD : (m : G) ∈ 𝒟 := (hmemD m).2 ⟨m.2, a, fun v => by
      show ρ m v = a + v
      rw [hm]
      rfl⟩
    refine ⟨m, hmD, ?_⟩
    have h := htr m hmD 0
    have h' : conjLabel θ₂ ⟨m, hDN hmD⟩ (altLabel 0, 1) = (altLabel (0 + a), 1) := by
      rw [conjLabel_eq_iff, ← hℓ₁, ← hℓ₁]
      have h2 := hρ m 0
      rw [hm, show (Equiv.addLeft a) 0 = 0 + a by simp] at h2
      exact h2.symm
    rw [h] at h'
    have h3 := congrArg (fun X : binarySymMatrices 3 × ZMod 2 =>
      symThreeOff ((X.1 : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h'
    simpa only [symThreeOff_altLabel, zero_add] using h3
  ·
    obtain ⟨n, rfl⟩ := hσs D₀
    exact ⟨n, n.2, hlevi n⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem coe_radLabel_symm_z : (((θ₂).symm (Multiplicative.ofAdd (0, 1)) : ℛ) : G) = z :=
  RadicalLabels.radHom_z φ he hzC hz

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem layerSub_top_eq : BinarySymThreeOrbit.layerSub θ₂ ⊤ = 𝒜 := by
  ext x
  rw [BinarySymThreeOrbit.mem_layerSub, mem_A_iff hzC hinf hz φ he]
  exact ⟨fun ⟨B, _, h⟩ => ⟨B, h⟩, fun ⟨B, h⟩ => ⟨B, AddSubgroup.mem_top B, h⟩⟩

include hzC hsup hinf hz hb hnd hV he in
theorem translation_group_structure
    (halt : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)) :
    ∃ ν₂ : 𝒟 →* Multiplicative ↥BinarySymThreeOrbit.altSym,
      (∀ d : 𝒟, z⁻¹ * (d : G)⁻¹ * z * d = (θ₂).symm (Multiplicative.ofAdd
        (((Multiplicative.toAdd (ν₂ d) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3),
          0))) ∧
      Function.Surjective ν₂ ∧ ν₂.ker = (ℛ).subgroupOf 𝒟 ∧
      (∀ (d : 𝒟) (B : binarySymMatrices 3) (s : ZMod 2),
        (d : G)⁻¹ * (θ₂).symm (Multiplicative.ofAdd (B, s)) * d =
          (θ₂).symm (Multiplicative.ofAdd (B + s • ((Multiplicative.toAdd (ν₂ d) :
            ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3), s))) ∧
      (center 𝒟).map (𝒟).subtype = 𝒜 ∧
      ⁅𝒟, 𝒟⁆ = BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym ∧
      closure {x | ∃ d ∈ 𝒟, d ^ 2 = x} =
        BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym := by
  have H := altTranslationData hzC hsup hinf hz hb hnd hV φ he halt
  obtain ⟨ν, hν1, hν2, hν3, hν4⟩ := H.exists_nu
  have hz' := coe_radLabel_symm_z hzC hinf hz φ he
  obtain ⟨hAe, hAc, hAC, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  have hRC := centralizer_sup_eq hzC hsup hinf hz (pullSub_le φ _) hAe hAc hAC
  refine ⟨ν, fun d => ?_, hν2, hν3, hν4, ?_, H.commutator_eq, H.closure_sq_eq⟩
  · have h := hν1 d
    rw [hz'] at h
    exact h
  · rw [H.center_eq hRC, layerSub_top_eq hzC hinf hz φ he]

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
