module

public import CFSG.LieType.Steinberg.TwistedE6.Cert
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LieType.Chevalley.WeylRoots
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Twist
open CFSG.LieType.Universal

abbrev rhoPerm : Equiv.Perm (Fin (Tag.rank .E6)) := TwistTag.E6.perm

abbrev rho (γ : Fin (Tag.rank .E6) → ℤ) : Fin (Tag.rank .E6) → ℤ := permLattice rhoPerm γ

theorem isRoot_rho {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) : IsRoot .E6 (rho γ) :=
  IsRoot.permLattice (TwistTag.cartan_perm .E6) hγ

theorem rho_single (i : Fin (Tag.rank .E6)) : rho (Pi.single i 1) = Pi.single (rhoPerm i) 1 :=
  permLattice_single rhoPerm i

theorem rho_neg_single (i : Fin (Tag.rank .E6)) :
    rho (-Pi.single i 1) = -Pi.single (rhoPerm i) 1 := by
  rw [← rho_single]
  rfl

theorem isSPerm_pCode : IsSPerm e6Data.d pCode := by
  have h := checkPerm_eq
  simp only [checkPerm, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  refine ⟨fun a ha => h.1 a ha, fun a ha b hb hab => ?_⟩
  rcases h.2 a ha b hb with h' | h'
  · exact absurd hab h'
  · exact h'

theorem rhoIdx_spec {j : ℕ} (hj : j < (Tag.rootCertificate .E6).roots.length) :
    rhoIdx j < (Tag.rootCertificate .E6).roots.length ∧
      (Tag.rootCertificate .E6).root (rhoIdx j) = rho ((Tag.rootCertificate .E6).root j) := by
  have h := checkRho_eq
  simp only [checkRho, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact ⟨(h j hj).1, List.ofFn_injective (h j hj).2⟩

theorem trCheck_op {j : ℕ} (hj : j < (Tag.rootCertificate .E6).roots.length) :
    trCheck e6Data.d (e6Data.op j) (twistedOp j) = true := by
  have h := checkTranspose_eq
  simp only [checkTranspose, List.all_eq_true, List.mem_range] at h
  exact h j hj

theorem epsBit_single (i : Fin (Tag.rank .E6)) : epsBit i = false := by
  have h := checkSimple_eq
  simp only [checkSimple, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact (h i).1

theorem epsBit_image_self (i : Fin (Tag.rank .E6)) :
    epsBit ((Tag.rootCertificate .E6).image i i) = false := by
  have h := checkSimple_eq
  simp only [checkSimple, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact (h i).2

variable (k : Type*) [Field k]

@[expose] def pUnit : (Module.End k (Fin e6Data.d →₀ k))ˣ where
  val := toEnd k e6Data.d pCode
  inv := toEnd k e6Data.d (inv e6Data.d pCode)
  val_inv := isSPerm_pCode.toEnd_mul_inv e6Data_valid.d_le
  inv_val := isSPerm_pCode.toEnd_inv_mul e6Data_valid.d_le

@[expose] def sigmaGL (θ : k →+* k) :
    (Module.End k (Fin e6Data.d →₀ k))ˣ →* (Module.End k (Fin e6Data.d →₀ k))ˣ :=
  twistHom θ (pUnit k)

variable {k}

theorem frobT_E (θ : k →+* k) {j : ℕ} (hj : j < (Tag.rootCertificate .E6).roots.length) :
    frobT θ (e6Data.E k j) =
      ((if epsBit j then (1 : k) else -1) •
        ((((pUnit k)⁻¹ : (Module.End k (Fin e6Data.d →₀ k))ˣ) : Module.End k _) *
          e6Data.rootOp k (rho ((Tag.rootCertificate .E6).root j)) *
            ((pUnit k : (Module.End k (Fin e6Data.d →₀ k))ˣ) : Module.End k _))) := by
  have hc : toEnd k e6Data.d (conjOp j) =
      (((pUnit k)⁻¹ : (Module.End k (Fin e6Data.d →₀ k))ˣ) : Module.End k _) *
        e6Data.rootOp k (rho ((Tag.rootCertificate .E6).root j)) *
          ((pUnit k : (Module.End k (Fin e6Data.d →₀ k))ˣ) : Module.End k _) := by
    rw [conjOp, toEnd_comp isSPerm_pCode.wf, toEnd_comp (e6Data_valid.wf_op _), ← (rhoIdx_spec hj).2,
      MinData.rootOp_root (rhoIdx_spec hj).1]
    rfl
  rw [MinData.E, frobT_toEnd θ (trCheck_op hj), twistedOp]
  split_ifs
  · rw [hc, one_smul]
  · rw [toEnd_neg, hc, neg_one_smul]

theorem sigmaGL_xu_root (θ : k →+* k) {j : ℕ} (hj : j < (Tag.rootCertificate .E6).roots.length)
    (c : k) : sigmaGL k θ (e6Data_valid.xu k ((Tag.rootCertificate .E6).root j) c) =
      e6Data_valid.xu k (rho ((Tag.rootCertificate .E6).root j))
        ((if epsBit j then -1 else 1) * θ c) := by
  ext1
  have hP := Units.mul_inv (pUnit k)
  have hE : e6Data.rootOp k ((Tag.rootCertificate .E6).root j) = e6Data.E k j :=
    MinData.rootOp_root hj
  simp only [sigmaGL, twistHom_apply, Units.val_mul, dualHom, MonoidHom.coe_mk, OneHom.coe_mk,
    MinData.Valid.xu_val]
  have hinv : (((e6Data_valid.xu k ((Tag.rootCertificate .E6).root j) c)⁻¹ :
      (Module.End k (Fin e6Data.d →₀ k))ˣ) : Module.End k _) =
        1 - c • e6Data.rootOp k ((Tag.rootCertificate .E6).root j) := rfl
  rw [hinv, frobT_sub, frobT_one, frobT_smul, hE, frobT_E θ hj]
  set A : Module.End k (Fin e6Data.d →₀ k) := ((pUnit k)⁻¹).val
  set B : Module.End k (Fin e6Data.d →₀ k) := (pUnit k).val
  set E' := e6Data.rootOp k (rho ((Tag.rootCertificate .E6).root j))
  have key : B * (1 - θ c • ((if epsBit j then (1 : k) else -1) • (A * E' * B))) * A =
      1 + ((if epsBit j then (-1 : k) else 1) * θ c) • E' := by
    have hBA : B * A = 1 := hP
    have e1 : B * (A * E' * B) * A = E' := by
      rw [← mul_assoc, ← mul_assoc, hBA, one_mul, mul_assoc, hBA, mul_one]
    rw [mul_sub, sub_mul, mul_one, hBA, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      smul_mul_assoc, e1, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 2
    split_ifs <;> ring
  rw [key]

theorem sigmaGL_xu (θ : k →+* k) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ (∀ j < (Tag.rootCertificate .E6).roots.length,
      (Tag.rootCertificate .E6).root j = γ → epsBit j = false → ε = 1) ∧
      ∀ c : k, sigmaGL k θ (e6Data_valid.xu k γ c) = e6Data_valid.xu k (rho γ) (ε * θ c) := by
  obtain ⟨j, hj, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hγ
  refine ⟨if epsBit j then -1 else 1, ?_, ?_, sigmaGL_xu_root θ hj⟩
  · split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro j' hj' hroot hbit
    have := MinData.root_injOn hj' hj hroot
    subst this
    rw [hbit]
    rfl

theorem sigmaGL_xu_single (θ : k →+* k) (i : Fin (Tag.rank .E6)) (c : k) :
    sigmaGL k θ (e6Data_valid.xu k (Pi.single i 1) c) =
      e6Data_valid.xu k (Pi.single (rhoPerm i) 1) (θ c) := by
  obtain ⟨ε, -, hε, h⟩ := sigmaGL_xu θ (isRoot_single .E6 i)
  have hi : (i : ℕ) < (Tag.rootCertificate .E6).roots.length :=
    lt_of_lt_of_le i.2 MinData.rank_le_length
  rw [h, hε i hi (MinData.root_basis i) (epsBit_single i), one_mul, rho_single]

theorem sigmaGL_xu_neg_single (θ : k →+* k) (i : Fin (Tag.rank .E6)) (c : k) :
    sigmaGL k θ (e6Data_valid.xu k (-Pi.single i 1) c) =
      e6Data_valid.xu k (-Pi.single (rhoPerm i) 1) (θ c) := by
  obtain ⟨ε, -, hε, h⟩ := sigmaGL_xu θ (isRoot_neg_single .E6 i)
  have hi : (Tag.rootCertificate .E6).image i i < (Tag.rootCertificate .E6).roots.length :=
    MinData.image_lt (lt_of_lt_of_le i.2 MinData.rank_le_length) i
  rw [h, hε _ hi (MinData.root_image_self i) (epsBit_image_self i), one_mul, rho_neg_single]

theorem sigmaGL_mem (θ : k →+* k) {g : (Module.End k (Fin e6Data.d →₀ k))ˣ}
    (hg : g ∈ e6Data_valid.minGroup k) : sigmaGL k θ g ∈ e6Data_valid.minGroup k := by
  have hle : e6Data_valid.minGroup k ≤ (e6Data_valid.minGroup k).comap (sigmaGL k θ) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    obtain ⟨ε, -, -, h⟩ := sigmaGL_xu θ hγ
    rw [SetLike.mem_coe, Subgroup.mem_comap, h c]
    exact e6Data_valid.xu_mem k _ _
  exact hle hg

variable (k)

@[expose] def sigma (θ : k →+* k) : e6Data_valid.minGroup k →* e6Data_valid.minGroup k :=
  ((sigmaGL k θ).domRestrict (e6Data_valid.minGroup k)).codRestrict (e6Data_valid.minGroup k)
    fun g => sigmaGL_mem θ g.2

theorem coe_sigma (θ : k →+* k) (g : e6Data_valid.minGroup k) :
    ((sigma k θ g : e6Data_valid.minGroup k) : (Module.End k (Fin e6Data.d →₀ k))ˣ) =
      sigmaGL k θ g := rfl

@[expose] def fixedGroup (θ : k →+* k) : Subgroup (e6Data_valid.minGroup k) :=
  MonoidHom.eqLocus (sigma k θ) (MonoidHom.id _)

@[expose] def orbitMap : Fin (Tag.rank .E6) → Fin (Tag.rank .F4) :=
  (![3, 0, 2, 1, 2, 3] : Fin 6 → Fin 4)

@[expose] def twistedRootGroup (θ : k →+* k) (β : Fin (Tag.rank .F4) → ℤ) :
    Subgroup (fixedGroup k θ) :=
  (twistedRootSubgroup {α | IsRoot .E6 α} orbitMap (e6Data_valid.rootGroup k) (sigma k θ)
    β).subgroupOf (fixedGroup k θ)

@[expose] def twistedDatum (θ : k →+* k) : UniversalRootDatum (fixedGroup k θ) where
  rank := Tag.rank .F4
  cartan := Tag.cartan .F4
  isFiniteType := CFSG.LieType.Chevalley.isFiniteType_cartan .F4
  divisible := ∅
  rootGroup := twistedRootGroup k θ

end CFSG.LieType.Steinberg.TwistedE6
