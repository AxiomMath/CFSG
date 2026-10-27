module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMat
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem lin_structure {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    (linearAutGroup n K).Normal ∧
    (∀ a b : MulAut (projectiveSL n K), a * b * a⁻¹ * b⁻¹ ∈ linearAutGroup n K) ∧
    (conjAut n K).ker = (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm'⟩ := FiniteField.card K ℓ
  have hm : Nat.card K = ℓ ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm'
  obtain ⟨hker, -, -, -, -, hDn, hab, -⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent (n := n) (K := K)
      hℓp m.pos hn hm
  exact ⟨hDn, hab, hker⟩

@[expose] noncomputable def statedEquivL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (QuotientGroup.congr (scalars n K) ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K) (by
      rw [scalars_eq_center]
      exact CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars n K)).symm

theorem statedEquivL_mk (n : ℕ) (K : Type) [Field K] (A : StatedSL n K) :
    statedEquivL n K (QuotientGroup.mk A) =
      proj n K ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm A) := by
  apply (statedEquivL n K).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change _ = QuotientGroup.mk (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm A))
  rw [MulEquiv.apply_symm_apply]

variable {Y : Type} [Group Y] {L : Subgroup Y} [L.Normal] {K : Type} [Field K] {n : ℕ}

theorem thetaP_eq_conjAut {x : Y} (e : (↥L ⧸ center ↥L) ≃* StatedProj (StatedSL n K))
    (y : GL (Fin n) K)
    (hact : ∀ (g g' : ↥L) (A B : ↥(StatedSL n K)), x * (g : Y) * x⁻¹ = (g' : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B : GL (Fin n) K) = y * (A : GL (Fin n) K) * y⁻¹ →
      e (QuotientGroup.mk g') = QuotientGroup.mk B) :
    thetaP L (e.trans (statedEquivL n K)) x = conjAut n K y := by
  ext z
  obtain ⟨w, rfl⟩ := (e.trans (statedEquivL n K)).surjective z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk g))
  set ϕ := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K with hϕ
  set g₁ : SpecialLinearGroup (Fin n) K := ϕ.symm A with hg₁
  set B : ↥(StatedSL n K) :=
    ϕ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K y g₁) with hB
  have hBA : (B : GL (Fin n) K) = y * (A : GL (Fin n) K) * y⁻¹ := by
    apply Units.ext
    rw [hB, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, coe_slConjugation,
      Units.val_mul, Units.val_mul]
    have : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g₁ : Matrix (Fin n) (Fin n) K) := by
      rw [hg₁, ← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
        MulEquiv.apply_symm_apply]
    rw [this]
  have h1 : e (QuotientGroup.mk (MulAut.conjNormal x g)) = QuotientGroup.mk B :=
    hact g (MulAut.conjNormal x g) A B (by simp [MulAut.conjNormal_apply]) hA.symm hBA
  have hL : thetaP L (e.trans (statedEquivL n K)) x
      ((e.trans (statedEquivL n K)) (QuotientGroup.mk g)) =
        statedEquivL n K (e (QuotientGroup.mk (MulAut.conjNormal x g))) := by
    rw [thetaP_apply, MulEquiv.symm_apply_apply, theta_mk]
    rfl
  rw [hL, h1, statedEquivL_mk]
  change _ = conjAut n K y (statedEquivL n K (e (QuotientGroup.mk g)))
  rw [← hA, statedEquivL_mk, conjAut_proj, hB, MulEquiv.symm_apply_apply]

theorem two_elt_mem_inner_lin [Finite K] (hn : 1 ≤ n) (hodd : Odd n)
    {α : MulAut (projectiveSL n K)} (hα : α ∈ linearAutGroup n K) {k : ℕ}
    (hk : α ^ (2 ^ k) = 1) : α ∈ inner (projectiveSL n K) := by
  have hdvd := UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := n) hn
  set D := linearAutGroup n K with hD
  set I := inner (projectiveSL n K) with hI
  set c : D ⧸ I.subgroupOf D := QuotientGroup.mk ⟨α, hα⟩ with hc
  have hc2 : c ^ (2 ^ k) = 1 := by
    rw [hc, ← QuotientGroup.mk_pow]
    have : (⟨α, hα⟩ : D) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have hodd' : Odd (I.relIndex D) :=
    hodd.of_dvd_nat (hdvd.trans (Nat.gcd_dvd_left _ _))
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2
  have h2 : orderOf c ∣ I.relIndex D := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard c
  have hcop : Nat.Coprime (2 ^ k) (I.relIndex D) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd')
  have h3 : orderOf c ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  have h4 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have h5 : (⟨α, hα⟩ : D) ∈ I.subgroupOf D := (QuotientGroup.eq_one_iff _).1 h4
  exact Subgroup.mem_subgroupOf.1 h5

theorem conjAut_not_mem_inner [Finite K] (hn : 3 ≤ n) (y : GL (Fin n) K)
    (hdet : ∀ b : K, b ^ n ≠ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) :
    conjAut n K y ∉ inner (projectiveSL n K) := by
  rintro ⟨z, hz⟩
  obtain ⟨g, rfl⟩ := proj_surjective n K z
  rw [← conjAut_toGL] at hz
  obtain ⟨-, -, hker⟩ := lin_structure (K := K) hn
  have hmem : y * (SpecialLinearGroup.toGL g)⁻¹ ∈ (conjAut n K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hz, mul_inv_cancel]
  rw [hker] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hy : y = GeneralLinearGroup.scalar (Fin n) c * SpecialLinearGroup.toGL g := by
    rw [hc]
    group
  apply hdet (c : K)
  rw [hy, Units.val_mul, Matrix.det_mul, det_scalar_eq]
  have : ((SpecialLinearGroup.toGL g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g := rfl
  rw [this, Matrix.SpecialLinearGroup.det_coe, mul_one]

theorem le_of_relIndex_dvd_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {I D S : Subgroup G}
    (hIS : I ≤ S) (hdvd : I.relIndex D ∣ p) {d : G} (hd : d ∈ D) (hdS : d ∈ S)
    (hdI : d ∉ I) : D ≤ S := by
  set J : Subgroup D := I.subgroupOf D with hJ
  set a : D := ⟨d, hd⟩ with ha
  have haJ : a ∉ J := fun h => hdI (Subgroup.mem_subgroupOf.1 h)
  set J' : Subgroup D := J ⊔ Subgroup.zpowers a with hJ'
  have hJle : J ≤ J' := le_sup_left
  have h1 : J.relIndex J' * J'.index = J.index := Subgroup.relIndex_mul_index hJle
  have hJidx : J.index ∣ p := hdvd
  have hJ0 : J.index ≠ 0 := fun h0 => hp.ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ hJidx))
  have hJ'top : J' = ⊤ := by
    by_contra hne
    have hidx : J'.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    have hd1 : J'.index ∣ p := (Dvd.intro_left _ h1).trans hJidx
    have hidxp : J'.index = p := ((Nat.dvd_prime hp).1 hd1).resolve_left hidx
    have h2 : J.relIndex J' = 1 := by
      rw [hidxp] at h1
      have h3 : J.relIndex J' * p ≤ p := h1 ▸ Nat.le_of_dvd hp.pos hJidx
      have h4 : J.relIndex J' ≠ 0 := fun h0 => hJ0 (by rw [← h1, h0, zero_mul])
      nlinarith [hp.pos, Nat.pos_of_ne_zero h4]
    have h5 : J' ≤ J := Subgroup.relIndex_eq_one.1 h2
    exact haJ (h5 (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
  have hle : J' ≤ S.subgroupOf D := by
    refine sup_le (fun y hy => ?_) ?_
    · exact Subgroup.mem_subgroupOf.2 (hIS (Subgroup.mem_subgroupOf.1 hy))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_subgroupOf.2 hdS
  intro x hx
  have : (⟨x, hx⟩ : D) ∈ S.subgroupOf D := hle (hJ'top ▸ Subgroup.mem_top _)
  exact Subgroup.mem_subgroupOf.1 this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
