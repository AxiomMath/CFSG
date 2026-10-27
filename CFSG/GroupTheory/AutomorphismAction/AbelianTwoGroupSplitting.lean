module


public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.GroupTheory.AutomorphismAction

open scoped Pointwise commutatorElement
open CFSG

theorem abelian_twoGroup_splitting {H : Type*} [Group H] [Finite H] (R A : Subgroup H)
    (hR : IsPGroup 2 R) (hAodd : Odd (Nat.card A)) (hAR : A ≤ Subgroup.normalizer (R : Set H))
    (hRab : IsMulCommutative R) :
    (⁅R, A⁆ ⊔ (R ⊓ Subgroup.centralizer (A : Set H)) = R) ∧
      Disjoint ⁅R, A⁆ (R ⊓ Subgroup.centralizer (A : Set H)) ∧
      ⁅R, A⁆ ≤ Subgroup.centralizer
        ((R ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) : Set H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have coprime_decomp_gen {R A : Subgroup H} (hR : IsPGroup 2 R)
      (hA_norm_R : A ≤ Subgroup.normalizer (R : Set H)) (hAodd : Odd (Nat.card A)) :
      (R : Set H) =
        (⁅R, A⁆ : Subgroup H) *
          ((R ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) : Set H) := by
    let : Subgroup.Normalizes A R := ⟨hA_norm_R⟩
    let Cfix : Subgroup R := fixedPointSubgroup A R
    let Ccomm : Subgroup R := commutatorAction (A := A) (G := R)
    have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
      obtain ⟨k, hk⟩ := hR.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hAodd)
    have hsolvR : Group.IsSolvable R := @IsNilpotent.to_isSolvable _ _ hR.isNilpotent
    have hsup : Cfix ⊔ Ccomm = ⊤ :=
      fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hsolvR hcop
    have hcommMap : Ccomm.map R.subtype = ⁅R, A⁆ :=
      commutatorAction_subgroup_conj_map_eq_commutator R A hA_norm_R
    have hfixEq : Cfix = ((R ⊓ Subgroup.centralizer (A : Set H)).subgroupOf R) := by
      simpa [subgroupCentralizerIn] using
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R A hA_norm_R
    have : Ccomm.Normal :=
      (commutatorAction_normal_and_invariant (A := A) (G := R)).1
    apply Set.Subset.antisymm
    · intro x hxR
      let xR : R := ⟨x, hxR⟩
      have hxTop : xR ∈ Ccomm ⊔ Cfix := by
        rw [sup_comm, hsup]
        exact Subgroup.mem_top xR
      rcases (Subgroup.mem_sup_of_normal_left.mp hxTop) with ⟨k, hk, c, hc, hkc⟩
      rw [Set.mem_mul]
      refine ⟨(k : H), ?_, (c : H), ?_, ?_⟩
      · rw [← hcommMap]
        exact ⟨k, hk, rfl⟩
      · rw [hfixEq] at hc
        exact hc
      · exact congrArg Subtype.val hkc
    · intro x hx
      rw [Set.mem_mul] at hx
      rcases hx with ⟨k, hk, c, hc, rfl⟩
      have hkR : k ∈ R := by
        rw [← hcommMap] at hk
        exact Subgroup.map_subtype_le Ccomm hk
      exact R.mul_mem hkR hc.1
  haveI : Fintype A := Fintype.ofFinite A
  have hcomm : ∀ x y : R, x * y = y * x := fun x y => hRab.is_comm.comm x y
  letI : CommGroup R := { (inferInstance : Group R) with mul_comm := hcomm }
  have hconj : ∀ a : A, ∀ r ∈ R, (a : H)⁻¹ * r * (a : H) ∈ R := by
    intro a r hr
    have ha := hAR a.2
    exact (Subgroup.mem_set_normalizer_iff''.mp ha r).1 hr
  have hdec := coprime_decomp_gen hR hAR hAodd
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hAodd)
  have hKR : ⁅R, A⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro g hg a ha
    have comm_eq : (⁅g, a⁆ : H) = g * ((a⁻¹)⁻¹ * g⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [comm_eq]
    exact R.mul_mem hg (hconj ⟨a⁻¹, A.inv_mem ha⟩ g⁻¹ (R.inv_mem hg))
  have hsup : ⁅R, A⁆ ⊔ (R ⊓ Subgroup.centralizer (A : Set H)) = R := by
    apply le_antisymm
    · exact sup_le hKR inf_le_left
    · intro x hx
      have hx' : x ∈ (R : Set H) := hx
      rw [hdec] at hx'
      obtain ⟨k, hk, c, hc, rfl⟩ := hx'
      exact Subgroup.mul_mem_sup hk hc
  let φ : A → R → R := fun a x => ⟨(a : H)⁻¹ * x * a, hconj a x x.2⟩
  have hφmul : ∀ a x y, φ a (x * y) = φ a x * φ a y := by
    intro a x y
    apply Subtype.ext
    simp only [φ, Subgroup.coe_mul]
    group
  have hφone : ∀ a, φ a 1 = 1 := by
    intro a
    apply Subtype.ext
    simp [φ]
  have hφcomp : ∀ a b x, φ b (φ a x) = φ (a * b) x := by
    intro a b x
    apply Subtype.ext
    simp only [φ, Subgroup.coe_mul]
    group
  let N : R →* R :=
    { toFun := fun x => ∏ a : A, φ a x
      map_one' := by simp [hφone]
      map_mul' := fun x y => by simp [hφmul, Finset.prod_mul_distrib] }
  have hN : ∀ x : R, N x = ∏ a : A, φ a x := fun x => rfl
  have hNconj : ∀ a x, N (φ a x) = N x := by
    intro a x
    rw [hN, hN]
    simp only [hφcomp]
    exact Equiv.prod_comp (Equiv.mulLeft a) (fun b => φ b x)
  have hNcentral : ∀ x : R, (∀ a : A, (a : H)⁻¹ * (x : H) * a = x) →
      N x = x ^ Nat.card A := by
    intro x hfix
    rw [hN]
    have : ∀ a : A, φ a x = x := fun a => Subtype.ext (hfix a)
    simp [this, Finset.prod_const, Nat.card_eq_fintype_card]
  let L : Subgroup H := (N.ker).map R.subtype
  have hKL : ⁅R, A⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro g hg a ha
    have comm_eq : (⁅g, a⁆ : H) =
        (((⟨g, hg⟩ : R) * (φ (⟨a, ha⟩ : A)⁻¹ ⟨g, hg⟩)⁻¹ : R) : H) := by
      simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [comm_eq]
    refine Subgroup.mem_map.mpr
      ⟨(⟨g, hg⟩ : R) * (φ (⟨a, ha⟩ : A)⁻¹ ⟨g, hg⟩)⁻¹, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hNconj, mul_inv_cancel]
  refine ⟨hsup, ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hxK hxC
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hKL hxK)
    have hxR : x ∈ R := hKR hxK
    let w : R := ⟨x, hxR⟩
    have hzw : z = w := Subtype.ext hzx
    have hNw : N w = 1 := by
      rw [← hzw]
      exact (MonoidHom.mem_ker).mp hz
    have hfix : ∀ a : A, (a : H)⁻¹ * (w : H) * a = w := by
      intro a
      have h1 := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxC |>.2)) a a.2
      show (a : H)⁻¹ * x * a = x
      rw [mul_assoc, ← h1, inv_mul_cancel_left]
    have hpow : w ^ Nat.card A = 1 := by
      rw [← hNcentral w hfix, hNw]
    have hpowR : w ^ Nat.card R = 1 := pow_card_eq_one'
    have hg := (pow_gcd_eq_one (a := w) (m := Nat.card A) (n := Nat.card R)).mpr
      ⟨hpow, hpowR⟩
    rw [hcop.gcd_eq_one, pow_one] at hg
    exact congrArg Subtype.val hg
  · intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hc' : c ∈ R ⊓ Subgroup.centralizer (A : Set H) := hc
    have hkR : k ∈ R := hKR hk
    exact congrArg Subtype.val (hcomm ⟨c, hc'.1⟩ ⟨k, hkR⟩)

end CFSG.GroupTheory.AutomorphismAction
