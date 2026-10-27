module

public import CFSG.Assembly.OddCoreSpan
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type*} [Group G]

@[expose] def OddCoreSpanCompleted (A : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (oddCoreSpan A : Set G) ∧
  Odd (Nat.card (oddCoreSpan A)) ∧
  ∀ a ∈ A, a ≠ 1 →
    oddCoreSpan A ⊓ Subgroup.centralizer ({a} : Set G) = involutionOddCore a

private theorem not_isCyclic_of_elementary_two (B : Subgroup G)
    (hB : IsElemAbelian 2 B) (hcard : 4 ≤ Nat.card B) : ¬ IsCyclic B := by
  intro hcyc
  let : IsCyclic B := hcyc
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := B)
  have hbpow : b ^ 2 = 1 := Subtype.ext (hB.2 b.val b.property)
  have hdvd : Nat.card B ∣ 2 := hb ▸ orderOf_dvd_of_pow_eq_one hbpow
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  omega

theorem oddCoreSpan_eq_of_completed (A B : Subgroup G) (hA : IsElemAbelian 2 A)
    (hcardA : 8 ≤ Nat.card A) (hcomplete : OddCoreSpanCompleted A)
    (hBA : B ≤ A) (hcardB : 4 ≤ Nat.card B) : oddCoreSpan B = oddCoreSpan A := by
  let : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let : Finite B := Finite.of_injective (Subgroup.inclusion hBA)
    (Subgroup.inclusion_injective hBA)
  have hB : IsElemAbelian 2 B := by
    constructor
    · let : IsMulCommutative A := hA.1
      let : CommGroup A := IsMulCommutative.instCommGroup
      exact ⟨⟨fun x y => Subtype.ext (congrArg (fun a : A => a.val)
        (mul_comm (⟨x, hBA x.property⟩ : A) (⟨y, hBA y.property⟩ : A)))⟩⟩
    · intro b hb
      exact hA.2 b (hBA hb)
  let : IsMulCommutative B := hB.1
  let : CommGroup B := IsMulCommutative.instCommGroup
  have hP : IsPGroup 2 B := by
    intro b
    exact ⟨1, by simpa only [pow_one] using Subtype.ext (hB.2 b.val b.property)⟩
  let : Fact (IsPGroup 2 B) := ⟨hP⟩
  let R := oddCoreSpan A
  let : Finite R := Nat.finite_of_card_ne_zero (by
    intro hzero
    have hodd := hcomplete.2.1
    rw [show Nat.card (oddCoreSpan A) = 0 from hzero] at hodd
    exact (by decide : ¬ Odd 0) hodd)
  have hBR : B ≤ Subgroup.normalizer (R : Set G) := hBA.trans hcomplete.1
  let : MulDistribMulAction B R :=
    MulDistribMulAction.compHom R (Subgroup.inclusion hBR)
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := R) (A := B) 2
    (by simpa only [Nat.coprime_two_left] using hcomplete.2.1)
    (not_isCyclic_of_elementary_two B hB hcardB)
  have hfixed (b : B) :
      (CFSG.fixedPointSubgroup (Subgroup.zpowers b) R).map R.subtype =
        R ⊓ Subgroup.centralizer ({b.val} : Set G) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      change ∀ c : Subgroup.zpowers b, c • r = r at hr
      have hbfix := hr
        (⟨b, Subgroup.mem_zpowers b⟩ : Subgroup.zpowers b)
      have hc : b.val * r.val * b.val⁻¹ = r.val := congrArg Subtype.val hbfix
      have heq := congrArg (fun y : G => y * b.val) hc
      simpa only [Subgroup.subtype_apply, mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    · rintro ⟨hxR, hxb⟩
      refine ⟨⟨x, hxR⟩, ?_, rfl⟩
      change ∀ c : Subgroup.zpowers b, c • (⟨x, hxR⟩ : R) = ⟨x, hxR⟩
      intro c
      apply Subtype.ext
      change c.val.val * x * c.val.val⁻¹ = x
      have hbc : Subgroup.zpowers b.val ≤ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hxb).symm)
      have hc : c.val.val ∈ Subgroup.zpowers b.val := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp c.property
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hbc hc)
      rw [hcomm]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
  apply le_antisymm (oddCoreSpan_mono hBA)
  have htop : (⊤ : Subgroup R).map R.subtype = R := by
    ext x
    simp
  calc
    R = (⊤ : Subgroup R).map R.subtype := htop.symm
    _ = (⨆ (b : B) (_ : b ≠ 1),
        CFSG.fixedPointSubgroup (Subgroup.zpowers b) R).map R.subtype := by rw [hgen]
    _ = ⨆ (b : B) (_ : b ≠ 1), R ⊓ Subgroup.centralizer ({b.val} : Set G) := by
      simp only [Subgroup.map_iSup, hfixed]
    _ ≤ oddCoreSpan B := by
      refine iSup_le fun b => iSup_le fun hne => ?_
      have hbne : b.val ≠ 1 := fun h => hne (Subtype.ext h)
      rw [hcomplete.2.2 b.val (hBA b.property) hbne]
      exact involutionOddCore_le_span B b.property hbne

end CFSG.Assembly.Dichotomy
