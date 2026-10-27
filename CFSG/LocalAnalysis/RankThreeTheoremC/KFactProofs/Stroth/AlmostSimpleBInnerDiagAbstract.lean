module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem oddPCoreInClosure_centralizer_mk_of_dichotomy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Z : Subgroup X) [Z.Normal] (hZc : Z ≤ Subgroup.center X) (hZp : ∀ z ∈ Z, z ^ p = 1) (a : X)
    (hC : OddPCoreInClosure p ↥(Subgroup.centralizer ({a} : Set X)))
    (hD : (∃ g : X, (g : X ⧸ Z) ∈ Subgroup.centralizer ({(a : X ⧸ Z)} : Set (X ⧸ Z)) ∧
        g * a ≠ a * g) → ∀ t : X, t ^ 2 = 1 → t * a = a * t → t = 1) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({(a : X ⧸ Z)} : Set (X ⧸ Z))) := by
  set N : Subgroup X :=
    (Subgroup.centralizer ({(a : X ⧸ Z)} : Set (X ⧸ Z))).comap (QuotientGroup.mk' Z) with hN
  have hmemN : ∀ g : X, g ∈ N ↔ (g : X ⧸ Z) ∈ Subgroup.centralizer ({(a : X ⧸ Z)} : Set (X ⧸ Z)) :=
    fun g => Iff.rfl
  have hNoc : OddPCoreInClosure p ↥N := by
    by_cases hex : ∃ g : X, g ∈ N ∧ g * a ≠ a * g
    ·
      refine OddPCoreInClosure.of_odd_core fun K _ _ => ?_
      refine odd_natCard_of_forall_sq fun x hx2 => ?_
      obtain ⟨t, ht⟩ : ∃ t : X, t = (((x : ↥K) : ↥N) : X) := ⟨_, rfl⟩
      have htN : t ∈ N := ht ▸ ((x : ↥K) : ↥N).2
      have ht2 : t ^ 2 = 1 := by
        have h1 : (x : ↥K) ^ 2 = 1 := hx2
        have h2 := congrArg (fun y : ↥K => ((y : ↥N) : X)) h1
        rw [ht]
        simpa using h2
      have hz : t * a * t⁻¹ * a⁻¹ ∈ Z := by
        have h1 : (t : X ⧸ Z) * (a : X ⧸ Z) = (a : X ⧸ Z) * (t : X ⧸ Z) :=
          Subgroup.mem_centralizer_singleton_iff.1 ((hmemN t).1 htN)
        rw [← QuotientGroup.eq_one_iff]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [h1]
        simp
      obtain ⟨z, hzdef⟩ : ∃ z : X, z = t * a * t⁻¹ * a⁻¹ := ⟨_, rfl⟩
      rw [← hzdef] at hz
      have hzc : ∀ y : X, y * z = z * y := fun y => (Subgroup.mem_center_iff.1 (hZc hz) y)
      have hta : t * a * t⁻¹ = z * a := by
        rw [hzdef]
        simp
      have hz2 : z ^ 2 = 1 := by
        have h1 : t ^ 2 * a * (t ^ 2)⁻¹ = a := by
          rw [ht2, inv_one, one_mul, mul_one]
        have h2 : t ^ 2 * a * (t ^ 2)⁻¹ = z ^ 2 * a := by
          have e1 : t ^ 2 * a * (t ^ 2)⁻¹ = t * (t * a * t⁻¹) * t⁻¹ := by
            rw [pow_two, mul_inv_rev]
            simp only [mul_assoc]
          have e2 : t * z * t⁻¹ = z := by
            rw [hzc t, mul_assoc, mul_inv_cancel, mul_one]
          rw [e1, hta]
          calc t * (z * a) * t⁻¹ = (t * z * t⁻¹) * (t * a * t⁻¹) := by
                simp only [mul_assoc, inv_mul_cancel_left]
            _ = z * (z * a) := by rw [e2, hta]
            _ = z ^ 2 * a := by rw [pow_two, mul_assoc]
        have h3 : z ^ 2 * a = a := h2.symm.trans h1
        exact mul_right_cancel (h3.trans (one_mul a).symm)
      have hz1 : z = 1 := by
        have hzp : z ^ p = 1 := hZp z hz
        have hd2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
        have hdp : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
        have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
        exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd2 hdp))
      have hcomm : t * a = a * t := by
        have : t * a * t⁻¹ = a := by rw [hta, hz1, one_mul]
        calc t * a = t * a * t⁻¹ * t := by simp only [mul_assoc, inv_mul_cancel, mul_one]
          _ = a * t := by rw [this]
      have ht1 : t = 1 := hD hex t ht2 hcomm
      apply Subtype.ext
      apply Subtype.ext
      exact ht.symm.trans ht1
    ·
      push Not at hex
      have heq : Subgroup.centralizer ({a} : Set X) = N := by
        ext g
        constructor
        · intro hg
          have hg' : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 hg
          rw [hmemN]
          refine Subgroup.mem_centralizer_singleton_iff.2 ?_
          change (g : X ⧸ Z) * (a : X ⧸ Z) = (a : X ⧸ Z) * (g : X ⧸ Z)
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hg']
        · intro hg
          exact Subgroup.mem_centralizer_singleton_iff.2 (hex g hg)
      exact OddPCoreInClosure.of_mulEquiv (MulEquiv.subgroupCongr heq) hC
  let φ : ↥N →* ↥(Subgroup.centralizer ({(a : X ⧸ Z)} : Set (X ⧸ Z))) :=
    ((QuotientGroup.mk' Z).comp N.subtype).codRestrict _ (fun g => g.2)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (y : X ⧸ Z)
    have hgN : g ∈ N := by
      rw [hmemN, hg]
      exact y.2
    exact ⟨⟨g, hgN⟩, Subtype.ext hg⟩
  have hker : φ.ker ≤ Subgroup.center ↥N := by
    intro g hg
    have h1 : ((g : X) : X ⧸ Z) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hg)
    have hs : (g : X) ∈ Z := (QuotientGroup.eq_one_iff (g : X)).1 h1
    rw [Subgroup.mem_center_iff]
    intro h'
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZc hs) h'.1)
  exact OddPCoreInClosure.of_surjective_ker_le_center hp φ hsurj hker hNoc

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
