module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsLinear
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpTorus

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Universal.Spin

section Torus

variable {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
  {Qf : QuadraticForm K (σ → K)}

theorem spinMatrix_not_mem_scalars_of_actsBy (h2 : (2 : K) ≠ 0) {m : ℕ} {F : HypFrame Qf m}
    {x : spinGroup Qf} {s : Fin m → K} (hx : SpinPlusClosed.ActsBy F x s) {i j : Fin m}
    (hi : s i = -1) (hj : s j = 1) : spinMatrix Qf x ∉ StatedScalars σ K := by
  intro h
  rw [mem_statedScalars_iff, toLinEquiv_spinMatrix] at h
  obtain ⟨c, hc⟩ := mem_scalars.mp h
  have hv : ∀ p r, F.vec p r ≠ 0 := fun p r h0 => by
    have := F.polar_vec_not p r
    rw [h0, polar_zero_left] at this
    exact zero_ne_one this
  have h0 := hx i true
  have h1 := hx j true
  rw [hc] at h0 h1
  have hci : c = s i := smul_left_injective K (hv _ _) h0
  have hcj : c = s j := smul_left_injective K (hv _ _) h1
  rw [hi] at hci
  rw [hj, hci] at hcj
  exact h2 (by linear_combination -hcj)

theorem spin_four_group (h2 : (2 : K) ≠ 0) {m : ℕ} (F : HypFrame Qf m) (hm : 3 ≤ m) :
    ∃ a b : spinGroup Qf, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧
      spinMatrix Qf a ∉ StatedScalars σ K ∧ spinMatrix Qf b ∉ StatedScalars σ K ∧
      spinMatrix Qf (a * b) ∉ StatedScalars σ K := by
  set i0 : Fin m := ⟨0, by omega⟩
  set i1 : Fin m := ⟨1, by omega⟩
  set i2 : Fin m := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have ha := SpinPlusClosed.actsBy_longTorus_neg_one F h01
  have hb := SpinPlusClosed.actsBy_longTorus_neg_one F h12
  refine ⟨F.longTorus h01 true true (-1), F.longTorus h12 true true (-1), ?_, ?_,
    (HypFrame.commute_longTorus_longTorus F h01 true true (-1) h12 true true (-1)).eq,
    spinMatrix_not_mem_scalars_of_actsBy h2 ha (i := i0) (j := i2) (by simp)
      (by simp [h02.symm, h12.symm]),
    spinMatrix_not_mem_scalars_of_actsBy h2 hb (i := i1) (j := i0) (by simp)
      (by simp [h01, h02]),
    spinMatrix_not_mem_scalars_of_actsBy h2 (ha.mul hb) (i := i0) (j := i1)
      (by simp [h01, h02]) (by simp [h01.symm])⟩
  · rw [← map_mul, neg_one_mul, neg_neg, map_one]
  · rw [← map_mul, neg_one_mul, neg_neg, map_one]

end Torus

section Covers

variable {Q : Type} [Group Q] [Finite Q]

theorem three_le_pRank_of_spin (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) {Qf : QuadraticForm K (σ → K)} [Finite (spinGroup Qf)]
    {Q₀ : (σ → K) → K} (hR : (spinMatrix Qf).range = StatedOmega Q₀) {m : ℕ}
    (F : HypFrame Qf m) (hm : 3 ≤ m)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* spinGroup Qf),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : spinGroup Qf →* E, ∀ x, π (s x) = x)
    (e : Q ⧸ center Q ≃* StatedProj (StatedOmega Q₀)) : 3 ≤ CFSG.pRank 2 Q := by
  set πQ := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπQ
  have hπQs : Function.Surjective πQ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerQ := ker_quotientMap e
  have h2Q : IsPGroup 2 πQ.ker := hkerQ ▸ isPGroup_center_of_pPrimeCore_eq_bot hO
  set πG := spinToStatedProj Qf hR with hπG
  have hπG1 : ∀ x, πG x = 1 ↔ spinMatrix Qf x ∈ StatedScalars σ K := fun x => by
    rw [← MonoidHom.mem_ker, hπG, ker_spinToStatedProj, Subgroup.mem_comap]
  obtain ⟨s, hs⟩ := hsplit _ (pullbackFst πG πQ) (pullbackFst_surjective hπQs)
    (pullbackFst_ker_le_center hkerQ.le) (isPGroup_pullbackFst_ker h2Q)
  obtain ⟨τ, hτ⟩ := exists_lift_of_section hs
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hab1⟩ := spin_four_group h2 F hm
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  exact three_le_pRank_of_four_group hτ ha hb hab (by rwa [Ne, hπG1]) (by rwa [Ne, hπG1])
    (by rwa [Ne, hπG1]) hzZ hzz hz1 (by rw [← MonoidHom.mem_ker, hkerQ]; exact hzZ)

theorem three_le_pRank_of_POmegaOdd (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (e : Q ⧸ center Q ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    3 ≤ CFSG.pRank 2 Q := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  exact three_le_pRank_of_spin hO hzZ hz2 h2 (range_spinMatrix_quadOdd h2 hn)
    (oddFrame n K).toHypFrame hn
    (fun E _ _ π hπ hker hE => (LieType.Steinberg.spinOdd_central_two_extension_splitting hn hK
      hπ hker hE).imp fun _ h => h.1) e

theorem three_le_pRank_of_POmegaPlus (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (e : Q ⧸ center Q ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    3 ≤ CFSG.pRank 2 Q := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  exact three_le_pRank_of_spin hO hzZ hz2 h2 (range_spinMatrix_quadPlus hn) (plusFrame n K hn) hn
    (fun E _ _ π hπ hker hE => (LieType.Steinberg.spinPlus_central_two_extension_splitting hn hK
      hπ hker hE).imp fun _ h => h.1) e

theorem three_le_pRank_of_POmegaMinus (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : Q ⧸ center Q ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    3 ≤ CFSG.pRank 2 Q := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Finite (spinGroup (quadMinus n K b c)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact three_le_pRank_of_spin hO hzZ hz2 h2 (range_spinMatrix_quadMinus hn hirr)
    (Twisted.minusFrame n b c).toHypFrame (by omega)
    (fun E _ _ π hπ hker hE => (LieType.Steinberg.spinMinus_central_two_extension_splitting hn hK
      hirr hπ hker hE).imp fun _ h => h.1) e

end Covers

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
