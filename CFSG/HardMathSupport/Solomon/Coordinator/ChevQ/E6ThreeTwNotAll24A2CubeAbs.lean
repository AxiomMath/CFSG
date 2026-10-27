module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.LieType.Seitz CFSG.ComponentClassification

theorem mulAut_mul_conj_mul_inv {X : Type} [Group X] (φ : MulAut X) (s : X) :
    φ * (MulAut.conj s : MulAut X) * φ⁻¹ = MulAut.conj (φ s) := by
  ext x
  simp [MulAut.conj_apply]

theorem exists_mem_component_conj_mem {X : Type} [Group X] {E : Subgroup (MulAut X)}
    (hE : IsElemAbelian 3 E)
    (hEI : Nat.card ↥(E ⊓ OuterAutomorphisms.inner X) = 3 ^ 2)
    (hZ : ∀ s : X, (MulAut.conj s : MulAut X) = 1 → s = 1)
    {f : MulAut X} (hf : f ∈ E) {J : Subgroup X}
    (hidx : J.relIndex (fixedPoints (Subgroup.zpowers f)) ∣ 3) :
    ∃ s ∈ J, s ≠ 1 ∧ s ^ 3 = 1 ∧ (MulAut.conj s : MulAut X) ∈ E := by
  classical
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    exact hZ
  set P : Subgroup X := E.comap (MulAut.conj : X →* MulAut X) with hP
  have hPcard : Nat.card P = 3 ^ 2 := by
    rw [← hEI]
    have h1 : P.map (MulAut.conj : X →* MulAut X) = E ⊓ OuterAutomorphisms.inner X := by
      rw [hP, Subgroup.map_comap_eq, inf_comm]
      rfl
    rw [← h1]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective P (MulAut.conj : X →* MulAut X) hinj).toEquiv
  have hPE : ∀ s ∈ P, (MulAut.conj s : MulAut X) ∈ E := fun s hs => hs
  have hP3 : ∀ s ∈ P, s ^ 3 = 1 := by
    intro s hs
    apply hinj
    rw [map_pow, hE.2 _ (hPE s hs), map_one]
  have hPC : P ≤ fixedPoints (Subgroup.zpowers f) := by
    intro s hs
    have hcomm : f * MulAut.conj s = MulAut.conj s * f :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ ⟨_, hPE s hs⟩)
    have hfs : f s = s := by
      apply hinj
      rw [← mulAut_mul_conj_mul_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hstab : Subgroup.zpowers f ≤ MulAction.stabilizer (MulAut X) s :=
      Subgroup.zpowers_le.2 hfs
    intro φ hφ
    exact hstab hφ
  have hne : J.relIndex (fixedPoints (Subgroup.zpowers f)) ≠ 0 :=
    ne_zero_of_dvd_ne_zero (by norm_num) hidx
  have hrel : J.relIndex P ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hPC hne).trans (Nat.le_of_dvd (by norm_num) hidx)
  have hmul := Subgroup.relIndex_mul_card (H := J) (K := P)
  rw [hPcard] at hmul
  have hgt : 1 < Nat.card ↥(J ⊓ P) := by
    by_contra hle
    push Not at hle
    have : J.relIndex P * Nat.card ↥(J ⊓ P) ≤ 3 * 1 := Nat.mul_le_mul hrel hle
    omega
  have hbot : J ⊓ P ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hgt
    omega
  obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  exact ⟨s, (Subgroup.mem_inf.1 hs).1, hs1', hP3 s (Subgroup.mem_inf.1 hs).2,
    hPE s (Subgroup.mem_inf.1 hs).2⟩

theorem lineGen_of_cube_abstract {X : Type} [Group X] {E : Subgroup (MulAut X)}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hEI : Nat.card ↥(E ⊓ OuterAutomorphisms.inner X) = 3 ^ 2)
    (hZ : ∀ s : X, (MulAut.conj s : MulAut X) = 1 → s = 1)
    {f : MulAut X} (hf : f ∈ E) (hf1 : f ≠ 1) (hfo : f ∉ OuterAutomorphisms.inner X)
    {J : Subgroup X} (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers f)))
    (hidx : J.relIndex (fixedPoints (Subgroup.zpowers f)) ∣ 3)
    (hnorm : ∀ c ∈ fixedPoints (Subgroup.zpowers f), ∀ x ∈ J, c * x * c⁻¹ ∈ J)
    (hLA : ∀ y ∈ fixedPoints (Subgroup.zpowers f), y ^ 3 ∈ J → ∀ p ∈ J, p ^ 3 = 1 →
      ∃ j ∈ J, y * p * y⁻¹ = j * p * j⁻¹) :
    fixedPoints (Subgroup.zpowers f) ≤
      sSup {J | IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
        ⨆ (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F := by
  classical
  have hJle : J ≤ sSup {J | IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
      ⨆ (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F :=
    (le_sSup (show J ∈ {J | IsComponentOf J (fixedPoints (Subgroup.zpowers f))} from hJ)).trans
      le_sup_left
  by_cases hCJ : fixedPoints (Subgroup.zpowers f) ≤ J
  · exact hCJ.trans hJle
  obtain ⟨y₀, hy₀C, hy₀J⟩ := SetLike.not_le_iff_exists.1 hCJ
  have hidx3 : J.relIndex (fixedPoints (Subgroup.zpowers f)) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hidx with h | h
    · exact absurd (Subgroup.relIndex_eq_one.1 h) hCJ
    · exact h
  have hy₀3 : y₀ ^ 3 ∈ J := by
    haveI : (J.subgroupOf (fixedPoints (Subgroup.zpowers f))).Normal :=
      ⟨fun n hn g => hnorm g g.2 n hn⟩
    have h := Subgroup.pow_index_mem (J.subgroupOf (fixedPoints (Subgroup.zpowers f)))
      (⟨y₀, hy₀C⟩ : fixedPoints (Subgroup.zpowers f))
    have hix : (J.subgroupOf (fixedPoints (Subgroup.zpowers f))).index = 3 := hidx3
    rw [hix] at h
    exact h
  obtain ⟨s, hsJ, hs1, hs3, hsE⟩ := exists_mem_component_conj_mem hE hEI hZ hf hidx
  obtain ⟨j, hjJ, hj⟩ := hLA y₀ hy₀C hy₀3 s hsJ hs3
  have hjC : j ∈ fixedPoints (Subgroup.zpowers f) := hJ.1 hjJ
  set y₁ : X := j⁻¹ * y₀ with hy₁
  have hy₁C : y₁ ∈ fixedPoints (Subgroup.zpowers f) :=
    (fixedPoints (Subgroup.zpowers f)).mul_mem ((fixedPoints (Subgroup.zpowers f)).inv_mem hjC)
      hy₀C
  have hy₁J : y₁ ∉ J := fun h => hy₀J (by simpa [hy₁] using J.mul_mem hjJ h)
  have hy₁s : y₁ * s * y₁⁻¹ = s := by
    have : y₀ * s * y₀⁻¹ = j * s * j⁻¹ := hj
    calc y₁ * s * y₁⁻¹ = j⁻¹ * (y₀ * s * y₀⁻¹) * j := by simp [hy₁, mul_assoc]
      _ = s := by rw [this]; simp [mul_assoc]
  have hcs1 : (MulAut.conj s : MulAut X) ≠ 1 := fun h => hs1 (hZ s h)
  have hf3 : f ^ 3 = 1 := hE.2 f hf
  have hc3 : (MulAut.conj s : MulAut X) ^ 3 = 1 := hE.2 _ hsE
  have hcomm : Commute f (MulAut.conj s : MulAut X) :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ ⟨_, hsE⟩)
  have hnot : (MulAut.conj s : MulAut X) ∉ Subgroup.zpowers f := by
    intro hmem
    rcases eq_or_eq_inv_of_mem_zpowers hf3 hf1 hmem hcs1 with h | h
    · exact hfo ⟨s, h⟩
    · refine hfo ⟨s⁻¹, ?_⟩
      rw [map_inv, h, inv_inv]
  have hFE : Subgroup.zpowers f ⊔ Subgroup.zpowers (MulAut.conj s : MulAut X) ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hf) (Subgroup.zpowers_le.2 hsE)
  have hFc : Nat.card ↥(Subgroup.zpowers f ⊔ Subgroup.zpowers (MulAut.conj s : MulAut X)) =
      3 ^ 2 := card_zpowers_sup_zpowers hcomm hf1 hf3 hc3 hnot
  have hFi : (Subgroup.zpowers f ⊔ Subgroup.zpowers (MulAut.conj s : MulAut X)).relIndex E = 3 :=
    relIndex_eq_three hFE hEc hFc
  have hy₁F : y₁ ∈ fixedPoints
      (Subgroup.zpowers f ⊔ Subgroup.zpowers (MulAut.conj s : MulAut X)) := by
    have hstab : Subgroup.zpowers f ⊔ Subgroup.zpowers (MulAut.conj s : MulAut X) ≤
        MulAction.stabilizer (MulAut X) y₁ := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · exact hy₁C f (Subgroup.mem_zpowers f)
      · show (MulAut.conj s : MulAut X) y₁ = y₁
        rw [MulAut.conj_apply]
        rw [← mul_inv_eq_iff_eq_mul.1 hy₁s, mul_inv_cancel_right]
    intro φ hφ
    exact hstab hφ
  have hyle : y₁ ∈ sSup {J | IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
      ⨆ (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F := by
    refine le_sup_right (a := sSup {J | IsComponentOf J (fixedPoints (Subgroup.zpowers f))}) ?_
    exact (le_iSup₂ (f := fun (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F) =>
      fixedPoints F) (Subgroup.zpowers f ⊔ Subgroup.zpowers (MulAut.conj s : MulAut X))
        ⟨hFE, hFi, Subgroup.mem_sup_left (Subgroup.mem_zpowers f)⟩) hy₁F
  exact lineGen_of_index_prime Nat.prime_three hJ.1 hidx3 hJle ⟨y₁, hyle, hy₁J⟩

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
