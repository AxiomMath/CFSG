module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthGen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.T263.DX
open scoped commutatorElement Pointwise

section Ambient

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem sdo_special_data (hp : p.Prime) (hp2 : p ≠ 2) (hK3 : p = 3 → 4 ≤ Nat.card K)
    (hx : OddOrderIsometry Q p x) {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap)
    (hne1 : r ≠ X - 1) :
    specialBlock Q x r = ⊥ ∨ (CFSG.IsQuasisimple ↥(specialBlock Q x r) ∧
      specialBlock Q x r ≤ orthDerived Q ∧ p ∣ Nat.card ↥(specialBlock Q x r)) := by
  haveI : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap r
  · exact Or.inr (specialBlock_quasisimple_le_orthDerived_dvd_card hx hp hp2 hK3 hr hne1 hm)
  · left
    have hpos := hx.primaryMultiplicity_pos hr
    exact hx.specialBlock_eq_bot_of_finrank_eq_one hr (by omega)

theorem sdo_ambient [CharP K 2] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK3 : p = 3 → 4 ≤ Nat.card K) (hx : OddOrderIsometry Q p x)
    (B Y : Subgroup (V ≃ₗ[K] V)) (hB : B ≤ isometryCentralizer Q x ⊓ orthDerived Q)
    (hY : Y ≤ isometryCentralizer Q x ⊓ orthDerived Q) (hBp : ∀ b ∈ B, b ^ p = 1)
    (hY2 : ∀ y ∈ Y, ∃ n : ℕ, y ^ 2 ^ n = 1) (hYB : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (hne : ⁅B, Y⁆ ≠ ⊥) :
    ∃ J : Subgroup (V ≃ₗ[K] V), CFSG.Open.IsComponentOf J (isometryCentralizer Q x ⊓ orthDerived Q) ∧
      J ≤ orthDerived Q ∧ p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅⁅B, Y⁆, J⁆ ≠ ⊥ ∧
      ⁅B, Y⁆ ≤ J ⊔ (isometryCentralizer Q x ⊓ orthDerived Q ⊓
        Subgroup.centralizer (J : Set (V ≃ₗ[K] V))) := by
  classical
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨n, F, hn, hF, hFc, hdec, hinnF⟩ :=
    sdo_fixed_package hQ hp hp2 hK3 hx hRep B Y hB hY hBp
  set C : Subgroup (V ≃ₗ[K] V) := isometryCentralizer Q x ⊓ orthDerived Q with hC
  haveI : Finite {r : K[X] // r ∈ Rep ∧ r ≠ X - 1} :=
    Finite.of_injective (fun r => (⟨r.1, r.2.1⟩ : ↥Rep))
      (fun a b h => Subtype.ext (by simpa using congrArg (fun z : ↥Rep => (z : K[X])) h))
  let J : ({r : K[X] // r ∈ Rep ∧ r ≠ X - 1} ⊕ Fin n) → Subgroup (V ≃ₗ[K] V) :=
    Sum.elim (fun r => specialBlock Q x r.1) F
  have hSFD_C : supportedFixedDerived Q x ≤ C :=
    le_inf supportedFixedDerived_le_isometryCentralizer hx.supportedFixedDerived_le_orthDerived
  have hsp : ∀ r : {r : K[X] // r ∈ Rep ∧ r ≠ X - 1}, specialBlock Q x r.1 = ⊥ ∨
      (CFSG.IsQuasisimple ↥(specialBlock Q x r.1) ∧ specialBlock Q x r.1 ≤ orthDerived Q ∧
        p ∣ Nat.card ↥(specialBlock Q x r.1)) := fun r =>
    sdo_special_data hp hp2 hK3 hx (hRep.1 r.2.1) r.2.2
  have hJC : ∀ i, J i ≤ C := by
    intro i
    rcases i with r | k
    · rcases hsp r with h | h
      · show specialBlock Q x r.1 ≤ C
        rw [h]
        exact bot_le
      · exact le_inf (specialBlock_le_isometryCentralizer _) h.2.1
    · exact ((hF k).2.1).trans hSFD_C
  have hcomm : ∀ i j, i ≠ j → ∀ u ∈ J i, ∀ v ∈ J j, u * v = v * u := by
    intro i j hij u hu v hv
    rcases i with r | k <;> rcases j with s | l
    · have hrs : (⟨r.1, r.2.1⟩ : ↥Rep) ≠ ⟨s.1, s.2.1⟩ := by
        intro h
        apply hij
        have h' : r.1 = s.1 := congrArg (fun z : ↥Rep => (z : K[X])) h
        exact congrArg Sum.inl (Subtype.ext h')
      exact (hx.blocks_commute hRep hrs u v (specialBlock_le_supportedBlock _ hu)
        (specialBlock_le_supportedBlock _ hv)).eq
    · have hn0 : n ≠ 0 := by
        rintro rfl
        exact l.elim0
      have hrX : (⟨r.1, r.2.1⟩ : ↥Rep) ≠ ⟨X - 1, hn hn0⟩ := fun h =>
        r.2.2 (congrArg (fun z : ↥Rep => (z : K[X])) h)
      exact (hx.blocks_commute hRep hrX u v (specialBlock_le_supportedBlock _ hu)
        (supportedFixedDerived_le_supportedBlock ((hF l).2.1 hv))).eq
    · have hn0 : n ≠ 0 := by
        rintro rfl
        exact k.elim0
      have hrX : (⟨X - 1, hn hn0⟩ : ↥Rep) ≠ ⟨s.1, s.2.1⟩ := fun h =>
        s.2.2 (congrArg (fun z : ↥Rep => (z : K[X])) h).symm
      exact (hx.blocks_commute hRep hrX u v (supportedFixedDerived_le_supportedBlock ((hF k).2.1 hu))
        (specialBlock_le_supportedBlock _ hv)).eq
    · exact hFc k l (fun h => hij (by rw [h])) u hu v hv
  have hq : ∀ i, J i = ⊥ ∨ CFSG.Open.IsComponentOf (J i) C := by
    intro i
    rcases i with r | k
    · rcases hsp r with h | h
      · exact Or.inl h
      · refine Or.inr ⟨le_inf (specialBlock_le_isometryCentralizer _) h.2.1, ?_, open_of_native_dx h.1⟩
        have hle : specialBlock Q x r.1 ≤ C := le_inf (specialBlock_le_isometryCentralizer _) h.2.1
        have hnorm : ((specialBlock Q x r.1).subgroupOf C).Normal := by
          rw [Subgroup.normal_subgroupOf_iff hle]
          intro g k hg hk
          exact conj_mem_specialBlock (Subgroup.mem_inf.1 hk).1 hg
        exact CFSG.Open.IsSubnormal.step hle hnorm (CFSG.Open.IsSubnormal.refl C)
    · refine Or.inr ⟨(hJC (Sum.inr k)), ?_, open_of_native_dx (hF k).1⟩
      refine CFSG.Open.IsSubnormal.step ((hF k).2.1) (hF k).2.2.1 (CFSG.Open.IsSubnormal.step hSFD_C ?_ (CFSG.Open.IsSubnormal.refl C))
      rw [Subgroup.normal_subgroupOf_iff hSFD_C]
      intro g k' hg hk'
      exact hx.conj_mem_supportedFixedDerived (Subgroup.mem_inf.1 hk').1 hg
  have hz : ∀ i, ∀ z ∈ J i, (∀ l ∈ J i, z * l = l * z) → ∀ m : ℕ, z ^ 2 ^ m = 1 → z = 1 := by
    intro i
    rcases i with r | k
    · intro z hz hc m hzm
      have hh := hRep.1 r.2.1
      haveI : Fact (Irreducible r.1) := ⟨irreducible_of_mem_primaryFactors hh⟩
      by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap r.1
      · exact sdo_specialBlock_center_two hx hp hp2 hh r.2.2 hm hz hc m hzm
      · have hpos := hx.primaryMultiplicity_pos hh
        have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hh (by omega)
        have hz' : z ∈ (⊥ : Subgroup (V ≃ₗ[K] V)) := by rw [← hbot]; exact hz
        exact Subgroup.mem_bot.1 hz'
    · intro z hz hc m _
      exact (hF k).2.2.2 z hz hc
  have hR : ⁅B, Y⁆ ≤ ⨆ i, J i := by
    rw [Subgroup.commutator_le]
    intro b hb y hy
    obtain ⟨j, hj, f, hf, hbyjf⟩ := hdec b hb y hy
    rw [hbyjf]
    refine Subgroup.mul_mem _ ?_ ?_
    · refine (?_ : specialProduct Q x Rep ≤ ⨆ i, J i) hj
      refine iSup₂_le fun h hh => iSup_le fun hne1 => ?_
      exact le_iSup_of_le (Sum.inl ⟨h, hh, hne1⟩) le_rfl
    · refine (?_ : (⨆ i : Fin n, F i) ≤ ⨆ i, J i) hf
      exact iSup_le fun k => le_iSup_of_le (Sum.inr k) le_rfl
  have hinn : ∀ i, p ∣ Nat.card (↥(J i) ⧸ Subgroup.center ↥(J i)) ∨
      ∀ b ∈ B, ∃ c ∈ J i, ∀ l ∈ J i, b * l * b⁻¹ = c * l * c⁻¹ := by
    intro i
    rcases i with r | k
    · rcases hsp r with h | h
      · refine Or.inr fun b hb => ⟨1, one_mem _, fun l hl => ?_⟩
        have hl' : l ∈ (⊥ : Subgroup (V ≃ₗ[K] V)) := by
          have : l ∈ specialBlock Q x r.1 := hl
          rw [h] at this
          exact this
        rw [Subgroup.mem_bot.1 hl']
        simp
      · exact Or.inl (CFSG.dvd_card_quotient_center_of_quasisimple h.1 hp h.2.2)
    · exact Or.inr (hinnF k)
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := sdo_select_component p hp hp2 J C B Y hJC hcomm hq hz hBp hY2 hYB
    hR hne hinn
  exact ⟨J i, hi1, (hJC i).trans inf_le_right, hi2, hi3, hi4⟩

end Ambient

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
