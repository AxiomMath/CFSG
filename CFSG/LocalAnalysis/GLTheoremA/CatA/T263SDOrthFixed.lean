module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.F106.OddRadOrth
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q
open scoped commutatorElement Pointwise

section FixedPart

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem sdo_fixedPart (hx : OddOrderIsometry Q p x) {b : V ≃ₗ[K] V} (hb : b ∈ isometryCentralizer Q x) :
    ∃ (f : V ≃ₗ[K] V) (hf : f ∈ supportedBlock Q x (X - 1)),
      restrictFixed Q x ⟨f, hf⟩ = isometryRestrictFixed Q x ⟨b, hb⟩ ∧
      ∀ l ∈ supportedBlock Q x (X - 1), b * f⁻¹ * l = l * (b * f⁻¹) := by
  obtain ⟨g, hg⟩ := restrictFixed_surjective hx (isometryRestrictFixed Q x ⟨b, hb⟩)
    (isometryRestrictFixed_mem_orthogonalGroup _)
  refine ⟨g.1, g.2, hg, fun l hl => ?_⟩
  have hbc : b ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hb).2
  have hgM : g.1 ∈ isometryCentralizer Q x := supportedBlock_le_isometryCentralizer _ g.2
  have hgc : g.1 ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hgM).2
  have hlM : l ∈ isometryCentralizer Q x := supportedBlock_le_isometryCentralizer _ hl
  have hlc : l ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hlM).2
  have hfw : ∀ w ∈ fixedSpace x, g.1 w = b w := by
    intro w hw
    have := congrArg (fun φ : fixedSpace x ≃ₗ[K] fixedSpace x => (φ ⟨w, hw⟩ : V)) hg
    simpa [coe_restrictFixed, coe_isometryRestrictFixed] using this
  have hgr : ∀ r ∈ othersSpace x.toLinearMap (X - 1), g.1 r = r := fun r hr =>
    (mem_supportedBlock.mp g.2).2 r hr
  have hlr : ∀ r ∈ othersSpace x.toLinearMap (X - 1), l r = r := fun r hr =>
    (mem_supportedBlock.mp hl).2 r hr
  have hW : ∀ {c : V ≃ₗ[K] V}, c ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) →
      ∀ w ∈ fixedSpace x, c w ∈ fixedSpace x := fun hc w hw => mem_fixedSpace_of_apply hc hw
  have hR : ∀ {c : V ≃ₗ[K] V}, c ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) →
      ∀ r ∈ othersSpace x.toLinearMap (X - 1), c r ∈ othersSpace x.toLinearMap (X - 1) :=
    fun hc r hr => mem_othersSpace_of_apply hc hr
  have hginv : g.1⁻¹ ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := inv_mem hgc
  have hginvr : ∀ r ∈ othersSpace x.toLinearMap (X - 1), g.1⁻¹ r = r := by
    intro r hr
    show g.1.symm r = r
    rw [LinearEquiv.symm_apply_eq]
    exact (hgr r hr).symm
  have hbginv : ∀ w ∈ fixedSpace x, b (g.1⁻¹ w) = w := by
    intro w hw
    have h1 : g.1⁻¹ w ∈ fixedSpace x := hW hginv w hw
    rw [← hfw _ h1]
    show g.1 (g.1.symm w) = w
    exact g.1.apply_symm_apply w
  obtain ⟨hc, -⟩ := hx.fixed_others
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
  have hlw : l w ∈ fixedSpace x := hW hlc w hw
  have hbr : b r ∈ othersSpace x.toLinearMap (X - 1) := hR hbc r hr
  show b (g.1⁻¹ (l (w + r))) = l (b (g.1⁻¹ (w + r)))
  have e1 : b (g.1⁻¹ (l (w + r))) = l w + b r := by
    rw [map_add l, hlr r hr, map_add g.1⁻¹, hginvr r hr, map_add b, hbginv _ hlw]
  have e2 : l (b (g.1⁻¹ (w + r))) = l w + b r := by
    rw [map_add g.1⁻¹, hginvr r hr, map_add b, hbginv _ hw, map_add l, hlr _ hbr]
  exact e1.trans e2.symm

theorem sdo_fixedPart_pow (hx : OddOrderIsometry Q p x) {b : V ≃ₗ[K] V}
    (hb : b ∈ isometryCentralizer Q x) {f : V ≃ₗ[K] V} (hf : f ∈ supportedBlock Q x (X - 1))
    (hfb : restrictFixed Q x ⟨f, hf⟩ = isometryRestrictFixed Q x ⟨b, hb⟩) (hbp : b ^ p = 1) :
    f ^ p = 1 := by
  have h1 : restrictFixed Q x ⟨f, hf⟩ ^ p = 1 := by
    rw [hfb, ← map_pow]
    have : (⟨b, hb⟩ : ↥(isometryCentralizer Q x)) ^ p = 1 := Subtype.ext hbp
    rw [this, map_one]
  have h2 : (⟨f, hf⟩ : ↥(supportedBlock Q x (X - 1))) ^ p = 1 :=
    restrictFixed_injective hx (by rw [map_pow, h1, map_one])
  exact congrArg Subtype.val h2

theorem sdo_fixedPart_mem [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2) (hK3 : p = 3 → 4 ≤ Nat.card K)
    (hx : OddOrderIsometry Q p x) (hW3 : 3 ≤ finrank K (fixedSpace x))
    (hq : ∀ g ∈ supportedBlock Q x (X - 1), ∀ q : ℕ, q.Prime → 3 < q → g ^ q = 1 →
      g ∈ supportedFixedDerived Q x)
    {f : V ≃ₗ[K] V} (hf : f ∈ supportedBlock Q x (X - 1)) (hfp : f ^ p = 1) :
    f ∈ supportedFixedDerived Q x := by
  have hp3 : p = 3 ∨ 3 < p := by
    have := hp.two_le
    omega
  rcases hp3 with h3 | h3
  · have hδ : dicksonHom (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate
        ⟨restrictFixed Q x ⟨f, hf⟩, restrictFixed_mem_orthogonalGroup _⟩ = 1 := by
      refine dicksonHom_eq_one_of_pow_eq_one hx.polarBilin_fixed_nondegenerate
        (hp.odd_of_ne_two hp2) (n := p) ?_
      refine Subtype.ext ?_
      show (restrictFixed Q x ⟨f, hf⟩) ^ p = 1
      rw [← map_pow]
      have : (⟨f, hf⟩ : ↥(supportedBlock Q x (X - 1))) ^ p = 1 := Subtype.ext hfp
      rw [this, map_one]
    exact mem_supportedFixedDerived.mpr ⟨hf,
      dicksonDerived_fixedSpace_of_four_le_card (hK3 h3) hx hW3 _ hδ⟩
  · exact hq f hf p hp h3 hfp

theorem sdo_X_sub_one_mem_rep (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (h1 : 1 ≤ finrank K (fixedSpace x)) :
    (X - 1 : K[X]) ∈ Rep := by
  have hmem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hnot
    have := fixedSpace_eq_bot_of_not_mem hnot
    rw [this, finrank_bot] at h1
    omega
  obtain ⟨r, ⟨hr, hXr⟩, -⟩ := hRep.2 _ hmem
  rcases hXr with h | h
  · rw [h]
    exact hr
  · have h2 := hx.reciprocal_reciprocal_eq (hRep.1 hr)
    rw [← h, reciprocalPolynomial_X_sub_one] at h2
    rw [h2]
    exact hr

theorem sdo_fixed_package [CharP K 2] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK3 : p = 3 → 4 ≤ Nat.card K) (hx : OddOrderIsometry Q p x)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    (B Y : Subgroup (V ≃ₗ[K] V)) (hB : B ≤ isometryCentralizer Q x ⊓ orthDerived Q)
    (hY : Y ≤ isometryCentralizer Q x ⊓ orthDerived Q) (hBp : ∀ b ∈ B, b ^ p = 1) :
    ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)),
      (n ≠ 0 → (X - 1 : K[X]) ∈ Rep) ∧
      (∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
        ((F i).subgroupOf (supportedFixedDerived Q x)).Normal ∧
        ∀ z ∈ F i, (∀ f ∈ F i, z * f = f * z) → z = 1) ∧
      (∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u) ∧
      (∀ b ∈ B, ∀ y ∈ Y, ∃ j ∈ specialProduct Q x Rep, ∃ f ∈ ⨆ i, F i, ⁅b, y⁆ = j * f) ∧
      (∀ i, ∀ b ∈ B, ∃ c ∈ F i, ∀ l ∈ F i, b * l * b⁻¹ = c * l * c⁻¹) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hBM : ∀ b ∈ B, b ∈ isometryCentralizer Q x := fun b hb => (Subgroup.mem_inf.mp (hB hb)).1
  have hBΩ : ∀ b ∈ B, b ∈ orthDerived Q := fun b hb => (Subgroup.mem_inf.mp (hB hb)).2
  have hYM : ∀ y ∈ Y, y ∈ isometryCentralizer Q x := fun y hy => (Subgroup.mem_inf.mp (hY hy)).1
  have hYΩ : ∀ y ∈ Y, y ∈ orthDerived Q := fun y hy => (Subgroup.mem_inf.mp (hY hy)).2
  have hcm : ∀ b ∈ B, ∀ y ∈ Y,
      ⁅b, y⁆ ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ := fun b hb y hy =>
    Subgroup.commutator_mem_commutator (hBM b hb) (hYM y hy)
  by_cases hlist : 3 ≤ finrank K (fixedSpace x) ∧
      ¬ SmallFixedException (Q.comp (fixedSpace x).subtype)
  ·
    have hcov := (orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate hlist.1).2 hlist.2
    obtain ⟨n, F, -, -, hsup, hF, hcomm, hq⟩ := hx.exists_supported_factors hcov
    refine ⟨n, F, fun _ => sdo_X_sub_one_mem_rep hx hRep (by omega), fun i => ⟨(hF i).1, (hF i).2.1,
      (hF i).2.2, fun z hz hc => fixedFactor_center_eq_one hx hQ hlist.1 hlist.2 hsup hcomm i hz hc⟩,
      hcomm, fun b hb y hy => ?_, fun i b hb => ?_⟩
    · obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep (hcm b hb y hy)
      exact ⟨j, hj, f, by rw [hsup]; exact hf, hgjf⟩
    · obtain ⟨f, hf, hfres, hfc⟩ := sdo_fixedPart hx (hBM b hb)
      have hfp := sdo_fixedPart_pow hx (hBM b hb) hf hfres (hBp b hb)
      have hfΩ := sdo_fixedPart_mem hp hp2 hK3 hx hlist.1 hq hf hfp
      have hfsup : f ∈ ⨆ i, F i := by rw [hsup]; exact hfΩ
      obtain ⟨c, hc, c', hc', hfcc⟩ := sdo_mem_iSup_split F hcomm i hfsup
      refine ⟨c, hc, fun l hl => ?_⟩
      have hlB : l ∈ supportedBlock Q x (X - 1) :=
        supportedFixedDerived_le_supportedBlock ((hF i).2.1 hl)
      have hfl : f * l * f⁻¹ ∈ supportedBlock Q x (X - 1) :=
        mul_mem (mul_mem hf hlB) (inv_mem hf)
      have hcomm' : (b * f⁻¹) * (f * l * f⁻¹) = (f * l * f⁻¹) * (b * f⁻¹) := hfc _ hfl
      have e1 : b * l * b⁻¹ = f * l * f⁻¹ := by
        calc b * l * b⁻¹ = (b * f⁻¹) * (f * l * f⁻¹) * (b * f⁻¹)⁻¹ := by group
          _ = f * l * f⁻¹ := by rw [hcomm']; group
      have hcl' : l * c' = c' * l := Subgroup.mem_centralizer_iff.1 hc' l hl
      have e3 : c' * l * c'⁻¹ = l := by rw [← hcl']; group
      have e2 : f * l * f⁻¹ = c * l * c⁻¹ := by
        rw [hfcc]
        calc c * c' * l * (c * c')⁻¹ = c * (c' * l * c'⁻¹) * c⁻¹ := by group
          _ = c * l * c⁻¹ := by rw [e3]
      rw [e1, e2]
  ·
    refine ⟨0, fun i => i.elim0, fun h => absurd rfl h, fun i => i.elim0, fun i => i.elim0,
      fun b hb y hy => ?_, fun i => i.elim0⟩
    obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep (hcm b hb y hy)
    have hfM : f ∈ isometryCentralizer Q x := supportedFixedDerived_le_isometryCentralizer hf
    have hjM : j ∈ isometryCentralizer Q x :=
      iSup₂_le (fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h) hj
    have hgM : ⁅b, y⁆ ∈ isometryCentralizer Q x := by
      rw [hgjf]
      exact mul_mem hjM hfM
    have h2 : (⟨⁅b, y⁆, hgM⟩ : ↥(isometryCentralizer Q x)) =
        ⁅(⟨b, hBM b hb⟩ : ↥(isometryCentralizer Q x)), (⟨y, hYM y hy⟩ : ↥(isometryCentralizer Q x))⁆ :=
      Subtype.ext rfl
    have h1 : isometryRestrictFixed Q x ⟨⁅b, y⁆, hgM⟩ = 1 := by
      rw [h2, map_commutatorElement]
      by_cases hdim : 3 ≤ finrank K (fixedSpace x)
      ·
        have hexc : SmallFixedException (Q.comp (fixedSpace x).subtype) := by
          by_contra hne
          exact hlist ⟨hdim, hne⟩
        have hK3' : Nat.card K ≤ 3 := by
          rcases hexc with ⟨-, h⟩ | ⟨-, h | h⟩ <;> omega
        have hp3 : 3 < p := by
          have := hp.two_le
          by_contra hle
          have h3 : p = 3 := by omega
          have := hK3 h3
          omega
        obtain ⟨hno, -⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
          hx.polarBilin_fixed_nondegenerate hdim
        have hβ : isometryRestrictFixed Q x ⟨b, hBM b hb⟩ = 1 := by
          set β' : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
            ⟨isometryRestrictFixed Q x ⟨b, hBM b hb⟩, isometryRestrictFixed_mem_orthogonalGroup _⟩
          have hβp : β' ^ p = 1 := by
            refine Subtype.ext ?_
            show (isometryRestrictFixed Q x ⟨b, hBM b hb⟩) ^ p = 1
            rw [← map_pow]
            have : (⟨b, hBM b hb⟩ : ↥(isometryCentralizer Q x)) ^ p = 1 := Subtype.ext (hBp b hb)
            rw [this, map_one]
          have hd : orderOf β' ∣ p := orderOf_dvd_of_pow_eq_one hβp
          rcases (Nat.dvd_prime hp).mp hd with h | h
          · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
          · exact absurd h (hno hexc β' p hp hp3)
        rw [hβ]
        exact commutatorElement_one_left _
      · have hdim2 : finrank K (fixedSpace x) ≤ 2 := by omega
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (hx.restrict_commute_of_mem_orthDerived hp2' hQ hRep hdim2 (hBM b hb) (hBΩ b hb)
            (hYM y hy) (hYΩ y hy)).eq
    have h4 : (⟨⁅b, y⁆, hgM⟩ : ↥(isometryCentralizer Q x)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ :=
      Subtype.ext hgjf
    have h3 : isometryRestrictFixed Q x ⟨f, hfM⟩ = 1 := by
      rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM, one_mul] at h1
      exact h1
    have hfB := supportedFixedDerived_le_supportedBlock hf
    have h5 : restrictFixed Q x ⟨f, hfB⟩ = 1 := by
      rw [← isometryRestrictFixed_restrictFixed]
      exact h3
    have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
    exact ⟨j, hj, 1, one_mem _, by rw [hgjf, hf1]⟩

end FixedPart

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
