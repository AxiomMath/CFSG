module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU64b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open scoped commutatorElement

@[expose] def U64Fact : Prop :=
  ∀ (Kb : Type) [Group Kb] [Finite Kb] (lab : GLALabel),
    HasLabel Kb (fun l : GLALabel => l = lab) →
    ((lab.tag = .A ∧ 4 ∣ lab.n ∧ 5 ∣ lab.rank + 1) ∨
      (lab.tag = .twA ∧ lab.n % 4 = 2 ∧ 5 ∣ lab.rank + 1)) →
    5 ∣ Nat.card (Subgroup.center Kb) →
    ∀ β : MulAut Kb, β ^ 3 = 1 → ∀ Jb : Subgroup Kb, GLAPComponent 3 (fixSubgroup β) Jb →
      HasLabel ↥Jb (fun l : GLALabel => l = ⟨.twA, 4, 2⟩) →
      lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩ ∨ ∃ r : ℕ, 1 < r ∧ lab = ⟨.twA, 5 * r - 1, 2⟩

theorem hasLabel_of_equiv_centerQuot {X Y : Type} [Group X] [Group Y] {S : GLALabel → Prop}
    (hY : commutator Y = ⊤) (e : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y)
    (h : HasLabel X S) : HasLabel Y S := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hY, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, e.symm.trans θ, hθ⟩

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_le_core_center {r : ℕ} (hr : r.Prime) {H : Type} [Group H] [Finite H]
    {Y J' : Subgroup H} (hJ' : GLAPComponent r Y J') (hq : CFSG.Open.IsQuasisimple ↥J')
    (N : Subgroup H) [N.Normal] (hN : ¬ r ∣ Nat.card N) :
    N.subgroupOf J' ≤ Subgroup.center ↥J' := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hnorm : (N.subgroupOf J').Normal := inferInstance
  have hcop : Nat.Coprime r (Nat.card (N.subgroupOf J')) := by
    have h1 : Nat.card (N.subgroupOf J') ∣ Nat.card N := by
      have : (N.subgroupOf J').map J'.subtype ≤ N := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      rw [← Subgroup.card_map_of_injective J'.subtype_injective]
      exact Subgroup.card_dvd_of_le this
    exact Nat.Coprime.coprime_dvd_right h1 ((Nat.Prime.coprime_iff_not_dvd hr).2 hN)
  have hle : N.subgroupOf J' ≤ GLAPPrimeCore r ↥J' := le_sSup ⟨hnorm, hcop⟩
  exact hle.trans (le_center_of_normal_of_isQuasisimple hq inferInstance
    (glaPPrimeCore_ne_top hr hJ'))

theorem hasLabel_image_bar {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {X K J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hKp : GLAPComponent p X K) (hKr : GLAPComponent r X K)
    (hJ : GLAPComponent r (K ⊓ Subgroup.centralizer ({y} : Set G)) J) {S : GLALabel → Prop}
    (hJl : HasLabel ↥J S) :
    HasLabel ↥((J.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K))) S := by
  obtain ⟨hJK, hcomp'⟩ := glaPComponent_fixSubgroup_conjAut' hr K hy hJ
  have hl' : HasLabel ↥(J.subgroupOf K) S := (hasLabel_subgroupOf_iff hJK S).1 hJl
  have hq' : CFSG.Open.IsQuasisimple ↥(J.subgroupOf K) := hasLabel_isQuasisimple hl'
  set J' := J.subgroupOf K with hJ'
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥K) with hπ
  let φ : ↥J' →* ↥(J'.map π) :=
    (π.comp J'.subtype).codRestrict _ (fun j => Subgroup.mem_map_of_mem π j.2)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨_, ⟨j, hj, rfl⟩⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  haveI hperf : Group.IsPerfect ↥J' := ⟨hq'.1⟩
  have hker : φ.ker ≤ Subgroup.center ↥J' := by
    intro j hj
    have hj1 : π (j : ↥K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hj)
    have hjN : (j : ↥K) ∈ GLAPPrimeCore p ↥K := (QuotientGroup.eq_one_iff _).1 hj1
    apply mem_center_of_commutators_central' hperf
    intro j₁
    have hc : (j * j₁ * j⁻¹ * j₁⁻¹ : ↥J') ∈ (N0 p r K).subgroupOf J' := by
      rw [Subgroup.mem_subgroupOf]
      have h2 : ⁅(j : ↥K), (j₁ : ↥K)⁆ ∈ N0 p r K := mix_commutator_le hp hr hKp hKr
        (Subgroup.commutator_mem_commutator hjN (Subgroup.mem_top _))
      simpa [commutatorElement_def] using h2
    exact subgroupOf_le_core_center hr hcomp' hq' (N0 p r K) (n0_not_dvd hr K) hc
  obtain ⟨e⟩ := quotEquiv_of_perfect_central φ hφsurj hperf hker
  have hperf2 : commutator ↥(J'.map π) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := φ) hφsurj).commutator_eq_top
  exact hasLabel_of_equiv_centerQuot hperf2 e hl'

end CFSG.LocalAnalysis.GLTheoremA.Y10F
