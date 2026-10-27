module

public import CFSG.ClassicalInvolution.Asc77.AscBSCModel
public import CFSG.ClassicalInvolution.Uniform.U3Edge
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.Open.StatedAPI
public import CFSG.ClassicalInvolution.Q3.Q3WADict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NS

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.BSC
open scoped MatrixGroups


section Involution

variable {t : StatedLieTag} {n : ℕ}

theorem exists_inv3 (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (ModelK 3 t n 1)} (hR : R ∈ ModelFund 3 t n 1) :
    ∃ x : ModelK 3 t n 1, IsInvIn R x := by
  obtain ⟨φ⟩ := fund_equiv_sl2 (by norm_num) hfund hadm hG2 hD4 hR
  have hodd : Odd (Nat.card (GaloisField 3 1)) := Q3W.odd_gf3
  refine ⟨((φ.symm (-1) : R) : ModelK 3 t n 1), (φ.symm (-1)).2, ?_, ?_⟩
  · have h : φ.symm (-1) * φ.symm (-1) = 1 := by
      rw [← map_mul]
      simp
    exact congrArg Subtype.val h
  · intro h1
    have h2 : φ.symm (-1) = 1 := Subtype.ext h1
    have h3 : (-1 : SL(2, GaloisField 3 1)) = 1 := by
      have := congrArg φ h2
      simpa using this
    exact sl2_neg_one_ne_one hodd h3

theorem inv_unique3 (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (ModelK 3 t n 1)} (hR : R ∈ ModelFund 3 t n 1)
    {x y : ModelK 3 t n 1} (hx : IsInvIn R x) (hy : IsInvIn R y) : x = y := by
  obtain ⟨φ⟩ := fund_equiv_sl2 (by norm_num) hfund hadm hG2 hD4 hR
  have hodd : Odd (Nat.card (GaloisField 3 1)) := Q3W.odd_gf3
  have key : ∀ (w : ModelK 3 t n 1) (hw : IsInvIn R w), (⟨w, hw.1⟩ : R) = φ.symm (-1) := by
    intro w hw
    have hw2 : (⟨w, hw.1⟩ : R) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hw.2.1)
    have hw1 : (⟨w, hw.1⟩ : R) ≠ 1 := fun h => hw.2.2 (congrArg Subtype.val h)
    have hord : orderOf (⟨w, hw.1⟩ : R) = 2 := orderOf_eq_prime hw2 hw1
    exact (orderOf_eq_two_iff_of_equiv_sl2 hodd φ _).mp hord
  have h := (key x hx).trans (key y hy).symm
  exact congrArg Subtype.val h

end Involution

section Pair

variable {t : StatedLieTag} {n : ℕ}

theorem exists_commuting_pair_ne3 (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hnA1 : ¬ (t = .PSL ∧ n = 2))
    (hconn : CommFamilyConnected (ModelFund 3 t n 1)) {R₀ : Subgroup (ModelK 3 t n 1)}
    (hR₀ : R₀ ∈ ModelFund 3 t n 1) :
    ∃ R ∈ ModelFund 3 t n 1, ∃ S ∈ ModelFund 3 t n 1, Commutes R S ∧
      ∀ r ∈ R, ∀ s ∈ S, r * r ∈ Subgroup.center (ModelK 3 t n 1) →
        s * s ∈ Subgroup.center (ModelK 3 t n 1) → r ∉ Subgroup.center (ModelK 3 t n 1) →
        s ∉ Subgroup.center (ModelK 3 t n 1) → r * s⁻¹ ∉ Subgroup.center (ModelK 3 t n 1) := by
  by_contra hcon
  push Not at hcon
  have hK : CFSG.Open.IsQuasisimple (ModelK 3 t n 1) :=
    (ModelFacts.modelClauseZero t n 3 1 Fact.out hfund hadm).1
  have hinv : ∀ {R : Subgroup (ModelK 3 t n 1)}, R ∈ ModelFund 3 t n 1 → ∀ {x : ModelK 3 t n 1},
      x ∈ R → x * x ∈ Subgroup.center (ModelK 3 t n 1) →
      x ∉ Subgroup.center (ModelK 3 t n 1) → IsInvIn R x := by
    intro R hR x hxR hx2 hxZ
    refine ⟨hxR, eq_one_of_mem_center hfund hadm hnA1 hR (R.mul_mem hxR hxR) hx2, ?_⟩
    rintro rfl
    exact hxZ (Subgroup.one_mem _)
  have hall : ∀ S : Subgroup (ModelK 3 t n 1), Relation.ReflTransGen
      (fun U V : Subgroup (ModelK 3 t n 1) =>
        U ∈ ModelFund 3 t n 1 ∧ V ∈ ModelFund 3 t n 1 ∧ Commutes U V)
      R₀ S → ∀ {r s : ModelK 3 t n 1}, IsInvIn R₀ r → IsInvIn S s →
        r * s⁻¹ ∈ Subgroup.center (ModelK 3 t n 1) := by
    intro S hpath
    induction hpath with
    | refl =>
        intro r s hr hs
        have h := inv_unique3 hfund hadm hG2 hD4 hR₀ hr hs
        rw [h, mul_inv_cancel]
        exact Subgroup.one_mem _
    | @tail B C _ hbc ih =>
        intro r s hr hs
        obtain ⟨hB, hC, hBC⟩ := hbc
        obtain ⟨r', hr'B, s', hs'C, hr2, hs2, hrZ, hsZ, hrs⟩ := hcon B hB C hC hBC
        have hr'inv := hinv hB hr'B hr2 hrZ
        have hs'inv := hinv hC hs'C hs2 hsZ
        have e2 : s = s' := inv_unique3 hfund hadm hG2 hD4 hC hs hs'inv
        have h1 := ih hr hr'inv
        rw [e2]
        have e : r * s'⁻¹ = (r * r'⁻¹) * (r' * s'⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ h1 hrs
  obtain ⟨r₀, hr₀⟩ := exists_inv3 hfund hadm hG2 hD4 hR₀
  have hcent : ∀ y : ModelK 3 t n 1, r₀ * y * r₀⁻¹ * y⁻¹ ∈ Subgroup.center (ModelK 3 t n 1) := by
    intro y
    have hgR : conjSub y R₀ ∈ ModelFund 3 t n 1 := conjSub_mem_modelFund hR₀ y
    have hinv' : IsInvIn (conjSub y R₀) (y * r₀ * y⁻¹) := by
      refine ⟨conj_mem_conjSub hr₀.1, ?_, ?_⟩
      · calc y * r₀ * y⁻¹ * (y * r₀ * y⁻¹) = y * (r₀ * r₀) * y⁻¹ := by group
          _ = 1 := by rw [hr₀.2.1]; group
      · intro h
        apply hr₀.2.2
        have e : r₀ = y⁻¹ * (y * r₀ * y⁻¹) * y := by group
        rw [e, h]
        group
    have h := hall (conjSub y R₀) (hconn R₀ hR₀ _ hgR) hr₀ hinv'
    have e : r₀ * (y * r₀ * y⁻¹)⁻¹ = r₀ * y * r₀⁻¹ * y⁻¹ := by group
    rwa [e] at h
  have hz : r₀ ∈ Subgroup.center (ModelK 3 t n 1) :=
    ModelFacts.mem_center_of_commutators_mem_center hK hcent
  exact hr₀.2.2 (eq_one_of_mem_center hfund hadm hnA1 hR₀ hr₀.1 hz)

theorem exists_pair_indep_images {c : CompData} (hc : c = CompData.model t n)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hnA1 : ¬ (t = .PSL ∧ n = 2)) (hconn : CommFamilyConnected c.fund)
    {R₀ : Subgroup c.G} (hR₀ : R₀ ∈ c.fund) {X : Type} [Group X] (φ : c.G →* X)
    (hker : φ.ker ≤ Subgroup.center c.G) {zb : X} (hzb : ∀ y : c.G, φ y * zb = zb * φ y) :
    ∃ R ∈ c.fund, ∃ S ∈ c.fund, Commutes R S ∧ ∀ r ∈ R, ∀ s ∈ S, φ r * φ r = 1 →
      φ s * φ s = 1 → φ r ≠ 1 → φ s ≠ 1 → φ r ≠ φ s ∧ φ r * φ s ≠ zb := by
  subst hc
  obtain ⟨R, hR, S, hS, hRS, hpair⟩ := exists_commuting_pair_ne3 hfund hadm hG2 hD4 hnA1 hconn hR₀
  refine ⟨R, hR, S, hS, hRS, ?_⟩
  intro r hr s hs hr2 hs2 hr1 hs1
  have hK : CFSG.Open.IsQuasisimple (ModelK 3 t n 1) :=
    (ModelFacts.modelClauseZero t n 3 1 Fact.out hfund hadm).1
  have hrZ : r ∉ Subgroup.center (ModelK 3 t n 1) := fun h =>
    hr1 (by rw [eq_one_of_mem_center hfund hadm hnA1 hR hr h, map_one])
  have hsZ : s ∉ Subgroup.center (ModelK 3 t n 1) := fun h =>
    hs1 (by rw [eq_one_of_mem_center hfund hadm hnA1 hS hs h, map_one])
  have hr2' : r * r ∈ Subgroup.center (ModelK 3 t n 1) :=
    hker (by rw [MonoidHom.mem_ker, map_mul]; exact hr2)
  have hs2' : s * s ∈ Subgroup.center (ModelK 3 t n 1) :=
    hker (by rw [MonoidHom.mem_ker, map_mul]; exact hs2)
  have hrs := hpair r hr s hs hr2' hs2' hrZ hsZ
  refine ⟨fun h => hrs (hker ?_), fun h => hrs ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  · have hcent : ∀ y : ModelK 3 t n 1,
        r * s * y * (r * s)⁻¹ * y⁻¹ ∈ Subgroup.center (ModelK 3 t n 1) := by
      intro y
      apply hker
      have e : φ (r * s * y * (r * s)⁻¹ * y⁻¹) = zb * φ y * zb⁻¹ * (φ y)⁻¹ := by
        rw [← h]
        simp only [map_mul, map_inv]
      rw [MonoidHom.mem_ker, e, ← hzb y]
      group
    have hrsZ := ModelFacts.mem_center_of_commutators_mem_center hK hcent
    have e : r * s⁻¹ = (r * s) * (s * s)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hrsZ (Subgroup.inv_mem _ hs2')

end Pair

section Tags

@[expose] def ListedTwin3 (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSp ∧ n = 2) ∨ (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4) ∨ (t = .POmegaOdd ∧ n = 3) ∨
    (t = .POmegaPlus ∧ n = 4) ∨ (t = .POmegaMinus ∧ n = 4)

theorem tag_cases3 {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hnA1 : ¬ (t = .PSL ∧ n = 2)) :
    CommFamilyConnected (ModelFund 3 t n 1) ∨
      (((t = .PSL ∨ t = .PSU) ∧ n = 3) ∨ ListedTwin3 t n) := by
  rcases Uniform.tag_casesU (p := 3) (e := 1) (by norm_num) hfund hadm hG2 hD4 with h | hsmall
  · exact Or.inl h
  · right
    rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hk2 : 2 ≤ n := hadm.2.2.1
      have : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact (hnA1 ⟨rfl, rfl⟩).elim
      · exact Or.inl ⟨Or.inl rfl, rfl⟩
      · exact Or.inr (by simp [ListedTwin3])
    · have hk3 : 3 ≤ n := hadm.2.2.1
      have : n = 3 ∨ n = 4 := by omega
      rcases this with rfl | rfl
      · exact Or.inl ⟨Or.inr rfl, rfl⟩
      · exact Or.inr (by simp [ListedTwin3])
    · exact Or.inr (by simp [ListedTwin3])
    · exact Or.inr (by simp [ListedTwin3])
    · exact Or.inr (by simp [ListedTwin3])
    · exact Or.inr (by simp [ListedTwin3])

end Tags

section Comp

variable {t : StatedLieTag} {n : ℕ}

theorem singleClass_of_eq_model {c : CompData} (hc : c = CompData.model t n)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) : ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R := by
  subst hc
  exact ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three hfund hadm hG2 hD4

theorem commFamilyConnected_of_eq_model {c : CompData} (hc : c = CompData.model t n)
    (h : CommFamilyConnected (ModelFund 3 t n 1)) : CommFamilyConnected c.fund := by
  subst hc
  exact h

theorem not_psl_two_of_admissible {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n 3 1) :
    ¬ (t = .PSL ∧ n = 2) :=
  CFSG.Open.StatedAPI.not_psl_two_of_statedLieAdmissible_three_one hadm

end Comp

end CFSG.ClassicalInvolution.Q3.Q3NS
