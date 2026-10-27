module

public import CFSG.Quasithin.Background.BlueprintB2Frattini
public import CFSG.RankThree.PartTwo.Sec11.Item116R1H1bPure

public section

namespace CFSG.GroupTheory

open scoped IsMulCommutative
open CFSG.RankThree.PartOne.FixedRank36

section Normalizer

variable {Γ : Type*} [Group Γ] [Finite Γ] {q : ℕ} [Fact q.Prime]
  {P : Subgroup Γ} {b : Γ}

theorem orderOf_ne_of_inf_centralizer_eq_bot (hP : IsPGroup q P) (hP0 : P ≠ ⊥)
    (hb : b ∈ Subgroup.normalizer (P : Set Γ))
    (hC : P ⊓ Subgroup.centralizer ({b} : Set Γ) = ⊥) : orderOf b ≠ q := by
  intro hbq
  have hA : IsPGroup q (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbq, pow_one])
  have hC' : P ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set Γ) = ⊥ := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hC
  exact (CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
    (Fact.out : q.Prime) hA hP hP0 (Subgroup.zpowers_le.mpr hb)) hC'

end Normalizer

section Conjugation

variable {Γ : Type*} [Group Γ] [Finite Γ] {q : ℕ} [Fact q.Prime]
  {P : Subgroup Γ} [P.Normal] [IsElementaryAbelian q (↥P ⧸ frattini ↥P)]

theorem frattiniRep_conjNormal_eq_zero_of_inf_centralizer_eq_bot
    (hP : IsPGroup q P) {r : ℕ} (hr : r.Prime) {b : Γ}
    (hbr : orderOf b = r)
    (hC : P ⊓ Subgroup.centralizer ({b} : Set Γ) = ⊥)
    (v : Additive (↥P ⧸ frattini ↥P))
    (hv : CFSG.RankThree.PartOne.FixedRank36.frattiniRep q
      (MulAut.conjNormal (H := P)) b v = v) : v = 0 := by
  classical
  by_cases hP0 : P = ⊥
  · obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hvx : v = Additive.ofMul (x : ↥P ⧸ frattini ↥P) := by rw [hx]; rfl
    have hx1 : x = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp (hP0 ▸ x.2))
    rw [hvx, hx1]
    simp
  have hA : IsPGroup r (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbr, pow_one])
  have hq_ne : r ≠ q := hbr ▸ orderOf_ne_of_inf_centralizer_eq_bot hP hP0
    (Subgroup.le_normalizer_of_normal (H := P) (Subgroup.mem_zpowers b)) hC
  have hAρ : IsPGroup r (Subgroup.zpowers ((MulAut.conjNormal (H := P)) b)) := by
    rw [← MonoidHom.map_zpowers (MulAut.conjNormal (H := P)) b]
    exact hA.map _
  have hρv : v ∈ Module.End.eigenspace (R := ZMod q)
      (frattiniRep q (MulAut.conjNormal (H := P)) b) 1 := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact hv
  obtain ⟨x, hxfix, hxv⟩ :=
    CFSG.RankThree.PartTwo.Sec11.exists_fixed_lift_prime hP hr hq_ne
      (MulAut.conjNormal (H := P)) b hAρ v hρv
  have hxb : (x : Γ) ∈ Subgroup.centralizer ({b} : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hconj : b * (x : Γ) * b⁻¹ = (x : Γ) := by
      simpa [MulAut.conjNormal_apply] using congrArg Subtype.val hxfix
    simpa [mul_assoc] using congrArg (· * b) hconj
  have hxbot : (x : Γ) ∈ P ⊓ Subgroup.centralizer ({b} : Set Γ) := ⟨x.2, hxb⟩
  rw [hC] at hxbot
  have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hxbot)
  simpa [hx1] using hxv.symm

theorem mem_centralizer_of_frattiniRep_conjNormal_eq_one (hP : IsPGroup q P) (hq2 : q ≠ 2)
    {t : Γ} (ht : IsPGroup 2 (Subgroup.zpowers t))
    (h : CFSG.RankThree.PartOne.FixedRank36.frattiniRep q
      (MulAut.conjNormal (H := P)) t = 1) :
    t ∈ Subgroup.centralizer (P : Set Γ) := by
  have htρ : IsPGroup 2 (Subgroup.zpowers ((MulAut.conjNormal (H := P)) t)) := by
    rw [← MonoidHom.map_zpowers (MulAut.conjNormal (H := P)) t]
    exact ht.map _
  exact CFSG.Quasithin.BlueprintB2.mem_centralizer_of_conjNormal_eq_one
    (frattiniRep_eq_one hP hq2 (MulAut.conjNormal (H := P)) t htρ h)

end Conjugation

section Centralizer

variable {Γ : Type*} [Group Γ] [Finite Γ] {q : ℕ} [Fact q.Prime]

theorem mem_centralizer_of_mem_centralizer_map_subtype (hq2 : q ≠ 2) {Q : Subgroup Γ} [Q.Normal]
    {D : Subgroup ↥Q} (hD : IsPGroup q (fixingSubgroup (MulAut ↥Q) (D : Set ↥Q))) {t : Γ}
    (ht : IsPGroup 2 (Subgroup.zpowers t))
    (htD : t ∈ Subgroup.centralizer ((D.map Q.subtype : Subgroup Γ) : Set Γ)) :
    t ∈ Subgroup.centralizer (Q : Set Γ) := by
  have htρ : IsPGroup 2 (Subgroup.zpowers ((MulAut.conjNormal (H := Q)) t)) := by
    rw [← MonoidHom.map_zpowers (MulAut.conjNormal (H := Q)) t]
    exact ht.map _
  have hfixD : (MulAut.conjNormal (H := Q)) t ∈
      fixingSubgroup (MulAut ↥Q) (D : Set ↥Q) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    have hmem : (d : Γ) ∈ (D.map Q.subtype : Subgroup Γ) := ⟨d, hd, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp htD) (d : Γ) hmem
    have hconj : t * (d : Γ) * t⁻¹ = (d : Γ) := by
      calc t * (d : Γ) * t⁻¹ = ((d : Γ) * t) * t⁻¹ := by rw [hcomm.symm]
        _ = (d : Γ) := by group
    simpa [MulAut.conjNormal_apply] using hconj
  have hdisj : Disjoint (Subgroup.zpowers ((MulAut.conjNormal (H := Q)) t))
      (fixingSubgroup (MulAut ↥Q) (D : Set ↥Q)) :=
    IsPGroup.disjoint_of_ne 2 q (fun h => hq2 h.symm) _ _ htρ hD
  exact CFSG.Quasithin.BlueprintB2.mem_centralizer_of_conjNormal_eq_one
    (Subgroup.disjoint_def.mp hdisj
      (Subgroup.mem_zpowers ((MulAut.conjNormal (H := Q)) t)) hfixD)

end Centralizer

section CriticalSubgroup

variable {Γ : Type*} [Group Γ] [Finite Γ] {q : ℕ} [Fact q.Prime]

theorem exists_critical_map_subtype (hq2 : q ≠ 2) {Q : Subgroup Γ} [Q.Normal]
    (hQ : IsPGroup q Q) (hQ1 : Q ≠ ⊥) :
    ∃ D : Subgroup ↥Q, (D.map Q.subtype).Normal ∧
      IsPGroup q ↥(D.map Q.subtype) ∧ D.map Q.subtype ≠ ⊥ ∧
      (∀ y ∈ D.map Q.subtype, y ^ q = 1) ∧
      ⁅⁅D.map Q.subtype, D.map Q.subtype⁆, D.map Q.subtype⁆ = ⊥ ∧
      IsPGroup q (fixingSubgroup (MulAut ↥Q) (D : Set ↥Q)) := by
  classical
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
  obtain ⟨D, hDchar, hDne, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hQ
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, hDfix⟩
  · haveI : D.Characteristic := hDchar
    exact ConjAct.normal_of_characteristic_of_normal
  · exact (hQ.to_subgroup D).map Q.subtype
  · intro hbot
    exact hDne ((Subgroup.map_eq_bot_iff_of_injective (H := D) (f := Q.subtype)
      Q.subtype_injective).mp hbot)
  · rintro y ⟨d, hd, rfl⟩
    simpa [Subgroup.coe_pow] using congrArg Subtype.val (hDexp d hd)
  · have hDD : ⁅D, D⁆ ≤ D ⊓ Subgroup.centralizer (D : Set ↥Q) :=
      (Subgroup.commutator_mono le_rfl le_top).trans hDcomm
    have hcent : ⁅D, D⁆ ≤ Subgroup.centralizer (D : Set ↥Q) := hDD.trans inf_le_right
    have hbot : ⁅⁅D, D⁆, D⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hmap : (⁅⁅D, D⁆, D⁆ : Subgroup ↥Q).map Q.subtype =
        ⁅⁅D.map Q.subtype, D.map Q.subtype⁆, D.map Q.subtype⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator]
    rw [← hmap, hbot, Subgroup.map_bot]

end CriticalSubgroup
