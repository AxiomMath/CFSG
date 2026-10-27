module

public import CFSG.Walter.Cited.HuppertBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Core
public import CFSG.GroupTheory.ABGLocalTools.FixedPointCount
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS
open scoped commutatorElement

theorem eq_top_of_normal_not_le {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    {O : Subgroup J} [O.Normal] (hOodd : Odd (Nat.card O)) (hsimple : IsSimpleGroup (J ⧸ O))
    (R : Subgroup J) [hRn : R.Normal] (hR : ¬ R ≤ O) : R = ⊤ := by
  have hmap : R.map (QuotientGroup.mk' O) = ⊤ := by
    have : (R.map (QuotientGroup.mk' O)).Normal :=
      Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective O)
    rcases hsimple.eq_bot_or_eq_top_of_normal (R.map (QuotientGroup.mk' O)) with h | h
    · exfalso
      apply hR
      intro r hr
      have : QuotientGroup.mk' O r ∈ R.map (QuotientGroup.mk' O) := ⟨r, hr, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff r).1 this
    · exact h
  have hsurj : Function.Surjective ((QuotientGroup.mk' R).comp O.subtype) := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have : QuotientGroup.mk' O j ∈ R.map (QuotientGroup.mk' O) := by rw [hmap]; trivial
    obtain ⟨r, hr, hrj⟩ := this
    have ho : r⁻¹ * j ∈ O := QuotientGroup.eq.1 hrj
    refine ⟨⟨r⁻¹ * j, ho⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have := hRn.conj_mem r hr j⁻¹
    simpa [mul_assoc] using this
  have hdvd : Nat.card (J ⧸ R) ∣ Nat.card O := Subgroup.card_dvd_of_surjective hsurj
  have hQodd : Odd (Nat.card (J ⧸ R)) := Odd.of_dvd_nat hOodd hdvd
  have hsolv : Group.IsSolvable (J ⧸ R) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
  by_contra hne
  have hnsub : ¬ Subsingleton (J ⧸ R) := fun h => hne ((QuotientGroup.subsingleton_iff).1 h)
  have hnt : Nontrivial (J ⧸ R) := not_subsingleton_iff_nontrivial.1 hnsub
  exact Group.IsPerfect.not_isSolvable (J ⧸ R) hsolv

theorem eq_top_of_isPGroup_quotient {J : Type*} [Group J] [Finite J] [Group.IsPerfect J] {p : ℕ}
    [Fact p.Prime] (N : Subgroup J) [N.Normal] (h : IsPGroup p (J ⧸ N)) : N = ⊤ := by
  by_contra hne
  have hnsub : ¬ Subsingleton (J ⧸ N) := fun hs => hne ((QuotientGroup.subsingleton_iff).1 hs)
  have hnt : Nontrivial (J ⧸ N) := not_subsingleton_iff_nontrivial.1 hnsub
  have hnil : Group.IsNilpotent (J ⧸ N) := h.isNilpotent
  exact Group.IsPerfect.not_isSolvable (J ⧸ N) inferInstance

@[expose] def PStableAct (p : ℕ) {J Q : Type*} [Group J] [Group Q] (ρ : J →* MulAut Q) : Prop :=
  ∀ x : J, (∀ u : Q, ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) = u⁻¹ * ρ x⁻¹ u) →
    QuotientGroup.mk' ρ.ker x ∈ pCore p (J ⧸ ρ.ker)

theorem exists_not_quadratic {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    {O : Subgroup J} [O.Normal] (hOodd : Odd (Nat.card O)) (hsimple : IsSimpleGroup (J ⧸ O))
    {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] (ρ : J →* MulAut Q) (hstab : PStableAct p ρ)
    {x : J} (hxO : x ∉ O) (hx1 : ρ x ≠ 1) :
    ∃ u : Q, ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) ≠ u⁻¹ * ρ x⁻¹ u := by
  by_contra hq
  push Not at hq
  have hxR := hstab x hq
  set R : Subgroup J := (pCore p (J ⧸ ρ.ker)).comap (QuotientGroup.mk' ρ.ker) with hR
  have hRn : R.Normal := (pCore_normal (p := p) (G := J ⧸ ρ.ker)).comap _
  have hxR' : x ∈ R := hxR
  have hRtop : R = ⊤ := eq_top_of_normal_not_le hOodd hsimple R (fun h => hxO (h hxR'))
  have hcore : ∀ q : J ⧸ ρ.ker, q ∈ pCore p (J ⧸ ρ.ker) := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have : j ∈ R := by rw [hRtop]; trivial
    exact this
  have hpg : IsPGroup p (J ⧸ ρ.ker) := by
    intro g
    obtain ⟨n, hn⟩ := pCore_isPGroup (p := p) (G := J ⧸ ρ.ker) ⟨g, hcore g⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have hker : ρ.ker = ⊤ := eq_top_of_isPGroup_quotient ρ.ker hpg
  apply hx1
  have : x ∈ ρ.ker := by rw [hker]; trivial
  exact this

open CFSG.Walter.Huppert in
theorem frattini_action_ne_one {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    {O : Subgroup J} [O.Normal] (hOodd : Odd (Nat.card O)) (hsimple : IsSimpleGroup (J ⧸ O))
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : J →* MulAut P) {x : J} (hxO : x ∉ O) (hx1 : ρ x ≠ 1) :
    (frattiniAut P).comp ρ x ≠ 1 := by
  intro h
  set ρM : J →* MulAut (P ⧸ frattini P) := (frattiniAut P).comp ρ with hρM
  have hxker : x ∈ ρM.ker := h
  have hT : ρM.ker = ⊤ :=
    eq_top_of_normal_not_le hOodd hsimple ρM.ker (fun hle => hxO (hle hxker))
  have hall : ∀ j : J, ρ j ^ p ^ Nat.card (MulAut P) = 1 := by
    intro j
    have hj : frattiniAut P (ρ j) = 1 := by
      have : j ∈ ρM.ker := by rw [hT]; trivial
      exact this
    exact exists_pow_eq_one_of_frattiniAut_eq_one hP hj
  have hpg : IsPGroup p (J ⧸ ρ.ker) := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨Nat.card (MulAut P), ?_⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (by rw [MonoidHom.mem_ker, map_pow]; exact hall j)
  have hker : ρ.ker = ⊤ := eq_top_of_isPGroup_quotient ρ.ker hpg
  apply hx1
  have : x ∈ ρ.ker := by rw [hker]; trivial
  exact this

open CFSG.Walter.Huppert in
theorem exists_not_quadratic_frattini {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    {O : Subgroup J} [O.Normal] (hOodd : Odd (Nat.card O)) (hsimple : IsSimpleGroup (J ⧸ O))
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : J →* MulAut P) (hstab : PStableAct p ((frattiniAut P).comp ρ)) {x : J} (hxO : x ∉ O)
    (hx1 : ρ x ≠ 1) :
    ∃ z : P, (z⁻¹ * ρ x⁻¹ z)⁻¹ * ρ x⁻¹ (z⁻¹ * ρ x⁻¹ z) ∉ frattini P := by
  obtain ⟨u, hu⟩ := exists_not_quadratic hOodd hsimple ((frattiniAut P).comp ρ) hstab hxO
    (frattini_action_ne_one hOodd hsimple hP ρ hxO hx1)
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
  refine ⟨z, fun hmem => hu ?_⟩
  simp only [MonoidHom.comp_apply, frattiniAut_mk] at hu ⊢
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, frattiniAut_mk, QuotientGroup.eq]
  simpa using (frattini P).inv_mem hmem

end CFSG.GH74.GLS.Th2.Obs
