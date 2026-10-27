module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Red
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock

public section

namespace CFSG.QuasithinUnique.A5.Kc3G2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.QuasithinUnique.Vol2Native.L239.Lie
open scoped commutatorElement

variable {G : Type} [Group G]

theorem not_isPGroup_alt5 : ¬ IsPGroup 2 ↥(alternatingGroup (Fin 5)) := by
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h
  rw [Delta5.a5_card] at hn
  have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem le_ker_of_normal_pGroup {B : Type*} [Group B] (α : B →* ↥(alternatingGroup (Fin 5)))
    (hα : Function.Surjective α) {N : Subgroup B} [N.Normal] (hN : IsPGroup 2 N) :
    N ≤ α.ker := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hN2 : IsPGroup 2 ↥(N.map α) := hN.map α
  have hNn : (N.map α).Normal := Subgroup.Normal.map inferInstance α hα
  rcases hNn.eq_bot_or_eq_top with h | h
  · intro x hx
    have : α x ∈ N.map α := Subgroup.mem_map_of_mem α hx
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    rw [h] at hN2
    exact not_isPGroup_alt5 (hN2.of_equiv Subgroup.topEquiv)

theorem noTwoQuotient_of_perfect [Finite G] {B : Subgroup G} (hperf : ⁅B, B⁆ = B) :
    ∀ (N : Subgroup ↥B) [N.Normal], IsPGroup 2 (↥B ⧸ N) → N = ⊤ := by
  intro N _ hN
  by_contra hNtop
  have : Nontrivial (↥B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  have hP : Group.IsPerfect ↥B := by
    rw [Group.isPerfect_def]
    apply Subgroup.map_injective B.subtype_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      hperf]
  have hQ : Group.IsPerfect (↥B ⧸ N) := Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (↥B ⧸ N) := hN.isNilpotent
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥B ⧸ N)
  exact absurd (Group.isPerfect_def.1 hQ) (ne_top_of_lt h1)

theorem ParabolicFacts.no_d5 [Finite G] {P Q B : Subgroup G} (hF : ParabolicFacts P Q)
    (hBP : B ≤ P) (hsub : (B.subgroupOf P).IsSubnormal) (hperf : ⁅B, B⁆ = B) (hD : D5S B) :
    False := by
  obtain ⟨V, QB, hVQB, hQBB, hQB2, hBQB, hBV, hcomm, α, hα, hαQ, β, hβ⟩ := hD
  have hQ := hF.pGroup
  have hB2 := noTwoQuotient_of_perfect hperf
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBP.trans hF.normalizes
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) :=
    normalizes_of_subnormal hBP hsub hB2 hF.le hF.normalizes hQ
  have hBcore : B ≤ CFSG.Quasithin.perfectCore P :=
    CFSG.Quasithin.le_perfectCore_of_perfect hBP hperf
  have hbadQ : B ≤ Q → False := by
    intro hBQle
    have hB2g : IsPGroup 2 ↥B := hQ.to_le hBQle
    exact not_isPGroup_alt5 (hB2g.of_surjective α hα)
  rcases hF.levi with hPQ | ⟨hgen, T, instT, g, hT, hg, hker⟩
  · exact hbadQ (hBcore.trans hPQ)
  have hsub' : (B.subgroupOf (CFSG.Quasithin.perfectCore P)).IsSubnormal :=
    isSubnormal_subgroupOf_of_le (CFSG.Quasithin.perfectCore_le P) hsub
  have himg : ((B.subgroupOf (CFSG.Quasithin.perfectCore P)).map g).IsSubnormal :=
    isSubnormal_map_of_surjective g hg hsub'
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hT himg with hbot | htop
  ·
    apply hbadQ
    intro b hb
    have hbc : b ∈ CFSG.Quasithin.perfectCore P := hBcore hb
    let b' : ↥(CFSG.Quasithin.perfectCore P) := ⟨b, hbc⟩
    have hmem : g b' ∈ (B.subgroupOf (CFSG.Quasithin.perfectCore P)).map g := ⟨b', hb, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hker b' hmem
  ·
    have hPinf : ∀ x ∈ CFSG.Quasithin.perfectCore P, ∃ b ∈ B, ∃ q ∈ Q, x = b * q := by
      intro x hx
      let x' : ↥(CFSG.Quasithin.perfectCore P) := ⟨x, hx⟩
      have hmem : g x' ∈ (B.subgroupOf (CFSG.Quasithin.perfectCore P)).map g :=
        htop ▸ Subgroup.mem_top _
      obtain ⟨b', hb', hbx⟩ := hmem
      refine ⟨(b' : G), hb', ((b'⁻¹ * x' : ↥(CFSG.Quasithin.perfectCore P)) : G), hker _ ?_, ?_⟩
      · rw [map_mul, map_inv, hbx, inv_mul_cancel]
      · simp [x']
    have hQ1 : ⁅Q, CFSG.Quasithin.perfectCore P⁆ ≤ ⁅Q, B⁆ ⊔ ⁅Q, Q⁆ := by
      refine Subgroup.commutator_le.2 fun q hq x hx => ?_
      obtain ⟨b, hb, q', hq', rfl⟩ := hPinf x hx
      have hid : ⁅q, b * q'⁆ = ⁅q, b⁆ * (b * ⁅q, q'⁆ * b⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [hid]
      refine mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq hb)) ?_
      have hn : b ∈ Subgroup.normalizer ((⁅Q, Q⁆ : Subgroup G) : Set G) :=
        le_normalizer_commutator_of_le_normalizer B Q Q hBQ hBQ hb
      have := (Subgroup.mem_normalizer_iff.1 hn _).1 (Subgroup.commutator_mem_commutator hq hq')
      exact Subgroup.mem_sup_right this
    have hQBle : ⁅Q, B⁆ ≤ Q := (commutator_le_inf_of_normalizes hBQ hQB).trans inf_le_right
    have hsupQ : ⁅Q, B⁆ ⊔ ⁅Q, Q⁆ = Q :=
      le_antisymm (sup_le hQBle (commutator_self_le Q)) (hgen.trans hQ1)
    have hQfin : Finite Q := Finite.of_injective _ Q.subtype_injective
    have hQBeq : ⁅Q, B⁆ = Q := eq_of_sup_commutator_eq (p := 2) hQ hQBle hsupQ
    have hQleB : Q ≤ B ⊓ Q := by
      have h := commutator_le_inf_of_normalizes hBQ hQB
      rwa [hQBeq] at h
    have hQBsub : Q ≤ B := fun x hx => (hQleB hx).1
    have hQn : (Q.subgroupOf B).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQBsub).2 hBQ
    have hQ2B : IsPGroup 2 ↥(Q.subgroupOf B) :=
      hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQBsub).symm
    have hker2 := le_ker_of_normal_pGroup α hα hQ2B
    have hQQB : Q ≤ QB := by
      intro x hx
      have h1 : (⟨x, hQBsub hx⟩ : ↥B) ∈ Q.subgroupOf B := Subgroup.mem_subgroupOf.2 hx
      exact (hαQ _).1 (MonoidHom.mem_ker.1 (hker2 h1))
    have hQV : Q ≤ V := by
      calc Q = ⁅Q, B⁆ := hQBeq.symm
        _ ≤ ⁅QB, B⁆ := Subgroup.commutator_mono hQQB le_rfl
        _ ≤ V := hcomm
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    apply hxy
    have hv : ∀ a b : ↥V, a * b = b * a := fun a b =>
      β.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    have := hv ⟨x, hQV hx⟩ ⟨y, hQV hy⟩
    exact congrArg Subtype.val this

end CFSG.QuasithinUnique.A5.Kc3G2
