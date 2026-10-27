module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.RankThree.PartOne.S12.SectionalRank
public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo

public section

namespace CFSG.GF2Type.Aschbacher1976Common

open CFSG.ComponentClassification.AschbacherKnownGroup

abbrev TwoGenSubgroups (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup X, ∃ s : Finset X, s.card ≤ 2 ∧ Subgroup.closure (s : Set X) = P

theorem mul_mem_of_notMem_of_index_two {X : Type*} [Group X] {H : Subgroup X}
    (hH : H.index = 2) {x y : X} (hx : x ∉ H) (hy : y ∉ H) : x * y ∈ H := by
  obtain ⟨a, -, hall⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hH
  have hz : ∀ z : X, z ∉ H → z * a ∈ H := fun z hz' => (hall z).resolve_right hz'
  have hy' : y⁻¹ ∉ H := fun h => hy (by simpa using H.inv_mem h)
  have h1 : x * a ∈ H := hz x hx
  have h2 : y⁻¹ * a ∈ H := hz y⁻¹ hy'
  have h3 : x * y = (x * a) * (y⁻¹ * a)⁻¹ := by group
  rw [h3]
  exact H.mul_mem h1 (H.inv_mem h2)

theorem exists_two_gen_of_cyclic_coset {X : Type*} [Group X] (C : Subgroup X) [IsCyclic C]
    (hcoset : ∀ x y : X, x ∉ C → y ∉ C → x * y ∈ C) (P : Subgroup X) :
    ∃ s : Finset X, s.card ≤ 2 ∧ Subgroup.closure (s : Set X) = P := by
  classical
  haveI : IsCyclic ↥(P ⊓ C) := Subgroup.isCyclic_of_le inf_le_right
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := ↥(P ⊓ C))
  have hgP : (g : X) ∈ P := (Subgroup.mem_inf.mp g.2).1
  have hgz : ∀ x ∈ C, x ∈ P → x ∈ Subgroup.zpowers (g : X) := by
    intro x hxC hxP
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, Subgroup.mem_inf.mpr ⟨hxP, hxC⟩⟩)
    have hkx : (g : X) ^ k = x := by
      simpa using congrArg Subtype.val hk
    rw [← hkx]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  by_cases ht : ∃ t ∈ P, t ∉ C
  · obtain ⟨t, htP, htC⟩ := ht
    have hgcl : (g : X) ∈ Subgroup.closure (({(g : X), t} : Finset X) : Set X) :=
      Subgroup.subset_closure (by simp)
    have htcl : t ∈ Subgroup.closure (({(g : X), t} : Finset X) : Set X) :=
      Subgroup.subset_closure (by simp)
    have hzp : Subgroup.zpowers (g : X) ≤ Subgroup.closure (({(g : X), t} : Finset X) : Set X) :=
      Subgroup.zpowers_le.mpr hgcl
    refine ⟨{(g : X), t}, Finset.card_le_two, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hgP
      · exact htP
    · intro x hx
      by_cases hxC : x ∈ C
      · exact hzp (hgz x hxC hx)
      · have hxt : x * t ∈ C := hcoset x t hxC htC
        have hxtz : x * t ∈ Subgroup.zpowers (g : X) := hgz _ hxt (P.mul_mem hx htP)
        have hmem := (Subgroup.closure (({(g : X), t} : Finset X) : Set X)).mul_mem (hzp hxtz)
          ((Subgroup.closure (({(g : X), t} : Finset X) : Set X)).inv_mem htcl)
        simpa using hmem
  · push Not at ht
    refine ⟨{(g : X)}, by simp, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hy
      rw [hy]
      exact hgP
    · intro x hx
      have hzp : Subgroup.zpowers (g : X) ≤
          Subgroup.closure (({(g : X)} : Finset X) : Set X) :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      exact hzp (hgz x (ht x hx) hx)

theorem twoGen_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : TwoGenSubgroups Y) : TwoGenSubgroups X := by
  intro P
  obtain ⟨s, hs, hcl⟩ := hY (P.map e.toMonoidHom)
  have hmap : (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
    rw [Subgroup.map_map]
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
      ext x
      simp
    rw [hid, Subgroup.map_id]
  have key : Subgroup.closure ((e.symm : Y → X) '' (s : Set Y)) = P := by
    rw [← hmap, ← hcl]
    exact (MonoidHom.map_closure e.symm.toMonoidHom (s : Set Y)).symm
  refine ⟨s.map e.symm.toEmbedding, (Finset.card_map _).le.trans hs, ?_⟩
  rw [Finset.coe_map]
  exact key

theorem exists_two_gen_of_le {G : Type*} [Group G] (H : Subgroup G) (hH : TwoGenSubgroups ↥H)
    (P : Subgroup G) (hP : P ≤ H) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = P := by
  classical
  obtain ⟨s, hs, hcl⟩ := hH (P.subgroupOf H)
  have key : Subgroup.closure ((H.subtype : ↥H → G) '' (s : Set ↥H)) = P := by
    rw [← MonoidHom.map_closure, hcl, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP]
  refine ⟨s.image Subtype.val, (Finset.card_image_le).trans hs, ?_⟩
  rw [Finset.coe_image]
  exact key

theorem twoGen_dihedral (m : ℕ) [NeZero m] : TwoGenSubgroups (DihedralGroup m) := by
  classical
  have hr : ∀ i : ZMod m,
      DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) := by
    intro i
    have h : DihedralGroup.r i = (DihedralGroup.r 1 : DihedralGroup m) ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [h]
    exact pow_mem (Subgroup.mem_zpowers _) _
  have hcoset : ∀ x y : DihedralGroup m,
      x ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) →
      y ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) →
      x * y ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) := by
    intro x y hx hy
    cases x with
    | r i => exact absurd (hr i) hx
    | sr i =>
      cases y with
      | r j => exact absurd (hr j) hy
      | sr j =>
        rw [DihedralGroup.sr_mul_sr]
        exact hr _
  haveI : IsCyclic ↥(Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m)) :=
    Subgroup.isCyclic_zpowers _
  exact fun P => exists_two_gen_of_cyclic_coset _ hcoset P

theorem twoGen_semidihedral (n : ℕ) (hn : 4 ≤ n) :
    TwoGenSubgroups (CFSG.Open.SemidihedralGroup n) := by
  have hcoset : ∀ x y : CFSG.Open.SemidihedralGroup n,
      x ∉ CFSG.Semidihedral.rotationSubgroup n →
      y ∉ CFSG.Semidihedral.rotationSubgroup n →
      x * y ∈ CFSG.Semidihedral.rotationSubgroup n :=
    fun _ _ hx hy =>
      mul_mem_of_notMem_of_index_two (CFSG.Semidihedral.rotationSubgroup_index n (by omega)) hx hy
  haveI := CFSG.Semidihedral.rotationSubgroup_cyclic n
  exact fun P => exists_two_gen_of_cyclic_coset _ hcoset P

theorem twoGen_of_sylow {G : Type} [Group G] [Finite G] (T S : Sylow 2 G) {X : Type} [Group X]
    (eT : ↥(T : Subgroup G) ≃* X) (hX : TwoGenSubgroups X) :
    TwoGenSubgroups ↥(S : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hSeq : (S : Subgroup G) = (T : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] <;> rfl
  let eS : ↥(S : Subgroup G) ≃* ↥(T : Subgroup G) :=
    (MulEquiv.subgroupCongr hSeq).trans
      (Subgroup.equivMapOfInjective (T : Subgroup G) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  exact twoGen_of_mulEquiv (eS.trans eT) hX

theorem twoGen_of_isPGroup {G : Type} [Group G] [Finite G]
    (h : HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G) {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hS : TwoGenSubgroups ↥(S : Subgroup G) := by
    rcases h with ⟨T, n, -, ⟨eT⟩⟩ | ⟨T, n, hn, ⟨eT⟩⟩
    · haveI : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
      exact twoGen_of_sylow T S eT (twoGen_dihedral (2 ^ (n - 1)))
    · exact twoGen_of_sylow T S eT (twoGen_semidihedral n hn)
  exact exists_two_gen_of_le (S : Subgroup G) hS P hPS

theorem frattini_quotient_elementary_of_rank_le_two {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hrank : Group.rank Q ≤ 2) :
    ∃ d : ℕ, d ≤ 2 ∧ Nat.card (Q ⧸ frattini Q) = 2 ^ d ∧
      (∀ a b : Q ⧸ frattini Q, a * b = b * a) ∧ ∀ a : Q ⧸ frattini Q, a ^ 2 = 1 := by
  obtain ⟨-, hcomm, hpow, helem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  have hcard := CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := 2) (Q ⧸ frattini Q)
  refine ⟨CFSG.generatorRank (Q ⧸ frattini Q), ?_, hcard, fun a b => hcomm.is_comm.comm a b,
    hpow⟩
  rw [CFSG.generatorRank_eq_group_rank]
  exact (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini Q))
    (QuotientGroup.mk'_surjective _)).trans hrank

theorem card_mulAut_frattini_quotient_dvd_six {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hrank : Group.rank Q ≤ 2) : Nat.card (MulAut (Q ⧸ frattini Q)) ∣ 6 := by
  obtain ⟨d, hd, hcard, hcomm, hpow⟩ := frattini_quotient_elementary_of_rank_le_two hQ hrank
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  exact CFSG.ClassicalInvolution.Q3.GL4Two.prod_dvd_of_le_two hd

theorem le_one_of_prime_pow_dvd_six {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : r ^ k ∣ 6) :
    k ≤ 1 := by
  by_contra hk
  have h2 : r ^ 2 ∣ 6 := (pow_dvd_pow r (by omega)).trans h
  have hle : r ^ 2 ≤ 6 := Nat.le_of_dvd (by norm_num) h2
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have h9 : 9 ≤ r ^ 2 := by nlinarith
  exact absurd (h9.trans hle) (by norm_num)

theorem elemAbelian_oddPrime_rank_le_one {G : Type} [Group G] [Finite G]
    (h : HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G) (hchar : CFSG.Open.IsCharTwoType G)
    {M : Subgroup G} (hM : CFSG.Open.IsTwoLocal M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {E : Subgroup G} (hEM : E ≤ M) (hE : CFSG.Open.IsElemAbelian r E) {k : ℕ}
    (hk : Nat.card E = r ^ k) : k ≤ 1 := by
  have hQ : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
    CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 M
  obtain ⟨s, hs2, hs⟩ := twoGen_of_isPGroup h hQ
  have hrank : Group.rank (CFSG.Open.pCoreOf 2 M) ≤ 2 := by
    rw [← hs]
    exact (Subgroup.rank_closure_finset_le_card s).trans hs2
  obtain ⟨ψ, hψ⟩ :=
    CFSG.RankThree.PartOne.SectionalRank.exists_injective_hom_mulAut_frattini_quotient hQ
      (hEM.trans (CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 M)) hr hr2
      (fun x hx => hE.2 x hx)
      fun x hx hc => hchar M hM ⟨hEM hx, Subgroup.mem_centralizer_iff.2 hc⟩
  have hdvd := Subgroup.card_dvd_of_injective ψ hψ
  rw [hk] at hdvd
  exact le_one_of_prime_pow_dvd_six hr hr2
    (hdvd.trans (card_mulAut_frattini_quotient_dvd_six hQ hrank))

theorem evenRank_le_one_of_dihedral_or_semidihedral {G : Type} [Group G] [Finite G]
    (h : HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G) (hchar : CFSG.Open.IsCharTwoType G) :
    CFSG.Open.evenRank G ≤ 1 := by
  refine csSup_le' ?_
  rintro k ⟨p, H, hp, hp2, hH, rfl⟩
  refine csSup_le' ?_
  rintro j ⟨E, hEH, hE, hj⟩
  exact elemAbelian_oddPrime_rank_le_one h hchar hH hp hp2 hEH hE hj

end CFSG.GF2Type.Aschbacher1976Common
