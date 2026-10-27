module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

universe u

theorem map_subtype_normal_of_characteristic {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (K : Subgroup N) [hK : K.Characteristic] : (K.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hx
  have hmap := characteristic_iff_map_eq.mp hK (MulAut.conjNormal g)
  have hk' : MulAut.conjNormal g k ∈ K := by
    rw [← hmap]
    exact ⟨k, hk, rfl⟩
  exact ⟨_, hk', MulAut.conjNormal_apply g k⟩

theorem frattini_eq_pow_sup_commutator {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup p X) :
    frattini X = closure (Set.range fun x : X => x ^ p) ⊔ commutator X := by
  have : Fact (IsPGroup p X) := ⟨hX⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p), Subgroup.closure_union,
    closure_eq, sup_comm]

theorem frattini_quotient_le_map {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (N : Subgroup P) [N.Normal] :
    frattini (P ⧸ N) ≤ (frattini P).map (QuotientGroup.mk' N) := by
  rw [frattini_eq_pow_sup_commutator (hP.to_quotient N), frattini_eq_pow_sup_commutator hP,
    Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rw [closure_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨x ^ p, subset_closure ⟨x, rfl⟩, map_pow _ _ _⟩
  · rw [commutator_def, commutator_def, map_commutator,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

theorem p_group_Frattini_coinvariant_generator_bound {p : ℕ} [Fact p.Prime] {P : Type u}
    [Group P] [Finite P] (hP : IsPGroup p P) (N : Subgroup P) [N.Normal] {D : Subgroup P}
    (hD : D = (frattini N).map N.subtype ⊔ ⁅N, ⊤⁆) :
    (∀ (X : Type u) [Group X] [Finite X], IsPGroup p X →
      frattini X = closure (Set.range fun x : X => x ^ p) ⊔ commutator X) ∧
    D.Normal ∧ D ≤ N ∧
    (∃ _ : (D.subgroupOf N).Normal, CFSG.IsElementaryAbelian p (N ⧸ D.subgroupOf N)) ∧
    ∃ dP dQ dN : ℕ, Nat.card (P ⧸ frattini P) = p ^ dP ∧
      Nat.card ((P ⧸ N) ⧸ frattini (P ⧸ N)) = p ^ dQ ∧
      Nat.card (N ⧸ D.subgroupOf N) = p ^ dN ∧ dP ≤ dQ + dN ∧
      ∃ S : Finset P, S.card ≤ dQ + dN ∧ closure (S : Set P) = ⊤ := by
  classical
  subst hD
  have hPf : Fact (IsPGroup p P) := ⟨hP⟩
  have hNp : IsPGroup p N := hP.to_subgroup N
  have hNf : Fact (IsPGroup p N) := ⟨hNp⟩
  set D := (frattini N).map N.subtype ⊔ ⁅N, ⊤⁆ with hDdef
  have hD1n : ((frattini N).map N.subtype).Normal := map_subtype_normal_of_characteristic N _
  have hDn : D.Normal := Subgroup.sup_normal _ _
  have hDN : D ≤ N := sup_le (map_subtype_le _) (commutator_le_left N ⊤)
  have hDΦ : D ≤ frattini P := by
    refine sup_le ?_ ((commutator_mono le_top le_top).trans
      (CFSG.commutator_le_frattini_of_isPGroup (p := p)))
    rw [frattini_eq_pow_sup_commutator hNp, Subgroup.map_sup, MonoidHom.map_closure]
    refine sup_le ?_ ?_
    · rw [closure_le]
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact CFSG.pth_power_mem_frattini_of_isPGroup (p := p) (n : P)
    · rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
      exact (commutator_mono le_top le_top).trans
        (CFSG.commutator_le_frattini_of_isPGroup (p := p))
  have hDNn : (D.subgroupOf N).Normal := hDn.subgroupOf N
  have hEA : CFSG.IsElementaryAbelian p (N ⧸ D.subgroupOf N) := by
    have hcomm : IsMulCommutative (N ⧸ D.subgroupOf N) := by
      rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
      intro x hx
      rw [mem_subgroupOf]
      refine mem_sup_right ?_
      have : (x : P) ∈ ⁅N, N⁆ := by
        rw [← map_subtype_commutator]
        exact ⟨x, hx, rfl⟩
      exact commutator_mono le_rfl le_top this
    refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H n =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact mem_sup_left ⟨n ^ p, CFSG.pth_power_mem_frattini_of_isPGroup (p := p) n, rfl⟩
  obtain ⟨-, -, -, -, dP, hdP, ⟨e⟩⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  obtain ⟨-, -, -, -, dQ, hdQ, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient (hP.to_quotient N)
  obtain ⟨dN, hdN⟩ := (IsPGroup.iff_card).mp (hNp.to_quotient (D.subgroupOf N))
  have hΦn : (frattini P).Normal := inferInstance
  have hineq : (frattini P).index ≤ D.relIndex N * (frattini (P ⧸ N)).index := by
    have h1 := relIndex_mul_index (le_sup_right : frattini P ≤ N ⊔ frattini P)
    rw [relIndex_sup_right] at h1
    have h3 : (frattini P).relIndex N ≤ D.relIndex N :=
      relIndex_le_of_le_left hDΦ (by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    have h4 : (N ⊔ frattini P).index ≤ (frattini (P ⧸ N)).index := by
      have h5 : ((frattini P).map (QuotientGroup.mk' N)).index ≤ (frattini (P ⧸ N)).index :=
        index_antitone (frattini_quotient_le_map hP N)
      rwa [← index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), comap_map_eq,
        QuotientGroup.ker_mk', sup_comm] at h5
    rw [← h1]
    exact Nat.mul_le_mul h3 h4
  have hdPle : dP ≤ dQ + dN := by
    rw [index_eq_card, hdP, Subgroup.relIndex, index_eq_card, hdN, index_eq_card, hdQ,
      ← pow_add, add_comm dN] at hineq
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hineq
  refine ⟨fun X _ _ hX => frattini_eq_pow_sup_commutator hX, hDn, hDN, ⟨hDNn, hEA⟩, dP, dQ, dN,
    hdP, hdQ, hdN, hdPle, ?_⟩
  set g : Fin dP → P ⧸ frattini P := fun i => Additive.toMul (e.symm (Pi.single i 1)) with hg
  have hgen : closure (Set.range g) = ⊤ := by
    apply Subgroup.toAddSubgroup.injective
    rw [Subgroup.toAddSubgroup_closure, OrderIso.map_top]
    have hpre : (⇑Additive.toMul ⁻¹' Set.range g) =
        Set.range fun i : Fin dP => e.symm (Pi.single i 1) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_range, hg]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Additive.toMul.injective hi⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hpre, Set.range_comp' e.symm (fun i : Fin dP => (Pi.single i (1 : ZMod p))),
      show (⇑e.symm) = ⇑(e.symm.toAddMonoidHom) from rfl, ← AddMonoidHom.map_closure]
    have htop : AddSubgroup.closure (Set.range fun i : Fin dP => (Pi.single i (1 : ZMod p))) =
        ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [← Finset.univ_sum_single v]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      have : (Pi.single i (v i) : Fin dP → ZMod p) = (v i).val • Pi.single i 1 := by
        rw [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      rw [this]
      exact AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    rw [htop, AddSubgroup.map_top_of_surjective _ e.symm.surjective]
  set S : Finset P := Finset.univ.image fun i : Fin dP => (g i).out with hS
  refine ⟨S, (Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])).trans
    hdPle, ?_⟩
  apply CFSG.LocalAnalysis.ComponentInitial.frattini_generator_lifting
  convert hgen
  ext q
  simp only [hS, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image,
    Set.mem_range, exists_exists_eq_and, QuotientGroup.mk'_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (QuotientGroup.out_eq' (g i)).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, QuotientGroup.out_eq' (g i)⟩

end CFSG.LocalAnalysis.GorensteinLyons
