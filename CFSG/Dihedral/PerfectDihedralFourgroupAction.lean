module

public import CFSG.Dihedral.BlueprintDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public noncomputable section

namespace CFSG.GorensteinWalter

universe u

@[expose] def kleinFourAutPuncturedEquiv (V : Type u) [Group V] [IsKleinFour V] :
    MulAut V ≃* Equiv.Perm {v : V // v ≠ 1} := by
  classical
  let f : MulAut V →* Equiv.Perm {v : V // v ≠ 1} := {
    toFun := fun a => Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
    map_one' := by ext v; rfl
    map_mul' := by intro a b; ext v; rfl }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    ext v
    by_cases hv : v = 1
    · simp [hv]
    · exact congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)
  · intro p
    let e := Equiv.Perm.ofSubtype p
    have he : e 1 = 1 := by
      exact Equiv.Perm.ofSubtype_apply_of_not_mem p (by simp)
    refine ⟨IsKleinFour.mulEquiv e he, ?_⟩
    ext v
    exact Equiv.Perm.ofSubtype_apply_coe p v

theorem kleinFourAut_card (V : Type u) [Group V] [IsKleinFour V] :
    Nat.card (MulAut V) = 6 := by
  classical
  let : Finite V := Nat.finite_of_card_ne_zero (by
    rw [IsKleinFour.card_four (G := V)]; decide)
  let : Fintype V := Fintype.ofFinite V
  have hthree : Fintype.card {v : V // v ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {v : V // v = 1} = 1 := by simp
    rw [hone, IsKleinFour.card_four']
  rw [Nat.card_congr (kleinFourAutPuncturedEquiv V).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, hthree]
  decide

def kleinFourAutSymmetricThreeEquiv (V : Type u) [Group V] [IsKleinFour V] :
    MulAut V ≃* Equiv.Perm (Fin 3) := by
  classical
  let : Finite V := Nat.finite_of_card_ne_zero (by
    rw [IsKleinFour.card_four (G := V)]; decide)
  let : Fintype V := Fintype.ofFinite V
  have hthree : Fintype.card {v : V // v ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {v : V // v = 1} = 1 := by simp
    rw [hone, IsKleinFour.card_four']
  exact (kleinFourAutPuncturedEquiv V).trans
    (Equiv.permCongrHom (Fintype.equivFinOfCardEq hthree))

private theorem perfect_no_normal_indexTwo
    {G : Type u} [Group G] [Finite G] [Group.IsPerfect G] :
    ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  rintro ⟨N, hN, hindex⟩
  let : N.Normal := hN
  have hcard : Nat.card (G ⧸ N) = 2 := by
    simpa only [Subgroup.index_eq_card] using hindex
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  let : IsMulCommutative (G ⧸ N) := inferInstance
  have hsub : Subsingleton (G ⧸ N) := inferInstance
  have hone : Nat.card (G ⧸ N) = 1 := by
    let : Subsingleton (G ⧸ N) := hsub
    exact Nat.card_unique
  omega

theorem kleinFourAut_subgroup_eq_top
    (V : Type u) [Group V] [IsKleinFour V]
    (A : Subgroup (MulAut V)) (a b : MulAut V)
    (ha : a ∈ A) (ha2 : a ^ 2 ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) : A = ⊤ := by
  classical
  let : Finite V := Nat.finite_of_card_ne_zero (by
    rw [IsKleinFour.card_four (G := V)]; decide)
  have hdiv : Nat.card A ∣ 6 := by
    rw [← kleinFourAut_card V]
    exact Subgroup.card_subgroup_dvd_card A
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hle : Nat.card A ≤ 6 := Nat.le_of_dvd (by decide) hdiv
  have hcases : Nat.card A = 1 ∨ Nat.card A = 2 ∨
      Nat.card A = 3 ∨ Nat.card A = 6 := by
    interval_cases Nat.card A <;> simp_all
  have haA : (⟨a, ha⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
  have hbA : (⟨b, hb⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
  have haG : a ^ Nat.card A = 1 := congrArg Subtype.val haA
  have hbG : b ^ Nat.card A = 1 := congrArg Subtype.val hbA
  rcases hcases with hc | hc | hc | hc
  · rw [hc, pow_one] at haG
    exact (ha2 (by simp [haG])).elim
  · rw [hc] at haG
    exact (ha2 haG).elim
  · have hb3 : b ^ 3 = 1 := by simpa only [hc] using hbG
    have hbfix : b = 1 := by
      simpa only [pow_succ, hb2, one_mul] using hb3
    exact (hb1 hbfix).elim
  · apply Subgroup.eq_top_of_card_eq
    exact hc.trans (kleinFourAut_card V).symm

theorem perfect_dihedral_fourgroup_normalizer_surjective
    {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (V : Subgroup G) (hVS : V ≤ (S : Subgroup G)) (hV : IsKleinFour V) :
    Function.Surjective V.normalizerMonoidHom := by
  classical
  let : IsKleinFour V := hV
  have hdihedral : HasDihedralSylowTwo G := by
    intro T
    exact ⟨m, by omega, ⟨(Sylow.equiv S T).symm.trans e⟩⟩
  have hprime := (case1_no_index_two_fusion_and_normalizer
    hdihedral perfect_no_normal_indexTwo).2 S V hVS hV
  obtain ⟨x, hxN, hx2⟩ := (normalizerContainsCPrime_iff_exists V).mp hprime
  let a : MulAut V := V.normalizerMonoidHom ⟨x, hxN⟩
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have hker : (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ∈
        V.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact h
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    exact hx2 hker
  obtain ⟨y, hyS, hyN, hyfix, hymove, _hyall⟩ :=
    exists_dihedral_transposition_of_kleinFour_le_sylow S hm e hVS hV
  obtain ⟨v, hvV, hv1, hvz, _hv2, hzV⟩ :=
    exists_noncentral_of_kleinFour_le_sylow S hm e hVS hV
  let b : MulAut V := V.normalizerMonoidHom ⟨y, hyN⟩
  let z : V := ⟨zAmbient S e, hzV⟩
  have hz1 : z ≠ 1 := by
    intro h
    exact zAmbient_ne_one S (by omega) e (congrArg Subtype.val h)
  have hbfix : b z = z := Subtype.ext hyfix
  have hb2 : b ^ 2 = 1 := mulAut_sq_eq_one_of_fixed_ne_one b hz1 hbfix
  have hb1 : b ≠ 1 := by
    intro h
    have hfix := congrArg Subtype.val (DFunLike.congr_fun h (⟨v, hvV⟩ : V))
    exact hymove V hVS hV v hvV hv1 hvz hfix
  have hrange : V.normalizerMonoidHom.range = ⊤ :=
    kleinFourAut_subgroup_eq_top V V.normalizerMonoidHom.range a b
      ⟨⟨x, hxN⟩, rfl⟩ ha2 ⟨⟨y, hyN⟩, rfl⟩ hb1 hb2
  exact MonoidHom.range_eq_top.mp hrange

theorem perfect_dihedral_fourgroup_fullAutomorphismImage
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (V : Subgroup G) (hVS : V ≤ (S : Subgroup G)) (hV : IsKleinFour V) :
    DihedralBlueprint.FullAutomorphismImage (Subgroup.normalizer (V : Set G)) V := by
  intro a
  obtain ⟨x, hx⟩ := perfect_dihedral_fourgroup_normalizer_surjective S hm e V hVS hV a
  refine ⟨x, x.property, ?_⟩
  intro v
  exact (congrArg Subtype.val (DFunLike.congr_fun hx v)).symm

def perfect_dihedral_fourgroup_normalizer_quotient
    {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (V : Subgroup G) (hVS : V ≤ (S : Subgroup G)) (hV : IsKleinFour V) :
    (Subgroup.normalizer (V : Set G) ⧸
      (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))) ≃*
        Equiv.Perm (Fin 3) := by
  let : IsKleinFour V := hV
  have hsurj := perfect_dihedral_fourgroup_normalizer_surjective S hm e V hVS hV
  have hker := Subgroup.normalizerMonoidHom_ker V
  exact (QuotientGroup.congr _ _ (MulEquiv.refl _) (by
    change ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))).map (MonoidHom.id _) = _
    rw [Subgroup.map_id]
    exact hker.symm)).trans
    ((QuotientGroup.quotientKerEquivOfSurjective V.normalizerMonoidHom hsurj).trans
      (kleinFourAutSymmetricThreeEquiv V))

end CFSG.GorensteinWalter
