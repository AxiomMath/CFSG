module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOne

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Open
  CFSG.Blueprint.NativeSporadic

@[expose] def Co1Pair (G : Type) [Group G] (L K : Subgroup G) (u : G) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ Group.IsPerfect K ∧
    Nat.card K = 251596800

section Co1Local

theorem co1_equiv_GA {X : Type} [Group X] (h : IsSporadic X .Co1) : Nonempty (X ≃* GA) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans co1MatEquiv⟩

theorem co1_isSimpleGroup_of_isSporadic {X : Type} [Group X] (h : IsSporadic X .Co1) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co1.isSimpleGroup_Co1 e

theorem co1_exists_not_commute {X : Type} [Group X] (h : IsSporadic X .Co1) :
    ∃ a b : X, a * b ≠ b * a := by
  have hs := co1_isSimpleGroup_of_isSporadic h
  obtain ⟨e⟩ := h
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := X)
  have hcX : Nat.card X = 4157776806543360000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co1.card_Co1
  rw [hcX] at hp
  norm_num at hp

theorem co1_model {G : Type} [Group G] {L K : Subgroup G} {u : G} (hL : IsSporadic L .Co1)
    (hQ : Co1Pair G L K u) :
    ∃ Ψ : ↥L →* GL24, Function.Injective Ψ ∧ (∀ x, Ψ x ∈ GA) ∧
      (∀ y ∈ GA, ∃ x, Ψ x = y) ∧ Ψ ⟨u, hQ.1⟩ = A₁ := by
  obtain ⟨f⟩ := co1_equiv_GA hL
  have ha : orderOf (⟨u, hQ.1⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk, hQ.2.1]
  have hle : K.subgroupOf L ≤ Subgroup.centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  have hcK : Nat.card (K.subgroupOf L) = 251596800 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.2.2.1).toEquiv]
    exact hQ.2.2.2.2.2
  have hdvd : 251596800 ∣ Nat.card (Subgroup.centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcK] at this
  have hs : orderOf (f ⟨u, hQ.1⟩) = 2 := by rw [MulEquiv.orderOf_eq, ha]
  have hdvd' : 251596800 ∣ Nat.card (Subgroup.centralizer ({f ⟨u, hQ.1⟩} : Set GA)) := by
    rw [← card_centralizer_eq_of_mulEquiv_sub GA f]
    exact hdvd
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq GA f ⟨u, hQ.1⟩ a₁ (co1_isConj_a₁ hs hdvd')
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨe⟩ := exists_hom_of_mulEquiv_sub GA φ
  refine ⟨Ψ, hΨ, hΨL, hΨR, ?_⟩
  rw [hΨe, hφ]

theorem co1_two_subgroup_le {X : Type} [Group X] [Finite X] (f : X ≃* GA) {K' : Subgroup X}
    (hKperf : Group.IsPerfect K') (hKcard : Nat.card K' = 251596800) {S : Subgroup X}
    (hS : IsPGroup 2 S) (hSK : ∀ s ∈ S, ∀ k ∈ K', s * k = k * s) : Nat.card S ≤ 4 := by
  by_cases hS1 : S = ⊥
  · rw [hS1]
    simp
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).2 hS1
  have hcn : Nontrivial ↥(Subgroup.center ↥S) := hS.center_nontrivial
  have hpc : IsPGroup 2 ↥(Subgroup.center ↥S) := hS.to_subgroup _
  obtain ⟨n, hn0, hn⟩ := hpc.nontrivial_iff_card.mp inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥S)) 2 (by
    rw [hn]
    exact dvd_pow_self 2 hn0.ne')
  set t : X := (((t' : ↥(Subgroup.center ↥S)) : ↥S) : X) with htdef
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht']
  have htS : t ∈ S := ((t' : ↥(Subgroup.center ↥S)) : ↥S).2
  have htc : ∀ s ∈ S, s * t = t * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 t'.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hKt : K' ≤ Subgroup.centralizer ({t} : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hSK t htS k hk).symm
  have hdvd : 251596800 ∣ Nat.card (Subgroup.centralizer ({t} : Set X)) := by
    have := Subgroup.card_dvd_of_le hKt
    rwa [hKcard] at this
  have hs2 : orderOf (f t) = 2 := by rw [MulEquiv.orderOf_eq, ht2]
  have hdvd' : 251596800 ∣ Nat.card (Subgroup.centralizer ({f t} : Set GA)) := by
    rw [← card_centralizer_eq_of_mulEquiv_sub GA f]
    exact hdvd
  obtain ⟨ζ⟩ := exists_centralizer_mulEquiv GA f t a₁ (co1_isConj_a₁ hs2 hdvd')
  have hq := Quot2Data.comp_equiv_sub C₁ co1_quot2Data ζ
  have hperfK : Group.IsPerfect (K'.subgroupOf (Subgroup.centralizer ({t} : Set X))) :=
    isPerfect_subgroupOf_of_le hKt hKperf
  have hcardK : Nat.card (K'.subgroupOf (Subgroup.centralizer ({t} : Set X))) =
      Nat.card twoBD := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKt).toEquiv, hKcard, card_twoBD]
  have hcs : ∀ s ∈ S, s ∈ Subgroup.centralizer ({t} : Set X) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (htc s hs)
  have hker : ∀ s : S, ζ ⟨s.1, hcs s.1 s.2⟩ ∈ (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker := by
    intro s
    have h1 := hq.mem_ker_of_centralizes hperfK hcardK (fun y _ hy => co1_centralizer_trivial hy)
      (c := ⟨s.1, hcs s.1 s.2⟩) (fun k hk => Subtype.ext (hSK s.1 s.2 k.1
        (Subgroup.mem_subgroupOf.1 hk)))
    exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 h1)
  let F : S → (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker := fun s => ⟨ζ ⟨s.1, hcs s.1 s.2⟩, hker s⟩
  have hF : Function.Injective F := by
    intro a b hab
    have h1 : ζ ⟨a.1, hcs a.1 a.2⟩ = ζ ⟨b.1, hcs b.1 b.2⟩ := congrArg Subtype.val hab
    have h2 := ζ.injective h1
    exact Subtype.ext (Subtype.mk.inj h2)
  exact (Nat.card_le_card_of_injective F hF).trans co1_card_ker_le

theorem co1_twoAdic_centralizer {X : Type} [Group X] [Finite X] (f : X ≃* GA) {K' : Subgroup X}
    (hKperf : Group.IsPerfect K') (hKcard : Nat.card K' = 251596800) :
    twoAdic (Subgroup.centralizer (K' : Set X)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := Subgroup.centralizer (K' : Set X) with hC
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  set S : Subgroup X := (P : Subgroup ↥C).map C.subtype with hS
  have hSp : IsPGroup 2 S := P.isPGroup'.map C.subtype
  have hSK : ∀ s ∈ S, ∀ k ∈ K', s * k = k * s := by
    rintro _ ⟨c, -, rfl⟩ k hk
    exact (Subgroup.mem_centralizer_iff.1 c.2 k hk).symm
  have h4 := co1_two_subgroup_le f hKperf hKcard hSp hSK
  have hcardS : Nat.card S = 2 ^ twoAdic C := by
    rw [hS, Subgroup.card_map_of_injective C.subtype_injective, P.card_eq_multiplicity]
    rfl
  rw [hcardS] at h4
  by_contra hlt
  push Not at hlt
  have h8 : 2 ^ 3 ≤ 2 ^ twoAdic C := Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem solomonLocal_co1 {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .Co1) (hQ : Co1Pair G L K u) : SolomonLocal L K u := by
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := co1_model hL hQ
  obtain ⟨M⟩ := co1_outModel
  have hKL := hQ.2.2.1
  have hcardK : Nat.card (K.subgroupOf L) = 251596800 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hQ.2.2.2.2.2
  obtain ⟨eK⟩ := M.equiv_D hQ.1 hKL hQ.2.2.2.1 Ψ hΨ hΨL hΨu hQ.2.2.2.2.1
    (hQ.2.2.2.2.2.trans card_twoBD.symm)
  obtain ⟨f⟩ := co1_equiv_GA hL
  let eK' : ↥(K.subgroupOf L) ≃* ↥twoBD := (Subgroup.subgroupOfEquivOfLe hKL).trans eK
  have hquasi : CFSG.Open.IsQuasisimple ↥(K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv' eK'.symm
      (isQuasisimple_of_simple isSimpleGroup_twoBD ⟨xD, yD, xD_yD_ne⟩)
  have hperfK : Group.IsPerfect (K.subgroupOf L) := isPerfect_subgroupOf_of_le hKL hQ.2.2.2.2.1
  have hu2 : orderOf (⟨u, hQ.1⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk, hQ.2.1]
  have huC : (⟨u, hQ.1⟩ : ↥L) ∈ Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  have huniq : ∀ t : ↥L, orderOf t = 2 →
      t ∈ Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) →
      ∀ K'' : Subgroup ↥L, K'' ≤ Subgroup.centralizer ({t} : Set ↥L) → Group.IsPerfect K'' →
        Nat.card K'' = Nat.card (K.subgroupOf L) → K'' = K.subgroupOf L := by
    intro t ht2 htC K'' hK'' hperf'' hcard''
    have hKt : K.subgroupOf L ≤ Subgroup.centralizer ({t} : Set ↥L) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 htC k hk
    have hdvd : 251596800 ∣ Nat.card (Subgroup.centralizer ({t} : Set ↥L)) := by
      have := Subgroup.card_dvd_of_le hKt
      rwa [hcardK] at this
    have hs2 : orderOf (f t) = 2 := by rw [MulEquiv.orderOf_eq, ht2]
    have hdvd' : 251596800 ∣ Nat.card (Subgroup.centralizer ({f t} : Set GA)) := by
      rw [← card_centralizer_eq_of_mulEquiv_sub GA f]
      exact hdvd
    obtain ⟨ζ⟩ := exists_centralizer_mulEquiv GA f t a₁ (co1_isConj_a₁ hs2 hdvd')
    have hq := Quot2Data.comp_equiv_sub C₁ co1_quot2Data ζ
    have hperfK' : Group.IsPerfect ((K.subgroupOf L).subgroupOf (Subgroup.centralizer
        ({t} : Set ↥L))) :=
      isPerfect_subgroupOf_of_le hKt hperfK
    have hcardK' : Nat.card ((K.subgroupOf L).subgroupOf (Subgroup.centralizer
        ({t} : Set ↥L))) = Nat.card twoBD := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKt).toEquiv, hcardK, card_twoBD]
    have hcard2 : Nat.card (K''.subgroupOf (Subgroup.centralizer ({t} : Set ↥L))) =
        Nat.card twoBD := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'').toEquiv, hcard'', hcardK, card_twoBD]
    have heq := hq.eq_of_perfect hperfK' hcardK' (isPerfect_subgroupOf_of_le hK'' hperf'')
      hcard2
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hK'', inf_eq_left.2 hKt] at heq
    exact heq
  have hcent : twoAdic (Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) <
      twoAdic (K.subgroupOf L) := by
    have h1 := co1_twoAdic_centralizer f hperfK hcardK
    have h2 : twoAdic (K.subgroupOf L) = 12 := by
      unfold twoAdic
      rw [hcardK, show (251596800 : ℕ) = 2 ^ 12 * 61425 by norm_num]
      exact factorization_two_pow_mul 12 (by norm_num) (by norm_num)
    omega
  have hinn : ∀ α : MulAut ↥L, ∃ c : ↥L, ∀ x, α x = c * x * c⁻¹ := by
    intro α
    obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.TwoCo1.HypOne.allInner_of_isSporadic hL α
    exact ⟨g, fun x => by rw [hg]; rfl⟩
  exact
  { simpleL := co1_isSimpleGroup_of_isSporadic hL
    nonabelianL := co1_exists_not_commute hL
    u_order := hQ.2.1
    u_mem := hQ.1
    K_le := hKL
    u_mem_centralizer_K := Subgroup.mem_centralizer_iff.2 fun k hk => hQ.2.2.2.1 k hk
    standard_in_L := standard_of_unique hquasi hu2 huC huniq hcent
    autCentralizer_two := (twoAdic_autCentralizer_le_of_allInner hinn).trans
      (co1_twoAdic_centralizer f hperfK hcardK) }

end Co1Local

end CFSG.EvenSporadicStandard.Solomon78
