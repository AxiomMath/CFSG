module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearGenerated
public import CFSG.Walter.Bender1970

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open scoped MatrixGroups

theorem alternatingGroup_five_not_isSolvable :
    ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  have := alternatingGroup.isSimpleGroup (α := Fin 5) (by rw [Nat.card_fin])
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr h
  have ha : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 5) :=
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide)
      (by decide)).mem_alternatingGroup
  have hb : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 3 ∈ alternatingGroup (Fin 5) :=
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide)
      (by decide)).mem_alternatingGroup
  have hne : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) * (Equiv.swap 0 1 * Equiv.swap 0 3) ≠
      (Equiv.swap 0 1 * Equiv.swap 0 3) * (Equiv.swap 0 1 * Equiv.swap 0 2) := by decide
  exact hne (congrArg Subtype.val (hcomm ⟨_, ha⟩ ⟨_, hb⟩))

theorem even_card_psl_two_odd {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f) :
    Even (Nat.card (PSL(2, GaloisField p f))) := by
  have hne : (-1 : GaloisField p f) ≠ 1 := by
    refine Ring.neg_one_ne_one_of_char_ne_two ?_
    rw [ringChar.eq (GaloisField p f) p]
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hp) even_two
  have hc := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hne
  have h := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := GaloisField p f)
  rw [hc, GaloisField.card p f (by omega)] at h
  obtain ⟨k, hk⟩ := hp.pow (n := f)
  rw [hk, show (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) from
    Nat.sub_eq_of_eq_add (by ring)] at h
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  exact ⟨(2 * k + 1) * 2 * j, by rw [hj] at h; linarith⟩

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

theorem JankoConfiguration.hasAbelianSylowTwo (hconf : JankoConfiguration G S z) :
    CFSG.Walter.HasAbelianSylowTwo G :=
  CFSG.Walter.hasAbelianSylowTwo_of_sylow S ⟨⟨fun a b => Subtype.ext (hconf.abelian _ a.2 _ b.2)⟩⟩

theorem JankoConfiguration.not_isSolvable_centralizer (hconf : JankoConfiguration G S z) :
    ¬ Group.IsSolvable (Subgroup.centralizer ({z} : Set G)) := by
  intro hsolv
  obtain ⟨J, -, ⟨e⟩, -, -⟩ := hconf.quotient
  have : Group.IsSolvable (EscapingQuotient z) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective J.subtype_injective
  exact alternatingGroup_five_not_isSolvable
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem oddCore_centralizer_eq_bot_of_isTypeJR (hJR : CFSG.Walter.IsTypeJR G) {t : G}
    (ht : orderOf t = 2) : pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  obtain ⟨-, p, f, hp, L, hpodd, hf, h5, hLC, hLn, ⟨e⟩, hCL⟩ := hJR.2.2 t ht
  set C := Subgroup.centralizer ({t} : Set G)
  set O := pPrimeCore 2 C
  set L' := L.subgroupOf C
  have hO : Odd (Nat.card O) := escaping_oddCore_odd t
  let e' : L' ≃* PSL(2, GaloisField p f) := (Subgroup.subgroupOfEquivOfLe hLC).trans e
  have hL'even : Even (Nat.card L') := by
    rw [Nat.card_congr e'.toEquiv]
    exact even_card_psl_two_odd hpodd hf
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hsimple : IsSimpleGroup L' := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := GaloisField p f) 2 le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
    exact e'.isSimpleGroup
  have hL'n : L'.Normal := hLn
  have hOL : O ⊓ L' = ⊥ := by
    have hN : ((O ⊓ L').subgroupOf L').Normal := Subgroup.Normal.subgroupOf inferInstance L'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O ⊓ L').subgroupOf L') with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
    · exfalso
      have hle : L' ≤ O := (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left
      have hodd : Odd (Nat.card L') := Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le hle)
      exact (Nat.not_even_iff_odd.mpr hodd) hL'even
  have hcomm : ⁅O, L'⁆ = ⊥ := le_bot_iff.mp (hOL ▸ Subgroup.commutator_le_inf O L')
  have hOcent : O ≤ Subgroup.centralizer L' :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  refine eq_bot_iff.mpr fun o ho => ?_
  have hoL : (o : G) ∈ C ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨o.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp (hOcent ho) ⟨l, hLC hl⟩
      (Subgroup.mem_subgroupOf.mpr hl)
    exact congrArg Subtype.val h
  rw [hCL] at hoL
  have h1 : orderOf (o : G) ∣ 2 := ht ▸ orderOf_dvd_of_mem_zpowers hoL
  have h2 : Odd (orderOf (o : G)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O ho)
  have h3 : orderOf (o : G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) (by decide)
  rw [orderOf_eq_one_iff] at h3
  exact Subgroup.mem_bot.mpr (Subtype.ext h3)

theorem centralOddCoreTrivial :
    CentralOddCoreTrivial := by
  intro G _ _ S H z hset hz hesc hconf
  have := hset.simple
  have hab := hconf.hasAbelianSylowTwo
  have hrank : 3 ≤ CFSG.Open.twoRank G := by
    rw [← CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq S]
    exact hset.rank
  have hSC := CFSG.Walter.simpleCaseHyp_of_benderHyp CFSG.Walter.benderHyp
  rcases CFSG.Walter.benderHyp G hset.simple hset.nonabelian hab hrank
      (fun K _ => CFSG.Walter.isAStar_of_hasAbelianSylowTwo hSC (hab.subgroup K)) with
    hJR | ⟨M, hM⟩
  · exact oddCore_centralizer_eq_bot_of_isTypeJR hJR hz.2.1
  · exfalso
    obtain ⟨q, k, hB⟩ :=
      isBenderGroup_exists_fusionBenderBorel (CFSG.BenderSuzuki.bender_suzuki M hM)
    have hCN : Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      involution_centralizer_le_of_fusionStronglyEmbedded (hB S).1 (Subgroup.le_normalizer hz.1)
        hz.2.1
    have := isSolvable_normalizer_sylow S
    exact hconf.not_isSolvable_centralizer
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCN))

theorem jankoConfigurationJOne :
    JankoConfigurationJOne :=
  jankoConfigurationJOne_of_oddCore centralOddCoreTrivial

end CFSG.ProperTwoGeneratedCore.Lemma37
