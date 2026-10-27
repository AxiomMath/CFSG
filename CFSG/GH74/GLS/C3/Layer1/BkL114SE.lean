module

public import CFSG.GH74.GLS.C3.Layer1.BkL114
public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

@[expose] def NW (x : G) : Subgroup G :=
  normalizer ((pPrimeCoreOf 2 (centralizer ({x} : Set G)) : Subgroup G) : Set G)

omit [Group G] in
theorem isSolvable_normalizer_sylow_two {X : Type*} [Group X] [Finite X] (S : Sylow 2 X) :
    Group.IsSolvable ↥(normalizer ((S : Subgroup X) : Set X)) := by
  set N := normalizer ((S : Subgroup X) : Set X) with hN
  have hSN : (S : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hTn : ((S : Subgroup X).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hS : Group.IsSolvable ↥(S : Subgroup X) := by
    have := S.isPGroup'.isNilpotent
    infer_instance
  have hT : Group.IsSolvable ↥((S : Subgroup X).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hSN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSN).injective
  have hodd : Odd (Nat.card (↥N ⧸ (S : Subgroup X).subgroupOf N)) := by
    change Odd ((S : Subgroup X).relIndex N)
    refine Nat.not_even_iff_odd.1 fun he => S.not_dvd_index ?_
    exact dvd_trans (even_iff_two_dvd.1 he) (Subgroup.relIndex_dvd_index_of_le hSN)
  have hQ : Group.IsSolvable (↥N ⧸ (S : Subgroup X).subgroupOf N) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range ((S : Subgroup X).subgroupOf N).subtype
    (QuotientGroup.mk' ((S : Subgroup X).subgroupOf N))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

omit [Group G] in
theorem isSolvable_centralizer_of_isBenderGroup {X : Type} [Group X] [Finite X]
    (hX : CFSG.BenderSuzuki.IsBenderGroup X) {t : X} (ht : orderOf t = 2) :
    Group.IsSolvable ↥(centralizer ({t} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 ↥(zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht]
    norm_num
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have htQ : t ∈ (Q : Subgroup X) := hQ (mem_zpowers t)
  have hSE := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hX Q
  have htN : t ∈ normalizer ((Q : Subgroup X) : Set X) := Subgroup.le_normalizer htQ
  have hle : centralizer ({t} : Set X) ≤ normalizer ((Q : Subgroup X) : Set X) := by
    intro g hg
    by_contra hgN
    have hodd := hSE.2.2 g hgN
    have hgt : g * t * g⁻¹ = t := by
      have := mem_centralizer_singleton_iff.1 hg
      rw [this]
      group
    have h1 : t ∈ (normalizer ((Q : Subgroup X) : Set X)).map (MulAut.conj g).toMonoidHom :=
      ⟨t, htN, by simpa [MulAut.conj_apply] using hgt⟩
    have h2 := Subgroup.orderOf_dvd_natCard _ (mem_inf.2 ⟨htN, h1⟩)
    rw [ht] at h2
    exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 hodd)
  have hsol := isSolvable_normalizer_sylow_two Q
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

omit [Group G] in
theorem alt_not_isSolvable (n : ℕ) (hn : n = 5 ∨ n = 7) :
    ¬ Group.IsSolvable (alternatingGroup (Fin n)) := by
  have hsimp : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> simp)
  intro hs
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin n))).2 hs
  let _ : CommGroup (alternatingGroup (Fin n)) :=
    { (inferInstance : Group (alternatingGroup (Fin n))) with mul_comm := hcomm }
  have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin n))
  rcases hn with rfl | rfl
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hp
    simp [Nat.factorial] at hp
    norm_num at hp
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hp
    simp [Nat.factorial] at hp
    norm_num at hp

@[expose] def B_L114_SE57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({5, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfigW n x K T Q S a → S = T ⊔ zpowers a →
      a ∈ NW x → pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥ →
        CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (NW x)

theorem false_of_isStronglyEmbeddedOrder_NW
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {n : ℕ} (hn : n = 5 ∨ n = 7) {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a)
    (hN : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (NW x)) : False := by
  have hB := CFSG.BenderSuzuki.bender_suzuki (NW x) hN
  have hsol := isSolvable_centralizer_of_isBenderGroup hB h.x_order
  have hKsol : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h.K_le_C)
      (Subgroup.inclusion_injective h.K_le_C)
  have hq : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := h.kbar
  have hA : Group.IsSolvable (alternatingGroup (Fin n)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact alt_not_isSolvable n hn hA

theorem b_L114_final57_of_SE (hSE : B_L114_SE57) :
    B_L114_final57 := by
  intro G _ _ hG n hn x K T Q S a h hS ha
  by_contra hW
  have hsimp : IsSimpleGroup G := (isKProperSimple_iff.1 hG.kproper).1
  have hn' : n = 5 ∨ n = 7 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  haveI : IsSimpleGroup G := hsimp
  exact false_of_isStronglyEmbeddedOrder_NW hn' h
    (hSE G hG n hn x K T Q S a h hS ha hW)

end CFSG.GH74.GLS.C3.Layer1.Bk
