module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLie
import CFSG.RankThree.OddKernel.FailureReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree Subgroup
open scoped commutatorElement

@[expose] def wPre {Y : Type} [Group Y] (P : Subgroup Y) : Subgroup Y :=
  ((wSup (↥P ⧸ CFSG.pCore 2 ↥P)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).map P.subtype

theorem wPre_le {Y : Type} [Group Y] (P : Subgroup Y) : wPre P ≤ P :=
  map_subtype_le _

variable {G : Type} [Group G] [Finite G]

theorem exists_inner_jZero_of_inner_wPre {M H L : Subgroup G} (hX : H ⊓ L ≤ M) {b : G}
    (hb : b ∈ M) (hbX : b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (h : ∃ v ∈ wPre (barM M (H ⊓ L)), ∀ w ∈ wPre (barM M (H ⊓ L)),
      ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * v, w⁆ ∈ pCoreOf 2 (barM M (H ⊓ L))) :
    ∃ j ∈ jZero H L, ∀ x ∈ jZero H L, ⁅j⁻¹ * b, x⁆ ∈ pCoreOf 2 (jZero H L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := H ⊓ L with hXdef
  set P := barM M X with hP
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set J := jZero H L with hJ
  have hJX : J ≤ X := jZero_le H L
  have hbJ : b ∈ normalizer (J : Set G) := le_normalizer_jZero H L hbX
  have hbP : mk ⟨b, hb⟩ ∈ normalizer (P : Set _) :=
    TenThreeThree.mem_normalizer_barM (X := X) hb hbX
  have hPO : ∀ y ∈ P, y ∈ normalizer (pCoreOf 2 P : Set _) := fun y hy =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (le_normalizer hy)
  obtain ⟨v, hv, hvw⟩ := h
  obtain ⟨v', hv', rfl⟩ := hv
  have hvW : hatHom M X hX ⁻¹' {QuotientGroup.mk' (CFSG.pCore 2 ↥P) v'} ∩
      ((J.subgroupOf X : Subgroup ↥X) : Set ↥X) ≠ ∅ := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥P) v' ∈
        (J.subgroupOf X).map (hatHom M X hX) := by
      rw [map_jZero_eq_wSup M H L hX]
      exact hv'
    obtain ⟨x₀, hx₀, hx₀v⟩ := h1
    exact Set.nonempty_iff_ne_empty.mp ⟨x₀, hx₀v, hx₀⟩
  obtain ⟨x₀, hx₀v, hx₀J⟩ := Set.nonempty_iff_ne_empty.mpr hvW
  have hx₀v' : hatHom M X hX x₀ = QuotientGroup.mk' (CFSG.pCore 2 ↥P) v' := hx₀v
  have hj'J : (x₀ : G) ∈ J := hx₀J
  have hoO : (barHom M X hX x₀)⁻¹ * v' ∈ CFSG.pCore 2 ↥P := by
    rw [hatHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hx₀v'
    exact hx₀v'
  set j' : G := (x₀ : G) with hj'
  have hj'M : j' ∈ M := hX x₀.2
  set u : ↥M ⧸ CFSG.pCore 2 ↥M := ((barHom M X hX x₀ : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M) with hu
  have hu' : u = mk ⟨j', hj'M⟩ := rfl
  have huP : u ∈ P := (barHom M X hX x₀).2
  set o : ↥M ⧸ CFSG.pCore 2 ↥M := u⁻¹ * (v' : ↥M ⧸ CFSG.pCore 2 ↥M) with ho
  have hoP : o ∈ pCoreOf 2 P := ⟨_, hoO, by simp [ho, hu]⟩
  have hcM : b * j' ∈ M := M.mul_mem hb hj'M
  set c := mk ⟨b * j', hcM⟩ with hc
  have hcbu : c = mk ⟨b, hb⟩ * u := by
    rw [hc, hu']
    rw [← map_mul]
    rfl
  have hcP : c ∈ normalizer (P : Set _) := by
    rw [hcbu]
    exact mul_mem hbP (le_normalizer huP)
  have hcO : c ∈ normalizer (pCoreOf 2 P : Set _) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P hcP
  have hbv : mk ⟨b, hb⟩ * (v' : ↥M ⧸ CFSG.pCore 2 ↥M) = c * o := by
    rw [hcbu, ho]
    group
  have hcw : ∀ w ∈ wPre P, c * w * c⁻¹ * w⁻¹ ∈ pCoreOf 2 P := by
    intro w hw
    have hwP : w ∈ P := wPre_le P hw
    have h1 : mk ⟨b, hb⟩ * (v' : ↥M ⧸ CFSG.pCore 2 ↥M) * w *
        (mk ⟨b, hb⟩ * (v' : ↥M ⧸ CFSG.pCore 2 ↥M))⁻¹ * w⁻¹ ∈ pCoreOf 2 P := hvw w hw
    rw [hbv] at h1
    have h2 : o * w * o⁻¹ * w⁻¹ ∈ pCoreOf 2 P := by
      have h4 : w * o⁻¹ * w⁻¹ ∈ pCoreOf 2 P :=
        (mem_normalizer_iff.mp (hPO w hwP) o⁻¹).mp (inv_mem hoP)
      have e : o * w * o⁻¹ * w⁻¹ = o * (w * o⁻¹ * w⁻¹) := by group
      rw [e]
      exact mul_mem hoP h4
    have h3 : c * (o * w * o⁻¹ * w⁻¹) * c⁻¹ ∈ pCoreOf 2 P :=
      (mem_normalizer_iff.mp hcO _).mp h2
    have e : c * w * c⁻¹ * w⁻¹ =
        (c * (o * w * o⁻¹ * w⁻¹) * c⁻¹)⁻¹ * (c * o * w * (c * o)⁻¹ * w⁻¹) := by
      group
    rw [e]
    exact mul_mem (inv_mem h3) h1
  have hcore : pCoreOf 2 X ⊓ J ≤ pCoreOf 2 J := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ inf_le_right ?_
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X).to_le inf_le_left)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X (hJX hj)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hj) y
    exact (Subgroup.mem_inf.trans (and_congr h1 h2)).trans Subgroup.mem_inf.symm
  have hcX : b * j' ∈ normalizer (X : Set G) := mul_mem hbX (le_normalizer x₀.2)
  have hcJ : b * j' ∈ normalizer (J : Set G) := mul_mem hbJ (le_normalizer hj'J)
  refine ⟨b * j'⁻¹ * b⁻¹, (mem_normalizer_iff.mp hbJ _).mp (inv_mem hj'J), fun x hx => ?_⟩
  have e0 : (b * j'⁻¹ * b⁻¹)⁻¹ * b = b * j' := by group
  rw [e0, commutatorElement_def]
  have hxX : x ∈ X := hJX hx
  set g := b * j' * x * (b * j')⁻¹ * x⁻¹ with hg
  have hgX : g ∈ X := mul_mem ((mem_normalizer_iff.mp hcX x).mp hxX) (inv_mem hxX)
  have hgJ : g ∈ J := mul_mem ((mem_normalizer_iff.mp hcJ x).mp hx) (inv_mem hx)
  have hwx : ((barHom M X hX ⟨x, hxX⟩ : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ wPre P := by
    refine ⟨barHom M X hX ⟨x, hxX⟩, ?_, rfl⟩
    show hatHom M X hX ⟨x, hxX⟩ ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P)
    rw [← map_jZero_eq_wSup M H L hX]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr hx)
  have h1 := hcw _ hwx
  have hbar : ((barHom M X hX ⟨g, hgX⟩ : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M) =
      c * ((barHom M X hX ⟨x, hxX⟩ : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M) * c⁻¹ *
        ((barHom M X hX ⟨x, hxX⟩ : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ := by
    rw [coe_barHom, coe_barHom, hc]
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [← hbar] at h1
  have hker : (⟨g, hgX⟩ : ↥X) ∈ (hatHom M X hX).ker := by
    obtain ⟨y, hy, hyg⟩ := h1
    rw [MonoidHom.mem_ker, hatHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have : y = barHom M X hX ⟨g, hgX⟩ := Subtype.ext hyg
    rwa [← this]
  have hgO : g ∈ pCoreOf 2 X := by
    rw [pCoreOf_eq_map_ker M X hX]
    exact ⟨_, hker, rfl⟩
  exact hcore ⟨hgO, hgJ⟩

theorem not_dvd_card_of_isPGroup_two {K : Type*} [Group K] [Finite K] (hK : IsPGroup 2 K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  rw [hn]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem dvd_card_wPre_of_dvd_jZero {M H L : Subgroup G} (hX : H ⊓ L ≤ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ Nat.card (jZero H L)) :
    p ∣ Nat.card (wPre (barM M (H ⊓ L))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set X := H ⊓ L
  set P := barM M X
  set Wh := wSup (↥P ⧸ CFSG.pCore 2 ↥P)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(jZero H L)) p h
  set y : ↥X := ⟨(x : G), jZero_le H L x.2⟩
  have hmapW : ((jZero H L).subgroupOf X).map (hatHom M X hX) = Wh := map_jZero_eq_wSup M H L hX
  have hyW : hatHom M X hX y ∈ Wh := by
    rw [← hmapW]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr x.2)
  have hy : orderOf y = p := by
    rw [← Subgroup.orderOf_coe, show (y : G) = (x : G) from rfl, Subgroup.orderOf_coe, hx]
  have hord : orderOf (hatHom M X hX y) = p := by
    have hdvd : orderOf (hatHom M X hX y) ∣ p := hy ▸ orderOf_map_dvd _ _
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      have hyk : y ∈ (hatHom M X hX).ker := by
        rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff, h1]
      obtain ⟨k, hk⟩ := isPGroup_ker_hatHom M X hX ⟨y, hyk⟩
      have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have : p ∣ 2 ^ k := hy ▸ orderOf_dvd_of_pow_eq_one hk'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
    · exact h1
  have hW : p ∣ Nat.card Wh := by
    have h0 : orderOf (⟨_, hyW⟩ : Wh) = p := by rw [Subgroup.orderOf_mk, hord]
    exact h0 ▸ orderOf_dvd_natCard _
  set C := Wh.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) with hC
  have hmap : C.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) = Wh :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have h1 := Subgroup.card_map_dvd C (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  rw [hmap] at h1
  have e : Nat.card (wPre P) = Nat.card C := Subgroup.card_map_of_injective P.subtype_injective
  rw [e]
  exact hW.trans h1

theorem pRank_wPre_le_pRank_jZero {M H L : Subgroup G} (hX : H ⊓ L ≤ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    Open.pRank p (wPre (barM M (H ⊓ L))) ≤ Open.pRank p (jZero H L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := H ⊓ L
  set P := barM M X
  set Wh := wSup (↥P ⧸ CFSG.pCore 2 ↥P)
  set C := Wh.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  have hbot : ∀ {A : Type} [Group A] (K : Subgroup A), ¬ p ∣ Nat.card K.subtype.ker := by
    intro A _ K
    rw [Subgroup.ker_subtype, Subgroup.card_bot]
    exact hp.not_dvd_one
  have h1 : Open.pRank p (wPre P) ≤ Open.pRank p C :=
    TenElevenOneLie.pRank_map_le hp P.subtype (hbot P) C
  have h2 : Open.pRank p C ≤ Open.pRank p (C.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))) :=
    CFSG.RankThree.OddKernel.pRank_le_map_of_not_dvd hp _ C (by
      rw [QuotientGroup.ker_mk']
      exact not_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup hp hp2)
  have hmapW : ((jZero H L).subgroupOf X).map (hatHom M X hX) = Wh := map_jZero_eq_wSup M H L hX
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _), ← hmapW] at h2
  have h3 := TenElevenOneLie.pRank_map_le hp (hatHom M X hX)
    (not_dvd_card_of_isPGroup_two (isPGroup_ker_hatHom M X hX) hp hp2) ((jZero H L).subgroupOf X)
  have h4 : Open.pRank p ((jZero H L).subgroupOf X) ≤
      Open.pRank p (((jZero H L).subgroupOf X).map X.subtype) :=
    CFSG.RankThree.OddKernel.pRank_le_map_of_not_dvd hp _ _ (hbot X)
  rw [subgroupOf_map_subtype, inf_of_le_left (jZero_le H L)] at h4
  exact h1.trans (h2.trans (h3.trans h4))

end CFSG.LocalAnalysis.RankThreeTheoremC
