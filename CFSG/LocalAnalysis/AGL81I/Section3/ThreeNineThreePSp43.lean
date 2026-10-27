module

public import CFSG.LocalAnalysis.StandardType.UFourTwoSylowFive
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder
import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem eq_V0_of_five_dvd_card
    {Y : Subgroup H6} (hT : T0 ≤ Y) (hV : Y ≤ V0)
    (h5 : 5 ∣ Nat.card Y) : Y = V0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hx5 : (y : H6) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    exact congrArg Subtype.val h
  have hx1 : (y : H6) ≠ 1 := by
    intro h
    have hy1 : y = 1 := Subtype.ext h
    rw [hy1, orderOf_one] at hy
    omega
  have hcov := CFSG.StandardType.UFourTwoSylow.order5_cover (hV y.2) hx1 hx5
  refine le_antisymm hV (hcov.trans (sup_le hT ?_))
  rw [Subgroup.zpowers_le]
  exact y.2

theorem not_five_dvd_card_of_not_dvd_index_V0
    {Y : Subgroup ↥V0}
    (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) : ¬ 5 ∣ Nat.card Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : T0 ≤ V0 := T0_le_V0
  have hcardP : Nat.card (T0.subgroupOf V0) = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv, card_T0]
  have hidx : ¬ 3 ∣ (T0.subgroupOf V0).index := by
    have h := Subgroup.card_mul_index (T0.subgroupOf V0)
    rw [hcardP, card_V0] at h
    omega
  let P : Sylow 3 ↥V0 := (IsPGroup.of_card hcardP).toSylow hidx
  have hP : (P : Subgroup ↥V0) = T0.subgroupOf V0 := IsPGroup.toSylow_coe _ _
  refine CFSG.StandardType.SylowOvergroup.forall_of_sylow_le P (fun Y => ¬ 5 ∣ Nat.card Y)
    ?_ ?_ hY h3
  · intro g Y hY'
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hY'
  · intro Y hPY hYtop h5
    rw [hP] at hPY
    have hTY : T0 ≤ Y.map V0.subtype := by
      intro t ht
      exact ⟨⟨t, hT ht⟩, hPY (Subgroup.mem_subgroupOf.2 ht), rfl⟩
    have hYV : Y.map V0.subtype ≤ V0 := Subgroup.map_subtype_le Y
    have h5' : 5 ∣ Nat.card (Y.map V0.subtype) := by
      rwa [Subgroup.card_map_of_injective V0.subtype_injective]
    have heq := eq_V0_of_five_dvd_card hTY hYV h5'
    refine hYtop (eq_top_iff.2 fun g _ => ?_)
    have hg : (g : H6) ∈ Y.map V0.subtype := by
      rw [heq]
      exact g.2
    obtain ⟨y, hy, hyg⟩ := hg
    rwa [← Subtype.ext hyg]

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_PSp43
    (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : StatedClassicalModel ↥K .PSp 2 3 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hP : StatedClassicalModel CFSG.GH74.Exceptional.PSp43 .PSp 2 3 1 :=
    ⟨hK.1, ZMod 3, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hK hP
  obtain ⟨e₂⟩ := nonempty_PSp43_mulEquiv_V0
  let e : ↥K ≃* ↥V0 := e₁.trans e₂
  have hcard : Nat.card ↥K = 25920 := by rw [Nat.card_congr e.toEquiv, card_V0]
  have : IsSimpleGroup ↥V0 := isSimpleGroup_V0
  have : IsSimpleGroup ↥K := e.isSimpleGroup
  have hZ : Subgroup.center ↥K = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun hc => by
      have := hc
      have hp := Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup ↥K)
      rw [hcard] at hp
      norm_num at hp
  have hOut : Nat.card (Outer ↥K) ∣ 2 := by
    obtain ⟨-, F, _, _, hF, ⟨ψ⟩⟩ := hK
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence ψ).toEquiv]
    have := (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
      (ℓ := 3) (f := 1) (r := 2) Nat.prime_three (by norm_num) le_rfl le_rfl hF).1
    norm_num at this
    exact this
  obtain ⟨hY, hm3, -, -, hdY, hdK⟩ := h.index_facts hZ
    (fun h3 => by have := h3.trans hOut; omega)
    (fun hd => h.d_ne_two ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp (hd.trans hOut)))
  rw [hcard] at hdY hdK
  have hd5 : d = 5 := by
    have hfac : (25920 : ℕ) = 2 ^ 6 * 3 ^ 4 * 5 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp h1
  have h3idx : ¬ 3 ∣ (X₁.subgroupOf K).index := by
    intro h3
    have := hm3
    unfold Nat.ModEq at this
    omega
  have h5Y : 5 ∣ Nat.card (X₁.subgroupOf K) := by
    subst hd5
    exact (dvd_pow_self 5 (Nat.Prime.factorization_pos_of_dvd Nat.prime_five (by norm_num)
      (by norm_num : 5 ∣ 25920)).ne').trans hdY
  exact CFSG.StandardType.SylowOvergroup.forall_of_mulEquiv (p := 3) e
    (fun A _ => ¬ 5 ∣ Nat.card A) (fun A B _ _ f hA => by rwa [← Nat.card_congr f.toEquiv])
    (fun Y hY h3 => not_five_dvd_card_of_not_dvd_index_V0 hY h3) _ hY h3idx h5Y

end CFSG.LocalAnalysis.AGL81I.Section3
