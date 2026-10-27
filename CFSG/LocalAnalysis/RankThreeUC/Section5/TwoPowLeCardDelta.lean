module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne
import CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowSubOneExponentDvd
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientShape

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowLeCardDelta

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section5
  CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter
open scoped Pointwise

theorem smul_eq_map {H : Type} [Group H] (ψ : MulAut H) (K : Subgroup H) : ψ • K = K.map ψ.toMonoidHom :=
  rfl

theorem succ_lt_two_pow {e : ℕ} (he : 2 ≤ e) : e + 1 < 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem image_orbit_eq_Delta (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    (fun K : Subgroup ↥P => K.map P.subtype) ''
        MulAction.orbit ↥(Sstar P T B) ((⁅B, P⁆ : Subgroup G).subgroupOf P) = Delta p P ρ := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  have h520 := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  have hDP : (⁅B, P⁆ : Subgroup G) ≤ P := h520.1.1
  have hD : ((⁅B, P⁆ : Subgroup G).subgroupOf P).map P.subtype = ⁅B, P⁆ :=
    Subgroup.map_subgroupOf_eq_of_le hDP
  have key : ∀ s : G,
      (((⁅B, P⁆ : Subgroup G).subgroupOf P).map (conjOnP P hP s).toMonoidHom).map P.subtype =
        (⁅B, P⁆ : Subgroup G).map (MulAut.conj s).toMonoidHom := fun s => by
    rw [map_subtype_map_conjOnP, hD]
  ext E
  constructor
  · rintro ⟨K, ⟨ψ, rfl⟩, rfl⟩
    obtain ⟨s, -, hψ⟩ := (mem_Sstar_iff hP).mp ψ.2
    show ((ψ : MulAut ↥P) • ((⁅B, P⁆ : Subgroup G).subgroupOf P)).map P.subtype ∈ Delta p P ρ
    rw [smul_eq_map, ← hψ, key]
    exact DeltaConjugationAction.map_mem hP ρ s h520.1
  · intro hE
    obtain ⟨s, hs, rfl⟩ := h520.2.2.2.2.1 ⁅B, P⁆ h520.1 E hE
    refine ⟨(⟨conjOnP P hP s, (mem_Sstar_iff hP).mpr ⟨s, hs, rfl⟩⟩ : ↥(Sstar P T B)) •
      ((⁅B, P⁆ : Subgroup G).subgroupOf P), MulAction.mem_orbit _ _, ?_⟩
    show ((conjOnP P hP s) • ((⁅B, P⁆ : Subgroup G).subgroupOf P)).map P.subtype = _
    rw [smul_eq_map, key]

theorem stabilizer_eq_center (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    MulAction.stabilizer ↥(Sstar P T B) ((⁅B, P⁆ : Subgroup G).subgroupOf P) =
      Subgroup.center ↥(Sstar P T B) := by
  ext ψ
  rw [MulAction.mem_stabilizer_iff]
  have h1 : ψ ∈ Subgroup.center ↥(Sstar P T B) ↔
      ((⁅B, P⁆ : Subgroup G).subgroupOf P).map (ψ : MulAut ↥P).toMonoidHom =
        (⁅B, P⁆ : Subgroup G).subgroupOf P :=
    (Subgroup.mem_map_iff_mem (Sstar P T B).subtype_injective).symm.trans (mem_center_Sstar_iff hc ψ.2)
  rw [h1]
  exact Iff.rfl

theorem card_Delta_eq (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card ↥(Delta p P ρ) = 2 ^ (2 * n) := by
  obtain ⟨n, hn, hcard⟩ :=
    CFSG.RankThree.PartOne.Quotient36.exists_card_eq_pow_extraspecial (isExtraspecialPGroup_Sstar hc)
  refine ⟨n, hn, ?_⟩
  have hidx := MulAction.index_stabilizer ↥(Sstar P T B) ((⁅B, P⁆ : Subgroup G).subgroupOf P)
  rw [stabilizer_eq_center hc] at hidx
  have hmul := (Subgroup.center ↥(Sstar P T B)).card_mul_index
  have horb : (MulAction.orbit ↥(Sstar P T B) ((⁅B, P⁆ : Subgroup G).subgroupOf P)).ncard =
      Nat.card ↥(Delta p P ρ) := by
    rw [Nat.card_coe_set_eq, ← image_orbit_eq_Delta hc,
      Set.ncard_image_of_injective _ (Subgroup.map_injective P.subtype_injective)]
  rw [card_center_Sstar hc, hcard, hidx, horb, pow_add, pow_one] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul

theorem prime_dvd_card_Delta_sub_one (hc : BinaryActionRankCounterexample G p P T B e ρ) {r : ℕ}
    (hr : r.Prime) (hrB : r ∣ Nat.card B) : r ∣ Nat.card ↥(Delta p P ρ) - 1 := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  have h520 := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
  letI : MulAction G ↥(Delta p P ρ) :=
    MulAction.compHom ↥(Delta p P ρ) (DeltaConjugationAction.act (p := p) hP ρ)
  have hsmul : ∀ (g : G) (D : ↥(Delta p P ρ)),
      ((g • D : ↥(Delta p P ρ)) : Subgroup G) = (D : Subgroup G).map (MulAut.conj g).toMonoidHom :=
    fun _ _ => rfl
  have hbG : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe]; exact hb
  have hb1 : (b : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hbG
    exact hr.one_lt.ne hbG
  have hZcard : Nat.card (Subgroup.zpowers (b : G)) = r ^ 1 := by rw [Nat.card_zpowers, hbG, pow_one]
  have hZp : IsPGroup r (Subgroup.zpowers (b : G)) := IsPGroup.of_card hZcard
  have hmod := hZp.card_modEq_card_fixedPoints ↥(Delta p P ρ)
  have hBD : ∀ g ∈ B, (⁅B, P⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⁅B, P⁆ := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (NotIsPrimePowTwoPowSubOne.mem_normalizer_commutator_of (Subgroup.le_normalizer hg)
        (hc.oddPrimeClassTwoAction.setting.normB hg))
  have hZB : Subgroup.zpowers (b : G) ≤ B := (Subgroup.zpowers_le).mpr b.2
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers (b : G)) ↥(Delta p P ρ)) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨⁅B, P⁆, h520.1⟩, fun z => Subtype.ext ?_⟩, ?_⟩
    · show (⁅B, P⁆ : Subgroup G).map (MulAut.conj (z : G)).toMonoidHom = ⁅B, P⁆
      exact hBD _ (hZB z.2)
    · rintro ⟨⟨F, hF⟩, hFfix⟩
      have hbF : (F : Subgroup G).map (MulAut.conj (b : G)).toMonoidHom = F := by
        have h := congrArg Subtype.val (hFfix ⟨(b : G), Subgroup.mem_zpowers _⟩)
        rw [Subgroup.smul_def, hsmul] at h
        exact h
      have hbN : (b : G) ∈ Subgroup.normalizer (F : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hbF
      by_contra hne
      have hFD : F ≠ ⁅B, P⁆ := fun h => hne (by subst h; rfl)
      exact h520.2.2.2.1 (b : G) b.2 hb1 F hF hFD hbN
  rw [hfix] at hmod
  have hpos : 1 ≤ Nat.card ↥(Delta p P ρ) := by
    haveI : Nonempty ↥(Delta p P ρ) := ⟨⟨⁅B, P⁆, h520.1⟩⟩
    exact Nat.card_pos
  exact (Nat.modEq_iff_dvd' hpos).mp hmod.symm

theorem dvd_of_card_Delta_eq (hc : BinaryActionRankCounterexample G p P T B e ρ) {N : ℕ}
    (hN : Nat.card ↥(Delta p P ρ) = 2 ^ N) : e ∣ N := by
  have he : 0 < e := by
    have := hc.oddPrimeClassTwoAction.two_lt
    omega
  refine TwoPowSubOneExponentDvd.dvd_of_forall_prime_dvd he fun r hr hrd => ?_
  have hrπ : r ∈ piOf B := by
    rw [hc.oddPrimeClassTwoAction.pi_eq]
    exact ⟨hr, hrd⟩
  rw [← hN]
  exact prime_dvd_card_Delta_sub_one hc hr hrπ.2

end CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowLeCardDelta

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowLeCardDelta

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem two_pow_le_card_Delta (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    2 ^ e ≤ Nat.card ↥(Delta p P ρ) ∧ (Odd e → 4 ^ e ≤ Nat.card ↥(Delta p P ρ)) := by
  obtain ⟨n, hn, hcard⟩ := card_Delta_eq hc
  have hdvd : e ∣ 2 * n := dvd_of_card_Delta_eq hc hcard
  rw [hcard]
  refine ⟨Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (by omega) hdvd), fun hodd => ?_⟩
  have hen : e ∣ n := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) hdvd
  have hle : e ≤ n := Nat.le_of_dvd (by omega) hen
  calc 4 ^ e = 2 ^ (2 * e) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem lt_card_Delta (hc : BinaryActionRankCounterexample G p P T B e ρ) : e + 1 < Nat.card ↥(Delta p P ρ) :=
  lt_of_lt_of_le (succ_lt_two_pow (by have := hc.oddPrimeClassTwoAction.two_lt; omega))
    (two_pow_le_card_Delta hc).1

end CFSG.LocalAnalysis.RankThreeUC.Section5
