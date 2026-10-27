module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenNormIOf
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreeSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc5
import CFSG.RankThree.PartOne.S12.PerfectOddPrime
import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofCore
import CFSG.RankThree.PartOne.CTP.StrongPQuotient
import CFSG.Quasithin.Background.C41PfE
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34NoRem
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenNotXOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable (G : Type) [Group G] [Finite G] in
@[expose] def AGL81TenThreeTwoRankCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ (n : ℕ) (J : Fin n → Subgroup G), (∀ i, J i ∈ cZero (H ⊓ L)) →
      Function.Injective (fun i => CFSG.ComponentClassification.AS76b.oUpperTwo (J i)) →
      n ≤ CFSG.Open.pRank 3 L

namespace TenTenClaim

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem elemAbelian_sup_card {p : ℕ} {A C : Subgroup Y} (hA : IsElemAbelian p A)
    (hC : IsElemAbelian p C) (hc : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hAC : A ⊓ C = ⊥) :
    IsElemAbelian p (A ⊔ C) ∧ Nat.card (A ⊔ C : Subgroup Y) = Nat.card A * Nat.card C := by
  refine ⟨hA.sup_of_commute hC hc, ?_⟩
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A C hc).1
  rw [hAC, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_zpowers_three {e : Y} (he : e ^ 3 = 1) (he1 : e ≠ 1) :
    Nat.card (zpowers e) = 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime he he1

theorem elemAbelian_zpowers_sup {B C : Subgroup Y} {e : Y} (he : e ^ 3 = 1)
    (heB : e ∉ centralizer (B : Set Y)) (hC : IsElemAbelian 3 C)
    (hCB : C ≤ centralizer (B : Set Y)) (hce : ∀ c ∈ C, e * c = c * e) :
    IsElemAbelian 3 (zpowers e ⊔ C) ∧ Nat.card (zpowers e ⊔ C : Subgroup Y) = 3 * Nat.card C := by
  have he1 : e ≠ 1 := by
    rintro rfl
    exact heB (one_mem _)
  have hinf : zpowers e ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxC⟩
    rw [mem_bot]
    by_contra hx1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hord : orderOf e = 3 := orderOf_eq_prime he he1
    have hk : ¬ (3 : ℤ) ∣ k := by
      intro h3
      apply hx1
      rw [← orderOf_dvd_iff_zpow_eq_one, hord]
      exact_mod_cast h3
    have hcop : IsCoprime k 3 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := Int.gcd_dvd_right (a := k) (b := 3)
      have hp : Nat.Prime 3 := Nat.prime_three
      rcases (Nat.dvd_prime hp).1 (by exact_mod_cast this) with h | h
      · exact h
      · exfalso
        apply hk
        have := Int.gcd_dvd_left (a := k) (b := 3)
        rw [h] at this
        exact_mod_cast this
    obtain ⟨u, v, huv⟩ := hcop
    have hmem : e ∈ C := by
      have h1 : e = (e ^ k) ^ u * (e ^ (3 : ℤ)) ^ v := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm k u, mul_comm (3 : ℤ) v, huv, zpow_one]
      have h3 : e ^ (3 : ℤ) = 1 := by exact_mod_cast he
      rw [h1, h3, one_zpow, mul_one]
      exact C.zpow_mem hxC u
    exact heB (hCB hmem)
  have hA := CFSG.Open.isElemAbelian_zpowers (p := 3) he
  have hc : ∀ a ∈ zpowers e, ∀ c ∈ C, a * c = c * a := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.zpow_left (hce c hc) k))
  obtain ⟨h1, h2⟩ := elemAbelian_sup_card hA hC hc hinf
  exact ⟨h1, by rw [h2, card_zpowers_three he he1]⟩

end Generic

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_lift {M W : Subgroup G} (hWM : W ≤ M)
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hE : IsElemAbelian 3 E) (hEW : E ≤ barM M W) :
    ∃ E' : Subgroup G, E' ≤ W ∧ IsElemAbelian 3 E' ∧ Nat.card E' = Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set Y : Subgroup ↥M := (W.subgroupOf M) ⊓ E.comap π with hY
  set f : ↥Y →* ↥E := (π.comp Y.subtype).codRestrict E (fun y => y.2.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨w, hw, rfl⟩ := hEW he
    exact ⟨⟨w, hw, he⟩, rfl⟩
  have hEp : IsPGroup 3 (⊤ : Subgroup ↥E) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hE.2 _ g.1.2))⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 ↥Y))
  have hQ : (Q₀ : Subgroup ↥Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hEp le_top).symm
  have hinj : ∀ y ∈ (Q₀ : Subgroup ↥Y), f y = 1 → y = 1 := by
    intro y hy h1
    have hyk : ((y : ↥M)) ∈ CFSG.pCore 2 ↥M := by
      have : π (y : ↥M) = 1 := congrArg Subtype.val h1
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨k, hk⟩ := Q₀.isPGroup' ⟨y, hy⟩
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, hyk⟩
    have hk' : ((y : ↥M)) ^ 3 ^ k = 1 := by
      have := congrArg (fun z : (Q₀ : Subgroup ↥Y) => ((z : ↥Y) : ↥M)) hk
      simpa using this
    have hj' : ((y : ↥M)) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hcop : Nat.Coprime (3 ^ k) (2 ^ j) := Nat.Coprime.pow k j (by norm_num)
    have h1' : orderOf (y : ↥M) = 1 := by
      have ha := orderOf_dvd_of_pow_eq_one hk'
      have hb := orderOf_dvd_of_pow_eq_one hj'
      exact Nat.eq_one_of_dvd_coprimes hcop ha hb
    exact Subtype.ext (orderOf_eq_one_iff.mp h1')
  have hinjQ : Function.Injective (f.comp (Q₀ : Subgroup ↥Y).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [mem_bot]
    exact Subtype.ext (hinj y y.2 hy)
  have hcardQ : Nat.card (Q₀ : Subgroup ↥Y) = Nat.card E := by
    have h1 : Nat.card ((⊤ : Subgroup (Q₀ : Subgroup ↥Y)).map (f.comp (Q₀ : Subgroup ↥Y).subtype)) =
        Nat.card (Q₀ : Subgroup ↥Y) := by
      rw [Subgroup.card_map_of_injective hinjQ, Subgroup.card_top]
    have h2 : (⊤ : Subgroup (Q₀ : Subgroup ↥Y)).map (f.comp (Q₀ : Subgroup ↥Y).subtype) = ⊤ := by
      rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hQ]
    rw [← h1, h2, Subgroup.card_top]
  have hQab : IsElemAbelian 3 (Q₀ : Subgroup ↥Y) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · have hc : f a * f b = f b * f a := Subtype.ext (hE.comm (f a).2 (f b).2)
      have h1 : f ((a : ↥Y) * b * ((b : ↥Y) * a)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
      have h2 := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) h1
      exact mul_inv_eq_one.mp h2
    · refine hinj _ (pow_mem hy 3) ?_
      rw [map_pow]
      exact Subtype.ext (hE.2 _ (f y).2)
  refine ⟨((Q₀ : Subgroup ↥Y).map Y.subtype).map M.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact y.2.1
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hQab _) _
  · rw [Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective Y.subtype_injective, hcardQ]

end Lift


section NonCentral

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.AS76b (oUpperTwo)

theorem not_oUpperTwo_le_center {Q : Type} [Group Q] [Finite Q] (h : IsSymThreeOrSUThreeTwo Q) :
    ¬ oUpperTwo (⊤ : Subgroup Q) ≤ center Q := by
  intro hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen : ∀ g : Q, (∃ k : ℕ, g ^ 3 ^ k = 1) → g ∈ center Q := by
    rintro g ⟨k, hk⟩
    apply hc
    apply Subgroup.subset_closure
    refine ⟨mem_top g, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    rw [hj]
    exact Odd.pow (by decide)
  obtain ⟨N, hN, hcop, hq⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5.hasNormalPComplement_of_pElements_central
      hcen
  have h2 : ∀ t : Q, (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∈ N := by
    rintro t ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hq (QuotientGroup.mk t)
    have h1 : (QuotientGroup.mk t : Q ⧸ N) ^ 2 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    have hcop' : Nat.Coprime (2 ^ k) (3 ^ j) := Nat.Coprime.pow k j (by norm_num)
    have ho : orderOf (QuotientGroup.mk t : Q ⧸ N) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop' (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hj)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at ho
    exact ho
  have htop : N = ⊤ := by
    rw [eq_top_iff, ← IsSymThreeOrSUThreeTwo.closure_two kFactSUThreeTwoShape_holds h]
    exact (closure_le _).2 fun t ht => h2 t ht
  have h3 := IsSymThreeOrSUThreeTwo.three_dvd_card h
  rw [htop, Subgroup.card_top] at hcop
  have := Nat.Coprime.eq_one_of_dvd hcop h3
  omega

theorem eq_one_of_odd_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {y : G} (hy : y ∈ P)
    (hodd : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · exfalso
    rw [hj, pow_succ] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (Nat.even_mul.mpr (Or.inr even_two))

theorem exists_noncentral {M L X I₀ : Subgroup G} (hLM : L ≤ M) (hI₀ : I₀ ∈ cZero X)
    (hI₀L : I₀ ≤ L) (h3 : 3 ∣ Nat.card (oUpperTwo I₀)) :
    ∃ e ∈ barM M (oUpperTwo I₀), e ^ 3 = 1 ∧ e ∉ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hI₀M : I₀ ≤ M := hI₀L.trans hLM
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hbarL : barM M I₀ ≤ barM M L := Subgroup.map_mono fun x hx => hI₀L hx
  rcases (IsCZeroMember.shape hI₀) with ha | ⟨hO2, hb⟩
  ·
    have hperf : ⁅I₀, I₀⁆ = I₀ := ha.perfect
    rw [SevenFourL34.oUpperTwo_eq_of_perfect hperf] at h3 ⊢
    set B := barM M I₀ with hB
    let ψ : ↥I₀ →* ↥B := (π.comp (Subgroup.inclusion hI₀M)).codRestrict B
      (fun x => ⟨Subgroup.inclusion hI₀M x, x.2, rfl⟩)
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, ⟨y, hy, rfl⟩⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    haveI : Group.IsPerfect ↥I₀ := Subgroup.isPerfect_iff.mpr hperf
    haveI hBp : Group.IsPerfect ↥B := Group.IsPerfect.ofSurjective (f := ψ) hψ
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥I₀) 3 h3
    have hψy : orderOf (ψ y) = 3 := by
      apply orderOf_eq_prime
      · rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
      · intro h1
        have hk : π (Subgroup.inclusion hI₀M y) = 1 := congrArg Subtype.val h1
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
        have hodd : Odd (orderOf (Subgroup.inclusion hI₀M y)) := by
          rw [orderOf_injective _ (Subgroup.inclusion_injective hI₀M), hy]
          decide
        have := eq_one_of_odd_of_isPGroup (G := ↥M) CFSG.pCore_isPGroup hk hodd
        have h1' : orderOf y = 1 := by
          rw [← orderOf_injective _ (Subgroup.inclusion_injective hI₀M), this, orderOf_one]
        rw [hy] at h1'
        norm_num at h1'
    have h3B : 3 ∣ Nat.card ↥B := hψy ▸ orderOf_dvd_natCard (ψ y)
    obtain ⟨e, he3, hez⟩ :=
      CFSG.RankThree.PartOne.exists_pow_eq_one_not_mem_center_of_isPerfect (p := 3) (by norm_num)
        hBp h3B
    refine ⟨e.1, e.2, by simpa using congrArg Subtype.val he3, ?_⟩
    intro hcen
    apply hez
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hcen b.1 (hbarL b.2)
    simpa using this
  ·
    by_contra hcon
    push Not at hcon
    have hcube : ∀ y ∈ I₀, Odd (orderOf y) → y ^ 3 = 1 := by
      intro y hy hodd
      have hyO : y ∈ oUpperTwo I₀ := Subgroup.subset_closure ⟨hy, hodd⟩
      have h1 := IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds hb y hyO
      refine eq_one_of_odd_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I₀) h1 ?_
      exact hodd.of_dvd_nat (orderOf_pow_dvd 3)
    have hcentr : ∀ x ∈ oUpperTwo I₀, ∀ hx : x ∈ M,
        π ⟨x, hx⟩ ∈ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        intro hyM
        refine hcon _ ⟨⟨y, hyM⟩, ?_, rfl⟩ ?_
        · exact Subgroup.subset_closure hy
        · rw [← map_pow]
          have : (⟨y, hyM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hcube y hy.1 hy.2)
          rw [this, map_one]
      | one => intro _; exact Subgroup.one_mem _
      | mul a b ha hb iha ihb =>
        intro hab
        have haM : a ∈ M := hI₀M (oUpperTwo_le_self I₀ ha)
        have hbM : b ∈ M := hI₀M (oUpperTwo_le_self I₀ hb)
        have e1 : (⟨a * b, hab⟩ : ↥M) = ⟨a, haM⟩ * ⟨b, hbM⟩ := rfl
        rw [e1, map_mul]
        exact mul_mem (iha haM) (ihb hbM)
      | inv a ha iha =>
        intro hai
        have haM : a ∈ M := hI₀M (oUpperTwo_le_self I₀ ha)
        have e1 : (⟨a⁻¹, hai⟩ : ↥M) = (⟨a, haM⟩ : ↥M)⁻¹ := rfl
        rw [e1, map_inv]
        exact inv_mem (iha haM)
    set N₂ : Subgroup ↥I₀ := (pCoreOf 2 M).subgroupOf I₀ with hN₂
    have hN₂n : N₂.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hN₂, Subgroup.mem_subgroupOf] at hn ⊢
      have h := localGroup_le_normalizer_pCoreOf 2 M (hI₀M g.2)
      exact (Subgroup.mem_normalizer_iff.mp h n).mp hn
    have hN₂p : IsPGroup 2 N₂ := by
      rintro ⟨n, hn⟩
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨n.1, hn⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    have hN₂le : N₂ ≤ CFSG.pCore 2 ↥I₀ :=
      CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof.le_pCore_of_normal hN₂n hN₂p
    set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥I₀) with hρ
    have hcomm : ∀ g x : ↥I₀, (x : G) ∈ oUpperTwo I₀ → ρ g * ρ x = ρ x * ρ g := by
      intro g x hx
      have hxc := hcentr x hx (hI₀M x.2)
      have hgL : π ⟨g, hI₀M g.2⟩ ∈ barM M L := ⟨⟨g, hI₀M g.2⟩, hI₀L g.2, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxc _ hgL
      have h2 : π (⟨g, hI₀M g.2⟩ * ⟨x, hI₀M x.2⟩ * (⟨g, hI₀M g.2⟩ : ↥M)⁻¹ *
          (⟨x, hI₀M x.2⟩ : ↥M)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 : g * x * g⁻¹ * x⁻¹ ∈ N₂ := by
        rw [hN₂, Subgroup.mem_subgroupOf]
        exact ⟨_, h2, rfl⟩
      have h4 := hN₂le h3
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hρ] at h4
      simp only [map_mul, map_inv] at h4
      calc ρ g * ρ x = (ρ g * ρ x * (ρ g)⁻¹ * (ρ x)⁻¹) * (ρ x * ρ g) := by group
        _ = ρ x * ρ g := by rw [h4, one_mul]
    apply not_oUpperTwo_le_center hb
    intro q hq
    have hmap : (oUpperTwo (⊤ : Subgroup ↥I₀)).map ρ = oUpperTwo (⊤ : Subgroup (↥I₀ ⧸ CFSG.pCore 2 ↥I₀)) := by
      rw [SUPair.map_oUpperTwo, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hsub : (oUpperTwo (⊤ : Subgroup ↥I₀)).map I₀.subtype = oUpperTwo I₀ := by
      rw [SUPair.map_oUpperTwo, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hmap] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    have hyO : (y : G) ∈ oUpperTwo I₀ := hsub ▸ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q'
    exact hcomm g y hyO

end NonCentral

section Family

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_elemAbelian_of_family : ∀ (n : ℕ) (B : Fin n → Subgroup Y) (e : Fin n → Y),
    (∀ i j, i ≠ j → B j ≤ centralizer (B i : Set Y)) → (∀ i, e i ∈ B i) → (∀ i, e i ^ 3 = 1) →
    (∀ i, e i ∉ centralizer (B i : Set Y)) →
    ∃ E : Subgroup Y, E ≤ closure (Set.range e) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ n
  | 0, _, _, _, _, _, _ => ⟨⊥, bot_le, CFSG.Open.isElemAbelian_bot 3, by simp⟩
  | n + 1, B, e, hc, he, h3, hnc => by
    obtain ⟨E', hE'le, hE', hE'card⟩ := exists_elemAbelian_of_family n (fun i => B i.succ)
      (fun i => e i.succ) (fun i j hij => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)))
      (fun i => he i.succ) (fun i => h3 i.succ) (fun i => hnc i.succ)
    have hcl : closure (Set.range fun i : Fin n => e i.succ) ≤ centralizer (B 0 : Set Y) := by
      rw [closure_le]
      rintro _ ⟨i, rfl⟩
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm (he i.succ)
    have hE'B : E' ≤ centralizer (B 0 : Set Y) := hE'le.trans hcl
    have hce : ∀ c ∈ E', e 0 * c = c * e 0 := by
      intro c hcE
      exact (Subgroup.mem_centralizer_iff.mp (hE'B hcE) (e 0) (he 0))
    obtain ⟨h1, h2⟩ := elemAbelian_zpowers_sup (h3 0) (hnc 0) hE' hE'B hce
    refine ⟨zpowers (e 0) ⊔ E', sup_le ?_ (hE'le.trans (closure_mono ?_)), h1, ?_⟩
    · rw [zpowers_le]
      exact subset_closure ⟨0, rfl⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨i.succ, rfl⟩
    · rw [h2, hE'card, pow_succ, mul_comm]

end Family

section Conj

variable {G : Type} [Group G] [Finite G]

theorem map_conj_pow_ne {X : Subgroup G} {q : G} {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hq : q ^ p ^ k = 1) (hX : X.map (MulAut.conj q).toMonoidHom ≠ X) {d : ℕ} (hd1 : 1 ≤ d)
    (hdp : d < p) : X.map (MulAut.conj (q ^ d)).toMonoidHom ≠ X := by
  intro h
  apply hX
  have hcop : Nat.Coprime d (p ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun hpd => absurd (Nat.le_of_dvd (by omega) hpd) (by omega)))
  have hgcd : d.gcd (orderOf q) = 1 :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hq) hcop
  have hqmem : q ∈ zpowers (q ^ d) := mem_zpowers_pow_iff.mpr hgcd
  have hN : q ^ d ∈ normalizer (X : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp ((zpowers_le.mpr hN) hqmem)

theorem map_conj_pow_inj {X : Subgroup G} {q : G} {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hq : q ^ p ^ k = 1) (hX : X.map (MulAut.conj q).toMonoidHom ≠ X) {i j : ℕ} (hij : i < j)
    (hjp : j < p) :
    X.map (MulAut.conj (q ^ i)).toMonoidHom ≠ X.map (MulAut.conj (q ^ j)).toMonoidHom := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have e1 : X.map (MulAut.conj (q ^ (i + d + 1))).toMonoidHom =
      (X.map (MulAut.conj (q ^ (d + 1))).toMonoidHom).map (MulAut.conj (q ^ i)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, pow_add, mul_assoc]
  rw [e1] at h
  exact map_conj_pow_ne hp hq hX (d := d + 1) (by omega) (by omega)
    ((Subgroup.map_injective (MulAut.conj (q ^ i)).injective) h).symm

theorem eq_of_barM_eq {M L₁ L₂ : Subgroup G} (h₁ : IsTwoPrimeComponent M L₁)
    (h₂ : IsTwoPrimeComponent M L₂) (h : barM M L₁ = barM M L₂) : L₁ = L₂ := by
  have key : ∀ {A B : Subgroup G}, IsTwoPrimeComponent M A → IsTwoPrimeComponent M B →
      barM M A = barM M B → A ≤ B := by
    intro A B hA hB hAB
    have hle : A ≤ B ⊔ pCoreOf 2 M := by
      intro x hx
      have hxM : x ∈ M := hA.le hx
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M B :=
        hAB ▸ ⟨⟨x, hxM⟩, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hmem
      have hv : y⁻¹ * ⟨x, hxM⟩ ∈ CFSG.pCore 2 ↥M := by
        rw [← QuotientGroup.eq_one_iff]
        show QuotientGroup.mk' (CFSG.pCore 2 ↥M) _ = 1
        rw [map_mul, map_inv, hyx, inv_mul_cancel]
      have e : x = (y : G) * ((y⁻¹ * ⟨x, hxM⟩ : ↥M) : G) := by simp
      rw [e]
      exact mul_mem (mem_sup_left (mem_subgroupOf.mp hy)) (mem_sup_right ⟨_, hv, rfl⟩)
    exact CFSG.Quasithin.C41Pf.le_of_perfect_of_le_sup
      (TenTenNormI.pCoreOf_le_normalizer hB.le hB.subnormal hB.perfect)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hA.perfect hle
  exact le_antisymm (key h₁ h₂ h) (key h₂ h₁ h.symm)

theorem barM_le_centralizer {M L₁ L₂ : Subgroup G} (h₁ : IsTwoPrimeComponent M L₁)
    (h₂ : IsTwoPrimeComponent M L₂) (hne : L₁ ≠ L₂) :
    barM M L₂ ≤ centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hB : barM M L₁ ≠ barM M L₂ := fun h => hne (eq_of_barM_eq h₁ h₂ h)
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact commute_of_isComponentOf_ne h₁.component h₂.component hB x hx y hy

theorem conj_noncentral {M L : Subgroup G} {e : ↥M ⧸ CFSG.pCore 2 ↥M} (he : e ∈ barM M L)
    (h3 : e ^ 3 = 1) (hnc : e ∉ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {g : G} (hg : g ∈ M) :
    MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩) e ∈
        barM M (L.map (MulAut.conj g).toMonoidHom) ∧
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩) e) ^ 3 = 1 ∧
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩) e ∉
        centralizer (barM M (L.map (MulAut.conj g).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set c := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩) with hc
  rw [barM_map_conj hg]
  refine ⟨⟨e, he, rfl⟩, by rw [← map_pow, h3, map_one], ?_⟩
  intro hcen
  apply hnc
  rw [Subgroup.mem_centralizer_iff] at hcen ⊢
  intro b hb
  have := hcen (c b) ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul] at this
  exact c.injective this

end Conj

section Cfg

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.AS76b (oUpperTwo)

theorem normalizer_facts (h98 : AGL81NineEightFour G) (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {I₀ : Subgroup G} (hI₀ : I₀ ∈ cZero (H ⊓ L)) :
    pCoreOf 2 M ≤ normalizer (oUpperTwo I₀ : Set G) ∧
      ∀ m ∈ M, L.map (MulAut.conj m).toMonoidHom ≠ L →
        L.map (MulAut.conj m).toMonoidHom ≤ normalizer (oUpperTwo I₀ : Set G) := by
  set I := oUpperTwo I₀ with hIdef
  obtain ⟨-, hMH, hHM⟩ := hd.nineEightFour' hS h98
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hVI : pCoreOf 2 H ≤ normalizer (I : Set G) := pCoreOf_le_normalizer_oUpperTwo hL hI₀ hHM hNH
  have hgen : I ≤ closure {x : G | x ∈ I ∧ Odd (orderOf x)} := by
    have h := NoRem.oUpperTwo_idem I₀
    calc I = oUpperTwo I := h.symm
      _ ≤ _ := le_rfl
  have hIL : I ≤ L := (oUpperTwo_le_self I₀).trans (hI₀.le.trans inf_le_right)
  refine ⟨hMH.trans hVI, fun m hm hne g hg => ?_⟩
  refine TenTenNotX.mem_normalizer_of_commutator_mem hgen (hMH.trans hVI)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) fun x hx => ?_
  have h := TenTenNormI.commutator_mem_of_ne hL.toIsTwoPrimeComponent hm hne x (hIL hx) g hg
  have h' := (pCoreOf 2 M).inv_mem h
  have e : (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ := by group
  rwa [e] at h'

theorem pRank_le_pRank_barM {M L : Subgroup G} (hLM : L ≤ M) :
    CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 (barM M L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEL, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
  set E₁ : Subgroup ↥M := E.subgroupOf M with hE₁
  have hE₁p : IsPGroup 3 E₁ := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hE.2 _ x.2))⟩
  have h2 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hc1 : Nat.card (E₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) = Nat.card E₁ :=
    CFSG.RankThree.PartOne.StrongP.card_map_quotient_of_coprime hE₁p h2
  have hc2 : Nat.card E₁ = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEL.trans hLM)).toEquiv
  have hE₁ab : IsElemAbelian 3 E₁ :=
    hE.comap (f := M.subtype) M.subtype_injective
  refine CFSG.SectionRank.le_pRank (p := 3) (H := barM M L)
    (E := E₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) (by norm_num) ?_
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₁ab _) ?_
  · exact Subgroup.map_mono fun x hx => hEL hx
  · rw [hc1, hc2, hcard]

theorem exists_E_conj {M L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    {e : ↥M ⧸ CFSG.pCore 2 ↥M} (he : e ∈ barM M L) (h3 : e ^ 3 = 1)
    (hnc : e ∉ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (n : ℕ) (g : Fin n → G)
    (hg : ∀ i, g i ∈ M)
    (hdist : ∀ i j, i ≠ j → L.map (MulAut.conj (g i)).toMonoidHom ≠ L.map (MulAut.conj (g j)).toMonoidHom) :
    ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ closure (Set.range fun i => MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g i, hg i⟩) e) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ n := by
  refine exists_elemAbelian_of_family n (fun i => barM M (L.map (MulAut.conj (g i)).toMonoidHom))
    _ (fun i j hij => barM_le_centralizer (hL.map_conj (hg i)) (hL.map_conj (hg j)) (hdist i j hij))
    (fun i => (conj_noncentral he h3 hnc (hg i)).1) (fun i => (conj_noncentral he h3 hnc (hg i)).2.1)
    (fun i => (conj_noncentral he h3 hnc (hg i)).2.2)

theorem barM_self (M : Subgroup G) : barM M M = ⊤ := by
  rw [barM, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem le_pRank_of_conj {M L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    {e : ↥M ⧸ CFSG.pCore 2 ↥M} (he : e ∈ barM M L) (h3 : e ^ 3 = 1)
    (hnc : e ∉ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (n : ℕ) (g : Fin n → G)
    (hg : ∀ i, g i ∈ M)
    (hdist : ∀ i j, i ≠ j → L.map (MulAut.conj (g i)).toMonoidHom ≠ L.map (MulAut.conj (g j)).toMonoidHom) :
    n ≤ CFSG.Open.pRank 3 M := by
  obtain ⟨E, -, hE, hcard⟩ := exists_E_conj hL he h3 hnc n g hg hdist
  obtain ⟨E', hE'M, hE', hcard'⟩ := exists_elemAbelian_lift le_rfl hE ((barM_self M).symm ▸ le_top)
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE'M hE' (hcard'.trans hcard)

theorem map_conj_one (L : Subgroup G) : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
  ext x
  simp [MulAut.conj_apply]

theorem map_one_mulAut (L : Subgroup G) : L.map (MulEquiv.toMonoidHom (1 : MulAut G)) = L := by
  ext x
  simp

end Cfg

end TenTenClaim

open TenTenClaim

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.AS76b (oUpperTwo) in
theorem agl81TenTenClaimCfg_of (h1032 : AGL81TenThreeTwoRankCfg G) (h1031 : AGL81TenThreeOneAt G)
    (h98 : AGL81NineEightFour G) : AGL81TenTenClaimCfg G := by
  intro hS p P M H Q K hd L hL hNL I₀ hI₀
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := oUpperTwo I₀ with hIdef
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hp : p.Prime := he.prime
  have hp2 : p ≠ 2 := he.ne_two
  obtain ⟨hVM, hconjN⟩ := normalizer_facts h98 hS hd hL hI₀
  have hLc : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hLM : L ≤ M := hLc.le
  have hI₀L : I₀ ≤ L := hI₀.le.trans inf_le_right
  have hIL : I ≤ L := (oUpperTwo_le_self I₀).trans hI₀L
  have hIM : I ≤ M := hIL.trans hLM
  have h3 : 3 ∣ Nat.card I := h1031 hS p P M H Q K hd L hL I₀ hI₀
  obtain ⟨e, heI, he3, hnc⟩ := exists_noncentral hLM hI₀ hI₀L h3
  have heL : e ∈ barM M L := barM_mono hIL heI
  have hrkM : CFSG.Open.pRank 3 M ≤ 3 := by
    have h := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M he.maxTwoLocal_M.1
    rw [hS.rank] at h
    exact h
  have hrkL : CFSG.Open.pRank 3 L ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hLM).trans hrkM
  have hconjM : ∀ g ∈ M, L.map (MulAut.conj g).toMonoidHom ≤ M := fun g hg => (hLc.map_conj hg).le
  have hQH : Q ≤ H := hd.le_H
  have hQM : Q ≤ M := hd.base.1
  have hQp : IsPGroup p Q := hd.base.2.1
  have horbitI : ∀ q ∈ Q, L.map (MulAut.conj q).toMonoidHom = L →
      I.map (MulAut.conj q).toMonoidHom ≠ I → ∀ n ≤ p, n ≤ CFSG.Open.pRank 3 L := by
    intro q hq hLq hIq n hn
    obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
    have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hqHL : q ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
      have hjA : q ∈ normalizer (H : Set G) := le_normalizer (hQH hq)
      have hjB : q ∈ normalizer (L : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLq
      rw [mem_normalizer_iff] at hjA hjB ⊢
      intro h
      rw [mem_inf, mem_inf, hjA h, hjB h]
    refine h1032 hS p P M H Q K hd L hL n
      (fun i => I₀.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
      (fun i => IsCZeroMember.map_conj hI₀ (Subgroup.pow_mem _ hqHL _)) ?_
    intro i j hij
    simp only at hij
    rw [← SUPair.map_oUpperTwo, ← SUPair.map_oUpperTwo] at hij
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact map_conj_pow_inj hp hk' hIq h (by omega) hij
    · exact map_conj_pow_inj hp hk' hIq h (by omega) hij.symm
  have hlift : ∀ W : Subgroup G, W ≤ M → W ≤ normalizer (I : Set G) →
      ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M W → IsElemAbelian 3 E →
        Nat.card E = 3 ^ 3 →
        ∃ Q₀ : Subgroup G, IsAGLQ 3 M Q₀ ∧ Q₀ ≤ normalizer (I : Set G) := by
    intro W hWM hWN E hEW hE hEcard
    obtain ⟨Q₀, hQ₀W, hQ₀, hQ₀card⟩ := exists_elemAbelian_lift hWM hE hEW
    refine ⟨Q₀, ⟨hQ₀W.trans hWM, fun x => ⟨1, Subtype.ext (by simpa using hQ₀.2 _ x.2)⟩, Or.inl ?_⟩,
      hQ₀W.trans hWN⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hQ₀ (hQ₀card.trans hEcard)
  rcases eq_or_ne p 3 with rfl | hp3
  ·
    by_cases h3c : ∃ a ∈ M, ∃ b ∈ M, L.map (MulAut.conj a).toMonoidHom ≠ L ∧
        L.map (MulAut.conj b).toMonoidHom ≠ L ∧
        L.map (MulAut.conj a).toMonoidHom ≠ L.map (MulAut.conj b).toMonoidHom
    · obtain ⟨a, ha, b, hb, hLa, hLb, hab⟩ := h3c
      have hg : ∀ i, (![a, b] : Fin 2 → G) i ∈ M := by
        intro i
        fin_cases i
        · exact ha
        · exact hb
      have hab' := Ne.symm hab
      obtain ⟨E₂, hE₂cl, hE₂, hE₂card⟩ := exists_E_conj hLc heL he3 hnc 2 ![a, b] hg (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all)
      have hmemL : ∀ i, MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(![a, b] : Fin 2 → G) i, hg i⟩) e ∈
          barM M (L.map (MulAut.conj ((![a, b] : Fin 2 → G) i)).toMonoidHom) :=
        fun i => (conj_noncentral heL he3 hnc (hg i)).1
      have hneL : ∀ i, L ≠ L.map (MulAut.conj ((![a, b] : Fin 2 → G) i)).toMonoidHom := by
        intro i
        fin_cases i
        · exact Ne.symm hLa
        · exact Ne.symm hLb
      have hE₂cent : E₂ ≤ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        refine hE₂cl.trans ?_
        rw [closure_le]
        rintro _ ⟨i, rfl⟩
        exact barM_le_centralizer hLc (hLc.map_conj (hg i)) (hneL i) (hmemL i)
      have hce : ∀ c ∈ E₂, e * c = c * e := fun c hc =>
        Subgroup.mem_centralizer_iff.mp (hE₂cent hc) e heL
      obtain ⟨hEab, hEcard⟩ := elemAbelian_zpowers_sup he3 hnc hE₂ hE₂cent hce
      set W := I ⊔ L.map (MulAut.conj a).toMonoidHom ⊔ L.map (MulAut.conj b).toMonoidHom ⊔
        pCoreOf 2 M with hW
      have hWM : W ≤ M := sup_le (sup_le (sup_le hIM (hconjM a ha)) (hconjM b hb))
        (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
      have hWN : W ≤ normalizer (I : Set G) := sup_le (sup_le (sup_le le_normalizer
        (hconjN a ha hLa)) (hconjN b hb hLb)) hVM
      have hLW : ∀ i, L.map (MulAut.conj ((![a, b] : Fin 2 → G) i)).toMonoidHom ≤ W := by
        intro i
        fin_cases i
        · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
        · exact le_sup_right.trans le_sup_left
      refine hlift W hWM hWN (zpowers e ⊔ E₂) (sup_le ?_ ?_) hEab (by rw [hEcard, hE₂card]; norm_num)
      · rw [zpowers_le]
        exact barM_mono (le_sup_left.trans (le_sup_left.trans le_sup_left)) heI
      · refine hE₂cl.trans ?_
        rw [closure_le]
        rintro _ ⟨i, rfl⟩
        exact barM_mono (hLW i) (hmemL i)
    · push Not at h3c
      obtain ⟨m, hm, hne⟩ : ∃ m ∈ M, L.map (MulAut.conj m).toMonoidHom ≠ L := by
        by_contra hcon
        push Not at hcon
        apply hNL
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have h := hcon g g.2
        rw [← h]
        exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
      by_cases hr : 2 ≤ CFSG.Open.pRank 3 (barM M L)
      ·
        obtain ⟨E0, hE0L, hE0, hE0card⟩ :=
          CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (barM M L)
        have hE0p : IsPGroup 3 ↥E0 := fun x => ⟨1, Subtype.ext (by simpa using hE0.2 _ x.2)⟩
        obtain ⟨K9, hK9⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hE0p
          (n := 2) (by rw [hE0card]; exact Nat.pow_le_pow_right (by norm_num) hr)
        set E9 := K9.map E0.subtype with hE9
        have hE9le : E9 ≤ E0 := Subgroup.map_subtype_le K9
        have hE9ab : IsElemAbelian 3 E9 := by
          have := hE0.1
          exact ⟨isMulCommutative_anti hE9le, fun x hx => hE0.2 x (hE9le hx)⟩
        have hE9card : Nat.card E9 = 3 ^ 2 := by
          rw [hE9, Subgroup.card_map_of_injective E0.subtype_injective, hK9]
        set c := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m, hm⟩) with hc
        set E9' := E9.map c.toMonoidHom with hE9'
        have hE9'L : E9' ≤ barM M (L.map (MulAut.conj m).toMonoidHom) := by
          rw [barM_map_conj hm]
          exact Subgroup.map_mono (hE9le.trans hE0L)
        have hE9'ab : IsElemAbelian 3 E9' :=
          CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE9ab _
        have hE9'card : Nat.card E9' = 3 ^ 2 := by
          rw [hE9', Subgroup.card_map_of_injective c.injective, hE9card]
        have hE9'cent : E9' ≤ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
          hE9'L.trans (barM_le_centralizer hLc (hLc.map_conj hm) (Ne.symm hne))
        have hce : ∀ c ∈ E9', e * c = c * e := fun c hc =>
          Subgroup.mem_centralizer_iff.mp (hE9'cent hc) e heL
        obtain ⟨hEab, hEcard⟩ := elemAbelian_zpowers_sup he3 hnc hE9'ab hE9'cent hce
        set W := I ⊔ L.map (MulAut.conj m).toMonoidHom ⊔ pCoreOf 2 M with hW
        have hWM : W ≤ M := sup_le (sup_le hIM (hconjM m hm)) (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
        have hWN : W ≤ normalizer (I : Set G) :=
          sup_le (sup_le le_normalizer (hconjN m hm hne)) hVM
        refine hlift W hWM hWN (zpowers e ⊔ E9') (sup_le ?_ ?_) hEab
          (by rw [hEcard, hE9'card]; norm_num)
        · rw [zpowers_le]
          exact barM_mono (le_sup_left.trans le_sup_left) heI
        · exact hE9'L.trans (barM_mono (le_sup_right.trans le_sup_left))
      ·
        push Not at hr
        refine ⟨Q, hd.base, fun q hq => ?_⟩
        obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
        have hk' : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hLq : L.map (MulAut.conj q).toMonoidHom = L := by
          by_contra hLq
          have h2 : L.map (MulAut.conj (q ^ 2)).toMonoidHom ≠ L :=
            map_conj_pow_ne Nat.prime_three hk' hLq (d := 2) (by norm_num) (by norm_num)
          have h12 := map_conj_pow_inj Nat.prime_three hk' hLq (i := 1) (j := 2) (by norm_num)
            (by norm_num)
          rw [pow_one] at h12
          exact h12 (h3c q (hQM hq) (q ^ 2) (M.pow_mem (hQM hq) 2) hLq h2)
        by_contra hIq'
        have hIq : I.map (MulAut.conj q).toMonoidHom ≠ I := fun h =>
          hIq' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
        have h1 := horbitI q hq hLq hIq 3 le_rfl
        have h2 := pRank_le_pRank_barM hLM (M := M) (L := L)
        omega
  ·
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra h
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by decide)
    refine ⟨Q, hd.base, fun q hq => ?_⟩
    obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
    have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hLq : L.map (MulAut.conj q).toMonoidHom = L := by
      by_contra hLq
      have h4 := le_pRank_of_conj hLc heL he3 hnc 4 (fun i => q ^ (i : ℕ))
        (fun i => M.pow_mem (hQM hq) _) (by
          intro i j hij
          have hne' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
          rcases lt_or_gt_of_ne hne' with h | h
          · exact map_conj_pow_inj hp hk' hLq h (by omega)
          · exact (map_conj_pow_inj hp hk' hLq h (by omega)).symm)
      omega
    by_contra hIq'
    have hIq : I.map (MulAut.conj q).toMonoidHom ≠ I := fun h =>
      hIq' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have := horbitI q hq hLq hIq 5 hp5
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
