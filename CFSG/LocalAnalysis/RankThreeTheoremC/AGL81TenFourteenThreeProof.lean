module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedTenFourteenThree
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.RankThree.PartTwo.Sec19.Item194Proof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin
open Subgroup

namespace TenFourteenThree

theorem nonempty_quot_mulEquiv_of_sup_eq_top {Λ : Type*} [Group Λ] [Finite Λ] {K : Subgroup Λ}
    (hK : K ⊔ CFSG.pCore 2 Λ = ⊤) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Λ ⧸ CFSG.pCore 2 Λ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 Λ with hN
  haveI hNn : N.Normal := CFSG.pCore_normal
  set f : ↥K →* Λ ⧸ N := (QuotientGroup.mk' N).comp K.subtype with hf
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x ∈ ((K ⊔ N : Subgroup Λ) : Set Λ) := by rw [hK]; exact mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨k, hk, n, hn, rfl⟩ := hx
    refine ⟨⟨k, hk⟩, ?_⟩
    simp only [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa using N.inv_mem hn
  have hker : f.ker = CFSG.pCore 2 ↥K := by
    have hk : f.ker = N.comap K.subtype := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    apply le_antisymm
    · rw [hk]
      exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (hNn.comap _)
        (IsPGroup.comap_of_injective CFSG.pCore_isPGroup _ K.subtype_injective)
    · rw [← Subgroup.map_eq_bot_iff, ← le_bot_iff,
        ← CFSG.RankThree.PartTwo.Sec18.pCore_quotient_pCore_eq_bot (X := Λ) 2]
      exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (CFSG.pCore_normal.map f hsurj)
        (CFSG.pCore_isPGroup.map f)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_cover_of_commutator_le {L : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : G} (hao : orderOf a = p) (hc : ⁅zpowers a, L⁆ ≤ pCoreOf 2 L) :
    ∀ l ∈ L, ∃ c ∈ L ⊓ centralizer ({a} : Set G), c⁻¹ * l ∈ pCoreOf 2 L := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pCoreOf 2 L with hNdef
  set Y := normalizer (N : Set G) with hY
  have hNL : N ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have haL : a ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      have h := hNL (hc (commutator_mem_commutator (mem_zpowers a) hl))
      have := L.mul_mem h hl
      simpa [commutatorElement_def, mul_assoc] using this
    · intro hl
      have h := hNL (hc (commutator_mem_commutator (inv_mem (mem_zpowers a)) hl))
      have := L.mul_mem h hl
      simpa [commutatorElement_def, mul_assoc] using this
  have haY : a ∈ Y := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L haL
  have hLY : L ≤ Y := fun l hl =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (le_normalizer hl)
  have hzY : zpowers a ≤ Y := (zpowers_le).mpr haY
  set T : Subgroup Y := (zpowers a).subgroupOf Y with hT
  set Nn : Subgroup Y := N.subgroupOf Y with hNn
  have hzp : IsPGroup p (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  haveI : Fact (IsPGroup p T) := ⟨IsPGroup.comap_of_injective hzp _ Y.subtype_injective⟩
  have hNnN : Nn.Normal := normal_in_normalizer
  have hNn2 : IsPGroup 2 Nn := IsPGroup.comap_of_injective hN2 _ Y.subtype_injective
  have hcop : Nat.Coprime p (Nat.card Nn) := by
    obtain ⟨k, hk⟩ := hNn2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hcent := CFSG.centralizer_map_quotient_eq_map_centralizer p T Nn hNnN hcop
  intro l hl
  set ly : Y := ⟨l, hLY hl⟩
  have hmem : QuotientGroup.mk' Nn ly ∈
      centralizer ((T.map (QuotientGroup.mk' Nn) : Subgroup (Y ⧸ Nn)) : Set (Y ⧸ Nn)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    have htz : (t : G) ∈ zpowers a := ht
    have h := hc ((commutator_comm (zpowers a) L) ▸
      commutator_mem_commutator (L.inv_mem hl) (inv_mem htz))
    simpa [ly, commutatorElement_def, mul_assoc] using h
  rw [hcent] at hmem
  obtain ⟨y, hy, hyl⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hyl
  have hyl' : (y : G)⁻¹ * l ∈ N := by simpa [ly] using hyl
  have hyL : (y : G) ∈ L := by
    have := L.mul_mem hl (L.inv_mem (hNL hyl'))
    simpa using this
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hyL, ?_⟩, hyl'⟩
  rw [mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  have hat : (⟨a, haY⟩ : Y) ∈ T := by rw [hT, mem_subgroupOf]; exact mem_zpowers a
  have := (mem_centralizer_iff.mp hy) _ hat
  exact congrArg Subtype.val this

theorem exists_isTwoPrimeComponent_centralizer_iso {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (ha : a ∈ M)
    (hao : orderOf a = p) (hc : ⁅zpowers a, L⁆ ≤ pCoreOf 2 L) :
    ∃ I : Subgroup G, IsTwoPrimeComponent (centralizer ({a} : Set G) ⊓ M) I ∧ I ≤ L ∧
      Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥L ⧸ CFSG.pCore 2 ↥L) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card L → r ∣ Nat.card I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({a} : Set G) ⊓ M with hCdef
  set C₀ := L ⊓ C with hC₀
  set P := CFSG.pCore 2 ↥L with hP
  haveI : P.Normal := CFSG.pCore_normal
  set q := QuotientGroup.mk' P with hq
  set C₀' := C₀.subgroupOf L with hC₀'
  have hcov := exists_cover_of_commutator_le hp hp2 hao hc
  have hC₀P : C₀' ⊔ P = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨l, hl⟩ -
    obtain ⟨c, ⟨hcL, hcC⟩, hcl⟩ := hcov l hl
    obtain ⟨n, hn, hnl⟩ := hcl
    have hlc : (⟨l, hl⟩ : L) = ⟨c, hcL⟩ * n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [show (n : G) = c⁻¹ * l from hnl]
      group
    rw [hlc]
    exact mul_mem (mem_sup_left (by
      rw [hC₀', mem_subgroupOf]
      exact ⟨hcL, hcC, hL.le hcL⟩)) (mem_sup_right hn)
  have hLperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    have := CFSG.RankThree.PartTwo.Sec18.commutator_subgroupOf_eq (le_refl L) hL.perfect
    rwa [subgroupOf_self] at this
  have hqtop : ⁅(⊤ : Subgroup (↥L ⧸ P)), (⊤ : Subgroup (↥L ⧸ P))⁆ = (⊤ : Subgroup (↥L ⧸ P)) := by
    have h := congrArg (Subgroup.map q) hLperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective P)] at h
  have hmapC₀ : C₀'.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) hC₀P
    rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective P),
      show P.map q = ⊥ by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'], sup_bot_eq] at h
  set I' := CFSG.Quasithin.perfectCore C₀' with hI'
  have hI'top : I' ⊔ P = ⊤ := by
    have h1 : I'.map q = ⊤ := by
      rw [hI', CFSG.Quasithin.map_perfectCore, hmapC₀,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect hqtop]
    have h2 := Subgroup.comap_map_eq q I'
    rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm
  set I := I'.map L.subtype with hIdef
  have hIeq : I = CFSG.Quasithin.perfectCore C₀ := by
    rw [hIdef, hI', CFSG.Quasithin.map_perfectCore, hC₀',
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have e : ↥I' ≃* ↥I := I'.equivMapOfInjective L.subtype L.subtype_injective
  obtain ⟨e₁⟩ := nonempty_quot_mulEquiv_of_sup_eq_top hI'top
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.RankThree.PartTwo.Sec18.isQuasisimple_of_mem_oTwoComponentsIn
      (CFSG.RankThree.PartTwo.Sec19.Item194Proof.mem_oTwoComponentsIn_of_isTwoPrimeComponent hL)
  have hIq : CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((e₁.symm.trans (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e))))
      hLq
  have hIC : I ≤ C := by rw [hIeq]; exact (CFSG.Quasithin.perfectCore_le C₀).trans inf_le_right
  have hIL : I ≤ L := by rw [hIeq]; exact (CFSG.Quasithin.perfectCore_le C₀).trans inf_le_left
  have hIperf : ⁅I, I⁆ = I := by rw [hIeq]; exact CFSG.Quasithin.perfectCore_perfect C₀
  have hIsn : CFSG.Open.IsSubnormal I C := by
    rw [hIeq]
    exact CFSG.Quasithin.A3.subnormal_perfectCore
      (CFSG.Quasithin.A3.subnormal_inf_right hL.subnormal inf_le_right)
  refine ⟨I, CFSG.RankThree.PartTwo.Sec19.Item194Proof.isTwoPrimeComponent_of_mem_oTwoComponentsIn
    (CFSG.RankThree.PartTwo.Sec18.mem_oTwoComponentsIn_of_quasisimple hIC
      (CFSG.RankThree.PartTwo.Sec19.Item194Proof.isSubnormal_subgroupOf_of_open hIsn) hIperf hIq),
    hIL, ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).symm.trans e₁⟩,
    fun r hr hr2 hrL => ?_⟩
  have hcardL := Subgroup.card_eq_card_quotient_mul_card_subgroup P
  have hrP : ¬ r ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
  have hrQ : r ∣ Nat.card (L ⧸ P) := by
    rw [hcardL] at hrL
    exact ((hr.dvd_mul).mp hrL).resolve_right hrP
  rw [← Nat.card_congr e₁.toEquiv] at hrQ
  rw [← Nat.card_congr e.toEquiv]
  exact hrQ.trans (Subgroup.card_quotient_dvd_card _)

theorem exists_isTwoPrimeComponent_centralizer {M L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (ha : a ∈ M) (hao : orderOf a = p)
    (hc : ⁅zpowers a, L⁆ ≤ pCoreOf 2 L) :
    ∃ I : Subgroup G, IsTwoPrimeComponent (centralizer ({a} : Set G) ⊓ M) I ∧ I ≤ L ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card L → r ∣ Nat.card I := by
  obtain ⟨I, hI, hIL, -, hdvd⟩ := exists_isTwoPrimeComponent_centralizer_iso hL hp hp2 ha hao hc
  exact ⟨I, hI, hIL, hdvd⟩

end TenFourteenThree

variable {G : Type} [Group G] [Finite G]

theorem agl81TenFourteenThreeCfg_of (h1014 : AGL81TenFourteenTwoThree G) :
    AGL81TenFourteenThreeCfg G := by
  intro hS P M H Q K hd L hL h3 a ha hao hC hU hcomm
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  obtain ⟨I, hI, -, hdvd⟩ := TenFourteenThree.exists_isTwoPrimeComponent_centralizer
    hL.toIsTwoPrimeComponent Nat.prime_three (by decide) ha hao hcomm
  exact h1014 hS P M H₁ R₁ hesc a ha hao hC hU I hI (hdvd 3 Nat.prime_three (by decide) h3)

end CFSG.LocalAnalysis.RankThreeTheoremC
