module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Sylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Local
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Pick
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Tools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.NormalizerQuotient

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isSylowTwoIn_of_le_sup_odd {W Z O : Subgroup X} (hZW : Z ≤ W) (hZ : IsPGroup 2 ↥Z)
    (hO : Odd (Nat.card O)) (hZO : Z ≤ normalizer (O : Set X)) (hW : W ≤ O ⊔ Z) :
    IsSylowTwoIn W Z := by
  have _ := ‹Finite X›
  refine ⟨hZW, hZ, ?_⟩
  have htriv : ∀ x : X, x ∈ Z → x ∈ O → x = 1 := by
    intro x hxZ hxO
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hZ) ⟨x, hxZ⟩
    have hk' : orderOf x = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
    have hd : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    have hcop : Nat.Coprime (2 ^ k) (Nat.card O) := (Nat.coprime_two_left.2 hO).pow_left k
    have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop (hk' ▸ dvd_rfl) hd
    exact orderOf_eq_one_iff.1 h1
  have hdecomp : ∀ w ∈ W, ∃ o ∈ W ⊓ O, ∃ ζ ∈ Z, o * ζ = w := by
    intro w hw
    have hw' : w ∈ ((O ⊔ Z : Subgroup X) : Set X) := hW hw
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O Z hZO] at hw'
    obtain ⟨o, ho, ζ, hζ, rfl⟩ := hw'
    refine ⟨o, ⟨?_, ho⟩, ζ, hζ, rfl⟩
    have h1 : o = (o * ζ) * ζ⁻¹ := by group
    rw [h1]
    exact W.mul_mem hw (W.inv_mem (hZW hζ))
  let f : ↥(W ⊓ O) → ↥W ⧸ Z.subgroupOf W := fun a => QuotientGroup.mk ⟨(a : X), a.2.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : (⟨(a : X), a.2.1⟩ : ↥W)⁻¹ * ⟨(b : X), b.2.1⟩ ∈ Z.subgroupOf W :=
        QuotientGroup.eq.1 hab
      have h2 : (a : X)⁻¹ * b ∈ Z := h1
      have h3 : (a : X)⁻¹ * b ∈ O := O.mul_mem (O.inv_mem a.2.2) b.2.2
      exact Subtype.ext (inv_mul_eq_one.1 (htriv _ h2 h3))
    · intro q
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨o, ho, ζ, hζ, hoζ⟩ := hdecomp w w.2
      refine ⟨⟨o, ho⟩, ?_⟩
      show (QuotientGroup.mk ⟨o, ho.1⟩ : ↥W ⧸ Z.subgroupOf W) = QuotientGroup.mk w
      rw [QuotientGroup.eq]
      show o⁻¹ * (w : X) ∈ Z
      have h1 : o⁻¹ * (w : X) = ζ := by rw [← hoζ]; group
      rw [h1]
      exact hζ
  have hrel : Z.relIndex W = Nat.card (W ⊓ O : Subgroup X) := by
    rw [Subgroup.relIndex, Subgroup.index]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [hrel]
  have hodd : Odd (Nat.card (W ⊓ O : Subgroup X)) :=
    Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le inf_le_right)
  intro h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem le_centralizer_of_isPCompIn_of_normal_pgroup {N E Z : Subgroup X} (hE : IsPCompIn 2 N E)
    (hZN : Z ≤ N) (hNZ : N ≤ normalizer (Z : Set X)) (hZ : IsPGroup 2 ↥Z) :
    E ≤ centralizer (Z : Set X) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEN, hEcomp⟩ := hE
  have hZ'norm : (Z.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).2 hNZ
  have hZ'p : IsPGroup 2 ↥(Z.subgroupOf N) :=
    hZ.of_equiv (Subgroup.subgroupOfEquivOfLe hZN).symm
  rcases contains_or_normalizes_core 2 (E.subgroupOf N) (Z.subgroupOf N) hEcomp
      hZ'norm.isSubnormal with hle | ⟨-, hcomm⟩
  ·
    exfalso
    have hEZ : E ≤ Z := fun x hx => hle (show (⟨x, hEN hx⟩ : ↥N) ∈ E.subgroupOf N from hx)
    have hq : IsTwoGenQuasi ↥E :=
      (isTwoGenQuasi_subgroupOf_iff hEN).1 (isPComponent_two_iff.1 hEcomp).2
    have hEp : IsPGroup 2 ↥E := hZ.to_le hEZ
    have hnt : Nontrivial (↥E ⧸ pPrimeCore 2 ↥E) := CFSG.LocalCores.isQuasisimple_nontrivial hq.2
    obtain ⟨hperf, -⟩ := hq.2
    have hnil : Group.IsNilpotent (↥E ⧸ pPrimeCore 2 ↥E) := (hEp.to_quotient _).isNilpotent
    exact Group.IsPerfect.not_isNilpotent _ hnil
  · intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro ζ hζ
    have he' : (⟨e, hEN he⟩ : ↥N) ∈ E.subgroupOf N := he
    have hζ' : (⟨ζ, hZN hζ⟩ : ↥N) ∈ Z.subgroupOf N := hζ
    have h1 : ⁅(⟨e, hEN he⟩ : ↥N), ⟨ζ, hZN hζ⟩⁆ ∈ pPrimeCoreOf 2 (E.subgroupOf N) :=
      hcomm (Subgroup.commutator_mem_commutator he' hζ')
    have h2 : ⁅(⟨e, hEN he⟩ : ↥N), ⟨ζ, hZN hζ⟩⁆ ∈ Z.subgroupOf N := by
      rw [commutatorElement_def]
      exact (Z.subgroupOf N).mul_mem (hZ'norm.conj_mem _ hζ' _) ((Z.subgroupOf N).inv_mem hζ')
    have h3 := eq_one_of_mem_pPrimeCoreOf_of_isPGroup h1 hZ'p h2
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact (congrArg Subtype.val h3).symm

theorem isPCompIn_normalizer_of_centralizer {E Z : Subgroup X}
    (hE : IsPCompIn 2 (centralizer (Z : Set X)) E) : IsPCompIn 2 (normalizer (Z : Set X)) E := by
  have hCN : centralizer (Z : Set X) ≤ normalizer (Z : Set X) :=
    Subgroup.centralizer_le_normalizer (Z : Set X)
  obtain ⟨hEC, hEcomp⟩ := hE
  have hEN : E ≤ normalizer (Z : Set X) := hEC.trans hCN
  refine ⟨hEN, ?_⟩
  have hnorm : ((centralizer (Z : Set X)).subgroupOf (normalizer (Z : Set X))).Normal :=
    inferInstance
  obtain ⟨hsub, hquasi⟩ := isPComponent_two_iff.1 hEcomp
  exact isPComponent_two_iff.2
    ⟨isSubnormal_subgroupOf_of_normal_overgroup hEC hCN hsub hnorm,
      (isTwoGenQuasi_subgroupOf_iff hEN).2 ((isTwoGenQuasi_subgroupOf_iff hEC).1 hquasi)⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem forall_comm_mem_of_sSup {S : Set (Subgroup X)} {O : Subgroup X} {p : X}
    (hp : p ∈ normalizer (O : Set X)) (hS : ∀ A ∈ S, A ≤ normalizer (O : Set X))
    (h : ∀ A ∈ S, ∀ a ∈ A, ⁅a, p⁆ ∈ O) : ∀ a ∈ sSup S, ⁅a, p⁆ ∈ O := by
  let U : Subgroup X :=
    { carrier := {a | a ∈ normalizer (O : Set X) ∧ ⁅a, p⁆ ∈ O}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have h1 : ⁅a * b, p⁆ = a * ⁅b, p⁆ * a⁻¹ * ⁅a, p⁆ := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact O.mul_mem (((Subgroup.mem_normalizer_iff.1 ha) _).1 hbp) hap
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have h1 : ⁅a⁻¹, p⁆ = a⁻¹ * (⁅a, p⁆)⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [h1]
        have ha' : a⁻¹ ∈ normalizer (O : Set X) := Subgroup.inv_mem _ ha
        have h2 := ((Subgroup.mem_normalizer_iff.1 ha') _).1 (O.inv_mem hap)
        rw [inv_inv] at h2
        exact h2 }
  have hSU : sSup S ≤ U := sSup_le fun A hA a ha => ⟨hS A hA ha, h A hA a ha⟩
  intro a ha
  exact (show a ∈ normalizer (O : Set X) ∧ ⁅a, p⁆ ∈ O from hSU ha).2

theorem mem_zStar_of_comm_cover {K E : Subgroup X} {p : X} (hpK : p ∈ K) (hEK : E ≤ K)
    (hKE : K ≤ pPrimeCoreOf 2 K ⊔ E) (hpE : ∀ e ∈ E, ⁅e, p⁆ ∈ pPrimeCoreOf 2 K) :
    p ∈ zStar K := by
  have hpO : p ∈ normalizer (pPrimeCoreOf 2 K : Set X) := mem_normalizer_pPrimeCoreOf_of_mem hpK
  refine ⟨hpK, Subgroup.le_normalizer hpK, hpO, ?_⟩
  have hS : ∀ A ∈ ({pPrimeCoreOf 2 K, E} : Set (Subgroup X)),
      A ≤ normalizer (pPrimeCoreOf 2 K : Set X) := by
    intro A hA
    rcases Set.mem_insert_iff.1 hA with hA | hA
    · rw [hA]
      exact Subgroup.le_normalizer
    · rw [Set.mem_singleton_iff.1 hA]
      exact fun e he => mem_normalizer_pPrimeCoreOf_of_mem (hEK he)
  have h : ∀ A ∈ ({pPrimeCoreOf 2 K, E} : Set (Subgroup X)), ∀ a ∈ A,
      ⁅a, p⁆ ∈ pPrimeCoreOf 2 K := by
    intro A hA a ha
    rcases Set.mem_insert_iff.1 hA with hA | hA
    · rw [hA] at ha
      have h1 : ⁅a, p⁆ = a * (p * a⁻¹ * p⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h1]
      exact Subgroup.mul_mem _ ha
        (((Subgroup.mem_normalizer_iff.1 hpO) _).1 (Subgroup.inv_mem _ ha))
    · rw [Set.mem_singleton_iff.1 hA] at ha
      exact hpE a ha
  intro k hk
  refine forall_comm_mem_of_sSup hpO hS h k ?_
  rw [sSup_pair]
  exact hKE hk

set_option linter.unusedSectionVars false in
theorem le_of_le_sup_of_isPGroup {P Z O : Subgroup X} (hZP : Z ≤ P) (hP : IsPGroup 2 ↥P)
    (hO : Odd (Nat.card O)) (hZO : Z ≤ normalizer (O : Set X)) (hPO : P ≤ O ⊔ Z) : P ≤ Z := by
  intro p hp
  have hmem : p ∈ ((O ⊔ Z : Subgroup X) : Set X) := hPO hp
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O Z hZO] at hmem
  obtain ⟨o, ho, ζ, hζ, hoζ⟩ := hmem
  have hoζ' : o * ζ = p := hoζ
  have hoP : o ∈ P := by
    have h1 : o = p * ζ⁻¹ := by rw [← hoζ']; group
    rw [h1]
    exact P.mul_mem hp (P.inv_mem (hZP hζ))
  obtain ⟨i, hi⟩ := hP ⟨o, hoP⟩
  have hi' : o ^ (2 ^ i) = 1 := by
    simpa using congrArg Subtype.val hi
  have ho1 : o = 1 := eq_one_of_pow_two_pow_of_mem_odd_subgroup hO ho hi'
  rw [← hoζ', ho1, one_mul]
  exact hζ

set_option linter.unusedSectionVars false in
theorem le_pTwoCoreOf {F P : Subgroup X} (hPF : P ≤ F) (hP : IsPGroup 2 ↥P)
    (hn : F ≤ normalizer (P : Set X)) : P ≤ pTwoCoreOf F := by
  have hnorm : (P.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPF).mpr hn
  have hsub : IsPGroup 2 (P.subgroupOf F) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPF).symm
  have hcore : P.subgroupOf F ≤ pCore 2 ↥F := le_sSup ⟨hnorm, hsub⟩
  unfold pTwoCoreOf
  rw [← Subgroup.map_subgroupOf_eq_of_le hPF]
  exact Subgroup.map_mono hcore

set_option linter.unusedSectionVars false in
theorem pTwoCoreOf_le_oddTwoCoreOf (F : Subgroup X) : pTwoCoreOf F ≤ oddTwoCoreOf F := by
  have hmap : (pCore 2 ↥F).map (QuotientGroup.mk' (pPrimeCore 2 ↥F)) ≤
      pCore 2 (↥F ⧸ pPrimeCore 2 ↥F) :=
    le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal _ (QuotientGroup.mk'_surjective _),
      (CFSG.pCore_isPGroup (p := 2) (G := ↥F)).map _⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hmap ⟨x, hx, rfl⟩, rfl⟩

set_option linter.unusedSectionVars false in
theorem isPGroup_pTwoCoreOf (F : Subgroup X) : IsPGroup 2 ↥(pTwoCoreOf F) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥F)).map F.subtype

set_option linter.unusedSectionVars false in
theorem le_normalizer_pTwoCoreOf (F : Subgroup X) : F ≤ normalizer (pTwoCoreOf F : Set X) := by
  have hle : pTwoCoreOf F ≤ F := Subgroup.map_subtype_le _
  have hsub : (pTwoCoreOf F).subgroupOf F = pCore 2 ↥F :=
    Subgroup.comap_map_eq_self_of_injective F.subtype_injective _
  have hn : ((pTwoCoreOf F).subgroupOf F).Normal := by
    rw [hsub]
    exact CFSG.pCore_normal
  exact (normal_subgroupOf_iff_le_normalizer hle).mp hn

set_option linter.unusedSectionVars false in
theorem pTwoCoreOf_le (F : Subgroup X) : pTwoCoreOf F ≤ F :=
  Subgroup.map_subtype_le _

set_option linter.unusedSectionVars false in
theorem not_le_oddTwoCoreOf_of_isPCompIn {F E : Subgroup X} (hE : IsPCompIn 2 F E) :
    ¬ E ≤ oddTwoCoreOf F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  obtain ⟨hEF, hEc⟩ := hE
  obtain ⟨hsubn, hq⟩ := isPComponent_two_iff.1 hEc
  have hcore : pPrimeCore 2 ↥(E.subgroupOf F) =
      (pPrimeCore 2 ↥F).subgroupOf (E.subgroupOf F) :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 _
      hsubn
  have hP : IsPGroup 2 (↥(E.subgroupOf F) ⧸ pPrimeCore 2 ↥(E.subgroupOf F)) := by
    intro r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
    have hxW : ((x : ↥F) : X) ∈ oddTwoCoreOf F := hle (Subgroup.mem_subgroupOf.mp x.2)
    obtain ⟨y, hy, hyx⟩ := hxW
    have hyx' : y = (x : ↥F) := Subtype.ext hyx
    rw [hyx'] at hy
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥F ⧸ pPrimeCore 2 ↥F))
      ⟨QuotientGroup.mk' (pPrimeCore 2 ↥F) (x : ↥F), hy⟩
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥F)) ((x : ↥F) ^ (2 ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 : (x : ↥F) ^ (2 ^ k) ∈ pPrimeCore 2 ↥F := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : x ^ (2 ^ k) ∈ pPrimeCore 2 ↥(E.subgroupOf F) := by
      rw [hcore, Subgroup.mem_subgroupOf]
      simpa using h2
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr h3
  obtain ⟨hperf, hsimp, a, b, hab⟩ := hq.2
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq.2
  have hsolv : Group.IsSolvable
      (↥(E.subgroupOf F) ⧸ pPrimeCore 2 ↥(E.subgroupOf F)) := by
    have : Group.IsNilpotent (↥(E.subgroupOf F) ⧸ pPrimeCore 2 ↥(E.subgroupOf F)) :=
      hP.isNilpotent
    infer_instance
  exact Group.IsPerfect.not_isSolvable _ hsolv

set_option linter.unusedSectionVars false in
theorem aux_comm_mem_of_isPCompIn_oddTwoCoreOf_map {F E : Subgroup X} (hEF : E ≤ F) :
    (pPrimeCoreOf 2 (E.subgroupOf F)).map F.subtype = pPrimeCoreOf 2 E := by
  let e : ↥(E.subgroupOf F) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEF
  unfold pPrimeCoreOf
  rw [Subgroup.map_map, ← pPrimeCore_map_iso 2 e, Subgroup.map_map]
  rfl

set_option linter.unusedSectionVars false in
theorem comm_mem_of_isPCompIn_oddTwoCoreOf {F E : Subgroup X} (hE : IsPCompIn 2 F E) :
    ∀ e ∈ E, ∀ w ∈ oddTwoCoreOf F, ⁅e, w⁆ ∈ pPrimeCoreOf 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnotle := not_le_oddTwoCoreOf_of_isPCompIn hE
  obtain ⟨hEF, hEc⟩ := hE
  have hWF : oddTwoCoreOf F ≤ F := oddTwoCoreOf_le F
  have hWn : ((oddTwoCoreOf F).subgroupOf F).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWF).mpr (le_normalizer_oddTwoCoreOf F)
  rcases contains_or_normalizes_core 2 (E.subgroupOf F) ((oddTwoCoreOf F).subgroupOf F) hEc
      hWn.isSubnormal with hle | ⟨-, hcomm⟩
  · exfalso
    apply hnotle
    intro e he
    have h1 : (⟨e, hEF he⟩ : ↥F) ∈ E.subgroupOf F := Subgroup.mem_subgroupOf.mpr he
    exact Subgroup.mem_subgroupOf.mp (hle h1)
  · intro e he w hw
    have hc : ⁅(⟨e, hEF he⟩ : ↥F), (⟨w, hWF hw⟩ : ↥F)⁆ ∈
        ⁅E.subgroupOf F, (oddTwoCoreOf F).subgroupOf F⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr he)
        (Subgroup.mem_subgroupOf.mpr hw)
    have h2 : ⁅e, w⁆ ∈ (pPrimeCoreOf 2 (E.subgroupOf F)).map F.subtype :=
      ⟨_, hcomm hc, rfl⟩
    rw [aux_comm_mem_of_isPCompIn_oddTwoCoreOf_map hEF] at h2
    exact h2

end CFSG.OddStandard.Solomon75
