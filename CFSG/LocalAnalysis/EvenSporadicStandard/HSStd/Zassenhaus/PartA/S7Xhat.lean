module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Lam
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Dihedral
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.Schreier.PairHSFaithful
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

section HS

theorem card_mulAut_of_isSporadic_hs
    {N : Type} [Group N] (h : IsSporadic N .HS) : Nat.card (MulAut N) = 88704000 := by
  obtain ⟨e⟩ := h
  obtain ⟨-, -, -, -, hc⟩ := CFSG.Sporadic.SmallOddCore.hs_full_automorphism_model
  have e2 : N ≃* CFSG.Sporadic.Schreier.hsP := e.trans CFSG.Sporadic.Schreier.hsPermEquiv
  rw [Nat.card_congr (MulAut.congr e2).toEquiv]
  exact hc

end HS

section Action

variable {X : Type} [Group X] [Finite X]

theorem ker_conjNormal_eq (N : Subgroup X) [N.Normal] :
    (MulAut.conjNormal : X →* MulAut N).ker = centralizer (N : Set X) := by
  ext x
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h n hn
    have h1 := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : X)) h
    simp only [MulAut.conjNormal_val, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro h
    ext ⟨n, hn⟩
    simp only [MulAut.conjNormal_val, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.2 (h n hn).symm

theorem card_dvd_card_centralizer_mul (N : Subgroup X) [N.Normal] :
    Nat.card X ∣ Nat.card (centralizer (N : Set X)) * Nat.card (MulAut N) := by
  haveI : Finite (MulAut N) :=
    Finite.of_injective (fun f : MulAut N => (f : N → N)) DFunLike.coe_injective
  have hker := ker_conjNormal_eq N
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAut.conjNormal : X →* MulAut N).ker
  have h2 : Nat.card (X ⧸ (MulAut.conjNormal : X →* MulAut N).ker) =
      Nat.card (MulAut.conjNormal : X →* MulAut N).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  have h3 : Nat.card (MulAut.conjNormal : X →* MulAut N).range ∣ Nat.card (MulAut N) :=
    Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card X = Nat.card (MulAut.conjNormal : X →* MulAut N).range *
      Nat.card (centralizer (N : Set X)) := by
    rw [h1, h2, hker]
  rw [h4, mul_comm]
  exact mul_dvd_mul_left _ h3

end Action

section Burnside

variable {X : Type} [Group X] [Finite X]

theorem card_eq_two_of_cent_le (hO : Open.fusionOddCore X = ⊥) {t : X} (ht : orderOf t = 2)
    (B : Subgroup X) [B.Normal] (htB : t ∈ B)
    (hcent : ∀ b ∈ B, b * t = t * b → b = 1 ∨ b = t) : Nat.card B = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : B := ⟨t, htB⟩ with ht'
  have ht'2 : orderOf t' = 2 := by rw [← ht, ← Subgroup.orderOf_coe]
  have hCB : ∀ b : B, b * t' = t' * b → b = 1 ∨ b = t' := by
    intro b hb
    rcases hcent b b.2 (congrArg Subtype.val hb) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have ht'ne : t' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht'2
    omega
  have hP : IsPGroup 2 (zpowers t') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht'2]
    norm_num
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have ht'S : t' ∈ S := hS (mem_zpowers t')
  have hSle : ∀ s ∈ S, s = 1 ∨ s = t' := by
    have hSp : IsPGroup 2 S := S.isPGroup'
    haveI : Nontrivial S := ⟨⟨⟨t', ht'S⟩, 1, fun h => ht'ne (congrArg Subtype.val h)⟩⟩
    haveI : Nontrivial (center S) := hSp.center_nontrivial
    have hZp : IsPGroup 2 (center S) := hSp.to_subgroup _
    have h2dvd : 2 ∣ Nat.card (center S) := by
      obtain ⟨n, hn⟩ := hZp.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact not_nontrivial_iff_subsingleton.2 (Nat.card_eq_one_iff_unique.1 hn).1 inferInstance
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 h2dvd
    set z' : B := z.1.1 with hz'
    have hz'2 : orderOf z' = 2 := by
      rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
    have hz'comm : ∀ s ∈ S, z' * s = s * z' := by
      intro s hs
      have := mem_center_iff.1 z.2 ⟨s, hs⟩
      have h2 := congrArg (fun a : S => (a : B)) this
      exact h2.symm
    have hz't : z' = t' := by
      rcases hCB z' (hz'comm t' ht'S) with h | h
      · rw [h, orderOf_one] at hz'2; omega
      · exact h
    intro s hs
    apply hCB s
    have := hz'comm s hs
    rw [hz't] at this
    exact this.symm
  have hScard : Nat.card S = 2 := by
    show Nat.card (S : Subgroup B) = 2
    have hsub : (S : Subgroup B) = zpowers t' := by
      apply le_antisymm
      · intro s hs
        rcases hSle s hs with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact mem_zpowers t'
      · rwa [zpowers_le]
    rw [hsub, Nat.card_zpowers, ht'2]
  have hcyc : IsCyclic S := isCyclic_of_prime_card (p := 2) hScard
  have h2dvd : 2 ∣ Nat.card B := by
    rw [← ht'2]; exact orderOf_dvd_natCard t'
  have hminFac : (Nat.card B).minFac = 2 := Nat.minFac_eq_two_iff _ |>.2 h2dvd
  have hcompl := IsCyclic.isComplement' (P := S) hminFac hcyc
  set K : Subgroup B := (MonoidHom.transferSylow S (hcyc.normalizer_le_centralizer hminFac)).ker
    with hK
  haveI hKn : K.Normal := MonoidHom.normal_ker _
  have hKodd : ¬ 2 ∣ Nat.card K :=
    MonoidHom.not_dvd_card_ker_transferSylow S (hcyc.normalizer_le_centralizer hminFac)
  have hKcard : Nat.card K * 2 = Nat.card B := by
    have := hcompl.card_mul_card
    rw [hScard] at this
    exact this
  set φ := MonoidHom.transferSylow S (hcyc.normalizer_le_centralizer hminFac) with hφ
  let K' : Subgroup X := K.map B.subtype
  haveI hK'n : K'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk, rfl⟩ := hn
    have hgB : g * (k : X) * g⁻¹ ∈ B := (‹B.Normal›).conj_mem (k : X) k.2 g
    set b : B := ⟨g * (k : X) * g⁻¹, hgB⟩ with hb
    have hord : orderOf b = orderOf k := by
      have h0 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (k : X)
      have h1 : orderOf (b : X) = orderOf b := Subgroup.orderOf_coe b
      have h2 : orderOf (k : X) = orderOf k := Subgroup.orderOf_coe k
      rw [← h1, ← h2]
      show orderOf (g * (k : X) * g⁻¹) = orderOf (k : X)
      simpa [MulAut.conj_apply] using h0
    have hodd : Odd (orderOf b) := by
      rw [hord]
      have hdvd : orderOf k ∣ Nat.card K := by
        have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
        rwa [← Subgroup.orderOf_coe (⟨k, hk⟩ : K)] at this
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      exact hKodd ((even_iff_two_dvd.1 hev).trans hdvd)
    have h1 : orderOf (φ b) ∣ 2 := by
      have := orderOf_dvd_natCard (φ b)
      rwa [hScard] at this
    have h2 : orderOf (φ b) ∣ orderOf b := orderOf_map_dvd φ b
    have h3 : orderOf (φ b) = 1 := by
      have h4 : orderOf (φ b) ∣ Nat.gcd (orderOf b) 2 := Nat.dvd_gcd h2 h1
      have h5 : Nat.gcd (orderOf b) 2 = 1 := by
        rw [Nat.gcd_comm]
        exact (Nat.coprime_two_left.2 hodd)
      rw [h5] at h4
      exact Nat.dvd_one.1 h4
    have h6 : φ b = 1 := orderOf_eq_one_iff.1 h3
    exact ⟨b, MonoidHom.mem_ker.2 h6, rfl⟩
  have hK'odd : Odd (Nat.card K') := by
    have : Nat.card K' = Nat.card K := Subgroup.card_map_of_injective B.subtype_injective
    rw [this]
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    exact hKodd (even_iff_two_dvd.1 hev)
  have hle := le_fusionOddCore_of_odd' hK'odd
  rw [hO] at hle
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have : (k : X) ∈ K' := ⟨k, hk, rfl⟩
    have h1 := hle this
    rw [Subgroup.mem_bot] at h1
    have : k = 1 := Subtype.ext h1
    rw [this]; exact one_mem _
  have : Nat.card K = 1 := by rw [hKbot]; exact Subgroup.card_bot
  omega

end Burnside

section Lhat

variable {X : Type} [Group X] [Finite X] {t : X}

theorem map_commutator_lam
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6) :
    (_root_.commutator ↥(centralizer ({t} : Set X))).map e.toMonoidHom =
      _root_.commutator (Multiplicative (ZMod 2) × MulAut A6) := by
  rw [_root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, ← _root_.commutator_def]

theorem commutator_lam_perfect
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6) :
    ⁅_root_.commutator ↥(centralizer ({t} : Set X)),
        _root_.commutator ↥(centralizer ({t} : Set X))⁆ =
      _root_.commutator ↥(centralizer ({t} : Set X)) := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_commutator, map_commutator_lam e, commutator_prod_alt6,
    ← Subgroup.map_commutator, innA6_perfect]

theorem lhat_perfect
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6) :
    ⁅centralizerDerived t, centralizerDerived t⁆ = centralizerDerived t := by
  unfold centralizerDerived
  rw [← Subgroup.map_commutator, commutator_lam_perfect e]

theorem lhat_equiv
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6) :
    Nonempty (↥(centralizerDerived t) ≃* A6) := by
  haveI := isSimple_alt6
  have f1 : ↥(centralizerDerived t) ≃* ↥(_root_.commutator ↥(centralizer ({t} : Set X))) :=
    (Subgroup.equivMapOfInjective (_root_.commutator ↥(centralizer ({t} : Set X)))
      (centralizer ({t} : Set X)).subtype (centralizer ({t} : Set X)).subtype_injective).symm
  have f2 := Subgroup.equivMapOfInjective (_root_.commutator ↥(centralizer ({t} : Set X)))
    e.toMonoidHom e.injective
  have f3 : ↥((_root_.commutator ↥(centralizer ({t} : Set X))).map e.toMonoidHom) ≃*
      ↥(innA6.map (MonoidHom.inr (Multiplicative (ZMod 2)) (MulAut A6))) :=
    MulEquiv.subgroupCongr (by rw [map_commutator_lam e, commutator_prod_alt6])
  have hinr : Function.Injective (MonoidHom.inr (Multiplicative (ZMod 2)) (MulAut A6)) :=
    fun a b h => (Prod.mk.inj h).2
  have f4 := (Subgroup.equivMapOfInjective innA6
    (MonoidHom.inr (Multiplicative (ZMod 2)) (MulAut A6)) hinr).symm
  have f5 : ↥innA6 ≃* A6 :=
    (MonoidHom.ofInjective (conj_injective_of_simple alt6_nonabelian)).symm
  exact ⟨(((f1.trans f2).trans f3).trans f4).trans f5⟩

theorem perfect_le_derived {H : Subgroup X} (hH : H ≤ centralizer ({t} : Set X))
    (hp : ⁅H, H⁆ = H) : H ≤ centralizerDerived t := by
  calc H = ⁅H, H⁆ := hp.symm
    _ ≤ centralizerDerived t := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, hH ha⟩ : ↥(centralizer ({t} : Set X))), ⟨b, hH hb⟩⁆, ?_, rfl⟩
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem normalClosure_eq_derived_of_le
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    (hle : normalClosureOf (centralizerDerived t) ≤ centralizer ({t} : Set X)) :
    normalClosureOf (centralizerDerived t) = centralizerDerived t := by
  have hnorm : (centralizerDerived t).Normal := by
    refine ⟨fun n hn g => ?_⟩
    set H : Subgroup X := (centralizerDerived t).map (MulAut.conj g).toMonoidHom with hH
    have hnc : (normalClosureOf (centralizerDerived t)).Normal := by
      unfold normalClosureOf; infer_instance
    have hHN : H ≤ normalClosureOf (centralizerDerived t) := by
      rintro _ ⟨m, hm, rfl⟩
      exact hnc.conj_mem m (Subgroup.subset_normalClosure hm) g
    have hHp : ⁅H, H⁆ = H := by
      rw [hH, ← Subgroup.map_commutator, lhat_perfect e]
    have := perfect_le_derived (hHN.trans hle) hHp
    exact this ⟨n, hn, rfl⟩
  apply le_antisymm
  · unfold normalClosureOf
    exact Subgroup.normalClosure_le_normal (fun x hx => hx)
  · exact Subgroup.subset_normalClosure

end Lhat

section Cases

variable {X : Type} [Group X] [Finite X]

theorem harris_cases
    (hHs : Harris311) (hU : U43Config) (hL : HarrisL39L43NoD8)
    (hKX : CFSG.SectionRank.IsKGroupCat X)
    (hO : Open.fusionOddCore X = ⊥) {t : X} (ht : orderOf t = 2)
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    {y c k : X} (hS : SigmaConfig t y c k) :
    centralizer ((normalClosureOf (centralizerDerived t) : Subgroup X) : Set X) = ⊥ ∧
      (Nonempty (↥(normalClosureOf (centralizerDerived t)) ≃* A6 × A6) ∨
        (LieModel ↥(normalClosureOf (centralizerDerived t)) .PSU 4 3 1 ∧
          Nat.card ↥(centralizer ({y} : Set X)) = 1944 ∧
          Nat.card ↥(centralizer ({y, c, t * c * t⁻¹, k, t * k * t⁻¹} : Set X)) = 3)) := by
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup X, N = normalClosureOf (centralizerDerived t) := ⟨_, rfl⟩
  rw [← hNdef]
  haveI hNn : N.Normal := by
    rw [hNdef]; unfold normalClosureOf; infer_instance
  have hLN : centralizerDerived t ≤ N := by
    rw [hNdef]; exact Subgroup.subset_normalClosure
  have h27c : Nat.card ↥(Subgroup.closure ({y, c, t * c * t⁻¹} : Set X)) = 27 :=
    hS.2.2.2.2.2.2.2.2.2.1
  have h27 : 27 ∣ Nat.card X := by
    have := Subgroup.card_subgroup_dvd_card
      (Subgroup.closure ({y, c, t * c * t⁻¹} : Set X))
    rwa [h27c] at this
  rcases cent_normal_dichotomy hO ht e (N := N) hLN with htB | hB
  ·
    exfalso
    have hNle : N ≤ centralizer ({t} : Set X) := by
      intro n hn
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 htB n hn
    have hNeq : N = centralizerDerived t := by
      rw [hNdef] at hNle ⊢
      exact normalClosure_eq_derived_of_le e hNle
    have hB2 : Nat.card (centralizer (N : Set X)) = 2 := by
      refine card_eq_two_of_cent_le hO ht _ htB ?_
      intro b hb hbt
      have hbc : b ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.2 hbt
      have hz := mem_zpowers_of_commute_derived ht e hbc fun l hl =>
        (mem_centralizer_iff.1 hb l (hLN hl)).symm
      obtain ⟨n, hn0⟩ := hz
      have hn : t ^ n = b := hn0
      rw [← hn]
      have hsq : t * t = 1 := mul_self_of_orderOf_two ht
      have hmod : t ^ n = t ^ (n % 2) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul]
        have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hsq
        rw [this, one_zpow, mul_one]
      have : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases this with h | h
      · left; rw [hmod, h]; simp
      · right; rw [hmod, h]; simp
    obtain ⟨f⟩ := lhat_equiv e
    have f' : ↥N ≃* A6 := (MulEquiv.subgroupCongr hNeq).trans f
    have hMA : Nat.card (MulAut N) = 1440 := by
      rw [Nat.card_congr (MulAut.congr f').toEquiv]
      exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
    have hdvd := card_dvd_card_centralizer_mul N
    rw [hB2, hMA] at hdvd
    have := h27.trans hdvd
    omega
  · refine ⟨hB, ?_⟩
    have hdvd : Nat.card X ∣ Nat.card (MulAut N) := by
      have := card_dvd_card_centralizer_mul N
      rwa [hB, Subgroup.card_bot, one_mul] at this
    have h27' : 27 ∣ Nat.card (MulAut N) := h27.trans hdvd
    have hHarris := hHs X hKX hO t ht ⟨e⟩
    rw [← hNdef] at hHarris
    unfold HarrisOutcome at hHarris
    rcases hHarris with hA6 | hA66 | hU4 | hHS | hL3 | hL4
    · exfalso
      obtain ⟨f⟩ := hA6
      have hMA : Nat.card (MulAut N) = 1440 := by
        rw [Nat.card_congr (MulAut.congr f).toEquiv]
        exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
      rw [hMA] at h27'
      omega
    · exact Or.inl hA66
    · obtain ⟨hy, hSig⟩ := hU X N hU4 hB t ht ⟨e⟩ y c k hS
      exact Or.inr ⟨hU4, hy, hSig⟩
    · exfalso
      rw [card_mulAut_of_isSporadic_hs hHS] at h27'
      omega
    · exact absurd (eight_dvd_card_centralizer_of_sigma ht hS)
        (hL X N hNn hB (Or.inl hL3) t ht ⟨e⟩ y hS.2.1 hS.1)
    · exact absurd (eight_dvd_card_centralizer_of_sigma ht hS)
        (hL X N hNn hB (Or.inr hL4) t ht ⟨e⟩ y hS.2.1 hS.1)

end Cases

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
