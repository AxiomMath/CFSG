module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec26
public import CFSG.GH74.GLS.C3.Layer2.L5C7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup
open CFSG.ABGLocalTools

private lemma exists_pow_ne_one_mul_self_eq_one {M : Type*} [Group M] {h : M}
    (h2 : ∃ k : ℕ, h ^ (2 ^ k) = 1) (hne : h ≠ 1) :
    ∃ n : ℕ, h ^ n ≠ 1 ∧ h ^ n * (h ^ n) = 1 := by
  classical
  have hk0 : h ^ (2 ^ Nat.find h2) = 1 := Nat.find_spec h2
  have hpos : 0 < Nat.find h2 := by
    rcases Nat.eq_zero_or_pos (Nat.find h2) with h | h
    · rw [h] at hk0
      simp only [pow_zero, pow_one] at hk0
      exact absurd hk0 hne
    · exact h
  refine ⟨2 ^ (Nat.find h2 - 1), ?_, ?_⟩
  · intro hm
    exact Nat.find_min h2 (Nat.sub_lt hpos one_pos) hm
  · have hexp : 2 ^ (Nat.find h2 - 1) * 2 = 2 ^ Nat.find h2 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
    rw [← pow_two, ← pow_mul, hexp, hk0]

private lemma mulAut_pow_apply_eq_self {E : Type*} [Group E] (h : MulAut E) {e : E}
    (he : h e = e) (n : ℕ) : (h ^ n) e = e := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, he, ih]

private lemma card_inf_centralizer_eq_card_fix {G : Type*} [Group G] {E : Subgroup G}
    {x : G} (hx : x ∈ Subgroup.normalizer (E : Set G)) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card {e : ↥E // E.normalizerMonoidHom ⟨x, hx⟩ e = e} := by
  let f : ↥(E ⊓ Subgroup.centralizer ({x} : Set G)) →
      {e : ↥E // E.normalizerMonoidHom ⟨x, hx⟩ e = e} := fun y =>
    ⟨⟨y.1, y.2.1⟩, by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hy : y.1 * x = x * y.1 := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
      rw [← hy]
      group⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (congrArg (fun z => z.1.1) hab)
  · intro u
    have hcent : (u.1 : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have he : x * (u.1 : G) * x⁻¹ = (u.1 : G) := by
        have := congrArg Subtype.val u.2
        rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
      calc (u.1 : G) * x = (x * u.1 * x⁻¹) * x := by rw [he]
        _ = x * u.1 := by group
    refine ⟨⟨u.1.1, Subgroup.mem_inf.mpr ⟨u.1.2, hcent⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

private lemma card_inf_centralizer_le_of_not_mem_sup {G : Type} [Group G] [Finite G]
    {E S : Subgroup G} {t : G} (hS : IsSylowOf 2 S (Subgroup.normalizer (E : Set G)))
    (hker2 : ∀ x ∈ Subgroup.centralizer (E : Set G),
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ E)
    (hK1 : ∀ h ∈ (E.normalizerMonoidHom).range, h ≠ 1 → h * h = 1 →
      Nat.card {e : ↥E // h e = e} = 16) :
    ∀ s ∈ S, s ∉ E ⊔ Subgroup.zpowers t →
      Nat.card ↥(E ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 16 := by
  intro s hsS hsnot
  have hsN : s ∈ Subgroup.normalizer (E : Set G) := hS.le hsS
  have hsE : s ∉ E := fun h => hsnot (Subgroup.mem_sup_left h)
  let h : MulAut ↥E := E.normalizerMonoidHom ⟨s, hsN⟩
  have hhne : h ≠ 1 := by
    intro h1
    have hker : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (E : Set G))) ∈
        E.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr h1
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    have hsC : s ∈ Subgroup.centralizer (E : Set G) := Subgroup.mem_subgroupOf.mp hker
    have hs2 : ∃ k : ℕ, s ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hsS⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact hsE (hker2 s hsC hs2)
  have hh2 : ∃ k : ℕ, h ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hsS⟩
    refine ⟨k, ?_⟩
    have hsNpow : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [← map_pow, hsNpow, map_one]
  obtain ⟨n, hn_ne, hn_sq⟩ := exists_pow_ne_one_mul_self_eq_one hh2 hhne
  have hhrange : h ^ n ∈ (E.normalizerMonoidHom).range := by
    refine ⟨(⟨s, hsN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ n, ?_⟩
    rw [map_pow]
  have hfix16 : Nat.card {e : ↥E // (h ^ n) e = e} = 16 :=
    hK1 (h ^ n) hhrange hn_ne hn_sq
  have hcard_cent : Nat.card ↥(E ⊓ Subgroup.centralizer ({s} : Set G)) =
      Nat.card {e : ↥E // h e = e} :=
    card_inf_centralizer_eq_card_fix hsN
  have hle : Nat.card {e : ↥E // h e = e} ≤
      Nat.card {e : ↥E // (h ^ n) e = e} :=
    Finite.card_le_of_embedding
      ⟨fun e => ⟨e.1, mulAut_pow_apply_eq_self h e.2 n⟩,
        fun a b hab => Subtype.ext (congrArg (fun z => z.1) hab)⟩
  rw [hcard_cent]
  omega

private lemma relIndex_le_of_isElemAbelian {G : Type} [Group G] [Finite G]
    {E S : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hS : IsSylowOf 2 S (Subgroup.normalizer (E : Set G)))
    (hker2 : ∀ x ∈ Subgroup.centralizer (E : Set G),
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ E)
    (hK2 : ∀ R : Subgroup (MulAut ↥E), R ≤ (E.normalizerMonoidHom).range →
      (∀ r ∈ R, r * r = 1) → Nat.card ↥R ≤ 8)
    {B' : Subgroup G} (hB'S : B' ≤ S) (hBel : CFSG.Open.IsElemAbelian 2 B') :
    E.relIndex B' ≤ 8 := by
  have hSN : S ≤ Subgroup.normalizer (E : Set G) := hS.le
  have hB'N : B' ≤ Subgroup.normalizer (E : Set G) := hB'S.trans hSN
  let B'N : Subgroup ↥(Subgroup.normalizer (E : Set G)) := B'.subgroupOf _
  let R : Subgroup (MulAut ↥E) := B'N.map E.normalizerMonoidHom
  have hRle : R ≤ (E.normalizerMonoidHom).range := B'N.map_le_range E.normalizerMonoidHom
  have hRexp : ∀ r ∈ R, r * r = 1 := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := hr
    have hb2 : b ^ 2 = 1 := by
      apply Subtype.ext
      show (b : G) ^ 2 = 1
      exact hBel.2 b.1 (Subgroup.mem_subgroupOf.mp hb)
    rw [← map_mul, ← sq, hb2, map_one]
  have hR8 : Nat.card ↥R ≤ 8 := hK2 R hRle hRexp
  have hrel : E.relIndex B' = Nat.card ↥R := by
    have h1 : E.normalizerMonoidHom.ker.relIndex B'N = Nat.card ↥R :=
      Subgroup.relIndex_ker E.normalizerMonoidHom (K := B'N)
    have hker_eq : E.normalizerMonoidHom.ker =
        (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)) :=
      Subgroup.normalizerMonoidHom_ker E
    have hCE : Subgroup.centralizer (E : Set G) ⊓ B' = E ⊓ B' := by
      apply le_antisymm
      · intro x hx
        exact ⟨hker2 x hx.1 ⟨1, by simpa using hBel.2 x hx.2⟩, hx.2⟩
      · intro x hx
        exact ⟨Subgroup.mem_centralizer_iff.mpr (fun y hy =>
          CFSG.OddStandard.Seitz77.L34.comm_of_isElemAbelian hE hy hx.1), hx.2⟩
    have hker_inf : E.normalizerMonoidHom.ker ⊓ B'N =
        (E ⊓ B').subgroupOf (Subgroup.normalizer (E : Set G)) := by
      rw [hker_eq]
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_subgroupOf]
        have hy1 : (y : G) ∈ Subgroup.centralizer (E : Set G) := hy.1
        have hy2 : (y : G) ∈ B' := hy.2
        have hmem : (y : G) ∈ Subgroup.centralizer (E : Set G) ⊓ B' := ⟨hy1, hy2⟩
        rwa [hCE] at hmem
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        have hmem : (y : G) ∈ Subgroup.centralizer (E : Set G) ⊓ B' := by
          rw [hCE]
          exact hy
        exact ⟨hmem.1, hmem.2⟩
    have hcard_B'N : Nat.card ↥B'N = Nat.card ↥B' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'N).toEquiv
    have hcard_ker : Nat.card ↥(E.normalizerMonoidHom.ker ⊓ B'N) =
        Nat.card ↥(E ⊓ B') := by
      rw [hker_inf]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hB'N)).toEquiv
    have hmain : E.relIndex B' * Nat.card ↥(E ⊓ B') =
        Nat.card ↥R * Nat.card ↥(E ⊓ B') := by
      calc E.relIndex B' * Nat.card ↥(E ⊓ B') = Nat.card ↥B' :=
            Subgroup.relIndex_mul_card (H := E) (K := B')
        _ = Nat.card ↥B'N := hcard_B'N.symm
        _ = E.normalizerMonoidHom.ker.relIndex B'N *
              Nat.card ↥(E.normalizerMonoidHom.ker ⊓ B'N) :=
            (Subgroup.relIndex_mul_card (H := E.normalizerMonoidHom.ker) (K := B'N)).symm
        _ = Nat.card ↥R * Nat.card ↥(E ⊓ B') := by rw [h1, hcard_ker]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmain
  rw [hrel]
  exact hR8

theorem fusion_in_E {G : Type} [Group G] [Finite G] (E B : Subgroup G) (t : G)
    (hE : IsElemAb2 E 8) (hB : Nat.card ↥B = 16) (hCt : E ⊓ centralizer ({t} : Set G) = B)
    (ht2 : t * t = 1) (htX : t ∈ normalizer (E : Set G))
    (hker2 : ∀ x ∈ centralizer (E : Set G), (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ E)
    (hK1 : ∀ h ∈ (E.normalizerMonoidHom).range, h ≠ 1 → h * h = 1 →
      Nat.card {e : ↥E // h e = e} = 16)
    (hK2 : ∀ R : Subgroup (MulAut ↥E), R ≤ (E.normalizerMonoidHom).range →
      (∀ r ∈ R, r * r = 1) → Nat.card ↥R ≤ 8) :
    ∀ x ∈ E, ∀ y ∈ E, IsConj x y → ∃ n ∈ normalizer (E : Set G), n * x * n⁻¹ = y := by
  classical
  let N : Subgroup G := Subgroup.normalizer (E : Set G)
  have hEN : E ≤ N := Subgroup.le_normalizer
  let tN : ↥N := ⟨t, htX⟩
  have htN2 : tN * tN = 1 := by
    apply Subtype.ext
    show t * t = (1 : G)
    simpa using ht2
  have hz : IsPGroup 2 ↥(Subgroup.zpowers tN) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one, pow_one]
    show tN ^ 2 = 1
    rw [pow_two]
    exact htN2
  obtain ⟨P, htP⟩ := hz.exists_le_sylow
  let S : Subgroup G := (P : Subgroup ↥N).map N.subtype
  have hS : IsSylowOf 2 S N := ⟨P, rfl⟩
  have hSN : S ≤ N := hS.le
  have htS : t ∈ S := by
    have : tN ∈ (P : Subgroup ↥N) := htP (Subgroup.mem_zpowers tN)
    exact ⟨tN, this, rfl⟩
  have hEpgN : IsPGroup 2 ↥(E.subgroupOf N) := by
    refine IsPGroup.of_card (n := 8) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]
    exact hE.2
  have hEsub_le_P : E.subgroupOf N ≤ (P : Subgroup ↥N) :=
    IsPGroup.le_sylow_of_normal hEpgN P
  have hES : E ≤ S := by
    have h := Subgroup.map_mono (f := N.subtype) hEsub_le_P
    rwa [Subgroup.map_subgroupOf_eq_of_le hEN] at h
  have hR2 := card_inf_centralizer_le_of_not_mem_sup (E := E) (S := S) (t := t) hS hker2 hK1
  have hR1 : ∀ B' : Subgroup G, B' ≤ S → CFSG.Open.IsElemAbelian 2 B' →
      E.relIndex B' ≤ 8 :=
    fun B' hB'S hBel => relIndex_le_of_isElemAbelian hE.1 hS hker2 hK2 hB'S hBel
  have hweak := CFSG.OddStandard.Seitz77.Sec26.weak_closure_of_actions hSN hE.1 hE.2
    htS ht2 hCt hB hR2 hR1
  have hSylTop : IsSylowOf 2 S ⊤ :=
    CFSG.OddStandard.Seitz77.Sec26.isSylowOf_top_of_weakly_closed hS hES hweak
  have hSyl2 : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In S ⊤ :=
    isSylowOf_iff.mp hSylTop
  have hweak' : ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ S →
      E.map (MulAut.conj g).toMonoidHom = E := by
    intro g hg
    have h1 : CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate E g⁻¹ ≤ S := by
      simpa [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate] using hg
    have h2 := hweak g⁻¹ h1
    simpa [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate] using h2
  have hburn := CFSG.GH74.GLS.C3.Layer2.L5.burnside_weak S E hS.isPGroup hSyl2 hES
    (fun a ha b hb => CFSG.OddStandard.Seitz77.L34.comm_of_isElemAbelian hE.1 ha hb) hweak'
  intro x hx y hy hxy
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hcyx : c⁻¹ * y * c = x := by rw [← hc]; group
  obtain ⟨n, hn, hn'⟩ := hburn y hy c (by rw [hcyx]; exact hx)
  have hnx : n⁻¹ * y * n = x := hn'.trans hcyx
  exact ⟨n, hn, by rw [← hnx]; group⟩

end C10

end CFSG.OddStandard.SmallF3.Omega
