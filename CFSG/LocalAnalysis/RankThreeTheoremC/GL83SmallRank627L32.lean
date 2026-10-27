module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped MatrixGroups

namespace L32Insp

open CFSG.QuasithinUnique.Setup.Family

private abbrev X : Type := Multiplicative (ZMod 3)

private theorem X_mem_zpowers {a : X} (ha : a ≠ 1) (c : X) : c ∈ zpowers a := by
  have key : ∀ a c : X, a ≠ 1 → c = 1 ∨ c = a ∨ c = a * a := by decide
  rcases key a c ha with rfl | rfl | rfl
  exacts [one_mem _, mem_zpowers c, mul_mem (mem_zpowers a) (mem_zpowers a)]

private theorem X_eq_one_of_two_pow {b : X} {k : ℕ} (hb : b ^ 2 ^ k = 1) : b = 1 := by
  have h3 : b ^ 3 = 1 := by
    have key : ∀ b : X, b * b * b = 1 := by decide
    rw [pow_succ, pow_two]
    exact key b
  have := pow_gcd_eq_one.2 ⟨hb, h3⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)),
    pow_one] at this

private theorem X_conj_one (a : X) : 1 * a * 1⁻¹ = a := by
  revert a
  decide

private theorem X_eq_one_of_mul_self {a : X} (h : a * a = a) : a = 1 := by
  revert a
  decide

private abbrev inr {A : Type} [Group A] : A →* X × A := MonoidHom.inr X A

private theorem inr_injective {A : Type} [Group A] : Function.Injective (inr (A := A)) :=
  fun _ _ h => congrArg Prod.snd h

private theorem snd_mem_center {A : Type} [Group A] {x : X × A} (hx : x ∈ center (X × A)) :
    x.2 ∈ center A :=
  mem_center_iff.2 fun h => by simpa using congrArg Prod.snd (mem_center_iff.1 hx (1, h))

private theorem mk_one_mem_center {A : Type} [Group A] (c : X) :
    ((c, 1) : X × A) ∈ center (X × A) :=
  mem_center_iff.2 fun _ => Prod.ext (mul_comm _ _) ((mul_one _).trans (one_mul _).symm)

private theorem mem_range_inr {A : Type} [Group A] {v : X × A} {k : ℕ} (hv : v ^ 2 ^ k = 1) :
    v ∈ (inr (A := A)).range :=
  ⟨v.2, Prod.ext (X_eq_one_of_two_pow (k := k) (by simpa using congrArg Prod.fst hv)).symm rfl⟩

private theorem mem_normalizer_comap_inr {A : Type} [Group A] {S : Subgroup (X × A)} {l : A}
    (h : inr l ∈ normalizer (S : Set (X × A))) :
    l ∈ normalizer ((S.comap inr : Subgroup A) : Set A) :=
  le_normalizer_comap (H := S) inr (mem_comap.2 h)

private theorem inr_mem_normalizer_map {A : Type} [Group A] {P : Subgroup A} {g : A}
    (h : g ∈ normalizer (P : Set A)) :
    inr g ∈ normalizer ((P.map inr : Subgroup (X × A)) : Set (X × A)) :=
  le_normalizer_map (H := P) inr (mem_map_of_mem inr h)

private theorem isElemAbelian_two {G : Type*} [Group G] {E : Subgroup G}
    (h : ∀ x ∈ E, x ^ 2 = 1) : IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, h⟩
  have hinv : ∀ y ∈ E, y⁻¹ = y := fun y hy =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h y hy)
  change (a : G) * b = b * a
  rw [← hinv _ (mul_mem a.2 b.2), mul_inv_rev, hinv _ a.2, hinv _ b.2]

private def Concl {C : Type} [Group C] (x z : C) (K : Subgroup C) : Prop :=
  ∃ U : Subgroup C, IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
    zpowers x ⊔ zpowers z ≤ normalizer (U : Set C) ∧ ¬ U ≤ K ∧
    (∀ S : Subgroup C, S ≤ U → S ≠ ⊥ → zpowers x ⊔ zpowers z ≤ normalizer (S : Set C) →
      S = U) ∧
    (∀ S : Subgroup C, IsPGroup 2 S → zpowers x ⊔ zpowers z ≤ normalizer (S : Set C) →
      S ≤ K ∨ S ≤ U) ∧
    ∃ t ∈ normalizer (U : Set C), t * z * t⁻¹ = z⁻¹

private theorem core_one {x z : X × GL32} {K V : Subgroup (X × GL32)}
    (hx : x ∈ center (X × GL32)) (hx1 : x ≠ 1) (hz3 : z ^ 3 = 1) (hzx : z ∉ zpowers x)
    (hzl : z.2 ∈ zpowers l₀)
    (hNz : normalizer ((zpowers x ⊔ zpowers z : Subgroup (X × GL32)) : Set (X × GL32)) ≤
      normalizer ((zpowers z : Subgroup (X × GL32)) : Set (X × GL32)))
    (hVsq : ∀ v ∈ V, v ^ 2 = 1) (hV4 : Nat.card V = 4)
    (hVB : zpowers x ⊔ zpowers z ≤ normalizer (V : Set (X × GL32)))
    (hNV : normalizer (V : Set (X × GL32)) ≤ K) (hK : K ≠ ⊤) : Concl x z K := by
  have hx2 : x.2 = 1 := by
    have := snd_mem_center hx
    rwa [center_GL32, mem_bot] at this
  have hX : ∀ c : X, ((c, 1) : X × GL32) ∈ zpowers x := fun c => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (X_mem_zpowers (fun h => hx1 (Prod.ext h hx2)) c)
    exact mem_zpowers_iff.2 ⟨k, Prod.ext (by simpa using hk) (by simp [hx2])⟩
  have hz2 : z.2 ≠ 1 := fun h => by
    have hzz : ((z.1, 1) : X × GL32) = z := Prod.ext rfl h.symm
    exact hzx (hzz ▸ hX z.1)
  have h3 : z.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hz3
  have hzz : zpowers z.2 = zpowers l₀ := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine eq_of_le_of_card_ge (zpowers_le.2 hzl) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_l₀, orderOf_eq_prime h3 hz2]
  have hl₀ : l₀ ∈ zpowers z.2 := hzz ▸ mem_zpowers l₀
  have hB : (zpowers x ⊔ zpowers z : Subgroup (X × GL32)) =
      (zpowers l₀).comap (MonoidHom.snd X GL32) := by
    refine le_antisymm (sup_le (zpowers_le.2 ?_) (zpowers_le.2 hzl)) fun p hp => ?_
    · show x.2 ∈ zpowers l₀
      rw [hx2]
      exact one_mem _
    · have hp' : p.2 ∈ zpowers z.2 := by rw [hzz]; exact hp
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hp'
      have hpk : p = ((p.1 * (z ^ k).1⁻¹, 1) : X × GL32) * z ^ k :=
        Prod.ext (by simp only [Prod.fst_mul]; exact (inv_mul_cancel_right _ _).symm)
          (by simp [hk])
      rw [hpk]
      exact mul_mem (mem_sup_left (hX _)) (mem_sup_right (zpow_mem (mem_zpowers z) k))
  have htl : tL * z.2 * tL⁻¹ = z.2⁻¹ := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hzl
    rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, tL_conj_l₀, inv_zpow]
  have htB : ((1 : X), tL) ∈
      normalizer ((zpowers x ⊔ zpowers z : Subgroup (X × GL32)) : Set (X × GL32)) := by
    rw [hB]
    refine mem_normalizer_iff.2 fun p => ?_
    simpa using mem_normalizer_iff.1 tL_mem_normalizer_zpowers p.2
  have hz1 : z.1 = 1 := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ((mem_normalizer_iff.1 (hNz htB) z).1 (mem_zpowers z))
    have hw1 := congrArg Prod.fst hk
    have hw2 := congrArg Prod.snd hk
    simp only [Prod.fst_mul, Prod.fst_inv] at hw1
    simp only [Prod.snd_mul, Prod.snd_inv, htl] at hw2
    replace hw1 := hw1.trans (X_conj_one z.1)
    rw [zpow_eq_zpow_emod k (show z ^ (3 : ℤ) = 1 by exact_mod_cast hz3)] at hw1 hw2
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h <;> rw [h] at hw1 hw2
    · rw [zpow_zero, Prod.snd_one] at hw2
      exact absurd (inv_eq_one.1 hw2.symm) hz2
    · rw [zpow_one] at hw2
      have h2 : z.2 ^ 2 = 1 := by
        rw [sq]
        nth_rw 2 [hw2]
        exact mul_inv_cancel _
      exact absurd (by simpa using pow_gcd_eq_one.2 ⟨h2, h3⟩) hz2
    · rw [zpow_two, Prod.fst_mul] at hw1
      exact X_eq_one_of_mul_self hw1
  have hzinr : z = inr z.2 := Prod.ext hz1 rfl
  have hlS : ∀ S : Subgroup (X × GL32), zpowers x ⊔ zpowers z ≤ normalizer (S : Set _) →
      l₀ ∈ normalizer ((S.comap inr : Subgroup GL32) : Set GL32) := fun S hSB => by
    have h : inr z.2 ∈ normalizer (S : Set (X × GL32)) := by
      rw [← hzinr]
      exact hSB (mem_sup_right (mem_zpowers z))
    exact zpowers_le.2 (mem_normalizer_comap_inr h) hl₀
  obtain ⟨P, rfl⟩ : ∃ P : Subgroup GL32, V = P.map inr :=
    ⟨V.comap inr, (map_comap_eq_self fun v hv =>
      mem_range_inr (k := 1) (by rw [pow_one]; exact hVsq v hv)).symm⟩
  have hPsq : ∀ g ∈ P, g ^ 2 = 1 := fun g hg => by
    simpa using congrArg Prod.snd (hVsq _ (mem_map_of_mem inr hg))
  have hP4 : Nat.card P = 4 := (card_map_of_injective inr_injective).symm.trans hV4
  have hlP : l₀ ∈ normalizer (P : Set GL32) := by
    have h := hlS _ hVB
    rwa [comap_map_eq_self_of_injective inr_injective] at h
  obtain ⟨Q, hQ⟩ := exists_pair hPsq hP4 hlP
  have hzQ : z.2 ∈ normalizer (Q : Set GL32) := zpowers_le.2 hQ.l₀_mem hzl
  refine ⟨Q.map inr, isElemAbelian_two ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, hQ.sq g hg, map_one]
  · rw [card_map_of_injective inr_injective, hQ.card]
  · refine sup_le (zpowers_le.2 (center_le_normalizer _ hx)) (zpowers_le.2 ?_)
    rw [hzinr]
    exact inr_mem_normalizer_map hzQ
  · intro hQK
    have hKP : normalizer (P : Set GL32) ≤ K.comap inr := fun g hg =>
      hNV (inr_mem_normalizer_map hg)
    have hKtop : K.comap inr ≠ ⊤ := fun htop => hK (eq_top_iff.2 fun p _ => by
      have h1 : ((p.1, 1) : X × GL32) ∈ K := hNV (hVB (mem_sup_left (hX p.1)))
      have h2 : inr p.2 ∈ K := (htop ▸ mem_top p.2 : p.2 ∈ K.comap inr)
      have hp : ((p.1, 1) : X × GL32) * inr p.2 = p := Prod.ext (mul_one _) (one_mul _)
      exact hp ▸ mul_mem h1 h2)
    have hKeq := (eq_or_eq_top_of_index_seven hQ.index hKP).resolve_right hKtop
    exact hQ.not_le fun q hq => hKeq ▸ (hQK (mem_map_of_mem inr hq) : q ∈ K.comap inr)
  · intro S hSU hS1 hSB
    have hSeq : S = (S.comap inr).map inr :=
      (map_comap_eq_self (hSU.trans (map_le_range _ _))).symm
    have hSQ : S.comap inr ≤ Q := fun g hg => (mem_map_iff_mem inr_injective).1 (hSU hg)
    have hSne : S.comap inr ≠ ⊥ := fun h => hS1 (by rw [hSeq, h, Subgroup.map_bot])
    rw [hSeq, hQ.min _ hSQ hSne (hlS S hSB)]
  · intro S hS hSB
    have hSeq : S = (S.comap inr).map inr := (map_comap_eq_self fun s hs => by
      obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
      exact mem_range_inr (k := k) (by simpa using congrArg Subtype.val hk)).symm
    have h8 : ∀ g ∈ S.comap inr, g ^ 8 = 1 := fun g hg => by
      obtain ⟨k, hk⟩ := hS ⟨inr g, hg⟩
      exact pow_eight_eq_one (k := k)
        (by simpa using congrArg (fun p : S => (p : X × GL32).2) hk)
    rcases hQ.split _ h8 (hlS S hSB) with h | h
    · left
      rw [hSeq]
      exact (map_mono h).trans (le_normalizer.trans hNV)
    · right
      rw [hSeq]
      exact map_mono h
  · refine ⟨inr tL, inr_mem_normalizer_map hQ.tL_mem, Prod.ext ?_ ?_⟩
    · simp only [Prod.fst_mul, Prod.fst_inv, MonoidHom.inr_apply, hz1]
      decide
    · simp only [Prod.snd_mul, Prod.snd_inv, MonoidHom.inr_apply]
      exact htl

private abbrev ι : GL32 →* X × MulAut GL32 := inr.comp MulAut.conj

private theorem ι_injective : Function.Injective ι := inr_injective.comp innConj_injective

private theorem core_two {x z : X × MulAut GL32} {K V : Subgroup (X × MulAut GL32)}
    (hx : x ∈ center (X × MulAut GL32)) (hx1 : x ≠ 1) (hzx : z ∉ zpowers x)
    (hzl : z.2 ∈ (zpowers l₀).map MulAut.conj)
    (hNK : normalizer ((zpowers x ⊔ zpowers z : Subgroup (X × MulAut GL32)) :
      Set (X × MulAut GL32)) ≤ K)
    (hVsq : ∀ v ∈ V, v ^ 2 = 1) (hV4 : Nat.card V = 4)
    (hVB : zpowers x ⊔ zpowers z ≤ normalizer (V : Set (X × MulAut GL32)))
    (hNV : normalizer (V : Set (X × MulAut GL32)) ≤ K) (hK : K ≠ ⊤) : False := by
  have hx2 : x.2 = 1 := eq_one_of_mem_center_aut (snd_mem_center hx)
  have hX : ∀ c : X, ((c, 1) : X × MulAut GL32) ∈ zpowers x := fun c => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (X_mem_zpowers (fun h => hx1 (Prod.ext h hx2)) c)
    exact mem_zpowers_iff.2 ⟨k, Prod.ext (by simpa using hk) (by simp [hx2])⟩
  obtain ⟨l, hl, hlz⟩ := hzl
  have hl1 : l ≠ 1 := fun h => by
    have hzz : ((z.1, 1) : X × MulAut GL32) = z := Prod.ext rfl (by rw [← hlz, h, map_one])
    exact hzx (hzz ▸ hX z.1)
  have hll : l₀ ∈ zpowers l := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hl3 : l ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hl
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, l₀_pow_three, one_zpow]
    have heq : zpowers l = zpowers l₀ := eq_of_le_of_card_ge (zpowers_le.2 hl)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_l₀, orderOf_eq_prime hl3 hl1])
    exact heq ▸ mem_zpowers l₀
  have hzV : z ∈ normalizer (V : Set (X × MulAut GL32)) := hVB (mem_sup_right (mem_zpowers z))
  have hJ2 : (Inn.comap (MonoidHom.snd X (MulAut GL32))).index = 2 := by
    rw [index_comap_of_surjective _ fun a => ⟨(1, a), rfl⟩]
    exact index_Inn
  have hJn : (Inn.comap (MonoidHom.snd X (MulAut GL32))).Normal := normal_of_index_eq_two hJ2
  have hVJ : V ≤ Inn.comap (MonoidHom.snd X (MulAut GL32)) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (hJ2 ▸ relIndex_dvd_index_of_normal _ V) with h1 | h2
    · exact relIndex_eq_one.1 h1
    exfalso
    have hc := relIndex_mul_card (Inn.comap (MonoidHom.snd X (MulAut GL32))) V
    rw [h2, hV4] at hc
    have hc2 : Nat.card (Inn.comap (MonoidHom.snd X (MulAut GL32)) ⊓ V : Subgroup _) = 2 := by
      omega
    have hne : (Inn.comap (MonoidHom.snd X (MulAut GL32)) ⊓ V : Subgroup _) ≠ ⊥ := fun h => by
      rw [h, card_bot] at hc2
      norm_num at hc2
    obtain ⟨⟨β, hβ⟩, hβ1⟩ := ne_bot_iff_exists_ne_one.1 hne
    have hβ1' : β ≠ 1 := fun h => hβ1 (Subtype.ext h)
    have hβ2 : β ^ 2 = 1 := hVsq β hβ.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hJV : (Inn.comap (MonoidHom.snd X (MulAut GL32)) ⊓ V : Subgroup _) = zpowers β :=
      (eq_of_le_of_card_ge (zpowers_le.2 hβ)
        (by rw [hc2, Nat.card_zpowers, orderOf_eq_prime hβ2 hβ1'])).symm
    have hγ : z * β * z⁻¹ ∈ (Inn.comap (MonoidHom.snd X (MulAut GL32)) ⊓ V : Subgroup _) :=
      ⟨hJn.conj_mem β hβ.1 z, (mem_normalizer_iff.1 hzV β).1 hβ.2⟩
    rw [hJV] at hγ
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hγ
    rw [zpow_eq_zpow_emod k (show β ^ (2 : ℤ) = 1 by exact_mod_cast hβ2)] at hk
    have hzβ : z * β * z⁻¹ = β := by
      rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h <;> rw [h] at hk
      · rw [zpow_zero] at hk
        exact absurd (mul_eq_left.1 (mul_inv_eq_one.1 hk.symm)) hβ1'
      · rw [zpow_one] at hk
        exact hk.symm
    obtain ⟨σ, hσ⟩ := mem_Inn.1 (mem_comap.1 hβ.1)
    replace hσ : MulAut.conj σ = β.2 := hσ
    have hβ_1 : β.1 = 1 := X_eq_one_of_two_pow (k := 1) (by simpa using congrArg Prod.fst hβ2)
    have hσ2 : σ ^ 2 = 1 := innConj_injective (by
      rw [map_pow, hσ, map_one]
      simpa using congrArg Prod.snd hβ2)
    have hσ1 : σ ≠ 1 := fun h => hβ1' (Prod.ext hβ_1 (by rw [← hσ, h, map_one]; rfl))
    have hσl : l * σ = σ * l := by
      have h := congrArg Prod.snd hzβ
      simp only [Prod.snd_mul, Prod.snd_inv] at h
      rw [← hlz, ← hσ, aut_mul_conj, MulAut.conj_apply] at h
      have h' := innConj_injective h
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'
    obtain ⟨k', hk'⟩ := mem_zpowers_iff.1 hll
    have hc : Commute σ l₀ := hk' ▸ (Commute.zpow_right (Commute.symm hσl) k')
    exact hσ1 (eq_one_of_commute_l₀ hc.eq hσ2)
  obtain ⟨P, rfl⟩ : ∃ P : Subgroup GL32, V = P.map ι := by
    refine ⟨V.comap ι, (map_comap_eq_self fun v hv => ?_).symm⟩
    obtain ⟨s, hs⟩ := mem_Inn.1 (mem_comap.1 (hVJ hv))
    exact ⟨s, Prod.ext (X_eq_one_of_two_pow (k := 1) (by
      simpa using congrArg Prod.fst (hVsq v hv))).symm hs⟩
  have hPsq : ∀ g ∈ P, g ^ 2 = 1 := fun g hg => ι_injective (by
    rw [map_pow, map_one]
    exact hVsq _ (mem_map_of_mem ι hg))
  have hP4 : Nat.card P = 4 := (card_map_of_injective ι_injective).symm.trans hV4
  have hlP : l₀ ∈ normalizer (P : Set GL32) := by
    have hιl : ι l ∈ normalizer ((P.map ι : Subgroup _) : Set (X × MulAut GL32)) := by
      have h : ι l = ((z.1, 1) : X × MulAut GL32)⁻¹ * z :=
        eq_inv_mul_of_mul_eq (Prod.ext (mul_one _) (by simp [hlz]))
      rw [h]
      exact mul_mem (inv_mem (center_le_normalizer _ (mk_one_mem_center z.1))) hzV
    have h := le_normalizer_comap (H := P.map ι) ι (mem_comap.2 hιl)
    rw [comap_map_eq_self_of_injective ι_injective] at h
    exact zpowers_le.2 h hll
  obtain ⟨Q, hQ⟩ := exists_pair hPsq hP4 hlP
  have hτl : τ l = l := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hl
    rw [map_zpow, τ_l₀]
  have hnx : ((1 : X), τ) * x * ((1 : X), τ)⁻¹ = x :=
    Prod.ext (X_conj_one x.1) (by simp [hx2])
  have hnz : ((1 : X), τ) * z * ((1 : X), τ)⁻¹ = z := by
    refine Prod.ext (X_conj_one z.1) ?_
    simp only [Prod.snd_mul, Prod.snd_inv]
    rw [← hlz, aut_mul_conj, hτl]
  have hnK : ((1 : X), τ) ∈ K := by
    refine hNK ?_
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    change zpowers (((1 : X), τ) * x * ((1 : X), τ)⁻¹) ⊔
      zpowers (((1 : X), τ) * z * ((1 : X), τ)⁻¹) = _
    rw [hnx, hnz]
  have hBK : ∀ c : X, ((c, 1) : X × MulAut GL32) ∈ K := fun c =>
    hNK (le_normalizer (mem_sup_left (hX c)))
  have hKP : normalizer (P : Set GL32) ≤ K.comap ι := fun g hg =>
    hNV (le_normalizer_map (H := P) ι (mem_map_of_mem ι hg))
  have hKtop : K.comap ι ≠ ⊤ := fun htop => hK (eq_top_iff.2 fun p _ => by
    have hι : ∀ s, ι s ∈ K := fun s => (htop ▸ mem_top s : s ∈ K.comap ι)
    rcases mem_Inn_or p.2 with h | h
    · obtain ⟨s, hs⟩ := mem_Inn.1 h
      have hp : ((p.1, 1) : X × MulAut GL32) * ι s = p :=
        Prod.ext (mul_one _) ((one_mul _).trans hs)
      exact hp ▸ mul_mem (hBK p.1) (hι s)
    · obtain ⟨s, hs⟩ := mem_Inn.1 h
      have hp : ((p.1, 1) : X × MulAut GL32) * ι s * ((1 : X), τ) = p := by
        refine Prod.ext ((mul_one _).trans (mul_one _)) ?_
        change 1 * MulAut.conj s * τ = p.2
        rw [one_mul, hs, mul_assoc, τ_mul_τ, mul_one]
      exact hp ▸ mul_mem (mul_mem (hBK p.1) (hι s)) hnK)
  have hKeq := (eq_or_eq_top_of_index_seven hQ.index hKP).resolve_right hKtop
  obtain ⟨p, hp, hτp⟩ := hQ.tau
  have hpK : ι p ∈ K := show p ∈ K.comap ι by rw [hKeq]; exact le_normalizer hp
  have hnp : ((1 : X), τ) * ι p * ((1 : X), τ)⁻¹ = ι (τ p) := by
    refine Prod.ext (X_conj_one 1) ?_
    simp only [Prod.snd_mul, Prod.snd_inv]
    exact aut_mul_conj τ p
  have : ι (τ p) ∈ K := hnp ▸ mul_mem (mul_mem hnK hpK) (inv_mem hnK)
  exact hτp (hKeq ▸ (this : τ p ∈ K.comap ι))

section Transport

variable {C D : Type} [Group C] [Group D]

private theorem map_zpowers_equiv (φ : C ≃* D) (x : C) :
    (zpowers x).map φ.toMonoidHom = zpowers (φ x) :=
  MonoidHom.map_zpowers _ _

private theorem map_B (φ : C ≃* D) (x z : C) :
    (zpowers x ⊔ zpowers z).map φ.toMonoidHom = zpowers (φ x) ⊔ zpowers (φ z) := by
  rw [Subgroup.map_sup, map_zpowers_equiv, map_zpowers_equiv]

private theorem map_le_normalizer (φ : C ≃* D) {H V : Subgroup C}
    (h : H ≤ normalizer (V : Set C)) :
    H.map φ.toMonoidHom ≤ normalizer ((V.map φ.toMonoidHom : Subgroup D) : Set D) := by
  rw [← map_equiv_normalizer_eq]
  exact map_mono h

private theorem map_normalizer_le (φ : C ≃* D) {V K : Subgroup C}
    (h : normalizer (V : Set C) ≤ K) :
    normalizer ((V.map φ.toMonoidHom : Subgroup D) : Set D) ≤ K.map φ.toMonoidHom := by
  rw [← map_equiv_normalizer_eq]
  exact map_mono h

private theorem map_mem_center (φ : C ≃* D) {x : C} (hx : x ∈ center C) : φ x ∈ center D :=
  mem_center_iff.2 fun g => by
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.1 hx g']

private theorem map_ne_one (φ : C ≃* D) {x : C} (hx : x ≠ 1) : φ x ≠ 1 :=
  fun h => hx (φ.injective (h.trans (map_one φ).symm))

private theorem map_ne_top (φ : C ≃* D) {K : Subgroup C} (h : K ≠ ⊤) :
    K.map φ.toMonoidHom ≠ ⊤ :=
  fun h' => h (map_injective φ.injective (h'.trans (map_top_of_surjective _ φ.surjective).symm))

private theorem map_sq (φ : C ≃* D) {V : Subgroup C} (h : ∀ v ∈ V, v ^ 2 = 1) :
    ∀ v ∈ V.map φ.toMonoidHom, v ^ 2 = 1 := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_pow, h v hv, map_one]

private theorem map_not_mem_zpowers (φ : C ≃* D) {x z : C} (h : z ∉ zpowers x) :
    φ z ∉ zpowers (φ x) := by
  rw [← map_zpowers_equiv]
  exact fun h' => h ((mem_map_iff_mem (f := φ.toMonoidHom) φ.injective).1 h')

private theorem concl_of_map (φ : C ≃* D) {x z : C} {K : Subgroup C}
    (h : Concl (φ x) (φ z) (K.map φ.toMonoidHom)) : Concl x z K := by
  obtain ⟨U, hU2, hU4, hBU, hUK, hmin, hsplit, t, ht, htz⟩ := h
  have hmapN : ∀ S : Subgroup C, zpowers x ⊔ zpowers z ≤ normalizer (S : Set C) →
      zpowers (φ x) ⊔ zpowers (φ z) ≤ normalizer ((S.map φ.toMonoidHom : Subgroup D) : Set D) :=
    fun S hS => by
      rw [← map_B]
      exact map_le_normalizer φ hS
  have hUU : (U.comap φ.toMonoidHom).map φ.toMonoidHom = U :=
    map_comap_eq_self_of_surjective φ.surjective U
  refine ⟨U.comap φ.toMonoidHom, isElemAbelian_two fun u hu => φ.injective ?_, ?_, ?_, ?_, ?_, ?_,
    φ.symm t, ?_, ?_⟩
  · rw [map_pow, map_one]
    exact hU2.2 _ hu
  · have h := card_map_of_injective (K := U.comap φ.toMonoidHom) (f := φ.toMonoidHom) φ.injective
    rw [hUU, hU4] at h
    exact h.symm
  · refine (map_le_iff_le_comap.1 ?_).trans (le_normalizer_comap (H := U) φ.toMonoidHom)
    rw [map_B]
    exact hBU
  · intro hle
    apply hUK
    rw [← hUU]
    exact map_mono hle
  · intro S hSU hS1 hSB
    have := hmin _ (map_le_iff_le_comap.2 hSU)
      (fun h => hS1 ((map_eq_bot_iff_of_injective S (f := φ.toMonoidHom) φ.injective).1 h))
      (hmapN S hSB)
    rw [← this, comap_map_eq_self_of_injective φ.injective]
  · intro S hS hSB
    rcases hsplit _ (hS.map φ.toMonoidHom) (hmapN S hSB) with h | h
    · exact Or.inl ((map_le_map_iff_of_injective φ.injective).1 h)
    · exact Or.inr (map_le_iff_le_comap.1 h)
  · exact le_normalizer_comap (H := U) φ.toMonoidHom (mem_comap.2 (by simpa using ht))
  · apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, htz]

end Transport

end L32Insp

set_option linter.unusedVariables false in
open L32Insp CFSG.QuasithinUnique.Setup.Family in
theorem l32_inspection_of_prod {C : Type} [Group C] [Finite C]
    (e : C ≃* (Multiplicative (ZMod 3) × PSL(3, ZMod 2)))
    {x z : C} (hx : x ∈ center C) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hzx : z ∉ zpowers x) {K V : Subgroup C}
    (hBK : zpowers x ⊔ zpowers z ≤ K) (hK : K ≠ ⊤)
    (hCK : centralizer ((zpowers x ⊔ zpowers z : Subgroup C) : Set C) ≤ K)
    (hNK : normalizer ((zpowers x ⊔ zpowers z : Subgroup C) : Set C) ≤ K)
    (hNz : normalizer ((zpowers x ⊔ zpowers z : Subgroup C) : Set C) ≤
      normalizer ((zpowers z : Subgroup C) : Set C))
    (hV : IsElemAbelian 2 V) (hV4 : Nat.card V = 4) (hVK : V ≤ K)
    (hVB : zpowers x ⊔ zpowers z ≤ normalizer (V : Set C))
    (hVz : ∃ v ∈ V, z * v * z⁻¹ ≠ v) (hNV : normalizer (V : Set C) ≤ K) :
    ∃ U : Subgroup C, IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
      zpowers x ⊔ zpowers z ≤ normalizer (U : Set C) ∧ ¬ U ≤ K ∧
      (∀ S : Subgroup C, S ≤ U → S ≠ ⊥ → zpowers x ⊔ zpowers z ≤ normalizer (S : Set C) →
        S = U) ∧
      (∀ S : Subgroup C, IsPGroup 2 S → zpowers x ⊔ zpowers z ≤ normalizer (S : Set C) →
        S ≤ K ∨ S ≤ U) ∧
      ∃ t ∈ normalizer (U : Set C), t * z * t⁻¹ = z⁻¹ := by
  let φ₀ : C ≃* X × GL32 := e.trans (MulEquiv.prodCongr (MulEquiv.refl _) pslEquiv)
  have h3 : (φ₀ z).2 ^ 3 = 1 := by
    simpa using congrArg Prod.snd (show φ₀ z ^ 3 = 1 by rw [← map_pow, hz3, map_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers h3
  let φ : C ≃* X × GL32 := φ₀.trans (MulAut.conj ((1 : X), g))
  have hφz : (φ z).2 ∈ zpowers l₀ := hg
  refine concl_of_map φ (core_one (map_mem_center φ hx) (map_ne_one φ hx1)
    (by rw [← map_pow, hz3, map_one]) (map_not_mem_zpowers φ hzx) hφz ?_ (map_sq φ hV.2)
    ((card_map_of_injective (f := φ.toMonoidHom) φ.injective).trans hV4) ?_
    (map_normalizer_le φ hNV) (map_ne_top φ hK))
  · rw [← map_B φ x z, ← map_zpowers_equiv φ z, ← map_equiv_normalizer_eq,
      ← map_equiv_normalizer_eq]
    exact map_mono hNz
  · rw [← map_B φ x z]
    exact map_le_normalizer φ hVB

set_option linter.unusedVariables false in
open L32Insp CFSG.QuasithinUnique.Setup.Family in
theorem false_of_l32_aut_prod {C : Type} [Group C] [Finite C]
    (e : C ≃* (Multiplicative (ZMod 3) × MulAut PSL(3, ZMod 2)))
    {x z : C} (hx : x ∈ center C) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hzx : z ∉ zpowers x) {K V : Subgroup C}
    (hBK : zpowers x ⊔ zpowers z ≤ K) (hK : K ≠ ⊤)
    (hCK : centralizer ((zpowers x ⊔ zpowers z : Subgroup C) : Set C) ≤ K)
    (hNK : normalizer ((zpowers x ⊔ zpowers z : Subgroup C) : Set C) ≤ K)
    (hV : IsElemAbelian 2 V) (hV4 : Nat.card V = 4) (hVK : V ≤ K)
    (hVB : zpowers x ⊔ zpowers z ≤ normalizer (V : Set C))
    (hVz : ∃ v ∈ V, z * v * z⁻¹ ≠ v) (hNV : normalizer (V : Set C) ≤ K) : False := by
  let φ₀ : C ≃* X × MulAut GL32 :=
    e.trans (MulEquiv.prodCongr (MulEquiv.refl _) (MulAut.congr pslEquiv))
  have h3 : (φ₀ z).2 ^ 3 = 1 := by
    simpa using congrArg Prod.snd (show φ₀ z ^ 3 = 1 by rw [← map_pow, hz3, map_one])
  have h4 : (φ₀ z).2 = ((φ₀ z).2 ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  have hInn : (φ₀ z).2 ∈ Inn := by
    rw [h4]
    exact sq_mem_of_index_two index_Inn _
  obtain ⟨l, hl⟩ := mem_Inn.1 hInn
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers (l := l)
    (innConj_injective (by rw [map_pow, hl, h3, map_one]))
  let φ : C ≃* X × MulAut GL32 := φ₀.trans (MulAut.conj ((1 : X), MulAut.conj g))
  have hφz : (φ z).2 ∈ (zpowers l₀).map MulAut.conj := by
    have h : (φ z).2 = MulAut.conj (g * l * g⁻¹) := by
      change MulAut.conj g * (φ₀ z).2 * (MulAut.conj g)⁻¹ = _
      rw [← hl, ← map_inv, ← map_mul, ← map_mul]
    rw [h]
    exact mem_map_of_mem _ hg
  refine core_two (map_mem_center φ hx) (map_ne_one φ hx1) (map_not_mem_zpowers φ hzx) hφz ?_
    (map_sq φ hV.2) ((card_map_of_injective (f := φ.toMonoidHom) φ.injective).trans hV4) ?_
    (map_normalizer_le φ hNV) (map_ne_top φ hK)
  · rw [← map_B φ x z]
    exact map_normalizer_le φ hNK
  · rw [← map_B φ x z]
    exact map_le_normalizer φ hVB

end CFSG.LocalAnalysis.RankThreeTheoremC
