module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic
public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma22Full

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22
open scoped commutatorElement

section Tools

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul {a b z w : G} (hzb : Commute z b) (hzw : Commute z w)
    (hwa : Commute w a) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  calc ⁅a * z, b * w⁆ = a * (z * (b * w)) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by
          simp only [commutatorElement_def, mul_inv_rev]
          group
    _ = a * (b * w * z) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [(hzb.mul_right hzw).eq]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hwa.inv_right.eq]
    _ = ⁅a, b⁆ := by
          rw [commutatorElement_def]
          group

theorem aschbacherThm5OddCore_eq_pPrimeCore (X : Type*) [Group X] :
    aschbacherThm5OddCore X = CFSG.pPrimeCore 2 X := by
  unfold aschbacherThm5OddCore CFSG.pPrimeCore
  congr 1
  ext K
  exact and_congr_right fun _ => Nat.coprime_two_left.symm

theorem odd_card_aschbacherThm5OddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (aschbacherThm5OddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [aschbacherThm5OddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem aschbacherThm5OddCore_characteristic (X : Type*) [Group X] :
    (aschbacherThm5OddCore X).Characteristic := by
  rw [aschbacherThm5OddCore_eq_pPrimeCore]
  infer_instance

theorem core_le (D : Subgroup G) : aschbacherThm5Core D ≤ D :=
  map_subtype_le _

theorem odd_card_core [Finite G] (D : Subgroup G) : Odd (Nat.card (aschbacherThm5Core D)) := by
  rw [aschbacherThm5Core, card_map_of_injective (subtype_injective _)]
  exact odd_card_aschbacherThm5OddCore _

theorem normalizer_le_normalizer_core (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer (aschbacherThm5Core D : Set G) := by
  intro x hx
  let φ : D ≃* D := ((MulAut.conj x).subgroupMap D).trans
    (MulEquiv.subgroupCongr (conj_eq_self_iff.mpr hx))
  have hchar := aschbacherThm5OddCore_characteristic D
  have hmap : (aschbacherThm5OddCore D).map φ.toMonoidHom = aschbacherThm5OddCore D :=
    characteristic_iff_map_eq.mp hchar φ
  rw [← conj_eq_self_iff, conj, aschbacherThm5Core, map_map]
  conv_rhs => rw [← hmap, map_map]
  congr 1

theorem le_normalizer_core (D : Subgroup G) : D ≤ normalizer (aschbacherThm5Core D : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_core D)

theorem core_le_centralizer_of [Finite G] (D : Subgroup G) {M : Subgroup G}
    (hM : CFSG.Open.IsQuasisimple ↥M) (hMD : M ≤ D)
    (hOM : aschbacherThm5Core D ≤ normalizer (M : Set G)) :
    aschbacherThm5Core D ≤ centralizer (M : Set G) := by
  have hMN := hMD.trans (le_normalizer_core D)
  rcases le_or_inf_le_centralizer hM hMN with h | h
  · exfalso
    exact (Nat.not_even_iff_odd.mpr ((odd_card_core D).of_dvd_nat (card_dvd_of_le h)))
      (even_card_of_isQuasisimple hM)
  · exact fun o ho => mem_centralizer_of_mem hM hMN h (hOM ho) ho

end Tools

variable {G : Type} [Group G] [Finite G]

structure ClosureSetting (K R L : Subgroup G) (g : G) : Prop where
  tight : TightlyEmbedded K
  sylow : IsSylowOf 2 R K
  quasisimple : CFSG.Open.IsQuasisimple ↥L
  normalizer_le : normalizer (K : Set G) ≤ normalizer (L : Set G)
  sylow_centralizer : IsSylowOf 2 R (centralizer (L : Set G))
  conj_le : conj L g ≤ centralizer (L : Set G)
  le_normalizer : centralizer (L : Set G) ≤ normalizer (conj L g : Set G)
  le_conj : R ≤ conj L g

namespace ClosureSetting

variable {K R L : Subgroup G} {g : G} (hS : ClosureSetting K R L g)
include hS

theorem ne_bot : R ≠ ⊥ := ne_bot_of_isSylowOf_of_tightlyEmbedded hS.tight hS.sylow

theorem tightlyEmbedded_centralizer : TightlyEmbedded (centralizer (L : Set G)) :=
  tightlyEmbedded_of_isSylowOf hS.tight hS.sylow hS.sylow_centralizer hS.ne_bot
    (hS.normalizer_le.trans (normalizer_le_normalizer_centralizer L))

theorem normalizer_centralizer :
    normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G) :=
  le_antisymm (normalizer_centralizer_le hS.tight hS.sylow hS.sylow_centralizer hS.ne_bot
    hS.normalizer_le) (normalizer_le_normalizer_centralizer L)

theorem mem_conj_of_pow_eq_one {x : G} (hx : x ∈ centralizer (L : Set G)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ conj L g := by
  obtain ⟨m, hm, hr⟩ := Lemma22.exists_conj_mem_of_isSylowOf hS.sylow_centralizer hx
    (isPGroup_zpowers_of_pow_eq_one hk)
  have h := (mem_normalizer_iff.mp (hS.le_normalizer hm) _).mp (hS.le_conj hr)
  simpa [mul_assoc] using h

theorem le_conj_of_le_centralizer {M : Subgroup G} (hM : CFSG.Open.IsQuasisimple ↥M)
    (hMH : M ≤ centralizer (L : Set G)) : M ≤ conj L g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases le_or_inf_le_centralizer hM (hMH.trans hS.le_normalizer) with h | h
  · exact h
  · exfalso
    obtain ⟨S, hS'⟩ := exists_isSylowOf 2 M
    apply not_le_centralizer_of_isSylowOf hM hS'
    refine le_trans (le_inf hS'.le fun x hx => ?_) h
    obtain ⟨k, hk⟩ := hS'.isPGroup ⟨x, hx⟩
    exact hS.mem_conj_of_pow_eq_one (hMH (hS'.le hx)) (by simpa using congrArg Subtype.val hk)

theorem normalizer_le_normalizer_conj :
    normalizer (L : Set G) ≤ normalizer (conj L g : Set G) := by
  intro n hn
  have hnH : n ∈ normalizer (centralizer (L : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer L hn
  have hle : conj (conj L g) n ≤ conj L g := by
    apply hS.le_conj_of_le_centralizer (isQuasisimple_conj (isQuasisimple_conj hS.quasisimple g) n)
    calc conj (conj L g) n ≤ conj (centralizer (L : Set G)) n := map_mono hS.conj_le
      _ = centralizer (L : Set G) := conj_eq_self_iff.mpr hnH
  exact conj_eq_self_iff.mp (eq_of_le_of_card_ge hle (card_conj (conj L g) n).ge)

theorem normalizer_conj_eq : normalizer (conj L g : Set G) = normalizer (L : Set G) := by
  symm
  apply eq_of_le_of_card_ge hS.normalizer_le_normalizer_conj
  rw [normalizer_conj, card_conj]

theorem tightlyEmbedded_centralizer_conj : TightlyEmbedded (centralizer (conj L g : Set G)) := by
  rw [centralizer_conj]
  exact tightlyEmbedded_conj hS.tightlyEmbedded_centralizer g

omit [Finite G] in
theorem le_centralizer_conj : L ≤ centralizer (conj L g : Set G) :=
  le_centralizer_iff.mp hS.conj_le

theorem mem_conj_conj_of_pow_eq_one {x : G} (hx : x ∈ centralizer (conj L g : Set G)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ conj (conj L g) g := by
  rw [centralizer_conj, mem_conj_iff] at hx
  rw [mem_conj_iff]
  have hk' : (g⁻¹ * x * g) ^ 2 ^ k = 1 := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hk, mul_one,
      mul_inv_cancel]
  exact hS.mem_conj_of_pow_eq_one hx hk'

theorem conj_conj_eq : conj (conj L g) g = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ≤ normalizer (conj (conj L g) g : Set G) := by
    calc L ≤ centralizer (conj L g : Set G) := hS.le_centralizer_conj
      _ = conj (centralizer (L : Set G)) g := centralizer_conj L g
      _ ≤ conj (normalizer (conj L g : Set G)) g := map_mono hS.le_normalizer
      _ = normalizer (conj (conj L g) g : Set G) := (normalizer_conj (conj L g) g).symm
  have hle : L ≤ conj (conj L g) g := by
    rcases le_or_inf_le_centralizer hS.quasisimple hLN with h | h
    · exact h
    · exfalso
      obtain ⟨S, hS'⟩ := exists_isSylowOf 2 L
      apply not_le_centralizer_of_isSylowOf hS.quasisimple hS'
      refine le_trans (le_inf hS'.le fun x hx => ?_) h
      obtain ⟨k, hk⟩ := hS'.isPGroup ⟨x, hx⟩
      exact hS.mem_conj_conj_of_pow_eq_one (hS.le_centralizer_conj (hS'.le hx))
        (by simpa using congrArg Subtype.val hk)
  exact (eq_of_le_of_card_ge hle (by rw [card_conj, card_conj])).symm

theorem mem_of_pow_eq_one {x : G} (hx : x ∈ centralizer (conj L g : Set G)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ L := by
  have h := hS.mem_conj_conj_of_pow_eq_one hx hk
  rwa [hS.conj_conj_eq] at h

theorem le_of_le_centralizer_conj {M : Subgroup G} (hM : CFSG.Open.IsQuasisimple ↥M)
    (hMH : M ≤ centralizer (conj L g : Set G)) : M ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMN : M ≤ normalizer (L : Set G) := by
    rw [← hS.normalizer_conj_eq]
    exact hMH.trans (centralizer_le_normalizer _)
  rcases le_or_inf_le_centralizer hM hMN with h | h
  · exact h
  · exfalso
    obtain ⟨S, hS'⟩ := exists_isSylowOf 2 M
    apply not_le_centralizer_of_isSylowOf hM hS'
    refine le_trans (le_inf hS'.le fun x hx => ?_) h
    obtain ⟨k, hk⟩ := hS'.isPGroup ⟨x, hx⟩
    exact hS.mem_of_pow_eq_one (hMH (hS'.le hx)) (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem sup_le_normalizer : L ⊔ conj L g ≤ normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer (hS.conj_le.trans (centralizer_le_normalizer _))

theorem sup_le_normalizer_conj : L ⊔ conj L g ≤ normalizer (conj L g : Set G) := by
  rw [hS.normalizer_conj_eq]
  exact hS.sup_le_normalizer

theorem normalizer_le_normalizer_sup :
    normalizer (L : Set G) ≤ normalizer ((L ⊔ conj L g : Subgroup G) : Set G) :=
  le_normalizer_sup le_rfl hS.normalizer_le_normalizer_conj

theorem mem_normalizer_sup : g ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G) := by
  rw [← conj_eq_self_iff, conj, Subgroup.map_sup]
  change conj L g ⊔ conj (conj L g) g = L ⊔ conj L g
  rw [hS.conj_conj_eq, sup_comm]

theorem conj_eq_or_eq {h : G} (hh : h ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G)) :
    conj L h = L ∨ conj L h = conj L g := by
  set M := conj L h with hM
  have hMq : CFSG.Open.IsQuasisimple ↥M := isQuasisimple_conj hS.quasisimple h
  have hMD : M ≤ L ⊔ conj L g := by
    calc M ≤ conj (L ⊔ conj L g) h := map_mono le_sup_left
      _ = L ⊔ conj L g := conj_eq_self_iff.mpr hh
  have hDM : L ⊔ conj L g ≤ normalizer (M : Set G) := by
    calc L ⊔ conj L g = conj (L ⊔ conj L g) h := (conj_eq_self_iff.mpr hh).symm
      _ ≤ conj (normalizer (L : Set G)) h := map_mono hS.sup_le_normalizer
      _ = normalizer (M : Set G) := (normalizer_conj L h).symm
  rcases le_or_inf_le_centralizer hMq (hMD.trans hS.sup_le_normalizer) with h1 | h1
  · left
    exact eq_of_le_of_card_ge h1 (by rw [hM, card_conj])
  · right
    have hLC : L ≤ centralizer (M : Set G) := fun l hl =>
      mem_centralizer_of_mem hMq (hMD.trans hS.sup_le_normalizer) h1
        (hDM (mem_sup_left hl)) hl
    have hMH : M ≤ centralizer (L : Set G) := le_centralizer_iff.mp hLC
    exact eq_of_le_of_card_ge (hS.le_conj_of_le_centralizer hMq hMH)
      (by rw [hM, card_conj, card_conj])

theorem conj_normalizer_eq {h : G} (hh : h ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G)) :
    conj (normalizer (L : Set G)) h = normalizer (L : Set G) := by
  rw [← normalizer_conj]
  rcases hS.conj_eq_or_eq hh with h1 | h1
  · rw [h1]
  · rw [h1, hS.normalizer_conj_eq]

theorem inv_mul_mem_normalizer {x y : G}
    (hx : x ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G))
    (hy : y ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G))
    (hxL : x ∉ normalizer (L : Set G)) (hyL : y ∉ normalizer (L : Set G)) :
    x⁻¹ * y ∈ normalizer (L : Set G) := by
  have hx' : conj L x = conj L g := (hS.conj_eq_or_eq hx).resolve_left
    (fun h => hxL (conj_eq_self_iff.mp h))
  have hy' : conj L y = conj L g := (hS.conj_eq_or_eq hy).resolve_left
    (fun h => hyL (conj_eq_self_iff.mp h))
  rw [← conj_eq_self_iff, ← conj_conj, hy', ← hx', conj_conj, inv_mul_cancel, conj_one]

theorem commutator_mem_normalizer {x y : G}
    (hx : x ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G))
    (hy : y ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G)) :
    ⁅x, y⁆ ∈ normalizer (L : Set G) := by
  have hnorm : ∀ z ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G),
      ∀ n ∈ normalizer (L : Set G), z * n * z⁻¹ ∈ normalizer (L : Set G) := by
    intro z hz n hn
    have h := hS.conj_normalizer_eq hz
    rw [← h]
    exact conj_mem_conj hn
  rw [commutatorElement_def]
  by_cases hxL : x ∈ normalizer (L : Set G)
  · have h1 := hnorm y hy x⁻¹ (inv_mem hxL)
    have h2 := mul_mem hxL h1
    simpa [mul_assoc] using h2
  by_cases hyL : y ∈ normalizer (L : Set G)
  · have h1 := hnorm x hx y hyL
    exact mul_mem h1 (inv_mem hyL)
  · have hn := hS.inv_mul_mem_normalizer hx hy hxL hyL
    set n := x⁻¹ * y with hndef
    have hyx : y = x * n := by rw [hndef]; group
    have h1 := hnorm x hx n hn
    have h2 := hnorm x hx _ (mul_mem h1 (inv_mem hn))
    rw [hyx]
    convert h2 using 1
    group

theorem le_normalizer_of_le_normalizer_sup {B : Subgroup G} (hB : ⁅B, B⁆ = B)
    (hBD : B ≤ normalizer ((L ⊔ conj L g : Subgroup G) : Set G)) :
    B ≤ normalizer (L : Set G) := by
  rw [← hB, commutator_le]
  intro x hx y hy
  exact hS.commutator_mem_normalizer (hBD hx) (hBD hy)

theorem core_le_centralizer :
    aschbacherThm5Core (L ⊔ conj L g) ≤ centralizer (L : Set G) :=
  core_le_centralizer_of _ hS.quasisimple le_sup_left ((core_le _).trans hS.sup_le_normalizer)

theorem core_le_centralizer_conj :
    aschbacherThm5Core (L ⊔ conj L g) ≤ centralizer (conj L g : Set G) :=
  core_le_centralizer_of _ (isQuasisimple_conj hS.quasisimple g) le_sup_right
    ((core_le _).trans hS.sup_le_normalizer_conj)

theorem commute_of_mem_core {o x : G} (ho : o ∈ aschbacherThm5Core (L ⊔ conj L g))
    (hx : x ∈ L ⊔ conj L g) : Commute o x := by
  have hD : L ⊔ conj L g ≤ centralizer ({o} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun a ha => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hS.core_le_centralizer ho) l hl)
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hS.core_le_centralizer_conj ho) a ha)
  exact (mem_centralizer_singleton_iff.mp (hD hx)).symm

theorem mem_normalizer_sup_of_conj_le {y : G}
    (hy : conj L y ≤ normalizer ((L ⊔ conj L g : Subgroup G) : Set G)) :
    y ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := conj L y with hBdef
  have hBq : CFSG.Open.IsQuasisimple ↥B := isQuasisimple_conj hS.quasisimple y
  have hBL : B ≤ normalizer (L : Set G) :=
    hS.le_normalizer_of_le_normalizer_sup (commutator_self_eq hBq) hy
  have hBA : B ≤ normalizer (conj L g : Set G) := hS.normalizer_conj_eq ▸ hBL
  have hBH : B ≤ normalizer (centralizer (L : Set G) : Set G) := hS.normalizer_centralizer ▸ hBL
  by_cases h1 : B ≤ centralizer (L : Set G)
  · have hBA' : B = conj L g :=
      eq_of_le_of_card_ge (hS.le_conj_of_le_centralizer hBq h1) (by rw [card_conj, card_conj])
    have hgy : g⁻¹ * y ∈ normalizer (L : Set G) := by
      rw [← conj_eq_self_iff, ← conj_conj, ← hBdef, hBA', conj_conj, inv_mul_cancel, conj_one]
    have h := mul_mem hS.mem_normalizer_sup (hS.normalizer_le_normalizer_sup hgy)
    simpa using h
  by_cases h2 : B ≤ centralizer (conj L g : Set G)
  · have hBL' : B = L :=
      eq_of_le_of_card_ge (hS.le_of_le_centralizer_conj hBq h2) (by rw [card_conj])
    exact hS.normalizer_le_normalizer_sup (conj_eq_self_iff.mp hBL')
  exfalso
  have hBC : B ⊓ centralizer (L : Set G) ≤ centralizer (B : Set G) :=
    (le_or_inf_le_centralizer hBq hBH).resolve_left h1
  obtain ⟨S, hSB⟩ := exists_isSylowOf 2 B
  have hS1 : S ≠ ⊥ := by
    intro hbot
    apply not_le_centralizer_of_isSylowOf hBq hSB
    rw [hbot]
    exact bot_le
  set H := centralizer (L : Set G) with hHdef
  have hSH : S ≤ normalizer (H : Set G) := hSB.le.trans hBH
  set Y := H ⊔ S with hY
  have hYH : Y ≤ normalizer (H : Set G) := sup_le Subgroup.le_normalizer hSH
  obtain ⟨P, hSP⟩ := (hSB.isPGroup.comap_subtype (K := Y)).exists_le_sylow
  set P' : Subgroup G := (P : Subgroup Y).map Y.subtype with hP'
  have hP'Y : IsSylowOf 2 P' Y := ⟨P, rfl⟩
  have hSP' : S ≤ P' := fun s hs => ⟨⟨s, (le_sup_right : S ≤ Y) hs⟩, hSP hs, rfl⟩
  have hPH : IsSylowOf 2 (P' ⊓ H) H := hP'Y.inf_of_le_normalizer le_sup_left hYH
  have hPH1 : P' ⊓ H ≠ ⊥ := ne_bot_of_isSylowOf_of_tightlyEmbedded hS.tightlyEmbedded_centralizer hPH
  have : Group.IsNilpotent ↥P' := hP'Y.isPGroup.isNilpotent
  have hPY : P' ≤ normalizer (H : Set G) := hP'Y.le.trans hYH
  have hnorm : ((P' ⊓ H).subgroupOf P').Normal := by
    rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro p hp
    rw [mem_normalizer_iff]
    intro x
    rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp (Subgroup.le_normalizer hp) x,
      ← mem_normalizer_iff.mp (hPY hp) x]
  have hne : (P' ⊓ H).subgroupOf P' ≠ ⊥ := by
    intro hbot
    apply hPH1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (mem_inf.mp hx).1⟩ : P') ∈ (P' ⊓ H).subgroupOf P' := hx
    rw [hbot, mem_bot] at hx'
    simpa using congrArg Subtype.val hx'
  obtain ⟨⟨u, hu⟩, hu1⟩ := (ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨huPH, huZ⟩ := mem_inf.mp hu
  rw [mem_subgroupOf] at huPH
  set u₀ : G := (u : G) with hu₀
  have hu₀H : u₀ ∈ H := (mem_inf.mp huPH).2
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    apply hu1
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨k, hk⟩ := hP'Y.isPGroup u
  have hu₀k : u₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hu₀A : u₀ ∈ conj L g := hS.mem_conj_of_pow_eq_one hu₀H hu₀k
  have hu₀S : u₀ ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have h := mem_center_iff.mp huZ ⟨s, hSP' hs⟩
    simpa using congrArg Subtype.val h
  have hQ : TightlyEmbedded (centralizer (conj (conj L g) y : Set G)) := by
    rw [centralizer_conj]
    exact tightlyEmbedded_conj hS.tightlyEmbedded_centralizer_conj y
  have hSQ : S ≤ centralizer (conj (conj L g) y : Set G) := by
    rw [centralizer_conj]
    exact hSB.le.trans (map_mono hS.le_centralizer_conj)
  have hNQ : normalizer (centralizer (conj (conj L g) y : Set G) : Set G) =
      normalizer (B : Set G) := by
    rw [centralizer_conj, normalizer_conj, centralizer_conj, normalizer_conj,
      hS.normalizer_centralizer, ← normalizer_conj L g, hS.normalizer_conj_eq, hBdef,
      normalizer_conj]
  have hu₀B : u₀ ∈ normalizer (B : Set G) := by
    rw [← hNQ]
    exact centralizer_two_subgroup_le _ S hQ hSB.isPGroup hSQ hS1 hu₀S
  have hu₀CB : u₀ ∈ centralizer (B : Set G) :=
    mem_centralizer_of_mem hBq hBA (le_trans (inf_le_inf_left B hS.conj_le) hBC) hu₀B hu₀A
  have hyN : y⁻¹ ∈ normalizer (H : Set G) := by
    by_contra hyN
    have hodd := hS.tightlyEmbedded_centralizer.2 y⁻¹ hyN
    have hmem : u₀ ∈ H ⊓ rightConjugate H y⁻¹ := by
      refine mem_inf.mpr ⟨hu₀H, ?_⟩
      rw [mem_rightConjugate_iff, inv_inv]
      have h := hu₀CB
      rw [hBdef, centralizer_conj, mem_conj_iff] at h
      exact h
    have hdvd : orderOf u₀ ∣ Nat.card (H ⊓ rightConjugate H y⁻¹ : Subgroup G) := by
      rw [← Subgroup.orderOf_mk u₀ hmem]
      exact orderOf_dvd_natCard _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu₀k)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hu₀1 (orderOf_eq_one_iff.mp (by simpa using hj))
    have h2 : 2 ∣ Nat.card (H ⊓ rightConjugate H y⁻¹ : Subgroup G) :=
      (dvd_pow_self 2 hj0).trans (hj ▸ hdvd)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hyL : y ∈ normalizer (L : Set G) := by
    rw [← hS.normalizer_centralizer]
    simpa using inv_mem hyN
  apply h2
  rw [hBdef, conj_eq_self_iff.mpr hyL]
  exact hS.le_centralizer_conj

end ClosureSetting

end Lemma22Full

end CFSG.ComponentClassification.AS76b
