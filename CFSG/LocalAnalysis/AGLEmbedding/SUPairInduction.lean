module

public import CFSG.LocalAnalysis.AGLEmbedding.SUPairInvolution
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.AGLEmbedding.SUPair

open Subgroup

variable {Y : Type} [Group Y]

@[expose] def aOf (K : Subgroup Y) (y : Y) : Subgroup Y := ⁅K, zpowers (y ^ 2)⁆

structure Good (K Z : Subgroup Y) (y : Y) : Prop where
  pow4 : y ^ 4 = 1
  heis : Heis27 (aOf K y) Z
  le : aOf K y ≤ K
  normal : K ≤ normalizer (aOf K y : Set Y)

abbrev conjS (g : Y) (H : Subgroup Y) : Subgroup Y := H.map (MulAut.conj g).toMonoidHom

theorem mem_conjS {g x : Y} {H : Subgroup Y} : x ∈ conjS g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_mem_conjS {g a : Y} {H : Subgroup Y} (ha : a ∈ H) : g * a * g⁻¹ ∈ conjS g H :=
  ⟨a, ha, by simp [MulAut.conj_apply]⟩

theorem conjS_eq_of_mem_normalizer {g : Y} {H : Subgroup Y} (hg : g ∈ normalizer (H : Set Y)) :
    conjS g H = H := by
  ext x
  rw [mem_conjS]
  have := (mem_normalizer_iff.mp (inv_mem hg) x)
  simpa [mul_assoc] using this.symm

theorem conjS_mul (g h : Y) (H : Subgroup Y) : conjS (g * h) H = conjS g (conjS h H) := by
  ext x
  simp only [mem_conjS, mul_inv_rev]
  group

theorem conjS_injective (g : Y) : Function.Injective (conjS g) := by
  intro H₁ H₂ h
  ext x
  have := congrArg (fun H => g * x * g⁻¹ ∈ H) h
  simp only [mem_conjS] at this
  simpa [mul_assoc] using this

theorem aOf_conj {K : Subgroup Y} {g y : Y} (hg : g ∈ normalizer (K : Set Y)) :
    aOf K (g * y * g⁻¹) = conjS g (aOf K y) := by
  rw [aOf, aOf, conjS, map_commutator, MonoidHom.map_zpowers]
  rw [show K.map (MulAut.conj g).toMonoidHom = conjS g K from rfl, conjS_eq_of_mem_normalizer hg]
  congr 2
  simp [MulAut.conj_apply, conj_pow]

variable {A Z : Subgroup Y}

theorem Heis27.conj (hA : Heis27 A Z) {g : Y} (hg : ∀ z ∈ Z, g * z = z * g) :
    Heis27 (conjS g A) Z := by
  have hgz : ∀ z ∈ Z, g * z * g⁻¹ = z := fun z hz => by rw [hg z hz]; group
  have hgz' : ∀ z ∈ Z, g⁻¹ * z * g = z := fun z hz => by
    have := hgz z hz
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [this]
      _ = z := by group
  have hmem : ∀ x, x ∈ conjS g A → ∃ a ∈ A, x = g * a * g⁻¹ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  refine ⟨?_, ?_, hA.card_center, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjS, card_map_of_injective (MulAut.conj g).injective, hA.card]
  · intro z hz
    rw [mem_conjS, hgz' z hz]
    exact hA.le hz
  · intro z hz x hx
    obtain ⟨a, ha, rfl⟩ := hmem x hx
    have h := hA.central z hz a ha
    calc z * (g * a * g⁻¹) = g * (g⁻¹ * z * g) * a * g⁻¹ := by group
      _ = g * (z * a) * g⁻¹ := by rw [hgz' z hz]; group
      _ = g * (a * z) * g⁻¹ := by rw [h]
      _ = g * a * g⁻¹ * (g * z * g⁻¹) := by group
      _ = g * a * g⁻¹ * z := by rw [hgz z hz]
  · intro x hx x' hx'
    obtain ⟨a, ha, rfl⟩ := hmem x hx
    obtain ⟨b, hb, rfl⟩ := hmem x' hx'
    have h := hA.comm_mem _ ha _ hb
    have e : g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ =
        g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by group
    rw [e, hgz _ h]
    exact h
  · intro c hc hcen
    obtain ⟨c', hc', rfl⟩ := hmem c hc
    have h : c' ∈ Z := by
      refine hA.center_le _ hc' fun a ha => ?_
      have := hcen (g * a * g⁻¹) (conj_mem_conjS ha)
      have e : g * (c' * a) * g⁻¹ = g * (a * c') * g⁻¹ := by
        calc g * (c' * a) * g⁻¹ = g * c' * g⁻¹ * (g * a * g⁻¹) := by group
          _ = g * a * g⁻¹ * (g * c' * g⁻¹) := this
          _ = g * (a * c') * g⁻¹ := by group
      have := congrArg (fun x => g⁻¹ * x * g) e
      simpa [mul_assoc] using this
    rw [hgz c' h]
    exact h
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hmem x hx
    rw [conj_pow, hA.cube a ha]
    group
  · obtain ⟨a, ha, b, hb, hab⟩ := hA.nonabelian
    refine ⟨g * a * g⁻¹, conj_mem_conjS ha, g * b * g⁻¹, conj_mem_conjS hb, fun h => hab ?_⟩
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this

variable {K : Subgroup Y}

theorem Good.conj {y : Y} (hy : Good K Z y) {g : Y} (hgK : g ∈ normalizer (K : Set Y))
    (hgZ : ∀ z ∈ Z, g * z = z * g) : Good K Z (g * y * g⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [conj_pow, hy.pow4]
    group
  · rw [aOf_conj hgK]
    exact hy.heis.conj hgZ
  · calc aOf K (g * y * g⁻¹) = conjS g (aOf K y) := aOf_conj hgK
      _ ≤ conjS g K := map_mono hy.le
      _ = K := conjS_eq_of_mem_normalizer hgK
  · rw [aOf_conj hgK]
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    rw [mem_conjS, mem_conjS]
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hgK) k).mp hk
      simpa using this
    have := mem_normalizer_iff.mp (hy.normal hk') (g⁻¹ * x * g)
    rw [show g⁻¹ * k * g * (g⁻¹ * x * g) * (g⁻¹ * k * g)⁻¹ = g⁻¹ * (k * x * k⁻¹) * g by group]
      at this
    exact this

theorem mem_of_mem_inf_of_commute (hA : Heis27 A Z) {B : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {c : Y} (hcA : c ∈ A) (hcB : c ∈ B) : c ∈ Z :=
  hA.center_le c hcA fun a ha => (hAB a ha c hcB).symm

variable [Finite Y]

theorem card_sup_ge_of_commute (hA : Heis27 A Z) {B : Subgroup Y} (hB : Nat.card B = 27)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : 243 ≤ Nat.card ↥(A ⊔ B) := by
  classical
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => show (a : Y) * b = b * a from hAB _ a.2 _ b.2
  set φ : ↥A × ↥B →* Y := MonoidHom.noncommCoprod A.subtype B.subtype hcomm with hφ
  have hφapp : ∀ k : ↥A × ↥B, φ k = (k.1 : Y) * k.2 := fun k => by
    rw [hφ, MonoidHom.noncommCoprod_apply]
    rfl
  have hrange : φ.range = A ⊔ B := by
    rw [hφ, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hcard : Nat.card (↥A × ↥B) = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← card_eq_card_quotient_mul_card_subgroup]
  rw [Nat.card_prod, hA.card, hB] at hcard
  have hmemZ : ∀ k : φ.ker, ((k : ↥A × ↥B).1 : Y) ∈ Z := by
    rintro ⟨⟨a, b⟩, hk⟩
    have hab : (a : Y) * (b : Y) = 1 := (hφapp (a, b)).symm.trans hk
    have hb : (a : Y) = (b : Y)⁻¹ := eq_inv_of_mul_eq_one_left hab
    exact mem_of_mem_inf_of_commute hA hAB a.2 (hb ▸ B.inv_mem b.2)
  have hker : Nat.card φ.ker ≤ 3 := by
    have hinj : Function.Injective (fun k : φ.ker => (⟨_, hmemZ k⟩ : ↥Z)) := by
      rintro ⟨⟨a, b⟩, hk⟩ ⟨⟨a', b'⟩, hk'⟩ h
      have hab : (a : Y) * (b : Y) = 1 := (hφapp (a, b)).symm.trans hk
      have hab' : (a' : Y) * (b' : Y) = 1 := (hφapp (a', b')).symm.trans hk'
      have haa : (a : Y) = a' := by simpa using congrArg Subtype.val h
      have hbb : (b : Y) = b' := by
        have e1 : (b : Y) = (a : Y)⁻¹ := eq_inv_of_mul_eq_one_right hab
        have e2 : (b' : Y) = (a' : Y)⁻¹ := eq_inv_of_mul_eq_one_right hab'
        rw [e1, e2, haa]
      exact Subtype.ext (Prod.ext (Subtype.ext haa) (Subtype.ext hbb))
    exact (Nat.card_le_card_of_injective _ hinj).trans hA.card_center.le
  rw [← hrange]
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  nlinarith

theorem good_claim (hK : Nat.card K ≤ 243) :
    ∀ P : Subgroup Y, IsPGroup 2 P → P ≤ normalizer (K : Set Y) →
      (∀ g ∈ P, ∀ z ∈ Z, g * z = z * g) →
      ∀ y ∈ P, ∀ y' ∈ P, Good K Z y → Good K Z y' →
        aOf K y' = aOf K y ∨ ∀ a ∈ aOf K y, ∀ b ∈ aOf K y', a * b = b * a := by
  suffices key : ∀ n : ℕ, ∀ P : Subgroup Y, Nat.card P = n → IsPGroup 2 P →
      P ≤ normalizer (K : Set Y) → (∀ g ∈ P, ∀ z ∈ Z, g * z = z * g) →
      ∀ y ∈ P, ∀ y' ∈ P, Good K Z y → Good K Z y' →
        aOf K y' = aOf K y ∨ ∀ a ∈ aOf K y, ∀ b ∈ aOf K y', a * b = b * a from
    fun P => key _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hPn hP2 hPK hPZ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have step1 : ∀ x ∈ P, Good K Z x → ∀ g ∈ P,
      conjS g (aOf K x) = aOf K x ∨
        ∀ a ∈ aOf K x, ∀ b ∈ conjS g (aOf K x), a * b = b * a := by
    intro x hx hgx g hg
    by_cases htop : zpowers x = P
    · left
      have hgx' : g ∈ zpowers x := htop ▸ hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hgx'
      rw [← aOf_conj (hPK hg)]
      congr 1
      rw [((Commute.refl x).zpow_left k).eq]
      group
    ·
      set H' : Subgroup ↥P := (zpowers x).subgroupOf P with hH'
      have hxP : zpowers x ≤ P := zpowers_le.mpr hx
      have hH'top : H' ≠ ⊤ := by
        intro h
        apply htop
        exact le_antisymm hxP ((subgroupOf_eq_top.mp h))
      obtain ⟨M', hM'c, hHM'⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H').resolve_left hH'top
      haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
      have hM'n : M'.Normal :=
        NormalizerCondition.normal_of_coatom M' normalizerCondition_of_isNilpotent hM'c
      set M : Subgroup Y := M'.map P.subtype with hM
      have hMP : M ≤ P := map_subtype_le M'
      have hxM : x ∈ M := ⟨⟨x, hx⟩, hHM' (mem_subgroupOf.mpr (mem_zpowers x)), rfl⟩
      have hgxM : g * x * g⁻¹ ∈ M := by
        obtain ⟨m, hm, hmx⟩ := hxM
        refine ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, hM'n.conj_mem m hm ⟨g, hg⟩, ?_⟩
        rw [← hmx]
        simp
      have hMcard : Nat.card M < n := by
        rw [← hPn, hM, card_map_of_injective P.subtype_injective]
        have hlt : M' < ⊤ := hM'c.lt_top
        have := Subgroup.card_lt_of_lt hlt
        rwa [card_top] at this
      have := ih _ hMcard M rfl (hP2.to_le hMP) (hMP.trans hPK) (fun g' hg' => hPZ g' (hMP hg'))
        x hxM (g * x * g⁻¹) hgxM hgx (hgx.conj (hPK hg) (hPZ g hg))
      rwa [aOf_conj (hPK hg)] at this
  intro y hy y' hy' hgy hgy'
  set A := aOf K y with hA
  set u' := y' ^ 2 with hu'
  have hu'P : u' ∈ P := pow_mem hy' 2
  have hu'2 : u' ^ 2 = 1 := by rw [hu', ← pow_mul]; exact hgy'.pow4
  have step2 : conjS u' A = A := by
    rcases step1 y hy hgy u' hu'P with h1 | h1
    · exact h1
    exfalso
    rcases step1 y hy hgy y' hy' with h2 | h2
    · apply absurd hgy.heis.nonabelian
      push Not
      intro a ha b hb
      have hA' : conjS u' A = A := by rw [hu', sq, conjS_mul, h2, h2]
      exact h1 a ha b (hA' ▸ hb)
    have hgood'' := hgy.conj (hPK hy') (hPZ y' hy')
    have hy''P : y' * y * y'⁻¹ ∈ P := P.mul_mem (P.mul_mem hy' hy) (P.inv_mem hy')
    have hA'' : aOf K (y' * y * y'⁻¹) = conjS y' A := aOf_conj (hPK hy')
    rcases step1 _ hy''P hgood'' y' hy' with h3 | h3
    ·
      rw [hA''] at h3
      have : conjS y' A = A := conjS_injective y' h3
      apply absurd hgy.heis.nonabelian
      push Not
      intro a ha b hb
      exact h2 a ha b (this ▸ hb)
    · rw [hA'', ← conjS_mul] at h3
      have hAy : Heis27 (conjS y' A) Z := hA'' ▸ hgood''.heis
      have hAu : Heis27 (conjS u' A) Z := by
        have := (hgy.conj (hPK hu'P) (hPZ u' hu'P)).heis
        rwa [aOf_conj (hPK hu'P)] at this
      have hcard := card_sup_ge_of_commute hgy.heis hAy.card h2
      have hsupK : A ⊔ conjS y' A ≤ K := sup_le hgy.le (hA'' ▸ hgood''.le)
      have hsup : A ⊔ conjS y' A = K :=
        eq_of_le_of_card_ge hsupK (hK.trans hcard)
      have hcen : ∀ b ∈ conjS u' A, ∀ k ∈ K, b * k = k * b := by
        intro b hb k hk
        rw [← hsup] at hk
        have hle : A ⊔ conjS y' A ≤ centralizer ({b} : Set Y) := by
          refine sup_le (fun a ha => ?_) (fun a ha => ?_)
          · exact mem_centralizer_singleton_iff.mpr (h1 a ha b hb)
          · exact mem_centralizer_singleton_iff.mpr
              (h3 a ha b (by rwa [show y' * y' = u' by rw [hu', sq]]))
        have hcl : k ∈ centralizer ({b} : Set Y) := hle hk
        exact (mem_centralizer_singleton_iff.mp hcl).symm
      apply absurd hAu.nonabelian
      push Not
      intro a ha b hb
      have hbK : b ∈ K := by
        have := (hgy.conj (hPK hu'P) (hPZ u' hu'P)).le
        rw [aOf_conj (hPK hu'P)] at this
        exact this hb
      exact hcen a ha b hbK
  have huA : ∀ a ∈ A, u' * a * u'⁻¹ ∈ A := fun a ha => step2 ▸ conj_mem_conjS ha
  rcases centralizes_or_le_commutator hgy.heis hu'2 huA (hPZ u' hu'P) with hc | hc
  · right
    have h1 : ⁅⁅zpowers u', A⁆, K⁆ = ⊥ := by
      have : ⁅zpowers u', A⁆ = ⊥ := by
        rw [commutator_eq_bot_iff_le_centralizer]
        intro g hg
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
        rw [mem_centralizer_iff]
        intro a ha
        exact ((Commute.zpow_right (hc a ha).symm k : Commute a (u' ^ k))).eq
      rw [this, commutator_bot_left]
    have h2 : ⁅⁅A, K⁆, zpowers u'⁆ = ⊥ := by
      have hle : ⁅A, K⁆ ≤ A := by
        rw [commutator_le]
        intro a ha k hk
        rw [commutatorElement_def]
        have := (mem_normalizer_iff.mp (hgy.normal hk) a⁻¹).mp (inv_mem ha)
        rw [show a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) by group]
        exact A.mul_mem ha this
      refine eq_bot_iff.mpr ((commutator_mono hle le_rfl).trans (le_of_eq ?_))
      rw [commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left (hc a ha) k : Commute (u' ^ k) a)).eq
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    have h4 : ⁅aOf K y', A⁆ = ⊥ := by rw [aOf, ← hu']; exact h3
    intro a ha b hb
    rw [commutator_eq_bot_iff_le_centralizer] at h4
    exact (mem_centralizer_iff.mp (h4 hb) a ha)
  · left
    have hle : A ≤ aOf K y' := hc.trans (commutator_mono hgy.le le_rfl)
    exact (eq_of_le_of_card_ge hle (by rw [hgy.heis.card, hgy'.heis.card])).symm

end CFSG.AGLEmbedding.SUPair
