module

import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.ClassTwoRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreScalar
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.Open
open scoped commutatorElement IsMulCommutative

section PrimeOrder

open Subgroup

theorem sup_zpowers_eq_top_of_index_eq_prime {A : Type*} [Group A] {p : ℕ} [Fact p.Prime]
    {F : Subgroup A} (hF : F.index = p) {ζ : A} (hζ : ζ ∉ F) : F ⊔ zpowers ζ = ⊤ := by
  have hp : p.Prime := Fact.out
  have h1 := Subgroup.relIndex_mul_index (le_sup_left : F ≤ F ⊔ zpowers ζ)
  rw [hF] at h1
  rcases (Nat.dvd_prime hp).mp (Dvd.intro_left _ h1) with h | h
  · exact Subgroup.index_eq_one.mp h
  · rw [h] at h1
    have h2 : F.relIndex (F ⊔ zpowers ζ) = 1 := by
      have := hp.pos
      nlinarith
    exact absurd (Subgroup.relIndex_eq_one.mp h2
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers ζ))) hζ

theorem zpowers_eq_of_ne_one_of_card_eq_prime {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {Z : Subgroup G} (hZ : Nat.card Z = p) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    zpowers z = Z := by
  have hp : p.Prime := Fact.out
  have hdvd : Nat.card (zpowers z) ∣ p :=
    hZ ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz)
  have hfinZ : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; exact hp.ne_zero)
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
    exact absurd h hz1
  · rw [h, hZ]

theorem mem_zpowers_of_orderOf_eq_prime {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {ζ y : G}
    (hζ : orderOf ζ = p) (hy : y ∈ zpowers ζ) (hy1 : y ≠ 1) : ζ ∈ zpowers y := by
  rw [zpowers_eq_of_ne_one_of_card_eq_prime (Z := zpowers ζ) (by rw [Nat.card_zpowers, hζ]) hy hy1]
  exact Subgroup.mem_zpowers ζ

theorem le_center_of_card_eq_prime_of_commutator {R : Type*} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] {Z : Subgroup R} (hZc : Nat.card Z = p) (hRR : commutator R = Z)
    (hexp : ∀ r : R, r ^ p = 1) : Z ≤ center R := by
  have hp : p.Prime := Fact.out
  have hZbot : Z ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hZc
    exact hp.one_lt.ne hZc
  have hnil : Group.IsNilpotent R :=
    IsPGroup.isNilpotent (p := p) fun r => ⟨1, by rw [pow_one]; exact hexp r⟩
  have : Z.Normal := hRR ▸ inferInstance
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hZbot
  have hdvd : Nat.card (Z ⊓ center R : Subgroup R) ∣ p :=
    hZc ▸ Subgroup.card_dvd_of_le (inf_le_left : Z ⊓ center R ≤ Z)
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hne
  · have hfinZ : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZc]; exact hp.ne_zero)
    exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge (inf_le_left : Z ⊓ center R ≤ Z)
      (by rw [h, hZc]))

end PrimeOrder

section Hyperplanes

variable {A : Type*} [CommGroup A]

theorem map_pow_ne_of_heisenberg {p : ℕ} [Fact p.Prime] {ζ a₀ : A} {α : MulAut A}
    (hζ : orderOf ζ = p) (hαζ : α ζ = ζ)
    (hαx : ∀ (k : ℕ) (x : A), (α ^ k) x * x⁻¹ ∈ Subgroup.zpowers ζ)
    (hαa : ∀ k : ℕ, 0 < k → k < p → (α ^ k) a₀ ≠ a₀) {k : ℕ} (hk0 : 0 < k) (hkp : k < p)
    {F : Subgroup A} (hF : F.index = p) (hζF : ζ ∉ F) : F.map (α ^ k).toMonoidHom ≠ F := by
  intro h
  have hαkζ : ∀ k : ℕ, (α ^ k) ζ = ζ := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hαζ, ih]
  have hfix : ∀ x ∈ F, (α ^ k) x = x := by
    intro x hx
    have hmem : (α ^ k) x ∈ F := h ▸ Subgroup.mem_map_of_mem (α ^ k).toMonoidHom hx
    have hy : (α ^ k) x * x⁻¹ ∈ F := F.mul_mem hmem (F.inv_mem hx)
    by_contra hne
    exact hζF (Subgroup.zpowers_le.mpr hy (mem_zpowers_of_orderOf_eq_prime hζ (hαx k x)
      fun h1 => hne (mul_inv_eq_one.mp h1)))
  obtain ⟨f, hf, z, hz, hfz⟩ := Subgroup.mem_sup.mp
    ((sup_zpowers_eq_top_of_index_eq_prime hF hζF) ▸ Subgroup.mem_top a₀)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine hαa k hk0 hkp ?_
  rw [← hfz, map_mul, hfix f hf, map_zpow, hαkζ]

end Hyperplanes

section Abstract

open Subgroup

variable {A D : Type*} [CommGroup A] [Finite A] [Group D] [Finite D]

theorem exists_isMulCommutative_pow_four_le_card_of_heisenberg {s p : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hp5 : 5 ≤ p) (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1)
    (hD : ∀ d : D, d ^ s = 1) (hc : commutator D ≤ center D) (ψ : A →* MulAut D) {ζ : A}
    (hψ : ψ ζ ≠ 1) {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hlen : ∀ k : ℕ, 0 < k → k < p → ∀ F : Subgroup A, F.index = p → ζ ∉ F →
      F.map (α ^ k).toMonoidHom ≠ F) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have hs : s.Prime := Fact.out
  by_cases hZ : ∀ z ∈ center D, ψ ζ z = z
  · exact exists_isMulCommutative_pow_four_le_card hs hD hc
      ((Nat.pow_le_pow_right hs.pos hp5).trans
        (pow_le_card_quotient_center_of_heisenberg hsp hA hD hc ψ hψ hατ hlen hZ))
  · push Not at hZ
    obtain ⟨z, hz, hzζ⟩ := hZ
    exact ⟨center D, inferInstance, (Nat.pow_le_pow_right hs.pos (by omega)).trans
      (pow_le_card_center_of_heisenberg hsp hA hD ψ hατ hlen ⟨z, hz, hzζ⟩)⟩

end Abstract

section HeisenbergGroup

open Subgroup

variable {R D : Type*} [Group R] [Finite R] [Group D] [Finite D]

theorem mem_zpowers_of_coe_mem_zpowers {G : Type*} [Group G] {A : Subgroup G} {ζ y : A}
    (h : (y : G) ∈ zpowers (ζ : G)) : y ∈ zpowers ζ := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩

theorem exists_isMulCommutative_pow_four_le_card_of_derived {s p : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hp5 : 5 ≤ p) (hsp : s ≠ p) {Z : Subgroup R} (hZc : Nat.card Z = p)
    (hRR : commutator R = Z) (hexp : ∀ r : R, r ^ p = 1) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (φ : R →* MulAut D) (hφ : ∃ z ∈ Z, φ z ≠ 1) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have hp : p.Prime := Fact.out
  obtain ⟨ζ, hζZ, hζφ⟩ := hφ
  have hZcen : Z ≤ center R := le_center_of_card_eq_prime_of_commutator hZc hRR hexp
  have hζ1 : ζ ≠ 1 := fun h => hζφ (h ▸ map_one φ)
  have hZgen : zpowers ζ = Z := zpowers_eq_of_ne_one_of_card_eq_prime hZc hζZ hζ1
  have hζord : orderOf ζ = p := by rw [← Nat.card_zpowers, hZgen, hZc]
  obtain ⟨a, b, hab⟩ : ∃ a b : R, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hbot : commutator R ≤ ⊥ := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
      exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (h g₁ g₂))
    have hZbot : Z = ⊥ := le_bot_iff.mp (hRR ▸ hbot)
    rw [hZbot, Subgroup.card_bot] at hZc
    exact hp.one_lt.ne hZc
  have hacen : a ∈ centralizer (Z : Set R) := fun z hz =>
    (Subgroup.mem_center_iff.mp (hZcen hz) a).symm
  have : IsMulCommutative Z :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hZcen y.2) x)⟩⟩
  set A : Subgroup R := Z ⊔ zpowers a with hAdef
  have hAcomm : IsMulCommutative A := isMulCommutative_sup_zpowers hacen
  have hZA : Z ≤ A := le_sup_left
  have haA : a ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hAnormal : A.Normal := Subgroup.Normal.of_commutator_le R (hRR ▸ hZA)
  have hbA : b ∈ normalizer (A : Set R) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top b
  let ψ : A →* MulAut D := φ.comp A.subtype
  let α : MulAut A := A.normalizerMonoidHom ⟨b, hbA⟩
  have hατ : ∀ x : A, φ b * ψ x = ψ (α x) * φ b := fun x => by
    change φ b * φ (x : R) = φ ((α x : A) : R) * φ b
    rw [← map_mul, ← map_mul]
    congr 1
    change b * (x : R) = b * x * b⁻¹ * b
    group
  let ζA : A := ⟨ζ, hZA hζZ⟩
  have hαζ : α ζA = ζA := by
    refine Subtype.ext ?_
    change b * ζ * b⁻¹ = ζ
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_center_iff.mp (hZcen hζZ) b
  have hαx : ∀ (k : ℕ) (x : A), (α ^ k) x * x⁻¹ ∈ zpowers ζA := fun k x => by
    refine mem_zpowers_of_coe_mem_zpowers ?_
    have h1 : (((α ^ k) x * x⁻¹ : A) : R) = ⁅b ^ k, (x : R)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom_pow_apply hbA k x,
        commutatorElement_def]
    have h2 : ⁅b ^ k, (x : R)⁆ ∈ Z := hRR ▸ (_root_.commutator_def R ▸
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    rw [h1]
    exact hZgen ▸ h2
  have hαa : ∀ k : ℕ, 0 < k → k < p → (α ^ k) ⟨a, haA⟩ ≠ ⟨a, haA⟩ := by
    intro k hk0 hkp h
    have h1 := congrArg Subtype.val h
    rw [coe_normalizerMonoidHom_pow_apply hbA k] at h1
    have hcomm : Commute (b ^ k) a := mul_inv_eq_iff_eq_mul.mp h1
    have hpk : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd =>
      Nat.not_le.mpr hkp (Nat.le_of_dvd hk0 hd)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := b) (n := k)
      (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one (hexp b)) hpk.symm)
    have := hcomm.pow_left m
    rw [hm] at this
    exact hab this.eq.symm
  exact exists_isMulCommutative_pow_four_le_card_of_heisenberg hp5 hsp
    (fun x : A => Subtype.ext (hexp x)) hD hc ψ (ζ := ζA) hζφ hατ
    fun k hk0 hkp F hF hζF => map_pow_ne_of_heisenberg (a₀ := ⟨a, haA⟩)
      (by rw [← Subgroup.orderOf_coe]; exact hζord) hαζ hαx hαa hk0 hkp hF hζF

end HeisenbergGroup

section Quotient

open Subgroup

variable {R D : Type*} [Group R] [Finite R] [Group D] [Finite D]

theorem exists_isMulCommutative_pow_four_le_card_of_quotient {s p m lam : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hpm : 5 ≤ (p - 1) * m) {Z : Subgroup R}
    (hRR : commutator R = Z) (hexp : ∀ r : R, r ^ p = 1) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (φ : R →* MulAut D) (hφZ : ∀ z ∈ Z, φ z = 1)
    (hφ : ∃ r, φ r ≠ 1) (σ : MulAut R) {τ : MulAut D} (hστ : ∀ r, τ * φ r = φ (σ r) * τ)
    (hord : orderOf (lam : ZMod p) = p - 1) (hσ : ∀ r, ∃ z ∈ Z, (σ ^ m) r = r ^ lam * z)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup R, Z ≤ F → F.index = p →
      F.map (σ ^ k).toMonoidHom ≠ F) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have : Z.Normal := hRR ▸ inferInstance
  have hσZ : Z.map σ.toMonoidHom = Z := by
    rw [← hRR, map_commutator_eq, MonoidHom.range_eq_top.mpr σ.surjective, ← commutator_def]
  have hcomm : IsMulCommutative (R ⧸ Z) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hRR.le
  let ψ : R ⧸ Z →* MulAut D := QuotientGroup.lift Z φ fun z hz => hφZ z hz
  let α : MulAut (R ⧸ Z) := QuotientGroup.congr Z Z σ hσZ
  have hαmk : ∀ (n : ℕ) (r : R), (α ^ n) (r : R ⧸ Z) = ((σ ^ n) r : R ⧸ Z) := by
    intro n
    induction n with
    | zero => intro r; rfl
    | succ n ih =>
      intro r
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
      exact (congrArg (α ^ n) (QuotientGroup.congr_mk Z Z σ hσZ r)).trans (ih (σ r))
  refine exists_isMulCommutative_pow_four_le_card_of_scalar' (A := R ⧸ Z) hsp ?_ hpm hD hc ψ
    ?_ (α := α) (τ := τ) ?_ ?_ hord ?_
  · intro a
    induction a using QuotientGroup.induction_on with
    | H r => rw [← QuotientGroup.mk_pow, hexp r]; rfl
  · obtain ⟨r, hr⟩ := hφ
    exact ⟨(r : R ⧸ Z), hr⟩
  · intro a
    induction a using QuotientGroup.induction_on with
    | H r => exact hστ r
  · intro a
    induction a using QuotientGroup.induction_on with
    | H r =>
      obtain ⟨z, hz, hzr⟩ := hσ r
      rw [hαmk, hzr, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one,
        QuotientGroup.mk_pow]
  · intro k hk0 hkm F hF hmap
    refine hlen k hk0 hkm (F.comap (QuotientGroup.mk' Z)) ?_ ?_ ?_
    · intro n hn
      change QuotientGroup.mk' Z n ∈ F
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
      exact F.one_mem
    · rw [Subgroup.index_comap_of_surjective F (QuotientGroup.mk'_surjective Z)]
      exact hF
    · ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h1 : (α ^ k) (y : R ⧸ Z) ∈ F.map (α ^ k).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hy
        rw [hmap, hαmk] at h1
        exact h1
      · intro hx
        have hx' : ((x : R) : R ⧸ Z) ∈ F.map (α ^ k).toMonoidHom := by rw [hmap]; exact hx
        obtain ⟨w, hw, hwx⟩ := hx'
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
        refine ⟨((σ ^ k).symm x), ?_, (σ ^ k).apply_symm_apply x⟩
        have h3 : (((σ ^ k).symm x : R) : R ⧸ Z) = (y : R ⧸ Z) := by
          refine (α ^ k).injective ?_
          rw [hαmk k, MulEquiv.apply_symm_apply]
          exact hwx.symm
        change QuotientGroup.mk' Z ((σ ^ k).symm x) ∈ F
        rw [QuotientGroup.mk'_apply, h3]
        exact hw

end Quotient

section Rank

open Subgroup

theorem exists_isMulCommutative_pow_four_le_card_of_derived_action {R D : Type*} [Group R]
    [Finite R] [Group D] [Finite D] {s p m lam : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hp5 : 5 ≤ p) (hm : 2 ≤ m) (hsp : s ≠ p) {Z : Subgroup R} (hZc : Nat.card Z = p)
    (hRR : commutator R = Z) (hexp : ∀ r : R, r ^ p = 1) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (φ : R →* MulAut D) (hφ : ∃ r, φ r ≠ 1) (σ : MulAut R)
    {τ : MulAut D} (hστ : ∀ r, τ * φ r = φ (σ r) * τ) (hord : orderOf (lam : ZMod p) = p - 1)
    (hσ : ∀ r, ∃ z ∈ Z, (σ ^ m) r = r ^ lam * z)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup R, Z ≤ F → F.index = p →
      F.map (σ ^ k).toMonoidHom ≠ F) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  by_cases hact : ∃ z ∈ Z, φ z ≠ 1
  · exact exists_isMulCommutative_pow_four_le_card_of_derived hp5 hsp hZc hRR hexp hD hc φ hact
  · push Not at hact
    refine exists_isMulCommutative_pow_four_le_card_of_quotient hsp ?_ hRR hexp hD hc φ hact hφ σ
      hστ hord hσ hlen
    calc 5 ≤ 4 * 2 := by norm_num
      _ ≤ (p - 1) * m := Nat.mul_le_mul (by omega) hm

theorem stmtOddCoreRankHeis {Y : Type} [Group Y] [Finite Y] {s p m : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 2 ≤ m) (hsp : s ≠ p)
    (Sg R Z : Subgroup Y) (t : Y) (lam : ℕ) (hSg : IsPGroup s Sg)
    (hRS : R ≤ Subgroup.normalizer (Sg : Set Y)) (hZc : Nat.card Z = p) (hRR : ⁅R, R⁆ = Z)
    (hexp : ∀ r ∈ R, r ^ p = 1) (htS : t ∈ Subgroup.normalizer (Sg : Set Y))
    (htR : t ∈ Subgroup.normalizer (R : Set Y)) (hord : orderOf (lam : ZMod p) = p - 1)
    (hscal : ∀ x ∈ R, ∃ z ∈ Z, t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z)
    (horb : ∀ k, 0 < k → k < m → ∀ F : Subgroup Y, Z ≤ F → F ≤ R → F.relIndex R = p →
      t ^ k ∉ Subgroup.normalizer (F : Set Y))
    (hnc : ¬ R ≤ Subgroup.centralizer (Sg : Set Y)) : 4 ≤ Open.pRank s Sg := by
  have := Fact.mk hs
  have := Fact.mk hp
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnc fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexpD, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let φR : R →* MulAut D := φ.comp (Subgroup.inclusion hRS)
  let σ : MulAut R := R.normalizerMonoidHom ⟨t, htR⟩
  have hστ : ∀ r : R, φ ⟨t, htS⟩ * φR r = φR (σ r) * φ ⟨t, htS⟩ := fun r => by
    change φ ⟨t, htS⟩ * φ (Subgroup.inclusion hRS r) =
      φ (Subgroup.inclusion hRS (σ r)) * φ ⟨t, htS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * (r : Y) = t * r * t⁻¹ * t
    group
  have hψ : ∃ r : R, φR r ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hxR, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hnc
    apply hx
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨x, hRS hxR⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) (hall ⟨x, hxR⟩)
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ p = 1 := by
      have hn : (⟨x, hRS hxR⟩ : Subgroup.normalizer (Sg : Set Y)) ^ p = 1 :=
        Subtype.ext (hexp x hxR)
      change (Sg.normalizerMonoidHom ⟨x, hRS hxR⟩) ^ p = 1
      rw [← map_pow, hn, map_one]
    have hθ : θ = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hθk, hθp⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k ((Nat.coprime_primes hs hp).mpr hsp)),
        pow_one] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = y := congrArg (fun f : MulAut Sg => ((f ⟨y, hy⟩ : Sg) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexpD d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  have hZR : Z ≤ R := by
    rw [← hRR]
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hg₁ hg₂) (R.inv_mem hg₁)) (R.inv_mem hg₂)
  have hcommR : commutator R = Z.subgroupOf R := by
    refine Subgroup.map_injective R.subtype_injective ?_
    rw [map_commutator_eq, Subgroup.range_subtype, hRR, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hZR]
  have hZc' : Nat.card (Z.subgroupOf R) = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv).trans hZc
  have hσ : ∀ r : R, ∃ z ∈ Z.subgroupOf R, (σ ^ m) r = r ^ lam * z := fun r => by
    obtain ⟨z, hz, hzr⟩ := hscal r r.2
    refine ⟨⟨z, hZR hz⟩, Subgroup.mem_subgroupOf.mpr hz, Subtype.ext ?_⟩
    rw [coe_normalizerMonoidHom_pow_apply htR m r, hzr]
    rfl
  have hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup R, Z.subgroupOf R ≤ F → F.index = p →
      F.map (σ ^ k).toMonoidHom ≠ F := by
    intro k hk0 hkm F hZF hF hmap
    have hrel : (F.map R.subtype).subgroupOf R = F :=
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective F
    refine horb k hk0 hkm (F.map R.subtype)
      (fun z hz => ⟨⟨z, hZR hz⟩, hZF (Subgroup.mem_subgroupOf.mpr hz), rfl⟩)
      (Subgroup.map_subtype_le F) ?_ (pow_mem_normalizer_map_subtype htR k hmap)
    change ((F.map R.subtype).subgroupOf R).index = p
    rw [hrel]
    exact hF
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_pow_four_le_card_of_derived_action
    (R := R) (m := m) (lam := lam) hp5 hm hsp hZc' hcommR (fun r => Subtype.ext (hexp r r.2)) hD
    hc φR hψ σ hστ hord hσ hlen
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  rw [hn] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hn (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

end Rank

end CFSG.AGLEmbeddingD2
