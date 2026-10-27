module

public import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped commutatorElement

section Abstract

open Subgroup

variable {A D : Type*} [CommGroup A] [Finite A] [Group D] [Finite D]

open scoped IsMulCommutative in
theorem pow_le_card_center_of_equivariant {s p r : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hA2 : p ^ 2 ≤ Nat.card A)
    (hD : ∀ d : D, d ^ s = 1) (ψ : A →* MulAut D) {α : MulAut A} {τ : MulAut D}
    (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ F : Subgroup A, F.map (α ^ k).toMonoidHom = F →
      F = ⊥ ∨ F = ⊤)
    (hnt : ∃ a : A, ∃ z ∈ center D, ψ a z ≠ z) : s ^ r ≤ Nat.card (center D) := by
  let ρ : MulAut D →* MulAut (center D) := MulAut.characteristic (center D)
  let _ : MulDistribMulAction A (center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  obtain ⟨a, z, hz, haz⟩ := hnt
  refine pow_le_card_of_equivariant hsp hA hA2
    (fun z => ⟨1, by rw [pow_one]; exact Subtype.ext (hD z)⟩)
    ⟨a, ⟨z, hz⟩, fun h => haz (congrArg Subtype.val h)⟩ (β := ρ τ) (fun a v => ?_) hirr
  change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
  rw [← map_mul, ← map_mul, hατ]

open scoped IsMulCommutative in
theorem exists_isMulCommutative_pow_le_card_of_center {s p r : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hA2 : p ^ 2 ≤ Nat.card A)
    (hD : ∀ d : D, d ^ s = 1) (hc : commutator D ≤ center D) (ψ : A →* MulAut D)
    (hψ : ∃ a, ψ a ≠ 1) {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ F : Subgroup A, F.map (α ^ k).toMonoidHom = F →
      F = ⊥ ∨ F = ⊤)
    (hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ r ≤ Nat.card E := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hcomm : IsMulCommutative (D ⧸ center D) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
  let ρ : MulAut D →* MulAut (D ⧸ center D) := quotientCenterAut
  let _ : MulDistribMulAction A (D ⧸ center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  have hDp : IsPGroup s D := fun d => ⟨1, by rw [pow_one]; exact hD d⟩
  have hVp : IsPGroup s (D ⧸ center D) := hDp.to_quotient _
  have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
  obtain ⟨m, hm⟩ := hAp.exists_card_eq
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (D ⧸ center D)) := by
    rw [hm, hn]
    exact Nat.coprime_pow_primes m n hp hs hsp.symm
  have hpV : ¬ p ∣ Nat.card (D ⧸ center D) := fun h => by
    rw [hn] at h
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow h)).symm
  have hnt : ∃ (a : A) (v : D ⧸ center D), a • v ≠ v := by
    obtain ⟨a, ha⟩ := hψ
    obtain ⟨d, hd⟩ : ∃ d : D, ψ a d ≠ d := by
      by_contra h
      push Not at h
      exact ha (MulEquiv.ext h)
    refine ⟨a, d, fun h => hd (apply_eq_of_mk_apply_eq ((Nat.coprime_primes hp hs).mpr
      hsp.symm) hD ?_ (hZ a) h)⟩
    rw [← map_pow, hA a, map_one]
  have hαβ : ∀ (a : A) (v : D ⧸ center D), ρ τ (a • v) = α a • ρ τ v := fun a v => by
    change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
    rw [← map_mul, ← map_mul, hατ]
  obtain ⟨F, hinj, hF, hne⟩ := exists_injective_fixedPiece_ne_bot hA hA2 hpV hnt hαβ hirr
  choose w hw hw1 using fun j => (Subgroup.bot_or_exists_ne_one
    (fixedPiece (F j) : Subgroup (D ⧸ center D))).resolve_left (hne j)
  have hcl := pow_card_le_card_closure_of_fixedPiece hp hVp hcop hinj hF hw hw1
  rw [Fintype.card_fin] at hcl
  choose d hd using fun j => QuotientGroup.mk_surjective (w j)
  have hB : ∀ (a : A) (v v' : D ⧸ center D),
      commPairing hc (a • v) (a • v') = commPairing hc v v' :=
    fun a v v' => commPairing_aut hc (hZ a) v v'
  have hcommute : (Set.range d).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    have h1 := pairing_fixedPiece_eq_one hp hcop (commPairing hc) hB (hF i) (hF j)
      (hinj.ne hij') (hw i) (hw j)
    rw [← hd i, ← hd j, commPairing_mk_mk] at h1
    have h2 : ⁅d i, d j⁆ = 1 := congrArg Subtype.val h1
    exact commutatorElement_eq_one_iff_commute.mp h2
  refine ⟨Subgroup.closure (Set.range d), Subgroup.isMulCommutative_closure hcommute,
    hcl.trans ?_⟩
  have hmap : (Subgroup.closure (Set.range d)).map (QuotientGroup.mk' (center D)) =
      Subgroup.closure (Set.range w) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    have hcomp : (⇑(QuotientGroup.mk' (center D)) ∘ d) = w := funext hd
    rw [hcomp]
  rw [← hmap]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)

theorem exists_isMulCommutative_pow_le_card {s p r : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hA2 : p ^ 2 ≤ Nat.card A)
    (hD : ∀ d : D, d ^ s = 1) (hc : commutator D ≤ center D) (ψ : A →* MulAut D)
    (hψ : ∃ a, ψ a ≠ 1) {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ F : Subgroup A, F.map (α ^ k).toMonoidHom = F →
      F = ⊥ ∨ F = ⊤) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ r ≤ Nat.card E := by
  by_cases hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z
  · exact exists_isMulCommutative_pow_le_card_of_center hsp hA hA2 hD hc ψ hψ hατ hirr hZ
  · push Not at hZ
    exact ⟨center D, inferInstance, pow_le_card_center_of_equivariant hsp hA hA2 hD ψ hατ hirr hZ⟩

end Abstract

theorem stmtOddCoreRank' :
    ∀ {Y : Type} [Group Y] [Finite Y] {s p r : ℕ}, s.Prime → s ≠ 2 → p.Prime → s ≠ p →
      ∀ (Sg X : Subgroup Y) (t : Y), IsPGroup s Sg → X ≤ Subgroup.normalizer (Sg : Set Y) →
        IsElemAbelian p X → p ^ 2 ≤ Nat.card X → t ∈ Subgroup.normalizer (Sg : Set Y) →
        t ∈ Subgroup.normalizer (X : Set Y) →
        (∀ k : ℕ, ¬ r ∣ k → ∀ Y₀ : Subgroup Y, Y₀ ≤ X →
          t ^ k ∈ Subgroup.normalizer (Y₀ : Set Y) → Y₀ = ⊥ ∨ Y₀ = X) →
        ¬ X ≤ Subgroup.centralizer (Sg : Set Y) → r ≤ Open.pRank s Sg := by
  intro Y _ _ s p r hs hs2 hp hsp Sg X t hSg hXN hX hX2 htS htX hirr hnt
  have := Fact.mk hs
  have := Fact.mk hp
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnt fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let _ : CommGroup X := @IsMulCommutative.instCommGroup _ _ hX.1
  let ψ : X →* MulAut D := φ.comp (Subgroup.inclusion hXN)
  let α : MulAut X := X.normalizerMonoidHom ⟨t, htX⟩
  have hατ : ∀ x : X, φ ⟨t, htS⟩ * ψ x = ψ (α x) * φ ⟨t, htS⟩ := fun x => by
    change φ ⟨t, htS⟩ * φ (Subgroup.inclusion hXN x) =
      φ (Subgroup.inclusion hXN (α x)) * φ ⟨t, htS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * (x : Y) = t * x * t⁻¹ * t
    group
  have hψ : ∃ x : X, ψ x ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hxX, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hnt
    apply hx
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨x, hXN hxX⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) (hall ⟨x, hxX⟩)
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ p = 1 := by
      have hn : (⟨x, hXN hxX⟩ : Subgroup.normalizer (Sg : Set Y)) ^ p = 1 :=
        Subtype.ext (hX.2 x hxX)
      change (Sg.normalizerMonoidHom ⟨x, hXN hxX⟩) ^ p = 1
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
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexp d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_pow_le_card hsp
    (fun x => Subtype.ext (hX.2 x x.2)) hX2 hD hc ψ hψ hατ
    (eq_bot_or_eq_top_of_map_normalizerMonoidHom_pow htX hirr)
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  rw [hm] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hm (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

theorem stmtOddCoreRank :
    ∀ {Y : Type} [Group Y] [Finite Y] {s p r : ℕ}, s.Prime → s ≠ 2 → p.Prime → s ≠ p → r.Prime →
      ∀ (Sg X : Subgroup Y) (t : Y), IsPGroup s Sg → X ≤ Subgroup.normalizer (Sg : Set Y) →
        IsElemAbelian p X → p ^ 2 ≤ Nat.card X → t ∈ Subgroup.normalizer (Sg : Set Y) →
        t ∈ Subgroup.normalizer (X : Set Y) →
        (∀ k : ℕ, ¬ r ∣ k → ∀ Y₀ : Subgroup Y, Y₀ ≤ X →
          t ^ k ∈ Subgroup.normalizer (Y₀ : Set Y) → Y₀ = ⊥ ∨ Y₀ = X) →
        ¬ X ≤ Subgroup.centralizer (Sg : Set Y) → r ≤ Open.pRank s Sg := by
  intro Y _ _ s p r hs hs2 hp hsp _ Sg X t hSg hXN hX hX2 htS htX hirr hnt
  exact stmtOddCoreRank' hs hs2 hp hsp Sg X t hSg hXN hX hX2 htS htX hirr hnt

end CFSG.AGLEmbedding
