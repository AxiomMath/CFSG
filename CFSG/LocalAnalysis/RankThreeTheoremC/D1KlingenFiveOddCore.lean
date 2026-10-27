module

import CFSG.LocalAnalysis.AGLEmbeddingD2.ClassTwoRank
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces
public import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open
open scoped commutatorElement

section Pieces

open CFSG.AGLEmbedding

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem kl5_exists_fixedPiece_ne_bot [Finite A] [Finite V] {p : ℕ} [Fact p.Prime]
    (hA : ∀ a : A, a ^ p = 1) (hV : ¬ p ∣ Nat.card V) {z : A} (hz : ∃ v : V, z • v ≠ v) :
    ∃ F : Subgroup A, F.index = p ∧ z ∉ F ∧ (fixedPiece F : Subgroup V) ≠ ⊥ := by
  by_contra hno
  push Not at hno
  have hle : ∀ F : Subgroup A, F.index = 1 ∨ F.index = p →
      (fixedBy F : Subgroup V) ≤ fixedBy (Subgroup.zpowers z) := by
    intro F hF
    by_cases hzF : z ∈ F
    · exact fun v hv a ha => hv a (Subgroup.zpowers_le.mpr hzF ha)
    · rcases hF with hF | hF
      · exact absurd (Subgroup.index_eq_one.mp hF ▸ Subgroup.mem_top z) hzF
      · exact (fixedPiece_eq_bot_iff.mp (hno F hF hzF)).trans (fixedBy_top_le _)
  have htop := CFSG.PreuniquenessRankFour.Helpers.coprime_group_generated_by_prime_fixedSubgroups
    (acting := A) (source := V) p hV hA
  have hsup : sSup {fixedGroup : Subgroup V | ∃ kernel : Subgroup A,
      (kernel.index = 1 ∨ kernel.index = p) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} ≤
      fixedBy (Subgroup.zpowers z) :=
    sSup_le fun Y ⟨F, hF, hY⟩ =>
      (show Y ≤ fixedBy F from fun y hy a ha => hY a ha y hy).trans (hle F hF)
  obtain ⟨v, hv⟩ := hz
  exact hv (hsup (htop ▸ Subgroup.mem_top v) z (Subgroup.mem_zpowers z))

theorem kl5_map_eq_self_of_pow_eq_self {p : ℕ} (hp : p.Prime) {α : MulAut A} (hαp : α ^ p = 1)
    {F : Subgroup A} {k : ℕ} (hk0 : 0 < k) (hkp : k < p)
    (hF : F.map (α ^ k).toMonoidHom = F) : F.map α.toMonoidHom = F := by
  have hpk : Nat.Coprime k p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd =>
      Nat.not_le.mpr hkp (Nat.le_of_dvd hk0 hd)).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := α) (n := k)
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hαp) hpk)
  have hpow : ∀ m : ℕ, F.map ((α ^ k) ^ m).toMonoidHom = F := by
    intro m
    induction m with
    | zero => exact Subgroup.map_id F
    | succ m ih => rw [pow_succ, map_mul_toMonoidHom, hF, ih]
  rw [← hm]
  exact hpow m

theorem kl5_exists_injective_fixedPiece_ne_bot [Finite A] [Finite V] {p : ℕ} [Fact p.Prime]
    (hA : ∀ a : A, a ^ p = 1) (hV : ¬ p ∣ Nat.card V) {z : A} (hz : ∃ v : V, z • v ≠ v)
    {α : MulAut A} {β : MulAut V} (hαβ : ∀ a v, β (a • v) = α a • β v) (hαp : α ^ p = 1)
    (hnoinv : ∀ F : Subgroup A, F.index = p → z ∉ F → F.map α.toMonoidHom ≠ F) :
    ∃ F : Fin p → Subgroup A, Function.Injective F ∧ (∀ j, (F j).index = p) ∧
      ∀ j, (fixedPiece (F j) : Subgroup V) ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨F₀, hF₀, hzF₀, hne⟩ := kl5_exists_fixedPiece_ne_bot hA hV hz
  have hmap : ∀ i j : ℕ, i < j → j < p →
      F₀.map (α ^ i).toMonoidHom ≠ F₀.map (α ^ j).toMonoidHom := by
    intro i j hij hjp h
    have hj : α ^ j = α ^ i * α ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hj, map_mul_toMonoidHom] at h
    exact hnoinv F₀ hF₀ hzF₀ (kl5_map_eq_self_of_pow_eq_self hp hαp (by omega) (by omega)
      (Subgroup.map_injective (α ^ i).injective h).symm)
  refine ⟨fun j => F₀.map (α ^ (j : ℕ)).toMonoidHom, ?_, fun j => ?_, fun j => ?_⟩
  · intro i j hij
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with h | h
    · exact hmap i j h j.2 hij
    · exact hmap j i h i.2 hij.symm
  · change (F₀.map (α ^ (j : ℕ)).toMonoidHom).index = p
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact hF₀
  · intro hbot
    obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
    have hmem := map_fixedPiece_le (pow_apply_smul hαβ j) F₀ ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 ((β ^ (j : ℕ)).injective (hmem.trans (map_one _).symm))

theorem kl5_pow_le_card_of_orbit [Finite A] [Finite V] {s p : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : IsPGroup s V) {z : A}
    (hz : ∃ v : V, z • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v) (hαp : α ^ p = 1)
    (hnoinv : ∀ F : Subgroup A, F.index = p → z ∉ F → F.map α.toMonoidHom ≠ F) :
    s ^ p ≤ Nat.card V := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
  obtain ⟨a, ha⟩ := hAp.exists_card_eq
  obtain ⟨b, hb⟩ := hV.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [ha, hb]
    exact Nat.coprime_pow_primes a b hp hs hsp.symm
  have hpV : ¬ p ∣ Nat.card V := fun h => by
    rw [hb] at h
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨F, hinj, hF, hne⟩ := kl5_exists_injective_fixedPiece_ne_bot hA hpV hz hαβ hαp hnoinv
  simpa using pow_card_le_card_of_fixedPiece_ne_bot hp hV hcop hinj hF hne

end Pieces

section Abstract

open Subgroup CFSG.AGLEmbedding

variable {A D : Type*} [CommGroup A] [Finite A] [Group D] [Finite D]

open scoped IsMulCommutative in
theorem kl5_exists_isMulCommutative_pow_four_le_card {s p : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hp5 : 5 ≤ p) (hA : ∀ a : A, a ^ p = 1) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (ψ : A →* MulAut D) {z : A} (hψ : ψ z ≠ 1)
    {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ) (hαp : α ^ p = 1)
    (hnoinv : ∀ F : Subgroup A, F.index = p → z ∉ F → F.map α.toMonoidHom ≠ F) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  by_cases hZ : ∀ w ∈ center D, ψ z w = w
  ·
    have hcomm : IsMulCommutative (D ⧸ center D) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
    let ρ : MulAut D →* MulAut (D ⧸ center D) := quotientCenterAut
    let _ : MulDistribMulAction A (D ⧸ center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
    have hV : ∀ v : D ⧸ center D, v ^ s = 1 := fun v => by
      induction v using QuotientGroup.induction_on with
      | H d => rw [← QuotientGroup.mk_pow, hD d]; rfl
    have hnt : ∃ v : D ⧸ center D, z • v ≠ v := by
      obtain ⟨d, hd⟩ : ∃ d : D, ψ z d ≠ d := by
        by_contra h
        push Not at h
        exact hψ (MulEquiv.ext h)
      refine ⟨d, fun h => hd (apply_eq_of_mk_apply_eq ((Nat.coprime_primes hp hs).mpr
        hsp.symm) hD ?_ hZ h)⟩
      rw [← map_pow, hA z, map_one]
    have hcard : s ^ p ≤ Nat.card (D ⧸ center D) :=
      kl5_pow_le_card_of_orbit hsp hA (fun v => ⟨1, by rw [pow_one]; exact hV v⟩) hnt
        (β := ρ τ) (fun a v => by
          change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
          rw [← map_mul, ← map_mul, hατ]) hαp hnoinv
    exact CFSG.AGLEmbeddingD2.exists_isMulCommutative_pow_four_le_card hs hD hc
      ((Nat.pow_le_pow_right hs.pos hp5).trans hcard)
  ·
    push Not at hZ
    obtain ⟨w, hw, hwz⟩ := hZ
    let ρ : MulAut D →* MulAut (center D) := MulAut.characteristic (center D)
    let _ : MulDistribMulAction A (center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
    have hcard : s ^ p ≤ Nat.card (center D) :=
      kl5_pow_le_card_of_orbit hsp hA
        (fun w => ⟨1, by rw [pow_one]; exact Subtype.ext (hD w)⟩) (z := z)
        ⟨⟨w, hw⟩, fun h => hwz (congrArg Subtype.val h)⟩ (β := ρ τ) (fun a v => by
          change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
          rw [← map_mul, ← map_mul, hατ]) hαp hnoinv
    exact ⟨center D, inferInstance, (Nat.pow_le_pow_right hs.pos (by omega)).trans hcard⟩

end Abstract

theorem oddCore_centralized_of_hyperplane {Y : Type} [Group Y] [Finite Y] {s p : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p)
    (Sg X : Subgroup Y) (σ z : Y) (hSg : IsPGroup s Sg) (hrank : Open.pRank s Sg ≤ 3)
    (hXS : X ≤ Subgroup.normalizer (Sg : Set Y))
    (hσS : σ ∈ Subgroup.normalizer (Sg : Set Y)) (hX : IsElemAbelian p X)
    (hσX : σ ∈ Subgroup.normalizer (X : Set Y))
    (hσp : ∀ x ∈ X, σ ^ p * x * (σ ^ p)⁻¹ = x) (hzX : z ∈ X)
    (hz : ∀ F : Subgroup Y, F ≤ X → F.relIndex X = p →
      σ ∈ Subgroup.normalizer (F : Set Y) → z ∈ F) :
    z ∈ Subgroup.centralizer (Sg : Set Y) := by
  by_contra hnc
  have := Fact.mk hs
  have := Fact.mk hp
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnc (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let _ : CommGroup X := @IsMulCommutative.instCommGroup _ _ hX.1
  let ψ : X →* MulAut D := φ.comp (Subgroup.inclusion hXS)
  let α : MulAut X := X.normalizerMonoidHom ⟨σ, hσX⟩
  let z' : X := ⟨z, hzX⟩
  have hατ : ∀ x : X, φ ⟨σ, hσS⟩ * ψ x = ψ (α x) * φ ⟨σ, hσS⟩ := fun x => by
    change φ ⟨σ, hσS⟩ * φ (Subgroup.inclusion hXS x) =
      φ (Subgroup.inclusion hXS (α x)) * φ ⟨σ, hσS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change σ * (x : Y) = σ * x * σ⁻¹ * σ
    group
  have hψ : ψ z' ≠ 1 := by
    intro hall
    apply hnc
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨z, hXS hzX⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) hall
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ p = 1 := by
      have hn : (⟨z, hXS hzX⟩ : Subgroup.normalizer (Sg : Set Y)) ^ p = 1 :=
        Subtype.ext (hX.2 z hzX)
      change (Sg.normalizerMonoidHom ⟨z, hXS hzX⟩) ^ p = 1
      rw [← map_pow, hn, map_one]
    have hθ : θ = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hθk, hθp⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k ((Nat.coprime_primes hs hp).mpr hsp)),
        pow_one] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : z * y * z⁻¹ = y := congrArg (fun f : MulAut Sg => ((f ⟨y, hy⟩ : Sg) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexp d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun w => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (w : Sg) w.2)
  have hαp : α ^ p = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [CFSG.AGLEmbedding.coe_normalizerMonoidHom_pow_apply hσX p x]
    exact hσp x x.2
  have hnoinv : ∀ F : Subgroup X, F.index = p → z' ∉ F → F.map α.toMonoidHom ≠ F := by
    intro F hF hzF hmap
    refine hzF ?_
    have hrel : (F.map X.subtype).subgroupOf X = F :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective F
    have hnorm : σ ∈ Subgroup.normalizer ((F.map X.subtype : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨α x, ?_, rfl⟩
        rw [← hmap]
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x', hx', hx'eq⟩
        have hyX : y ∈ X := by
          have hmem : σ * y * σ⁻¹ ∈ X := hx'eq ▸ x'.2
          exact ((Subgroup.mem_normalizer_iff.mp hσX) y).mpr hmem
        refine ⟨⟨y, hyX⟩, ?_, rfl⟩
        have h1 : α ⟨y, hyX⟩ = x' := Subtype.ext hx'eq.symm
        have h2 : α ⟨y, hyX⟩ ∈ F.map α.toMonoidHom := by rw [hmap, h1]; exact hx'
        obtain ⟨w, hw, hweq⟩ := h2
        rwa [α.injective hweq] at hw
    obtain ⟨x, hx, hxz⟩ := hz (F.map X.subtype) (Subgroup.map_subtype_le F)
      (by
        change ((F.map X.subtype).subgroupOf X).index = p
        rw [hrel]
        exact hF) hnorm
    have hxz' : x = z' := Subtype.ext hxz
    rwa [hxz'] at hx
  obtain ⟨E, hEcomm, hEcard⟩ := kl5_exists_isMulCommutative_pow_four_le_card hsp hp5
    (fun x => Subtype.ext (hX.2 x x.2)) hD hc ψ hψ hατ hαp hnoinv
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  rw [hn] at hEcard
  have h4 : 4 ≤ Open.pRank s Sg :=
    ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
      (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
        (fun e => Subtype.ext (hD e)) hn (Sg.subtype.comp (D.subtype.comp E.subtype))
        (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) (by
          rintro _ ⟨e, rfl⟩
          exact ((e : D) : Sg).2))
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
