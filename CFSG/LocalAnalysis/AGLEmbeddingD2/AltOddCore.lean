module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltData
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.ClassTwoRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreD2
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreLemmaSPrime
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCorePiecesD2
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreScalar
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding
open scoped commutatorElement

section Pieces

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem pow_two_mul_le_card_of_scalar' [Finite A] [Finite V] {s p m lam : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : ∀ v : V, v ^ s = 1)
    (hnt : ∃ a : A, ∃ v : V, a • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v) (hα : ∀ a, (α ^ m) a = a ^ lam)
    (hord : orderOf (lam : ZMod p) = p - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F) :
    s ^ ((p - 1) * m) ≤ Nat.card V := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
  have hVp : IsPGroup s V := fun v => ⟨1, by rw [pow_one]; exact hV v⟩
  obtain ⟨a, ha⟩ := hAp.exists_card_eq
  obtain ⟨b, hb⟩ := hVp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [ha, hb]
    exact Nat.coprime_pow_primes a b hp hs hsp.symm
  have hpV : ¬ p ∣ Nat.card V := fun h => by
    rw [hb] at h
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨F, hinj, hF, hne⟩ := exists_injective_fixedPiece_ne_bot_of_orbit hA hpV hnt hαβ hlen
  have hind := iSupIndep_fixedPiece (pairwise_sup_eq_top_of_index_eq_prime hp hinj hF) hcop
  calc s ^ ((p - 1) * m) = (s ^ (p - 1)) ^ Fintype.card (Fin m) := by
        rw [Fintype.card_fin, pow_mul]
    _ ≤ Nat.card (⨆ j, fixedPiece (F j) : Subgroup V) :=
        pow_card_le_card_iSup hind fun j =>
          pow_pred_le_card_fixedPiece hp hs hsp hA hV hαβ m lam hα hord (hF j) (hne j)
    _ ≤ Nat.card V := Subgroup.card_le_card_group _

end Pieces

section Abstract

open Subgroup

variable {A D : Type*} [CommGroup A] [Finite A] [Group D] [Finite D]

open scoped IsMulCommutative in
theorem pow_two_mul_le_card_center_of_scalar' {s p m lam : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hD : ∀ d : D, d ^ s = 1) (ψ : A →* MulAut D)
    {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hα : ∀ a, (α ^ m) a = a ^ lam) (hord : orderOf (lam : ZMod p) = p - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F)
    (hnt : ∃ a : A, ∃ z ∈ center D, ψ a z ≠ z) : s ^ ((p - 1) * m) ≤ Nat.card (center D) := by
  let ρ : MulAut D →* MulAut (center D) := MulAut.characteristic (center D)
  let _ : MulDistribMulAction A (center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  obtain ⟨a, z, hz, haz⟩ := hnt
  refine pow_two_mul_le_card_of_scalar' hsp hA (fun z => Subtype.ext (hD z))
    ⟨a, ⟨z, hz⟩, fun h => haz (congrArg Subtype.val h)⟩ (β := ρ τ) (fun a v => ?_) hα hord hlen
  change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
  rw [← map_mul, ← map_mul, hατ]

open scoped IsMulCommutative in
theorem pow_two_mul_le_card_quotient_center_of_scalar' {s p m lam : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (ψ : A →* MulAut D) (hψ : ∃ a, ψ a ≠ 1) {α : MulAut A}
    {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ) (hα : ∀ a, (α ^ m) a = a ^ lam)
    (hord : orderOf (lam : ZMod p) = p - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F)
    (hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z) :
    s ^ ((p - 1) * m) ≤ Nat.card (D ⧸ center D) := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hcomm : IsMulCommutative (D ⧸ center D) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
  let ρ : MulAut D →* MulAut (D ⧸ center D) := quotientCenterAut
  let _ : MulDistribMulAction A (D ⧸ center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  have hV : ∀ v : D ⧸ center D, v ^ s = 1 := fun v => by
    induction v using QuotientGroup.induction_on with
    | H d => rw [← QuotientGroup.mk_pow, hD d]; rfl
  have hnt : ∃ (a : A) (v : D ⧸ center D), a • v ≠ v := by
    obtain ⟨a, ha⟩ := hψ
    obtain ⟨d, hd⟩ : ∃ d : D, ψ a d ≠ d := by
      by_contra h
      push Not at h
      exact ha (MulEquiv.ext h)
    refine ⟨a, d, fun h => hd (apply_eq_of_mk_apply_eq ((Nat.coprime_primes hp hs).mpr
      hsp.symm) hD ?_ (hZ a) h)⟩
    rw [← map_pow, hA a, map_one]
  refine pow_two_mul_le_card_of_scalar' hsp hA hV hnt (β := ρ τ) (fun a v => ?_) hα hord hlen
  change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
  rw [← map_mul, ← map_mul, hατ]

theorem exists_isMulCommutative_pow_four_le_card_of_scalar' {s p m lam : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hpm : 5 ≤ (p - 1) * m)
    (hD : ∀ d : D, d ^ s = 1) (hc : commutator D ≤ center D) (ψ : A →* MulAut D)
    (hψ : ∃ a, ψ a ≠ 1) {α : MulAut A} {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hα : ∀ a, (α ^ m) a = a ^ lam) (hord : orderOf (lam : ZMod p) = p - 1)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have hs : s.Prime := Fact.out
  by_cases hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z
  · exact exists_isMulCommutative_pow_four_le_card hs hD hc
      ((Nat.pow_le_pow_right hs.pos hpm).trans (pow_two_mul_le_card_quotient_center_of_scalar'
        hsp hA hD hc ψ hψ hατ hα hord hlen hZ))
  · push Not at hZ
    exact ⟨center D, inferInstance, (Nat.pow_le_pow_right hs.pos (by omega)).trans
      (pow_two_mul_le_card_center_of_scalar' hsp hA hD ψ hατ hα hord hlen hZ)⟩

end Abstract

theorem stmtOddCoreRankOrbit {Y : Type} [Group Y] [Finite Y] {s p m : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hp : p.Prime) (hpm : 5 ≤ (p - 1) * m) (hsp : s ≠ p) (Sg X : Subgroup Y)
    (t : Y) (lam : ℕ) (hSg : IsPGroup s Sg) (hXS : X ≤ Subgroup.normalizer (Sg : Set Y))
    (hX : IsElemAbelian p X) (hXc : Nat.card X = p ^ 2)
    (htS : t ∈ Subgroup.normalizer (Sg : Set Y)) (htX : t ∈ Subgroup.normalizer (X : Set Y))
    (hord : orderOf (lam : ZMod p) = p - 1)
    (hscal : ∀ x ∈ X, t ^ m * x * (t ^ m)⁻¹ = x ^ lam)
    (horb : ∀ k, 0 < k → k < m → ∀ Y₀ : Subgroup Y, Y₀ ≤ X → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set Y))
    (hnc : ¬ X ≤ Subgroup.centralizer (Sg : Set Y)) : 4 ≤ Open.pRank s Sg := by
  have := Fact.mk hs
  have := Fact.mk hp
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnc fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let _ : CommGroup X := @IsMulCommutative.instCommGroup _ _ hX.1
  let ψ : X →* MulAut D := φ.comp (Subgroup.inclusion hXS)
  let α : MulAut X := X.normalizerMonoidHom ⟨t, htX⟩
  have hατ : ∀ x : X, φ ⟨t, htS⟩ * ψ x = ψ (α x) * φ ⟨t, htS⟩ := fun x => by
    change φ ⟨t, htS⟩ * φ (Subgroup.inclusion hXS x) =
      φ (Subgroup.inclusion hXS (α x)) * φ ⟨t, htS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * (x : Y) = t * x * t⁻¹ * t
    group
  have hψ : ∃ x : X, ψ x ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hxX, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hnc
    apply hx
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨x, hXS hxX⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) (hall ⟨x, hxX⟩)
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ p = 1 := by
      have hn : (⟨x, hXS hxX⟩ : Subgroup.normalizer (Sg : Set Y)) ^ p = 1 :=
        Subtype.ext (hX.2 x hxX)
      change (Sg.normalizerMonoidHom ⟨x, hXS hxX⟩) ^ p = 1
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
  have hαm : ∀ x : X, (α ^ m) x = x ^ lam := fun x =>
    Subtype.ext (by
      rw [coe_normalizerMonoidHom_pow_apply htX, hscal x x.2]
      rfl)
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_pow_four_le_card_of_scalar' hsp
    (fun x => Subtype.ext (hX.2 x x.2)) hpm hD hc ψ hψ hατ hαm hord
    (fun k hk0 hkm F hF => map_normalizerMonoidHom_pow_ne htX hXc horb hk0 hkm hF)
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  rw [hn] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hn (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem eq_one_of_mem_twoCore (h : AGLPair p M H R) {X : Subgroup G} (hX : IsElemAbelian p X)
    {x : G} (hx : x ∈ X) (hxQ : x ∈ pCoreOf 2 M) : x = 1 := by
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨x, hxQ⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes h.prime Nat.prime_two).mpr h.ne_two)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one (hX.2 x hx)) (orderOf_dvd_of_pow_eq_one hk'))

theorem eq_of_mk_eq_of_isElemAbelian (h : AGLPair p M H R) {X : Subgroup G}
    (hX : IsElemAbelian p X) {x y : ↥M} (hx : (x : G) ∈ X) (hy : (y : G) ∈ X)
    (hxy : QuotientGroup.mk' (CFSG.pCore 2 ↥M) x = QuotientGroup.mk' (CFSG.pCore 2 ↥M) y) :
    x = y := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 := h.eq_one_of_mem_twoCore hX (X.mul_mem (X.inv_mem hx) hy)
    (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  exact inv_mul_eq_one.mp (Subtype.ext h2)

omit [Finite G] in
theorem isElemAbelian_barM_of_isElemAbelian {X : Subgroup G} (hX : IsElemAbelian p X) :
    IsElemAbelian p (barM M X) :=
  CFSG.AGLEmbedding.isElemAbelian_barM_of_isElemAbelian hX

theorem card_barM_of_isElemAbelian (h : AGLPair p M H R) {X : Subgroup G} (hXM : X ≤ M)
    (hX : IsElemAbelian p X) (hcard : Nat.card X = p ^ 2) : Nat.card (barM M X) = p ^ 2 := by
  let f : X → barM M X := fun x =>
    ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hXM x.2⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (congrArg (fun z : ↥M => (z : G)) (h.eq_of_mk_eq_of_isElemAbelian hX x.2 y.2
      (congrArg Subtype.val hxy)))
  refine le_antisymm ?_ (hcard ▸ Nat.card_le_card_of_injective f hf)
  rw [← hcard, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)

theorem pow_notMem_normalizer_barM_of_isElemAbelian (h : AGLPair p M H R) {X : Subgroup G}
    (hX : IsElemAbelian p X) (hXM : X ≤ M) {t : G} (htM : t ∈ M)
    (htX : t ∈ Subgroup.normalizer (X : Set G)) {m : ℕ}
    (horb : ∀ k, 0 < k → k < m → ∀ Y₀ : Subgroup G, Y₀ ≤ X → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set G))
    {k : ℕ} (hk0 : 0 < k) (hkm : k < m) {Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hY₀ : Y₀ ≤ barM M X) (hcard : Nat.card Y₀ = p) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ k ∉ Subgroup.normalizer (Y₀ : Set _) := by
  intro hgY₀
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have htk : mk ⟨t, htM⟩ ^ k = mk ⟨t ^ k, M.pow_mem htM k⟩ := by
    rw [← map_pow]
    rfl
  rw [htk] at hgY₀
  set Y₁ : Subgroup G := X ⊓ (Y₀.comap mk).map M.subtype with hY₁
  have hgY₁ : t ^ k ∈ Subgroup.normalizer (Y₁ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.pow_mem _ htX k,
      Subgroup.le_normalizer_map M.subtype
        (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap mk hgY₀))⟩
  have hmem : ∀ (x : G) (hx : x ∈ X), x ∈ Y₁ ↔ mk ⟨x, hXM hx⟩ ∈ Y₀ := by
    intro x hx
    refine ⟨fun h => ?_, fun h => ⟨hx, ⟨x, hXM hx⟩, h, rfl⟩⟩
    obtain ⟨m, hm, hmx⟩ := h.2
    have : m = ⟨x, hXM hx⟩ := Subtype.ext hmx
    rw [← this]
    exact hm
  have hcard₁ : Nat.card Y₁ = p := by
    rw [← hcard]
    refine Nat.card_eq_of_bijective
      (fun y => ⟨mk ⟨y, hXM y.2.1⟩, (hmem y y.2.1).mp y.2⟩) ⟨fun y y' hyy' => ?_, ?_⟩
    · have h1 : mk ⟨(y : G), hXM y.2.1⟩ = mk ⟨(y' : G), hXM y'.2.1⟩ := congrArg Subtype.val hyy'
      exact Subtype.ext (congrArg (fun z : ↥M => (z : G))
        (h.eq_of_mk_eq_of_isElemAbelian hX y.2.1 y'.2.1 h1))
    · rintro ⟨_, hy⟩
      obtain ⟨z, hz, rfl⟩ := hY₀ hy
      have hzX : (z : G) ∈ X := Subgroup.mem_subgroupOf.mp hz
      exact ⟨⟨z, (hmem z hzX).mpr hy⟩, rfl⟩
  exact horb k hk0 hkm Y₁ inf_le_left hcard₁ hgY₁

end AGLPair

namespace D2AltData

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem false_of_oddCore_not_centralized (h : D2AltData p M H R X) (hD1 : D1For G)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsp : s ≠ p)
    (hns : ¬ barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    False := by
  have hp : p.Prime := Fact.out
  have hp5 := h.five_le
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨t, g, htK, htX, hord, -, hscal, hline⟩ := h.scalar_no_fixed_line
  have htM : t ∈ M := htK.2
  have hXM : X ≤ M := h.eq_R.le.trans h.pair.le_M
  have hscal' : ∀ x ∈ X, t ^ 2 * x * (t ^ 2)⁻¹ = x ^ g := fun x hx => by
    rw [← hscal x hx, pow_two]
    group
  have horb : ∀ k, 0 < k → k < 2 → ∀ Y₀ : Subgroup G, Y₀ ≤ X → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set G) := by
    intro k hk0 hk2 Y₀ hY₀ hcard
    obtain rfl : k = 1 := by omega
    rw [pow_one]
    exact hline Y₀ hY₀ hcard
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : 4 ≤ Open.pRank s Sg :=
    stmtOddCoreRankOrbit (m := 2) hs hs2 hp (by omega) hsp Sg (barM M X) (mk ⟨t, htM⟩) g
      CFSG.pCore_isPGroup (le_top.trans hSgN)
      (AGLPair.isElemAbelian_barM_of_isElemAbelian h.elem)
      (h.pair.card_barM_of_isElemAbelian hXM h.elem h.card)
      (hSgN (Subgroup.mem_top _)) (mem_normalizer_barM htM htX) hord
      (barM_conj_pow_eq_pow htM hscal')
      (fun k hk0 hkm _ hY₀ hcard =>
        h.pair.pow_notMem_normalizer_barM_of_isElemAbelian h.elem hXM htM htX horb hk0 hkm hY₀
          hcard)
      hns
  have hSgK : Sg ≤ barM M (H ⊓ M) :=
    h.pair.le_barM_inf_of_le_centralizer
      ((pCore_le_pPrimeCore_two hs hs2).trans (h.pair.oddCore_le_centralizer h84 hD2))
  have h4 : 4 ≤ Open.pRank s (H ⊓ M) :=
    hrank.trans ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono s hs hSgK).trans
      (pRank_barM_le hs hs2 M (H ⊓ M) inf_le_right))
  exact h.pair.false_of_four_le_pRank hD1 hs hs2 h4

theorem le_centralizer_oddCore (h : D2AltData p M H R X) (hD1 : D1For G) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) :=
  fun _ hs hs2 hsp => by_contra fun hns =>
    h.false_of_oddCore_not_centralized hD1 h84 hD2 hs hs2 hsp hns

end D2AltData

end CFSG.AGLEmbeddingD2
