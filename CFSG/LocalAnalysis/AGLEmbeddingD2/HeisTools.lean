module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ComponentsK
public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePiecesAux
import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces
import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

section Reduced

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

namespace D2AlmostSimple

theorem isSimpleGroup_K (h : D2AlmostSimple p X R A X₀ K) : IsSimpleGroup K := by
  have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := h.component.2.2.2
  exact ((QuotientGroup.quotientMulEquivOfEq h.center_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem exists_noncomm_K (h : D2AlmostSimple p X R A X₀ K) : ∃ a b : K, a * b ≠ b * a := by
  have hcen : Subgroup.center K = ⊥ := h.center_eq_bot
  let e' : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
      h.component.2.2
  refine ⟨e'.symm a, e'.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e' hba

theorem six_lt_card_K (h : D2AlmostSimple p X R A X₀ K) (hp5 : 5 ≤ p) : 6 < Nat.card K := by
  obtain ⟨m, hm⟩ := h.dvd
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    have : Fact (Nat.card K).Prime := ⟨hm ▸ h.prime⟩
    have : IsCyclic K := isCyclic_of_prime_card rfl
    obtain ⟨a, b, hab⟩ := h.exists_noncomm_K
    exact hab (mul_comm' a b)
  rw [hm]
  nlinarith [Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩]

end D2AlmostSimple

end Reduced

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.simpleSection_of_simple (h : D2Escape p P M A H R)
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hK6 : 6 < Nat.card K) {X : Subgroup G} (hXR : X ≤ R)
    (hXK : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ≤ K) :
    D2SimpleSection p H X := by
  set O := primeComplementCore (G := H) p with hO
  set mk := QuotientGroup.mk' O with hmk
  set H₁ : Subgroup G := (K.comap mk).map H.subtype with hH₁
  have hH₁H : H₁ ≤ H := Subgroup.map_subtype_le _
  have hmemK : ∀ g : H₁, mk ⟨g.1, hH₁H g.2⟩ ∈ K := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    exact hk
  let φ : ↥H₁ →* ↥K :=
    { toFun := fun g => ⟨mk ⟨g.1, hH₁H g.2⟩, hmemK g⟩
      map_one' := Subtype.ext (map_one mk)
      map_mul' := fun a b => Subtype.ext (map_mul mk ⟨a.1, hH₁H a.2⟩ ⟨b.1, hH₁H b.2⟩) }
  have := hK.isSimpleGroup_K
  refine ⟨K, inferInstance, inferInstance, H₁, φ, hH₁H, fun a ha => ?_, fun κ => ?_,
    inferInstance, hK6, hK.exists_noncomm_K, ?_⟩
  · have haH : a ∈ H := h.le_H (hXR ha)
    exact ⟨⟨a, haH⟩, hXK ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, rfl⟩
  · obtain ⟨hh, hhκ⟩ := QuotientGroup.mk'_surjective O κ.1
    have hhK : hh ∈ K.comap mk := by
      show mk hh ∈ K
      rw [hmk, hhκ]
      exact κ.2
    exact ⟨⟨(hh : G), ⟨hh, hhK, rfl⟩⟩, Subtype.ext hhκ⟩
  · have hle : (φ.ker).map H₁.subtype ≤ GLBPrimeCore p H := by
      rintro _ ⟨g, hg, rfl⟩
      have h1 : mk ⟨g.1, hH₁H g.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      rw [glbPrimeCore_eq_primeComplementCoreOf p H]
      exact ⟨⟨g.1, hH₁H g.2⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    rw [← Subgroup.card_map_of_injective H₁.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) (glbPrimeCore_coprime p H)

theorem D2Escape.barM_le_centralizer_of_le_inf_of_simple (h : D2Escape p P M A H R)
    (hpair : AGLPair p M H R)
    (hperf : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H)
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {X : Subgroup G} (hXR : X ≤ R)
    (hXK : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ≤ K)
    (hD1 : D1For G) (hp5 : 5 ≤ p) (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M) :
    barM M X ≤ Subgroup.centralizer (barM M L : Set _) :=
  hpair.barM_le_centralizer_of_simpleSection hXR hperf
    (h.simpleSection_of_simple hK (hK.six_lt_card_K hp5) hXR hXK) hD1 hp5 hα hSch hL hLK

end Escape

section Heisenberg

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem exists_fixedPiece_ne_bot_of_central [Finite A] [Finite V] {p : ℕ} [Fact p.Prime]
    (hA : ∀ a : A, a ^ p = 1) (hV : ¬ p ∣ Nat.card V) {ζ : A} (hζ : ∃ v : V, ζ • v ≠ v) :
    ∃ F : Subgroup A, F.index = p ∧ ζ ∉ F ∧ (fixedPiece F : Subgroup V) ≠ ⊥ := by
  by_contra hno
  push Not at hno
  have hle : ∀ F : Subgroup A, F.index = 1 ∨ F.index = p →
      (fixedBy F : Subgroup V) ≤ fixedBy (Subgroup.zpowers ζ) := by
    intro F hF
    by_cases hζF : ζ ∈ F
    · exact fun v hv a ha => hv a (Subgroup.zpowers_le.mpr hζF ha)
    · rcases hF with hF | hF
      · exact absurd (Subgroup.index_eq_one.mp hF ▸ Subgroup.mem_top ζ) hζF
      · exact (fixedPiece_eq_bot_iff.mp (hno F hF hζF)).trans (fixedBy_top_le _)
  have htop := CFSG.PreuniquenessRankFour.Helpers.coprime_group_generated_by_prime_fixedSubgroups
    (acting := A) (source := V) p hV hA
  have hsup : sSup {fixedGroup : Subgroup V | ∃ kernel : Subgroup A,
      (kernel.index = 1 ∨ kernel.index = p) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} ≤
      fixedBy (Subgroup.zpowers ζ) :=
    sSup_le fun Y ⟨F, hF, hY⟩ =>
      (show Y ≤ fixedBy F from fun y hy a ha => hY a ha y hy).trans (hle F hF)
  obtain ⟨v, hv⟩ := hζ
  exact hv (hsup (htop ▸ Subgroup.mem_top v) ζ (Subgroup.mem_zpowers ζ))

theorem exists_injective_fixedPiece_ne_bot_of_central [Finite A] [Finite V] {p m : ℕ}
    [Fact p.Prime] (hA : ∀ a : A, a ^ p = 1) (hV : ¬ p ∣ Nat.card V) {ζ : A}
    (hζ : ∃ v : V, ζ • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p → ζ ∉ F →
      F.map (α ^ k).toMonoidHom ≠ F) :
    ∃ F : Fin m → Subgroup A, Function.Injective F ∧ (∀ j, (F j).index = p) ∧
      ∀ j, (fixedPiece (F j) : Subgroup V) ≠ ⊥ := by
  obtain ⟨F₀, hF₀, hζF₀, hne⟩ := exists_fixedPiece_ne_bot_of_central hA hV hζ
  have hmap : ∀ i j : ℕ, i < j → j < m →
      F₀.map (α ^ i).toMonoidHom ≠ F₀.map (α ^ j).toMonoidHom := by
    intro i j hij hjm h
    have hj : α ^ j = α ^ i * α ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hj, map_mul_toMonoidHom] at h
    exact hlen (j - i) (by omega) (by omega) F₀ hF₀ hζF₀
      (Subgroup.map_injective (α ^ i).injective h).symm
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

theorem pow_le_card_of_central_orbit [Finite A] [Finite V] {s p m : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : IsPGroup s V) {ζ : A}
    (hζ : ∃ v : V, ζ • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p → ζ ∉ F →
      F.map (α ^ k).toMonoidHom ≠ F) :
    s ^ m ≤ Nat.card V := by
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
  obtain ⟨F, hinj, hF, hne⟩ :=
    exists_injective_fixedPiece_ne_bot_of_central hA hpV hζ hαβ hlen
  simpa using pow_card_le_card_of_fixedPiece_ne_bot hp hV hcop hinj hF hne

theorem pow_le_card_of_heisenberg [Finite A] [Finite V] {s p : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : IsPGroup s V) {ζ : A}
    (hζ : ∃ v : V, ζ • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v)
    (hlen : ∀ k : ℕ, 0 < k → k < p → ∀ F : Subgroup A, F.index = p → ζ ∉ F →
      F.map (α ^ k).toMonoidHom ≠ F) :
    s ^ p ≤ Nat.card V :=
  pow_le_card_of_central_orbit hsp hA hV hζ hαβ hlen

end Heisenberg

section Abstract

open Subgroup

variable {A D : Type*} [CommGroup A] [Finite A] [Group D] [Finite D]

open scoped IsMulCommutative in
theorem pow_le_card_center_of_heisenberg {s p : ℕ} [Fact s.Prime] [Fact p.Prime] (hsp : s ≠ p)
    (hA : ∀ a : A, a ^ p = 1) (hD : ∀ d : D, d ^ s = 1) (ψ : A →* MulAut D) {α : MulAut A}
    {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ) {ζ : A}
    (hlen : ∀ k : ℕ, 0 < k → k < p → ∀ F : Subgroup A, F.index = p → ζ ∉ F →
      F.map (α ^ k).toMonoidHom ≠ F)
    (hnt : ∃ z ∈ center D, ψ ζ z ≠ z) : s ^ p ≤ Nat.card (center D) := by
  let ρ : MulAut D →* MulAut (center D) := MulAut.characteristic (center D)
  let _ : MulDistribMulAction A (center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  obtain ⟨z, hz, hzζ⟩ := hnt
  refine pow_le_card_of_heisenberg hsp hA (fun z => ⟨1, by rw [pow_one]; exact Subtype.ext (hD z)⟩)
    (ζ := ζ) ⟨⟨z, hz⟩, fun h => hzζ (congrArg Subtype.val h)⟩ (β := ρ τ) (fun a v => ?_) hlen
  change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
  rw [← map_mul, ← map_mul, hατ]

open scoped IsMulCommutative in
theorem pow_le_card_quotient_center_of_heisenberg {s p : ℕ} [Fact s.Prime] [Fact p.Prime]
    (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (ψ : A →* MulAut D) {ζ : A} (hψ : ψ ζ ≠ 1) {α : MulAut A}
    {τ : MulAut D} (hατ : ∀ a, τ * ψ a = ψ (α a) * τ)
    (hlen : ∀ k : ℕ, 0 < k → k < p → ∀ F : Subgroup A, F.index = p → ζ ∉ F →
      F.map (α ^ k).toMonoidHom ≠ F)
    (hZ : ∀ z ∈ center D, ψ ζ z = z) : s ^ p ≤ Nat.card (D ⧸ center D) := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hcomm : IsMulCommutative (D ⧸ center D) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
  let ρ : MulAut D →* MulAut (D ⧸ center D) := quotientCenterAut
  let _ : MulDistribMulAction A (D ⧸ center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
  have hV : ∀ v : D ⧸ center D, v ^ s = 1 := fun v => by
    induction v using QuotientGroup.induction_on with
    | H d => rw [← QuotientGroup.mk_pow, hD d]; rfl
  have hnt : ∃ v : D ⧸ center D, ζ • v ≠ v := by
    obtain ⟨d, hd⟩ : ∃ d : D, ψ ζ d ≠ d := by
      by_contra h
      push Not at h
      exact hψ (MulEquiv.ext h)
    refine ⟨d, fun h => hd (apply_eq_of_mk_apply_eq ((Nat.coprime_primes hp hs).mpr
      hsp.symm) hD ?_ hZ h)⟩
    rw [← map_pow, hA ζ, map_one]
  refine pow_le_card_of_heisenberg hsp hA (fun v => ⟨1, by rw [pow_one]; exact hV v⟩) hnt
    (β := ρ τ) (fun a v => ?_) hlen
  change (ρ τ * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ τ) v
  rw [← map_mul, ← map_mul, hατ]

end Abstract

end CFSG.AGLEmbeddingD2
