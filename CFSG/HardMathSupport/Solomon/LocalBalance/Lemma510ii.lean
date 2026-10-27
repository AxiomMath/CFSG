module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

namespace Lemma510iiNs

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open Lemma513Ns

theorem mulAut_eq_one_of_central {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    (α : MulAut Y) (h : ∀ x : Y, x⁻¹ * α x ∈ Subgroup.center Y) : α = 1 := by
  let c : Y →* Y :=
    { toFun := fun x => x⁻¹ * α x
      map_one' := by simp
      map_mul' := fun x y => by
        have hx := Subgroup.mem_center_iff.1 (h x) y⁻¹
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by simp [mul_assoc]
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hx]
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by simp [mul_assoc] }
  have hc : ∀ x, c x = x⁻¹ * α x := fun x => rfl
  have hker : commutator Y ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, hc, hc, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.1 (h a) _).symm
  have hall : ∀ x, c x = 1 := fun x => by
    have : x ∈ c.ker := hker (hperf ▸ Subgroup.mem_top x)
    exact this
  ext x
  have := hall x
  rw [hc] at this
  show α x = x
  exact (inv_mul_eq_one.1 this).symm

theorem isPGroup_center_of_core_bot {Y : Type*} [Group Y] [Finite Y]
    (h : GLAPPrimeCore 3 Y = ⊥) : IsPGroup 3 (Subgroup.center Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card (Subgroup.center Y)).primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := Subgroup.center Y)).ne' ?_
  intro r hr hrd
  by_contra hr3
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) r hrd
  set S : Subgroup Y := Subgroup.zpowers (z : Y) with hS
  have hSc : S ≤ Subgroup.center Y := by
    rw [hS, Subgroup.zpowers_le]; exact z.2
  have hSn : S.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hSc hn) g
    have e : g * n * g⁻¹ = n := by rw [this]; group
    rw [e]; exact hn⟩
  have hcard : Nat.card S = r := by
    rw [hS, Nat.card_zpowers]
    have : orderOf (z : Y) = orderOf z := Subgroup.orderOf_coe z
    rw [this, hz]
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    rw [hcard]; exact (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3)
  have hle : S ≤ GLAPPrimeCore 3 Y := le_sSup ⟨hSn, hcop⟩
  rw [h] at hle
  have : Nat.card S = 1 := by
    have := le_bot_iff.1 hle
    rw [this]; simp
  rw [hcard] at this
  exact hr.ne_one this


section Bar

variable {G : Type} [Group G] [Finite G]

theorem pCore_barOf_eq_center {X L : Subgroup G} (hL : GLAPComponent 3 X L) :
    CFSG.pCore 3 (barOf 3 L) = Subgroup.center (barOf 3 L) := by
  have hq := isQuasisimple_quotient_of_glaPComponent hL
  apply le_antisymm (Lemma510Ns.pCore_le_center Nat.prime_three hq)
  have hZ := isPGroup_center_of_core_bot
    (glaPPrimeCore_quotient_eq_bot (p := 3) Nat.prime_three (Z := ↥L))
  exact le_sSup ⟨inferInstance, hZ⟩

theorem isPGroup_center_barOf (L : Subgroup G) : IsPGroup 3 (Subgroup.center (barOf 3 L)) :=
  isPGroup_center_of_core_bot (glaPPrimeCore_quotient_eq_bot (p := 3) Nat.prime_three (Z := ↥L))

theorem isLThreeFour_barOf_center {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (h : IsLThreeFour (↥L ⧸ oPrimeP 3 ↥L)) :
    IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) := by
  set N := CFSG.pCore 3 (barOf 3 L) with hN
  let φ : ↥L →* barOf 3 L ⧸ N :=
    (QuotientGroup.mk' N).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective N).comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = oPrimeP 3 ↥L := by
    ext x
    simp [φ, oPrimeP, hN, QuotientGroup.eq_one_iff]
  let e : (↥L ⧸ oPrimeP 3 ↥L) ≃* (barOf 3 L ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have h1 := UniquenessMaximal.IsLThreeFour.of_mulEquiv e h
  exact UniquenessMaximal.IsLThreeFour.of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (pCore_barOf_eq_center hL)) h1

end Bar


section Cover

variable {G : Type} [Group G] [Finite G]

theorem barAut_eq_one_of_mem_centralizerQuot {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    {g : G} (hg : g ∈ centralizerQuot L (oPrimePOf 3 L)) : barAut 3 L ⟨g, hg.1⟩ = 1 := by
  have hq := isQuasisimple_quotient_of_glaPComponent hL
  refine mulAut_eq_one_of_central hq.1 _ fun z => ?_
  induction z using QuotientGroup.induction_on with | H x => ?_
  have h1 := hg.2.2 (x : G)⁻¹ (L.inv_mem x.2)
  obtain ⟨w, hw, hwe⟩ := h1
  rw [barAut_mk, ← pCore_barOf_eq_center hL]
  have e : w = x⁻¹ * L.normalizerMonoidHom ⟨g, hg.1⟩ x := by
    apply Subtype.ext
    have h' : (w : G) = (x : G)⁻¹ * g * (x : G)⁻¹⁻¹ * g⁻¹ := hwe
    show (w : G) = (x : G)⁻¹ * (g * x * g⁻¹)
    rw [h']
    group
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← e]
  exact hw

omit [Finite G] in
theorem GLAPPrimeCoreOf_le_oPrimePOf (L : Subgroup G) : GLAPPrimeCoreOf 3 L ≤ oPrimePOf 3 L := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) y ∈ CFSG.pCore 3 _
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  rw [h1]
  exact one_mem _

theorem mem_centralizerQuot_oPrimeP_iff {X L : Subgroup G} (hL : GLAPComponent 3 X L) {g : G}
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ centralizerQuot L (oPrimePOf 3 L) ↔ g ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
  constructor
  · intro hg
    exact (mem_centralizerQuot_iff_barAut' 3 ⟨g, hgN⟩).2 (barAut_eq_one_of_mem_centralizerQuot hL hg)
  · intro hg
    have hb1 := (mem_centralizerQuot_iff_barAut' 3 ⟨g, hgN⟩).1 hg
    have key : ∀ (g' : G) (hg' : g' ∈ Subgroup.normalizer (L : Set G)),
        barAut 3 L ⟨g', hg'⟩ = 1 → ∀ y ∈ oPrimePOf 3 L, g' * y * g'⁻¹ ∈ oPrimePOf 3 L := by
      intro g' hg' h1 y hy
      obtain ⟨w, hw, rfl⟩ := hy
      refine ⟨L.normalizerMonoidHom ⟨g', hg'⟩ w, ?_, rfl⟩
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (L.normalizerMonoidHom ⟨g', hg'⟩ w) ∈
        CFSG.pCore 3 _
      have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (L.normalizerMonoidHom ⟨g', hg'⟩ w) =
          barAut 3 L ⟨g', hg'⟩ (QuotientGroup.mk w) := by
        rw [barAut_mk]; rfl
      rw [this, h1]
      exact hw
    refine ⟨hgN, ?_, fun x hx => GLAPPrimeCoreOf_le_oPrimePOf L (hg.2.2 x hx)⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hgN hb1 y, fun hy => ?_⟩
    have hgi : barAut 3 L ⟨g⁻¹, inv_mem hgN⟩ = 1 := by
      have : (⟨g⁻¹, inv_mem hgN⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨g, hgN⟩)⁻¹ := rfl
      rw [this, map_inv, hb1, inv_one]
    have := key g⁻¹ (inv_mem hgN) hgi _ hy
    simpa [mul_assoc] using this

theorem card_autBar_eq_of_relIndex {X L : Subgroup G} (hL : GLAPComponent 3 X L) {B : Subgroup G}
    (h : (centralizerQuot L (oPrimePOf 3 L)).relIndex (B ⊓ Subgroup.normalizer (L : Set G)) = 9) :
    Nat.card (autBar 3 B L) = 9 := by
  set K : Subgroup G := B ⊓ Subgroup.normalizer (L : Set G) with hK
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  let ρ : ↥K →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hKN)
  have hrange : autBar 3 B L = ρ.range := by
    unfold autBar
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ρ.ker = (centralizerQuot L (oPrimePOf 3 L)).subgroupOf K := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : barAut 3 L ⟨g.1, hKN g.2⟩ = 1 := h1
      exact (mem_centralizerQuot_oPrimeP_iff hL (hKN g.2)).2
        ((mem_centralizerQuot_iff_barAut' 3 ⟨g.1, hKN g.2⟩).2 h2)
    · intro h1
      exact barAut_eq_one_of_mem_centralizerQuot hL h1
  rw [hrange, ← Subgroup.index_ker, hker]
  exact h

end Cover


section Clauses

@[expose] def InputSL34Sylow : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → IsPGroup 3 (Subgroup.center Y) →
    Subgroup.center Y ≠ ⊥ → IsLThreeFour (Y ⧸ Subgroup.center Y) →
    ∀ P : Subgroup Y, IsPGroup 3 P → Subgroup.center Y ≤ P →
      Nat.card P = 9 * Nat.card (Subgroup.center Y) →
      (∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) ∧ ∀ x ∈ P, x ^ 3 = 1

variable {G : Type} [Group G] [Finite G]

theorem autBar_le_innerAut {X L B : Subgroup G} (hL : GLAPComponent 3 X L)
    (h : ∀ b ∈ B ⊓ Subgroup.normalizer (L : Set G),
      ∃ l ∈ L, l⁻¹ * b ∈ centralizerQuot L (oPrimePOf 3 L)) :
    autBar 3 B L ≤ innerAut (barOf 3 L) := by
  rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
  obtain ⟨l, hl, hc⟩ := h b (Subgroup.mem_subgroupOf.1 hb)
  have h1 := barAut_eq_one_of_mem_centralizerQuot hL hc
  have e : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨l, Subgroup.le_normalizer hl⟩ * ⟨l⁻¹ * b, hc.1⟩ := Subtype.ext (by simp)
  rw [e, map_mul, h1, mul_one, ← rho_of_mem (Subgroup.le_normalizer hl), rho_of_mem_L hl]
  exact ⟨_, rfl⟩

omit [Finite G] in
theorem card_comap_conj {Y : Type*} [Group Y] [Finite Y] (Bt : Subgroup (MulAut Y))
    (hBt : Bt ≤ innerAut Y) :
    Nat.card (Bt.comap (MulAut.conj : Y →* MulAut Y)) =
      Nat.card (Subgroup.center Y) * Nat.card Bt := by
  set P0 := Bt.comap (MulAut.conj : Y →* MulAut Y) with hP0
  let f : ↥P0 →* MulAut Y := (MulAut.conj : Y →* MulAut Y).comp P0.subtype
  have hr : f.range = Bt := by
    ext β
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact hy
    · intro hβ
      obtain ⟨y, hy⟩ := hBt hβ
      exact ⟨⟨y, by rw [hP0, Subgroup.mem_comap, hy]; exact hβ⟩, hy⟩
  have hk : Nat.card f.ker = Nat.card (Subgroup.center Y) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, (conj_eq_one_iff_mem_center x.1.1).1
          (MonoidHom.mem_ker.1 x.2 : MulAut.conj (x.1.1 : Y) = 1)⟩
        invFun := fun z => ⟨⟨z.1, by
          have hz : (MulAut.conj (z.1 : Y) : MulAut Y) = 1 := (conj_eq_one_iff_mem_center _).2 z.2
          show MulAut.conj z.1 ∈ Bt
          rw [hz]
          exact one_mem _⟩, by
          have hz : (MulAut.conj (z.1 : Y) : MulAut Y) = 1 := (conj_eq_one_iff_mem_center _).2 z.2
          exact MonoidHom.mem_ker.2 hz⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hk, hr] at h1
  rw [← h1, mul_comm]


theorem clauses_of_lemma31iii (hSyl : InputSL34Sylow) {X L B : Subgroup G}
    (hL : GLAPComponent 3 X L) (hBel : IsElemAbelian 3 B) (h3 : Lemma31iii 3 B L) :
    Nat.card ↥(autBar 3 B L ⊓ innerDiag (barOf 3 L)) = 9 ∧
    (∀ x : barOf 3 L, MulAut.conj x ∈ autBar 3 B L → x ^ 3 = 1) ∧
    ∀ (Ŵ : Type) [Group Ŵ] (π : Ŵ →* MulAut (barOf 3 L)) (ι : barOf 3 L →* Ŵ),
      IsThreeCover π ι → (∀ x, π x ∈ innerDiag (barOf 3 L)) →
      autBar 3 B L ⊓ innerDiag (barOf 3 L) ≤ π.range →
      ∃ x ∈ (autBar 3 B L ⊓ innerDiag (barOf 3 L)).comap π,
        ∃ y ∈ (autBar 3 B L ⊓ innerDiag (barOf 3 L)).comap π, x * y ≠ y * x := by
  obtain ⟨-, -, hL34, hrel, hinn⟩ := h3
  have hq := isQuasisimple_quotient_of_glaPComponent hL
  set Bt := autBar 3 B L with hBt
  have hBtInn : Bt ≤ innerAut (barOf 3 L) := autBar_le_innerAut hL hinn
  have hBt9 : Nat.card Bt = 9 := card_autBar_eq_of_relIndex hL hrel
  have hBel' : IsElemAbelian 3 (B ⊓ Subgroup.normalizer (L : Set G)) :=
    Lemma54Ns.isElemAbelian_of_le' hBel inf_le_left
  have hBtEl : IsElemAbelian 3 Bt := isElemAbelian_map (isElemAbelian_subgroupOf hBel') _
  have hinf : Bt ⊓ innerDiag (barOf 3 L) = Bt :=
    inf_eq_left.2 (hBtInn.trans (innerAut_le_innerDiag _))
  rw [hinf]
  set P0 : Subgroup (barOf 3 L) := Bt.comap (MulAut.conj : barOf 3 L →* MulAut (barOf 3 L)) with hP0
  have hZ3 := isPGroup_center_barOf L
  have hP : Subgroup.center (barOf 3 L) ≠ ⊥ →
      (∃ x ∈ P0, ∃ y ∈ P0, x * y ≠ y * x) ∧ ∀ x ∈ P0, x ^ 3 = 1 := by
    intro hZne
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card P0 = Nat.card (Subgroup.center (barOf 3 L)) * 9 := by
      rw [hP0, card_comap_conj Bt hBtInn, hBt9]
    refine hSyl (barOf 3 L) hq hZ3 hZne (isLThreeFour_barOf_center hL hL34) P0 ?_ ?_ ?_
    · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ3
      exact IsPGroup.of_card (n := k + 2) (by rw [hcard, hk]; ring)
    · intro z hz
      show MulAut.conj z ∈ Bt
      rw [(conj_eq_one_iff_mem_center z).2 hz]
      exact one_mem _
    · rw [hcard, mul_comm]
  refine ⟨hBt9, ?_, ?_⟩
  · intro x hx
    by_cases hZ : Subgroup.center (barOf 3 L) = ⊥
    · have h1 : (MulAut.conj x : MulAut (barOf 3 L)) ^ 3 = 1 := hBtEl.2 _ hx
      have h2 : x ^ 3 ∈ Subgroup.center (barOf 3 L) := by
        rw [← conj_eq_one_iff_mem_center, map_pow]
        exact h1
      rw [hZ] at h2
      exact Subgroup.mem_bot.1 h2
    · exact (hP hZ).2 x hx
  · intro Ŵ _ π ι hcov _ _
    have hZne : Subgroup.center (barOf 3 L) ≠ ⊥ := by
      intro hZ
      have hker : π.ker = ⊥ := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_bot]
        constructor
        · intro hx
          obtain ⟨l, rfl⟩ := hcov.inner x (by rw [hx]; exact one_mem _)
          have h1 : (MulAut.conj l : MulAut (barOf 3 L)) = 1 := by
            rw [← hcov.conj l]; exact hx
          have h2 := (conj_eq_one_iff_mem_center l).1 h1
          rw [hZ] at h2
          rw [Subgroup.mem_bot.1 h2, map_one]
        · rintro rfl
          exact map_one π
      have := hcov.card
      rw [hker, Subgroup.card_bot] at this
      exact absurd this (by norm_num)
    obtain ⟨⟨u, hu, v, hv, huv⟩, -⟩ := hP hZne
    have hmem : ∀ w ∈ P0, ι w ∈ Bt.comap π := by
      intro w hw
      rw [Subgroup.mem_comap, hcov.conj]
      exact hw
    refine ⟨ι u, hmem u hu, ι v, hmem v hv, fun h => huv ?_⟩
    apply hcov.inj
    rw [map_mul, map_mul]
    exact h

end Clauses

section BranchB

@[expose] def Input19_7_Seitz : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsPGroup 3 (Subgroup.center K) →
    (IsExtremalType K ∨ IsSLThreeEps K) →
    ∀ D H : Subgroup (MulAut K), IsEkIn 3 2 ⊤ D → innerAut K ≤ H →
      D ≤ Subgroup.normalizer (H : Set (MulAut K)) → localDeltaIn 3 H D ≠ ⊥ →
      (D ≤ innerDiag K ∧ ∀ α ∈ innerDiag K, (∀ d ∈ D, α * d = d * α) → α ∈ D) ∧
      (∀ x : K, (MulAut.conj x : MulAut K) ≠ 1 → (MulAut.conj x : MulAut K) ∈ D → x ^ 3 = 1) ∧
      ∀ (Ŵ : Type) [Group Ŵ] (π : Ŵ →* MulAut K) (ι : K →* Ŵ), IsThreeCover π ι →
        π.range = D ⊔ innerAut K → ∃ x ∈ D.comap π, ∃ y ∈ D.comap π, x * y ≠ y * x

theorem isThreeCover_restrict {Y : Type*} [Group Y] {Ŵ : Type*} [Group Ŵ] {π : Ŵ →* MulAut Y}
    {ι : Y →* Ŵ} (hc : IsThreeCover π ι) (S : Subgroup (MulAut Y)) (hS : innerAut Y ≤ S) :
    IsThreeCover (π.comp (S.comap π).subtype)
      (ι.codRestrict (S.comap π) (fun l => by
        show π (ι l) ∈ S
        rw [hc.conj]
        exact hS ⟨l, rfl⟩)) where
  inj := fun a b h => hc.inj (congrArg Subtype.val h)
  conj := fun l => hc.conj l
  inner := fun x hx => by
    obtain ⟨l, hl⟩ := hc.inner x.1 hx
    exact ⟨l, Subtype.ext hl⟩
  central := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 (hc.central (show x.1 ∈ π.ker from hx)) y.1
  card := by
    rw [← hc.card]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, by
          show π y.1 ∈ S
          rw [MonoidHom.mem_ker.1 y.2]
          exact one_mem _⟩, y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }

theorem range_restrict_comap {Y : Type*} [Group Y] {Ŵ : Type*} [Group Ŵ] (π : Ŵ →* MulAut Y)
    (S : Subgroup (MulAut Y)) (hS : S ≤ π.range) : (π.comp (S.comap π).subtype).range = S := by
  ext β
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hβ
    obtain ⟨x, hx⟩ := hS hβ
    exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact hβ⟩, hx⟩

end BranchB

section BranchBMain

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem pow_three_eq_one_of_mem_center {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hZ : IsPGroup 3 (Subgroup.center Y))
    (hty : IsExtremalType Y ∨ IsSLThreeEps Y) {x : Y} (hx : x ∈ Subgroup.center Y) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := card_center_le_three_of_type hq hty
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ
  have hd : Nat.card (Subgroup.center Y) ∣ 3 := by
    rw [hk]
    rcases k with _ | _ | k
    · simp
    · simp
    · exfalso
      have h1 : 3 ^ (k + 2) = 9 * 3 ^ k := by ring
      have h2 := Nat.one_le_pow k 3 (by norm_num)
      omega
  have h3 : orderOf (⟨x, hx⟩ : Subgroup.center Y) ∣ 3 :=
    (orderOf_dvd_natCard _).trans hd
  have h4 := orderOf_dvd_iff_pow_eq_one.1 h3
  exact congrArg Subtype.val h4

theorem clauses_of_branch_b (hSeitz : Input19_7_Seitz) (h191 : Lemma54Ns.Input19_1_2)
    {m : ℕ} (hS : GLStanding G m 3) {B : Subgroup G} (hBel : IsElemAbelian 3 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hcomp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L))
    {D : Subgroup G} (hD : IsEkIn 3 2 B D)
    (hnot : ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L) :
    Nat.card ↥(autBar 3 B L ⊓ innerDiag (barOf 3 L)) = 9 ∧
    (∀ x : barOf 3 L, MulAut.conj x ∈ autBar 3 B L → x ^ 3 = 1) ∧
    ∀ (Ŵ : Type) [Group Ŵ] (π : Ŵ →* MulAut (barOf 3 L)) (ι : barOf 3 L →* Ŵ),
      IsThreeCover π ι → (∀ x, π x ∈ innerDiag (barOf 3 L)) →
      autBar 3 B L ⊓ innerDiag (barOf 3 L) ≤ π.range →
      ∃ x ∈ (autBar 3 B L ⊓ innerDiag (barOf 3 L)).comap π,
        ∃ y ∈ (autBar 3 B L ⊓ innerDiag (barOf 3 L)).comap π, x * y ≠ y * x := by
  have := hS.simple
  obtain ⟨hDB, hDel, hDcard⟩ := hD
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set X : Subgroup G := GLADelta 3 D ⊓ C with hXdef
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hbD : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact elemAbelian_comm hBel (hDB hd) hb
  obtain ⟨hnorm, hmain⟩ :=
    h191 G hS.nonabelian hS.kProper 3 Nat.prime_three D hDel hDne b hbD hb1 (hBel.2 b hb)
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := hnorm L hcomp
  have hnot' : ¬ ⁅L, X⁆ ≤ GLAPPrimeCoreOf 3 C := by
    intro hle
    apply hnot
    have hLX : ⁅L, X⁆ ≤ L := Subgroup.commutator_le.2 fun ℓ hℓ x hx => by
      rw [commutatorElement_def]
      have h1 := (Subgroup.mem_normalizer_iff.1 (hXN hx) ℓ⁻¹).1 (L.inv_mem hℓ)
      have h2 := L.mul_mem hℓ h1
      simpa [mul_assoc] using h2
    intro y hy
    have h3 := gLAPPrimeCoreOf_inf_le Nat.prime_three C L ⟨hle hy, hLX hy⟩
    rwa [inf_eq_right.2 hcomp.1] at h3
  obtain ⟨hker, hDN, himg⟩ := hmain L hcomp hnot'
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hcomp
  set Dt : Subgroup (MulAut (barOf 3 L)) :=
    (D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hDt
  set Ht : Subgroup (MulAut (barOf 3 L)) :=
    ((X ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hHt
  have hDcard9 : Nat.card ↥Dt = 9 := by
    rw [hDt, Lemma54Ns.card_map_barAut_of_kerB_eq_bot hDN hker, hDcard]
    norm_num
  have hDtE : IsEkIn 3 2 ⊤ Dt :=
    ⟨le_top, isElemAbelian_map (isElemAbelian_subgroupOf hDel) _, by rw [hDcard9]; norm_num⟩
  have hinn : innerAut (barOf 3 L) ≤ Ht :=
    Lemma54Ns.innerAut_le_map (p := 3) (le_sup_right : L ≤ X ⊔ L)
  have hconjT : ∀ d ∈ D, ∀ t ∈ X ⊔ L, d * t * d⁻¹ ∈ X ⊔ L := by
    intro d hd t ht
    have hle : X ⊔ L ≤ (X ⊔ L).comap (MulAut.conj d).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun ℓ hℓ => ?_)
      · have hdx : d * x = x * d :=
          Subgroup.mem_centralizer_iff.1 (Lemma54Ns.gLADelta_le_centralizer hd hx.1) d rfl
        have e : d * x * d⁻¹ = x := by rw [hdx]; group
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
        exact Subgroup.mem_sup_left hx
      · have hdl : d * ℓ * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hDN hd) ℓ).1 hℓ
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_right hdl
    have := hle ht
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hconjH : ∀ d ∈ Dt, ∀ h ∈ Ht, d * h * d⁻¹ ∈ Ht := by
    rintro _ ⟨⟨d, hdN⟩, hdD, rfl⟩ _ ⟨⟨t, htN⟩, htT, rfl⟩
    refine ⟨⟨d, hdN⟩ * ⟨t, htN⟩ * ⟨d, hdN⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact Subgroup.mem_subgroupOf.2
      (hconjT d (Subgroup.mem_subgroupOf.1 hdD) t (Subgroup.mem_subgroupOf.1 htT))
  have hnormH : Dt ≤ Subgroup.normalizer (Ht : Set (MulAut (barOf 3 L))) := by
    intro d hd
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hconjH d hd h hh, fun hh => ?_⟩
    have h2 := hconjH d⁻¹ (Dt.inv_mem hd) _ hh
    have e : d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have hdelta : localDeltaIn 3 Ht Dt ≠ ⊥ := by
    intro hbot
    rw [hbot] at himg
    exact Lemma54Ns.map_barAut_ne_bot hXN hnot (le_bot_iff.1 himg)
  obtain ⟨⟨hDW, hDC⟩, hf, h4⟩ := hSeitz (barOf 3 L) hq (isPGroup_center_barOf L) hty Dt Ht hDtE
    hinn hnormH hdelta
  set Bt := autBar 3 B L with hBt
  have hDtB : Dt ≤ Bt := Subgroup.map_mono (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hDB hx, x.2⟩)
  have hBtcomm : ∀ β ∈ Bt, ∀ γ ∈ Bt, β * γ = γ * β := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact elemAbelian_comm hBel (Subgroup.mem_subgroupOf.1 hx).1 (Subgroup.mem_subgroupOf.1 hy).1
  have heq : Bt ⊓ innerDiag (barOf 3 L) = Dt := by
    apply le_antisymm
    · rintro β ⟨hβB, hβW⟩
      exact hDC β hβW (fun d hd => hBtcomm β hβB d (hDtB hd))
    · exact le_inf hDtB hDW
  rw [heq]
  refine ⟨hDcard9, ?_, ?_⟩
  · intro x hx
    have hxW : (MulAut.conj x : MulAut (barOf 3 L)) ∈ innerDiag (barOf 3 L) :=
      innerAut_le_innerDiag _ ⟨x, rfl⟩
    have : (MulAut.conj x : MulAut (barOf 3 L)) ∈ Bt ⊓ innerDiag (barOf 3 L) := ⟨hx, hxW⟩
    rw [heq] at this
    by_cases h1 : (MulAut.conj x : MulAut (barOf 3 L)) = 1
    · exact pow_three_eq_one_of_mem_center hq (isPGroup_center_barOf L) hty
        ((conj_eq_one_iff_mem_center x).1 h1)
    · exact hf x h1 this
  · intro Ŵ _ π ι hcov hπW hrange
    set S : Subgroup (MulAut (barOf 3 L)) := Dt ⊔ innerAut (barOf 3 L) with hSdef
    have hSle : S ≤ π.range := sup_le hrange (by
      rintro _ ⟨l, rfl⟩
      exact ⟨ι l, hcov.conj l⟩)
    obtain ⟨x, hx, y, hy, hxy⟩ := h4 ↥(S.comap π) (π.comp (S.comap π).subtype)
      (ι.codRestrict (S.comap π) (fun l => by
        show π (ι l) ∈ S
        rw [hcov.conj]
        exact (le_sup_right : innerAut (barOf 3 L) ≤ S) ⟨l, rfl⟩))
      (isThreeCover_restrict hcov S le_sup_right) (range_restrict_comap π S hSle)
    exact ⟨x.1, hx, y.1, hy, fun h => hxy (Subtype.ext h)⟩

end BranchBMain



section Assembly

variable {G : Type} [Group G] [Finite G]

theorem lemma31iii_of_alternative_a (h31 : Lemma31) (h59 : Lemma59) {m : ℕ}
    (hS : GLStanding G m 3) (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hLC : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hΛ : L ≤ lambdaOf 3 B b) (hψ : ¬ L ≤ psiStarGroup 3 B) : Lemma31iii 3 B L := by
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hB
  have hsc : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB1
  have hlam := lambdaOf_eq_of_lemma31 h31 hS hB.1 hsc hb hb1
  rw [lambdaMOf_eq_bot_of_ne_five (by norm_num), sup_bot_eq] at hlam
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCdef
  set S1 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
    IsInGOne 3 B L} with hS1
  set S2 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
    Lemma31iii 3 B L} with hS2
  set S3 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
    Lemma31iv 3 B L} with hS3
  have hle : L ≤ sSup (S1 ∪ S2 ∪ S3) := by
    rw [sSup_union, sSup_union]
    have : lambdaOf 3 B b = sSup S1 ⊔ sSup S2 ⊔ sSup S3 := hlam
    rw [← this]
    exact hΛ
  have hmem := Lemma510Ns.mem_of_le_sSup hLC (fun A hA => by
    rcases hA with (hA | hA) | hA
    · exact hA.1
    · exact hA.1
    · exact hA.1) hle
  rcases hmem with (hm | hm) | hm
  · exfalso
    apply hψ
    have h1 : L ≤ psiOf 3 B b := le_sSup hm
    have h2 : psiOf 3 B b ≤ psiStarGroup 3 B :=
      le_iSup₂_of_le b hb (le_iSup_of_le hb1 (le_sup_left.trans le_sup_left))
    exact h1.trans h2
  · exact hm.2.2
  · exact absurd hm.2.2.2.2.1 (h59 G m hS hC B hB b hb hb1 L ⟨hLC, Or.inl ⟨hΛ, hψ⟩⟩)

end Assembly

end Lemma510iiNs

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem lemma510ii_of_inputs (h31 : Lemma31) (h59 : Lemma59) (h510 : Lemma510)
    (h191 : Lemma54Ns.Input19_1_2) (hSeitz : Lemma510iiNs.Input19_7_Seitz)
    (hSyl : Lemma510iiNs.InputSL34Sylow) : Lemma513Ns.Lemma510ii := by
  intro G _ _ m hS hC B hB b hb hb1 L hL
  have hty := (h510 G m hS hC B hB b hb hb1 L hL).1
  have hBel : IsElemAbelian 3 B := hB.1.1
  obtain ⟨hLC, hdisj⟩ := hL
  rcases hdisj with ⟨hΛ, hψ⟩ | ⟨D, hD, hDnc⟩
  · exact Lemma510iiNs.clauses_of_lemma31iii hSyl hLC hBel
      (Lemma510iiNs.lemma31iii_of_alternative_a h31 h59 hS hC hB hb hb1 hLC hΛ hψ)
  · exact Lemma510iiNs.clauses_of_branch_b hSeitz h191 hS hBel hb hb1 hLC hty hD hDnc

end CFSG.HardMathSupport.Solomon.LocalBalance
