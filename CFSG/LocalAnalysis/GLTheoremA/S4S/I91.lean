module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem i91_mem_O_iff {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {x : G} (hx : x ∈ L) :
    x ∈ GLAPPrimeCoreOf p L ↔ (⟨x, hx⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem i91_mem_core_iff {G : Type} [Group G] {p : ℕ} {L : Subgroup G} (u : ↥L) :
    u ∈ GLAPPrimeCore p ↥L ↔ (u : G) ∈ GLAPPrimeCoreOf p L := by
  constructor
  · intro hu
    exact Subgroup.mem_map_of_mem L.subtype hu
  · rintro ⟨v, hv, hvu⟩
    have : v = u := Subtype.ext hvu
    exact this ▸ hv

private theorem i91_conj_mem {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {l y : G} (hl : l ∈ L)
    (hy : y ∈ GLAPPrimeCoreOf p L) : l * y * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
  exact Subgroup.mem_map.2 ⟨⟨l, hl⟩ * z * (⟨l, hl⟩ : ↥L)⁻¹,
    Subgroup.Normal.conj_mem (GLAPPrimeCore.normal p ↥L) z hz ⟨l, hl⟩, rfl⟩

private theorem i91_coe_normalizerMonoidHom {G : Type} [Group G] {L : Subgroup G}
    (γ : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L) :
    ((L.normalizerMonoidHom γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹ := rfl

private theorem i91_barAut_of_mem {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {l : G}
    (hl : l ∈ L) :
    barAut p L ⟨l, Subgroup.le_normalizer hl⟩ =
      MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl

private theorem i91_inducesInnerMod_of_barAut {G : Type} [Group G] {p : ℕ} {L : Subgroup G}
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) {k : ↥L ⧸ GLAPPrimeCore p ↥L}
    (h : barAut p L ⟨a, ha⟩ = MulAut.conj k) : InducesInnerMod p L a := by
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective k
  have ha' : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ ha
  have hinv : barAut p L ⟨a⁻¹, ha'⟩ =
      MulAut.conj (QuotientGroup.mk k'⁻¹ : ↥L ⧸ GLAPPrimeCore p ↥L) := by
    have e : (⟨a⁻¹, ha'⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨a, ha⟩)⁻¹ := rfl
    rw [e, map_inv, h, QuotientGroup.mk_inv, map_inv]
  refine ⟨(k' : G), k'.2, fun y hy => ?_⟩
  have h1 := congrArg (fun φ : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) =>
    φ (QuotientGroup.mk (⟨y, hy⟩ : ↥L))) hinv
  simp only [barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at h1
  rw [QuotientGroup.eq] at h1
  refine Subgroup.mem_map.2 ⟨_, Subgroup.inv_mem _ h1, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, i91_coe_normalizerMonoidHom, Subgroup.coe_mk,
    Subgroup.coe_subtype]
  group

private theorem i91_barAut_eq_conj_of_inducesInnerMod {G : Type} [Group G] {p : ℕ}
    {L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (h : InducesInnerMod p L a) :
    ∃ k : ↥L ⧸ GLAPPrimeCore p ↥L, barAut p L ⟨a, ha⟩ = MulAut.conj k := by
  obtain ⟨l, hl, hy⟩ := h
  refine ⟨QuotientGroup.mk ⟨l, hl⟩, ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine (i91_mem_core_iff _).2 ?_
    have hu : a * (x : G) * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 ha (x : G)).1 x.2
    have e : (((L.normalizerMonoidHom ⟨a, ha⟩ x)⁻¹ * (⟨l, hl⟩ * x * (⟨l, hl⟩ : ↥L)⁻¹) : ↥L) : G) =
        l * ((l⁻¹ * (a * (x : G) * a⁻¹) * l)⁻¹ * (a⁻¹ * (a * (x : G) * a⁻¹) * a)) * l⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, i91_coe_normalizerMonoidHom, Subgroup.coe_mk]
      group
    rw [e]
    exact i91_conj_mem hl (hy _ hu)

private theorem i91_coprime_O {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (L : Subgroup G) : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p L)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

private theorem i91_fixed_lift {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {L : Subgroup G} {a x0 : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ p = 1)
    (hx0 : x0 ∈ L)
    (hfix : barAut p L ⟨a, ha⟩ (QuotientGroup.mk ⟨x0, hx0⟩) = QuotientGroup.mk ⟨x0, hx0⟩) :
    ∃ x ∈ L, x * a = a * x ∧ x⁻¹ * x0 ∈ GLAPPrimeCoreOf p L := by
  classical
  have hOL : GLAPPrimeCoreOf p L ≤ L := Subgroup.map_subtype_le _
  have hOle : GLAPPrimeCoreOf p L ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    Subgroup.le_normalizer (hOL hx)
  haveI hNn : ((GLAPPrimeCoreOf p L).subgroupOf (Subgroup.normalizer (L : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).2
      (normalizer_le_normalizer_glaPPrimeCoreOf p L)
  have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCoreOf p L).subgroupOf
      (Subgroup.normalizer (L : Set G)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOle).toEquiv]
    exact i91_coprime_O hp L
  have hc : (a * x0 * a⁻¹)⁻¹ * x0 ∈ GLAPPrimeCoreOf p L := by
    rw [barAut_mk, QuotientGroup.eq] at hfix
    have h1 := (i91_mem_core_iff _).1 hfix
    convert h1 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, i91_coe_normalizerMonoidHom, Subgroup.coe_mk]
  have hcoset : (⟨a, ha⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨x0, Subgroup.le_normalizer hx0⟩ *
      (⟨a, ha⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * (⟨x0, Subgroup.le_normalizer hx0⟩)⁻¹ ∈
      (GLAPPrimeCoreOf p L).subgroupOf (Subgroup.normalizer (L : Set G)) := by
    rw [Subgroup.mem_subgroupOf]
    show a * x0 * a⁻¹ * x0⁻¹ ∈ GLAPPrimeCoreOf p L
    have e : a * x0 * a⁻¹ * x0⁻¹ = x0 * ((a * x0 * a⁻¹)⁻¹ * x0)⁻¹ * x0⁻¹ := by group
    rw [e]
    exact i91_conj_mem hx0 (inv_mem hc)
  have ha' : (⟨a, ha⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
    Subtype.ext (by simpa using ha3)
  obtain ⟨x, hxw, hxa⟩ := CFSG.SignalizerFunctorTheorem.exists_fixed_of_coprime hp ha' _ hcop
    hcoset
  have hxO : (x : G) * x0⁻¹ ∈ GLAPPrimeCoreOf p L := by
    have h1 := Subgroup.mem_subgroupOf.1 hxw
    simpa using h1
  have hxconj : a * (x : G) * a⁻¹ = x := by
    have h1 := congrArg Subtype.val hxa
    simpa using h1
  have hx1L : (x : G) ∈ L := by
    have h1 : (x : G) = ((x : G) * x0⁻¹) * x0 := by group
    rw [h1]
    exact mul_mem (hOL hxO) hx0
  refine ⟨(x : G), hx1L, ?_, ?_⟩
  · exact (mul_inv_eq_iff_eq_mul.1 hxconj).symm
  · have h2 : (x : G)⁻¹ * x0 = (x : G)⁻¹ * ((x : G) * x0⁻¹)⁻¹ * (x : G)⁻¹⁻¹ := by group
    rw [h2]
    exact i91_conj_mem (inv_mem hx1L) (inv_mem hxO)

private theorem i91_quasisimple_of_simple (T : Type) [Group T] [IsSimpleGroup T]
    (hnon : ∃ a b : T, a * b ≠ b * a) : CFSG.Open.IsQuasisimple T := by
  refine ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top T hnon, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.ComponentClassification.Helpers.center_eq_bot T hnon)).trans
      (QuotientGroup.quotientBot (G := T))).isSimpleGroup

private theorem i91_ker_eq_core {p : ℕ} (hp : p.Prime) {A S : Type} [Group A] [Finite A] [Group S]
    [IsSimpleGroup S] (ψ : A →* S) (hψ : Function.Surjective ψ) (hpS : p ∣ Nat.card S)
    (hker : Nat.Coprime p (Nat.card ψ.ker)) : ψ.ker = GLAPPrimeCore p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · exact le_sSup (show ψ.ker ∈ normalPPrimeSubgroups p A from ⟨inferInstance, hker⟩)
  · haveI := Subgroup.Normal.map (GLAPPrimeCore.normal p A) ψ hψ
    rcases Subgroup.Normal.eq_bot_or_eq_top ((GLAPPrimeCore p A).map ψ) with h1 | h1
    · intro x hx
      have hx' : ψ x ∈ (GLAPPrimeCore p A).map ψ := Subgroup.mem_map_of_mem ψ hx
      rw [h1, Subgroup.mem_bot] at hx'
      exact hx'
    · exfalso
      have hc1 : Nat.card ((GLAPPrimeCore p A).map ψ) = Nat.card S := by
        rw [h1, Subgroup.card_top]
      have hc2 : Nat.card ((GLAPPrimeCore p A).map ψ) ∣ Nat.card (GLAPPrimeCore p A) :=
        Subgroup.card_map_dvd (H := GLAPPrimeCore p A) ψ
      have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCore p A).map ψ)) :=
        Nat.Coprime.coprime_dvd_right hc2 CFSG.pPrimeCore_coprime_card
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (by rw [hc1]; exact hpS)

private theorem i91_pow_eq {M : Type*} [Monoid M] {α : M} {k : ℕ} (h3 : α ^ 3 = 1)
    (hk : k % 3 = 1) : α ^ k = α := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 3 * m + 1 := ⟨k / 3, by omega⟩
  rw [pow_succ, pow_mul, h3, one_pow, one_mul]

theorem i91At_of {G : Type} [Group G] [Finite G] (h : KD91) : I91At G := by
  intro X L b hL hcat hbN hb3 hbni
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ :=
    (h (PSimple 3 L) hcat).1 (PQuot 3 L) hq (I2611.isPGroup_center_pQuot' hp L) ⟨MulEquiv.refl _⟩
  let e1 : PQuot 3 L ≃* PSimple 3 L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hQcat : catalogIs (PQuot 3 L) (onLie isTrialityD4Big) := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    exact ⟨i, hi, ⟨e1.trans e⟩⟩
  have hγ3 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
    Subtype.ext (by simpa using hb3)
  have hβ3 : barAut 3 L ⟨b, hbN⟩ ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
  have hβni : barAut 3 L ⟨b, hbN⟩ ∉ innerAut (PQuot 3 L) := by
    intro hmem
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hmem
    exact hbni (i91_inducesInnerMod_of_barAut hbN hk.symm)
  obtain ⟨g, hg3, hgcat⟩ := (h (PQuot 3 L) hQcat).2.1 _ hβ3 hβni
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective g
  have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
  have hyN : l * b ∈ Subgroup.normalizer (L : Set G) := mul_mem hlN hbN
  obtain ⟨α, hα⟩ : ∃ α : MulAut (PQuot 3 L),
      α = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) * barAut 3 L ⟨b, hbN⟩ := ⟨_, rfl⟩
  rw [← hα] at hg3 hgcat
  have hα3 : α ^ 3 = 1 := hg3
  have hγα : barAut 3 L ⟨l * b, hyN⟩ = α := by
    rw [show (⟨l * b, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨l, hlN⟩ * ⟨b, hbN⟩ from rfl,
      map_mul, i91_barAut_of_mem hl, hα]
  have hbl : ∀ x ∈ L, b * x * b⁻¹ ∈ L := fun x hx => (Subgroup.mem_normalizer_iff.1 hbN x).1 hx
  have hcube : (l * b) ^ 3 = l * (b * l * b⁻¹) * (b * (b * l * b⁻¹) * b⁻¹) := by
    have e : (l * b) ^ 3 = l * (b * l * b⁻¹) * (b * (b * l * b⁻¹) * b⁻¹) * b ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hb3, mul_one]
  have hzL : (l * b) ^ 3 ∈ L := by
    rw [hcube]
    exact mul_mem (mul_mem hl (hbl l hl)) (hbl _ (hbl l hl))
  have hzN : (l * b) ^ 3 ∈ Subgroup.normalizer (L : Set G) := pow_mem hyN 3
  have hzγ : barAut 3 L ⟨(l * b) ^ 3, hzN⟩ = 1 := by
    rw [show (⟨(l * b) ^ 3, hzN⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨l * b, hyN⟩ ^ 3 from
      Subtype.ext (by simp), map_pow, hγα, hα3]
  have hzO : (l * b) ^ 3 ∈ GLAPPrimeCoreOf 3 L := by
    have hcen : (QuotientGroup.mk (⟨(l * b) ^ 3, hzL⟩ : ↥L) : PQuot 3 L) ∈
        Subgroup.center (PQuot 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        have h1 := congrArg (fun φ : MulAut (PQuot 3 L) => φ (QuotientGroup.mk x)) hzγ
        simp only [MulAut.one_apply, barAut_mk] at h1
        have h2 : QuotientGroup.mk (⟨(l * b) ^ 3, hzL⟩ : ↥L) * QuotientGroup.mk x *
            (QuotientGroup.mk (⟨(l * b) ^ 3, hzL⟩ : ↥L) : PQuot 3 L)⁻¹ = QuotientGroup.mk x := by
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          exact h1
        exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
    exact (i91_mem_O_iff hzL).2 hcen
  obtain ⟨s, hscard⟩ : ∃ s : ℕ, Nat.card ↥(GLAPPrimeCoreOf 3 L) = s := ⟨_, rfl⟩
  have hcopS : Nat.Coprime 3 s := hscard ▸ i91_coprime_O hp L
  have hzs : ((l * b) ^ 3) ^ s = 1 := by
    have h1 : (⟨(l * b) ^ 3, hzO⟩ : ↥(GLAPPrimeCoreOf 3 L)) ^
        Nat.card ↥(GLAPPrimeCoreOf 3 L) = 1 := pow_card_eq_one'
    rw [hscard] at h1
    simpa using congrArg Subtype.val h1
  have hs2 : (s * s) % 3 = 1 := by
    have h3 : ¬ 3 ∣ s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcopS
    have h4 : s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases h4 with h4 | h4 <;> simp [Nat.mul_mod, h4]
  obtain ⟨y, hy⟩ : ∃ y : G, y = (l * b) ^ (s * s) := ⟨_, rfl⟩
  have hyS : y ∈ L ⊔ Subgroup.zpowers b := by
    rw [hy]
    exact Subgroup.pow_mem _
      (mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))) _
  have hy3 : y ^ 3 = 1 := by
    rw [hy]
    calc ((l * b) ^ (s * s)) ^ 3 = ((l * b) ^ 3) ^ (s * s) := pow_right_comm _ _ _
      _ = (((l * b) ^ 3) ^ s) ^ s := pow_mul _ _ _
      _ = 1 := by rw [hzs, one_pow]
  have hyN' : y ∈ Subgroup.normalizer (L : Set G) := by
    rw [hy]
    exact pow_mem hyN _
  have hyα : barAut 3 L ⟨y, hyN'⟩ = α := by
    rw [show (⟨y, hyN'⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨l * b, hyN⟩ ^ (s * s) from
      Subtype.ext (by simp [hy]), map_pow, hγα, i91_pow_eq hα3 hs2]
  have hyni : ¬ InducesInnerMod 3 L y := by
    intro hind
    obtain ⟨k, hk⟩ := i91_barAut_eq_conj_of_inducesInnerMod hyN' hind
    rw [hyα] at hk
    apply hβni
    refine MonoidHom.mem_range.2 ⟨(QuotientGroup.mk (⟨l, hl⟩ : ↥L))⁻¹ * k, ?_⟩
    calc MulAut.conj ((QuotientGroup.mk (⟨l, hl⟩ : ↥L))⁻¹ * k)
        = (MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)))⁻¹ * MulAut.conj k := by
          rw [map_mul, map_inv]
      _ = (MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)))⁻¹ * α := by rw [hk]
      _ = barAut 3 L ⟨b, hbN⟩ := by
          rw [hα, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨Xs, hXs⟩ : ∃ Xs : Subgroup G, Xs = L ⊓ Subgroup.centralizer ({y} : Set G) := ⟨_, rfl⟩
  have hXsL : Xs ≤ L := by
    rw [hXs]
    exact inf_le_left
  have hXsC : ∀ x ∈ Xs, x * y = y * x := by
    intro x hx
    rw [hXs] at hx
    exact Subgroup.mem_centralizer_singleton_iff.1 hx.2
  have hXsmem : ∀ x ∈ L, x * y = y * x → x ∈ Xs := by
    intro x hx hc
    rw [hXs]
    exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥Xs →* ↥L ⧸ GLAPPrimeCore 3 ↥L,
      ∀ x : ↥Xs, ρ x = QuotientGroup.mk ⟨(x : G), hXsL x.2⟩ :=
    ⟨(QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hXsL), fun x => rfl⟩
  have hrange : ρ.range = fixSubgroup α := by
    ext q
    rw [mem_fixSubgroup]
    constructor
    · intro hq
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hq
      have hc : (x : G) * y = y * x := hXsC (x : G) x.2
      rw [hρ, ← hyα, barAut_mk]
      congr 1
      apply Subtype.ext
      show y * (x : G) * y⁻¹ = x
      rw [← hc, mul_inv_cancel_right]
    · intro hq
      obtain ⟨⟨x0, hx0⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hfix : barAut 3 L ⟨y, hyN'⟩ (QuotientGroup.mk ⟨x0, hx0⟩) =
          QuotientGroup.mk ⟨x0, hx0⟩ := by
        rw [hyα]
        exact hq
      obtain ⟨x, hxL, hxy, hxO⟩ := i91_fixed_lift hp hyN' hy3 hx0 hfix
      refine MonoidHom.mem_range.2 ⟨⟨x, hXsmem x hxL hxy⟩, ?_⟩
      rw [hρ]
      exact QuotientGroup.eq.2 ((i91_mem_core_iff _).2 hxO)
  have hsurj : Function.Surjective ρ.rangeRestrict := MonoidHom.rangeRestrict_surjective ρ
  have hTcat : catalogIs ↥(ρ.range) (onLie isG2Big) := by
    rw [hrange]
    exact hgcat
  obtain ⟨hTsimp, hTnon, hT3⟩ := (h (PQuot 3 L) hQcat).2.2 ↥(ρ.range) hTcat
  haveI := hTsimp
  have hTq : CFSG.Open.IsQuasisimple ↥(ρ.range) := i91_quasisimple_of_simple _ hTnon
  have hkerρ : ρ.ker = GLAPPrimeCore 3 ↥Xs := by
    have hcopK : Nat.Coprime 3 (Nat.card ρ.ker) := by
      have hle : ρ.ker.map (Subgroup.inclusion hXsL) ≤ GLAPPrimeCore 3 ↥L := by
        rintro _ ⟨x, hx, rfl⟩
        have h1 : ρ x = 1 := MonoidHom.mem_ker.1 hx
        rw [hρ] at h1
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hc1 : Nat.card (ρ.ker.map (Subgroup.inclusion hXsL)) = Nat.card ρ.ker :=
        Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXsL)
      rw [← hc1]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
        CFSG.pPrimeCore_coprime_card
    have hk := i91_ker_eq_core hp ρ.rangeRestrict hsurj hT3
      (by rw [MonoidHom.ker_rangeRestrict]; exact hcopK)
    rwa [MonoidHom.ker_rangeRestrict] at hk
  let eX : PQuot 3 Xs ≃* ↥(ρ.range) :=
    (QuotientGroup.quotientMulEquivOfEq
      (by rw [MonoidHom.ker_rangeRestrict, hkerρ] :
        GLAPPrimeCore 3 ↥Xs = ρ.rangeRestrict.ker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ.rangeRestrict hsurj)
  have hXq : CFSG.Open.IsQuasisimple (PQuot 3 Xs) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eX.symm hTq
  obtain ⟨hJcomp, -, hJbar⟩ := glaPLayer_of_isQuasisimple hXq
  have hJX : GLAPLayer 3 Xs ≤ Xs := hJcomp.1
  have hsup : GLAPLayer 3 Xs ⊔ GLAPPrimeCoreOf 3 Xs = Xs :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJX hJbar
  obtain ⟨-, ⟨e4⟩⟩ := cover_facts hp hJX hsup
  let e5 : PQuot 3 (GLAPLayer 3 Xs) ≃* ↥(ρ.range) := e4.trans eX
  haveI : IsSimpleGroup (PQuot 3 (GLAPLayer 3 Xs)) := e5.isSimpleGroup
  have hJnon : ∃ a b : PQuot 3 (GLAPLayer 3 Xs), a * b ≠ b * a := by
    obtain ⟨a, c, hac⟩ := hTnon
    refine ⟨e5.symm a, e5.symm c, fun heq => hac ?_⟩
    have := congrArg e5 heq
    simpa using this
  have hJc : Subgroup.center (PQuot 3 (GLAPLayer 3 Xs)) = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot _ hJnon
  let eP : PSimple 3 (GLAPLayer 3 Xs) ≃* PQuot 3 (GLAPLayer 3 Xs) :=
    (QuotientGroup.quotientMulEquivOfEq hJc).trans QuotientGroup.quotientBot
  obtain ⟨i, hi, ⟨ei⟩⟩ := hTcat
  refine ⟨y, hyS, hy3, hyni, ?_, ?_⟩
  · subst hXs
    exact hJcomp
  · subst hXs
    exact ⟨i, hi, ⟨eP.trans (e5.trans ei)⟩⟩

end CFSG.LocalAnalysis.GLTheoremA
