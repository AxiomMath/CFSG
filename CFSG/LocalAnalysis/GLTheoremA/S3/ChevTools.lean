module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevToolsK
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
  (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner centerQuotient_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom centerQuotientHom_injective onCenterQuotient_apply_mk
    hom_eq_id_of_central_displacement)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open scoped commutatorElement

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def pQuotHom (p : ℕ) (K : Subgroup G) : ↥K →* PQuot p K :=
  QuotientGroup.mk' (GLAPPrimeCore p ↥K)

@[expose] noncomputable def chevQuotHom (p : ℕ) (K : Subgroup G) : ↥K →* PSimple p K :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p K))).comp (pQuotHom p K)

@[expose] noncomputable def chevAut (p : ℕ) (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (PSimple p K) :=
  (centerQuotientHom (PQuot p K)).comp (barAut p K)

theorem pQuotHom_surjective (p : ℕ) (K : Subgroup G) : Function.Surjective (pQuotHom p K) :=
  QuotientGroup.mk'_surjective _

theorem ker_pQuotHom (p : ℕ) (K : Subgroup G) : (pQuotHom p K).ker = GLAPPrimeCore p ↥K :=
  QuotientGroup.ker_mk' _

theorem chevQuotHom_surjective (p : ℕ) (K : Subgroup G) : Function.Surjective (chevQuotHom p K) :=
  (QuotientGroup.mk'_surjective _).comp (pQuotHom_surjective p K)

theorem barAut_pQuotHom (p : ℕ) (K : Subgroup G) (γ : ↥(Subgroup.normalizer (K : Set G)))
    (k : ↥K) : barAut p K γ (pQuotHom p K k) = pQuotHom p K (K.normalizerMonoidHom γ k) :=
  barAut_mk p K γ k

theorem chevAut_chevQuotHom (p : ℕ) (K : Subgroup G) (γ : ↥(Subgroup.normalizer (K : Set G)))
    (k : ↥K) :
    chevAut p K γ (chevQuotHom p K k) = chevQuotHom p K (K.normalizerMonoidHom γ k) := by
  show (centerQuotientHom (PQuot p K) (barAut p K γ))
    ((QuotientGroup.mk' (Subgroup.center (PQuot p K))) (pQuotHom p K k)) = _
  show CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (barAut p K γ)
    ((QuotientGroup.mk' (Subgroup.center (PQuot p K))) (pQuotHom p K k)) = _
  rw [onCenterQuotient_apply_mk, barAut_pQuotHom]
  rfl

theorem chev_mem_glaPPrimeCoreOf_iff {p : ℕ} {L : Subgroup G} {x : G} (hx : x ∈ L) :
    x ∈ GLAPPrimeCoreOf p L ↔ (⟨x, hx⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem chev_conj_mem_glaPPrimeCoreOf {p : ℕ} {L : Subgroup G} {l y : G} (hl : l ∈ L)
    (hy : y ∈ GLAPPrimeCoreOf p L) : l * y * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
  exact Subgroup.mem_map.2 ⟨⟨l, hl⟩ * z * (⟨l, hl⟩ : ↥L)⁻¹,
    Subgroup.Normal.conj_mem (GLAPPrimeCore.normal p ↥L) z hz ⟨l, hl⟩, rfl⟩

theorem chev_coe_normalizerMonoidHom {L : Subgroup G} (γ : ↥(Subgroup.normalizer (L : Set G)))
    (x : ↥L) : ((L.normalizerMonoidHom γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹ := rfl

theorem chev_barAut_eq_one_iff {p : ℕ} {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    barAut p L ⟨a, ha⟩ = 1 ↔ ∀ l ∈ L, ⁅l, a⁆ ∈ GLAPPrimeCoreOf p L := by
  constructor
  · intro h l hl
    have h1 := congrArg (fun φ : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) =>
      φ (QuotientGroup.mk (⟨l, hl⟩ : ↥L))) h
    simp only [MulAut.one_apply] at h1
    rw [barAut_mk, QuotientGroup.eq] at h1
    have h2 := Subgroup.mem_map_of_mem L.subtype h1
    have e : ⁅l, a⁆ =
        l * (((L.normalizerMonoidHom ⟨a, ha⟩ ⟨l, hl⟩)⁻¹ * ⟨l, hl⟩ : ↥L) : G) * l⁻¹ := by
      simp only [commutatorElement_def, chev_coe_normalizerMonoidHom, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    rw [e]
    exact chev_conj_mem_glaPPrimeCoreOf hl h2
  · intro h
    ext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [barAut_mk, MulAut.one_apply, QuotientGroup.eq]
      have hc := chev_conj_mem_glaPPrimeCoreOf (L.inv_mem x.2) (h (x : G) x.2)
      have key : (((L.normalizerMonoidHom ⟨a, ha⟩ x)⁻¹ * x : ↥L) : G) ∈ GLAPPrimeCoreOf p L := by
        have e : (((L.normalizerMonoidHom ⟨a, ha⟩ x)⁻¹ * x : ↥L) : G) =
            (x : G)⁻¹ * ⁅(x : G), a⁆ * ((x : G)⁻¹)⁻¹ := by
          simp only [commutatorElement_def, chev_coe_normalizerMonoidHom, Subgroup.coe_mul,
            Subgroup.coe_inv]
          group
        rw [e]
        exact hc
      exact (chev_mem_glaPPrimeCoreOf_iff _).1 key

theorem chev_barAut_eq_one_iff_centMod {p : ℕ} {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) : barAut p L ⟨a, ha⟩ = 1 ↔ CentMod p L a := by
  rw [centMod_iff, chev_barAut_eq_one_iff ha, mem_centModSubgroup]
  exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

theorem pQuot_mk_eq_mk_iff {p : ℕ} {L : Subgroup G} (x y : ↥L) :
    (QuotientGroup.mk x : PQuot p L) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * (y : G) ∈ GLAPPrimeCoreOf p L := by
  rw [QuotientGroup.eq]
  exact (chev_mem_glaPPrimeCoreOf_iff (L.mul_mem (L.inv_mem x.2) y.2)).symm

theorem barAut_inv_eq_conj_iff {p : ℕ} {L : Subgroup G} {a : G}
    (ha' : a⁻¹ ∈ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) :
    barAut p L ⟨a⁻¹, ha'⟩ = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)⁻¹ : PQuot p L) ↔
      ∀ y ∈ L, (l⁻¹ * y * l)⁻¹ * (a⁻¹ * y * a) ∈ GLAPPrimeCoreOf p L := by
  constructor
  · intro h y hy
    have h1 := congrArg (fun φ : MulAut (PQuot p L) => φ (QuotientGroup.mk ⟨y, hy⟩)) h
    simp only [barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at h1
    rw [pQuot_mk_eq_mk_iff] at h1
    have h2 := (GLAPPrimeCoreOf p L).inv_mem h1
    have e : ((l⁻¹ * y * l)⁻¹ * (a⁻¹ * y * a) : G) =
        ((((L.normalizerMonoidHom ⟨a⁻¹, ha'⟩ ⟨y, hy⟩ : ↥L) : G))⁻¹ *
          (((⟨l, hl⟩ : ↥L)⁻¹ * ⟨y, hy⟩ * (⟨l, hl⟩ : ↥L)⁻¹⁻¹ : ↥L) : G))⁻¹ := by
      simp only [chev_coe_normalizerMonoidHom, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rw [e]
    exact h2
  · intro h
    ext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      simp only [barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
      rw [pQuot_mk_eq_mk_iff]
      have h2 := (GLAPPrimeCoreOf p L).inv_mem (h (x : G) x.2)
      have e : (((L.normalizerMonoidHom ⟨a⁻¹, ha'⟩ x : ↥L) : G))⁻¹ *
          (((⟨l, hl⟩ : ↥L)⁻¹ * x * (⟨l, hl⟩ : ↥L)⁻¹⁻¹ : ↥L) : G) =
          ((l⁻¹ * (x : G) * l)⁻¹ * (a⁻¹ * (x : G) * a))⁻¹ := by
        simp only [chev_coe_normalizerMonoidHom, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rw [e]
      exact h2

theorem inducesInnerMod_iff_barAut_mem_inner {p : ℕ} {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    InducesInnerMod p L a ↔ barAut p L ⟨a, ha⟩ ∈ inner (PQuot p L) := by
  have ha' : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ ha
  have hinv : (⟨a⁻¹, ha'⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨a, ha⟩)⁻¹ := rfl
  have key : barAut p L ⟨a, ha⟩ ∈ inner (PQuot p L) ↔
      ∃ (l : G) (hl : l ∈ L), barAut p L ⟨a⁻¹, ha'⟩ =
        MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)⁻¹ : PQuot p L) := by
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
      refine ⟨(l : G), l.2, ?_⟩
      rw [hinv, map_inv, ← hk, QuotientGroup.mk_inv, map_inv]
    · rintro ⟨l, hl, h⟩
      refine ⟨QuotientGroup.mk (⟨l, hl⟩ : ↥L), ?_⟩
      have h2 : (barAut p L ⟨a, ha⟩)⁻¹ =
          (MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : PQuot p L))⁻¹ := by
        rw [← map_inv (barAut p L), ← hinv, h, QuotientGroup.mk_inv, map_inv]
      exact (inv_inj.1 h2).symm
  rw [key]
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, (barAut_inv_eq_conj_iff ha' hl).2 h⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, (barAut_inv_eq_conj_iff ha' hl).1 h⟩

theorem chevAut_eq_one_iff [Finite G] {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K)
    {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    chevAut p K ⟨a, ha⟩ = 1 ↔ CentMod p K a := by
  haveI : Group.IsPerfect (PQuot p K) := ⟨(isQuasisimple_pQuot_of_glaPComponent hp hK).1⟩
  rw [← chev_barAut_eq_one_iff_centMod ha]
  show centerQuotientHom (PQuot p K) (barAut p K ⟨a, ha⟩) = 1 ↔ _
  rw [← map_one (centerQuotientHom (PQuot p K))]
  exact (centerQuotientHom_injective (PQuot p K)).eq_iff

theorem chevAut_mem_inner_iff [Finite G] {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    chevAut p K ⟨a, ha⟩ ∈ inner (PSimple p K) ↔ InducesInnerMod p K a := by
  haveI : Group.IsPerfect (PQuot p K) := ⟨(isQuasisimple_pQuot_of_glaPComponent hp hK).1⟩
  rw [inducesInnerMod_iff_barAut_mem_inner ha]
  constructor
  · intro h
    exact mem_inner_of_centerQuotientHom_mem h
  · rintro ⟨k, hk⟩
    refine ⟨QuotientGroup.mk' (Subgroup.center (PQuot p K)) k, ?_⟩
    rw [← centerQuotient_conj, hk]
    rfl

theorem chevAut_pow_eq_one (p : ℕ) (K : Subgroup G) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : a ^ n = 1) :
    chevAut p K ⟨a, ha⟩ ^ n = 1 := by
  rw [← map_pow]
  have : (⟨a, ha⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ n = 1 := Subtype.ext hn
  rw [this, map_one]

@[expose] def centModAt (p : ℕ) (L : Subgroup G) (l : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧ ⁅l, g⁆ ∈ GLAPPrimeCoreOf p L}
  one_mem' := ⟨Subgroup.one_mem _, by
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, hLa⟩ ⟨hb, hLb⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    rw [commutatorElement_mul_right]
    refine Subgroup.mul_mem _ hLa ?_
    exact (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L ha) _).1 hLb
  inv_mem' := by
    rintro a ⟨ha, hLa⟩
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    rw [commutatorElement_inv_right]
    have hinv := Subgroup.inv_mem _ ha
    have := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L hinv) ⁅l, a⁆⁻¹).1
      (Subgroup.inv_mem _ hLa)
    simpa [inv_inv] using this

theorem exists_mul_mem_centralizer_of_commutator_mem [Finite G] {p : ℕ}
    (hp : p.Prime) {L : Subgroup G} {a l : G} (ha : IsPGroup p (Subgroup.zpowers a))
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L)
    (hc : ⁅l⁻¹, a⁆ ∈ GLAPPrimeCoreOf p L) :
    ∃ o ∈ GLAPPrimeCoreOf p L, l * o ∈ Subgroup.centralizer ({a} : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p L with hO
  set P := Subgroup.zpowers a with hP
  have hPC : P ≤ centModAt p L l⁻¹ := Subgroup.zpowers_le.2 ⟨haL, hc⟩
  have hmem : ∀ g ∈ P, ∀ o ∈ O, l⁻¹ * (g * (l * o) * g⁻¹) ∈ O := by
    intro g hg o ho
    have hgC := hPC hg
    have h1 : ⁅l⁻¹, g⁆ ∈ O := hgC.2
    have h2 : g * o * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L hgC.1) o).1 ho
    have h3 : l⁻¹ * (g * (l * o) * g⁻¹) = ⁅l⁻¹, g⁆ * (g * o * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact O.mul_mem h1 h2
  letI act : MulAction P O :=
    { smul := fun g o => ⟨l⁻¹ * ((g : G) * (l * (o : G)) * (g : G)⁻¹), hmem g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (show l⁻¹ * (((1 : P) : G) * (l * (o : G)) *
          ((1 : P) : G)⁻¹) = (o : G) by simp)
      mul_smul := fun g h o => Subtype.ext (show l⁻¹ * (((g * h : P) : G) * (l * (o : G)) *
          ((g * h : P) : G)⁻¹) = l⁻¹ * ((g : G) * (l * (l⁻¹ * ((h : G) * (l * (o : G)) *
          (h : G)⁻¹))) * (g : G)⁻¹) by simp only [Subgroup.coe_mul]; group) }
  have hOp : ¬ p ∣ Nat.card O := CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf hp L
  obtain ⟨o, ho⟩ := ha.nonempty_fixed_point_of_prime_not_dvd_card O hOp
  have hfa : l⁻¹ * (a * (l * (o : G)) * a⁻¹) = o :=
    congrArg Subtype.val (ho ⟨a, Subgroup.mem_zpowers a⟩)
  refine ⟨o, o.2, ?_⟩
  have hy : a * (l * (o : G)) * a⁻¹ = l * o := by
    calc a * (l * (o : G)) * a⁻¹ = l * (l⁻¹ * (a * (l * (o : G)) * a⁻¹)) := by group
      _ = l * o := by rw [hfa]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc l * (o : G) * a = a * (l * (o : G)) * a⁻¹ * a := by rw [hy]
    _ = a * (l * o) := by group

end Action

section Quotients

variable {A B : Type} [Group A] [Group B] {p : ℕ}

theorem map_glaPPrimeCore_le_of_surjective [Finite A] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) : (GLAPPrimeCore p A).map f ≤ GLAPPrimeCore p B := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := Finite.of_surjective f hf
  exact le_sSup ⟨Subgroup.Normal.map inferInstance f hf,
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) CFSG.pPrimeCore_coprime_card⟩

@[expose] noncomputable def pQuotMapOfSurjective [Finite A] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) : (A ⧸ GLAPPrimeCore p A) →* (B ⧸ GLAPPrimeCore p B) :=
  QuotientGroup.map _ _ f (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact map_glaPPrimeCore_le_of_surjective hp f hf)

theorem pQuotMapOfSurjective_mk [Finite A] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) (x : A) :
    pQuotMapOfSurjective hp f hf (QuotientGroup.mk x) = QuotientGroup.mk (f x) := rfl

theorem pQuotMapOfSurjective_surjective [Finite A] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) : Function.Surjective (pQuotMapOfSurjective hp f hf) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨QuotientGroup.mk x, rfl⟩

@[expose] noncomputable def pSimpleMapOfSurjective [Finite A] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) :
    ((A ⧸ GLAPPrimeCore p A) ⧸ Subgroup.center (A ⧸ GLAPPrimeCore p A)) →*
      ((B ⧸ GLAPPrimeCore p B) ⧸ Subgroup.center (B ⧸ GLAPPrimeCore p B)) :=
  QuotientGroup.map _ _ (pQuotMapOfSurjective hp f hf) (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact Subgroup.map_center_le_center (pQuotMapOfSurjective_surjective hp f hf))

theorem pSimpleMapOfSurjective_surjective [Finite A] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) : Function.Surjective (pSimpleMapOfSurjective hp f hf) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := pQuotMapOfSurjective_surjective hp f hf y
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem nonempty_pSimple_equiv_of_surjective [Finite A] [Finite B] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) (hA : CFSG.Open.IsQuasisimple (A ⧸ GLAPPrimeCore p A))
    (hB : CFSG.Open.IsQuasisimple (B ⧸ GLAPPrimeCore p B)) :
    Nonempty (((A ⧸ GLAPPrimeCore p A) ⧸ Subgroup.center (A ⧸ GLAPPrimeCore p A)) ≃*
      ((B ⧸ GLAPPrimeCore p B) ⧸ Subgroup.center (B ⧸ GLAPPrimeCore p B))) := by
  haveI : IsSimpleGroup ((A ⧸ GLAPPrimeCore p A) ⧸ Subgroup.center (A ⧸ GLAPPrimeCore p A)) :=
    hA.2
  haveI : IsSimpleGroup ((B ⧸ GLAPPrimeCore p B) ⧸ Subgroup.center (B ⧸ GLAPPrimeCore p B)) :=
    hB.2
  have hinj : Function.Injective (pSimpleMapOfSurjective hp f hf) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pSimpleMapOfSurjective hp f hf).ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne
        ((B ⧸ GLAPPrimeCore p B) ⧸ Subgroup.center (B ⧸ GLAPPrimeCore p B))
      obtain ⟨a', rfl⟩ := pSimpleMapOfSurjective_surjective hp f hf a
      obtain ⟨b', rfl⟩ := pSimpleMapOfSurjective_surjective hp f hf b
      apply hab
      have h1 : pSimpleMapOfSurjective hp f hf a' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : pSimpleMapOfSurjective hp f hf b' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      rw [h1, h2]
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, pSimpleMapOfSurjective_surjective hp f hf⟩⟩

theorem nonempty_pSimple_equiv_map [Finite A] [Finite B] (hp : p.Prime) (π : A →* B)
    {X : Subgroup A} {Y : Subgroup B} {J : Subgroup A} (hJ : GLAPComponent p X J)
    (hJπ : GLAPComponent p Y (J.map π)) :
    Nonempty (PSimple p J ≃* PSimple p (J.map π)) :=
  nonempty_pSimple_equiv_of_surjective hp (π.subgroupMap J) (π.subgroupMap_surjective J)
    (isQuasisimple_pQuot_of_glaPComponent hp hJ) (isQuasisimple_pQuot_of_glaPComponent hp hJπ)

theorem ker_pQuotMapOfSurjective_le_center [Finite A] (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) (hA : CFSG.Open.IsQuasisimple (A ⧸ GLAPPrimeCore p A))
    (hB : Nontrivial (B ⧸ GLAPPrimeCore p B)) :
    (pQuotMapOfSurjective hp f hf).ker ≤ Subgroup.center (A ⧸ GLAPPrimeCore p A) := by
  refine le_center_of_normal_of_isQuasisimple hA (MonoidHom.normal_ker _) fun htop => ?_
  obtain ⟨a, b, hab⟩ := exists_pair_ne (B ⧸ GLAPPrimeCore p B)
  obtain ⟨a', rfl⟩ := pQuotMapOfSurjective_surjective hp f hf a
  obtain ⟨b', rfl⟩ := pQuotMapOfSurjective_surjective hp f hf b
  apply hab
  have h1 : pQuotMapOfSurjective hp f hf a' = 1 := by
    rw [← MonoidHom.mem_ker, htop]
    trivial
  have h2 : pQuotMapOfSurjective hp f hf b' = 1 := by
    rw [← MonoidHom.mem_ker, htop]
    trivial
  rw [h1, h2]

end Quotients

section Injective

variable {A B : Type*} [Group A] [Group B] {p : ℕ}

theorem glaPComponent_eq_of_map_eq_of_ker_le_center (π : A →* B)
    (hker : π.ker ≤ Subgroup.center A) {X J₁ J₂ : Subgroup A} (h₁ : GLAPComponent p X J₁)
    (h₂ : GLAPComponent p X J₂) (h : J₁.map π = J₂.map π) : J₁ = J₂ := by
  have key : ∀ {K₁ K₂ : Subgroup A}, GLAPComponent p X K₁ → GLAPComponent p X K₂ →
      K₁.map π = K₂.map π → K₁ ≤ K₂ := by
    intro K₁ K₂ hK₁ hK₂ hK
    rw [← glaPComponent_perfect hK₁, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨u, hu, hux⟩ : π x ∈ K₂.map π := hK ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨v, hv, hvy⟩ : π y ∈ K₂.map π := hK ▸ Subgroup.mem_map_of_mem π hy
    have hz : u⁻¹ * x ∈ Subgroup.center A := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel])
    have hz' : v⁻¹ * y ∈ Subgroup.center A := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvy, inv_mul_cancel])
    have e : ⁅x, y⁆ = ⁅u, v⁆ := by
      have hx' : x = u * (u⁻¹ * x) := by group
      have hy' : y = v * (v⁻¹ * y) := by group
      rw [hx', hy', commutatorElement_mul_center_left hz, commutatorElement_mul_center_right hz']
    rw [e, commutatorElement_def]
    exact K₂.mul_mem (K₂.mul_mem (K₂.mul_mem hu hv) (K₂.inv_mem hu)) (K₂.inv_mem hv)
  exact le_antisymm (key h₁ h₂ h) (key h₂ h₁ h.symm)

end Injective

section InjectiveCoprime

variable {A B : Type} [Group A] [Group B] [Finite A] {p : ℕ}

theorem glaPComponent_eq_of_map_eq (hp : p.Prime) (ψ : A →* B) {X J₁ J₂ : Subgroup A}
    (hker : Nat.Coprime p (Nat.card ↥(X ⊓ ψ.ker))) (h₁ : GLAPComponent p X J₁)
    (h₂ : GLAPComponent p X J₂) (h : J₁.map ψ = J₂.map ψ) : J₁ = J₂ := by
  refine glaPComponent_unique h₁ h₂ ?_
  have e1 := lcEquiv_barX hp ψ X hker h₁.1
  have e2 := lcEquiv_barX hp ψ X hker h₂.1
  rw [h, ← e2] at e1
  exact Subgroup.map_injective (lcEquiv hp ψ X hker).injective e1

end InjectiveCoprime

section Transfer

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem fixSubgroup_normalizerMonoidHom {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩) =
      (K ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf K := by
  ext k
  rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hk
    have h1 : ((K.normalizerMonoidHom ⟨a, ha⟩ k : ↥K) : G) = (k : G) := congrArg Subtype.val hk
    rw [chev_coe_normalizerMonoidHom] at h1
    exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
  · rintro ⟨-, hk⟩
    apply Subtype.ext
    rw [chev_coe_normalizerMonoidHom]
    exact mul_inv_eq_iff_eq_mul.2 hk.symm

theorem map_fixSubgroup_pQuotHom (hp : p.Prime) {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : IsPGroup p (Subgroup.zpowers a)) :
    (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)).map (pQuotHom p K) =
      fixSubgroup (barAut p K ⟨a, ha⟩) := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [mem_fixSubgroup, barAut_pQuotHom, mem_fixSubgroup.1 hk]
  · intro hy
    obtain ⟨k, rfl⟩ := pQuotHom_surjective p K y
    rw [mem_fixSubgroup, barAut_pQuotHom] at hy
    have hy' : (QuotientGroup.mk (K.normalizerMonoidHom ⟨a, ha⟩ k) : PQuot p K) =
        QuotientGroup.mk k := hy
    have h1 := (pQuot_mk_eq_mk_iff (p := p) k _).1 hy'.symm
    have hc : ⁅(k : G)⁻¹, a⁆ ∈ GLAPPrimeCoreOf p K := by
      have e : ⁅(k : G)⁻¹, a⁆ =
          (k : G)⁻¹ * ((K.normalizerMonoidHom ⟨a, ha⟩ k : ↥K) : G) := by
        rw [chev_coe_normalizerMonoidHom, commutatorElement_def]
        group
      rw [e]
      exact h1
    obtain ⟨o, ho, hko⟩ := exists_mul_mem_centralizer_of_commutator_mem hp hap ha k.2 hc
    have hoK : o ∈ K := Subgroup.map_subtype_le _ ho
    refine ⟨⟨(k : G) * o, K.mul_mem k.2 hoK⟩, ?_, ?_⟩
    · refine SetLike.mem_coe.2 (mem_fixSubgroup.2 ?_)
      apply Subtype.ext
      rw [chev_coe_normalizerMonoidHom]
      exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_singleton_iff.1 hko).symm
    · show (QuotientGroup.mk (⟨(k : G) * o, K.mul_mem k.2 hoK⟩ : ↥K) : PQuot p K) =
        QuotientGroup.mk k
      rw [pQuot_mk_eq_mk_iff]
      have e : ((⟨(k : G) * o, K.mul_mem k.2 hoK⟩ : ↥K) : G)⁻¹ * (k : G) = o⁻¹ := by
        simp
      rw [e]
      exact (GLAPPrimeCoreOf p K).inv_mem ho

theorem coprime_card_inf_ker_pQuotHom (hp : p.Prime) (K : Subgroup G) (X : Subgroup ↥K) :
    Nat.Coprime p (Nat.card ↥(X ⊓ (pQuotHom p K).ker)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) ?_
  rw [ker_pQuotHom]
  exact CFSG.pPrimeCore_coprime_card

@[expose] noncomputable def chevTransfer (p : ℕ) (K J : Subgroup G) : Subgroup (PSimple p K) :=
  (J.subgroupOf K).map (chevQuotHom p K)

theorem chevTransfer_eq (p : ℕ) (K J : Subgroup G) :
    chevTransfer p K J =
      ((J.subgroupOf K).map (pQuotHom p K)).map
        (QuotientGroup.mk' (Subgroup.center (PQuot p K))) :=
  (Subgroup.map_map _ _ _).symm

theorem glaPComponent_map_pQuotHom (hp : p.Prime) {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : IsPGroup p (Subgroup.zpowers a))
    {J : Subgroup G} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) J) :
    GLAPComponent p (fixSubgroup (barAut p K ⟨a, ha⟩)) ((J.subgroupOf K).map (pQuotHom p K)) := by
  have hJ0 : GLAPComponent p (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)) (J.subgroupOf K) := by
    rw [fixSubgroup_normalizerMonoidHom ha]
    exact glaPComponent_subgroupOf hp inf_le_left hJ
  have h := glaPComponent_map hp (pQuotHom p K)
    (coprime_card_inf_ker_pQuotHom hp K (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩))) hJ0
  rwa [map_fixSubgroup_pQuotHom hp ha hap] at h

theorem glaPComponent_chevTransfer (hp : p.Prime) {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : IsPGroup p (Subgroup.zpowers a))
    {J : Subgroup G} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) J) :
    GLAPComponent p (fixSubgroup (chevAut p K ⟨a, ha⟩)) (chevTransfer p K J) := by
  rw [chevTransfer_eq]
  exact glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center (PQuot p K)))
    (by rw [QuotientGroup.ker_mk']) (barAut p K ⟨a, ha⟩) (chevAut p K ⟨a, ha⟩)
    (fun k => (onCenterQuotient_apply_mk (barAut p K ⟨a, ha⟩) k).symm)
    (QuotientGroup.mk'_surjective _) hp (glaPComponent_map_pQuotHom hp ha hap hJ)

theorem nonempty_pSimple_equiv_chevTransfer (hp : p.Prime) {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : IsPGroup p (Subgroup.zpowers a))
    {J : Subgroup G} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) J) :
    Nonempty (PSimple p J ≃* PSimple p (chevTransfer p K J)) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJ0 : GLAPComponent p (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)) (J.subgroupOf K) := by
    rw [fixSubgroup_normalizerMonoidHom ha]
    exact glaPComponent_subgroupOf hp inf_le_left hJ
  have hJ1 := glaPComponent_map_pQuotHom hp ha hap hJ
  have hJ2 : GLAPComponent p (fixSubgroup (chevAut p K ⟨a, ha⟩))
      (((J.subgroupOf K).map (pQuotHom p K)).map
        (QuotientGroup.mk' (Subgroup.center (PQuot p K)))) := by
    rw [← chevTransfer_eq]
    exact glaPComponent_chevTransfer hp ha hap hJ
  obtain ⟨g⟩ := nonempty_pQuot_equiv_subgroupOf p hJK
  obtain ⟨e₁⟩ := nonempty_pSimple_equiv_map hp (pQuotHom p K) hJ0 hJ1
  obtain ⟨e₂⟩ := nonempty_pSimple_equiv_map hp (QuotientGroup.mk' (Subgroup.center (PQuot p K)))
    hJ1 hJ2
  have e₀ : PSimple p J ≃* PSimple p (J.subgroupOf K) :=
    QuotientGroup.congr _ _ g.symm (Subgroup.map_center_eq g.symm)
  rw [chevTransfer_eq]
  exact ⟨e₀.trans (e₁.trans e₂)⟩

theorem eq_of_chevTransfer_eq (hp : p.Prime) {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : IsPGroup p (Subgroup.zpowers a))
    {J J' : Subgroup G} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) J)
    (hJ' : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) J')
    (h : chevTransfer p K J = chevTransfer p K J') : J = J' := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJK' : J' ≤ K := hJ'.1.trans inf_le_left
  have hmk : ∀ {L : Subgroup G}, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L →
      GLAPComponent p (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)) (L.subgroupOf K) := by
    intro L hL
    rw [fixSubgroup_normalizerMonoidHom ha]
    exact glaPComponent_subgroupOf hp inf_le_left hL
  have h1 : (J.subgroupOf K).map (pQuotHom p K) = (J'.subgroupOf K).map (pQuotHom p K) :=
    glaPComponent_eq_of_map_eq_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center (PQuot p K))) (by rw [QuotientGroup.ker_mk'])
      (glaPComponent_map_pQuotHom hp ha hap hJ) (glaPComponent_map_pQuotHom hp ha hap hJ')
      (by rw [chevTransfer_eq, chevTransfer_eq] at h; exact h)
  have h2 : J.subgroupOf K = J'.subgroupOf K :=
    glaPComponent_eq_of_map_eq hp (pQuotHom p K)
      (coprime_card_inf_ker_pQuotHom hp K (fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩)))
      (hmk hJ) (hmk hJ') h1
  rw [← Subgroup.map_subgroupOf_eq_of_le hJK, ← Subgroup.map_subgroupOf_eq_of_le hJK', h2]

end Transfer

section OneElement

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem chev_isChevSimple_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsChevSimple p T) : IsChevSimple p S := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

theorem chev_pSimple_simple_nonabelian (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K) :
    IsSimpleGroup (PSimple p K) ∧ ∃ a b : PSimple p K, a * b ≠ b * a := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
  exact ⟨hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq⟩

theorem chev_one_element (hp : p.Prime) (hD : KDChevDown p) (hU : KDChevUnique p)
    {X K : Subgroup G} (hK : GLAPComponent p X K) (hchev : IsChevSimple p (PSimple p K)) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : a ^ p = 1) :
    (∀ L : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L →
      IsChevSimple p (PSimple p L)) ∧
    (∀ L L' : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L' → L = L') := by
  obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian hp hK
  have hap' : IsPGroup p (Subgroup.zpowers a) := isPGroup_zpowers_of_pow_eq_one hap
  have hα : chevAut p K ⟨a, ha⟩ ^ p = 1 := chevAut_pow_eq_one p K ha hap
  refine ⟨fun L hL => ?_, fun L L' hL hL' => ?_⟩
  · obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp ha hap' hL
    exact chev_isChevSimple_of_mulEquiv e
      (hD (PSimple p K) hsimple hnonab hchev _ hα _ (glaPComponent_chevTransfer hp ha hap' hL))
  · exact eq_of_chevTransfer_eq hp ha hap' hL hL'
      (hU (PSimple p K) hsimple hnonab hchev _ hα _ _ (glaPComponent_chevTransfer hp ha hap' hL)
        (glaPComponent_chevTransfer hp ha hap' hL'))

theorem chev_one_element_inner (hp : p.Prime) (hI : KDChevInner p) {X K : Subgroup G}
    (hK : GLAPComponent p X K) (hchev : IsChevSimple p (PSimple p K)) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : a ^ p = 1) (hnc : ¬ CentMod p K a)
    (hin : InducesInnerMod p K a) (L : Subgroup G) :
    ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L := by
  intro hL
  obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian hp hK
  have hap' : IsPGroup p (Subgroup.zpowers a) := isPGroup_zpowers_of_pow_eq_one hap
  have hα : chevAut p K ⟨a, ha⟩ ^ p = 1 := chevAut_pow_eq_one p K ha hap
  have hα1 : chevAut p K ⟨a, ha⟩ ≠ 1 := fun h => hnc ((chevAut_eq_one_iff hp hK ha).1 h)
  have hαin : chevAut p K ⟨a, ha⟩ ∈ inner (PSimple p K) := (chevAut_mem_inner_iff hp hK ha).2 hin
  have hbot := hI (PSimple p K) hsimple hnonab hchev _ hα hα1 hαin
  have hL' := glaPComponent_chevTransfer hp ha hap' hL
  exact glaPComponent_ne_bot' hL' (le_bot_iff.1 (hbot ▸ le_sSup hL'))

end OneElement

section Balance

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem chev_commute_conj_iff {c y h : G} (hcy : Commute c y) :
    Commute c (y * h * y⁻¹) ↔ Commute c h := by
  constructor
  · intro H
    have := (hcy.inv_right.mul_right H).mul_right hcy
    simpa [mul_assoc] using this
  · intro H
    exact (hcy.mul_right H).mul_right hcy.inv_right

theorem chev_inf_centralizer_le_normalizer {Y K : Subgroup G}
    (hYK : Y ≤ Subgroup.normalizer (K : Set G)) (A : Subgroup G) :
    Y ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro y hy
  obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.1 hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hK := Subgroup.mem_normalizer_iff.1 (hYK hyY) h
  rw [Subgroup.mem_centralizer_iff] at hyC
  simp only [Subgroup.mem_inf, SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  refine and_congr hK ⟨fun hh c hc => ?_, fun hh c hc => ?_⟩
  · exact (chev_commute_conj_iff (hyC c hc)).2 (hh c hc)
  · exact (chev_commute_conj_iff (hyC c hc)).1 (hh c hc)

theorem glaPComponent_le_glaPLayer_centralizer_singleton (hp : p.Prime) (hB : LBalanceAt G p)
    {K A : Subgroup G} (hK : CFSG.Open.IsKGroup ↥K) (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {a : G} (ha : a ∈ A) {J : Subgroup G}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J) :
    J ≤ GLAPLayer p (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hApg : IsPGroup p A := isPGroup_of_isElemAbelian hA
  have hYK : K ⊔ A ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hAK
  have hY : CFSG.Open.IsKGroup ↥(K ⊔ A) := chevTools_isKGroup_sup hp hK hAK hApg
  have hX' : CFSG.Open.IsKGroup ↥((K ⊔ A) ⊓ Subgroup.centralizer ({a} : Set G)) :=
    CFSG.Open.IsKGroup.of_le hY inf_le_left
  have hAX' : A ≤ (K ⊔ A) ⊓ Subgroup.centralizer ({a} : Set G) := by
    refine le_inf le_sup_right fun b hb => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.1.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have h1 := hB _ A hX' hAX' hApg
  have e1 : ((K ⊔ A) ⊓ Subgroup.centralizer ({a} : Set G)) ⊓ Subgroup.centralizer (A : Set G) =
      (K ⊔ A) ⊓ Subgroup.centralizer (A : Set G) := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.1 h3) a ha).symm
  rw [e1] at h1
  have hSX : K ⊓ Subgroup.centralizer (A : Set G) ≤ (K ⊔ A) ⊓ Subgroup.centralizer (A : Set G) :=
    inf_le_inf_right _ le_sup_left
  have hsub : IsSubnormal (K ⊓ Subgroup.centralizer (A : Set G))
      ((K ⊔ A) ⊓ Subgroup.centralizer (A : Set G)) :=
    IsSubnormal.step hSX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hSX).2
        (chev_inf_centralizer_le_normalizer hYK A)) (IsSubnormal.refl _)
  have hJY := glaPComponent_of_isSubnormal' hp hsub hJ
  have hJL : J ≤ GLAPLayer p ((K ⊔ A) ⊓ Subgroup.centralizer (A : Set G)) := le_sSup hJY
  refine hJL.trans (h1.trans (sSup_le fun L hL => ?_))
  have hLK : L ≤ K := chevTools_perfect_le_of_sup hp hAK hApg (hL.1.trans inf_le_left)
    (glaPComponent_perfect hL)
  have hLK' : L ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := le_inf hLK (hL.1.trans inf_le_right)
  exact le_sSup (glaPComponent_of_le hp hL hLK' (inf_le_inf_right _ le_sup_left))

end Balance

section Inner

theorem chev_mem_inner_of_central_surjective {Q Q' : Type*} [Group Q] [Group Q'] [Group.IsPerfect Q]
    (Ψ : Q →* Q') (hΨ : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center Q)
    {θ : MulAut Q} {θ' : MulAut Q'} (hθ : ∀ q, Ψ (θ q) = θ' (Ψ q)) (h : θ' ∈ inner Q') :
    θ ∈ inner Q := by
  obtain ⟨q', hq'⟩ := h
  obtain ⟨q₀, rfl⟩ := hΨ q'
  let φ : Q →* Q := ((MulAut.conj q₀⁻¹ : MulAut Q) : Q →* Q).comp (θ : Q →* Q)
  have hc : ∀ q, q⁻¹ * φ q ∈ Subgroup.center Q := by
    intro q
    apply hker
    rw [MonoidHom.mem_ker]
    have h1 : Ψ (φ q) = (Ψ q₀)⁻¹ * θ' (Ψ q) * Ψ q₀ := by
      show Ψ (q₀⁻¹ * θ q * q₀⁻¹⁻¹) = _
      rw [map_mul, map_mul, map_inv, hθ, inv_inv]
    rw [map_mul, map_inv, h1, ← hq', MulAut.conj_apply]
    group
  have hid := hom_eq_id_of_central_displacement φ hc
  refine ⟨q₀, ?_⟩
  ext q
  have h2 := congrArg (fun f : Q →* Q => f q) hid
  simp only [φ, MonoidHom.comp_apply, MonoidHom.id_apply] at h2
  change q₀⁻¹ * θ q * q₀⁻¹⁻¹ = q at h2
  change q₀ * q * q₀⁻¹ = θ q
  calc q₀ * q * q₀⁻¹ = q₀ * (q₀⁻¹ * θ q * q₀⁻¹⁻¹) * q₀⁻¹ := by rw [h2]
    _ = θ q := by group

theorem chev_center_eq_bot_of_simple_nonabelian {T : Type*} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

end Inner

section Chain

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem inf_glaPPrimeCoreOf_le (hp : p.Prime) {H K : Subgroup G} (hHK : H ≤ K) :
    H ⊓ GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p H := by
  set O := GLAPPrimeCoreOf p K with hO
  set N0 : Subgroup ↥H := O.subgroupOf H with hN0
  have hnorm : N0.Normal := by
    refine ⟨fun n hn h' => ?_⟩
    show ((h' * n * h'⁻¹ : ↥H) : G) ∈ O
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p K (hHK h'.2)) (n : G)).1 hn
    simpa using this
  have hdvd : Nat.card N0 ∣ Nat.card O := by
    have h1 : N0.map H.subtype = H ⊓ O := by
      rw [hN0, ← Subgroup.inf_subgroupOf_right O H]
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : O ⊓ H ≤ H)]
      exact inf_comm _ _
    have h2 : Nat.card (N0.map H.subtype) = Nat.card N0 :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h2, h1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime p (Nat.card N0) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf hp K (hd.trans hdvd)
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : N0 ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx.2), rfl⟩

theorem centMod_of_le (hp : p.Prime) {K₁ K : Subgroup G} (hK₁K : K₁ ≤ K) {b : G}
    (hb : b ∈ Subgroup.normalizer (K₁ : Set G)) (hbK : CentMod p K b) : CentMod p K₁ b := by
  rw [centMod_iff]
  refine ⟨hb, fun l hl => ?_⟩
  have h1 : ⁅l, b⁆ ∈ K₁ := by
    have := K₁.mul_mem hl ((Subgroup.mem_normalizer_iff.1 hb l⁻¹).1 (K₁.inv_mem hl))
    simpa [commutatorElement_def, mul_assoc] using this
  exact inf_glaPPrimeCoreOf_le hp hK₁K ⟨h1, (centMod_iff.1 hbK).2 l (hK₁K hl)⟩

theorem centMod_of_le_centralizer {K₁ : Subgroup G} {a : G}
    (h : K₁ ≤ Subgroup.centralizer ({a} : Set G)) : CentMod p K₁ a :=
  centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (h hk))

theorem inf_centModSubgroup_le (hp : p.Prime) {K K₁ A : Subgroup G} {a : G}
    (hK₁ : K₁ ≤ K ⊓ Subgroup.centralizer ({a} : Set G))
    (hA : A ≤ Subgroup.normalizer (K₁ : Set G)) :
    A ⊓ centModSubgroup p K ≤ A ⊓ centModSubgroup p K₁ := fun b hb =>
  ⟨hb.1, centMod_iff.1 (centMod_of_le hp (hK₁.trans inf_le_left) (hA hb.1)
    (centMod_iff.2 hb.2))⟩

end Chain

end CFSG.LocalAnalysis.GLTheoremA
