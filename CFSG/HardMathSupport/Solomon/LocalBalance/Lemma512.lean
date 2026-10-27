module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def IsSLThreeEpsAny (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧
      Nonempty (Y ≃* ↥(StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      q ≠ 2 ∧ Nonempty (Y ≃* ↥(StatedSU 3 q K)))

@[expose] def fixedSub {Y : Type*} [Group Y] (α : MulAut Y) : Subgroup Y :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y)

abbrev Cen {G : Type*} [Group G] (v : G) : Subgroup G := Subgroup.centralizer ({v} : Set G)

abbrev conjHull {G : Type*} [Group G] (v : G) (J : Subgroup G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 (Cen v), GLBConj g J

abbrev CBarOf {G : Type*} [Group G] (v : G) : Type _ := ↥(Cen v) ⧸ GLAPPrimeCore 3 ↥(Cen v)

@[expose] def Input25_3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K J A : Subgroup Y) (b : Y) (hbJ : b ∈ J),
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K → GLAPPrimeCore 3 ↥K = ⊥ → b ∈ K →
    orderOf b = 3 →
    CFSG.Open.IsComponentOf J (GLALayer (K ⊓ Subgroup.centralizer ({b} : Set Y))) →
    IsSLThreeEpsAny (barOf 3 J) →
    Subgroup.center (barOf 3 J) = Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)) →
    A ≤ Subgroup.normalizer (K : Set Y) → CFSG.Open.IsElemAbelian 3 A → Nat.card A = 9 →
    b ∈ A → (∀ a ∈ A, a ≠ 1 → InducesFieldAut 3 J a) →
      J = K ∨ ∃ a ∈ A, a ≠ 1 ∧ b ∉ oPrimePOf 3 (K ⊓ Subgroup.centralizer ({a} : Set Y))

@[expose] def Input18_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ u v : G, orderOf u = 3 → orderOf v = 3 → u * v = v * u →
      ∀ J : Subgroup G, GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 (Cen u) ⊓ Cen v)) J →
        ((∃ L₁ : Subgroup G, GLAPComponent 3 (Cen v) L₁ ∧ conjHull v J = L₁ ∧
            GLBConj u L₁ = L₁) ∨
          (∃ L₁ L₂ L₃ : Subgroup G, GLAPComponent 3 (Cen v) L₁ ∧ GLAPComponent 3 (Cen v) L₂ ∧
            GLAPComponent 3 (Cen v) L₃ ∧ L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₃ ≠ L₁ ∧ GLBConj u L₁ = L₂ ∧
            GLBConj u L₂ = L₃ ∧ GLBConj u L₃ = L₁ ∧ conjHull v J = L₁ ⊔ L₂ ⊔ L₃)) ∧
        ∀ hu : u ∈ Cen v,
          CFSG.Open.IsComponentOf (barX 3 (Cen v) J)
            (GLALayer (barX 3 (Cen v) (conjHull v J) ⊓
              Subgroup.centralizer ({(QuotientGroup.mk ⟨u, hu⟩ : CBarOf v)} : Set (CBarOf v))))

@[expose] def InputSL3FieldFixed : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) → (∃ z ∈ Subgroup.center Y, z ≠ 1) →
    ∀ α : MulAut Y, α ^ 3 = 1 → IsFieldAutThree α →
      CFSG.Open.IsQuasisimple ↥(fixedSub α) ∧ IsSLThreeEpsAny ↥(fixedSub α)

@[expose] def InputSL3FieldRestrict : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) → (∃ z ∈ Subgroup.center Y, z ≠ 1) →
    ∀ α : MulAut Y, α ^ 3 = 1 → IsFieldAutThree α →
      ∀ E : Subgroup (MulAut Y), α ∈ E → (∀ ε ∈ E, IsFieldAutThree ε) →
        ∀ ε ∈ E, ∃ ρ : MulAut ↥(fixedSub α),
          (∀ y : ↥(fixedSub α), ((ρ y : ↥(fixedSub α)) : Y) = ε (y : Y)) ∧ IsFieldAutThree ρ

theorem orderOf_mk_prime_three {G : Type*} [Group G] [Finite G] {X : Subgroup G} {b : G}
    (hbX : b ∈ X) (hb : orderOf b = 3) :
    orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b, hbX⟩) = 3 := by
  have hb3 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b, hbX⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa [hb] using pow_orderOf_eq_one b)
    rw [this, map_one]
  have hne : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b, hbX⟩) ≠ 1 := by
    intro h
    have hmem : (⟨b, hbX⟩ : ↥X) ∈ GLAPPrimeCore 3 ↥X := (QuotientGroup.eq_one_iff _).1 h
    have h1 : orderOf (⟨⟨b, hbX⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥X)) = 3 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      simpa using hb
    have h2 := orderOf_dvd_natCard (⟨⟨b, hbX⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥X))
    rw [h1] at h2
    have h3 := coprime_card_gLAPPrimeCore_aux 3 ↥X
    exact absurd (Nat.eq_one_of_dvd_coprimes h3 (dvd_refl 3) h2) (by norm_num)
  exact orderOf_eq_prime hb3 hne

theorem center_eq_zpowers_of_card_three {Y : Type*} [Group Y] {Z : Subgroup Y}
    (hZ : Nat.card Z = 3) {z : Y} (hz : z ∈ Z) (hz1 : z ≠ 1) : Z = Subgroup.zpowers z := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hz3 : orderOf z = 3 := by
    have h1 : orderOf z ∣ 3 := by
      rw [← hZ]
      have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
      rwa [← Subgroup.orderOf_coe] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hle : Subgroup.zpowers z ≤ Z := (Subgroup.zpowers_le).2 hz
  have hcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hcard])).symm

theorem exists_commute_mul {G : Type*} [Group G] {a : G} (ha : a ^ 3 = 1) {M : Subgroup G}
    [Finite M]
    (haM : a ∈ Subgroup.normalizer (M : Set G)) (hcop : Nat.Coprime 3 (Nat.card M)) {h : G}
    (hhM : h ∈ Subgroup.normalizer (M : Set G)) (hfix : a * h * a⁻¹ * h⁻¹ ∈ M) :
    ∃ m ∈ M, a * (h * m) = (h * m) * a := by
  classical
  have := Fintype.ofFinite ↥M
  have hmemN : ∀ g ∈ Subgroup.normalizer (M : Set G), ∀ m ∈ M, g * m * g⁻¹ ∈ M :=
    fun g hg m hm => (Subgroup.mem_normalizer_iff.1 hg m).1 hm
  have hmemN' : ∀ g ∈ Subgroup.normalizer (M : Set G), ∀ m ∈ M, g⁻¹ * m * g ∈ M :=
    fun g hg m hm => by
      have := hmemN g⁻¹ (inv_mem hg) m hm
      simpa using this
  have hf : ∀ m ∈ M, h⁻¹ * (a * (h * m) * a⁻¹) ∈ M := by
    intro m hm
    have h1 : h⁻¹ * (a * (h * m) * a⁻¹) =
        (h⁻¹ * (a * h * a⁻¹ * h⁻¹) * h) * (a * m * a⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hmemN' h hhM _ hfix) (hmemN a haM m hm)
  have hg : ∀ m ∈ M, h⁻¹ * (a⁻¹ * (h * m) * a) ∈ M := by
    intro m hm
    have hv : (a⁻¹ * h * a * h⁻¹) ∈ M := by
      have h2 := hmemN' a haM _ hfix
      have h3 : a⁻¹ * (a * h * a⁻¹ * h⁻¹) * a = (a⁻¹ * h * a * h⁻¹)⁻¹ := by group
      rw [h3] at h2
      simpa using M.inv_mem h2
    have h1 : h⁻¹ * (a⁻¹ * (h * m) * a) =
        (h⁻¹ * (a⁻¹ * h * a * h⁻¹) * h) * (a⁻¹ * m * a) := by group
    rw [h1]
    exact M.mul_mem (hmemN' h hhM _ hv) (hmemN' a haM m hm)
  have ha3 : a * a * a = 1 := by simpa [pow_succ] using ha
  let σ : Equiv.Perm ↥M :=
    { toFun := fun m => ⟨h⁻¹ * (a * (h * (m : G)) * a⁻¹), hf m m.2⟩
      invFun := fun m => ⟨h⁻¹ * (a⁻¹ * (h * (m : G)) * a), hg m m.2⟩
      left_inv := fun m => Subtype.ext (by simp only; group)
      right_inv := fun m => Subtype.ext (by simp only; group) }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext m
    simp only [pow_one, Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq]
    show h⁻¹ * (a * (h * (h⁻¹ * (a * (h * (h⁻¹ * (a * (h * (m : G)) * a⁻¹))) * a⁻¹))) * a⁻¹)
      = m
    have e : h⁻¹ * (a * (h * (h⁻¹ * (a * (h * (h⁻¹ * (a * (h * (m : G)) * a⁻¹))) * a⁻¹))) * a⁻¹)
        = h⁻¹ * ((a * a * a) * (h * (m : G)) * (a * a * a)⁻¹) := by group
    rw [e, ha3]
    group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hndvd : ¬ 3 ∣ Fintype.card ↥M := by
    rw [← Nat.card_eq_fintype_card]
    intro hd
    exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) hd) (by norm_num)
  obtain ⟨m, hm⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) hndvd hσ
  refine ⟨m, m.2, ?_⟩
  have h1 : h⁻¹ * (a * (h * (m : G)) * a⁻¹) = m := congrArg Subtype.val hm
  have h2 : a * (h * (m : G)) * a⁻¹ = h * m := by
    have := congrArg (fun y => h * y) h1
    simpa using this
  calc a * (h * (m : G)) = a * (h * (m : G)) * a⁻¹ * a := by group
    _ = (h * (m : G)) * a := by rw [h2]

theorem mem_gLAPPrimeCoreOf_iff {G : Type*} [Group G] (p : ℕ) (L : Subgroup G) (y : G) :
    y ∈ GLAPPrimeCoreOf p L ↔ ∃ h : y ∈ L, (⟨y, h⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

theorem gLAPPrimeCoreOf_le {G : Type*} [Group G] (p : ℕ) (L : Subgroup G) :
    GLAPPrimeCoreOf p L ≤ L := Subgroup.map_subtype_le _

theorem conj_mem_gLAPPrimeCoreOf {G : Type*} [Group G] (p : ℕ) (L : Subgroup G) {l : G}
    (hl : l ∈ L) {y : G} (hy : y ∈ GLAPPrimeCoreOf p L) : l * y * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨hyL, hy'⟩ := (mem_gLAPPrimeCoreOf_iff p L y).1 hy
  rw [mem_gLAPPrimeCoreOf_iff]
  refine ⟨L.mul_mem (L.mul_mem hl hyL) (L.inv_mem hl), ?_⟩
  have := (GLAPPrimeCore.normal p ↥L).conj_mem _ hy' ⟨l, hl⟩
  exact this

theorem le_normalizer_gLAPPrimeCoreOf {G : Type*} [Group G] (p : ℕ) (L : Subgroup G) :
    L ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => conj_mem_gLAPPrimeCoreOf p L hl hy
  · intro hy
    have := conj_mem_gLAPPrimeCoreOf p L (L.inv_mem hl) hy
    simpa [mul_assoc] using this

theorem mem_normalizer_gLAPPrimeCoreOf {G : Type*} [Group G] (p : ℕ) {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hx ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hx]

theorem card_gLAPPrimeCoreOf_coprime {G : Type*} [Group G] [Finite G] (p : ℕ) (L : Subgroup G) :
    Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p L)) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact coprime_card_gLAPPrimeCore_aux p ↥L

theorem fixedSub_barAut_eq {G : Type*} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hx3 : x ^ 3 = 1) (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    fixedSub (barAut 3 L ⟨x, hxN⟩) = barX 3 L (L ⊓ Cen x) := by
  have hxL : ∀ l : ↥L, x * (l : G) * x⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.1 hxN l).1 l.2
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) y
  have hα : ∀ l : ↥L, barAut 3 L ⟨x, hxN⟩ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨x * (l : G) * x⁻¹, hxL l⟩ : ↥L) :=
    fun l => barAut_mk 3 L ⟨x, hxN⟩ l
  show barAut 3 L ⟨x, hxN⟩ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l ↔ _
  constructor
  · intro h
    rw [hα] at h
    have h1 : (⟨x * (l : G) * x⁻¹, hxL l⟩ : ↥L)⁻¹ * l ∈ GLAPPrimeCore 3 ↥L :=
      QuotientGroup.eq.1 h
    have hw : x * (l : G)⁻¹ * x⁻¹ * (l : G) ∈ GLAPPrimeCoreOf 3 L := by
      rw [mem_gLAPPrimeCoreOf_iff]
      refine ⟨?_, ?_⟩
      · exact L.mul_mem (by simpa using hxL ⟨(l : G)⁻¹, L.inv_mem l.2⟩) l.2
      · convert h1 using 1
        apply Subtype.ext
        simp [mul_assoc]
    have hfix : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
      have := conj_mem_gLAPPrimeCoreOf 3 L l.2 ((GLAPPrimeCoreOf 3 L).inv_mem hw)
      convert this using 1
      group
    obtain ⟨m, hm, hcomm⟩ := exists_commute_mul hx3 (mem_normalizer_gLAPPrimeCoreOf 3 hxN)
      (card_gLAPPrimeCoreOf_coprime 3 L) (le_normalizer_gLAPPrimeCoreOf 3 L l.2) hfix
    have hmL : m ∈ L := gLAPPrimeCoreOf_le 3 L hm
    refine ⟨⟨(l : G) * m, L.mul_mem l.2 hmL⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2
        ⟨L.mul_mem l.2 hmL, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
    · have hm' : (⟨m, hmL⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := ((mem_gLAPPrimeCoreOf_iff 3 L m).1 hm).2
      have h2 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) ⟨m, hmL⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).2 hm'
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (l * ⟨m, hmL⟩) = _
      rw [map_mul, h2, mul_one]
  · rintro ⟨⟨h, hhL⟩, hh, hhl⟩
    have hh' : h ∈ L ⊓ Cen x := Subgroup.mem_subgroupOf.1 hh
    have hcomm : x * h = h * x := (Subgroup.mem_centralizer_singleton_iff.1 hh'.2).symm
    rw [← hhl, hα]
    congr 1
    apply Subtype.ext
    show x * h * x⁻¹ = h
    rw [hcomm]; group

theorem mem_of_barX_eq_top {G : Type*} [Group G] [Finite G] {H J : Subgroup G} {b : G}
    (hJ : barX 3 H J = ⊤) (hbH : b ∈ H) (hb3 : b ^ 3 = 1) (hc : ∀ h ∈ H, b * h = h * b) :
    b ∈ J := by
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) ⟨b, hbH⟩ ∈ barX 3 H J := by
    rw [hJ]; exact Subgroup.mem_top _
  obtain ⟨⟨j, hjH⟩, hjJ, hjb⟩ := hmem
  have hjJ' : j ∈ J := Subgroup.mem_subgroupOf.1 hjJ
  have hn : (⟨j, hjH⟩ : ↥H)⁻¹ * ⟨b, hbH⟩ ∈ GLAPPrimeCore 3 ↥H := QuotientGroup.eq.1 hjb
  set n : G := j⁻¹ * b with hn_def
  have hnM : n ∈ GLAPPrimeCoreOf 3 H := by
    rw [mem_gLAPPrimeCoreOf_iff]
    exact ⟨H.mul_mem (H.inv_mem hjH) hbH, hn⟩
  have hbn : b = j * n := by simp [hn_def]
  have hnH : n ∈ H := gLAPPrimeCoreOf_le 3 H hnM
  have hcomm : j * n = n * j := by
    have h1 : b * n = n * b := hc n hnH
    have hj : j = b * n⁻¹ := by rw [hbn]; group
    have h2 : n⁻¹ * b = b * n⁻¹ := by
      calc n⁻¹ * b = n⁻¹ * (b * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * b) * n⁻¹ := by rw [h1]
        _ = b * n⁻¹ := by group
    rw [hj]
    calc b * n⁻¹ * n = b := by group
      _ = n * (b * n⁻¹) := by rw [← h2]; group
  have hord : Nat.Coprime 3 (orderOf n) := by
    have hcop := card_gLAPPrimeCoreOf_coprime 3 H
    refine Nat.Coprime.coprime_dvd_right ?_ hcop
    have := orderOf_dvd_natCard (⟨n, hnM⟩ : ↥(GLAPPrimeCoreOf 3 H))
    rwa [← Subgroup.orderOf_coe] at this
  have hbm : b ^ orderOf n = j ^ orderOf n := by
    have : b ^ orderOf n = (j * n) ^ orderOf n := by rw [← hbn]
    rw [this, (Commute.mul_pow (show Commute j n from hcomm) (orderOf n)), pow_orderOf_eq_one n,
      mul_one]
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hb3) hord.symm)
  rw [← hu, hbm]
  exact J.pow_mem (J.pow_mem hjJ' _) _

theorem barX_card_elemAbelian {G : Type*} [Group G] [Finite G] {C A : Subgroup G} (hAC : A ≤ C)
    (hA : CFSG.Open.IsElemAbelian 3 A) :
    CFSG.Open.IsElemAbelian 3 (barX 3 C A) ∧ Nat.card (barX 3 C A) = Nat.card A := by
  set f := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hf
  set H := A.subgroupOf C with hH
  have hHcomm : ∀ x y : ↥C, x ∈ H → y ∈ H → x * y = y * x := by
    intro x y hx hy
    have hx' : (x : G) ∈ A := Subgroup.mem_subgroupOf.1 hx
    have hy' : (y : G) ∈ A := Subgroup.mem_subgroupOf.1 hy
    have := hA.1.is_comm.comm ⟨(x : G), hx'⟩ ⟨(y : G), hy'⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have hHexp : ∀ x : ↥C, x ∈ H → x ^ 3 = 1 := by
    intro x hx
    have hx' : (x : G) ∈ A := Subgroup.mem_subgroupOf.1 hx
    exact Subtype.ext (by simpa using hA.2 _ hx')
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
    apply Subtype.ext
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, hHcomm x y hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hHexp x hx, map_one]
  · let f' : ↥H →* ↥C ⧸ GLAPPrimeCore 3 ↥C := f.comp H.subtype
    have hinj : Function.Injective f' := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro z hz
      rw [MonoidHom.mem_ker] at hz
      have hz1 : (z : ↥C) ∈ GLAPPrimeCore 3 ↥C := (QuotientGroup.eq_one_iff _).1 hz
      have h1 : orderOf (⟨(z : ↥C), hz1⟩ : ↥(GLAPPrimeCore 3 ↥C)) ∣
          Nat.card (GLAPPrimeCore 3 ↥C) := orderOf_dvd_natCard _
      have h2 : orderOf (z : ↥C) ∣ 3 := orderOf_dvd_of_pow_eq_one (hHexp z z.2)
      have h3 : orderOf (z : ↥C) ∣ Nat.card (GLAPPrimeCore 3 ↥C) := by
        rwa [← Subgroup.orderOf_coe] at h1
      have h4 := Nat.eq_one_of_dvd_coprimes (coprime_card_gLAPPrimeCore_aux 3 ↥C) h2 h3
      have : (z : ↥C) = 1 := orderOf_eq_one_iff.1 h4
      exact Subtype.ext this
    have hmap : barX 3 C A = f'.range := (MonoidHom.domRestrict_range H f).symm
    rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv

theorem comm_mem_core_of_barX {G : Type*} [Group G] [Finite G] {C J K : Subgroup G}
    (hKC : K ≤ C) (hKJ : barX 3 C K ≤ barX 3 C J) {b : G} (hbC : b ∈ C)
    (hbJ : ∀ j ∈ J, j * b = b * j) :
    ∀ k ∈ K, k * b * k⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf 3 C := by
  intro k hk
  have hkC : k ∈ C := hKC hk
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hkC⟩ ∈ barX 3 C J :=
    hKJ ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  obtain ⟨⟨j, hjC⟩, hjJ, hjk⟩ := hmem
  have hjJ' : j ∈ J := Subgroup.mem_subgroupOf.1 hjJ
  have hn : (⟨j, hjC⟩ : ↥C)⁻¹ * ⟨k, hkC⟩ ∈ GLAPPrimeCore 3 ↥C := QuotientGroup.eq.1 hjk
  have hnN : j⁻¹ * k ∈ GLAPPrimeCoreOf 3 C := by
    rw [mem_gLAPPrimeCoreOf_iff]
    exact ⟨C.mul_mem (C.inv_mem hjC) hkC, hn⟩
  have hjb : j * b = b * j := hbJ j hjJ'
  have hu : (j⁻¹ * k) * (b * (j⁻¹ * k)⁻¹ * b⁻¹) ∈ GLAPPrimeCoreOf 3 C :=
    (GLAPPrimeCoreOf 3 C).mul_mem hnN
      (conj_mem_gLAPPrimeCoreOf 3 C hbC ((GLAPPrimeCoreOf 3 C).inv_mem hnN))
  have := conj_mem_gLAPPrimeCoreOf 3 C hjC hu
  have hjb' : j * b⁻¹ * j⁻¹ = b⁻¹ := by
    have : Commute j b⁻¹ := (show Commute j b from hjb).inv_right
    rw [this.eq]; group
  convert this using 1
  calc k * b * k⁻¹ * b⁻¹ = k * b * k⁻¹ * (j * b⁻¹ * j⁻¹) := by rw [hjb']
    _ = _ := by group

theorem isSLThreeEpsAny_congr {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsSLThreeEpsAny Y) : IsSLThreeEpsAny Y' := by
  rcases h with ⟨K, F, fin, hK, ⟨e'⟩⟩ | ⟨K, F, fin, q, hK, hq, hq2, ⟨e'⟩⟩
  · exact Or.inl ⟨K, F, fin, hK, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨K, F, fin, q, hK, hq, hq2, ⟨e.symm.trans e'⟩⟩

theorem isFieldAutThree_congr {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {α : MulAut Y} {α' : MulAut Y'} (h : ∀ y, e (α y) = α' (e y)) (hα : IsFieldAutThree α) :
    IsFieldAutThree α' := by
  have hc : (Subgroup.center Y).map e.toMonoidHom = Subgroup.center Y' := Subgroup.map_center_eq e
  let ec : (Y ⧸ Subgroup.center Y) ≃* (Y' ⧸ Subgroup.center Y') := QuotientGroup.congr _ _ e hc
  have hec : ∀ y : Y, ec (QuotientGroup.mk y) = QuotientGroup.mk (e y) := fun y => rfl
  rcases hα with rfl | ⟨K, F, fin, θ, σ, φ, γ, hφ, hθ⟩ | ⟨K, F, fin, q, θ, σ, φ, γ, hK, hodd, hφ, hθ⟩
  · left
    ext y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have := h y
    simp only [MulAut.one_apply] at this
    simpa using this.symm
  · right; left
    refine ⟨K, F, fin, ec.symm.trans θ, σ, φ, γ, hφ, ?_⟩
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have h1 : (ec.symm.trans θ) (QuotientGroup.mk (e y)) = θ (QuotientGroup.mk y) := by
      show θ (ec.symm (QuotientGroup.mk (e y))) = _
      rw [← hec, ec.symm_apply_apply]
    have h2 : (ec.symm.trans θ) (QuotientGroup.mk (α' (e y))) = θ (QuotientGroup.mk (α y)) := by
      show θ (ec.symm (QuotientGroup.mk (α' (e y)))) = _
      rw [← h y, ← hec, ec.symm_apply_apply]
    rw [h2, h1]
    exact hθ y
  · right; right
    refine ⟨K, F, fin, q, ec.symm.trans θ, σ, φ, γ, hK, hodd, hφ, ?_⟩
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have h1 : (ec.symm.trans θ) (QuotientGroup.mk (e y)) = θ (QuotientGroup.mk y) := by
      show θ (ec.symm (QuotientGroup.mk (e y))) = _
      rw [← hec, ec.symm_apply_apply]
    have h2 : (ec.symm.trans θ) (QuotientGroup.mk (α' (e y))) = θ (QuotientGroup.mk (α y)) := by
      show θ (ec.symm (QuotientGroup.mk (α' (e y)))) = _
      rw [← h y, ← hec, ec.symm_apply_apply]
    rw [h2, h1]
    exact hθ y

theorem le_gLBConj_gLAPLayer {G : Type*} [Group G] [Finite G] (p : ℕ) {X : Subgroup G} {a : G}
    (haX : a ∈ Subgroup.normalizer (X : Set G)) :
    GLAPLayer p X ≤ GLBConj a (GLAPLayer p X) := by
  have hX' : GLBConj a⁻¹ X = X := mem_normalizer_iff_gLBConj_eq.1 (inv_mem haX)
  refine sSup_le fun K hK => ?_
  have hK' : GLAPComponent p X (GLBConj a⁻¹ K) := by
    have := glaPComponent_gLBConj a⁻¹ hK
    rwa [hX'] at this
  have hle : GLBConj a⁻¹ K ≤ GLAPLayer p X := le_sSup hK'
  intro y hy
  rw [mem_gLBConj]
  apply hle
  rw [mem_gLBConj]
  have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rw [e]
  exact hy

theorem le_normalizer_gLAPLayer {G : Type*} [Group G] [Finite G] (p : ℕ) {X : Subgroup G}
    {B : Subgroup G} (hB : B ≤ Subgroup.normalizer (X : Set G)) :
    B ≤ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  intro a ha
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm ?_ (le_gLBConj_gLAPLayer p (hB ha))
  have h := gLBConj_mono a (le_gLBConj_gLAPLayer p (hB (B.inv_mem ha)))
  rwa [gLBConj_gLBConj_inv] at h

theorem le_normalizer_conjHull {G : Type*} [Group G] [Finite G] {x : G} {A J₀ : Subgroup G}
    (hAC : A ≤ Cen x) (hAJ : A ≤ Subgroup.normalizer (J₀ : Set G)) :
    A ≤ Subgroup.normalizer (conjHull x J₀ : Set G) := by
  have hAN : A ≤ Subgroup.normalizer (Cen x : Set G) := by
    intro a ha
    rw [mem_normalizer_iff_gLBConj_eq]
    exact gLBConj_centralizer_singleton_of_commute (Subgroup.mem_centralizer_singleton_iff.1 (hAC ha))
  have hAL := le_normalizer_gLAPLayer 3 hAN
  have gc : ∀ (g : G) (H T : Subgroup G), GLBConj g H ≤ T ↔ H ≤ GLBConj g⁻¹ T := by
    intro g H T
    constructor
    · intro h
      have := gLBConj_mono g⁻¹ h
      rwa [gLBConj_inv_gLBConj] at this
    · intro h
      have := gLBConj_mono g h
      rwa [gLBConj_gLBConj_inv] at this
  have key : ∀ b ∈ A, GLBConj b (conjHull x J₀) ≤ conjHull x J₀ := by
    intro b hb
    rw [gc]
    refine iSup₂_le fun g hg => ?_
    rw [← gc, gLBConj_gLBConj]
    have hg' : b⁻¹ * g * b⁻¹⁻¹ ∈ GLAPLayer 3 (Cen x) := by
      have := (Subgroup.mem_normalizer_iff.1 (hAL (A.inv_mem hb)) g).1 hg
      exact this
    have hgb : g * b = b * (b⁻¹ * g * b) := by group
    have hg'' : b⁻¹ * g * b ∈ GLAPLayer 3 (Cen x) := by simpa using hg'
    have e : GLBConj (g * b) J₀ = GLBConj (b⁻¹ * g * b) J₀ := by
      rw [hgb, ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer (hAJ hb)]
    rw [e]
    exact le_iSup₂ (f := fun g _ => GLBConj g J₀) (b⁻¹ * g * b) hg''
  intro b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key b hb) ?_
  have h2 := (gc b⁻¹ _ _).1 (key b⁻¹ (A.inv_mem hb))
  rwa [inv_inv] at h2

theorem isSubnormal_le' {G : Type*} [Group G] {H K : Subgroup G} (h : CFSG.Open.IsSubnormal H K) :
    H ≤ K :=
  h.le

theorem isPGroup_gLBConj {G : Type*} [Group G] {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P)
    (m : G) : IsPGroup p (GLBConj m P) := hP.map _

theorem isPGroup_subgroupOf {G : Type*} [Group G] {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P)
    (H : Subgroup G) : IsPGroup p (P.subgroupOf H) := by
  let f : ↥(P.subgroupOf H) →* ↥P :=
    (H.subtype.comp (P.subgroupOf H).subtype).codRestrict P fun x => x.2
  refine hP.of_injective f ?_
  intro x y hxy
  have := congrArg (fun z : ↥P => (z : G)) hxy
  exact Subtype.ext (Subtype.ext this)

theorem exists_normal_pGroup_of_isSubnormal {G : Type*} [Group G] [Finite G] (p : ℕ)
    {H K : Subgroup G} (hHK : CFSG.Open.IsSubnormal H K) :
    ∀ P : Subgroup G, P ≤ H → H ≤ Subgroup.normalizer (P : Set G) → IsPGroup p P →
      ∃ R : Subgroup G, R ≤ K ∧ K ≤ Subgroup.normalizer (R : Set G) ∧ IsPGroup p R ∧ P ≤ R := by
  induction hHK with
  | refl H =>
    intro P hPH hPn hP
    exact ⟨P, hPH, hPn, hP, le_rfl⟩
  | @step H M K hHM hHMn hMK ih =>
    intro P hPH hPn hP
    have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hHMn
    have hmH : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H := fun m hm h hh =>
      (Subgroup.mem_normalizer_iff.1 (hMH hm) h).1 hh
    have hconjH : ∀ m ∈ M, GLBConj m P ≤ H := by
      intro m hm y hy
      rw [mem_gLBConj] at hy
      have hH : GLBConj m H = H := mem_normalizer_iff_gLBConj_eq.1 (hMH hm)
      have : m * y * m⁻¹ ∈ H := hPH hy
      have h2 : y ∈ GLBConj m H := by rw [mem_gLBConj]; exact this
      rwa [hH] at h2
    have hconjn : ∀ m ∈ M, H ≤ Subgroup.normalizer (GLBConj m P : Set G) := by
      intro m hm h hh
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ h ∈ H, ∀ z ∈ GLBConj m P, h * z * h⁻¹ ∈ GLBConj m P := by
        intro h hh z hz
        rw [mem_gLBConj] at hz ⊢
        have hmh : m * h * m⁻¹ ∈ H := hmH m hm h hh
        have := (Subgroup.mem_normalizer_iff.1 (hPn hmh) (m * z * m⁻¹)).1 hz
        have e : m * (h * z * h⁻¹) * m⁻¹ = m * h * m⁻¹ * (m * z * m⁻¹) * (m * h * m⁻¹)⁻¹ := by
          group
        rw [e]; exact this
      intro y
      constructor
      · exact fun hy => key h hh y hy
      · intro hy
        have := key h⁻¹ (H.inv_mem hh) _ hy
        simpa [mul_assoc] using this
    have hcore : IsPGroup p ((CFSG.pCore p ↥H).map H.subtype) :=
      (CFSG.pCore_isPGroup).map H.subtype
    have hconjle : ∀ m ∈ M, GLBConj m P ≤ (CFSG.pCore p ↥H).map H.subtype := by
      intro m hm y hy
      have hyH : y ∈ H := hconjH m hm hy
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      have hn : ((GLBConj m P).subgroupOf H).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (hconjH m hm)).2 (hconjn m hm)
      have hpg : IsPGroup p ((GLBConj m P).subgroupOf H) :=
        isPGroup_subgroupOf (isPGroup_gLBConj hP m) H
      exact le_sSup (show (GLBConj m P).subgroupOf H ∈
        {K : Subgroup ↥H | K.Normal ∧ IsPGroup p K} from ⟨hn, hpg⟩)
        (Subgroup.mem_subgroupOf.2 hy)
    set P' : Subgroup G := ⨆ m ∈ M, GLBConj m P with hP'
    have hPP' : P ≤ P' := by
      have := le_iSup₂ (f := fun m (_ : m ∈ M) => GLBConj m P) 1 (one_mem _)
      rwa [gLBConj_one] at this
    have hP'H : P' ≤ H := iSup₂_le fun m hm => hconjH m hm
    have hP'p : IsPGroup p P' := by
      have hle : P' ≤ (CFSG.pCore p ↥H).map H.subtype :=
        iSup₂_le fun m hm => hconjle m hm
      exact hcore.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hP'n : M ≤ Subgroup.normalizer (P' : Set G) := by
      have gc : ∀ (g : G) (A T : Subgroup G), GLBConj g A ≤ T ↔ A ≤ GLBConj g⁻¹ T := by
        intro g A T
        constructor
        · intro h
          have := gLBConj_mono g⁻¹ h
          rwa [gLBConj_inv_gLBConj] at this
        · intro h
          have := gLBConj_mono g h
          rwa [gLBConj_gLBConj_inv] at this
      have key : ∀ b ∈ M, GLBConj b P' ≤ P' := by
        intro b hb
        rw [gc]
        refine iSup₂_le fun g hg => ?_
        rw [← gc, gLBConj_gLBConj]
        exact le_iSup₂ (f := fun m (_ : m ∈ M) => GLBConj m P) (g * b) (M.mul_mem hg hb)
      intro b hb
      rw [mem_normalizer_iff_gLBConj_eq]
      refine le_antisymm (key b hb) ?_
      have h2 := (gc b⁻¹ _ _).1 (key b⁻¹ (M.inv_mem hb))
      rwa [inv_inv] at h2
    obtain ⟨R, hRK, hRn, hRp, hP'R⟩ := ih P' (hP'H.trans hHM) hP'n hP'p
    exact ⟨R, hRK, hRn, hRp, hPP'.trans hP'R⟩

theorem glaPPrimeCore_eq_bot_of_isSubnormal {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hY : GLAPPrimeCore p Y = ⊥) {S : Subgroup Y}
    (hS : CFSG.Open.IsSubnormal S ⊤) : GLAPPrimeCore p ↥S = ⊥ := by
  have h1 := glaPPrimeCoreOf_le_of_isSubnormal p hS
  have h2 : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
    have hmap := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y)
    rw [hY] at hmap
    have : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 hmap
    unfold GLAPPrimeCoreOf
    rw [this, Subgroup.map_bot]
  rw [h2, le_bot_iff] at h1
  unfold GLAPPrimeCoreOf at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h1

theorem glaPPrimeCore_eq_bot_of_quasisimple {Y : Type*} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hc : Nat.card (Subgroup.center Y) = 3) :
    GLAPPrimeCore 3 Y = ⊥ := by
  obtain ⟨hperf, hsimple⟩ := hq
  set N := GLAPPrimeCore 3 Y with hN
  have hNn : N.Normal := inferInstance
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_gLAPPrimeCore_aux 3 Y
  set M : Subgroup (Y ⧸ Subgroup.center Y) := N.map (QuotientGroup.mk' (Subgroup.center Y)) with hM
  have hMn : M.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal M with h | h
  ·
    have hNZ : N ≤ Subgroup.center Y := by
      intro n hn
      have : QuotientGroup.mk' (Subgroup.center Y) n ∈ M := ⟨n, hn, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff n).1 this
    have hd : Nat.card N ∣ 3 := by
      rw [← hc]
      exact Subgroup.card_dvd_of_le hNZ
    have h1 : Nat.card N = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hd
    exact Subgroup.eq_bot_of_card_eq N h1
  ·
    exfalso
    have hcomm : commutator Y ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [commutatorElement_def]
      have h1 : QuotientGroup.mk' (Subgroup.center Y) g₁ ∈ M := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨n₁, hn₁, e₁⟩ := h1
      have hz₁ : n₁⁻¹ * g₁ ∈ Subgroup.center Y := QuotientGroup.eq.1 e₁
      have hz : ∀ y : Y, y * (n₁⁻¹ * g₁) = (n₁⁻¹ * g₁) * y := Subgroup.mem_center_iff.1 hz₁
      have e : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = n₁ * (g₂ * n₁⁻¹ * g₂⁻¹) := by
        have hg : g₁ = n₁ * (n₁⁻¹ * g₁) := by group
        have h2 : (n₁⁻¹ * g₁) * g₂ * (n₁⁻¹ * g₁)⁻¹ = g₂ := by
          rw [← hz g₂]; group
        calc g₁ * g₂ * g₁⁻¹ * g₂⁻¹
            = n₁ * ((n₁⁻¹ * g₁) * g₂ * (n₁⁻¹ * g₁)⁻¹) * n₁⁻¹ * g₂⁻¹ := by
              conv_lhs => rw [hg]
              group
          _ = n₁ * (g₂ * n₁⁻¹ * g₂⁻¹) := by rw [h2]; group
      rw [e]
      exact N.mul_mem hn₁ (hNn.conj_mem _ (N.inv_mem hn₁) g₂)
    have hNtop : N = ⊤ := by
      rw [eq_top_iff, ← hperf]; exact hcomm
    have hcopY : Nat.Coprime 3 (Nat.card Y) := by
      have := hcop
      rwa [hNtop, Subgroup.card_top] at this
    have hd : 3 ∣ Nat.card Y := by
      have := Subgroup.card_subgroup_dvd_card (Subgroup.center Y)
      rwa [hc] at this
    exact absurd (Nat.eq_one_of_dvd_coprimes hcopY (dvd_refl 3) hd) (by norm_num)

theorem mem_oPrimePOf_of_central_subnormal {G : Type*} [Group G] [Finite G] {C K : Subgroup G}
    (hKC : CFSG.Open.IsSubnormal K C) {b : G} (hbK : b ∈ K) (hb3 : b ^ 3 = 1)
    (hz : ∀ k ∈ K, k * b * k⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf 3 C) : b ∈ oPrimePOf 3 C := by
  have hKC' : K ≤ C := isSubnormal_le' hKC
  have hbC : b ∈ C := hKC' hbK
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  set bt : ↥C ⧸ GLAPPrimeCore 3 ↥C := π ⟨b, hbC⟩ with hbt
  have hKsn : CFSG.Open.IsSubnormal (barX 3 C K) ⊤ := by
    have h1 := isSubnormal_comap' C.subtype hKC
    rw [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at h1
    have h2 := isSubnormal_map' π h1
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at h2
  have hcent : ∀ g ∈ barX 3 C K, g * bt = bt * g := by
    rintro _ ⟨⟨k, hkC⟩, hk, rfl⟩
    have hk' : k ∈ K := Subgroup.mem_subgroupOf.1 hk
    have h1 := hz k hk'
    have h2 : (⟨k * b * k⁻¹ * b⁻¹, C.mul_mem (C.mul_mem (C.mul_mem hkC hbC) (C.inv_mem hkC))
        (C.inv_mem hbC)⟩ : ↥C) ∈ GLAPPrimeCore 3 ↥C := ((mem_gLAPPrimeCoreOf_iff 3 C _).1 h1).2
    have h3 : π ⟨k * b * k⁻¹ * b⁻¹, _⟩ = 1 := (QuotientGroup.eq_one_iff _).2 h2
    have h4 : π (⟨k, hkC⟩ * ⟨b, hbC⟩ * ⟨k, hkC⟩⁻¹ * ⟨b, hbC⟩⁻¹) = 1 := h3
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h4
    have h5 : π ⟨k, hkC⟩ * bt * (π ⟨k, hkC⟩)⁻¹ = bt := by
      have := mul_inv_eq_one.1 (show π ⟨k, hkC⟩ * bt * (π ⟨k, hkC⟩)⁻¹ * bt⁻¹ = 1 from h4)
      exact this
    calc π ⟨k, hkC⟩ * bt = π ⟨k, hkC⟩ * bt * (π ⟨k, hkC⟩)⁻¹ * π ⟨k, hkC⟩ := by group
      _ = bt * π ⟨k, hkC⟩ := by rw [h5]
  have hbtK : bt ∈ barX 3 C K := ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbK, rfl⟩
  have hbt3 : bt ^ 3 = 1 := by
    rw [hbt, ← map_pow]
    have : (⟨b, hbC⟩ : ↥C) ^ 3 = 1 := Subtype.ext hb3
    rw [this, map_one]
  have hP3 : IsPGroup 3 (Subgroup.zpowers bt) := by
    have hord : orderOf bt ∣ 3 := orderOf_dvd_of_pow_eq_one hbt3
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
    · refine IsPGroup.iff_card.2 ⟨0, ?_⟩
      rw [Nat.card_zpowers, h]; simp
    · refine IsPGroup.iff_card.2 ⟨1, ?_⟩
      rw [Nat.card_zpowers, h]; simp
  have hPle : Subgroup.zpowers bt ≤ barX 3 C K := (Subgroup.zpowers_le).2 hbtK
  have hconjg : ∀ g ∈ barX 3 C K, ∀ y ∈ Subgroup.zpowers bt, g * y * g⁻¹ ∈ Subgroup.zpowers bt := by
    intro g hg y hy
    have hc : g * bt = bt * g := hcent g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have : g * bt ^ i * g⁻¹ = bt ^ i := by
      rw [(Commute.zpow_right (show Commute g bt from hc) i).eq]; group
    rw [this]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers bt) i
  have hPn : barX 3 C K ≤ Subgroup.normalizer (Subgroup.zpowers bt : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconjg g hg y hy, fun hy => ?_⟩
    have := hconjg g⁻¹ ((barX 3 C K).inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hPnorm : ((Subgroup.zpowers bt).subgroupOf (barX 3 C K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).2 hPn
  have hPsn : CFSG.Open.IsSubnormal (Subgroup.zpowers bt) ⊤ :=
    CFSG.Open.IsSubnormal.step hPle hPnorm hKsn
  obtain ⟨R, -, hRn, hRp, hPR⟩ := exists_normal_pGroup_of_isSubnormal 3 hPsn
    (Subgroup.zpowers bt) le_rfl (Subgroup.le_normalizer) hP3
  have hRnormal : R.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_le_iff.1 hRn
  have hbtR : bt ∈ CFSG.pCore 3 (↥C ⧸ GLAPPrimeCore 3 ↥C) :=
    le_sSup (show R ∈ {K : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) | K.Normal ∧ IsPGroup 3 K} from
      ⟨hRnormal, hRp⟩) (hPR (Subgroup.mem_zpowers bt))
  exact ⟨⟨b, hbC⟩, hbtR, rfl⟩

theorem isCatalogGroup_of_isKGroup_of_surjective {X : Type*} [Group X] (hX : CFSG.Open.IsKGroup X)
    (K : Subgroup X) {S : Type*} [Group S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (φ : K →* S) (hφ : Function.Surjective φ) : CFSG.Open.IsCatalogGroup S :=
  CFSG.KCore.KGroupNonab.catalogue_of_surjective_transfer CFSG.Open.isCatalogGroup_isoTransfer hX K
    hnab φ hφ

theorem isKGroup_subgroup_quotient {X : Type} [Group X] (hX : CFSG.Open.IsKGroup X)
    (M : Subgroup X) [M.Normal] (S : Subgroup (X ⧸ M)) : CFSG.Open.IsKGroup ↥S :=
  (hX.quotient M).subgroup S

theorem isQuasisimple_of_surjective_of_nontrivial {Q R : Type*} [Group Q] [Group R]
    (hQ : CFSG.Open.IsQuasisimple Q) (f : Q →* R) (hf : Function.Surjective f)
    [Nontrivial R] : CFSG.Open.IsQuasisimple R := by
  obtain ⟨hperf, hsimple⟩ := hQ
  have hRperf : commutator R = ⊤ := by
    have h1 : (commutator Q).map f = commutator R := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective f hf]
    rw [← h1, hperf, Subgroup.map_top_of_surjective f hf]
  refine ⟨hRperf, ?_⟩
  let ψ : Q →* R ⧸ Subgroup.center R := (QuotientGroup.mk' (Subgroup.center R)).comp f
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hf
  have hZle : Subgroup.center Q ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (Subgroup.center R) (f z) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro r
    obtain ⟨q, rfl⟩ := hf r
    rw [← map_mul, ← map_mul, hz q]
  have hker : ψ.ker = Subgroup.center Q := by
    set M : Subgroup (Q ⧸ Subgroup.center Q) := ψ.ker.map (QuotientGroup.mk' (Subgroup.center Q))
    have hMn : M.Normal := (inferInstance : ψ.ker.Normal).map _ (QuotientGroup.mk'_surjective _)
    rcases hsimple.eq_bot_or_eq_top_of_normal M with h | h
    · refine le_antisymm (fun k hk => ?_) hZle
      have : QuotientGroup.mk' (Subgroup.center Q) k ∈ M := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff k).1 this
    · exfalso
      have hall : ∀ q : Q, ψ q = 1 := by
        intro q
        have h1 : QuotientGroup.mk' (Subgroup.center Q) q ∈ M := by
          rw [h]; exact Subgroup.mem_top _
        obtain ⟨k, hk, e⟩ := h1
        have hz : k⁻¹ * q ∈ Subgroup.center Q := QuotientGroup.eq.1 e
        have hq : q = k * (k⁻¹ * q) := by group
        rw [hq, map_mul, (MonoidHom.mem_ker.1 hk), one_mul]
        exact MonoidHom.mem_ker.1 (hZle hz)
      have hRcentral : ∀ r : R, r ∈ Subgroup.center R := by
        intro r
        obtain ⟨q, rfl⟩ := hf r
        have := hall q
        change QuotientGroup.mk' (Subgroup.center R) (f q) = 1 at this
        exact (QuotientGroup.eq_one_iff _).1 this
      have hcomm : commutator R = ⊥ := by
        rw [commutator_def]
        exact Subgroup.commutator_top_right_eq_bot_iff_le_center.2 (fun r _ => hRcentral r)
      rw [hRperf] at hcomm
      obtain ⟨x, hx⟩ := exists_ne (1 : R)
      have hxt : x ∈ (⊤ : Subgroup R) := Subgroup.mem_top x
      rw [hcomm, Subgroup.mem_bot] at hxt
      exact hx hxt
  have := hsimple
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm.isSimpleGroup

theorem isQuasisimple_barOf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X L : Subgroup G} (hL : GLAPComponent p X L) (hnt : Nontrivial (barOf p L)) :
    CFSG.Open.IsQuasisimple (barOf p L) := by
  have hQ : CFSG.Open.IsQuasisimple ↥(barX p X L) := hL.2.2.1.2.2
  let f0 : ↥L →* ↥(barX p X L) :=
    ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp
      (Subgroup.inclusion hL.1 : ↥L →* ↥X)).codRestrict (barX p X L)
      (fun x => ⟨⟨x, hL.1 x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)
  have hf0 : Function.Surjective f0 := by
    rintro ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩⟩
    exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩
  let g : ↥L →* barOf p L := QuotientGroup.mk' (GLAPPrimeCore p ↥L)
  have hker : f0.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) (⟨(x : G), hL.1 x.2⟩ : ↥X) = 1 :=
      congrArg Subtype.val hx
    have h2 : (⟨(x : G), hL.1 x.2⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : (x : G) ∈ GLAPPrimeCoreOf p X := ⟨⟨(x : G), hL.1 x.2⟩, h2, rfl⟩
    have h4 : (x : G) ∈ GLAPPrimeCoreOf p L := by
      have := gLAPPrimeCoreOf_inf_le hp X L ⟨h3, x.2⟩
      rwa [inf_eq_right.2 hL.1] at this
    exact (QuotientGroup.eq_one_iff x).2 ((mem_gLAPPrimeCoreOf_iff p L x).1 h4).2
  let f1 : ↥(barX p X L) →* barOf p L :=
    (QuotientGroup.lift f0.ker g hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective f0 hf0).symm.toMonoidHom
  have hf1 : Function.Surjective f1 := by
    intro r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) r
    refine ⟨f0 l, ?_⟩
    show (QuotientGroup.lift f0.ker g hker)
      ((QuotientGroup.quotientKerEquivOfSurjective f0 hf0).symm (f0 l)) = _
    have : (QuotientGroup.quotientKerEquivOfSurjective f0 hf0).symm (f0 l) =
        (QuotientGroup.mk l : ↥L ⧸ f0.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this, QuotientGroup.lift_mk]
  exact isQuasisimple_of_surjective_of_nontrivial hQ f1 hf1

theorem barX_isSubnormal_top {G : Type*} [Group G] (p : ℕ) {X J : Subgroup G}
    (hJ : CFSG.Open.IsSubnormal J X) : CFSG.Open.IsSubnormal (barX p X J) ⊤ := by
  have h1 := isSubnormal_comap' X.subtype hJ
  rw [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at h1
  have h2 := isSubnormal_map' (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) h1
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2

theorem inf_gLAPPrimeCoreOf_eq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup G} (hJ : CFSG.Open.IsSubnormal J X) :
    J ⊓ GLAPPrimeCoreOf p X = GLAPPrimeCoreOf p J := by
  have hJX := isSubnormal_le' hJ
  refine le_antisymm ?_ (le_inf (gLAPPrimeCoreOf_le p J) (glaPPrimeCoreOf_le_of_isSubnormal p hJ))
  intro y hy
  have := gLAPPrimeCoreOf_inf_le hp X J ⟨hy.2, hy.1⟩
  rwa [inf_eq_right.2 hJX] at this

noncomputable def barXHom {G : Type*} [Group G] (p : ℕ) {X J : Subgroup G} (hJX : J ≤ X) :
    ↥J →* ↥(barX p X J) :=
  ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion hJX)).codRestrict
    (barX p X J) (fun x => ⟨⟨x, hJX x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)

theorem barXHom_surjective {G : Type*} [Group G] (p : ℕ) {X J : Subgroup G} (hJX : J ≤ X) :
    Function.Surjective (barXHom p hJX) := by
  rintro ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩⟩
  exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩

theorem barXHom_ker {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : CFSG.Open.IsSubnormal J X) :
    (barXHom p (isSubnormal_le' hJ)).ker = GLAPPrimeCore p ↥J := by
  ext x
  rw [MonoidHom.mem_ker]
  have h1 : barXHom p (isSubnormal_le' hJ) x = 1 ↔
      (⟨(x : G), isSubnormal_le' hJ x.2⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
    rw [← QuotientGroup.eq_one_iff]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [h1]
  have h2 : (⟨(x : G), isSubnormal_le' hJ x.2⟩ : ↥X) ∈ GLAPPrimeCore p ↥X ↔
      (x : G) ∈ GLAPPrimeCoreOf p X := by
    rw [mem_gLAPPrimeCoreOf_iff]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  rw [h2]
  have h3 : (x : G) ∈ GLAPPrimeCoreOf p X ↔ (x : G) ∈ GLAPPrimeCoreOf p J := by
    rw [← inf_gLAPPrimeCoreOf_eq hp hJ]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [h3, mem_gLAPPrimeCoreOf_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

noncomputable def barXEquiv {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup G} (hJ : CFSG.Open.IsSubnormal J X) : barOf p J ≃* ↥(barX p X J) :=
  (QuotientGroup.quotientMulEquivOfEq (barXHom_ker hp hJ)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (barXHom_surjective p (isSubnormal_le' hJ)))

theorem isQuasisimple_barX_iff {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup G} (hJ : CFSG.Open.IsSubnormal J X) :
    CFSG.Open.IsQuasisimple ↥(barX p X J) ↔ CFSG.Open.IsQuasisimple (barOf p J) :=
  ⟨fun h => CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (barXEquiv hp hJ).symm h,
   fun h => CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (barXEquiv hp hJ) h⟩

theorem barX_eq_iff_cov {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X J J' : Subgroup G} (hJ : CFSG.Open.IsSubnormal J X) (hJ'J : J' ≤ J) :
    barX p X J' = barX p X J ↔ ∀ j ∈ J, ∃ j' ∈ J', j'⁻¹ * j ∈ GLAPPrimeCoreOf p J := by
  have hJX := isSubnormal_le' hJ
  have hmono : barX p X J' ≤ barX p X J :=
    Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.2 (hJ'J (Subgroup.mem_subgroupOf.1 hx))
  constructor
  · intro h j hj
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j, hJX hj⟩ ∈ barX p X J' := by
      rw [h]; exact ⟨⟨j, hJX hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    obtain ⟨⟨j', hj'X⟩, hj', e⟩ := hmem
    have hj'J' : j' ∈ J' := Subgroup.mem_subgroupOf.1 hj'
    refine ⟨j', hj'J', ?_⟩
    have h1 : (⟨j', hj'X⟩ : ↥X)⁻¹ * ⟨j, hJX hj⟩ ∈ GLAPPrimeCore p ↥X := QuotientGroup.eq.1 e
    have h2 : j'⁻¹ * j ∈ GLAPPrimeCoreOf p X := (mem_gLAPPrimeCoreOf_iff p X _).2
      ⟨X.mul_mem (X.inv_mem hj'X) (hJX hj), h1⟩
    rw [← inf_gLAPPrimeCoreOf_eq hp hJ]
    exact ⟨J.mul_mem (J.inv_mem (hJ'J hj'J')) hj, h2⟩
  · intro h
    refine le_antisymm hmono ?_
    rintro _ ⟨⟨j, hjX⟩, hj, rfl⟩
    have hj' : j ∈ J := Subgroup.mem_subgroupOf.1 hj
    obtain ⟨j', hj'J', hc⟩ := h j hj'
    refine ⟨⟨j', hJX (hJ'J hj'J')⟩, Subgroup.mem_subgroupOf.2 hj'J', ?_⟩
    have hc' : j'⁻¹ * j ∈ GLAPPrimeCoreOf p X := by
      have := glaPPrimeCoreOf_le_of_isSubnormal p hJ hc
      exact this
    have h5 : (⟨j', hJX (hJ'J hj'J')⟩ : ↥X)⁻¹ * ⟨j, hjX⟩ ∈ GLAPPrimeCore p ↥X :=
      ((mem_gLAPPrimeCoreOf_iff p X _).1 hc').2
    exact QuotientGroup.eq.2 h5

theorem glaPComponent_down {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X Z J : Subgroup G} (hJ : GLAPComponent p X J) (hJZ : J ≤ Z) (hZX : Z ≤ X) :
    GLAPComponent p Z J := by
  have hJsnZ : CFSG.Open.IsSubnormal J Z := isSubnormal_of_le_of_le hJ.2.1 hJZ hZX
  refine ⟨hJZ, hJsnZ, ⟨le_top, barX_isSubnormal_top p hJsnZ, ?_⟩, ?_⟩
  · have hq : CFSG.Open.IsQuasisimple ↥(barX p X J) := hJ.2.2.1.2.2
    exact (isQuasisimple_barX_iff hp hJsnZ).2 ((isQuasisimple_barX_iff hp hJ.2.1).1 hq)
  · intro J' hlt hJ'sn heq
    have hJ'J : J' ≤ J := hlt.le
    have hJ'sn : CFSG.Open.IsSubnormal J' J := isSubnormal_of_le_of_le hJ'sn hJ'J hJZ
    have hJ'X : CFSG.Open.IsSubnormal J' X := isSubnormal_trans' hJ'sn hJ.2.1
    exact hJ.2.2.2 J' hlt hJ'X
      ((barX_eq_iff_cov hp hJ.2.1 hJ'J).2 ((barX_eq_iff_cov hp hJsnZ hJ'J).1 heq))

theorem glaPComponent_up {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X Z J : Subgroup G} (hJ : GLAPComponent p Z J) (hZX : Z ≤ X)
    (hsn : CFSG.Open.IsSubnormal J X) : GLAPComponent p X J := by
  refine ⟨hJ.1.trans hZX, hsn, ⟨le_top, barX_isSubnormal_top p hsn, ?_⟩, ?_⟩
  · have hq : CFSG.Open.IsQuasisimple ↥(barX p Z J) := hJ.2.2.1.2.2
    exact (isQuasisimple_barX_iff hp hsn).2 ((isQuasisimple_barX_iff hp hJ.2.1).1 hq)
  · intro J' hlt hJ'sn heq
    have hJ'J : J' ≤ J := hlt.le
    have hJ'Z : CFSG.Open.IsSubnormal J' Z :=
      isSubnormal_of_le_of_le hJ'sn (hJ'J.trans hJ.1) hZX
    exact hJ.2.2.2 J' hlt hJ'Z
      ((barX_eq_iff_cov hp hJ.2.1 hJ'J).2 ((barX_eq_iff_cov hp hsn hJ'J).1 heq))

theorem map_gLAPPrimeCore_le' {A B : Type*} [Group A] [Group B] [Finite A] (p : ℕ) (f : A →* B)
    (hf : Function.Surjective f) : (GLAPPrimeCore p A).map f ≤ GLAPPrimeCore p B := by
  have hn : ((GLAPPrimeCore p A).map f).Normal := (GLAPPrimeCore.normal p A).map f hf
  have hc : Nat.Coprime p (Nat.card ((GLAPPrimeCore p A).map f)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) (coprime_card_gLAPPrimeCore_aux p A)
  exact le_sSup (show (GLAPPrimeCore p A).map f ∈
    {N : Subgroup B | N.Normal ∧ Nat.Coprime p (Nat.card N)} from ⟨hn, hc⟩)

theorem barX_eq_top_iff {G : Type*} [Group G] (p : ℕ) {X K : Subgroup G} (hKX : K ≤ X) :
    barX p X K = ⊤ ↔ ∀ h ∈ X, ∃ k ∈ K, k⁻¹ * h ∈ GLAPPrimeCoreOf p X := by
  constructor
  · intro htop h hh
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨h, hh⟩ ∈ barX p X K := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨⟨k, hkX⟩, hk, e⟩ := hmem
    refine ⟨k, Subgroup.mem_subgroupOf.1 hk, ?_⟩
    have h1 : (⟨k, hkX⟩ : ↥X)⁻¹ * ⟨h, hh⟩ ∈ GLAPPrimeCore p ↥X := QuotientGroup.eq.1 e
    exact (mem_gLAPPrimeCoreOf_iff p X _).2 ⟨X.mul_mem (X.inv_mem hkX) hh, h1⟩
  · intro h
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨⟨y, hyX⟩, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥X) z
    obtain ⟨k, hk, hc⟩ := h y hyX
    refine ⟨⟨k, hKX hk⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
    exact QuotientGroup.eq.2 ((mem_gLAPPrimeCoreOf_iff p X _).1 hc).2

theorem gLAPPrimeCoreOf_eq_inf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {L H : Subgroup G} (hHL : H ≤ L) (hF : GLAPPrimeCore p ↥(barX p L H) = ⊥) :
    GLAPPrimeCoreOf p H = H ⊓ GLAPPrimeCoreOf p L := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨hyH, hy'⟩ := (mem_gLAPPrimeCoreOf_iff p H y).1 hy
    refine ⟨hyH, ?_⟩
    have h1 := map_gLAPPrimeCore_le' p (barXHom p hHL) (barXHom_surjective p hHL)
    have h2 : barXHom p hHL ⟨y, hyH⟩ ∈ GLAPPrimeCore p ↥(barX p L H) := h1 (Subgroup.mem_map.2 ⟨⟨y, hyH⟩, hy', rfl⟩)
    rw [hF, Subgroup.mem_bot] at h2
    have h3 : (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) ⟨y, hHL hyH⟩ = 1 := congrArg Subtype.val h2
    exact (mem_gLAPPrimeCoreOf_iff p L y).2 ⟨hHL hyH, (QuotientGroup.eq_one_iff _).1 h3⟩
  · intro y hy
    have := gLAPPrimeCoreOf_inf_le hp L H ⟨hy.2, hy.1⟩
    rwa [inf_eq_right.2 hHL] at this

theorem exists_J0 {G : Type*} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hFq : CFSG.Open.IsQuasisimple ↥(barX 3 L (L ⊓ Cen x)))
    (hZ : Nat.card (Subgroup.center ↥(barX 3 L (L ⊓ Cen x))) = 3) :
    ∃ J₀ : Subgroup G, GLAPComponent 3 (L ⊓ Cen x) J₀ ∧ barX 3 (L ⊓ Cen x) J₀ = ⊤ ∧
      barX 3 L J₀ = barX 3 L (L ⊓ Cen x) ∧
      ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) → g * x = x * g →
        g ∈ Subgroup.normalizer (J₀ : Set G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set H : Subgroup G := L ⊓ Cen x with hH
  have hHL : H ≤ L := inf_le_left
  have hFcore : GLAPPrimeCore 3 ↥(barX 3 L H) = ⊥ := glaPPrimeCore_eq_bot_of_quasisimple hFq hZ
  have hcoreEq := gLAPPrimeCoreOf_eq_inf hp hHL hFcore
  let f := barXHom 3 hHL
  have hf : Function.Surjective f := barXHom_surjective 3 hHL
  have hker : f.ker = GLAPPrimeCore 3 ↥H := by
    ext y
    rw [MonoidHom.mem_ker]
    have h1 : f y = 1 ↔ (⟨(y : G), hHL y.2⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := by
      rw [← QuotientGroup.eq_one_iff]
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [h1]
    have h2 : (⟨(y : G), hHL y.2⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L ↔ (y : G) ∈ GLAPPrimeCoreOf 3 L := by
      rw [mem_gLAPPrimeCoreOf_iff]
      exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
    rw [h2]
    have h3 : (y : G) ∈ GLAPPrimeCoreOf 3 L ↔ (y : G) ∈ GLAPPrimeCoreOf 3 H := by
      rw [hcoreEq]; exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
    rw [h3, mem_gLAPPrimeCoreOf_iff]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨y.2, h⟩⟩
  let e : (↥H ⧸ GLAPPrimeCore 3 ↥H) ≃* ↥(barX 3 L H) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hQq : CFSG.Open.IsQuasisimple (↥H ⧸ GLAPPrimeCore 3 ↥H) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hFq
  have hcomp : CFSG.Open.IsComponentOf (⊤ : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H)) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H)) ≃* _).symm hQq⟩
  obtain ⟨J₀, hJ0, hJ0top⟩ := exists_glaPComponent_barX_eq (p := 3) H hcomp
  have hJ0H : J₀ ≤ H := hJ0.1
  have hcov := (barX_eq_top_iff 3 hJ0H).1 hJ0top
  refine ⟨J₀, hJ0, hJ0top, ?_, ?_⟩
  · refine le_antisymm
      (Subgroup.map_mono fun z hz => Subgroup.mem_subgroupOf.2
        (hJ0H (Subgroup.mem_subgroupOf.1 hz))) ?_
    rintro _ ⟨⟨h, hhL⟩, hh, rfl⟩
    have hhH : h ∈ H := Subgroup.mem_subgroupOf.1 hh
    obtain ⟨k, hk, hkc⟩ := hcov h hhH
    have hkc' : k⁻¹ * h ∈ GLAPPrimeCoreOf 3 L := by
      have : k⁻¹ * h ∈ GLAPPrimeCoreOf 3 H := hkc
      rw [hcoreEq] at this
      exact this.2
    refine ⟨⟨k, hHL (hJ0H hk)⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
    exact QuotientGroup.eq.2 ((mem_gLAPPrimeCoreOf_iff 3 L _).1 hkc').2
  · intro g hgL hgx
    have hgC : g ∈ Subgroup.normalizer (Cen x : Set G) := by
      rw [mem_normalizer_iff_gLBConj_eq]
      exact gLBConj_centralizer_singleton_of_commute hgx
    have hgH : g ∈ Subgroup.normalizer (H : Set G) := by
      rw [mem_normalizer_iff_gLBConj_eq] at hgL hgC ⊢
      ext y
      rw [mem_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf]
      have h1 : g * y * g⁻¹ ∈ L ↔ y ∈ L := by
        rw [← mem_gLBConj, hgL]
      have h2 : g * y * g⁻¹ ∈ Cen x ↔ y ∈ Cen x := by
        rw [← mem_gLBConj, hgC]
      rw [h1, h2]
    have hgH' : GLBConj g H = H := mem_normalizer_iff_gLBConj_eq.1 hgH
    have hcomp' : GLAPComponent 3 H (GLBConj g J₀) := by
      have := glaPComponent_gLBConj g hJ0
      rwa [hgH'] at this
    have hKH : GLBConj g J₀ ≤ H := hcomp'.1
    have hKtop : barX 3 H (GLBConj g J₀) = ⊤ := by
      rw [barX_eq_top_iff 3 hKH]
      intro h hh
      have hh' : g * h * g⁻¹ ∈ H := by
        have : h ∈ GLBConj g H := by rw [hgH']; exact hh
        exact (mem_gLBConj).1 this
      obtain ⟨j₀, hj₀, hc⟩ := hcov _ hh'
      refine ⟨g⁻¹ * j₀ * g, ?_, ?_⟩
      · rw [mem_gLBConj]
        have e : g * (g⁻¹ * j₀ * g) * g⁻¹ = j₀ := by group
        rw [e]; exact hj₀
      · have := (Subgroup.mem_normalizer_iff.1
          (mem_normalizer_gLAPPrimeCoreOf 3 (inv_mem hgH)) _).1 hc
        convert this using 1
        group
    have := glaPComponent_uniqueAux hcomp' hJ0 (by rw [hKtop, hJ0top])
    rw [mem_normalizer_iff_gLBConj_eq]
    exact this

theorem barXHom_ker_le_core {G : Type*} [Group G] [Finite G] (p : ℕ) {X J : Subgroup G}
    (hJX : J ≤ X) : (barXHom p hJX).ker ≤ GLAPPrimeCore p ↥J := by
  set K := (barXHom p hJX).ker with hK
  have hmem : ∀ x ∈ K, (x : G) ∈ GLAPPrimeCoreOf p X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h3 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ⟨(x : G), hJX x.2⟩ = 1 :=
      congrArg Subtype.val hx
    exact (mem_gLAPPrimeCoreOf_iff p X _).2 ⟨hJX x.2, (QuotientGroup.eq_one_iff _).1 h3⟩
  have hle : K.map J.subtype ≤ GLAPPrimeCoreOf p X := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x hx
  have hcop : Nat.Coprime p (Nat.card K) := by
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card (K.map J.subtype) = Nat.card K :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 (card_gLAPPrimeCoreOf_coprime p X)
  exact le_sSup (show K ∈ {N : Subgroup ↥J | N.Normal ∧ Nat.Coprime p (Nat.card N)} from
    ⟨inferInstance, hcop⟩)

theorem exists_equiv_barOf_barX {G : Type*} [Group G] [Finite G] {L C J₀ : Subgroup G}
    (hJL : J₀ ≤ L) (hJC : J₀ ≤ C) (hF : GLAPPrimeCore 3 ↥(barX 3 L J₀) = ⊥) :
    ∃ e : barOf 3 (barX 3 C J₀) ≃* ↥(barX 3 L J₀),
      (∀ (j : G) (hj : j ∈ J₀),
        ((e (QuotientGroup.mk
            (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨j, hJC hj⟩,
              ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩⟩ : ↥(barX 3 C J₀))) :
          ↥(barX 3 L J₀)) : barOf 3 L) = QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨j, hJL hj⟩) ∧
      ∀ (a : G) (haC : a ∈ C) (haL : a ∈ Subgroup.normalizer (L : Set G))
        (_haJ : a ∈ Subgroup.normalizer (J₀ : Set G)) (ρ : MulAut ↥(barX 3 L J₀)),
        (∀ y : ↥(barX 3 L J₀), ((ρ y : ↥(barX 3 L J₀)) : barOf 3 L) = barAut 3 L ⟨a, haL⟩ y) →
        IsFieldAutThree ρ →
        InducesFieldAut 3 (barX 3 C J₀) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩) := by
  set φ := barXHom 3 hJL with hφ
  set ψ0 := barXHom 3 hJC with hψ0
  have hφs : Function.Surjective φ := barXHom_surjective 3 hJL
  have hψs : Function.Surjective ψ0 := barXHom_surjective 3 hJC
  have hkerφ : φ.ker = GLAPPrimeCore 3 ↥J₀ := by
    refine le_antisymm (barXHom_ker_le_core 3 hJL) ?_
    intro y hy
    have h1 := map_gLAPPrimeCore_le' 3 φ hφs (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    rw [hF, Subgroup.mem_bot] at h1
    exact h1
  have hk : ψ0.ker ≤ φ.ker := hkerφ ▸ barXHom_ker_le_core 3 hJC
  let φ' : ↥(barX 3 C J₀) →* ↥(barX 3 L J₀) :=
    (QuotientGroup.lift ψ0.ker φ hk).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ0 hψs).symm.toMonoidHom
  have hφ' : ∀ j : ↥J₀, φ' (ψ0 j) = φ j := by
    intro j
    show (QuotientGroup.lift ψ0.ker φ hk)
      ((QuotientGroup.quotientKerEquivOfSurjective ψ0 hψs).symm (ψ0 j)) = _
    have : (QuotientGroup.quotientKerEquivOfSurjective ψ0 hψs).symm (ψ0 j) =
        (QuotientGroup.mk j : ↥J₀ ⧸ ψ0.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this, QuotientGroup.lift_mk]
  have hφ's : Function.Surjective φ' := by
    intro y
    obtain ⟨j, rfl⟩ := hφs y
    exact ⟨ψ0 j, hφ' j⟩
  have hO1 : GLAPPrimeCore 3 ↥(barX 3 C J₀) ≤ φ'.ker := by
    intro y hy
    have h1 := map_gLAPPrimeCore_le' 3 φ' hφ's (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    rw [hF, Subgroup.mem_bot] at h1
    exact h1
  have hO2 : φ'.ker ≤ GLAPPrimeCore 3 ↥(barX 3 C J₀) := by
    intro y hy
    obtain ⟨j, rfl⟩ := hψs y
    rw [MonoidHom.mem_ker, hφ'] at hy
    have : j ∈ GLAPPrimeCore 3 ↥J₀ := hkerφ ▸ hy
    exact map_gLAPPrimeCore_le' 3 ψ0 hψs (Subgroup.mem_map.2 ⟨j, this, rfl⟩)
  let φ'' : barOf 3 (barX 3 C J₀) →* ↥(barX 3 L J₀) :=
    QuotientGroup.lift (GLAPPrimeCore 3 ↥(barX 3 C J₀)) φ' hO1
  have hφ'' : ∀ x, φ'' (QuotientGroup.mk x) = φ' x := fun x => QuotientGroup.lift_mk _ _ x
  have hinj : Function.Injective φ'' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [MonoidHom.mem_ker, hφ''] at hw
    have : x ∈ GLAPPrimeCore 3 ↥(barX 3 C J₀) := hO2 hw
    exact (QuotientGroup.eq_one_iff x).2 this
  have hsurj : Function.Surjective φ'' := by
    intro y
    obtain ⟨x, rfl⟩ := hφ's y
    exact ⟨QuotientGroup.mk x, hφ'' x⟩
  let e : barOf 3 (barX 3 C J₀) ≃* ↥(barX 3 L J₀) := MulEquiv.ofBijective φ'' ⟨hinj, hsurj⟩
  have he : ∀ x, e (QuotientGroup.mk x) = φ' x := fun x => hφ'' x
  refine ⟨e, ?_, ?_⟩
  · intro j hj
    have := he (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨j, hJC hj⟩,
      ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩⟩ : ↥(barX 3 C J₀))
    rw [this]
    exact congrArg (fun z : ↥(barX 3 L J₀) => (z : barOf 3 L)) (hφ' ⟨j, hj⟩)
  · intro a haC haL haJ ρ hρ hρf
    have hnorm : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩ ∈
        Subgroup.normalizer (barX 3 C J₀ : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
      have := barX_le_normalizer (p := 3) (C := C) (S := J₀) (T := Subgroup.zpowers a)
        (Subgroup.zpowers_le.2 haJ)
      exact this ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers a), rfl⟩
    refine ⟨hnorm, ?_⟩
    refine isFieldAutThree_congr e.symm (α := ρ)
      (α' := barAut 3 (barX 3 C J₀) ⟨_, hnorm⟩) ?_ hρf
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [MulEquiv.symm_apply_apply, ← MulEquiv.symm_apply_apply e
      (barAut 3 (barX 3 C J₀) ⟨_, hnorm⟩ w)]
    congr 1
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨j, rfl⟩ := hψs x
    have hj' : a * (j : G) * a⁻¹ ∈ J₀ := (Subgroup.mem_normalizer_iff.1 haJ j).1 j.2
    have h1 : (barAut 3 (barX 3 C J₀) ⟨_, hnorm⟩) (QuotientGroup.mk (ψ0 j)) =
        QuotientGroup.mk (ψ0 ⟨a * (j : G) * a⁻¹, hj'⟩) := by
      rw [barAut_mk]
      congr 1
    rw [h1, he, he, hφ', hφ']
    apply Subtype.ext
    rw [hρ]
    show barAut 3 L ⟨a, haL⟩ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨(j : G), hJL j.2⟩) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨a * (j : G) * a⁻¹, hJL hj'⟩
    exact barAut_mk 3 L ⟨a, haL⟩ ⟨(j : G), hJL j.2⟩

theorem barX_gLBConj' {G : Type*} [Group G] (p : ℕ) {C : Subgroup G} {g : G} (hg : g ∈ C)
    (K : Subgroup G) :
    barX p C (GLBConj g K) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨g, hg⟩) (barX p C K) := by
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  ext z
  rw [mem_gLBConj]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : (g : G) * (w : G) * g⁻¹ ∈ K := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hw)
    refine ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, Subgroup.mem_subgroupOf.2 hw', ?_⟩
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨w', hw', e⟩
    have hz : z = π (⟨g, hg⟩⁻¹ * w' * ⟨g, hg⟩) := by
      rw [map_mul, map_mul, map_inv, e]; group
    refine ⟨⟨g, hg⟩⁻¹ * w' * ⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ?_, hz.symm⟩
    rw [mem_gLBConj]
    have := Subgroup.mem_subgroupOf.1 hw'
    simpa [mul_assoc] using this

theorem not_diag {G : Type*} [Group G] [Finite G] {C J₀ L₁ L₂ L₃ : Subgroup G} {b : G}
    (hbJ : b ∈ J₀) (hJ : J₀ ≤ L₁ ⊔ L₂ ⊔ L₃)
    (h₁ : GLAPComponent 3 C L₁) (h₂ : GLAPComponent 3 C L₂) (h₃ : GLAPComponent 3 C L₃)
    (h12 : L₁ ≠ L₂) (h31 : L₃ ≠ L₁) (hb : GLBConj b L₁ = L₂) : False := by
  have hbC : b ∈ C := sup_le (sup_le h₁.1 h₂.1) h₃.1 (hJ hbJ)
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  have hcomm : ∀ {A B : Subgroup G}, GLAPComponent 3 C A → GLAPComponent 3 C B → A ≠ B →
      barX 3 C A ≤ Subgroup.centralizer (barX 3 C B : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
    intro A B hA hB hAB
    have hne : barX 3 C A ≠ barX 3 C B := fun h => hAB (glaPComponent_uniqueAux hA hB h)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA.2.2.1 hB.2.2.1 hne)
  have hsup : barX 3 C (L₁ ⊔ L₂ ⊔ L₃) = barX 3 C L₁ ⊔ barX 3 C L₂ ⊔ barX 3 C L₃ := by
    unfold barX
    rw [Subgroup.subgroupOf_sup (sup_le h₁.1 h₂.1) h₃.1, Subgroup.subgroupOf_sup h₁.1 h₂.1,
      Subgroup.map_sup, Subgroup.map_sup]
  have hπb : π ⟨b, hbC⟩ ∈ barX 3 C L₁ ⊔ barX 3 C L₂ ⊔ barX 3 C L₃ := by
    rw [← hsup]
    exact ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (hJ hbJ), rfl⟩
  have hnorm : π ⟨b, hbC⟩ ∈ Subgroup.normalizer (barX 3 C L₁ : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
    have h2 : barX 3 C L₂ ≤ Subgroup.normalizer (barX 3 C L₁ : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
      (hcomm h₂ h₁ h12.symm).trans (Subgroup.centralizer_le_normalizer _)
    have h3 : barX 3 C L₃ ≤ Subgroup.normalizer (barX 3 C L₁ : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
      (hcomm h₃ h₁ h31).trans (Subgroup.centralizer_le_normalizer _)
    exact sup_le (sup_le Subgroup.le_normalizer h2) h3 hπb
  have heq : barX 3 C (GLBConj b L₁) = barX 3 C L₁ := by
    rw [barX_gLBConj' 3 hbC]
    exact mem_normalizer_iff_gLBConj_eq.1 hnorm
  have hcomp : GLAPComponent 3 C (GLBConj b L₁) := by
    have := glaPComponent_gLBConj b h₁
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hbC : b ∈ Subgroup.normalizer (C : Set G))]
      at this
  have := glaPComponent_uniqueAux hcomp h₁ heq
  rw [hb] at this
  exact h12 this.symm

theorem conj_mem_oPrimePOf {G : Type*} [Group G] (p : ℕ) {M : Subgroup G} {l : G} (hl : l ∈ M)
    {y : G} (hy : y ∈ oPrimePOf p M) : l * y * l⁻¹ ∈ oPrimePOf p M := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨⟨l, hl⟩ * z * ⟨l, hl⟩⁻¹, (oPrimeP.normal p ↥M).conj_mem z hz ⟨l, hl⟩, rfl⟩

theorem oPrimePOf_le {G : Type*} [Group G] (p : ℕ) (M : Subgroup G) : oPrimePOf p M ≤ M :=
  Subgroup.map_subtype_le _

theorem exists_pow_mem_core_of_mem_oPrimePOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    {M : Subgroup G} {y : G} (hy : y ∈ oPrimePOf p M) :
    ∃ n : ℕ, y ^ (p ^ n) ∈ GLAPPrimeCoreOf p M := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' : QuotientGroup.mk' (GLAPPrimeCore p ↥M) z ∈ CFSG.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) := hz
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ GLAPPrimeCore p ↥M))
    ⟨_, hz'⟩
  refine ⟨n, ?_⟩
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) (z ^ (p ^ n)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  exact ⟨z ^ (p ^ n), (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem le_oPrimePOf_of_core {G : Type*} [Group G] [Finite G] {p : ℕ} {M S S₀ : Subgroup G}
    (hSM : S ≤ M) (hSn : M ≤ Subgroup.normalizer (S : Set G)) (hS₀n : M ≤ Subgroup.normalizer (S₀ : Set G))
    (hS₀M : S₀ ≤ M) (hcop : Nat.Coprime p (Nat.card S₀))
    (hpow : ∀ s ∈ S, ∃ n : ℕ, s ^ (p ^ n) ∈ S₀) : S ≤ oPrimePOf p M := by
  have hS₀le : S₀ ≤ GLAPPrimeCoreOf p M := by
    have hn : (S₀.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hS₀M).2 hS₀n
    have hc : Nat.Coprime p (Nat.card (S₀.subgroupOf M)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀M).toEquiv]
      exact hcop
    have hle : S₀.subgroupOf M ≤ GLAPPrimeCore p ↥M := le_sSup ⟨hn, hc⟩
    intro y hy
    exact ⟨⟨y, hS₀M hy⟩, hle (Subgroup.mem_subgroupOf.2 hy), rfl⟩
  have hSnorm : (S.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).2 hSn
  set S' : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) :=
    (S.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) with hS'
  have hS'n : S'.Normal := hSnorm.map _ (QuotientGroup.mk'_surjective _)
  have hS'p : IsPGroup p S' := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    obtain ⟨n, hn⟩ := hpow (s : G) (Subgroup.mem_subgroupOf.1 hs)
    refine ⟨n, Subtype.ext ?_⟩
    show (QuotientGroup.mk' (GLAPPrimeCore p ↥M) s) ^ (p ^ n) = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have : (s : G) ^ (p ^ n) ∈ GLAPPrimeCoreOf p M := hS₀le hn
    exact ((mem_gLAPPrimeCoreOf_iff p M _).1 this).2
  intro s hs
  have hsM : s ∈ M := hSM hs
  refine ⟨⟨s, hsM⟩, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨s, hsM⟩ ∈ CFSG.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)
  exact le_sSup (show S' ∈ {K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) | K.Normal ∧ IsPGroup p K} from
    ⟨hS'n, hS'p⟩) ⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩

theorem mem_normalizer_inf' {G : Type*} [Group G] {K S : Subgroup G} {a : G}
    (hK : a ∈ Subgroup.normalizer (K : Set G)) (hS : a ∈ Subgroup.normalizer (S : Set G)) :
    a ∈ Subgroup.normalizer ((K ⊓ S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hK hS ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hK y, hS y]

theorem mem_oPrimePOf_barX {G : Type*} [Group G] [Finite G] {C K : Subgroup G} {a b : G}
    (hKC : K ≤ C) (haC : a ∈ C) (ha3 : a ^ 3 = 1) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hbK : b ∈ K) (hbC : b ∈ C) (hb : b ∈ oPrimePOf 3 (Cen a)) :
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩) ∈
      oPrimePOf 3 (barX 3 C K ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩)} :
          Set (↥C ⧸ GLAPPrimeCore 3 ↥C))) := by
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  set M' : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) :=
    barX 3 C K ⊓ Subgroup.centralizer ({π ⟨a, haC⟩} : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) with hM'
  set R : Subgroup G := oPrimePOf 3 (Cen a) with hR
  set N : Subgroup G := GLAPPrimeCoreOf 3 (Cen a) with hN
  set D : Subgroup G := K ⊓ Cen a with hD
  have hDC : D ≤ C := inf_le_left.trans hKC
  have hM'D : ∀ m ∈ M', ∃ d ∈ D, ∃ hd : d ∈ C, π ⟨d, hd⟩ = m := by
    rintro m ⟨⟨⟨k, hkC⟩, hk, rfl⟩, hmc⟩
    have hk' : k ∈ K := Subgroup.mem_subgroupOf.1 hk
    have hcomm : π ⟨k, hkC⟩ * π ⟨a, haC⟩ = π ⟨a, haC⟩ * π ⟨k, hkC⟩ :=
      Subgroup.mem_centralizer_singleton_iff.1 hmc
    have h1 : π (⟨a, haC⟩ * ⟨k, hkC⟩ * ⟨a, haC⟩⁻¹ * ⟨k, hkC⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm]; group
    have h2 : a * k * a⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 C :=
      (mem_gLAPPrimeCoreOf_iff 3 C _).2
        ⟨C.mul_mem (C.mul_mem (C.mul_mem haC hkC) (C.inv_mem haC)) (C.inv_mem hkC),
          (QuotientGroup.eq_one_iff _).1 h1⟩
    have h3 : a * k * a⁻¹ * k⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 haK k).1 hk'
      exact K.mul_mem this (K.inv_mem hk')
    have hNC := le_normalizer_gLAPPrimeCoreOf 3 C
    have haN : a ∈ Subgroup.normalizer ((K ⊓ GLAPPrimeCoreOf 3 C : Subgroup G) : Set G) :=
      mem_normalizer_inf' haK (hNC haC)
    have hkN : k ∈ Subgroup.normalizer ((K ⊓ GLAPPrimeCoreOf 3 C : Subgroup G) : Set G) :=
      mem_normalizer_inf' (Subgroup.le_normalizer hk') (hNC hkC)
    have hcop : Nat.Coprime 3 (Nat.card (K ⊓ GLAPPrimeCoreOf 3 C : Subgroup G)) := by
      have h1 := Subgroup.card_dvd_of_le (inf_le_right : K ⊓ GLAPPrimeCoreOf 3 C ≤ _)
      exact Nat.Coprime.coprime_dvd_right h1 (card_gLAPPrimeCoreOf_coprime 3 C)
    obtain ⟨m, hm, hmc⟩ := exists_commute_mul ha3 haN hcop hkN ⟨h3, h2⟩
    refine ⟨k * m, ⟨K.mul_mem hk' hm.1, ?_⟩, C.mul_mem hkC (gLAPPrimeCoreOf_le 3 C hm.2), ?_⟩
    · show k * m ∈ Cen a
      exact Subgroup.mem_centralizer_singleton_iff.2 hmc.symm
    · have hmC : m ∈ C := gLAPPrimeCoreOf_le 3 C hm.2
      have hm1 : π ⟨m, hmC⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).2 ((mem_gLAPPrimeCoreOf_iff 3 C m).1 hm.2).2
      show π (⟨k, hkC⟩ * ⟨m, hmC⟩) = _
      rw [map_mul, hm1, mul_one]
  have hRle : R ≤ Cen a := oPrimePOf_le 3 _
  have hNle : N ≤ Cen a := gLAPPrimeCoreOf_le 3 _
  have hRD : R ⊓ D ≤ C := inf_le_right.trans hDC
  have hT : R ⊓ D ⊓ N ≤ C := inf_le_left.trans hRD
  set S : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C (R ⊓ D) with hS
  set S₀ : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C (R ⊓ D ⊓ N) with hS₀
  have hconj : ∀ (T : Subgroup G), T ≤ C → (∀ d ∈ D, ∀ t ∈ T, d * t * d⁻¹ ∈ T) →
      ∀ m ∈ M', ∀ y ∈ barX 3 C T, m * y * m⁻¹ ∈ barX 3 C T := by
    intro T hTC hTn m hm y hy
    obtain ⟨d, hdD, hdC, rfl⟩ := hM'D m hm
    obtain ⟨⟨t, htC⟩, ht, rfl⟩ := hy
    refine ⟨⟨d, hdC⟩ * ⟨t, htC⟩ * ⟨d, hdC⟩⁻¹, Subgroup.mem_subgroupOf.2
      (hTn d hdD t (Subgroup.mem_subgroupOf.1 ht)), ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hnorm_of : ∀ (T : Subgroup G), T ≤ C → (∀ d ∈ D, ∀ t ∈ T, d * t * d⁻¹ ∈ T) →
      M' ≤ Subgroup.normalizer (barX 3 C T : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
    intro T hTC hTn m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj T hTC hTn m hm y hy, fun hy => ?_⟩
    have := hconj T hTC hTn m⁻¹ (M'.inv_mem hm) _ hy
    simpa [mul_assoc] using this
  have hRDn : ∀ d ∈ D, ∀ t ∈ R ⊓ D, d * t * d⁻¹ ∈ R ⊓ D := by
    intro d hd t ht
    exact ⟨conj_mem_oPrimePOf 3 hd.2 ht.1,
      D.mul_mem (D.mul_mem hd ht.2) (D.inv_mem hd)⟩
  have hTn : ∀ d ∈ D, ∀ t ∈ R ⊓ D ⊓ N, d * t * d⁻¹ ∈ R ⊓ D ⊓ N := by
    intro d hd t ht
    exact ⟨hRDn d hd t ht.1, conj_mem_gLAPPrimeCoreOf 3 _ hd.2 ht.2⟩
  have hSM : S ≤ M' := by
    rintro _ ⟨⟨r, hrC⟩, hr, rfl⟩
    have hr' : r ∈ R ⊓ D := Subgroup.mem_subgroupOf.1 hr
    refine ⟨⟨⟨r, hrC⟩, Subgroup.mem_subgroupOf.2 hr'.2.1, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    show π ⟨r, hrC⟩ * π ⟨a, haC⟩ = π ⟨a, haC⟩ * π ⟨r, hrC⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hr'.2.2)
  have hS₀S : S₀ ≤ S := by
    refine Subgroup.map_mono fun z hz => Subgroup.mem_subgroupOf.2 ?_
    have := Subgroup.mem_subgroupOf.1 hz
    exact this.1
  have hcop : Nat.Coprime 3 (Nat.card S₀) := by
    have h1 : Nat.card S₀ ∣ Nat.card ((R ⊓ D ⊓ N).subgroupOf C) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ((R ⊓ D ⊓ N).subgroupOf C) = Nat.card (R ⊓ D ⊓ N : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
    have h3 : Nat.card (R ⊓ D ⊓ N : Subgroup G) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right (h1.trans h3) (card_gLAPPrimeCoreOf_coprime 3 _)
  have hpow : ∀ s ∈ S, ∃ n : ℕ, s ^ (3 ^ n) ∈ S₀ := by
    rintro _ ⟨⟨r, hrC⟩, hr, rfl⟩
    have hr' : r ∈ R ⊓ D := Subgroup.mem_subgroupOf.1 hr
    obtain ⟨n, hn⟩ := exists_pow_mem_core_of_mem_oPrimePOf hr'.1
    have hmem : (⟨r, hrC⟩ ^ (3 ^ n) : ↥C) ∈ (R ⊓ D ⊓ N).subgroupOf C :=
      Subgroup.mem_subgroupOf.2
        (show r ^ (3 ^ n) ∈ R ⊓ D ⊓ N from ⟨⟨R.pow_mem hr'.1 _, D.pow_mem hr'.2 _⟩, hn⟩)
    exact ⟨n, ⟨_, hmem, by rw [map_pow]⟩⟩
  have hle := le_oPrimePOf_of_core (p := 3) hSM (hnorm_of _ hRD hRDn) (hnorm_of _ hT hTn)
    (hS₀S.trans hSM) hcop hpow
  exact hle ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 ⟨hb, hbK, hRle hb⟩, rfl⟩

theorem card_rootsOfUnity_three' {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (rootsOfUnity 3 K) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  exact (IsPrimitiveRoot.iff_orderOf.mpr hζ).card_rootsOfUnity'

theorem card_center_statedSL_three' {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (Subgroup.center ↥(StatedSL 3 K)) = 3 := by
  show Nat.card (Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K)) = 3
  rw [← Nat.card_congr (Subgroup.centerCongr
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    Fintype.card_fin]
  exact card_rootsOfUnity_three' h3

theorem card_center_statedSU_three {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : q % 3 = 2) (hq2 : q ≠ 2) :
    Nat.card (Subgroup.center ↥(StatedSU 3 q K)) = 3 := by
  have hpp : IsPrimePow q := by
    have := Fintype.ofFinite K
    have h1 : IsPrimePow (Nat.card K) := by
      rw [Nat.card_eq_fintype_card]; exact FiniteField.isPrimePow_card K
    rw [hK] at h1
    exact (isPrimePow_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).1 h1
  obtain ⟨p, f, hp, hf, rfl⟩ := (isPrimePow_nat_iff q).1 hpp
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = (p ^ f) ^ 2 := hK
  have h1 := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := f) (n := 3) hK' le_rfl (fun h => hq2 (by simpa using congrArg Prod.snd h))
  have h2 := (CFSG.LinearGroups.unitary_scalar_kernel hp hK' (n := 3) (by norm_num)).2.2
  have hcen : Nat.card (Subgroup.center ↥(StatedSU 3 (p ^ f) K)) = 3 := by
    show Nat.card (Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) = 3
    rw [h1.2, h2]
    have : 3 ∣ p ^ f + 1 := by omega
    exact Nat.gcd_eq_left this
  exact hcen

theorem card_center_of_isSLThreeEpsAny {Y : Type*} [Group Y] (h : IsSLThreeEpsAny Y) :
    Nat.card (Subgroup.center Y) = 3 := by
  rcases h with ⟨K, F, fin, hK, ⟨e⟩⟩ | ⟨K, F, fin, q, hK, hq, hq2, ⟨e⟩⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_statedSL_three' (by omega)
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_statedSU_three hK hq hq2

theorem lemma512_aux (h510 : Lemma510) (i183 : Input18_3) (i253 : Input25_3)
    (iFix : InputSL3FieldFixed) (iRes : InputSL3FieldRestrict) : Lemma512 := by
  intro G _ _ m hS h4 B hB b hb hb1 L hL hbL A hA hbA x hxb hx3 hxA hfld
  have hBe : CFSG.Open.IsElemAbelian 3 B := hB.1.1
  have hb3 : b ^ 3 = 1 := hBe.2 b hb
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hbx : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hxb
  have hLb : L ≤ Cen b := hL.1.1
  have hbZ : ∀ l ∈ L, l * b = b * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLb hl)
  have hAB : A ≤ B := hA.1
  have hxmem : x ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hgN : ∀ g ∈ A ⊔ Subgroup.zpowers x, g ∈ Subgroup.normalizer (L : Set G) :=
    fun g hg => (hfld g hg).1
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hgN x hxmem
  have hAC : A ≤ Cen x := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hxA) a ha
  obtain ⟨hty, -, hiv⟩ := h510 G m hS h4 B hB b hb hb1 L hL
  have hbL1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨b, hbL⟩ : barOf 3 L) ≠ 1 := by
    intro h
    have := orderOf_mk_prime_three hbL hbo
    rw [h, orderOf_one] at this
    omega
  have : Nontrivial (barOf 3 L) := ⟨⟨_, 1, hbL1⟩⟩
  have hLq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_barOf Nat.prime_three hL.1 inferInstance
  have hbcen : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨b, hbL⟩ : barOf 3 L) ∈
      Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbZ l l.2)
  have hα3 : (barAut 3 L ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hx3'
    rw [this, map_one]
  have hαf : IsFieldAutThree (barAut 3 L ⟨x, hxN⟩) := (hfld x hxmem).2
  set E : Subgroup (MulAut (barOf 3 L)) :=
    ((A ⊔ Subgroup.zpowers x).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L)
    with hE
  have hαE : barAut 3 L ⟨x, hxN⟩ ∈ E :=
    ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.2 hxmem, rfl⟩
  have hEf : ∀ ε ∈ E, IsFieldAutThree ε := by
    rintro ε ⟨γ, hγ, rfl⟩
    exact (hfld γ.1 (Subgroup.mem_subgroupOf.1 hγ)).2
  obtain ⟨hFq, hFt⟩ := iFix (barOf 3 L) hLq hty ⟨_, hbcen, hbL1⟩ _ hα3 hαf
  have hres := iRes (barOf 3 L) hLq hty ⟨_, hbcen, hbL1⟩ _ hα3 hαf
  have hfix := fixedSub_barAut_eq hx3' hxN
  rw [hfix] at hFq hFt hres
  have hZ : Nat.card (Subgroup.center ↥(barX 3 L (L ⊓ Cen x))) = 3 :=
    card_center_of_isSLThreeEpsAny hFt
  obtain ⟨J₀, hJ0c, hJ0top, hJ0F, hJ0N⟩ := exists_J0 hFq hZ
  rw [← hJ0F] at hFq hFt hres hZ
  have hbH : b ∈ L ⊓ Cen x :=
    ⟨hbL, Subgroup.mem_centralizer_singleton_iff.2 hbx.symm⟩
  have hbJ0 : b ∈ J₀ :=
    mem_of_barX_eq_top hJ0top hbH hb3 (fun h hh => (hbZ h hh.1).symm)
  have hLle : L ≤ GLAPLayer 3 (Cen b) := le_sSup hL.1
  have hLayer_le : ∀ X : Subgroup G, GLAPLayer 3 X ≤ X := fun X => sSup_le fun K hK => hK.1
  have hLsn : CFSG.Open.IsSubnormal L (GLAPLayer 3 (Cen b)) :=
    isSubnormal_of_le_of_le hL.1.2.1 hLle (hLayer_le _)
  have hHsnM : CFSG.Open.IsSubnormal (L ⊓ Cen x) (GLAPLayer 3 (Cen b) ⊓ Cen x) :=
    isSubnormal_inf hLsn (Cen x)
  have hJ0snM : CFSG.Open.IsSubnormal J₀ (GLAPLayer 3 (Cen b) ⊓ Cen x) :=
    isSubnormal_trans' hJ0c.2.1 hHsnM
  have hJ0M : GLAPComponent 3 (GLAPLayer 3 (Cen b) ⊓ Cen x) J₀ :=
    glaPComponent_up Nat.prime_three hJ0c (inf_le_inf_right _ hLle) hJ0snM
  have hJ0Mle : J₀ ≤ GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen x) := le_sSup hJ0M
  have hJ0Ml : GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen x)) J₀ :=
    glaPComponent_down Nat.prime_three hJ0M hJ0Mle (hLayer_le _)
  have := hS.simple
  obtain ⟨hdich, h3⟩ := i183 G hS.nonabelian hS.kProper b x hbo hx3 hbx.symm J₀ hJ0Ml
  have hbC : b ∈ Cen x := Subgroup.mem_centralizer_singleton_iff.2 hbx.symm
  have hJK : J₀ ≤ conjHull x J₀ := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Cen x)) => GLBConj g J₀) 1 (one_mem _)
    rwa [gLBConj_one] at this
  obtain ⟨L₁, hL₁, hK⟩ : ∃ L₁ : Subgroup G, GLAPComponent 3 (Cen x) L₁ ∧ conjHull x J₀ = L₁ := by
    rcases hdich with ⟨L₁, hL₁, hK, -⟩ | ⟨L₁, L₂, L₃, h₁, h₂, h₃, h12, h23, h31, hu1, -, -, hK⟩
    · exact ⟨L₁, hL₁, hK⟩
    · exact (not_diag hbJ0 (hK ▸ hJK) h₁ h₂ h₃ h12 h31 hu1).elim
  have hJ0L : J₀ ≤ L := fun j hj => (hJ0c.1 hj).1
  have hJ0C : J₀ ≤ Cen x := fun j hj => (hJ0c.1 hj).2
  have hCne : Cen x ≠ ⊤ := by
    intro htop
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Cen x := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have hnorm : (Subgroup.center G).Normal := inferInstance
    rcases hS.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h] at hxc
      have : x = 1 := hxc
      rw [this, orderOf_one] at hx3
      omega
    · obtain ⟨a, c, hac⟩ := hS.nonabelian
      have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
      exact hac ((Subgroup.mem_center_iff.1 ha) c).symm
  have hKgrpC : CFSG.Open.IsKGroup ↥(Cen x) := isKGroup_of_isKProper hS.kProper hCne
  have hKC : conjHull x J₀ ≤ Cen x := hK ▸ hL₁.1
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cen x) (conjHull x J₀)) := by
    rw [hK]; exact hL₁.2.2.1.2.2
  have hKsn : CFSG.Open.IsSubnormal (barX 3 (Cen x) (conjHull x J₀)) ⊤ := by
    rw [hK]; exact hL₁.2.2.1.2.1
  have hKg : CFSG.Open.IsKGroup ↥(barX 3 (Cen x) (conjHull x J₀)) :=
    isKGroup_subgroup_quotient hKgrpC (GLAPPrimeCore 3 ↥(Cen x)) _
  have hKcore : GLAPPrimeCore 3 ↥(barX 3 (Cen x) (conjHull x J₀)) = ⊥ :=
    glaPPrimeCore_eq_bot_of_isSubnormal (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hKsn
  have hbK : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) ∈
      barX 3 (Cen x) (conjHull x J₀) :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (hJK hbJ0), rfl⟩
  have hbJ' : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) ∈
      barX 3 (Cen x) J₀ := ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbJ0, rfl⟩
  have hbo' : orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) = 3 :=
    orderOf_mk_prime_three hbC hbo
  have hJcomp := h3 hbC
  have hAcomm : ∀ a ∈ A, a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1 (hAC ha)
  have hAnorm : A ≤ Subgroup.normalizer (conjHull x J₀ : Set G) :=
    le_normalizer_conjHull hAC fun a ha =>
      hJ0N a (hgN a (Subgroup.mem_sup_left ha)) (hAcomm a ha)
  have hAel := barX_card_elemAbelian hAC hA.2.1
  have hAcard : Nat.card (barX 3 (Cen x) A) = 9 := by
    rw [hAel.2, hA.2.2]; norm_num
  have hAnorm' : barX 3 (Cen x) A ≤
      Subgroup.normalizer (barX 3 (Cen x) (conjHull x J₀) : Set (CBarOf x)) :=
    barX_le_normalizer hAnorm
  have hbA' : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩) ∈ barX 3 (Cen x) A :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbA, rfl⟩
  have hF0 : GLAPPrimeCore 3 ↥(barX 3 L J₀) = ⊥ := glaPPrimeCore_eq_bot_of_quasisimple hFq hZ
  obtain ⟨e, he1, he2⟩ := exists_equiv_barOf_barX hJ0L hJ0C hF0
  have hFt' : IsSLThreeEpsAny ↥(barX 3 L J₀) := hFt
  have ha' : IsSLThreeEpsAny (barOf 3 (barX 3 (Cen x) J₀)) := isSLThreeEpsAny_congr e.symm hFt'
  have hb' : Subgroup.center (barOf 3 (barX 3 (Cen x) J₀)) =
      Subgroup.zpowers (QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x))
        ⟨b, hbC⟩, hbJ'⟩ : ↥(barX 3 (Cen x) J₀))) := by
    have hcard : Nat.card (Subgroup.center (barOf 3 (barX 3 (Cen x) J₀))) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact hZ
    have hmem : ((QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x))
        ⟨b, hbC⟩, hbJ'⟩ : ↥(barX 3 (Cen x) J₀)) : barOf 3 (barX 3 (Cen x) J₀))) ∈
        Subgroup.center (barOf 3 (barX 3 (Cen x) J₀)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨⟨j, hjC⟩, hj, hjw⟩ := w.2
      have hj' : j ∈ J₀ := Subgroup.mem_subgroupOf.1 hj
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show (w : CBarOf x) * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨b, hbC⟩ * (w : CBarOf x)
      rw [← hjw, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hbZ j (hJ0L hj'))
    have hne : ((QuotientGroup.mk (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x))
        ⟨b, hbC⟩, hbJ'⟩ : ↥(barX 3 (Cen x) J₀)) : barOf 3 (barX 3 (Cen x) J₀))) ≠ 1 := by
      intro h
      have := he1 b hbJ0
      rw [h, map_one] at this
      exact hbL1 this.symm
    exact center_eq_zpowers_of_card_three hcard hmem hne
  have hc' : ∀ a ∈ barX 3 (Cen x) A, a ≠ 1 → InducesFieldAut 3 (barX 3 (Cen x) J₀) a := by
    rintro _ ⟨⟨a, haC⟩, ha, rfl⟩ -
    have haA : a ∈ A := Subgroup.mem_subgroupOf.1 ha
    have haE : barAut 3 L ⟨a, hgN a (Subgroup.mem_sup_left haA)⟩ ∈ E :=
      ⟨⟨a, hgN a (Subgroup.mem_sup_left haA)⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left haA), rfl⟩
    obtain ⟨ρ, hρ, hρf⟩ := hres E hαE hEf _ haE
    exact (he2 a haC (hgN a (Subgroup.mem_sup_left haA))
      (hJ0N a (hgN a (Subgroup.mem_sup_left haA)) (hAcomm a haA)) ρ hρ hρf)
  have hmain := i253 (CBarOf x) (barX 3 (Cen x) (conjHull x J₀)) (barX 3 (Cen x) J₀)
    (barX 3 (Cen x) A) _ hbJ' hKq hKg hKcore hbK hbo' hJcomp ha' hb' hAnorm' hAel.1 hAcard hbA'
    hc'
  rcases hmain with hJK' | ⟨ã, hã, hã1, hnot⟩
  ·
    have hz := comm_mem_core_of_barX hKC hJK'.symm.le hbC
      (fun j hj => hbZ j (hJ0L hj))
    exact mem_oPrimePOf_of_central_subnormal (hK ▸ hL₁.2.1) (hJK hbJ0) hb3 hz
  ·
    exfalso
    obtain ⟨⟨a, haC⟩, ha, rfl⟩ := hã
    have haA : a ∈ A := Subgroup.mem_subgroupOf.1 ha
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hã1 (by
        show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen x)) ⟨1, haC⟩ = 1
        exact map_one _)
    have ha3 : a ^ 3 = 1 := hBe.2 a (hAB haA)
    have hbCa : b ∈ oPrimePOf 3 (Cen a) := by
      have h4 := (hiv a (hAB haA) ha1 (hfld a (Subgroup.mem_sup_left haA))).2.2
      exact h4 ⟨hb, mem_oPrimePOf_of_forall_comm Nat.prime_three hbL
        (fun y hy => (hbZ y hy).symm)⟩
    exact hnot (mem_oPrimePOf_barX hKC haC ha3 (hAnorm haA) (hJK hbJ0) hbC hbCa)


end Lemma512Ns

theorem lemma512_of_inputs (h510 : Lemma510) (i183 : Lemma512Ns.Input18_3)
    (i253 : Lemma512Ns.Input25_3) (iFix : Lemma512Ns.InputSL3FieldFixed)
    (iRes : Lemma512Ns.InputSL3FieldRestrict) : Lemma512 :=
  Lemma512Ns.lemma512_aux h510 i183 i253 iFix iRes

end CFSG.HardMathSupport.Solomon.LocalBalance
