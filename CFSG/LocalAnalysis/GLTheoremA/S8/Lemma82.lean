module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Common
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open scoped commutatorElement

namespace S8

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure Sp82 (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L : Subgroup G) : Prop where
  hB : GLAIsBmax p B
  hxB : x ∈ B
  hx1 : x ≠ 1
  hL : GLAPComponent p (cx x) L
  hBN : B ≤ Subgroup.normalizer (L : Set G)
  hcent : ∀ b ∈ B, CentMod p L b ↔ b ∈ Subgroup.zpowers x
  hcyc : CycModSylow p L
  huniq : ∀ J : Subgroup G, GLAPComponent p (cx x) J → J = L
  hBL : B ≤ (B ⊓ L) ⊔ Subgroup.zpowers x
  hT : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
    (⁅T, B⁆ : Subgroup G) = T ∧ ¬ T ≤ GLAPPrimeCoreOf p L

theorem orderOf_eq_of_isElemAbelian {B : Subgroup G} {x : G} (hp : p.Prime) (hB : IsElemAbelian p B)
    (hx : x ∈ B) (hx1 : x ≠ 1) : orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (hB.2 x hx) hx1

theorem le_cx_of_isElemAbelian {B : Subgroup G} {x : G} (hB : IsElemAbelian p B) (hx : x ∈ B) :
    B ≤ cx x := by
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact isElemAbelian_commute hB hb hx

theorem barX_conj_eq {p : ℕ} {X L J : Subgroup G} (hLX : L ≤ X) (hJX : J ≤ X)
    (hcomm : ⁅L, J⁆ ≤ GLAPPrimeCoreOf p X) {j : G} (hj : j ∈ J) :
    barX p X (GLBConj j L) = barX p X L := by
  have hmem : ∀ x : ↥X, x ∈ GLAPPrimeCore p ↥X ↔ (x : G) ∈ GLAPPrimeCoreOf p X := fun x =>
    (Subgroup.mem_map_iff_mem (f := X.subtype) X.subtype_injective).symm
  have hjX : j ∈ X := hJX hj
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : j * (w : G) * j⁻¹ ∈ L := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hw)
    refine ⟨⟨j * (w : G) * j⁻¹, X.mul_mem (X.mul_mem hjX w.2) (X.inv_mem hjX)⟩,
      Subgroup.mem_subgroupOf.2 hw', ?_⟩
    show (QuotientGroup.mk _ : ↥X ⧸ GLAPPrimeCore p ↥X) = QuotientGroup.mk w
    rw [QuotientGroup.eq, hmem]
    have h1 : ⁅(j * (w : G) * j⁻¹)⁻¹, j⁻¹⁆ ∈ GLAPPrimeCoreOf p X :=
      hcomm (Subgroup.commutator_mem_commutator (L.inv_mem hw') (J.inv_mem hj))
    convert h1 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_inv_rev, inv_inv]
    group
  · rintro ⟨w, hw, rfl⟩
    have hw' : (w : G) ∈ L := Subgroup.mem_subgroupOf.1 hw
    refine ⟨⟨j⁻¹ * (w : G) * j, X.mul_mem (X.mul_mem (X.inv_mem hjX) w.2) hjX⟩,
      Subgroup.mem_subgroupOf.2 (mem_gLBConj.2 (by
        have e : j * (j⁻¹ * (w : G) * j) * j⁻¹ = w := by group
        rw [e]; exact hw')), ?_⟩
    show (QuotientGroup.mk _ : ↥X ⧸ GLAPPrimeCore p ↥X) = QuotientGroup.mk w
    rw [QuotientGroup.eq, hmem]
    have h1 : ⁅(w : G)⁻¹, j⁻¹⁆⁻¹ ∈ GLAPPrimeCoreOf p X := Subgroup.inv_mem _
      (hcomm (Subgroup.commutator_mem_commutator (L.inv_mem hw') (J.inv_mem hj)))
    convert h1 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_inv_rev, inv_inv]
    group

theorem centMod_of_other_component {p : ℕ} (hp : p.Prime) {x : G} {L J : Subgroup G}
    (hL : GLAPComponent p (cx x) L) (hJ : GLAPComponent p (cx x) J) (hne : J ≠ L) :
    ∀ j ∈ J, CentMod p L j := by
  intro j hj
  have hcomm : ⁅L, J⁆ ≤ GLAPPrimeCoreOf p (cx x) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp hL hJ hne.symm
  have hjX : j ∈ cx x := hJ.1 hj
  have hX : GLBConj j (cx x) = cx x :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hjX)
  have h1 : GLAPComponent p (cx x) (GLBConj j L) := by
    have := glaPComponent_gLBConj hL j
    rwa [hX] at this
  have h2 : barX p (cx x) (GLBConj j L) = barX p (cx x) L := barX_conj_eq hL.1 hJ.1 hcomm hj
  have h3 : GLBConj j L = L := glaPComponent_unique h1 hL h2
  have hjN : j ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 h3
  refine ⟨hjN, ?_⟩
  rw [Subgroup.commutator_le]
  intro ℓ hℓ c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hjk : j ^ k ∈ J := J.zpow_mem hj k
  have hjkN : j ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hjN k
  have hA : ⁅ℓ, j ^ k⁆ ∈ L := by
    have h4 := (Subgroup.mem_normalizer_iff.1 hjkN ℓ⁻¹).1 (L.inv_mem hℓ)
    have h5 := L.mul_mem hℓ h4
    simpa [commutatorElement_def, mul_assoc] using h5
  have hB : ⁅ℓ, j ^ k⁆ ∈ GLAPPrimeCoreOf p (cx x) :=
    hcomm (Subgroup.commutator_mem_commutator hℓ hjk)
  have h6 := glaPPrimeCoreOf_inf_eq_of_isSubnormal (p := p) hp hL.2.1
  rw [← h6]
  exact ⟨hA, hB⟩

theorem not_mem_of_cyclic_sylow {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J)
    (hcyc : ∀ P : Sylow p ↥J, IsCyclic (P : Subgroup ↥J)) {x : G} (hx : orderOf x = p) (hxJ : x ∈ J)
    (hcen : ∀ y ∈ J, x * y = y * x) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI : Group.IsPerfect (PQuot p J) := ⟨hq.1⟩
  let π : ↥J →* PQuot p J := QuotientGroup.mk' (GLAPPrimeCore p ↥J)
  let f : PQuot p J →* PQuot p J ⧸ Subgroup.center (PQuot p J) := QuotientGroup.mk' _
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hfker : f.ker ≤ Subgroup.center (PQuot p J) := by
    rw [QuotientGroup.ker_mk']
  set x₀ : ↥J := ⟨x, hxJ⟩ with hx₀
  have hx5 : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx₀p : x₀ ^ p = 1 := Subtype.ext (by simpa using hx5)
  have hxhc : π x₀ ∈ Subgroup.center (PQuot p J) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    show (QuotientGroup.mk y : PQuot p J) * QuotientGroup.mk x₀ = QuotientGroup.mk x₀ * QuotientGroup.mk y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcen y y.2).symm
  have hxhk : π x₀ ∈ f.ker := by
    rw [QuotientGroup.ker_mk']
    exact hxhc
  by_cases hx1 : π x₀ = 1
  · have hmem : x₀ ∈ GLAPPrimeCore p ↥J := (QuotientGroup.eq_one_iff _).1 hx1
    have h5 : orderOf (⟨x₀, hmem⟩ : ↥(GLAPPrimeCore p ↥J)) = p := by
      rw [Subgroup.orderOf_mk, hx₀, Subgroup.orderOf_mk, hx]
    have h6 := orderOf_dvd_natCard (⟨x₀, hmem⟩ : ↥(GLAPPrimeCore p ↥J))
    rw [h5] at h6
    exact ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) h6
  · let Xh : ↥f.ker := ⟨π x₀, hxhk⟩
    have hXhp : IsPGroup p (Subgroup.zpowers Xh) := by
      refine (CFSG.Open.isElemAbelian_zpowers (p := p) (x := Xh) ?_).isPGroup
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one, Xh]
      rw [← map_pow, hx₀p, map_one]
    obtain ⟨C, hC⟩ := IsPGroup.exists_le_sylow hXhp
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p (PQuot p J ⧸ Subgroup.center (PQuot p J))))
    have hQcyc : IsCyclic (Q : Subgroup (PQuot p J ⧸ Subgroup.center (PQuot p J))) := by
      obtain ⟨Ph, hPh⟩ := Sylow.mapSurjective_surjective hfsurj p Q
      obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπsurj p Ph
      have h1 : (P : Subgroup ↥J).map π = (Ph : Subgroup (PQuot p J)) := by
        rw [← Sylow.coe_mapSurjective hπsurj P, hP]
      have h2 : (Ph : Subgroup (PQuot p J)).map f = (Q : Subgroup _) := by
        rw [← Sylow.coe_mapSurjective hfsurj Ph, hPh]
      have h3 : IsCyclic ((P : Subgroup ↥J).map π) := by
        haveI := hcyc P
        exact isCyclic_of_surjective (π.subgroupMap (P : Subgroup ↥J))
          (π.subgroupMap_surjective _)
      rw [h1] at h3
      have h4 : IsCyclic ((Ph : Subgroup (PQuot p J)).map f) := by
        haveI := h3
        exact isCyclic_of_surjective (f.subgroupMap (Ph : Subgroup (PQuot p J)))
          (f.subgroupMap_surjective _)
      rw [h2] at h4
      exact h4
    have hbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot f hfsurj hfker C Q
      hQcyc
    have hmemC : Xh ∈ (C : Subgroup ↥f.ker) := hC (Subgroup.mem_zpowers Xh)
    rw [hbot, Subgroup.mem_bot] at hmemC
    exact hx1 (congrArg Subtype.val hmemC)

theorem unique_pcomponent (hc : S8Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : ∀ J : Subgroup G, GLAPComponent p (cx x) J → J = L := by
  intro J hJ
  by_contra hne
  obtain ⟨hB, hxB, hx1, hL, -, -, hcyc, -⟩ := sStarFacts hc h
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hJcm : ∀ j ∈ J, CentMod p L j := centMod_of_other_component hp hL hJ hne
  have hxord : orderOf x = p := orderOf_eq_of_isElemAbelian hp hB.1 hxB hx1
  have hx5 : x ^ p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hcycJ : ∀ P : Sylow p ↥J, IsCyclic (P : Subgroup ↥J) := by
    intro P
    have hP'p : IsPGroup p ((P : Subgroup ↥J).map J.subtype) := P.isPGroup'.map J.subtype
    have hcm : ∀ g ∈ (P : Subgroup ↥J).map J.subtype, CentMod p L g := by
      rintro g ⟨y, -, rfl⟩
      exact hJcm y y.2
    have h1 := hcyc _ hcm hP'p
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥J) J.subtype J.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hxcen : ∀ y ∈ J, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hy)).symm
  have hxJ : x ∉ J := fun hxJ => not_mem_of_cyclic_sylow hp hJ hcycJ hxord hxJ hxcen
  have hpd : p ∣ Nat.card J := by
    refine (dvd_card_pQuot_of_component hp hJ).trans ?_
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) p hpd
  set j : G := (y : G) with hjdef
  have hjJ : j ∈ J := y.2
  have hjord : orderOf j = p := by rw [hjdef, Subgroup.orderOf_coe, hyord]
  have hj5 : j ^ p = 1 := by rw [← hjord]; exact pow_orderOf_eq_one j
  have hjcm : CentMod p L j := hJcm j hjJ
  have hxj : x * j = j * x := hxcen j hjJ
  have hxcm : CentMod p L x :=
    centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hl)))
  have hjx : j ∉ Subgroup.zpowers x := by
    intro hj
    have hle : Subgroup.zpowers j ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hj
    have hc1 : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
    have hc2 : Nat.card (Subgroup.zpowers j) = p := by rw [Nat.card_zpowers, hjord]
    have heq : Subgroup.zpowers j = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
    apply hxJ
    have : x ∈ Subgroup.zpowers j := heq ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.2 hjJ) this
  set S : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers j with hS
  have hSel : IsElemAbelian p S :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hx5)
      (CFSG.Open.isElemAbelian_zpowers hj5) (fun a ha b hb => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact ((Commute.zpow_zpow (show Commute x j from hxj) m n)).eq)
  have hSp : IsPGroup p S := fun g => ⟨1, Subtype.ext (by simpa using hSel.2 g g.2)⟩
  have hSle : S ≤ centModSubgroup p L :=
    sup_le (Subgroup.zpowers_le.2 (centMod_iff.1 hxcm)) (Subgroup.zpowers_le.2 (centMod_iff.1 hjcm))
  have hcycS : IsCyclic S := hcyc S (fun g hg => centMod_iff.2 (hSle hg)) hSp
  have hlt : Subgroup.zpowers x < S := by
    refine lt_of_le_of_ne le_sup_left fun heq => hjx ?_
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers j)
  have hcard1 : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  have hcard2 : p < Nat.card S := hcard1 ▸ Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hSp.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at this
    omega
  exact S3.not_isCyclic_of_card hp hSel (by
    rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2) hcycS

theorem normalizer_of_unique {X L : Subgroup G} (hL : GLAPComponent p X L)
    (huniq : ∀ J : Subgroup G, GLAPComponent p X J → J = L) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  have hX : GLBConj g X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  have h1 := glaPComponent_gLBConj hL g
  rw [hX] at h1
  exact huniq _ h1

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.OuterAutomorphisms in
theorem inducesInnerMod_of_inner' {J : Subgroup G}
    [Group.IsPerfect (PQuot p J)] {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : centerQuotientHom (PQuot p J) (barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩) ∈
      inner (PSimple p J)) : InducesInnerMod p J g := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J)) m
  have hu : barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ = MulAut.conj u :=
    (centerQuotientHom_injective (PQuot p J)) (hm.symm.trans (centerQuotient_conj u).symm)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
  set γ : ↥(Subgroup.normalizer (J : Set G)) := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ with hγ
  refine ⟨((w : ↥J) : G)⁻¹, J.inv_mem w.2, fun y hy => ?_⟩
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom γ y : ↥J) : G) = g⁻¹ * y * g := fun y => by
    change (g⁻¹ : G) * y * (g⁻¹)⁻¹ = _
    rw [inv_inv]
  have h1 : barAut p J γ (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk (w * ⟨y, hy⟩ * w⁻¹) := by
    rw [hu, MulAut.conj_apply]
    rfl
  rw [barAut_mk] at h1
  have h2 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) ∈
      GLAPPrimeCoreOf p J :=
    Subgroup.mem_map_of_mem J.subtype (QuotientGroup.eq.1 h1.symm)
  have h3 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) =
      (((w : G)⁻¹)⁻¹ * y * (w : G)⁻¹)⁻¹ * (g⁻¹ * y * g) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs, inv_inv]
  rwa [h3] at h2

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.OuterAutomorphisms in
theorem inducesInner_spor (hc : S8Ctx G p) (hOut : SporadicOuterLeTwo) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) (hsp : catalogIs (PSimple p L) isSporIndex) :
    ∀ b ∈ B, InducesInnerMod p L b := by
  intro b hb
  obtain ⟨hB, hxB, hx1, hL, hBN, -⟩ := sStarFacts hc h
  have hp := hc.ctx.prime
  obtain ⟨hsimple, hnonab, -⟩ := catalog_of_component hc.ctx hx1 hL
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  haveI : Group.IsPerfect (PQuot p L) := ⟨hq.1⟩
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBN hb
  have hbp : b ^ p = 1 := hB.1.2 b hb
  obtain ⟨i, hi, ⟨e⟩⟩ := hsp
  cases i with
  | sporadic s =>
    have hout : Nat.card (Outer (PSimple p L)) ≤ 2 := hOut _ hsimple hnonab s ⟨e⟩
    apply inducesInnerMod_of_inner' hbN
    set φb := centerQuotientHom (PQuot p L) (barAut p L ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩) with hφb
    have hφp : φb ^ p = 1 := by
      rw [hφb, ← map_pow, ← map_pow]
      have : (⟨b⁻¹, Subgroup.inv_mem _ hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 := by
        apply Subtype.ext
        simp [inv_pow, hbp]
      rw [this, map_one, map_one]
    set ψ : Outer (PSimple p L) := QuotientGroup.mk φb
    have hψ : ψ ^ p = 1 := by rw [← QuotientGroup.mk_pow, hφp, QuotientGroup.mk_one]
    have hord : orderOf ψ ∣ p := orderOf_dvd_of_pow_eq_one hψ
    have hord2 : orderOf ψ ∣ Nat.card (Outer (PSimple p L)) := orderOf_dvd_natCard ψ
    have hle : orderOf ψ ≤ 2 := (Nat.le_of_dvd Nat.card_pos hord2).trans hout
    have h1 : orderOf ψ = 1 := by
      rcases (Nat.dvd_prime hp).1 hord with h1 | h1
      · exact h1
      · rw [h1] at hle
        have := hc.ctx.odd
        have := hp.two_le
        omega
    rw [orderOf_eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff φb).mp h1
  | cyclic _ _ => exact absurd hi (by simp [isSporIndex])
  | alternating _ _ => exact absurd hi (by simp [isSporIndex])
  | lie _ => exact absurd hi (by simp [isSporIndex])

theorem centMod_of_inducesInner {p : ℕ} {L : Subgroup G} {b l₀ : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hl₀ : l₀ ∈ L)
    (h : ∀ y ∈ L, (l₀⁻¹ * y * l₀)⁻¹ * (b⁻¹ * y * b) ∈ GLAPPrimeCoreOf p L) :
    CentMod p L (b * l₀⁻¹) := by
  have hl₀N : l₀ ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.le_normalizer hl₀)
  have hcN : b * l₀⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ hb (Subgroup.inv_mem _ (Subgroup.le_normalizer hl₀))
  have hinv : (b * l₀⁻¹)⁻¹ ∈ centModSubgroup p L := by
    refine ⟨Subgroup.inv_mem _ hcN, fun y hy => ?_⟩
    have h1 := h y⁻¹ (L.inv_mem hy)
    have h2 := (Subgroup.mem_normalizer_iff.1 hl₀N _).1 h1
    have h3 : l₀ * ((l₀⁻¹ * y⁻¹ * l₀)⁻¹ * (b⁻¹ * y⁻¹ * b)) * l₀⁻¹ = ⁅y, (b * l₀⁻¹)⁻¹⁆ := by
      simp only [commutatorElement_def, mul_inv_rev, inv_inv]
      group
    rwa [h3] at h2
  have hmem : b * l₀⁻¹ ∈ centModSubgroup p L := by
    have := Subgroup.inv_mem _ hinv
    rwa [inv_inv] at this
  exact centMod_iff.2 hmem

theorem mul_pow_mem_core {O : Subgroup G} {l c : G} (hl : l ∈ Subgroup.normalizer (O : Set G))
    (hc : c ∈ Subgroup.normalizer (O : Set G)) (hlc : ⁅l, c⁆ ∈ O) (n : ℕ) :
    ((l * c) ^ n)⁻¹ * (l ^ n * c ^ n) ∈ O := by
  set H := Subgroup.normalizer (O : Set G) with hH
  haveI : (O.subgroupOf H).Normal := Subgroup.normal_in_normalizer
  have hO : ∀ g : H, (g : G) ∈ O ↔ g ∈ O.subgroupOf H := fun g => Iff.rfl
  let l' : H := ⟨l, hl⟩
  let c' : H := ⟨c, hc⟩
  have hcomm : Commute (QuotientGroup.mk l' : H ⧸ O.subgroupOf H) (QuotientGroup.mk c') := by
    show (QuotientGroup.mk l' : H ⧸ O.subgroupOf H) * QuotientGroup.mk c' =
      QuotientGroup.mk c' * QuotientGroup.mk l'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (l' * c')⁻¹ * (c' * l') ∈ O.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have : ((l' * c')⁻¹ * (c' * l') : H).val = c⁻¹ * l⁻¹ * (c * l) := by
        simp [l', c', mul_inv_rev, mul_assoc]
      rw [this]
      have h2 := Subgroup.inv_mem _ hlc
      have hg : (l * c)⁻¹ ∈ H := H.inv_mem (H.mul_mem hl hc)
      have h3 := (Subgroup.mem_normalizer_iff.1 hg _).1 h2
      have h4 : (l * c)⁻¹ * (⁅l, c⁆)⁻¹ * ((l * c)⁻¹)⁻¹ = c⁻¹ * l⁻¹ * (c * l) := by
        simp only [commutatorElement_def, mul_inv_rev, inv_inv]; group
      rwa [h4] at h3
    exact h1
  have h := hcomm.mul_pow n
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
    ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have h4 : ((l' * c') ^ n)⁻¹ * (l' ^ n * c' ^ n) ∈ O.subgroupOf H := h
  have h5 := Subgroup.mem_subgroupOf.1 h4
  have h6 : (((l' * c') ^ n)⁻¹ * (l' ^ n * c' ^ n) : H).val = ((l * c) ^ n)⁻¹ * (l ^ n * c ^ n) := by
    simp [l', c']
  rwa [h6] at h5

theorem exists_pparts {p : ℕ} (hp : p.Prime) {O : Subgroup G} {l c b : G}
    (hl : l ∈ Subgroup.normalizer (O : Set G)) (hc : c ∈ Subgroup.normalizer (O : Set G))
    (hlc : ⁅l, c⁆ ∈ O) (hb : b ^ p = 1) (hbl : b⁻¹ * (l * c) ∈ O) :
    ∃ m n : ℕ, (∃ k : ℕ, (l ^ m) ^ (p ^ k) = 1) ∧ (∃ k : ℕ, (c ^ n) ^ (p ^ k) = 1) ∧
      b⁻¹ * (l ^ m * c ^ n) ∈ O := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hl0 : 0 < orderOf l := orderOf_pos l
  have hc0 : 0 < orderOf c := orderOf_pos c
  set N := p * orderOf l * orderOf c with hN
  have hN0 : N ≠ 0 := by rw [hN]; exact (Nat.mul_pos (Nat.mul_pos hp.pos hl0) hc0).ne'
  obtain ⟨a, m', hm', hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.ne_one
  have ha : 1 ≤ a := by
    by_contra ha
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero, one_mul] at hNm
    apply hm'
    rw [← hNm, hN]
    exact (dvd_mul_right p _).trans (dvd_mul_right _ _)
  have hcop : Nat.Coprime (p ^ a) m' :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hm')
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
  have hkp : k ≡ 1 [MOD p] := Nat.ModEq.of_dvd (dvd_pow_self p (by omega)) hk1
  have hkmod : k % p = 1 := by
    have := hkp
    unfold Nat.ModEq at this
    rw [this]
    exact Nat.mod_eq_of_lt hp.one_lt
  have hbk : b ^ k = b := by
    have hk : k = p * (k / p) + 1 := by
      have := Nat.div_add_mod k p
      omega
    conv_lhs => rw [hk]
    rw [pow_add, pow_mul, hb, one_pow, one_mul, pow_one]
  have hm'k : m' ∣ k := (Nat.modEq_zero_iff_dvd.1 hk0)
  have hNk : N ∣ k * p ^ a := by
    obtain ⟨t, ht⟩ := hm'k
    refine ⟨t, ?_⟩
    rw [hNm, ht]
    ring
  have hlN : orderOf l ∣ N := ⟨p * orderOf c, by rw [hN]; ring⟩
  have hcN : orderOf c ∣ N := ⟨p * orderOf l, by rw [hN]; ring⟩
  have hlk : (l ^ k) ^ (p ^ a) = 1 := by
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    exact hlN.trans hNk
  have hck : (c ^ k) ^ (p ^ a) = 1 := by
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    exact hcN.trans hNk
  refine ⟨k, k, ⟨a, hlk⟩, ⟨a, hck⟩, ?_⟩
  set o := b⁻¹ * (l * c) with ho
  have hlc' : l * c = b * o := by rw [ho]; group
  have hoN : o ∈ Subgroup.normalizer (O : Set G) := Subgroup.le_normalizer hbl
  have hbN : b ∈ Subgroup.normalizer (O : Set G) := by
    have : b = (l * c) * o⁻¹ := by rw [ho]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hl hc) (Subgroup.inv_mem _ hoN)
  have hbo : ⁅b, o⁆ ∈ O := by
    have h1 : b * o * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hbN o).1 hbl
    have h2 := O.mul_mem h1 (O.inv_mem hbl)
    simpa [commutatorElement_def, mul_assoc] using h2
  have u1 := mul_pow_mem_core hl hc hlc k
  have u2 := mul_pow_mem_core hbN hoN hbo k
  rw [hbk] at u2
  rw [hlc'] at u1
  have hid : b⁻¹ * (l ^ k * c ^ k) = o ^ k * (((b * o) ^ k)⁻¹ * (b * o ^ k))⁻¹ *
      (((b * o) ^ k)⁻¹ * (l ^ k * c ^ k)) := by
    simp only [mul_inv_rev, inv_inv]
    group
  rw [hid]
  exact O.mul_mem (O.mul_mem (O.pow_mem hbl k) (O.inv_mem u2)) u1


theorem exists_decomp_mod_core (hc : S8Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hinn : ∀ b ∈ B, InducesInnerMod p L b) :
    ∀ b ∈ B, ∃ l ∈ L, ∃ c ∈ cx x, CentMod p L c ∧ (∃ k : ℕ, l ^ (p ^ k) = 1) ∧
      (∃ k : ℕ, c ^ (p ^ k) = 1) ∧ b⁻¹ * (l * c) ∈ GLAPPrimeCoreOf p L := by
  intro b hb
  obtain ⟨hB, hxB, hx1, hL, hBN, -⟩ := sStarFacts hc h
  have hp := hc.ctx.prime
  obtain ⟨l₀, hl₀, hl₀h⟩ := hinn b hb
  have hbN := hBN hb
  have hc₀ : CentMod p L (b * l₀⁻¹) := centMod_of_inducesInner hbN hl₀ hl₀h
  have hb5 : b ^ p = 1 := hB.1.2 b hb
  have hbx : b ∈ cx x := le_cx_of_isElemAbelian hB.1 hxB hb
  have hl₀x : l₀ ∈ cx x := hL.1 hl₀
  have hc₀x : b * l₀⁻¹ ∈ cx x := Subgroup.mul_mem _ hbx (Subgroup.inv_mem _ hl₀x)
  have hNO : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L
  have hcN : b * l₀⁻¹ ∈ Subgroup.normalizer (L : Set G) := hc₀.1
  have hcomm : ⁅l₀, b * l₀⁻¹⁆ ∈ GLAPPrimeCoreOf p L := (centMod_iff.1 hc₀).2 l₀ hl₀
  have hbl : b⁻¹ * (l₀ * (b * l₀⁻¹)) ∈ GLAPPrimeCoreOf p L := by
    have := (centMod_iff.1 (centMod_inv hc₀)).2 l₀⁻¹ (L.inv_mem hl₀)
    have e : ⁅l₀⁻¹, (b * l₀⁻¹)⁻¹⁆ = b⁻¹ * (l₀ * (b * l₀⁻¹)) := by
      simp only [commutatorElement_def, mul_inv_rev, inv_inv]
      group
    rwa [e] at this
  obtain ⟨m, n, ⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, hmn⟩ :=
    exists_pparts hp (hNO (Subgroup.le_normalizer hl₀)) (hNO hcN) hcomm hb5 hbl
  refine ⟨l₀ ^ m, L.pow_mem hl₀ m, (b * l₀⁻¹) ^ n, Subgroup.pow_mem _ hc₀x n, ?_, ⟨k₁, hk₁⟩,
    ⟨k₂, hk₂⟩, hmn⟩
  rw [centMod_iff]
  exact Subgroup.pow_mem _ (centMod_iff.1 hc₀) n

theorem mem_zpowers_of_cyclic {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x c : G}
    (hcyc : CycModSylow p L) (hx : orderOf x = p) (hxcm : CentMod p L x) (hcx : c ∈ cx x)
    (hcm : CentMod p L c) (hcp : c ^ p = 1) : c ∈ Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx5 : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxc : x * c = c * x := (Subgroup.mem_centralizer_singleton_iff.1 hcx).symm
  set S : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers c with hS
  have hSel : IsElemAbelian p S :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hx5)
      (CFSG.Open.isElemAbelian_zpowers hcp) (fun a ha b hb => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact ((Commute.zpow_zpow (show Commute x c from hxc) m n)).eq)
  have hSp : IsPGroup p S := fun g => ⟨1, Subtype.ext (by simpa using hSel.2 g g.2)⟩
  have hSle : S ≤ centModSubgroup p L :=
    sup_le (Subgroup.zpowers_le.2 (centMod_iff.1 hxcm)) (Subgroup.zpowers_le.2 (centMod_iff.1 hcm))
  have hcycS : IsCyclic S := hcyc S (fun g hg => centMod_iff.2 (hSle hg)) hSp
  have hcard : Nat.card S ≤ p := by
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    by_contra hlt
    push Not at hlt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      rw [pow_one] at this
      omega
    exact S3.not_isCyclic_of_card hp hSel (by rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2) hcycS
  have hcard1 : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have heq : Subgroup.zpowers x = S :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard1]; exact hcard)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

theorem central_pth_power_mem_core (h66 : I66At) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hsp : catalogIs (PSimple p L) isSporIndex) {l : G} (hl : l ∈ L)
    (hcen : ∀ y ∈ L, ⁅y, l ^ p⁆ ∈ GLAPPrimeCoreOf p L) : l ^ p ∈ GLAPPrimeCoreOf p L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hO : GLAPPrimeCore p (PQuot p L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hmem : ∀ x : ↥L, x ∈ GLAPPrimeCore p ↥L ↔ (x : G) ∈ GLAPPrimeCoreOf p L := fun x =>
    (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm
  set a : ↥L := ⟨l, hl⟩ with ha
  set u : PQuot p L := QuotientGroup.mk a with hu
  have hz : u ^ p ∈ Subgroup.center (PQuot p L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [hu, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, hmem]
    have h1 := hcen ((y : G)⁻¹) (L.inv_mem y.2)
    have hlp : (l ^ p)⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
      normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.le_normalizer (L.inv_mem (L.pow_mem hl p)))
    have h2 := (Subgroup.mem_normalizer_iff.1 hlp _).1 h1
    have h3 : (((y * a ^ p)⁻¹ * (a ^ p * y) : ↥L) : G) =
        (l ^ p)⁻¹ * ⁅(y : G)⁻¹, l ^ p⁆ * ((l ^ p)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, commutatorElement_def, ha,
        mul_inv_rev, inv_inv]
      group
    rw [h3]
    exact h2
  have hu1 : u ^ p = 1 := by
    have hsp' : catalogIs (PQuot p L ⧸ Subgroup.center (PQuot p L)) isSporIndex := hsp
    rcases Nat.lt_or_ge p 5 with hlt | hge
    · have h3 : p = 3 := by
        have := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · rfl
        · exact absurd hp (by norm_num)
      subst h3
      by_contra hne
      set z : PQuot 3 L := u ^ 3 with hzdef
      have hzc : z ∈ Subgroup.center (PQuot 3 L) := hz
      have hz1 : z ≠ 1 := hne
      have hz0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
      obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz0 3 (by norm_num)
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hz0 (by rw [hbm, mul_zero])
      have hm1 : m = 1 := by
        set z' : PQuot 3 L := z ^ (3 ^ b) with hz'
        have hz'c : z' ∈ Subgroup.center (PQuot 3 L) := Subgroup.pow_mem _ hzc _
        have hz'm : z' ^ m = 1 := by
          rw [hz', ← pow_mul, ← hbm]
          exact pow_orderOf_eq_one z
        have hord_dvd : orderOf z' ∣ m := orderOf_dvd_of_pow_eq_one hz'm
        have hcop3 : Nat.Coprime 3 (Nat.card (Subgroup.zpowers z')) := by
          rw [Nat.card_zpowers]
          exact Nat.Coprime.coprime_dvd_right hord_dvd
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm)
        have hnormal : (Subgroup.zpowers z').Normal := ⟨fun n hn g => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
          have hk : (z' ^ k) ∈ Subgroup.center (PQuot 3 L) := Subgroup.zpow_mem _ hz'c k
          have : g * (z' ^ k) * g⁻¹ = z' ^ k := by
            rw [mul_inv_eq_iff_eq_mul]
            exact Subgroup.mem_center_iff.1 hk g
          rw [this]
          exact hn⟩
        have hbot : Subgroup.zpowers z' = ⊥ :=
          (CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := PQuot 3 L)).1 hO _ hnormal hcop3
        have hz'1 : z' = 1 := Subgroup.zpowers_eq_bot.1 hbot
        have hdvd : orderOf z ∣ 3 ^ b := orderOf_dvd_of_pow_eq_one hz'1
        rw [hbm] at hdvd
        have hle : 3 ^ b * m ≤ 3 ^ b * 1 := by
          rw [mul_one]
          exact Nat.le_of_dvd (by positivity) hdvd
        have := Nat.le_of_mul_le_mul_left hle (by positivity)
        omega
      subst hm1
      rw [mul_one] at hbm
      have hb1 : 1 ≤ b := by
        by_contra hb0
        have hb0' : b = 0 := by omega
        rw [hb0', pow_zero] at hbm
        exact hz1 (orderOf_eq_one_iff.1 hbm)
      set z'' : PQuot 3 L := z ^ (3 ^ (b - 1)) with hz''
      have hz''c : z'' ∈ Subgroup.center (PQuot 3 L) := Subgroup.pow_mem _ hzc _
      have hz''3 : z'' ^ 3 = 1 := by
        rw [hz'', ← pow_mul, show 3 ^ (b - 1) * 3 = 3 ^ b by
          rw [← pow_succ]; congr 1; omega, ← hbm]
        exact pow_orderOf_eq_one z
      have hz''1 : z'' ≠ 1 := by
        intro h1
        have hdvd : orderOf z ∣ 3 ^ (b - 1) := orderOf_dvd_of_pow_eq_one h1
        rw [hbm] at hdvd
        have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 hdvd
        omega
      have hz''ord : orderOf z'' = 3 := orderOf_eq_prime hz''3 hz''1
      have hcube : (u ^ (3 ^ (b - 1))) ^ 3 = z'' := by
        rw [← pow_mul, hz'', hzdef, ← pow_mul, mul_comm]
      exact h66.1 (PQuot 3 L) hq hO hsp' z'' hz''c hz''ord _ hcube
    · have h5 := h66.2 (PQuot p L) hq hsp' p hp hge hO
      rw [h5] at hz
      simpa using hz
  rw [hu, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmem] at hu1
  simpa [ha] using hu1

theorem lpow_mul_cpow_mem_core {p : ℕ} {L : Subgroup G} {b l c : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L) (hcm : CentMod p L c) (hb : b ^ p = 1)
    (hbo : b⁻¹ * (l * c) ∈ GLAPPrimeCoreOf p L) : l ^ p * c ^ p ∈ GLAPPrimeCoreOf p L := by
  set O := GLAPPrimeCoreOf p L with hO
  have hNO := normalizer_le_normalizer_glaPPrimeCoreOf p L
  have hlO : l ∈ Subgroup.normalizer (O : Set G) := hNO (Subgroup.le_normalizer hl)
  have hcO : c ∈ Subgroup.normalizer (O : Set G) := hNO hcm.1
  have hbO : b ∈ Subgroup.normalizer (O : Set G) := hNO hbN
  have hlc : ⁅l, c⁆ ∈ O := (centMod_iff.1 hcm).2 l hl
  set o := b⁻¹ * (l * c) with ho
  have hlc' : l * c = b * o := by rw [ho]; group
  have hbo' : ⁅b, o⁆ ∈ O := by
    have h1 : b * o * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hbO o).1 hbo
    have h2 := O.mul_mem h1 (O.inv_mem hbo)
    simpa [commutatorElement_def, mul_assoc] using h2
  have u1 := mul_pow_mem_core hlO hcO hlc p
  have u2 := mul_pow_mem_core hbO (Subgroup.le_normalizer hbo) hbo' p
  rw [hlc'] at u1
  rw [hb, one_mul] at u2
  have hid : l ^ p * c ^ p = (o ^ p * (((b * o) ^ p)⁻¹ * o ^ p)⁻¹) *
      (((b * o) ^ p)⁻¹ * (l ^ p * c ^ p)) := by
    simp only [mul_inv_rev, inv_inv]
    group
  rw [hid]
  exact O.mul_mem (O.mul_mem (O.pow_mem hbo p) (O.inv_mem u2)) u1

theorem cpow_eq_one_of_decomp (h66 : I66At) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hsp : catalogIs (PSimple p L) isSporIndex) {l c : G} (hl : l ∈ L)
    (hcm : CentMod p L c) (hcp : ∃ k : ℕ, c ^ (p ^ k) = 1)
    (h : l ^ p * c ^ p ∈ GLAPPrimeCoreOf p L) : c ^ p = 1 := by
  set O := GLAPPrimeCoreOf p L with hO
  have hNO := normalizer_le_normalizer_glaPPrimeCoreOf p L
  have hcpm : CentMod p L ((c ^ p)⁻¹) := by
    rw [centMod_iff]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (centMod_iff.1 hcm) p)
  have hcen : ∀ y ∈ L, ⁅y, l ^ p⁆ ∈ O := by
    intro y hy
    have e : l ^ p = (l ^ p * c ^ p) * (c ^ p)⁻¹ := by group
    rw [e, commutatorElement_mul_right]
    have hyO : y ∈ Subgroup.normalizer (O : Set G) := hNO (Subgroup.le_normalizer hy)
    have h1 : ⁅y, l ^ p * c ^ p⁆ ∈ O := by
      have h2 : y * (l ^ p * c ^ p) * y⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hyO _).1 h
      have h3 := O.mul_mem h2 (O.inv_mem h)
      simpa [commutatorElement_def, mul_assoc] using h3
    have h4 : ⁅y, (c ^ p)⁻¹⁆ ∈ O := (centMod_iff.1 hcpm).2 y hy
    exact O.mul_mem h1 (O.mul_mem (O.mul_mem h (by exact h4)) (O.inv_mem h))
  have h1 : l ^ p ∈ O := central_pth_power_mem_core h66 hp hp2 hL hsp hl hcen
  have h2 : c ^ p ∈ O := by
    have := O.mul_mem (O.inv_mem h1) h
    simpa using this
  obtain ⟨k, hk⟩ := hcp
  have hcop : Nat.Coprime p (Nat.card O) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp L
  have h3 : orderOf (c ^ p) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [← pow_mul, mul_comm, pow_mul, hk, one_pow])
  have h4 : orderOf (⟨c ^ p, h2⟩ : ↥O) ∣ Nat.card O := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h4
  have h5 : Nat.Coprime (orderOf (c ^ p)) (Nat.card O) :=
    Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_left k hcop)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h5 h4)

theorem pow_eq_one_of_decomp (hc : S8Ctx G p) (h66 : I66At) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hsp : catalogIs (PSimple p L) isSporIndex) {b l c : G} (hb : b ∈ B)
    (hl : l ∈ L) (hcm : CentMod p L c) (hcp : ∃ k : ℕ, c ^ (p ^ k) = 1)
    (hbo : b⁻¹ * (l * c) ∈ GLAPPrimeCoreOf p L) : c ^ p = 1 := by
  obtain ⟨hB, hxB, hx1, hL, hBN, -⟩ := sStarFacts hc h
  have hp := hc.ctx.prime
  exact cpow_eq_one_of_decomp h66 hp hc.ctx.odd hL hsp hl hcm hcp
    (lpow_mul_cpow_mem_core (hBN hb) hl hcm (hB.1.2 b hb) hbo)

theorem decomp_in_zpowers (hc : S8Ctx G p) (h66 : I66At) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hsp : catalogIs (PSimple p L) isSporIndex) :
    (∀ b ∈ B, ∃ l ∈ L, ∃ c ∈ cx x, CentMod p L c ∧ (∃ k : ℕ, l ^ (p ^ k) = 1) ∧
      (∃ k : ℕ, c ^ (p ^ k) = 1) ∧ b⁻¹ * (l * c) ∈ GLAPPrimeCoreOf p L) →
    ∀ b ∈ B, ∃ l ∈ L, ∃ i : ℤ, b = l * x ^ i := by
  intro hdec b hb
  obtain ⟨hB, hxB, hx1, hL, hBN, hcent, hcyc, -⟩ := sStarFacts hc h
  have hp := hc.ctx.prime
  obtain ⟨l, hl, c, hcx, hcm, hlp, hcp, hbo⟩ := hdec b hb
  have hc1 : c ^ p = 1 := pow_eq_one_of_decomp hc h66 h hsp hb hl hcm hcp hbo
  have hxord : orderOf x = p := orderOf_eq_of_isElemAbelian hp hB.1 hxB hx1
  have hxcm : CentMod p L x :=
    centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hl)))
  have hcz : c ∈ Subgroup.zpowers x := mem_zpowers_of_cyclic hp hcyc hxord hxcm hcx hcm hc1
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcz
  set o := b⁻¹ * (l * x ^ i) with ho
  have hoL : o ∈ L := (Subgroup.map_subtype_le _) hbo
  have hxo : Commute o x := (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hoL))
  have hox : o * x ^ i = x ^ i * o := ((hxo.zpow_right i).eq)
  refine ⟨l * o⁻¹, L.mul_mem hl (L.inv_mem hoL), i, ?_⟩
  have h1 : b = l * x ^ i * o⁻¹ := by rw [ho]; group
  have h2 : x ^ i * o⁻¹ = o⁻¹ * x ^ i := by
    have := hox
    calc x ^ i * o⁻¹ = o⁻¹ * (o * x ^ i) * o⁻¹ := by group
      _ = o⁻¹ * (x ^ i * o) * o⁻¹ := by rw [hox]
      _ = o⁻¹ * x ^ i := by group
  rw [h1, mul_assoc, h2, ← mul_assoc]

theorem exists_T (hc : S8Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) :
    ∃ T : Subgroup G, T ≤ cx x ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) = T ∧ T ≠ ⊥ := by
  obtain ⟨hB, hxB, hx1, hL, hBN, -, -, -⟩ := sStarFacts hc h
  obtain ⟨-, -, T₀, hT₀x, hT₀2, hBT₀, hne, -⟩ := h.1.1.1.2.1
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : (⁅T₀, B⁆ : Subgroup G) ≤ T₀ := commutator_le_left_of_normalizes hBT₀
  have hcop : Nat.Coprime p (Nat.card T₀) := by
    obtain ⟨k, hk⟩ := hT₀2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hc.ctx.odd)
  have hres : ∀ N : Subgroup G, N ≤ B → (N.subgroupOf B).Normal →
      Nat.Coprime p (N.subgroupOf B).index → N = B := by
    intro N hNB _ hcopi
    have hdvd : (N.subgroupOf B).index ∣ Nat.card B := Subgroup.index_dvd_card _
    obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian hB.1).exists_card_eq
    rw [hm] at hdvd
    have h1 : (N.subgroupOf B).index = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left m hcopi).symm hdvd
    have h2 : N.subgroupOf B = ⊤ := Subgroup.index_eq_one.1 h1
    exact le_antisymm hNB (Subgroup.subgroupOf_eq_top.1 h2)
  refine ⟨⁅T₀, B⁆, hle.trans hT₀x, hT₀2.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle), le_normalizer_commutator hBT₀ Subgroup.le_normalizer,
    ?_, ?_⟩
  · exact i321UsedAt_holds p hp T₀ B hcop hBT₀ hres
  · exact hne
theorem comm_eq_of_decomp {t l x : G} (i : ℤ) (htx : t * x ^ i = x ^ i * t) :
    ⁅t, l * x ^ i⁆ = (t * l * t⁻¹) * l⁻¹ := by
  have hxt : x ^ i * t⁻¹ = t⁻¹ * x ^ i := by
    calc x ^ i * t⁻¹ = t⁻¹ * (t * x ^ i) * t⁻¹ := by group
      _ = t⁻¹ * (x ^ i * t) * t⁻¹ := by rw [htx]
      _ = t⁻¹ * x ^ i := by group
  rw [commutatorElement_def]
  calc t * (l * x ^ i) * t⁻¹ * (l * x ^ i)⁻¹
      = t * l * (x ^ i * t⁻¹) * (x ^ i)⁻¹ * l⁻¹ := by group
    _ = t * l * (t⁻¹ * x ^ i) * (x ^ i)⁻¹ * l⁻¹ := by rw [hxt]
    _ = (t * l * t⁻¹) * l⁻¹ := by group

theorem T_le_L {B T L : Subgroup G} {x : G} (hTx : T ≤ cx x) (hTB : (⁅T, B⁆ : Subgroup G) = T)
    (hBL : ∀ b ∈ B, ∃ l ∈ L, ∃ i : ℤ, b = l * x ^ i)
    (hLn : cx x ≤ Subgroup.normalizer (L : Set G)) : T ≤ L := by
  conv_lhs => rw [← hTB]
  rw [Subgroup.commutator_le]
  intro t ht b hb
  obtain ⟨l, hl, i, rfl⟩ := hBL b hb
  have hxt : Commute t x := Subgroup.mem_centralizer_singleton_iff.1 (hTx ht)
  have htx : t * x ^ i = x ^ i * t := (hxt.zpow_right i).eq
  rw [comm_eq_of_decomp i htx]
  have hLt : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hLn (hTx ht)) l).1 hl
  exact L.mul_mem hLt (L.inv_mem hl)

theorem T_not_le_core {p : ℕ} (hp : p.Prime) {B T L : Subgroup G} {x : G} (hL : GLAPComponent p (cx x) L)
    (hTx : T ≤ cx x) (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥) (hTB : (⁅T, B⁆ : Subgroup G) = T)
    (hBL : ∀ b ∈ B, ∃ l ∈ L, ∃ i : ℤ, b = l * x ^ i)
    (hodd : Odd (Nat.card (⁅L, GLAPPrimeCoreOf p (cx x)⁆ : Subgroup G))) :
    ¬ T ≤ GLAPPrimeCoreOf p L := by
  intro hle
  have hO : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p (cx x) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1
  have hTle : T ≤ (⁅L, GLAPPrimeCoreOf p (cx x)⁆ : Subgroup G) := by
    conv_lhs => rw [← hTB]
    rw [Subgroup.commutator_le]
    intro t ht b hb
    obtain ⟨l, hl, i, rfl⟩ := hBL b hb
    have hxt : Commute t x := Subgroup.mem_centralizer_singleton_iff.1 (hTx ht)
    have htx : t * x ^ i = x ^ i * t := (hxt.zpow_right i).eq
    rw [comm_eq_of_decomp i htx]
    have h1 : ⁅l, t⁆ ∈ (⁅L, GLAPPrimeCoreOf p (cx x)⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hl (hO (hle ht))
    have h2 : t * l * t⁻¹ * l⁻¹ = (⁅l, t⁆)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact Subgroup.inv_mem _ h1
  have hdvd : Nat.card T ∣ Nat.card (⁅L, GLAPPrimeCoreOf p (cx x)⁆ : Subgroup G) :=
    Subgroup.card_dvd_of_le hTle
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have h2 : ¬ 2 ∣ Nat.card (⁅L, GLAPPrimeCoreOf p (cx x)⁆ : Subgroup G) := by
    rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hodd
  have hk0 : k = 0 := by
    by_contra hk0
    exact h2 (((dvd_pow_self 2 hk0).trans (hk ▸ dvd_refl _)).trans hdvd)
  apply hTne
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem lemma82 (hc : S8Ctx G p) (hOut : SporadicOuterLeTwo) (h66 : I66At) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) (hsp : catalogIs (PSimple p L) isSporIndex) :
    Sp82 G p B x L := by
  obtain ⟨hB, hxB, hx1, hL, hBN, hcent, hcyc, hodd⟩ := sStarFacts hc h
  have huniq := unique_pcomponent hc h
  have hLn := normalizer_of_unique hL huniq
  have hinn := inducesInner_spor hc hOut h hsp
  have hdec := exists_decomp_mod_core hc h hinn
  have hel := decomp_in_zpowers hc h66 h hsp hdec
  have hBL : B ≤ (B ⊓ L) ⊔ Subgroup.zpowers x := by
    intro b hb
    obtain ⟨l, hl, i, rfl⟩ := hel b hb
    have hxi : x ^ i ∈ B := B.zpow_mem hxB i
    have hlB : l ∈ B := by
      have := B.mul_mem hb (B.inv_mem hxi)
      simpa using this
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hlB, hl⟩)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i)
  obtain ⟨T, hTx, hT2, hTB, hTT, hT1⟩ := exists_T hc h
  have hTL : T ≤ L := T_le_L hTx hTT hel hLn
  exact ⟨hB, hxB, hx1, hL, hBN, hcent, hcyc, huniq, hBL,
    ⟨T, hTL, hT2, hTB, hTT, T_not_le_core hc.ctx.prime hL hTx hT2 hT1 hTT hel hodd⟩⟩

end S8

end CFSG.LocalAnalysis.GLTheoremA
