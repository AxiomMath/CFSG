module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremB.A7Centralizer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.LocalAnalysis.LargeEvenClassification.ProperSections

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk map_gLAPPrimeCore barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff barXEquiv barXHom
  barXHom_surjective barXHom_ker isSubnormal_le' inf_gLAPPrimeCoreOf_eq gLAPPrimeCoreOf_le)
open scoped MatrixGroups

@[expose] def fixSub {K : Type} [Group K] (σ : MulAut K) : Subgroup K where
  carrier := {x | σ x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv, ha]

theorem mem_fixSub {K : Type} [Group K] {σ : MulAut K} {x : K} :
    x ∈ fixSub σ ↔ σ x = x :=
  Iff.rfl

@[expose] def Input23_2AutStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (D : Type) [Group D] [Finite D] (ψ : D →* MulAut K),
    Function.Injective ψ → IsAltType 7 K → IsPGroup 3 D → Nat.card D = 9 →
      (⊤ : Subgroup K) ≤ ⨆ (d : D) (_ : d ≠ 1), pCoreOf 2 (fixSub (ψ d))

@[expose] def Cex134_O2Statement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m p B M E A D T L), p = 3 → GLAPPrimeCoreOf p L ≤ pCoreOf 2 L

@[expose] def Sec13_compStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T L : Subgroup G}
    (h : Sec13 G m p B M E A D T), GLAPComponent p (Iof p M D) L →
      GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤
        Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M))

theorem exists_fixed_mem_coset {G : Type} [Group G] [Finite G] (d : G) (hd : d ^ 3 = 1)
    (Q : Subgroup G) [Finite Q] (hcop : ¬ 3 ∣ Nat.card Q) (hQn : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q)
    (x : G) (hx : x⁻¹ * (d * x * d⁻¹) ∈ Q) :
    ∃ q ∈ Q, d * (x * q) * d⁻¹ = x * q := by
  classical
  have hφ : ∀ q ∈ Q, x⁻¹ * (d * (x * q) * d⁻¹) ∈ Q := by
    intro q hq
    have e : x⁻¹ * (d * (x * q) * d⁻¹) = (x⁻¹ * (d * x * d⁻¹)) * (d * q * d⁻¹) := by group
    rw [e]
    exact Q.mul_mem hx (hQn q hq)
  let f : Function.End Q := fun q => ⟨x⁻¹ * (d * (x * q) * d⁻¹), hφ q q.2⟩
  have hiter : ∀ (n : ℕ) (q : Q), ((f ^ n) q : G) = x⁻¹ * (d ^ n * (x * q) * (d ^ n)⁻¹) := by
    intro n
    induction n with
    | zero =>
      intro q
      show (q : G) = x⁻¹ * (d ^ 0 * (x * q) * (d ^ 0)⁻¹)
      simp
    | succ n ih =>
      intro q
      have e1 : ((f ^ (n + 1)) q : G) = x⁻¹ * (d * (x * ((f ^ n) q : G)) * d⁻¹) := by
        show ((f^[n + 1] q : Q) : G) = _
        rw [Function.iterate_succ_apply']
        rfl
      rw [e1, ih q, pow_succ' d n]
      simp only [mul_inv_rev]
      group
  have hf3 : f ^ 3 = 1 := by
    funext q
    apply Subtype.ext
    show ((f ^ 3) q : G) = (q : G)
    rw [hiter 3 q, hd]
    simp
  have hf : f ^ 3 ^ 1 = 1 := by simpa using hf3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fintype Q := Fintype.ofFinite Q
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have hne : Fintype.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    apply hcop
    rw [Nat.card_eq_fintype_card]
    exact (Nat.modEq_zero_iff_dvd).1 hmod
  obtain ⟨⟨q, hq⟩⟩ := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  have hq' : f q = q := Function.mem_fixedPoints_iff.1 hq
  refine ⟨q, q.2, ?_⟩
  have h1 : x⁻¹ * (d * (x * q) * d⁻¹) = (q : G) := congrArg Subtype.val hq'
  calc d * (x * q) * d⁻¹ = x * (x⁻¹ * (d * (x * q) * d⁻¹)) := by group
    _ = x * q := by rw [h1]


theorem barX_mono_of_le {G : Type} [Group G] (p : ℕ) {M X Y : Subgroup G} (h : X ≤ Y) :
    barX p M X ≤ barX p M Y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)), rfl⟩

theorem mem_barX_iff {G : Type} [Group G] (p : ℕ) {M X : Subgroup G}
    (y : ↥M ⧸ GLAPPrimeCore p ↥M) :
    y ∈ barX p M X ↔ ∃ x : ↥M, (x : G) ∈ X ∧ QuotientGroup.mk' (GLAPPrimeCore p ↥M) x = y := by
  unfold barX
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem isPGroup_barX {G : Type} [Group G] [Finite G] {p q : ℕ} {M X : Subgroup G}
    (hX : IsPGroup q ↥X) : IsPGroup q ↥(barX p M X) := by
  intro y
  obtain ⟨x, hxX, hxy⟩ := (mem_barX_iff p (y : ↥M ⧸ GLAPPrimeCore p ↥M)).1 y.2
  obtain ⟨k, hk⟩ := hX ⟨(x : G), hxX⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hxk : x ^ q ^ k = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hxy, ← map_pow, hxk, map_one]

theorem conj_mem_glaPPrimeCoreOf {G : Type} [Group G] (p : ℕ) {L : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) {q : G} (hq : q ∈ GLAPPrimeCoreOf p L) :
    d * q * d⁻¹ ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨hqL, hqc⟩ := (mem_gLAPPrimeCoreOf_iff p L q).1 hq
  have hconj : d * q * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hd q).1 hqL
  have hmap := map_gLAPPrimeCore p (Subgroup.normalizerMonoidHom L ⟨d, hd⟩)
  have hmem : Subgroup.normalizerMonoidHom L ⟨d, hd⟩ ⟨q, hqL⟩ ∈ GLAPPrimeCore p ↥L := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hqc
  have key : Subgroup.normalizerMonoidHom L ⟨d, hd⟩ ⟨q, hqL⟩ = ⟨d * q * d⁻¹, hconj⟩ := by
    apply Subtype.ext
    rfl
  rw [key] at hmem
  exact (mem_gLAPPrimeCoreOf_iff p L _).2 ⟨hconj, hmem⟩


theorem exists_mk_pCore_of_fixed {G : Type} [Group G] [Finite G] {L : Subgroup G} {d : G}
    (hdL : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hQ2 : IsPGroup 2 ↥(GLAPPrimeCoreOf 3 L))
    (k : ↥L ⧸ GLAPPrimeCore 3 ↥L) (hk : k ∈ pCoreOf 2 (fixSub (barAut 3 L ⟨d, hdL⟩))) :
    ∃ y : ↥L, (y : G) ∈ pCoreOf 2 (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      (QuotientGroup.mk y : ↥L ⧸ GLAPPrimeCore 3 ↥L) = k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ := barAut 3 L ⟨d, hdL⟩ with hσ
  set Q : Subgroup G := GLAPPrimeCoreOf 3 L with hQ
  set H : Subgroup G := L ⊓ Subgroup.centralizer ({d} : Set G) with hH
  set P := pCoreOf 2 (fixSub σ) with hP
  have hcop : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
    rw [hn]
    intro h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hQn : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q := fun q hq => conj_mem_glaPPrimeCoreOf 3 hdL hq
  have hHL : H ≤ L := inf_le_left
  let φ : ↥H →* (↥L ⧸ GLAPPrimeCore 3 ↥L) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hHL)
  have hφ_apply : ∀ h : ↥H, φ h = QuotientGroup.mk (⟨(h : G), hHL h.2⟩ : ↥L) := fun h => rfl
  have hcomm : ∀ h : ↥H, d * (h : G) * d⁻¹ = h := by
    intro h
    have hc : (h : G) * d = d * (h : G) := (Subgroup.mem_centralizer_singleton_iff).1 h.2.2
    calc d * (h : G) * d⁻¹ = (h : G) * d * d⁻¹ := by rw [← hc]
      _ = (h : G) := by group
  have hφfix : ∀ h : ↥H, φ h ∈ fixSub σ := by
    intro h
    rw [mem_fixSub, hφ_apply, hσ, barAut_mk]
    congr 1
    apply Subtype.ext
    exact hcomm h
  set W' : Subgroup ↥H := P.comap φ with hW'
  have hW'norm : W'.Normal := by
    refine ⟨fun w hw g => ?_⟩
    have hw' : φ w ∈ P := hw
    have hg : φ g ∈ Subgroup.normalizer (P : Set (↥L ⧸ GLAPPrimeCore 3 ↥L)) :=
      le_normalizer_pCoreOf 2 (fixSub σ) (hφfix g)
    have hc := (Subgroup.mem_normalizer_iff.1 hg (φ w)).1 hw'
    show φ (g * w * g⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hc
  have hW'p : IsPGroup 2 ↥W' := by
    intro w
    have hw1 : φ w.1 ∈ P := w.2
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fixSub σ)) ⟨φ w.1, hw1⟩
    have ha' : φ w.1 ^ 2 ^ a = 1 := congrArg Subtype.val ha
    set y : ↥H := w.1 ^ 2 ^ a with hy
    have hφy : φ y = 1 := by rw [hy, map_pow, ha']
    have hyQ : (y : G) ∈ Q := by
      have h1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (Subgroup.inclusion hHL y)) = 1 := hφy
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      exact (mem_gLAPPrimeCoreOf_iff 3 L (y : G)).2 ⟨(Subgroup.inclusion hHL y).2, h2⟩
    obtain ⟨b, hb⟩ := hQ2 ⟨(y : G), hyQ⟩
    have hb' : (y : G) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    have hy2 : y ^ 2 ^ b = 1 := Subtype.ext (by simpa using hb')
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    have : (w.1 : ↥H) ^ 2 ^ a = y := rfl
    rw [this, hy2]
  have hWle : W' ≤ CFSG.pCore 2 ↥H := CFSG.LieType.BorelTits.le_pCore 2 hW'norm hW'p
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
  have hkfix : σ (QuotientGroup.mk x) = QuotientGroup.mk x :=
    (mem_fixSub).1 ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) hk)
  rw [hσ, barAut_mk] at hkfix
  have h1 : ((L.normalizerMonoidHom ⟨d, hdL⟩ x)⁻¹ * x : ↥L) ∈ GLAPPrimeCore 3 ↥L :=
    QuotientGroup.eq.1 hkfix
  have hx : (x : G)⁻¹ * (d * (x : G) * d⁻¹) ∈ Q := by
    have h2 : ((L.normalizerMonoidHom ⟨d, hdL⟩ x)⁻¹ * x : ↥L)⁻¹ ∈ GLAPPrimeCore 3 ↥L :=
      inv_mem h1
    have hcoe : ((L.normalizerMonoidHom ⟨d, hdL⟩ x : ↥L) : G) = d * (x : G) * d⁻¹ := rfl
    have h3 := (mem_gLAPPrimeCoreOf_iff 3 L (((L.normalizerMonoidHom ⟨d, hdL⟩ x)⁻¹ * x : ↥L)⁻¹ : G)).2
      ⟨((L.normalizerMonoidHom ⟨d, hdL⟩ x)⁻¹ * x : ↥L)⁻¹.2, h2⟩
    have e : (((L.normalizerMonoidHom ⟨d, hdL⟩ x)⁻¹ * x : ↥L)⁻¹ : G) = (x : G)⁻¹ * (d * (x : G) * d⁻¹) := by
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, hcoe]
      group
    rw [e] at h3
    exact h3
  obtain ⟨q, hqQ, hq⟩ := exists_fixed_mem_coset d hd3 Q hcop hQn (x : G) hx
  have hqL : q ∈ L := gLAPPrimeCoreOf_le 3 L hqQ
  have hxq : (x : G) * q ∈ L := L.mul_mem x.2 hqL
  let y0 : ↥L := ⟨(x : G) * q, hxq⟩
  have hcen : (x : G) * q ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * q * d = d * ((x : G) * q) * d⁻¹ * d := by rw [hq]
      _ = d * ((x : G) * q) := by group
  have hy0H : (y0 : G) ∈ H := ⟨hxq, hcen⟩
  have hmk : (QuotientGroup.mk y0 : ↥L ⧸ GLAPPrimeCore 3 ↥L) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    have hq' : y0⁻¹ * x = (⟨q⁻¹, L.inv_mem hqL⟩ : ↥L) := by
      apply Subtype.ext
      simp [y0, mul_inv_rev, mul_assoc]
    rw [hq']
    obtain ⟨_, h2⟩ := (mem_gLAPPrimeCoreOf_iff 3 L q⁻¹).1 (inv_mem hqQ)
    exact h2
  refine ⟨y0, ?_, hmk⟩
  have hφw0 : φ ⟨(y0 : G), hy0H⟩ = QuotientGroup.mk x := by
    rw [hφ_apply]
    exact hmk
  have hw0 : (⟨(y0 : G), hy0H⟩ : ↥H) ∈ W' := by
    rw [hW', Subgroup.mem_comap, hφw0]
    exact hk
  have hw0core := hWle hw0
  exact Subgroup.mem_map.2 ⟨_, hw0core, rfl⟩


theorem eq_bot_of_normal_two {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7))
    (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 ↥N) : N = ⊥ := by
  haveI := S7.isSimple_Alt7
  have hN' : (N.map e.toMonoidHom).Normal := inferInstance
  have hN2 : IsPGroup 2 ↥(N.map e.toMonoidHom) :=
    hN.of_equiv (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map e.toMonoidHom) with hbot | htop
  · rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hmem : e n ∈ N.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hn
    rw [hbot, Subgroup.mem_bot] at hmem
    exact e.injective (by rw [hmem, map_one])
  · exfalso
    apply S7.not_isPGroup_two_Alt7
    have htop2 : IsPGroup 2 ↥(⊤ : Subgroup (alternatingGroup (Fin 7))) := htop ▸ hN2
    exact htop2.of_equiv Subgroup.topEquiv

theorem mk_eq_of_mem_glaPPrimeCoreOf {G : Type} [Group G] (p : ℕ) {M : Subgroup G} {a b : G}
    (ha : a ∈ M) (hb : b ∈ M) (h : a⁻¹ * b ∈ GLAPPrimeCoreOf p M) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨a, ha⟩ : ↥M ⧸ GLAPPrimeCore p ↥M) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hb⟩ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  obtain ⟨_, h2⟩ := (mem_gLAPPrimeCoreOf_iff p M (a⁻¹ * b)).1 h
  convert h2 using 1

theorem glaPPrimeCore_centralizer_le_piStar {G : Type} [Group G] (p : ℕ) {D : Subgroup G} {d : G}
    (hd : d ∈ D) (hd1 : d ≠ 1) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) ≤ piStar p D :=
  le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hd1 le_sup_right))


theorem prop134_of_cex_of_inputs
    (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (h136 : Lemma136Statement) (hI23 : Input23_2AutStatement)
    (hO2 : Cex134_O2Statement) (hcomp : Sec13_compStatement) :
    Prop134_of_cexStatement := by
  intro G _ _ m p B M E A D T L h
  have hS : GLStanding G m p := h.standing
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hp2 : p ≠ 2 := hS.ne_two
  have hD : IsEkIn p 2 A D := h.hD
  have hDA : D ≤ A := hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hyp : Prop95Hyp p M D :=
    { twoLocal := h.pre.1.1
      le := hDM
      plane := ⟨hD.2.1, hD.2.2⟩
      clause_a := fun d hd hd1 =>
        (pCoreOf_two_le_glaPPrimeCoreOf hS.prime hp2 _).trans (h111 h.toSec11 (hDA hd) hd1)
      clause_b := fun d hd hd1 => by
        by_contra hc
        exact h121 (⟨h.toSec11, ⟨hDA hd, hd1⟩, hc⟩ : Cex121 G m p B M E A d)
      clause_c := h.hT1.trans (h.hT2.trans (gammaStar_le_gammaD p D)) }
  have hP := hP95 G m p hS M D hyp
  obtain ⟨hLc, hnc⟩ := hcomp h.toSec13 h.hL
  have hγ : Prop95Gamma p M D L := by
    rcases (hP.2.2 L hLc).2 with hc | ⟨-, ha | hb | hg⟩
    · exact absurd ((barX_mono_of_le p (gammaStar_le_gammaD p D)).trans hc) hnc
    · exact absurd ha (fun ha => h.notAB (Or.inl ha))
    · exact absurd hb (fun hb => h.notAB (Or.inr hb))
    · exact hg
  unfold Prop95Gamma at hγ
  obtain ⟨hp3, e, -⟩ := hγ
  subst hp3
  have hsub : CFSG.Open.IsSubnormal L M := hLc.2.1
  have hLM : L ≤ M := hLc.1
  have hpr : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ2' : GLAPPrimeCoreOf 3 L ≤ pCoreOf 2 L := hO2 h rfl
  have hQ2 : IsPGroup 2 ↥(GLAPPrimeCoreOf 3 L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hQ2'
  obtain ⟨⟨hDN, hC⟩, hO⟩ := h136 h
  have hBE : barOf 3 L ≃* ↥(barX 3 M L) := barXEquiv hpr hsub
  have hAlt : IsAltType 7 (barOf 3 L) := ⟨hBE.trans e⟩
  let ψ : ↥D →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hDN)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz' : barAut 3 L (Subgroup.inclusion hDN z) = 1 := hz
    have hmem : (z : G) ∈ centBar 3 ⊤ L :=
      ⟨Subgroup.mem_map.2 ⟨Subgroup.inclusion hDN z, (MonoidHom.mem_ker).2 hz', rfl⟩,
        Subgroup.mem_top _⟩
    exact Subtype.ext (hC z z.2 hmem)
  have hPG : IsPGroup 3 ↥D := IsPGroup.iff_card.2 ⟨2, hD.2.2⟩
  have hcardD : Nat.card ↥D = 9 := by rw [hD.2.2]; norm_num
  have hgen := hI23 (barOf 3 L) ↥D ψ hinj hAlt hPG hcardD
  let Ψ : Subgroup (barOf 3 L) :=
    ((piStar 3 D ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))
  have hΨ : (⊤ : Subgroup (barOf 3 L)) ≤ Ψ := by
    refine hgen.trans (iSup₂_le fun d hd => ?_)
    intro k hk
    have hd_ne : (d : G) ≠ 1 := fun h1 => hd (Subtype.ext h1)
    have hd3 : (d : G) ^ 3 = 1 := hD.2.1.2 _ d.2
    obtain ⟨y, hy, hymk⟩ := exists_mk_pCore_of_fixed (hDN d.2) hd3 hQ2 k hk
    have hyP : (y : G) ∈ piStar 3 D :=
      glaPPrimeCore_centralizer_le_piStar 3 d.2 hd_ne (hO d.1 d.2 hd_ne hy)
    exact Subgroup.mem_map.2 ⟨y, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hyP, y.2⟩), hymk⟩
  have hcover : ∀ x : G, x ∈ L → ∃ l : G, l ∈ L ∧ l ∈ piStar 3 D ∧ l⁻¹ * x ∈ GLAPPrimeCoreOf 3 L := by
    intro x hxL
    obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.1 (hΨ (Subgroup.mem_top (QuotientGroup.mk (⟨x, hxL⟩ : ↥L))))
    have h1 : l⁻¹ * (⟨x, hxL⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := QuotientGroup.eq.1 hlk
    have hmem : (l : G)⁻¹ * x ∈ GLAPPrimeCoreOf 3 L := by
      refine (mem_gLAPPrimeCoreOf_iff 3 L _).2 ⟨L.mul_mem (L.inv_mem l.2) hxL, ?_⟩
      have e : (⟨(l : G)⁻¹ * x, L.mul_mem (L.inv_mem l.2) hxL⟩ : ↥L) = l⁻¹ * ⟨x, hxL⟩ := by
        apply Subtype.ext
        simp
      rw [e]
      exact h1
    exact ⟨(l : G), l.2, (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hl)).1, hmem⟩
  have hrep : ∀ y ∈ barX 3 M L, ∃ l : ↥M, (l : G) ∈ piStar 3 D ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) l = y := by
    intro y hy
    obtain ⟨x, hxL, rfl⟩ := (mem_barX_iff 3 _).1 hy
    obtain ⟨l, hlL, hlpi, hlx⟩ := hcover x hxL
    have hlM : l ∈ M := hLM hlL
    refine ⟨⟨l, hlM⟩, hlpi, ?_⟩
    exact mk_eq_of_mem_glaPPrimeCoreOf 3 hlM x.2 (glaPPrimeCoreOf_le_of_isSubnormal hpr hsub hlx)
  have hU2 : IsPGroup 2 ↥(barX 3 M (pCoreOf 2 (piStar 3 D))) :=
    isPGroup_barX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (piStar 3 D))
  have hGGU : barX 3 M (gammaStar 3 D) ≤ barX 3 M (pCoreOf 2 (piStar 3 D)) :=
    barX_mono_of_le 3 (show gammaStar 3 D ≤ pCoreOf 2 (piStar 3 D) from inf_le_right)
  have hconjU : ∀ l : ↥M, (l : G) ∈ piStar 3 D → ∀ u ∈ barX 3 M (pCoreOf 2 (piStar 3 D)),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) l * u * (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) l)⁻¹ ∈
        barX 3 M (pCoreOf 2 (piStar 3 D)) := by
    intro l hl u hu
    obtain ⟨v, hv, rfl⟩ := (mem_barX_iff 3 u).1 hu
    rw [← map_inv, ← map_mul, ← map_mul]
    refine (mem_barX_iff 3 _).2 ⟨l * v * l⁻¹, ?_, rfl⟩
    show (l : G) * (v : G) * (l : G)⁻¹ ∈ pCoreOf 2 (piStar 3 D)
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (piStar 3 D) hl) (v : G)).1 hv
  have hconjY : ∀ y ∈ barX 3 M L, ∀ u ∈ barX 3 M (pCoreOf 2 (piStar 3 D)),
      y * u * y⁻¹ ∈ barX 3 M (pCoreOf 2 (piStar 3 D)) ∧
        y⁻¹ * u * y ∈ barX 3 M (pCoreOf 2 (piStar 3 D)) := by
    intro y hy u hu
    obtain ⟨l, hl, rfl⟩ := hrep y hy
    refine ⟨hconjU l hl u hu, ?_⟩
    have := hconjU l⁻¹ (piStar 3 D |>.inv_mem hl) u hu
    simpa [map_inv] using this
  have hNormGG : ∀ g ∈ barX 3 M (gammaStar 3 D),
      g ∈ Subgroup.normalizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
    fun g hg => (hP.2.2 L hLc).1 (barX_mono_of_le 3 (gammaStar_le_gammaD 3 D) hg)
  have hcomm : ∀ g ∈ barX 3 M (gammaStar 3 D), ∀ y ∈ barX 3 M L, g * y = y * g := by
    intro g hg y hy
    have hgU : g ∈ barX 3 M (pCoreOf 2 (piStar 3 D)) := hGGU hg
    have hginvN : g⁻¹ ∈ Subgroup.normalizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := inv_mem (hNormGG g hg)
    have hcKM : g⁻¹ * y⁻¹ * g * y ∈ barX 3 M L := by
      have h1 : g⁻¹ * y⁻¹ * g⁻¹⁻¹ ∈ barX 3 M L :=
        (Subgroup.mem_normalizer_iff.1 hginvN y⁻¹).1 ((barX 3 M L).inv_mem hy)
      have e2 : g⁻¹ * y⁻¹ * g * y = (g⁻¹ * y⁻¹ * g⁻¹⁻¹) * y := by group
      rw [e2]
      exact (barX 3 M L).mul_mem h1 hy
    have hcU : g⁻¹ * y⁻¹ * g * y ∈ barX 3 M (pCoreOf 2 (piStar 3 D)) := by
      have h2 := (hconjY y hy g hgU).2
      have e3 : g⁻¹ * y⁻¹ * g * y = g⁻¹ * (y⁻¹ * g * y) := by group
      rw [e3]
      exact (barX 3 M (pCoreOf 2 (piStar 3 D))).mul_mem ((barX 3 M (pCoreOf 2 (piStar 3 D))).inv_mem hgU) h2
    set N₀ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M) :=
      barX 3 M L ⊓ barX 3 M (pCoreOf 2 (piStar 3 D)) with hN₀
    have hN0normal : (N₀.subgroupOf (barX 3 M L)).Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnK, hnU⟩ := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have := (barX 3 M L).mul_mem ((barX 3 M L).mul_mem k.2 hnK) ((barX 3 M L).inv_mem k.2)
        simpa [mul_assoc] using this
      · have := (hconjY k.1 k.2 _ hnU).1
        simpa [mul_assoc] using this
    have hN0p : IsPGroup 2 ↥(N₀.subgroupOf (barX 3 M L)) :=
      (hU2.to_le (inf_le_right : N₀ ≤ barX 3 M (pCoreOf 2 (piStar 3 D)))).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : N₀ ≤ barX 3 M L)).symm
    haveI := hN0normal
    have hbot := eq_bot_of_normal_two e (N₀.subgroupOf (barX 3 M L)) hN0p
    have hcmem : (⟨g⁻¹ * y⁻¹ * g * y, hcKM⟩ : ↥(barX 3 M L)) ∈ N₀.subgroupOf (barX 3 M L) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hcKM, hcU⟩)
    rw [hbot, Subgroup.mem_bot] at hcmem
    have hc1 : g⁻¹ * y⁻¹ * g * y = 1 := by simpa using congrArg Subtype.val hcmem
    have h2 : y⁻¹ * g * y = g := by
      calc y⁻¹ * g * y = g * (g⁻¹ * y⁻¹ * g * y) := by group
        _ = g := by rw [hc1, mul_one]
    calc g * y = y * (y⁻¹ * g * y) := by group
      _ = y * g := by rw [h2]
  have hcent : barX 3 M (gammaStar 3 D) ≤
      Subgroup.centralizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm g hg y hy).symm
  exact absurd hcent hnc


@[expose] def BStar137Statement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T),
    ∃ y ∈ M, IsPGroup p ↥(A ⊔ GLBConj y B) ∧
      ∀ x ∈ GLBConj y B, ∀ g ∈ gammaStar p D, x * g * x⁻¹ * g⁻¹ ∈ pCoreOf 2 M

theorem lemma137_i_of_bstar (hB : BStar137Statement) : Lemma137_iStatement := by
  intro G _ _ m p B M E A D T h
  obtain ⟨y, hyM, hpg, hcomm⟩ := hB h
  have hT1 : pCoreOf 2 M ≤ T := h.hT1
  have hT2 : T ≤ gammaStar p D := h.hT2
  have hkey : ∀ x ∈ GLBConj y B, ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
    intro x hx t ht
    have hc : x * t * x⁻¹ * t⁻¹ ∈ pCoreOf 2 M := hcomm x hx t (hT2 ht)
    have e : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact T.mul_mem (hT1 hc) ht
  have hnorm : GLBConj y B ≤ Nof T := by
    intro x hx
    rw [Nof, Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => hkey x hx t ht, fun ht => ?_⟩
    have h1 := hkey x⁻¹ ((GLBConj y B).inv_mem hx) (x * t * x⁻¹) ht
    have e : x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t := by group
    rw [e] at h1
    exact h1
  exact h.choiceB (GLBConj y B) ⟨y, hyM, rfl⟩ hpg hnorm

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
