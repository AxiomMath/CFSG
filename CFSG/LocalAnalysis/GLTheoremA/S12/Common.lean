module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma88
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.I2_5
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Cfg12 (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) : Prop where
  ctx : S12Ctx G m p
  tri : Triple12 G p B x L
  std : GLAStdSub p B x L D K

namespace Cfg12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem pre (h : Cfg12 G m p B x L D K) : GLAStdSubPre p B x L D K := h.std.1

theorem prime (h : Cfg12 G m p B x L D K) : p.Prime := h.ctx.ctx.ctx.prime

theorem odd (h : Cfg12 G m p B x L D K) : p ≠ 2 := h.ctx.ctx.ctx.odd

theorem DB (h : Cfg12 G m p B x L D K) : D ≤ B := h.pre.1

theorem elem (h : Cfg12 G m p B x L D K) : IsElemAbelian p D := h.pre.2.1

theorem card_D (h : Cfg12 G m p B x L D K) : Nat.card D = p ^ 2 := h.pre.2.2.1

theorem xD (h : Cfg12 G m p B x L D K) : x ∈ D := h.pre.2.2.2.1

theorem K_eq (h : Cfg12 G m p B x L D K) : K = GLALayer (L ⊓ Subgroup.centralizer (D : Set G)) := h.pre.2.2.2.2.1

theorem K_comp (h : Cfg12 G m p B x L D K) : IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set G)) :=
  h.pre.2.2.2.2.2.1

theorem D_eq (h : Cfg12 G m p B x L D K) : D = B ⊓ Subgroup.centralizer (K : Set G) := h.pre.2.2.2.2.2.2

theorem K_qs (h : Cfg12 G m p B x L D K) : CFSG.Open.IsQuasisimple ↥K := h.K_comp.2.2

theorem K_le_L (h : Cfg12 G m p B x L D K) : K ≤ L := h.K_comp.1.trans inf_le_left

theorem K_le_cs (h : Cfg12 G m p B x L D K) : K ≤ Subgroup.centralizer (D : Set G) := h.K_comp.1.trans inf_le_right

theorem card_B (h : Cfg12 G m p B x L D K) : Nat.card B = p ^ m := h.ctx.card_B h.tri.bmax

theorem four_le (h : Cfg12 G m p B x L D K) : 4 ≤ m := h.ctx.rank ▸ h.ctx.ctx.ctx.rank_ge

theorem pow_four_le (h : Cfg12 G m p B x L D K) : p ^ 4 ≤ Nat.card B := by
  rw [h.card_B]
  exact Nat.pow_le_pow_right h.prime.pos h.four_le

end Cfg12

structure NbrCfg (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) (y : G)
    (J : Subgroup G) : Prop where
  cfg : Cfg12 G m p B x L D K
  shat : GLASHat p B y J
  nb : GLANeighbor p x y J D K

namespace NbrCfg

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G} {y : G} {J : Subgroup G}

theorem bmax (h : NbrCfg G m p B x L D K y J) : GLAIsBmax p B := h.shat.1

theorem yB (h : NbrCfg G m p B x L D K y J) : y ∈ B := h.shat.2.1

theorem y_ne_one (h : NbrCfg G m p B x L D K y J) : y ≠ 1 := h.shat.2.2.1

theorem J_le_cy (h : NbrCfg G m p B x L D K y J) : J ≤ Subgroup.centralizer ({y} : Set G) := h.shat.2.2.2.1

theorem J_comp (h : NbrCfg G m p B x L D K y J) : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) J := h.shat.2.2.2.2.1

theorem J_cent (h : NbrCfg G m p B x L D K y J) : CentModEqZpowers p B J y := by
  intro b hb
  have hb' := h.shat.2.2.2.2.2 b
  exact ⟨fun hc => hb'.1 ⟨hb, hc.1, hc.2⟩, fun hz => ⟨(hb'.2 hz).2.1, (hb'.2 hz).2.2⟩⟩

theorem D_closure (h : NbrCfg G m p B x L D K y J) : D = Subgroup.closure {x, y} := h.nb.1

theorem not_cent_x (h : NbrCfg G m p B x L D K y J) :
    ¬ (⁅J, Subgroup.zpowers x⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p J := h.nb.2.2

theorem J_le_Ky (h : NbrCfg G m p B x L D K y J) : J ≤ Ky p K y := by
  rw [Ky, closureIn_eq_iSup_gLBConj]
  exact h.nb.2.1

end NbrCfg

namespace Cfg12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem exists_y (h : Cfg12 G m p B x L D K) : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
  by_contra hcon
  push Not at hcon
  have hD : D ≤ Subgroup.zpowers x := hcon
  have hcard := Subgroup.card_le_of_le hD
  rw [h.card_D, Nat.card_zpowers] at hcard
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one
  rw [hord] at hcard
  have := hp.two_le
  nlinarith

theorem D_eq_sup (h : Cfg12 G m p B x L D K) {y : G} (hy : y ∈ D) (hyx : y ∉ Subgroup.zpowers x) :
    D = Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
  le_antisymm (S8.L89.le_sup_zpowers h.prime h.elem h.card_D h.xD h.tri.ne_one hy hyx)
    (sup_le (Subgroup.zpowers_le.2 h.xD) (Subgroup.zpowers_le.2 hy))

theorem cs_eq (h : Cfg12 G m p B x L D K) {y : G} (hy : y ∈ D) (hyx : y ∉ Subgroup.zpowers x) :
    Subgroup.centralizer (D : Set G) = Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) :=
  S8.L89.centralizer_eq_inf h.prime h.elem h.card_D h.xD h.tri.ne_one hy hyx

end Cfg12

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem three_subgroups_mod {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set K := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hmap : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf K, B.subgroupOf K⁆, C.subgroupOf K⁆).map K.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔
        ⁅⁅(A.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)),
          (B.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆,
          (C.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem mem_normalizer_inf' {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.1 hA w) (Subgroup.mem_normalizer_iff.1 hC w)

theorem mem_normalizer_sup' {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hC ⊢
  unfold GLBConj at hA hC ⊢
  rw [Subgroup.map_sup, hA, hC]

theorem mem_zpowers_of_prime_order {x u : G} {q : ℕ} [Fact q.Prime] (hx : orderOf x = q)
    (hu : u ∈ Subgroup.zpowers x) (hu1 : u ≠ 1) : x ∈ Subgroup.zpowers u := by
  have hdord : orderOf u = q := by
    have h1 : orderOf u ∣ q := hx ▸ orderOf_dvd_of_mem_zpowers hu
    rcases (Nat.dvd_prime Fact.out).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hu1
    · exact h2
  have hle : Subgroup.zpowers u ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hu
  have heq : Subgroup.zpowers u = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hdord, hx])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem mem_normalizer_glaLayer' {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLALayer X : Set G) := by
  have hle : ∀ g ∈ Subgroup.normalizer (X : Set G), GLBConj g (GLALayer X) ≤ GLALayer X := by
    intro g hg
    refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun J hJ => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.HardMathSupport.Solomon.Coordinator.i25_isComponentOf_gLBConj hJ hg)
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (hle g hg) ?_
  have h := gLBConj_mono (g := g) (hle g⁻¹ (Subgroup.inv_mem _ hg))
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h

theorem B_norm_K (h : Cfg12 G m p B x L D K) : B ≤ Subgroup.normalizer (K : Set G) := by
  have hbcs : ∀ b ∈ B, b ∈ Subgroup.centralizer (D : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact isElemAbelian_commute h.tri.bmax.1 (h.DB hd) hb
  have hBX : B ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf h.tri.norm (fun b hb => Subgroup.le_normalizer (hbcs b hb))
  intro b hb
  rw [h.K_eq]
  exact mem_normalizer_glaLayer' (hBX hb)

theorem std_quot_catalog (h : Cfg12 G m p B x L D K) :
    IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) ∧ (∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a) ∧
      CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) := by
  have hKG : CFSG.Open.IsKGroup ↥K :=
    CFSG.Open.IsKGroup.of_le (kGroup_centralizer h.ctx.toS6 h.tri.ne_one) (h.K_le_L.trans h.tri.comp.1)
  exact ⟨h.K_qs.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K h.K_qs,
    CFSG.HardMathSupport.Solomon.LocalBalance.isCatalogGroup_center_quotient_of_isKGroup hKG h.K_qs⟩

theorem faithful_quot (h : Cfg12 G m p B x L D K) {b : G} (hb : b ∈ B)
    (hc : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ Subgroup.centralizer (K : Set G)) : b ∈ D := by
  have h1 : (⁅(⁅K, Subgroup.zpowers b⁆ : Subgroup G), K⁆ : Subgroup G) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hc
  have h2 : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ :=
    CFSG.LocalCores.perfect_double_commutator ⟨h.K_qs.1⟩ h1
  have h3 : K ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  rw [h.D_eq]
  refine ⟨hb, ?_⟩
  show b ∈ Subgroup.centralizer (K : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact ((Subgroup.mem_centralizer_iff.1 (h3 hk)) b (Subgroup.mem_zpowers b)).symm

theorem pRank_aut_ge (h : Cfg12 G m p B x L D K) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := B_norm_K h
  haveI : Group.IsPerfect ↥K := ⟨h.K_qs.1⟩
  let φ : ↥B →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K).comp
      (K.normalizerMonoidHom.comp (Subgroup.inclusion hBK))
  have hker : φ.ker ≤ D.subgroupOf B := by
    intro b hb
    have h0 : (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K)
        (K.normalizerMonoidHom (Subgroup.inclusion hBK b)) = 1 := hb
    have h1 : K.normalizerMonoidHom (Subgroup.inclusion hBK b) = 1 := by
      apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥K
      rw [h0, map_one]
    have h2 : Subgroup.inclusion hBK b ∈ K.normalizerMonoidHom.ker := h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    rw [Subgroup.mem_subgroupOf, h.D_eq]
    exact ⟨b.2, h2⟩
  have hcardD : Nat.card (D.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.DB).toEquiv]
    exact h.card_D
  have hkerdvd : Nat.card φ.ker ∣ p ^ 2 := hcardD ▸ Subgroup.card_dvd_of_le hker
  obtain ⟨f, hf2, hfker⟩ := (Nat.dvd_prime_pow hp).1 hkerdvd
  have hrdvd : Nat.card φ.range ∣ p ^ m := h.card_B ▸ Subgroup.card_range_dvd φ
  obtain ⟨e, hem, herange⟩ := (Nat.dvd_prime_pow hp).1 hrdvd
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hfker, herange, h.card_B, ← pow_add] at hmul
  have hfe : f + e = m := Nat.pow_right_injective hp.two_le hmul
  have h4 := h.four_le
  have he2 : 2 ≤ e := by omega
  have hrange_el : IsElemAbelian p φ.range := by
    have := CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf h.tri.bmax.1 B) φ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  obtain ⟨E, -, hEel, hEcard⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hrange_el
    (n := 2) (by rw [herange]; exact pow_dvd_pow p he2)
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hEcard

theorem std_dvd (h : Cfg12 G m p B x L D K)
    (i713 : CFSG.HardMathSupport.Solomon.Coordinator.I_7_13_1_pPrime) :
    p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  by_contra hnd
  obtain ⟨hs, hna, hcat⟩ := std_quot_catalog h
  have h1 := i713 p h.prime h.odd (↥K ⧸ Subgroup.center ↥K) hs hna hcat hnd
  have h2 := pRank_aut_ge h
  omega

theorem eq_of_barX_top_of_central {p : ℕ} {K J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hOZ : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K) (hJK : J ≤ K) (hbar : barX p K J = ⊤) : J = K := by
  classical
  have hdec : ∀ g : ↥K, ∃ j : ↥K, j ∈ J.subgroupOf K ∧ ∃ u : ↥K, u ∈ Subgroup.center ↥K ∧ g = j * u := by
    intro g
    have hle : barX p K K ≤ barX p K J := by rw [barX_self, hbar]
    obtain ⟨j, hjJ, hjz⟩ := exists_of_barX_le hle g.2 g.2
    unfold GLAPPrimeCoreOf at hjz
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hjz
    refine ⟨⟨j, hJK hjJ⟩, Subgroup.mem_subgroupOf.2 hjJ, u, hOZ hu, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (u : G) = j⁻¹ * g from hue, mul_inv_cancel_left]
  have hcomm : commutator ↥K ≤ J.subgroupOf K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨j₁, hj₁, u₁, hu₁, rfl⟩ := hdec g
    obtain ⟨j₂, hj₂, u₂, hu₂, rfl⟩ := hdec h
    rw [commutatorElement_mul_center_left hu₁, commutatorElement_mul_center_right hu₂,
      commutatorElement_def]
    exact (J.subgroupOf K).mul_mem ((J.subgroupOf K).mul_mem ((J.subgroupOf K).mul_mem hj₁ hj₂)
      ((J.subgroupOf K).inv_mem hj₁)) ((J.subgroupOf K).inv_mem hj₂)
  rw [hq.1, top_le_iff] at hcomm
  apply le_antisymm hJK
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥K) ∈ J.subgroupOf K := by
    rw [hcomm]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hmem

theorem glaPComponent_of_quasisimple' {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hKX : IsSubnormal K X)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hdvd : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    GLAPComponent p X K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card ↥K := hdvd.trans (Subgroup.card_quotient_dvd_card _)
  have hOp : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥K) := by
    have h := not_dvd_card_glaPPrimeCoreOf hp K
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  have hOne : GLAPPrimeCore p ↥K ≠ ⊤ := by
    intro h
    apply hOp
    rw [h, Subgroup.card_top]
    exact hpK
  have hOZ : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K :=
    le_center_of_normal_of_isQuasisimple hq (GLAPPrimeCore.normal p ↥K) hOne
  have hQ : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient hq _ hOZ
  obtain ⟨I, hI, hIbar⟩ := exists_glaPComponent_of_isQuasisimple hQ
  have hIK : I = K := eq_of_barX_top_of_central hq hOZ hI.1 hIbar
  have hKK : GLAPComponent p K K := hIK ▸ hI
  exact glaPComponent_of_isSubnormal' hp hKX hKK

theorem std_pcomp_L (h : Cfg12 G m p B x L D K) (hdvd : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) K :=
  glaPComponent_of_quasisimple' h.prime h.K_comp.2.1 h.K_qs hdvd

theorem std_comm_core_central (h : Cfg12 G m p B x L D K) (i145 : I145UsedAt G p)
    {P : Subgroup G} (hP : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) P) :
    (⁅(⁅P, GLAPPrimeCoreOf p P⁆ : Subgroup G), P⁆ : Subgroup G) = ⊥ := by
  have hp := h.prime
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G)) (Subgroup.centralizer (D : Set G)) :=
    h.tri.comp.2.1.inf_of_le (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.xD))
  have hPC := glaPComponent_of_isSubnormal' hp hsub hP
  have hPL : P ≤ GLAPLayer p (Subgroup.centralizer (D : Set G)) := le_sSup hPC
  have hOP : GLAPPrimeCoreOf p P ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hPC.2.1
  have hOPle : GLAPPrimeCoreOf p P ≤ P := Subgroup.map_subtype_le _
  have hDx : D ≤ Subgroup.centralizer ({x} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.elem hd h.xD)
  have hI := i145 hp h.odd _ D (kGroup_centralizer h.ctx.toS6 h.tri.ne_one) hDx (isPGroup_of_isElemAbelian h.elem)
  rw [inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.xD))] at hI
  have hPperf : (⁅P, P⁆ : Subgroup G) = P := glaPComponent_perfect hP
  have hPL₀ : P ≤ L := hP.1.trans inf_le_left
  have hY1 : (⁅P, GLAPPrimeCoreOf p P⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) :=
    (Subgroup.commutator_mono hPL hOP).trans hI
  have hY2 : (⁅P, GLAPPrimeCoreOf p P⁆ : Subgroup G) ≤ L :=
    ((Subgroup.commutator_mono le_rfl hOPle).trans hPperf.le).trans hPL₀
  have hY : (⁅P, GLAPPrimeCoreOf p P⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp h.tri.comp.2.1]
    exact le_inf hY2 hY1
  have hOL : (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) = ⊥ :=
    S9.commutator_eq_bot_of_isQuasisimple hp h.tri.comp (h.tri.qs h.ctx)
  rw [Subgroup.commutator_comm] at hOL
  exact le_bot_iff.1 ((Subgroup.commutator_mono hY hPL₀).trans hOL.le)

theorem primeCore_le_normalizer {C M : Subgroup G} (hM : GLAPComponent p C M) :
    GLAPPrimeCoreOf p C ≤ Subgroup.normalizer (M : Set G) := by
  have hNP : GLAPPrimeCoreOf p C ≤ preimBarX p C M := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show QuotientGroup.mk' (GLAPPrimeCore p ↥C) n ∈ barX p C M
    rw [h1]
    exact one_mem _
  exact hNP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX p hM.1)).1
    (glaPComponent_normal_preimBarX hM))

theorem comm_le_primeCore (hp : p.Prime) {C M : Subgroup G} (hM : GLAPComponent p C M) :
    (⁅M, GLAPPrimeCoreOf p C⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p M := by
  have hNM := primeCore_le_normalizer hM
  have hMN : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) :=
    hM.1.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p C))
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hM.2.1]
  refine le_inf (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing M _ hNM) ?_
  rw [Subgroup.commutator_comm]
  exact CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ M hMN

theorem not_isPGroup_of_isQuasisimple {Q : Type} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hq : CFSG.Open.IsQuasisimple Q) : ¬ IsPGroup q Q := by
  intro hPG
  haveI : Nontrivial Q := isQuasisimple_nontrivial hq
  haveI : Group.IsPerfect Q := ⟨hq.1⟩
  haveI : Group.IsNilpotent Q := hPG.isNilpotent
  exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem core_comm_eq_bot {X P : Subgroup G} (hP : GLAPComponent p X P)
    (hc : (⁅(⁅P, GLAPPrimeCoreOf p P⁆ : Subgroup G), P⁆ : Subgroup G) = ⊥) :
    (⁅P, GLAPPrimeCoreOf p P⁆ : Subgroup G) = ⊥ :=
  CFSG.LocalCores.perfect_double_commutator (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hP)) hc

theorem isQuasisimple_of_core_comm (hp : p.Prime) {X P : Subgroup G} (hP : GLAPComponent p X P)
    (hc : (⁅P, GLAPPrimeCoreOf p P⁆ : Subgroup G) = ⊥) : CFSG.Open.IsQuasisimple ↥P :=
  S9.isQuasisimple_of_commutator_eq_bot hp hP hc

theorem std_comp_quasi (h : Cfg12 G m p B x L D K) (i145 : I145UsedAt G p)
    {P : Subgroup G} (hP : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) P) :
    CFSG.Open.IsQuasisimple ↥P :=
  isQuasisimple_of_core_comm h.prime hP (core_comm_eq_bot hP (std_comm_core_central h i145 hP))

theorem std_layer_L (h : Cfg12 G m p B x L D K) (hdvd : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K))
    (hquasi : ∀ P : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) P → CFSG.Open.IsQuasisimple ↥P) :
    GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)) = K :=
  le_antisymm (sSup_le fun P hP => h.K_eq ▸ le_sSup ⟨hP.1, hP.2.1, hquasi P hP⟩) (le_sSup (std_pcomp_L h hdvd))

theorem layer_cs_eq' (h : Cfg12 G m p B x L D K) (hbal : LBalanceEqAt G p) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hxE : x ∈ E) :
    GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) = GLAPLayer p (Subgroup.centralizer (E : Set G)) := by
  have hp := h.prime
  have hxp : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_mem hE hxE
  have hcomm : ∀ d ∈ Subgroup.zpowers x, ∀ e ∈ E, d * e = e * d := fun d hd e he => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact Commute.zpow_left (show Commute x e from isElemAbelian_commute hE hxE he) n
  have h1 := hbal hp h.ctx.ctx.ctx.kProper (Subgroup.zpowers x) E hxp (isPGroup_of_isElemAbelian hE) hcomm
  rw [S3.centralizer_zpowers x, h.tri.layer h.ctx] at h1
  have hle : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.centralizer_le ?_
    simpa using hxE
  rwa [inf_eq_right.2 hle] at h1

theorem layer_cs_eq (h : Cfg12 G m p B x L D K) (hbal : LBalanceEqAt G p) :
    GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)) = GLAPLayer p (Subgroup.centralizer (D : Set G)) :=
  layer_cs_eq' h hbal h.elem h.xD

theorem B_inf_centMod_eq (h : Cfg12 G m p B x L D K) :
    B ⊓ centModSubgroup p L = Subgroup.zpowers x := by
  ext g
  constructor
  · rintro ⟨hgB, hg⟩
    exact (h.tri.cent h.ctx g hgB).1 (centMod_iff.2 hg)
  · intro hg
    have hgB : g ∈ B := (Subgroup.zpowers_le.2 h.tri.mem) hg
    exact ⟨hgB, centMod_iff.1 ((h.tri.cent h.ctx g hgB).2 hg)⟩

theorem card_B_inf_centMod_L (h : Cfg12 G m p B x L D K) : Nat.card ↥(B ⊓ centModSubgroup p L) = p := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  rw [B_inf_centMod_eq h, Nat.card_zpowers]
  exact orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one

theorem cx_le_normalizer_L (h : Cfg12 G m p B x L D K) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro t ht
  have hle : ∀ (g : G) (X : Subgroup G), GLBConj g (GLAPLayer p X) ≤ GLAPLayer p (GLBConj g X) := by
    intro g X
    refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun M hM => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_gLBConj hM g)
  have h1 := gLBConj_eq_of_forall_ge (F := GLAPLayer p) hle t (Subgroup.centralizer ({x} : Set G))
  rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer ht), h.tri.layer h.ctx] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 h1.symm

theorem closureIn_le_of_le_normalizer {K H L : Subgroup G} (hK : K ≤ L) (hH : H ≤ Subgroup.normalizer (L : Set G)) :
    closureIn K H ≤ L := by
  rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun a ha => ?_
  have h1 : GLBConj a K ≤ GLBConj a L := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono a hK
  rwa [mem_normalizer_iff_gLBConj_eq.1 (hH ha)] at h1

theorem std_pcomp (h : Cfg12 G m p B x L D K) (hdvd : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    GLAPComponent p (Subgroup.centralizer (D : Set G)) K :=
  glaPComponent_of_isSubnormal' h.prime
    (h.tri.comp.2.1.inf_of_le (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.xD))) (std_pcomp_L h hdvd)

end S12

structure CommonInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i713 : CFSG.HardMathSupport.Solomon.Coordinator.I_7_13_1_pPrime
  i145 : I145UsedAt G p
  bal : LBalanceEqAt G p
  i183 : Input18_3_4
  chev2 : Chev2DownAt G p
  i171one : I171OneAt G

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem std_layer (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) :
    GLAPLayer p (Subgroup.centralizer (D : Set G)) = K := by
  have hdvd := std_dvd h hin.i713
  have h1 := std_layer_L h hdvd (fun P hP => std_comp_quasi h hin.i145 hP)
  rw [← layer_cs_eq h hin.bal]
  exact h1

theorem std_pcomp' (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) :
    GLAPComponent p (Subgroup.centralizer (D : Set G)) K :=
  std_pcomp h (std_dvd h hin.i713)

theorem std_pcomp_Ly (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) :
    GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) K := by
  have hdvd := std_dvd h hin.i713
  have hKc := std_pcomp_L h hdvd
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := h.tri.comp.1
  have heq : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [h.cs_eq hy hyx, ← inf_assoc, inf_eq_left.2 hLx]
  rwa [heq] at hKc

theorem std_chev2 (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) : IsChevSimple 2 (PSimple p K) := by
  obtain ⟨y, hyD, hyx⟩ := h.exists_y
  have hp := h.prime
  have hxy : x ≠ 1 := h.tri.ne_one
  have hKL := std_pcomp_Ly h hin hyD hyx
  have hyp : y ^ p = 1 := h.elem.2 y hyD
  have hyB : y ∈ B := h.DB hyD
  exact hin.chev2 hp h.odd _ L y (kGroup_centralizer h.ctx.toS6 hxy) h.tri.comp hyp (h.tri.norm hyB)
    (h.tri.chev2 h.ctx) K hKL

theorem std_inner (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) : InnDiagOn p B K :=
  hin.i171one p B x L D K h.prime h.odd h.tri.star h.pow_four_le (h.tri.qs h.ctx) (h.tri.chev2 h.ctx)
    (kGroup_centralizer h.ctx.toS6 h.tri.ne_one) h.tri.idiag h.pre

theorem centMod_inf_eq (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) :
    B ⊓ centModSubgroup p K = D := by
  apply le_antisymm
  · rintro g ⟨hgB, hg⟩
    have hO : (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) = ⊥ :=
      S9.commutator_eq_bot_of_isQuasisimple h.prime (std_pcomp' h hin) h.K_qs
    refine faithful_quot h hgB (le_trans (centMod_iff.2 hg).2 ?_)
    rw [Subgroup.commutator_comm] at hO
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hO
  · intro g hg
    have hg' := hg
    rw [h.D_eq] at hg'
    exact ⟨h.DB hg, centMod_iff.1 (centMod_of_mem_centralizer hg'.2)⟩

theorem ky_le_cy (h : Cfg12 G m p B x L D K) {y : G} (hy : y ∈ D) :
    Ky p K y ≤ Subgroup.centralizer ({y} : Set G) :=
  closureIn_le_of_le_normalizer (h.K_le_cs.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hy)))
    ((sSup_le fun _ hJ => hJ.1).trans Subgroup.le_normalizer)

theorem ky_norm (h : Cfg12 G m p B x L D K) {y : G} (hy : y ∈ D) :
    B ≤ Subgroup.normalizer (Ky p K y : Set G) := fun b hb =>
  mem_normalizer_closureIn (B_norm_K h hb)
    (mem_normalizer_glaPLayer (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2
      (isElemAbelian_commute h.tri.bmax.1 hb (h.DB hy)))))

theorem ky_family (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) :
    ∃ 𝒞 : Set (Subgroup G), (∀ M ∈ 𝒞, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) ∧
      (⨆ M ∈ 𝒞, M) = Ky p K y ∧ (∀ M ∈ 𝒞, GLBConj x M ∈ 𝒞) ∧
      ∀ M ∈ 𝒞, ∀ M' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e M = M' := by
  have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ Subgroup.one_mem _)
  have hKy : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G)) := kGroup_centralizer h.ctx.toS6 hy1
  have hxy : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute h.elem h.xD hy
  have hE : Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set G) := Subgroup.zpowers_le.2 hxy
  have hEel : IsElemAbelian p (Subgroup.zpowers x) := isElemAbelian_mono h.elem (Subgroup.zpowers_le.2 h.xD)
  have hJ : GLAPComponent p (Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) K := by
    have hc := std_pcomp' h hin
    rw [h.cs_eq hy hyx, inf_comm] at hc
    rwa [S3.centralizer_zpowers x]
  obtain ⟨𝒞, h1, h2, h3, h4⟩ := hin.i183 G _ hKy p h.prime (Subgroup.zpowers x) hE hEel K hJ
  refine ⟨𝒞, h1, ?_, fun M hM => h3 M hM x (Subgroup.mem_zpowers x), h4⟩
  rw [h2, Ky, closureIn_eq_iSup_gLBConj]

theorem ky_pcomp_cent (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) :
    GLAPComponent p (Ky p K y ⊓ Subgroup.centralizer ({x} : Set G)) K := by
  have hc := std_pcomp' h hin
  have hKle : K ≤ Ky p K y ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf (le_closureIn_self K _) (h.K_le_L.trans h.tri.comp.1)
  refine glaPComponent_of_le h.prime hc hKle ?_
  rw [h.cs_eq hy hyx]
  exact fun g hg => ⟨hg.2, ky_le_cy h hy hg.1⟩

end S12

end CFSG.LocalAnalysis.GLTheoremA
