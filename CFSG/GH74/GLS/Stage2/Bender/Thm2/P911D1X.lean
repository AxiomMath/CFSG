module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Hyp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915D1
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {X V N : Subgroup G}

theorem exists_I_d1_X (hC : Ctx9 G z k S M p) (hzN : z ∈ N) (hXN : X ≤ N)
    (hXA : X ≤ L915.A1 z M N p) (hXE : ¬ X ≤ centralizer (Em N : Set G))
    (hd1 : C43d1 k (zSec z N hzN (pCore p ↥N)) (xBar p N (L915.A1 z M N p))) :
    ∃ I : Subgroup ↥N, IsQuasisimple ↥I ∧
      I ≤ centralizer ({(⟨z, hzN⟩ : ↥N)} : Set ↥N) ∧
      (L915.A1 z M N p).subgroupOf N ≤ centralizer (I : Set ↥N) ∧
      (∀ c ∈ centralizer ({(⟨z, hzN⟩ : ↥N)} : Set ↥N), c ∈ normalizer (I : Set ↥N)) ∧
      (∀ c ∈ centralizer ((X.subgroupOf N : Subgroup ↥N) : Set ↥N),
        c ∈ normalizer (I : Set ↥N)) := by
  have hp := hC.prime
  obtain ⟨J, hJ, hXJ⟩ := L915.exists_component_noncentral_of_Em hXN hXE
  have hOJ : pCore p ↥N ≤ centralizer (J : Set ↥N) :=
    L915.pCore_le_centralizer_component hp hJ
  have hJ' : IsComponent (J.map (QuotientGroup.mk' (pCore p ↥N))) :=
    L915.isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hA₁ : X.subgroupOf N ≤ (L915.A1 z M N p).subgroupOf N := fun x hx => hXA hx
  have hnc : ¬ xBar p N (L915.A1 z M N p) ≤
      centralizer ((J.map (QuotientGroup.mk' (pCore p ↥N)) : Subgroup _) : Set _) :=
    L915.not_le_centralizer_map hp hJ hA₁ hXJ
  set Xb := xBar p N (L915.A1 z M N p) with hXb
  set zb := zSec z N hzN (pCore p ↥N) with hzb
  have : (ncl Xb).Normal := Subgroup.normalClosure_normal
  have hJK : J.map (QuotientGroup.mk' (pCore p ↥N)) ≤ ncl Xb :=
    L915.component_le_of_noncentral inferInstance hJ' Subgroup.subset_normalClosure hnc
  have hK3 : IsPGL3Four ↥(ncl Xb) := hd1.2.2.1
  have hJeq : J.map (QuotientGroup.mk' (pCore p ↥N)) = ⁅ncl Xb, ncl Xb⁆ :=
    L915.pgl3four_component_eq hK3 hJ' hJK
  have hJn' : (J.map (QuotientGroup.mk' (pCore p ↥N))).Normal := by
    rw [hJeq]
    infer_instance
  have hJn : ∀ y : ↥N, y ∈ normalizer (J : Set ↥N) := by
    intro y
    refine L915.mem_normalizer_of_image hp hJ ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr hJn']
    exact Subgroup.mem_top _
  have hĪq : IsQuasisimple ↥(ncl Xb ⊓ centralizer ({zb} : Set (↥N ⧸ pCore p ↥N))) :=
    L52Two.I1.isQuasisimple_of_isL2 (q := 4) (by norm_num) hd1.2.2.2.2.1
  have hĪJ : ncl Xb ⊓ centralizer ({zb} : Set (↥N ⧸ pCore p ↥N)) ≤
      J.map (QuotientGroup.mk' (pCore p ↥N)) := by
    rw [hd1.2.2.2.1, hJeq]
    exact inf_le_left
  obtain ⟨I, hIq, hIJ, hIπ, hIn, hIc⟩ :=
    L915.exists_lift_quasisimple (O := pCore p ↥N) hOJ hJn hĪq hĪJ
  have hπz : QuotientGroup.mk' (pCore p ↥N) (⟨z, hzN⟩ : ↥N) = zb := rfl
  have hIbX : ∀ x ∈ ncl Xb ⊓ centralizer ({zb} : Set (↥N ⧸ pCore p ↥N)), ∀ y ∈ Xb,
      y * x = x * y := by
    intro x hx y hy
    have hx' : x ∈ ⁅ncl Xb, ncl Xb⁆ ⊓ centralizer (Xb : Set (↥N ⧸ pCore p ↥N)) :=
      hd1.2.2.2.1 ▸ hx
    exact Subgroup.mem_centralizer_iff.mp hx'.2 y hy
  have hA₁X : ∀ a ∈ (L915.A1 z M N p).subgroupOf N,
      QuotientGroup.mk' (pCore p ↥N) a ∈ Xb :=
    fun a ha => ⟨a, ha, rfl⟩
  have hXX : (X.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) = Xb := by
    have hle : (X.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) ≤ Xb :=
      Subgroup.map_mono hA₁
    have hcard : Nat.card ↥Xb = 3 := hd1.2.1
    have hne : (X.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) ≠ ⊥ := by
      intro hbot
      apply hXJ
      intro a ha
      have h1 : QuotientGroup.mk' (pCore p ↥N) a ∈
          (X.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) := ⟨a, ha, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact hOJ ((QuotientGroup.eq_one_iff _).mp h1)
    have hdvd : Nat.card ↥((X.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N))) ∣ 3 :=
      hcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h3])
  refine ⟨I, hIq, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : (⟨z, hzN⟩ : ↥N) ∈ centralizer (I : Set ↥N) := by
      apply hIc
      rw [hπz, Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
    intro i hi
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h1 i hi
  ·
    intro a ha
    apply hIc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hIbX x hx _ (hA₁X a ha)).symm
  ·
    intro c hc
    apply hIn
    have hcz : zb * QuotientGroup.mk' (pCore p ↥N) c =
        QuotientGroup.mk' (pCore p ↥N) c * zb := by
      have h1 := congrArg (QuotientGroup.mk' (pCore p ↥N))
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
      rw [map_mul, map_mul] at h1
      exact h1.symm
    refine Thm1.mem_normalizer_inf ?_ ?_
    · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (ncl Xb).Normal)]
      exact Subgroup.mem_top _
    · refine L915.mem_normalizer_centralizer_of_comm (S := {zb}) fun s hs => ?_
      rw [Set.mem_singleton_iff.mp hs]
      exact hcz
  ·
    intro c hc
    apply hIn
    rw [hd1.2.2.2.1]
    have hXc : ∀ x ∈ Xb, x * QuotientGroup.mk' (pCore p ↥N) c =
        QuotientGroup.mk' (pCore p ↥N) c * x := by
      intro x hx
      rw [← hXX] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have h1 := Subgroup.mem_centralizer_iff.mp hc a ha
      rw [← map_mul, ← map_mul, h1]
    refine Thm1.mem_normalizer_inf ?_ ?_
    · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⁅ncl Xb, ncl Xb⁆).Normal)]
      exact Subgroup.mem_top _
    · exact L915.mem_normalizer_centralizer_of_comm
        (S := (Xb : Set (↥N ⧸ pCore p ↥N))) hXc

theorem false_of_d1_X (h512 : IG_5_12) (H : Hyp911 z k S M p X V N) (hzN : z ∈ N)
    (hXA : X ≤ L915.A1 z M N p) (hXE : ¬ X ≤ centralizer (Em N : Set G))
    (hd1 : C43d1 k (zSec z N hzN (pCore p ↥N)) (xBar p N (L915.A1 z M N p))) : False := by
  have hC : Ctx9 G z k S M p := H.ctx
  have hp := hC.prime
  have hXN : X ≤ N := Subgroup.le_normalizer.trans H.hXN
  obtain ⟨I, hIq, hIz, hIA, hIN1, hIN2⟩ := exists_I_d1_X hC hzN hXN hXA hXE hd1
  have hVN : V ≤ N := (H.hV.trans inf_le_left).trans inf_le_right
  have hVP : V ≤ Op p M := (H.hV.trans inf_le_left).trans inf_le_left
  have : Fact p.Prime := ⟨hp⟩
  have hUp : IsPGroup p ↥((Op p M ⊓ N ⊓ Cen z).subgroupOf N) := by
    have hUP : Op p M ⊓ N ⊓ Cen z ≤ Op p M := inf_le_left.trans inf_le_left
    have hUN : Op p M ⊓ N ⊓ Cen z ≤ N := inf_le_left.trans inf_le_right
    have hUp' : IsPGroup p ↥(Op p M ⊓ N ⊓ Cen z) := hC.P_pgroup.to_le hUP
    exact hUp'.of_injective (Subgroup.subgroupOfEquivOfLe hUN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUN).injective
  have hUC : (Op p M ⊓ N ⊓ Cen z).subgroupOf N ≤ centralizer (I : Set ↥N) := by
    refine L915.commute_of_normal_pgroup_of_normal_quasisimple hp
      (H := centralizer ({(⟨z, hzN⟩ : ↥N)} : Set ↥N)) hIq hIz hIN1 ?_ ?_ hUp
    · intro u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hu' : (u : G) ∈ Cen z := (Subgroup.mem_subgroupOf.mp hu).2
      have := Subgroup.mem_centralizer_singleton_iff.mp hu'
      exact Subtype.ext this
    · intro c hc
      have hcz : (c : G) * z = z * (c : G) := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hc
        exact congrArg Subtype.val this
      have hcC : (c : G) ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hcz
      have hcM : (c : G) ∈ M := hC.cen_le hcC
      have h1 : (c : G) ∈ normalizer ((Op p M ⊓ N ⊓ Cen z : Subgroup G) : Set G) :=
        Thm1.mem_normalizer_inf (Thm1.mem_normalizer_inf (le_normalizer_Op' p M hcM)
          (Subgroup.le_normalizer c.2))
          (L915.mem_normalizer_centralizer_of_comm (S := {z}) fun s hs => by
            rw [Set.mem_singleton_iff.mp hs]; exact hcz.symm)
      rw [mem_normalizer_iff]
      intro x
      have h2 := (mem_normalizer_iff.mp h1) (x : G)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using h2
  have hp1 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
  have hV1 : V ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥V = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [H.hV2] at h1
    omega
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvN : v ∈ N := hVN hvV
  have hvP : v ∈ Op p M := hVP hvV
  have hvv := H.hv v hvV hv1'
  have hY : NN z p ⊤ (zpowers v) := ⟨le_top, hvv.2.1, hvv.2.2.1, hvv.2.2.2⟩
  have hW : IsPGroup p ↥(X ⊔ zpowers v) :=
    hC.P_pgroup.to_le (sup_le H.hXP (Subgroup.zpowers_le.mpr hvP))
  have hYN : X ⊔ zpowers v ≤ N := sup_le hXN (Subgroup.zpowers_le.mpr hvN)
  obtain ⟨-, hE⟩ := lemma_9_3 h512 G z k S M p hC N X (zpowers v) H.hN H.hXN
    (Subgroup.zpowers_le.mpr hvN) hY hW
  have hCI : X ⊔ zpowers v ≤ (centralizer (I : Set ↥N)).map N.subtype := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨⟨x, hXN hx⟩, hIA (Subgroup.mem_subgroupOf.mpr (hXA hx)), rfl⟩
    · intro u hu
      have huV : u ∈ V := Subgroup.zpowers_le.mpr hvV hu
      have huU : (⟨u, hVN huV⟩ : ↥N) ∈ (Op p M ⊓ N ⊓ Cen z).subgroupOf N :=
        Subgroup.mem_subgroupOf.mpr (H.hV huV)
      exact ⟨⟨u, hVN huV⟩, hUC huU, rfl⟩
  set Y' : Subgroup ↥N := (X ⊔ zpowers v).subgroupOf N with hY'
  have hYmap : Y'.map N.subtype = X ⊔ zpowers v := Subgroup.map_subgroupOf_eq_of_le hYN
  have hYI : Y' ≤ centralizer (I : Set ↥N) := by
    intro y hy
    obtain ⟨y₀, hy₀, hy₀eq⟩ := hCI (Subgroup.mem_subgroupOf.mp hy)
    have : y₀ = y := Subtype.ext hy₀eq
    rwa [← this]
  have hIC : I ≤ centralizer (Y' : Set ↥N) := Subgroup.le_centralizer_iff.mp hYI
  have hE' : Em (N ⊓ centralizer ((Y'.map N.subtype : Subgroup G) : Set G)) = ⊥ := by
    rw [hYmap]
    exact hE
  have hXY : ((X.subgroupOf N : Subgroup ↥N) : Set ↥N) ⊆ (Y' : Set ↥N) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
  exact L915.no_quasisimple_normal_of_Em_bot Y' hE' I hIq hIC fun c hc =>
    hIN2 c (Subgroup.centralizer_le hXY hc)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
