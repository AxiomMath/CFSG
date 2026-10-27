module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Trans
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Lift
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Pgl3
public import CFSG.Walter.Bender1970.S3.Involution
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915A1
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section D1

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {N A B : Subgroup G}

theorem mem_normalizer_centralizer_of_comm {Q : Type} [Group Q] {S : Set Q} {g : Q}
    (hg : ∀ s ∈ S, s * g = g * s) : g ∈ normalizer ((centralizer S : Subgroup Q) : Set Q) := by
  have key : ∀ g : Q, (∀ s ∈ S, s * g = g * s) → ∀ x ∈ centralizer S,
      g * x * g⁻¹ ∈ centralizer S := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro s hs
    have h1 := hg s hs
    have h2 := hx s hs
    have h3 : s * g⁻¹ = g⁻¹ * s := by
      calc s * g⁻¹ = g⁻¹ * (g * s) * g⁻¹ := by group
        _ = g⁻¹ * (s * g) * g⁻¹ := by rw [h1]
        _ = g⁻¹ * s := by group
    calc s * (g * x * g⁻¹) = (s * g) * x * g⁻¹ := by group
      _ = (g * s) * x * g⁻¹ := by rw [h1]
      _ = g * (s * x) * g⁻¹ := by group
      _ = g * (x * s) * g⁻¹ := by rw [h2]
      _ = g * x * (s * g⁻¹) := by group
      _ = g * x * g⁻¹ * s := by rw [h3]; group
  have hg' : ∀ s ∈ S, s * g⁻¹ = g⁻¹ * s := by
    intro s hs
    have h1 := hg s hs
    calc s * g⁻¹ = g⁻¹ * (g * s) * g⁻¹ := by group
      _ = g⁻¹ * (s * g) * g⁻¹ := by rw [h1]
      _ = g⁻¹ * s := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have h2 := key g⁻¹ hg' _ hx
  have h3 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [h3] at h2

theorem exists_I_d1 (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B)
    (hAE : ¬ A ≤ centralizer (Em N : Set G))
    (hd1 : C43d1 k (zSec z N (z_mem_N h) (pCore p ↥N)) (xBar p N (A1 z M N p))) :
    ∃ I : Subgroup ↥N, IsQuasisimple ↥I ∧
      I ≤ centralizer ({(⟨z, z_mem_N h⟩ : ↥N)} : Set ↥N) ∧
      (A1 z M N p).subgroupOf N ≤ centralizer (I : Set ↥N) ∧
      (∀ c ∈ centralizer ({(⟨z, z_mem_N h⟩ : ↥N)} : Set ↥N), c ∈ normalizer (I : Set ↥N)) ∧
      (∀ c ∈ centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N), c ∈ normalizer (I : Set ↥N)) := by
  have hp := hC.prime
  have hzN : z ∈ N := z_mem_N h
  obtain ⟨J, hJ, hAJ⟩ := exists_component_noncentral_of_Em h.A_N hAE
  have hOJ : pCore p ↥N ≤ centralizer (J : Set ↥N) := pCore_le_centralizer_component hp hJ
  have hJ' : IsComponent (J.map (QuotientGroup.mk' (pCore p ↥N))) :=
    isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hA₁ : A.subgroupOf N ≤ (A1 z M N p).subgroupOf N := fun x hx => A_le_A1 h hx
  have hnc : ¬ xBar p N (A1 z M N p) ≤
      centralizer ((J.map (QuotientGroup.mk' (pCore p ↥N)) : Subgroup _) : Set _) :=
    not_le_centralizer_map hp hJ hA₁ hAJ
  set Xb := xBar p N (A1 z M N p) with hXb
  set zb := zSec z N hzN (pCore p ↥N) with hzb
  have : (ncl Xb).Normal := Subgroup.normalClosure_normal
  have hJK : J.map (QuotientGroup.mk' (pCore p ↥N)) ≤ ncl Xb :=
    component_le_of_noncentral inferInstance hJ' Subgroup.subset_normalClosure hnc
  have hK3 : IsPGL3Four ↥(ncl Xb) := hd1.2.2.1
  have hJeq : J.map (QuotientGroup.mk' (pCore p ↥N)) = ⁅ncl Xb, ncl Xb⁆ :=
    pgl3four_component_eq hK3 hJ' hJK
  have hJn' : (J.map (QuotientGroup.mk' (pCore p ↥N))).Normal := by
    rw [hJeq]
    infer_instance
  have hJn : ∀ y : ↥N, y ∈ normalizer (J : Set ↥N) := by
    intro y
    refine mem_normalizer_of_image hp hJ ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr hJn']
    exact Subgroup.mem_top _
  have hĪq : IsQuasisimple ↥(ncl Xb ⊓ centralizer ({zb} : Set (↥N ⧸ pCore p ↥N))) :=
    L52Two.I1.isQuasisimple_of_isL2 (q := 4) (by norm_num) hd1.2.2.2.2.1
  have hĪJ : ncl Xb ⊓ centralizer ({zb} : Set (↥N ⧸ pCore p ↥N)) ≤
      J.map (QuotientGroup.mk' (pCore p ↥N)) := by
    rw [hd1.2.2.2.1, hJeq]
    exact inf_le_left
  obtain ⟨I, hIq, hIJ, hIπ, hIn, hIc⟩ :=
    exists_lift_quasisimple (O := pCore p ↥N) hOJ hJn hĪq hĪJ
  have hπz : QuotientGroup.mk' (pCore p ↥N) (⟨z, hzN⟩ : ↥N) = zb := rfl
  have hIbX : ∀ x ∈ ncl Xb ⊓ centralizer ({zb} : Set (↥N ⧸ pCore p ↥N)), ∀ y ∈ Xb, y * x = x * y := by
    intro x hx y hy
    have hx' : x ∈ ⁅ncl Xb, ncl Xb⁆ ⊓ centralizer (Xb : Set (↥N ⧸ pCore p ↥N)) :=
      hd1.2.2.2.1 ▸ hx
    exact Subgroup.mem_centralizer_iff.mp hx'.2 y hy
  have hA₁X : ∀ a ∈ (A1 z M N p).subgroupOf N, QuotientGroup.mk' (pCore p ↥N) a ∈ Xb :=
    fun a ha => ⟨a, ha, rfl⟩
  have hAX : (A.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) = Xb := by
    have hle : (A.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) ≤ Xb :=
      Subgroup.map_mono hA₁
    have hcard : Nat.card ↥Xb = 3 := hd1.2.1
    have hne : (A.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) ≠ ⊥ := by
      intro hbot
      apply hAJ
      intro a ha
      have h1 : QuotientGroup.mk' (pCore p ↥N) a ∈
          (A.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N)) := ⟨a, ha, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact hOJ ((QuotientGroup.eq_one_iff _).mp h1)
    have hdvd : Nat.card ↥((A.subgroupOf N).map (QuotientGroup.mk' (pCore p ↥N))) ∣ 3 :=
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
    have hcz : zb * QuotientGroup.mk' (pCore p ↥N) c = QuotientGroup.mk' (pCore p ↥N) c * zb := by
      have h1 := congrArg (QuotientGroup.mk' (pCore p ↥N))
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
      rw [map_mul, map_mul] at h1
      exact h1.symm
    refine Thm1.mem_normalizer_inf ?_ ?_
    · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (ncl Xb).Normal)]
      exact Subgroup.mem_top _
    · refine mem_normalizer_centralizer_of_comm (S := {zb}) fun s hs => ?_
      rw [Set.mem_singleton_iff.mp hs]
      exact hcz
  ·
    intro c hc
    apply hIn
    rw [hd1.2.2.2.1]
    have hXc : ∀ x ∈ Xb, x * QuotientGroup.mk' (pCore p ↥N) c =
        QuotientGroup.mk' (pCore p ↥N) c * x := by
      intro x hx
      rw [← hAX] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have h1 := Subgroup.mem_centralizer_iff.mp hc a ha
      rw [← map_mul, ← map_mul, h1]
    refine Thm1.mem_normalizer_inf ?_ ?_
    · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⁅ncl Xb, ncl Xb⁆).Normal)]
      exact Subgroup.mem_top _
    · exact mem_normalizer_centralizer_of_comm (S := (Xb : Set (↥N ⧸ pCore p ↥N))) hXc

omit [Finite G] in
theorem no_quasisimple_normal_of_Em_bot {N : Subgroup G} (Y' : Subgroup ↥N)
    (hE : Em (N ⊓ centralizer ((Y'.map N.subtype : Subgroup G) : Set G)) = ⊥) (K : Subgroup ↥N)
    (hKq : IsQuasisimple ↥K) (hKC : K ≤ centralizer (Y' : Set ↥N))
    (hKn : ∀ c ∈ centralizer (Y' : Set ↥N), c ∈ normalizer (K : Set ↥N)) : False := by
  set Y : Subgroup G := Y'.map N.subtype with hYdef
  have hDeq : (centralizer (Y' : Set ↥N)).map N.subtype = N ⊓ centralizer (Y : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro y ⟨b, hb, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp ha b hb
      exact congrArg Subtype.val this
    · rintro ⟨hxN, hxC⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro b hb
      have := Subgroup.mem_centralizer_iff.mp hxC (b : G) ⟨b, hb, rfl⟩
      exact Subtype.ext this
  have hnorm : (K.subgroupOf (centralizer (Y' : Set ↥N))).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (mem_normalizer_iff.mp (hKn c c.2) (x : ↥N)).mp hx
    simpa using this
  have hcomp : IsComponent (K.subgroupOf (centralizer (Y' : Set ↥N))) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hKq,
      hnorm.isSubnormal⟩
  let e : ↥(centralizer (Y' : Set ↥N)) ≃* ↥(N ⊓ centralizer (Y : Set G)) :=
    (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr hDeq)
  have hc2 := CFSG.LocalCores.isComponent_map_mulEquiv e hcomp
  have hlayer : layer ↥(N ⊓ centralizer (Y : Set G)) = ⊥ := by
    have := hE
    rw [Em_def', Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  have hle := CFSG.LocalCores.component_le_layer hc2
  rw [hlayer] at hle
  have hbot := le_bot_iff.mp hle
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hc2.1
  rw [hbot] at hnt
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt rfl

theorem false_of_d1 (h512 : IG_5_12) (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B)
    (hAE : ¬ A ≤ centralizer (Em N : Set G))
    (hd1 : C43d1 k (zSec z N (z_mem_N h) (pCore p ↥N)) (xBar p N (A1 z M N p))) : False := by
  obtain ⟨I, hIq, hIz, hIA, hIN1, hIN2⟩ := exists_I_d1 hC h hAE hd1
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hzN : z ∈ N := z_mem_N h
  have hBN : B ≤ N := le_trans Subgroup.le_normalizer h.B_norm
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hC.orderOf_z, pow_two] at h1
    exact h1
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p ↥B := hC.P_pgroup.to_le h.B_le
  have hBodd : Odd (Nat.card ↥B) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hBp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hUp : IsPGroup p ↥((Op p M ⊓ N ⊓ Cen z).subgroupOf N) := by
    have hUP : Op p M ⊓ N ⊓ Cen z ≤ Op p M := inf_le_left.trans inf_le_left
    have hUN : Op p M ⊓ N ⊓ Cen z ≤ N := inf_le_left.trans inf_le_right
    have hUp' : IsPGroup p ↥(Op p M ⊓ N ⊓ Cen z) := hC.P_pgroup.to_le hUP
    exact hUp'.of_injective (Subgroup.subgroupOfEquivOfLe hUN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUN).injective
  have hUC : (Op p M ⊓ N ⊓ Cen z).subgroupOf N ≤ centralizer (I : Set ↥N) := by
    refine CFSG.GH74.GLS.Stage2.Bender.Thm2.L915.commute_of_normal_pgroup_of_normal_quasisimple hp
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
          (mem_normalizer_centralizer_of_comm (S := {z}) fun s hs => by
            rw [Set.mem_singleton_iff.mp hs]; exact hcz.symm)
      rw [mem_normalizer_iff]
      intro x
      have h2 := (mem_normalizer_iff.mp h1) (x : G)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using h2
  have hBI : B.subgroupOf N ≤ centralizer (I : Set ↥N) := by
    intro b hb
    obtain ⟨c, hc, m, hm, hbcm⟩ := CFSG.Walter.exists_mem_centralizer_mul_mem_commutator hz2
      h.B_inv hBodd (Subgroup.mem_subgroupOf.mp hb)
    have hcN : c ∈ N := hBN hc.1
    have hmA : m ∈ A1 z M N p :=
      Subgroup.commutator_mono (le_inf h.B_le hBN) le_rfl hm
    have hmN : m ∈ N := (A1_le hC hzN) hmA |>.2
    have hcU : (⟨c, hcN⟩ : ↥N) ∈ (Op p M ⊓ N ⊓ Cen z).subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr ⟨⟨h.B_le hc.1, hcN⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hc.2)⟩
    have hmI : (⟨m, hmN⟩ : ↥N) ∈ centralizer (I : Set ↥N) := hIA (Subgroup.mem_subgroupOf.mpr hmA)
    have hbeq : b = ⟨c, hcN⟩ * ⟨m, hmN⟩ := Subtype.ext hbcm
    rw [hbeq]
    exact mul_mem (hUC hcU) hmI
  have hAA : A.subgroupOf N ≤ centralizer (I : Set ↥N) := fun x hx => hIA (A_le_A1 h hx)
  have hCI : B ⊔ A ≤ (centralizer (I : Set ↥N)).map N.subtype := by
    refine sup_le ?_ ?_
    · intro b hb
      exact ⟨⟨b, hBN hb⟩, hBI (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
    · intro a ha
      exact ⟨⟨a, h.A_N ha⟩, hAA (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  set Y' : Subgroup ↥N := (B ⊔ A).subgroupOf N with hY'
  have hYmap : Y'.map N.subtype = B ⊔ A := Subgroup.map_subgroupOf_eq_of_le (sup_le hBN h.A_N)
  have hYI : Y' ≤ centralizer (I : Set ↥N) := by
    intro y hy
    obtain ⟨y₀, hy₀, hy₀eq⟩ := hCI (Subgroup.mem_subgroupOf.mp hy)
    have : y₀ = y := Subtype.ext hy₀eq
    rwa [← this]
  have hIC : I ≤ centralizer (Y' : Set ↥N) := Subgroup.le_centralizer_iff.mp hYI
  have hAN : NN z p ⊤ A := ⟨le_top, h.A_ne, h.A_inv, h.A_mem.2.2.2⟩
  have hW : IsPGroup p ↥(B ⊔ A) := hC.P_pgroup.to_le (sup_le h.B_le h.A_le)
  obtain ⟨-, hE⟩ := lemma_9_3 h512 G z k S M p hC N B A h.coatom h.B_norm h.A_N hAN hW
  have hE' : Em (N ⊓ centralizer ((Y'.map N.subtype : Subgroup G) : Set G)) = ⊥ := by
    rw [hYmap]
    exact hE
  have hAY : ((A.subgroupOf N : Subgroup ↥N) : Set ↥N) ⊆ (Y' : Set ↥N) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  exact no_quasisimple_normal_of_Em_bot Y' hE' I hIq hIC fun c hc =>
    hIN2 c (Subgroup.centralizer_le hAY hc)

end D1

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
