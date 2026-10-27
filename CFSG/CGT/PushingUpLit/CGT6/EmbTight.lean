module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbThompson
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFive
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Std
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Main

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherKnownGroup (AschbacherKnownGroupFacts)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

section Quasisimple

theorem isQuasisimple_sl2_gf {k : ℕ} (hk : 2 ≤ k) : CFSG.Open.IsQuasisimple (SLq k) := by
  have hS : IsSimpleGroup (SLq k) := isSimpleGroup_sl2_gf hk
  have hc : Subgroup.center (SLq k) = ⊥ := center_sl2_eq_bot (Fq k)
  refine ⟨(isPerfect_sl2 hk).commutator_eq_top, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

variable {V : Type} [CommGroup V] [Finite V]

theorem isQuasisimple_of_inClassX (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : InClassX ↥(yuHol Y)) : CFSG.Open.IsQuasisimple ↥Y := by
  have hP : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hker : (QuotientGroup.mk' (pCore 2 ↥Y)).ker ≤ Subgroup.center ↥Y := by
    rw [QuotientGroup.ker_mk']
    exact pCore_le_center_of_inClassX hV hperf hX.1
  have hq : CFSG.IsQuasisimple (↥Y ⧸ pCore 2 ↥Y) := by
    rcases hX.1.quotient_type with hq | hp
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (yuTop Y hV) hq
    · exfalso
      have hp' : (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime := by
        rwa [← Nat.card_congr (yuTop Y hV).toEquiv]
      have : Fact (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime := ⟨hp'⟩
      have hcyc := isCyclic_of_prime_card (α := ↥Y ⧸ pCore 2 ↥Y) rfl
      have : Group.IsPerfect (↥Y ⧸ pCore 2 ↥Y) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pCore 2 ↥Y))
          (QuotientGroup.mk'_surjective _)
      have : Nontrivial (↥Y ⧸ pCore 2 ↥Y) := Finite.one_lt_card_iff_nontrivial.mp hp'.one_lt
      exact Group.IsPerfect.not_isSolvable (↥Y ⧸ pCore 2 ↥Y)
        (Group.isSolvable_of_comm fun a b => mul_comm' a b)
  have h := (CFSG.LocalCores.isQuasisimple_iff_of_surjective hP (QuotientGroup.mk' (pCore 2 ↥Y))
    (QuotientGroup.mk'_surjective _) hker).mpr hq
  exact ⟨h.1.commutator_eq_top, h.2.1⟩

theorem isQuasisimple_of_classX4 (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y)
    (hY : InClassX ↥(yuHol Y) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) :
    CFSG.Open.IsQuasisimple ↥Y := by
  rcases hY with hX | ⟨n, hn, hΩ⟩
  · exact isQuasisimple_of_inClassX hV hperf hX
  · obtain ⟨-, θ, -⟩ := hΩ
    exact Components.quasisimple_of_equiv θ (isQuasisimple_sl2_gf (by omega))

theorem qs_subgroupOf (hV : ∀ v : V, v ^ 2 = 1) {G Y : Subgroup (MulAut V)} (hYG : Y ≤ G)
    (hperf : ⁅Y, Y⁆ = Y)
    (hY : InClassX ↥(yuHol Y) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) :
    Nine7.QS (Y.subgroupOf G) :=
  Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hYG)
    (isQuasisimple_of_classX4 hV hperf hY)

end Quasisimple

section Transfer

variable {V : Type} [CommGroup V]

theorem star_subgroupOf {G Y : Subgroup (MulAut V)} (hYG : Y ≤ G)
    (hcent : ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
      (Y.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal) :
    Nine7.Star (Y.subgroupOf G) := by
  intro a ha hAa
  have ha2 : (a : MulAut V) ^ 2 = 1 := by
    have : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    exact congrArg Subtype.val this
  have ha1 : (a : MulAut V) ≠ 1 := by
    intro h
    have h1 : a = 1 := Subtype.ext h
    rw [h1, orderOf_one] at ha
    omega
  have hmem : (a : MulAut V) ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) := by
    refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 : (⟨y, hYG hy⟩ : ↥G) ∈ Subgroup.centralizer ({a} : Set ↥G) :=
      hAa (Subgroup.mem_subgroupOf.mpr hy)
    have h2 := congrArg Subtype.val (Nine7.mem_centralizer_single.mp h1)
    exact h2.symm
  have hsub := hcent (a : MulAut V) hmem ha1 ha2
  have hC : (G ⊓ Subgroup.centralizer ({(a : MulAut V)} : Set (MulAut V))).subgroupOf G =
      Subgroup.centralizer ({a} : Set ↥G) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Nine7.mem_centralizer_single]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
  have h := (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff (B := Y)
    (L := G ⊓ Subgroup.centralizer ({(a : MulAut V)} : Set (MulAut V))) (K := G)
    inf_le_left).mpr hsub
  rw [hC] at h
  exact h

theorem even_card_centralizer_subgroupOf [Finite V] {G T Y : Subgroup (MulAut V)} (hTG : T ≤ G)
    (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 ↥T) (hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V))) :
    Even (Nat.card ↥(Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥T := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 h2
  let a : ↥G := ⟨(t : MulAut V), hTG t.2⟩
  have haC : a ∈ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hy' : (y : MulAut V) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    exact Subgroup.mem_centralizer_iff.mp (hTY t.2) _ hy'
  have hord : orderOf (⟨a, haC⟩ : ↥(Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) :
      Set ↥G))) = 2 := by
    rw [← ht, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)

theorem lift4_self [Finite V] {G Y : Subgroup (MulAut V)} (hYG : Y ≤ G)
    (hsub : (Y.subgroupOf G).IsSubnormal) (hcls : ClassX4 Y) : Lift4 G Y Y := by
  unfold Lift4
  refine ⟨le_rfl, hYG, hsub, ?_⟩
  rcases hcls with hX | ⟨n, hn, hΩ⟩ | ⟨n, hn, hΩ⟩
  · exact Or.inl ⟨hX, Or.inl rfl⟩
  · exact Or.inr ⟨n, hn, Or.inr hΩ, Or.inl rfl⟩
  · exact Or.inr ⟨n, hn, Or.inl hΩ, Or.inl rfl⟩

end Transfer

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem twin_of_outcome_two (hM4 : SchurMultL2Two) (hV : ∀ v : V, v ^ 2 = 1)
    {G Y : Subgroup (MulAut V)} (hYG : Y ≤ G) (hperf : ⁅Y, Y⁆ = Y)
    (hY : InClassX ↥(yuHol Y) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥)
    {x z : ↥G} (hcomm : ⁅Y.subgroupOf G, CFSG.conjugate (Y.subgroupOf G) x⁆ = ⊥)
    (hz2 : orderOf z = 2) (hzA : z ∈ Y.subgroupOf G)
    (hzC : z ∈ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G)) : Twin G Y := by
  have hQS : Nine7.QS (Y.subgroupOf G) := qs_subgroupOf hV hYG hperf hY
  let y : ↥Y := ⟨(z : MulAut V), Subgroup.mem_subgroupOf.mp hzA⟩
  have hyc : y ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hw : (⟨(w : MulAut V), hYG w.2⟩ : ↥G) ∈ Y.subgroupOf G :=
      Subgroup.mem_subgroupOf.mpr w.2
    have h := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hzC _ hw)
    exact h
  have hy1 : y ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    have h1 : z = 1 := Subtype.ext h'
    rw [h1, orderOf_one] at hz2
    omega
  have hcenter : Subgroup.center ↥Y ≠ ⊥ := fun h => hy1 (by
    have := hyc
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hsl5 : YSL5 Y := by
    rcases hY with hX | ⟨n, hn, hΩ⟩
    · rcases emb_four_five_core Y hM4 hV hperf hX with h | ⟨h5, -⟩
      · exact absurd h hcenter
      · exact h5
    · exfalso
      obtain ⟨-, θ, -⟩ := hΩ
      refine hcenter ?_
      rw [Subgroup.eq_bot_iff_forall]
      intro w hw
      have hθ : θ w ∈ Subgroup.center (SLq (2 * n)) := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨u, rfl⟩ := θ.surjective s
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw u]
      rw [center_sl2_eq_bot (Fq (2 * n)), Subgroup.mem_bot] at hθ
      exact θ.injective (hθ.trans (map_one θ).symm)
  have hAY : (Y.subgroupOf G).map G.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYG
  have hconj : (CFSG.conjugate (Y.subgroupOf G) x).map G.subtype =
      Y.map (MulAut.conj ((x⁻¹ : ↥G) : MulAut V)).toMonoidHom := by
    have h1 : (CFSG.conjugate (Y.subgroupOf G) x).map G.subtype =
        (Y.subgroupOf G).map (G.subtype.comp (MulAut.conj x⁻¹).toMonoidHom) := by
      rw [CFSG.conjugate, Subgroup.map_map]
    have h2 : Y.map (MulAut.conj ((x⁻¹ : ↥G) : MulAut V)).toMonoidHom =
        (Y.subgroupOf G).map ((MulAut.conj ((x⁻¹ : ↥G) : MulAut V)).toMonoidHom.comp
          G.subtype) := by
      rw [← Subgroup.map_map, hAY]
    rw [h1, h2]
    congr 1
  refine ⟨hsl5, ((x⁻¹ : ↥G) : MulAut V), (x⁻¹ : ↥G).2, ?_, ?_⟩
  · intro h
    rw [← hconj] at h
    have h' : (CFSG.conjugate (Y.subgroupOf G) x).map G.subtype =
        (Y.subgroupOf G).map G.subtype := h.trans hAY.symm
    have h'' := Subgroup.map_injective G.subtype_injective h'
    rw [h''] at hcomm
    exact Nine7.qs_commutator_ne_bot hQS hcomm
  · have h := Subgroup.map_commutator (Y.subgroupOf G) (CFSG.conjugate (Y.subgroupOf G) x)
      G.subtype
    rw [hcomm, Subgroup.map_bot, hAY, hconj] at h
    exact h.symm

theorem out49_of_cfg (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    (hS : SchreierFor Assembly.InCatalog) (hM4 : SchurMultL2Two) (hV : ∀ v : V, v ^ 2 = 1)
    {G T Y : Subgroup (MulAut V)} (cfg : Emb4Cfg G T Y) (hnp : ¬ OmegaPlusType Y) :
    Out49 G Y := by
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hcls2 : InClassX ↥(yuHol Y) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥ := by
    rcases cfg.adm.hcls with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnp
  refine ⟨hcls2, ?_⟩
  have hQS := qs_subgroupOf hV hYG cfg.adm.hperf hcls2
  have hStar := star_subgroupOf hYG cfg.cent
  have hKP : Assembly.KProper Assembly.InCatalog ↥G := kProper_of_isKGroup' cfg.kgroup
  rcases Nine7.nine_seven_star_of_kproper h5 hK hS hKP hQS hStar with
    ⟨-, hD, hnc⟩ | ⟨x, hcomm, -, -, -, -, ⟨z, hz2, hzA, -, hzC, -⟩⟩ | hsub
  · exact Or.inl (Nine7.isStandard_of_outcome_one hQS hStar
      (even_card_centralizer_subgroupOf cfg.adm.hTG cfg.adm.hT1 cfg.adm.hT2
        cfg.adm.le_centralizer) hD hnc)
  · exact Or.inr (twin_of_outcome_two hM4 hV hYG cfg.adm.hperf hcls2 hcomm hz2 hzA hzC)
  · exact absurd ⟨Y, lift4_self hYG hsub cfg.adm.hcls⟩ cfg.nolift

theorem step49_of_inputs (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    (hS : SchreierFor Assembly.InCatalog) (hM4 : SchurMultL2Two) : Step49 :=
  fun _ _ _ hV _ _ _ cfg hnp => out49_of_cfg h5 hK hS hM4 hV cfg hnp

end Main

end CFSG.CGT.PushingUpLit.CGT6
