module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SteinbergCEInnerComponentActionsLayer
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.Quasithin.Background.C2PushQuot
import CFSG.Quasithin.Background.F7TwoE2Comp
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux2

public section

namespace CFSG.LocalAnalysis

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_card_eq_prime_of_dvd_card {A L : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hA : Nat.card A = r) (hAL : A ≤ normalizer (L : Set G))
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup G) ≤ 1) (hrL : r ∣ Nat.card L) : A ≤ L := by
  have : Fact r.Prime := ⟨hr⟩
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [pow_one, hA])
  obtain ⟨Q, hQ⟩ := (hAp.comap_subtype (K := A ⊔ L)).exists_le_sylow
  set R : Subgroup G := (Q : Subgroup ↥(A ⊔ L)).map (A ⊔ L).subtype with hRdef
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf r R (A ⊔ L) := ⟨Q, rfl⟩
  have hAR : A ≤ R := fun a ha =>
    ⟨⟨a, (le_sup_left : A ≤ A ⊔ L) ha⟩, hQ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  have hRL : CFSG.ABGLocalTools.IsSylowOf r (R ⊓ L) L :=
    hRsyl.inf_of_le_normalizer le_sup_right (sup_le hAL Subgroup.le_normalizer)
  have hne : R ⊓ L ≠ ⊥ := by
    intro hbot
    have hcard := hRL.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hk : 0 < (Nat.card L).factorization r :=
      hr.factorization_pos_of_dvd Nat.card_pos.ne' hrL
    exact (one_lt_pow₀ hr.one_lt hk.ne').ne hcard
  have hRcyc : IsCyclic ↥R :=
    CFSG.isCyclic_of_le_of_pRank_le_one hr hr2 hRsyl.isPGroup le_top hrank
  exact (CFSG.Goldschmidt.G53.le_of_isCyclic_of_card_eq_prime hr hRcyc hRsyl.isPGroup hAR hA
    inf_le_left hne).trans inf_le_right

omit [Finite G] in
theorem component_conj_ne_of_not_le_normalizer {A L : Subgroup G}
    (hA : (Nat.card A).Prime) (hAL : ¬ A ≤ normalizer (L : Set G))
    {x y : A} (hxy : x ≠ y) :
    L.map (MulAut.conj (x : G)).toMonoidHom ≠
      L.map (MulAut.conj (y : G)).toMonoidHom := by
  intro heq
  have hmap : L.map (MulAut.conj ((y : G)⁻¹ * (x : G))).toMonoidHom = L := by
    have h := congrArg (fun K : Subgroup G =>
      K.map (MulAut.conj (y : G)⁻¹).toMonoidHom) heq
    rw [CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.map_conj_map_conj,
      CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.map_conj_map_conj] at h
    rw [show (y : G)⁻¹ * (y : G) = 1 by group,
      CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.map_conj_one] at h
    simpa using h
  have hmem : (y : G)⁻¹ * (x : G) ∈ normalizer (L : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hzA : (y : G)⁻¹ * (x : G) ∈ A := A.mul_mem (A.inv_mem y.2) x.2
  have hzne : (y : G)⁻¹ * (x : G) ≠ 1 := by
    intro h
    exact hxy (Subtype.ext (by
      calc (x : G) = (y : G) * ((y : G)⁻¹ * (x : G)) := by group
        _ = (y : G) * 1 := by rw [h]
        _ = (y : G) := mul_one _))
  have hzne' : (⟨(y : G)⁻¹ * (x : G), hzA⟩ : A) ≠ 1 := by
    intro h
    exact hzne (congrArg Subtype.val h)
  have : Fact (Nat.card A).Prime := ⟨hA⟩
  have htop : Subgroup.zpowers (⟨(y : G)⁻¹ * (x : G), hzA⟩ : A) = ⊤ :=
    zpowers_eq_top_of_prime_card (p := Nat.card A) rfl hzne'
  have hAleN : A ≤ normalizer (L : Set G) := by
    intro b hb
    have hb' : (⟨b, hb⟩ : A) ∈
        Subgroup.zpowers (⟨(y : G)⁻¹ * (x : G), hzA⟩ : A) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hkG : ((y : G)⁻¹ * (x : G)) ^ k = b := by
      have := congrArg Subtype.val hk
      simpa using this
    exact Subgroup.zpowers_le_of_mem hmem (Subgroup.mem_zpowers_iff.mpr ⟨k, hkG⟩)
  exact hAL hAleN

theorem not_le_centralizer_iSup_map_conj_of_isComponent
    (hrad : CFSG.solvableRadical G = ⊥) {A L P₁ : Subgroup G} (hL : CFSG.IsComponent L)
    (hP₁L : P₁ ≤ L) (hP₁ne : P₁ ≠ ⊥) {a : G} (haA : a ∈ A)
    (haN : a ∉ normalizer (L : Set G)) :
    ¬ A ≤ centralizer (((⨆ x : A, P₁.map (MulAut.conj (x : G)).toMonoidHom) : Subgroup G) :
      Set G) := by
  intro hAC
  have hP : P₁ ≤ ⨆ x : A, P₁.map (MulAut.conj (x : G)).toMonoidHom := by
    have h := le_iSup (fun x : A => P₁.map (MulAut.conj (x : G)).toMonoidHom)
      (⟨1, A.one_mem⟩ : A)
    rw [show ((⟨1, A.one_mem⟩ : A) : G) = 1 from rfl,
      CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.map_conj_one] at h
    simpa using h
  have hP₁_le_Pa : P₁ ≤ P₁.map (MulAut.conj a).toMonoidHom := by
    intro p hp
    have hpa : p * a = a * p :=
      Subgroup.mem_centralizer_iff.mp (hAC haA) p (hP hp)
    have hconj : (MulAut.conj a).toMonoidHom p = p := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc a * p * a⁻¹ = (p * a) * a⁻¹ := by rw [hpa]
        _ = p := by group
    exact hconj ▸ Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hp
  let Lfun : Subgroup G := L.map (MulAut.conj a).toMonoidHom
  have hLfun_comp : CFSG.IsComponent Lfun :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hL
  have hLfun_ne : Lfun ≠ L := by
    intro h
    exact haN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hLfunC : Lfun ≤ Subgroup.centralizer (L : Set G) := by
    rcases CFSG.LocalCores.distinct_components_commute hLfun_comp hL with heq | hbot
    · exact absurd heq hLfun_ne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hP₁_center : P₁ ≤ (Subgroup.center ↥L).map L.subtype := by
    intro p hp
    have hpL : p ∈ L := hP₁L hp
    have hpLa : p ∈ Lfun := by
      have := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hP₁L (hP₁_le_Pa hp)
      simpa [Lfun] using this
    have hpC : p ∈ Subgroup.centralizer (L : Set G) := hLfunC hpLa
    refine ⟨⟨p, hpL⟩, ?_, rfl⟩
    change (⟨p, hpL⟩ : ↥L) ∈ Subgroup.center ↥L
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hpC (y : G) y.2)
  have hP₁bot : P₁ = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    have hmem := hP₁_center hp
    rw [CFSG.Quasithin.F7Two.center_eq_bot_of_isComponent hrad hL, Subgroup.map_bot] at hmem
    exact hmem
  exact hP₁ne hP₁bot

theorem exists_isPGroup_not_le_centralizer_of_not_le_normalizer
    (hrad : CFSG.solvableRadical G = ⊥) {A L : Subgroup G} (hL : CFSG.IsComponent L)
    (hA : (Nat.card A).Prime) (hAL : ¬ A ≤ normalizer (L : Set G)) {s : ℕ} (hs : s.Prime)
    (hsL : s ∣ Nat.card L) :
    ∃ P : Subgroup G, IsPGroup s P ∧ A ≤ normalizer (P : Set G) ∧
      ¬ A ≤ centralizer (P : Set G) := by
  classical
  obtain ⟨a, haA, haN⟩ := SetLike.not_le_iff_exists.mp hAL
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨P₁, hP₁⟩ := CFSG.ABGLocalTools.exists_isSylowOf (G := G) s L
  let Pfun : A → Subgroup G := fun x => P₁.map (MulAut.conj (x : G)).toMonoidHom
  let P : Subgroup G := ⨆ x : A, Pfun x
  have hPfun : ∀ x : A, IsPGroup s (Pfun x) := fun x => hP₁.isPGroup.map _
  have hPcomm : ∀ x y : A, x ≠ y → ⁅Pfun x, Pfun y⁆ = ⊥ := by
    intro x y hxy
    have hne : L.map (MulAut.conj (x : G)).toMonoidHom ≠
        L.map (MulAut.conj (y : G)).toMonoidHom :=
      component_conj_ne_of_not_le_normalizer hA hAL hxy
    have hxcomp : CFSG.IsComponent (L.map (MulAut.conj (x : G)).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (x : G)) hL
    have hycomp : CFSG.IsComponent (L.map (MulAut.conj (y : G)).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (y : G)) hL
    rcases CFSG.LocalCores.distinct_components_commute hxcomp hycomp with heq | hbot
    · exact absurd heq hne
    · have hle : ⁅Pfun x, Pfun y⁆ ≤ ⁅L.map (MulAut.conj (x : G)).toMonoidHom,
          L.map (MulAut.conj (y : G)).toMonoidHom⁆ :=
        Subgroup.commutator_mono (Subgroup.map_mono hP₁.le) (Subgroup.map_mono hP₁.le)
      rw [hbot] at hle
      exact le_bot_iff.mp hle
  have hPp : IsPGroup s P := by
    have := CFSG.Quasithin.C2Push.isPGroup_iSup_of_pairwise_commute Pfun hPfun hPcomm
    simpa [P] using this
  have hP_eq : P = ⨆ x ∈ A, P₁.map (MulAut.conj x).toMonoidHom := by
    dsimp [P, Pfun]
    exact iSup_subtype'' (A : Set G) (fun x : G => P₁.map (MulAut.conj x).toMonoidHom)
  have hPN : A ≤ normalizer (P : Set G) := by
    rw [hP_eq]
    exact CFSG.GroupTheory.le_normalizer_iSup_map_conj A P₁
  have hPnotC : ¬ A ≤ centralizer (P : Set G) := by
    have hP₁ne : P₁ ≠ ⊥ := by
      obtain ⟨Q, hQ⟩ := hP₁
      have hQne : (Q : Subgroup L) ≠ ⊥ := Q.ne_bot_of_dvd_card hsL
      intro hbot
      have hmapbot : (Q : Subgroup L).map L.subtype = ⊥ := by rw [hQ, hbot]
      exact hQne (Subgroup.map_eq_bot_iff_of_injective (Q : Subgroup L)
        L.subtype_injective |>.mp hmapbot)
    have := not_le_centralizer_iSup_map_conj_of_isComponent hrad hL hP₁.le hP₁ne haA haN
    simpa [P, Pfun] using this
  exact ⟨P, hPp, hPN, hPnotC⟩

theorem eq_one_of_inner_on_component
    (hrad : CFSG.solvableRadical G = ⊥) {L : Subgroup G} (hL : CFSG.IsComponent L)
    {r : ℕ} (hr : r.Prime) (hrL : ¬ r ∣ Nat.card L) {a k₀ : G} (har : a ^ r = 1)
    (hk₀ : k₀ ∈ L) (hconj : ∀ x ∈ L, a⁻¹ * x * a = k₀⁻¹ * x * k₀) : k₀ = 1 := by
  have key : ∀ n : ℕ, ∀ x ∈ L,
      (a⁻¹) ^ n * x * a ^ n = (k₀⁻¹) ^ n * x * k₀ ^ n := by
    intro n
    induction n with
    | zero =>
      intro x _
      simp
    | succ n ih =>
      intro x hx
      have hy : (k₀⁻¹) ^ n * x * k₀ ^ n ∈ L :=
        L.mul_mem (L.mul_mem (L.pow_mem (L.inv_mem hk₀) n) hx) (L.pow_mem hk₀ n)
      calc (a⁻¹) ^ (n + 1) * x * a ^ (n + 1)
          = a⁻¹ * ((a⁻¹) ^ n * x * a ^ n) * a := by group
        _ = a⁻¹ * ((k₀⁻¹) ^ n * x * k₀ ^ n) * a := by rw [ih x hx]
        _ = k₀⁻¹ * ((k₀⁻¹) ^ n * x * k₀ ^ n) * k₀ := hconj _ hy
        _ = (k₀⁻¹) ^ (n + 1) * x * k₀ ^ (n + 1) := by group
  have hxr : ∀ x ∈ L, x * k₀ ^ r = k₀ ^ r * x := by
    intro x hx
    have h := key r x hx
    have hainv : (a⁻¹) ^ r = 1 := by rw [inv_pow, har, inv_one]
    have hkinv : (k₀⁻¹) ^ r = (k₀ ^ r)⁻¹ := inv_pow k₀ r
    rw [hainv, hkinv, har] at h
    have hx' : x = (k₀ ^ r)⁻¹ * x * k₀ ^ r := by simpa using h
    have hk : k₀ ^ r * x = x * k₀ ^ r := by
      conv_lhs => rw [hx']
      group
    exact hk.symm
  have hcenter : (⟨k₀ ^ r, L.pow_mem hk₀ r⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hxr y y.2)
  have hz : (⟨k₀ ^ r, L.pow_mem hk₀ r⟩ : ↥L) = 1 := by
    have hbot : Subgroup.center ↥L = ⊥ :=
      CFSG.Quasithin.F7Two.center_eq_bot_of_isComponent hrad hL
    rw [hbot] at hcenter
    exact Subgroup.mem_bot.mp hcenter
  have hk0r : k₀ ^ r = 1 := congrArg Subtype.val hz
  have hdvd : orderOf k₀ ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hk0r
  have hdvdL : orderOf k₀ ∣ Nat.card L := Subgroup.orderOf_dvd_natCard L hk₀
  have hcop : Nat.Coprime r (Nat.card L) := (hr.coprime_iff_not_dvd).mpr hrL
  have hgcd : Nat.gcd r (Nat.card L) = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
  have hdvd1 : orderOf k₀ ∣ 1 := by
    rw [← hgcd]
    exact Nat.dvd_gcd hdvd hdvdL
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

theorem le_centralizer_singleton_of_inner_on_component
    (hrad : CFSG.solvableRadical G = ⊥) {L : Subgroup G} (hL : CFSG.IsComponent L)
    {r : ℕ} (hr : r.Prime) (hrL : ¬ r ∣ Nat.card L) {a k₀ : G} (har : a ^ r = 1)
    (hk₀ : k₀ ∈ L) (hconj : ∀ x ∈ L, a⁻¹ * x * a = k₀⁻¹ * x * k₀) :
    L ≤ Subgroup.centralizer ({a} : Set G) := by
  have hk0 : k₀ = 1 := eq_one_of_inner_on_component hrad hL hr hrL har hk₀ hconj
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hconj x hx
  rw [hk0] at h
  simp only [inv_one, one_mul, mul_one] at h
  calc x * a = a * (a⁻¹ * x * a) := by group
    _ = a * x := by rw [h]

theorem layer_eq_top_of_inner_component_actions
    (hrad : CFSG.solvableRadical G = ⊥) {A : Subgroup G}
    (hgen : normalClosure (A : Set G) = ⊤)
    (hnorm : ∀ L : Subgroup G, CFSG.IsComponent L → A ≤ normalizer (L : Set G))
    (hInner : ∀ a ∈ A, ∀ L : Subgroup G, CFSG.IsComponent L →
      ∃ k₀ ∈ L, ∀ x ∈ L, a⁻¹ * x * a = k₀⁻¹ * x * k₀) :
    CFSG.layer G = ⊤ := by
  have hA_layer : A ≤ CFSG.layer G := by
    intro a ha
    exact inner_component_actions_force_layer hrad a
      (fun K hK => hnorm K hK ha) (fun K hK => hInner a ha K hK)
  have : (CFSG.layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  have hle : normalClosure (A : Set G) ≤ CFSG.layer G :=
    Subgroup.normalClosure_le_normal (fun x hx => hA_layer hx)
  rw [hgen] at hle
  exact top_le_iff.mp hle

theorem isSimpleGroup_of_inner_component_actions_of_dvd
    (hrad : CFSG.solvableRadical G = ⊥) {A : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hA : Nat.card A = r) (hgen : normalClosure (A : Set G) = ⊤)
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup G) ≤ 1)
    (hnorm : ∀ L : Subgroup G, CFSG.IsComponent L → A ≤ normalizer (L : Set G))
    (hlayer_top : CFSG.layer G = ⊤)
    (hdiv : ∃ L : Subgroup G, CFSG.IsComponent L ∧ r ∣ Nat.card L) :
    IsSimpleGroup G := by
  obtain ⟨L, hL, hrL⟩ := hdiv
  have hA_L : A ≤ L :=
    le_of_card_eq_prime_of_dvd_card hr hr2 hA (hnorm L hL) hrank hrL
  have hLnorm : L.Normal :=
    CFSG.LocalCores.component_normal_of_layer_eq_top hlayer_top hL
  have : L.Normal := hLnorm
  have htop_le_L : (⊤ : Subgroup G) ≤ L := by
    rw [← hgen]
    exact Subgroup.normalClosure_le_normal (fun x hx => hA_L hx)
  have hLtop : L = ⊤ := top_le_iff.mp htop_le_L
  have : IsSimpleGroup ↥L := CFSG.Quasithin.F7Two.isSimpleGroup_of_isComponent hrad hL
  have : IsSimpleGroup ↥(⊤ : Subgroup G) := by
    rw [← hLtop]
    exact ‹IsSimpleGroup ↥L›
  exact MulEquiv.isSimpleGroup Subgroup.topEquiv.symm

theorem false_of_inner_component_actions_of_not_dvd
    (hrad : CFSG.solvableRadical G = ⊥) {A : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hA : Nat.card A = r)
    (hInner : ∀ a ∈ A, ∀ L : Subgroup G, CFSG.IsComponent L →
      ∃ k₀ ∈ L, ∀ x ∈ L, a⁻¹ * x * a = k₀⁻¹ * x * k₀)
    (hlayer_top : CFSG.layer G = ⊤)
    (hno : ∀ L : Subgroup G, CFSG.IsComponent L → ¬ r ∣ Nat.card L) :
    False := by
  have hAr : ∀ a ∈ A, a ^ r = 1 := by
    intro a ha
    have hdvd : orderOf a ∣ r := by
      simpa [hA] using Subgroup.orderOf_dvd_natCard A ha
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hcenterA : A ≤ Subgroup.center G := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    have hLcent : CFSG.layer G ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [CFSG.layer.eq_sSup]
      refine sSup_le fun K hK => ?_
      obtain ⟨k₀, hk₀, hconj⟩ := hInner a ha K hK
      exact le_centralizer_singleton_of_inner_on_component hrad hK hr (hno K hK)
        (hAr a ha) hk₀ hconj
    have hg : g ∈ CFSG.layer G := by
      rw [hlayer_top]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLcent hg)
  have hcenter_le : Subgroup.center G ≤ CFSG.solvableRadical G :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical inferInstance inferInstance
  have hcenter_bot : Subgroup.center G = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' := hcenter_le hz
    rwa [hrad] at hz'
  have hAbot : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hza := hcenterA ha
    rw [hcenter_bot] at hza
    exact hza
  have hcard : Nat.card A = 1 := by rw [hAbot, Subgroup.card_bot]
  exact hr.ne_one (by rw [← hA, hcard])

theorem exists_isComponent_of_not_inner_on_component
    {A : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hA : Nat.card A = r)
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup G) ≤ 1)
    (hnorm : ∀ L : Subgroup G, CFSG.IsComponent L → A ≤ normalizer (L : Set G))
    {a : G} (ha : a ∈ A) {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hno : ∀ k₀ ∈ L, ¬ ∀ x ∈ L, a⁻¹ * x * a = k₀⁻¹ * x * k₀) :
    CFSG.IsComponent L ∧ A ≤ normalizer (L : Set G) ∧ ¬ r ∣ Nat.card L ∧ ⁅L, A⁆ ≠ ⊥ := by
  have hAL : A ≤ normalizer (L : Set G) := hnorm L hL
  have hnotle : ¬ A ≤ L := by
    intro hAle
    exact (hno a (hAle ha)) (fun x _ => rfl)
  have hrL : ¬ r ∣ Nat.card L := by
    intro hrL
    exact hnotle (le_of_card_eq_prime_of_dvd_card hr hr2 hA hAL hrank hrL)
  have hcomm : ⁅L, A⁆ ≠ ⊥ := by
    intro hbot
    rw [Subgroup.commutator_comm] at hbot
    have hAleC : A ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact (hno 1 (L.one_mem)) (fun x hx => by
      have hx' : x * a = a * x := Subgroup.mem_centralizer_iff.mp (hAleC ha) x hx
      calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
        _ = a⁻¹ * (a * x) := by rw [hx']
        _ = x := by group
        _ = (1 : G)⁻¹ * x * 1 := by simp)
  exact ⟨hL, hAL, hrL, hcomm⟩

theorem isSimpleGroup_or_exists_isComponent (hrad : CFSG.solvableRadical G = ⊥)
    {A : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hA : Nat.card A = r)
    (hgen : normalClosure (A : Set G) = ⊤) (hrank : CFSG.Open.pRank r (⊤ : Subgroup G) ≤ 1)
    (hnorm : ∀ L : Subgroup G, CFSG.IsComponent L → A ≤ normalizer (L : Set G)) :
    IsSimpleGroup G ∨ ∃ L : Subgroup G, CFSG.IsComponent L ∧ A ≤ normalizer (L : Set G) ∧
      ¬ r ∣ Nat.card L ∧ ⁅L, A⁆ ≠ ⊥ := by
  classical
  by_cases hInner : ∀ a ∈ A, ∀ L : Subgroup G, CFSG.IsComponent L →
      ∃ k₀ ∈ L, ∀ x ∈ L, a⁻¹ * x * a = k₀⁻¹ * x * k₀
  · have hlayer_top : CFSG.layer G = ⊤ :=
      layer_eq_top_of_inner_component_actions hrad hgen hnorm hInner
    by_cases hdiv : ∃ L : Subgroup G, CFSG.IsComponent L ∧ r ∣ Nat.card L
    · exact Or.inl (isSimpleGroup_of_inner_component_actions_of_dvd hrad hr hr2 hA hgen hrank
        hnorm hlayer_top hdiv)
    · push Not at hdiv
      exact (false_of_inner_component_actions_of_not_dvd hrad hr hA hInner hlayer_top hdiv).elim
  · push Not at hInner
    obtain ⟨a, ha, L, hL, hno⟩ := hInner
    have hno' : ∀ k₀ ∈ L, ¬ ∀ x ∈ L, a⁻¹ * x * a = k₀⁻¹ * x * k₀ := by
      intro k₀ hk₀ h
      obtain ⟨x, hx, hne⟩ := hno k₀ hk₀
      exact hne (h x hx)
    exact Or.inr ⟨L,
      exists_isComponent_of_not_inner_on_component hr hr2 hA hrank hnorm ha hL hno'⟩

end CFSG.LocalAnalysis
