module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)

section General

variable {G : Type*} [Group G]

theorem le_centralizer_of_isQuasisimple_of_odd [Finite G] {F M : Subgroup G}
    (hF : CFSG.IsQuasisimple F) (hM : Odd (Nat.card M)) (hFM : F ≤ normalizer (M : Set G))
    (hMF : M ≤ normalizer (F : Set G)) : M ≤ centralizer (F : Set G) := by
  have hc1 : ⁅F, M⁆ ≤ M := le_normalizer_iff_commutator_le_right.1 hFM
  have hc2 : ⁅F, M⁆ ≤ F := le_normalizer_iff_commutator_le_left.1 hMF
  have hn : ((M ⊓ F).subgroupOf F).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact ⟨(mem_normalizer_iff.1 (hFM g.2) n).1 hn.1,
      F.mul_mem (F.mul_mem g.2 hn.2) (F.inv_mem g.2)⟩⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hF hn with htop | hcen
  · exfalso
    have hFM' : F ≤ M := fun f hf => by
      have : (⟨f, hf⟩ : F) ∈ (M ⊓ F).subgroupOf F := htop ▸ mem_top _
      exact (mem_subgroupOf.1 this).1
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hM.of_dvd_nat (card_dvd_of_le hFM'))
    have : Nontrivial F := CFSG.LocalCores.isQuasisimple_nontrivial hF
    have : Group.IsPerfect F := hF.1
    exact Group.IsPerfect.not_isSolvable F hsolv
  · have hcc : ⁅F, M⁆ ≤ centralizer (F : Set G) := fun c hc => by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := mem_center_iff.1 (hcen (mem_subgroupOf.2
        (show ((⟨c, hc2 hc⟩ : F) : G) ∈ M ⊓ F from ⟨hc1 hc, hc2 hc⟩))) ⟨y, hy⟩
      exact congrArg Subtype.val h1
    have hbot := CFSG.LocalCores.perfect_double_commutator hF.1
      (commutator_eq_bot_iff_le_centralizer.2 hcc)
    rw [commutator_comm] at hbot
    exact commutator_eq_bot_iff_le_centralizer.1 hbot

theorem mem_of_mem_sup_of_mem_centralizer {Y D : Subgroup G}
    (hYD : Y ≤ centralizer (D : Set G)) (hZ : center D = ⊥) {g : G} (hg : g ∈ Y ⊔ D)
    (hgD : g ∈ centralizer (D : Set G)) : g ∈ Y := by
  have hYN : Y ≤ normalizer (D : Set G) := hYD.trans (Subgroup.centralizer_le_normalizer _)
  have hg' : g ∈ ((Y ⊔ D : Subgroup G) : Set G) := hg
  rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at hg'
  obtain ⟨y, hy, d, hd, rfl⟩ := Set.mem_mul.1 hg'
  have hdC : d ∈ centralizer (D : Set G) := by
    have := mul_mem (inv_mem (hYD hy)) hgD
    rwa [inv_mul_cancel_left] at this
  have hd1 : d = 1 := by
    have : (⟨d, hd⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro z
      exact Subtype.ext (mem_centralizer_iff.1 hdC z z.2)
    rw [hZ, mem_bot] at this
    exact congrArg Subtype.val this
  rw [hd1, mul_one]
  exact hy

theorem mem_centralizer_of_mem_oddCore_of_commute [Finite G] {H D : Subgroup G} {t : G}
    (htH : t ∈ H) (hDH : D ≤ H) (hDt : D ≤ centralizer ({t} : Set G))
    (hDq : CFSG.IsQuasisimple D)
    (hDn : ∀ c ∈ H ⊓ centralizer ({t} : Set G), ∀ d ∈ D, c * d * c⁻¹ ∈ D) {c : H}
    (hc : c ∈ oddCore H) (hct : c * ⟨t, htH⟩ = ⟨t, htH⟩ * c) :
    (c : G) ∈ centralizer (D : Set G) := by
  have hOodd : Odd (Nat.card (oddCore H)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hDq' : CFSG.IsQuasisimple (D.subgroupOf H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDH).symm hDq
  have hModd : Odd (Nat.card (oddCore H ⊓ centralizer ({⟨t, htH⟩} : Set H) : Subgroup H)) :=
    hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hconjM : ∀ d ∈ D.subgroupOf H, ∀ m ∈ oddCore H ⊓ centralizer ({⟨t, htH⟩} : Set H),
      d * m * d⁻¹ ∈ oddCore H ⊓ centralizer ({⟨t, htH⟩} : Set H) := by
    intro d hd m hm
    refine mem_inf.2 ⟨(oddCore_normal (G := H)).conj_mem m (mem_inf.1 hm).1 d, ?_⟩
    have hdt : d * ⟨t, htH⟩ = ⟨t, htH⟩ * d :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
    have hdt' : d⁻¹ * ⟨t, htH⟩ = ⟨t, htH⟩ * d⁻¹ := by
      calc d⁻¹ * ⟨t, htH⟩ = d⁻¹ * (⟨t, htH⟩ * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * ⟨t, htH⟩) * d⁻¹ := by rw [hdt]
        _ = ⟨t, htH⟩ * d⁻¹ := by group
    have hmt := mem_centralizer_singleton_iff.1 (mem_inf.1 hm).2
    rw [mem_centralizer_singleton_iff]
    calc d * m * d⁻¹ * ⟨t, htH⟩ = d * m * (d⁻¹ * ⟨t, htH⟩) := by group
      _ = d * m * (⟨t, htH⟩ * d⁻¹) := by rw [hdt']
      _ = d * (m * ⟨t, htH⟩) * d⁻¹ := by group
      _ = d * (⟨t, htH⟩ * m) * d⁻¹ := by rw [hmt]
      _ = (d * ⟨t, htH⟩) * m * d⁻¹ := by group
      _ = (⟨t, htH⟩ * d) * m * d⁻¹ := by rw [hdt]
      _ = ⟨t, htH⟩ * (d * m * d⁻¹) := by group
  have hDM : D.subgroupOf H ≤
      normalizer ((oddCore H ⊓ centralizer ({⟨t, htH⟩} : Set H) : Subgroup H) : Set H) :=
    fun d hd => by
      rw [mem_normalizer_iff]
      intro m
      refine ⟨hconjM d hd m, fun h => ?_⟩
      have := hconjM d⁻¹ ((D.subgroupOf H).inv_mem hd) _ h
      have e : d⁻¹ * (d * m * d⁻¹) * d⁻¹⁻¹ = m := by group
      rwa [e] at this
  have hconjD : ∀ m ∈ oddCore H ⊓ centralizer ({⟨t, htH⟩} : Set H), ∀ d ∈ D.subgroupOf H,
      m * d * m⁻¹ ∈ D.subgroupOf H := by
    intro m hm d hd
    have hmC : (m : G) ∈ H ⊓ centralizer ({t} : Set G) :=
      mem_inf.2 ⟨m.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 (mem_inf.1 hm).2))⟩
    rw [mem_subgroupOf] at hd ⊢
    simpa using hDn _ hmC _ hd
  have hMD : oddCore H ⊓ centralizer ({⟨t, htH⟩} : Set H) ≤
      normalizer ((D.subgroupOf H : Subgroup H) : Set H) := fun m hm => by
    rw [mem_normalizer_iff]
    intro d
    refine ⟨hconjD m hm d, fun h => ?_⟩
    have := hconjD m⁻¹ (inv_mem hm) _ h
    have e : m⁻¹ * (m * d * m⁻¹) * m⁻¹⁻¹ = d := by group
    rwa [e] at this
  have hMDc := le_centralizer_of_isQuasisimple_of_odd hDq' hModd hDM hMD
  have hcM : c ∈ oddCore H ⊓ centralizer ({⟨t, htH⟩} : Set H) :=
    mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hct⟩
  rw [mem_centralizer_iff]
  intro d hd
  have := mem_centralizer_iff.1 (hMDc hcM) ⟨d, hDH hd⟩ (mem_subgroupOf.2 hd)
  exact congrArg Subtype.val this

end General

section F4

variable {K : Type} [Field K]


private theorem mem_C3Levi_iff_mem_c3PerpLevi' {x : adjointGroup .F4 K} :
    x ∈ C3Levi K ↔ (x : ModGL .F4 K) ∈ c3PerpLevi K := by
  have h : c3PerpRoots = c3LeviRoots := by
    ext γ
    rw [mem_c3PerpRoots_iff, mem_c3LeviRoots]
  rw [mem_C3Levi_iff, c3PerpLevi, h]

variable {G : Type*} [Group G] {L : Subgroup G}

theorem exists_mem_inv_mul_mem_zpowers [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {X : Subgroup G} {Y : Subgroup (adjointGroup .F4 K)}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) ≤ Y ⊔ C3Levi K)
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) {c : G}
    (hcX : c ∈ centralizer (X : Set G)) (hct : c * t = t * c)
    (hcD : c ∈ centralizer (D : Set G)) :
    ∃ y ∈ (Y.map e.symm.toMonoidHom).map L.subtype, y⁻¹ * c ∈ zpowers t := by
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  have hf := one_le_of_natCard_eq_two_pow hKc
  set XC : Subgroup (adjointGroup .F4 K) := (X.subgroupOf L).map e.toMonoidHom with hXCdef
  have hcN : c ∈ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
      (mem_centralizer_singleton_iff.2 hct)
  set β := L.normalizerMonoidHom ⟨c, hcN⟩ with hβ
  have hβapp : ∀ a : L, ((β a : L) : G) = c * a * c⁻¹ := fun a => by
    simp [hβ, normalizerMonoidHom_apply_apply_coe]
  have hβ'app : ∀ x, MulAut.congr e β x = e (β (e.symm x)) := fun x => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hfixD : ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ c3PerpLevi K →
      MulAut.congr e β x = x := by
    intro x hx
    have hxD : x ∈ C3Levi K := mem_C3Levi_iff_mem_c3PerpLevi'.2 hx
    have hmem : ((e.symm x : L) : G) ∈ D := by
      rw [hDe]
      exact ⟨e.symm x, ⟨x, hxD, rfl⟩, rfl⟩
    have h1 : β (e.symm x) = e.symm x := by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 hcD _ hmem, mul_inv_cancel_right]
    rw [hβ'app, h1, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg, hgD⟩ := exists_eq_conj_of_fix_c3PerpLevi hf hKc _ hfixD
  have hgX : g ∈ centralizer (XC : Set (adjointGroup .F4 K)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 : β a = a := by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 hcX _ (mem_subgroupOf.1 ha), mul_inv_cancel_right]
    have h2 : MulAut.congr e β (e a) = e a := by
      rw [hβ'app, MulEquiv.symm_apply_apply, h1]
    rw [hg, MulAut.conj_apply] at h2
    calc e.toMonoidHom a * g = g * e a * g⁻¹ * g := by rw [h2]; rfl
      _ = g * e.toMonoidHom a := by simp
  have hgD' : g ∈ centralizer (C3Levi K : Set (adjointGroup .F4 K)) :=
    mem_centralizer_iff.2 fun x hx => (hgD x (mem_C3Levi_iff_mem_c3PerpLevi'.1 hx)).symm
  have hgY : g ∈ Y := mem_of_mem_sup_of_mem_centralizer hYD center_C3Levi_eq_bot (hXc hgX) hgD'
  set a₀ : L := e.symm g with ha₀
  have hga₀ : e a₀ = g := by rw [ha₀, MulEquiv.apply_symm_apply]
  have hβa : ∀ l : L, β l = a₀ * l * a₀⁻¹ := by
    intro l
    have h1 : MulAut.congr e β (e l) = g * e l * g⁻¹ := by rw [hg, MulAut.conj_apply]
    rw [hβ'app, MulEquiv.symm_apply_apply, ← hga₀] at h1
    apply e.injective
    rw [h1]
    simp
  have hcen : (a₀ : G)⁻¹ * c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun l hl => ?_, ?_⟩
    · have h1 := congrArg Subtype.val (hβa ⟨l, hl⟩)
      rw [hβapp] at h1
      simp only [coe_mul, coe_inv] at h1
      calc l * ((a₀ : G)⁻¹ * c) = (a₀ : G)⁻¹ * ((a₀ : G) * l * (a₀ : G)⁻¹) * c := by group
        _ = (a₀ : G)⁻¹ * (c * l * c⁻¹) * c := by rw [h1]
        _ = (a₀ : G)⁻¹ * c * l := by group
    · rw [mem_centralizer_singleton_iff]
      have hta : (a₀ : G) * t = t * a₀ := mem_centralizer_iff.1 htC _ a₀.2
      have hta' : (a₀ : G)⁻¹ * t = t * (a₀ : G)⁻¹ := by
        calc (a₀ : G)⁻¹ * t = (a₀ : G)⁻¹ * (t * a₀) * (a₀ : G)⁻¹ := by group
          _ = (a₀ : G)⁻¹ * ((a₀ : G) * t) * (a₀ : G)⁻¹ := by rw [hta]
          _ = t * (a₀ : G)⁻¹ := by group
      calc (a₀ : G)⁻¹ * c * t = (a₀ : G)⁻¹ * (c * t) := by group
        _ = (a₀ : G)⁻¹ * (t * c) := by rw [hct]
        _ = ((a₀ : G)⁻¹ * t) * c := by group
        _ = (t * (a₀ : G)⁻¹) * c := by rw [hta']
        _ = t * ((a₀ : G)⁻¹ * c) := by group
  rw [hK] at hcen
  exact ⟨a₀, ⟨a₀, ⟨g, hgY, rfl⟩, rfl⟩, hcen⟩

theorem mem_map_of_mem_oddCore_of_commute [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {X : Subgroup G} {Y : Subgroup (adjointGroup .F4 K)}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) ≤ Y ⊔ C3Levi K)
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K))) (hYodd : Odd (Nat.card Y))
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    {c : centralizer (X : Set G)} (hc : c ∈ oddCore (centralizer (X : Set G)))
    (hct : c * ⟨t, htX⟩ = ⟨t, htX⟩ * c) : (c : G) ∈ (Y.map e.symm.toMonoidHom).map L.subtype := by
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  have hOodd : Odd (Nat.card (oddCore (centralizer (X : Set G)))) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  have hDLX : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  have hcD : (c : G) ∈ centralizer (D : Set G) := by
    refine mem_centralizer_of_mem_oddCore_of_commute htX (hDLX.trans inf_le_right)
      (fun d hd => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDLX hd).1))
      (hDe ▸ isQuasisimple_map_C3Levi e) (fun m hm d hd => ?_) hc hct
    have hd' : d ∈ inSubgroup layer (L ⊓ centralizer (X : Set G)) := hD ▸ hd
    have := layer_centralizer_normalized hLt hm hd'
    rwa [← hD] at this
  obtain ⟨y, hy, hyc⟩ := exists_mem_inv_mul_mem_zpowers hKc hL htC ht hK e hXc hYD hDe c.2
    (congrArg Subtype.val hct) hcD
  set Y' : Subgroup G := (Y.map e.symm.toMonoidHom).map L.subtype with hY'
  have hY'L : Y' ≤ L := map_subtype_le _
  have hY'odd : Odd (Nat.card Y') := by
    rw [hY', card_map_of_injective L.subtype_injective,
      card_map_of_injective e.symm.injective]
    exact hYodd
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hyc with h1 | h1
  · have hcy : (c : G) = y := by
      calc (c : G) = y * (y⁻¹ * c) := by group
        _ = y := by rw [h1, mul_one]
    rw [hcy]
    exact hy
  · exfalso
    have hcodd : Odd (orderOf (c : G)) := by
      rw [orderOf_submonoid]
      exact hOodd.of_dvd_nat ((oddCore (centralizer (X : Set G))).orderOf_dvd_natCard hc)
    have hyt : y * t = t * y := mem_centralizer_iff.1 htC y (hY'L hy)
    have hcy : (c : G) = y * t := by
      calc (c : G) = y * (y⁻¹ * c) := by group
        _ = y * t := by rw [h1]
    obtain ⟨j, hj⟩ := hcodd
    have hpow : (c : G) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have htt : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [hcy, (show Commute y t from hyt).mul_pow, pow_succ t, pow_mul, htt, one_pow,
      one_mul] at hpow
    have htY : t ∈ Y' := by
      have : t = (y ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]
      exact Y'.inv_mem (Y'.pow_mem hy _)
    have h2 := Y'.orderOf_dvd_natCard htY
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.2 hY'odd) (even_iff_two_dvd.2 h2)

theorem oddCore_inf_centralizer_le_X [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {X : Subgroup G} (hXL : X ≤ L) (hXodd : Odd (Nat.card X))
    (htX : t ∈ centralizer (X : Set G))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) = (X.subgroupOf L).map e.toMonoidHom ⊔ C3Levi K)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    {c : centralizer (X : Set G)} (hc : c ∈ oddCore (centralizer (X : Set G)))
    (hct : c * ⟨t, htX⟩ = ⟨t, htX⟩ * c) : (c : G) ∈ X := by
  have hXD : (X.subgroupOf L).map e.toMonoidHom ≤
      centralizer (C3Levi K : Set (adjointGroup .F4 K)) := by
    rw [le_centralizer_iff, hXc]
    exact le_sup_right
  have hXCodd : Odd (Nat.card ((X.subgroupOf L).map e.toMonoidHom)) := by
    rw [card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hXL).toEquiv]
    exact hXodd
  obtain ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, hca⟩ :=
    mem_map_of_mem_oddCore_of_commute hKc hL htC ht hK e hXc.le hXD hXCodd htX hDe hD hc hct
  rw [← hca]
  simpa using mem_subgroupOf.1 ha

theorem mem_center_of_mem_oddCore_of_commute [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {X : Subgroup G} (hXL : X ≤ L) (hXodd : Odd (Nat.card X))
    (htX : t ∈ centralizer (X : Set G))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) = (X.subgroupOf L).map e.toMonoidHom ⊔ C3Levi K)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  intro c hc hct
  have hcX := oddCore_inf_centralizer_le_X hKc hL htC ht hK e hXL hXodd htX hXc hDe hD hc hct
  rw [mem_center_iff]
  intro h
  exact Subtype.ext (mem_centralizer_iff.1 h.2 _ hcX).symm

theorem hasBLift_neighbour [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {X : Subgroup G} (hXL : X ≤ L) (hXodd : Odd (Nat.card X))
    (htX : t ∈ centralizer (X : Set G))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) = (X.subgroupOf L).map e.toMonoidHom ⊔ C3Levi K)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  have htt : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [coe_mul, ← sq, ← ht, pow_orderOf_eq_one, coe_one])
  exact hasBLift_of_le_center htt hE htE hEt
    (mem_center_of_mem_oddCore_of_commute hKc hL htC ht hK e hXL hXodd htX hXc hDe hD)

theorem isComponent_oddCoreLift_neighbour [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {X : Subgroup G} (hXL : X ≤ L) (hXodd : Odd (Nat.card X))
    (htX : t ∈ centralizer (X : Set G))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) = (X.subgroupOf L).map e.toMonoidHom ⊔ C3Levi K)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : CFSG.IsComponent E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (htE' : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) :
    HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
      (oddCoreLift E).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = E ∧
      (oddCore (centralizer (X : Set G))).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) := by
  have htt : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [coe_mul, ← sq, ← ht, pow_orderOf_eq_one, coe_one])
  exact isComponent_oddCoreLift_of_le_center htt hE htE htE'
    (mem_center_of_mem_oddCore_of_commute hKc hL htC ht hK e hXL hXodd htX hXc hDe hD)

theorem hasBLift_neighbour_swap [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {X : Subgroup G} (hXL : X ≤ L) (hXodd : Odd (Nat.card X))
    (htX : t ∈ centralizer (X : Set G))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) = (X.subgroupOf L).map e.toMonoidHom ⊔ C3Levi K)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : ⁅Kb, Kb⁆ = Kb)
    (hcomm : ⁅Kb, Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥) :
    HasBLift (Kb ⊔ Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) ∧
      HasBLift Kb := by
  have htt : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [coe_mul, ← sq, ← ht, pow_orderOf_eq_one, coe_one])
  exact hasBLift_sup_conj_of_le_center htt hKb hcomm
    (mem_center_of_mem_oddCore_of_commute hKc hL htC ht hK e hXL hXodd htX hXc hDe hD)

theorem mem_center_of_mem_oddCore_of_commute_sup [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {A Y : Subgroup (adjointGroup .F4 K)}
    (hA : centralizer (A : Set (adjointGroup .F4 K)) = Y ⊔ C3Levi K)
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .F4 K))) (hYodd : Odd (Nat.card Y))
    (hYA : Y ≤ A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  have hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) ≤ Y ⊔ C3Levi K := by
    rw [hX, map_subgroupOf_map_symm]
    exact hA.le
  have hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
    rw [hX, inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc isQuasisimple_C3Levi, hDe]
  intro c hc hct
  have hcY := mem_map_of_mem_oddCore_of_commute hKc hL htC ht hK e hXc hYD hYodd htX hDe hD hc
    hct
  have hAX : ∀ y : G, y ∈ (A.map e.symm.toMonoidHom).map L.subtype → y ∈ X := fun y hy => by
    rw [hX]
    exact hy
  have hcX : (c : G) ∈ X := hAX _ (map_mono (map_mono hYA) hcY)
  rw [mem_center_iff]
  intro h
  exact Subtype.ext (mem_centralizer_iff.1 h.2 _ hcX).symm

theorem hasBLift_neighbour_sup [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {A Y : Subgroup (adjointGroup .F4 K)}
    (hA : centralizer (A : Set (adjointGroup .F4 K)) = Y ⊔ C3Levi K)
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .F4 K))) (hYodd : Odd (Nat.card Y))
    (hYA : Y ≤ A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  have htt : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [coe_mul, ← sq, ← ht, pow_orderOf_eq_one, coe_one])
  exact hasBLift_of_le_center htt hE htE hEt
    (mem_center_of_mem_oddCore_of_commute_sup hKc hL htC ht hK e hA hYD hYc hYodd hYA hX htX hDe)

theorem isComponent_oddCoreLift_neighbour_sup [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .F4 K) {A Y : Subgroup (adjointGroup .F4 K)}
    (hA : centralizer (A : Set (adjointGroup .F4 K)) = Y ⊔ C3Levi K)
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .F4 K))) (hYodd : Odd (Nat.card Y))
    (hYA : Y ≤ A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : CFSG.IsComponent E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (htE' : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) :
    HasBLift E ∧ CFSG.IsComponent (oddCoreLift E) ∧
      (oddCoreLift E).map (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = E ∧
      (oddCore (centralizer (X : Set G))).subgroupOf (oddCoreLift E) ≤ center (oddCoreLift E) := by
  have htt : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [coe_mul, ← sq, ← ht, pow_orderOf_eq_one, coe_one])
  exact isComponent_oddCoreLift_of_le_center htt hE htE htE'
    (mem_center_of_mem_oddCore_of_commute_sup hKc hL htC ht hK e hA hYD hYc hYodd hYA hX htX hDe)

theorem hasBLift_neighbour_nonsplit [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  have hf := one_le_of_natCard_eq_two_pow hKc
  obtain ⟨hcen, -, hXD⟩ := centralizer_nonsplit hXJ hcyc hX₀
  have hodd : Odd (Nat.card X₀) := by
    rw [hX₀, hKc]
    exact (Nat.even_pow' (by omega)).2 even_two |>.add_one
  exact hasBLift_neighbour_sup hKc hL htC ht hK e hcen hXD (le_centralizer_self_of_isCyclic hcyc)
    hodd le_rfl hX htX hDe hE htE hEt

end F4

end CFSG.SeitzReduction.F4Pilot
