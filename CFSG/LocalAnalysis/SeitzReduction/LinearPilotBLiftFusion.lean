module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOddCore
import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftF4
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.Inheritance

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

variable {G : Type*} [Group G]

section FourGroup

variable [Finite G]

omit [Finite G] in
theorem mem_normalizer_map_oddCore {H : Subgroup G} {h : G} (hh : h ∈ H) :
    h ∈ normalizer (((oddCore H).map H.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) hh hk, fun hk => ?_⟩
  have := conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) (H.inv_mem hh) hk
  rwa [show h⁻¹ * (h * k * h⁻¹) * h⁻¹⁻¹ = k by group] at this

theorem commute_of_mem_oddCore_of_four_group {H : Subgroup G} {t z : G} (htH : t ∈ H)
    (hzH : z ∈ H) (ht : orderOf t = 2) (hz : orderOf z = 2) (htz : t * z = z * t) (hne : t ≠ z)
    (h₁ : ∀ c ∈ (oddCore H).map H.subtype, c * t = t * c → c * z = z * c)
    (h₃ : ∀ c ∈ (oddCore H).map H.subtype, c * (t * z) = t * z * c → c * z = z * c) :
    ∀ c ∈ (oddCore H).map H.subtype, c * z = z * c := by
  classical
  set O : Subgroup G := (oddCore H).map H.subtype with hO
  have hOodd : Odd (Nat.card O) := by
    rw [hO, card_map_of_injective H.subtype_injective]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hT : IsKleinFour (closure ({t, z} : Set G)) :=
    CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair ht hz
      htz hne
  have hTO : closure ({t, z} : Set G) ≤ normalizer (O : Set G) := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact mem_normalizer_map_oddCore htH
    · exact mem_normalizer_map_oddCore hzH
  have h₁T : t ∈ closure ({t, z} : Set G) := subset_closure (Set.mem_insert _ _)
  have h₂T : z ∈ closure ({t, z} : Set G) := subset_closure (Set.mem_insert_of_mem _ rfl)
  have h₃T : t * z ∈ closure ({t, z} : Set G) := mul_mem h₁T h₂T
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htz1 : t * z ≠ 1 := fun h => hne (by
    calc t = t * (t * z) := by rw [h, mul_one]
      _ = t * t * z := by group
      _ = z := by rw [htt, one_mul])
  have h13 : t ≠ t * z := fun h => hz1 (by
    calc z = t⁻¹ * (t * z) := by group
      _ = t⁻¹ * t := by rw [← h]
      _ = 1 := inv_mul_cancel t)
  have h23 : z ≠ t * z := fun h => ht1 (by
    calc t = (t * z) * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel z)
  have hmain := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers hOodd hTO h₁T h₂T h₃T ht1
    hz1 htz1 hne h13 h23
  intro c hc
  have hc' : c ∈ (O : Set G) := hc
  rw [hmain] at hc'
  obtain ⟨ab, hab, c₃, hc₃, rfl⟩ := Set.mem_mul.1 hc'
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := Set.mem_mul.1 hab
  have e₁ : Commute c₁ z := h₁ c₁ hc₁.1 (mem_centralizer_singleton_iff.1 hc₁.2)
  have e₂ : Commute c₂ z := mem_centralizer_singleton_iff.1 hc₂.2
  have e₃ : Commute c₃ z := h₃ c₃ hc₃.1 (mem_centralizer_singleton_iff.1 hc₃.2)
  exact ((e₁.mul_left e₂).mul_left e₃).eq

end FourGroup

section Conjugate

variable [Finite G] {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem commute_of_mem_oddCore_of_commute_of_le (hK : 4 ≤ Nat.card K) {L' X : Subgroup G}
    (φ : L' ≃* LinearFlag.projectiveSL n K) (hXL' : X ≤ L') (hXc : IsCyclic X)
    (hXo : Odd (Nat.card X)) {s z : G}
    (hsN : centralizer ({s} : Set G) ≤ normalizer (L' : Set G)) (hzL' : z ∈ L')
    (hzX : z ∈ centralizer (X : Set G)) (hz : orderOf z = 2) (hzs : z * s = s * z) :
    ∀ c ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype,
      c * s = s * c → c * z = z * c := by
  set H := centralizer (X : Set G) with hH
  set O : Subgroup G := (oddCore H).map H.subtype with hO
  set S : Subgroup G := O ⊓ centralizer ({s} : Set G) with hS
  have hOodd : Odd (Nat.card O) := by
    rw [hO, card_map_of_injective H.subtype_injective]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hSodd : Odd (Nat.card S) := hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hzs' : z⁻¹ * s = s * z⁻¹ := by
    calc z⁻¹ * s = z⁻¹ * (s * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * s) * z⁻¹ := by rw [hzs]
      _ = s * z⁻¹ := by group
  have hzS : ∀ x ∈ S, z * x * z⁻¹ ∈ S := by
    intro x hx
    refine mem_inf.2 ⟨conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) hzX hx.1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hxs : x * s = s * x := mem_centralizer_singleton_iff.1 hx.2
    calc z * x * z⁻¹ * s = z * x * (z⁻¹ * s) := by group
      _ = z * x * (s * z⁻¹) := by rw [hzs']
      _ = z * (x * s) * z⁻¹ := by group
      _ = z * (s * x) * z⁻¹ := by rw [hxs]
      _ = (z * s) * x * z⁻¹ := by group
      _ = (s * z) * x * z⁻¹ := by rw [hzs]
      _ = s * (z * x * z⁻¹) := by group
  have hzp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hA10 := map_oddCore_inf_centralizer_le_centralizer hK φ hXL' hXc hXo hzL' hzX hzp
  have hc : ∀ x ∈ S, Commute z (x⁻¹ * (z * x * z⁻¹)) := by
    intro x hx
    have hwL' : x⁻¹ * (z * x * z⁻¹) ∈ L' := by
      have hxN : x⁻¹ ∈ normalizer (L' : Set G) := hsN (inv_mem hx.2)
      have h1 : x⁻¹ * z * x⁻¹⁻¹ ∈ L' := (mem_normalizer_iff.1 hxN z).1 hzL'
      have e : x⁻¹ * (z * x * z⁻¹) = (x⁻¹ * z * x⁻¹⁻¹) * z⁻¹ := by group
      rw [e]
      exact L'.mul_mem h1 (L'.inv_mem hzL')
    have hwO : x⁻¹ * (z * x * z⁻¹) ∈ O :=
      O.mul_mem (O.inv_mem hx.1) (conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) hzX hx.1)
    have hwX : x⁻¹ * (z * x * z⁻¹) ∈ centralizer (X : Set G) := map_subtype_le _ hwO
    set M : Subgroup G := L' ⊓ centralizer (X : Set G) with hM
    have hnormal : (O.subgroupOf M).Normal := ⟨fun m hm g => by
      rw [mem_subgroupOf] at hm ⊢
      exact conj_mem_map_subtype_of_normal (CFSG.oddCore_normal H) g.2.2 hm⟩
    have hodd : Odd (Nat.card (O.subgroupOf M)) := by
      have h1 : Nat.card (O.subgroupOf M) = Nat.card (O ⊓ M : Subgroup G) := by
        rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective M.subtype_injective]
      rw [h1]
      exact hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
    have hle := CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _ hnormal hodd
    have hwcore : x⁻¹ * (z * x * z⁻¹) ∈ (oddCore M).map M.subtype :=
      ⟨⟨_, hwL', hwX⟩, hle (mem_subgroupOf.2 hwO), rfl⟩
    exact (mem_centralizer_singleton_iff.1 (hA10 hwcore)).symm
  have hiter := commute_of_conj_mul_mem_of_coprime (S := S) hz2
    (Nat.coprime_two_left.2 hSodd) hzS hc
  intro c hc' hcs
  exact (hiter c ⟨hc', mem_centralizer_singleton_iff.2 hcs⟩).symm

theorem le_centralizer_oddCore_of_fused (hK : 4 ≤ Nat.card K) {L : Subgroup G}
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (hXc : IsCyclic X) (hXo : Odd (Nat.card X))
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) (hDq : CFSG.IsQuasisimple D)
    (hZD : Odd (Nat.card (center D))) {z g : G} (hzD : z ∈ D) (hz : orderOf z = 2)
    (hg : g⁻¹ * t * g = t * z) (hXg : X ≤ conjugate L g) (hzg : z ∈ conjugate L g) :
    ∀ c ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype,
      ∀ d ∈ D, c * d = d * c := by
  set H := centralizer (X : Set G) with hH
  set O : Subgroup G := (oddCore H).map H.subtype with hO
  have hDLX : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  have hzL : z ∈ L := (hDLX hzD).1
  have hzH : z ∈ H := (hDLX hzD).2
  have htz : t * z = z * t := (mem_centralizer_iff.1 htC z hzL).symm
  have hnotcen : ∀ y ∈ D, orderOf y = 2 → ¬ (∀ d ∈ D, y * d = d * y) := by
    intro y hyD hy hcen
    have hyZ : (⟨y, hyD⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro d
      exact Subtype.ext (hcen d d.2).symm
    have h2 := (center D).orderOf_dvd_natCard hyZ
    rw [orderOf_mk, hy] at h2
    exact (Nat.not_even_iff_odd.2 hZD) (even_iff_two_dvd.2 h2)
  have hne : t ≠ z := by
    rintro rfl
    exact hnotcen t hzD ht fun d hd => (mem_centralizer_iff.1 htC d (hDLX hd).1).symm
  have h₁ : ∀ c ∈ O, c * t = t * c → c * z = z * c := by
    rintro _ ⟨c, hc, rfl⟩ hct
    have hcD := F4Pilot.mem_centralizer_of_mem_oddCore_of_commute htX (hDLX.trans inf_le_right)
      (fun d hd => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDLX hd).1))
      hDq (fun m hm d hd => by
        have hd' : d ∈ inSubgroup layer (L ⊓ centralizer (X : Set G)) := hD ▸ hd
        have := layer_centralizer_normalized hLt hm hd'
        rwa [← hD] at this) hc (Subtype.ext hct)
    exact (mem_centralizer_iff.1 hcD z hzD).symm
  set L' : Subgroup G := conjugate L g with hL'
  have φ : L' ≃* LinearFlag.projectiveSL n K :=
    ((L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm).trans e
  have hsN : centralizer ({t * z} : Set G) ≤ normalizer (L' : Set G) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [← hg] at hx
      calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hx]
        _ = t * (g * x * g⁻¹) := by group
    have hxN := hLt hx'
    rw [mem_normalizer_iff]
    intro y
    have hmem : ∀ w : G, w ∈ L' ↔ g * w * g⁻¹ ∈ L := by
      intro w
      constructor
      · rintro ⟨l, hl, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hl
      · intro hw
        exact ⟨g * w * g⁻¹, hw, by simp [mul_assoc]⟩
    rw [hmem, hmem, mem_normalizer_iff.1 hxN]
    have e1 : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ := by group
    rw [e1]
  have h₃ := commute_of_mem_oddCore_of_commute_of_le hK φ hXg hXc hXo hsN hzg hzH hz
    (by rw [← mul_assoc, ← htz, mul_assoc])
  have hzO := commute_of_mem_oddCore_of_four_group (mem_centralizer_iff.2 fun x hx =>
    (mem_centralizer_iff.1 htX x hx)) hzH ht hz htz hne h₁ h₃
  set C : Subgroup G := D ⊓ centralizer (O : Set G) with hC
  have hzC : z ∈ C := ⟨hzD, mem_centralizer_iff.2 fun c hc => hzO c hc⟩
  have hCn : (C.subgroupOf D).Normal := ⟨fun m hm d => by
    rw [mem_subgroupOf] at hm ⊢
    refine ⟨D.mul_mem (D.mul_mem d.2 hm.1) (D.inv_mem d.2), mem_centralizer_iff.2 fun o ho => ?_⟩
    have hdN := mem_normalizer_map_oddCore (H := H) (hDLX.trans inf_le_right d.2)
    have ho' : (d : G)⁻¹ * o * (d : G)⁻¹⁻¹ ∈ O := (mem_normalizer_iff.1 (inv_mem hdN) o).1 ho
    have h1 := mem_centralizer_iff.1 hm.2 _ ho'
    calc o * ((d : G) * m * (d : G)⁻¹) =
        (d : G) * (((d : G)⁻¹ * o * (d : G)⁻¹⁻¹) * m) * (d : G)⁻¹ := by group
      _ = (d : G) * (m * ((d : G)⁻¹ * o * (d : G)⁻¹⁻¹)) * (d : G)⁻¹ := by rw [h1]
      _ = (d : G) * m * (d : G)⁻¹ * o := by group⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hDq hCn with htop | hcen
  · intro c hc d hd
    have hdC : (⟨d, hd⟩ : D) ∈ C.subgroupOf D := htop ▸ mem_top _
    exact (mem_centralizer_iff.1 (mem_subgroupOf.1 hdC).2 c hc)
  · exfalso
    refine hnotcen z hzD hz fun d hd => ?_
    have h1 := mem_center_iff.1 (hcen (mem_subgroupOf.2 (show ((⟨z, hzD⟩ : D) : G) ∈ C from hzC)))
      ⟨d, hd⟩
    exact (congrArg Subtype.val h1).symm

end Conjugate

section Lift

variable {H : Type*} [Group H] [Finite H]

theorem hasBLift_of_le_map_centralizer {E : Subgroup (H ⧸ oddCore H)}
    (hE : E ≤ (centralizer (oddCore H : Set H)).map (QuotientGroup.mk' (oddCore H))) :
    HasBLift E := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set C := centralizer (oddCore H : Set H) with hCdef
  set Y := E.comap π with hY
  have hOY : oddCore H ≤ Y := fun x hx => by
    rw [hY, mem_comap, show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem E
  have hAY : Y ⊓ C ≤ Y := inf_le_left
  have hAn : ((Y ⊓ C).subgroupOf Y).Normal := ⟨fun m hm y => by
    rw [mem_subgroupOf] at hm ⊢
    exact ⟨Y.mul_mem (Y.mul_mem y.2 hm.1) (Y.inv_mem y.2),
      (inferInstance : C.Normal).conj_mem _ hm.2 y⟩⟩
  have hYeq : Y = (Y ⊓ C) ⊔ oddCore H := by
    refine le_antisymm (fun y hy => ?_) (sup_le hAY hOY)
    obtain ⟨c, hc, hcy⟩ := hE hy
    have hcY : c ∈ Y := by
      rw [hY, mem_comap, hcy]
      exact hy
    have hn : c⁻¹ * y ∈ oddCore H := by
      rw [← QuotientGroup.ker_mk' (oddCore H), MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hcy,
        inv_mul_cancel]
    have := mul_mem (mem_sup_left ⟨hcY, hc⟩ : c ∈ (Y ⊓ C) ⊔ oddCore H)
      (mem_sup_right hn : c⁻¹ * y ∈ (Y ⊓ C) ⊔ oddCore H)
    rwa [mul_inv_cancel_left] at this
  have hsolv : Group.IsSolvable (oddCore H) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  exact (CFSG.Quasithin.perfectCore_le_of_sup_solvable hAY hAn hYeq hsolv).trans inf_le_right

theorem le_map_centralizer_of_isComponent {D : Subgroup H}
    (hDO : D ≤ centralizer (oddCore H : Set H)) {Kb : Subgroup (H ⧸ oddCore H)}
    (hK : CFSG.IsComponent Kb) (hKD : ⁅Kb, D.map (QuotientGroup.mk' (oddCore H))⁆ ≠ ⊥) :
    Kb ≤ (centralizer (oddCore H : Set H)).map (QuotientGroup.mk' (oddCore H)) := by
  have hN : ((centralizer (oddCore H : Set H)).map (QuotientGroup.mk' (oddCore H))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.component_normal_subgroup hK hN with h | h
  · exact h
  · exact absurd (le_bot_iff.1 (h ▸ commutator_mono le_rfl (map_mono hDO))) hKD

theorem hasBLift_of_isComponent_of_le_centralizer {D : Subgroup H}
    (hDO : D ≤ centralizer (oddCore H : Set H)) {K₁ K₂ : Subgroup (H ⧸ oddCore H)}
    (hK₁ : CFSG.IsComponent K₁) (hK₂ : CFSG.IsComponent K₂)
    (hK₁D : ⁅K₁, D.map (QuotientGroup.mk' (oddCore H))⁆ ≠ ⊥)
    (hK₂D : ⁅K₂, D.map (QuotientGroup.mk' (oddCore H))⁆ ≠ ⊥) :
    HasBLift K₁ ∧ HasBLift (K₁ ⊔ K₂) :=
  ⟨hasBLift_of_le_map_centralizer (le_map_centralizer_of_isComponent hDO hK₁ hK₁D),
    hasBLift_of_le_map_centralizer (sup_le (le_map_centralizer_of_isComponent hDO hK₁ hK₁D)
      (le_map_centralizer_of_isComponent hDO hK₂ hK₂D))⟩

end Lift

end CFSG.SeitzReduction.LinearPilot
