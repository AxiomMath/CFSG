module

public import CFSG.CGT.Foote82.T66.CaseIT
import CFSG.LargeExtraspecial.S5Comp
public import CFSG.CGT.Foote82.T66.CaseIClimb
public import CFSG.CGT.Foote82.T66.CaseIEnd
public import CFSG.CGT.Foote82.T66.Overgroup

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart CaseIClimbAux

theorem false_of_sup_odd {E : Type*} [Group E] [Finite E] {P J A : Subgroup E} [J.Normal]
    [A.Normal] (hJA : J ⊔ A = ⊤) (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    (hPJ : P ⊓ J = ⊥) (hPA : P ⊓ A = ⊥) (hP1 : P ≠ ⊥) : False := by
  have key : ∀ K : Subgroup E, K.Normal → P ⊓ K = ⊥ → Odd (Nat.card K) := by
    intro K hK hPK
    have h1 : K.relIndex (P ⊔ K) = K.relIndex P := Subgroup.relIndex_sup_right P K
    have h2 := Subgroup.relIndex_mul_card K P
    rw [inf_comm, hPK, Subgroup.card_bot, mul_one] at h2
    have h3 := Subgroup.relIndex_mul_card K (P ⊔ K)
    rw [inf_eq_left.2 le_sup_right, h1, h2] at h3
    have h4 : Nat.card ↥(P ⊔ K) ∣ Nat.card E := Subgroup.card_subgroup_dvd_card _
    rw [← h3, ← Subgroup.card_mul_index P] at h4
    have h5 : Nat.card K ∣ P.index :=
      Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h4
    exact Odd.of_dvd_nat (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hPidx)) h5
  have hJ := key J ‹_› hPJ
  have hA := key A ‹_› hPA
  have hE : Odd (Nat.card E) := by
    have h1 := Subgroup.relIndex_mul_card A (J ⊔ A)
    rw [inf_eq_left.2 le_sup_right, Subgroup.relIndex_sup_right, hJA, Subgroup.card_top] at h1
    have h2 := Subgroup.relIndex_mul_card A J
    have h3 : A.relIndex J ∣ Nat.card J := ⟨_, h2.symm⟩
    rw [← h1]
    exact (Odd.of_dvd_nat hJ h3).mul hA
  have hP : 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP2
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hP1 hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  exact (Nat.not_even_iff_odd.2 hE) (even_iff_two_dvd.2 (hP.trans (Subgroup.card_subgroup_dvd_card P)))

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem Hyp.relIndex_layerIn (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) : (layerIn G).relIndex G = 2 := by
  have hE : (layerIn G).subgroupOf G = CFSG.layer ↥G := layerIn_subgroupOf G
  haveI : ((layerIn G).subgroupOf G).Normal := by
    rw [hE]
    have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hzG : Subgroup.zpowers z ≤ G := Subgroup.zpowers_le.2 h.z_mem_G
  have hsup : (Subgroup.zpowers z).subgroupOf G ⊔ (layerIn G).subgroupOf G = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hzG (layerIn_le G), sup_comm, ← h.std.eq_layerIn_sup]
    exact Subgroup.subgroupOf_self G
  have h1 : (layerIn G).relIndex G = ((layerIn G).subgroupOf G).relIndex
      ((Subgroup.zpowers z).subgroupOf G) := by
    rw [← Subgroup.relIndex_sup_right ((Subgroup.zpowers z).subgroupOf G)
      ((layerIn G).subgroupOf G), hsup, Subgroup.relIndex_top_right]
    rfl
  have h2 := Subgroup.relIndex_mul_card ((layerIn G).subgroupOf G)
    ((Subgroup.zpowers z).subgroupOf G)
  have hcard : Nat.card ↥((Subgroup.zpowers z).subgroupOf G) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzG).toEquiv, Nat.card_zpowers,
      h.std.orderOf_s]
  rw [hcard] at h2
  have hle : (layerIn G).relIndex G ≤ 2 := by
    rw [h1]
    exact Nat.le_of_dvd (by norm_num) ⟨_, h2.symm⟩
  have hne : (layerIn G).relIndex G ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle'
    exact h.z_not_mem_layerIn hK2 h25 (hle' h.z_mem_G)
  have hpos : (layerIn G).relIndex G ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  omega

theorem Hyp.card_G_eq (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) : Nat.card G = 2 * Nat.card (layerIn G) := by
  have := Subgroup.relIndex_mul_card (layerIn G) G
  rw [h.relIndex_layerIn hK2 h25, inf_eq_left.2 (layerIn_le G)] at this
  exact this.symm

noncomputable abbrev PP (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2)))
    (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) : Subgroup (GLV V) :=
  (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).map (pe ψ)

theorem Hyp.PP_le_H (h : Hyp G L z v H₁ m ψ) (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) :
    PP ψ T₀ ≤ HH G L v := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact (h.mem_H_iff σ).2 hσ.2

theorem Hyp.P_relIndex (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) (T₀ : Sylow 2 (Perm (Fin (m + 6 + 2))))
    (hzT : swap 0 1 ∈ T₀) :
    (PP ψ (T₀ : Subgroup (Perm (Fin (m + 6 + 2))))).relIndex (layerIn G) =
      ((T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ)).relIndex G := by
  set T := (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) with hT
  set P := PP ψ (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) with hP
  have hPT : P ≤ T := Subgroup.map_mono inf_le_left
  have hPE : P ≤ layerIn G := (h.PP_le_H _).trans h.H_le_layerIn
  have e1 := Subgroup.relIndex_mul_card P T
  rw [inf_eq_left.2 hPT, relIndex_alt _ hzT] at e1
  have e2 := Subgroup.relIndex_mul_card P (layerIn G)
  rw [inf_eq_left.2 hPE] at e2
  have e3 := Subgroup.relIndex_mul_card T G
  rw [inf_eq_left.2 (h.T_le_G _)] at e3
  have e4 := h.card_G_eq hK2 h25
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have : (2 * Nat.card P) * P.relIndex (layerIn G) = (2 * Nat.card P) * T.relIndex G := by
    calc (2 * Nat.card P) * P.relIndex (layerIn G) = 2 * (P.relIndex (layerIn G) * Nat.card P) :=
          by ring
      _ = 2 * Nat.card (layerIn G) := by rw [e2]
      _ = Nat.card G := e4.symm
      _ = T.relIndex G * Nat.card T := e3.symm
      _ = (2 * Nat.card P) * T.relIndex G := by rw [← e1]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem Hyp.P_not_dvd (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) (T₀ : Sylow 2 (Perm (Fin (m + 6 + 2))))
    (hzT : swap 0 1 ∈ T₀) (hyT : swap 2 3 ∈ T₀) :
    ¬ 2 ∣ (PP ψ (T₀ : Subgroup (Perm (Fin (m + 6 + 2))))).relIndex (layerIn G) := by
  rw [h.P_relIndex hK2 h25 T₀ hzT]
  exact h.T_not_dvd hK2 h25 T₀ hzT hyT

theorem Hyp.center_H_eq_bot (h : Hyp G L z v H₁ m ψ) :
    Subgroup.center ↥(HH G L v) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxH : (x : GLV V) ∈ (alternatingGroup (Fin (m + 6 + 2))).map (pe ψ) := by
    rw [← h.H_eq]; exact x.2
  obtain ⟨σ, hσ, hσx⟩ := hxH
  have hc : ∀ a ∈ alternatingGroup (Fin (m + 6 + 2)), σ * a = a * σ := by
    intro a ha
    have h1 := Subgroup.mem_center_iff.1 hx ⟨pe ψ a, (h.mem_H_iff a).2 ha⟩
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    rw [← hσx, ← map_mul, ← map_mul] at h2
    exact (pe_injective h2).symm
  have h1 := CaseIAut.eq_one_of_commute_alternatingGroup (by omega) hc
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hσx, h1, map_one]
  rfl

theorem Hyp.H_le_or_inf_eq_bot (h : Hyp G L z v H₁ m ψ) {K : Subgroup (GLV V)}
    (hK : ∀ x ∈ HH G L v, ∀ y ∈ K, x * y * x⁻¹ ∈ K) :
    HH G L v ≤ K ∨ HH G L v ⊓ K = ⊥ := by
  have hn : (K.subgroupOf (HH G L v)).Normal :=
    ⟨fun y hy x => Subgroup.mem_subgroupOf.2 (hK x x.2 y (Subgroup.mem_subgroupOf.1 hy))⟩
  rcases normal_eq_top_or_le_center' h.H_isComponentOf.2.2 hn with h1 | h1
  · left
    intro x hx
    have : (⟨x, hx⟩ : ↥(HH G L v)) ∈ K.subgroupOf (HH G L v) := by rw [h1]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  · right
    rw [h.center_H_eq_bot] at h1
    rw [eq_bot_iff]
    rintro x ⟨hxH, hxK⟩
    have := h1 (Subgroup.mem_subgroupOf.2 hxK : (⟨x, hxH⟩ : ↥(HH G L v)) ∈ K.subgroupOf _)
    rw [Subgroup.mem_bot] at this ⊢
    exact congrArg Subtype.val this

theorem Hyp.exists_component_eq (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) : ∃ J : Subgroup (GLV V), IsComponentOf J G ∧ layerIn G = J := by
  have hext := h.std.extremal
  obtain ⟨T₀, hzT, hyT⟩ := exists_sylow_T₀ (m := m)
  set P := PP ψ (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) with hP
  have hPH : P ≤ HH G L v := h.PP_le_H _
  have hHE : HH G L v ≤ layerIn G := h.H_le_layerIn
  have hPE : P ≤ layerIn G := hPH.trans hHE
  obtain ⟨J, hJ, hJH⟩ : ∃ J : Subgroup (GLV V), IsComponentOf J G ∧
      ¬ HH G L v ≤ Subgroup.centralizer (J : Set (GLV V)) := by
    by_contra hc
    push Not at hc
    have hle : layerIn G ≤ Subgroup.centralizer (HH G L v : Set (GLV V)) := by
      rw [layerIn_eq_sSup]
      exact sSup_le fun J hJ => Subgroup.le_centralizer_iff.1 (hc J hJ)
    obtain ⟨hperf, hne⟩ := perfect_ne_bot_of_isQuasisimple h.H_isComponentOf.2.2
    apply hne
    have hcomm : ⁅HH G L v, HH G L v⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hHE.trans hle)
    rw [← hperf, hcomm]
  have hJE : J ≤ layerIn G := le_layerIn_of_isComponentOf hJ
  have hother : ∀ J' : Subgroup (GLV V), IsComponentOf J' G → J' ≠ J →
      J' ≤ Subgroup.centralizer (J : Set (GLV V)) := by
    intro J' hJ' hne
    have hc := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hJ' hJ hne
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
  have hEnorm : layerIn G ≤ Subgroup.normalizer (J : Set (GLV V)) := by
    rw [layerIn_eq_sSup]
    refine sSup_le fun J' hJ' => ?_
    by_cases hne : J' = J
    · rw [hne]; exact Subgroup.le_normalizer
    · exact (hother J' hJ' hne).trans (Subgroup.centralizer_le_normalizer _)
  set A : Subgroup (GLV V) := layerIn G ⊓ Subgroup.centralizer (J : Set (GLV V)) with hA
  have hAE : A ≤ layerIn G := inf_le_left
  have hEJA : layerIn G ≤ J ⊔ A := by
    conv_lhs => rw [layerIn_eq_sSup]
    refine sSup_le fun J' hJ' => ?_
    by_cases hne : J' = J
    · rw [hne]; exact le_sup_left
    · exact le_sup_of_le_right (le_inf (le_layerIn_of_isComponentOf hJ') (hother J' hJ' hne))
  have hJconj : ∀ x ∈ layerIn G, ∀ y ∈ J, x * y * x⁻¹ ∈ J := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hEnorm hx) y).1 hy
  have hAconj : ∀ x ∈ layerIn G, ∀ y ∈ A, x * y * x⁻¹ ∈ A := by
    intro x hx y hy
    refine ⟨(layerIn G).mul_mem ((layerIn G).mul_mem hx hy.1) ((layerIn G).inv_mem hx),
      Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
    have hj' : x⁻¹ * j * x ∈ J := by
      have := hJconj x⁻¹ ((layerIn G).inv_mem hx) j hj
      rwa [inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.1 hy.2 _ hj'
    calc j * (x * y * x⁻¹) = x * ((x⁻¹ * j * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * j * x)) * x⁻¹ := by rw [hc]
      _ = x * y * x⁻¹ * j := by group
  have hHJ : HH G L v ≤ J := by
    rcases h.H_le_or_inf_eq_bot (fun x hx y hy => hJconj x (hHE hx) y hy) with h1 | hHJ
    · exact h1
    exfalso
    rcases h.H_le_or_inf_eq_bot (fun x hx y hy => hAconj x (hHE hx) y hy) with h2 | hHA
    · exact hJH (h2.trans inf_le_right)
    set E := layerIn G with hEdef
    haveI hJn : (J.subgroupOf E).Normal :=
      ⟨fun y hy x => Subgroup.mem_subgroupOf.2 (hJconj x x.2 y (Subgroup.mem_subgroupOf.1 hy))⟩
    haveI hAn : (A.subgroupOf E).Normal :=
      ⟨fun y hy x => Subgroup.mem_subgroupOf.2 (hAconj x x.2 y (Subgroup.mem_subgroupOf.1 hy))⟩
    have hsup : J.subgroupOf E ⊔ A.subgroupOf E = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hJE hAE, Subgroup.subgroupOf_eq_top]
      exact hEJA
    have hP2 : IsPGroup 2 (P.subgroupOf E) :=
      ((T₀.isPGroup'.to_inf_left).map _).comap_subtype
    have hPidx : ¬ 2 ∣ (P.subgroupOf E).index := h.P_not_dvd hK2 h25 T₀ hzT hyT
    have hPJ : P.subgroupOf E ⊓ J.subgroupOf E = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxP, hxJ⟩
      have h1 : (x : GLV V) ∈ HH G L v ⊓ J := ⟨hPH (Subgroup.mem_subgroupOf.1 hxP),
        Subgroup.mem_subgroupOf.1 hxJ⟩
      rw [hHJ, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.2 (Subtype.ext h1)
    have hPA : P.subgroupOf E ⊓ A.subgroupOf E = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxP, hxA⟩
      have h1 : (x : GLV V) ∈ HH G L v ⊓ A := ⟨hPH (Subgroup.mem_subgroupOf.1 hxP),
        Subgroup.mem_subgroupOf.1 hxA⟩
      rw [hHA, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.2 (Subtype.ext h1)
    have hP1 : P.subgroupOf E ≠ ⊥ := by
      have hdt : swap (0 : Fin (m + 6 + 2)) 1 * swap 2 3 ∈
          (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) ⊓ alternatingGroup (Fin (m + 6 + 2)) :=
        Subgroup.mem_inf.2 ⟨T₀.mul_mem hzT hyT, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_swap ne01, sign_swap ne23]; rfl⟩
      have hmem : pe ψ (swap 0 1 * swap 2 3) ∈ P := ⟨_, hdt, rfl⟩
      intro hbot
      have h1 : (⟨_, hPE hmem⟩ : ↥E) ∈ P.subgroupOf E := Subgroup.mem_subgroupOf.2 hmem
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : pe ψ (swap 0 1 * swap 2 3) = 1 := congrArg Subtype.val h1
      have h3 := pe_injective (h2.trans (map_one _).symm)
      have h4 := congrArg (fun π : Perm (Fin (m + 6 + 2)) => π 0) h3
      simp only [Perm.mul_apply, Perm.one_apply] at h4
      rw [swap_apply_of_ne_of_ne ne02 ne03, swap_apply_left] at h4
      exact ne01 h4.symm
    exact false_of_sup_odd hsup hP2 hPidx hPJ hPA hP1
  refine ⟨J, hJ, le_antisymm ?_ hJE⟩
  calc layerIn G = normalClosure (layerIn G) L := hext.setup.normalClosure_layerIn.symm
    _ ≤ J := by
      rw [normalClosure, Subgroup.closure_le]
      rintro _ ⟨e, he, l, hl, rfl⟩
      exact hJconj e he l (hHJ (h.L_le_H hl))

theorem Hyp.mul_self_mem_layerIn (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) {x : GLV V} (hx : x ∈ G) : x * x ∈ layerIn G := by
  have hE : (layerIn G).subgroupOf G = CFSG.layer ↥G := layerIn_subgroupOf G
  haveI : ((layerIn G).subgroupOf G).Normal := by
    rw [hE]
    have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hcard : Nat.card (↥G ⧸ (layerIn G).subgroupOf G) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact h.relIndex_layerIn hK2 h25
  have h1 := pow_card_eq_one' (G := ↥G ⧸ (layerIn G).subgroupOf G)
    (x := ((⟨x, hx⟩ : ↥G) : ↥G ⧸ (layerIn G).subgroupOf G))
  rw [hcard, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa [sq] using h1

theorem Hyp.centralizer_layerIn_le (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) :
    G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)) ≤
      (Subgroup.center ↥(layerIn G)).map (layerIn G).subtype := by
  have hext := h.std.extremal
  intro x hx
  have hodd : Odd (orderOf x) := by
    have := Subgroup.orderOf_dvd_natCard _ hx
    exact Odd.of_dvd_nat hext.setup.odd_card_centralizer_layerIn this
  have hxE : x ∈ layerIn G := by
    obtain ⟨k, hk⟩ := hodd
    have e : x = (x * x) ^ (k + 1) := by
      calc x = x * x ^ orderOf x := by rw [pow_orderOf_eq_one, mul_one]
        _ = x ^ (2 * k + 2) := by rw [hk, ← pow_succ']
        _ = (x * x) ^ (k + 1) := by rw [← sq, ← pow_mul]; ring_nf
    rw [e]
    exact (layerIn G).pow_mem (h.mul_self_mem_layerIn hK2 h25 hx.1) _
  refine ⟨⟨x, hxE⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
  exact (Subgroup.mem_centralizer_iff.1 hx.2 g g.2)

theorem Hyp.odd_card_center_layerIn (h : Hyp G L z v H₁ m ψ) :
    Odd (Nat.card ↥(Subgroup.center ↥(layerIn G))) := by
  have hext := h.std.extremal
  have hle : (Subgroup.center ↥(layerIn G)).map (layerIn G).subtype ≤
      G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)) := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨layerIn_le G c.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨g, hg⟩))
  have h1 := Odd.of_dvd_nat hext.setup.odd_card_centralizer_layerIn (Subgroup.card_dvd_of_le hle)
  rwa [Subgroup.card_map_of_injective (layerIn G).subtype_injective] at h1

noncomputable def eL (h : Hyp G L z v H₁ m ψ) : ↥L ≃* alternatingGroup (Fin (m + 6)) :=
  ((MonoidHom.ofInjective (jL_injective (ψ := ψ))).trans (MulEquiv.subgroupCongr h.range_jL)).symm

theorem Hyp.jL_eL (h : Hyp G L z v H₁ m ψ) (c : ↥L) : jL ψ (eL h c) = c := by
  have := MulEquiv.apply_symm_apply
    ((MonoidHom.ofInjective (jL_injective (ψ := ψ))).trans (MulEquiv.subgroupCongr h.range_jL)) c
  have h2 := congrArg Subtype.val this
  exact h2

theorem Hyp.finrank_eq_two (h : Hyp G L z v H₁ m ψ) (c : ↥L)
    (hc : ((eL h c : alternatingGroup (Fin (m + 6))) : Perm (Fin (m + 6))).IsThreeCycle) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (c : GLV V)) ⊤) = 2 := by
  set a := eL h c with ha
  have hca : (c : GLV V) = jL ψ a := (h.jL_eL c).symm
  rw [hca]
  refine le_antisymm (h.finrank_jL_le_two hc) ?_
  obtain ⟨β, hβ⟩ := h.heartFor
  have hι : (iota2 (m + 6) (a : Perm (Fin (m + 6)))).IsThreeCycle := by
    rw [← card_support_eq_three_iff, ← Equiv.Perm.sum_cycleType, cycleType_iota2,
      Equiv.Perm.sum_cycleType, card_support_eq_three_iff]
    exact hc
  have e : ψ.toMonoidHom ⟨jL ψ a, pe_mem _⟩ = iota2 (m + 6) (a : Perm (Fin (m + 6))) := psi_jL a
  obtain ⟨p, hp⟩ : ∃ p, iota2 (m + 6) (a : Perm (Fin (m + 6))) p ≠ p := by
    by_contra hcon
    push Not at hcon
    have h1 : iota2 (m + 6) (a : Perm (Fin (m + 6))) = 1 := Perm.ext hcon
    rw [h1] at hι
    have := hι.orderOf
    rw [orderOf_one] at this
    exact absurd this (by norm_num)
  have h3 : iota2 (m + 6) (a : Perm (Fin (m + 6))) ^ 3 = 1 := by
    rw [← hι.orderOf]; exact pow_orderOf_eq_one _
  exact two_le_finrank hβ (pe_mem _) (h.L_le_H (h.jL_mem a)) (by rw [e]; exact h3)
    (p := p) (by rw [e]; exact hp)

theorem Hyp.isAltNaturalModule_L (h : Hyp G L z v H₁ m ψ) : IsAltNaturalModule L (m + 6) := by
  obtain ⟨ρL, βL, hH, -, honto, -⟩ := h.heartL
  exact hH.isAltNaturalModule fun σ hσ => by
    obtain ⟨l, hl⟩ := honto σ hσ
    exact ⟨l, l.2, hl⟩

theorem relIndex_inf_alt_eq (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) (hzT : swap 0 1 ∈ T₀) :
    (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).relIndex (alternatingGroup (Fin (m + 6 + 2))) =
      T₀.index := by
  have e1 := Subgroup.relIndex_mul_card (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2)))
    (alternatingGroup (Fin (m + 6 + 2)))
  rw [inf_eq_left.2 inf_le_right] at e1
  have e2 : (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).relIndex T₀ = 2 := by
    set f : ↥T₀ →* ℤˣ := Equiv.Perm.sign.comp T₀.subtype with hf
    have hker : f.ker = (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).subgroupOf T₀ := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hf,
        MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Equiv.Perm.mem_alternatingGroup]
      exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
    have hsurj : Function.Surjective f := by
      intro u
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one f⟩
      · exact ⟨⟨swap 0 1, hzT⟩, by simp [hf, sign_swap ne01]⟩
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj,
      Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  have e2' := Subgroup.relIndex_mul_card (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))) T₀
  rw [inf_eq_left.2 inf_le_left, e2] at e2'
  have e3 := Subgroup.card_mul_index T₀
  have e4 : Nat.card (alternatingGroup (Fin (m + 6 + 2))) * 2 = Nat.card (Perm (Fin (m + 6 + 2))) := by
    have := Subgroup.card_mul_index (alternatingGroup (Fin (m + 6 + 2)))
    rwa [alternatingGroup.index_eq_two] at this
  have hpos : 0 < Nat.card ↥(T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))) := Nat.card_pos
  have : (2 * Nat.card ↥(T₀ ⊓ alternatingGroup (Fin (m + 6 + 2)))) *
      (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).relIndex (alternatingGroup (Fin (m + 6 + 2))) =
      (2 * Nat.card ↥(T₀ ⊓ alternatingGroup (Fin (m + 6 + 2)))) * T₀.index := by
    calc _ = 2 * ((T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).relIndex
          (alternatingGroup (Fin (m + 6 + 2))) * Nat.card ↥(T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))))
          := by ring
      _ = Nat.card (Perm (Fin (m + 6 + 2))) := by rw [e1, ← e4]; ring
      _ = Nat.card T₀ * T₀.index := e3.symm
      _ = _ := by rw [← e2']
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

end CaseIAux

end CFSG.CGT.Foote82
