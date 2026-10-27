module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3ULemma
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial (pointRadical eichler_mem_pointRadical eichler_eq_one_iff)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_conj eichler_mul eichler_inv)
open scoped commutatorElement Pointwise

namespace Sec3SHat

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem mem_pointRadical_of_comm (hq : q.polarBilin.Nondegenerate) {a : V} (ha0 : a ≠ 0)
    (ha : q a = 0) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hga : g a = a) (hcomm : ∀ t ∈ pointRadical q a, g * t = t * g) :
    g ∈ pointRadical q a := by
  refine ⟨hg, hga, fun x hx => ?_, fun v => ?_⟩
  · have hE := hcomm _ (eichler_mem_pointRadical ha hx)
    have hconj : g * eichler q a x * g⁻¹ = eichler q a (g x) := by
      rw [eichler_conj hg, hga]
    have hgx : polar q a (g x) = 0 := by
      rw [← hga, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, hx]
    have h1 : eichler q a (g x) = eichler q a x := by
      rw [← hconj, hE, mul_inv_cancel_right]
    have hgxx : polar q a (g x - x) = 0 := by rw [polar_sub_right, hgx, hx, sub_self]
    have hnx : polar q a (-x) = 0 := by rw [polar_neg_right, hx, neg_zero]
    have h2 : eichler q a (g x - x) = 1 := by
      rw [sub_eq_add_neg, ← eichler_mul hgx hnx, ← eichler_inv hx, h1, mul_inv_cancel]
    exact (eichler_eq_one_iff hq ha0 ha hgxx).mp h2
  · rw [polar_sub_right, ← hga, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, hga,
      sub_self]

end Sec3SHat

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem oddCoreIn_le_centralizer_sec3F
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G)) :
    AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G) := by
  set Fs := sec3F (Q₀ ⊔ Q) with hFs
  set C := centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) with hC
  set W₁ := AS76b.oddCoreIn C with hW₁
  have hW₁C : W₁ ≤ C := AS76b.oddCoreIn_le C
  have hW₁N : W₁ ≤ H.xsub.N := hW₁C.trans (centralizer_le_normalizer _)
  have hNW : H.xsub.N ≤ normalizer (W₁ : Set G) := fun n hn =>
    AS76b.normalizer_le_normalizer_oddCoreIn C (AS81.mem_normalizer_centralizer hn)
  have hle : Fs ⊓ W₁ ≤ AS76b.oddCoreIn (Fs ⊓ C) :=
    Sec3SHat.le_oddCoreIn_of_odd (inf_le_inf_left _ hW₁C)
      (fun c hc => mem_normalizer_inf (H.N_le_normalizer_F (centralizer_le_normalizer _ hc.2))
        (hNW (centralizer_le_normalizer _ hc.2)))
      ((AS76b.odd_card_oddCoreIn C).of_dvd_nat (card_dvd_of_le inf_le_right))
  have hFW : ⁅Fs, W₁⁆ ≤ Fs ⊓ W₁ := by
    rw [Subgroup.commutator_le]
    intro f hf w hw
    rw [commutatorElement_def]
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h := (mem_normalizer_iff.mp (H.N_le_normalizer_F (hW₁N hw)) f⁻¹).mp (inv_mem hf)
      rw [show f * w * f⁻¹ * w⁻¹ = f * (w * f⁻¹ * w⁻¹) by group]
      exact mul_mem hf h
    · exact mul_mem ((mem_normalizer_iff.mp (hNW (H.F_le_N hf)) w).mp hw) (inv_mem hw)
  have hRF : ⁅Fs, W₁⁆ ≤ centralizer (Fs : Set G) := (hFW.trans hle).trans hRc
  have h1 : ⁅⁅Fs, W₁⁆, Fs⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hRF
  have h2 : ⁅⁅W₁, Fs⁆, Fs⁆ = ⊥ := by rw [commutator_comm W₁ Fs]; exact h1
  have h3 : ⁅⁅Fs, Fs⁆, W₁⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [F_perfect] at h3
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h3)

theorem exists_mul_of_comm_SHat (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {k : G} (hkN : k ∈ H.xsub.N) (hkZ : k ∈ centralizer (Zs : Set G))
    (hkS : ∀ s ∈ sec3SHat (Q₀ ⊔ Q) Zs, k * s * k⁻¹ * s⁻¹ ∈ Zs) :
    ∃ s ∈ sec3SHat (Q₀ ⊔ Q) Zs,
      ∃ w ∈ AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)), k = s * w := by
  obtain ⟨z₂, hz₂, hz₂z⟩ := H.exists_z₂
  set a := H.xsub.cl z₂ with ha
  set S := sec3SHat (Q₀ ⊔ Q) Zs with hSdef
  set C := centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) with hC
  set W₁ := AS76b.oddCoreIn C with hW₁
  have hSC := CFSG.LieType.BorelTits.pCoreOf_le 2 (sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G))
  have hZQ₁ : Zs ≤ H.xsub.Q₁ := hZQ.trans H.Q_le
  have hcomm : ∀ t ∈ pointRadical H.xsub.q a, H.ρG ⟨k, hkN⟩ * t = t * H.ρG ⟨k, hkN⟩ := by
    intro t ht
    obtain ⟨s, hsS, hst⟩ := H.exists_mem_SHat_of_mem_pointRadical hΩ hQF hRc hZQ hz₂ hz₂z ht
    have hsN : (s : G) ∈ H.xsub.N := H.F_le_N s.2
    have hc := hkS s hsS
    have hcN : k * s * k⁻¹ * s⁻¹ ∈ H.xsub.N :=
      mul_mem (mul_mem (mul_mem hkN hsN) (inv_mem hkN)) (inv_mem hsN)
    have h1 : H.ρG ⟨k * s * k⁻¹ * s⁻¹, hcN⟩ = 1 :=
      (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem (hZQ₁ hc))
    have e : (⟨k * s * k⁻¹ * s⁻¹, hcN⟩ : H.xsub.N) =
        ⟨k, hkN⟩ * ⟨s, hsN⟩ * (⟨k, hkN⟩)⁻¹ * (⟨s, hsN⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have hts : H.ρG ⟨s, hsN⟩ = t := hst
    rw [hts] at h1
    calc H.ρG ⟨k, hkN⟩ * t =
          (H.ρG ⟨k, hkN⟩ * t * (H.ρG ⟨k, hkN⟩)⁻¹ * t⁻¹) * (t * H.ρG ⟨k, hkN⟩) := by group
      _ = t * H.ρG ⟨k, hkN⟩ := by rw [h1, one_mul]
  have hka : H.ρG ⟨k, hkN⟩ a = a := H.ρG_cl_z₂ hZQ hz₂ hkZ
  have hkNa : H.ρG ⟨k, hkN⟩ ∈ pointRadical H.xsub.q a :=
    Sec3SHat.mem_pointRadical_of_comm H.xsub.q_nondegenerate (H.cl_ne_zero hZQ hz₂ hz₂z)
      (H.q_cl_eq_zero hZQ hz₂) (H.xsub.ρ _).2 hka hcomm
  obtain ⟨s₀, hs₀S, hs₀⟩ := H.exists_mem_SHat_of_mem_pointRadical hΩ hQF hRc hZQ hz₂ hz₂z hkNa
  have hs₀N : (s₀ : G) ∈ H.xsub.N := H.F_le_N s₀.2
  have hdN : (s₀ : G)⁻¹ * k ∈ H.xsub.N := mul_mem (inv_mem hs₀N) hkN
  have hρ1 : H.ρG ⟨(s₀ : G)⁻¹ * k, hdN⟩ = 1 := by
    have e : (⟨(s₀ : G)⁻¹ * k, hdN⟩ : H.xsub.N) = (⟨s₀, hs₀N⟩)⁻¹ * ⟨k, hkN⟩ := rfl
    have hs₀' : H.ρG ⟨s₀, hs₀N⟩ = H.ρG ⟨k, hkN⟩ := hs₀
    rw [e, map_mul, map_inv, hs₀', inv_mul_cancel]
  obtain ⟨c, hcQ, hcd⟩ := H.xsub.exists_mem_of_ρ_eq_one ((H.ρG_eq_one_iff _).mp hρ1)
  set d := c⁻¹ * ((s₀ : G)⁻¹ * k) with hd
  have hdZ : d ∈ centralizer (Zs : Set G) := Subgroup.centralizer_le hZQ₁ hcd
  have hs₀Z : (s₀ : G) ∈ centralizer (Zs : Set G) := (hSC hs₀S).2
  have hcZ : c ∈ centralizer (Zs : Set G) := by
    have e : c = ((s₀ : G)⁻¹ * k) * d⁻¹ := by rw [hd]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hs₀Z) hkZ) (inv_mem hdZ)
  have hcS : c ∈ S := H.U_le_SHat hQF (mem_inf.mpr ⟨hcQ, hcZ⟩)
  have hdC : d ∈ C := hcd
  have hQW : Q₀ ⊔ Q ≤ normalizer (W₁ : Set G) := fun q hq =>
    AS76b.normalizer_le_normalizer_oddCoreIn C
      (AS81.mem_normalizer_centralizer (le_normalizer hq))
  have hdmem : d ∈ (((Q₀ ⊔ Q) ⊔ W₁ : Subgroup G) : Set G) :=
    H.le_sup_oddCoreIn_of_le_centralizer le_rfl hdC
  rw [coe_mul_of_left_le_normalizer_right _ _ hQW] at hdmem
  obtain ⟨c', hc'Q, w, hwW, hdcw⟩ := hdmem
  have hc'C : c' ∈ C := by
    have e : c' = d * w⁻¹ := by rw [← hdcw]; group
    rw [e]
    exact mul_mem hdC (inv_mem (AS76b.oddCoreIn_le C hwW))
  have hc'z : c' ∈ zpowers z := by
    rw [← H.center_sup]
    exact ⟨hc'Q, hc'C⟩
  have hc'S : c' ∈ S :=
    H.U_le_SHat hQF (H.Zs_le_U hZQ ((zpowers_le.mpr H.z_mem_Zs) hc'z))
  refine ⟨(s₀ : G) * c * c', mul_mem (mul_mem hs₀S hcS) hc'S, w, hwW, ?_⟩
  have e1 : k = (s₀ : G) * c * d := by rw [hd]; group
  rw [e1, ← hdcw]
  group

end Sec38Hyp

end CFSG.ComponentClassification.AS81
