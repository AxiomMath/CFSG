module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Klein7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Perm3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Common
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltFix

public section

open Equiv CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD1426Klein CFSG.LocalAnalysis.GLTheoremA.KD264Orbit
open CFSG.LocalAnalysis.GLTheoremA.KD264Rank

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenKlein

theorem card_le_nine_of_2520 {G : Type} [Group G] [Finite G] (hG : Nat.card G = 2520)
    {H : Subgroup G} (hH : ∀ g ∈ H, g ^ 3 = 1) : Nat.card H ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 H := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hH g.1 g.2⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
  have hdvd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  rw [hm, hG] at hdvd
  have hm2 : m ≤ 2 := by
    by_contra h
    push Not at h
    have h27 : 3 ^ 3 ∣ 3 ^ m := pow_dvd_pow 3 h
    have := dvd_trans h27 hdvd
    norm_num at this
  rw [hm]
  calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 9 := by norm_num

theorem isElemAbelian_subgroupOf {G : Type} [Group G] {p : ℕ} {F H : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian p H) : CFSG.Open.IsElemAbelian p (H.subgroupOf F) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have h := hH.1.is_comm.comm (⟨(x : G), Subgroup.mem_subgroupOf.1 x.2⟩ : ↥H)
      ⟨(y : G), Subgroup.mem_subgroupOf.1 y.2⟩
    simpa using congrArg Subtype.val h
  · apply Subtype.ext
    have := hH.2 (x : G) (Subgroup.mem_subgroupOf.1 hx)
    simpa using this

theorem decomp_P {σ : ↥(alternatingGroup (Fin 10))} (h3 : σ ^ 3 = 1)
    (hc : ((σ : ↥(alternatingGroup (Fin 10))) : Equiv.Perm (Fin 10)).support.card = 3)
    {P : Subgroup ↥(alternatingGroup (Fin 10))} (hP : CFSG.Open.IsElemAbelian 3 P) (hσP : σ ∈ P)
    (x : ↥(alternatingGroup (Fin 10))) (hx : x ∈ P) :
    ∃ i : ℕ, i < 3 ∧ (σ ^ i)⁻¹ * x ∈ P ⊓ altFix (σ : Equiv.Perm (Fin 10)) := by
  have hcomm : (x : Equiv.Perm (Fin 10)) * (σ : Equiv.Perm (Fin 10)) =
      (σ : Equiv.Perm (Fin 10)) * (x : Equiv.Perm (Fin 10)) := by
    have h := hP.1.is_comm.comm (⟨x, hx⟩ : ↥P) ⟨σ, hσP⟩
    exact congrArg (fun g : ↥P => ((g : ↥(alternatingGroup (Fin 10))) : Equiv.Perm (Fin 10))) h
  have h3' : (σ : Equiv.Perm (Fin 10)) ^ 3 = 1 := by
    have := congrArg (fun g : ↥(alternatingGroup (Fin 10)) => (g : Equiv.Perm (Fin 10))) h3
    simpa using this
  obtain ⟨i, hi3, hpow⟩ := KD1426Perm3.centralizer_eq_pow_on_support h3' hc hcomm
  refine ⟨i, hi3, Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem (P.pow_mem hσP i)) hx, ?_⟩⟩
  rw [mem_altFix_iff]
  intro u hu
  have h1 := hpow u hu
  have h2 : ((((σ ^ i)⁻¹ * x : ↥(alternatingGroup (Fin 10))) : ↥(alternatingGroup (Fin 10))) :
      Equiv.Perm (Fin 10)) = ((σ : Equiv.Perm (Fin 10)) ^ i)⁻¹ * (x : Equiv.Perm (Fin 10)) := by
    simp
  rw [h2, Perm.mul_apply, h1, Equiv.Perm.inv_eq_iff_eq]

theorem altFix_comm_pow {σ : ↥(alternatingGroup (Fin 10))}
    (hc : ((σ : ↥(alternatingGroup (Fin 10))) : Equiv.Perm (Fin 10)).support.card = 3)
    {u : ↥(alternatingGroup (Fin 10))} (hu : u ∈ altFix (σ : Equiv.Perm (Fin 10))) (j : ℕ) :
    σ ^ j * u = u * σ ^ j := by
  have hle : altFix (σ : Equiv.Perm (Fin 10)) ≤
      Subgroup.centralizer (((Subgroup.zpowers σ : Subgroup ↥(alternatingGroup (Fin 10))) :
        Set ↥(alternatingGroup (Fin 10)))) := by
    apply altFix_le_centralizer
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [Subgroup.coe_zpow]
    exact Equiv.Perm.support_zpow_le _ _
  have hm := Subgroup.mem_centralizer_iff.1 (hle hu) (σ ^ j) (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) j)
  exact hm

theorem klein_on_P {σ : ↥(alternatingGroup (Fin 10))} (h3 : σ ^ 3 = 1)
    (hc : ((σ : ↥(alternatingGroup (Fin 10))) : Equiv.Perm (Fin 10)).support.card = 3)
    {P : Subgroup ↥(alternatingGroup (Fin 10))} (hP : CFSG.Open.IsElemAbelian 3 P) (hσP : σ ∈ P)
    (hPc : Nat.card P = 27) :
    ∃ TA : Subgroup ↥(alternatingGroup (Fin 10)), Nat.card TA = 4 ∧
      CFSG.Open.IsElemAbelian 2 TA ∧
      (∀ t ∈ TA, t ∈ altFix (σ : Equiv.Perm (Fin 10))) ∧
      (∀ x ∈ P, ∀ t ∈ TA, x * t * x⁻¹ ∈ TA) ∧
      (∀ t ∈ TA, ∃ d ∈ P, ∃ s ∈ TA, d * s * d⁻¹ * s⁻¹ = t) := by
  classical
  set F : Subgroup ↥(alternatingGroup (Fin 10)) := altFix (σ : Equiv.Perm (Fin 10)) with hF
  set D : Subgroup ↥(alternatingGroup (Fin 10)) := P ⊓ F with hD
  obtain ⟨R⟩ : Nonempty (↥F ≃* ↥(alternatingGroup (Fin 7))) := by
    have hm : 10 - (σ : Equiv.Perm (Fin 10)).support.card = 7 := by rw [hc]
    exact nonempty_altFix_equiv (σ : Equiv.Perm (Fin 10)) hm
  have hFcard : Nat.card ↥F = 2520 := by
    rw [Nat.card_congr R.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hDel : CFSG.Open.IsElemAbelian 3 D := KD1426Common.isElemAbelian_of_le inf_le_left hP
  have hDF_map : (D.subgroupOf F).map F.subtype = D := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 inf_le_right
  have hDFcard : Nat.card (D.subgroupOf F) = Nat.card D := by
    rw [← Subgroup.card_map_of_injective F.subtype_injective, hDF_map]
  have hDle9 : Nat.card D ≤ 9 := by
    rw [← hDFcard]
    apply card_le_nine_of_2520 hFcard
    intro g hg
    apply Subtype.ext
    simpa using hP.2 (g : ↥(alternatingGroup (Fin 10)))
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1
  have hPle : Nat.card P ≤ 3 * Nat.card D := by
    let Φ : Fin 3 × ↥D → ↥P := fun q => ⟨σ ^ (q.1 : ℕ) * (q.2 : ↥(alternatingGroup (Fin 10))),
      P.mul_mem (P.pow_mem hσP _) (Subgroup.mem_inf.1 q.2.2).1⟩
    have hsurj : Function.Surjective Φ := by
      intro x
      obtain ⟨i, hi3, hmem⟩ := decomp_P h3 hc hP hσP x.1 x.2
      refine ⟨(⟨i, hi3⟩, ⟨(σ ^ i)⁻¹ * x.1, hmem⟩), ?_⟩
      apply Subtype.ext
      simp [Φ]
    have := Nat.card_le_card_of_surjective Φ hsurj
    simpa [Nat.card_prod, Nat.card_fin, mul_comm] using this
  have hDcard : Nat.card D = 9 := by
    rw [hPc] at hPle
    omega
  set DA : Subgroup ↥(alternatingGroup (Fin 7)) := (D.subgroupOf F).map R.toMonoidHom with hDA
  have hDAel : CFSG.Open.IsElemAbelian 3 DA :=
    isElemAbelian_map R.injective (isElemAbelian_subgroupOf hDel)
  have hDAcard : Nat.card DA = 9 := by
    rw [hDA, Subgroup.card_map_of_injective R.injective, hDFcard, hDcard]
  obtain ⟨T7, hT7el, hT7card, hT7norm, hT7cov⟩ := KD1426Klein.klein7 DA hDAel hDAcard
  set ψ0 : ↥(alternatingGroup (Fin 7)) →* ↥(alternatingGroup (Fin 10)) :=
    F.subtype.comp R.symm.toMonoidHom with hψ0
  have hψ0inj : Function.Injective ψ0 := F.subtype_injective.comp R.symm.injective
  have hψ0R : ∀ d : ↥F, ψ0 (R d) = (d : ↥(alternatingGroup (Fin 10))) := by
    intro d
    simp [hψ0]
  refine ⟨T7.map ψ0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hψ0inj, hT7card]
  · exact isElemAbelian_map hψ0inj hT7el
  · intro t ht
    obtain ⟨s, _, rfl⟩ := Subgroup.mem_map.1 ht
    have := (R.symm s).2
    simpa [hψ0] using this
  ·
    intro x hx t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨i, hi3, hdD⟩ := decomp_P h3 hc hP hσP x hx
    set d : ↥(alternatingGroup (Fin 10)) := (σ ^ i)⁻¹ * x with hd_def
    have hxd : x = σ ^ i * d := by
      rw [hd_def]
      group
    have hdF : d ∈ F := (Subgroup.mem_inf.1 hdD).2
    have hdDF : (⟨d, hdF⟩ : ↥F) ∈ D.subgroupOf F := Subgroup.mem_subgroupOf.2 hdD
    have hRd : R ⟨d, hdF⟩ ∈ DA := Subgroup.mem_map.2 ⟨_, hdDF, rfl⟩
    have hsN := hT7norm (R ⟨d, hdF⟩) hRd s hs
    have hu : d * ψ0 s * d⁻¹ ∈ T7.map ψ0 :=
      by
        have h1 : ψ0 (R ⟨d, hdF⟩ * s * (R ⟨d, hdF⟩)⁻¹) = d * ψ0 s * d⁻¹ := by
          rw [map_mul, map_mul, map_inv, hψ0R]
        rw [← h1]
        exact Subgroup.mem_map.2 ⟨_, hsN, rfl⟩
    have hψF : ψ0 s ∈ F := (R.symm s).2
    have hu_F : d * ψ0 s * d⁻¹ ∈ F := F.mul_mem (F.mul_mem hdF hψF) (F.inv_mem hdF)
    have hc2 := altFix_comm_pow hc hu_F i
    have key : x * ψ0 s * x⁻¹ = d * ψ0 s * d⁻¹ := by
      rw [hxd]
      calc σ ^ i * d * ψ0 s * (σ ^ i * d)⁻¹ = σ ^ i * (d * ψ0 s * d⁻¹) * (σ ^ i)⁻¹ := by group
        _ = (d * ψ0 s * d⁻¹) * σ ^ i * (σ ^ i)⁻¹ := by rw [hc2]
        _ = d * ψ0 s * d⁻¹ := by group
    rw [key]
    exact hu
  ·
    intro t ht
    obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨dA, hdA, s, hs, hcomm⟩ := hT7cov s0 hs0
    obtain ⟨dF, hdF, rfl⟩ := Subgroup.mem_map.1 hdA
    refine ⟨(dF : ↥(alternatingGroup (Fin 10))), ?_, ψ0 s, Subgroup.mem_map.2 ⟨s, hs, rfl⟩, ?_⟩
    · exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hdF)).1
    · rw [← hcomm]
      simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, hψ0R]

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenKlein

end
