module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Str
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ker

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.Open

theorem HCtx.exists_equiv_cent {G : Type} [Group G] {E B : Subgroup G} {u : MulAut ↥E}
    {A H : Subgroup (MulAut ↥E)} (S : HCtx E B u A H) :
    Nonempty (↥(centralizer ({(⟨u, S.u_H⟩ : ↥H)} : Set ↥H)) ≃*
      Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) := by
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [S.hE.2]; norm_num)
  have horder : orderOf u = 2 := by
    have hdvd : orderOf u ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact S.u_sq)
    have hne1 : orderOf u ≠ 1 := by
      intro h
      exact S.u_A (by rw [orderOf_eq_one_iff.mp h]; exact A.one_mem)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hcases : ∀ v ∈ zpowers u, v = 1 ∨ v = u := by
    intro v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have h3 : u ^ (i % (orderOf u : ℤ)) = u ^ i := zpow_mod_orderOf u i
    rw [horder] at h3
    push_cast at h3
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · left; rw [← h3, h]; simp
    · right; rw [← h3, h]; simp
  have hAcomm : ∀ a ∈ A, ∀ v ∈ zpowers u, a * v = v * a := by
    intro a ha v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute a u from S.A_comm a ha) i).eq
  have hzpu_comm : ∀ v ∈ zpowers u, v * u = u * v := by
    intro v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (Commute.refl u) i).eq.symm
  have hAdisj : A ⊓ zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hcases x hx.2 with h | h
    · simpa [h]
    · exact absurd (h ▸ hx.1) S.u_A
  have hle : A ⊔ zpowers u ≤ H :=
    sup_le S.A_H (Subgroup.zpowers_le.mpr S.u_H)
  have hsup_le_central :
      A ⊔ zpowers u ≤ Subgroup.centralizer ({u} : Set (MulAut ↥E)) := by
    rw [sup_le_iff]
    refine ⟨?_, ?_⟩
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact S.A_comm a ha
    · intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzpu_comm v hv
  let z0 : ↥H := ⟨u, S.u_H⟩
  let C : Subgroup ↥H := Subgroup.centralizer ({(z0 : ↥H)} : Set ↥H)
  have hCmem : ∀ c : ↥H, c ∈ C ↔ (c : MulAut ↥E) * u = u * (c : MulAut ↥E) := by
    intro c
    change c ∈ Subgroup.centralizer ({(z0 : ↥H)} : Set ↥H) ↔
      (c : MulAut ↥E) * u = u * (c : MulAut ↥E)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg (fun x : ↥H => (x : MulAut ↥E)) h,
      fun h => Subtype.ext (by simpa using h)⟩
  have hC : C = (A ⊔ zpowers u).subgroupOf H := by
    ext c
    rw [Subgroup.mem_subgroupOf, hCmem c]
    exact ⟨fun h => S.cent (c : MulAut ↥E) c.2 h,
      fun h => (Subgroup.mem_centralizer_singleton_iff).mp (hsup_le_central h)⟩
  let fA : ↥A →* ↥(A ⊔ zpowers u) := Subgroup.inclusion le_sup_left
  let fU : ↥(zpowers u) →* ↥(A ⊔ zpowers u) := Subgroup.inclusion le_sup_right
  have hcommA : ∀ x : ↥A, ∀ y : ↥(zpowers u), Commute (fA x) (fU y) := by
    intro x y
    rw [commute_iff_eq]
    apply Subtype.ext
    exact hAcomm x x.2 y y.2
  let ψ : ↥A × ↥(zpowers u) →* ↥(A ⊔ zpowers u) :=
    MonoidHom.noncommCoprod fA fU hcommA
  have hdisj : Disjoint fA.range fU.range := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨hxA, hxU⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hxA
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hxU
    have hcoe : (v : MulAut ↥E) = (a : MulAut ↥E) := congrArg Subtype.val hv
    have habot : (a : MulAut ↥E) ∈ (⊥ : Subgroup (MulAut ↥E)) := by
      rw [← hAdisj]
      exact ⟨a.2, hcoe ▸ v.2⟩
    have ha1 : a = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp habot
    rw [ha1, map_one]
    exact Subgroup.mem_bot.mpr rfl
  have hψinj : Function.Injective ψ :=
    (MonoidHom.noncommCoprod_injective fA fU hcommA).mpr
      ⟨Subgroup.inclusion_injective le_sup_left,
        Subgroup.inclusion_injective le_sup_right, hdisj⟩
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨a, ha, v, hv, hax⟩ := A3.exists_mul_of_comm hAcomm x.2
    refine ⟨(⟨a, ha⟩, ⟨v, hv⟩), ?_⟩
    apply Subtype.ext
    show (a : MulAut ↥E) * (v : MulAut ↥E) = (x : MulAut ↥E)
    exact hax.symm
  let eProd : ↥A × ↥(zpowers u) ≃* ↥(A ⊔ zpowers u) :=
    MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have eC : ↥C ≃* ↥(A ⊔ zpowers u) := by
    rw [hC]
    exact Subgroup.subgroupOfEquivOfLe hle
  obtain ⟨eA⟩ := S.A_iso
  have hcard : Nat.card ↥(zpowers u) = Nat.card (Multiplicative (ZMod 2)) := by
    rw [Nat.card_zpowers, horder]
    exact (Nat.card_zmod 2).symm
  let eU : ↥(zpowers u) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq hcard
  exact ⟨(eC.trans eProd.symm).trans
    ((eA.prodCongr eU).trans MulEquiv.prodComm)⟩

theorem oddNormal_fusionOddCore {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ) :
    OddNormal H ((fusionOddCore ↥H).map H.subtype) := by
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro h hh p hp
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
    exact Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥H) * p' * (⟨h, hh⟩ : ↥H)⁻¹,
      (CFSG.Open.fusionOddCore_normal ↥H).conj_mem p' hp' (⟨h, hh⟩ : ↥H), by simp⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd ↥H

theorem commutator_mem_of_central {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ) {u : Γ}
    (hu : u ∈ H)
    (hcen : ∀ y : ↥H ⧸ fusionOddCore ↥H, y * (QuotientGroup.mk (⟨u, hu⟩ : ↥H)) =
      (QuotientGroup.mk (⟨u, hu⟩ : ↥H)) * y) :
    ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ (fusionOddCore ↥H).map H.subtype := by
  intro h hh
  have hw1 : (QuotientGroup.mk' (fusionOddCore ↥H))
      ((⟨h, hh⟩ : ↥H) * (⟨u, hu⟩ : ↥H) * (⟨h, hh⟩ : ↥H)⁻¹ * (⟨u, hu⟩ : ↥H)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change (QuotientGroup.mk (⟨h, hh⟩ : ↥H)) * (QuotientGroup.mk (⟨u, hu⟩ : ↥H)) *
      (QuotientGroup.mk (⟨h, hh⟩ : ↥H))⁻¹ * (QuotientGroup.mk (⟨u, hu⟩ : ↥H))⁻¹ = 1
    rw [hcen (QuotientGroup.mk (⟨h, hh⟩ : ↥H))]
    group
  have hmem : (⟨h, hh⟩ : ↥H) * (⟨u, hu⟩ : ↥H) * (⟨h, hh⟩ : ↥H)⁻¹ * (⟨u, hu⟩ : ↥H)⁻¹ ∈
      fusionOddCore ↥H :=
    (QuotientGroup.eq_one_iff _).mp hw1
  exact Subgroup.mem_map.mpr ⟨_, hmem, by simp⟩

end C10

end CFSG.OddStandard.SmallF3.Omega
