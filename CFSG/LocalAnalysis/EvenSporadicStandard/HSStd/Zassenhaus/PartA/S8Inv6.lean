module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv4

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Count

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem mem_autCent_iff (k : ↥K) :
    QuotientGroup.mk k ∈ autCentralizer (tauHat hb a hK hcj hall) ↔
      k⁻¹ * sigmaK hb a hK hcj hall k ∈ center ↥K := by
  show tauHat hb a hK hcj hall (QuotientGroup.mk k) = QuotientGroup.mk k ↔ _
  rw [tauHat_mk, QuotientGroup.eq, ← inv_mem_iff (x := (sigmaK hb a hK hcj hall k)⁻¹ * k)]
  rw [mul_inv_rev, inv_inv]

theorem inv_card_le : Nat.card ↥(autCentralizer (tauHat hb a hK hcj hall)) ≤ 5760 := by
  classical
  set σ := sigmaK hb a hK hcj hall with hσ
  set τ := tauHat hb a hK hcj hall with hτ
  set N := autCentralizer τ with hN
  let mk : ↥K →* ↥K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  set D : Subgroup ↥K := N.comap mk with hD
  have hmemD : ∀ k : ↥K, k ∈ D ↔ k⁻¹ * σ k ∈ center ↥K := fun k => mem_autCent_iff hb a hK hcj hall k
  have hσc : ∀ z : ↥K, z ∈ center ↥K → σ z ∈ center ↥K := by
    intro z hz
    have : σ z ∈ (center ↥K).map (σ : ↥K →* ↥K) := ⟨z, hz, rfl⟩
    rwa [Subgroup.map_center_eq σ] at this
  let δ : ↥D →* ↥(center ↥K) :=
    { toFun := fun d => ⟨(d : ↥K)⁻¹ * σ d, (hmemD d).1 d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro d d'
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 ((hmemD d).1 d.2) ((d' : ↥K)⁻¹)
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc (d' : ↥K)⁻¹ * (d : ↥K)⁻¹ * (σ d * σ d')
            = (d' : ↥K)⁻¹ * ((d : ↥K)⁻¹ * σ d) * σ d' := by group
          _ = ((d : ↥K)⁻¹ * σ d) * (d' : ↥K)⁻¹ * σ d' := by rw [hc]
          _ = _ := by group }
  let f : ↥D →* ↥N := (mk.comp D.subtype).codRestrict N (fun d => d.2)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (x : ↥K ⧸ center ↥K)
    have hkD : k ∈ D := by
      show mk k ∈ N
      have : (mk k : ↥K ⧸ center ↥K) = x := hk
      rw [this]; exact x.2
    exact ⟨⟨k, hkD⟩, Subtype.ext hk⟩
  have hZker : Nat.card ↥(center ↥K) ≤ Nat.card ↥f.ker := by
    have hzD : ∀ z : ↥(center ↥K), (z : ↥K) ∈ D := by
      intro z
      rw [hmemD]
      exact mul_mem (inv_mem z.2) (hσc z z.2)
    refine Nat.card_le_card_of_injective (fun z => (⟨⟨z, hzD z⟩, ?_⟩ : ↥f.ker)) ?_
    · show f ⟨z, hzD z⟩ = 1
      apply Subtype.ext
      show mk (z : ↥K) = 1
      exact (QuotientGroup.eq_one_iff _).2 z.2
    · intro z z' h
      have := congrArg (fun y : ↥f.ker => ((y : ↥D) : ↥K)) h
      exact Subtype.ext this
  have h1 := Subgroup.card_ker_mul_card_of_surjective hf
  let δr : ↥D →* ↥δ.range := δ.rangeRestrict
  have hδr : Function.Surjective δr := δ.rangeRestrict_surjective
  have h2 := Subgroup.card_ker_mul_card_of_surjective hδr
  have hrange : Nat.card ↥δ.range ≤ Nat.card ↥(center ↥K) :=
    Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have hkerδ : Nat.card ↥δr.ker ≤ 5760 := by
    refine (Nat.card_le_card_of_injective
      (fun d : ↥δr.ker => (⟨(((d : ↥D) : ↥K) : ↥(Cen a.ub)), ?_⟩ :
        ↥(centralizer ({tG hb a.toPA6.toPA5} : Set ↥(Cen a.ub))))) ?_).trans
      (card_cent_le hb a.toPA6.toPA5)
    · have hd : δ (d : ↥D) = 1 := by
        have := d.2
        rw [MonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      have hd' : ((d : ↥D) : ↥K)⁻¹ * σ d = 1 := congrArg (fun x : ↥(center ↥K) => (x : ↥K)) hd
      have hσd : σ d = d := by
        have := mul_left_cancel (a := ((d : ↥D) : ↥K)⁻¹) (hd'.trans (inv_mul_cancel _).symm)
        exact this
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 := congrArg (fun x : ↥K => (x : ↥(Cen a.ub))) hσd
      simp only [hσ, sigmaK_apply] at h3
      calc (((d : ↥D) : ↥K) : ↥(Cen a.ub)) * tG hb a.toPA6.toPA5
          = (tG hb a.toPA6.toPA5 * (((d : ↥D) : ↥K) : ↥(Cen a.ub)) *
              (tG hb a.toPA6.toPA5)⁻¹) * tG hb a.toPA6.toPA5 := by rw [h3]
        _ = tG hb a.toPA6.toPA5 * (((d : ↥D) : ↥K) : ↥(Cen a.ub)) := by group
    · intro d d' h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have hcpos : 0 < Nat.card ↥(center ↥K) := Nat.card_pos
  have hmain : Nat.card ↥(center ↥K) * Nat.card ↥N ≤ 5760 * Nat.card ↥(center ↥K) := by
    calc Nat.card ↥(center ↥K) * Nat.card ↥N ≤ Nat.card ↥f.ker * Nat.card ↥N :=
          Nat.mul_le_mul_right _ hZker
      _ = Nat.card ↥δr.ker * Nat.card ↥δ.range := h1.trans h2.symm
      _ ≤ 5760 * Nat.card ↥(center ↥K) := Nat.mul_le_mul hkerδ hrange
  have : Nat.card ↥N * Nat.card ↥(center ↥K) ≤ 5760 * Nat.card ↥(center ↥K) := by
    rw [mul_comm]; exact hmain
  exact Nat.le_of_mul_le_mul_right this hcpos

end Count

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
