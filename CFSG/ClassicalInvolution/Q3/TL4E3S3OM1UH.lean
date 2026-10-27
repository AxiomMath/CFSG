module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UG
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1SD
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Aut
public import CFSG.LieType.Multipliers.U43

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.Sporadic.SmallOddCore
open CFSG.LinearGroups.UnitaryThreeOverNine


theorem conjSub_injective (g : Equiv.Perm (Fin 820)) : Function.Injective (conjSub g) := by
  intro A B h
  rw [← conjSub_one A, ← conjSub_one B, ← inv_mul_cancel g, conjSub_mul, conjSub_mul, h]

theorem model {K : Subgroup (Equiv.Perm (Fin 820))} {r ρ q w : Equiv.Perm (Fin 820)}
    (hd : Vtx.AmbientQuatDatum P K r) (hρ : ρ ∈ R) (hq : q ∈ P) (hqr : q * r = r * q)
    (hne : conjSub q K ≠ K) (hρ2 : ρ * ρ = 1) (hfix : ∀ a ∈ K, ρ * a = a * ρ)
    (hw : w ∈ conjSub q K) (hw4 : orderOf w = 4)
    (hwB : ∀ b ∈ conjSub q K, ρ * b * ρ⁻¹ = w * b * w⁻¹) : Concl K ρ := by
  obtain ⟨g, hg, hgr, hgK⟩ := exists_conj_K0 hd
  have hd0 : Vtx.AmbientQuatDatum P K0 r0P := by
    have h := hd.conj hg
    rwa [hgr, hgK] at h
  have hB : conjSub (g * q * g⁻¹) K0 = conjSub g (conjSub q K) := by rw [← hgK, conjSub_conj]
  have hc := model_K0 hd0 (ρ := g * ρ * g⁻¹) (q := g * q * g⁻¹) (w := g * w * g⁻¹)
    (R.mul_mem (R.mul_mem (P_le_R hg) hρ) (R.inv_mem (P_le_R hg)))
    (P.mul_mem (P.mul_mem hg hq) (P.inv_mem hg))
    (by rw [← hgr]; exact (comm_conj_iff g q r).2 hqr)
    (by rw [hB, ← hgK]; exact fun h => hne (conjSub_injective g h))
    (by rw [show g * ρ * g⁻¹ * (g * ρ * g⁻¹) = g * (ρ * ρ) * g⁻¹ by group, hρ2]; group)
    (by rw [← hgK]; rintro _ ⟨a, ha, rfl⟩; exact (comm_conj_iff g ρ a).2 (hfix a ha))
    (by rw [hB]; exact conj_mem_conjSub hw)
    (by rw [← hw4]; exact MulEquiv.orderOf_eq (MulAut.conj g) w)
    (by
      rw [hB]
      rintro _ ⟨b, hb, rfl⟩
      have h1 := hwB b hb
      show g * ρ * g⁻¹ * (g * b * g⁻¹) * (g * ρ * g⁻¹)⁻¹ =
        g * w * g⁻¹ * (g * b * g⁻¹) * (g * w * g⁻¹)⁻¹
      calc g * ρ * g⁻¹ * (g * b * g⁻¹) * (g * ρ * g⁻¹)⁻¹ = g * (ρ * b * ρ⁻¹) * g⁻¹ := by group
        _ = g * (w * b * w⁻¹) * g⁻¹ := by rw [h1]
        _ = g * w * g⁻¹ * (g * b * g⁻¹) * (g * w * g⁻¹)⁻¹ := by group)
  have h := concl_conj (P.inv_mem hg) hc
  rwa [← hgK, ← conjSub_mul, inv_mul_cancel, conjSub_one,
    show g⁻¹ * (g * ρ * g⁻¹) * g⁻¹⁻¹ = ρ by group] at h

theorem nonempty_mulEquiv_P {S : Type} [Group S] (hS : CFSG.Blueprint.LieModel S .PSU 4 3 1) :
    Nonempty (S ≃* ↥P) :=
  let ⟨e⟩ := nonempty_mulEquiv_X₀ hS
  ⟨e.trans psiEquiv⟩

theorem sigmaFixOm3_PSU {S : Type} [Group S]
    (hS : CFSG.Blueprint.LieModel S .PSU 4 3 1) : SigmaFixOm3 S := by
  obtain ⟨θ⟩ := nonempty_mulEquiv_P hS
  set φ : S →* Equiv.Perm (Fin 820) := P.subtype.comp θ.toMonoidHom with hφdef
  have hφinj : Function.Injective φ := Subtype.val_injective.comp θ.injective
  have hφP : ∀ s, φ s ∈ P := fun s => (θ s).2
  have hφsurj : ∀ p ∈ P, ∃ s, φ s = p := fun p hp =>
    ⟨θ.symm ⟨p, hp⟩, by simp [hφdef]⟩
  have hrange : φ.range = P := le_antisymm (by rintro _ ⟨s, rfl⟩; exact hφP s) fun p hp => by
    obtain ⟨s, hs⟩ := hφsurj p hp
    exact ⟨s, hs⟩
  intro A B r x hd ⟨q, hq, hqB⟩ hne hxx hfixA ⟨w, hwB, hw4, hwx⟩ _
  obtain ⟨ρ, hρR, hρ⟩ := autModel.surj (MulAut.congr θ x)
  have hρφ : ∀ s, φ (x s) = ρ * φ s * ρ⁻¹ := fun s => by
    have h1 := hρ (θ s)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hcomm_of : ∀ y, x y = y → ρ * φ y = φ y * ρ := fun y hy => by
    have h1 : ρ * φ y * ρ⁻¹ = φ y := by rw [← hρφ, hy]
    rw [← h1, inv_mul_cancel_right, h1]
  have hdP : Vtx.AmbientQuatDatum P (A.map φ) (φ r) := by
    have h := Vtx.ambientQuatDatum_map φ hφinj hd
    rwa [hrange] at h
  have hB' : conjSub (φ q) (A.map φ) = B.map φ := by rw [conjSub_map, hqB]
  have hρ2 : ρ * ρ = 1 := autModel.inj _ (R.mul_mem hρR hρR) fun p hp => by
    obtain ⟨s, rfl⟩ := hφsurj p hp
    have h1 : x (x s) = s := by
      have := congrArg (fun τ : MulAut S => τ s) hxx
      simpa using this
    calc ρ * ρ * φ s = ρ * (ρ * φ s * ρ⁻¹) * ρ⁻¹ * (ρ * ρ) := by group
      _ = φ (x (x s)) * (ρ * ρ) := by rw [← hρφ, ← hρφ]
      _ = φ s * (ρ * ρ) := by rw [h1]
  have hcon := model hdP hρR (hφP q)
    (by rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hq])
    (by rw [hB']; exact fun h => hne (Subgroup.map_injective hφinj h)) hρ2
    (by rintro _ ⟨a, ha, rfl⟩; exact hcomm_of a (hfixA a ha))
    (by rw [hB']; exact ⟨w, hwB, rfl⟩) (by rw [orderOf_injective φ hφinj w, hw4])
    (by
      rw [hB']
      rintro _ ⟨b, hb, rfl⟩
      rw [← hρφ, hwx b hb, map_mul, map_mul, map_inv])
  have hY : (sigmaFixGen A x).map φ = Yb (A.map φ) ρ := by
    simp only [sigmaFixGen, Yb, Subgroup.map_iSup]
    refine le_antisymm (iSup₂_le fun M hM => ?_) (iSup₂_le fun C hC => ?_)
    · obtain ⟨⟨s, rfl⟩, hMx⟩ := hM
      refine le_iSup₂_of_le ((conjSub s A).map φ) ⟨⟨φ s, hφP s, conjSub_map φ s A⟩, ?_⟩ le_rfl
      rintro _ ⟨y, hy, rfl⟩
      exact hcomm_of y (hMx y hy)
    · obtain ⟨⟨g, hg, rfl⟩, hcomm⟩ := hC
      obtain ⟨s, rfl⟩ := hφsurj g hg
      rw [conjSub_map]
      refine le_iSup₂_of_le (conjSub s A) ⟨⟨s, rfl⟩, fun y hy => hφinj ?_⟩ le_rfl
      rw [hρφ, hcomm _ (by rw [conjSub_map]; exact ⟨y, hy, rfl⟩), mul_inv_cancel_right]
  obtain ⟨⟨eY⟩, h3⟩ := hcon
  refine ⟨?_, ?_⟩
  · have e1 : ↥(sigmaFixGen A x) ≃* StatedSU 3 3 F9 :=
      ((sigmaFixGen A x).equivMapOfInjective φ hφinj).trans ((MulEquiv.subgroupCongr hY).trans eY)
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e1.symm
      (Or.inl ⟨by decide, classicalModel_statedSU natCard_F9⟩)
  · rintro _ ⟨s, rfl⟩ hCx
    have hCF : (conjSub s A).map φ ∈ FixSet (A.map φ) ρ := ⟨⟨φ s, hφP s, conjSub_map φ s A⟩, by
      rintro _ ⟨y, hy, rfl⟩
      exact hcomm_of y (hCx y hy)⟩
    obtain ⟨y', hy', hyC, hy3, c', hc', hyc⟩ := h3 _ hCF
    rw [← hY] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    obtain ⟨c, hc, rfl⟩ := hc'
    refine ⟨y, hy, Subgroup.map_injective hφinj (by rw [← conjSub_map, hyC]),
      hφinj (by rw [map_pow, hy3, map_one]), c, hc, fun h => hyc ?_⟩
    rw [← map_mul, ← map_mul, h]

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
