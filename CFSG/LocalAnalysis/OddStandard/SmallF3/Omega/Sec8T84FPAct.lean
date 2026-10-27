module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Vec4)

theorem sec8t84_conj_injective {Y : Type} [Group Y] {E H : Subgroup Y} [E.Normal]
    (hE : IsElemAb2 E 4) (hH : Nonempty (↥H ≃* alternatingGroup (Fin 6)))
    (htr : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → ∃ h ∈ H, h * a * h⁻¹ = b) :
    Function.Injective ((MulAut.conjNormal : Y →* MulAut ↥E).comp H.subtype) := by
  let φ : ↥H →* MulAut ↥E := (MulAut.conjNormal : Y →* MulAut ↥E).comp H.subtype
  haveI : IsSimpleGroup ↥H :=
    hH.some.isSimpleGroup_congr.mpr
      (alternatingGroup.isSimpleGroup (α := Fin 6) (by simp [Nat.card_eq_fintype_card]))
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
    · exact hbot
    · exfalso
      have hφ1 : φ = 1 := MonoidHom.ker_eq_top_iff.mp htop
      haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE.2]; norm_num)
      haveI : Fintype ↥E := Fintype.ofFinite ↥E
      have hcard : Fintype.card ↥E = 16 := by
        rw [← Nat.card_eq_fintype_card, hE.2]; norm_num
      obtain ⟨a, b, c, hab, hac, hbc⟩ :=
        Fintype.two_lt_card_iff.mp (show 2 < Fintype.card ↥E by rw [hcard]; norm_num)
      obtain ⟨p, q, hp1, hq1, hqp⟩ : ∃ p q : ↥E, p ≠ 1 ∧ q ≠ 1 ∧ q ≠ p := by
        by_cases ha : a = 1
        · exact ⟨b, c, fun hb => hab (ha.trans hb.symm),
            fun hc => hac (ha.trans hc.symm), Ne.symm hbc⟩
        · by_cases hb : b = 1
          · exact ⟨a, c, ha, fun hc => hbc (hb.trans hc.symm), Ne.symm hac⟩
          · exact ⟨a, b, ha, hb, Ne.symm hab⟩
      obtain ⟨h, hh, hconj⟩ := htr (p : Y) p.2 (fun h1 => hp1 (Subtype.ext h1))
        (q : Y) q.2 (fun h1 => hq1 (Subtype.ext h1))
      have hfix : (MulAut.conjNormal (h : Y)) p = p := by
        have hker : φ ⟨h, hh⟩ = 1 := by rw [hφ1]; rfl
        have h2 := congrArg (fun f : MulAut ↥E => f p) hker
        rw [show φ ⟨h, hh⟩ = MulAut.conjNormal (h : Y) from rfl] at h2
        simpa using h2
      have hcoe : (h : Y) * (p : Y) * (h : Y)⁻¹ = (p : Y) := by
        have h2 := congrArg Subtype.val hfix
        simpa only [MulAut.conjNormal_apply] using h2
      exact hqp (Subtype.ext (by rw [← hconj, hcoe]))
  exact hφ

theorem sec8t84_coords {Y : Type} [Group Y] {E H : Subgroup Y}
    [E.Normal] (hE : IsElemAb2 E 4) (hH : Nonempty (↥H ≃* alternatingGroup (Fin 6)))
    (htr : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → ∃ h ∈ H, h * a * h⁻¹ = b) :
    ∃ (e : ↥E ≃* Multiplicative Vec4) (ψ : ↥H ≃* alternatingGroup (Fin 6)),
      ∀ (h : ↥H) (x : ↥E), Multiplicative.toAdd (e (MulAut.conjNormal (h : Y) x)) =
        rho ((ψ h : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) *ᵥ
          Multiplicative.toAdd (e x) := by
  let φ : ↥H →* MulAut ↥E := (MulAut.conjNormal : Y →* MulAut ↥E).comp H.subtype
  have hinj : Function.Injective φ := sec8t84_conj_injective hE hH htr
  have hHrange : Nonempty (↥φ.range ≃* alternatingGroup (Fin 6)) :=
    ⟨(MonoidHom.ofInjective hinj).symm.trans hH.some⟩
  obtain ⟨e, ψ', hact, _⟩ := sec8t84_a6_conj (G := Y) E hE φ.range hHrange
  let ψ : ↥H ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hinj).trans ψ'
  refine ⟨e, ψ, ?_⟩
  intro h x
  have h1 := hact (MonoidHom.ofInjective hinj h) x
  rw [MonoidHom.ofInjective_apply] at h1
  have hψ : (ψ h : alternatingGroup (Fin 6)) = ψ' (MonoidHom.ofInjective hinj h) := rfl
  rw [hψ]
  rw [show φ h = MulAut.conjNormal (h : Y) from rfl] at h1
  change Multiplicative.toAdd (e (MulAut.conjNormal (h : Y) x)) =
    rho (↑(ψ' (MonoidHom.ofInjective hinj h)) : Equiv.Perm (Fin 6)) *ᵥ
      Multiplicative.toAdd (e x)
  exact h1

end CFSG.OddStandard.SmallF3.Omega
