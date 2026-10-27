module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Fours
public import CFSG.Sporadic.Recognition.CoverTransfer

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HSStd
open CFSG.Sporadic.Recognition.CoverTransfer (sq_eq_sq_of_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (onCenterQuotient onCenterQuotient_apply_mk centerQuotientHom centerQuotientHom_injective)

section Generic

variable {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} {L : Type*} [Group L]

theorem foursGroupCondition_of_cover [Group.IsPerfect L] (e : R ≃* MulAut P)
    (he : ∀ (x : R) (p : P),
      ((e x p : P) : Equiv.Perm (Fin n)) = (x : Equiv.Perm (Fin n)) * p * (x : _)⁻¹)
    (f : L ⧸ center L ≃* P) (hexp : ∀ c ∈ center L, c ^ 2 = 1) {x₁ : L} (hx₁ : x₁ ^ 2 = 1)
    (hx₁c : x₁ ∉ center L) (reps : List R)
    (hcover : ∀ τ : R, orderOf (τ : Equiv.Perm (Fin n)) = 2 → (τ : Equiv.Perm (Fin n)) ∉ P →
      ∃ ρ ∈ reps, ∃ g ∈ P, (τ : Equiv.Perm (Fin n)) = g * ρ * g⁻¹)
    (hwit : ∀ ρ ∈ reps, ∃ l c : P,
      (l : Equiv.Perm (Fin n)) * ρ * (l : Equiv.Perm (Fin n))⁻¹ * (ρ : Equiv.Perm (Fin n))⁻¹ =
        (c : Equiv.Perm (Fin n)) * (f (QuotientGroup.mk x₁) : Equiv.Perm (Fin n)) *
          (c : Equiv.Perm (Fin n))⁻¹) :
    CFSG.EvenSmallLie.FoursGroupCondition L := by
  intro φ hφ2 hφout
  let q : L →* P := f.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    ext x
    simp only [MonoidHom.mem_ker, q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]
  let α : MulAut P := MulAut.congr f (onCenterQuotient φ)
  have hα : ∀ l : L, α (q l) = q (φ l) := fun l => by
    have h : α (f (l : L ⧸ center L)) = f (onCenterQuotient φ (l : L ⧸ center L)) := by
      simp [α]
    exact h.trans (congrArg f (onCenterQuotient_apply_mk φ l))
  have hαα : α * α = 1 := by
    have h : onCenterQuotient φ * onCenterQuotient φ = 1 := by
      show centerQuotientHom L φ * centerQuotientHom L φ = 1
      rw [← map_mul, hφ2, map_one]
    rw [← map_mul, h, map_one]
  obtain ⟨a, ha⟩ := e.surjective α
  have haa : a * a = 1 := e.injective (by rw [map_mul, ha, hαα, map_one])
  have hαp : ∀ p : P, ((α p : P) : Equiv.Perm (Fin n)) =
      (a : Equiv.Perm (Fin n)) * p * (a : Equiv.Perm (Fin n))⁻¹ := fun p => by
    rw [← ha]
    exact he a p
  have haP : (a : Equiv.Perm (Fin n)) ∉ P := by
    intro hap
    obtain ⟨l₀, hl₀⟩ := hq ⟨a, hap⟩
    refine hφout l₀ (centerQuotientHom_injective L ?_)
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    apply f.injective
    refine Subtype.ext ?_
    have h1 : f (centerQuotientHom L φ (y : L ⧸ center L)) = q (φ y) :=
      congrArg f (onCenterQuotient_apply_mk φ y)
    have h2 : f (centerQuotientHom L (MulAut.conj l₀) (y : L ⧸ center L)) =
        q (l₀ * y * l₀⁻¹) := congrArg f (onCenterQuotient_apply_mk (MulAut.conj l₀) y)
    rw [h1, h2, ← hα, hαp, map_mul, map_mul, map_inv, hl₀]
    rfl
  have ha2 : orderOf (a : Equiv.Perm (Fin n)) = 2 :=
    orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, haa, Subgroup.coe_one])
      (fun h1 => haP (h1 ▸ P.one_mem))
  obtain ⟨ρ, hρ, g, hg, hag⟩ := hcover a ha2 haP
  obtain ⟨l, c, hlc⟩ := hwit ρ hρ
  obtain ⟨l', hl'⟩ := hq (⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹)
  have hqv : q (l' * (φ l')⁻¹) = (⟨g, hg⟩ * c) * q x₁ * (⟨g, hg⟩ * c)⁻¹ := by
    refine Subtype.ext ?_
    have e1 : ((q (φ l') : P) : Equiv.Perm (Fin n)) =
        (a : Equiv.Perm (Fin n)) * (q l' : Equiv.Perm (Fin n)) * (a : Equiv.Perm (Fin n))⁻¹ := by
      rw [← hα, hαp]
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, e1, hl', hag]
    calc ((⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹ : P) : Equiv.Perm (Fin n)) *
        (g * (ρ : Equiv.Perm (Fin n)) * g⁻¹ * ((⟨g, hg⟩ * l * ⟨g, hg⟩⁻¹ : P) :
          Equiv.Perm (Fin n)) * (g * (ρ : Equiv.Perm (Fin n)) * g⁻¹)⁻¹)⁻¹ =
        g * ((l : Equiv.Perm (Fin n)) * ρ * (l : Equiv.Perm (Fin n))⁻¹ *
          (ρ : Equiv.Perm (Fin n))⁻¹) * g⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
      _ = g * ((c : Equiv.Perm (Fin n)) * (f (QuotientGroup.mk x₁) : Equiv.Perm (Fin n)) *
          (c : Equiv.Perm (Fin n))⁻¹) * g⁻¹ := by rw [hlc]
      _ = _ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          exact (by group : g * (↑c * ↑(f (QuotientGroup.mk x₁)) * (↑c)⁻¹) * g⁻¹ =
            g * ↑c * ↑(f (QuotientGroup.mk x₁)) * (g * ↑c)⁻¹)
  have hv2 : (l' * (φ l')⁻¹) ^ 2 = 1 := by
    have h := sq_eq_sq_of_conj q hq hker.le (fun c hc => hexp c (hker ▸ hc)) hqv
      (by rw [← map_pow, hx₁, map_one])
    rw [h, hx₁]
  refine ⟨l', hv2, fun hv => hx₁c ?_⟩
  rw [← hker, MonoidHom.mem_ker, hqv] at hv
  rw [← hker, MonoidHom.mem_ker]
  have h1 : q x₁ = (⟨g, hg⟩ * c)⁻¹ * ((⟨g, hg⟩ * c) * q x₁ * (⟨g, hg⟩ * c)⁻¹) *
      (⟨g, hg⟩ * c) := by group
  rw [h1, hv]
  group

end Generic

section HS


theorem foursGroupCondition_of_isSporadic_cover_hs {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (hZ : Nat.card (center L) = 2) (hq : IsSporadic (L ⧸ center L) .HS) :
    CFSG.EvenSmallLie.FoursGroupCondition L := by
  obtain ⟨ψ⟩ := hq
  have ψ' : L ⧸ center L ≃* NativeSporadic.HS := ψ
  let f : L ⧸ center L ≃* hsP := ψ'.trans hsPermEquiv
  have hexp : ∀ c ∈ center L, c ^ 2 = 1 := by
    intro c hc
    have h : orderOf (⟨c, hc⟩ : center L) ∣ 2 := hZ ▸ orderOf_dvd_natCard _
    simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h)
  obtain ⟨a₁, a₂, a₃, n, hdat, hw2, hw3⟩ := cover_datum
  let q : L →* hsP := f.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    ext x
    simp only [MonoidHom.mem_ker, q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]
  obtain ⟨b₁, -, -, hb₁, -, -, hb₁sq, -, -, -, -, -⟩ :=
    hdat.exists_lift (φ := q) hq hker.le
  have hb₁c : b₁ ∉ center L := fun h => hdat.ne_one (by
    rw [← hb₁]
    exact (hker ▸ h : b₁ ∈ q.ker))
  obtain ⟨e, he, -, -, -⟩ := hs_full_automorphism_model
  obtain ⟨h0, h1, hR2, hP2, hR3, hP3, hcover⟩ := class_data_hs
  refine foursGroupCondition_of_cover e he f hexp hb₁sq hb₁c
    [⟨tp 3850 rho2, hR2⟩, ⟨tp 3850 rho3, hR3⟩] (fun τ hτ hτP => ?_) (fun ρ hρ => ?_)
  · obtain ⟨g, hg, hv⟩ := hcover τ τ.2 hτ
    rcases hv with hv | hv | hv | hv
    · exact absurd (hv ▸ hsP.mul_mem (hsP.mul_mem hg h0) (hsP.inv_mem hg)) hτP
    · exact absurd (hv ▸ hsP.mul_mem (hsP.mul_mem hg h1) (hsP.inv_mem hg)) hτP
    · exact ⟨⟨tp 3850 rho2, hR2⟩, List.mem_cons_self, g, hg, hv⟩
    · exact ⟨⟨tp 3850 rho3, hR3⟩, List.mem_cons_of_mem _ List.mem_cons_self, g, hg, hv⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · exact hw2.imp fun l => Exists.imp fun c h => by simpa [← hb₁, q] using h
    · exact hw3.imp fun l => Exists.imp fun c h => by simpa [← hb₁, q] using h

end HS

end CFSG.EvenSporadicStandard.TwoHS
