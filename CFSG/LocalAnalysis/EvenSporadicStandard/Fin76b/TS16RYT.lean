module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Pull

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

structure ThetaData (G : Type) [Group G] (L : Subgroup G) (z : G) : Prop where
  z_cent : ∀ ℓ ∈ L, ℓ * z = z * ℓ
  center_triv : ∀ ℓ : ↥L, (∀ m : ↥L, m * ℓ = ℓ * m) → ℓ = 1
  norm : ∀ g ∈ centralizer ({z} : Set G), ∀ ℓ ∈ L, g * ℓ * g⁻¹ ∈ L
  surj : ∀ r : MulAut ↥L, ∃ g ∈ centralizer ({z} : Set G),
    ∀ ℓ : ↥L, g * (ℓ : G) * g⁻¹ = ((r ℓ : ↥L) : G)
  ker : ∀ g ∈ centralizer ({z} : Set G), (∀ ℓ ∈ L, g * ℓ = ℓ * g) → g ∈ zpowers z

theorem ThetaData.of_pullHyp {G : Type} [Group G] {L : Subgroup G} {z t : G} {T : Subgroup G}
    {EY : Subgroup (MulAut (↥L ⧸ center ↥L))} (hP : PullHyp G L z t T EY)
    (hsurj : Function.Surjective (thetaH hP.cfg.cent_le)) : ThetaData G L z := by
  have hMN := hP.cfg.cent_le
  have hnorm : ∀ g ∈ centralizer ({z} : Set G), ∀ ℓ ∈ L, g * ℓ * g⁻¹ ∈ L :=
    fun g hg ℓ hℓ => (mem_normalizer_iff.1 (hMN hg) ℓ).1 hℓ
  have hinj : Function.Injective (QuotientGroup.mk' (center ↥L)) := by
    intro a b hab
    have h1 : (a : ↥L ⧸ center ↥L) = (b : ↥L ⧸ center ↥L) := hab
    rw [QuotientGroup.eq, hP.hZ, mem_bot] at h1
    exact inv_mul_eq_one.1 h1
  have hbij : Function.Bijective (QuotientGroup.mk' (center ↥L)) :=
    ⟨hinj, QuotientGroup.mk_surjective⟩
  let ψ : ↥L ≃* ↥L ⧸ center ↥L := MulEquiv.ofBijective (QuotientGroup.mk' (center ↥L)) hbij
  have hψ : ∀ ℓ : ↥L, ψ ℓ = (ℓ : ↥L ⧸ center ↥L) := fun ℓ => rfl
  have happ : ∀ (g : G) (hg : g ∈ centralizer ({z} : Set G)) (ℓ : ↥L),
      thetaH hMN ⟨g, hg⟩ (ℓ : ↥L ⧸ center ↥L) =
        ((⟨g * ℓ * g⁻¹, hnorm g hg ℓ ℓ.2⟩ : ↥L) : ↥L ⧸ center ↥L) :=
    fun g hg ℓ => thetaH_apply hMN ⟨g, hg⟩ ℓ ⟨g * ℓ * g⁻¹, hnorm g hg ℓ ℓ.2⟩ rfl
  refine ⟨fun ℓ hℓ => mem_centralizer_iff.1 hP.cfg.z_cent ℓ hℓ, fun ℓ hℓ => ?_, hnorm, ?_, ?_⟩
  · have hmem : ℓ ∈ center ↥L := Subgroup.mem_center_iff.2 hℓ
    rw [hP.hZ, mem_bot] at hmem
    exact hmem
  · intro r
    obtain ⟨⟨g, hg⟩, hgr⟩ := hsurj (MulAut.congr ψ r)
    refine ⟨g, hg, fun ℓ => ?_⟩
    have h1 := happ g hg ℓ
    rw [hgr] at h1
    have h2 : (MulAut.congr ψ r) (ℓ : ↥L ⧸ center ↥L) = ((r ℓ : ↥L) : ↥L ⧸ center ↥L) := by
      have e2 : ψ.symm (ℓ : ↥L ⧸ center ↥L) = ℓ := by
        rw [← hψ ℓ]
        exact ψ.symm_apply_apply ℓ
      show ψ (r (ψ.symm (ℓ : ↥L ⧸ center ↥L))) = _
      rw [e2, hψ]
    rw [h2] at h1
    have h3 : (⟨g * ℓ * g⁻¹, hnorm g hg ℓ ℓ.2⟩ : ↥L) = r ℓ := hinj h1.symm
    exact congrArg Subtype.val h3
  · intro g hg hcomm
    have h1 : thetaH hMN ⟨g, hg⟩ = 1 := by
      ext q
      obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
      have h2 := happ g hg ℓ
      have h3 : g * (ℓ : G) * g⁻¹ = ℓ := by
        calc g * (ℓ : G) * g⁻¹ = (ℓ * g) * g⁻¹ := by rw [hcomm ℓ ℓ.2]
          _ = ℓ := by group
      have h4 : (⟨g * ℓ * g⁻¹, hnorm g hg ℓ ℓ.2⟩ : ↥L) = ℓ := Subtype.ext h3
      rw [h4] at h2
      simpa using h2
    exact (hP.ker ⟨g, hg⟩).1 h1

end CFSG.EvenSporadicStandard.Fin76b
