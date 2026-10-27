module

public import CFSG.Timmesfeld.ARS.ExclNSFrames
public import CFSG.Timmesfeld.RankTwo.Presentation
public import CFSG.Timmesfeld.ARS.ExclNSDefs

public section

namespace CFSG.LargeExtraspecial.A2Mod

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley

namespace Frame

theorem three_le_of_nslType_cartanC {n : ℕ} {i₀ : Fin n}
    (h : NSLType n (Symplectic.cartanC n) i₀) : 3 ≤ n := by
  generalize hA : Symplectic.cartanC n = A at h
  cases h with
  | symplectic hn i₀ hi₀ => exact hn
  | orthogonal hm i₀ hi₀ => exact absurd hA.symm (cartanB_ne_cartanC (by omega))
  | g2 i₀ hi₀ => exact absurd hA.symm cartan_G2_ne_cartanC
  | f4 i₀ hi₀ => exact absurd hA.symm cartan_F4_ne_cartanC

theorem of_nslType_cartanB {m : ℕ} {i₀ : Fin m} (h : NSLType m (Spin.cartanB m) i₀) :
    3 ≤ m ∧ i₀.val + 1 < m := by
  generalize hA : Spin.cartanB m = A at h
  cases h with
  | symplectic hn i₀ hi₀ => exact absurd hA (cartanB_ne_cartanC (by omega))
  | orthogonal hm i₀ hi₀ => exact ⟨hm, hi₀⟩
  | g2 i₀ hi₀ => exact absurd hA (by decide)
  | f4 i₀ hi₀ => exact absurd hA (by decide)

theorem card_rootGroup_symplectic (n : ℕ) (F : Type) [Field F] (i : Fin n) :
    Nat.card ((Symplectic.rootDatum n F).rootGroup (Pi.single i 1)) = Nat.card F := by
  have hγ : (Pi.single i 1 : Fin n → ℤ) ∈ RootSystem.roots (Symplectic.isFiniteType_cartanC n) ∅ :=
    Or.inl ⟨1, i, by simp⟩
  obtain ⟨r, hr⟩ := Symplectic.SpExtras.exists_stdVec_of_mem_roots hγ
  refine (Nat.card_eq_of_bijective (fun c : F => (⟨Symplectic.SpExtras.elt r c,
    Symplectic.SpExtras.elt_mem_rootGroup hr c⟩ : (Symplectic.rootDatum n F).rootGroup
      (Pi.single i 1))) ⟨fun c d h => Symplectic.SpExtras.elt_injective r (congrArg Subtype.val h),
    fun x => ?_⟩).symm
  obtain ⟨c, hc⟩ := (Symplectic.SpExtras.mem_rootGroup_iff hr).mp x.2
  exact ⟨c, Subtype.ext hc.symm⟩

theorem card_rootGroup_minus (n : ℕ) {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    Nat.card ((Spin.Twisted.minusDatum n hirr).rootGroup (Pi.single k 1)) = Nat.card K := by
  change Nat.card (Spin.Twisted.minusRootGroup n hirr (Pi.single k 1)) = _
  rw [Spin.Twisted.minusRootGroup_single_of_lt n hirr hk]
  exact (Nat.card_congr (MonoidHom.ofInjective
    ((Spin.Twisted.minusFrame n b c).longRoot_injective _ true false)).toEquiv).symm

section Frames

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem rootGroup_single_inf_center (F : NSLFrameData G R) (i : Fin F.D.rank) :
    F.D.rootGroup (Pi.single i 1) ⊓ Subgroup.center F.K = ⊥ := by
  refine eq_bot_iff.mpr fun u hu => ?_
  obtain ⟨hu, hc⟩ := Subgroup.mem_inf.mp hu
  refine (Subgroup.mem_bot).mpr (F.hext.eq_one_of_mem_normalizer i u hu ?_)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← Subgroup.mem_center_iff.mp hc h, mul_inv_cancel_right]

theorem injective_restrict (F : NSLFrameData G R) (i : Fin F.D.rank) :
    Function.Injective (F.Ψ.comp (F.D.rootGroup (Pi.single i 1)).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker] at hx
  have hx' : (x : F.K) ∈ F.D.rootGroup (Pi.single i 1) ⊓ Subgroup.center F.K :=
    Subgroup.mem_inf.mpr ⟨x.2, F.ker hx⟩
  rw [rootGroup_single_inf_center, Subgroup.mem_bot] at hx'
  exact (Subgroup.mem_bot).mpr (Subtype.ext hx')

theorem card_map_rootGroup_single (F : NSLFrameData G R) (i : Fin F.D.rank) :
    Nat.card ((F.D.rootGroup (Pi.single i 1)).map F.Ψ) =
      Nat.card (F.D.rootGroup (Pi.single i 1)) := by
  have e : (F.D.rootGroup (Pi.single i 1)).map F.Ψ =
      (F.Ψ.comp (F.D.rootGroup (Pi.single i 1)).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e]
  exact Nat.card_congr (MonoidHom.ofInjective (injective_restrict F i)).toEquiv.symm

theorem ker_eq_center (F : NSLFrameData G R) (hZ : Subgroup.center G = ⊥) :
    F.Ψ.ker = Subgroup.center F.K := by
  refine le_antisymm F.ker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have : F.Ψ z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := F.surj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
  rwa [hZ, Subgroup.mem_bot] at this

noncomputable def centerQuotientEquiv (F : NSLFrameData G R) (hZ : Subgroup.center G = ⊥) :
    F.K ⧸ Subgroup.center F.K ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq_center F hZ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective F.Ψ F.surj)

theorem lieModel_of_centerQuotient (F : NSLFrameData G R) (hZ : Subgroup.center G = ⊥)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel (F.K ⧸ Subgroup.center F.K) t n p f) :
    LieModel G t n p f :=
  CurtisTits.lieModel_of_mulEquiv (centerQuotientEquiv F hZ) h

theorem card_rootGroup_g2 (K : Type) [Field K] (i : Fin (Tag.rank .G2)) :
    Nat.card ((Steinberg.Adjoint.g2Datum K).rootGroup (Pi.single i 1)) = Nat.card K := by
  have hγ := isRoot_single .G2 i
  refine (Nat.card_eq_of_bijective (fun c : K => (⟨Steinberg.Adjoint.xPar _ _ c,
    Steinberg.Adjoint.xPar_mem hγ c⟩ : (Steinberg.Adjoint.g2Datum K).rootGroup (Pi.single i 1)))
    ⟨fun c d h => Steinberg.Adjoint.xPar_injective hγ (congrArg Subtype.val h),
      fun x => ?_⟩).symm
  obtain ⟨c, hc⟩ := (Steinberg.Adjoint.mem_rootGroup_iff hγ x.1).mp x.2
  exact ⟨c, Subtype.ext hc⟩

theorem lieModel_trialityD4_of_twistedGroup {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : Steinberg.TwistedD4.twistedGroup σ ⧸
      Subgroup.center (Steinberg.TwistedD4.twistedGroup σ) ≃* G) :
    LieModel G .trialityD4 0 2 f :=
  CurtisTits.lieModel_of_mulEquiv e
    (CFSG.Timmesfeld.lieModel_twistedD4_quotient Nat.prime_two hf hK σ hσ)

end Frames

end Frame

end CFSG.LargeExtraspecial.A2Mod
