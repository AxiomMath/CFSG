module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ElemAbList
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPInputs
public import Certificates.Certificate442020

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace MoCE16

open Certificates.OmegaInv (fixCnt)

theorem mem_P_of_fixCnt {t : P45}
    (ht : t ∈ QA45.originalSubgroup) (hsq : t * t = 1) (hne : t ≠ 1)
    (hf : fixCnt t = 45 ∨ fixCnt t = 13 ∨ fixCnt t = 5) : t ∈ QP45.originalSubgroup := by
  rcases MoInv.class_cases ht hsq hne with ⟨-, hP, -, h⟩ | ⟨-, hP, -, h⟩ | ⟨-, -, -, h⟩ |
    ⟨-, -, -, h⟩ <;> first | exact hP | omega

theorem fixCnt_of_invCent_1440
    {t : P45} (h : InvCent 1440 t) : fixCnt t = 15 := by
  obtain ⟨ht, hsq, hne, hc⟩ := h
  rcases MoInv.class_cases ht hsq hne with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ |
    ⟨-, -, -, h1⟩ <;> omega

theorem model
    {S : Subgroup P45} (hS : S ≤ QA45.originalSubgroup)
    (hcard : Nat.card S = 16) (hsq : ∀ x ∈ S, x * x = 1) :
    ((∀ x ∈ S, x ∈ QP45.originalSubgroup) ∨ ∃ x ∈ S, fixCnt x = 15) ∧
      ∀ F : Finset P45, (∀ x ∈ F, x ∈ S ∧ fixCnt x = 15) → F.card ≤ 4 := by
  obtain ⟨hcases, hle⟩ := Certificates.certificate442020 S hS hcard hsq
  refine ⟨?_, hle⟩
  rcases hcases with h | h
  · left
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact QP45.originalSubgroup.one_mem
    · exact mem_P_of_fixCnt (hS hx) (hsq x hx) hx1 (h x hx)
  · exact Or.inr h

end MoCE16

open Certificates.OmegaInv (fixCnt)

theorem ne_one_of_fixCnt_fifteen {t : P45} (h : fixCnt t = 15) : t ≠ 1 := by
  rintro rfl
  simp [fixCnt] at h

theorem asc82FactCE16_of_cert :
    Asc82FactCE16 := by
  intro G _ _ L hL X hXN hXC hcard hsq
  obtain ⟨F⟩ := exists_pspFrame hL
  let φX : ↥X →* P45 := F.φ.comp (Subgroup.inclusion hXN)
  have hφX : ∀ x : ↥X, φX x = F.φ ⟨(x : G), hXN x.2⟩ := fun x => rfl
  have hinj : Function.Injective φX := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : G) ∈ X ⊓ centralizer (L : Set G) :=
      ⟨x.2, (F.ker_iff ⟨(x : G), hXN x.2⟩).1 (by rw [← hφX]; exact hx)⟩
    rw [hXC] at h1
    exact Subtype.ext (Subgroup.mem_bot.1 h1)
  have hSA : φX.range ≤ QA45.originalSubgroup := by
    rintro _ ⟨x, rfl⟩
    rw [hφX]
    exact F.mem_A _
  have hScard : Nat.card φX.range = 16 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hcard
  have hSsq : ∀ s ∈ φX.range, s * s = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsq x x.2), map_one]
  obtain ⟨hmain, hbound⟩ := MoCE16.model hSA hScard hSsq
  have hinv : ∀ x : ↥X, fixCnt (φX x) = 15 → InducesTypeSome L (x : G) 5 1 4 (-1) := by
    intro x hx
    refine (TyDict.inducesTypeSome_four_minus_iff hL F (x : G)).2 ⟨hXN x.2, ?_⟩
    rw [hφX] at hx
    exact MoInv.invCent_1440_of_fixCnt (F.mem_A _) (by rw [← hφX]; exact hSsq _ ⟨x, rfl⟩)
      (ne_one_of_fixCnt_fifteen hx) hx
  refine ⟨?_, ?_⟩
  · rcases hmain with hP | ⟨s, ⟨x, rfl⟩, hs15⟩
    · left
      intro x hx
      have hxN : x ∈ normalizer (L : Set G) := hXN hx
      have h1 : (⟨x, hxN⟩ : ↥(normalizer (L : Set G))) ∈
          (L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
        rw [F.sup_subgroupOf_eq]
        exact hP _ ⟨⟨x, hx⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.1 h1
    · exact Or.inr ⟨(x : G), x.2, hinv x hs15⟩
  · intro Fs hFs
    classical
    let ψ : G → P45 := fun x => if h : x ∈ X then φX ⟨x, h⟩ else 1
    have hψ : ∀ x : ↥X, ψ (x : G) = φX x := fun x => by simp [ψ]
    have hfix : ∀ x ∈ Fs, fixCnt (ψ x) = 15 := by
      intro x hx
      obtain ⟨hxX, hxT⟩ := hFs x hx
      obtain ⟨hs, hc⟩ := (TyDict.inducesTypeSome_four_minus_iff hL F x).1 hxT
      have h1 := MoCE16.fixCnt_of_invCent_1440 hc
      simp only [ψ, dif_pos hxX]
      rw [hφX]
      exact h1
    have hinjOn : Set.InjOn ψ (Fs : Set G) := by
      intro x hx y hy hxy
      have hxX := (hFs x hx).1
      have hyX := (hFs y hy).1
      have h1 := hψ ⟨x, hxX⟩
      have h2 := hψ ⟨y, hyX⟩
      simp only at h1 h2
      have h3 : φX ⟨x, hxX⟩ = φX ⟨y, hyX⟩ := by rw [← h1, ← h2]; exact hxy
      exact congrArg Subtype.val (hinj h3)
    have hle := hbound (Fs.image ψ) (by
      intro s hs
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
      refine ⟨?_, hfix x hx⟩
      have hxX := (hFs x hx).1
      have h1 := hψ ⟨x, hxX⟩
      simp only at h1
      rw [h1]
      exact ⟨⟨x, hxX⟩, rfl⟩)
    rwa [Finset.card_image_of_injOn hinjOn] at hle

end CFSG.OddStandard.SmallF3.Omega
