module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Pos
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypeDict2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {F : PspFrame L} {t : G}
  {S : Subgroup G} {K1 K2 : Subgroup G} (h : Setup107 L t S)

namespace Setup107

section Case

variable
  (hFP : F.img (S ⊓ L) = QT0.originalSubgroup)
  (hQL : secQ K1 K2 ≤ L) (hQ : F.img (secQ K1 K2) = Q32)

include h hFP hQL hQ in
theorem exists_r {X : Subgroup G} (hXS : X ≤ S) (hX : IsElemAb2 X 5) (hXA : X ≠ secA t S L) :
    ∃ (B2 : Subgroup P45) (y2 : P45), Mo107.Model107 (F.imgS S S) B2 y2 ∧
      ∃ r ∈ S, F.phiG r = y2 ∧ r * r = 1 := by
  obtain ⟨-, hcard, hpre, hcomm, hsq⟩ := h.e32_data (F := F) hXS hX
  have hnle : ¬ F.imgS S X ≤ QT0.originalSubgroup := by
    intro hle
    apply hXA
    have hB : F.imgS S X = B0 := eq_B0_of_abelian hle hcomm (by rw [hcard]; norm_num)
    calc X = F.preS S (F.imgS S X) := hpre.symm
      _ = F.preS S B0 := by rw [hB]
      _ = secA t S L := (h.secA_eq hFP).symm
  obtain ⟨w, hwX, hwT0⟩ := SetLike.not_le_iff_exists.1 hnle
  obtain ⟨B2, y2, hM⟩ := Mo107.model107 (h.T0_le_imgS hFP) (h.imgS_le_A (F := F) S)
    (h.isPGroup_imgS (F := F) (le_refl S)) (h.imgS_mono (F := F) hXS hwX) hwT0
  obtain ⟨y, hyX, hyB, hyT0⟩ :=
    hM.meet (F.imgS S X) (h.imgS_mono (F := F) hXS) hcomm hsq hcard hnle
  refine ⟨B2, y2, hM, ?_⟩
  obtain ⟨x, hxX, hxS, hxy⟩ := (F.mem_imgS h.S_le_N).1 hyX
  have hx2 : x * x = 1 := hX.1.mul_self_eq_one hxX
  rcases (hM.mem_B2 y).1 hyB with ⟨hyQ, -⟩ | ⟨c, hc, hcy, hcx⟩
  · exact absurd (Mo107.Q32_le_T0 hyQ) hyT0
  · obtain ⟨l, hlQ, hl⟩ := h.exists_psi hQ hc
    have hqS : (l : G) ∈ S := h.secQ_le_S hFP hQL hQ hlQ
    have hcB2 : c ∈ B2 := (hM.mem_B2 c).2 (Or.inl ⟨hc, hcy⟩)
    have hcc : c * c = 1 := hM.sq c hcB2
    have hl2 : l * l = 1 := by
      apply F.ψ_injective
      rw [map_mul, hl, hcc, map_one]
    have hq2 : (l : G) * (l : G) = 1 := congrArg Subtype.val hl2
    have hcy' : c * y = y * c := by
      rw [← hcx]
      calc c * (c * y2) = c * c * y2 := (mul_assoc _ _ _).symm
        _ = y2 := by rw [hcc, one_mul]
        _ = c * y2 * c := by rw [mul_assoc, ← hcy, ← mul_assoc, hcc, one_mul]
    have hqx : (l : G) * x = x * (l : G) :=
      (h.comm_lift hxS hxy l).2 (by rw [hl]; exact hcy')
    refine ⟨(l : G) * x, S.mul_mem hqS hxS, ?_, ?_⟩
    · rw [F.phiG_mul (h.S_le_N hqS) (h.S_le_N hxS), F.phiG_psi l, hl, hxy, ← hcx, ← mul_assoc,
        hcc, one_mul]
    · calc (l : G) * x * ((l : G) * x) = (l : G) * (x * (l : G)) * x := by group
        _ = (l : G) * ((l : G) * x) * x := by rw [← hqx]
        _ = ((l : G) * (l : G)) * (x * x) := by group
        _ = 1 := by rw [hq2, hx2, one_mul]

include h hFP hQL hQ in
theorem case107 (hLg : IsPSp43 L) :
    secA t S L = JElem S ∨ ∃ r ∈ S, orderOf r = 2 ∧ InducesTypeSome L r 5 1 4 (-1) ∧
      secA2 t r K1 K2 ≠ secA t S L ∧
      ∀ X : Subgroup G, IsNormalE32In S X ↔ (X = secA t S L ∨ X = secA2 t r K1 K2) := by
  by_cases hD : ∀ X : Subgroup G, X ≤ S → IsElemAb2 X 5 → X = secA t S L
  · exact Or.inl (h.jElem_eq_secA hFP hD)
  · right
    push_neg at hD
    obtain ⟨X0, hX0S, hX0, hX0A⟩ := hD
    obtain ⟨B2, y2, hM, r, hrS, hrφ, hr2⟩ := h.exists_r hFP hQL hQ hX0S hX0 hX0A
    refine ⟨r, hrS, ?_, ?_, h.secA2_ne hFP hQL hQ hM hrS hrφ, ?_⟩
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (by rw [pow_two]; exact hr2) fun hr1 => hM.y2_out ?_
      rw [← hrφ, hr1, F.phiG_one]
      exact QT0.originalSubgroup.one_mem
    · refine (TyDict.inducesTypeSome_four_minus_iff hLg F r).2 ⟨h.S_le_N hrS, ?_⟩
      rw [← F.phiG_of_mem (h.S_le_N hrS), hrφ]
      exact hM.y2_inv
    · intro X
      constructor
      · rintro ⟨hXS, hX, hXn⟩
        obtain ⟨-, hcard, hpre, hcomm, hsq⟩ := h.e32_data (F := F) hXS hX
        have hnormX : ∀ g ∈ F.imgS S S, ∀ p ∈ F.imgS S X, g * p * g⁻¹ ∈ F.imgS S X :=
          h.normal_imgS hXn
        rcases hM.normal_elem (F.imgS S X) (h.imgS_mono (F := F) hXS) hcomm hsq hcard hnormX with
          he | he
        · left
          rw [← hpre, he, h.secA_eq hFP]
        · right
          rw [← hpre, he, h.secA2_eq hFP hQL hQ hM hrS hrφ]
      · rintro (rfl | rfl)
        · exact ⟨h.secA_le hFP, h.isElemAb2_secA hFP, h.normal_secA hFP hM⟩
        · refine ⟨?_, h.isElemAb2_secA2 hFP hQL hQ hM hrS hrφ hr2,
            h.normal_secA2 hFP hQL hQ hM hrS hrφ⟩
          rw [h.secA2_eq hFP hQL hQ hM hrS hrφ]
          exact h.preS_le B2

end Case

end Setup107

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
