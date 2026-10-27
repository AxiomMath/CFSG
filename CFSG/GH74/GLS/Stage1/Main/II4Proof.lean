module

public import CFSG.GH74.GLS.IVK.Lifted.Quat44
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Quat

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage1.Main

section Pure

theorem natCard_center_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center B) = Nat.card (Subgroup.center A) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective (f := (e : A →* B)) e.injective]

theorem conj_eq_one_of_mem_center' {Q : Type} [Group Q] {c : Q} (hc : c ∈ Subgroup.center Q) :
    MulAut.conj c = 1 := by
  ext x
  rw [MulAut.conj_apply, MulAut.one_apply]
  have := Subgroup.mem_center_iff.1 hc x
  calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [← this]
    _ = x := mul_inv_cancel_right x c

theorem mem_center_of_conj_eq_one {Q : Type} [Group Q] {c : Q} (h : MulAut.conj c = 1) :
    c ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := DFunLike.congr_fun h g
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem isSL2Or2A7_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsSL2Or2A7 A) :
    IsSL2Or2A7 B := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, (natCard_center_congr e).trans h2⟩
  rcases h1 with ⟨F, hF, hFin, hP, ⟨e1⟩⟩ | ⟨hq, hc, ⟨e7⟩⟩
  · exact Or.inl ⟨F, hF, hFin, hP, ⟨e.symm.trans e1⟩⟩
  · exact Or.inr ⟨LocalCores.isQuasisimple_of_mulEquiv e hq, (natCard_center_congr e).trans hc,
      ⟨(QuotientGroup.congr (Subgroup.center B) (Subgroup.center A) e.symm
        (Subgroup.map_center_eq e.symm)).trans e7⟩⟩

theorem sl2_or_2A7_of_rank_one
    {J : Type} [Group J] [Finite J] (hrank : CFSG.pRank 2 J ≤ 1)
    (hA : CFSG.IsQuasisimple (J ⧸ CFSG.oddCore J)) :
    ((∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧
        Nonempty ((J ⧸ CFSG.oddCore J) ≃* SL(2, F))) ∨
      (CFSG.IsQuasisimple (J ⧸ CFSG.oddCore J) ∧
        Nat.card (Subgroup.center (J ⧸ CFSG.oddCore J)) = 2 ∧
        Nonempty (((J ⧸ CFSG.oddCore J) ⧸ Subgroup.center (J ⧸ CFSG.oddCore J)) ≃*
          alternatingGroup (Fin 7)))) ∧
    Nat.card (Subgroup.center (J ⧸ CFSG.oddCore J)) = 2 := by
  classical
  obtain ⟨-, z, hz, -, -, hZcard, r, hr, -, -, hsimple, hnonab, hsylT, hlift⟩ :=
    ComponentClassification.UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover
      hrank hA
  refine ⟨?_, hZcard⟩
  have := hsimple
  obtain ⟨P⟩ : Nonempty (Sylow 2 ((J ⧸ CFSG.oddCore J) ⧸ Subgroup.center (J ⧸ CFSG.oddCore J))) :=
    inferInstance
  obtain ⟨hPd, -, -⟩ := hsylT P
  rcases GorensteinWalter.gorenstein_walter _ hnonab P ⟨2 ^ (r - 2), hPd⟩ with
    ⟨⟨e7⟩⟩ | ⟨p, k, hp, hpodd, h5, ⟨eP⟩⟩
  · exact Or.inr ⟨hA, hZcard, ⟨e7⟩⟩
  · have hk0 : k ≠ 0 := by
      rintro rfl
      simp at h5
    have hcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hchar : ringChar (GaloisField p k) ≠ 2 := by
      rw [ringChar.eq (GaloisField p k) p]
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hpodd) even_two
    obtain ⟨F, -, -⟩ := hlift (GaloisField p k) hchar
      (eP.trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        2 (GaloisField p k)))
    exact Or.inl ⟨GaloisField p k, inferInstance, inferInstance, by rw [hcard]; exact hpodd.pow,
      by rw [hcard]; exact h5, ⟨F⟩⟩

end Pure

section Hat

variable {G : Type} [Group G] [Finite G]

theorem ii4_44_thm
    : CFSG.GH74.GLS.Stage1.Thm2.Recip.II4_44 := by
  intro G _ _ hG t ht K hKC hrk
  have hquasi : CFSG.IsQuasisimple (Hat K) := TwoThin.isQuasisimple_hat hKC
  have hO : CFSG.oddCore ↥K = CFSG.pPrimeCore 2 ↥K :=
    (CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm
  let e : (↥K ⧸ CFSG.oddCore ↥K) ≃* Hat K := QuotientGroup.quotientMulEquivOfEq hO
  have hA : CFSG.IsQuasisimple (↥K ⧸ CFSG.oddCore ↥K) :=
    LocalCores.isQuasisimple_of_mulEquiv e.symm hquasi
  obtain ⟨hmain, hcard⟩ := sl2_or_2A7_of_rank_one hrk.le hA
  refine isSL2Or2A7_of_mulEquiv e ⟨?_, hcard⟩
  rcases hmain with ⟨F, hF, hFin, hodd, h5, ⟨eF⟩⟩ | h7
  · exact Or.inl ⟨F, hF, hFin, ⟨hodd, h5⟩,
      ⟨eF.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)⟩⟩
  · exact Or.inr h7

omit [Finite G] in
theorem mem_zStar_iff {K : Subgroup G} {x : G} (hx : x ∈ K) :
    x ∈ zStar K ↔ hatMk K ⟨x, hx⟩ ∈ Subgroup.center (Hat K) := by
  have h1 : x ∈ zStar K ↔ x ∈ cSec K := ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  rw [h1, ← phi_eq_one_iff K (le_normalizer hx), phi_of_mem K hx]
  exact ⟨mem_center_of_conj_eq_one, conj_eq_one_of_mem_center'⟩

theorem exists_sylow_inf {z : G} {S K : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)))
    (hKC : IsPCompIn 2 (centralizer ({z} : Set G)) K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K := by
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.2 hS
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := hKC.2
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.1
    (CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS' hKC.1 hsub)

theorem card_inf_zStar {S K : Subgroup G} (hS2 : IsPGroup 2 ↥S) (P : Sylow 2 ↥K)
    (hP : (P : Subgroup ↥K).map K.subtype = S ⊓ K)
    (hZ : Nat.card (Subgroup.center (Hat K)) = 2) :
    Nat.card ↥(S ⊓ zStar K) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pbar, hPbar⟩ := CFSG.GH74.GLS.IVK.Lifted.exists_sylow_hatImg ⟨P, hP⟩
  have hSK2 : IsPGroup 2 ↥(S ⊓ K) := hS2.to_inf_left
  have hZ2 : IsPGroup 2 ↥(Subgroup.center (Hat K)) :=
    IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num)
  have hZle : Subgroup.center (Hat K) ≤ (Pbar : Subgroup (Hat K)) := hZ2.le_sylow_of_normal Pbar
  rw [← hZ]
  have hzK : ∀ x : ↥(S ⊓ zStar K), (x : G) ∈ K := fun x => (Subgroup.mem_inf.1 x.2.2).1
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : ↥(S ⊓ zStar K) =>
      (⟨hatMk K ⟨x, hzK x⟩, (mem_zStar_iff (hzK x)).1 (Subgroup.mem_inf.1 x.2).2⟩ :
        ↥(Subgroup.center (Hat K)))) ⟨?_, ?_⟩)
  · intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (eq_of_hatMk_eq (S := S ⊓ K) inf_le_right hSK2
      ⟨(Subgroup.mem_inf.1 x.2).1, hzK x⟩ ⟨(Subgroup.mem_inf.1 y.2).1, hzK y⟩ this)
  · rintro ⟨c, hc⟩
    have hc' : c ∈ hatImg K (S ⊓ K) := hPbar ▸ hZle hc
    obtain ⟨a, ha, rfl⟩ := mem_hatImg.1 hc'
    have haz : (a : G) ∈ zStar K := (mem_zStar_iff a.2).2 hc
    exact ⟨⟨a, (Subgroup.mem_inf.1 ha).1, haz⟩, rfl⟩

end Hat

theorem ii4_4_4_center_thm
    : CFSG.GH74.GLS.Stage1.Thm3.Sec4.II4_4_4_center := by
  intro G _ _ hG z hz S K hS hKC hrk
  obtain ⟨P, hP⟩ := exists_sylow_inf hS hKC
  refine ⟨card_inf_zStar hS.isPGroup P hP (ii4_44_thm G hG z hz K hKC hrk).2, ?_⟩
  obtain ⟨n, hn⟩ := CFSG.GH74.GLS.IVK.Lifted.ii4_4_quat G hG z hz S K hS hKC hrk
  exact CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1.card_ge_of_quat hn

end CFSG.GH74.GLS.Stage1.Main

