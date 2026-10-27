module

public import CFSG.GH74.E2.BoxT5Hii
public import CFSG.GH74.E2.BoxT5Core
public import CFSG.GH74.E2.BoxB5

public section

namespace CFSG.GH74.E2.Box

open Subgroup CFSG.GH74.GLS CFSG.Open

section Final

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem two_le_openPRank (H : Subgroup G) {u v : G} (hu : u ∈ H) (hv : v ∈ H)
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v) :
    2 ≤ CFSG.Open.pRank 2 H := by
  obtain ⟨V, hVcl, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hu2 hv2 huv hne
  have hVH : V ≤ H := hVcl.trans ((Subgroup.closure_le H).2 (by
    intro x hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv))
  have hVe : CFSG.Open.IsElemAbelian 2 V :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).1 hV
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨V, hVH, hVe, by rw [hVcard]; norm_num⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num : 1 < 2)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

theorem Setup.two_le_pRank
    (S : Setup K) (hL : L33Tables) : 2 ≤ CFSG.Open.pRank 2 K := by
  have hT : SD16Tables ↥K := by
    rcases S.shape with h | h
    · exact hL.tables ↥K h
    · exact S.m11.tables ↥K h
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨e⟩ := hT.sylow T
  obtain ⟨u, v, hu, hv, huv, hcomm⟩ := exists_two_comm_involutions_of_sd16 _ e
  refine two_le_openPRank K u.2 v.2 ?_ ?_ ?_ ?_
  · rw [Subgroup.orderOf_coe]; exact hu
  · rw [Subgroup.orderOf_coe]; exact hv
  · exact congrArg Subtype.val hcomm
  · intro h
    exact huv (Subtype.ext h)


theorem no_conj_comp_of_T5
    (hT5 : AschbacherTheorem5Statement) (hL : L33Tables) (S : Setup K)
    (g : G) : ¬ IsCompIn (centralizer (K : Set G)) (conjugate K g) := by
  intro hK'
  have hpair : CommPair K K (conjugate K g) :=
    ⟨ConjOf.refl K, ⟨g, rfl⟩, hK', isCompIn_symm S.term hK'⟩
  have key : CFSG.Open.pRank 2 K = 1 :=
    thm5_two_factors hT5 hpair.commute S.quasi (S.quasi_of ⟨g, rfl⟩) (hpair.ne S)
      (fun N hN hodd => hpair.odd_normal_bot S N hN hodd)
      (fun h hh => ⟨hpair.map_conj_normalizer S hh (Or.inl rfl),
        hpair.map_conj_normalizer S hh (Or.inr rfl)⟩)
      (fun P Q hP hQ t g h2 htc c1 c2 => hpair.hi S hP hQ h2 htc c1 c2)
      (fun P hP g hX => hpair.hii S hP hX) (hpair.normalizer_ne_top S)
  have := S.two_le_pRank hL
  omega

theorem noLocalGL23_T5
    (hT5 : AschbacherTheorem5Statement) (hAS : AschbacherStandardL33)
    (hASM : AschbacherStandardM11) (hComp : ComponentList) (hD : K0Data) (hD3 : K0Data3)
    (hP : PumpUpData) (hM : M11Tables) (hL : L33Tables) : NoLocalGL23 := by
  intro G _ _ hH t K c hd hsh hinner hSD
  have hterm := termComp_of_shapeLM hComp hP hH hd.order_t hd.comp hsh
  have S : Setup K := ⟨hH, hD, hD3, hComp, hM, hsh, hterm, isCompCen_quasisimple hd.comp⟩
  exact false_of_b5 hAS hASM hH hd.order_t hd.comp hsh hterm
    (fun g => no_conj_comp_of_T5 hT5 hL S g) hSD

end Final

end CFSG.GH74.E2.Box
