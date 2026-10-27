module

public import CFSG.CGT.PushingUpLit.BHS7.Offenders
public import CFSG.CGT.PushingUpLit.BHS7.BlockV
public import CFSG.CGT.PushingUpLit.BHS7.Dedekind
public import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem commutator_mem_centralizer_of_commutator_autOn_eq_bot {V X Y : Subgroup Γ}
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) (hY : Y ≤ Subgroup.normalizer (V : Set Γ))
    (h : ⁅autOn X V, autOn Y V⁆ = ⊥) :
    ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
  intro x hx y hy
  have hxa : conjAct V ⟨x, hX hx⟩ ∈ autOn X V := mem_autOn_iff.mpr ⟨⟨x, hX hx⟩, hx, rfl⟩
  have hya : conjAct V ⟨y, hY hy⟩ ∈ autOn Y V := mem_autOn_iff.mpr ⟨⟨y, hY hy⟩, hy, rfl⟩
  have h1 : ⁅conjAct V ⟨x, hX hx⟩, conjAct V ⟨y, hY hy⟩⁆ ∈ (⁅autOn X V, autOn Y V⁆ : Subgroup _) :=
    Subgroup.commutator_mem_commutator hxa hya
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact (conjAct_comm_eq_one_iff V ⟨x, hX hx⟩ ⟨y, hY hy⟩).mp h1

theorem two_sixteen_block {G T F V U A : Subgroup Γ} (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hF : IsBTBlock G T F) (hV : IsElemAbelian 2 V) (hVQ : V ≤ pCoreOf 2 G)
    (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) (hFU : F ≤ U) (hAU : A ≤ U)
    (hsub : IsSubnormal F U) (hne : ⁅F, V⁆ ≠ ⊥) (hOff : IsOffG V A)
    (hcomm : ⁅autOn F V, autOn A V⁆ ≠ ⊥) :
    autOn A V ≤ Subgroup.normalizer (autOn F V : Set (MulAut ↥V)) ∧
      (blockW F ⊓ Subgroup.centralizer (A : Set Γ)).relIndex (blockW F) =
        (A ⊓ Subgroup.centralizer (blockW F : Set Γ)).relIndex A := by
  have hFV : F ≤ Subgroup.normalizer (V : Set Γ) := hF.le.trans hGV
  have hAV : A ≤ Subgroup.normalizer (V : Set Γ) := hOff.1
  have hOffA : @IsOff ↥V (commGroupOfElemAbelian hV) (autOn A V) :=
    (isOffG_iff_isOff_autOn hV hAV).mp hOff
  have hW : ⁅F, V⁆ = blockW F := commutator_eq_blockW hG hT hF hVQ hFV hne
  have hWV : blockW F ≤ V := hW ▸ commutator_le_of_le_normalizer hFV
  have hsubA : IsSubnormal (autOn F V) (autOn U V) := autOn_isSubnormal hsub
  have hFA : autOn F V ≤ autOn U V := autOn_le_autOn V hFU
  have hAA : autOn A V ≤ autOn U V := autOn_le_autOn V hAU
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hV.2 v v.2)
  have key : autOn A V ≤ Subgroup.normalizer (autOn F V : Set (MulAut ↥V)) ∧
      (fixV (autOn A V)).relIndex (commOn hV F) =
        (cenIn (autOn A V) (commOn hV F)).relIndex (autOn A V) := by
    rcases hF.type with ⟨n, hn2, hn⟩ | ⟨m, hm1, hm⟩
    · have hnat := isSLNatSection_autOn_of_isBTBlock hG hT hF hn hV hVQ hFV hne
      have h := two_sixteen_sl hV2 hn2 hOffA hAA hFA hsubA hnat hcomm
      exact ⟨h.1, h.2.2.2.2⟩
    · have hnat := isAltNatSection_autOn_of_isBTBlock hG hT hF hm hV hVQ hFV hne
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · have hm1' : m = 1 := by omega
        subst hm1'
        have h := two_sixteen_three hV2 hOffA hAA hsubA hnat hcomm
        exact ⟨h.1, h.2.2.2.2⟩
      · obtain ⟨hAN, -, β, θX, -, -, -, -, hrel⟩ :=
          two_sixteen_alt hV2 hm2 hOffA hAA hFA hsubA hnat hcomm
        exact ⟨hAN, hrel⟩
  refine ⟨key.1, ?_⟩
  have h1 := key.2
  rw [commOn_eq hV hFV, hW] at h1
  rw [relIndex_fixV_autOn hV hAV hWV, relIndex_cenIn_autOn hV hAV hWV] at h1
  exact h1

theorem offender_block_dichotomy {G T F V U A : Subgroup Γ} (hG : CharTwo G)
    (hT : IsSylowOf 2 T G) (hF : IsBTBlock G T F) (hV : IsElemAbelian 2 V)
    (hVQ : V ≤ pCoreOf 2 G) (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) (hFU : F ≤ U)
    (hAU : A ≤ U) (hsub : IsSubnormal F U) (hne : ⁅F, V⁆ ≠ ⊥) (hOff : IsOffG V A) :
    (∀ a ∈ A, ∀ f ∈ F, ⁅a, f⁆ ∈ Subgroup.centralizer (V : Set Γ)) ∨
      ((∀ a ∈ A, ∀ f ∈ F, ∃ f' ∈ F,
          (a * f * a⁻¹) * f'⁻¹ ∈ Subgroup.centralizer (V : Set Γ)) ∧
        (blockW F ⊓ Subgroup.centralizer (A : Set Γ)).relIndex (blockW F) =
          (A ⊓ Subgroup.centralizer (blockW F : Set Γ)).relIndex A) := by
  have hFV : F ≤ Subgroup.normalizer (V : Set Γ) := hF.le.trans hGV
  have hAV : A ≤ Subgroup.normalizer (V : Set Γ) := hOff.1
  by_cases hcomm : ⁅autOn F V, autOn A V⁆ = ⊥
  · left
    intro a ha f hf
    have h := commutator_mem_centralizer_of_commutator_autOn_eq_bot hFV hAV hcomm f hf a ha
    have h2 : ⁅a, f⁆ = ⁅f, a⁆⁻¹ := (commutatorElement_inv f a).symm
    rw [h2]
    exact Subgroup.inv_mem _ h
  · right
    obtain ⟨hN, hrel⟩ := two_sixteen_block hG hT hF hV hVQ hGV hFU hAU hsub hne hOff hcomm
    refine ⟨?_, hrel⟩
    intro a ha f hf
    exact conj_mem_mul_centralizer_of_autOn_normalizes hFV hAV hN a ha f hf

theorem commutator_le_of_offStarMin {G T F V U A : Subgroup Γ} (hG : CharTwo G)
    (hT : IsSylowOf 2 T G) (hF : IsBTBlock G T F) (hV : IsElemAbelian 2 V)
    (hVQ : V ≤ pCoreOf 2 G) (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) (hFU : F ≤ U)
    (hAU : A ≤ U) (hsub : IsSubnormal F U) (hne : ⁅F, V⁆ ≠ ⊥) (hA : A ∈ offStarMin V T) :
    ∀ a ∈ A, ∀ f ∈ F, ⁅a, f⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
  have hFV : F ≤ Subgroup.normalizer (V : Set Γ) := hF.le.trans hGV
  have hStar : IsOffStarG V A := hA.1.2
  have hOff : IsOffG V A := hStar.1
  have hAV : A ≤ Subgroup.normalizer (V : Set Γ) := hOff.1
  have hW : ⁅F, V⁆ = blockW F := commutator_eq_blockW hG hT hF hVQ hFV hne
  have hWV : blockW F ≤ V := hW ▸ commutator_le_of_le_normalizer hFV
  rcases offender_block_dichotomy hG hT hF hV hVQ hGV hFU hAU hsub hne hOff with h | ⟨hnorm, hrel⟩
  · exact h
  have hAW : A ≤ Subgroup.centralizer (blockW F : Set Γ) := by
    have hcA : A ⊓ Subgroup.centralizer (blockW F : Set Γ) = A := by
      rcases offender_card_lt_or_G hV hAV hOff hStar.2 hWV with hlt | ⟨hO, hwt⟩
      · exact absurd hrel (ne_of_lt hlt)
      · exact hA.2 _ ⟨inf_le_left.trans hA.1.1, hO, hwt⟩ inf_le_left
    exact inf_eq_left.mp hcA
  have hFC : F ⊓ Subgroup.centralizer (blockW F : Set Γ) ≤ Subgroup.centralizer (V : Set Γ) := by
    have := (bridge_data_of_isBTBlock hG hT hF hVQ hFV hne).2.2
    exact (this ▸ inf_le_right : F ⊓ Subgroup.centralizer (blockW F : Set Γ) ≤ _)
  have hWF : ∀ f ∈ F, ∀ w ∈ blockW F, f * w * f⁻¹ ∈ blockW F := fun f hf w hw =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockW F hf) w).mp hw
  intro a ha f hf
  obtain ⟨f', hf', hc⟩ := hnorm a ha f hf
  set c : Γ := (a * f * a⁻¹) * f'⁻¹ with hcdef
  have hfN : f ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set Γ) : Set Γ) :=
    B6.le_normalizer_centralizer hGV (hF.le hf)
  have hact : ∀ w ∈ blockW F, f' * w * f'⁻¹ = f * w * f⁻¹ := by
    intro w hw
    have h1 : f * w * f⁻¹ ∈ blockW F := hWF f hf w hw
    have h2 : f' * w * f'⁻¹ ∈ blockW F := hWF f' hf' w hw
    have h3 : (a * f * a⁻¹) * w * (a * f * a⁻¹)⁻¹ = f * w * f⁻¹ := by
      have e1 : a⁻¹ * w * a = w := by
        have := Subgroup.mem_centralizer_iff.mp (hAW (inv_mem ha)) w hw
        calc a⁻¹ * w * a = w * a⁻¹ * a := by rw [this]
          _ = w := by group
      have e2 : a * (f * w * f⁻¹) * a⁻¹ = f * w * f⁻¹ := by
        have := Subgroup.mem_centralizer_iff.mp (hAW ha) (f * w * f⁻¹) h1
        calc a * (f * w * f⁻¹) * a⁻¹ = (f * w * f⁻¹) * a * a⁻¹ := by rw [this]
          _ = f * w * f⁻¹ := by group
      calc (a * f * a⁻¹) * w * (a * f * a⁻¹)⁻¹
          = a * (f * (a⁻¹ * w * a) * f⁻¹) * a⁻¹ := by group
        _ = a * (f * w * f⁻¹) * a⁻¹ := by rw [e1]
        _ = f * w * f⁻¹ := e2
    have h4 : a * f * a⁻¹ = c * f' := by rw [hcdef]; group
    have h5 : c * (f' * w * f'⁻¹) * c⁻¹ = f' * w * f'⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hc (f' * w * f'⁻¹) (hWV h2)
      calc c * (f' * w * f'⁻¹) * c⁻¹ = (f' * w * f'⁻¹) * c * c⁻¹ := by rw [this]
        _ = f' * w * f'⁻¹ := by group
    calc f' * w * f'⁻¹ = c * (f' * w * f'⁻¹) * c⁻¹ := h5.symm
      _ = (a * f * a⁻¹) * w * (a * f * a⁻¹)⁻¹ := by rw [h4]; group
      _ = f * w * f⁻¹ := h3
  have hd : f⁻¹ * f' ∈ Subgroup.centralizer (V : Set Γ) := by
    refine hFC ⟨F.mul_mem (F.inv_mem hf) hf', ?_⟩
    show f⁻¹ * f' ∈ Subgroup.centralizer (blockW F : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := hact w hw
    calc w * (f⁻¹ * f') = (f⁻¹ * (f * w * f⁻¹) * f) * (f⁻¹ * f') := by group
      _ = f⁻¹ * (f' * w * f'⁻¹) * f * (f⁻¹ * f') := by rw [← this]
      _ = (f⁻¹ * f') * w := by group
  have hd' : f * (f⁻¹ * f') * f⁻¹ ∈ Subgroup.centralizer (V : Set Γ) :=
    (Subgroup.mem_normalizer_iff.mp hfN _).mp hd
  have hcomm_eq : ⁅a, f⁆ = c * (f * (f⁻¹ * f') * f⁻¹) := by
    rw [hcdef]; simp only [commutatorElement_def]; group
  rw [hcomm_eq]
  exact Subgroup.mul_mem _ hc hd'

end CFSG.CGT.PushingUpLit.BHS7
