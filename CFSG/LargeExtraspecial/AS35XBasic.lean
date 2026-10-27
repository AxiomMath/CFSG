module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35LMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem DbarAsc_subset_Mbar_X : S.DbarAsc ⊆ S.Mbar := by
  rintro _ ⟨t, -, htM, rfl⟩
  exact ⟨⟨t, htM⟩, rfl⟩

theorem LbarAsc_le_Mbar_X : S.LbarAsc ≤ S.Mbar :=
  (closure_le _).mpr DbarAsc_subset_Mbar_X

theorem conj_mem_LbarAsc_X {m x : S.O} (hm : m ∈ S.Mbar) (hx : x ∈ S.LbarAsc) :
    m * x * m⁻¹ ∈ S.LbarAsc :=
  conj_mem_closure_of_conj_mem (fun _ hy => S.conj_mem_DbarAsc_L hm hy) x hx

theorem mul_self_of_mem_DbarAsc_X {d : S.O} (hd : d ∈ S.DbarAsc) : d * d = 1 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))

theorem isTypeA_of_mem_DbarAsc_X (hS : S.SixHyp) {d : S.O} (hd : d ∈ S.DbarAsc) :
    IsTypeA S.q (d : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact (S.fiveOne_two hS.sixFour hS.weak ht htM).1

theorem DbarAsc_subset_Dbar12_X (hS : S.SixHyp) : S.DbarAsc ⊆ S.Dbar12 :=
  fun _ hd => ⟨DbarAsc_subset_Mbar_X hd, isTypeA_of_mem_DbarAsc_X hS hd⟩

theorem comp12_subset_DbarAsc_X (hS : S.SixHyp) {τ : S.O} (hτ : τ ∈ S.DbarAsc) :
    S.comp12 τ ⊆ S.DbarAsc := by
  intro e he
  have hτ12 := DbarAsc_subset_Dbar12_X hS hτ
  obtain ⟨x, hx, rfl⟩ := S14.rootInvolutionComponentsInput S.Qt S.q S.q_nondegenerate S.Mbar
    S.s12_noNormalTwo_Mbar S.Dbar12 rfl τ hτ12 e he
  have hxM : x ∈ S.Mbar :=
    (closure_le _).mpr (fun y hy => (comp12_subset_Dbar12 hτ12 hy).1) hx
  exact S.conj_mem_DbarAsc_L hxM hτ

theorem orderOf_mul_le_four_X (hS : S.SixHyp) {d e : S.O} (hd : d ∈ S.DbarAsc)
    (he : e ∈ S.DbarAsc) : orderOf (d * e) ≤ 4 :=
  Dbar12_rootInvolution.1 d (DbarAsc_subset_Dbar12_X hS hd) e (DbarAsc_subset_Dbar12_X hS he)

theorem sq_mem_DbarAsc_X (hS : S.SixHyp) {d e : S.O} (hd : d ∈ S.DbarAsc) (he : e ∈ S.DbarAsc)
    (h4 : orderOf (d * e) = 4) : (d * e) ^ 2 ∈ S.DbarAsc := by
  have hdD := DbarAsc_subset_Dbar12_X hS hd
  have heD := DbarAsc_subset_Dbar12_X hS he
  have hdd : d * d = 1 := Subtype.ext hdD.2.2.2.1
  have hee : e * e = 1 := Subtype.ext heD.2.2.2.1
  have hde : d * e ≠ e * d := by
    intro h
    have h2 : (d * e) ^ 2 = 1 := by
      calc (d * e) ^ 2 = d * (e * d) * e := by rw [pow_two]; group
        _ = d * (d * e) * e := by rw [h]
        _ = (d * d) * (e * e) := by group
        _ = 1 := by rw [hdd, hee, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at this
    norm_num at this
  have hec : e ∈ S.comp12 d := Relation.ReflTransGen.single ⟨hdD, heD, hde⟩
  exact comp12_subset_DbarAsc_X hS hd (sq_mem_comp12 hdD hec h4)

theorem eq_one_of_central_X {y : S.O} (hy : y ∈ S.LbarAsc)
    (hc : ∀ x ∈ S.LbarAsc, x * y = y * x) (hyy : y * y = 1) : y = 1 := by
  let Ω : Subgroup S.O :=
    { carrier := {w | w ∈ S.LbarAsc ∧ (∀ x ∈ S.LbarAsc, x * w = w * x) ∧ w * w = 1}
      mul_mem' := by
        rintro a b ⟨ha, hac, haa⟩ ⟨hb, hbc, hbb⟩
        refine ⟨mul_mem ha hb, fun x hx => ?_, ?_⟩
        · calc x * (a * b) = (x * a) * b := (mul_assoc _ _ _).symm
            _ = (a * x) * b := by rw [hac x hx]
            _ = a * (x * b) := mul_assoc _ _ _
            _ = a * (b * x) := by rw [hbc x hx]
            _ = a * b * x := (mul_assoc _ _ _).symm
        · calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hbc a ha]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [haa, hbb, one_mul]
      one_mem' := ⟨one_mem _, fun x _ => by rw [mul_one, one_mul], mul_one 1⟩
      inv_mem' := by
        rintro a ⟨ha, hac, haa⟩
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
        show a⁻¹ ∈ S.LbarAsc ∧ (∀ x ∈ S.LbarAsc, x * a⁻¹ = a⁻¹ * x) ∧ a⁻¹ * a⁻¹ = 1
        rw [hai]
        exact ⟨ha, hac, haa⟩ }
  have hconj : ∀ m ∈ S.Mbar, ∀ w ∈ Ω, m * w * m⁻¹ ∈ Ω := by
    rintro m hm w ⟨hw, hwc, hww⟩
    refine ⟨conj_mem_LbarAsc_X hm hw, fun x hx => ?_, ?_⟩
    · have hx' : m⁻¹ * x * m⁻¹⁻¹ ∈ S.LbarAsc := conj_mem_LbarAsc_X (S.Mbar.inv_mem hm) hx
      rw [inv_inv] at hx'
      have h1 := hwc _ hx'
      calc x * (m * w * m⁻¹) = m * ((m⁻¹ * x * m) * w) * m⁻¹ := by group
        _ = m * (w * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
        _ = m * w * m⁻¹ * x := by group
    · calc m * w * m⁻¹ * (m * w * m⁻¹) = m * (w * w) * m⁻¹ := by group
        _ = 1 := by rw [hww, mul_one, mul_inv_cancel]
  have hΩ : Ω = ⊥ := by
    refine S.eq_bot_of_normalized_L (fun w hw => LbarAsc_le_Mbar_X hw.1) (fun m hm => ?_) ?_
    · rw [mem_normalizer_iff]
      intro w
      refine ⟨fun hw => hconj m hm w hw, fun hw => ?_⟩
      have := hconj m⁻¹ (S.Mbar.inv_mem hm) _ hw
      rwa [show m⁻¹ * (m * w * m⁻¹) * m⁻¹⁻¹ = w by group] at this
    · intro w
      refine ⟨1, Subtype.ext ?_⟩
      have hw : (w : S.O) * w = 1 := w.2.2.2
      simpa [pow_one, pow_two] using hw
  have hmem : y ∈ Ω := ⟨hy, hc, hyy⟩
  rw [hΩ, mem_bot] at hmem
  exact hmem

theorem eq_one_of_mem_center_X {c : S.LbarAsc} (hc : c ∈ center S.LbarAsc) (hcc : c * c = 1) :
    c = 1 := by
  refine Subtype.ext (eq_one_of_central_X c.2 (fun x hx => ?_) (congrArg Subtype.val hcc))
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hx⟩)

end Setting

end CFSG.LargeExtraspecial
