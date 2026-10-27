module

public import CFSG.LargeExtraspecial.AS35YRU33
public import CFSG.LargeExtraspecial.AS35TMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
  CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def conjL_YS (hst : S.Asc512Standing) : S.Mbar →* MulAut S.LbarAsc where
  toFun m :=
    { toFun := fun l => ⟨(m : S.O) * l * (m : S.O)⁻¹, hst.normal m m.2 l l.2⟩
      invFun := fun l => ⟨(m : S.O)⁻¹ * l * (m : S.O)⁻¹⁻¹, hst.normal _ (S.Mbar.inv_mem m.2) l l.2⟩
      left_inv := fun l => Subtype.ext (by simp only; group)
      right_inv := fun l => Subtype.ext (by simp only; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  map_one' := MulEquiv.ext fun l => Subtype.ext (by simp)
  map_mul' a b := MulEquiv.ext fun l => Subtype.ext (by
    change ((a * b : S.Mbar) : S.O) * l * ((a * b : S.Mbar) : S.O)⁻¹ =
      (a : S.O) * ((b : S.O) * l * (b : S.O)⁻¹) * (a : S.O)⁻¹
    rw [Subgroup.coe_mul]
    group)

theorem conjL_YS_apply (hst : S.Asc512Standing) (m : S.Mbar) (l : S.LbarAsc) :
    ((conjL_YS hst m l : S.LbarAsc) : S.O) = (m : S.O) * l * (m : S.O)⁻¹ :=
  rfl

theorem commute_of_conjL_eq_one (hst : S.Asc512Standing) {m : S.Mbar} (h : conjL_YS hst m = 1)
    (l : S.LbarAsc) : (m : S.O) * l = l * m := by
  have e : ((conjL_YS hst m l : S.LbarAsc) : S.O) = l := by rw [h]; rfl
  rw [conjL_YS_apply] at e
  calc (m : S.O) * l = (m : S.O) * l * (m : S.O)⁻¹ * m := by group
    _ = l * m := by rw [e]

theorem injective_of_center_YS {P H : Type*} [Group P] [Group H] [Finite P] (hP : IsPGroup 2 P)
    (f : P →* H) (c : P) (hc : ∀ x ∈ center P, x = 1 ∨ x = c) (hfc : f c ≠ 1) :
    Function.Injective f := by
  have : Group.IsNilpotent P := hP.isNilpotent
  refine (MonoidHom.ker_eq_bot_iff f).mp ?_
  by_contra hne
  have hnb := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ f.ker ⊓ center P, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hnb ((Subgroup.eq_bot_iff_forall _).mpr hcon)
  obtain ⟨hyk, hyc⟩ := mem_inf.mp hy
  rcases hc y hyc with h0 | h0
  · exact hy1 h0
  · exact hfc (h0 ▸ hyk)

theorem conjL_ne_one_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    {d : S.O} (hd : d ∈ S.DbarAsc) : conjL_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩ ≠ 1 := by
  intro h1
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hcen : (⟨d, subset_closure hd⟩ : S.LbarAsc) ∈ center S.LbarAsc := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (commute_of_conjL_eq_one hst h1 l).symm
  rw [hc, mem_bot] at hcen
  exact (isTypeA_of_mem_DbarAsc_YL hS hd).2.1
    (congrArg (fun x : S.LbarAsc => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) hcen)

theorem conjL_inj_pbar_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) :
    Function.Injective ((conjL_YS hst).comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype) := by
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  obtain ⟨htP, hext, -, hcent, -, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hP2 : IsPGroup 2 ((S.PbarAsc g).subgroupOf S.Mbar) :=
    IsPGroup.of_equiv hext.1 (subgroupOfEquivOfLe hPM).symm
  have : Finite ((S.PbarAsc g).subgroupOf S.Mbar) := Subtype.finite
  refine injective_of_center_YS hP2 _ ⟨⟨_, DbarAsc_subset_Mbar_YL htD⟩, mem_subgroupOf.mpr htP⟩
    (fun x hx => ?_) (conjL_ne_one_YS hS hst hnd htD)
  have hxc : ∀ z ∈ S.PbarAsc g, ((x : S.Mbar) : S.O) * z = z * ((x : S.Mbar) : S.O) := by
    intro z hz
    have := mem_center_iff.mp hx ⟨⟨z, hPM hz⟩, mem_subgroupOf.mpr hz⟩
    exact (congrArg (fun w : (S.PbarAsc g).subgroupOf S.Mbar => ((w : S.Mbar) : S.O))
      this).symm
  rcases hcent _ (mem_subgroupOf.mp x.2) hxc with h0 | h0
  · left
    exact Subtype.ext (Subtype.ext h0)
  · right
    exact Subtype.ext (Subtype.ext h0)

theorem width_le_four_of_u33_YS
    (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSU 3 3 1) :
    S.width ≤ 4 := by
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨e⟩ := equiv_of_lieModel hL
  have hAut : Nat.card (MulAut S.LbarAsc) = 12096 :=
    card_mulAut ((AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e)
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  have hPcard := (S14.asc512PbarStmt G S hS g ht htM).2.2.1
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hinj := conjL_inj_pbar_YS hS hst hnd ht htM
  have hdvd : Nat.card (S.PbarAsc g) ∣ 12096 := by
    rw [← hAut, ← Nat.card_congr (subgroupOfEquivOfLe hPM).toEquiv,
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hPcard] at hdvd
  by_contra h5
  push Not at h5
  have h7 : 2 ^ 7 ∣ 2 ^ (2 * S.width - 3) := Nat.pow_dvd_pow 2 (by omega)
  exact absurd (h7.trans hdvd) (by norm_num)

theorem width_ne_three_of_u33_YS
    (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSU 3 3 1) :
    S.width ≠ 3 := by
  intro h3
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨e⟩ := equiv_of_lieModel hL
  have hLcard : Nat.card S.LbarAsc = 6048 := by
    rw [Nat.card_congr ((AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e).toEquiv,
      AS35YR.card_QP]
  have hdim : finrank (ZMod 2) S.Qt = 2 * (2 + 1) := by rw [S.finrank_Qt_eq_two_mul_width, h3]
  refine AS35YR.not_dvd_card_orthogonalGroup S.q_nondegenerate (le_refl 2) hdim ?_
  rw [← hLcard]
  have h1 : Nat.card S.LbarAsc ∣ Nat.card S.O := Subgroup.card_subgroup_dvd_card S.LbarAsc
  have h2 : Nat.card S.O = Nat.card (TauCeti.QuadraticMap.orthogonalGroup S.q) := rfl
  rw [h2] at h1
  exact h1

theorem width_eq_four_of_u33_YS
    (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSU 3 3 1) :
    S.width = 4 := by
  have h4 := width_le_four_of_u33_YS hS hst hnd hL
  have h3 := width_ne_three_of_u33_YS hS hst hnd hL
  have := hS.three_le_width
  omega

end Setting

end CFSG.LargeExtraspecial
