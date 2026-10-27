module

public import CFSG.CGT.PushingUpLit.BHS.FourFourA
public import CFSG.CGT.PushingUpLit.BHS.FourThreeE

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

theorem four_twelve {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} (hA : A ∈ D)
    (hAc : A ∉ dCore P D M) :
    ∃ g ∈ P, ∃ L ∈ lamSet P D M, A ≤ L ∧ A ≤ conjSub g M ∧ ¬ L ≤ conjSub g M := by
  by_contra hcon
  push Not at hcon
  set D₀ : Set (Subgroup (MulAut V)) := {X | X ∈ D ∧ ∃ g ∈ P, ∃ L ∈ lamSet P D M, X ≤ L ∧
    X ≤ conjSub g M ∧ ¬ L ≤ conjSub g M} with hD₀
  set Ds : Set (Subgroup (MulAut V)) := D₀ ∪ dCore P D M with hDs
  set Dl : Set (Subgroup (MulAut V)) := {X | X ∈ D ∧ X ∉ Ds} with hDl
  have hDsP : ∀ X ∈ Ds, ∀ p ∈ P, conjSub p X ∈ Ds := by
    intro X hX p hp
    rcases hX with ⟨hXD, g, hg, L, hL, hXL, hXg, hLg⟩ | ⟨hXD, hXc⟩
    · refine Or.inl ⟨h.conj_mem X hXD p hp, p * g, P.mul_mem hp hg, conjSub p L,
        lamSet_conj h.toHyp41 hL hp, conjSub_mono p hXL, ?_, fun hle => hLg ?_⟩
      · rw [conjSub_mul]
        exact conjSub_mono p hXg
      · have := conjSub_mono p⁻¹ hle
        rwa [FourTwoTools.conjSub_inv_conjSub, ← conjSub_mul, inv_mul_cancel_left] at this
    · refine Or.inr ⟨h.conj_mem X hXD p hp, fun g hg => ?_⟩
      have h1 := conjSub_mono p (hXc (p⁻¹ * g) (P.mul_mem (P.inv_mem hp) hg))
      rwa [← conjSub_mul, mul_inv_cancel_left] at h1
  have hDlP : ∀ X ∈ Dl, ∀ p ∈ P, conjSub p X ∈ Dl := by
    intro X hX p hp
    refine ⟨h.conj_mem X hX.1 p hp, fun hXs => hX.2 ?_⟩
    have := hDsP _ hXs p⁻¹ (P.inv_mem hp)
    rwa [FourTwoTools.conjSub_inv_conjSub] at this
  have hAl : A ∈ Dl := by
    refine ⟨hA, fun hAs => ?_⟩
    rcases hAs with ⟨-, g, hg, L, hL, hAL, hAg, hLg⟩ | hAcore
    · exact hLg (hcon g hg L hL hAL hAg)
    · exact hAc hAcore
  have hcomm : ∀ X ∈ Dl, ∀ Y ∈ Ds, ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
    intro X hX Y hY
    have hYD : Y ∈ D := by
      rcases hY with hY | hY
      · exact hY.1
      · exact hY.1
    rcases h.toHyp41.four_eight_conj hX.1 hYD with hc | ⟨g, hg, hYg⟩
    · exact hc
    · exfalso
      have hgP : g ∈ P := (sup_le (h.le X hX.1) (h.le Y hYD)) hg
      have hYg' : Y = conjSub g X := hYg
      have := hDlP X hX g hgP
      rw [← hYg'] at this
      exact this.2 hY
  set T₁ : Set (Subgroup (MulAut V)) := {X | X ∈ dInter D T ∧ X ∈ Ds} with hT₁
  have hT₁sub : T₁ ⊆ dInter D T := fun X hX => hX.1
  have hDlM : ∀ X ∈ Dl, setNormalizer P T₁ ≤ M → X ≤ M := by
    intro X hX hN a ha
    refine hN (FourTwoTools.mem_setNormalizer_of_comm (h.le X hX.1 ha) fun B hB b hb => ?_)
    exact hcomm X hX B hB.2 a ha b hb
  have hN₁ : ¬ setNormalizer P T₁ ≤ M := by
    intro hN
    refine hAl.2 (Or.inr ⟨hA, fun g hg => ?_⟩)
    have h1 := hDlM _ (hDlP A hAl g⁻¹ (P.inv_mem hg)) hN
    have := conjSub_mono g h1
    rwa [FourTwoTools.conjSub_conjSub_inv] at this
  set F : Set (Set (Subgroup (MulAut V))) :=
    {S | S ⊆ dInter D T ∧ T₁ ⊆ S ∧ ¬ setNormalizer P S ≤ M} with hF
  have hT₁F : T₁ ∈ F := ⟨hT₁sub, subset_rfl, hN₁⟩
  obtain ⟨U, ⟨hUT, hT₁U, hNU⟩, hUmax⟩ :=
    Set.exists_max_image F Set.ncard (Set.toFinite _) ⟨T₁, hT₁F⟩
  have hmax : ∀ S : Set (Subgroup (MulAut V)), S ⊆ dInter D T → U ⊆ S →
      ¬ setNormalizer P S ≤ M → S = U := by
    intro S hS hUS hNS
    have hmem : S ∈ F := ⟨hS, hT₁U.trans hUS, hNS⟩
    exact (Set.eq_of_subset_of_ncard_le hUS (hUmax S hmem) (Set.toFinite _)).symm
  obtain ⟨⟨B, hBD, hBN, hBM⟩, ⟨A₀, hA₀D, hA₀M, hA₀N, hA₀U⟩, h3⟩ :=
    four_eleven h hV hUT hNU hmax
  have hL := h3 A₀ hA₀D hA₀M hA₀N hA₀U B hBD hBN hBM
  have hA₀s : A₀ ∈ Ds := Or.inl ⟨hA₀D, 1, P.one_mem, A₀ ⊔ B, hL.1, le_sup_left,
    by rw [conjSub_one]; exact hA₀M,
    by rw [conjSub_one]; exact fun hle => hBM (le_sup_right.trans hle)⟩
  have hNP : setNormalizer P U ≤ P := fun g hg => hg.1
  obtain ⟨T₀, hdT₀, hH⟩ := four_nine h hNP (fun X hX => ⟨hX.1, h.le_setNormalizer hUT hX⟩)
    (fun hsub => hBM (hsub ⟨hBD, hBN⟩).2)
  have hsub : ∀ X ∈ D, X ≤ setNormalizer P U → X ∈ Ds → X ∈ U := by
    intro X hXD hXN hXs
    obtain ⟨n, hn, hnX⟩ := Glauberman.exists_conj_le_of_isSylowOf hH.syl
      (isPGroup_of_isElemAbelian2 (h.elemAb X hXD)) hXN
    have hnD : conjSub n X ∈ D := h.conj_mem X hXD n (hNP hn)
    have hT : conjSub n X ∈ dInter D T := by
      rw [← hdT₀]
      exact ⟨hnD, hnX⟩
    have hnU : conjSub n X ∈ U := hT₁U ⟨hT, hDsP X hXs n (hNP hn)⟩
    have hn' : n⁻¹ ∈ setNormalizer P U := Subgroup.inv_mem _ hn
    have h2 := (hn'.2 (conjSub n X)).1 hnU
    rwa [FourTwoTools.conjSub_inv_conjSub] at h2
  exact hA₀U (hsub A₀ hA₀D hA₀N hA₀s)

end CFSG.CGT.PushingUpLit.BHS
