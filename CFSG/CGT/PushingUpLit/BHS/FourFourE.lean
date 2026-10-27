module

public import CFSG.CGT.PushingUpLit.BHS.FourFourC
public import CFSG.CGT.PushingUpLit.BHS.FourFourB
public import CFSG.CGT.PushingUpLit.BHS.FourOne

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_inf_fixV_le_of_conj {S B : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ S ⊔ B)
    (hBq : IsQuadratic B) (hB : B = conjSub g S) : commV B ⊓ fixV S ≤ commV S := by
  intro y hy
  have hyB : y ∈ fixV B := hBq hy.1
  have hgy : g y = y := by
    have : y ∈ fixV (S ⊔ B) := by rw [fixV_sup]; exact ⟨hy.2, hyB⟩
    exact this g hg
  have hmap : commV B = (commV S).map g.toMonoidHom := by
    rw [hB]
    exact B19.commV_map_conj g S
  have hy' : y ∈ (commV S).map g.toMonoidHom := by
    rw [← hmap]
    exact hy.1
  obtain ⟨y', hy'S, hyy'⟩ := hy'
  have h2 : g y' = g y := by
    rw [hgy]
    exact hyy'
  have : y' = y := g.injective h2
  exact this ▸ hy'S

theorem mSet_subset_of_comm_ne_bot {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L S B : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    (hS : IsSylowOf 2 S L) (hB : B ∈ D) {g : MulAut V} (hg : g ∈ S ⊔ B) (hBg : B = conjSub g S)
    {b : MulAut V} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hy : commV (Subgroup.zpowers b) ⊓ fixV S ≠ ⊥) : mSet P M S ⊆ mSet P M B := by
  obtain ⟨-, -, hΛ2, -⟩ := hL
  have hSD : S ∈ D := ((hΛ2 S).2 hS).1
  rintro M' ⟨⟨p, hp, rfl⟩, hSM'⟩
  refine ⟨⟨p, hp, rfl⟩, ?_⟩
  by_contra hBM
  obtain ⟨⟨y, hym⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hy
  have hy1 : y ≠ 1 := fun e => hne (Subtype.ext e)
  have hbB : commV (Subgroup.zpowers b) ≤ commV B :=
    B19.commV_mono (Subgroup.zpowers_le.2 hb)
  have hyS : y ∈ commV S :=
    commV_inf_fixV_le_of_conj hg (h.quad B hB) hBg ⟨hbB hym.1, hym.2⟩
  obtain ⟨T', hST', hT'⟩ := h.exists_conj hp hS.2.1 hSM'
  have hSE : S ≤ ⨆ X ∈ dInter D T', X :=
    le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ dInter D T') => X) S
      ⟨hSD, hST'⟩ le_rfl
  have hEq : IsQuadratic (⨆ X ∈ dInter D T', X : Subgroup (MulAut V)) :=
    (four_seven hT'.toHyp41 hT'.syl).2
  have hyE : y ∈ fixV (⨆ X ∈ dInter D T', X : Subgroup (MulAut V)) :=
    hEq (B19.commV_mono hSE hyS)
  set Y : Subgroup V := fixV (⨆ X ∈ dInter D T', X : Subgroup (MulAut V)) ⊓
    commV (Subgroup.zpowers b) with hY
  have hyY : y ∈ Y := ⟨hyE, hym.1⟩
  have hHP : cenIn P Y ≤ P := cenIn_le P Y
  have hdT : dInter D T' ⊆ dInter D (cenIn P Y) := by
    intro X hX
    refine ⟨hX.1, fun x hx => ⟨h.le X hX.1 hx, fun u hu => ?_⟩⟩
    exact hu.1 x (le_iSup₂_of_le
      (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ dInter D T') => X) X hX le_rfl hx)
  have hBH : B ≤ cenIn P Y := fun x hx =>
    ⟨h.le B hB hx, fun u hu => (h.quad B hB (hbB hu.2)) x hx⟩
  have hM : ¬ dInter D (cenIn P Y) ⊆ dInter D (conjSub p M) := fun hsub =>
    hBM (hsub ⟨hB, hBH⟩).2
  obtain ⟨T₀, -, hH42⟩ := four_nine hT' hHP hdT hM
  obtain ⟨g', hg', Lh, hLh, hBLh, -, -⟩ := four_twelve hH42 hV ⟨hB, hBH⟩ (fun hc => by
    have := hc.2 1 (cenIn P Y).one_mem
    rw [conjSub_one] at this
    exact hBM (this.trans inf_le_left))
  obtain ⟨hLhH, ⟨nh, hnh, hSLh⟩, hΛh2, -⟩ := hLh
  have hBsyl : IsSylowOf 2 B Lh := (hΛh2 B).1 ⟨⟨hB, hBH⟩, hBLh⟩
  have hG : SylowGood Lh := fun S' hS' => by
    have hS'D : S' ∈ dInter D (cenIn P Y) := ((hΛh2 S').2 hS').1
    exact ⟨hH42.quad S' hS'D, hH42.card_eq S' hS'D⟩
  have hk9 := hSLh.commV_zpowers_inf_fixV hnh hG hBsyl hb hb1
  have hyLh : y ∈ fixV Lh := fun x hx => (hLhH hx).2 y hyY
  have hmem : y ∈ commV (Subgroup.zpowers b) ⊓ fixV Lh := ⟨hym.1, hyLh⟩
  rw [hk9] at hmem
  exact hy1 (Subgroup.mem_bot.1 hmem)

theorem mSet_eq_of_subset_conj {P M S B : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ P)
    (hB : B = conjSub g S) (hsub : mSet P M S ⊆ mSet P M B) : mSet P M S = mSet P M B := by
  have himg : mSet P M B = conjSub g '' mSet P M S := by
    rw [hB]
    exact mSet_conjSub hg
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [himg, Set.ncard_image_of_injective _ (FourTwoTools.conjSub_injective g)]

theorem exists_comm_sylow {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    {B : Subgroup (MulAut V)} (hB : B ∈ D) :
    ∃ A ∈ D, A ≤ L ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  by_contra hno
  push Not at hno
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, hΛ3⟩ := hL'
  have hSD : ∀ S, IsSylowOf 2 S L → S ∈ D := fun S hS => ((hΛ2 S).2 hS).1
  have hG : SylowGood L := fun S hS => ⟨h.quad S (hSD S hS), h.card_eq S (hSD S hS)⟩
  have hconj : ∀ S, IsSylowOf 2 S L → ∃ g ∈ S ⊔ B, B = conjSub g S := by
    intro S hS
    rcases h.toHyp41.four_eight_conj (hSD S hS) hB with hc | ⟨g, hg, hBg⟩
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := hno S (hSD S hS) hS.1
      exact hne (hc a ha b hb)
    · exact ⟨g, hg, hBg⟩
  have hM : ∀ S, IsSylowOf 2 S L → ∀ b ∈ B, b ≠ 1 → commV (Subgroup.zpowers b) ⊓ fixV S ≠ ⊥ →
      mSet P M S = mSet P M B := by
    intro S hS b hb hb1 hy
    obtain ⟨g, hg, hBg⟩ := hconj S hS
    have hgP : g ∈ P := (sup_le (h.le S (hSD S hS)) (h.le B hB)) hg
    exact mSet_eq_of_subset_conj hgP hBg
      (mSet_subset_of_comm_ne_bot h hV hL hS hB hg hBg hb hb1 hy)
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h.ne_bot B hB (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  obtain ⟨v, hv⟩ : ∃ v : V, b₀ v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hb₀1 (MulEquiv.ext hcon)
  have hv₀ : b₀ v * v⁻¹ ≠ 1 := fun e => hv (mul_inv_eq_one.1 e)
  obtain ⟨S₀, hS₀, hv₀S⟩ := hSL.exists_sylow_mem_fixV hn1 hG (b₀ v * v⁻¹)
  have hS₀B : mSet P M S₀ = mSet P M B := by
    refine hM S₀ hS₀ b₀ hb₀ hb₀1 fun hbot => hv₀ ?_
    have hmem : b₀ v * v⁻¹ ∈ commV (Subgroup.zpowers b₀) ⊓ fixV S₀ :=
      ⟨G6.mem_commV_of_mem (Subgroup.mem_zpowers b₀) v, hv₀S⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hB' : ∀ b ∈ B, ∀ w : V, b w * w⁻¹ ∈ fixV S₀ := by
    intro b hb w
    by_cases h1 : b w * w⁻¹ = 1
    · rw [h1]
      exact one_mem _
    · have hb1 : b ≠ 1 := fun e => h1 (by simp [e])
      obtain ⟨S, hS, hvS⟩ := hSL.exists_sylow_mem_fixV hn1 hG (b w * w⁻¹)
      have hne : commV (Subgroup.zpowers b) ⊓ fixV S ≠ ⊥ := fun hbot => h1 (by
        have hmem : b w * w⁻¹ ∈ commV (Subgroup.zpowers b) ⊓ fixV S :=
          ⟨G6.mem_commV_of_mem (Subgroup.mem_zpowers b) w, hvS⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.1 hmem)
      have heq := hM S hS b hb hb1 hne
      have hSS : S = S₀ := by
        by_contra hSS
        exact hΛ3 S ((hΛ2 S).2 hS) S₀ ((hΛ2 S₀).2 hS₀) hSS (heq.trans hS₀B.symm)
      rw [← hSS]
      exact hvS
  obtain ⟨g₀, hg₀, hBg₀⟩ := hconj S₀ hS₀
  have hcB : commV B ≤ fixV S₀ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, w, rfl⟩
    exact hB' x hx w
  have hcBq : commV B ≤ fixV B := h.quad B hB
  have hSB : commV S₀ ≤ commV B := by
    intro u hu
    have hmap : commV B = (commV S₀).map g₀.toMonoidHom := by
      rw [hBg₀]
      exact B19.commV_map_conj g₀ S₀
    have h1 : g₀ u ∈ commV B := by
      rw [hmap]
      exact ⟨u, hu, rfl⟩
    have h2 : g₀ (g₀ u) = g₀ u := by
      have : g₀ u ∈ fixV (S₀ ⊔ B) := by
        rw [fixV_sup]
        exact ⟨hcB h1, hcBq h1⟩
      exact this g₀ hg₀
    have h3 : g₀ u = u := g₀.injective h2
    rw [← h3]
    exact h1
  have hcomm : ∀ a ∈ S₀, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    ext v
    simp only [MulAut.mul_apply]
    have hxa : a (b v * v⁻¹) = b v * v⁻¹ := hB' b hb v a ha
    have hyb : b (a v * v⁻¹) = a v * v⁻¹ :=
      (hcBq (hSB (G6.mem_commV_of_mem ha v))) b hb
    have hbv : b v = (b v * v⁻¹) * v := by group
    have hav : a v = (a v * v⁻¹) * v := by group
    calc a (b v) = a ((b v * v⁻¹) * v) := by rw [← hbv]
      _ = (b v * v⁻¹) * ((a v * v⁻¹) * v) := by rw [map_mul, hxa, ← hav]
      _ = (a v * v⁻¹) * ((b v * v⁻¹) * v) := by rw [mul_left_comm]
      _ = (a v * v⁻¹) * b v := by rw [← hbv]
      _ = b ((a v * v⁻¹) * v) := by rw [map_mul, hyb]
      _ = b (a v) := by rw [← hav]
  obtain ⟨a, ha, b, hb, hne⟩ := hno S₀ (hSD S₀ hS₀) hS₀.1
  exact hne (hcomm a ha b hb)

end CFSG.CGT.PushingUpLit.BHS
