module

public import CFSG.CGT.PushingUpLit.BHS.ThreeSixC
public import CFSG.CGT.PushingUpLit.BHS.NatSL2
public import CFSG.CGT.PushingUpLit.BHS.FourOneD

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

structure LocMax (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (M : Subgroup (MulAut V)) : Prop where
  hyp : Hyp41 P D
  M_le : M ≤ P
  uniq : ∀ A ∈ D, A ≤ M → ∀ g ∈ P, A ≤ conjSub g M → conjSub g M = M
  self : ∀ g ∈ P, conjSub g M = M → g ∈ M
  cen : ∀ R : Subgroup (MulAut V), R ≤ M → IsPGroup 2 R → cenIn P (fixV R) ≤ M

namespace LocMax

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {M : Subgroup (MulAut V)}

omit [Finite V] in
theorem mem_of_le_conjSub (h : LocMax P D M) {A : Subgroup (MulAut V)} (hA : A ∈ D) (hAM : A ≤ M)
    {g : MulAut V} (hg : g ∈ P) (hle : A ≤ conjSub g M) : g ∈ M :=
  h.self g hg (h.uniq A hA hAM g hg hle)

omit [Finite V] in
theorem mem_of_conjSub_inv_le (h : LocMax P D M) {A : Subgroup (MulAut V)} (hA : A ∈ D)
    (hAM : A ≤ M) {x : MulAut V} (hx : x ∈ P) (hle : conjSub x⁻¹ A ≤ M) : x ∈ M := by
  refine h.mem_of_le_conjSub hA hAM hx ?_
  have := conjSub_mono x hle
  rwa [FourTwoTools.conjSub_conjSub_inv] at this

theorem commute_of_isPGroup (h : LocMax P D M) {X Y : Subgroup (MulAut V)} (hX : X ∈ D)
    (hY : Y ∈ D) (hXY : IsPGroup 2 ↥(X ⊔ Y)) : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  obtain ⟨T', hT', hle⟩ := Glauberman.exists_isSylowOf_ge (K := P) hXY
    (sup_le (h.hyp.le X hX) (h.hyp.le Y hY))
  exact h.hyp.four_seven_pairs hT' X ⟨hX, le_sup_left.trans hle⟩ Y ⟨hY, le_sup_right.trans hle⟩

omit [Finite V] in
theorem fixV_eq_of_le (h : LocMax P D M) {A B' : Subgroup (MulAut V)} (hA : A ∈ D) (hBA : B' ≤ A)
    (hB0 : B' ≠ ⊥) : fixV B' = fixV A := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB0
  have h1 : fixV B' ≤ fixV (Subgroup.zpowers b) :=
    fixV_anti ((Subgroup.zpowers_le).2 hb)
  have h2 := h.hyp.fixV_eq A hA b (hBA hb) (fun h' => hb1 (Subtype.ext h'))
  exact le_antisymm (h1.trans h2.le) (fixV_anti hBA)


theorem sup_mem_lamSet_of_caseII (h : LocMax P D M)
    (hV : ∀ v : V, v ^ 2 = 1) {A B : Subgroup (MulAut V)} (hA : A ∈ D) (hAM : A ≤ M)
    (hB : B ∈ D) (hBM : ¬ B ≤ M) (hnc : ¬ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hII : ∀ l ∈ A ⊔ B, A ⊔ conjSub l A < A ⊔ B → conjSub l A ≤ M) :
    A ⊔ B ∈ lamSet P D M := by
  set L : Subgroup (MulAut V) := A ⊔ B with hL
  have hAL : A ≤ L := le_sup_left
  have hBL : B ≤ L := le_sup_right
  have hLP : L ≤ P := sup_le (h.hyp.le A hA) (h.hyp.le B hB)
  have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian2 (h.hyp.elemAb A hA)
  have hLM : ¬ L ≤ M := fun hLM => hBM (hBL.trans hLM)
  have hgen : ∀ x ∈ L, x ∉ M → A ⊔ conjSub x A = L := by
    intro x hx hxM
    have hxA : conjSub x A ≤ L := by
      have := conjSub_mono x hAL
      rwa [conjSub_self_of_mem hx] at this
    by_contra hne
    have hlt : A ⊔ conjSub x A < L := lt_of_le_of_ne (sup_le hAL hxA) hne
    have h1 : conjSub x A ≤ M := hII x hx hlt
    refine hxM ?_
    have h2 : x⁻¹ ∈ M := h.mem_of_conjSub_inv_le hA hAM (hLP (L.inv_mem hx))
      (by simpa using h1)
    simpa using M.inv_mem h2
  obtain ⟨T₀, hT₀, hAT₀⟩ := Glauberman.exists_isSylowOf_ge hA2 hAL
  have hT₀M : T₀ ≤ M := by
    have hU : T₀ ⊓ M = T₀ := by
      refine Nine.eq_of_inf_normalizer_le hT₀.2.1 inf_le_left fun t ht => ?_
      obtain ⟨htT, htn⟩ := ht
      have h1 : conjSub t (T₀ ⊓ M) = T₀ ⊓ M := conjSub_eq_of_mem_normalizer htn
      have hAU : A ≤ T₀ ⊓ M := le_inf hAT₀ hAM
      have h2 : conjSub t A ≤ M := by
        have := conjSub_mono t hAU
        rw [h1] at this
        exact this.trans inf_le_right
      have h3 : t⁻¹ ∈ M := h.mem_of_conjSub_inv_le hA hAM (hLP (hT₀.1 (T₀.inv_mem htT)))
        (by simpa using h2)
      exact ⟨htT, by simpa using M.inv_mem h3⟩
    exact inf_eq_left.1 hU
  have hmin : MinPar L T₀ (L ⊓ M) :=
    { syl := hT₀
      not_normal := fun hn => by
        obtain ⟨x, hxL, hxM⟩ := IsConcreteLE.not_le_iff_exists.1 hLM
        have h1 : conjSub x T₀ = T₀ := conjSub_eq_of_mem_normalizer (hn hxL)
        have h2 : L ≤ T₀ := by
          rw [← hgen x hxL hxM]
          exact sup_le hAT₀ ((conjSub_mono x hAT₀).trans h1.le)
        exact hnc (h.commute_of_isPGroup hA hB (hT₀.2.1.to_le h2))
      le_M := le_inf hT₀.1 hT₀M
      lt_P := lt_of_le_of_ne inf_le_left fun e => hLM (by rw [← e]; exact inf_le_right)
      max := fun X hTX hXL => by
        refine le_inf hXL.le ?_
        by_contra hXM
        obtain ⟨x, hxX, hxM⟩ := IsConcreteLE.not_le_iff_exists.1 hXM
        have hAX : A ≤ X := hAT₀.trans hTX
        have h1 : L ≤ X := by
          rw [← hgen x (hXL.le hxX) hxM]
          exact sup_le hAX ((conjSub_mono x hAX).trans (conjSub_self_of_mem hxX).le)
        exact hXL.not_ge h1 }
  have hel : IsElemAbelian2 A := h.hyp.elemAb A hA
  have hcard : Nat.card V ≤ wt A := (h.hyp.card_eq A hA).le
  have hlt : ∀ B' : Subgroup (MulAut V), B' ≤ A → B' ≠ ⊥ → B' ≠ A → wt B' < wt A := by
    intro B' hBA hB0 hne
    unfold wt
    rw [h.fixV_eq_of_le hA hBA hB0]
    exact Nat.mul_lt_mul_of_pos_right (FourOneTools.card_lt_of_le_of_ne hBA hne) Nat.card_pos
  have hnt : ∃ g ∈ L, ∃ z ∈ fixV T₀, g z ≠ z := by
    by_contra hno
    push Not at hno
    have hLc : L ≤ cenIn P (fixV T₀) := fun g hg => ⟨hLP hg, fun u hu => hno g hg u hu⟩
    exact hLM (hLc.trans (h.cen T₀ hT₀M hT₀.2.1))
  obtain ⟨n, hn1, hAn, hVc, hfix, hzp, hSL⟩ := three_five hV hmin hAT₀ hel hcard hlt hnt
    (fun x hx hxM => hgen x hx fun hxM' => hxM ⟨hx, hxM'⟩)
  have hcardL := hSL.card_L hn1
  have hAsyl : IsSylowOf 2 A L := by
    refine ⟨hAL, hA2, ?_⟩
    have h1 := Subgroup.relIndex_mul_card A L
    rw [inf_eq_left.2 hAL, hAn, hcardL] at h1
    have h2 : A.relIndex L = 4 ^ n - 1 :=
      Nat.eq_of_mul_eq_mul_right (m := 2 ^ n) (by positivity) (by rw [h1]; ring)
    rw [h2]
    rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ : 2 ∣ 4 ^ n := dvd_pow (by norm_num) (by omega)
    have := Nat.one_le_pow n 4 (by norm_num)
    omega
  have hΛ2 : ∀ X : Subgroup (MulAut V), X ∈ dInter D L ↔ IsSylowOf 2 X L := by
    intro X
    constructor
    · rintro ⟨hXD, hXL⟩
      rcases h.hyp.four_eight_conj hA hXD with hc | ⟨g, hg, hXg⟩
      · have hnc' : ∃ a ∈ A, ∃ b ∈ B, a * b ≠ b * a := by
          by_contra hno
          push Not at hno
          exact hnc hno
        rcases h.hyp.four_eight_main hA hB hnc' hXD hXL (fun c hc' a ha => (hc a ha c hc').symm)
          with hz | hXA
        · exfalso
          refine h.hyp.ne_bot X hXD (eq_bot_iff.2 fun c hc' => ?_)
          have := hSL.center_eq_bot hn1 (hXL hc') (fun y hy => (hz c hc' y hy).symm)
          rw [this]
          exact (Subgroup.mem_bot).2 rfl
        · rwa [hXA]
      · have hgL : g ∈ L := (sup_le hAL hXL) hg
        have := isSylowOf_conjSub hAsyl g
        rw [conjSub_self_of_mem hgL] at this
        rw [hXg]
        exact this
    · intro hXs
      obtain ⟨x, hx, hXx⟩ := IsSLNatSection.sylow_conj hAsyl hXs
      exact ⟨hXx ▸ h.hyp.conj_mem A hA x (hLP hx), hXs.1⟩
  refine ⟨hLP, ⟨n, hn1, hSL⟩, hΛ2, fun X hX Y hY hXY heq => ?_⟩
  have hXs := (hΛ2 X).1 hX
  have hYs := (hΛ2 Y).1 hY
  obtain ⟨l, hl, hXl⟩ := IsSLNatSection.sylow_conj hAsyl hXs
  have hXM : X ≤ conjSub l M := by rw [hXl]; exact conjSub_mono l hAM
  have hmem : conjSub l M ∈ mSet P M X := ⟨⟨l, hLP hl, rfl⟩, hXM⟩
  rw [heq] at hmem
  have hLl : L ≤ conjSub l M := by
    rw [← hSL.sylow_sup_eq hn1 hXs hYs hXY]
    exact sup_le hXM hmem.2
  refine hLM ?_
  have := conjSub_mono l⁻¹ hLl
  rwa [FourTwoTools.conjSub_inv_conjSub, conjSub_self_of_mem (L.inv_mem hl)] at this

end LocMax

end CFSG.CGT.PushingUpLit.BHS
