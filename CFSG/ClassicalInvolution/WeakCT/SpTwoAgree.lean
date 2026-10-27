module

public import CFSG.ClassicalInvolution.WeakCT.FieldTwoAux2

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
open Matrix
open scoped MatrixGroups

section FieldTwoSp

variable {F : Type} [Field F] {X : Type} [Group X]

private theorem center_sp_eq_bot_of_card_two (hF : Nat.card F = 2) :
    Subgroup.center (StatedSp 2 F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨c, -, hc⟩ := center_sp_scalar hg
  have hc1 : c = 1 := by
    rcases eq_zero_or_one_of_card_two hF (c : F) with h | h
    · exact absurd h c.ne_zero
    · exact Units.ext h
  apply SpExtras.mat_injective
  simp [SpExtras.mat_apply, hc, hc1]

private theorem injective_of_ker_le_center_sp (hF : Nat.card F = 2) {θ : StatedSp 2 F →* X}
    (hθ : θ.ker ≤ Subgroup.center (StatedSp 2 F)) : Function.Injective θ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := hθ hg
  rwa [center_sp_eq_bot_of_card_two hF, Subgroup.mem_bot] at h

private theorem comp_spBlock_injective (hF : Nat.card F = 2) {θ : StatedSp 2 F →* X}
    (hθ : θ.ker ≤ Subgroup.center (StatedSp 2 F)) (j : Fin 2) :
    Function.Injective (θ.comp (spBlock F j)) :=
  (injective_of_ker_le_center_sp hF hθ).comp (spBlock_injective j)

theorem commute_x_short_neg_long (a b : F) :
    Commute (Steinberg.Sp.x 2 F (Pi.single 0 1) a)
      (Steinberg.Sp.x 2 F (-Pi.single 1 1) b) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have h := commute_of_nil (D := rootDatum 2 F) (x := Steinberg.Sp.x 2 F)
    (C := Steinberg.Sp.commC) (O := O) hE rfl sp_cartan_01 sp_cartan_10
    (z := (1, 0)) (w := (0, -1)) (by decide) (by decide) (by decide) (by decide) a b
  rw [pair_one_zero, pair_zero_neg_one] at h
  exact h

theorem commute_x_neg_short_long (a b : F) :
    Commute (Steinberg.Sp.x 2 F (-Pi.single 0 1) a)
      (Steinberg.Sp.x 2 F (Pi.single 1 1) b) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have h := commute_of_nil (D := rootDatum 2 F) (x := Steinberg.Sp.x 2 F)
    (C := Steinberg.Sp.commC) (O := O) hE rfl sp_cartan_01 sp_cartan_10
    (z := (-1, 0)) (w := (0, 1)) (by decide) (by decide) (by decide) (by decide) a b
  rw [pair_neg_one_zero, pair_zero_one] at h
  exact h

theorem not_commute_x_short_long :
    ¬ Commute (Steinberg.Sp.x 2 F (Pi.single 0 1) (1 : F))
      (Steinberg.Sp.x 2 F (Pi.single 1 1) (1 : F)) := by
  intro h
  have hm : Commute (SpExtras.mat 2 F (Steinberg.Sp.x 2 F (Pi.single 0 1) (1 : F)))
      (SpExtras.mat 2 F (Steinberg.Sp.x 2 F (Pi.single 1 1) (1 : F))) :=
    h.map (SpExtras.mat 2 F)
  rw [show SpExtras.mat 2 F (Steinberg.Sp.x 2 F (Pi.single 0 1) (1 : F)) =
      1 + (1 : F) • (Matrix.single (Sum.inl 0) (Sum.inl 1) 1 -
        Matrix.single (Sum.inr 1) (Sum.inr 0) 1) from by
    rw [Steinberg.Sp.x_eq (SpExtras.stdVec_shortPos_eq (n := 2) (k := 0) (by decide)) (1 : F),
      SpExtras.mat_elt]
    rfl,
    show SpExtras.mat 2 F (Steinberg.Sp.x 2 F (Pi.single 1 1) (1 : F)) =
      Matrix.transvection (Sum.inl 1) (Sum.inr 1) (1 : F) from by
    rw [Steinberg.Sp.x_eq (SpExtras.stdVec_positiveLong_eq (n := 2) (k := 1) (by decide))
      (1 : F), SpExtras.mat_elt_positiveLong]] at hm
  have h_entry : (1 : F) = 0 := by
    have h := congrFun (congrFun hm.eq (Sum.inl 0)) (Sum.inr 1)
    simp [Matrix.transvection, Matrix.single_apply, Matrix.add_apply, Matrix.mul_apply] at h
  exact one_ne_zero h_entry

theorem not_commute_x_neg_short_neg_long :
    ¬ Commute (Steinberg.Sp.x 2 F (-Pi.single 0 1) (1 : F))
      (Steinberg.Sp.x 2 F (-Pi.single 1 1) (1 : F)) := by
  intro h
  have hm : Commute (SpExtras.mat 2 F (Steinberg.Sp.x 2 F (-Pi.single 0 1) (1 : F)))
      (SpExtras.mat 2 F (Steinberg.Sp.x 2 F (-Pi.single 1 1) (1 : F))) :=
    h.map (SpExtras.mat 2 F)
  rw [show SpExtras.mat 2 F (Steinberg.Sp.x 2 F (-Pi.single 0 1) (1 : F)) =
      1 + (1 : F) • (Matrix.single (Sum.inl 1) (Sum.inl 0) 1 -
        Matrix.single (Sum.inr 0) (Sum.inr 1) 1) from by
    rw [Steinberg.Sp.x_eq (SpExtras.stdVec_shortNeg_eq (n := 2) (k := 0) (by decide)) (1 : F),
      SpExtras.mat_elt]
    rfl,
    show SpExtras.mat 2 F (Steinberg.Sp.x 2 F (-Pi.single 1 1) (1 : F)) =
      Matrix.transvection (Sum.inr 1) (Sum.inl 1) (1 : F) from by
    rw [Steinberg.Sp.x_eq (SpExtras.stdVec_negativeLong_eq (n := 2) (k := 1) (by decide))
      (1 : F), SpExtras.mat_elt_negativeLong]] at hm
  have h_entry : (1 : F) = 0 := by
    have h := congrFun (congrFun hm.eq (Sum.inr 1)) (Sum.inl 0)
    simp [Matrix.transvection, Matrix.single_apply, Matrix.add_apply, Matrix.mul_apply] at h
  exact one_ne_zero h_entry

theorem spBlock_comm_upper_rev_lower (u : Fin 2) (a b : F) :
    Commute (spBlock F u (tv 0 1 a)) (spBlock F u.rev (tv 1 0 b)) := by
  fin_cases u
  · simpa [spBlock_upper, spBlock_lower] using commute_x_short_neg_long (F := F) a b
  · simpa [spBlock_upper, spBlock_lower] using
      (commute_x_neg_short_long (F := F) b a).symm

theorem spBlock_comm_lower_rev_upper (u : Fin 2) (a b : F) :
    Commute (spBlock F u (tv 1 0 a)) (spBlock F u.rev (tv 0 1 b)) := by
  fin_cases u
  · simpa [spBlock_upper, spBlock_lower] using commute_x_neg_short_long (F := F) a b
  · simpa [spBlock_upper, spBlock_lower] using
      (commute_x_short_neg_long (F := F) b a).symm

theorem spBlock_upper_not_comm_upper (u : Fin 2) :
    ¬ Commute (spBlock F u (tv 0 1 (1 : F))) (spBlock F u.rev (tv 0 1 (1 : F))) := by
  fin_cases u
  · simpa [spBlock_upper] using not_commute_x_short_long (F := F)
  · intro h
    exact not_commute_x_short_long (F := F) (by simpa [spBlock_upper] using h.symm)

theorem spBlock_lower_not_comm_lower (u : Fin 2) :
    ¬ Commute (spBlock F u (tv 1 0 (1 : F))) (spBlock F u.rev (tv 1 0 (1 : F))) := by
  fin_cases u
  · simpa [spBlock_lower] using not_commute_x_neg_short_neg_long (F := F)
  · intro h
    exact not_commute_x_neg_short_neg_long (F := F) (by simpa [spBlock_lower] using h.symm)

private theorem weyl_preimage_aux (hfin : Finite F) (hF : Nat.card F = 2) (u t : Fin 2)
    {θ₁ : StatedSp 2 F →* X} {θ₂ : SL(3, F) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center (StatedSp 2 F))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F))
    (hM : (θ₁.comp (spBlock F u)).range = (Bs F t).map θ₂) :
    ∃ A : SL(2, F), θ₁ (spBlock F u A) = θ₂ (blk F t (weylTwo F)) ∧ A * A = 1 ∧ A ≠ 1 := by
  classical
  have hinj₁ : Function.Injective (θ₁.comp (spBlock F u)) := comp_spBlock_injective hF h₁ u
  have hinj₂ : Function.Injective (θ₂.comp (blk F t)) := comp_blk_injective h₂ t
  have hx_mem : θ₂ (blk F t (weylTwo F)) ∈ (Bs F t).map θ₂ :=
    ⟨blk F t (weylTwo F), blk_mem_Bs t (weylTwo F), rfl⟩
  rw [← hM] at hx_mem
  obtain ⟨A, hA⟩ := hx_mem
  refine ⟨A, hA, ?_, ?_⟩
  · apply hinj₁
    have h : (θ₁.comp (spBlock F u)) (A * A) = 1 := by
      rw [map_mul, hA, ← map_mul, ← map_mul (blk F t), @weylTwo_mul_self F _ hfin hF,
        map_one (blk F t), map_one θ₂]
    simpa using h
  · intro h1
    have hx1 : θ₂ (blk F t (weylTwo F)) = 1 := by
      rw [← hA, h1]
      simp
    exact @weylTwo_ne_one F _ hfin hF (hinj₂ (by simpa using hx1))

private theorem weyl_closure_aux (hfin : Finite F) (hF : Nat.card F = 2) (u t : Fin 2)
    {θ₁ : StatedSp 2 F →* X} {θ₂ : SL(3, F) →* X}
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (Bs F t.rev).map θ₂,
      x * y = y * x)
    {A : SL(2, F)} (hA : θ₁ (spBlock F u A) = θ₂ (blk F t (weylTwo F)))
    {c : StatedSp 2 F} (hc : c ∈ (spBlock F u.rev).range)
    (hcA : Commute c (spBlock F u A)) :
    ∃ H : Subgroup X, (∀ y ∈ H, θ₁ c * y = y * θ₁ c) ∧ Bs F t ≤ H.comap θ₂ := by
  obtain ⟨a, ha⟩ := hc
  have hcθ_mem : θ₁ c ∈ (θ₁.comp (spBlock F u.rev)).range := by
    rw [← ha]
    exact ⟨a, rfl⟩
  have hcent_bs : ∀ y ∈ (Bs F t.rev).map θ₂, θ₁ c * y = y * θ₁ c :=
    fun y hy => hcomm (θ₁ c) hcθ_mem y hy
  have hcent_w : θ₁ c * θ₂ (blk F t (weylTwo F)) =
      θ₂ (blk F t (weylTwo F)) * θ₁ c := by
    rw [← hA]
    exact (hcA.map θ₁).eq
  let H : Subgroup X :=
    Subgroup.closure ((Bs F t.rev).map θ₂ ∪ {θ₂ (blk F t (weylTwo F))})
  have hHle : H ≤ Subgroup.centralizer ({θ₁ c} : Set X) := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hcent_bs y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hcent_w
  refine ⟨H, fun y hy => ?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mp (hHle hy) (θ₁ c) rfl
  · refine (@Bs_le_closure_rev_weylTwo F _ hfin hF t).trans ?_
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · exact Subgroup.subset_closure (Set.mem_union_left _ ⟨y, hy, rfl⟩)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.subset_closure (Set.mem_union_right _ rfl)

private theorem weyl_centralizer_aux (hfin : Finite F) (hF : Nat.card F = 2) (u t : Fin 2)
    {θ₁ : StatedSp 2 F →* X} {θ₂ : SL(3, F) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center (StatedSp 2 F))
    (hM : (θ₁.comp (spBlock F u)).range = (Bs F t).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (Bs F t.rev).map θ₂,
      x * y = y * x)
    {A : SL(2, F)} (hA : θ₁ (spBlock F u A) = θ₂ (blk F t (weylTwo F)))
    {c : StatedSp 2 F} (hc : c ∈ (spBlock F u.rev).range)
    (hcA : Commute c (spBlock F u A)) :
    ∀ z ∈ (spBlock F u).range, c * z = z * c := by
  have hinjθ₁ : Function.Injective θ₁ := injective_of_ker_le_center_sp hF h₁
  obtain ⟨H, hHcomm, hgen⟩ := weyl_closure_aux hfin hF u t hcomm hA hc hcA
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨y, hy, hzy⟩ : θ₁ (spBlock F u w) ∈ (Bs F t).map θ₂ := by
    rw [← hM]
    exact ⟨w, rfl⟩
  have hzH : θ₁ (spBlock F u w) ∈ H := by
    rw [← hzy]
    exact hgen hy
  have hcommz := hHcomm _ hzH
  apply hinjθ₁
  rw [map_mul, map_mul]
  exact hcommz

private theorem weyl_cases_aux (hfin : Finite F) (hF : Nat.card F = 2) (u t : Fin 2)
    {θ₁ : StatedSp 2 F →* X} {θ₂ : SL(3, F) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center (StatedSp 2 F))
    (hM : (θ₁.comp (spBlock F u)).range = (Bs F t).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (Bs F t.rev).map θ₂,
      x * y = y * x)
    {A : SL(2, F)} (hA : θ₁ (spBlock F u A) = θ₂ (blk F t (weylTwo F)))
    (hA1 : A ≠ 1) (hA2 : A * A = 1) :
    θ₁ (spBlock F u (weylTwo F)) = θ₂ (blk F t (weylTwo F)) := by
  classical
  have contra : ∀ c d : StatedSp 2 F, c ∈ (spBlock F u.rev).range →
      d ∈ (spBlock F u).range → c * d ≠ d * c → Commute c (spBlock F u A) → False :=
    fun c d hc hd hcd hcA =>
      hcd (weyl_centralizer_aux hfin hF u t h₁ hM hcomm hA hc hcA d hd)
  rcases @eq_one_or_tv_of_mul_self F _ hfin hF A hA2 with h1 | h2 | h3 | h4
  · exact absurd h1 hA1
  · exfalso
    refine contra (spBlock F u.rev (tv 1 0 (1 : F))) (spBlock F u (tv 1 0 (1 : F)))
      ⟨tv 1 0 (1 : F), rfl⟩ ⟨tv 1 0 (1 : F), rfl⟩ ?_ ?_
    · intro hcd
      exact spBlock_lower_not_comm_lower u ((commute_iff_eq _ _).2 hcd.symm)
    · rw [h2]
      exact (spBlock_comm_upper_rev_lower u 1 1).symm
  · exfalso
    refine contra (spBlock F u.rev (tv 0 1 (1 : F))) (spBlock F u (tv 0 1 (1 : F)))
      ⟨tv 0 1 (1 : F), rfl⟩ ⟨tv 0 1 (1 : F), rfl⟩ ?_ ?_
    · intro hcd
      exact spBlock_upper_not_comm_upper u ((commute_iff_eq _ _).2 hcd.symm)
    · rw [h3]
      exact (spBlock_comm_lower_rev_upper u 1 1).symm
  · simpa [h4] using hA

theorem weylTwo_agree_sp_sl3 (hF : Nat.card F = 2) (u t : Fin 2) {θ₁ : StatedSp 2 F →* X}
    {θ₂ : SL(3, F) →* X} (h₁ : θ₁.ker ≤ Subgroup.center (StatedSp 2 F))
    (h₂ : θ₂.ker ≤ Subgroup.center SL(3, F))
    (hM : (θ₁.comp (spBlock F u)).range = (Bs F t).map θ₂)
    (hcomm : ∀ x ∈ (θ₁.comp (spBlock F u.rev)).range, ∀ y ∈ (Bs F t.rev).map θ₂,
      x * y = y * x) :
    θ₁ (spBlock F u (weylTwo F)) = θ₂ (blk F t (weylTwo F)) := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨A, hA, hA2, hA1⟩ := weyl_preimage_aux hfin hF u t h₁ h₂ hM
  exact weyl_cases_aux hfin hF u t h₁ hM hcomm hA hA1 hA2

private theorem adjust_ab_aux (hF : Nat.card F = 2) (i : Fin 2) {θ₀ : StatedSp 2 F →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center (StatedSp 2 F)) {ρ : SL(2, F) →* X}
    (hrange : ρ.range = (θ₀.comp (spBlock F i)).range) :
    ∃ a b : SL(2, F), θ₀ (spBlock F i a) = ρ (tv 0 1 (1 : F)) ∧
      θ₀ (spBlock F i b) = ρ (tv 1 0 (1 : F)) ∧ a * a = 1 ∧ b * b = 1 := by
  classical
  let ι : SL(2, F) →* X := θ₀.comp (spBlock F i)
  have hι_inj : Function.Injective ι := comp_spBlock_injective hF hθ₀ i
  have hu_mem : ρ (tv 0 1 (1 : F)) ∈ ι.range := by
    rw [show ι.range = ρ.range from hrange.symm]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := hu_mem
  have hv_mem : ρ (tv 1 0 (1 : F)) ∈ ι.range := by
    rw [show ι.range = ρ.range from hrange.symm]
    exact ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := hv_mem
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · apply hι_inj
    have h : ι (a * a) = 1 := by
      rw [map_mul, ha, ← map_mul ρ (tv 0 1 (1 : F)) (tv 0 1 (1 : F)), tv01_mul_self hF,
        map_one]
    simpa using h
  · apply hι_inj
    have h : ι (b * b) = 1 := by
      rw [map_mul, hb, ← map_mul ρ (tv 1 0 (1 : F)) (tv 1 0 (1 : F)), tv10_mul_self hF,
        map_one]
    simpa using h

private theorem adjust_classify_aux (hfin : Finite F) (hF : Nat.card F = 2) (i : Fin 2)
    {θ₀ : StatedSp 2 F →* X} {ρ : SL(2, F) →* X} (hρ : Function.Injective ρ)
    (hw : ρ (weylTwo F) = θ₀ (spBlock F i (weylTwo F))) {a b : SL(2, F)}
    (ha : θ₀ (spBlock F i a) = ρ (tv 0 1 (1 : F)))
    (hb : θ₀ (spBlock F i b) = ρ (tv 1 0 (1 : F))) (ha2 : a * a = 1) (hb2 : b * b = 1) :
    (a = tv 0 1 (1 : F) ∧ b = tv 1 0 (1 : F)) ∨
      (a = tv 1 0 (1 : F) ∧ b = tv 0 1 (1 : F)) := by
  classical
  have haw : a ≠ weylTwo F := by
    intro h
    have h1 : ρ (tv 0 1 (1 : F)) = ρ (weylTwo F) := by
      rw [← ha, h]
      exact hw.symm
    exact @tv01_ne_weylTwo F _ hfin hF (hρ h1)
  have hbw : b ≠ weylTwo F := by
    intro h
    have h1 : ρ (tv 1 0 (1 : F)) = ρ (weylTwo F) := by
      rw [← hb, h]
      exact hw.symm
    exact @tv10_ne_weylTwo F _ hfin hF (hρ h1)
  have hab : a ≠ b := by
    intro h
    have h1 : ρ (tv 0 1 (1 : F)) = ρ (tv 1 0 (1 : F)) := by
      rw [← ha, h, hb]
    exact tv01_ne_tv10 (hρ h1)
  have ha_cases : a = tv 0 1 (1 : F) ∨ a = tv 1 0 (1 : F) := by
    rcases @eq_one_or_tv_of_mul_self F _ hfin hF a ha2 with h | h | h | h
    · exfalso
      have h1 : ρ (tv 0 1 (1 : F)) = ρ 1 := by
        rw [← ha, h, map_one (spBlock F i), map_one θ₀, map_one ρ]
      exact tv01_ne_one (hρ h1)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h haw
  have hb_cases : b = tv 0 1 (1 : F) ∨ b = tv 1 0 (1 : F) := by
    rcases @eq_one_or_tv_of_mul_self F _ hfin hF b hb2 with h | h | h | h
    · exfalso
      have h1 : ρ (tv 1 0 (1 : F)) = ρ 1 := by
        rw [← hb, h, map_one (spBlock F i), map_one θ₀, map_one ρ]
      exact tv10_ne_one (hρ h1)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hbw
  rcases ha_cases with hau | hav <;> rcases hb_cases with hbu | hbv
  · exact absurd (hau.trans hbu.symm) hab
  · exact Or.inl ⟨hau, hbv⟩
  · exact Or.inr ⟨hav, hbu⟩
  · exact absurd (hav.trans hbv.symm) hab

private theorem adjust_same_aux (hF : Nat.card F = 2) (i : Fin 2) {θ₀ : StatedSp 2 F →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center (StatedSp 2 F)) {ρ : SL(2, F) →* X}
    {a b : SL(2, F)} (ha : θ₀ (spBlock F i a) = ρ (tv 0 1 (1 : F)))
    (hb : θ₀ (spBlock F i b) = ρ (tv 1 0 (1 : F)))
    (hau : a = tv 0 1 (1 : F)) (hbv : b = tv 1 0 (1 : F)) :
    ∃ θ' : StatedSp 2 F →* X, θ'.ker ≤ Subgroup.center (StatedSp 2 F) ∧
      θ'.comp (spBlock F i) = ρ ∧ ∀ j, Function.Injective (θ'.comp (spBlock F j)) ∧
        (θ'.comp (spBlock F j)).range = (θ₀.comp (spBlock F j)).range := by
  refine ⟨θ₀, hθ₀, ?_, fun j => ⟨comp_spBlock_injective hF hθ₀ j, rfl⟩⟩
  apply hom_ext_sl2_two hF
  · have h := ha
    rw [hau] at h
    simpa using h
  · have h := hb
    rw [hbv] at h
    simpa using h

private theorem adjust_swap_aux (hF : Nat.card F = 2) (i : Fin 2) {θ₀ : StatedSp 2 F →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center (StatedSp 2 F)) {ρ : SL(2, F) →* X}
    {a b : SL(2, F)} (ha : θ₀ (spBlock F i a) = ρ (tv 0 1 (1 : F)))
    (hb : θ₀ (spBlock F i b) = ρ (tv 1 0 (1 : F)))
    (hav : a = tv 1 0 (1 : F)) (hbu : b = tv 0 1 (1 : F)) :
    ∃ θ' : StatedSp 2 F →* X, θ'.ker ≤ Subgroup.center (StatedSp 2 F) ∧
      θ'.comp (spBlock F i) = ρ ∧ ∀ j, Function.Injective (θ'.comp (spBlock F j)) ∧
        (θ'.comp (spBlock F j)).range = (θ₀.comp (spBlock F j)).range := by
  classical
  let θ' : StatedSp 2 F →* X := θ₀.comp (MulAut.conj (spW0 F)).toMonoidHom
  have hcomp : ∀ j : Fin 2, θ'.comp (spBlock F j) =
      (θ₀.comp (spBlock F j)).comp (invTransposeSL 2).toMonoidHom := by
    intro j
    rw [show θ' = θ₀.comp (MulAut.conj (spW0 F)).toMonoidHom from rfl]
    rw [MonoidHom.comp_assoc, spW0_block j, ← MonoidHom.comp_assoc]
  refine ⟨θ', ker_comp_mulEquiv_le_center hθ₀ (MulAut.conj (spW0 F)), ?_, fun j => ?_⟩
  · rw [hcomp i]
    apply hom_ext_sl2_two hF
    · rw [MonoidHom.comp_apply,
        show (invTransposeSL 2).toMonoidHom (tv 0 1 (1 : F)) =
          invTransposeSL 2 (tv 0 1 (1 : F)) from rfl, invTransposeSL_tv01_one hF]
      have h := ha
      rw [hav] at h
      simpa using h
    · rw [MonoidHom.comp_apply,
        show (invTransposeSL 2).toMonoidHom (tv 1 0 (1 : F)) =
          invTransposeSL 2 (tv 1 0 (1 : F)) from rfl, invTransposeSL_tv10_one hF]
      have h := hb
      rw [hbu] at h
      simpa using h
  · rw [hcomp j]
    exact ⟨(comp_spBlock_injective hF hθ₀ j).comp (invTransposeSL 2).injective,
      range_comp_mulEquiv (θ₀.comp (spBlock F j)) (invTransposeSL 2)⟩

theorem exists_adjust_sp_two (hF : Nat.card F = 2) (i : Fin 2) {θ₀ : StatedSp 2 F →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center (StatedSp 2 F)) {ρ : SL(2, F) →* X}
    (hρ : Function.Injective ρ) (hrange : ρ.range = (θ₀.comp (spBlock F i)).range)
    (hw : ρ (weylTwo F) = θ₀ (spBlock F i (weylTwo F))) :
    ∃ θ' : StatedSp 2 F →* X, θ'.ker ≤ Subgroup.center (StatedSp 2 F) ∧
      θ'.comp (spBlock F i) = ρ ∧ ∀ j, Function.Injective (θ'.comp (spBlock F j)) ∧
        (θ'.comp (spBlock F j)).range = (θ₀.comp (spBlock F j)).range := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨a, b, ha, hb, ha2, hb2⟩ := adjust_ab_aux hF i hθ₀ hrange
  rcases adjust_classify_aux hfin hF i hρ hw ha hb ha2 hb2 with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
  · exact adjust_same_aux hF i hθ₀ ha hb hau hbv
  · exact adjust_swap_aux hF i hθ₀ ha hb hav hbu

end FieldTwoSp

end CFSG.ClassicalInvolution.WeakCT
