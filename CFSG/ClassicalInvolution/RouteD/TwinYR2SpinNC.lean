module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinV

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Geom

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_frame_of_hypPair [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) {X : Submodule F V} (hX : PolarNondegOn Q X)
    (h5 : 5 ≤ Module.finrank F X) (P : HypPair Q) (hPe : P.e ∈ X) (hPf : P.f ∈ X) :
    ∃ G : OFrame Q, G.span ≤ X ∧ G.P = P := by
  have hX' : PolarNondegOn Q (X ⊓ P.perp) := hX.inf_perp P hPe hPf
  have hd := CFSG.ClassicalInvolution.Asc77.finrank_inf_perp_hypPair hQ P hPe hPf
  obtain ⟨P', hP'e, hP'f⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd hX' (by omega)
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP'e).2
  obtain ⟨h3, h4⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP'f).2
  refine ⟨⟨P, P', ⟨h1, h3, h2, h4⟩⟩, ?_, rfl⟩
  rintro _ ⟨Y, rfl⟩
  rw [Frame.incl_apply]
  exact X.add_mem (X.add_mem (X.add_mem (X.smul_mem _ hPe) (X.smul_mem _ hPf))
    (X.smul_mem _ (Submodule.mem_inf.mp hP'e).1)) (X.smul_mem _ (Submodule.mem_inf.mp hP'f).1)

theorem exists_frame_through [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) {X : Submodule F V} (hX : PolarNondegOn Q X)
    (h5 : 5 ≤ Module.finrank F X) {P : HypPair Q} (hPe : P.e ∈ X) (hPf : P.f ∈ X) {y : V}
    (hyX : y ∈ X) (hye : polar Q y P.e = 0) (hyf : polar Q y P.f = 0) :
    ∃ G : OFrame Q, G.span ≤ X ∧ G.e₁ = P.e + y - Q y • P.f ∧ G.f₁ = P.f := by
  have hye' : polar Q P.e y = 0 := by rw [polar_comm]; exact hye
  have hyf' : polar Q P.f y = 0 := by rw [polar_comm]; exact hyf
  have hQe : Q (P.e + y - Q y • P.f) = 0 := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      map_smul_eq_sq, P.Q_e, P.Q_f, hye', polar_add_left]
    simp only [polar_neg_right, polar_smul_right_eq, P.polar_ef, hyf]
    ring
  have hpol : polar Q (P.e + y - Q y • P.f) P.f = 1 := by
    rw [polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ef, hyf,
      polar_self_eq_zero P.Q_f]
    ring
  let P₁ : HypPair Q := HypPair.ofPolarEqOne hQe hpol
  have hP₁f : P₁.f = P.f := by
    show P.f - Q P.f • (P.e + y - Q y • P.f) = P.f
    rw [P.Q_f, zero_smul, sub_zero]
  have hP₁e : P₁.e = P.e + y - Q y • P.f := rfl
  have hmem1 : P₁.e ∈ X := by
    rw [hP₁e]
    exact X.sub_mem (X.add_mem hPe hyX) (X.smul_mem _ hPf)
  have hmem2 : P₁.f ∈ X := by
    rw [hP₁f]
    exact hPf
  obtain ⟨G, hG, hGP⟩ := exists_frame_of_hypPair hodd hQ hX h5 P₁ hmem1 hmem2
  refine ⟨G, hG, ?_, ?_⟩
  · have : G.e₁ = P₁.e := by rw [← hGP]
    rw [this, hP₁e]
  · have : G.f₁ = P₁.f := by rw [← hGP]
    rw [this, hP₁f]

theorem OFrame.e₁_mem_span (G : OFrame Q) : G.e₁ ∈ G.span :=
  ⟨!![1, 0; 0, 0], by simp [Frame.incl_apply]⟩

theorem OFrame.f₁_mem_span (G : OFrame Q) : G.f₁ ∈ G.span :=
  ⟨!![0, 0; 0, 1], by simp [Frame.incl_apply]⟩

theorem OFrame.e₂_mem_span (G : OFrame Q) : G.e₂ ∈ G.span :=
  ⟨!![0, -1; 0, 0], by simp [Frame.incl_apply]⟩

theorem OFrame.f₂_mem_span (G : OFrame Q) : G.f₂ ∈ G.span :=
  ⟨!![0, 0; 1, 0], by simp [Frame.incl_apply]⟩

theorem mem_perp_of_mem_hypPair_perp {G : OFrame Q} {w : V} (h1 : w ∈ G.P.perp)
    (h2 : w ∈ G.P'.perp) : w ∈ G.perp := by
  obtain ⟨a1, a2⟩ := HypPair.mem_perp.mp h1
  obtain ⟨a3, a4⟩ := HypPair.mem_perp.mp h2
  rw [Frame.mem_perp_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Frame.coords_apply, polar_comm Q w, a1, a2, a3, a4]

theorem exists_perp_frame [FiniteDimensional F V] (hQ : (polarBilin Q).Nondegenerate)
    {X : Submodule F V} (hX : PolarNondegOn Q X) (h5 : 5 ≤ Module.finrank F X) {G : OFrame Q}
    (hG : G.span ≤ X) :
    PolarNondegOn Q (X ⊓ G.P.perp ⊓ G.P'.perp) ∧ (X ⊓ G.P.perp ⊓ G.P'.perp) ≠ ⊥ := by
  obtain ⟨hPe, hPf, hP'e, hP'f⟩ := OFrame.vectors_mem hG
  have hP'e₁ : G.P'.e ∈ X ⊓ G.P.perp := ⟨hP'e, HypPair.mem_perp.mpr ⟨G.orth.ee, G.orth.fe⟩⟩
  have hP'f₁ : G.P'.f ∈ X ⊓ G.P.perp := ⟨hP'f, HypPair.mem_perp.mpr ⟨G.orth.ef, G.orth.ff⟩⟩
  refine ⟨(hX.inf_perp G.P hPe hPf).inf_perp G.P' hP'e₁ hP'f₁, fun h => ?_⟩
  have hd1 := CFSG.ClassicalInvolution.Asc77.finrank_inf_perp_hypPair hQ G.P hPe hPf
  have hd2 := CFSG.ClassicalInvolution.Asc77.finrank_inf_perp_hypPair hQ G.P' hP'e₁ hP'f₁
  rw [h, finrank_bot] at hd2
  omega

theorem La_neg_one_eq_of_commutes_frames [Finite F] [FiniteDimensional F V]
    (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate) (hdim : 9 ≤ Module.finrank F V)
    {F₁ F'' : OFrame Q}
    (hcomm : ∀ G : OFrame Q, G.span ≤ F₁.perp → Commutes F''.La.range G.La.range) :
    F''.La (-1) = F₁.La (-1) := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hW : PolarNondegOn Q F₁.perp := CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ F₁
  have hWdim : 5 ≤ Module.finrank F F₁.perp := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₁
    omega
  have hstar : ∀ G : OFrame Q, G.span ≤ F₁.perp →
      (∀ X Y, polar Q (G.incl X) (F''.incl Y) = 0) ∨ F''.La (-1) = G.La (-1) := by
    intro G hG
    have hc : F''.La (-1) * G.La (-1) = G.La (-1) * F''.La (-1) :=
      hcomm G hG _ ⟨-1, rfl⟩ _ ⟨-1, rfl⟩
    have hcent : ∀ A : SL(2, F), F''.La (-1) * G.La A = G.La A * F''.La (-1) := fun A =>
      hcomm G hG _ ⟨-1, rfl⟩ _ ⟨A, rfl⟩
    exact Frame.orth_or_eq h2 hc hcent
  by_cases hB : ∃ G : OFrame Q, G.span ≤ F₁.perp ∧ F''.La (-1) = G.La (-1)
  ·
    exfalso
    obtain ⟨G, hGW, hGeq⟩ := hB
    have hspan : F''.span = G.span := Frame.span_eq_of_La_neg_one_eq h2 hGeq
    obtain ⟨hnd, hne⟩ := exists_perp_frame hQ hW hWdim hGW
    obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hw₀P : w₀ ∈ G.P.perp := hw₀.1.2
    have hw₀P' : w₀ ∈ G.P'.perp := hw₀.2
    have hw₀W : w₀ ∈ F₁.perp := hw₀.1.1
    have hw₀e : polar Q w₀ G.P.e = 0 := by
      rw [polar_comm]
      exact (HypPair.mem_perp.mp hw₀P).1
    have hw₀f : polar Q w₀ G.P.f = 0 := by
      rw [polar_comm]
      exact (HypPair.mem_perp.mp hw₀P).2
    obtain ⟨hPe, hPf, -, -⟩ := OFrame.vectors_mem hGW
    obtain ⟨G', hG'W, hG'e, hG'f⟩ := exists_frame_through hodd hQ hW hWdim hPe hPf hw₀W hw₀e hw₀f
    rcases hstar G' hG'W with horth | heq
    · obtain ⟨Y, hY⟩ : G.f₁ ∈ F''.span := by rw [hspan]; exact G.f₁_mem_span
      have h1 := horth !![1, 0; 0, 0] Y
      rw [← CFSG.ClassicalInvolution.ModelFacts.Frame.e₁_eq_incl, hY] at h1
      have h3 : polar Q G'.e₁ G'.f₁ = 1 := G'.polar_e₁_f₁
      have h4 : G'.f₁ = G.f₁ := hG'f
      rw [h4] at h3
      rw [h3] at h1
      exact one_ne_zero h1
    · have hspan' : F''.span = G'.span := Frame.span_eq_of_La_neg_one_eq h2 heq
      have he' : G'.e₁ ∈ G.span := by
        rw [← hspan, hspan']
        exact G'.e₁_mem_span
      have hw₀span : w₀ ∈ G.span := by
        have : w₀ = G'.e₁ - G.e₁ + Q w₀ • G.f₁ := by
          rw [hG'e]
          show w₀ = G.P.e + w₀ - Q w₀ • G.P.f - G.P.e + Q w₀ • G.P.f
          abel
        rw [this]
        exact G.span.add_mem (G.span.sub_mem he' G.e₁_mem_span)
          (G.span.smul_mem _ G.f₁_mem_span)
      have hw₀perp : w₀ ∈ G.perp := mem_perp_of_mem_hypPair_perp hw₀P hw₀P'
      exact hw₀0 ((Submodule.disjoint_def.mp (Frame.isCompl_span_perp G).disjoint) w₀ hw₀span
        hw₀perp)
  · push Not at hB
    have hallorth : ∀ G : OFrame Q, G.span ≤ F₁.perp → ∀ X Y,
        polar Q (G.incl X) (F''.incl Y) = 0 := by
      intro G hG
      rcases hstar G hG with h | h
      · exact h
      · exact absurd h (hB G hG)
    have hle : F''.span ≤ F₁.span := by
      intro b hb
      obtain ⟨b₄, hb₄, b₀, hb₀, hbsum⟩ : ∃ b₄ ∈ F₁.span, ∃ b₀ ∈ F₁.perp, b₄ + b₀ = b := by
        have : b ∈ F₁.span ⊔ F₁.perp := by
          rw [(Frame.isCompl_span_perp F₁).sup_eq_top]
          trivial
        obtain ⟨b₄, hb₄, b₀, hb₀, h⟩ := Submodule.mem_sup.mp this
        exact ⟨b₄, hb₄, b₀, hb₀, h⟩
      suffices hb0 : b₀ = 0 by
        rw [← hbsum, hb0, add_zero]
        exact hb₄
      by_contra hne
      obtain ⟨G₀, hG₀⟩ := CFSG.ClassicalInvolution.Asc77.exists_frame_le_of_five_le hodd hQ hW hWdim
      obtain ⟨hnd, -⟩ := exists_perp_frame hQ hW hWdim hG₀
      obtain ⟨hPe, hPf, hP'e, hP'f⟩ := OFrame.vectors_mem hG₀
      obtain ⟨Y, hY⟩ := hb
      obtain ⟨Y₄, hY₄⟩ := hb₄
      have hb₀G : ∀ X, polar Q (G₀.incl X) b₀ = 0 := by
        intro X
        have h1 := hallorth G₀ hG₀ X Y
        rw [hY, ← hbsum, polar_add_right, ← hY₄] at h1
        have h3 : polar Q (G₀.incl X) (F₁.incl Y₄) = 0 :=
          (Frame.mem_perp_iff_forall_incl F₁).mp (hG₀ ⟨X, rfl⟩) Y₄
        rw [h3, zero_add] at h1
        exact h1
      have hb₀e : polar Q G₀.e₁ b₀ = 0 := by
        have := hb₀G !![1, 0; 0, 0]
        rwa [← CFSG.ClassicalInvolution.ModelFacts.Frame.e₁_eq_incl] at this
      have hb₀f : polar Q G₀.f₁ b₀ = 0 := by
        have := hb₀G !![0, 0; 0, 1]
        rwa [← CFSG.ClassicalInvolution.ModelFacts.Frame.f₁_eq_incl] at this
      have hb₀e₂ : polar Q G₀.e₂ b₀ = 0 := by
        have := hb₀G !![0, -1; 0, 0]
        rwa [← CFSG.ClassicalInvolution.ModelFacts.Frame.e₂_eq_incl] at this
      have hb₀f₂ : polar Q G₀.f₂ b₀ = 0 := by
        have := hb₀G !![0, 0; 1, 0]
        rwa [← CFSG.ClassicalInvolution.ModelFacts.Frame.f₂_eq_incl] at this
      have hb₀mem : b₀ ∈ F₁.perp ⊓ G₀.P.perp ⊓ G₀.P'.perp :=
        ⟨⟨hb₀, HypPair.mem_perp.mpr ⟨hb₀e, hb₀f⟩⟩, HypPair.mem_perp.mpr ⟨hb₀e₂, hb₀f₂⟩⟩
      obtain ⟨y, hy, hpy⟩ := hnd.exists_polar_ne_zero hb₀mem hne
      have hyW : y ∈ F₁.perp := hy.1.1
      have hye : polar Q y G₀.P.e = 0 := by
        rw [polar_comm]
        exact (HypPair.mem_perp.mp hy.1.2).1
      have hyf : polar Q y G₀.P.f = 0 := by
        rw [polar_comm]
        exact (HypPair.mem_perp.mp hy.1.2).2
      obtain ⟨G', hG'W, hG'e, -⟩ := exists_frame_through hodd hQ hW hWdim hPe hPf hyW hye hyf
      have hort := hallorth G' hG'W !![1, 0; 0, 0] Y
      rw [← CFSG.ClassicalInvolution.ModelFacts.Frame.e₁_eq_incl, hG'e, hY, ← hbsum,
        polar_add_right] at hort
      have h5 : polar Q (G₀.P.e + y - Q y • G₀.P.f) (F₁.incl Y₄) = 0 := by
        have hmem : G₀.P.e + y - Q y • G₀.P.f ∈ F₁.perp :=
          F₁.perp.sub_mem (F₁.perp.add_mem (hG₀ G₀.e₁_mem_span) hyW)
            (F₁.perp.smul_mem _ (hG₀ G₀.f₁_mem_span))
        exact (Frame.mem_perp_iff_forall_incl F₁).mp hmem Y₄
      rw [← hY₄, h5, zero_add, polar_sub_left, polar_add_left, polar_smul_left_eq] at hort
      rw [hb₀e, hb₀f] at hort
      apply hpy
      rw [polar_comm]
      linear_combination hort
    have heq : F''.span = F₁.span :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [Frame.finrank_span, Frame.finrank_span])
    exact Frame.La_neg_one_eq_of_span_eq heq

end Geom

section Main

open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.Models.Transfer

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem spinGroup_mfNC [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 9 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    {x x' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q))
    {𝓕 : Set (Subgroup (spinGroup Q))} (h𝓕perf : ∀ S ∈ 𝓕, S ≤ ⁅S, S⁆)
    (h𝓕surj : ∀ L ∈ fundSet Q, ∃ S ∈ 𝓕, S.map (spinAction Q) = L)
    {R'' : Subgroup (spinGroup Q)} (hR'' : R''.map (spinAction Q) ∈ fundSet Q)
    (hR''p : R'' ≤ ⁅R'', R''⁆)
    (hS : ∀ S ∈ 𝓕, Commutes S R → Commutes S R' → Commutes R'' S) : R'' = R ∨ R'' = R' := by
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨F₁, hF₁, hF₁', -, -⟩ := exists_pair_frame hodd hrange hZ (by omega) hproj hRp hR'p hR hR'
    hnc hnc' hne hx hcx hx1 hx' hcx' hx'1 hsame
  obtain ⟨i'', F'', hF'', -⟩ := hR''
  have hperfeq : ∀ S : Subgroup (spinGroup Q), S ≤ ⁅S, S⁆ → ⁅S, S⁆ = S := fun S hS =>
    le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) hS
  have hcomm : ∀ G : OFrame Q, G.span ≤ F₁.perp → Commutes F''.La.range G.La.range := by
    intro G hG
    obtain ⟨S, hS𝓕, hSG⟩ := h𝓕surj G.La.range ⟨G.La (-1), IsFundamental.of_frame G⟩
    have hperpF : ∀ (X Y : Matrix (Fin 2) (Fin 2) F), polar Q (G.incl X) (F₁.incl Y) = 0 :=
      fun X Y => (Frame.mem_perp_iff_forall_incl F₁).mp (hG ⟨X, rfl⟩) Y
    have h1 : Commutes S R := by
      rw [← CFSG.ClassicalInvolution.RouteD.Gaps.commutes_map_iff hker (hperfeq S (h𝓕perf S hS𝓕)),
        hSG, hF₁]
      exact commutes_La_range hperpF
    have h1' : Commutes S R' := by
      rw [← CFSG.ClassicalInvolution.RouteD.Gaps.commutes_map_iff hker (hperfeq S (h𝓕perf S hS𝓕)),
        hSG, hF₁']
      refine commutes_La_range (fun X Y => ?_)
      have hY : F₁.swap.incl Y ∈ F₁.span := by
        rw [← Frame.span_eq_swap_span]
        exact ⟨Y, rfl⟩
      obtain ⟨Y', hY'⟩ := hY
      rw [← hY']
      exact hperpF X Y'
    have h3 := hS S hS𝓕 h1 h1'
    have h4 := (CFSG.ClassicalInvolution.RouteD.Gaps.commutes_map_iff hker
      (hperfeq R'' hR''p)).mpr h3
    rwa [hF'', hSG] at h4
  have hi := La_neg_one_eq_of_commutes_frames hodd hQ hV hcomm
  rcases Frame.La_range_eq_or_eq_swap h2 hi with h | h
  · left
    exact CFSG.ClassicalInvolution.Asc77.ih8_eq_of_map_eq (spinAction Q) hker hR''p hRp
      (by rw [hF'', hF₁, h])
  · right
    exact CFSG.ClassicalInvolution.Asc77.ih8_eq_of_map_eq (spinAction Q) hker hR''p hR'p
      (by rw [hF'', hF₁', h])

end Main

section Spin

open CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.Transfer

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

omit [DecidableEq ι] in
theorem twinMFCommutantOn_of_spin (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 9 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinMFCommutantOn t ⟨spinGroup Q, D⟩ := by
  intro R R' x x' hd R'' hR'' hc
  exact spinGroup_mfNC hodd hQ hrange hZ hV hproj (hperf R hd.mem) (hperf R' hd.mem')
    (hcorr R hd.mem) (hcorr R' hd.mem') (hnc R hd.mem) (hnc R' hd.mem') hd.ne hd.hx hd.cx hd.nx
    hd.hx' hd.cx' hd.nx' hd.same (𝓕 := fundamentalSubgroups t D) hperf hsurj (hcorr R'' hR'')
    (hperf R'' hR'') hc

end Spin

end CFSG.ClassicalInvolution.RouteD.TwinY
