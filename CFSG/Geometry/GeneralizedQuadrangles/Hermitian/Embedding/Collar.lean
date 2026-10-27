module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Closure3

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Closure

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
variable {K : Type*} [Field K] [Fintype K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem ncard_fullLinesThrough_collar_mul (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι A ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K A = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXA : X ≤ A)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) {y : V} (hyX : y ∈ collar c ι X) :
    (fullLinesThrough Γ (collar c ι X) y).ncard * ℓ = s + ℓ := by
  classical
  have hy0 : c y = 0 := hyX.1
  have hXH : X ≤ perpSpan c ι y := hyX.2
  have hHA : perpSpan c ι y ≤ A := perpSpan_le_ambient hι y
  haveI : FiniteDimensional K (perpSpan c ι y) := Submodule.finiteDimensional_of_le hHA
  have hHdim := finrank_perpSpan_add_one hP hT hι hy0
  have hH4 : finrank K (perpSpan c ι y) = 4 := by omega
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  let T : Submodule K W := X ⊔ ι y
  let H : Submodule K W := perpSpan c ι y
  have hXne : X ≠ ι y := fun h => hXP ⟨y, hy0, h.symm⟩
  have hT2 : finrank K T = 2 :=
    finrank_sup_eq_two_of_finrank_eq_one hX1 (hι.finrank_point y hy0) hXne
  have hTleH : T ≤ H :=
    sup_le hXH (submodule_le_perpSpan ⟨hy0, by simp⟩)
  let Mset : Set (Submodule K W) := {M | T ≤ M ∧ M ≤ H ∧ finrank K M = 3}
  have hMsetcard : Mset.ncard = s + 1 := by
    have hgap : finrank K H = finrank K T + 2 := by rw [hH4, hT2]
    have h := card_submodule_between_two (K := K) (W := W) (U := T) (X := H) hTleH hgap
    have hEq : Mset = {M : Submodule K W | T ≤ M ∧ M ≤ H ∧
        finrank K M = finrank K T + 1} := by
      ext M
      simp only [Mset, Set.mem_setOf_eq, hT2]
    have h1 : Nat.card {M : Submodule K W // T ≤ M ∧ M ≤ H ∧
        finrank K M = finrank K T + 1} = s + 1 := by
      rw [h, card_field_eq_of_isProjGQ hP hT c hdeg hι]
    have h2 : {M : Submodule K W | T ≤ M ∧ M ≤ H ∧
        finrank K M = finrank K T + 1}.ncard = s + 1 := by
      rw [← Nat.card_coe_set_eq]
      exact h1
    rw [hEq, h2]
  haveI : Finite A := Module.finite_of_finite K
  haveI hfinSub : Finite {M : Submodule K W // M ≤ A} := by
    haveI : Finite (Submodule K A) :=
      Finite.of_injective (fun L : Submodule K A => (L : Set A)) SetLike.coe_injective
    exact Finite.of_equiv (Submodule K A) (Submodule.MapSubtype.orderIso A).toEquiv
  haveI : Finite Mset :=
    Finite.of_injective (fun M : Mset => (⟨M.1, M.2.2.1.trans hHA⟩ :
      {M : Submodule K W // M ≤ A}))
      (fun a b h => Subtype.ext
        (congrArg (fun x : {M : Submodule K W // M ≤ A} => (x : Submodule K W)) h))
  letI : Fintype Mset := Fintype.ofFinite Mset
  let Lset : Set V := {L | c L = 1 ∧ Γ.Adj y L}
  have hLsetcard : Lset.ncard = t + 1 := by
    have hEq : Lset = Γ.neighborSet y := by
      ext L
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        exact ⟨color_eq_one_of_adj_of_color_eq_zero hy0 h, h⟩
    rw [hEq, ncard_neighborSet, hdeg y, if_pos hy0]
  letI : Fintype Lset := Fintype.ofFinite Lset
  let k : Submodule K W → ℕ := fun M => {L : V | L ∈ Lset ∧ ι L ≤ M}.ncard
  have hrow : ∀ L : Lset, (Finset.univ.bipartiteAbove
      (fun (L : Lset) (M : Mset) => ι L.1 ≤ M.1) L).card = 1 := by
    intro L
    obtain ⟨hL1, hyL⟩ := L.2
    have hXnotL : ¬ X ≤ ι L.1 := by
      intro hle
      obtain ⟨x, hxL, hxX⟩ := hι.full L.1 hL1 X hX1 hle
      exact hXP ⟨x, color_eq_zero_of_adj_of_color_eq_one hL1 hxL, hxX⟩
    have hM0dim : finrank K ↥(X ⊔ ι L.1) = 3 :=
      finrank_sup_eq_three_of_finrank_eq_one_of_not_le hX1
        (hι.finrank_line L.1 hL1) hXnotL
    have hM0mem : X ⊔ ι L.1 ∈ Mset := by
      refine ⟨?_, ?_, hM0dim⟩
      · refine sup_le le_sup_left ?_
        exact ((hι.adj_iff y L.1 hy0 hL1).1 hyL).trans le_sup_right
      · refine sup_le hXH ?_
        rw [show H = perpSpan c ι y from rfl, perpSpan_eq_iSup_neighborFinset hP hT hι hy0]
        exact le_iSup_of_le L.1 (le_iSup_of_le (by simpa using hyL) le_rfl)
    have huniq : ∀ M : Submodule K W, M ∈ Mset → ι L.1 ≤ M → M = X ⊔ ι L.1 := by
      intro M hM hle
      haveI : FiniteDimensional K M := Submodule.finiteDimensional_of_le (hM.2.1.trans hHA)
      have hsup : X ⊔ ι L.1 ≤ M :=
        sup_le (le_trans le_sup_left hM.1) hle
      exact (Submodule.eq_of_le_of_finrank_eq hsup (by rw [hM.2.2, hM0dim])).symm
    refine Finset.card_eq_one.mpr ⟨⟨X ⊔ ι L.1, hM0mem⟩, ?_⟩
    ext M
    simp only [Finset.mem_bipartiteAbove, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hM
      exact Subtype.ext (huniq M.1 M.2 hM)
    · intro hM
      rw [hM]
      exact le_sup_right
  have hcol : ∀ M : Mset, (Finset.univ.bipartiteBelow
      (fun (L : Lset) (M : Mset) => ι L.1 ≤ M.1) M).card = k M.1 := by
    intro M
    have h1 : (Finset.univ.bipartiteBelow
        (fun (L : Lset) (M : Mset) => ι L.1 ≤ M.1) M).card =
        Nat.card {L : Lset // ι L.1 ≤ M.1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [Finset.bipartiteBelow]
    rw [h1]
    have h2 : Nat.card {L : Lset // ι L.1 ≤ M.1} =
        Nat.card {L : V // L ∈ Lset ∧ ι L ≤ M.1} :=
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun L : V => L ∈ Lset)
        (fun L => ι L ≤ M.1))
    rw [h2]
    exact Nat.card_coe_set_eq _
  have hsum : (∑ M : Mset, k M.1) = t + 1 := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun (L : Lset) (M : Mset) => ι L.1 ≤ M.1)
      (s := (Finset.univ : Finset Lset)) (t := (Finset.univ : Finset Mset))
    have h' : (∑ L : Lset, (Finset.univ.bipartiteAbove
          (fun (L : Lset) (M : Mset) => ι L.1 ≤ M.1) L).card) =
        ∑ M : Mset, k M.1 := by
      rw [h]
      exact Finset.sum_congr rfl fun M _ => hcol M
    rw [← h']
    calc ∑ L : Lset, (Finset.univ.bipartiteAbove
          (fun (L : Lset) (M : Mset) => ι L.1 ≤ M.1) L).card
        = ∑ _L : Lset, (1 : ℕ) := Finset.sum_congr rfl fun L _ => hrow L
      _ = Fintype.card Lset := by simp
      _ = t + 1 := by rw [Set.fintypeCard_eq_ncard, hLsetcard]
  have hk1 : ∀ M ∈ Mset, 1 ≤ k M := by
    intro M hM
    obtain ⟨hTM, hMH, hM3⟩ := hM
    obtain ⟨L, hL1, hyL, hLM⟩ :=
      exists_line_le_of_le_perpSpan hP hT c hdeg hι hsec hℓ h5 hy0
        (le_trans le_sup_right hTM) hMH hM3
    have hpos : 0 < k M := by
      change 0 < {L : V | L ∈ Lset ∧ ι L ≤ M}.ncard
      exact (Set.ncard_pos (s := {L : V | L ∈ Lset ∧ ι L ≤ M})).mpr
        ⟨L, ⟨⟨hL1, hyL⟩, hLM⟩⟩
    omega
  have hk2 : ∀ M ∈ Mset, 2 ≤ k M → k M = ℓ + 1 := by
    intro M hM hkge
    obtain ⟨hTM, hMH, hM3⟩ := hM
    haveI : FiniteDimensional K M := Submodule.finiteDimensional_of_le (hMH.trans hHA)
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (ι y)
    let R : Submodule K W := C ⊓ M
    have hRleM : R ≤ M := inf_le_right
    have hRleH : R ≤ H := hRleM.trans hMH
    have hRdisj : ι y ⊓ R = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro v hv
      exact (Disjoint.le_bot hC.disjoint) ⟨hv.1, hv.2.1⟩
    have hRsup : ι y ⊔ R = M := by
      refine le_antisymm (sup_le (le_trans le_sup_right hTM) hRleM) ?_
      intro e he
      have htop : e ∈ (ι y) ⊔ C := by
        rw [codisjoint_iff.mp hC.codisjoint]
        exact Submodule.mem_top
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp htop
      have hcM : c ∈ M := by
        have h : c = e - a := by
          rw [← hac]
          abel
        rw [h]
        exact M.sub_mem he ((le_trans le_sup_right hTM) ha)
      exact Submodule.mem_sup.mpr ⟨a, ha, c, ⟨hc, hcM⟩, hac⟩
    have hRdim : finrank K R = 2 := by
      have hy1 : finrank K (ι y) = 1 := hι.finrank_point y hy0
      haveI : FiniteDimensional K (ι y) := Module.finite_of_finrank_pos (by rw [hy1]; norm_num)
      haveI : FiniteDimensional K R := Submodule.finiteDimensional_of_le hRleM
      have h := Submodule.finrank_sup_add_finrank_inf_eq (ι y) R
      rw [hRsup, hM3, hRdisj, finrank_bot, hy1] at h
      omega
    have hRnoty : ¬ ι y ≤ R := by
      intro hle
      have hbot : ι y ≤ (⊥ : Submodule K W) := by
        rw [← hRdisj]
        exact le_inf le_rfl hle
      have heq : ι y = ⊥ := le_antisymm hbot bot_le
      have h1 := hι.finrank_point y hy0
      rw [heq, finrank_bot] at h1
      omega
    have hRnotline : ∀ L, c L = 1 → ι L ≠ R := by
      intro L hL1 hEq
      have hdegL : Γ.degree L = s + 1 := by
        rw [hdeg L, if_neg (by rw [hL1]; decide)]
      have h1lt : 1 < (Γ.neighborSet L).ncard := by
        rw [ncard_neighborSet]
        omega
      obtain ⟨z, hzL, z', hz'L, hzz'⟩ :=
        (Set.one_lt_ncard (s := Γ.neighborSet L)).mp h1lt
      have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hzL
      have hz'0 : c z' = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hz'L
      have hzR : ι z ≤ R := by
        rw [← hEq]
        exact (hι.adj_iff z L hz0 hL1).1 hzL.symm
      have hz'R : ι z' ≤ R := by
        rw [← hEq]
        exact (hι.adj_iff z' L hz'0 hL1).1 hz'L.symm
      have hzy : z ≠ y := fun h => hRnoty (h ▸ hzR)
      have hz'y : z' ≠ y := fun h => hRnoty (h ▸ hz'R)
      have hzy2 : Γ.dist y z = 2 :=
        dist_eq_two_of_le_perpSpan hP hT hι hy0 hz0 (hzR.trans hRleH) hzy
      have hz'y2 : Γ.dist y z' = 2 :=
        dist_eq_two_of_le_perpSpan hP hT hι hy0 hz'0 (hz'R.trans hRleH) hz'y
      have hzperp : z ∈ ptPerp Γ c {y} :=
        ⟨hz0, by
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hzy2⟩
      have hz'perp : z' ∈ ptPerp Γ c {y} :=
        ⟨hz'0, by
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hz'y2⟩
      have hNotAdj : ¬ Γ.Adj y L := by
        intro hyL
        exact hRnoty (hEq ▸ ((hι.adj_iff y L hy0 hL1).1 hyL))
      exact hzz' (eq_of_mem_ptPerp_of_adj_line hP hy0 hNotAdj hzL hz'L hzperp hz'perp)
    have hdim_inf : ∀ L, c L = 1 → Γ.Adj y L → ι L ≤ M →
        finrank K ↥(ι L ⊓ R) = 1 := by
      intro L hL1 hyL hLM
      have hyLle : ι y ≤ ι L := (hι.adj_iff y L hy0 hL1).1 hyL
      have hL2 : finrank K (ι L) = 2 := hι.finrank_line L hL1
      haveI : FiniteDimensional K (ι L) := Module.finite_of_finrank_pos (by rw [hL2]; norm_num)
      have hnotle : ¬ ι L ≤ R := by
        intro hle
        exact hRnoty (hyLle.trans hle)
      have hsup_le : ι L ⊔ R ≤ M := sup_le hLM hRleM
      haveI : FiniteDimensional K ↥(ι L ⊔ R) := Submodule.finiteDimensional_of_le hsup_le
      have hsup_dim : finrank K ↥(ι L ⊔ R) ≤ 3 := by
        have := Submodule.finrank_mono hsup_le
        rwa [hM3] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq (ι L) R
      rw [hL2, hRdim] at h
      have hinf_le : finrank K ↥(ι L ⊓ R) ≤ 2 := by
        have := Submodule.finrank_mono (inf_le_left : ι L ⊓ R ≤ ι L)
        rwa [hL2] at this
      have hinf_ne2 : finrank K ↥(ι L ⊓ R) ≠ 2 := by
        intro h2
        have heq : ι L ⊓ R = ι L :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, hL2])
        exact hnotle (heq ▸ inf_le_right)
      have hinf_ne0 : finrank K ↥(ι L ⊓ R) ≠ 0 := by
        intro h0
        omega
      omega
    let Lin : Set V := {L : V | L ∈ Lset ∧ ι L ≤ M}
    let f : ∀ L ∈ Lin, V := fun L hL =>
      Classical.choose (hι.full L hL.1.1 (ι L ⊓ R)
        (hdim_inf L hL.1.1 hL.1.2 hL.2) inf_le_left)
    have hf : ∀ (L : V) (hL : L ∈ Lin),
        Γ.Adj L (f L hL) ∧ ι (f L hL) = ι L ⊓ R := by
      intro L hL
      exact Classical.choose_spec (hι.full L hL.1.1 (ι L ⊓ R)
        (hdim_inf L hL.1.1 hL.1.2 hL.2) inf_le_left)
    have hRsection : k M = (sectionPoints c ι R).ncard := by
      change Lin.ncard = (sectionPoints c ι R).ncard
      refine Set.ncard_congr (fun L hL => f L hL) ?_ ?_ ?_
      · intro L hL
        obtain ⟨hLx, hxU⟩ := hf L hL
        exact ⟨color_eq_zero_of_adj_of_color_eq_one hL.1.1 hLx, hxU ▸ inf_le_right⟩
      · intro L L' hL hL' heq
        obtain ⟨hxL, hxU⟩ := hf L hL
        obtain ⟨hxL', hxU'⟩ := hf L' hL'
        have hx : f L hL = f L' hL' := heq
        have hxR : ι (f L hL) ≤ R := hxU ▸ inf_le_right
        have hxy : f L hL ≠ y := by
          intro h
          exact hRnoty (h ▸ hxR)
        have hx0 : c (f L hL) = 0 := color_eq_zero_of_adj_of_color_eq_one hL.1.1 hxL
        have hdist : Γ.dist y (f L hL) = 2 :=
          dist_eq_two_of_le_perpSpan hP hT hι hy0 hx0 (hxR.trans hRleH) hxy
        have hxL' : Γ.Adj L' (f L hL) := by
          rw [hx]
          exact hxL'
        exact (existsUnique_commonNeighbor hP hdist).unique
          ⟨hL.1.2, hxL.symm⟩ ⟨hL'.1.2, hxL'.symm⟩
      · intro x hx
        have hx0 : c x = 0 := hx.1
        have hxR : ι x ≤ R := hx.2
        have hxy : x ≠ y := by
          intro h
          exact hRnoty (h ▸ hxR)
        have hdist : Γ.dist y x = 2 :=
          dist_eq_two_of_le_perpSpan hP hT hι hy0 hx0 (hxR.trans hRleH) hxy
        let L : V := commonNeighbor hP hdist
        have hyL : Γ.Adj y L := commonNeighbor_adj_left hP hdist
        have hxL : Γ.Adj x L := commonNeighbor_adj_right hP hdist
        have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hyL
        have hLleM : ι L ≤ M := by
          rw [line_eq_sup_of_two_adjacent_points hι hy0 hx0 hxy.symm hyL hxL]
          exact sup_le (le_trans le_sup_right hTM) (hxR.trans hRleM)
        have hLmem : L ∈ Lin := ⟨⟨hL1, hyL⟩, hLleM⟩
        have hdimL := hdim_inf L hL1 hyL hLleM
        have hspec := hf L hLmem
        have hxle : ι x ≤ ι L ⊓ R := le_inf ((hι.adj_iff x L hx0 hL1).1 hxL) hxR
        have hx1 : finrank K (ι x) = 1 := hι.finrank_point x hx0
        haveI : FiniteDimensional K ↥(ι L ⊓ R) := Submodule.finiteDimensional_of_le inf_le_right
        have heq : ι L ⊓ R = ι x :=
          (Submodule.eq_of_le_of_finrank_eq hxle (by rw [hdimL, hx1])).symm
        have hfeq : f L hLmem = x := by
          apply hι.injective
          rw [hspec.2, heq]
        refine ⟨L, hLmem, ?_⟩
        exact hfeq
    have hsecR : (sectionPoints c ι R).ncard = ℓ + 1 :=
      hsec R (hRleH.trans hHA) hRdim hRnotline (by rw [← hRsection]; exact hkge)
    rw [hRsection, hsecR]
  have hcover : ∀ M ∈ Mset, k M = 1 ∨ k M = ℓ + 1 := by
    intro M hM
    rcases Nat.eq_or_lt_of_le (hk1 M hM) with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hk2 M hM (by omega))
  have hsingle_eq : ∀ M ∈ Mset, k M = 1 → ∀ L, c L = 1 → Γ.Adj y L → ι L ≤ M →
      ∀ y', Γ.Adj L y' → y' ≠ y → M = perpSpan c ι y ⊓ perpSpan c ι y' := by
    intro M hM hk L hL1 hyL hLM y' hy'L hy'ne
    obtain ⟨hTM, hMH, hM3⟩ := hM
    haveI : FiniteDimensional K M := Submodule.finiteDimensional_of_le (hMH.trans hHA)
    have hy'0 : c y' = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hy'L
    by_cases hle : M ≤ perpSpan c ι y'
    · have hdim : finrank K ↥(perpSpan c ι y ⊓ perpSpan c ι y') = 3 := by
        have h := finrank_perpSpan_inf_add_two hP hT hι hy0 hy'0 (Ne.symm hy'ne) hyL hy'L.symm
        omega
      exact Submodule.eq_of_le_of_finrank_eq (le_inf hMH hle) (by rw [hM3, hdim])
    · exfalso
      have hsup : perpSpan c ι y' ⊔ M = A :=
        perpSpan_sup_eq_of_not_le hP hT hι hy'0 (hMH.trans hHA) hle
      haveI : FiniteDimensional K (perpSpan c ι y') :=
        Submodule.finiteDimensional_of_le (perpSpan_le_ambient hι y')
      have hintdim : finrank K ↥(M ⊓ perpSpan c ι y') = 2 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq M (perpSpan c ι y')
        rw [sup_comm M (perpSpan c ι y'), hsup, h5] at h
        have h' := finrank_perpSpan_add_one hP hT hι hy'0
        omega
      have hLle : ι L ≤ M ⊓ perpSpan c ι y' := by
        refine le_inf hLM ?_
        rw [perpSpan_eq_iSup_neighborFinset hP hT hι hy'0]
        exact le_iSup_of_le L (le_iSup_of_le (by simpa using hy'L.symm) le_rfl)
      haveI : FiniteDimensional K (ι L) :=
        Module.finite_of_finrank_pos (by rw [hι.finrank_line L hL1]; norm_num)
      haveI : FiniteDimensional K ↥(M ⊓ perpSpan c ι y') :=
        Submodule.finiteDimensional_of_le inf_le_left
      have hInt : M ⊓ perpSpan c ι y' = ι L :=
        (Submodule.eq_of_le_of_finrank_eq hLle
          (by rw [hintdim, hι.finrank_line L hL1])).symm
      have hy'Lle : ι y' ≤ M := ((hι.adj_iff y' L hy'0 hL1).1 hy'L.symm).trans hLM
      let Nset : Set (Submodule K W) := {N | ι y' ≤ N ∧ N ≤ M ∧ finrank K N = 2}
      have hNsetcard' : Nset.ncard = s + 1 := by
        have hgap : finrank K M = finrank K (ι y') + 2 := by
          rw [hM3, hι.finrank_point y' hy'0]
        have h := card_submodule_between_two (K := K) (W := W) (U := ι y') (X := M)
          hy'Lle hgap
        have h1 : Nat.card {N : Submodule K W // ι y' ≤ N ∧ N ≤ M ∧
            finrank K N = finrank K (ι y') + 1} = s + 1 := by
          rw [h, card_field_eq_of_isProjGQ hP hT c hdeg hι]
        have h2 : Nat.card {N : Submodule K W // ι y' ≤ N ∧ N ≤ M ∧
            finrank K N = 2} = s + 1 := by
          rw [← h1]
          exact Nat.card_congr (Equiv.subtypeEquivRight fun N => by
            rw [hι.finrank_point y' hy'0])
        rw [← Nat.card_coe_set_eq Nset]
        exact h2
      have hNlt : 1 < Nset.ncard := by
        rw [hNsetcard']
        omega
      haveI : Finite ↥Nset :=
        Finite.of_injective (fun N : Nset =>
          (⟨N.1, N.2.2.1.trans (hMH.trans hHA)⟩ : {T : Submodule K W // T ≤ A}))
          (fun a b h => Subtype.ext
            (congrArg (fun x : {T : Submodule K W // T ≤ A} => (x : Submodule K W)) h))
      obtain ⟨N, hN, N', hN', hNN'⟩ := (Set.one_lt_ncard (s := Nset)).mp hNlt
      have hexN : ∃ N, N ∈ Nset ∧ N ≠ ι L := by
        rcases eq_or_ne N (ι L) with hNl | hNl
        · refine ⟨N', hN', ?_⟩
          intro hN'l
          exact hNN' (hNl.trans hN'l.symm)
        · exact ⟨N, hN, hNl⟩
      obtain ⟨N, hN, hNne⟩ := hexN
      obtain ⟨hNy', hNM, hN2⟩ := hN
      have hNnotle : ¬ N ≤ perpSpan c ι y' := by
        intro hleN
        have hleI : N ≤ M ⊓ perpSpan c ι y' := le_inf hNM hleN
        have heq : N = M ⊓ perpSpan c ι y' :=
          Submodule.eq_of_le_of_finrank_eq hleI (by rw [hN2, hintdim])
        exact hNne (heq.trans hInt)
      obtain ⟨w, hw0, hwN, hy'w4⟩ :=
        exists_dist_eq_four_of_not_le_perpSpan hP hT hι hy'0 hN2 hNy'
          (hNM.trans (hMH.trans hHA)) hNnotle
      have hwM : ι w ≤ M := hwN.trans hNM
      have hwy : w ≠ y := by
        intro hwy
        rw [hwy] at hy'w4
        have h2 : Γ.dist y' y = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hy'L.symm hyL.symm hy'ne
        omega
      have hwy2 : Γ.dist y w = 2 :=
        dist_eq_two_of_le_perpSpan hP hT hι hy0 hw0 (hwM.trans hMH) hwy
      let L₂ : V := commonNeighbor hP hwy2
      have hyL₂ : Γ.Adj y L₂ := commonNeighbor_adj_left hP hwy2
      have hwL₂ : Γ.Adj w L₂ := commonNeighbor_adj_right hP hwy2
      have hL₂1 : c L₂ = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hyL₂
      have hL₂M : ι L₂ ≤ M := by
        rw [line_eq_sup_of_two_adjacent_points hι hy0 hw0 hwy.symm hyL₂ hwL₂]
        exact sup_le (le_trans le_sup_right hTM) hwM
      have hL₂ne : L₂ ≠ L := by
        intro hEq
        have hwL : Γ.Adj L w := (hEq ▸ hwL₂).symm
        have h2 : Γ.dist y' w = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hy'L.symm hwL (by
            intro h
            rw [h] at hy'w4
            simp at hy'w4)
        omega
      have hmem : 1 < {L : V | L ∈ Lset ∧ ι L ≤ M}.ncard :=
        (Set.one_lt_ncard (s := {L : V | L ∈ Lset ∧ ι L ≤ M})).mpr
          ⟨L, ⟨⟨hL1, hyL⟩, hLM⟩, L₂, ⟨⟨hL₂1, hyL₂⟩, hL₂M⟩, Ne.symm hL₂ne⟩
      have hkm : {L : V | L ∈ Lset ∧ ι L ≤ M}.ncard = k M := rfl
      rw [hkm, hk] at hmem
      omega
  let Fset : Set V := fullLinesThrough Γ (collar c ι X) y
  have hex : ∀ L : V, L ∈ Fset → ∃ y' : V, y' ∈ Γ.neighborSet L ∧ y' ≠ y := by
    intro L hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hL.1
    have hdegL : Γ.degree L = s + 1 := by
      rw [hdeg L, if_neg (by rw [hL1]; decide)]
    have h1lt : 1 < (Γ.neighborSet L).ncard := by
      rw [ncard_neighborSet]
      omega
    obtain ⟨y', hy'L, hy'ne⟩ := Set.exists_ne_of_one_lt_ncard h1lt y
    exact ⟨y', hy'L, hy'ne⟩
  let y' : (L : V) → L ∈ Fset → V := fun L hL => Classical.choose (hex L hL)
  have hy'mem : ∀ (L : V) (hL : L ∈ Fset), y' L hL ∈ Γ.neighborSet L :=
    fun L hL => (Classical.choose_spec (hex L hL)).1
  have hy'ne : ∀ (L : V) (hL : L ∈ Fset), y' L hL ≠ y :=
    fun L hL => (Classical.choose_spec (hex L hL)).2
  have hMof_mem : ∀ (L : V) (hL : L ∈ Fset),
      perpSpan c ι y ⊓ perpSpan c ι (y' L hL) ∈ Mset := by
    intro L hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hL.1
    have hCart : y' L hL ∈ collar c ι X := hL.2 (hy'mem L hL)
    have hy'0 : c (y' L hL) = 0 := hCart.1
    have hXy' : X ≤ perpSpan c ι (y' L hL) := hCart.2
    have hy'L : Γ.Adj L (y' L hL) := hy'mem L hL
    refine ⟨?_, ?_, ?_⟩
    · refine sup_le ?_ ?_
      · exact le_inf hXH hXy'
      · refine le_inf (submodule_le_perpSpan ⟨hy0, by simp⟩) ?_
        refine submodule_le_perpSpan ⟨hy0, ?_⟩
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hL.1 hy'L (Ne.symm (hy'ne L hL)))
    · exact inf_le_left
    · have h := finrank_perpSpan_inf_add_two hP hT hι hy0 hy'0
        (Ne.symm (hy'ne L hL)) hL.1 hy'L.symm
      omega
  let Mof : (L : V) → (hL : L ∈ Fset) → Mset :=
    fun L hL => ⟨perpSpan c ι y ⊓ perpSpan c ι (y' L hL), hMof_mem L hL⟩
  have hMof_sec : ∀ (L : V) (hL : L ∈ Fset),
      sectionPoints c ι (perpSpan c ι y ⊓ perpSpan c ι (y' L hL)) = Γ.neighborSet L := by
    intro L hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hL.1
    have hy'0 : c (y' L hL) = 0 := (hL.2 (hy'mem L hL)).1
    exact sectionPoints_perpSpan_inf hP hT hι hy0 hy'0 (Ne.symm (hy'ne L hL)) hL.1
      (hy'mem L hL).symm
  have hMof_k : ∀ (L : V) (hL : L ∈ Fset), k (Mof L hL).1 = 1 := by
    intro L hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hL.1
    have hy'L : Γ.Adj L (y' L hL) := hy'mem L hL
    have hsecM := hMof_sec L hL
    have hset : {L₂ : V | L₂ ∈ Lset ∧ ι L₂ ≤ (Mof L hL).1} = {L} := by
      ext L₂
      constructor
      · rintro ⟨⟨hL₂1, hyL₂⟩, hL₂le⟩
        have hdegL₂ : Γ.degree L₂ = s + 1 := by
          rw [hdeg L₂, if_neg (by rw [hL₂1]; decide)]
        have h1lt : 1 < (Γ.neighborSet L₂).ncard := by
          rw [ncard_neighborSet]
          omega
        obtain ⟨z, hzL₂, z', hz'L₂, hzz'⟩ :=
          (Set.one_lt_ncard (s := Γ.neighborSet L₂)).mp h1lt
        have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL₂1 hzL₂
        have hz'0 : c z' = 0 := color_eq_zero_of_adj_of_color_eq_one hL₂1 hz'L₂
        have hzle : ι z ≤ (Mof L hL).1 := ((hι.adj_iff z L₂ hz0 hL₂1).1 hzL₂.symm).trans hL₂le
        have hz'le : ι z' ≤ (Mof L hL).1 :=
          ((hι.adj_iff z' L₂ hz'0 hL₂1).1 hz'L₂.symm).trans hL₂le
        have hzsec : z ∈ sectionPoints c ι (Mof L hL).1 := ⟨hz0, hzle⟩
        have hz'sec : z' ∈ sectionPoints c ι (Mof L hL).1 := ⟨hz'0, hz'le⟩
        rw [hsecM] at hzsec hz'sec
        exact eq_of_two_common_points hP hzz' hzL₂ hz'L₂ hzsec hz'sec
      · intro hL2
        rw [hL2]
        refine ⟨⟨hL1, hL.1⟩, ?_⟩
        change ι L ≤ perpSpan c ι y ⊓ perpSpan c ι (y' L hL)
        refine le_inf ?_ ?_
        · rw [perpSpan_eq_iSup_neighborFinset hP hT hι hy0]
          exact le_iSup_of_le L (le_iSup_of_le (by simpa using hL.1) le_rfl)
        · rw [perpSpan_eq_iSup_neighborFinset hP hT hι ((hL.2 (hy'mem L hL)).1)]
          exact le_iSup_of_le L (le_iSup_of_le (by simpa using hy'L.symm) le_rfl)
    change {L₂ : V | L₂ ∈ Lset ∧ ι L₂ ≤ (Mof L hL).1}.ncard = 1
    rw [hset, Set.ncard_singleton]
  have hMof_inj : ∀ (L : V) (hL : L ∈ Fset) (L' : V) (hL' : L' ∈ Fset),
      Mof L hL = Mof L' hL' → L = L' := by
    intro L hL L' hL' heq
    have hval : perpSpan c ι y ⊓ perpSpan c ι (y' L hL) =
        perpSpan c ι y ⊓ perpSpan c ι (y' L' hL') := by
      have h := congrArg Subtype.val heq
      simpa [Mof] using h
    have hsec : Γ.neighborSet L = Γ.neighborSet L' := by
      rw [← hMof_sec L hL, ← hMof_sec L' hL', hval]
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hL.1
    have hdegL : Γ.degree L = s + 1 := by
      rw [hdeg L, if_neg (by rw [hL1]; decide)]
    have h1lt : 1 < (Γ.neighborSet L).ncard := by
      rw [ncard_neighborSet]
      omega
    obtain ⟨z, hzL, z', hz'L, hzz'⟩ :=
      (Set.one_lt_ncard (s := Γ.neighborSet L)).mp h1lt
    have hzL' : z ∈ Γ.neighborSet L' := by rw [← hsec]; exact hzL
    have hz'L' : z' ∈ Γ.neighborSet L' := by rw [← hsec]; exact hz'L
    exact eq_of_two_common_points hP hzz' hzL hz'L hzL' hz'L'
  have hMof_surj : ∀ M : Mset, k M.1 = 1 → ∃ (L : V) (hL : L ∈ Fset), Mof L hL = M := by
    intro M hk
    obtain ⟨hTM, hMH, hM3⟩ := M.2
    have hpos : 0 < {L : V | L ∈ Lset ∧ ι L ≤ M.1}.ncard := by
      change 0 < k M.1
      omega
    obtain ⟨L, hLmem⟩ := (Set.ncard_pos (s := {L : V | L ∈ Lset ∧ ι L ≤ M.1})).mp hpos
    obtain ⟨⟨hL1, hyL⟩, hLM⟩ := hLmem
    have hdegL : Γ.degree L = s + 1 := by
      rw [hdeg L, if_neg (by rw [hL1]; decide)]
    have h1lt : 1 < (Γ.neighborSet L).ncard := by
      rw [ncard_neighborSet]
      omega
    obtain ⟨y'', hy''L, hy''ne⟩ := Set.exists_ne_of_one_lt_ncard h1lt y
    have hMeq : M.1 = perpSpan c ι y ⊓ perpSpan c ι y'' :=
      hsingle_eq M.1 M.2 hk L hL1 hyL hLM y'' hy''L hy''ne
    have hLfull : L ∈ Fset := by
      refine ⟨hyL, ?_⟩
      intro z hzL
      have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hzL
      have hy''0 : c y'' = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hy''L
      refine ⟨hz0, ?_⟩
      have hXY : X ≤ perpSpan c ι y ⊓ perpSpan c ι y'' := by
        rw [← hMeq]
        exact le_trans le_sup_left hTM
      exact hXY.trans (perpSpan_inf_le_perpSpan hP hT hι hy0 hy''0 hz0
        (Ne.symm hy''ne) hyL hy''L.symm hzL.symm)
    have hMeq' : M.1 = perpSpan c ι y ⊓ perpSpan c ι (y' L hLfull) :=
      hsingle_eq M.1 M.2 hk L hL1 hyL hLM (y' L hLfull) (hy'mem L hLfull)
        (hy'ne L hLfull)
    refine ⟨L, hLfull, ?_⟩
    apply Subtype.ext
    exact hMeq'.symm
  let A1 : Set Mset := {M | k M.1 = 1}
  let A2 : Set Mset := {M | k M.1 = ℓ + 1}
  have hA1F : Fset.ncard = A1.ncard := by
    refine Set.ncard_congr (fun L hL => Mof L hL) ?_ ?_ ?_
    · intro L hL
      exact hMof_k L hL
    · intro L L' hL hL' heq
      exact hMof_inj L hL L' hL' heq
    · intro M hM
      exact hMof_surj M hM
  let a1 : ℕ := (Finset.univ.filter fun M : Mset => k M.1 = 1).card
  let a2 : ℕ := (Finset.univ.filter fun M : Mset => k M.1 = ℓ + 1).card
  have ha1 : a1 = A1.ncard := by
    change (Finset.univ.filter (fun M : Mset => k M.1 = 1)).card = A1.ncard
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq A1
  have ha2 : a2 = A2.ncard := by
    change (Finset.univ.filter (fun M : Mset => k M.1 = ℓ + 1)).card = A2.ncard
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq A2
  have hpartition : a1 + a2 = s + 1 := by
    have hunion : A1 ∪ A2 = Set.univ := by
      apply Set.ext
      intro M
      constructor
      · intro _; exact Set.mem_univ M
      · intro _
        rcases hcover M.1 M.2 with h | h
        · exact Set.mem_union_left _ h
        · exact Set.mem_union_right _ h
    have hdisj : Disjoint A1 A2 := by
      rw [Set.disjoint_left]
      intro M h1 h2
      have h1' : k M.1 = 1 := h1
      have h2' : k M.1 = ℓ + 1 := h2
      omega
    have hfin : Mset.ncard = A1.ncard + A2.ncard := by
      have h := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
      rw [hunion] at h
      rwa [Set.ncard_univ, Nat.card_coe_set_eq] at h
    rw [ha1, ha2, ← hfin, hMsetcard]
  have hnotfilter : (Finset.univ.filter fun M : Mset => ¬ k M.1 = 1) =
      (Finset.univ.filter fun M : Mset => k M.1 = ℓ + 1) := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases hcover M.1 M.2 with h1 | h1
      · exact absurd h1 h
      · exact h1
    · intro h h1
      omega
  have hsumsplit : (∑ M : Mset, k M.1) = a1 + a2 * (ℓ + 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun M : Mset => k M.1 = 1) (f := fun M : Mset => k M.1), hnotfilter]
    have h1 : (∑ M ∈ Finset.univ.filter (fun M : Mset => k M.1 = 1), k M.1) = a1 := by
      have h := Finset.sum_const_nat
        (s := Finset.univ.filter (fun M : Mset => k M.1 = 1)) (m := 1)
        (f := fun M : Mset => k M.1) (fun M hM => (Finset.mem_filter.mp hM).2)
      rw [h, mul_one]
    have h2 : (∑ M ∈ Finset.univ.filter (fun M : Mset => k M.1 = ℓ + 1), k M.1) =
        a2 * (ℓ + 1) := by
      have h := Finset.sum_const_nat
        (s := Finset.univ.filter (fun M : Mset => k M.1 = ℓ + 1)) (m := ℓ + 1)
        (f := fun M : Mset => k M.1) (fun M hM => (Finset.mem_filter.mp hM).2)
      rw [h]
    rw [h1, h2]
  have ht' : t = ℓ * s := t_eq_mul_of_finrank_eq_five hP hT c hdeg hι hsec h5
  have hsum2 : a1 + a2 * (ℓ + 1) = ℓ * s + 1 := by
    rw [← hsumsplit, hsum, ht']
  have hgoalZ : (a1 : ℤ) * ℓ = (s : ℤ) + ℓ := by
    have h1Z : (a1 : ℤ) + a2 = (s : ℤ) + 1 := by exact_mod_cast hpartition
    have h2Z : (a1 : ℤ) + (a2 : ℤ) * ((ℓ : ℤ) + 1) = (ℓ : ℤ) * (s : ℤ) + 1 := by
      exact_mod_cast hsum2
    nlinarith
  have hgoal : a1 * ℓ = s + ℓ := by exact_mod_cast hgoalZ
  change Fset.ncard * ℓ = s + ℓ
  rw [hA1F, ← ha1, hgoal]

end Closure

end CFSG.Geometry.GeneralizedQuadrangles

end
