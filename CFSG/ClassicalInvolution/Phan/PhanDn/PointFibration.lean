module

public import CFSG.ClassicalInvolution.Phan.PhanDn.PointResidue
public import CFSG.ClassicalInvolution.Phan.PhanDn.SolidResidue
public import CFSG.ClassicalInvolution.Phan.PhanDn.KleinChambers
public import CFSG.ClassicalInvolution.Phan.PhanDn.Diameter
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanG
  CFSG.ClassicalGroups.Unitary QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {σ : K ≃+* K} {s : ℕ}

@[expose] def ptFib (hσ : ∀ x, σ (σ x) = x) (s : ℕ) :
    Fib (dChamberSystem σ (s + 3)) (flipGraph σ (s + 4)) where
  P c := ⟨c.line 0, c.isFlipflopPt_line 0⟩
  a := 0
  J' := {i | i ≠ 0}
  Q _ := True
  step_Q := fun _ _ _ => trivial
  step_P := fun {i e g} hi hadj _ => by
    have hline : e.line 0 = g.line 0 := by
      rw [← FlipFrame.elt_zero e.toFlipFrame (show 2 ≤ s + 3 by omega),
        ← FlipFrame.elt_zero g.toFlipFrame (show 2 ≤ s + 3 by omega)]
      exact (dChamberSystem_adj_iff σ (s + 3) i e g).mp hadj 0 (Ne.symm hi)
    exact Subtype.ext hline
  step_a := fun {e g} hadj _ => by
    have hgal := (dChamberSystem_adj_iff σ (s + 3) 0 e g).mp hadj
    have h1 : e.elt 1 = g.elt 1 := hgal 1 (by
      intro hh
      have hv : ((1 : Fin (s + 4)) : ℕ) = ((0 : Fin (s + 4)) : ℕ) := congrArg Fin.val hh
      rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (show 1 < s + 4 by omega)] at hv
      exact Nat.one_ne_zero hv)
    by_cases h : e.line 0 = g.line 0
    · exact Or.inl (DChamber.eq_of_adj_zero hσ (show 2 ≤ s + 3 by omega) hadj h)
    · have hL : IsFlipLine σ (e.line 0 ⊔ e.line 1) := by
        have he1 : e.elt 1 = e.line 0 ⊔ e.line 1 :=
          FlipFrame.elt_one e.toFlipFrame (show 3 ≤ s + 3 by omega)
        rw [← he1]
        refine ⟨FlipFrame.isFlipflopSub_elt hσ e.toFlipFrame 1, ?_⟩
        rw [FlipFrame.finrank_elt hσ e.toFlipFrame 1]
        have hv1 : ((1 : Fin (s + 4)) : ℕ) = 1 := by
          rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
        rw [hv1, if_pos (show 1 + 1 < s + 3 by omega)]
      have hx : e.line 0 ∈ ptsOn σ (e.line 0 ⊔ e.line 1) :=
        ⟨e.isFlipflopPt_line 0, le_sup_left⟩
      have hy : g.line 0 ∈ ptsOn σ (e.line 0 ⊔ e.line 1) := by
        refine ⟨g.isFlipflopPt_line 0, ?_⟩
        rw [← FlipFrame.elt_one e.toFlipFrame (show 3 ≤ s + 3 by omega), h1,
          FlipFrame.elt_one g.toFlipFrame (show 3 ≤ s + 3 by omega)]
        exact le_sup_left
      exact Or.inr (flipColl_of_le_line hL hx hy h)

private theorem isFlipLine_line_sup_line_one (hσ : ∀ x, σ (σ x) = x) {m : ℕ}
    (c : DChamber σ (m + 1)) (hm : 3 ≤ m) : IsFlipLine σ (c.line 0 ⊔ c.line 1) := by
  have h1 : c.elt 1 = c.line 0 ⊔ c.line 1 := FlipFrame.elt_one c.toFlipFrame hm
  rw [← h1]
  refine ⟨FlipFrame.isFlipflopSub_elt hσ c.toFlipFrame 1, ?_⟩
  rw [FlipFrame.finrank_elt hσ c.toFlipFrame 1]
  have hv1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rw [hv1, if_pos (show 1 + 1 < m by omega)]

private theorem line_sup_line_eq_of_adj_zero (hσ : ∀ x, σ (σ x) = x) {m : ℕ} (hm : 3 ≤ m)
    {c f : DChamber σ (m + 1)} {p x : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hadj : (dChamberSystem σ m).adj 0 c f) (hc : c.line 0 = p) (hf : f.line 0 = x)
    (hL : IsFlipLine σ (p ⊔ x)) : c.line 0 ⊔ c.line 1 = p ⊔ x := by
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    intro hh
    have hv : ((1 : Fin (m + 1)) : ℕ) = ((0 : Fin (m + 1)) : ℕ) := congrArg Fin.val hh
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    exact Nat.one_ne_zero hv
  have h1 : c.elt 1 = f.elt 1 :=
    (dChamberSystem_adj_iff σ m 0 c f).mp hadj 1 h10
  have hc1 : IsFlipLine σ (c.line 0 ⊔ c.line 1) := isFlipLine_line_sup_line_one hσ c hm
  refine (Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hL.2, hc1.2])).symm
  refine sup_le ?_ ?_
  · rw [hc]
    exact le_sup_left
  · calc x = f.line 0 := hf.symm
      _ ≤ f.line 0 ⊔ f.line 1 := le_sup_left
      _ = f.elt 1 := (FlipFrame.elt_one f.toFlipFrame hm).symm
      _ = c.elt 1 := h1.symm
      _ = c.line 0 ⊔ c.line 1 := FlipFrame.elt_one c.toFlipFrame hm

theorem ptFib_rigid (hσ : IsUnitaryInvolution σ) (s : ℕ)
    (hsc : (dChamberSystem σ (s + 2)).SimplyTwoConnected)
    (hconn : (dChamberSystem σ (s + 1)).Connected) : (ptFib hσ.invol s).Rigid where
  null := fun {e γ} _ hγ hend =>
    twoHomotopic_nil_of_isJGallery_ne_zero hσ (s + 1) hsc hγ hend
  edge := by
    intro e e' f f' ρ ρ' x' _ _ hPe hΓ hρ hf hPf hρ' hf' hPf'
    have hPg : (ptFib hσ.invol s).P (galleryEnd e ρ) = (ptFib hσ.invol s).P e :=
      (ptFib hσ.invol s).P_galleryEnd trivial hρ
    have hPg' : (ptFib hσ.invol s).P (galleryEnd e' ρ') = (ptFib hσ.invol s).P e' :=
      (ptFib hσ.invol s).P_galleryEnd trivial hρ'
    have hPgval : (galleryEnd e ρ).line 0 = e.line 0 := congrArg Subtype.val hPg
    have hPg'val : (galleryEnd e' ρ').line 0 = e'.line 0 := congrArg Subtype.val hPg'
    have hPee' : e.line 0 = e'.line 0 := congrArg Subtype.val hPe
    have hΓc : FlipColl σ (e.line 0) x'.1 := hΓ
    have hΓL : IsFlipLine σ (e.line 0 ⊔ x'.1) :=
      hΓc.isFlipLine (e.isFlipflopPt_line 0) x'.2
    have hL1 := line_sup_line_eq_of_adj_zero hσ.invol (m := s + 3) (show 3 ≤ s + 3 by omega)
      (c := galleryEnd e ρ) (f := f) (p := e.line 0) (x := x'.1) hf hPgval
      (congrArg Subtype.val hPf) hΓL
    have hL2 := line_sup_line_eq_of_adj_zero hσ.invol (m := s + 3) (show 3 ≤ s + 3 by omega)
      (c := galleryEnd e' ρ') (f := f') (p := e.line 0) (x := x'.1) hf'
      (by rw [hPg'val, hPee']) (congrArg Subtype.val hPf') hΓL
    have hg0 : (galleryEnd e ρ).line 0 = (galleryEnd e' ρ').line 0 := by
      rw [hPgval, hPg'val, hPee']
    have hsup : (galleryEnd e ρ).line 0 ⊔ (galleryEnd e ρ).line 1 =
        (galleryEnd e' ρ').line 0 ⊔ (galleryEnd e' ρ').line 1 := hL1.trans hL2.symm
    obtain ⟨α, hα, hαend⟩ := exists_flag_gallery hσ s hconn hg0 hsup
    have hcomm : ∀ i ∈ ({i : Fin (s + 4) | i ≠ 0 ∧ i ≠ 1} : Set (Fin (s + 4))),
        CommuteTypes (dChamberSystem σ (s + 3)) 0 i := fun i hi =>
      commuteTypes_zero hσ.invol (show 3 ≤ s + 3 by omega) hi.1 hi.2
    have hfg : (dChamberSystem σ (s + 3)).adj 0 f (galleryEnd e ρ) := adj_symm hf
    obtain ⟨α', hα'gal, hα'J, hα'adj, hα'hom⟩ :=
      exists_push (X := dChamberSystem σ (s + 3)) (J₁ := {i | i ≠ 0 ∧ i ≠ 1}) (j := 0)
        hcomm α f (galleryEnd e ρ) hfg hα.1 hα.2
    have hα'adj' : (dChamberSystem σ (s + 3)).adj 0 (galleryEnd f α')
        (galleryEnd e' ρ') := by
      rw [← hαend]
      exact hα'adj
    have hf''eq : galleryEnd f α' = f' := by
      have hα'JG : IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0} f α' :=
        ⟨hα'gal, fun i hi => (hα'J i hi).1⟩
      have hPα' : (ptFib hσ.invol s).P (galleryEnd f α') = (ptFib hσ.invol s).P f :=
        (ptFib hσ.invol s).P_galleryEnd trivial hα'JG
      have hline : (galleryEnd f α').line 0 = f'.line 0 := by
        calc (galleryEnd f α').line 0 = f.line 0 := congrArg Subtype.val hPα'
          _ = x'.1 := congrArg Subtype.val hPf
          _ = f'.line 0 := (congrArg Subtype.val hPf').symm
      exact DChamber.eq_of_adj_zero hσ.invol (show 2 ≤ s + 3 by omega)
        (adj_trans hα'adj' hf') hline
    have hτgal : IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0} e
        (ρ ++ α ++ galleryReverse e' ρ') := by
      have hαJ : IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0}
          (galleryEnd e ρ) α := hα.mono (fun i hi => hi.1)
      have hrev : IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0}
          (galleryEnd e (ρ ++ α)) (galleryReverse e' ρ') := by
        rw [galleryEnd_append, hαend]
        exact hρ'.reverse
      exact (hρ.append hαJ).append hrev
    have hτend : galleryEnd e (ρ ++ α ++ galleryReverse e' ρ') = e' := by
      rw [galleryEnd_append, galleryEnd_append, hαend, galleryEnd_galleryReverse]
    have hτ'gal : IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0} f α' :=
      ⟨hα'gal, fun i hi => (hα'J i hi).1⟩
    have hA0 : (dChamberSystem σ (s + 3)).TwoHomotopic (galleryEnd e (ρ ++ α))
        (galleryReverse e' ρ' ++ ρ' ++ [(0, f')]) [(0, f')] := by
      have h := (twoHomotopic_reverse_append hρ'.1).append_right [(0, f')]
      simp only [List.nil_append] at h
      rw [galleryEnd_append, hαend]
      simpa only [List.append_assoc] using h
    have hA := TwoHomotopic.append_left (X := dChamberSystem σ (s + 3)) (x := e)
      (ρ ++ α) hA0
    have hbt1 : (dChamberSystem σ (s + 3)).TwoHomotopic (galleryEnd e ρ)
        (α ++ [(0, f')]) ([(0, f), (0, galleryEnd e ρ)] ++ α ++ [(0, f')]) :=
      (twoHomotopic_backtrack (X := dChamberSystem σ (s + 3)) (x := galleryEnd e ρ) []
        (α ++ [(0, f')]) (i := 0) (y := f) hf).symm
    have hpush1 := TwoHomotopic.append_left (X := dChamberSystem σ (s + 3))
      (x := galleryEnd e ρ) [(0, f)] hα'hom
    have hpush2 := hpush1.append_right [(0, f')]
    have hbt2 : (dChamberSystem σ (s + 3)).TwoHomotopic f
        (α' ++ [(0, galleryEnd (galleryEnd e ρ) α), (0, galleryEnd f α')])
        (α' ++ []) := by
      refine TwoHomotopic.append_left (X := dChamberSystem σ (s + 3)) (x := f) α' ?_
      have hy : (dChamberSystem σ (s + 3)).adj 0 (galleryEnd f α')
          (galleryEnd (galleryEnd e ρ) α) := by
        rw [hf''eq, hαend]
        exact adj_symm hf'
      simpa using twoHomotopic_backtrack (X := dChamberSystem σ (s + 3))
        (x := galleryEnd f α') [] [] (i := 0) (y := galleryEnd (galleryEnd e ρ) α) hy
    have hbt3 := TwoHomotopic.append_left (X := dChamberSystem σ (s + 3))
      (x := galleryEnd e ρ) [(0, f)] hbt2
    have h23 : (dChamberSystem σ (s + 3)).TwoHomotopic (galleryEnd e ρ)
        (([(0, f)] ++ (α' ++ [(0, galleryEnd (galleryEnd e ρ) α)])) ++ [(0, f')])
        ((0, f) :: α') := by
      simpa [hf''eq, List.append_assoc] using hbt3
    have h12 : (dChamberSystem σ (s + 3)).TwoHomotopic (galleryEnd e ρ)
        ([(0, f), (0, galleryEnd e ρ)] ++ α ++ [(0, f')]) ((0, f) :: α') := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hpush2.trans h23
    have hB : (dChamberSystem σ (s + 3)).TwoHomotopic (galleryEnd e ρ)
        (α ++ [(0, f')]) ((0, f) :: α') := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hbt1.trans h12
    have hB' := TwoHomotopic.append_left (X := dChamberSystem σ (s + 3)) (x := e) ρ hB
    refine ⟨ρ ++ α ++ galleryReverse e' ρ', α', hτgal, hτend, hτ'gal, hf''eq, ?_⟩
    have hmid : (dChamberSystem σ (s + 3)).TwoHomotopic e
        (ρ ++ α ++ [(0, f')]) (ρ ++ (0, f) :: α') := by
      simpa only [List.append_assoc] using hB'
    have hA' : (dChamberSystem σ (s + 3)).TwoHomotopic e
        (ρ ++ α ++ galleryReverse e' ρ' ++ ρ' ++ [(0, f')]) (ρ ++ α ++ [(0, f')]) := by
      simpa only [List.append_assoc] using hA
    simpa only [List.append_assoc, ptFib] using hA'.trans hmid

theorem ptFib_lift (hσ : IsUnitaryInvolution σ) (s : ℕ)
    (hconn : (dChamberSystem σ (s + 2)).Connected) {e : DChamber σ (s + 4)}
    {x' : FlipPt σ (s + 4)}
    (hx' : (flipGraph σ (s + 4)).Adj ((ptFib hσ.invol s).P e) x') :
    ∃ ρ f, IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0} e ρ ∧
      (dChamberSystem σ (s + 3)).adj 0 (galleryEnd e ρ) f ∧ (ptFib hσ.invol s).P f = x' := by
  have hΓc : FlipColl σ (e.line 0) x'.1 := hx'
  have hΓL : IsFlipLine σ (e.line 0 ⊔ x'.1) :=
    hΓc.isFlipLine (e.isFlipflopPt_line 0) x'.2
  let p₁ : Submodule K (Fin (s + 4) ⊕ Fin (s + 4) → K) :=
    (e.line 0 ⊔ x'.1) ⊓ flipOrth σ (e.line 0)
  have hpne : e.line 0 ≠ ⊥ := by
    intro hbot
    have h := (e.isFlipflopPt_line 0).2
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hpa : e.line 0 = K ∙ a :=
    eq_span_singleton_of_mem_of_finrank_eq_one (e.isFlipflopPt_line 0).2 ha ha0
  have haa : flipHerm σ a a ≠ 0 := by
    have hsub : IsFlipflopSub σ (K ∙ a) := by
      rw [← hpa]
      exact (e.isFlipflopPt_line 0).1
    exact ((isFlipflopSub_span_singleton_iff ha0).mp hsub).2
  have haL : a ∈ K ∙ a ⊔ x'.1 :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
  have hK : IsFlipflopSub σ
      ((K ∙ a : Submodule K (Fin (s + 4) ⊕ Fin (s + 4) → K)) ⊔ x'.1) := by
    rw [← hpa]
    exact hΓL.1
  have hΓK : Module.finrank K ↥(K ∙ a ⊔ x'.1) = 2 := by
    rw [← hpa]
    exact hΓL.2
  have hsplit : K ∙ a ⊔ p₁ = K ∙ a ⊔ x'.1 := by
    change K ∙ a ⊔ ((e.line 0 ⊔ x'.1) ⊓ flipOrth σ (e.line 0)) = K ∙ a ⊔ x'.1
    rw [hpa]
    exact span_sup_inf_flipOrth hσ.invol haL haa
  have hp₁ : IsFlipflopPt σ p₁ := by
    refine ⟨?_, ?_⟩
    · change IsFlipflopSub σ ((e.line 0 ⊔ x'.1) ⊓ flipOrth σ (e.line 0))
      rw [hpa]
      exact hK.inf_flipOrth_span hσ.invol haL haa
    · have hdisj : Disjoint (K ∙ a) p₁ := by
        change Disjoint (K ∙ a) ((e.line 0 ⊔ x'.1) ⊓ flipOrth σ (e.line 0))
        rw [hpa]
        exact (disjoint_span_flipOrth haa).mono_right inf_le_right
      have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a) p₁
      rw [hdisj.eq_bot, finrank_bot, add_zero, hsplit, hΓK,
        finrank_span_singleton ha0] at h
      omega
  have hle : p₁ ≤ LinearMap.range (e.pointMap hσ) := by
    refine e.le_range_pointMap hσ ?_ ?_
    · intro u hu v hv
      have huL : u ∈ e.line 0 ⊔ x'.1 := Submodule.mem_sup_left hu
      have hvL : v ∈ e.line 0 ⊔ x'.1 := hv.1
      have hsum : u + v ∈ e.line 0 ⊔ x'.1 :=
        Submodule.add_mem (e.line 0 ⊔ x'.1) huL hvL
      have h := hΓL.1.total (u + v) hsum
      rw [QuadraticMap.map_add (quadPlus (s + 4) K) u v,
        hΓL.1.total u huL, hΓL.1.total v hvL] at h
      simpa using h
    · intro u hu v hv
      exact (mem_flipOrth.mp hv.2) u hu
  have hmap₁ : (p₁.comap (e.pointMap hσ)).map (e.pointMap hσ) = p₁ :=
    Submodule.map_comap_eq_of_le hle
  have hp₁' : IsFlipflopPt σ (p₁.comap (e.pointMap hσ)) := by
    have hfin : Module.finrank K ↥(p₁.comap (e.pointMap hσ)) = 1 := by
      have hrank := rank_map_eq (e.pointMap_injective hσ) (p₁.comap (e.pointMap hσ))
      have hfin' : Module.finrank K
          ((p₁.comap (e.pointMap hσ)).map (e.pointMap hσ)) =
          Module.finrank K (p₁.comap (e.pointMap hσ)) := by
        simpa [Module.finrank] using congrArg Cardinal.toNat hrank
      rw [← hfin', hmap₁, hp₁.2]
    refine ⟨⟨?_, ?_⟩, hfin⟩
    · intro v hv
      have hv' : e.pointMap hσ v ∈ p₁ := hmap₁ ▸ Submodule.mem_map_of_mem hv
      rw [← e.quadPlus_pointMap hσ v]
      exact hp₁.1.total (e.pointMap hσ v) hv'
    · intro v hv hvorth
      apply e.pointMap_injective hσ
      rw [map_zero]
      refine hp₁.1.nondeg (e.pointMap hσ v) (hmap₁ ▸ Submodule.mem_map_of_mem hv) ?_
      intro w hw
      obtain ⟨w₀, hw₀, rfl⟩ := Submodule.mem_map.mp (hmap₁ ▸ hw)
      rw [e.flipHerm_pointMap hσ]
      exact hvorth w₀ hw₀
  obtain ⟨d₁, hd₁⟩ := DChamber.exists_line_zero_eq hσ (k := s + 2) (by omega) hp₁'
  let g : DChamber σ (s + 4) := e.pointEmb hσ d₁
  have hg0 : g.line 0 = e.line 0 := DChamber.pointEmb_line_zero hσ e d₁
  have hg1 : g.line 1 = p₁ := by
    have h := DChamber.pointEmb_line_succ hσ e d₁ (0 : Fin (s + 3))
    rw [hd₁, hmap₁] at h
    simpa using h
  have hxle : x'.1 ≤ g.line 0 ⊔ g.line 1 := by
    rw [hg0, hg1]
    have hEq : e.line 0 ⊔ p₁ = e.line 0 ⊔ x'.1 := by
      rw [hpa, hsplit]
    rw [hEq]
    exact le_sup_right
  obtain ⟨f, hadj, hfline⟩ :=
    DChamber.exists_adj_zero_line_eq hσ.invol (show 1 ≤ s + 3 by omega) g x'.2 hxle
  obtain ⟨ρ, hρ, hρend⟩ :=
    exists_fibre_gallery hσ (s + 1) hconn (c := e) (c' := g) (by rw [hg0])
  refine ⟨ρ, f, hρ, ?_, ?_⟩
  · rw [hρend]
    exact hadj
  · exact Subtype.ext hfline

theorem fibreNull_of_mem_solidWalks (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (s : ℕ) (R : (ptFib hσ.invol s).Rigid)
    (hconn : (dChamberSystem σ (s + 2)).Connected) {u : FlipPt σ (s + 4)}
    {c : (flipGraph σ (s + 4)).Walk u u} (hc : c ∈ solidWalks σ (s + 4) u) :
    (ptFib hσ.invol s).FibreNull c := by
  obtain ⟨M, hM, hsupp⟩ := mem_solidWalks_iff.mp hc
  obtain ⟨C, hCinj, hCf, hCl⟩ := hM.exists_solidChart (t := s + 1) hσ
  let F : Fib (dChamberSystem σ (s + 3)) (flipGraph σ (s + 4)) :=
    { P := (ptFib hσ.invol s).P
      a := 0
      J' := {i | i ≠ 0 ∧ i ∈ Set.range C.τ}
      Q := fun d => d ∈ Set.range C.emb
      step_Q := by
        intro i e g hi hadj hQe
        obtain ⟨j, hj⟩ : i ∈ Set.range C.τ := by
          rcases Set.mem_insert_iff.mp hi with rfl | hi
          · exact ⟨0, C.τ_zero⟩
          · exact hi.2
        obtain ⟨x, hx⟩ := hQe
        obtain ⟨y, hyadj, hy⟩ := hCl j x g (by rw [hx, hj]; exact hadj)
        exact ⟨y, hy⟩
      step_P := fun {i e g} hi hadj _ => (ptFib hσ.invol s).step_P hi.1 hadj trivial
      step_a := fun {e g} hadj _ => (ptFib hσ.invol s).step_a hadj trivial }
  have hlift : ∀ {e : DChamber σ (s + 4)} {x' : FlipPt σ (s + 4)},
      F.Q e → (F.P e).1 ≤ M → x'.1 ≤ M → (flipGraph σ (s + 4)).Adj (F.P e) x' →
      ∃ (ρ : List (Fin (s + 4) × DChamber σ (s + 4))) (f : DChamber σ (s + 4)),
        IsJGallery (dChamberSystem σ (s + 3)) F.J' e ρ ∧
        (dChamberSystem σ (s + 3)).adj 0 (galleryEnd e ρ) f ∧ F.P f = x' ∧ F.Q f := by
    intro e x' hQe hDe hDx' hAdj
    obtain ⟨c, rfl⟩ := hQe
    have hAdj' : FlipColl σ ((c.line 0).map C.φ) x'.1 := by
      simpa [F, ptFib, flipGraph, C.emb_line_zero c] using hAdj
    let x'' : Submodule K (Fin (s + 4) → K) := x'.1.comap C.φ
    have hx''map : x''.map C.φ = x'.1 :=
      Submodule.map_comap_eq_of_le (by rw [C.range_φ]; exact hDx')
    have hx''fin : Module.finrank K x'' = 1 := by
      have hrank := rank_map_eq C.injective_φ x''
      have hfin' : Module.finrank K (x''.map C.φ) = Module.finrank K x'' := by
        simpa [Module.finrank] using congrArg Cardinal.toNat hrank
      rw [← hfin', hx''map, x'.2.2]
    have hx''nd : Nondeg σ x'' :=
      (nondeg_iff_isFlipflopSub_map (W := x'') hσ.invol hM C.injective_φ C.range_φ
        C.flipHerm_φ).mpr (by rw [hx''map]; exact x'.2.1)
    have hx''ns : x'' ∈ nsPts σ (c.spanAt (posInt (s + 3) 0 (s + 3))) := by
      have hpos : posInt (s + 3) 0 (s + 3) = Finset.univ := by
        ext k
        simp only [mem_posInt, Finset.mem_univ, iff_true]
        exact ⟨Nat.zero_le _, by have := k.is_lt; omega⟩
      rw [hpos, Frame.spanAt_univ hσ]
      exact ⟨le_top, hx''fin, hx''nd⟩
    have hcol : IsCollinear σ (c.line 0) x'' :=
      (isCollinear_iff_flipColl hσ.invol hM C.injective_φ C.range_φ C.flipHerm_φ).mpr (by
        rw [hx''map]
        exact hAdj')
    obtain ⟨ρ₀, f₀, hρ₀, hadj₀, hf₀⟩ :=
      exists_edge_lift hσ hK (by omega : 3 ≤ q) (n := s + 3) (i := 0) (b := s + 3)
        (by omega) (by omega) (e := c) hx''ns hcol
    have hρgal : IsJGallery (dChamberSystem σ (s + 3)) F.J' (C.emb c)
        (galleryMapT C.τ C.emb ρ₀) := by
      refine ⟨hCf.isGallery hρ₀.1, ?_⟩
      intro j hj
      obtain ⟨i, hi, rfl⟩ := (mem_galleryType_galleryMapT C.τ C.emb ρ₀ j).1 hj
      have hi1 : (1 : ℕ) ≤ (i : ℕ) := (hρ₀.2 i hi).1
      have hi0 : i ≠ 0 := by
        intro h
        rw [h] at hi1
        simp at hi1
      refine ⟨?_, ⟨i, rfl⟩⟩
      intro hzero
      exact hi0 (C.injective_τ (by rw [hzero, C.τ_zero]))
    have hadjF : (dChamberSystem σ (s + 3)).adj 0
        (galleryEnd (C.emb c) (galleryMapT C.τ C.emb ρ₀)) (C.emb f₀) := by
      have h := hCf 0 (galleryEnd c ρ₀) f₀ hadj₀
      rw [C.τ_zero] at h
      rwa [← galleryEnd_galleryMapT C.τ C.emb c ρ₀] at h
    have hPf : F.P (C.emb f₀) = x' := by
      apply Subtype.ext
      show (C.emb f₀).line 0 = x'.1
      rw [C.emb_line_zero, show f₀.line 0 = x'' from by simpa using hf₀, hx''map]
    exact ⟨galleryMapT C.τ C.emb ρ₀, C.emb f₀, hρgal, hadjF, hPf, ⟨f₀, rfl⟩⟩
  have huM : u.1 ≤ M := hsupp u c.start_mem_support
  let A : Submodule K (Fin (s + 4) → K) := u.1.comap C.φ
  have hAdef : A.map C.φ = u.1 :=
    Submodule.map_comap_eq_of_le (by rw [C.range_φ]; exact huM)
  have hAnd : Nondeg σ A :=
    (nondeg_iff_isFlipflopSub_map (W := A) hσ.invol hM C.injective_φ C.range_φ
      C.flipHerm_φ).mpr (by rw [hAdef]; exact u.2.1)
  have hAdim : Module.finrank K A = 1 := by
    have hrank := rank_map_eq C.injective_φ A
    have hfin' : Module.finrank K (A.map C.φ) = Module.finrank K A := by
      simpa [Module.finrank] using congrArg Cardinal.toNat hrank
    rw [← hfin', hAdef, u.2.2]
  have hAle : A ≤ (stdFrame σ (s + 4)).spanAt (posInt (s + 3) 0 (s + 3)) := by
    have hpos : posInt (s + 3) 0 (s + 3) = Finset.univ := by
      ext k
      simp only [mem_posInt, Finset.mem_univ, iff_true]
      exact ⟨Nat.zero_le _, by have := k.is_lt; omega⟩
    rw [hpos, Frame.spanAt_univ hσ]
    exact le_top
  obtain ⟨c₁, hc₁res, hc₁line, -⟩ :=
    exists_adapted hσ hK (by omega : 3 ≤ q) 0 0 (s + 3) (by omega) (by omega)
      (stdFrame σ (s + 4)) A hAle hAnd (by simpa using hAdim) A ⟨le_rfl, hAdim, hAnd⟩
  have hline0 : c₁.line 0 = A := by simpa using hc₁line
  have hc₁map : (c₁.line 0).map C.φ = u.1 := by rw [hline0, hAdef]
  let e₁ : DChamber σ (s + 4) := C.emb c₁
  have hPe₁ : F.P e₁ = u := by
    apply Subtype.ext
    show (C.emb c₁).line 0 = u.1
    rw [C.emb_line_zero, hc₁map]
  obtain ⟨γ₁, hγ₁⟩ :=
    F.exists_lift (D := fun v : FlipPt σ (s + 4) => v.1 ≤ M) hlift c hsupp e₁
      ⟨c₁, rfl⟩ hPe₁
  have hl₁ : (ptFib hσ.invol s).Lift c e₁ γ₁ :=
    Fib.Lift.mono (F := F) (F' := ptFib hσ.invol s) rfl rfl (fun i hi => hi.1) hγ₁
  let e₂ : DChamber σ (s + 4) := galleryEnd e₁ γ₁
  have hQe₂ : F.Q e₂ := hγ₁.Q_galleryEnd ⟨c₁, rfl⟩
  obtain ⟨c₂, hc₂⟩ := hQe₂
  have hPe₂ : F.P e₂ = u := hγ₁.end_eq ⟨c₁, rfl⟩
  have hline₂ : (C.emb c₂).line 0 = u.1 := by
    have h : e₂.line 0 = u.1 := congrArg Subtype.val hPe₂
    rwa [← hc₂] at h
  have hline : c₂.line 0 = c₁.line 0 := by
    apply Submodule.map_injective_of_injective C.injective_φ
    rw [← C.emb_line_zero c₂, hline₂, hc₁map]
  have hres : c₁ ∈ (frameSystem σ (s + 3)).residue (typeInt (s + 3) 1 (s + 3)) c₂ :=
    mem_residue_typeInt hσ hK (by omega : 3 ≤ q) (s + 2) 1 (s + 3) (by omega) (by omega) c₂ c₁
      (by
        intro k hk
        have hk0 : k = 0 := by
          by_contra hk0
          apply hk
          rw [mem_posInt]
          constructor
          · have hkval : (k : ℕ) ≠ 0 := fun h => hk0 (Fin.ext (by simpa using h))
            omega
          · have := k.is_lt
            omega
        rw [hk0]
        exact hline.symm)
  obtain ⟨η, hηgal, hηJ, hηend⟩ := hres
  have hτ₁gal : IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0} e₂
      (galleryMapT C.τ C.emb η) := by
    have hgal : (dChamberSystem σ (s + 3)).IsGallery e₂ (galleryMapT C.τ C.emb η) := by
      rw [← hc₂]
      exact hCf.isGallery hηgal
    refine ⟨hgal, ?_⟩
    intro j hj
    obtain ⟨i, hi, rfl⟩ := (mem_galleryType_galleryMapT C.τ C.emb η j).1 hj
    have hi1 : (1 : ℕ) ≤ (i : ℕ) := (hηJ i hi).1
    have hi0 : i ≠ 0 := by
      intro h
      rw [h] at hi1
      simp at hi1
    intro hzero
    exact hi0 (C.injective_τ (by rw [hzero, C.τ_zero]))
  have hτ₁end : galleryEnd e₂ (galleryMapT C.τ C.emb η) = e₁ := by
    rw [← hc₂, galleryEnd_galleryMapT, hηend]
  have hclosed : (dChamberSystem σ (s + 3)).IsGallery e₁
      (γ₁ ++ galleryMapT C.τ C.emb η) := hl₁.isJGallery.1.append hτ₁gal.1
  have htypes : ∀ j ∈ galleryType (γ₁ ++ galleryMapT C.τ C.emb η), j ∈ Set.range C.τ := by
    intro j hj
    rw [galleryType_append, List.mem_append] at hj
    rcases hj with hj | hj
    · rcases Set.mem_insert_iff.mp (hγ₁.isJGallery.2 j hj) with rfl | h
      · exact ⟨0, C.τ_zero⟩
      · exact h.2
    · obtain ⟨i, -, rfl⟩ := (mem_galleryType_galleryMapT C.τ C.emb η j).1 hj
      exact ⟨i, rfl⟩
  have hend : galleryEnd e₁ (γ₁ ++ galleryMapT C.τ C.emb η) = e₁ := by
    rw [galleryEnd_append, hτ₁end]
  have hnull : (dChamberSystem σ (s + 3)).TwoHomotopic e₁
      (γ₁ ++ galleryMapT C.τ C.emb η) [] :=
    twoHomotopic_nil_of_isPanelLift hCf hCl hCinj
      (frameSystem_simplyTwoConnected hσ hK hq (s + 3)) hclosed htypes hend
  have hconn₁ : ∀ {e e' : DChamber σ (s + 4)}, (ptFib hσ.invol s).Q e →
      (ptFib hσ.invol s).Q e' → (ptFib hσ.invol s).P e = (ptFib hσ.invol s).P e' →
      ∃ τ, IsJGallery (dChamberSystem σ (s + 3)) {i | i ≠ 0} e τ ∧ galleryEnd e τ = e' :=
    fun {e e'} _ _ hP => exists_fibre_gallery hσ (s + 1) hconn (congrArg Subtype.val hP)
  exact R.fibreNull_of_exists hconn₁ trivial hl₁ hτ₁gal hτ₁end hnull

theorem connected_dChamberSystem_succ (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (s : ℕ)
    (hconn : (dChamberSystem σ (s + 2)).Connected) : (dChamberSystem σ (s + 3)).Connected := by
  intro x y
  have hG : (flipGraph σ (s + 4)).Connected := flipGraph_connected hσ hK hq (by omega)
  obtain ⟨w⟩ := hG.preconnected ((ptFib hσ.invol s).P x) ((ptFib hσ.invol s).P y)
  obtain ⟨γ, hγ⟩ := (ptFib hσ.invol s).exists_lift (D := fun _ => True)
    (fun {e x'} _ _ _ hΓ => by
      obtain ⟨ρ, f, h1, h2, h3⟩ := ptFib_lift hσ s hconn hΓ
      exact ⟨ρ, f, h1, h2, h3, trivial⟩) w (fun _ _ => trivial) x trivial rfl
  have hend : (ptFib hσ.invol s).P (galleryEnd x γ) = (ptFib hσ.invol s).P y :=
    hγ.end_eq trivial
  obtain ⟨τ, hτ, hτe⟩ := exists_fibre_gallery hσ (s + 1) hconn (congrArg Subtype.val hend)
  refine ⟨γ ++ τ, hγ.isJGallery.1.append hτ.1, ?_⟩
  rw [galleryEnd_append, hτe]

theorem simplyTwoConnected_dChamberSystem_succ (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (s : ℕ)
    (hsc : (dChamberSystem σ (s + 2)).SimplyTwoConnected)
    (hconn : (dChamberSystem σ (s + 2)).Connected)
    (hconn' : (dChamberSystem σ (s + 1)).Connected)
    (htriv : CycleTrivial (solidWalks σ (s + 4))) :
    (dChamberSystem σ (s + 3)).SimplyTwoConnected := by
  let F := ptFib hσ.invol s
  have R := ptFib_rigid hσ s hsc hconn'
  intro x γ hγ hend
  refine R.twoHomotopic_nil (E := solidWalks σ (s + 4))
    (fun _ _ hc => fibreNull_of_mem_solidWalks hσ hK hq s R hconn hc)
    (fun {e x'} _ hΓ => by
      obtain ⟨ρ, f, h1, h2, h3⟩ := ptFib_lift hσ s hconn hΓ
      exact ⟨ρ, f, h1, h2, h3, trivial⟩)
    htriv (trivial : F.Q x) ⟨hγ, ?_⟩ hend
  intro i _
  change i ∈ insert (0 : Fin (s + 4)) {i | i ≠ 0}
  by_cases hi : i = 0
  · exact Set.mem_insert_iff.mpr (Or.inl hi)
  · exact Set.mem_insert_iff.mpr (Or.inr hi)

theorem connected_dChamberSystem (hσ : IsUnitaryInvolution σ) [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) {m : ℕ} (hm : 1 ≤ m) :
    (dChamberSystem σ m).Connected := by
  induction m, hm using Nat.le_induction with
  | base => exact connected_dChamberSystem_one hσ.invol
  | succ m hm ih =>
    by_cases hm1 : m = 1
    · subst hm1
      exact connected_dChamberSystem_two hσ hK (by omega)
    · have h := connected_dChamberSystem_succ hσ hK hq (s := m - 2) ?_
      · rwa [show m - 2 + 3 = m + 1 by omega] at h
      · rwa [show m - 2 + 2 = m by omega]

theorem simplyTwoConnected_dChamberSystem_of_cycleTrivial (hσ : IsUnitaryInvolution σ) [Finite K]
    [CharP K 2] {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    (htriv : ∀ n, 4 ≤ n → CycleTrivial (solidWalks σ n)) {m : ℕ} (hm : 2 ≤ m) :
    (dChamberSystem σ m).SimplyTwoConnected := by
  induction m, hm using Nat.le_induction with
  | base => exact simplyTwoConnected_dChamberSystem_two hσ hK hq
  | succ m hm ih =>
    have h := simplyTwoConnected_dChamberSystem_succ hσ hK hq (s := m - 2)
      (by rwa [show m - 2 + 2 = m by omega])
      (connected_dChamberSystem hσ hK hq (by omega))
      (connected_dChamberSystem hσ hK hq (by omega))
      (by rw [show m - 2 + 4 = m + 2 by omega]; exact htriv (m + 2) (by omega))
    rwa [show m - 2 + 3 = m + 1 by omega] at h

end CFSG.ClassicalInvolution.PhanDn

end
