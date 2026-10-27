module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (ShareFour rankTwoSpan)
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Defs

variable {Y : Type} [Group Y]

@[expose] def starFrameSet (R : Subgroup Y) (t : Y) : Set (Subgroup Y) :=
  {B | ∃ (g : Y) (J K'' : Subgroup Y) (u w : Y), StarFrameAt R t J K'' u w ∧
    B = conjSub g (Subgroup.closure ({t, u, w} : Set Y))}

@[expose] def starVert (R : Subgroup Y) (t : Y) (B : Subgroup Y) : Set Y :=
  {a | ∃ (g : Y) (J K'' : Subgroup Y) (u w : Y), StarFrameAt R t J K'' u w ∧
    B = conjSub g (Subgroup.closure ({t, u, w} : Set Y)) ∧ (a = g * t * g⁻¹ ∨ a = g * u * g⁻¹)}

@[expose] def StarLinkStep (R : Subgroup Y) (t : Y) (J J' : Subgroup Y) : Prop :=
  ∃ (K'' : Subgroup Y) (u w : Y), StarFrameAt R t J K'' u w ∧
    ∃ g ∈ Subgroup.centralizer ({t} : Set Y),
      g ∈ rankTwoSpan (Subgroup.closure ({t, u, w} : Set Y)) ∧ J' = conjSub g J

theorem starFrameSet_conj {R : Subgroup Y} {t : Y} {B : Subgroup Y} (hB : B ∈ starFrameSet R t)
    (h : Y) : B.map (MulAut.conj h).toMonoidHom ∈ starFrameSet R t := by
  obtain ⟨g, J, K'', u, w, hF, rfl⟩ := hB
  exact ⟨h * g, J, K'', u, w, hF, by rw [conjSub_mul]; rfl⟩

theorem closure_mem_starFrameSet {R : Subgroup Y} {t : Y} {J K'' : Subgroup Y} {u w : Y}
    (hF : StarFrameAt R t J K'' u w) :
    Subgroup.closure ({t, u, w} : Set Y) ∈ starFrameSet R t :=
  ⟨1, J, K'', u, w, hF, (conjSub_one _).symm⟩

theorem mem_closure_three_left (a b c : Y) : a ∈ Subgroup.closure ({a, b, c} : Set Y) ∧
    b ∈ Subgroup.closure ({a, b, c} : Set Y) ∧ c ∈ Subgroup.closure ({a, b, c} : Set Y) :=
  ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp)⟩

theorem conj_mem_conjSub {B : Subgroup Y} {x : Y} (hx : x ∈ B) (g : Y) :
    g * x * g⁻¹ ∈ conjSub g B := by
  rw [mem_conjSub_iff]
  simpa [mul_assoc] using hx

theorem starVert_conj {R : Subgroup Y} {t : Y} {B : Subgroup Y} {a : Y} (h : a ∈ starVert R t B)
    (h' : Y) : h' * a * h'⁻¹ ∈ starVert R t (B.map (MulAut.conj h').toMonoidHom) := by
  obtain ⟨g, J, K'', u, w, hF, rfl, ha⟩ := h
  refine ⟨h' * g, J, K'', u, w, hF, by rw [conjSub_mul]; rfl, ?_⟩
  rcases ha with rfl | rfl
  · left; group
  · right; group

end Defs

section Cit3


@[expose] def TightStar289GenR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (StarLinkStep R t) J J'

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_pair_of_mem_starVert (hL : TightLargeHypR r n Y R S t) {A : Subgroup Y}
    (hA : t ∈ starVert R t A) :
    A ∈ starFrameSet R t ∧ ∃ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∃ u₁ : Y, IsUniqueInvolution J₁ u₁ ∧ t ∈ A ∧ u₁ ∈ A := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  obtain ⟨g, J, K'', u, w, hF, rfl, h⟩ := hA
  have hm := mem_closure_three_left t u w
  refine ⟨⟨g, J, K'', u, w, hF, rfl⟩, ?_⟩
  rcases h with h | h
  · have hgt : g * t * g⁻¹ = t := h.symm
    have hg : g ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [hgt]
    have h1 := conj_mem_conjSub hm.1 g
    rw [← h] at h1
    exact ⟨conjSub g J, conjSub_mem_omegaNbr_core hL hF.memJ hg, g * u * g⁻¹, hF.invJ.conj g,
      h1, conj_mem_conjSub hm.2.1 g⟩
  · have hJg : conjSub g J = tightCore R :=
      eq_core_of_isUniqueInvolution hL (hΩ.conjInvariant g J hF.memJ.1) (by
        rw [h]
        exact hF.invJ.conj g)
    have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (CoreAssembly.mem_conjClass_self _)
      hF.memJ.1 hF.memJ
    have h1 := omegaNbr_conj hΩ.conjInvariant hKJ g
    rw [hJg] at h1
    have h2 := conj_mem_conjSub hm.2.1 g
    rw [← h] at h2
    exact ⟨conjSub g (tightCore R), h1, g * t * g⁻¹, ht.conj g, h2, conj_mem_conjSub hm.1 g⟩

theorem star_link_at_core (hL : TightLargeHypR r n Y R S t)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (StarLinkStep R t) J J')
    {A A' : Subgroup Y} (hA : t ∈ starVert R t A) (hA' : t ∈ starVert R t A') :
    Relation.ReflTransGen
      (fun X X' => X ∈ starFrameSet R t ∧ X' ∈ starFrameSet R t ∧ ShareFour X X') A A' := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hinv : ∀ B ∈ starFrameSet R t, ∀ g : Y, B.map (MulAut.conj g).toMonoidHom ∈
      starFrameSet R t := fun B hB g => starFrameSet_conj hB g
  obtain ⟨hAm, J₁, hJ₁, u₁, hu₁, htA, hu₁A⟩ := exists_pair_of_mem_starVert hL hA
  obtain ⟨hA'm, J₂, hJ₂, u₂, hu₂, htA', hu₂A'⟩ := exists_pair_of_mem_starVert hL hA'
  have key : ∀ J, Relation.ReflTransGen (StarLinkStep R t) J₁ J →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
        ∀ u : Y, IsUniqueInvolution J u →
          ∀ A'' ∈ starFrameSet R t, t ∈ A'' → u ∈ A'' →
            Relation.ReflTransGen
              (fun X X' => X ∈ starFrameSet R t ∧ X' ∈ starFrameSet R t ∧ ShareFour X X')
              A A'' := by
    intro J hJ
    induction hJ with
    | refl =>
      refine ⟨hJ₁, fun u hu A'' hA'' htA'' huA'' => ?_⟩
      obtain rfl := hu.eq hu₁
      exact Relation.ReflTransGen.single ⟨hAm, hA'', shareFour_of_mem_pair hL hJ₁ hu
        htA hu₁A htA'' huA''⟩
    | @tail J J'' _ hstep ih =>
      obtain ⟨hJΩ, hJlink⟩ := ih
      obtain ⟨K'', u, w, hF, g, hgt, hg, rfl⟩ := hstep
      have hm := mem_closure_three_left t u w
      have hB := closure_mem_starFrameSet (t := t) hF
      have hAB := hJlink u hF.invJ _ hB hm.1 hm.2.1
      have hBg := Theorem5.reflTransGen_shareFour_map_of_mem_rankTwoSpan hinv hB hg
      have hgt' : g * t * g⁻¹ = t := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hgt, mul_inv_cancel_right]
      have hJ'' := conjSub_mem_omegaNbr_core hL hJΩ hgt
      refine ⟨hJ'', fun u'' hu'' A'' hA'' htA'' huA'' => (hAB.trans hBg).tail
        ⟨hinv _ hB g, hA'', ?_⟩⟩
      have e : u'' = g * u * g⁻¹ := hu''.eq (hF.invJ.conj g)
      refine shareFour_of_mem_pair hL hJ'' hu'' ?_ ?_ htA'' huA''
      · have h1 := conj_mem_conjSub hm.1 g
        rwa [hgt'] at h1
      · rw [e]
        exact conj_mem_conjSub hm.2.1 g
  exact (key J₂ (hgen J₁ hJ₁ J₂ hJ₂)).2 u₂ hu₂ _ hA'm htA' hu₂A'

theorem star_link_at_vertex (hL : TightLargeHypR r n Y R S t)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (StarLinkStep R t) J J') :
    ∀ a ∈ memberInvSet (CoreAssembly.conjClass (tightCore R)),
      ∀ A ∈ starFrameSet R t, ∀ A' ∈ starFrameSet R t, a ∈ starVert R t A → a ∈ starVert R t A' →
        Relation.ReflTransGen
          (fun X X' => X ∈ starFrameSet R t ∧ X' ∈ starFrameSet R t ∧ ShareFour X X') A A' := by
  rintro a ⟨M, hM, ha⟩ A - A' - haA haA'
  have hd := hL.datum
  obtain ⟨g, hgM'⟩ := hM
  have hgM : conjSub g (tightCore R) = M := hgM'
  have hga : g * t * g⁻¹ = a := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgM] at h1
    exact h1.eq ha
  have hta : g⁻¹ * a * g⁻¹⁻¹ = t := by
    rw [← hga]
    group
  have h1 := starVert_conj haA g⁻¹
  have h2 := starVert_conj haA' g⁻¹
  rw [hta] at h1 h2
  have hc := reflTransGen_shareFour_map (fun B hB g => starFrameSet_conj hB g)
    (star_link_at_core hL hgen h1 h2) g
  rwa [map_conj_map_conj_inv, map_conj_map_conj_inv] at hc

theorem starFramesV (hL : TightLargeHypR r n Y R S t)
    (hstar : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ a : Y, IsUniqueInvolution M a →
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M, ∀ b : Y, IsUniqueInvolution N b →
        ∃ A ∈ starFrameSet R t, a ∈ starVert R t A ∧ b ∈ starVert R t A := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  intro M hM a ha N hN b hb
  obtain ⟨g, hgM'⟩ := hM
  have hgM : conjSub g (tightCore R) = M := hgM'
  have hga : g * t * g⁻¹ = a := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgM] at h1
    exact h1.eq ha
  have hN' : conjSub g⁻¹ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hΩ.conjInvariant hN g⁻¹
    rwa [← hgM, conjSub_inv_conjSub] at h1
  obtain ⟨K'', w, hF⟩ := hstar _ hN' _ (hb.conj g⁻¹)
  refine ⟨conjSub g (Subgroup.closure ({t, g⁻¹ * b * g⁻¹⁻¹, w} : Set Y)),
    ⟨g, _, K'', _, w, hF, rfl⟩, ⟨g, _, K'', _, w, hF, rfl, Or.inl hga.symm⟩,
    ⟨g, _, K'', _, w, hF, rfl, Or.inr (by group)⟩⟩

theorem starFrames_of (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hH : ∀ (J K'' : Subgroup Y) (u w : Y), StarFrameAt R t J K'' u w →
      Hyp51 (Subgroup.closure ({t, u, w} : Set Y)))
    (hstar : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (StarLinkStep R t) J J') :
    FramesAtEdges (CoreAssembly.conjClass (tightCore R)) (tightCore R) t (starFrameSet R t) ∧
      FramesHyp51 (starFrameSet R t) ∧ FramesConnected (starFrameSet R t) := by
  have hΩ := hL.datum.hypOmegaGen
  refine ⟨fun J hJ u hu => ?_, ?_, fun B hB g => starFrameSet_conj hB g, fun B hB B' hB' => ?_⟩
  · obtain ⟨K'', w, hF⟩ := hstar J hJ u hu
    exact ⟨_, closure_mem_starFrameSet (t := t) hF, closure_pair_le_closure_triangle⟩
  · rintro B ⟨g, J, K'', u, w, hF, rfl⟩
    exact ExactLayer.hyp51_conj_mp g (hH J K'' u w hF)
  have hv := vtxAdjFn_of_dConnected hΩ hc (starFramesV hL hstar)
  have hlk := star_link_at_vertex hL hgen
  obtain ⟨g, J, K'', u, w, hF, hBx⟩ := id hB
  obtain ⟨g', J', K''', u', w', hF', hBx'⟩ := id hB'
  exact reflTransGen_shareFour_of_vertexFn (starVert R t) hv hlk hB hB'
    ⟨conjSub g (tightCore R), ⟨g, rfl⟩, hL.datum.isUniqueInvolution_core.conj g⟩
    ⟨g, J, K'', u, w, hF, hBx, Or.inl rfl⟩
    ⟨conjSub g' (tightCore R), ⟨g', rfl⟩, hL.datum.isUniqueInvolution_core.conj g'⟩
    ⟨g', J', K''', u', w', hF', hBx', Or.inl rfl⟩

theorem alphaOf_eq_bot_of_starFrames (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hH : ∀ (J K'' : Subgroup Y) (u w : Y), StarFrameAt R t J K'' u w →
      Hyp51 (Subgroup.closure ({t, u, w} : Set Y)))
    (hstar : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (StarLinkStep R t) J J') :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
  obtain ⟨ha, hb, hcon⟩ := starFrames_of hL hc hH hstar hgen
  exact alphaOf_eq_bot_of_frames hL ha hb hcon

theorem alphaOf_eq_bot_of_star289 (hz : TightStar289ZR r n) (ht : TightStar289TR r n)
    (hzt : TightStar289ZTR r n) (ho : TightStar289OrbR r n) (hg : TightStar289GenR r n)
    (hL : TightLargeHypR r n Y R S t) (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hA : ¬ TriNbrAll R t) (hcase : LinkS3S4 R t)
    (hstar : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ (K'' : Subgroup Y) (w : Y), StarFrameAt R t J K'' u w) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ :=
  alphaOf_eq_bot_of_starFrames hL hc
    (fun _ _ _ _ hF => hyp51_starFrame_of_residuals hz ht hzt ho hL hc hA hcase hF) hstar
    (hg Y R S t hL hc hA hcase)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
