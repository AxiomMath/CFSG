module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9F

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (ShareFour rankTwoSpan)
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Defs

variable {Y : Type} [Group Y]

@[expose] def frameSetP (P : Subgroup Y → Y → Y → Prop) (t : Y) : Set (Subgroup Y) :=
  {B | ∃ (g : Y) (J : Subgroup Y) (u w : Y), P J u w ∧
    B = conjSub g (Subgroup.closure ({t, u, w} : Set Y))}

@[expose] def frameVertP (P : Subgroup Y → Y → Y → Prop) (t : Y) (B : Subgroup Y) : Set Y :=
  {a | ∃ (g : Y) (J : Subgroup Y) (u w : Y), P J u w ∧
    B = conjSub g (Subgroup.closure ({t, u, w} : Set Y)) ∧ (a = g * t * g⁻¹ ∨ a = g * u * g⁻¹)}

@[expose] def FrameLinkStepP (P : Subgroup Y → Y → Y → Prop) (t : Y) (J J' : Subgroup Y) :
    Prop :=
  ∃ (u w : Y), P J u w ∧ ∃ g ∈ Subgroup.centralizer ({t} : Set Y),
    g ∈ rankTwoSpan (Subgroup.closure ({t, u, w} : Set Y)) ∧ J' = conjSub g J

variable {P : Subgroup Y → Y → Y → Prop} {t : Y}

theorem frameSetP_conj {B : Subgroup Y} (hB : B ∈ frameSetP P t) (h : Y) :
    B.map (MulAut.conj h).toMonoidHom ∈ frameSetP P t := by
  obtain ⟨g, J, u, w, hF, rfl⟩ := hB
  exact ⟨h * g, J, u, w, hF, by rw [conjSub_mul]; rfl⟩

theorem closure_mem_frameSetP {J : Subgroup Y} {u w : Y} (hF : P J u w) :
    Subgroup.closure ({t, u, w} : Set Y) ∈ frameSetP P t :=
  ⟨1, J, u, w, hF, (conjSub_one _).symm⟩

theorem frameVertP_conj {B : Subgroup Y} {a : Y} (h : a ∈ frameVertP P t B) (h' : Y) :
    h' * a * h'⁻¹ ∈ frameVertP P t (B.map (MulAut.conj h').toMonoidHom) := by
  obtain ⟨g, J, u, w, hF, rfl, ha⟩ := h
  refine ⟨h' * g, J, u, w, hF, by rw [conjSub_mul]; rfl, ?_⟩
  rcases ha with rfl | rfl
  · left; group
  · right; group

end Defs

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {P : Subgroup Y → Y → Y → Prop}

theorem exists_pair_of_mem_frameVertP (hL : TightLargeHypR r n Y R S t)
    (hP : ∀ J u w, P J u w →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧ IsUniqueInvolution J u)
    {A : Subgroup Y} (hA : t ∈ frameVertP P t A) :
    A ∈ frameSetP P t ∧ ∃ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∃ u₁ : Y, IsUniqueInvolution J₁ u₁ ∧ t ∈ A ∧ u₁ ∈ A := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  obtain ⟨g, J, u, w, hF, rfl, h⟩ := hA
  obtain ⟨hJ, hu⟩ := hP J u w hF
  have hm := mem_closure_three_left t u w
  refine ⟨⟨g, J, u, w, hF, rfl⟩, ?_⟩
  rcases h with h | h
  · have hgt : g * t * g⁻¹ = t := h.symm
    have hg : g ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [hgt]
    have h1 := conj_mem_conjSub hm.1 g
    rw [← h] at h1
    exact ⟨conjSub g J, conjSub_mem_omegaNbr_core hL hJ hg, g * u * g⁻¹, hu.conj g,
      h1, conj_mem_conjSub hm.2.1 g⟩
  · have hJg : conjSub g J = tightCore R :=
      eq_core_of_isUniqueInvolution hL (hΩ.conjInvariant g J hJ.1) (by
        rw [h]
        exact hu.conj g)
    have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (CoreAssembly.mem_conjClass_self _)
      hJ.1 hJ
    have h1 := omegaNbr_conj hΩ.conjInvariant hKJ g
    rw [hJg] at h1
    have h2 := conj_mem_conjSub hm.2.1 g
    rw [← h] at h2
    exact ⟨conjSub g (tightCore R), h1, g * t * g⁻¹, ht.conj g, h2, conj_mem_conjSub hm.1 g⟩

theorem link_at_coreP (hL : TightLargeHypR r n Y R S t)
    (hP : ∀ J u w, P J u w →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧ IsUniqueInvolution J u)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (FrameLinkStepP P t) J J')
    {A A' : Subgroup Y} (hA : t ∈ frameVertP P t A) (hA' : t ∈ frameVertP P t A') :
    Relation.ReflTransGen
      (fun X X' => X ∈ frameSetP P t ∧ X' ∈ frameSetP P t ∧ ShareFour X X') A A' := by
  have hinv : ∀ B ∈ frameSetP P t, ∀ g : Y, B.map (MulAut.conj g).toMonoidHom ∈
      frameSetP P t := fun B hB g => frameSetP_conj hB g
  obtain ⟨hAm, J₁, hJ₁, u₁, hu₁, htA, hu₁A⟩ := exists_pair_of_mem_frameVertP hL hP hA
  obtain ⟨hA'm, J₂, hJ₂, u₂, hu₂, htA', hu₂A'⟩ := exists_pair_of_mem_frameVertP hL hP hA'
  have key : ∀ J, Relation.ReflTransGen (FrameLinkStepP P t) J₁ J →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
        ∀ u : Y, IsUniqueInvolution J u →
          ∀ A'' ∈ frameSetP P t, t ∈ A'' → u ∈ A'' →
            Relation.ReflTransGen
              (fun X X' => X ∈ frameSetP P t ∧ X' ∈ frameSetP P t ∧ ShareFour X X')
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
      obtain ⟨u, w, hF, g, hgt, hg, rfl⟩ := hstep
      have huJ := (hP J u w hF).2
      have hm := mem_closure_three_left t u w
      have hB := closure_mem_frameSetP (t := t) hF
      have hAB := hJlink u huJ _ hB hm.1 hm.2.1
      have hBg := Theorem5.reflTransGen_shareFour_map_of_mem_rankTwoSpan hinv hB hg
      have hgt' : g * t * g⁻¹ = t := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hgt, mul_inv_cancel_right]
      have hJ'' := conjSub_mem_omegaNbr_core hL hJΩ hgt
      refine ⟨hJ'', fun u'' hu'' A'' hA'' htA'' huA'' => (hAB.trans hBg).tail
        ⟨hinv _ hB g, hA'', ?_⟩⟩
      have e : u'' = g * u * g⁻¹ := hu''.eq (huJ.conj g)
      refine shareFour_of_mem_pair hL hJ'' hu'' ?_ ?_ htA'' huA''
      · have h1 := conj_mem_conjSub hm.1 g
        rwa [hgt'] at h1
      · rw [e]
        exact conj_mem_conjSub hm.2.1 g
  exact (key J₂ (hgen J₁ hJ₁ J₂ hJ₂)).2 u₂ hu₂ _ hA'm htA' hu₂A'

theorem link_at_vertexP (hL : TightLargeHypR r n Y R S t)
    (hP : ∀ J u w, P J u w →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧ IsUniqueInvolution J u)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (FrameLinkStepP P t) J J') :
    ∀ a ∈ memberInvSet (CoreAssembly.conjClass (tightCore R)),
      ∀ A ∈ frameSetP P t, ∀ A' ∈ frameSetP P t, a ∈ frameVertP P t A →
        a ∈ frameVertP P t A' →
        Relation.ReflTransGen
          (fun X X' => X ∈ frameSetP P t ∧ X' ∈ frameSetP P t ∧ ShareFour X X') A A' := by
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
  have h1 := frameVertP_conj haA g⁻¹
  have h2 := frameVertP_conj haA' g⁻¹
  rw [hta] at h1 h2
  have hc := reflTransGen_shareFour_map (fun B hB g => frameSetP_conj hB g)
    (link_at_coreP hL hP hgen h1 h2) g
  rwa [map_conj_map_conj_inv, map_conj_map_conj_inv] at hc

theorem framesVP (hL : TightLargeHypR r n Y R S t)
    (hex : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ w : Y, P J u w) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ a : Y, IsUniqueInvolution M a →
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M, ∀ b : Y, IsUniqueInvolution N b →
        ∃ A ∈ frameSetP P t, a ∈ frameVertP P t A ∧ b ∈ frameVertP P t A := by
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
  obtain ⟨w, hF⟩ := hex _ hN' _ (hb.conj g⁻¹)
  refine ⟨conjSub g (Subgroup.closure ({t, g⁻¹ * b * g⁻¹⁻¹, w} : Set Y)),
    ⟨g, _, _, w, hF, rfl⟩, ⟨g, _, _, w, hF, rfl, Or.inl hga.symm⟩,
    ⟨g, _, _, w, hF, rfl, Or.inr (by group)⟩⟩

theorem framesP_of (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hP : ∀ J u w, P J u w →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧ IsUniqueInvolution J u)
    (hH : ∀ (J : Subgroup Y) (u w : Y), P J u w → Hyp51 (Subgroup.closure ({t, u, w} : Set Y)))
    (hex : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ w : Y, P J u w)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (FrameLinkStepP P t) J J') :
    FramesAtEdges (CoreAssembly.conjClass (tightCore R)) (tightCore R) t (frameSetP P t) ∧
      FramesHyp51 (frameSetP P t) ∧ FramesConnected (frameSetP P t) := by
  have hΩ := hL.datum.hypOmegaGen
  refine ⟨fun J hJ u hu => ?_, ?_, fun B hB g => frameSetP_conj hB g, fun B hB B' hB' => ?_⟩
  · obtain ⟨w, hF⟩ := hex J hJ u hu
    exact ⟨_, closure_mem_frameSetP (t := t) hF, closure_pair_le_closure_triangle⟩
  · rintro B ⟨g, J, u, w, hF, rfl⟩
    exact ExactLayer.hyp51_conj_mp g (hH J u w hF)
  have hv := vtxAdjFn_of_dConnected hΩ hc (framesVP hL hex)
  have hlk := link_at_vertexP hL hP hgen
  obtain ⟨g, J, u, w, hF, hBx⟩ := id hB
  obtain ⟨g', J', u', w', hF', hBx'⟩ := id hB'
  exact reflTransGen_shareFour_of_vertexFn (frameVertP P t) hv hlk hB hB'
    ⟨conjSub g (tightCore R), ⟨g, rfl⟩, hL.datum.isUniqueInvolution_core.conj g⟩
    ⟨g, J, u, w, hF, hBx, Or.inl rfl⟩
    ⟨conjSub g' (tightCore R), ⟨g', rfl⟩, hL.datum.isUniqueInvolution_core.conj g'⟩
    ⟨g', J', u', w', hF', hBx', Or.inl rfl⟩

theorem alphaOf_eq_bot_of_framesP (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hP : ∀ J u w, P J u w →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧ IsUniqueInvolution J u)
    (hH : ∀ (J : Subgroup Y) (u w : Y), P J u w → Hyp51 (Subgroup.closure ({t, u, w} : Set Y)))
    (hex : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → ∃ w : Y, P J u w)
    (hgen : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (FrameLinkStepP P t) J J') :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
  obtain ⟨ha, hb, hcon⟩ := framesP_of hL hc hP hH hex hgen
  exact alphaOf_eq_bot_of_frames hL ha hb hcon

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
