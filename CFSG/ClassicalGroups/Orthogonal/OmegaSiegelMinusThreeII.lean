module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeCase
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelGen
public import CFSG.ClassicalGroups.Orthogonal.SiegelOverlap

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

noncomputable abbrev rootAxis (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) (a w : N) :
    Submodule K V :=
  ⨆ μ : K', movedSpace (rhoE ρ a (μ • w))

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
theorem MinusThreeFrame.swap {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v) :
    MinusThreeFrame QN f e p p' u v := by
  obtain ⟨he, hf, hp, hp', hef, hpp', hep, hep', hfp, hfp', hu, hv, hQu, han, hspan⟩ := hF
  refine ⟨hf, he, hp, hp', ?_, hpp', hfp, hfp', hep, hep', ⟨hu.2.1, hu.1, hu.2.2⟩,
    ⟨hv.2.1, hv.1, hv.2.2⟩, hQu, han, fun x => ?_⟩
  · rw [polar_comm]
    exact hef
  · rw [show ({f, e, p, p', u, v} : Set N) = {e, f, p, p', u, v} from Set.insert_comm _ _ _]
    exact hspan x

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private def perpEF (QN : QuadraticForm K' N) (e f : N) : Submodule K' N where
  carrier := {y | polar QN y e = 0 ∧ polar QN y f = 0}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by rw [polar_add_left, h1, h1', add_zero], by rw [polar_add_left, h2, h2', add_zero]⟩
  zero_mem' := ⟨polar_zero_left QN e, polar_zero_left QN f⟩
  smul_mem' := by
    rintro c a ⟨h1, h2⟩
    exact ⟨by rw [polar_smul_left_eq, h1, mul_zero], by rw [polar_smul_left_eq, h2, mul_zero]⟩

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private def fixSub (A : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ z ∈ A, g z = z}
  one_mem' := fun z _ => rfl
  mul_mem' := fun {a b} ha hb z hz => by rw [LinearEquiv.mul_apply, hb z hz, ha z hz]
  inv_mem' := fun {g} hg z hz => by
    calc g⁻¹ z = g⁻¹ (g z) := by rw [hg z hz]
      _ = z := by simp

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private def movesInto (U : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ v, g v - v ∈ U}
  one_mem' := fun v => by simp
  mul_mem' := fun {g h} hg hh v => by
    have e : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [e]
    exact U.add_mem (hg _) (hh v)
  inv_mem' := fun {g} hg v => by
    have e : g⁻¹ v - v = -(g (g⁻¹ v) - g⁻¹ v) := by
      rw [show g (g⁻¹ v) = v by simp]
      abel
    rw [e]
    exact U.neg_mem (hg _)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem movedSpace_rhoE_zero (u : N) : movedSpace (rhoE ρ u 0) = ⊥ := by
  rw [rhoE_zero_right]
  unfold movedSpace
  rw [LinearMap.range_eq_bot]
  ext v
  simp

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem apply_eq_of_mem_orthogonal_movedSpace
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {g : V ≃ₗ[K] V}
    (hg : ∀ v, Qf (g v) = Qf v) {z : V}
    (hz : z ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace g)) : g z = z := by
  rw [← ker_sub_one_eq_orthogonal_movedSpace hnd hg, LinearMap.mem_ker] at hz
  simpa [sub_eq_zero] using hz

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem OmegaSetting.rhoE_isometry (hs : OmegaSetting QN Qf ρ) (u w : N) (v : V) :
    Qf (rhoE ρ u w v) = Qf v :=
  hs.iso _ v

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem OmegaSetting.nd_N (hs : OmegaSetting QN Qf ρ) :
    ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 :=
  fun x hx => hs.ndN.1 x fun y => hx y

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem linearIndependent_pair_of_perp
    (hnd : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0) {e f s : N} (hef : polar QN e f = 1)
    (hsf : polar QN s f = 0) (hs0 : s ≠ 0) : LinearIndependent K' ![e, s] := by
  obtain ⟨z, hz⟩ : ∃ z, polar QN s z ≠ 0 := by
    by_contra! h
    exact hs0 (hnd s h)
  exact linearIndependent_pair_of_polar (by rw [hef]; exact one_ne_zero) hsf hz

omit [Finite K'] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.isLongRootElement_rhoE_perp (hs : OmegaSetting QN Qf ρ) {e f s : N}
    (he : QN e = 0) (hef : polar QN e f = 1) (hsQ : QN s = 0) (hs0 : s ≠ 0)
    (hse : polar QN s e = 0) (hsf : polar QN s f = 0) : IsLongRootElement Qf (rhoE ρ e s) :=
  hs.isLongRootElement_rhoE he hsQ (by rw [polar_comm]; exact hse)
    (linearIndependent_pair_of_perp hs.nd_N hef hsf hs0)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem rhoE_mul_comm {e x y : N} (hx : polar QN e x = 0) (hy : polar QN e y = 0) :
    rhoE ρ e x * rhoE ρ e y = rhoE ρ e y * rhoE ρ e x := by
  rw [rhoE_mul hx hy, rhoE_mul hy hx, add_comm]

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem movedSpace_rhoE_smul_le_orthogonal (hs : OmegaSetting QN Qf ρ) {e f w : N}
    (he : QN e = 0) (hef : polar QN e f = 1) (hw : QN w = 0) (hw0 : w ≠ 0)
    (hwe : polar QN w e = 0) (hwf : polar QN w f = 0) {μ c : K'} (hμ : μ ≠ 0) (hc : c ≠ 0) :
    movedSpace (rhoE ρ e (μ • w)) ≤
      LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace (rhoE ρ e (c • w))) := by
  have hQ : ∀ t : K', QN (t • w) = 0 := fun t => by rw [map_smul_eq_sq, hw, mul_zero]
  have hE : ∀ t : K', polar QN (t • w) e = 0 := fun t => by
    rw [polar_smul_left_eq, hwe, mul_zero]
  have hF : ∀ t : K', polar QN (t • w) f = 0 := fun t => by
    rw [polar_smul_left_eq, hwf, mul_zero]
  have hE' : ∀ t : K', polar QN e (t • w) = 0 := fun t => by rw [polar_comm]; exact hE t
  have h1 : IsLongRootElement Qf (rhoE ρ e (μ • w)) :=
    hs.isLongRootElement_rhoE_perp he hef (hQ μ) (smul_ne_zero hμ hw0) (hE μ) (hF μ)
  have h2 : IsLongRootElement Qf (rhoE ρ e (c • w)) :=
    hs.isLongRootElement_rhoE_perp he hef (hQ c) (smul_ne_zero hc hw0) (hE c) (hF c)
  by_cases hμc : μ = c
  · subst hμc
    exact le_orthogonal_of_totallySingular fun x hx => h1.qf_eq_zero_of_mem_movedSpace hx
  · have hmul : rhoE ρ e (μ • w) * rhoE ρ e (c • w) = rhoE ρ e ((μ + c) • w) := by
      rw [rhoE_mul (hE' μ) (hE' c), add_smul]
    refine movedSpace_le_orthogonal_of_commute_of_isLongRootElement_mul hs.nd h1 h2
      (rhoE_mul_comm (hE' μ) (hE' c)) ?_
    rw [hmul]
    exact hs.isLongRootElement_rhoE_perp he hef (hQ _)
      (smul_ne_zero (fun h => hμc (CharTwo.add_eq_zero.mp h)) hw0) (hE _) (hF _)

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem rhoE_mem_of_forall_singular (Y : Subgroup (V ≃ₗ[K] V)) {u e₂ f₂ : N}
    {H : Submodule K' N} (he₂ : e₂ ∈ H) (hf₂ : f₂ ∈ H) (hQe₂ : QN e₂ = 0) (hQf₂ : QN f₂ = 0)
    (hef₂ : polar QN e₂ f₂ = 1) (hHu : ∀ w ∈ H, polar QN u w = 0)
    (hY : ∀ w ∈ H, QN w = 0 → rhoE ρ u w ∈ Y) {x : N} (hx : x ∈ H) : rhoE ρ u x ∈ Y := by
  obtain ⟨g, hg, hgx⟩ := eichler_mem_of_forall_singular (Q := QN)
    (Y := (Y.comap ρ).map (elementaryGroup QN).subtype) he₂ hf₂ hQe₂ hQf₂ hef₂ hHu
    (fun w hw hQw => ⟨⟨eichler QN u w, eichler_mem_elementaryGroup QN u w⟩, hY w hw hQw, rfl⟩) hx
  have : g = ⟨eichler QN u x, eichler_mem_elementaryGroup QN u x⟩ := Subtype.ext hgx
  rw [this] at hg
  exact hg

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem rootAxis_le_orthogonal (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {w s : N} (hw : QN w = 0) (hw0 : w ≠ 0) (hwe : polar QN w e = 0) (hwf : polar QN w f = 0)
    (hsQ : QN s = 0) (hse : polar QN s e = 0) (hsf : polar QN s f = 0) :
    rootAxis ρ e w ≤
      LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace (rhoE ρ e s)) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    have h := hF.ef
    rw [polar_zero_left] at h
    exact zero_ne_one h
  refine iSup_le fun μ => ?_
  by_cases hμ : μ = 0
  · subst hμ
    rw [zero_smul, movedSpace_rhoE_zero]
    exact bot_le
  by_cases hs0 : s = 0
  · subst hs0
    rw [movedSpace_rhoE_zero, LinearMap.BilinForm.orthogonal_bot]
    exact le_top
  by_cases hws : polar QN w s = 0
  · obtain ⟨c, rfl⟩ := hF.eq_smul_of_polar_eq_zero hwe hwf hse hsf hw hsQ hw0 hws
    have hc : c ≠ 0 := fun h => hs0 (by rw [h, zero_smul])
    exact movedSpace_rhoE_smul_le_orthogonal hs hF.e_sing hF.ef hw hw0 hwe hwf hμ hc
  · have hμQ : QN (μ • w) = 0 := by rw [map_smul_eq_sq, hw, mul_zero]
    have hμe : polar QN (μ • w) e = 0 := by rw [polar_smul_left_eq, hwe, mul_zero]
    have hμf : polar QN (μ • w) f = 0 := by rw [polar_smul_left_eq, hwf, mul_zero]
    have hse' : polar QN e s = 0 := by rw [polar_comm]; exact hse
    have hμe' : polar QN e (μ • w) = 0 := by rw [polar_comm]; exact hμe
    have hflag : IsFlag QN e s (μ • w) := by
      refine ⟨hF.e_sing, he0, hsQ, hμQ, hse', hμe', ?_⟩
      rw [polar_smul_right_eq, polar_comm QN s w]
      exact mul_ne_zero hμ hws
    have hs' := hs.isLongRootElement_rhoE_perp hF.e_sing hF.ef hsQ hs0 hse hsf
    have hμw := hs.isLongRootElement_rhoE_perp hF.e_sing hF.ef hμQ
      (smul_ne_zero hμ hw0) hμe hμf
    exact movedSpace_le_orthogonal_of_commute hs' hμw (rhoE_mul_comm hse' hμe')
      (disjoint_iff.mpr (hII e s (μ • w) hflag))

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
theorem OmegaSetting.caseII_fix (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {w x : N} (hw : QN w = 0) (hw0 : w ≠ 0) (hwe : polar QN w e = 0) (hwf : polar QN w f = 0)
    (hxe : polar QN x e = 0) (hxf : polar QN x f = 0) {z : V} (hz : z ∈ rootAxis ρ e w) :
    rhoE ρ e x z = z := by
  have hA : ∀ s ∈ perpEF QN e f, QN s = 0 → rhoE ρ e s ∈ fixSub (rootAxis ρ e w) := by
    intro s hsH hsQ z' hz'
    exact apply_eq_of_mem_orthogonal_movedSpace hs.nd (hs.rhoE_isometry e s)
      (rootAxis_le_orthogonal hs hF hII hw hw0 hwe hwf hsQ hsH.1 hsH.2 hz')
  have key := rhoE_mem_of_forall_singular (ρ := ρ) (fixSub (rootAxis ρ e w)) (u := e) (e₂ := p)
    (f₂ := p') (H := perpEF QN e f)
    ⟨by rw [polar_comm]; exact hF.ep, by rw [polar_comm]; exact hF.fp⟩
    ⟨by rw [polar_comm]; exact hF.ep', by rw [polar_comm]; exact hF.fp'⟩ hF.p_sing hF.p'_sing
    hF.pp' (fun y hy => by rw [polar_comm]; exact hy.1) hA ⟨hxe, hxf⟩
  exact key z hz

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem rhoE_sub_smul_self {e : N} (he : QN e = 0) (x : N) (c : K') :
    rhoE ρ e (x - c • e) = rhoE ρ e x := by
  have h := eichler_add_smul_self he (x - c • e) c
  rw [sub_add_cancel] at h
  unfold rhoE
  exact congrArg ρ (Subtype.ext h.symm)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem rhoE_mem_of_perp (Y : Subgroup (V ≃ₗ[K] V)) {e f : N} (he : QN e = 0)
    (hef : polar QN e f = 1)
    (h : ∀ x, polar QN x e = 0 → polar QN x f = 0 → rhoE ρ e x ∈ Y) {x : N}
    (hx : polar QN e x = 0) : rhoE ρ e x ∈ Y := by
  have hx' : polar QN x e = 0 := by rw [polar_comm]; exact hx
  rw [← rhoE_sub_smul_self (ρ := ρ) he x (polar QN x f)]
  refine h _ ?_ ?_
  · rw [polar_sub_left, polar_smul_left_eq, hx', polar_self_eq_zero he]
    ring
  · rw [polar_sub_left, polar_smul_left_eq, hef]
    ring

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
theorem OmegaSetting.caseII_inf_eq_bot (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {w w' : N} (hw : QN w = 0) (hw' : QN w' = 0) (hwe : polar QN w e = 0)
    (hwf : polar QN w f = 0) (hw'e : polar QN w' e = 0) (hw'f : polar QN w' f = 0)
    (hww' : polar QN w w' = 1) : rootAxis ρ e w ⊓ rootAxis ρ f w' = ⊥ := by
  rw [eq_bot_iff]
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at hww'
    exact zero_ne_one hww'
  have hw'0 : w' ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hww'
    exact zero_ne_one hww'
  set A := rootAxis ρ e w ⊓ rootAxis ρ f w' with hA
  have hFe : ∀ x, polar QN x e = 0 → polar QN x f = 0 → rhoE ρ e x ∈ fixSub A :=
    fun x hxe hxf z hz => hs.caseII_fix hF hII hw hw0 hwe hwf hxe hxf hz.1
  have hFf : ∀ x, polar QN x f = 0 → polar QN x e = 0 → rhoE ρ f x ∈ fixSub A :=
    fun x hxf hxe z hz => hs.caseII_fix hF.swap hII hw' hw'0 hw'f hw'e hxf hxe hz.2
  have hef := hF.ef
  have hfe : polar QN f e = 1 := by rw [polar_comm]; exact hef
  have hRe : rootGroup QN e ≤ ((fixSub A).comap ρ).map (elementaryGroup QN).subtype := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := mem_rootGroup.mp hg
    exact ⟨⟨eichler QN e x, eichler_mem_elementaryGroup QN e x⟩,
      rhoE_mem_of_perp (fixSub A) hF.e_sing hef hFe hx, rfl⟩
  have hRf : rootGroup QN f ≤ ((fixSub A).comap ρ).map (elementaryGroup QN).subtype := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := mem_rootGroup.mp hg
    exact ⟨⟨eichler QN f x, eichler_mem_elementaryGroup QN f x⟩,
      rhoE_mem_of_perp (fixSub A) hF.f_sing hfe hFf hx, rfl⟩
  have hle : elementaryGroup QN ≤ ((fixSub A).comap ρ).map (elementaryGroup QN).subtype :=
    (elementaryGroup_le_rootGroup_sup hs.nd_N hF.e_sing hF.f_sing hef
      (by rw [polar_comm]; exact hF.u_perp.1) (by rw [polar_comm]; exact hF.u_perp.2.1)
      hF.Qu).trans (sup_le hRe hRf)
  have hall : ∀ g : ↥(elementaryGroup QN), ρ g ∈ fixSub A := fun g => by
    obtain ⟨g', hg', hgg'⟩ := hle g.2
    have : g' = g := Subtype.ext hgg'
    rw [this] at hg'
    exact hg'
  intro z hz
  exact (Submodule.mem_bot K).mpr (hfix z fun g => hall g z hz)

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem exists_dual_singular (hnd : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0) {e f w : N}
    (he : QN e = 0) (hf : QN f = 0) (hef : polar QN e f = 1) (hw : QN w = 0) (hw0 : w ≠ 0)
    (hwe : polar QN w e = 0) (hwf : polar QN w f = 0) :
    ∃ w' : N, QN w' = 0 ∧ polar QN w w' = 1 ∧ polar QN w' e = 0 ∧ polar QN w' f = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, polar QN w y ≠ 0 := by
    by_contra! h
    exact hw0 (hnd w h)
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have hfe : polar QN f e = 1 := by rw [polar_comm]; exact hef
  have hee := polar_self_eq_zero he
  have hff := polar_self_eq_zero hf
  have hww := polar_self_eq_zero hw
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = y + polar QN y f • e + polar QN y e • f := ⟨_, rfl⟩
  have hy₀e : polar QN y₀ e = 0 := by
    rw [hy₀]
    simp only [polar_add_left, polar_smul_left_eq, hee, hfe]
    linear_combination (polar QN y e) * h2
  have hy₀f : polar QN y₀ f = 0 := by
    rw [hy₀]
    simp only [polar_add_left, polar_smul_left_eq, hff, hef]
    linear_combination (polar QN y f) * h2
  have hwy₀ : polar QN w y₀ = polar QN w y := by
    rw [hy₀]
    simp only [polar_add_right, polar_smul_right_eq, hwe, hwf, mul_zero, add_zero]
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = (polar QN w y)⁻¹ • y₀ := ⟨_, rfl⟩
  have hy₁e : polar QN y₁ e = 0 := by rw [hy₁, polar_smul_left_eq, hy₀e, mul_zero]
  have hy₁f : polar QN y₁ f = 0 := by rw [hy₁, polar_smul_left_eq, hy₀f, mul_zero]
  have hwy₁ : polar QN w y₁ = 1 := by
    rw [hy₁, polar_smul_right_eq, hwy₀, inv_mul_cancel₀ hy]
  have hy₁w : polar QN y₁ w = 1 := by rw [polar_comm]; exact hwy₁
  refine ⟨y₁ + QN y₁ • w, ?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add QN, map_smul_eq_sq, hw, polar_smul_right_eq, hy₁w]
    linear_combination (QN y₁) * h2
  · rw [polar_add_right, polar_smul_right_eq, hwy₁, hww]
    ring
  · rw [polar_add_left, polar_smul_left_eq, hy₁e, hwe]
    ring
  · rw [polar_add_left, polar_smul_left_eq, hy₁f, hwf]
    ring

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem conj_apply_e {e f w w' : N} {α : K'} (hα : α ≠ 0) (he : QN e = 0) (hf : QN f = 0)
    (hw : QN w = 0) (hw' : QN w' = 0) (hef : polar QN e f = 1) (hww' : polar QN w w' = 1)
    (hwe : polar QN w e = 0) (hw'e : polar QN w' e = 0) (hw'f : polar QN w' f = 0) :
    (eichler QN e (α • w) * eichler QN f (α⁻¹ • w') * eichler QN e (α • w)) e =
      α⁻¹ • w' := by
  have h2e : (2 : K') • e = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have hQαw : QN (α • w) = 0 := by rw [map_smul_eq_sq, hw, mul_zero]
  have hQw' : QN (α⁻¹ • w') = 0 := by rw [map_smul_eq_sq, hw', mul_zero]
  have hee : polar QN e e = 0 := polar_self_eq_zero he
  have hew : polar QN e w = 0 := by rw [polar_comm]; exact hwe
  have hew' : polar QN e w' = 0 := by rw [polar_comm]; exact hw'e
  have hwp : polar QN w' w = 1 := by rw [polar_comm]; exact hww'
  have hfw' : polar QN f w' = 0 := by rw [polar_comm]; exact hw'f
  have hpe1 : polar QN e (α • w) = 0 := by rw [polar_smul_right_eq, hew, mul_zero]
  have hpf2 : polar QN f (α⁻¹ • w') = 0 := by rw [polar_smul_right_eq, hfw', mul_zero]
  have h1 : eichler QN e (α • w) e = e := eichler_apply_of_polar_eq_zero hee hpe1
  have h2 : eichler QN f (α⁻¹ • w') e = e + α⁻¹ • w' := by
    rw [eichler_apply_of_singular hf hQw' hpf2, hef, one_smul, polar_smul_right_eq, hew',
      mul_zero, zero_smul, add_zero]
  have h3 : eichler QN e (α • w) w' = w' + α • e := by
    rw [eichler_apply_of_singular he hQαw hpe1, hw'e, zero_smul, add_zero, polar_smul_right_eq,
      hwp, mul_one]
  simp only [LinearEquiv.mul_apply, h1, h2, map_add, map_smul, h3]
  rw [smul_add, smul_smul, inv_mul_cancel₀ hα, one_smul]
  linear_combination (norm := module) h2e

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem conj_apply_w {e f w w' : N} {α : K'} (hα : α ≠ 0) (he : QN e = 0) (hf : QN f = 0)
    (hw : QN w = 0) (hw' : QN w' = 0) (hef : polar QN e f = 1) (hww' : polar QN w w' = 1)
    (hwe : polar QN w e = 0) (hwf : polar QN w f = 0) (hw'f : polar QN w' f = 0) :
    (eichler QN e (α • w) * eichler QN f (α⁻¹ • w') * eichler QN e (α • w)) w =
      α⁻¹ • f := by
  have h2w : (2 : K') • w = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have hQαw : QN (α • w) = 0 := by rw [map_smul_eq_sq, hw, mul_zero]
  have hQw' : QN (α⁻¹ • w') = 0 := by rw [map_smul_eq_sq, hw', mul_zero]
  have hww : polar QN w w = 0 := polar_self_eq_zero hw
  have hew : polar QN e w = 0 := by rw [polar_comm]; exact hwe
  have hfe : polar QN f e = 1 := by rw [polar_comm]; exact hef
  have hfw : polar QN f w = 0 := by rw [polar_comm]; exact hwf
  have hfw' : polar QN f w' = 0 := by rw [polar_comm]; exact hw'f
  have hpe1 : polar QN e (α • w) = 0 := by rw [polar_smul_right_eq, hew, mul_zero]
  have hpf2 : polar QN f (α⁻¹ • w') = 0 := by rw [polar_smul_right_eq, hfw', mul_zero]
  have hpww : polar QN w (α • w) = 0 := by rw [polar_smul_right_eq, hww, mul_zero]
  have h1 : eichler QN e (α • w) w = w := eichler_apply_of_polar_eq_zero hwe hpww
  have h2 : eichler QN f (α⁻¹ • w') w = w + α⁻¹ • f := by
    rw [eichler_apply_of_singular hf hQw' hpf2, hwf, zero_smul, add_zero, polar_smul_right_eq,
      hww', mul_one]
  have h3 : eichler QN e (α • w) f = f + α • w := by
    rw [eichler_apply_of_singular he hQαw hpe1, hfe, one_smul, polar_smul_right_eq, hfw, mul_zero,
      zero_smul, add_zero]
  simp only [LinearEquiv.mul_apply, h1, h2, map_add, map_smul, h3]
  rw [smul_add, smul_smul, inv_mul_cancel₀ hα, one_smul]
  linear_combination (norm := module) h2w

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem mem_movedSpace_of_inf_eq_bot {A B : Submodule K V} {U Vv : V ≃ₗ[K] V}
    (hU : movedSpace U ≤ A) (hV : movedSpace Vv ≤ B) (hAB : A ⊓ B = ⊥)
    (hmap : ∀ z ∈ A, (U * Vv * U) z ∈ B) {z : V} (hz : z ∈ A) (hUz : U z = z) :
    z ∈ movedSpace U := by
  have h1 : U (Vv z) = U (Vv z - z) + z := by
    rw [map_sub, hUz]
    abel
  have hWz : (U * Vv * U) z = U (Vv z - z) + z := by
    simp only [LinearEquiv.mul_apply]
    rw [hUz, h1]
  have ht : Vv z - z ∈ B := hV (sub_mem_movedSpace Vv z)
  have hd : U (Vv z - z) - (Vv z - z) ∈ A := hU (sub_mem_movedSpace U _)
  have hy1 : z + (U (Vv z - z) - (Vv z - z)) ∈ A := A.add_mem hz hd
  have hy2 : z + (U (Vv z - z) - (Vv z - z)) ∈ B := by
    have : z + (U (Vv z - z) - (Vv z - z)) = (U * Vv * U) z - (Vv z - z) := by
      rw [hWz]
      abel
    rw [this]
    exact B.sub_mem (hmap z hz) ht
  have hy0 : z + (U (Vv z - z) - (Vv z - z)) = 0 := by
    have hmem : z + (U (Vv z - z) - (Vv z - z)) ∈ A ⊓ B := ⟨hy1, hy2⟩
    rw [hAB] at hmem
    exact (Submodule.mem_bot K).mp hmem
  have hz' := eq_neg_of_add_eq_zero_left hy0
  rw [hz']
  exact (movedSpace U).neg_mem (sub_mem_movedSpace _ _)

omit [Finite K'] [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
private theorem rootAxis_map_le {e f w w' : N} {α : K'} (hα : α ≠ 0) (he : QN e = 0)
    (hf : QN f = 0) (hw : QN w = 0) (hw' : QN w' = 0) (hef : polar QN e f = 1)
    (hww' : polar QN w w' = 1) (hwe : polar QN w e = 0) (hwf : polar QN w f = 0)
    (hw'e : polar QN w' e = 0) (hw'f : polar QN w' f = 0) {z : V} (hz : z ∈ rootAxis ρ e w) :
    (rhoE ρ e (α • w) * rhoE ρ f (α⁻¹ • w') * rhoE ρ e (α • w)) z ∈ rootAxis ρ f w' := by
  let gu : ↥(elementaryGroup QN) := ⟨eichler QN e (α • w), eichler_mem_elementaryGroup QN _ _⟩
  let gv : ↥(elementaryGroup QN) :=
    ⟨eichler QN f (α⁻¹ • w'), eichler_mem_elementaryGroup QN _ _⟩
  have hWe : ((gu * gv * gu : ↥(elementaryGroup QN)) : N ≃ₗ[K'] N) e = α⁻¹ • w' :=
    conj_apply_e hα he hf hw hw' hef hww' hwe hw'e hw'f
  have hWw : ((gu * gv * gu : ↥(elementaryGroup QN)) : N ≃ₗ[K'] N) w = α⁻¹ • f :=
    conj_apply_w hα he hf hw hw' hef hww' hwe hwf hw'f
  have hrho : ∀ μ : K', rhoE ρ (α⁻¹ • w') (μ • α⁻¹ • f) =
      rhoE ρ f ((α⁻¹ * μ * α⁻¹) • w') := by
    intro μ
    have hQc : QN ((α⁻¹ * μ * α⁻¹) • f) = 0 := by rw [map_smul_eq_sq, hf, mul_zero]
    have hpc : polar QN w' ((α⁻¹ * μ * α⁻¹) • f) = 0 := by
      rw [polar_smul_right_eq, hw'f, mul_zero]
    rw [rhoE_smul_left, smul_smul, smul_smul, rhoE_comm hw' hQc hpc, rhoE_smul_left]
  have hle : (rootAxis ρ e w).map (ρ (gu * gv * gu) : V →ₗ[K] V) ≤ rootAxis ρ f w' := by
    unfold rootAxis
    rw [Submodule.map_iSup]
    refine iSup_le fun μ => ?_
    rw [← movedSpace_rhoE_apply (ρ := ρ) (gu * gv * gu) e (μ • w), hWe, map_smul, hWw, hrho μ]
    exact le_iSup (fun μ : K' => movedSpace (rhoE ρ f (μ • w'))) _
  have hρW : ρ (gu * gv * gu) =
      rhoE ρ e (α • w) * rhoE ρ f (α⁻¹ • w') * rhoE ρ e (α • w) := by
    rw [map_mul, map_mul]
    rfl
  rw [← hρW]
  exact hle ⟨z, hz, rfl⟩

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
theorem OmegaSetting.caseII_single_axis (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {w : N} (hw : QN w = 0) (hw0 : w ≠ 0) (hwe : polar QN w e = 0) (hwf : polar QN w f = 0)
    {α : K'} (hα : α ≠ 0) : movedSpace (rhoE ρ e (α • w)) = rootAxis ρ e w := by
  refine le_antisymm (le_iSup (fun μ : K' => movedSpace (rhoE ρ e (μ • w))) α) fun z hz => ?_
  obtain ⟨w', hw'Q, hww', hw'e, hw'f⟩ :=
    exists_dual_singular hs.nd_N hF.e_sing hF.f_sing hF.ef hw hw0 hwe hwf
  exact mem_movedSpace_of_inf_eq_bot (le_iSup (fun μ : K' => movedSpace (rhoE ρ e (μ • w))) α)
    (le_iSup (fun μ : K' => movedSpace (rhoE ρ f (μ • w'))) α⁻¹)
    (hs.caseII_inf_eq_bot hfix hF hII hw hw'Q hwe hwf hw'e hw'f hww')
    (fun z hz => rootAxis_map_le hα hF.e_sing hF.f_sing hw hw'Q hF.ef hww' hwe hwf hw'e hw'f hz)
    hz (hs.caseII_fix hF hII hw hw0 hwe hwf (by rw [polar_smul_left_eq, hwe, mul_zero])
      (by rw [polar_smul_left_eq, hwf, mul_zero]) hz)

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem ne_zero_of_polar_eq_one {a b : N} (h : polar QN a b = 1) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · rintro rfl
    rw [polar_zero_left] at h
    exact zero_ne_one h
  · rintro rfl
    rw [polar_zero_right] at h
    exact zero_ne_one h

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.movedSpace_rhoE_smul_eq (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {q : N} (hq : QN q = 0) (hq0 : q ≠ 0) (hqe : polar QN q e = 0) (hqf : polar QN q f = 0)
    {c : K'} (hc : c ≠ 0) : movedSpace (rhoE ρ e (c • q)) = movedSpace (rhoE ρ e q) := by
  have h1 := hs.caseII_single_axis hfix hF hII hq hq0 hqe hqf hc
  have h2 := hs.caseII_single_axis hfix hF hII hq hq0 hqe hqf (one_ne_zero : (1 : K') ≠ 0)
  rw [one_smul] at h2
  rw [h1, h2]

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem fourth_vector_facts {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    {w : N} (hw : QN w = 0) (hw0 : w ≠ 0) (hwe : polar QN w e = 0) (hwf : polar QN w f = 0)
    {α β γ : K'} (hα : α ≠ 0) (hβ : β ≠ 0) {w₃ : N} (hw₃ : w₃ = α • p + β • p' + γ • w)
    (hQ3 : QN w₃ = 0) :
    polar QN w₃ e = 0 ∧ polar QN w₃ f = 0 ∧ w₃ + γ • w = α • p + β • p' ∧ w₃ ≠ 0 ∧
      polar QN w w₃ ≠ 0 := by
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have hp := hF.p_sing
  have hp' := hF.p'_sing
  have hpp' := hF.pp'
  have hpe : polar QN p e = 0 := by rw [polar_comm]; exact hF.ep
  have hpf : polar QN p f = 0 := by rw [polar_comm]; exact hF.fp
  have hp'e : polar QN p' e = 0 := by rw [polar_comm]; exact hF.ep'
  have hp'f : polar QN p' f = 0 := by rw [polar_comm]; exact hF.fp'
  have hw₃e : polar QN w₃ e = 0 := by
    rw [hw₃]
    simp [polar_add_left, hpe, hp'e, hwe]
  have hw₃f : polar QN w₃ f = 0 := by
    rw [hw₃]
    simp [polar_add_left, hpf, hp'f, hwf]
  have hsum : w₃ + γ • w = α • p + β • p' := by
    have h2' : (2 : K') • (γ • w) = 0 := by rw [h2, zero_smul]
    rw [hw₃]
    linear_combination (norm := module) h2'
  have hnot : ∀ c : K', α • p + β • p' ≠ c • w := by
    intro c h
    have hQ := congrArg (fun x => QN x) h
    simp only [QuadraticMap.map_add QN, map_smul_eq_sq, polar_smul_left_eq, polar_smul_right_eq,
      hp, hp', hw, hpp'] at hQ
    exact mul_ne_zero hα hβ (by linear_combination hQ)
  refine ⟨hw₃e, hw₃f, hsum, fun h => ?_, fun h => ?_⟩
  · rw [h, zero_add] at hsum
    exact hnot γ hsum.symm
  · obtain ⟨c, hc⟩ := hF.eq_smul_of_polar_eq_zero hwe hwf hw₃e hw₃f hw hQ3 hw0 h
    rw [hc, ← add_smul] at hsum
    exact hnot (c + γ) hsum.symm

omit [Finite K'] [Finite K] in
private theorem OmegaSetting.movedSpace_le_sup_of_fourth (hs : OmegaSetting QN Qf ρ)
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {w : N} (hw : QN w = 0) (hw0 : w ≠ 0) (hwe : polar QN w e = 0) (hwf : polar QN w f = 0)
    {α β γ : K'} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hQ3 : QN (α • p + β • p' + γ • w) = 0) :
    movedSpace (rhoE ρ e (γ • w)) ≤
      movedSpace (rhoE ρ e (α • p)) ⊔ movedSpace (rhoE ρ e (β • p')) := by
  have he := hF.e_sing
  have hef := hF.ef
  have hp := hF.p_sing
  have hp' := hF.p'_sing
  have hpp' := hF.pp'
  have hpe : polar QN p e = 0 := by rw [polar_comm]; exact hF.ep
  have hpf : polar QN p f = 0 := by rw [polar_comm]; exact hF.fp
  have hp'e : polar QN p' e = 0 := by rw [polar_comm]; exact hF.ep'
  have hp'f : polar QN p' f = 0 := by rw [polar_comm]; exact hF.fp'
  have he0 := (ne_zero_of_polar_eq_one hef).1
  have hp0 := (ne_zero_of_polar_eq_one hpp').1
  have hp'0 := (ne_zero_of_polar_eq_one hpp').2
  obtain ⟨w₃, hw₃⟩ : ∃ w₃, w₃ = α • p + β • p' + γ • w := ⟨_, rfl⟩
  rw [← hw₃] at hQ3
  obtain ⟨hw₃e, hw₃f, hsum, hw₃0, hww₃⟩ := fourth_vector_facts hF hw hw0 hwe hwf hα hβ hw₃ hQ3
  have hw₃e' : polar QN e w₃ = 0 := by rw [polar_comm]; exact hw₃e
  have hQs : ∀ (q : N) (c : K'), QN q = 0 → QN (c • q) = 0 := fun q c hq => by
    rw [map_smul_eq_sq, hq, mul_zero]
  have hEs : ∀ (q : N) (c : K'), polar QN q e = 0 → polar QN e (c • q) = 0 := fun q c h => by
    rw [polar_smul_right_eq, polar_comm, h, mul_zero]
  have hSs : ∀ (q : N) (c : K'), QN q = 0 → q ≠ 0 → polar QN q e = 0 → polar QN q f = 0 →
      c ≠ 0 → IsLongRootElement Qf (rhoE ρ e (c • q)) := fun q c hq hq0 hqe hqf hc =>
    hs.isLongRootElement_rhoE_perp he hef (hQs q c hq) (smul_ne_zero hc hq0)
      (by rw [polar_smul_left_eq, hqe, mul_zero]) (by rw [polar_smul_left_eq, hqf, mul_zero])
  have hid : rhoE ρ e (α • p) * rhoE ρ e (β • p') = rhoE ρ e w₃ * rhoE ρ e (γ • w) := by
    rw [rhoE_mul (hEs p α hpe) (hEs p' β hp'e), rhoE_mul hw₃e' (hEs w γ hwe), hsum]
  have hfl1 : IsFlag QN e (α • p) (β • p') :=
    ⟨he, he0, hQs p α hp, hQs p' β hp', hEs p α hpe, hEs p' β hp'e, by
      rw [polar_smul_left_eq, polar_smul_right_eq, hpp']
      exact mul_ne_zero hα (mul_ne_zero hβ one_ne_zero)⟩
  have hfl2 : IsFlag QN e w₃ (γ • w) :=
    ⟨he, he0, hQ3, hQs w γ hw, hw₃e', hEs w γ hwe, by
      rw [polar_smul_right_eq, polar_comm QN w₃ w]
      exact mul_ne_zero hγ hww₃⟩
  have hS1 := movedSpace_mul_eq_sup_of_commute hs.nd (hSs p α hp hp0 hpe hpf hα)
    (hSs p' β hp' hp'0 hp'e hp'f hβ) (rhoE_mul_comm (hEs p α hpe) (hEs p' β hp'e))
    (disjoint_iff.mpr (hII e _ _ hfl1))
  have hS2 := movedSpace_mul_eq_sup_of_commute hs.nd
    (hs.isLongRootElement_rhoE_perp he hef hQ3 hw₃0 hw₃e hw₃f) (hSs w γ hw hw0 hwe hwf hγ)
    (rhoE_mul_comm hw₃e' (hEs w γ hwe)) (disjoint_iff.mpr (hII e _ _ hfl2))
  rw [hid, hS2] at hS1
  rw [← hS1]
  exact le_sup_right

omit [Finite K] in
theorem OmegaSetting.caseII_le_sup (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    (hK : 2 < Nat.card K') {w : N} (hw : QN w = 0) (hwe : polar QN w e = 0)
    (hwf : polar QN w f = 0) :
    movedSpace (rhoE ρ e w) ≤ movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p') := by
  have hp := hF.p_sing
  have hp' := hF.p'_sing
  have hpp' := hF.pp'
  have hpe : polar QN p e = 0 := by rw [polar_comm]; exact hF.ep
  have hpf : polar QN p f = 0 := by rw [polar_comm]; exact hF.fp
  have hp'e : polar QN p' e = 0 := by rw [polar_comm]; exact hF.ep'
  have hp'f : polar QN p' f = 0 := by rw [polar_comm]; exact hF.fp'
  have hp0 := (ne_zero_of_polar_eq_one hpp').1
  have hp'0 := (ne_zero_of_polar_eq_one hpp').2
  by_cases hw0 : w = 0
  · subst hw0
    rw [movedSpace_rhoE_zero]
    exact bot_le
  by_cases hpw : polar QN p w = 0
  · obtain ⟨c, rfl⟩ := hF.eq_smul_of_polar_eq_zero hpe hpf hwe hwf hp hw hp0 hpw
    have hc : c ≠ 0 := fun h => hw0 (by rw [h, zero_smul])
    rw [hs.movedSpace_rhoE_smul_eq hfix hF hII hp hp0 hpe hpf hc]
    exact le_sup_left
  by_cases hp'w : polar QN p' w = 0
  · obtain ⟨c, rfl⟩ := hF.eq_smul_of_polar_eq_zero hp'e hp'f hwe hwf hp' hw hp'0 hp'w
    have hc : c ≠ 0 := fun h => hw0 (by rw [h, zero_smul])
    rw [hs.movedSpace_rhoE_smul_eq hfix hF hII hp' hp'0 hp'e hp'f hc]
    exact le_sup_right
  obtain ⟨α, β, γ, hα, hβ, hγ, hQ3⟩ := exists_fourth_point hK hp hp' hw
    (by rw [hpp']; exact one_ne_zero) hpw
  have h := hs.movedSpace_le_sup_of_fourth hF hII hw hw0 hwe hwf hα hβ hγ hQ3
  rw [← hs.movedSpace_rhoE_smul_eq hfix hF hII hw hw0 hwe hwf hγ,
    ← hs.movedSpace_rhoE_smul_eq hfix hF hII hp hp0 hpe hpf hα,
    ← hs.movedSpace_rhoE_smul_eq hfix hF hII hp' hp'0 hp'e hp'f hβ]
  exact h

omit [Finite K] in
private theorem OmegaSetting.movedSpace_rhoE_le_of_caseII (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    (x : N) : movedSpace (rhoE ρ e x) ≤ movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p') := by
  by_cases hx : polar QN e x = 0
  · have hx' : polar QN x e = 0 := by rw [polar_comm]; exact hx
    have hmem : rhoE ρ e (x - polar QN x f • e) ∈
        movesInto (movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p')) := by
      refine rhoE_mem_of_forall_singular (ρ := ρ)
        (movesInto (movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p'))) (u := e) (e₂ := p)
        (f₂ := p') (H := perpEF QN e f)
        ⟨by rw [polar_comm]; exact hF.ep, by rw [polar_comm]; exact hF.fp⟩
        ⟨by rw [polar_comm]; exact hF.ep', by rw [polar_comm]; exact hF.fp'⟩ hF.p_sing
        hF.p'_sing hF.pp' (fun y hy => by rw [polar_comm]; exact hy.1)
        (fun w hw hQw v' => ?_) ?_
      · exact hs.caseII_le_sup hfix hF hII hK hQw hw.1 hw.2 (sub_mem_movedSpace _ v')
      · refine ⟨?_, ?_⟩
        · rw [polar_sub_left, polar_smul_left_eq, hx', polar_self_eq_zero hF.e_sing]
          ring
        · rw [polar_sub_left, polar_smul_left_eq, hF.ef]
          ring
    rw [← rhoE_sub_smul_self (ρ := ρ) hF.e_sing x (polar QN x f)]
    intro y hy
    obtain ⟨v', rfl⟩ := mem_movedSpace_iff.mp hy
    exact hmem v'
  · have h0 : rhoE ρ e x = rhoE ρ e 0 := by
      have h : eichler QN e x = eichler QN e 0 := by
        rw [eichler_of_polar_ne_zero hx, eichler_zero_right]
      unfold rhoE
      exact congrArg ρ (Subtype.ext h)
    rw [h0, movedSpace_rhoE_zero]
    exact bot_le

omit [Finite K'] [Finite K] in
private theorem OmegaSetting.finrank_axes_le_four (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) :
    finrank K ↥(movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p')) ≤ 4 := by
  have hpp' := hF.pp'
  have hp0 := (ne_zero_of_polar_eq_one hpp').1
  have hp'0 := (ne_zero_of_polar_eq_one hpp').2
  have h1 := (hs.isLongRootElement_rhoE_perp hF.e_sing hF.ef hF.p_sing hp0
    (by rw [polar_comm]; exact hF.ep) (by rw [polar_comm]; exact hF.fp)).finrank_movedSpace hs.nd
  have h2 := (hs.isLongRootElement_rhoE_perp hF.e_sing hF.ef hF.p'_sing hp'0
    (by rw [polar_comm]; exact hF.ep') (by rw [polar_comm]; exact hF.fp')).finrank_movedSpace
    hs.nd
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (movedSpace (rhoE ρ e p))
    (movedSpace (rhoE ρ e p'))
  omega

omit [Finite K] in
theorem OmegaSetting.finrank_le_eight_of_caseII (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥) :
    finrank K V ≤ 8 := by
  have hef := hF.ef
  have hbe := hs.movedSpace_rhoE_le_of_caseII hfix hK hF hII
  have hbf := hs.movedSpace_rhoE_le_of_caseII hfix hK hF.swap hII
  have hgen : elementaryGroup QN ≤ Subgroup.closure {g | ∃ (i : N ⊕ N), ∃ c : K',
      g = eichler QN (Sum.elim (fun _ => e) (fun _ => f) i) (c • Sum.elim id id i)} := by
    refine (elementaryGroup_le_rootGroup_sup hs.nd_N hF.e_sing hF.f_sing hef
      (by rw [polar_comm]; exact hF.u_perp.1) (by rw [polar_comm]; exact hF.u_perp.2.1)
      hF.Qu).trans (sup_le ?_ ?_)
    · intro g hg
      obtain ⟨x, -, rfl⟩ := mem_rootGroup.mp hg
      exact Subgroup.subset_closure ⟨Sum.inl x, 1, by simp⟩
    · intro g hg
      obtain ⟨x, -, rfl⟩ := mem_rootGroup.mp hg
      exact Subgroup.subset_closure ⟨Sum.inr x, 1, by simp⟩
  have htop' := top_le_iSup_of_generate (ρ := ρ) htop (ι := N ⊕ N)
    (Sum.elim (fun _ => e) (fun _ => f)) (Sum.elim id id) hgen
    (A := Sum.elim (fun _ => movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p'))
      (fun _ => movedSpace (rhoE ρ f p) ⊔ movedSpace (rhoE ρ f p')))
    (fun i c => by
      rcases i with x | x
      · exact hbe _
      · exact hbf _)
  have hle : (⊤ : Submodule K V) ≤ (movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p')) ⊔
      (movedSpace (rhoE ρ f p) ⊔ movedSpace (rhoE ρ f p')) :=
    htop'.trans (iSup_le fun i => by
      rcases i with x | x
      · exact le_sup_left
      · exact le_sup_right)
  have h1 : finrank K V ≤ finrank K ↥((movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p')) ⊔
      (movedSpace (rhoE ρ f p) ⊔ movedSpace (rhoE ρ f p'))) := by
    rw [← finrank_top K V]
    exact Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p'))
    (movedSpace (rhoE ρ f p) ⊔ movedSpace (rhoE ρ f p'))
  have h3 := hs.finrank_axes_le_four hF
  have h4 := hs.finrank_axes_le_four hF.swap
  omega

omit [Finite K] in
theorem OmegaSetting.iSup_movedSpace_rhoE_eq_of_caseII (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥) :
    ⨆ (w : N) (_ : polar QN e w = 0), movedSpace (rhoE ρ e w) =
      movedSpace (rhoE ρ e p) ⊔ movedSpace (rhoE ρ e p') :=
  le_antisymm (iSup₂_le fun w _ => hs.movedSpace_rhoE_le_of_caseII hfix hK hF hII w)
    (sup_le (le_iSup₂_of_le p hF.ep le_rfl) (le_iSup₂_of_le p' hF.ep' le_rfl))

omit [Finite K'] [Finite K] in
private theorem OmegaSetting.axes_sup_facts (hs : OmegaSetting QN Qf ρ) {e f b c : N}
    (he : QN e = 0) (hef : polar QN e f = 1) (hb : QN b = 0) (hc : QN c = 0)
    (hbe : polar QN b e = 0) (hbf : polar QN b f = 0) (hce : polar QN c e = 0)
    (hcf : polar QN c f = 0) (hbc : polar QN b c ≠ 0)
    (hdisj : movedSpace (rhoE ρ e b) ⊓ movedSpace (rhoE ρ e c) = ⊥) :
    movedSpace (rhoE ρ e b * rhoE ρ e c) = movedSpace (rhoE ρ e b) ⊔ movedSpace (rhoE ρ e c) ∧
      finrank K ↥(movedSpace (rhoE ρ e b) ⊔ movedSpace (rhoE ρ e c)) = 4 ∧
      ∀ x ∈ movedSpace (rhoE ρ e b) ⊔ movedSpace (rhoE ρ e c), Qf x = 0 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at hbc
    exact hbc rfl
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hbc
    exact hbc rfl
  have h1 := hs.isLongRootElement_rhoE_perp he hef hb hb0 hbe hbf
  have h2 := hs.isLongRootElement_rhoE_perp he hef hc hc0 hce hcf
  have hdisj' : Disjoint (movedSpace (rhoE ρ e b)) (movedSpace (rhoE ρ e c)) :=
    disjoint_iff.mpr hdisj
  have hcomm : rhoE ρ e b * rhoE ρ e c = rhoE ρ e c * rhoE ρ e b :=
    rhoE_mul_comm (by rw [polar_comm]; exact hbe) (by rw [polar_comm]; exact hce)
  refine ⟨movedSpace_mul_eq_sup_of_commute hs.nd h1 h2 hcomm hdisj', ?_, fun x hx => ?_⟩
  · have h3 := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace (rhoE ρ e b))
      (movedSpace (rhoE ρ e c))
    rw [hdisj, finrank_bot, h1.finrank_movedSpace hs.nd, h2.finrank_movedSpace hs.nd] at h3
    omega
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hyz : polar Qf y z = 0 :=
      mem_orthogonal_iff_polar.mp (movedSpace_le_orthogonal_of_commute h1 h2 hcomm hdisj' hz) y hy
    rw [QuadraticMap.map_add Qf, h1.qf_eq_zero_of_mem_movedSpace hy,
      h2.qf_eq_zero_of_mem_movedSpace hz, hyz, add_zero, add_zero]

omit [Finite K] in
private theorem OmegaSetting.iSup_rhoE_facts_frame (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥) :
    finrank K ↥(⨆ (w : N) (_ : polar QN e w = 0), movedSpace (rhoE ρ e w)) = 4 ∧
      ∀ x ∈ ⨆ (w : N) (_ : polar QN e w = 0), movedSpace (rhoE ρ e w), Qf x = 0 := by
  have he0 := (ne_zero_of_polar_eq_one hF.ef).1
  have hpp' : polar QN p p' ≠ 0 := by rw [hF.pp']; exact one_ne_zero
  rw [hs.iSup_movedSpace_rhoE_eq_of_caseII hfix hK hF hII]
  exact (hs.axes_sup_facts hF.e_sing hF.ef hF.p_sing hF.p'_sing
    (by rw [polar_comm]; exact hF.ep) (by rw [polar_comm]; exact hF.fp)
    (by rw [polar_comm]; exact hF.ep') (by rw [polar_comm]; exact hF.fp') hpp'
    (hII e p p' ⟨hF.e_sing, he0, hF.p_sing, hF.p'_sing, hF.ep, hF.ep', hpp'⟩)).2

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem OmegaSetting.exists_singular_polar_ne_zero (hs : OmegaSetting QN Qf ρ)
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v) {w : N}
    (hwe : polar QN w e = 0) (hwf : polar QN w f = 0) (hw : QN w ≠ 0) :
    ∃ s : N, QN s = 0 ∧ polar QN s e = 0 ∧ polar QN s f = 0 ∧ polar QN s w ≠ 0 := by
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have hpe : polar QN p e = 0 := by rw [polar_comm]; exact hF.ep
  have hpf : polar QN p f = 0 := by rw [polar_comm]; exact hF.fp
  have hp'e : polar QN p' e = 0 := by rw [polar_comm]; exact hF.ep'
  have hp'f : polar QN p' f = 0 := by rw [polar_comm]; exact hF.fp'
  by_cases hp : polar QN p w = 0
  swap
  · exact ⟨p, hF.p_sing, hpe, hpf, hp⟩
  by_cases hp' : polar QN p' w = 0
  swap
  · exact ⟨p', hF.p'_sing, hp'e, hp'f, hp'⟩
  have key : ∀ x : N, polar QN x e = 0 → polar QN x f = 0 → polar QN x p = 0 →
      polar QN x p' = 0 → polar QN x w ≠ 0 →
      ∃ s : N, QN s = 0 ∧ polar QN s e = 0 ∧ polar QN s f = 0 ∧ polar QN s w ≠ 0 := by
    intro x hxe hxf hxp hxp' hxw
    have hpx : polar QN p x = 0 := by rw [polar_comm]; exact hxp
    have hp'x : polar QN p' x = 0 := by rw [polar_comm]; exact hxp'
    refine ⟨p + QN x • p' + x, ?_, ?_, ?_, ?_⟩
    · simp only [QuadraticMap.map_add QN, map_smul_eq_sq, polar_add_left, polar_smul_left_eq,
        polar_smul_right_eq, hF.p_sing, hF.p'_sing, hF.pp', hpx, hp'x]
      linear_combination (QN x) * h2
    · rw [polar_add_left, polar_add_left, polar_smul_left_eq, hpe, hp'e, hxe]
      ring
    · rw [polar_add_left, polar_add_left, polar_smul_left_eq, hpf, hp'f, hxf]
      ring
    · rw [polar_add_left, polar_add_left, polar_smul_left_eq, hp, hp', zero_add, mul_zero,
        zero_add]
      exact hxw
  obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
  obtain ⟨hve, hvf, hvp, hvp'⟩ := hF.v_perp
  by_cases hu : polar QN u w = 0
  swap
  · exact key u hue huf hup hup' hu
  by_cases hv : polar QN v w = 0
  swap
  · exact key v hve hvf hvp hvp' hv
  exfalso
  have hker : Submodule.span K' ({e, f, p, p', u, v} : Set N) ≤
      LinearMap.ker (polarBilin QN w) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply]
    rcases hy with h | h | h | h | h | h <;> rw [h]
    · exact hwe
    · exact hwf
    · rw [polar_comm]; exact hp
    · rw [polar_comm]; exact hp'
    · rw [polar_comm]; exact hu
    · rw [polar_comm]; exact hv
  apply hw
  have hw0 : w = 0 := hs.nd_N w fun y => by
    have hy := hker (hF.span y)
    rwa [LinearMap.mem_ker, polarBilin_apply_apply] at hy
  rw [hw0, QuadraticMap.map_zero]

omit [Finite K] in
private theorem OmegaSetting.movedSpace_rhoE_eq_iSup_of_perp (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {w : N} (hwe : polar QN w e = 0) (hwf : polar QN w f = 0) (hw : QN w ≠ 0) :
    movedSpace (rhoE ρ e w) = ⨆ (x : N) (_ : polar QN e x = 0), movedSpace (rhoE ρ e x) := by
  obtain ⟨s, hsQ, hse, hsf, hsw⟩ := hs.exists_singular_polar_ne_zero hF hwe hwf hw
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have he0 := (ne_zero_of_polar_eq_one hF.ef).1
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : N, s₁ = (QN w / polar QN s w) • s := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂ : N, s₂ = w + s₁ := ⟨_, rfl⟩
  have h1Q : QN s₁ = 0 := by rw [hs₁, map_smul_eq_sq, hsQ, mul_zero]
  have h1e : polar QN s₁ e = 0 := by rw [hs₁, polar_smul_left_eq, hse, mul_zero]
  have h1f : polar QN s₁ f = 0 := by rw [hs₁, polar_smul_left_eq, hsf, mul_zero]
  have h1w : polar QN s₁ w = QN w := by
    rw [hs₁, polar_smul_left_eq, div_mul_cancel₀ _ hsw]
  have h2Q : QN s₂ = 0 := by
    rw [hs₂, QuadraticMap.map_add QN, h1Q, polar_comm QN w s₁, h1w]
    linear_combination (QN w) * h2
  have h2e : polar QN s₂ e = 0 := by rw [hs₂, polar_add_left, hwe, h1e, add_zero]
  have h2f : polar QN s₂ f = 0 := by rw [hs₂, polar_add_left, hwf, h1f, add_zero]
  have h12 : polar QN s₁ s₂ ≠ 0 := by
    rw [hs₂, polar_add_right, h1w, polar_self_eq_zero h1Q, add_zero]
    exact hw
  have hsum : s₁ + s₂ = w := by
    have h2' : (2 : K') • s₁ = 0 := by rw [h2, zero_smul]
    rw [hs₂]
    linear_combination (norm := module) h2'
  have hflag : IsFlag QN e s₁ s₂ :=
    ⟨hF.e_sing, he0, h1Q, h2Q, by rw [polar_comm]; exact h1e, by rw [polar_comm]; exact h2e, h12⟩
  obtain ⟨hmul, hfin, -⟩ := hs.axes_sup_facts hF.e_sing hF.ef h1Q h2Q h1e h1f h2e h2f h12
    (hII e s₁ s₂ hflag)
  have hrho : rhoE ρ e w = rhoE ρ e s₁ * rhoE ρ e s₂ := by
    rw [rhoE_mul (by rw [polar_comm]; exact h1e) (by rw [polar_comm]; exact h2e), hsum]
  rw [hrho, hmul]
  refine Submodule.eq_of_le_of_finrank_eq (sup_le (le_iSup₂_of_le s₁ ?_ le_rfl)
    (le_iSup₂_of_le s₂ ?_ le_rfl)) ?_
  · rw [polar_comm]; exact h1e
  · rw [polar_comm]; exact h2e
  · rw [hfin, (hs.iSup_rhoE_facts_frame hfix hK hF hII).1]

omit [Finite K] in
private theorem OmegaSetting.movedSpace_rhoE_eq_iSup_frame (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {w : N} (hew : polar QN e w = 0) (hw : QN w ≠ 0) :
    movedSpace (rhoE ρ e w) = ⨆ (x : N) (_ : polar QN e x = 0), movedSpace (rhoE ρ e x) := by
  have hwe : polar QN w e = 0 := by rw [polar_comm]; exact hew
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have hee : polar QN e e = 0 := polar_self_eq_zero hF.e_sing
  have h1e : polar QN (w - polar QN w f • e) e = 0 := by
    rw [polar_sub_left, polar_smul_left_eq, hwe, hee]
    ring
  have h1f : polar QN (w - polar QN w f • e) f = 0 := by
    rw [polar_sub_left, polar_smul_left_eq, hF.ef]
    ring
  have h1Q : QN (w - polar QN w f • e) = QN w := by
    have hsub : w - polar QN w f • e = w + polar QN w f • e := by
      have h2e : (2 : K') • e = 0 := by rw [h2, zero_smul]
      linear_combination (norm := module) (-polar QN w f) • h2e
    rw [hsub, QuadraticMap.map_add QN, map_smul_eq_sq, hF.e_sing, polar_smul_right_eq, hwe]
    ring
  rw [← rhoE_sub_smul_self (ρ := ρ) hF.e_sing w (polar QN w f)]
  exact hs.movedSpace_rhoE_eq_iSup_of_perp hfix hK hF hII h1e h1f (by rw [h1Q]; exact hw)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem OmegaSetting.exists_elementary_apply_frame (hs : OmegaSetting QN Qf ρ)
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v) {a : N} (ha : QN a = 0)
    (ha0 : a ≠ 0) : ∃ g : ↥(elementaryGroup QN), (g : N ≃ₗ[K'] N) e = a := by
  have he0 := (ne_zero_of_polar_eq_one hF.ef).1
  let P₁ : HypPair QN := ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩
  let P₂ : HypPair QN := ⟨p, p', hF.p_sing, hF.p'_sing, hF.pp'⟩
  have horth : P₁.Orth P₂ := ⟨hF.ep, hF.ep', hF.fp, hF.fp'⟩
  obtain ⟨g, hg, hge⟩ := exists_mem_elementaryGroup_apply_eq hs.ndN horth he0 ha0
    (hF.e_sing.trans ha.symm)
  exact ⟨⟨g, hg⟩, hge⟩

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
private theorem iSup_movedSpace_rhoE_apply (g : ↥(elementaryGroup QN)) (a : N) :
    ⨆ (w : N) (_ : polar QN ((g : N ≃ₗ[K'] N) a) w = 0),
        movedSpace (rhoE ρ ((g : N ≃ₗ[K'] N) a) w) =
      (⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)).map (ρ g : V →ₗ[K] V) := by
  have hgO : (g : N ≃ₗ[K'] N) ∈ TauCeti.QuadraticMap.orthogonalGroup QN :=
    elementaryGroup_le_orthogonalGroup QN g.2
  refine le_antisymm (iSup₂_le fun w hw => ?_) ?_
  · have hgw : (g : N ≃ₗ[K'] N) ((g : N ≃ₗ[K'] N).symm w) = w := LinearEquiv.apply_symm_apply _ w
    have hw' : polar QN a ((g : N ≃ₗ[K'] N).symm w) = 0 := by
      rw [← polar_map_of_mem hgO, hgw]
      exact hw
    have h := movedSpace_rhoE_apply (ρ := ρ) g a ((g : N ≃ₗ[K'] N).symm w)
    rw [hgw] at h
    rw [h]
    exact Submodule.map_mono (le_iSup₂_of_le _ hw' le_rfl)
  · rw [Submodule.map_le_iff_le_comap]
    refine iSup₂_le fun w hw => ?_
    rw [← Submodule.map_le_iff_le_comap, ← movedSpace_rhoE_apply]
    exact le_iSup₂_of_le _ (by rw [polar_map_of_mem hgO]; exact hw) le_rfl

omit [Finite K] in
theorem OmegaSetting.finrank_iSup_movedSpace_rhoE_of_caseII (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {a : N} (ha : QN a = 0) (ha0 : a ≠ 0) :
    finrank K ↥(⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)) = 4 := by
  obtain ⟨g, hg⟩ := hs.exists_elementary_apply_frame hF ha ha0
  have h := iSup_movedSpace_rhoE_apply (ρ := ρ) g e
  rw [hg] at h
  rw [h, LinearEquiv.finrank_map_eq]
  exact (hs.iSup_rhoE_facts_frame hfix hK hF hII).1

omit [Finite K] in
theorem OmegaSetting.qf_eq_zero_of_mem_iSup_movedSpace_rhoE_of_caseII (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {a : N} (ha : QN a = 0) (ha0 : a ≠ 0) {x : V}
    (hx : x ∈ ⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)) : Qf x = 0 := by
  obtain ⟨g, hg⟩ := hs.exists_elementary_apply_frame hF ha ha0
  have h := iSup_movedSpace_rhoE_apply (ρ := ρ) g e
  rw [hg] at h
  rw [h] at hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact (hs.iso g y).trans ((hs.iSup_rhoE_facts_frame hfix hK hF hII).2 y hy)

omit [Finite K] in
theorem OmegaSetting.movedSpace_rhoE_eq_iSup_of_caseII (hs : OmegaSetting QN Qf ρ)
    (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0) (hK : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (hII : ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥)
    {a w : N} (ha : QN a = 0) (ha0 : a ≠ 0) (haw : polar QN a w = 0) (hw : QN w ≠ 0) :
    movedSpace (rhoE ρ a w) = ⨆ (x : N) (_ : polar QN a x = 0), movedSpace (rhoE ρ a x) := by
  obtain ⟨g, hg⟩ := hs.exists_elementary_apply_frame hF ha ha0
  have hgO : (g : N ≃ₗ[K'] N) ∈ TauCeti.QuadraticMap.orthogonalGroup QN :=
    elementaryGroup_le_orthogonalGroup QN g.2
  have hgw : (g : N ≃ₗ[K'] N) ((g : N ≃ₗ[K'] N).symm w) = w := LinearEquiv.apply_symm_apply _ w
  have hw' : polar QN e ((g : N ≃ₗ[K'] N).symm w) = 0 := by
    rw [← polar_map_of_mem hgO, hg, hgw]
    exact haw
  have hQw' : QN ((g : N ≃ₗ[K'] N).symm w) = QN w := by
    rw [← map_of_mem hgO ((g : N ≃ₗ[K'] N).symm w), hgw]
  have h1 := movedSpace_rhoE_apply (ρ := ρ) g e ((g : N ≃ₗ[K'] N).symm w)
  rw [hg, hgw] at h1
  have h2 := iSup_movedSpace_rhoE_apply (ρ := ρ) g e
  rw [hg] at h2
  rw [h1, hs.movedSpace_rhoE_eq_iSup_frame hfix hK hF hII hw' (by rw [hQw']; exact hw)]
  exact h2.symm

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
