module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthIso
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Lemma610

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polarNondegOn_of_isCompl {X Y : Submodule K V} (hQ : (polarBilin Q).Nondegenerate)
    (hXY : IsCompl X Y) (horth : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0) : PolarNondegOn Q X := by
  intro x hx h
  apply eq_zero_of_polar_eq_zero hQ
  intro v
  have hv : v ∈ X ⊔ Y := by
    rw [hXY.sup_eq_top]
    trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [polar_add_right, h a ha, horth x hx b hb, zero_add]

variable [Finite K] [FiniteDimensional K V]

theorem exists_hypPair_le (hodd : Odd (Nat.card K)) {X : Submodule K V}
    (hX : PolarNondegOn Q X) (h3 : 3 ≤ Module.finrank K X) :
    ∃ P : HypPair Q, P.e ∈ X ∧ P.f ∈ X := by
  have hnd : (polarBilin (Q.restrict X)).Nondegenerate := nondegenerate_polarBilin_restrict hX
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_finrank_ge_three hodd (Q.restrict X) hnd h3
  have hQe : Q (v : V) = 0 := by simpa using hvQ
  have hve : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨y, hy, hey⟩ := hX.exists_polar_ne_zero v.2 hve
  have h1 : polar Q (v : V) ((polar Q (v : V) y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hey]
  refine ⟨HypPair.ofPolarEqOne hQe h1, v.2, ?_⟩
  exact X.sub_mem (X.smul_mem _ hy) (X.smul_mem _ v.2)

omit [Finite K] in
theorem finrank_inf_perp_hypPair (hQ : (polarBilin Q).Nondegenerate) {X : Submodule K V}
    (P : HypPair Q) (hPe : P.e ∈ X) (hPf : P.f ∈ X) :
    Module.finrank K ↥(X ⊓ P.perp) + 2 = Module.finrank K X := by
  have hsup : X ⊔ P.perp = ⊤ := by
    rw [eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr ⟨polar Q v P.f • P.e + polar Q v P.e • P.f, ?_, P.proj v,
      P.proj_mem_perp v, ?_⟩
    · exact X.add_mem (X.smul_mem _ hPe) (X.smul_mem _ hPf)
    · exact (P.eq_add_proj v).symm
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq X P.perp
  rw [hsup, finrank_top] at h1
  have h2 := finrank_hypPair_perp hQ P
  omega

theorem exists_frame_le_of_five_le (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    {X : Submodule K V} (hX : PolarNondegOn Q X) (h5 : 5 ≤ Module.finrank K X) :
    ∃ F : Frame Q, F.span ≤ X := by
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_le hodd hX (by omega)
  have hX' : PolarNondegOn Q (X ⊓ P.perp) := hX.inf_perp P hPe hPf
  have hd := finrank_inf_perp_hypPair hQ P hPe hPf
  obtain ⟨P', hP'e, hP'f⟩ := exists_hypPair_le hodd hX' (by omega)
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP'e).2
  obtain ⟨h3, h4⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP'f).2
  refine ⟨⟨P, P', ⟨h1, h3, h2, h4⟩⟩, ?_⟩
  rintro _ ⟨Y, rfl⟩
  rw [Frame.incl_apply]
  exact X.add_mem (X.add_mem (X.add_mem (X.smul_mem _ hPe) (X.smul_mem _ hPf))
    (X.smul_mem _ (Submodule.mem_inf.mp hP'e).1)) (X.smul_mem _ (Submodule.mem_inf.mp hP'f).1)

omit [Finite K] [FiniteDimensional K V] in
theorem map_mem_perp_of_scalar {F : Frame Q} {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c : K} (hc2 : c * c = 1)
    (hg : ∀ x ∈ F.span, g x = c • x) {r : V} (hr : r ∈ F.perp) : g r ∈ F.perp := by
  rw [Frame.mem_perp_iff_forall_incl]
  intro Y
  have hY : F.incl Y ∈ F.span := ⟨Y, rfl⟩
  have h1 : g (c • F.incl Y) = F.incl Y := by
    rw [map_smul, hg _ hY, smul_smul, hc2, one_smul]
  have h2 := polar_map_of_mem hgO r (c • F.incl Y)
  rw [h1, polar_smul_right_eq, (Frame.mem_perp_iff_forall_incl F).mp hr Y, mul_zero] at h2
  exact h2

omit [Finite K] [FiniteDimensional K V] in
theorem commute_La_neg_one_of_scalar {F : Frame Q} {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c : K} (hc2 : c * c = 1)
    (hg : ∀ x ∈ F.span, g x = c • x) : g * F.La (-1) = F.La (-1) * g := by
  refine LinearEquiv.ext fun x => ?_
  have hr : x - F.incl (F.coords x) ∈ F.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  have hgr := map_mem_perp_of_scalar hgO hc2 hg hr
  have hca : F.coords (g x) = c • F.coords x := by
    have h1 : g x = c • F.incl (F.coords x) + g (x - F.incl (F.coords x)) := by
      rw [← hg _ ⟨F.coords x, rfl⟩, ← map_add]
      congr 1
      abel
    rw [h1, map_add, map_smul, Frame.coords_incl, (Frame.mem_perp_iff F).mp hgr, add_zero]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_neg_one_apply,
    Frame.La_neg_one_apply, map_sub, map_smul, hg _ ⟨F.coords x, rfl⟩, hca, map_smul]

omit [Finite K] [FiniteDimensional K V] in
theorem commute_La_of_scalar_on_span (h2 : (2 : K) ≠ 0) {F : Frame Q} {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c : K} (hc2 : c * c = 1)
    (hg : ∀ x ∈ F.span, g x = c • x) (A : SL(2, K)) :
    g * F.La A = F.La A * g ∧ g * F.swap.La A = F.swap.La A * g := by
  have key : ∀ F' : Frame Q, (∀ x ∈ F'.span, g x = c • x) → ∀ A : SL(2, K),
      g * F'.La A = F'.La A * g := fun F' hF' A => by
    have hcomm := commute_La_neg_one_of_scalar hgO hc2 hF'
    refine Frame.commute_of_transport_eq_smul h2 hcomm hc2 (fun Y => ?_) A
    rw [Frame.transport_apply, hF' _ ⟨Y, rfl⟩, map_smul, Frame.coords_incl]
  exact ⟨key F hg A, key F.swap (fun x hx => hg x (by rwa [Frame.span_eq_swap_span] at hx)) A⟩

theorem exists_frame_scalar_of_commuting (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank K V) {i₁ i₂ : V ≃ₗ[K] V}
    (h₁ : i₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : i₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hi₁ : i₁ * i₁ = 1) (hi₂ : i₂ * i₂ = 1)
    (hc : i₁ * i₂ = i₂ * i₁) (h4₁ : Module.finrank K (negSpace i₁) = 4)
    (h4₂ : Module.finrank K (negSpace i₂) = 4)
    (hd : Odd (Module.finrank K ↥(negSpace i₁ ⊓ negSpace i₂))) :
    ∃ (F : Frame Q) (c : K), c * c = 1 ∧ ∀ x ∈ F.span, i₁ (i₂ x) = c • x := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set f : Module.End K V := (i₁ : Module.End K V) with hf_def
  set g : Module.End K V := (i₂ : Module.End K V) with hg_def
  have hf : f * f = 1 := LinearMap.ext fun x => LinearEquiv.congr_fun hi₁ x
  have hg : g * g = 1 := LinearMap.ext fun x => LinearEquiv.congr_fun hi₂ x
  have hfg : f * g = g * f := LinearMap.ext fun x => LinearEquiv.congr_fun hc x
  have hn1 : negSpace i₁ = f.eigenspace (signOf K false) := rfl
  have hn2 : negSpace i₂ = g.eigenspace (signOf K false) := rfl
  have hff : negSpace i₁ ⊓ negSpace i₂ = jointEigenspace f g (false, false) := rfl
  have e1 := finrank_eigenspace_eq h2 hg hfg false
  have e2 := finrank_eigenspace_eq' h2 hf hfg false
  have e3 := finrank_eigenspace_eq h2 hg hfg true
  rw [← hn1, h4₁] at e1
  rw [← hn2, h4₂] at e2
  have e4 : Module.finrank K (plusSp i₁) + Module.finrank K (minusSp i₁) =
      Module.finrank K V := Submodule.finrank_add_eq_of_isCompl (isCompl_plusSp_minusSp h2 hi₁)
  have hp1 : plusSp i₁ = f.eigenspace (signOf K true) := rfl
  have hm1 : minusSp i₁ = negSpace i₁ := rfl
  rw [hp1, e3, hm1, h4₁] at e4
  rw [hff] at hd
  have ha4 : Module.finrank K ↥(jointEigenspace f g (false, false)) ≤ 4 := by
    have := Submodule.finrank_mono (inf_le_left : negSpace i₁ ⊓ negSpace i₂ ≤ negSpace i₁)
    rw [hff, h4₁] at this
    exact this
  set ab : V ≃ₗ[K] V := i₁ * i₂ with hab
  have habO : ab ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.mul_mem _ h₁ h₂
  have habab : ab * ab = 1 := by
    calc i₁ * i₂ * (i₁ * i₂) = i₁ * (i₂ * i₁) * i₂ := by group
      _ = i₁ * (i₁ * i₂) * i₂ := by rw [← hc]
      _ = (i₁ * i₁) * (i₂ * i₂) := by group
      _ = 1 := by rw [hi₁, hi₂, one_mul]
  have hndPlus : PolarNondegOn Q (plusSp ab) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 habab)
      (fun x hx y hy => polar_plusSp_minusSp h2 habO hx hy)
  have hndMinus : PolarNondegOn Q (minusSp ab) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 habab).symm
      (fun x hx y hy => by rw [polar_comm]; exact polar_plusSp_minusSp h2 habO hy hx)
  have hdis : ∀ b₁ b₂ : Bool, Disjoint (jointEigenspace f g (false, b₁))
      (jointEigenspace f g (true, b₂)) := by
    intro b₁ b₂
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hs : f x = -x := by simpa using (mem_jointEigenspace.mp hx).1
    have ht : f x = x := by simpa using (mem_jointEigenspace.mp hx').1
    have h : -x = x := hs.symm.trans ht
    have h' : (2 : K) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel x
    exact (smul_eq_zero.mp h').resolve_left h2
  have hfin : ∀ b₁ b₂ : Bool, Module.finrank K ↥(jointEigenspace f g (false, b₁) ⊔
      jointEigenspace f g (true, b₂)) = Module.finrank K ↥(jointEigenspace f g (false, b₁)) +
        Module.finrank K ↥(jointEigenspace f g (true, b₂)) := by
    intro b₁ b₂
    have := Submodule.finrank_sup_add_finrank_inf_eq (jointEigenspace f g (false, b₁))
      (jointEigenspace f g (true, b₂))
    rw [(hdis b₁ b₂).eq_bot, finrank_bot] at this
    omega
  have hcases : Module.finrank K ↥(jointEigenspace f g (false, false)) = 1 ∨
      Module.finrank K ↥(jointEigenspace f g (false, false)) = 3 := by
    obtain ⟨k, hk⟩ := hd
    omega
  rcases hcases with h1 | h3
  ·
    have hsub : jointEigenspace f g (false, true) ⊔ jointEigenspace f g (true, false) ≤
        minusSp ab := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨hx1, hx2⟩ := mem_jointEigenspace.mp hx
        rw [mem_minusSp]
        simp only [signOf_false, signOf_true, neg_smul, one_smul] at hx1 hx2
        show i₁ (i₂ x) = -x
        have h1' : i₁ x = -x := hx1
        have h2' : i₂ x = x := hx2
        rw [h2', h1']
      · obtain ⟨hx1, hx2⟩ := mem_jointEigenspace.mp hx
        rw [mem_minusSp]
        simp only [signOf_false, signOf_true, neg_smul, one_smul] at hx1 hx2
        show i₁ (i₂ x) = -x
        have h1' : i₁ x = x := hx1
        have h2' : i₂ x = -x := hx2
        rw [h2', map_neg, h1']
    have h5 : 5 ≤ Module.finrank K (minusSp ab) := by
      have := Submodule.finrank_mono hsub
      rw [hfin true false] at this
      omega
    obtain ⟨F, hF⟩ := exists_frame_le_of_five_le hodd hQ hndMinus h5
    refine ⟨F, -1, by ring, fun x hx => ?_⟩
    have := mem_minusSp.mp (hF hx)
    rw [neg_one_smul]
    exact this
  ·
    have hsub : jointEigenspace f g (false, false) ⊔ jointEigenspace f g (true, true) ≤
        plusSp ab := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨hx1, hx2⟩ := mem_jointEigenspace.mp hx
        rw [mem_plusSp]
        simp only [signOf_false, neg_smul, one_smul] at hx1 hx2
        show i₁ (i₂ x) = x
        have h1' : i₁ x = -x := hx1
        have h2' : i₂ x = -x := hx2
        rw [h2', map_neg, h1', neg_neg]
      · obtain ⟨hx1, hx2⟩ := mem_jointEigenspace.mp hx
        rw [mem_plusSp]
        simp only [signOf_true, one_smul] at hx1 hx2
        show i₁ (i₂ x) = x
        have h1' : i₁ x = x := hx1
        have h2' : i₂ x = x := hx2
        rw [h2', h1']
    have h5 : 5 ≤ Module.finrank K (plusSp ab) := by
      have := Submodule.finrank_mono hsub
      rw [hfin false true] at this
      omega
    obtain ⟨F, hF⟩ := exists_frame_le_of_five_le hodd hQ hndPlus h5
    refine ⟨F, 1, by ring, fun x hx => ?_⟩
    have := mem_plusSp.mp (hF hx)
    rw [one_smul]
    exact this

end CFSG.ClassicalInvolution.Asc77
