module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6

set_option linter.unusedSectionVars false

section Planes

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_hypPair_plane {W : Submodule K V} (hnd : PolarNondegOn Q W)
    (hW2 : Module.finrank K W = 2) {u : V} (hu : u ∈ W) (hu0 : u ≠ 0) (hQu : Q u = 0) :
    ∃ P : HypPair Q, hypPlane P = W ∧ P.e = u := by
  obtain ⟨y, hyW, hy⟩ := hnd.exists_polar_ne_zero hu hu0
  have h1 : polar Q u ((polar Q u y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hy]
  refine ⟨HypPair.ofPolarEqOne hQu h1, ?_, rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [hypPlane, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact hu
    · exact W.sub_mem (W.smul_mem _ hyW) (W.smul_mem _ hu)
  · rw [finrank_hypPlane, hW2]

theorem two_le_finrank_of_singular {W : Submodule K V}
    (hnd : PolarNondegOn Q W) {u : V} (hu : u ∈ W) (hu0 : u ≠ 0) (hQu : Q u = 0) :
    2 ≤ Module.finrank K W := by
  obtain ⟨y, hyW, hy⟩ := hnd.exists_polar_ne_zero hu hu0
  have hli : LinearIndependent K ![u, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun v => polar Q u v) hst
    simp only [polar_add_right, polar_smul_right_eq, polar_zero_right,
      polar_self_eq_zero hQu] at h1
    have ht : t = 0 := by
      have : t * polar Q u y = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_right hy
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hu0, rfl⟩
  have hle : Submodule.span K (Set.range ![u, y]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hyW
  have h2 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h2
  exact h2

end Planes

section Eigen

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem mem_negSpace_iff' {g : V ≃ₗ[K] V} {x : V} : x ∈ negSpace g ↔ g x = -x := by
  rw [negSpace, Module.End.mem_eigenspace_iff]
  simp

theorem mem_posSpace_iff' {g : V ≃ₗ[K] V} {x : V} : x ∈ posSpace g ↔ g x = x := by
  rw [posSpace, Module.End.mem_eigenspace_iff]
  simp

theorem polar_pos_neg (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {e n : V} (he : g e = e) (hn : g n = -n) :
    polar Q e n = 0 :=
  polar_eigen_orth h2 hgO (a := 1) (by norm_num) (by rw [he, one_smul])
    (by rw [hn, neg_smul, one_smul])

theorem exists_singular_eigen (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    {L : V →ₗ[K] V}
    (hiso : ∀ v w, polar Q (L v) w + polar Q v (L w) + polar Q (L v) (L w) = 0)
    (hQL : ∀ v, Q (L v) + polar Q v (L v) = 0)
    (hgL : ∀ v, g (L v) = -L (g v)) (hL0 : ∃ v, L v ≠ 0) :
    (∃ x, g x = x ∧ L x ≠ 0 ∧ Q (L x) = 0 ∧ g (L x) = -L x) ∧
      (∃ y, g y = -y ∧ L y ≠ 0 ∧ Q (L y) = 0 ∧ g (L y) = L y) := by
  have hgg : ∀ x, g (g x) = x := fun x => by simpa using LinearEquiv.congr_fun hg2 x
  have decomp : ∀ v : V, ∃ e n : V, g e = e ∧ g n = -n ∧ v = e + n := by
    intro v
    obtain ⟨e, n, he, hn, hv⟩ := exists_eigen_decomp h2 hg2 (a := 1) (by norm_num) v
    exact ⟨e, n, by simpa using he, by simpa using hn, hv⟩
  have hplus : ∀ x, g x = x → g (L x) = -L x ∧ Q (L x) = 0 := by
    intro x hx
    have e1 : g (L x) = -L x := by rw [hgL, hx]
    refine ⟨e1, ?_⟩
    have hp : polar Q x (L x) = 0 := polar_pos_neg h2 hgO hx e1
    have := hQL x
    rw [hp, add_zero] at this
    exact this
  have hminus : ∀ y, g y = -y → g (L y) = L y ∧ Q (L y) = 0 := by
    intro y hy
    have e1 : g (L y) = L y := by rw [hgL, hy, map_neg, neg_neg]
    refine ⟨e1, ?_⟩
    have hp : polar Q y (L y) = 0 := by
      rw [polar_comm]
      exact polar_pos_neg h2 hgO e1 hy
    have := hQL y
    rw [hp, add_zero] at this
    exact this
  have hexP : ∃ x, g x = x ∧ L x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv⟩ := hL0
    obtain ⟨e, n, he, hn, hvv⟩ := decomp v
    have hLe : L e = 0 := hcon e he
    have hLn : L n = 0 := by
      refine eq_zero_of_polar_eq_zero hQ fun w => ?_
      obtain ⟨e', n', he', hn', hww⟩ := decomp w
      have e1 : g (L n) = L n := by rw [hgL, hn, map_neg, neg_neg]
      have h1 : polar Q (L n) e' = 0 := by
        have := hiso n e'
        have hLe' : L e' = 0 := hcon e' he'
        rwa [hLe', polar_zero_right, polar_zero_right, add_zero, add_zero] at this
      have h3 : polar Q (L n) n' = 0 := polar_pos_neg h2 hgO e1 hn'
      rw [hww, polar_add_right, h1, h3, add_zero]
    exact hv (by rw [hvv, map_add, hLe, hLn, add_zero])
  have hexM : ∃ y, g y = -y ∧ L y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv⟩ := hL0
    obtain ⟨e, n, he, hn, hvv⟩ := decomp v
    have hLn : L n = 0 := hcon n hn
    have hLe : L e = 0 := by
      refine eq_zero_of_polar_eq_zero hQ fun w => ?_
      obtain ⟨e', n', he', hn', hww⟩ := decomp w
      have e1 : g (L e) = -L e := by rw [hgL, he]
      have h1 : polar Q (L e) n' = 0 := by
        have := hiso e n'
        have hLn' : L n' = 0 := hcon n' hn'
        rwa [hLn', polar_zero_right, polar_zero_right, add_zero, add_zero] at this
      have h3 : polar Q (L e) e' = 0 := by
        rw [polar_comm]
        exact polar_pos_neg h2 hgO he' e1
      rw [hww, polar_add_right, h3, h1, add_zero]
    exact hv (by rw [hvv, map_add, hLe, hLn, add_zero])
  obtain ⟨x, hx, hLx⟩ := hexP
  obtain ⟨y, hy, hLy⟩ := hexM
  exact ⟨⟨x, hx, hLx, (hplus x hx).2, (hplus x hx).1⟩, ⟨y, hy, hLy, (hminus y hy).2,
    (hminus y hy).1⟩⟩


theorem exists_planes_of_singular_eigen (h2 : (2 : K) ≠ 0)
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    {W : Submodule K V} (hWnd : PolarNondegOn Q W) (hW4 : Module.finrank K W = 4)
    (hgW : ∀ x ∈ W, g x ∈ W) {uP uM : V} (huP : uP ∈ W) (hgP : g uP = uP) (h0P : uP ≠ 0)
    (hQP : Q uP = 0) (huM : uM ∈ W) (hgM : g uM = -uM) (h0M : uM ≠ 0) (hQM : Q uM = 0) :
    ∃ π ρ : HypPair Q, π.Orth ρ ∧ hypPlane π ⊔ hypPlane ρ = W ∧
      (∀ x ∈ hypPlane π, g x = -x) ∧ (∀ x ∈ hypPlane ρ, g x = x) := by
  have hgg : ∀ x, g (g x) = x := fun x => by simpa using LinearEquiv.congr_fun hg2 x
  set Wp : Submodule K V := W ⊓ posSpace g with hWp
  set Wm : Submodule K V := W ⊓ negSpace g with hWm
  have memWp : ∀ x, x ∈ Wp ↔ x ∈ W ∧ g x = x := fun x => by
    rw [hWp, Submodule.mem_inf, mem_posSpace_iff']
  have memWm : ∀ x, x ∈ Wm ↔ x ∈ W ∧ g x = -x := fun x => by
    rw [hWm, Submodule.mem_inf, mem_negSpace_iff']
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have split : ∀ w ∈ W, ∃ e ∈ Wp, ∃ n ∈ Wm, w = e + n := by
    intro w hw
    have hgw := hgW w hw
    refine ⟨(2 : K)⁻¹ • (w + g w), (memWp _).mpr ⟨W.smul_mem _ (W.add_mem hw hgw), ?_⟩,
      (2 : K)⁻¹ • (w - g w), (memWm _).mpr ⟨W.smul_mem _ (W.sub_mem hw hgw), ?_⟩, ?_⟩
    · simp only [map_smul, map_add, hgg, add_comm]
    · simp only [map_smul, map_sub, hgg]
      rw [← smul_neg, neg_sub]
    · rw [← smul_add]
      have : w + g w + (w - g w) = (2 : K) • w := by module
      rw [this, smul_smul, h22, one_smul]
  have hpm : ∀ x ∈ Wp, ∀ y ∈ Wm, polar Q x y = 0 := fun x hx y hy =>
    polar_pos_neg h2 hgO ((memWp x).mp hx).2 ((memWm y).mp hy).2
  have hndp : PolarNondegOn Q Wp := by
    intro x hx hx0
    refine hWnd x ((memWp x).mp hx).1 fun w hw => ?_
    obtain ⟨e, he, n, hn, rfl⟩ := split w hw
    rw [polar_add_right, hx0 e he, hpm x hx n hn, add_zero]
  have hndm : PolarNondegOn Q Wm := by
    intro x hx hx0
    refine hWnd x ((memWm x).mp hx).1 fun w hw => ?_
    obtain ⟨e, he, n, hn, rfl⟩ := split w hw
    rw [polar_add_right, polar_comm Q x e, hpm e he x hx, hx0 n hn, add_zero]
  have h2p : 2 ≤ Module.finrank K Wp := two_le_finrank_of_singular hndp
    ((memWp uP).mpr ⟨huP, hgP⟩) h0P hQP
  have h2m : 2 ≤ Module.finrank K Wm := two_le_finrank_of_singular hndm
    ((memWm uM).mpr ⟨huM, hgM⟩) h0M hQM
  have hdisj : Disjoint Wp Wm := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have e1 := ((memWp x).mp hx).2
    have e2 := ((memWm x).mp hx').2
    have : (2 : K) • x = 0 := by
      have h3 : x = -x := e1.symm.trans e2
      calc (2 : K) • x = x + x := two_smul K x
        _ = x + -x := by rw [← h3]
        _ = 0 := add_neg_cancel x
    exact (smul_eq_zero.mp this).resolve_left h2
  have hsup : Wp ⊔ Wm = W := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    obtain ⟨e, he, n, hn, rfl⟩ := split w hw
    exact Submodule.add_mem_sup he hn
  have hdim : Module.finrank K Wp + Module.finrank K Wm = 4 := by
    have := Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint hdisj
    rw [hsup] at this
    omega
  have hp2 : Module.finrank K Wp = 2 := by omega
  have hm2 : Module.finrank K Wm = 2 := by omega
  obtain ⟨ρ, hρ, hρe⟩ := exists_hypPair_plane hndp hp2 ((memWp uP).mpr ⟨huP, hgP⟩) h0P hQP
  obtain ⟨π, hπ, hπe⟩ := exists_hypPair_plane hndm hm2 ((memWm uM).mpr ⟨huM, hgM⟩) h0M hQM
  have hmemρ : ∀ x ∈ hypPlane ρ, x ∈ Wp := fun x hx => hρ ▸ hx
  have hmemπ : ∀ x ∈ hypPlane π, x ∈ Wm := fun x hx => hπ ▸ hx
  refine ⟨π, ρ, ?_, ?_, fun x hx => ((memWm x).mp (hmemπ x hx)).2,
    fun x hx => ((memWp x).mp (hmemρ x hx)).2⟩
  · have hc : ∀ (a b : V), a ∈ Wm → b ∈ Wp → polar Q a b = 0 := fun a b ha hb => by
      rw [polar_comm]
      exact hpm b hb a ha
    exact ⟨hc _ _ (hmemπ _ (e_mem_hypPlane π)) (hmemρ _ (e_mem_hypPlane ρ)),
      hc _ _ (hmemπ _ (e_mem_hypPlane π)) (hmemρ _ (f_mem_hypPlane ρ)),
      hc _ _ (hmemπ _ (f_mem_hypPlane π)) (hmemρ _ (e_mem_hypPlane ρ)),
      hc _ _ (hmemπ _ (f_mem_hypPlane π)) (hmemρ _ (f_mem_hypPlane ρ))⟩
  · rw [hπ, hρ, sup_comm, hsup]

end Eigen

section Class

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem isCompl_pos_neg (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V} (hg2 : g * g = 1) :
    IsCompl (posSpace g) (negSpace g) :=
  isCompl_eigenspace_of_mul_self h2 (T := (g : Module.End K V)) (by
    refine LinearMap.ext fun x => ?_
    have := LinearEquiv.congr_fun hg2 x
    simpa using this)

theorem eq_self_of_perp_plane (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1) (π : HypPair Q)
    (hneg : negSpace g = hypPlane π) {y : V} (hy : y ∈ π.perp) : g y = y := by
  have hgg : ∀ x, g (g x) = x := fun x => by simpa using LinearEquiv.congr_fun hg2 x
  obtain ⟨e, n, he, hn, hyv⟩ := exists_eigen_decomp h2 hg2 (a := 1) (by norm_num) y
  have he' : g e = e := by simpa using he
  have hn' : g n = -n := by simpa using hn
  have hnπ : n ∈ hypPlane π := hneg ▸ mem_negSpace_iff'.mpr hn'
  have hperp : ∀ x ∈ hypPlane π, polar Q n x = 0 := by
    intro x hx
    have h1 : polar Q y x = 0 := by
      obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff π).mp hx
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q y π.e,
        polar_comm Q y π.f, (HypPair.mem_perp.mp hy).1, (HypPair.mem_perp.mp hy).2]
      ring
    have h3 : polar Q e x = 0 :=
      polar_pos_neg h2 hgO he' (mem_negSpace_iff'.mp (hneg ▸ hx))
    rw [hyv, polar_add_left, h3, zero_add] at h1
    exact h1
  have hn0 : n = 0 := polarNondegOn_hypPlane π n hnπ hperp
  rw [hyv, hn0, add_zero]
  exact he'


theorem negSpace_eq_plane_b4 (h2 : (2 : K) ≠ 0) (hd : Module.finrank K V = 9)
    {g h : V ≃ₗ[K] V} (hg2 : g * g = 1)
    {WM WJ : Submodule K V} (hWM : Module.finrank K WM = 4) (hWMnd : PolarNondegOn Q WM)
    (hMJ : ∀ x ∈ WM, ∀ y ∈ WJ, polar Q x y = 0) (hgM : ∀ x ∈ WM, g x = x)
    (π ρ : HypPair Q) (hsup : hypPlane π ⊔ hypPlane ρ = WJ)
    (hgπ : ∀ x ∈ hypPlane π, g x = -x) (hgρ : ∀ x ∈ hypPlane ρ, g x = x)
    (hhneg : negSpace h ≤ WM) (hhdim : Module.finrank K (negSpace h) = 2)
    (hhfix : ∀ x, (∀ w ∈ WM, polar Q x w = 0) → h x = x)
    {W₁ W₂ : Submodule K V} (hW₁ : Module.finrank K W₁ = 4) (hW₂ : Module.finrank K W₂ = 4)
    (hne : W₁ ≠ W₂) {ε₁ ε₂ : K} (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hg₁ : ∀ x ∈ W₁, g x = ε₁ • x) (hg₂ : ∀ x ∈ W₂, g x = ε₂ • x)
    (hh₁ : ∀ x ∈ W₁, h x = x) (hh₂ : ∀ x ∈ W₂, h x = x) :
    negSpace g = hypPlane π := by
  classical
  have hcompl := isCompl_pos_neg h2 hg2
  have hsum : Module.finrank K (posSpace g) + Module.finrank K (negSpace g) = 9 := by
    rw [← hd]
    exact Submodule.finrank_add_eq_of_isCompl hcompl
  have hπle : hypPlane π ≤ negSpace g := fun x hx => mem_negSpace_iff'.mpr (hgπ x hx)
  have hρle : hypPlane ρ ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgρ x hx)
  have hWMle : WM ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgM x hx)
  have hρJ : hypPlane ρ ≤ WJ := hsup ▸ le_sup_right
  have hdisj : Disjoint WM (hypPlane ρ) := by
    rw [Submodule.disjoint_def]
    intro x hxM hxρ
    exact hWMnd x hxM fun w hw => by rw [polar_comm]; exact hMJ w hw x (hρJ hxρ)
  have hdimρ : Module.finrank K ↥(WM ⊔ hypPlane ρ) = 6 := by
    rw [Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint hdisj, hWM, finrank_hypPlane]
  have hpos6 : 6 ≤ Module.finrank K (posSpace g) := by
    have := Submodule.finrank_mono (sup_le hWMle hρle)
    omega
  have hneg2 : 2 ≤ Module.finrank K (negSpace g) := by
    have := Submodule.finrank_mono hπle
    rw [finrank_hypPlane] at this
    exact this
  rcases (by omega : Module.finrank K (negSpace g) = 2 ∨ Module.finrank K (negSpace g) = 3) with
    h2' | h3'
  · exact (Submodule.eq_of_le_of_finrank_eq hπle (by rw [finrank_hypPlane, h2'])).symm
  · exfalso
    have hposeq : posSpace g = WM ⊔ hypPlane ρ :=
      (Submodule.eq_of_le_of_finrank_eq (sup_le hWMle hρle) (by omega)).symm
    have hA : Module.finrank K ↥(posSpace h ⊓ WM) ≤ 2 := by
      have hdisjA : Disjoint (posSpace h ⊓ WM) (negSpace h) := by
        rw [Submodule.disjoint_def]
        intro x hx hxn
        have e1 := mem_posSpace_iff'.mp hx.1
        have e2 := mem_negSpace_iff'.mp hxn
        have : (2 : K) • x = 0 := by
          have h3 : x = -x := e1.symm.trans e2
          calc (2 : K) • x = x + x := two_smul K x
            _ = x + -x := by rw [← h3]
            _ = 0 := add_neg_cancel x
        exact (smul_eq_zero.mp this).resolve_left h2
      have hle : posSpace h ⊓ WM ⊔ negSpace h ≤ WM := sup_le inf_le_right hhneg
      have h4 := Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint hdisjA
      have h5 := Submodule.finrank_mono hle
      omega
    have hZ : Module.finrank K ↥((posSpace h ⊓ WM) ⊔ hypPlane ρ) ≤ 4 := by
      have := Submodule.finrank_add_le_finrank_add_finrank (posSpace h ⊓ WM) (hypPlane ρ)
      rw [finrank_hypPlane] at this
      omega
    have hWi : ∀ (Wi : Submodule K V) (εi : K), Module.finrank K Wi = 4 →
        (εi = 1 ∨ εi = -1) → (∀ x ∈ Wi, g x = εi • x) → (∀ x ∈ Wi, h x = x) →
        Wi = (posSpace h ⊓ WM) ⊔ hypPlane ρ := by
      intro Wi εi hWi hεi hgi hhi
      have hεi1 : εi = 1 := by
        rcases hεi with rfl | rfl
        · rfl
        · exfalso
          have hle : Wi ≤ negSpace g := fun x hx =>
            mem_negSpace_iff'.mpr (by rw [hgi x hx, neg_smul, one_smul])
          have := Submodule.finrank_mono hle
          omega
      subst hεi1
      have hleZ : Wi ≤ (posSpace h ⊓ WM) ⊔ hypPlane ρ := by
        intro w hw
        have hwpos : w ∈ posSpace g := mem_posSpace_iff'.mpr (by rw [hgi w hw, one_smul])
        rw [hposeq] at hwpos
        obtain ⟨m, hm, p, hp, rfl⟩ := Submodule.mem_sup.mp hwpos
        have hpp : h p = p := hhfix p fun x hx => by
          rw [polar_comm]
          exact hMJ x hx p (hρJ hp)
        have hhm : h m = m := by
          have := hhi (m + p) hw
          rw [map_add, hpp] at this
          exact add_right_cancel this
        exact Submodule.add_mem_sup ⟨mem_posSpace_iff'.mpr hhm, hm⟩ hp
      have := Submodule.finrank_mono hleZ
      exact Submodule.eq_of_le_of_finrank_eq hleZ (by omega)
    exact hne ((hWi W₁ ε₁ hW₁ hε₁ hg₁ hh₁).trans (hWi W₂ ε₂ hW₂ hε₂ hg₂ hh₂).symm)


theorem eq_smul_of_perp_b4 (h2 : (2 : K) ≠ 0) (hd : Module.finrank K V = 9)
    {g h : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    {WM WJ : Submodule K V} (hWM : Module.finrank K WM = 4) (hWMnd : PolarNondegOn Q WM)
    (hMJ : ∀ x ∈ WM, ∀ y ∈ WJ, polar Q x y = 0) {ε : K} (hε : ε = 1 ∨ ε = -1)
    (hgM : ∀ x ∈ WM, g x = ε • x)
    (π ρ : HypPair Q) (hsup : hypPlane π ⊔ hypPlane ρ = WJ)
    (hgπ : ∀ x ∈ hypPlane π, g x = (-ε) • x) (hgρ : ∀ x ∈ hypPlane ρ, g x = ε • x)
    (hhneg : negSpace h ≤ WM) (hhdim : Module.finrank K (negSpace h) = 2)
    (hhfix : ∀ x, (∀ w ∈ WM, polar Q x w = 0) → h x = x)
    {W₁ W₂ : Submodule K V} (hW₁ : Module.finrank K W₁ = 4) (hW₂ : Module.finrank K W₂ = 4)
    (hne : W₁ ≠ W₂) {ε₁ ε₂ : K} (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hg₁ : ∀ x ∈ W₁, g x = ε₁ • x) (hg₂ : ∀ x ∈ W₂, g x = ε₂ • x)
    (hh₁ : ∀ x ∈ W₁, h x = x) (hh₂ : ∀ x ∈ W₂, h x = x) :
    ∀ y, y ∈ π.perp → g y = ε • y := by
  rcases hε with rfl | rfl
  · have hneg := negSpace_eq_plane_b4 h2 hd hg2 hWM hWMnd hMJ (fun x hx => by
      simpa using hgM x hx) π ρ hsup (fun x hx => by simpa using hgπ x hx)
      (fun x hx => by simpa using hgρ x hx) hhneg hhdim hhfix hW₁ hW₂ hne hε₁ hε₂ hg₁ hg₂ hh₁ hh₂
    intro y hy
    simpa using eq_self_of_perp_plane h2 hgO hg2 π hneg hy
  · let g' : V ≃ₗ[K] V := g.trans (LinearEquiv.neg K)
    have hg'x : ∀ x, g' x = -(g x) := fun x => rfl
    have hg'2 : g' * g' = 1 := by
      refine LinearEquiv.ext fun x => ?_
      have := LinearEquiv.congr_fun hg2 x
      simp only [LinearEquiv.mul_apply, hg'x, map_neg, neg_neg] at this ⊢
      simpa using this
    have hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
      rw [hg'x, QuadraticMap.map_neg]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO x
    have hneg := negSpace_eq_plane_b4 (g := g') h2 hd hg'2 hWM hWMnd hMJ (fun x hx => by
      rw [hg'x, hgM x hx]; simp) π ρ hsup (fun x hx => by
        rw [hg'x, hgπ x hx]; simp) (fun x hx => by
        rw [hg'x, hgρ x hx]; simp) hhneg hhdim hhfix hW₁ hW₂ hne (ε₁ := -ε₁) (ε₂ := -ε₂)
      (by rcases hε₁ with rfl | rfl <;> simp) (by rcases hε₂ with rfl | rfl <;> simp)
      (fun x hx => by rw [hg'x, hg₁ x hx]; simp) (fun x hx => by rw [hg'x, hg₂ x hx]; simp) hh₁ hh₂
    intro y hy
    have := eq_self_of_perp_plane h2 hg'O hg'2 π hneg hy
    rw [hg'x] at this
    have h3 : g y = -y := by
      have := congrArg Neg.neg this
      simpa using this
    rw [h3]
    simp

end Class

end CFSG.ClassicalInvolution.RouteD.TWE.B4
