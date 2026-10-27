module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Transport
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace Frame

variable {F F' : Frame Q}

theorem span_eq_of_La_neg_one_eq (h2 : (2 : K) ≠ 0) (h : F'.La (-1) = F.La (-1)) :
    F'.span = F.span := by
  ext x
  rw [mem_span_iff_inv F' h2, mem_span_iff_inv F h2, h]

theorem mem_perp_iff_forall_incl (F : Frame Q) {x : V} :
    x ∈ F.perp ↔ ∀ Y, polar Q x (F.incl Y) = 0 := by
  rw [mem_perp_iff]
  constructor
  · intro h Y
    rw [polar_incl_right, h]
    simp
  · intro h
    have h1 := h !![1, 0; 0, 0]
    have h2 := h !![0, 0; 0, 1]
    have h3 := h !![0, 1; 0, 0]
    have h4 := h !![0, 0; 1, 0]
    rw [polar_incl_right] at h1 h2 h3 h4
    simp at h1 h2 h3 h4
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem perp_eq_of_span_eq (h : F'.span = F.span) : F'.perp = F.perp := by
  ext x
  rw [mem_perp_iff_forall_incl, mem_perp_iff_forall_incl]
  constructor
  · intro hx Y
    have : F.incl Y ∈ F'.span := by rw [h]; exact ⟨Y, rfl⟩
    obtain ⟨Z, hZ⟩ := this
    rw [← hZ]
    exact hx Z
  · intro hx Y
    have : F'.incl Y ∈ F.span := by rw [← h]; exact ⟨Y, rfl⟩
    obtain ⟨Z, hZ⟩ := this
    rw [← hZ]
    exact hx Z

@[expose] def comparison (F F' : Frame Q) : Module.End K (Matrix (Fin 2) (Fin 2) K) :=
  F.coords ∘ₗ F'.incl

theorem comparison_apply (Y : Matrix (Fin 2) (Fin 2) K) :
    comparison F F' Y = F.coords (F'.incl Y) :=
  rfl

theorem incl_comparison (h : F'.span = F.span) (Y : Matrix (Fin 2) (Fin 2) K) :
    F.incl (comparison F F' Y) = F'.incl Y :=
  ((mem_span_iff F).mp (h ▸ ⟨Y, rfl⟩ : F'.incl Y ∈ F.span)).symm

theorem comparison_comparison (h : F'.span = F.span) (Z : Matrix (Fin 2) (Fin 2) K) :
    comparison F F' (comparison F' F Z) = Z := by
  rw [comparison_apply, incl_comparison h.symm, ← comparison_apply]
  exact F.coords_incl Z

theorem coords_eq_comparison (h : F'.span = F.span) (x : V) :
    F'.coords x = comparison F' F (F.coords x) := by
  have hr : x - F.incl (F.coords x) ∈ F'.perp := by
    rw [perp_eq_of_span_eq h, mem_perp_iff, map_sub, coords_incl, sub_self]
  rw [mem_perp_iff, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem La_eq_embLin_comparison (h : F'.span = F.span) (A : SL(2, K)) (x : V) :
    F'.La A x = F.embLin (comparison F F' ∘ₗ rhoL A ∘ₗ comparison F' F) x := by
  rw [La_apply, embLin_apply, coords_eq_comparison h x]
  have h1 := incl_comparison h (((A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
    comparison F' F (F.coords x) - comparison F' F (F.coords x))
  rw [← h1, map_sub, comparison_comparison h]
  rfl

@[expose] def comparisonEquiv (h : F'.span = F.span) :
    Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearEquiv.ofLinearMap (comparison F F') (comparison F' F)
    (LinearMap.ext fun Z => comparison_comparison h Z)
    (LinearMap.ext fun Z => comparison_comparison h.symm Z)

theorem comparisonEquiv_mem_orthogonalGroup (h : F'.span = F.span) :
    comparisonEquiv h ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun Y => ?_
  rw [detQ_apply, detQ_apply, ← F.Q_incl, ← F'.Q_incl]
  change Q (F.incl (comparison F F' Y)) = _
  rw [incl_comparison h]

theorem La_eq_embGrp_comparison (h : F'.span = F.span) (A : SL(2, K)) :
    F'.La A = F.embGrp (comparisonEquiv h * lmulEquiv A * (comparisonEquiv h)⁻¹) := by
  refine LinearEquiv.ext fun x => ?_
  rw [La_eq_embLin_comparison h, embGrp_apply]
  rfl

theorem La_range_eq_map_conjSubgroup (h : F'.span = F.span) :
    F'.La.range = (conjSubgroup (comparisonEquiv h) leftGrp).map F.embGrp := by
  ext y
  rw [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨comparisonEquiv h * lmulEquiv A * (comparisonEquiv h)⁻¹, ?_,
      (La_eq_embGrp_comparison h A).symm⟩
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using lmulEquiv_mem_leftGrp A
  · rintro ⟨x, hx, rfl⟩
    rw [mem_conjSubgroup] at hx
    obtain ⟨A, hA⟩ := hx
    refine ⟨A, ?_⟩
    rw [La_eq_embGrp_comparison h]
    congr 1
    have : (comparisonEquiv h)⁻¹ * x * comparisonEquiv h = lmulEquiv A :=
      LinearEquiv.ext hA
    rw [← this]
    group

theorem La_range_eq_or_eq_swap (h2 : (2 : K) ≠ 0) (h : F'.La (-1) = F.La (-1)) :
    F'.La.range = F.La.range ∨ F'.La.range = F.swap.La.range := by
  have hs := span_eq_of_La_neg_one_eq h2 h
  rw [La_range_eq_map_conjSubgroup hs]
  rcases isometry_trichotomy h2 (comparisonEquiv_mem_orthogonalGroup hs) with
    ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  · left
    rw [h1, La_range_eq_map (F := F)]
  · right
    rw [h1, swap_La_range_eq_map (F := F)]

theorem La_range_ne_swap_La_range (F : Frame Q) : F.La.range ≠ F.swap.La.range := by
  intro h
  rw [La_range_eq_map, swap_La_range_eq_map] at h
  have hinj : Function.Injective F.embGrp := F.embGrp_injective
  exact leftGrp_ne_rightGrp (Subgroup.map_injective hinj h)

theorem La_mem_swap_range_iff (F : Frame Q) (A : SL(2, K)) :
    F.La A ∈ F.swap.La.range ↔ A = 1 ∨ A = -1 := by
  constructor
  · rintro ⟨B, hB⟩
    rw [swap_La_eq_embGrp, La_eq_embGrp] at hB
    have h1 := F.embGrp_injective hB
    have h2 : ∀ X : Matrix (Fin 2) (Fin 2) K,
        X * ((sigmaSL B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
          (A : Matrix (Fin 2) (Fin 2) K) * X := fun X => LinearEquiv.congr_fun h1 X
    have h3 : ((sigmaSL B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) := by simpa using h2 1
    rw [h3] at h2
    have hc : A ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact h2 g
    exact (CFSG.ClassicalInvolution.mem_center_sl2_iff A).mp hc
  · rintro (rfl | rfl)
    · rw [map_one]
      exact Subgroup.one_mem _
    · rw [← La_swap_neg_one F]
      exact ⟨-1, rfl⟩

@[expose] noncomputable def prodHom (F : Frame Q) : SL(2, K) × SL(2, K) →* (V ≃ₗ[K] V) :=
  F.La.noncommCoprod F.swap.La (fun A B => F.La_comm_La_swap A B)

theorem prodHom_apply (F : Frame Q) (A B : SL(2, K)) : F.prodHom (A, B) = F.La A * F.swap.La B :=
  rfl

theorem prodHom_eq_one_iff (F : Frame Q) (A B : SL(2, K)) :
    F.prodHom (A, B) = 1 ↔ (A = 1 ∧ B = 1) ∨ (A = -1 ∧ B = -1) := by
  constructor
  · intro h
    rw [prodHom_apply] at h
    have h1 : F.La A = F.swap.La B⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left h
    have h2 : F.La A ∈ F.swap.La.range := ⟨B⁻¹, h1.symm⟩
    rcases (La_mem_swap_range_iff F A).mp h2 with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      rw [map_one, one_mul] at h
      exact F.swap.La_injective (h.trans F.swap.La.map_one.symm)
    · right
      refine ⟨rfl, ?_⟩
      rw [← La_swap_neg_one F, ← map_mul] at h
      have h3 : (-1 : SL(2, K)) * B = 1 := F.swap.La_injective (h.trans F.swap.La.map_one.symm)
      rw [neg_one_mul, neg_eq_iff_eq_neg] at h3
      exact h3
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [prodHom_apply]
    · rw [prodHom_apply, ← La_swap_neg_one F, ← map_mul, neg_mul_neg, one_mul, map_one]

theorem range_prodHom (F : Frame Q) : F.prodHom.range = F.La.range ⊔ F.swap.La.range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨A, B⟩, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨A, rfl⟩) (Subgroup.mem_sup_right ⟨B, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      exact ⟨(A, 1), by simp [prodHom_apply]⟩
    · rintro _ ⟨B, rfl⟩
      exact ⟨(1, B), by simp [prodHom_apply]⟩

end Frame

@[expose] def IsFundamental (Q : QuadraticForm K V) (L : Subgroup (V ≃ₗ[K] V))
    (i : V ≃ₗ[K] V) : Prop :=
  ∃ F : Frame Q, L = F.La.range ∧ i = F.La (-1)

@[expose] def centralizerΩ (Q : QuadraticForm K V) (i : V ≃ₗ[K] V) : Subgroup (V ≃ₗ[K] V) :=
  elementaryGroup Q ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[K] V))

namespace IsFundamental

variable {L L' : Subgroup (V ≃ₗ[K] V)} {i i' : V ≃ₗ[K] V}

theorem of_frame (F : Frame Q) : IsFundamental Q F.La.range (F.La (-1)) :=
  ⟨F, rfl, rfl⟩

theorem conj {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h : IsFundamental Q L i) :
    IsFundamental Q (L.map (MulAut.conj g).toMonoidHom) (g * i * g⁻¹) := by
  obtain ⟨F, rfl, rfl⟩ := h
  refine ⟨F.map hg, ?_, (Frame.map_La F hg (-1)).symm⟩
  rw [← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (MonoidHom.ext fun A => (Frame.map_La F hg A).symm)

theorem of_frame_swap (F : Frame Q) : IsFundamental Q F.swap.La.range (F.La (-1)) :=
  ⟨F.swap, rfl, (Frame.La_swap_neg_one F).symm⟩

theorem nonempty_mulEquiv (h : IsFundamental Q L i) : Nonempty (SL(2, K) ≃* L) := by
  obtain ⟨F, rfl, -⟩ := h
  exact ⟨MonoidHom.ofInjective F.La_injective⟩

theorem mem (h : IsFundamental Q L i) : i ∈ L := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact ⟨-1, rfl⟩

theorem mul_self (h : IsFundamental Q L i) : i * i = 1 := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact F.La_neg_one_mul_self

theorem le_centralizer (h : IsFundamental Q L i) :
    L ≤ Subgroup.centralizer ({i} : Set (V ≃ₗ[K] V)) := by
  obtain ⟨F, rfl, rfl⟩ := h
  rintro _ ⟨A, rfl⟩ _ hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact F.La_neg_one_comm A

theorem le_elementaryGroup (h : IsFundamental Q L i) : L ≤ elementaryGroup Q := by
  obtain ⟨F, rfl, -⟩ := h
  rintro _ ⟨A, rfl⟩
  exact F.La_mem_elementaryGroup A

theorem le_centralizerΩ (h : IsFundamental Q L i) : L ≤ centralizerΩ Q i :=
  le_inf h.le_elementaryGroup h.le_centralizer

variable [Finite K]

theorem two_ne_zero_of_odd (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 :=
  CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd

theorem ne_one (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) : i ≠ 1 := by
  obtain ⟨F, rfl, rfl⟩ := h
  intro h1
  exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
    (F.La_injective (h1.trans F.La.map_one.symm))

theorem orderOf_eq_two (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) : orderOf i = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.mul_self) (h.ne_one hodd)

theorem eq_of_orderOf_eq_two (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) {x : V ≃ₗ[K] V}
    (hx : x ∈ L) (hx2 : orderOf x = 2) : x = i := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨A, rfl⟩ := hx
  have hA : A = -1 := by
    refine (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd A).mp ?_
    rw [← orderOf_injective F.La F.La_injective A]
    exact hx2
  rw [hA]

theorem involution_unique (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i)
    (h' : IsFundamental Q L i') : i = i' :=
  (eq_of_orderOf_eq_two hodd h h'.mem (h'.orderOf_eq_two hodd)).symm

theorem exists_twin (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) :
    ∃ L' : Subgroup (V ≃ₗ[K] V), IsFundamental Q L' i ∧ L' ≠ L ∧
      (∀ x ∈ L, ∀ y ∈ L', x * y = y * x) ∧
      ∀ L'', IsFundamental Q L'' i → L'' = L ∨ L'' = L' := by
  have h2 := two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  refine ⟨F.swap.La.range, of_frame_swap F, (Frame.La_range_ne_swap_La_range F).symm, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact F.La_comm_La_swap A B
  · rintro L'' ⟨F'', rfl, hF''⟩
    exact Frame.La_range_eq_or_eq_swap h2 hF''.symm

theorem ncard_eq_two (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) :
    {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' i}.ncard = 2 := by
  obtain ⟨L', hL', hne, -, huniq⟩ := exists_twin hodd h
  have : {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' i} = {L, L'} := by
    ext L''
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨huniq L'', fun h'' => h''.elim (fun e => e ▸ h) (fun e => e ▸ hL')⟩
  rw [this, Set.ncard_pair hne.symm]

end IsFundamental

section Centralizer

variable (F : Frame Q)

theorem commute_of_mem_centralizerΩ {g : V ≃ₗ[K] V} (hg : g ∈ centralizerΩ Q (F.La (-1))) :
    g * F.La (-1) = F.La (-1) * g :=
  ((Subgroup.mem_centralizer_iff.mp hg.2) _ (Set.mem_singleton _)).symm

variable {F}

noncomputable def chi (h2 : (2 : K) ≠ 0) (F : Frame Q) :
    centralizerΩ Q (F.La (-1)) →* Kˣ where
  toFun g := LinearEquiv.det (Frame.transportEquiv h2 (commute_of_mem_centralizerΩ F g.2))
  map_one' := by
    have : Frame.transportEquiv h2 (commute_of_mem_centralizerΩ F
        (1 : centralizerΩ Q (F.La (-1))).2) = 1 :=
      LinearEquiv.ext fun Y => by
        simp [Frame.transportEquiv_apply, Frame.transport_apply, Frame.coords_incl]
    rw [this, map_one]
  map_mul' g h := by
    have : Frame.transportEquiv h2 (commute_of_mem_centralizerΩ F (g * h).2) =
        Frame.transportEquiv h2 (commute_of_mem_centralizerΩ F g.2) *
          Frame.transportEquiv h2 (commute_of_mem_centralizerΩ F h.2) :=
      LinearEquiv.ext fun Y => by
        have := LinearMap.congr_fun (Frame.transport_mul h2 (commute_of_mem_centralizerΩ F h.2)
          (g := g.1)) Y
        simpa [Frame.transportEquiv_apply] using this
    show LinearEquiv.det (Frame.transportEquiv h2 (commute_of_mem_centralizerΩ F (g * h).2)) = _
    rw [this, map_mul]

theorem conjSubgroup_eq_of_chi_eq_one (h2 : (2 : K) ≠ 0) (g : centralizerΩ Q (F.La (-1)))
    (hg : chi h2 F g = 1) : conjSubgroup g.1 F.La.range = F.La.range := by
  have hgO : g.1 ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q g.2.1
  rcases Frame.conjSubgroup_La_range h2 hgO (commute_of_mem_centralizerΩ F g.2) with
    ⟨-, h, -⟩ | ⟨hd, -, -⟩
  · exact h
  · exfalso
    have : chi h2 F g = -1 := hd
    rw [this] at hg
    have h' := congrArg (fun u : Kˣ => (u : K)) hg
    exact neg_one_ne_one h2 (by simpa using h')

theorem conjSubgroup_eq_of_mem_derivedSeries_two (h2 : (2 : K) ≠ 0)
    (g : centralizerΩ Q (F.La (-1))) (hg : g ∈ derivedSeries (centralizerΩ Q (F.La (-1))) 2) :
    conjSubgroup g.1 F.La.range = F.La.range := by
  refine conjSubgroup_eq_of_chi_eq_one h2 g ?_
  have h1 : derivedSeries (centralizerΩ Q (F.La (-1))) 2 ≤ (chi h2 F).ker :=
    (derivedSeries_antitone (G := centralizerΩ Q (F.La (-1))) (by norm_num : 1 ≤ 2)).trans
      (Abelianization.commutator_subset_ker _)
  exact MonoidHom.mem_ker.mp (h1 hg)

end Centralizer

namespace IsFundamental

variable {L L' : Subgroup (V ≃ₗ[K] V)} {i i' : V ≃ₗ[K] V} [Finite K]

theorem commutator_eq (h4 : 4 ≤ Nat.card K) (h : IsFundamental Q L i) : ⁅L, L⁆ = L := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  have hperf : Group.IsPerfect L :=
    CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 e.symm
  exact Subgroup.isPerfect_iff.mp hperf

theorem le_derivedSeries_two (h4 : 4 ≤ Nat.card K) (h : IsFundamental Q L i) :
    L.subgroupOf (centralizerΩ Q i) ≤ derivedSeries (centralizerΩ Q i) 2 := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  have hLC := h.le_centralizerΩ
  have hperf : Group.IsPerfect (L.subgroupOf (centralizerΩ Q i)) :=
    CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4
      ((Subgroup.subgroupOfEquivOfLe hLC).trans e.symm)
  have h1 := Subgroup.isPerfect_iff.mp hperf
  have h2 : L.subgroupOf (centralizerΩ Q i) ≤ derivedSeries (centralizerΩ Q i) 1 := by
    rw [← h1]
    exact Subgroup.commutator_mono le_top le_top
  rw [← h1]
  exact Subgroup.commutator_mono h2 h2

theorem derivedSeries_two_le_normalizer (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) :
    derivedSeries (centralizerΩ Q i) 2 ≤
      Subgroup.normalizer ((L.subgroupOf (centralizerΩ Q i) : Subgroup _) : Set _) := by
  have h2 := two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  intro g hg
  have hn := conjSubgroup_eq_of_mem_derivedSeries_two h2 g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  have := Set.ext_iff.mp (congrArg (fun N : Subgroup (V ≃ₗ[K] V) => (N : Set _)) hn) x.1
  simpa [mem_conjSubgroup, Subgroup.mem_subgroupOf] using this.symm

theorem inf_twin (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) {L' : Subgroup (V ≃ₗ[K] V)}
    (hL' : IsFundamental Q L' i) (hne : L' ≠ L) : L ⊓ L' = Subgroup.zpowers i := by
  have h2 := two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  have hL'' : L' = F.swap.La.range := by
    obtain ⟨F', rfl, hF'⟩ := hL'
    exact (Frame.La_range_eq_or_eq_swap h2 hF'.symm).resolve_left hne
  subst hL''
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨A, rfl⟩, hx⟩
    rcases (Frame.La_mem_swap_range_iff F A).mp hx with rfl | rfl
    · rw [map_one]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨-1, rfl⟩, ⟨-1, F.La_swap_neg_one⟩⟩

theorem isSubnormal (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) (h : IsFundamental Q L i) :
    (L.subgroupOf (centralizerΩ Q i)).IsSubnormal := by
  refine Subgroup.IsSubnormal.step _ (derivedSeries (centralizerΩ Q i) 2)
    (h.le_derivedSeries_two h4) (Subgroup.Normal.isSubnormal (derivedSeries_normal _ 2)) ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (h.le_derivedSeries_two h4)]
  exact h.derivedSeries_two_le_normalizer hodd

end IsFundamental

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
