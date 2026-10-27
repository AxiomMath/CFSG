module

public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSlice

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (isSubnormal_subgroupOf_of_normalizes)

variable {S X : Type} [Group S] [Group X]

open scoped IsMulCommutative in
theorem commute_of_comm_mem_center {M : Subgroup S} (hM : Group.IsPerfect M) {g : S}
    (hg : ∀ m ∈ M, m * g * m⁻¹ * g⁻¹ ∈ center S) : ∀ m ∈ M, g * m = m * g := by
  let φ : M →* center S :=
    { toFun := fun m => ⟨m * g * (m : S)⁻¹ * g⁻¹, hg m m.2⟩
      map_one' := by
        apply Subtype.ext
        change (1 : S) * g * (1 : S)⁻¹ * g⁻¹ = 1
        group
      map_mul' := fun m m' => by
        apply Subtype.ext
        change ((m : S) * m') * g * ((m : S) * m')⁻¹ * g⁻¹ =
          ((m : S) * g * (m : S)⁻¹ * g⁻¹) * ((m' : S) * g * (m' : S)⁻¹ * g⁻¹)
        have h1 := mem_center_iff.1 (hg m' m'.2) (m : S)
        have h2 := mem_center_iff.1 (hg m' m'.2) ((m : S) * g * (m : S)⁻¹ * g⁻¹)
        calc ((m : S) * m') * g * ((m : S) * m')⁻¹ * g⁻¹ =
            (m : S) * ((m' : S) * g * (m' : S)⁻¹ * g⁻¹) * g * (m : S)⁻¹ * g⁻¹ := by group
          _ = ((m' : S) * g * (m' : S)⁻¹ * g⁻¹) * (m : S) * g * (m : S)⁻¹ * g⁻¹ := by
            rw [h1]
          _ = ((m' : S) * g * (m' : S)⁻¹ * g⁻¹) * ((m : S) * g * (m : S)⁻¹ * g⁻¹) := by
            group
          _ = _ := h2.symm }
  have hker : commutator M ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro m hm
  have h1 : φ ⟨m, hm⟩ = 1 := by
    rw [← MonoidHom.mem_ker]
    apply hker
    rw [hM.commutator_eq_top]
    exact mem_top _
  have h2 : m * g * m⁻¹ * g⁻¹ = 1 := congrArg Subtype.val h1
  calc g * m = (m * g * m⁻¹ * g⁻¹)⁻¹ * (m * g) := by group
    _ = m * g := by rw [h2, inv_one, one_mul]

theorem conj_mem_centralizer_of_central {a h x : S} (hc : h * a * h⁻¹ * a⁻¹ ∈ center S)
    (hx : x ∈ centralizer ({a} : Set S)) : h * x * h⁻¹ ∈ centralizer ({a} : Set S) := by
  rw [mem_centralizer_singleton_iff] at hx ⊢
  have h1 : Commute (h * x * h⁻¹) (h * a * h⁻¹) := Commute.conj hx h
  have h2 : Commute (h * x * h⁻¹) (h * a * h⁻¹ * a⁻¹) := mem_center_iff.1 hc _
  have h3 := h2.inv_right.mul_right h1
  rw [show (h * a * h⁻¹ * a⁻¹)⁻¹ * (h * a * h⁻¹) = a by group] at h3
  exact h3

theorem lift_commute_of_subnormal [Finite X] (π : S →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → s ∈ center S) (a : S) {M N : Subgroup S} (hMq : IsQuasisimple M)
    (hMN : M ≤ N) (hMn : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hNC : N ≤ centralizer ({a} : Set S))
    (hNn : ∀ x ∈ centralizer ({a} : Set S), ∀ n ∈ N, x * n * x⁻¹ ∈ N) {g : X}
    (hg : ∀ K : Subgroup (centralizer ({π a} : Set X)), IsComponent K → Even (Nat.card K) →
      ∀ k ∈ K, (k : X) * g = g * k)
    {g' : S} (hg' : π g' = g) : ∀ m ∈ M, g' * m = m * g' := by
  have hCH : (centralizer ({a} : Set S)).map π ≤ centralizer ({π a} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  have hMH : M.map π ≤ centralizer ({π a} : Set X) :=
    ((map_mono hMN).trans (map_mono hNC)).trans hCH
  have hC' : (((centralizer ({a} : Set S)).map π).subgroupOf
      (centralizer ({π a} : Set X))).IsSubnormal := by
    refine Normal.isSubnormal ⟨fun y hy h => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨h', hh'⟩ := hπ (h : X)
    have hh : (h : X) * π a = π a * h := mem_centralizer_singleton_iff.1 h.2
    have hc : h' * a * h'⁻¹ * a⁻¹ ∈ center S := hker _ (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hh', hh]
      group)
    refine ⟨h' * x * h'⁻¹, conj_mem_centralizer_of_central hc hx, ?_⟩
    rw [map_mul, map_mul, map_inv, hh', hxy]
    rfl
  have hN' : ((N.map π).subgroupOf (centralizer ({π a} : Set X))).IsSubnormal := by
    refine isSubnormal_subgroupOf_of_normalizes (map_mono hNC) ?_ hC'
    rintro _ ⟨x, hx, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨x * n * x⁻¹, hNn x hx n hn, by simp only [map_mul, map_inv]⟩
  have hM' : ((M.map π).subgroupOf (centralizer ({π a} : Set X))).IsSubnormal := by
    refine isSubnormal_subgroupOf_of_normalizes (map_mono hMN) ?_ hN'
    rintro _ ⟨x, hx, rfl⟩ _ ⟨m, hm, rfl⟩
    exact ⟨x * m * x⁻¹, hMn x hx m hm, by simp only [map_mul, map_inv]⟩
  have hne : ∃ m : M, π.subgroupMap M m ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, u, v, huv⟩ := hMq
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    apply huv
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hu : π u = 1 := congrArg Subtype.val (hcon u)
    exact mem_center_iff.1 (hker _ hu) (v : S) |>.symm
  have hq : IsQuasisimple ((M.map π).subgroupOf (centralizer ({π a} : Set X))) :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMH).symm
      (LieType.CurtisTits.isQuasisimple_of_surjective hMq (π.subgroupMap_surjective M) hne)
  have hev := RankThree.OddKernel.even_card_of_isQuasisimple hq
  have hcomm : ∀ m ∈ M, m * g' * m⁻¹ * g'⁻¹ ∈ center S := by
    intro m hm
    refine hker _ ?_
    have e := hg _ ⟨hq, hM'⟩ hev ⟨π m, hMH ⟨m, hm, rfl⟩⟩ (mem_subgroupOf.2 ⟨m, hm, rfl⟩)
    change π m * g = g * π m at e
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg', e]
    group
  exact commute_of_comm_mem_center hMq.1 hcomm

theorem card_le_of_forall_lift_mem {β : Type*} (π : S →* X) {f : S → β}
    (hf : Function.Injective f) {P : Subgroup X} (T : Finset β)
    (hT : ∀ g ∈ P, ∃ s, π s = g ∧ f s ∈ T) : Nat.card P ≤ T.card := by
  classical
  have hsub : (P : Set X) ⊆ ((T.image fun b => π (Function.invFun f b) : Finset X) : Set X) := by
    intro g hg
    obtain ⟨s, rfl, hs⟩ := hT g hg
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨f s, hs, ?_⟩)
    rw [Function.leftInverse_invFun hf s]
  calc Nat.card P = (P : Set X).ncard := Nat.card_coe_set_eq _
    _ ≤ _ := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = _ := Set.ncard_coe_finset _
    _ ≤ T.card := Finset.card_image_le

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
