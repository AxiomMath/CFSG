module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarFrame
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapChain

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter CFSG.CGT.PushingUpLit.BHSSym

section Hom

variable {G : Type*} [Group G] {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem exists_completion_of_hom (φ : Perm α →* G) (hφ : Function.Injective φ) {k : ℕ}
    (hk : 2 ≤ k) {t : ℕ → G} (hts : ∀ i < k, ∃ τ : Perm α, τ.IsSwap ∧ φ τ = t i)
    (hcomm : ∀ i j, i + 2 ≤ j → j < k → t i * t j = t j * t i)
    (hne : ∀ i j, i < k → j < k → i ≠ j → t i ≠ t j)
    {c : G} (hcs : ∃ γ : Perm α, γ.IsSwap ∧ φ γ = c) (hcne : ∀ i < k, c ≠ t i)
    (hccomm : ∀ i < k, c * t i = t i * c) :
    ∃ δ : Perm α, δ.IsSwap ∧ (t (k - 1) * φ δ) ^ 3 = 1 ∧ (φ δ * c) ^ 3 = 1 ∧
      (∀ i, i + 2 ≤ k → φ δ * t i = t i * φ δ) ∧ (∀ i < k, φ δ ≠ t i) ∧ φ δ ≠ c := by
  classical
  have hpre : ∀ i, ∃ τ : Perm α, i < k → τ.IsSwap ∧ φ τ = t i := by
    intro i
    by_cases hi : i < k
    · obtain ⟨τ, hτ, h⟩ := hts i hi
      exact ⟨τ, fun _ => ⟨hτ, h⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose τ hτ using hpre
  obtain ⟨γ, hγ, hγc⟩ := hcs
  obtain ⟨δ, hδ, h1, h2, h3, h4, h5⟩ := exists_swap_completion (α := α) hk (t := τ)
    (fun i hi => (hτ i hi).1)
    (fun i j hij hj => hφ (by
      rw [map_mul, map_mul, (hτ i (by omega)).2, (hτ j hj).2]
      exact hcomm i j hij hj))
    (fun i j hi hj hij h => hne i j hi hj hij (by
      rw [← (hτ i hi).2, ← (hτ j hj).2, h]))
    hγ (fun i hi h => hcne i hi (by rw [← hγc, ← (hτ i hi).2, h]))
    (fun i hi => hφ (by
      rw [map_mul, map_mul, hγc, (hτ i hi).2]
      exact hccomm i hi))
  refine ⟨δ, hδ, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg φ h1
    rwa [map_pow, map_mul, map_one, (hτ (k - 1) (by omega)).2] at this
  · have := congrArg φ h2
    rwa [map_pow, map_mul, map_one, hγc] at this
  · intro i hi
    have := congrArg φ (h3 i hi)
    rwa [map_mul, map_mul, (hτ i (by omega)).2] at this
  · intro i hi h
    exact h4 i hi (hφ (by rw [h, (hτ i hi).2]))
  · intro h
    exact h5 (hφ (by rw [h, hγc]))

omit [Fintype α] in
theorem commute_of_chain_three_of_hom (φ : Perm α →* G) (hφ : Function.Injective φ)
    {u v w s : G} (hu : ∃ u' : Perm α, u'.IsSwap ∧ φ u' = u)
    (hv : ∃ v' : Perm α, v'.IsSwap ∧ φ v' = v) (hw : ∃ w' : Perm α, w'.IsSwap ∧ φ w' = w)
    (hs : ∃ s' : Perm α, s'.IsSwap ∧ φ s' = s) (huv : u ≠ v)
    (hvw : v ≠ w) (huw : u ≠ w) (h3uv : (u * v) ^ 3 = 1) (h3vw : (v * w) ^ 3 = 1)
    (hcuw : u * w = w * u) (hsu : s * u = u * s) (hsw : s * w = w * s) (hsune : s ≠ u)
    (hswne : s ≠ w) : s * v = v * s := by
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨w', hw', rfl⟩ := hw
  obtain ⟨s', hs', rfl⟩ := hs
  have := AltStdSec.commute_of_chain_three hu' hv' hw' hs'
    (fun h => huv (by rw [h])) (fun h => hvw (by rw [h])) (fun h => huw (by rw [h]))
    (hφ (by rw [map_pow, map_mul, map_one]; exact h3uv))
    (hφ (by rw [map_pow, map_mul, map_one]; exact h3vw))
    (hφ (by rw [map_mul, map_mul]; exact hcuw))
    (hφ (by rw [map_mul, map_mul]; exact hsu))
    (hφ (by rw [map_mul, map_mul]; exact hsw))
    (fun h => hsune (by rw [h])) (fun h => hswne (by rw [h]))
  have := congrArg φ this
  rwa [map_mul, map_mul] at this

end Hom

namespace NearData

variable {G : Type*} [Group G] {z : G} {n : ℕ}

@[expose] def hom (D : NearData z n) : Perm (Fin n) →* G := D.S.subtype.comp D.ι.toMonoidHom

theorem hom_injective (D : NearData z n) : Function.Injective D.hom :=
  Subtype.coe_injective.comp D.ι.injective

theorem exists_swap_of_isSwap (hn : 11 ≤ n) (D : NearData z n) {a : G} (ha : a ∈ Partners z)
    (hs : (D.π ⟨a, mem_centralizer_of_partner ha⟩).IsSwap) :
    ∃ τ : Perm (Fin n), τ.IsSwap ∧ D.hom τ = a :=
  ⟨_, hs, (D.near _ ha (isNearPerm_of_isSwap hn hs)).2.symm⟩

end NearData

section Chain

variable {G : Type*} [Group G] {z : G} {m : ℕ}

@[expose] def nxs (D : NearData z (m + 1)) (i : ℕ) : G := (D.ι (adjSwap m i) : G)

theorem nxs_mem (D : NearData z (m + 1)) (i : ℕ) : nxs D i ∈ D.S := (D.ι _).2

theorem nxs_partner (D : NearData z (m + 1)) {i : ℕ} (hi : i < m) : nxs D i ∈ Partners z :=
  D.swap_mem _ (adjSwap_isSwap hi)

theorem nxs_π (D : NearData z (m + 1)) {i : ℕ} (hi : i < m) :
    (D.π ⟨nxs D i, NearData.mem_centralizer_of_partner (nxs_partner D hi)⟩).IsSwap := by
  have : D.π ⟨nxs D i, NearData.mem_centralizer_of_partner (nxs_partner D hi)⟩ = adjSwap m i :=
    D.π_ι _
  rw [this]
  exact adjSwap_isSwap hi

theorem isCoxeterA_nxs (D : NearData z (m + 1)) : IsCoxeterA m (nxs D) :=
  IsCoxeterA.map D.hom (isCoxeterA_adjSwap m)

theorem nxs_sq (D : NearData z (m + 1)) {i : ℕ} (hi : i < m) : nxs D i * nxs D i = 1 :=
  (isCoxeterA_nxs D).sq i hi

theorem nxs_comm (D : NearData z (m + 1)) {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < m) :
    nxs D i * nxs D j = nxs D j * nxs D i :=
  (isCoxeterA_nxs D).comm i j hij hj

theorem nxs_ne (D : NearData z (m + 1)) {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    nxs D i ≠ nxs D j := fun h => hij (adjSwap_inj hi hj (D.hom_injective h))

theorem nxs_comm_z (D : NearData z (m + 1)) (i : ℕ) : nxs D i * z = z * nxs D i :=
  D.ι_comm _

theorem nxs_ne_z (D : NearData z (m + 1)) (i : ℕ) : nxs D i ≠ z := by
  intro h
  have := nxs_mem D i
  rw [h] at this
  exact D.z_notMem this

theorem nxs_swap_of (hm : 10 ≤ m) (D : NearData z (m + 1)) {i j : ℕ} (hi : i < m) (hj : j < m)
    (hij : i + 2 ≤ j ∨ j + 2 ≤ i) (Di : NearData (nxs D i) (m + 1)) :
    ∃ τ : Perm (Fin (m + 1)), τ.IsSwap ∧ Di.hom τ = nxs D j := by
  have hc : nxs D j * nxs D i = nxs D i * nxs D j := by
    rcases hij with h | h
    · exact (nxs_comm D h hj).symm
    · exact nxs_comm D h hi
  have hne : nxs D j ≠ nxs D i := nxs_ne D hj hi (by omega)
  have hp : nxs D j ∈ Partners (nxs D i) :=
    Partners.of_isConj (nxs_partner D hi) (nxs_partner D hj).1 hne hc
  have hs := NearData.isSwap_of_swap_partners (by omega) D Di (nxs_partner D hi)
    (nxs_partner D hj) (nxs_π D hi) (nxs_π D hj) hc hne
  exact NearData.exists_swap_of_isSwap (by omega) Di hp hs

theorem z_swap_of (hm : 10 ≤ m) (D : NearData z (m + 1)) {i : ℕ} (hi : i < m)
    (Di : NearData (nxs D i) (m + 1)) :
    ∃ τ : Perm (Fin (m + 1)), τ.IsSwap ∧ Di.hom τ = z := by
  have hp : z ∈ Partners (nxs D i) := Partners.symm (nxs_partner D hi)
  have hs := NearData.isSwap_symm (by omega) D Di (nxs_partner D hi) (nxs_π D hi)
  exact NearData.exists_swap_of_isSwap (by omega) Di hp hs

theorem exists_en_near (hm : 10 ≤ m) (D : NearData z (m + 1)) :
    ∃ en : G, IsConj z en ∧ en * en = 1 ∧ en ≠ z ∧ (nxs D (m - 1) * en) ^ 3 = 1 ∧
      (en * z) ^ 3 = 1 ∧ (∀ i, i + 2 ≤ m → nxs D i * en = en * nxs D i) ∧
      (∀ i, 2 ≤ i → i < m → en ≠ nxs D i) := by
  obtain ⟨D₀⟩ := D.nonempty_of_isConj (nxs_partner D (by omega : 0 < m)).1
  have hp : ∀ i, 2 ≤ i → i < m → nxs D i ∈ Partners (nxs D 0) := fun i hi2 him =>
    Partners.of_isConj (nxs_partner D (by omega : 0 < m)) (nxs_partner D him).1
      (nxs_ne D him (by omega) (by omega))
      (nxs_comm D (by omega) him).symm
  have hpz : z ∈ Partners (nxs D 0) := Partners.symm (nxs_partner D (by omega : 0 < m))
  obtain ⟨δ, hδ, h1, h2, h3, h4, h5⟩ := exists_completion_of_hom D₀.hom D₀.hom_injective
    (k := m - 2) (by omega) (t := fun j => nxs D (j + 2))
    (fun j hj => nxs_swap_of hm D (by omega : 0 < m) (by omega : j + 2 < m)
      (Or.inl (by omega)) D₀)
    (fun i j hij hj => nxs_comm D (by omega) (by omega))
    (fun i j hi hj hij => nxs_ne D (by omega) (by omega) (by omega))
    (z_swap_of hm D (by omega : 0 < m) D₀)
    (fun i hi => (nxs_ne_z D (i + 2)).symm)
    (fun i hi => (nxs_comm_z D (i + 2)).symm)
  set en := D₀.hom δ with hen
  have hm1 : m - 2 - 1 + 2 = m - 1 := by omega
  simp only [hm1] at h1
  have hen_p : en ∈ Partners (nxs D 0) := D₀.swap_mem δ hδ
  have hen2 : en * en = 1 := Partners.mul_self_of hen_p (nxs_sq D (by omega : 0 < m))
  have hcomm : ∀ i, 2 ≤ i → i + 2 ≤ m → nxs D i * en = en * nxs D i := by
    intro i hi2 him
    have := h3 (i - 2) (by omega)
    rwa [show i - 2 + 2 = i by omega, eq_comm] at this
  have hne : ∀ i, 2 ≤ i → i < m → en ≠ nxs D i := by
    intro i hi2 him
    have := h4 (i - 2) (by omega)
    rwa [show i - 2 + 2 = i by omega] at this
  obtain ⟨D₃⟩ := D.nonempty_of_isConj (nxs_partner D (by omega : 3 < m)).1
  have hP3 : ∀ i, i < m → i ≠ 3 → i + 2 ≤ 3 ∨ 3 + 2 ≤ i → nxs D i ∈ Partners (nxs D 3) := by
    intro i him hi3 hi
    refine Partners.of_isConj (nxs_partner D (by omega : 3 < m)) (nxs_partner D him).1
      (nxs_ne D him (by omega) hi3) ?_
    rcases hi with hi | hi
    · exact nxs_comm D hi (by omega)
    · exact (nxs_comm D hi him).symm
  have hx3p : nxs D 3 ∈ Partners (nxs D 0) := hp 3 (by omega) (by omega)
  have hx3s : (D₀.π ⟨nxs D 3, NearData.mem_centralizer_of_partner hx3p⟩).IsSwap := by
    obtain ⟨τ, hτ, hτe⟩ := nxs_swap_of hm D (by omega : 0 < m) (by omega : 3 < m)
      (Or.inl (by omega)) D₀
    have : D₀.π ⟨nxs D 3, NearData.mem_centralizer_of_partner hx3p⟩ = τ := by
      rw [← D₀.π_ι τ]
      exact D₀.π_congr hτe.symm _ _
    rw [this]; exact hτ
  have henπ : (D₀.π ⟨en, NearData.mem_centralizer_of_partner hen_p⟩).IsSwap := by
    have : D₀.π ⟨en, NearData.mem_centralizer_of_partner hen_p⟩ = δ := D₀.π_ι δ
    rw [this]; exact hδ
  have hen3c : en * nxs D 3 = nxs D 3 * en := (hcomm 3 (by omega) (by omega)).symm
  have hen3ne : en ≠ nxs D 3 := hne 3 (by omega) (by omega)
  have hv : en ∈ Partners (nxs D 3) := Partners.of_isConj hx3p hen_p.1 hen3ne hen3c
  have hvs := NearData.isSwap_of_swap_partners (by omega) D₀ D₃ hx3p hen_p hx3s henπ hen3c
    hen3ne
  have hv' := NearData.exists_swap_of_isSwap (by omega) D₃ hv hvs
  have hu' := nxs_swap_of hm D (by omega : 3 < m) (by omega : m - 1 < m) (Or.inl (by omega)) D₃
  have hs' := nxs_swap_of hm D (by omega : 3 < m) (by omega : 1 < m) (Or.inr (by omega)) D₃
  have hw' := z_swap_of hm D (by omega : 3 < m) D₃
  have hone : nxs D 1 * en = en * nxs D 1 := commute_of_chain_three_of_hom D₃.hom
    D₃.hom_injective hu' hv' hw' hs'
    (hne (m - 1) (by omega) (by omega)).symm h5 (nxs_ne_z D (m - 1))
    h1 h2 (nxs_comm_z D (m - 1)) (nxs_comm D (by omega : 1 + 2 ≤ m - 1) (by omega))
    (nxs_comm_z D 1) (nxs_ne D (by omega : 1 < m) (by omega : m - 1 < m) (by omega))
    (nxs_ne_z D 1)
  refine ⟨en, (nxs_partner D (by omega : 0 < m)).1.trans hen_p.1, hen2, h5, h1, h2, ?_, hne⟩
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | hi2
  · exact hen_p.2.2.symm
  · exact hone
  · exact hcomm i hi2 hi

@[expose] def finIncl (m : ℕ) : Fin (m + 1) ≃ {i : Fin (m + 3) // (i : ℕ) < m + 1} where
  toFun i := ⟨⟨i, by omega⟩, i.2⟩
  invFun j := ⟨j.1, j.2⟩
  left_inv i := rfl
  right_inv j := rfl

@[expose] noncomputable def inclPerm (m : ℕ) : Perm (Fin (m + 1)) →* Perm (Fin (m + 3)) :=
  Perm.extendDomainHom (finIncl m)

theorem inclPerm_swap (a b : Fin (m + 1)) :
    inclPerm m (swap a b) = swap ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  apply Equiv.ext
  intro x
  show (swap a b).extendDomain (finIncl m) x = _
  by_cases hx : (x : ℕ) < m + 1
  · rw [Perm.extendDomain_apply_subtype (swap a b) (finIncl m) (b := x) hx]
    set y := (finIncl m).symm ⟨x, hx⟩ with hy
    have hxy : x = ((finIncl m y : {i : Fin (m + 3) // (i : ℕ) < m + 1}) : Fin (m + 3)) := by
      rw [hy, Equiv.apply_symm_apply]
    have hinj : Function.Injective (fun i : Fin (m + 1) =>
        ((finIncl m i : {i : Fin (m + 3) // (i : ℕ) < m + 1}) : Fin (m + 3))) := by
      intro i j h
      simp only [finIncl, Equiv.coe_fn_mk, Fin.mk.injEq] at h
      exact Fin.ext h
    have h1 := hinj.swap_apply a b y
    rw [hxy]
    exact h1.symm
  · rw [Perm.extendDomain_apply_not_subtype (swap a b) (finIncl m) (b := x) hx]
    have ha : x ≠ ⟨a, by omega⟩ := fun h => hx (by rw [h]; exact a.2)
    have hb : x ≠ ⟨b, by omega⟩ := fun h => hx (by rw [h]; exact b.2)
    rw [swap_apply_of_ne_of_ne ha hb]

theorem inclPerm_adjSwap {i : ℕ} (hi : i < m) : inclPerm m (adjSwap m i) = adjSwap (m + 2) i := by
  rw [adjSwap_of_lt hi, adjSwap_of_lt (by omega), inclPerm_swap]

theorem inclPerm_isSwap {σ : Perm (Fin (m + 1))} (hσ : σ.IsSwap) : (inclPerm m σ).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  rw [inclPerm_swap]
  exact ⟨_, _, fun h => hab (Fin.ext (by simpa using congrArg Fin.val h)), rfl⟩

theorem exists_symmetric_overgroup_near (hm : 10 ≤ m) (D : NearData z (m + 1)) :
    ∃ (M : Subgroup G) (eM : Perm (Fin (m + 3)) ≃* M),
      centralizer ({z} : Set G) ≤ M ∧ (eM (adjSwap (m + 2) (m + 1)) : G) = z ∧
      (∀ σ : Perm (Fin (m + 1)), (eM (inclPerm m σ) : G) = D.ι σ) ∧
      ∀ ρ : Perm (Fin (m + 3)), ρ.IsSwap → IsConj z (eM ρ : G) := by
  obtain ⟨en, -, hen2, hene, h1, h2, hcomm, hne⟩ := exists_en_near hm D
  have hz2 : z * z = 1 := D.sq
  let t : ℕ → G := snoc (m + 1) (snoc m (nxs D) en) z
  have ht : ∀ i, i < m → t i = nxs D i := fun i hi => by
    simp only [t]
    rw [snoc_of_lt (by omega), snoc_of_lt hi]
  have htz : t (m + 1) = z := snoc_self
  have hx1 : IsCoxeterA (m + 1) (snoc m (nxs D) en) :=
    IsCoxeterA.snoc (isCoxeterA_nxs D) hen2
      (fun _ => braid_of_pow_three (nxs_sq D (by omega)) hen2 h1)
      (fun i hi => hcomm i hi)
  have hx2 : IsCoxeterA (m + 2) t :=
    IsCoxeterA.snoc hx1 hz2
      (fun _ => by
        rw [show m + 1 - 1 = m by omega, snoc_self]
        exact braid_of_pow_three hen2 hz2 h2)
      (fun i hi => by
        rw [snoc_of_lt (by omega : i < m)]
        exact nxs_comm_z D i)
  have h01 : t 0 ≠ t 1 := by
    rw [ht 0 (by omega), ht 1 (by omega)]
    exact nxs_ne D (by omega) (by omega) (by omega)
  have h02 : t 0 ≠ t 2 := by
    rw [ht 0 (by omega), ht 2 (by omega)]
    exact nxs_ne D (by omega) (by omega) (by omega)
  obtain ⟨e, he⟩ := exists_mulEquiv_closure (n := m + 2) (by omega)
    hx2 h01 (fun _ => h02)
  have hzM : z ∈ Subgroup.closure (t '' Set.Iio (m + 2)) :=
    Subgroup.subset_closure ⟨m + 1, by simp, htz⟩
  have hcompat : ∀ σ : Perm (Fin (m + 1)), (e (inclPerm m σ) : G) = D.ι σ := by
    have heq : ((Subgroup.closure (t '' Set.Iio (m + 2))).subtype.comp
        (e.toMonoidHom.comp (inclPerm m))) = D.hom := by
      apply MonoidHom.eq_of_eqOn_top
      rw [← closure_adjSwap m]
      apply MonoidHom.eqOn_closure
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < m := hi
      show (e (inclPerm m (adjSwap m i)) : G) = D.ι (adjSwap m i)
      rw [inclPerm_adjSwap hi', he i (by omega), ht i hi']
      rfl
    intro σ
    exact DFunLike.congr_fun heq σ
  have hSM : ∀ σ : Perm (Fin (m + 1)), (D.ι σ : G) ∈ Subgroup.closure (t '' Set.Iio (m + 2)) := by
    intro σ
    rw [← hcompat σ]
    exact (e _).2
  refine ⟨_, e, ?_, ?_, hcompat, ?_⟩
  · intro x hx
    rcases D.eq_or ⟨x, hx⟩ with h | h
    · have : x = D.ι (D.π ⟨x, hx⟩) := h
      rw [this]; exact hSM _
    · have : x = z * D.ι (D.π ⟨x, hx⟩) := h
      rw [this]; exact mul_mem hzM (hSM _)
  · rw [he (m + 1) (by omega), htz]
  · intro ρ hρ
    have hconj : IsConj (adjSwap (m + 2) (m + 1)) ρ := by
      rw [adjSwap_of_lt (by omega)]
      obtain ⟨p, q, hpq, rfl⟩ := hρ
      exact isConj_swap (by simp [Fin.ext_iff]) hpq
    have h2' : IsConj (e (adjSwap (m + 2) (m + 1)) : G) (e ρ : G) :=
      ((Subgroup.closure (t '' Set.Iio (m + 2))).subtype.comp e.toMonoidHom).map_isConj hconj
    rwa [he (m + 1) (by omega), htz] at h2'

end Chain

end CFSG.OddStandard.AltStdSec
