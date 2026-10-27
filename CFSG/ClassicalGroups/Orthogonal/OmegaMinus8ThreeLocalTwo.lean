module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalModel
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalPlanes
import CFSG.ClassicalInvolution.RouteD.TWYType
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.Two

open CFSG.GroupTheory.WeirSylow

abbrev Aut : Type := ModelSpace (ZMod 2) ≃ₗ[ZMod 2] ModelSpace (ZMod 2)

noncomputable abbrev omega : Subgroup Aut := modelOmega (1 : ZMod 2) 1

abbrev tor (v : Fin 3 → ZMod 3) : Aut := cm (ZMod 2) (Multiplicative.ofAdd v)

@[expose] def weight (v : Fin 3 → ZMod 3) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

private abbrev V2 : Type := ModelSpace (ZMod 2)

private theorem three_ne_zero_two : (3 : ZMod 2) ≠ 0 := by decide

private theorem card_modEq_card_filter_perm_fixed {α : Type*} [DecidableEq α] (σ : Equiv.Perm α)
    {p : ℕ} [Fact p.Prime] (hσ : σ ^ p = 1) (S : Finset α) (hS : ∀ x, x ∈ S ↔ σ x ∈ S) :
    S.card ≡ (S.filter fun x => σ x = x).card [MOD p] := by
  set τ : Equiv.Perm {x // x ∈ S} := σ.subtypePerm (fun x => (hS x).symm) with hτdef
  have hτ : τ ^ p ^ 1 = 1 := by
    rw [pow_one, hτdef, Equiv.Perm.subtypePerm_pow]
    ext x
    simp [hσ]
  have h := Equiv.Perm.card_compl_support_modEq hτ
  have h1 : Fintype.card {x // x ∈ S} = S.card := Fintype.card_coe S
  have h2 : τ.supportᶜ.card = (S.filter fun x => σ x = x).card := by
    refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hy
      simp only [Finset.mem_filter]
      exact ⟨y.2, by simpa [hτdef] using congrArg Subtype.val hy⟩
    · intro y₁ _ y₂ _ h
      exact Subtype.ext h
    · intro x hx
      simp only [Finset.mem_filter] at hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      exact Subtype.ext (by simpa [hτdef] using hx.2)
  rw [h1, h2] at h
  exact h.symm

private theorem eq_two_or_three_of_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) {a b : ℕ}
    (h : ℓ ∣ 2 ^ a * 3 ^ b) : ℓ = 2 ∨ ℓ = 3 := by
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (hℓ.dvd_of_dvd_pow h))

private theorem isSolvable_of_natCard_dvd {G : Type*} [Group G] {a b : ℕ}
    (h : Nat.card G ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have : Finite G := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at h
    exact (by positivity : 2 ^ a * 3 ^ b ≠ 0) h
  exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three h

private theorem map_eq_one_of_commutator_eq_self {G H : Type*} [Group G] [Group H]
    [Group.IsSolvable H] {J : Subgroup G} (hJ : ⁅J, J⁆ = J) (f : ↥J →* H) (g : ↥J) : f g = 1 := by
  have htop : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, J.range_subtype, hJ]
  have hrange : f.range = ⊥ := by
    by_contra hne
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop] at hlt
    exact lt_irrefl _ hlt
  have hmem : f g ∈ f.range := ⟨g, rfl⟩
  rw [hrange] at hmem
  exact hmem

private def summandHom {R M V : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module R V] (G : Subgroup (M ≃ₗ[R] M)) (ι : V →ₗ[R] M) (π : M →ₗ[R] V)
    (hπι : ∀ v, π (ι v) = v) (hG : ∀ g ∈ G, ∀ v, ι (π (g (ι v))) = g (ι v)) :
    ↥G →* (V ≃ₗ[R] V) where
  toFun g := LinearEquiv.ofLinear (π ∘ₗ (g : M ≃ₗ[R] M).toLinearMap ∘ₗ ι)
    (π ∘ₗ ((g : M ≃ₗ[R] M)⁻¹).toLinearMap ∘ₗ ι)
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [hG _ (inv_mem g.2) v, ← LinearEquiv.mul_apply, mul_inv_cancel]
      exact hπι v)
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [hG _ g.2 v, ← LinearEquiv.mul_apply, inv_mul_cancel]
      exact hπι v)
  map_one' := LinearEquiv.ext fun v => by
    simp [hπι]
  map_mul' g h := LinearEquiv.ext fun v => by
    simp only [LinearEquiv.ofLinear_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hG _ h.2 v]

private theorem summandHom_apply {R M V : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module R V] (G : Subgroup (M ≃ₗ[R] M)) (ι : V →ₗ[R] M)
    (π : M →ₗ[R] V) (hπι : ∀ v, π (ι v) = v) (hG : ∀ g ∈ G, ∀ v, ι (π (g (ι v))) = g (ι v))
    (g : ↥G) (v : V) : summandHom G ι π hπι hG g v = π ((g : M ≃ₗ[R] M) (ι v)) :=
  rfl

private def summandOHom {R M V : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module R V] (Q : QuadraticForm R M) (Q' : QuadraticForm R V)
    (G : Subgroup (M ≃ₗ[R] M)) (hGQ : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ι : V →ₗ[R] M) (π : M →ₗ[R] V) (hπι : ∀ v, π (ι v) = v) (hι : ∀ v, Q (ι v) = Q' v)
    (hG : ∀ g ∈ G, ∀ v, ι (π (g (ι v))) = g (ι v)) :
    ↥G →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q') :=
  (summandHom G ι π hπι hG).codRestrict _ fun g =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      change Q' (π ((g : M ≃ₗ[R] M) (ι v))) = Q' v
      rw [← hι, hG _ g.2 v, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hGQ g.2), hι]

private theorem summandOHom_apply {R M V : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module R V] (Q : QuadraticForm R M) (Q' : QuadraticForm R V)
    (G : Subgroup (M ≃ₗ[R] M)) (hGQ : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ι : V →ₗ[R] M) (π : M →ₗ[R] V) (hπι : ∀ v, π (ι v) = v) (hι : ∀ v, Q (ι v) = Q' v)
    (hG : ∀ g ∈ G, ∀ v, ι (π (g (ι v))) = g (ι v)) (g : ↥G) (v : V) :
    (summandOHom Q Q' G hGQ ι π hπι hι hG g : V ≃ₗ[R] V) v = π ((g : M ≃ₗ[R] M) (ι v)) :=
  rfl

private theorem apply_eq_of_summandOHom_eq_one {R M V : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid V] [Module R V] (Q : QuadraticForm R M) (Q' : QuadraticForm R V)
    (G : Subgroup (M ≃ₗ[R] M)) (hGQ : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ι : V →ₗ[R] M) (π : M →ₗ[R] V) (hπι : ∀ v, π (ι v) = v) (hι : ∀ v, Q (ι v) = Q' v)
    (hG : ∀ g ∈ G, ∀ v, ι (π (g (ι v))) = g (ι v)) {g : ↥G}
    (h : summandOHom Q Q' G hGQ ι π hπι hι hG g = 1) (v : V) :
    (g : M ≃ₗ[R] M) (ι v) = ι v := by
  have h' : π ((g : M ≃ₗ[R] M) (ι v)) = v :=
    congrArg (fun e : ↥(TauCeti.QuadraticMap.orthogonalGroup Q') => (e : V ≃ₗ[R] V) v) h
  rw [← hG _ g.2 v, h']

private theorem commute_apply {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {g t : M ≃ₗ[R] M} (h : Commute g t) (x : M) : t (g x) = g (t x) := by
  calc t (g x) = (t * g) x := rfl
    _ = (g * t) x := by rw [h.eq]
    _ = g (t x) := rfl

private theorem fix_of_commute {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {g t : M ≃ₗ[R] M} (h : Commute g t) {x : M} (hx : t x = x) : t (g x) = g x := by
  rw [commute_apply h, hx]

private theorem sq_add_of_commute {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {g t : M ≃ₗ[R] M} (h : Commute g t) {x : M} (hx : t (t x) + t x + x = 0) :
    t (t (g x)) + t (g x) + g x = 0 := by
  rw [commute_apply h, commute_apply h, ← map_add, ← map_add, hx, map_zero]

private theorem rotPow_sq_add_of_ne_zero {K : Type} [Field K] {k : ZMod 3} (hk : k ≠ 0)
    (p : K × K) : rotPow K k (rotPow K k p) + rotPow K k p + p = 0 := by
  have h3 := rotLE_pow_three (K := K)
  have hsq := rotLE_sq_add (K := K)
  fin_cases k
  · exact absurd rfl hk
  · change (rotLE K ^ 1) ((rotLE K ^ 1) p) + (rotLE K ^ 1) p + p = 0
    simpa using hsq p
  · change (rotLE K ^ 2) ((rotLE K ^ 2) p) + (rotLE K ^ 2) p + p = 0
    have h4 : (rotLE K ^ 2) ((rotLE K ^ 2) p) = rotLE K p := by
      rw [← LinearEquiv.mul_apply, ← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, h3, one_mul,
        pow_one]
    rw [h4, pow_two, LinearEquiv.mul_apply]
    convert hsq p using 1
    abel

private theorem cmEquiv_sq_add_eq_zero_iff {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    (v : Fin 3 → ZMod 3) (x : ModelSpace K) :
    cmEquiv K v (cmEquiv K v x) + cmEquiv K v x + x = 0 ↔ x.2 = 0 ∧ ∀ l, v l = 0 → x.1 l = 0 := by
  have key : ∀ y : K × K, y + y + y = 0 ↔ y = 0 := fun y => by
    constructor
    · intro h
      have h' : (3 : K) • y = 0 := by
        rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
        exact h
      exact (smul_eq_zero.mp h').resolve_left h3
    · rintro rfl
      simp
  constructor
  · intro h
    have h1 : ∀ l, rotPow K (v l) (rotPow K (v l) (x.1 l)) + rotPow K (v l) (x.1 l) + x.1 l = 0 :=
      fun l => congrFun (congrArg Prod.fst h) l
    have h2 : x.2 + x.2 + x.2 = 0 := congrArg Prod.snd h
    refine ⟨(key _).mp h2, fun l hl => (key _).mp ?_⟩
    have h1l := h1 l
    rw [hl, rotPow_zero] at h1l
    simpa using h1l
  · rintro ⟨h2, h1⟩
    refine Prod.ext (funext fun l => ?_) ?_
    · change rotPow K (v l) (rotPow K (v l) (x.1 l)) + rotPow K (v l) (x.1 l) + x.1 l = 0
      by_cases hl : v l = 0
      · rw [h1 l hl]
        simp
      · exact rotPow_sq_add_of_ne_zero hl _
    · change x.2 + x.2 + x.2 = 0
      rw [h2]
      simp

private theorem fin_three_eq_or {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
  revert i j k l
  decide

private def rotPlaneIncl (K : Type) [Field K] (i : Fin 3) : (K × K) →ₗ[K] ModelSpace K :=
  (LinearMap.single K (fun _ : Fin 3 => K × K) i).prod 0

private def rotPlaneProj (K : Type) [Field K] (i : Fin 3) : ModelSpace K →ₗ[K] (K × K) :=
  (LinearMap.proj i).comp (LinearMap.fst K _ _)

private def rotPairIncl (K : Type) [Field K] (i j : Fin 3) :
    (K × K) × (K × K) →ₗ[K] ModelSpace K :=
  (rotPlaneIncl K i).coprod (rotPlaneIncl K j)

private def rotPairProj (K : Type) [Field K] (i j : Fin 3) :
    ModelSpace K →ₗ[K] (K × K) × (K × K) :=
  (rotPlaneProj K i).prod (rotPlaneProj K j)

private theorem rotPlaneIncl_apply {K : Type} [Field K] (i : Fin 3) (p : K × K) :
    rotPlaneIncl K i p = (Pi.single i p, 0) :=
  rfl

private theorem rotPairIncl_apply {K : Type} [Field K] (i j : Fin 3) (w : (K × K) × (K × K)) :
    rotPairIncl K i j w = (Pi.single i w.1 + Pi.single j w.2, 0) := by
  simp [rotPairIncl, rotPlaneIncl_apply]

private theorem rotPlaneIncl_apply_of_ne {K : Type} [Field K] {i l : Fin 3} (h : l ≠ i)
    (p : K × K) : (rotPlaneIncl K i p).1 l = 0 :=
  Pi.single_eq_of_ne (M := fun _ => K × K) h p

private theorem rotPlaneProj_rotPlaneIncl {K : Type} [Field K] (i : Fin 3) (p : K × K) :
    rotPlaneProj K i (rotPlaneIncl K i p) = p := by
  simp [rotPlaneProj, rotPlaneIncl_apply]

private theorem rotPairProj_rotPairIncl {K : Type} [Field K] {i j : Fin 3} (hij : i ≠ j)
    (w : (K × K) × (K × K)) : rotPairProj K i j (rotPairIncl K i j w) = w := by
  simp [rotPairProj, rotPlaneProj, rotPairIncl_apply, Pi.single_eq_of_ne hij,
    Pi.single_eq_of_ne hij.symm]

private theorem rotPlaneIncl_rotPlaneProj {K : Type} [Field K] {i : Fin 3} {x : ModelSpace K}
    (h2 : x.2 = 0) (h1 : ∀ l, l ≠ i → x.1 l = 0) : rotPlaneIncl K i (rotPlaneProj K i x) = x := by
  refine Prod.ext (funext fun l => ?_) h2.symm
  by_cases hl : l = i
  · subst hl
    simp [rotPlaneIncl_apply, rotPlaneProj]
  · simp [rotPlaneIncl_apply, Pi.single_eq_of_ne hl, h1 l hl]

private theorem rotPairIncl_rotPairProj {K : Type} [Field K] {i j : Fin 3} (hij : i ≠ j)
    {x : ModelSpace K} (h2 : x.2 = 0) (h1 : ∀ l, l ≠ i → l ≠ j → x.1 l = 0) :
    rotPairIncl K i j (rotPairProj K i j x) = x := by
  refine Prod.ext (funext fun l => ?_) (by simp [rotPairIncl_apply, h2])
  by_cases hli : l = i
  · subst hli
    simp [rotPairIncl_apply, rotPairProj, rotPlaneProj, Pi.single_eq_of_ne hij]
  by_cases hlj : l = j
  · subst hlj
    simp [rotPairIncl_apply, rotPairProj, rotPlaneProj, Pi.single_eq_of_ne (Ne.symm hij)]
  · simp [rotPairIncl_apply, Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj, h1 l hli hlj]

private theorem modelForm_rotPlaneIncl {K : Type} [Field K] (b c : K) (i : Fin 3) (p : K × K) :
    modelForm b c (rotPlaneIncl K i p) = rotForm K p := by
  rw [modelForm_apply, rotPlaneIncl_apply, Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

private theorem modelForm_rotPairIncl {K : Type} [Field K] (b c : K) {i j : Fin 3} (hij : i ≠ j)
    (w : (K × K) × (K × K)) :
    modelForm b c (rotPairIncl K i j w) = ((rotForm K).prod (rotForm K)) w := by
  rw [modelForm_apply, rotPairIncl_apply, QuadraticMap.prod_apply, Finset.sum_eq_add i j hij]
  · simp [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij)]
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl.1, Pi.single_eq_of_ne hl.2]
  · simp
  · simp

private theorem modelForm_inr {K : Type} [Field K] (b c : K) (p : K × K) :
    modelForm b c (LinearMap.inr K (Fin 3 → K × K) (K × K) p) = wForm b c p := by
  simp [modelForm_apply]

private theorem eq_rotPlaneIncl_add_rotPairIncl_add_inr {K : Type} [Field K] {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : ModelSpace K) :
    x = rotPlaneIncl K i (x.1 i) + rotPairIncl K j k (x.1 j, x.1 k) +
      LinearMap.inr K (Fin 3 → K × K) (K × K) x.2 := by
  refine Prod.ext (funext fun l => ?_) (by simp [rotPlaneIncl_apply, rotPairIncl_apply])
  rcases fin_three_eq_or hij hik hjk l with rfl | rfl | rfl
  · simp [rotPlaneIncl_apply, rotPairIncl_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
  · simp [rotPlaneIncl_apply, rotPairIncl_apply, Pi.single_eq_of_ne hij.symm,
      Pi.single_eq_of_ne hjk]
  · simp [rotPlaneIncl_apply, rotPairIncl_apply, Pi.single_eq_of_ne hik.symm,
      Pi.single_eq_of_ne hjk.symm]

private noncomputable def planeSummandHom {K : Type} [Field K] {b c : K}
    (G : Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K)) (hO : G ≤ modelO b c) (i : Fin 3)
    (hG : ∀ g ∈ G, ∀ p,
      rotPlaneIncl K i (rotPlaneProj K i (g (rotPlaneIncl K i p))) = g (rotPlaneIncl K i p)) :
    ↥G →* ↥(TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) :=
  summandOHom (modelForm b c) (rotForm K) G hO (rotPlaneIncl K i) (rotPlaneProj K i)
    (rotPlaneProj_rotPlaneIncl i) (modelForm_rotPlaneIncl b c i) hG

private noncomputable def pairSummandHom {K : Type} [Field K] {b c : K}
    (G : Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K)) (hO : G ≤ modelO b c) {i j : Fin 3}
    (hij : i ≠ j)
    (hG : ∀ g ∈ G, ∀ w,
      rotPairIncl K i j (rotPairProj K i j (g (rotPairIncl K i j w))) = g (rotPairIncl K i j w)) :
    ↥G →* ↥(TauCeti.QuadraticMap.orthogonalGroup ((rotForm K).prod (rotForm K))) :=
  summandOHom (modelForm b c) ((rotForm K).prod (rotForm K)) G hO (rotPairIncl K i j)
    (rotPairProj K i j) (rotPairProj_rotPairIncl hij) (modelForm_rotPairIncl b c hij) hG

private noncomputable def wSummandHom {K : Type} [Field K] {b c : K}
    (G : Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K)) (hO : G ≤ modelO b c)
    (hG : ∀ g ∈ G, ∀ p,
      LinearMap.inr K (Fin 3 → K × K) (K × K) (LinearMap.snd K (Fin 3 → K × K) (K × K)
        (g (LinearMap.inr K (Fin 3 → K × K) (K × K) p))) =
          g (LinearMap.inr K (Fin 3 → K × K) (K × K) p)) :
    ↥G →* ↥(TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) :=
  summandOHom (modelForm b c) (wForm b c) G hO (LinearMap.inr K (Fin 3 → K × K) (K × K))
    (LinearMap.snd K (Fin 3 → K × K) (K × K)) (fun _ => rfl) (modelForm_inr b c) hG

private theorem planeSummandHom_eq_one {K : Type} [Field K] {b c : K}
    {G : Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K)} {hO : G ≤ modelO b c} {i : Fin 3}
    {hG : ∀ g ∈ G, ∀ p,
      rotPlaneIncl K i (rotPlaneProj K i (g (rotPlaneIncl K i p))) = g (rotPlaneIncl K i p)}
    {g : ↥G} (h : planeSummandHom G hO i hG g = 1) (p : K × K) :
    (g : ModelSpace K ≃ₗ[K] ModelSpace K) (rotPlaneIncl K i p) = rotPlaneIncl K i p :=
  apply_eq_of_summandOHom_eq_one _ _ G hO _ _ _ _ hG h p

private theorem pairSummandHom_eq_one {K : Type} [Field K] {b c : K}
    {G : Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K)} {hO : G ≤ modelO b c} {i j : Fin 3}
    {hij : i ≠ j}
    {hG : ∀ g ∈ G, ∀ w,
      rotPairIncl K i j (rotPairProj K i j (g (rotPairIncl K i j w))) = g (rotPairIncl K i j w)}
    {g : ↥G} (h : pairSummandHom G hO hij hG g = 1) (w : (K × K) × (K × K)) :
    (g : ModelSpace K ≃ₗ[K] ModelSpace K) (rotPairIncl K i j w) = rotPairIncl K i j w :=
  apply_eq_of_summandOHom_eq_one _ _ G hO _ _ _ _ hG h w

private theorem wSummandHom_eq_one {K : Type} [Field K] {b c : K}
    {G : Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K)} {hO : G ≤ modelO b c}
    {hG : ∀ g ∈ G, ∀ p,
      LinearMap.inr K (Fin 3 → K × K) (K × K) (LinearMap.snd K (Fin 3 → K × K) (K × K)
        (g (LinearMap.inr K (Fin 3 → K × K) (K × K) p))) =
          g (LinearMap.inr K (Fin 3 → K × K) (K × K) p)}
    {g : ↥G} (h : wSummandHom G hO hG g = 1) (p : K × K) :
    (g : ModelSpace K ≃ₗ[K] ModelSpace K) (LinearMap.inr K (Fin 3 → K × K) (K × K) p) =
      LinearMap.inr K (Fin 3 → K × K) (K × K) p :=
  apply_eq_of_summandOHom_eq_one _ _ G hO _ _ _ _ hG h p

private theorem not_isSplit_zmod_two : ¬ IsSplit (ZMod 2) := by
  unfold IsSplit
  decide

private def rotQ (p : ZMod 2 × ZMod 2) : ZMod 2 := p.1 ^ 2 + (-1) * p.1 * p.2 + 1 * p.2 ^ 2

private def wQ (p : ZMod 2 × ZMod 2) : ZMod 2 := p.1 ^ 2 + (-1) * p.1 * p.2 + 0 * p.2 ^ 2

private theorem rotForm_two_apply (p : ZMod 2 × ZMod 2) : rotForm (ZMod 2) p = rotQ p := by
  rw [rotForm, binForm_apply]
  rfl

private theorem wForm_two_apply (p : ZMod 2 × ZMod 2) : wForm (1 : ZMod 2) 1 p = wQ p := by
  rw [wForm_of_not_isSplit not_isSplit_zmod_two, binForm_apply]
  rfl

private def qc (x : V2) : ZMod 2 := ∑ i, rotQ (x.1 i) + wQ x.2

private theorem modelForm_eq_qc (x : V2) : modelForm (1 : ZMod 2) 1 x = qc x := by
  rw [modelForm_apply, qc]
  simp only [rotForm_two_apply, wForm_two_apply]

private theorem qc_apply_of_mem {g : Aut} (hg : g ∈ modelO (1 : ZMod 2) 1) (x : V2) :
    qc (g x) = qc x := by
  rw [← modelForm_eq_qc, ← modelForm_eq_qc]
  have hg' := hg
  rw [modelO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg'
  exact hg' x

private theorem natCard_orthogonalGroup_rotForm_two :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (rotForm (ZMod 2))) = 6 := by
  rw [natCard_orthogonalGroup_rotForm three_ne_zero_two, Nat.card_zmod]
  decide

private theorem natCard_orthogonalGroup_wForm_two :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (wForm (1 : ZMod 2) 1)) = 2 := by
  rw [natCard_orthogonalGroup_wForm three_ne_zero_two (by decide), Nat.card_zmod]
  decide

private theorem natCard_orthogonalGroup_rotForm_prod {K : Type} [Field K] [Finite K]
    (h3 : (3 : K) ≠ 0) :
    (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup ((rotForm K).prod (rotForm K))) : ℤ) =
      2 * (Nat.card K : ℤ) ^ 2 * ((Nat.card K : ℤ) ^ 2 - 1) * ((Nat.card K : ℤ) ^ 2 - 1) := by
  have hnd := nondegenerate_polarBilin_rotForm h3
  have hdim : Module.finrank K (K × K) = 2 * 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have htype : IsPlusType ((rotForm K).prod (rotForm K)) :=
    (CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_prod_iff hnd hnd le_rfl le_rfl hdim
      hdim).mpr Iff.rfl
  have hcard := natCard_orthogonalGroup_of_type (nondegenerate_polarBilin_prod hnd hnd) (m := 1)
    (by rw [Module.finrank_prod, hdim]) (ε := 1) (Or.inl ⟨rfl, htype⟩)
  rw [hcard, Finset.Icc_self, Finset.prod_singleton]
  ring

private theorem natCard_orthogonalGroup_rotForm_prod_two :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      ((rotForm (ZMod 2)).prod (rotForm (ZMod 2)))) = 72 := by
  have h := natCard_orthogonalGroup_rotForm_prod (K := ZMod 2) three_ne_zero_two
  rw [Nat.card_zmod] at h
  exact_mod_cast h.trans (by norm_num : _ = (72 : ℤ))

private theorem isSolvable_orthogonalGroup_rotForm_two :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup (rotForm (ZMod 2))) :=
  isSolvable_of_natCard_dvd (a := 1) (b := 1)
    (dvd_of_eq (natCard_orthogonalGroup_rotForm_two.trans (by norm_num)))

private theorem isSolvable_orthogonalGroup_wForm_two :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup (wForm (1 : ZMod 2) 1)) :=
  isSolvable_of_natCard_dvd (a := 1) (b := 0)
    (dvd_of_eq (natCard_orthogonalGroup_wForm_two.trans (by norm_num)))

private theorem isSolvable_orthogonalGroup_rotForm_prod_two :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      ((rotForm (ZMod 2)).prod (rotForm (ZMod 2)))) :=
  isSolvable_of_natCard_dvd (a := 3) (b := 2)
    (dvd_of_eq (natCard_orthogonalGroup_rotForm_prod_two.trans (by norm_num)))

private theorem ne_zero_of_weight_eq_three (v : Fin 3 → ZMod 3) (hv : weight v = 3)
    (i : Fin 3) : v i ≠ 0 := by
  revert i
  revert v
  decide

private theorem card_sing_U :
    (Finset.univ.filter fun x : V2 => x.2 = 0 ∧ x ≠ 0 ∧ qc x = 0).card = 27 := by
  decide +kernel

private theorem card_U : (Finset.univ.filter fun x : V2 => x.2 = 0).card = 64 := by
  decide +kernel

private theorem card_W0 : (Finset.univ.filter fun x : V2 => x.1 = 0 ∧ x ≠ 0).card = 3 := by
  decide +kernel

private theorem natCard_V2 : Nat.card V2 = 256 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem tor_apply_eq_self_iff {v : Fin 3 → ZMod 3} (hv : ∀ i, v i ≠ 0) (x : V2) :
    tor v x = x ↔ x.1 = 0 := by
  rw [show tor v x = cmEquiv (ZMod 2) v x from rfl,
    cmEquiv_apply_eq_self_iff three_ne_zero_two v x]
  exact ⟨fun h => funext fun i => h i (hv i), fun h i _ => by rw [h]; rfl⟩

private theorem snd_apply_eq_zero {v : Fin 3 → ZMod 3} (hv : ∀ i, v i ≠ 0) {g : Aut}
    (hgc : Commute g (tor v)) {x : V2} (hx : x.2 = 0) : (g x).2 = 0 := by
  have hk := (cmEquiv_sq_add_eq_zero_iff three_ne_zero_two v x).mpr
    ⟨hx, fun l hl => absurd hl (hv l)⟩
  exact ((cmEquiv_sq_add_eq_zero_iff three_ne_zero_two v (g x)).mp
    (sq_add_of_commute hgc hk)).1

private theorem fst_apply_eq_zero {v : Fin 3 → ZMod 3} (hv : ∀ i, v i ≠ 0) {g : Aut}
    (hgc : Commute g (tor v)) {x : V2} (hx : x.1 = 0) : (g x).1 = 0 := by
  rw [← tor_apply_eq_self_iff hv] at hx ⊢
  exact fix_of_commute hgc hx

private theorem toEquiv_pow_eq_one {g : Aut} {n : ℕ} (h : g ^ n = 1) : g.toEquiv ^ n = 1 := by
  refine Equiv.ext fun x => ?_
  have := congrArg (fun f : Aut => f x) h
  simp only [LinearEquiv.coe_pow, LinearEquiv.coe_one, id_eq] at this
  simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq, LinearEquiv.coe_toEquiv] using this

private theorem tor_pow_three (v : Fin 3 → ZMod 3) : tor v ^ 3 = 1 := by
  have h3v : (Multiplicative.ofAdd v) ^ 3 = 1 := by
    rw [← ofAdd_nsmul]
    have : (3 : ℕ) • v = 0 := by
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    rw [this, ofAdd_zero]
  rw [tor, ← map_pow, h3v, map_one]

private theorem false_of_counts {ℓ k s : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hk : k ∣ 2 ^ 8) (hk64 : k ≠ 64) (hkle : k ≤ 64) (hsk : s < k) (hs27 : s ≤ 27)
    (dU : ℓ ∣ 64 - k) (d3U : 3 ∣ 64 - k) (dS : ℓ ∣ 27 - s) (d3S : 3 ∣ s) : False := by
  obtain ⟨d, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk
  have hd6 : d ≤ 6 := by
    by_contra h
    have : 2 ^ 7 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have key : ∀ a b : ℕ, ℓ ∣ 2 ^ a * 3 ^ b → False := fun a b h => by
    rcases eq_two_or_three_of_dvd hℓ h with h | h <;> contradiction
  interval_cases d
  · have hs0 : s = 0 := by omega
    subst hs0
    exact key 0 2 (by have := Nat.dvd_gcd dU dS; norm_num at this ⊢; exact this)
  · norm_num at d3U
  · have hcases : s = 0 ∨ s = 3 := by omega
    rcases hcases with rfl | rfl
    · exact key 0 1 (by have := Nat.dvd_gcd dU dS; norm_num at this ⊢; exact this)
    · exact key 2 1 (by have := Nat.dvd_gcd dU dS; norm_num at this ⊢; exact this)
  · norm_num at d3U
  · exact key 4 1 (by norm_num at dU ⊢; exact dU)
  · norm_num at d3U
  · exact hk64 rfl

private theorem false_of_prime_orderOf {v : Fin 3 → ZMod 3} (hv : ∀ i, v i ≠ 0) {g : Aut}
    (hgO : g ∈ modelO (1 : ZMod 2) 1) (hgc : Commute g (tor v)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hg : orderOf g = ℓ) : False := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hgℓ : g ^ ℓ = 1 := hg ▸ pow_orderOf_eq_one g
  have hQg : ∀ x, qc (g x) = qc x := qc_apply_of_mem hgO
  have hQt : ∀ x, qc (tor v x) = qc x := qc_apply_of_mem (cm_mem_modelO (1 : ZMod 2) 1 _)
  have hgc' : Commute g⁻¹ (tor v) := hgc.inv_left
  have hinv : ∀ x, g⁻¹ (g x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id_eq]
  have hU : ∀ x : V2, x.2 = 0 ↔ (g x).2 = 0 := fun x =>
    ⟨snd_apply_eq_zero hv hgc, fun h => by simpa only [hinv] using snd_apply_eq_zero hv hgc' h⟩
  have hW : ∀ x : V2, x.1 = 0 ↔ (g x).1 = 0 := fun x =>
    ⟨fst_apply_eq_zero hv hgc, fun h => by simpa only [hinv] using fst_apply_eq_zero hv hgc' h⟩
  have hne0 : ∀ (f : Aut) (x : V2), x ≠ 0 ↔ f x ≠ 0 := fun f x =>
    ⟨fun h hx => h (f.injective (hx.trans (map_zero f).symm)), fun h hx => h (hx ▸ map_zero f)⟩
  have hgt : ∀ x : V2, g x = x ↔ g (tor v x) = tor v x := fun x => by
    rw [← commute_apply hgc]
    exact ⟨fun h => by rw [h], fun h => (tor v).injective h⟩
  have htfix : ∀ x : V2, x.2 = 0 → tor v x = x → x = 0 := fun x hx h =>
    Prod.ext ((tor_apply_eq_self_iff hv x).1 h) hx
  have htsnd : ∀ x : V2, (tor v x).2 = x.2 := fun x => rfl
  obtain ⟨U, hUm, hUc⟩ : ∃ U : Finset V2, (∀ x, x ∈ U ↔ x.2 = 0) ∧ U.card = 64 :=
    ⟨_, fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and], card_U⟩
  obtain ⟨S, hSm, hSc⟩ : ∃ S : Finset V2,
      (∀ x, x ∈ S ↔ x.2 = 0 ∧ x ≠ 0 ∧ qc x = 0) ∧ S.card = 27 :=
    ⟨_, fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and], card_sing_U⟩
  obtain ⟨W, hWm, hWc⟩ : ∃ W : Finset V2, (∀ x, x ∈ W ↔ x.1 = 0 ∧ x ≠ 0) ∧ W.card = 3 :=
    ⟨_, fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and], card_W0⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Finset V2, K = U.filter fun x => g.toEquiv x = x := ⟨_, rfl⟩
  obtain ⟨Ks, hKsdef⟩ : ∃ Ks : Finset V2, Ks = S.filter fun x => g.toEquiv x = x := ⟨_, rfl⟩
  have hKm : ∀ x, x ∈ K ↔ x.2 = 0 ∧ g x = x := fun x => by
    rw [hKdef, Finset.mem_filter, hUm]; rfl
  have hKsm : ∀ x, x ∈ Ks ↔ (x.2 = 0 ∧ x ≠ 0 ∧ qc x = 0) ∧ g x = x := fun x => by
    rw [hKsdef, Finset.mem_filter, hSm]; rfl
  have hσ : g.toEquiv ^ ℓ = 1 := toEquiv_pow_eq_one hgℓ
  have hτ : (tor v).toEquiv ^ 3 = 1 := toEquiv_pow_eq_one (tor_pow_three v)
  have cU : U.card ≡ K.card [MOD ℓ] := by
    rw [hKdef]
    exact card_modEq_card_filter_perm_fixed g.toEquiv hσ U (fun x => by
      rw [hUm, hUm]; exact hU x)
  have cS : S.card ≡ Ks.card [MOD ℓ] := by
    rw [hKsdef]
    exact card_modEq_card_filter_perm_fixed g.toEquiv hσ S (fun x => by
      rw [hSm, hSm]
      show _ ↔ (g x).2 = 0 ∧ g x ≠ 0 ∧ qc (g x) = 0
      rw [← hU x, ← hne0 g x, hQg x])
  have cW : W.card ≡ (W.filter fun x => g.toEquiv x = x).card [MOD ℓ] :=
    card_modEq_card_filter_perm_fixed g.toEquiv hσ W (fun x => by
      rw [hWm, hWm]
      show _ ↔ (g x).1 = 0 ∧ g x ≠ 0
      rw [← hW x, ← hne0 g x])
  have c3U : (U \ K).card ≡ 0 [MOD 3] := by
    have := card_modEq_card_filter_perm_fixed (tor v).toEquiv hτ (U \ K) (fun x => by
      rw [Finset.mem_sdiff, Finset.mem_sdiff, hUm, hUm, hKm, hKm]
      show _ ↔ (tor v x).2 = 0 ∧ ¬ ((tor v x).2 = 0 ∧ g (tor v x) = tor v x)
      rw [htsnd, ← hgt x])
    have hempty : ((U \ K).filter fun x => (tor v).toEquiv x = x) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun x hx hfix => ?_
      rw [Finset.mem_sdiff, hUm, hKm] at hx
      have hx0 := htfix x hx.1 hfix
      exact hx.2 ⟨hx.1, by rw [hx0, map_zero]⟩
    rwa [hempty, Finset.card_empty] at this
  have c3Ks : Ks.card ≡ 0 [MOD 3] := by
    have := card_modEq_card_filter_perm_fixed (tor v).toEquiv hτ Ks (fun x => by
      rw [hKsm, hKsm]
      show _ ↔ ((tor v x).2 = 0 ∧ tor v x ≠ 0 ∧ qc (tor v x) = 0) ∧ g (tor v x) = tor v x
      rw [htsnd, ← hne0 (tor v) x, hQt x, ← hgt x])
    have hempty : (Ks.filter fun x => (tor v).toEquiv x = x) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun x hx hfix => ?_
      rw [hKsm] at hx
      exact hx.1.2.1 (htfix x hx.1.1 hfix)
    rwa [hempty, Finset.card_empty] at this
  have hKU : K ⊆ U := fun x hx => (hUm x).2 ((hKm x).1 hx).1
  have hKsS : Ks ⊆ S := fun x hx => (hSm x).2 ((hKsm x).1 hx).1
  have hl5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    by_contra h
    have h4 : ℓ = 4 := by omega
    rw [h4] at hℓ
    norm_num at hℓ
  have hWfix : ∀ x ∈ W, g x = x := by
    have key : ∀ F : Finset V2, F ⊆ W → 3 ≡ F.card [MOD ℓ] → F = W := by
      intro F hFW hF
      have hle : F.card ≤ 3 := hWc ▸ Finset.card_le_card hFW
      have hdiv : ℓ ∣ 3 - F.card := (Nat.modEq_iff_dvd' hle).1 hF.symm
      have h3 : 3 - F.card = 0 := by
        by_contra hne
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv
        omega
      exact Finset.eq_of_subset_of_card_le hFW (by omega)
    have hF := key _ (Finset.filter_subset _ _) (hWc ▸ cW)
    intro x hx
    have hx' : x ∈ W.filter fun x => g.toEquiv x = x := by rw [hF]; exact hx
    exact (Finset.mem_filter.1 hx').2
  have hW0 : ∀ x : V2, x.1 = 0 → g x = x := fun x hx => by
    by_cases h : x = 0
    · rw [h, map_zero]
    · exact hWfix x ((hWm x).2 ⟨hx, h⟩)
  let H : AddSubgroup V2 :=
    { carrier := {x | x.2 = 0 ∧ g x = x}
      add_mem' := fun {a b} ha hb => ⟨by rw [Prod.snd_add, ha.1, hb.1, add_zero],
        by rw [map_add, ha.2, hb.2]⟩
      zero_mem' := ⟨rfl, map_zero g⟩
      neg_mem' := fun {a} ha => ⟨by rw [Prod.snd_neg, ha.1]; rfl, by rw [map_neg, ha.2]; rfl⟩ }
  have hHK : Nat.card H = K.card := by
    have : (H : Set V2) = ↑K := by
      ext x
      rw [Finset.mem_coe, hKm]
      rfl
    rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hKdvd : K.card ∣ 2 ^ 8 := by
    rw [← hHK]
    have := AddSubgroup.card_addSubgroup_dvd_card H
    rwa [natCard_V2] at this
  have hKle : K.card ≤ 64 := hUc ▸ Finset.card_le_card hKU
  have hK64 : K.card ≠ 64 := by
    intro h
    have hKeq : K = U := Finset.eq_of_subset_of_card_le hKU (by rw [h, hUc])
    have hUfix : ∀ x : V2, x.2 = 0 → g x = x := fun x hx =>
      ((hKm x).1 (hKeq ▸ (hUm x).2 hx)).2
    have hg1 : g = 1 := by
      refine LinearEquiv.ext fun x => ?_
      have hx : x = ((x.1, 0) : V2) + ((0, x.2) : V2) := by
        refine Prod.ext ?_ ?_ <;> simp
      rw [LinearEquiv.coe_one, id_eq, hx, map_add, hUfix _ rfl, hW0 _ rfl]
    rw [hg1, orderOf_one] at hg
    exact hℓ.one_lt.ne hg
  have hKsK : Ks.card < K.card := by
    have h0K : (0 : V2) ∈ K := (hKm 0).2 ⟨rfl, map_zero g⟩
    have hsub : Ks ⊆ K.erase 0 := fun x hx => by
      rw [hKsm] at hx
      exact Finset.mem_erase.2 ⟨hx.1.2.1, (hKm x).2 ⟨hx.1.1, hx.2⟩⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_of_mem h0K
    have h3 : 0 < K.card := Finset.card_pos.2 ⟨0, h0K⟩
    omega
  have hKsle : Ks.card ≤ 27 := hSc ▸ Finset.card_le_card hKsS
  have dU : ℓ ∣ 64 - K.card := by
    rw [hUc] at cU
    exact (Nat.modEq_iff_dvd' hKle).1 cU.symm
  have dS : ℓ ∣ 27 - Ks.card := by
    rw [hSc] at cS
    exact (Nat.modEq_iff_dvd' hKsle).1 cS.symm
  have d3U : 3 ∣ 64 - K.card := by
    have := (Nat.modEq_zero_iff_dvd).1 c3U
    rwa [Finset.card_sdiff_of_subset hKU, hUc] at this
  have d3Ks : 3 ∣ Ks.card := (Nat.modEq_zero_iff_dvd).1 c3Ks
  exact false_of_counts hℓ hℓ2 hℓ3 hKdvd hK64 hKle hKsK hKsle dU d3U dS d3Ks

theorem isSolvable_centralizer_of_weight_eq_three (v : Fin 3 → ZMod 3) (hv : weight v = 3) :
    Group.IsSolvable ↥(omega ⊓ Subgroup.centralizer {tor v}) := by
  have hv' := ne_zero_of_weight_eq_three v hv
  have : Finite Aut := Finite.of_injective (fun g : Aut => (g : V2 → V2)) DFunLike.coe_injective
  set C := omega ⊓ Subgroup.centralizer {tor v}
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card C → ℓ = 2 ∨ ℓ = 3 := by
    intro ℓ hℓ hdvd
    by_contra hne
    push Not at hne
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
    have hgO : (g : Aut) ∈ modelO (1 : ZMod 2) 1 := modelOmega_le_modelO 1 1 g.2.1
    have hgc : Commute (g : Aut) (tor v) := Subgroup.mem_centralizer_singleton_iff.1 g.2.2
    exact false_of_prime_orderOf hv' hgO hgc hℓ hne.1 hne.2 (by rw [Subgroup.orderOf_coe, hg])
  have hn : Nat.card C ≠ 0 := Nat.card_pos.ne'
  refine isSolvable_of_natCard_dvd (a := (Nat.card C).factorization 2)
    (b := (Nat.card C).factorization 3) (dvd_of_eq ?_)
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ (s := {2, 3}) ?_ _ (fun _ _ => pow_zero _)]
  · rw [Finset.prod_pair (by norm_num)]
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rcases hprime p hp.1 hp.2.1 with h | h <;> simp [h]

private theorem exists_of_weight_eq_two (v : Fin 3 → ZMod 3) (hv : weight v = 2) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ v i ≠ 0 ∧ v j ≠ 0 ∧ v k = 0 := by
  revert v
  decide

private theorem natCard_toAdd_eq_zero (k : Fin 3) :
    Nat.card {u : Multiplicative (Fin 3 → ZMod 3) // Multiplicative.toAdd u k = 0} = 9 := by
  rw [Nat.card_eq_fintype_card]
  revert k
  decide

theorem card_torus_inf_centralizer_of_weight_eq_two (v : Fin 3 → ZMod 3) (hv : weight v = 2)
    (J : Subgroup Aut) (hJ : J ≤ omega ⊓ Subgroup.centralizer {tor v}) (hJJ : ⁅J, J⁆ = J)
    (hJbot : J ≠ ⊥) :
    Nat.card ↥((cm (ZMod 2)).range ⊓ Subgroup.centralizer (J : Set Aut)) = 9 := by
  obtain ⟨i, j, k, hij, hik, hjk, hvi, hvj, hvk⟩ := exists_of_weight_eq_two v hv
  have h3 := three_ne_zero_two
  have hO : J ≤ modelO (1 : ZMod 2) 1 := hJ.trans (inf_le_left.trans (modelOmega_le_modelO 1 1))
  have hct : ∀ g ∈ J, Commute g (cmEquiv (ZMod 2) v) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJ hg).2
  have hv0 : ∀ l, v l = 0 ↔ l = k := by
    intro l
    refine ⟨fun h => ?_, fun h => h ▸ hvk⟩
    rcases fin_three_eq_or hij hik hjk l with rfl | rfl | rfl
    · exact absurd h hvi
    · exact absurd h hvj
    · rfl
  have := isSolvable_orthogonalGroup_rotForm_two
  have := isSolvable_orthogonalGroup_rotForm_prod_two
  have := isSolvable_orthogonalGroup_wForm_two
  have hPij : ∀ g ∈ J, ∀ w,
      rotPairIncl (ZMod 2) i j (rotPairProj (ZMod 2) i j (g (rotPairIncl (ZMod 2) i j w))) =
        g (rotPairIncl (ZMod 2) i j w) := by
    intro g hg w
    have hx := (cmEquiv_sq_add_eq_zero_iff h3 v (rotPairIncl (ZMod 2) i j w)).mpr
      ⟨by simp [rotPairIncl_apply], fun l hl => by
        rw [(hv0 l).mp hl, rotPairIncl_apply]
        simp [Pi.single_eq_of_ne hik.symm, Pi.single_eq_of_ne hjk.symm]⟩
    obtain ⟨h2, h1⟩ := (cmEquiv_sq_add_eq_zero_iff h3 _ _).mp (sq_add_of_commute (hct g hg) hx)
    refine rotPairIncl_rotPairProj hij h2 fun l hli hlj => h1 l ((hv0 l).mpr ?_)
    rcases fin_three_eq_or hij hik hjk l with h | h | h
    · exact absurd h hli
    · exact absurd h hlj
    · exact h
  have hfixij : ∀ g ∈ J, ∀ w, g (rotPairIncl (ZMod 2) i j w) = rotPairIncl (ZMod 2) i j w :=
    fun g hg w => pairSummandHom_eq_one (map_eq_one_of_commutator_eq_self hJJ
      (pairSummandHom J hO hij hPij) ⟨g, hg⟩) w
  have hfixz : ∀ g ∈ J, ∀ z : V2, z.2 = 0 → z.1 k = 0 → g z = z := by
    intro g hg z h2 hk
    have hz := rotPairIncl_rotPairProj (K := ZMod 2) hij h2 fun l hli hlj => by
      rcases fin_three_eq_or hij hik hjk l with h | h | h
      · exact absurd h hli
      · exact absurd h hlj
      · rw [h]
        exact hk
    rw [← hz]
    exact hfixij g hg _
  have hfixu : ∀ u : Fin 3 → ZMod 3, u k = 0 → ∀ z : V2, z.1 i = 0 → z.1 j = 0 →
      cmEquiv (ZMod 2) u z = z := by
    intro u hu z hzi hzj
    refine (cmEquiv_apply_eq_self_iff h3 u z).mpr fun l hl => ?_
    rcases fin_three_eq_or hij hik hjk l with rfl | rfl | rfl
    · exact hzi
    · exact hzj
    · exact absurd hu hl
  have hcomm : ∀ u : Fin 3 → ZMod 3, u k = 0 → ∀ g ∈ J, Commute g (cmEquiv (ZMod 2) u) := by
    intro u hu g hg
    refine LinearEquiv.ext fun x => ?_
    change g (cmEquiv (ZMod 2) u x) = cmEquiv (ZMod 2) u (g x)
    set P : V2 := (x.1 - Pi.single k (x.1 k), 0) with hP
    set y : V2 := (Pi.single k (x.1 k), x.2) with hy
    have hxPy : x = P + y := by
      refine Prod.ext ?_ ?_ <;> simp [hP, hy]
    have hyi : y.1 i = 0 := Pi.single_eq_of_ne hik _
    have hyj : y.1 j = 0 := Pi.single_eq_of_ne hjk _
    have hgy := (cmEquiv_apply_eq_self_iff h3 v _).mp
      (fix_of_commute (hct g hg) (hfixu v hvk y hyi hyj))
    have hPk : P.1 k = 0 := by simp [hP]
    have hcuPk : (cmEquiv (ZMod 2) u P).1 k = 0 := by
      change rotPow (ZMod 2) (u k) (P.1 k) = 0
      rw [hPk, map_zero]
    rw [hxPy]
    simp only [map_add]
    rw [hfixz g hg _ rfl hcuPk, hfixz g hg P rfl hPk, hfixu u hu y hyi hyj,
      hfixu u hu (g y) (hgy i hvi) (hgy j hvj)]
  have hnot : ∀ u : Fin 3 → ZMod 3, u k ≠ 0 →
      (∀ g ∈ J, Commute g (cmEquiv (ZMod 2) u)) → False := by
    intro u hu hJu
    have hPk : ∀ g ∈ J, ∀ p, rotPlaneIncl (ZMod 2) k (rotPlaneProj (ZMod 2) k
        (g (rotPlaneIncl (ZMod 2) k p))) = g (rotPlaneIncl (ZMod 2) k p) := by
      intro g hg p
      have hx := (cmEquiv_sq_add_eq_zero_iff h3 u (rotPlaneIncl (ZMod 2) k p)).mpr
        ⟨rfl, fun l hl => rotPlaneIncl_apply_of_ne (i := k) (l := l) (fun h => hu (h ▸ hl)) p⟩
      have h2 := ((cmEquiv_sq_add_eq_zero_iff h3 _ _).mp (sq_add_of_commute (hJu g hg) hx)).1
      have hfix := (cmEquiv_apply_eq_self_iff h3 v _).mp (fix_of_commute (hct g hg)
        (hfixu v hvk (rotPlaneIncl (ZMod 2) k p) (rotPlaneIncl_apply_of_ne hik p)
          (rotPlaneIncl_apply_of_ne hjk p)))
      refine rotPlaneIncl_rotPlaneProj h2 fun l hl => ?_
      rcases fin_three_eq_or hij hik hjk l with rfl | rfl | rfl
      · exact hfix _ hvi
      · exact hfix _ hvj
      · exact absurd rfl hl
    have hWk : ∀ g ∈ J, ∀ p,
        LinearMap.inr (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2)
          (LinearMap.snd (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2)
            (g (LinearMap.inr (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) p))) =
          g (LinearMap.inr (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) p) := by
      intro g hg p
      have hf1 := (cmEquiv_apply_eq_self_iff h3 v _).mp
        (fix_of_commute (hct g hg) (hfixu v hvk (LinearMap.inr (ZMod 2) _ _ p) rfl rfl))
      have hf2 := (cmEquiv_apply_eq_self_iff h3 u _).mp (fix_of_commute (hJu g hg)
        ((cmEquiv_apply_eq_self_iff h3 u (LinearMap.inr (ZMod 2) _ _ p)).mpr fun l _ => rfl))
      refine Prod.ext (funext fun l => ?_) rfl
      change (0 : ZMod 2 × ZMod 2) = _
      rcases fin_three_eq_or hij hik hjk l with rfl | rfl | rfl
      · exact (hf1 _ hvi).symm
      · exact (hf1 _ hvj).symm
      · exact (hf2 _ hu).symm
    refine hJbot ((Subgroup.eq_bot_iff_forall J).mpr fun g hg => ?_)
    have e1 := planeSummandHom_eq_one (map_eq_one_of_commutator_eq_self hJJ
      (planeSummandHom J hO k hPk) ⟨g, hg⟩)
    have e3 := wSummandHom_eq_one (map_eq_one_of_commutator_eq_self hJJ (wSummandHom J hO hWk)
      ⟨g, hg⟩)
    refine LinearEquiv.ext fun x => ?_
    change g x = x
    rw [eq_rotPlaneIncl_add_rotPairIncl_add_inr hik.symm hjk.symm hij x]
    simp only [map_add]
    rw [e1, hfixij g hg, e3]
  have hmem : ∀ u : Multiplicative (Fin 3 → ZMod 3),
      cm (ZMod 2) u ∈ Subgroup.centralizer (J : Set Aut) ↔ Multiplicative.toAdd u k = 0 := by
    intro u
    rw [Subgroup.mem_centralizer_iff]
    refine ⟨fun h => ?_, fun hu g hg => hcomm _ hu g hg⟩
    by_contra hu
    exact hnot _ hu fun g hg => h g hg
  have hcard : Nat.card ↥((Subgroup.centralizer (J : Set Aut)).comap (cm (ZMod 2))) = 9 :=
    (Nat.card_congr (Equiv.subtypeEquivRight hmem)).trans (natCard_toAdd_eq_zero k)
  rw [← Subgroup.map_comap_eq, Subgroup.card_map_of_injective cm_injective]
  exact hcard

namespace PlaneCoord

private abbrev V4 : Type := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

private noncomputable def Q4 : QuadraticForm (ZMod 2) V4 :=
  (rotForm (ZMod 2)).prod (wForm (1 : ZMod 2) 1)

private def q4 (v : V4) : ZMod 2 := rotQ v.1 + wQ v.2

private theorem Q4_apply (v : V4) : Q4 v = q4 v := by
  rw [Q4, QuadraticMap.prod_apply, rotForm_two_apply, wForm_two_apply]
  rfl

private def iotaFun (v : V4) : Fin 5 → ZMod 2 :=
  ![v.1.1 + v.2.2, v.1.1 + v.1.2 + v.2.2, v.1.2 + v.2.2, v.2.1, v.2.1 + v.2.2]

private def piFun (z : Fin 5 → ZMod 2) : V4 :=
  ((z 1 + z 2, z 0 + z 1), (z 0 + z 1 + z 2 + z 4, z 3 + z 4))

private theorem iotaFun_add : ∀ x y : V4, iotaFun (x + y) = iotaFun x + iotaFun y := by
  decide +kernel

private theorem iotaFun_smul : ∀ (c : ZMod 2) (x : V4), iotaFun (c • x) = c • iotaFun x := by
  decide +kernel

private def iotaL : V4 →ₗ[ZMod 2] (Fin 5 → ZMod 2) where
  toFun := iotaFun
  map_add' := iotaFun_add
  map_smul' := iotaFun_smul

private def piL : (Fin 5 → ZMod 2) →ₗ[ZMod 2] V4 where
  toFun := piFun
  map_add' x y := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp [piFun] <;> ring
  map_smul' c x := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp [piFun] <;> ring

private def permL (σ : Equiv.Perm (Fin 5)) : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) where
  toFun z a := z (σ.symm a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem piFun_iotaFun : ∀ v : V4, piFun (iotaFun v) = v := by
  decide +kernel

private theorem sum_iotaFun :
    ∀ v : V4, iotaFun v 0 + iotaFun v 1 + iotaFun v 2 + iotaFun v 3 + iotaFun v 4 = 0 := by
  decide +kernel

private theorem iotaFun_piFun_vec : ∀ a b c d e : ZMod 2, a + b + c + d + e = 0 →
    iotaFun (piFun ![a, b, c, d, e]) = ![a, b, c, d, e] := by
  decide +kernel

private theorem vec_eq (z : Fin 5 → ZMod 2) : ![z 0, z 1, z 2, z 3, z 4] = z := by
  funext a
  fin_cases a <;> rfl

private theorem iotaFun_piFun (z : Fin 5 → ZMod 2) (hz : z 0 + z 1 + z 2 + z 3 + z 4 = 0) :
    iotaFun (piFun z) = z := by
  have h := iotaFun_piFun_vec (z 0) (z 1) (z 2) (z 3) (z 4) hz
  rwa [vec_eq z] at h

private theorem sum_comp_iotaFun (τ : Equiv.Perm (Fin 5)) (v : V4) :
    iotaFun v (τ.symm 0) + iotaFun v (τ.symm 1) + iotaFun v (τ.symm 2) + iotaFun v (τ.symm 3) +
      iotaFun v (τ.symm 4) = 0 := by
  have h := Equiv.sum_comp τ.symm (iotaFun v)
  rw [Fin.sum_univ_five, Fin.sum_univ_five] at h
  rw [h]
  exact sum_iotaFun v

private def actL (σ : Equiv.Perm (Fin 5)) : V4 →ₗ[ZMod 2] V4 := piL ∘ₗ permL σ ∘ₗ iotaL

private theorem actL_apply (σ : Equiv.Perm (Fin 5)) (v : V4) :
    actL σ v = piFun fun a => iotaFun v (σ.symm a) := rfl

private theorem actL_one : actL 1 = LinearMap.id :=
  LinearMap.ext fun v => piFun_iotaFun v

private theorem actL_mul (σ τ : Equiv.Perm (Fin 5)) : actL (σ * τ) = actL σ ∘ₗ actL τ := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, actL_apply, actL_apply, actL_apply,
    iotaFun_piFun (fun b => iotaFun v (τ.symm b)) (sum_comp_iotaFun τ v)]
  rfl

private def gEquiv (σ : Equiv.Perm (Fin 5)) : V4 ≃ₗ[ZMod 2] V4 :=
  LinearEquiv.ofLinearMap (actL σ) (actL σ⁻¹)
    (by rw [← actL_mul, mul_inv_cancel, actL_one])
    (by rw [← actL_mul, inv_mul_cancel, actL_one])

private def gHom : Equiv.Perm (Fin 5) →* (V4 ≃ₗ[ZMod 2] V4) where
  toFun := gEquiv
  map_one' := LinearEquiv.ext fun v => by
    change actL 1 v = v
    rw [actL_one, LinearMap.id_apply]
  map_mul' σ τ := LinearEquiv.ext fun v => by
    change actL (σ * τ) v = actL σ (actL τ v)
    rw [actL_mul, LinearMap.comp_apply]

private theorem gHom_apply (σ : Equiv.Perm (Fin 5)) (v : V4) :
    gHom σ v = piFun fun a => iotaFun v (σ.symm a) := rfl

private theorem q4_act_swap : ∀ a b : Fin 5, ∀ v : V4,
    q4 (piFun fun c => iotaFun v ((Equiv.swap a b).symm c)) = q4 v := by
  decide +kernel

private theorem gHom_mem_orthogonalGroup (σ : Equiv.Perm (Fin 5)) :
    gHom σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q4 := by
  have h : Subgroup.closure {τ : Equiv.Perm (Fin 5) | τ.IsSwap} ≤
      (TauCeti.QuadraticMap.orthogonalGroup Q4).comap gHom := by
    rw [Subgroup.closure_le]
    rintro τ ⟨a, b, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [Q4_apply, Q4_apply, gHom_apply]
    exact q4_act_swap a b v
  rw [Equiv.Perm.closure_isSwap] at h
  exact h (Subgroup.mem_top σ)

private def rhoW : V4 ≃ₗ[ZMod 2] V4 :=
  (rotLE (ZMod 2)).prodCongr (LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2))

private theorem rhoW_apply (v : V4) : rhoW v = (rotLE (ZMod 2) v.1, v.2) := rfl

private def c3 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 0 1

private def c2 : Equiv.Perm (Fin 5) := Equiv.swap 2 4 * Equiv.swap 2 3

private theorem c3_mem : c3 ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨0, 2, by decide, rfl⟩ ⟨0, 1, by decide, rfl⟩

private theorem c2_mem : c2 ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨2, 4, by decide, rfl⟩ ⟨2, 3, by decide, rfl⟩

private theorem act_c3 :
    ∀ v : V4, (piFun fun a => iotaFun v (c3.symm a)) = ((-v.1.2, v.1.1 - v.1.2), v.2) := by
  decide +kernel

private theorem gHom_c3 : gHom c3 = rhoW := by
  refine LinearEquiv.ext fun v => ?_
  rw [gHom_apply, act_c3 v]
  rfl

private theorem act_noncomm :
    (piFun fun a => iotaFun (piFun fun b => iotaFun (((1, 0), (0, 0)) : V4) (c2.symm b))
        (c3.symm a)) ≠
      piFun fun a => iotaFun (piFun fun b => iotaFun (((1, 0), (0, 0)) : V4) (c3.symm b))
        (c2.symm a) := by
  decide +kernel

private theorem gHom_c3_c2 : gHom c3 * gHom c2 ≠ gHom c2 * gHom c3 := fun h =>
  act_noncomm (DFunLike.congr_fun h ((1, 0), (0, 0)))

private def prK (k : Fin 3) : V2 →ₗ[ZMod 2] V4 :=
  (LinearMap.proj k ∘ₗ LinearMap.fst (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2)).prod
    (LinearMap.snd (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2))

private theorem prK_apply (k : Fin 3) (x : V2) : prK k x = (x.1 k, x.2) := rfl

private def extK (k : Fin 3) (h : V4 ≃ₗ[ZMod 2] V4) : Aut where
  toFun x := (Function.update x.1 k (h (prK k x)).1, (h (prK k x)).2)
  invFun x := (Function.update x.1 k (h.symm (prK k x)).1, (h.symm (prK k x)).2)
  map_add' x y := by
    simp only [map_add, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Function.update_add]
  map_smul' c x := by
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, Function.update_smul,
      RingHom.id_apply]
  left_inv x := by
    simp only [prK_apply, Function.update_self, Prod.mk.eta, LinearEquiv.symm_apply_apply,
      Function.update_idem, Function.update_eq_self]
  right_inv x := by
    simp only [prK_apply, Function.update_self, Prod.mk.eta, LinearEquiv.apply_symm_apply,
      Function.update_idem, Function.update_eq_self]

private theorem extK_apply (k : Fin 3) (h : V4 ≃ₗ[ZMod 2] V4) (x : V2) :
    extK k h x = (Function.update x.1 k (h (x.1 k, x.2)).1, (h (x.1 k, x.2)).2) := rfl

private theorem extK_fst_self (k : Fin 3) (h : V4 ≃ₗ[ZMod 2] V4) (x : V2) :
    (extK k h x).1 k = (h (x.1 k, x.2)).1 := by
  rw [extK_apply]
  exact Function.update_self _ _ _

private theorem extK_fst_of_ne {i k : Fin 3} (hi : i ≠ k) (h : V4 ≃ₗ[ZMod 2] V4) (x : V2) :
    (extK k h x).1 i = x.1 i := by
  rw [extK_apply]
  exact Function.update_of_ne hi _ _

private theorem extK_snd (k : Fin 3) (h : V4 ≃ₗ[ZMod 2] V4) (x : V2) :
    (extK k h x).2 = (h (x.1 k, x.2)).2 := rfl

private def extHom (k : Fin 3) : (V4 ≃ₗ[ZMod 2] V4) →* Aut where
  toFun := extK k
  map_one' := LinearEquiv.ext fun x => by
    refine Prod.ext (funext fun i => ?_) ?_
    · by_cases hi : i = k
      · subst hi
        rw [extK_fst_self]
        rfl
      · rw [extK_fst_of_ne hi]
        rfl
    · rw [extK_snd]
      rfl
  map_mul' h₁ h₂ := LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply]
    refine Prod.ext (funext fun i => ?_) ?_
    · by_cases hi : i = k
      · subst hi
        simp only [extK_fst_self, extK_snd, LinearEquiv.mul_apply, Prod.mk.eta]
      · simp only [extK_fst_of_ne hi]
    · simp only [extK_fst_self, extK_snd, LinearEquiv.mul_apply, Prod.mk.eta]

private theorem extK_injective (k : Fin 3) : Function.Injective (extK k) := by
  intro h h' hh
  refine LinearEquiv.ext fun v => ?_
  have e1 := congrArg (fun e : Aut => (e (Pi.single k v.1, v.2)).1 k) hh
  have e2 := congrArg (fun e : Aut => (e (Pi.single k v.1, v.2)).2) hh
  simp only [extK_fst_self, extK_snd, Pi.single_eq_same, Prod.mk.eta] at e1 e2
  exact Prod.ext e1 e2

private theorem extK_mem_modelO (k : Fin 3) {h : V4 ≃ₗ[ZMod 2] V4}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q4) : extK k h ∈ modelO (1 : ZMod 2) 1 := by
  rw [modelO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  have key := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hh (x.1 k, x.2)
  simp only [Q4, QuadraticMap.prod_apply] at key
  rw [modelForm_apply, modelForm_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hs : ∑ i ∈ Finset.univ.erase k, rotForm (ZMod 2) ((extK k h x).1 i) =
      ∑ i ∈ Finset.univ.erase k, rotForm (ZMod 2) (x.1 i) :=
    Finset.sum_congr rfl fun i hi => by rw [extK_fst_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hs, extK_fst_self, extK_snd]
  linear_combination key

private theorem tor_fst (v : Fin 3 → ZMod 3) (y : V2) (i : Fin 3) :
    (tor v y).1 i = rotPow (ZMod 2) (v i) (y.1 i) := rfl

private theorem tor_snd (v : Fin 3 → ZMod 3) (y : V2) : (tor v y).2 = y.2 := rfl

private theorem rotPow_zero_apply' : ∀ p : ZMod 2 × ZMod 2, rotPow (ZMod 2) 0 p = p := by
  decide +kernel

private theorem rotPow_one_apply' :
    ∀ p : ZMod 2 × ZMod 2, rotPow (ZMod 2) 1 p = rotLE (ZMod 2) p := by
  decide +kernel

private theorem extK_commute_tor (k : Fin 3) (h : V4 ≃ₗ[ZMod 2] V4) {v : Fin 3 → ZMod 3}
    (hv : v k = 0) : Commute (extK k h) (tor v) := by
  have hk : ∀ y : V2, (tor v y).1 k = y.1 k := fun y => by
    rw [tor_fst, hv, rotPow_zero_apply']
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  refine Prod.ext (funext fun i => ?_) ?_
  · by_cases hi : i = k
    · subst hi
      simp only [extK_fst_self, hk, tor_snd]
    · simp only [extK_fst_of_ne hi, tor_fst]
  · simp only [extK_snd, tor_snd, hk]

private theorem extK_rhoW (k : Fin 3) : extK k rhoW = tor (Pi.single k 1) := by
  refine LinearEquiv.ext fun x => Prod.ext (funext fun i => ?_) ?_
  · by_cases hi : i = k
    · subst hi
      simp only [extK_fst_self, rhoW_apply, tor_fst, Pi.single_eq_same, rotPow_one_apply']
    · simp only [extK_fst_of_ne hi, tor_fst, Pi.single_eq_of_ne hi, rotPow_zero_apply']
  · simp only [extK_snd, rhoW_apply, tor_snd]

private theorem tor_single_ne_one (k : Fin 3) : tor (Pi.single k 1) ≠ 1 := by
  intro h
  have h1 : cm (ZMod 2) (Multiplicative.ofAdd (Pi.single k (1 : ZMod 3))) = cm (ZMod 2) 1 := by
    rw [map_one]
    exact h
  have h2 := congrArg (fun w : Multiplicative (Fin 3 → ZMod 3) => Multiplicative.toAdd w k)
    (cm_injective h1)
  simp at h2

private def fHom (k : Fin 3) : Equiv.Perm (Fin 5) →* Aut := (extHom k).comp gHom

private theorem fHom_apply (k : Fin 3) (σ : Equiv.Perm (Fin 5)) : fHom k σ = extK k (gHom σ) :=
  rfl

private theorem tor_mem_X (k : Fin 3) :
    tor (Pi.single k 1) ∈ (alternatingGroup (Fin 5)).map (fHom k) :=
  ⟨c3, c3_mem, by rw [fHom_apply, gHom_c3, extK_rhoW]⟩

private theorem X_le_omega (k : Fin 3) : (alternatingGroup (Fin 5)).map (fHom k) ≤ omega := by
  have hX : (alternatingGroup (Fin 5)).map (fHom k) ≤ modelO (1 : ZMod 2) 1 := by
    rintro _ ⟨σ, -, rfl⟩
    exact extK_mem_modelO k (gHom_mem_orthogonalGroup σ)
  have hA : ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ = alternatingGroup (Fin 5) :=
    commutator_alternatingGroup_eq_self (by simp)
  calc (alternatingGroup (Fin 5)).map (fHom k)
      = ⁅(alternatingGroup (Fin 5)).map (fHom k), (alternatingGroup (Fin 5)).map (fHom k)⁆ := by
        rw [← Subgroup.map_commutator, hA]
    _ ≤ ⁅modelO (1 : ZMod 2) 1, modelO (1 : ZMod 2) 1⁆ := Subgroup.commutator_mono hX hX

private theorem X_le_centralizer {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) :
    (alternatingGroup (Fin 5)).map (fHom k) ≤
      Subgroup.centralizer {tor (Pi.single i 1), tor (Pi.single j 1)} := by
  rintro _ ⟨σ, -, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro y (rfl | rfl)
  · exact (extK_commute_tor k (gHom σ) (v := Pi.single i 1)
      (by rw [Pi.single_eq_of_ne hik.symm])).eq.symm
  · exact (extK_commute_tor k (gHom σ) (v := Pi.single j 1)
      (by rw [Pi.single_eq_of_ne hjk.symm])).eq.symm

private theorem isSimpleGroup_X (k : Fin 3) :
    IsSimpleGroup ↥((alternatingGroup (Fin 5)).map (fHom k)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : Nontrivial ↥((alternatingGroup (Fin 5)).map (fHom k)) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have hmem := tor_mem_X k
    rw [hbot, Subgroup.mem_bot] at hmem
    exact tor_single_ne_one k hmem
  exact IsSimpleGroup.isSimpleGroup_of_surjective ((fHom k).subgroupMap _)
    ((fHom k).subgroupMap_surjective _)

private theorem X_nonabelian (k : Fin 3) :
    ∃ a b : ↥((alternatingGroup (Fin 5)).map (fHom k)), a * b ≠ b * a := by
  refine ⟨⟨fHom k c3, c3, c3_mem, rfl⟩, ⟨fHom k c2, c2, c2_mem, rfl⟩, fun h => ?_⟩
  have h' : fHom k c3 * fHom k c2 = fHom k c2 * fHom k c3 := congrArg Subtype.val h
  rw [← map_mul, ← map_mul, fHom_apply, fHom_apply] at h'
  apply gHom_c3_c2
  rw [← map_mul, ← map_mul]
  exact extK_injective k h'

end PlaneCoord

theorem exists_simple_le_centralizer_coord_pair (i j k : Fin 3) (_hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ X : Subgroup Aut,
      X ≤ omega ⊓ Subgroup.centralizer {tor (Pi.single i 1), tor (Pi.single j 1)} ∧
      IsSimpleGroup ↥X ∧ (∃ a b : ↥X, a * b ≠ b * a) ∧ tor (Pi.single k 1) ∈ X :=
  ⟨(alternatingGroup (Fin 5)).map (PlaneCoord.fHom k),
    le_inf (PlaneCoord.X_le_omega k) (PlaneCoord.X_le_centralizer hik hjk),
    PlaneCoord.isSimpleGroup_X k, PlaneCoord.X_nonabelian k, PlaneCoord.tor_mem_X k⟩

theorem isSolvable_centralizer_mixed_pair (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (s : ZMod 3) (hs : s ≠ 0) :
    Group.IsSolvable ↥(omega ⊓ Subgroup.centralizer
      {tor (Pi.single i 1), tor (Pi.single j 1 + s • Pi.single k 1)}) := by
  have h3 := three_ne_zero_two
  set G := omega ⊓ Subgroup.centralizer
    {tor (Pi.single i 1), tor (Pi.single j 1 + s • Pi.single k 1)}
  have hO : G ≤ modelO (1 : ZMod 2) 1 := inf_le_left.trans (modelOmega_le_modelO 1 1)
  have hc1 : ∀ g ∈ G, Commute g (cmEquiv (ZMod 2) (Pi.single i 1)) := fun g hg =>
    ((Subgroup.mem_centralizer_iff.mp hg.2) _ (Set.mem_insert _ _)).symm
  have hc2 : ∀ g ∈ G, Commute g (cmEquiv (ZMod 2) (Pi.single j 1 + s • Pi.single k 1)) :=
    fun g hg => ((Subgroup.mem_centralizer_iff.mp hg.2) _ (Set.mem_insert_of_mem _ rfl)).symm
  have hv1 : ∀ l, (Pi.single i 1 : Fin 3 → ZMod 3) l = 0 ↔ l ≠ i := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [hl]
  have hv2 : ∀ l, (Pi.single j 1 + s • Pi.single k 1 : Fin 3 → ZMod 3) l = 0 ↔ l = i := by
    intro l
    rcases fin_three_eq_or hij hik hjk l with rfl | rfl | rfl
    · simp [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
    · simp [Pi.single_eq_of_ne hjk, hij.symm]
    · simp [Pi.single_eq_of_ne hjk.symm, hs, hik.symm]
  have hPi : ∀ g ∈ G, ∀ p,
      rotPlaneIncl (ZMod 2) i (rotPlaneProj (ZMod 2) i (g (rotPlaneIncl (ZMod 2) i p))) =
        g (rotPlaneIncl (ZMod 2) i p) := by
    intro g hg p
    have hx := (cmEquiv_sq_add_eq_zero_iff h3 (Pi.single i 1) (rotPlaneIncl (ZMod 2) i p)).mpr
      ⟨rfl, fun l hl => rotPlaneIncl_apply_of_ne ((hv1 l).mp hl) p⟩
    obtain ⟨h2, h1⟩ := (cmEquiv_sq_add_eq_zero_iff h3 _ _).mp (sq_add_of_commute (hc1 g hg) hx)
    exact rotPlaneIncl_rotPlaneProj h2 fun l hl => h1 l ((hv1 l).mpr hl)
  have hPjk : ∀ g ∈ G, ∀ w,
      rotPairIncl (ZMod 2) j k (rotPairProj (ZMod 2) j k (g (rotPairIncl (ZMod 2) j k w))) =
        g (rotPairIncl (ZMod 2) j k w) := by
    intro g hg w
    have hx := (cmEquiv_sq_add_eq_zero_iff h3 (Pi.single j 1 + s • Pi.single k 1)
      (rotPairIncl (ZMod 2) j k w)).mpr ⟨by simp [rotPairIncl_apply], fun l hl => by
        rw [(hv2 l).mp hl, rotPairIncl_apply]
        simp [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]⟩
    obtain ⟨h2, h1⟩ := (cmEquiv_sq_add_eq_zero_iff h3 _ _).mp (sq_add_of_commute (hc2 g hg) hx)
    refine rotPairIncl_rotPairProj hjk h2 fun l hlj hlk => h1 l ((hv2 l).mpr ?_)
    rcases fin_three_eq_or hij hik hjk l with h | h | h
    · exact h
    · exact absurd h hlj
    · exact absurd h hlk
  have hW : ∀ g ∈ G, ∀ p,
      LinearMap.inr (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2)
        (LinearMap.snd (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2)
          (g (LinearMap.inr (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) p))) =
        g (LinearMap.inr (ZMod 2) (Fin 3 → ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) p) := by
    intro g hg p
    have hg1 := (cmEquiv_apply_eq_self_iff h3 _ _).mp (fix_of_commute (hc1 g hg)
      ((cmEquiv_apply_eq_self_iff h3 _ (LinearMap.inr (ZMod 2) _ _ p)).mpr fun l _ => rfl))
    have hg2 := (cmEquiv_apply_eq_self_iff h3 _ _).mp (fix_of_commute (hc2 g hg)
      ((cmEquiv_apply_eq_self_iff h3 _ (LinearMap.inr (ZMod 2) _ _ p)).mpr fun l _ => rfl))
    refine Prod.ext (funext fun l => ?_) rfl
    change (0 : ZMod 2 × ZMod 2) = _
    by_cases hl : l = i
    · subst hl
      exact (hg1 _ (by simp)).symm
    · exact (hg2 l (mt (hv2 l).mp hl)).symm
  have := isSolvable_orthogonalGroup_rotForm_two
  have := isSolvable_orthogonalGroup_rotForm_prod_two
  have := isSolvable_orthogonalGroup_wForm_two
  have hinj : Function.Injective
      ((planeSummandHom G hO i hPi).prod
        ((pairSummandHom G hO hjk hPjk).prod (wSummandHom G hO hW))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have e1 := planeSummandHom_eq_one (congrArg Prod.fst hg)
    have e2 := pairSummandHom_eq_one (congrArg (fun x => x.2.1) hg)
    have e3 := wSummandHom_eq_one (congrArg (fun x => x.2.2) hg)
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    change (g : Aut) x = x
    rw [eq_rotPlaneIncl_add_rotPairIncl_add_inr hij hik hjk x]
    simp only [map_add, e1, e2, e3]
  exact Group.isSolvable_of_isSolvable_injective hinj

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.Two
