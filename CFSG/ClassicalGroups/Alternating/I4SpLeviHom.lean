module

public import CFSG.ClassicalGroups.Alternating.I4SpLevi
public import CFSG.ClassicalGroups.Alternating.RT1SpFaithful

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

section GL2

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A]

lemma exists_eq_smul_add_smul_of_comm (hA : finrank K A = 2) {N : A →ₗ[K] A}
    (hNN : ∀ x, N (N x) = 0) (hN0 : N ≠ 0) {f : A →ₗ[K] A} (hf : ∀ x, f (N x) = N (f x)) :
    ∃ α β : K, ∀ x, f x = α • x + β • N x := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, N x₀ ≠ 0 := by
    by_contra hcon
    exact hN0 (LinearMap.ext fun x => not_not.mp fun hx => hcon ⟨x, hx⟩)
  have hli : LinearIndependent K ![x₀, N x₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs' : s • N x₀ = 0 := by
      have h := congrArg N hst
      simpa [map_add, map_smul, hNN] using h
    have hs : s = 0 := by
      rcases smul_eq_zero.mp hs' with h | h
      · exact h
      · exact absurd h hx₀
    subst hs
    have ht : t • N x₀ = 0 := by simpa using hst
    rcases smul_eq_zero.mp ht with h | h
    · exact ⟨rfl, h⟩
    · exact absurd h hx₀
  let b : Basis (Fin 2) K A := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hA])
  have hb0 : b 0 = x₀ := by simp [b]
  have hb1 : b 1 = N x₀ := by simp [b]
  obtain ⟨α, β, hfx₀⟩ : ∃ α β : K, f x₀ = α • x₀ + β • N x₀ :=
    ⟨b.repr (f x₀) 0, b.repr (f x₀) 1, by
      have h := b.sum_repr (f x₀)
      rw [Fin.sum_univ_two, hb0, hb1] at h
      exact h.symm⟩
  have hfy : f (N x₀) = α • N x₀ := by
    rw [hf x₀, hfx₀]
    simp [map_add, map_smul, hNN]
  have hfeq : f = α • LinearMap.id + β • N := by
    apply b.ext
    intro i
    fin_cases i
    · simp [hb0, hfx₀]
    · simp [hb1, hfy, hNN]
  refine ⟨α, β, fun x => ?_⟩
  have h := LinearMap.congr_fun hfeq x
  simpa using h

theorem commute_of_commute_of_mul_self [CharP K 2] (hA : finrank K A = 2) {u v w : A ≃ₗ[K] A}
    (hu : u * u = 1) (hu1 : u ≠ 1) (hv : Commute v u) (hw : Commute w u) : Commute v w := by
  have hu2 : ∀ x, u (u x) = x := fun x => by
    have h := congrArg (fun g : A ≃ₗ[K] A => g x) hu
    simpa using h
  have hchar : ∀ x : A, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  obtain ⟨N, hN⟩ : ∃ N : A →ₗ[K] A, N = (u : A →ₗ[K] A) - LinearMap.id := ⟨_, rfl⟩
  have hNx : ∀ x, N x = u x - x := fun x => by
    rw [hN]
    rfl
  have hNN : ∀ x, N (N x) = 0 := fun x => by
    rw [hNx (N x), hNx x, map_sub, hu2]
    have e : x - u x - (u x - x) = (x + x) - (u x + u x) := by abel
    rw [e, hchar, hchar, sub_self]
  have hN0 : N ≠ 0 := by
    intro h0
    apply hu1
    apply LinearEquiv.ext
    intro x
    have h := LinearMap.congr_fun h0 x
    rw [hNx, LinearMap.zero_apply, sub_eq_zero] at h
    simpa using h
  have hcomm : ∀ f : A ≃ₗ[K] A, Commute f u → ∀ x, f (N x) = N (f x) := by
    intro f hf x
    have hf' : f * u = u * f := hf
    have h : ∀ y, f (u y) = u (f y) := fun y => by
      have h' := congrArg (fun g : A ≃ₗ[K] A => g y) hf'
      simpa using h'
    rw [hNx, hNx, map_sub, h]
  obtain ⟨α, β, hα⟩ := exists_eq_smul_add_smul_of_comm hA hNN hN0
    (f := (v : A →ₗ[K] A)) (hcomm v hv)
  obtain ⟨α', β', hα'⟩ := exists_eq_smul_add_smul_of_comm hA hNN hN0
    (f := (w : A →ₗ[K] A)) (hcomm w hw)
  have hα_v : ∀ x, v x = α • x + β • N x := hα
  have hα_w : ∀ x, w x = α' • x + β' • N x := hα'
  show v * w = w * v
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply, hα_v, hα_w, map_add, map_smul, hNN, smul_add, smul_smul,
    smul_zero, add_zero]
  module

theorem eq_one_of_comm_target {L M : Type*} [Group L] [IsSimpleGroup L] {x y : L}
    (hxy : x * y ≠ y * x) [CommGroup M] (f : L →* M) : f = 1 := by
  rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with h | h
  · exfalso
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp h
    apply hxy
    apply hinj
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · ext g
    have hg : g ∈ f.ker := by
      rw [h]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp hg

theorem eq_one_of_mul_char {L : Type*} [Group L] [IsSimpleGroup L] {x y : L}
    (hxy : x * y ≠ y * x) (c : L → K) (hmul : ∀ g h : L, c (g * h) = c g * c h)
    (hne : ∀ g : L, c g ≠ 0) (g : L) : c g = 1 := by
  have hf : MonoidHom.mk' (fun g => Units.mk0 (c g) (hne g))
      (fun g h => Units.ext (by simpa using hmul g h)) = 1 :=
    eq_one_of_comm_target hxy _
  have h1 := congrArg (fun φ : L →* Kˣ => (φ g : K)) hf
  simpa using h1

theorem hom_eq_one_of_invariant_line {L : Type*} [Group L] [IsSimpleGroup L] {x y : L}
    (hxy : x * y ≠ y * x) (hA : finrank K A = 2) (ρ : L →* (A ≃ₗ[K] A)) {v : A} (hv : v ≠ 0)
    (hinv : ∀ g : L, ∃ s : K, ρ g v = s • v) : ρ = 1 := by
  choose χ hχ using hinv
  have hχne : ∀ g : L, χ g ≠ 0 := by
    intro g h0
    apply hv
    have h1 : ρ g v = 0 := by rw [hχ g, h0, zero_smul]
    exact (ρ g).map_eq_zero_iff.mp h1
  have hχmul : ∀ g h : L, χ (g * h) = χ g * χ h := by
    intro g h
    refine smul_left_injective K hv ?_
    show χ (g * h) • v = (χ g * χ h) • v
    rw [← hχ (g * h), map_mul, LinearEquiv.mul_apply, hχ h, map_smul, hχ g, smul_smul,
      mul_comm]
  have hχone : ∀ g : L, χ g = 1 := eq_one_of_mul_char hxy χ hχmul hχne
  have hρv : ∀ g : L, ρ g v = v := fun g => by rw [hχ g, hχone g, one_smul]
  have h1A : 1 < finrank K A := by rw [hA]; norm_num
  obtain ⟨w, hw⟩ := exists_linearIndependent_pair_of_one_lt_finrank h1A hv
  have hpair : ∀ s t : K, s • v + t • w = 0 → s = 0 ∧ t = 0 :=
    LinearIndependent.pair_iff.mp hw
  have hgen : ∀ a : A, ∃ c d : K, c • v + d • w = a := by
    have hspan : Submodule.span K (Set.range ![v, w]) = ⊤ :=
      hw.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hA])
    have hr : Set.range ![v, w] = ({v, w} : Set A) := by
      ext z
      simp [or_comm]
    intro a
    have ha : a ∈ Submodule.span K ({v, w} : Set A) := by
      rw [← hr, hspan]
      exact Submodule.mem_top
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp ha
    exact ⟨c, d, hcd⟩
  have hgen' : ∀ g : L, ∃ c d : K, c • v + d • w = ρ g w := fun g => hgen _
  choose β α hαβ using hgen'
  have hanti : ∀ g h : L, α (g * h) = α h * α g := by
    intro g h
    have key : β (g * h) • v + α (g * h) • w
        = (β h * χ g + α h * β g) • v + (α h * α g) • w := by
      rw [hαβ (g * h), map_mul, LinearEquiv.mul_apply, ← hαβ h, map_add, map_smul, map_smul,
        hχ g, ← hαβ g]
      module
    have hz := hpair (β (g * h) - (β h * χ g + α h * β g)) (α (g * h) - α h * α g)
      (by linear_combination (norm := module) key)
    exact sub_eq_zero.mp hz.2
  have hα1 : α 1 = 1 := by
    have hr1 : ρ 1 w = w := by simp
    have h1 : β 1 • v + (α 1 - 1) • w = 0 := by
      linear_combination (norm := module) hαβ 1 + hr1
    exact sub_eq_zero.mp (hpair _ _ h1).2
  have hαne : ∀ g : L, α g ≠ 0 := by
    intro g h0
    have h2 := hanti g g⁻¹
    rw [mul_inv_cancel, hα1, h0, mul_zero] at h2
    exact one_ne_zero h2
  have hαone : ∀ g : L, α g = 1 :=
    eq_one_of_mul_char hxy α (fun g h => by rw [hanti g h, mul_comm]) hαne
  have hρw : ∀ g : L, ρ g w = β g • v + w := fun g => by
    rw [← hαβ g, hαone g, one_smul]
  have hF2 : ∀ (g : L) (a : A), ∃ t : K, ρ g a = a + t • v := by
    intro g a
    obtain ⟨c, d, rfl⟩ := hgen a
    refine ⟨d * β g, ?_⟩
    rw [map_add, map_smul, map_smul, hρv g, hρw g]
    module
  have hcomm : ∀ (g h : L) (a : A), ρ g (ρ h a) = ρ h (ρ g a) := by
    intro g h a
    obtain ⟨t1, ht1⟩ := hF2 h a
    obtain ⟨t2, ht2⟩ := hF2 g a
    have e1 : ρ g (ρ h a) = ρ g a + t1 • v := by
      rw [ht1, map_add, map_smul, hρv g]
    have e2 : ρ h (ρ g a) = ρ h a + t2 • v := by
      rw [ht2, map_add, map_smul, hρv h]
    rw [e1, e2, ht1, ht2]
    abel
  have hker : ρ.ker = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ρ.ker with h | h
    · exfalso
      have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp h
      apply hxy
      apply hinj
      rw [map_mul, map_mul]
      ext a
      exact hcomm x y a
    · exact h
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ ρ.ker := by
    rw [hker]
    exact Subgroup.mem_top g
  rw [MonoidHom.one_apply]
  exact MonoidHom.mem_ker.mp hg

end GL2

section Pair

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem exists_pair_orthogonal_of_four_le {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (hdim : 4 ≤ finrank K V) {n : V} (hn : n ≠ 0) :
    ∃ e f : V, B n e = 0 ∧ B n f = 0 ∧ B e f ≠ 0 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (B n)
  have hr : finrank K (LinearMap.range (B n)) ≤ 1 := by
    have h := Submodule.finrank_le (LinearMap.range (B n))
    rwa [Module.finrank_self] at h
  have h2 : 2 ≤ finrank K (LinearMap.ker (B n)) := by omega
  have hnZ : n ∈ LinearMap.ker (B n) := LinearMap.mem_ker.mpr (hB.self_eq_zero n)
  obtain ⟨e, heZ, hli⟩ := exists_mem_linearIndependent_pair h2 hnZ hn
  obtain ⟨f, hf⟩ := exists_apply_eq_of_linearIndependent hBnd hli ![0, 1]
  have hfn : B f n = 0 := by simpa using hf 0
  have hfe : B f e = 1 := by simpa using hf 1
  refine ⟨e, f, LinearMap.mem_ker.mp heZ, ?_, ?_⟩
  · rw [← hB.neg_eq f n, hfn, neg_zero]
  · intro h
    rw [← hB.neg_eq f e, hfe] at h
    exact one_ne_zero (neg_eq_zero.mp h)

end Pair

section Hom

variable {K : Type} [Field K] [CharP K 2] {N : Type*} [AddCommGroup N] [Module K N]
  [FiniteDimensional K N] {BN : BilinForm K N} (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
  {ℓ H : Submodule K N} (hH : IsLeviSpace BN ℓ H)

omit [FiniteDimensional K N] in
include hBN hBNnd in
theorem not_commute_Tsp_of_form_ne_zero {e f : N} (hef : BN e f ≠ 0) :
    Tsp hBN e 1 * Tsp hBN f 1 ≠ Tsp hBN f 1 * Tsp hBN e 1 := by
  intro h
  have h1 : Tsp hBN e 1 * Tsp hBN f 1 * (Tsp hBN e 1)⁻¹ = Tsp hBN f 1 := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [Tsp_conj] at h1
  have h2 := Tsp_injective_one hBN hBNnd h1
  rw [Tsp_app] at h2
  have he0 : e ≠ 0 := fun h0 => hef (by rw [h0, map_zero, LinearMap.zero_apply])
  have hfe : BN f e ≠ 0 := fun h0 => hef (hBN.eq_iff.mpr h0)
  have h3 : (1 * BN f e) • e = 0 := by simpa using h2
  exact hfe (by simpa using (smul_eq_zero.mp h3).resolve_right he0)

omit [CharP K 2] [FiniteDimensional K N] in
include hBN in
theorem Tsp_mem_leviGroup {w : N} (hw : w ∈ BN.orthogonal H) (c : K) :
    Tsp hBN w c ∈ leviGroup BN H :=
  leviRoot_le_leviGroup hBN hw ((mem_leviRoot_iff hBN).mpr ⟨c, rfl⟩)

variable (hq : 4 ≤ Nat.card K)

include hBN hBNnd hq hH in
theorem isSimpleGroup_leviGroup (hdim : 6 ≤ finrank K N) : IsSimpleGroup (leviGroup BN H) := by
  have h2 : 2 ≤ finrank K ↥(BN.orthogonal H) := by
    rw [hH.finrank_orthogonal hBNnd]
    omega
  have := isSimpleGroup_Gsp hq (isAlt_restrict hBN _)
    (hH.restrict_orthogonal_nondegenerate hBN hBNnd) h2
  exact (leviEquiv hBN hH).symm.isSimpleGroup

include hBN hBNnd hq hH in
theorem levi_hom_eq_one_or_injective (hdim : 6 ≤ finrank K N) {G : Type*} [Group G]
    (ρ : leviGroup BN H →* G) : ρ = 1 ∨ Function.Injective ρ := by
  have := isSimpleGroup_leviGroup hBN hBNnd hH hq hdim
  rcases Subgroup.Normal.eq_bot_or_eq_top ρ.ker with h | h
  · exact Or.inr ((MonoidHom.ker_eq_bot_iff ρ).mp h)
  · refine Or.inl (MonoidHom.ext fun g => ?_)
    have : g ∈ ρ.ker := h ▸ Subgroup.mem_top g
    simpa using this

include hBN hBNnd hq hH in
theorem levi_hom_eq_one_of_eight_le (hdim : 8 ≤ finrank K N) {A : Type*} [AddCommGroup A]
    [Module K A] (hA : finrank K A = 2) (ρ : leviGroup BN H →* (A ≃ₗ[K] A)) : ρ = 1 := by
  rcases levi_hom_eq_one_or_injective hBN hBNnd hH hq (by omega) ρ with h | hinj
  · exact h
  exfalso
  have hWdim : 4 ≤ finrank K ↥(BN.orthogonal H) := by
    rw [hH.finrank_orthogonal hBNnd]
    omega
  have hWpos : 0 < finrank K ↥(BN.orthogonal H) := by omega
  have : Nontrivial ↥(BN.orthogonal H) := Module.nontrivial_of_finrank_pos hWpos
  obtain ⟨n, hn⟩ := exists_ne (0 : ↥(BN.orthogonal H))
  obtain ⟨e, f, hne, hnf, hef⟩ := exists_pair_orthogonal_of_four_le (isAlt_restrict hBN _)
    (hH.restrict_orthogonal_nondegenerate hBN hBNnd) hWdim hn
  have hn0 : (n : N) ≠ 0 := fun h => hn (Subtype.ext h)
  have hen : BN (e : N) (n : N) = 0 := hBN.eq_iff.mp hne
  have hfn : BN (f : N) (n : N) = 0 := hBN.eq_iff.mp hnf
  let Tn : leviGroup BN H := ⟨Tsp hBN (n : N) 1, Tsp_mem_leviGroup hBN n.2 1⟩
  let Te : leviGroup BN H := ⟨Tsp hBN (e : N) 1, Tsp_mem_leviGroup hBN e.2 1⟩
  let Tf : leviGroup BN H := ⟨Tsp hBN (f : N) 1, Tsp_mem_leviGroup hBN f.2 1⟩
  have hTn2 : Tn * Tn = 1 := Subtype.ext (Tsp_mul_self hBN _ _)
  have hTn1 : Tn ≠ 1 := fun h => by
    rcases (Tsp_eq_one_iff hBN hBNnd (n : N) 1).mp (congrArg Subtype.val h) with h0 | h0
    · exact hn0 h0
    · exact one_ne_zero h0
  have hcTe : Commute Te Tn := Subtype.ext (Tsp_comm hBN hen 1 1)
  have hcTf : Commute Tf Tn := Subtype.ext (Tsp_comm hBN hfn 1 1)
  have hρTn2 : ρ Tn * ρ Tn = 1 := by rw [← map_mul, hTn2, map_one]
  have hρTn1 : ρ Tn ≠ 1 := fun h => hTn1 (hinj (by rw [h, map_one]))
  have hcomm := commute_of_commute_of_mul_self hA hρTn2 hρTn1 (hcTe.map ρ) (hcTf.map ρ)
  have h1 : Te * Tf = Tf * Te := hinj (by rw [map_mul, map_mul]; exact hcomm.eq)
  exact not_commute_Tsp_of_form_ne_zero hBN hBNnd hef (congrArg Subtype.val h1)

include hBN hBNnd hq hH in
theorem levi_hom_no_invariant_line (hdim : finrank K N = 6) {A : Type*} [AddCommGroup A]
    [Module K A] (hA : finrank K A = 2) (ρ : leviGroup BN H →* (A ≃ₗ[K] A)) (hρ : ρ ≠ 1) :
    ¬ ∃ v : A, v ≠ 0 ∧ ∀ g, ∃ s : K, ρ g v = s • v := by
  rintro ⟨v, hv, hinv⟩
  have := isSimpleGroup_leviGroup hBN hBNnd hH hq (by omega)
  have hWdim : 0 < finrank K ↥(BN.orthogonal H) := by
    rw [hH.finrank_orthogonal hBNnd]
    omega
  have : Nontrivial ↥(BN.orthogonal H) := Module.nontrivial_of_finrank_pos hWdim
  obtain ⟨n, hn⟩ := exists_ne (0 : ↥(BN.orthogonal H))
  have hWnd := hH.restrict_orthogonal_nondegenerate hBN hBNnd
  obtain ⟨n', hnn'⟩ : ∃ n' : ↥(BN.orthogonal H), (BN.restrict (BN.orthogonal H)) n n' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn (hWnd.1 n hcon)
  let Tn : leviGroup BN H := ⟨Tsp hBN (n : N) 1, Tsp_mem_leviGroup hBN n.2 1⟩
  let Tn' : leviGroup BN H := ⟨Tsp hBN (n' : N) 1, Tsp_mem_leviGroup hBN n'.2 1⟩
  have hxy : Tn * Tn' ≠ Tn' * Tn := fun h =>
    not_commute_Tsp_of_form_ne_zero hBN hBNnd (e := (n : N)) (f := (n' : N)) hnn'
      (congrArg Subtype.val h)
  exact hρ (hom_eq_one_of_invariant_line hxy hA ρ hv hinv)

end Hom

end CFSG.ClassicalGroups.Alternating
