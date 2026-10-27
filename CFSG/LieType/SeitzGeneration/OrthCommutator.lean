module

public import CFSG.LieType.SeitzGeneration.OrthEx

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Commutator

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_swap {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q u w = eichler Q w (-u) := by
  refine LinearEquiv.ext fun x => ?_
  have hwu : polar Q w (-u) = 0 := by rw [polar_neg_right, polar_comm, huw, neg_zero]
  rw [eichler_apply hu huw, eichler_apply hw hwu, polar_neg_right, QuadraticMap.map_neg, hu,
    hw]
  module

theorem eichler_conj_pivot {σ w s t : V} (hσ : Q σ = 0) (hw : Q w = 0) (hs : Q s = 0)
    (hσw : polar Q σ w = 0) (hσs : polar Q σ s = 0) (hws : polar Q w s = 0)
    (hst : polar Q s t = 0) (hwt : polar Q w t = 0) :
    eichler Q s t * eichler Q σ w * (eichler Q s t)⁻¹ =
      eichler Q σ w * eichler Q w (polar Q σ t • s) := by
  have hY := eichler_mem_orthogonalGroup Q s t
  rw [eichler_conj hY]
  have h1 : eichler Q s t σ = σ - polar Q σ t • s := by
    rw [eichler_apply hs hst, hσs]
    simp
  have h2 : eichler Q s t w = w := by
    rw [eichler_apply hs hst, hws, hwt]
    simp
  rw [h1, h2]
  set θ := polar Q σ t with hθ
  have hsσ : polar Q s σ = 0 := by rw [polar_comm, hσs]
  have hsw : polar Q s w = 0 := by rw [polar_comm, hws]
  have hwσ : polar Q w σ = 0 := by rw [polar_comm, hσw]
  have hQ1 : Q (σ - θ • s) = 0 := by
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, map_smul_eq_sq, hσ, hs,
      polar_smul_right_eq, hσs]
    ring
  have hp1 : polar Q (σ - θ • s) w = 0 := by
    rw [polar_sub_left, polar_smul_left_eq, hσw, hsw]
    ring
  have hp2 : polar Q w (-(σ - θ • s)) = 0 := by
    rw [polar_neg_right, polar_sub_right, polar_smul_right_eq, hwσ, hws]
    ring
  have hp3 : polar Q w (-σ) = 0 := by rw [polar_neg_right, hwσ, neg_zero]
  have hp4 : polar Q w (θ • s) = 0 := by rw [polar_smul_right_eq, hws, mul_zero]
  rw [eichler_swap hQ1 hw hp1, eichler_swap hσ hw hσw]
  have : -(σ - θ • s) = -σ + θ • s := by abel
  rw [this, ← eichler_mul hp3 hp4]

end Commutator

section Orth

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem nondegenerate_of_polarNondegOn {U : Submodule K V} (hU : PolarNondegOn Q U) :
    (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate := by
  rw [← polarBilin_comp_subtype]
  have hrefl : (polarBilin (Q.comp U.subtype)).IsRefl :=
    (QuadraticMap.isSymm_polarBilin _).isRefl
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr ?_
  intro x hx
  refine Subtype.ext (hU x x.2 fun y hy => ?_)
  have := hx ⟨y, hy⟩
  rwa [polarBilin_apply_apply, polar_comp_subtype'] at this

omit [Finite K] in
theorem exists_add_inf_perp {U A : Submodule K V} (hA : PolarNondegOn Q A) (hAU : A ≤ U) {u : V}
    (hu : u ∈ U) : ∃ a ∈ A, ∃ r ∈ U ⊓ perp Q A, a + r = u := by
  obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp hA).sup_eq_top ▸
    Submodule.mem_top (x := u))
  refine ⟨a, ha, r, ⟨?_, hr⟩, rfl⟩
  have : r = (a + r) - a := by abel
  rw [this]
  exact U.sub_mem hu (hAU ha)

omit [Finite K] in
theorem polarNondegOn_inf_perp {U A : Submodule K V} (hU : PolarNondegOn Q U)
    (hA : PolarNondegOn Q A) (hAU : A ≤ U) : PolarNondegOn Q (U ⊓ perp Q A) := by
  intro x hx hxy
  refine hU x hx.1 fun y hy => ?_
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_add_inf_perp hA hAU hy
  rw [polar_add_right, hxy r hr, polar_comm Q x a, mem_perp.mp hx.2 a ha, add_zero]

theorem hasOrthPairs_of_dim {U : Submodule K V} (hU : PolarNondegOn Q U) (h5 : 5 ≤ finrank K U) :
    HasOrthPairs Q U := by
  classical
  obtain ⟨e₁, he₁U, he₁0, he₁Q⟩ := exists_singular_of_three_le_general hU (by omega)
  obtain ⟨f₁, hf₁U, hf₁Q, h11⟩ :=
    exists_hypPair_of_regular (nondegenerate_of_polarNondegOn hU) he₁U he₁0 he₁Q
  set P : Submodule K V := Submodule.span K {e₁, f₁} with hP
  have hPU : P ≤ U := Submodule.span_le.mpr (by rintro x (rfl | rfl); exacts [he₁U, hf₁U])
  have he₁P : e₁ ∈ P := Submodule.subset_span (by simp)
  have hf₁P : f₁ ∈ P := Submodule.subset_span (by simp)
  have hf1e : polar Q f₁ e₁ = 1 := by rw [polar_comm, h11]
  have hee : polar Q e₁ e₁ = 0 := polar_self_eq_zero he₁Q
  have hff : polar Q f₁ f₁ = 0 := polar_self_eq_zero hf₁Q
  have hPreg : PolarNondegOn Q P := by
    intro x hx hxy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    have h1 := hxy e₁ he₁P
    have h2 := hxy f₁ hf₁P
    simp only [polar_add_left, polar_smul_left_eq, hee, hf1e, h11, hff] at h1 h2
    have ha : a = 0 := by linear_combination h2
    have hb : b = 0 := by linear_combination h1
    rw [ha, hb]
    simp
  have hreg' := polarNondegOn_inf_perp hU hPreg hPU
  have hdisj : Disjoint P (U ⊓ perp Q P) := by
    rw [Submodule.disjoint_def]
    intro x hxP hxU
    exact hPreg x hxP fun y hy => by rw [polar_comm]; exact mem_perp.mp hxU.2 y hy
  have hsup : P ⊔ (U ⊓ perp Q P) = U := by
    refine le_antisymm (sup_le hPU inf_le_left) fun u hu => ?_
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_add_inf_perp hPreg hPU hu
    exact Submodule.add_mem_sup ha hr
  have hPdim : finrank K P ≤ 2 := by
    have := finrank_span_finset_le_card (R := K) ({e₁, f₁} : Finset V)
    rw [Finset.coe_pair] at this
    exact this.trans Finset.card_le_two
  have hdim : 3 ≤ finrank K ↥(U ⊓ perp Q P) := by
    have := finrank_sup_of_disjoint hdisj
    rw [hsup] at this
    omega
  obtain ⟨e₂, he₂, he₂0, he₂Q⟩ := exists_singular_of_three_le_general hreg' hdim
  have h12 : polar Q e₁ e₂ = 0 := mem_perp.mp he₂.2 e₁ he₁P
  have hf2 : polar Q f₁ e₂ = 0 := mem_perp.mp he₂.2 f₁ hf₁P
  refine exists_orthPairs (nondegenerate_of_polarNondegOn hU) he₁U he₂.1 he₁Q he₂Q h12 he₁0
    fun c hc => ?_
  have hc0 : c = 0 := by
    have : polar Q f₁ e₂ = c := by rw [hc, polar_smul_right_eq, hf1e, mul_one]
    rw [← this, hf2]
  exact he₂0 (by rw [hc, hc0, zero_smul])

end Orth

section Blocks

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

omit [Finite K] in
theorem commute_of_blocks {S₁ S₂ : Submodule K V} {g₁ g₂ : V ≃ₗ[K] V} (h₁ : PolarNondegOn Q S₁)
    (b₁ : IsBlock Q p S₁ g₁) (b₂ : IsBlock Q p S₂ g₂) (hsep : OrthSep Q S₁ S₂) :
    g₁ * g₂ = g₂ * g₁ := by
  have hO₁ := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup b₁.mem
  have hO₂ := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup b₂.mem
  have F1 : ∀ u ∈ S₁, g₂ u = u := fun u hu => b₂.fix u fun s hs => hsep.symm s hs u hu
  have F2 : ∀ u ∈ S₂, g₁ u = u := fun u hu => b₁.fix u fun s hs => hsep s hs u hu
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp h₁).sup_eq_top ▸
    Submodule.mem_top (x := v))
  have hw' := mem_perp.mp hw
  have h1 : g₁ w = w := b₁.fix w hw'
  have h2 : g₁ (g₂ w) = g₂ w := b₁.fix _ fun s hs => by
    have := hO₂ s w
    rw [F1 s hs] at this
    rw [this]
    exact hw' s hs
  have h3 : g₂ (g₁ u) = g₁ u := b₂.fix _ fun s hs => by
    have := hO₁ s u
    rw [F2 s hs] at this
    rw [this]
    exact hsep.symm s hs u hu
  have h4 : g₂ u = u := F1 u hu
  simp only [LinearEquiv.mul_apply, map_add, h1, h2, h3, h4]

omit [Finite K] in
theorem zpow_eq_one_of_fix {S : Submodule K V} {g : V ≃ₗ[K] V} (hS : PolarNondegOn Q S)
    (b : IsBlock Q p S g) {i : ℤ} (h : ∀ u ∈ S, (g ^ i) u = u) : g ^ i = 1 := by
  have hP : g ^ i ∈ stabPW (perp Q S) :=
    (stabPW (perp Q S)).zpow_mem (fun w hw => b.fix w (mem_perp.mp hw)) i
  have hS' : g ^ i ∈ stabPW S := h
  have : g ^ i ∈ stabPW (S ⊔ perp Q S) := by rw [stabPW_sup]; exact ⟨hS', hP⟩
  rw [(isCompl_perp hS).sup_eq_top, stabPW_top] at this
  exact Subgroup.mem_bot.mp this

theorem false_of_three_blocks (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hrank : RankLE2 p (orthDerived Q)) {S₁ S₂ S₃ : Submodule K V}
    {g₁ g₂ g₃ : V ≃ₗ[K] V} (h₁ : PolarNondegOn Q S₁) (h₂ : PolarNondegOn Q S₂)
    (b₁ : IsBlock Q p S₁ g₁) (b₂ : IsBlock Q p S₂ g₂) (b₃ : IsBlock Q p S₃ g₃)
    (s12 : OrthSep Q S₁ S₂) (s13 : OrthSep Q S₁ S₃) (s23 : OrthSep Q S₂ S₃) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h =>
      LinearEquiv.ext (congrFun h)
  have hg : ∀ {S : Submodule K V} {g : V ≃ₗ[K] V}, IsBlock Q p S g → g ∈ orthDerived Q :=
    fun b => mem_orthDerived_of_odd_pow hQ hT hodd b.mem b.pow
  have c12 : Commute (⟨g₁, hg b₁⟩ : orthDerived Q) ⟨g₂, hg b₂⟩ :=
    Subtype.ext (commute_of_blocks h₁ b₁ b₂ s12)
  have c13 : Commute (⟨g₁, hg b₁⟩ : orthDerived Q) ⟨g₃, hg b₃⟩ :=
    Subtype.ext (commute_of_blocks h₁ b₁ b₃ s13)
  have c23 : Commute (⟨g₂, hg b₂⟩ : orthDerived Q) ⟨g₃, hg b₃⟩ :=
    Subtype.ext (commute_of_blocks h₂ b₂ b₃ s23)
  refine false_of_three_independent hp hrank c12 c13 c23 (Subtype.ext b₁.pow)
    (Subtype.ext b₂.pow) (Subtype.ext b₃.pow) ?_
  intro i j k hijk
  have h' : g₁ ^ i * g₂ ^ j * g₃ ^ k = 1 := by
    have := congrArg Subtype.val hijk
    simpa using this
  have F21 : ∀ u ∈ S₁, g₂ u = u := fun u hu => b₂.fix u fun s hs => s12.symm s hs u hu
  have F31 : ∀ u ∈ S₁, g₃ u = u := fun u hu => b₃.fix u fun s hs => s13.symm s hs u hu
  have F32 : ∀ u ∈ S₂, g₃ u = u := fun u hu => b₃.fix u fun s hs => s23.symm s hs u hu
  have hi : g₁ ^ i = 1 := zpow_eq_one_of_fix h₁ b₁ fun u hu => by
    have := congrArg (fun f : V ≃ₗ[K] V => f u) h'
    simp only [LinearEquiv.mul_apply] at this
    rw [show (1 : V ≃ₗ[K] V) u = u from rfl] at this
    rwa [zpow_apply_of_fixed (F31 u hu) k, zpow_apply_of_fixed (F21 u hu) j] at this
  rw [hi, one_mul] at h'
  have hj : g₂ ^ j = 1 := zpow_eq_one_of_fix h₂ b₂ fun u hu => by
    have := congrArg (fun f : V ≃ₗ[K] V => f u) h'
    simp only [LinearEquiv.mul_apply] at this
    rw [show (1 : V ≃ₗ[K] V) u = u from rfl] at this
    rwa [zpow_apply_of_fixed (F32 u hu) k] at this
  rw [hj, one_mul] at h'
  have ho₁ : orderOf g₁ = p := orderOf_eq_prime b₁.pow b₁.ne
  have ho₂ : orderOf g₂ = p := orderOf_eq_prime b₂.pow b₂.ne
  have ho₃ : orderOf g₃ = p := orderOf_eq_prime b₃.pow b₃.ne
  refine ⟨?_, ?_, ?_⟩
  · have := orderOf_dvd_iff_zpow_eq_one.mpr hi
    rwa [ho₁] at this
  · have := orderOf_dvd_iff_zpow_eq_one.mpr hj
    rwa [ho₂] at this
  · have := orderOf_dvd_iff_zpow_eq_one.mpr h'
    rwa [ho₃] at this

end Blocks

section Pivot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] in
theorem exists_perp_not_perp {S : Submodule K V} (hS : PolarNondegOn Q S) {x₁ x₂ : V}
    (hx₁ : x₁ ∈ S) (hx₂ : x₂ ∈ S) (hind : ∀ c : K, x₁ ≠ c • x₂) :
    ∃ t ∈ S, polar Q t x₂ = 0 ∧ polar Q t x₁ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let L : V →ₗ[K] V →ₗ[K] K := (polarBilin Q).flip
  let L₁ : ↥S →ₗ[K] K := (L x₁).comp S.subtype
  let L₂ : ↥S →ₗ[K] K := (L x₂).comp S.subtype
  have hL : ∀ (y : V) (t : ↥S), L y t = polar Q (t : V) y := fun y t => by
    simp [L, polarBilin_apply_apply]
  have hker : ⨅ _ : Unit, LinearMap.ker L₂ ≤ LinearMap.ker L₁ := by
    intro t ht
    have ht2 : L₂ t = 0 := by simpa using ht
    have h1 : polar Q (t : V) x₂ = 0 := by
      have : L x₂ t = 0 := ht2
      rwa [hL] at this
    have : L x₁ t = 0 := by rw [hL]; exact hcon t t.2 h1
    exact this
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    (FiniteDimensional.mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => L₂) hker)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hc
  set c₀ : K := c default with hc₀
  have hall : ∀ t : ↥S, polar Q (t : V) (x₁ - c₀ • x₂) = 0 := by
    intro t
    have := congrArg (fun f : ↥S →ₗ[K] K => f t) hc
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    have h1 : L₁ t = polar Q (t : V) x₁ := hL x₁ t
    have h2 : L₂ t = polar Q (t : V) x₂ := hL x₂ t
    rw [polar_sub_right, polar_smul_right_eq, ← h1, ← h2, ← this]
    ring
  have : x₁ - c₀ • x₂ = 0 := hS _ (S.sub_mem hx₁ (S.smul_mem _ hx₂)) fun y hy => by
    rw [polar_comm]
    exact hall ⟨y, hy⟩
  exact hind c₀ (sub_eq_zero.mp this)

theorem exists_singular_in_kernel (h2 : (2 : K) ≠ 0) {S : Submodule K V} (h6 : 6 ≤ finrank K S)
    (f : Fin 3 → V →ₗ[K] K) : ∃ s ∈ S, s ≠ 0 ∧ Q s = 0 ∧ ∀ i, f i s = 0 := by
  let Φ : ↥S →ₗ[K] (Fin 3 → K) := LinearMap.pi fun i => (f i).comp S.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : finrank K Φ.range ≤ 3 := by
    have := Submodule.finrank_le Φ.range
    simpa using this
  set U : Submodule K V := (LinearMap.ker Φ).map S.subtype with hU
  have hUdim : 3 ≤ finrank K U := by
    have hinj : Function.Injective S.subtype := S.injective_subtype
    have : finrank K U = finrank K (LinearMap.ker Φ) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective S.subtype hinj (LinearMap.ker Φ))).symm
    omega
  obtain ⟨s, hsU, hs0, hsQ⟩ := exists_singular_of_three_le_odd h2 hUdim
  obtain ⟨s', hs', rfl⟩ := Submodule.mem_map.mp hsU
  refine ⟨(s' : V), s'.2, hs0, hsQ, fun i => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hs') i
  simpa [Φ] using this

end Pivot

end CFSG.LieType.SeitzGeneration.OrthBlk
