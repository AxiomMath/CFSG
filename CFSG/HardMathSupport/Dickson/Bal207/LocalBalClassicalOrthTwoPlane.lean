module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoTv
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.WeirSylow
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux
  (exists_map_ne_zero_polar_ne_zero card_two_charP)

section Small

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {Q : QuadraticForm K U}

structure IsSmall (Q : QuadraticForm K U) : Prop where
  card : Nat.card K = 2
  regular : (QuadraticMap.polarBilin Q).Nondegenerate
  shape : (finrank K U = 2 ∧ ¬ IsPlusType Q) ∨ (finrank K U = 4 ∧ IsPlusType Q)

namespace IsSmall

theorem charP (h : IsSmall Q) : CharP K 2 :=
  card_two_charP h.card

theorem two_eq_zero (h : IsSmall Q) : (2 : K) = 0 := by
  have := h.charP
  exact CharP.cast_eq_zero K 2

theorem cases (h : IsSmall Q) (c : K) : c = 0 ∨ c = 1 := card_two_cases' h.card c

theorem ne_zero_iff (h : IsSmall Q) (c : K) : c ≠ 0 ↔ c = 1 := by
  refine ⟨fun hc => (h.cases c).resolve_left hc, fun h1 => h1 ▸ one_ne_zero⟩

theorem aniso (h : IsSmall Q) (hd : finrank K U = 2) {u : U} (hu : u ≠ 0) : Q u = 1 := by
  rcases h.shape with ⟨-, hnp⟩ | ⟨hd4, -⟩
  · refine (h.cases (Q u)).resolve_left fun h0 => hnp ⟨Submodule.span K {u}, ?_, ?_⟩
    · rw [finrank_span_singleton hu, hd]
    · intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [QuadraticMap.map_smul, h0, smul_zero]
  · omega

theorem exists_nonsingular (h : IsSmall Q) : ∃ a : U, Q a = 1 := by
  have h0 : 0 < finrank K U := by rcases h.shape with ⟨hd, -⟩ | ⟨hd, -⟩ <;> omega
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos h0
  obtain ⟨c, hc⟩ := exists_ne (0 : U)
  rcases h.shape with ⟨hd, -⟩ | ⟨hd, -⟩
  · exact ⟨c, h.aniso hd hc⟩
  · obtain ⟨b, hb, -⟩ :=
      exists_map_ne_zero_polar_ne_zero h.regular (by omega) hc
    exact ⟨b, (h.ne_zero_iff _).1 hb⟩

theorem exists_partner (h : IsSmall Q) {a : U} (ha : Q a = 1) :
    ∃ b, Q b = 1 ∧ polar Q a b = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact zero_ne_one ha
  rcases h.shape with ⟨hd, -⟩ | ⟨hd, -⟩
  · obtain ⟨y, hy⟩ : ∃ y, polar Q a y ≠ 0 := by
      by_contra hno
      push Not at hno
      exact ha0 (h.regular.1 a fun y => by rw [polarBilin_apply_apply]; exact hno y)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [QuadraticMap.polar_zero_right] at hy
      exact hy rfl
    exact ⟨y, h.aniso hd hy0, (h.ne_zero_iff _).1 hy⟩
  · obtain ⟨b, hb, hab⟩ :=
      exists_map_ne_zero_polar_ne_zero h.regular (by omega) ha0
    exact ⟨b, (h.ne_zero_iff _).1 hb, (h.ne_zero_iff _).1 hab⟩

theorem Q_comb {a b : U} (ha : Q a = 1) (hb : Q b = 1) (hab : polar Q a b = 1) (α β : K) :
    Q (α • a + β • b) = α * α + β * β + α * β := by
  rw [map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, ha, hb, polar_smul_left,
    polar_smul_right, hab]
  simp only [smul_eq_mul, mul_one]

theorem quad_eq_zero (h : IsSmall Q) {α β : K} (h0 : α * α + β * β + α * β = 0) :
    α = 0 ∧ β = 0 := by
  have h2 := h.two_eq_zero
  rcases h.cases α with rfl | rfl <;> rcases h.cases β with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso
    simp at h0
  · exfalso
    simp at h0
  · exfalso
    exact one_ne_zero (by linear_combination h0 - h2 : (1 : K) = 0)

@[expose] def perp (Q : QuadraticForm K U) (a b w : U) : U :=
  w + (polar Q b w • a + polar Q a w • b)

theorem perp_orth (h : IsSmall Q) {a b : U} (hab : polar Q a b = 1) (w : U) :
    polar Q a (perp Q a b w) = 0 ∧ polar Q b (perp Q a b w) = 0 := by
  have := h.charP
  have h2 := h.two_eq_zero
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact hab
  unfold perp
  constructor
  · simp only [polar_add_right, polar_smul_right, smul_eq_mul, polar_self_eq_zero, hab, mul_zero,
      mul_one, add_zero]
    linear_combination (polar Q a w) * h2
  · simp only [polar_add_right, polar_smul_right, smul_eq_mul, polar_self_eq_zero, hba, mul_zero,
      mul_one, zero_add]
    linear_combination (polar Q b w) * h2

theorem perp_add_proj (h : IsSmall Q) (a b w : U) :
    perp Q a b w + (polar Q b w • a + polar Q a w • b) = w := by
  have := h.charP
  unfold perp
  rw [add_assoc, add_self_vec K, add_zero]

theorem polar_perp (h : IsSmall Q) {a b w : U} (hwa : polar Q a w = 0) (hwb : polar Q b w = 0)
    (v : U) : polar Q w (perp Q a b v) = polar Q w v := by
  have hwa' : polar Q w a = 0 := by rw [polar_comm]; exact hwa
  have hwb' : polar Q w b = 0 := by rw [polar_comm]; exact hwb
  unfold perp
  simp only [polar_add_right, polar_smul_right, smul_eq_mul, hwa', hwb', mul_zero, add_zero]

theorem polar_proj {a b w : U} (hwa : polar Q a w = 0) (hwb : polar Q b w = 0) (α β : K) :
    polar Q w (α • a + β • b) = 0 := by
  have hwa' : polar Q w a = 0 := by rw [polar_comm]; exact hwa
  have hwb' : polar Q w b = 0 := by rw [polar_comm]; exact hwb
  simp only [polar_add_right, polar_smul_right, smul_eq_mul, hwa', hwb', mul_zero, add_zero]

theorem perp_nonsingular (h : IsSmall Q) {a b : U} (ha : Q a = 1) (hb : Q b = 1)
    (hab : polar Q a b = 1) {w : U} (hwa : polar Q a w = 0) (hwb : polar Q b w = 0)
    (hw : w ≠ 0) : Q w = 1 := by
  have := h.charP
  have h2 := h.two_eq_zero
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact hab
  rcases h.shape with ⟨hd, -⟩ | ⟨hd, hp⟩
  · exact h.aniso hd hw
  refine (h.cases (Q w)).resolve_left fun hQw => ?_
  obtain ⟨S, hS2, hS0⟩ := hp
  let ψ : U →ₗ[K] K × K := (QuadraticMap.polarBilin Q a).prod (QuadraticMap.polarBilin Q b)
  have hψ : ∀ v, ψ v = (polar Q a v, polar Q b v) := fun v => by
    simp [ψ, polarBilin_apply_apply]
  let π : U →ₗ[K] U := LinearMap.id + (QuadraticMap.polarBilin Q b).smulRight a +
    (QuadraticMap.polarBilin Q a).smulRight b
  have hπ : ∀ v, π v = perp Q a b v := fun v => by
    simp [π, perp, polarBilin_apply_apply, add_assoc]
  have hker : ∀ v, v ∈ LinearMap.ker ψ ↔ polar Q a v = 0 ∧ polar Q b v = 0 := fun v => by
    rw [LinearMap.mem_ker, hψ, Prod.mk_eq_zero]
  have hdimker : finrank K (LinearMap.ker ψ) = 2 := by
    have hr := LinearMap.finrank_range_add_finrank_ker ψ
    have hsurj : LinearMap.range ψ = ⊤ := by
      rw [LinearMap.range_eq_top]
      rintro ⟨x, y⟩
      refine ⟨x • b + y • a, ?_⟩
      rw [hψ]
      simp only [polar_add_right, polar_smul_right, smul_eq_mul, hab, hba, polar_self_eq_zero,
        mul_one, mul_zero, add_zero, zero_add]
    rw [hsurj, finrank_top, Module.finrank_prod, finrank_self, hd] at hr
    omega
  have hπker : ∀ v, π v ∈ LinearMap.ker ψ := fun v => by
    rw [hπ, hker]
    exact perp_orth h hab v
  let φ : S →ₗ[K] LinearMap.ker ψ :=
    (π ∘ₗ S.subtype).codRestrict (LinearMap.ker ψ) (fun s => hπker s)
  have hφ : ∀ s : S, ((φ s : LinearMap.ker ψ) : U) = perp Q a b s := fun s => hπ (s : U)
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have h1 : perp Q a b s = 0 := by rw [← hφ s, hs]; rfl
    have hs' : (s : U) = polar Q b s • a + polar Q a s • b := by
      have := perp_add_proj h a b s
      rw [h1, zero_add] at this
      exact this.symm
    have hQs : Q (s : U) = 0 := hS0 s s.2
    rw [hs', Q_comb ha hb hab] at hQs
    obtain ⟨h0, h0'⟩ := h.quad_eq_zero hQs
    apply Subtype.ext
    rw [hs', h0, h0', zero_smul, zero_smul, add_zero]
    rfl
  have hfin : finrank K S = finrank K (LinearMap.ker ψ) := by
    rw [hdimker]
    omega
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hφinj
  have hwker : w ∈ LinearMap.ker ψ := (hker w).2 ⟨hwa, hwb⟩
  obtain ⟨s₁, hs₁⟩ := hφsurj ⟨w, hwker⟩
  have hs₁' : perp Q a b s₁ = w := by rw [← hφ s₁, hs₁]
  have hw_eq : (s₁ : U) = w := by
    have hQw' : Q (perp Q a b s₁) = 0 := by rw [hs₁']; exact hQw
    unfold perp at hQw'
    rw [map_add_eq, hS0 _ s₁.2, Q_comb ha hb hab, polar_add_right, polar_smul_right,
      polar_smul_right, polar_comm Q (s₁ : U) a, polar_comm Q (s₁ : U) b, smul_eq_mul,
      smul_eq_mul] at hQw'
    have e : polar Q b s₁ * polar Q b s₁ + polar Q a s₁ * polar Q a s₁ +
        polar Q b s₁ * polar Q a s₁ = 0 := by
      linear_combination hQw' - (polar Q b s₁ * polar Q a s₁) * h2
    obtain ⟨h0, h0'⟩ := h.quad_eq_zero e
    rw [← hs₁']
    unfold perp
    rw [h0, h0', zero_smul, zero_smul, add_zero, add_zero]
  obtain ⟨y, hy⟩ : ∃ y, polar Q w y = 1 := by
    obtain ⟨y, hy⟩ : ∃ y, polar Q w y ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hw (h.regular.1 w fun y => by rw [polarBilin_apply_apply]; exact hno y)
    exact ⟨y, (h.ne_zero_iff _).1 hy⟩
  obtain ⟨s₂, hs₂⟩ := hφsurj ⟨perp Q a b y, (hker _).2 (perp_orth h hab y)⟩
  have hs₂' : perp Q a b s₂ = perp Q a b y := by rw [← hφ s₂, hs₂]
  have hws : polar Q w s₂ = 1 := by
    have e := perp_add_proj h a b s₂
    rw [hs₂'] at e
    rw [← e, polar_add_right, polar_perp h hwa hwb, hy, polar_proj hwa hwb, add_zero]
  have hsum : Q ((s₁ : U) + s₂) = 0 := hS0 _ (S.add_mem s₁.2 s₂.2)
  rw [map_add_eq, hS0 _ s₁.2, hS0 _ s₂.2, hw_eq, hws] at hsum
  simp at hsum

theorem tri (h : IsSmall Q) {a b c : U} (ha : Q a = 1) (hb : Q b = 1) (hab : polar Q a b = 1)
    (hc : Q c = 1) :
    c = a ∨ c = b ∨ c = a + b ∨ (polar Q a c = 0 ∧ polar Q b c = 0) := by
  have := h.charP
  have h2 := h.two_eq_zero
  set α := polar Q b c with hα
  set β := polar Q a c with hβ
  have hdec : perp Q a b c + (α • a + β • b) = c := perp_add_proj h a b c
  obtain ⟨ho1, ho2⟩ := perp_orth h hab c
  have hkey : (α ≠ 0 ∨ β ≠ 0) → perp Q a b c = 0 := by
    intro hne
    by_contra hc'
    have hQc' : Q (perp Q a b c) = 1 := h.perp_nonsingular ha hb hab ho1 ho2 hc'
    have hQp : Q (α • a + β • b) = 1 := by
      rw [Q_comb ha hb hab]
      rcases h.cases α with h0 | h1 <;> rcases h.cases β with h0' | h1'
      · exact absurd hne (by simp [h0, h0'])
      · rw [h0, h1']; simp
      · rw [h1, h0']; simp
      · rw [h1, h1']
        linear_combination h2
    have hpol : polar Q (perp Q a b c) (α • a + β • b) = 0 := polar_proj ho1 ho2 α β
    have hQc := hc
    rw [← hdec, map_add_eq, hQc', hQp, hpol] at hQc
    exact one_ne_zero (by linear_combination h2 - hQc : (1 : K) = 0)
  rcases h.cases α with h0 | h1 <;> rcases h.cases β with h0' | h1'
  · exact Or.inr (Or.inr (Or.inr ⟨h0', h0⟩))
  · have hp0 := hkey (Or.inr (by rw [h1']; exact one_ne_zero))
    rw [hp0, h0, h1', zero_smul, one_smul, zero_add, zero_add] at hdec
    exact Or.inr (Or.inl hdec.symm)
  · have hp0 := hkey (Or.inl (by rw [h1]; exact one_ne_zero))
    rw [hp0, h1, h0', zero_smul, one_smul, zero_add, add_zero] at hdec
    exact Or.inl hdec.symm
  · have hp0 := hkey (Or.inl (by rw [h1]; exact one_ne_zero))
    rw [hp0, h1, h1', one_smul, one_smul, zero_add] at hdec
    exact Or.inr (Or.inr (Or.inl hdec.symm))

theorem span_nonsingular (h : IsSmall Q) : Submodule.span K {u : U | Q u = 1} = ⊤ := by
  obtain ⟨a, ha⟩ := h.exists_nonsingular
  obtain ⟨b, hb, hab⟩ := h.exists_partner ha
  rw [eq_top_iff]
  intro v _
  have hdec := perp_add_proj h a b v
  rw [← hdec]
  refine Submodule.add_mem _ ?_ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ha))
    (Submodule.smul_mem _ _ (Submodule.subset_span hb)))
  by_cases h0 : perp Q a b v = 0
  · rw [h0]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span
      (h.perp_nonsingular ha hb hab (perp_orth h hab v).1 (perp_orth h hab v).2 h0)

end IsSmall

end Small

section Braid

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem polar_comp_subtype' (W : Submodule K V) (u w : W) :
    polar (Q.comp W.subtype) u w = polar Q (u : V) (w : V) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  rfl

def braidSet (Q : QuadraticForm K V) (W : Submodule K V) : Set (V ≃ₗ[K] V) :=
  {ρ | ∃ a ∈ W, ∃ b ∈ W, Q a = 1 ∧ Q b = 1 ∧ polar Q a b = 1 ∧ ρ = rot Q a b}

theorem rot_mem_braidSet {W : Submodule K V} {a b : V} (ha : a ∈ W) (hb : b ∈ W)
    (hQa : Q a = 1) (hQb : Q b = 1) (hab : polar Q a b = 1) : rot Q a b ∈ braidSet Q W :=
  ⟨a, ha, b, hb, hQa, hQb, hab, rfl⟩

theorem braidSet_mem_orth {W : Submodule K V} {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ braidSet Q W) :
    ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  obtain ⟨a, -, b, -, ha, hb, -, rfl⟩ := hρ
  exact rot_mem ha hb

theorem braidSet_pow_three {W : Submodule K V} {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ braidSet Q W) :
    ρ ^ 3 = 1 := by
  obtain ⟨a, -, b, -, -, -, hab, rfl⟩ := hρ
  exact rot_cube hab

theorem braidSet_comm_of_fixed {W : Submodule K V} {x : V ≃ₗ[K] V}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxW : ∀ w ∈ W, x w = w)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ braidSet Q W) : x * ρ = ρ * x := by
  obtain ⟨a, ha, b, hb, -, -, -, rfl⟩ := hρ
  exact rot_comm_of_fixed hx (hxW a ha) (hxW b hb)

theorem braidSet_conj {W : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgW : ∀ w ∈ W, g w ∈ W)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ braidSet Q W) : g * ρ * g⁻¹ ∈ braidSet Q W := by
  obtain ⟨a, ha, b, hb, hQa, hQb, hab, rfl⟩ := hρ
  rw [rot_conj hg]
  refine ⟨g a, hgW a ha, g b, hgW b hb, ?_, ?_, ?_, rfl⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg a, hQa]
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg b, hQb]
  · rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg a b, hab]

theorem conj_mem_closure_braidSet {W : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgW : ∀ w ∈ W, g w ∈ W)
    {n : V ≃ₗ[K] V} (hn : n ∈ Subgroup.closure (braidSet Q W)) :
    g * n * g⁻¹ ∈ Subgroup.closure (braidSet Q W) := by
  induction hn using Subgroup.closure_induction with
  | mem s hs => exact Subgroup.subset_closure (braidSet_conj hg hgW hs)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem tri_mem {W : Submodule K V} (hs : IsSmall (Q.comp W.subtype)) {a b e : V} (ha : a ∈ W)
    (hb : b ∈ W) (he : e ∈ W) (hQa : Q a = 1) (hQb : Q b = 1) (hab : polar Q a b = 1)
    (hQe : Q e = 1) :
    (e = a ∨ e = b ∨ e = a + b) ∨ (polar Q a e = 0 ∧ polar Q b e = 0) := by
  have h := hs.tri (a := (⟨a, ha⟩ : W)) (b := ⟨b, hb⟩) (c := ⟨e, he⟩) hQa hQb
    (by rw [polar_comp_subtype']; exact hab) hQe
  rw [polar_comp_subtype', polar_comp_subtype'] at h
  rcases h with h | h | h | h
  · exact Or.inl (Or.inl (congrArg Subtype.val h))
  · exact Or.inl (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inl (Or.inr (Or.inr (congrArg Subtype.val h)))
  · exact Or.inr h

theorem polar_tri_perp {a b e f : V} (hf : f = a ∨ f = b ∨ f = a + b)
    (he : polar Q a e = 0 ∧ polar Q b e = 0) : polar Q f e = 0 := by
  rcases hf with h | h | h
  · rw [h]; exact he.1
  · rw [h]; exact he.2
  · rw [h, polar_add_left, he.1, he.2, add_zero]

theorem rot_tri_cases {a b c d : V} (ha : Q a = 1) (hab : polar Q a b = 1)
    (hc : c = a ∨ c = b ∨ c = a + b) (hd : d = a ∨ d = b ∨ d = a + b) (hcd : polar Q c d = 1) :
    rot Q c d = rot Q a b ∨ rot Q c d = (rot Q a b)⁻¹ := by
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact hab
  have hcyc := rot_cyc ha hab
  have hpa : polar Q a (a + b) = 1 := by
    rw [polar_add_right, polar_self_eq_zero, hab, zero_add]
  have hpb : polar Q b (a + b) = 1 := by
    rw [polar_add_right, hba, polar_self_eq_zero, add_zero]
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
  · rw [polar_self_eq_zero] at hcd; exact absurd hcd zero_ne_one
  · exact Or.inl rfl
  · right
    rw [rot_swap, hcyc.2]
  · right
    rw [rot_swap]
  · rw [polar_self_eq_zero] at hcd; exact absurd hcd zero_ne_one
  · left
    exact hcyc.1
  · left
    exact hcyc.2
  · right
    rw [rot_swap, hcyc.1]
  · rw [polar_self_eq_zero] at hcd; exact absurd hcd zero_ne_one

theorem braidSet_comm {W : Submodule K V} (hs : IsSmall (Q.comp W.subtype))
    {ρ₁ ρ₂ : V ≃ₗ[K] V} (h₁ : ρ₁ ∈ braidSet Q W) (h₂ : ρ₂ ∈ braidSet Q W) :
    ρ₁ * ρ₂ = ρ₂ * ρ₁ := by
  obtain ⟨a, ha, b, hb, hQa, hQb, hab, rfl⟩ := h₁
  obtain ⟨c, hc, d, hd, hQc, hQd, hcd, rfl⟩ := h₂
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact hab
  rcases tri_mem hs ha hb hc hQa hQb hab hQc with hcT | hcP <;>
    rcases tri_mem hs ha hb hd hQa hQb hab hQd with hdT | hdP
  · rcases rot_tri_cases hQa hab hcT hdT hcd with h | h
    · rw [h]
    · rw [h, mul_inv_cancel, inv_mul_cancel]
  · exfalso
    have := polar_tri_perp hcT hdP
    rw [hcd] at this
    exact zero_ne_one this.symm
  · exfalso
    have := polar_tri_perp hdT hcP
    rw [polar_comm, hcd] at this
    exact zero_ne_one this.symm
  · have hga : rot Q c d a = a := by
      rw [rot_apply hcd, polar_comm Q c a, polar_comm Q d a, hcP.1, hdP.1]
      simp
    have hgb : rot Q c d b = b := by
      rw [rot_apply hcd, polar_comm Q c b, polar_comm Q d b, hcP.2, hdP.2]
      simp
    exact (rot_comm_of_fixed (rot_mem hQc hQd) hga hgb).symm

theorem fixes_of_commute_braidSet (hK : Nat.card K = 2) {W : Submodule K V}
    (hs : IsSmall (Q.comp W.subtype)) {G : V ≃ₗ[K] V}
    (hG : ∀ ρ ∈ braidSet Q W, G * ρ = ρ * G) {k : ℕ} (hk : Nat.Coprime 3 k) (hGk : G ^ k = 1) :
    ∀ w ∈ W, G w = w := by
  have hnon : ∀ a : W, (Q.comp W.subtype) a = 1 → G (a : V) = a := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hs.exists_partner ha
    have hab' : polar Q (a : V) (b : V) = 1 := by rw [← polar_comp_subtype']; exact hab
    exact fixes_of_commute_rot hK hab'
      (hG _ (rot_mem_braidSet a.2 b.2 (show Q (a : V) = 1 from ha) (show Q (b : V) = 1 from hb)
        hab')) hk hGk
  have hall : ∀ x : W, G (x : V) = x := by
    intro x
    have hx : x ∈ Submodule.span K {u : W | (Q.comp W.subtype) u = 1} := by
      rw [hs.span_nonsingular]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem u hu => exact hnon u hu
    | zero => simp
    | add x y _ _ hx hy => rw [Submodule.coe_add, map_add, hx, hy]
    | smul c x _ hx => rw [Submodule.coe_smul, map_smul, hx]
  exact fun w hw => hall ⟨w, hw⟩

end Braid

end CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

end
