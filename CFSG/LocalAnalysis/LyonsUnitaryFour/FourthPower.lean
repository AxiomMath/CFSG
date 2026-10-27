module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFourCentralizer

public section

namespace CFSG.LyonsUnitaryFour

open scoped commutatorElement

section LinearAlgebra

variable {k : Type*} [Field k] {U : Type*} [AddCommGroup U] [Module k U]
  [FiniteDimensional k U]

theorem even_finrank_of_anticomm (hk : (2 : k) ≠ 0) (X Xinv T Tinv : U →ₗ[k] U)
    (hX : X * Xinv = 1) (hT : T * Tinv = 1) (hanti : T * X = -(X * T)) :
    Even (Module.finrank k U) := by
  have hdetX : LinearMap.det X ≠ 0 := by
    intro h
    have := congrArg LinearMap.det hX
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hdetT : LinearMap.det T ≠ 0 := by
    intro h
    have := congrArg LinearMap.det hT
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have h := congrArg LinearMap.det hanti
  rw [← neg_one_smul k (X * T), LinearMap.det_smul, map_mul, map_mul] at h
  have hpow : (-1 : k) ^ Module.finrank k U = 1 := by
    have h' : (-1 : k) ^ Module.finrank k U * (LinearMap.det X * LinearMap.det T) =
        1 * (LinearMap.det X * LinearMap.det T) := by
      rw [one_mul, ← h, mul_comm]
    exact mul_right_cancel₀ (mul_ne_zero hdetX hdetT) h'
  have hne : (-1 : k) ≠ 1 := by
    intro h1
    apply hk
    calc (2 : k) = 1 + 1 := by norm_num
      _ = 1 + -1 := by rw [h1]
      _ = 0 := by ring
  exact (neg_one_pow_eq_one_iff_even hne).mp hpow

omit [FiniteDimensional k U] in
theorem isCompl_ker_sub_one_ker_add_one (hk : (2 : k) ≠ 0) (R : U →ₗ[k] U) (hR : R * R = 1) :
    IsCompl (LinearMap.ker (R - 1)) (LinearMap.ker (R + 1)) := by
  have hR' : ∀ v, R (R v) = v := fun v => by
    have := congrArg (fun f : U →ₗ[k] U => f v) hR
    simpa using this
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at h2
    rw [h1] at h2
    have h3 : (2 : k) • v = 0 := by rw [two_smul]; exact h2
    exact (smul_eq_zero.mp h3).resolve_left hk
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have h2 : (2 : k)⁻¹ • (v + R v) + (2 : k)⁻¹ • (v - R v) = v := by
      rw [← smul_add, show v + R v + (v - R v) = (2 : k) • v by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [← h2]
    apply Submodule.add_mem_sup
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hR']
      rw [add_comm (R v) v, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hR']
      rw [← smul_add]
      simp

theorem finrank_ker_sub_one_eq_ker_add_one (R T Tinv : U →ₗ[k] U) (hT : Tinv * T = 1)
    (hT' : T * Tinv = 1) (hanti : T * R = -(R * T)) :
    Module.finrank k (LinearMap.ker (R - 1)) = Module.finrank k (LinearMap.ker (R + 1)) := by
  have hanti' : Tinv * R = -(R * Tinv) := by
    calc Tinv * R = Tinv * R * (T * Tinv) := by rw [hT', mul_one]
      _ = Tinv * (R * T) * Tinv := by simp only [mul_assoc]
      _ = Tinv * (-(T * R)) * Tinv := by rw [hanti, neg_neg]
      _ = -(Tinv * T * R * Tinv) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(R * Tinv) := by rw [hT, one_mul]
  have hmaps : ∀ (A : U →ₗ[k] U), A * R = -(R * A) → ∀ v ∈ LinearMap.ker (R - 1),
      A v ∈ LinearMap.ker (R + 1) := by
    intro A hA v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    have := congrArg (fun f : U →ₗ[k] U => f v) hA
    simp only [Module.End.mul_apply, LinearMap.neg_apply, hv] at this
    rw [eq_neg_iff_add_eq_zero] at this
    rw [add_comm]
    exact this
  have hmaps' : ∀ (A : U →ₗ[k] U), A * R = -(R * A) → ∀ v ∈ LinearMap.ker (R + 1),
      A v ∈ LinearMap.ker (R - 1) := by
    intro A hA v hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg] at hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have := congrArg (fun f : U →ₗ[k] U => f v) hA
    simp only [Module.End.mul_apply, LinearMap.neg_apply, hv, map_neg] at this
    exact (neg_inj.mp this).symm
  have hinjT : Function.Injective T := by
    intro a b h
    have := congrArg Tinv h
    have hTa : ∀ x, Tinv (T x) = x := fun x => by
      have := congrArg (fun f : U →ₗ[k] U => f x) hT; simpa using this
    rwa [hTa, hTa] at this
  have hinjTinv : Function.Injective Tinv := by
    intro a b h
    have := congrArg T h
    have hTa : ∀ x, T (Tinv x) = x := fun x => by
      have := congrArg (fun f : U →ₗ[k] U => f x) hT'; simpa using this
    rwa [hTa, hTa] at this
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := T.restrict (hmaps T hanti)) (fun a b h => Subtype.ext (hinjT
        (congrArg Subtype.val h)))
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := Tinv.restrict (hmaps' Tinv hanti')) (fun a b h => Subtype.ext (hinjTinv
        (congrArg Subtype.val h)))

end LinearAlgebra

section Representation

open CFSG.RankTwoShapes

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {P : Type*} [Group P]

@[expose] noncomputable def restrictRep (ρ : P →* Module.End k V) (W : Submodule k V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : P →* Module.End k W where
  toFun g := (ρ g).restrict (hW g)
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp [Module.End.mul_apply]

theorem restrictRep_apply (ρ : P →* Module.End k V) (W : Submodule k V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (g : P) (w : W) :
    ((restrictRep ρ W hW g w : W) : V) = ρ g w := rfl

theorem four_dvd_finrank_of_sign_pattern [FiniteDimensional k V] (hk : (2 : k) ≠ 0)
    (hcen : CentralCommutators P) (ρ : P →* Module.End k V) (W : Submodule k V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hsign : ∀ a b : P, (∀ w ∈ W, ρ (rcomm a b) w = w) ∨ (∀ w ∈ W, ρ (rcomm a b) w = -w))
    {c d s₁ s₂ s₃ : P} (hcd : c * d = d * c) (hc2 : ∀ w ∈ W, ρ (c * c) w = w)
    (hs₁ : ∀ w ∈ W, ρ (rcomm s₁ c) w = -w) (hs₂ : ∀ w ∈ W, ρ (rcomm s₂ d) w = -w)
    (hs₃ : ∀ w ∈ W, ρ (rcomm s₃ (c * d⁻¹)) w = -w) :
    4 ∣ Module.finrank k W := by
  set ρU := restrictRep ρ W hW with hρU
  have hplus : ∀ x : P, (∀ w ∈ W, ρ x w = w) → ρU x = 1 := by
    intro x hx; ext w; exact hx w w.2
  have hminus : ∀ x : P, (∀ w ∈ W, ρ x w = -w) → ρU x = -1 := by
    intro x hx; ext w; exact hx w w.2
  have hsignU : ∀ a b : P, ρU (rcomm a b) = 1 ∨ ρU (rcomm a b) = -1 := by
    intro a b
    rcases hsign a b with h | h
    · exact Or.inl (hplus _ h)
    · exact Or.inr (hminus _ h)
  have hm1 : ∀ f : Module.End k W, f * -1 = -f := by intro f; ext w; simp
  have h1m : ∀ f : Module.End k W, -1 * f = -f := by intro f; ext w; simp
  have hanti_of : ∀ a b : P, ρU (rcomm a b) = -1 → ρU a * ρU b = -(ρU b * ρU a) := by
    intro a b h
    rw [← map_mul, mul_eq_mul_rcomm a b, map_mul, map_mul, h, hm1]
  have hcomm_of : ∀ a b : P, ρU (rcomm a b) = 1 → ρU a * ρU b = ρU b * ρU a := by
    intro a b h
    rw [← map_mul, mul_eq_mul_rcomm a b, map_mul, map_mul, h, mul_one]
  set R := ρU c with hR
  have hRR : R * R = 1 := by rw [hR, ← map_mul]; exact hplus _ hc2
  have hT₁ : ρU s₁ * R = -(R * ρU s₁) := hanti_of s₁ c (hminus _ hs₁)
  have hsplit := Submodule.finrank_add_eq_of_isCompl (isCompl_ker_sub_one_ker_add_one hk R hRR)
  have hequal := finrank_ker_sub_one_eq_ker_add_one R (ρU s₁) (ρU s₁⁻¹)
    (by rw [← map_mul, inv_mul_cancel, map_one]) (by rw [← map_mul, mul_inv_cancel, map_one]) hT₁
  by_cases hW0 : Module.finrank k W = 0
  · rw [hW0]; exact dvd_zero 4
  have hne : (1 : Module.End k W) ≠ -1 := by
    intro h
    obtain ⟨w, hw⟩ : ∃ w : W, w ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hW0
      rw [Module.finrank_eq_zero_iff]
      intro w
      exact ⟨1, one_ne_zero, by rw [one_smul]; exact hall w⟩
    have h1 := congrArg (fun f : Module.End k W => f w) h
    simp only [Module.End.one_apply, LinearMap.neg_apply] at h1
    have h2 : (2 : k) • w = 0 := by rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel w
    exact hw ((smul_eq_zero.mp h2).resolve_left hk)
  have hinv_m : ∀ x : P, ρU x = -1 → ρU x⁻¹ = -1 := by
    intro x hx
    have h1 : ρU x⁻¹ * ρU x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hx] at h1
    calc ρU x⁻¹ = -(ρU x⁻¹ * -1) := by rw [hm1, neg_neg]
      _ = -1 := by rw [h1]
  have hinv_p : ∀ x : P, ρU x = 1 → ρU x⁻¹ = 1 := by
    intro x hx
    have h1 : ρU x⁻¹ * ρU x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rwa [hx, mul_one] at h1
  obtain ⟨s', hs'c, hs'd⟩ : ∃ s' : P, ρU (rcomm s' c) = 1 ∧ ρU (rcomm s' d) = -1 := by
    have h₂d := hminus _ hs₂
    rcases hsignU s₂ c with h₂c | h₂c
    · exact ⟨s₂, h₂c, h₂d⟩
    · have h₃ := hminus _ hs₃
      rw [rcomm_mul_right_central hcen, rcomm_inv_right_central hcen, map_mul] at h₃
      rcases hsignU s₃ c with h₃c | h₃c
      · rw [h₃c, one_mul] at h₃
        refine ⟨s₃, h₃c, ?_⟩
        rcases hsignU s₃ d with h₃d | h₃d
        · exact absurd (h₃.symm.trans (hinv_p _ h₃d)) (Ne.symm hne)
        · exact h₃d
      · rw [h₃c] at h₃
        have h₃d : ρU (rcomm s₃ d) = 1 := by
          rcases hsignU s₃ d with h₃d | h₃d
          · exact h₃d
          · rw [hinv_m _ h₃d, h1m, neg_neg] at h₃
            exact absurd h₃ hne
        refine ⟨s₃ * s₂, ?_, ?_⟩
        · rw [rcomm_mul_left_central hcen, map_mul, h₃c, h₂c, h1m, neg_neg]
        · rw [rcomm_mul_left_central hcen, map_mul, h₃d, h₂d, one_mul]
  set Vp := LinearMap.ker (R - 1) with hVp
  have hpres : ∀ A : Module.End k W, A * R = R * A → ∀ v ∈ Vp, A v ∈ Vp := by
    intro A hA v hv
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    have := congrArg (fun f : Module.End k W => f v) hA
    simp only [Module.End.mul_apply, hv] at this
    exact this.symm
  have hdc : ρU d * R = R * ρU d := by rw [hR, ← map_mul, ← map_mul, hcd]
  have hdic : ρU d⁻¹ * R = R * ρU d⁻¹ := by
    rw [hR, ← map_mul, ← map_mul]
    congr 1
    calc d⁻¹ * c = d⁻¹ * (c * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * c) * d⁻¹ := by rw [hcd]
      _ = c * d⁻¹ := by group
  have hs'R : ρU s' * R = R * ρU s' := hcomm_of s' c hs'c
  have hs'iR : ρU s'⁻¹ * R = R * ρU s'⁻¹ :=
    hcomm_of s'⁻¹ c (by rw [rcomm_inv_left_central hcen]; exact hinv_p _ hs'c)
  set X := (ρU d).restrict (hpres _ hdc)
  set Xinv := (ρU d⁻¹).restrict (hpres _ hdic)
  set T₂ := (ρU s').restrict (hpres _ hs'R)
  set T₂inv := (ρU s'⁻¹).restrict (hpres _ hs'iR)
  have hX : X * Xinv = 1 := by
    ext v
    simp only [X, Xinv, Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hT₂ : T₂ * T₂inv = 1 := by
    ext v
    simp only [T₂, T₂inv, Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hanti₂ : T₂ * X = -(X * T₂) := by
    have h := hanti_of s' d hs'd
    ext v
    simp only [T₂, X, Module.End.mul_apply, LinearMap.restrict_apply, LinearMap.neg_apply]
    have := congrArg (fun f : Module.End k W => f v) h
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at this
    rw [this]
    rfl
  have heven := even_finrank_of_anticomm hk X Xinv T₂ T₂inv hX hT₂ hanti₂
  obtain ⟨m, hm⟩ := heven
  rw [← hsplit, ← hequal, hm]
  exact ⟨m, by ring⟩

end Representation

section SylowFacts

variable {G : Type} [Group G] [Finite G]

theorem unitary_four_sylow_commutator_facts {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    (∀ x ∈ (S : Subgroup G), x ∉ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype →
      orderOf x = 4) ∧
    (∀ x ∈ (S : Subgroup G), x ∉ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype →
      ∀ e ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype,
        ∃ s ∈ (S : Subgroup G), s⁻¹ * x⁻¹ * s * x = e) ∧
    (∀ e ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, e ≠ 1 →
      ∃ c ∈ (S : Subgroup G), c * c = e) ∧
    (∀ c ∈ (S : Subgroup G), c ∉ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype →
      ∃ d ∈ (S : Subgroup G), c * d = d * c ∧
        d ∉ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ∧
        c * d⁻¹ ∉ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) := by
  classical
  obtain ⟨hcard, hcz, hsq1, hsqZ, hZcard⟩ := unitary_four_sylow_structure hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  have hZS : ∀ w ∈ Z, w ∈ Sg := fun w hw => (mem_map_center_iff.mp hw).1
  have hZcomm : ∀ w ∈ Z, ∀ s ∈ Sg, s * w = w * s := fun w hw => (mem_map_center_iff.mp hw).2
  have hZcardG : Nat.card Z = 4 := by
    rw [hZ, Subgroup.card_map_of_injective Sg.subtype_injective, hZcard]
  have hsqG : ∀ x ∈ Sg, x ^ 2 = 1 ↔ x ∈ Z := by
    intro x hx
    constructor
    · intro h
      refine ⟨⟨x, hx⟩, (hsq1 ⟨x, hx⟩).mp (Subtype.ext ?_), rfl⟩
      rw [Subgroup.coe_pow]; exact h
    · rintro ⟨y, hy, rfl⟩
      have h := congrArg Subtype.val ((hsq1 y).mpr hy)
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
  have hsqmem : ∀ x ∈ Sg, x ^ 2 ∈ Z := by
    intro x hx
    exact ⟨⟨x, hx⟩ ^ 2, hsqZ ⟨x, hx⟩, by simp⟩
  have hord4 : ∀ x ∈ Sg, x ∉ Z → orderOf x = 4 := by
    intro x hx hxZ
    have h2 : x ^ 2 ≠ 1 := fun h => hxZ ((hsqG x hx).mp h)
    have h4 : x ^ 4 = 1 := by
      rw [show 4 = 2 * 2 by rfl, pow_mul]
      exact (hsqG _ (Sg.pow_mem hx 2)).mpr (hsqmem x hx)
    have hdvd : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num [h4])
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases j
    · rw [pow_zero, orderOf_eq_one_iff] at hjeq
      exact absurd (by rw [hjeq, one_pow]) h2
    · exact absurd (by rw [← hjeq.trans (pow_one 2)]; exact pow_orderOf_eq_one x) h2
    · rw [hjeq]; norm_num
  have hcent16 : ∀ x ∈ Sg, x ∉ Z → Nat.card (Sg ⊓ Subgroup.centralizer ({x} : Set G) :
      Subgroup G) = 16 := fun x hx hxZ =>
    (unitary_four_sylow_centralizer_order_four hT S U hSU hx (hord4 x hx hxZ)).1
  have hC4 : ∀ u : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), u ^ 2 = 1 →
      ∃ v, v ^ 2 = u := by decide
  refine ⟨hord4, ?_, ?_, ?_⟩
  ·
    intro x hx hxZ
    let act : MulAction Sg G :=
      MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp Sg.subtype)
    have hsmul : ∀ (s : Sg) (y : G), s • y = (s : G) * y * (s : G)⁻¹ := fun s y => rfl
    have hstab : MulAction.stabilizer Sg x =
        (Subgroup.centralizer ({x} : Set G)).subgroupOf Sg := by
      ext s
      rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc (s : G) * x = ((s : G) * x * (s : G)⁻¹) * s := by group
          _ = x * s := by rw [h]
      · intro h
        rw [h]; group
    have hidx : ((Subgroup.centralizer ({x} : Set G)).subgroupOf Sg).index = 4 := by
      have h1 := Subgroup.card_mul_index ((Subgroup.centralizer ({x} : Set G)).subgroupOf Sg)
      have h2 : Nat.card ((Subgroup.centralizer ({x} : Set G)).subgroupOf Sg) = 16 := by
        rw [← Subgroup.card_map_of_injective Sg.subtype_injective, Subgroup.subgroupOf_map_subtype,
          inf_comm]
        exact hcent16 x hx hxZ
      rw [h2, hcard] at h1
      omega
    have horb : (MulAction.orbit Sg x).ncard = 4 := by
      rw [← MulAction.index_stabilizer, hstab, hidx]
    set xZ : Set G := (fun e => x * e) '' (Z : Set G) with hxZdef
    have hxZcard : xZ.ncard = 4 := by
      rw [hxZdef, Set.ncard_image_of_injective _ (mul_right_injective x), ← Nat.card_coe_set_eq]
      exact hZcardG
    have hcommZ : ∀ a b : Sg, ((⁅a, b⁆ : Sg) : G) ∈ Z := by
      intro a b
      have hmem : ⁅a, b⁆ ∈ Subgroup.center Sg := by
        rw [hcz, commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      exact ⟨_, hmem, rfl⟩
    have hsub : MulAction.orbit Sg x ⊆ xZ := by
      rintro _ ⟨s, rfl⟩
      refine ⟨x⁻¹ * ((s : G) * x * (s : G)⁻¹), ?_, ?_⟩
      · have h := hcommZ (⟨x, hx⟩ : Sg)⁻¹ s
        have heq : ((⁅(⟨x, hx⟩ : Sg)⁻¹, s⁆ : Sg) : G) = x⁻¹ * ((s : G) * x * (s : G)⁻¹) := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
          group
        rw [heq] at h
        exact h
      · show x * (x⁻¹ * ((s : G) * x * (s : G)⁻¹)) = (s : G) * x * (s : G)⁻¹
        group
    have horbeq : MulAction.orbit Sg x = xZ :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hxZcard, horb]) (Set.toFinite _)
    intro e he
    have hxe : x * e⁻¹ ∈ MulAction.orbit Sg x := by
      rw [horbeq]; exact ⟨e⁻¹, Z.inv_mem he, rfl⟩
    obtain ⟨t, ht⟩ := hxe
    change (t : G) * x * (t : G)⁻¹ = x * e⁻¹ at ht
    refine ⟨(t : G)⁻¹, Sg.inv_mem t.2, ?_⟩
    rw [inv_inv]
    have ht' : (t : G) * x⁻¹ * (t : G)⁻¹ = e * x⁻¹ := by
      have := congrArg (·⁻¹) ht
      simp only [mul_inv_rev, inv_inv] at this
      rw [← mul_assoc] at this
      exact this
    calc (t : G) * x⁻¹ * (t : G)⁻¹ * x = e * x⁻¹ * x := by rw [ht']
      _ = e := by group
  ·
    intro e he he1
    obtain ⟨x, hx, hxZ⟩ : ∃ x ∈ Sg, x ∉ Z := by
      by_contra hall
      push Not at hall
      have hle : Sg ≤ Z := fun x hx => hall x hx
      have := Subgroup.card_le_of_le hle
      rw [hcard, hZcardG] at this
      omega
    obtain ⟨-, ⟨φ⟩⟩ := unitary_four_sylow_centralizer_order_four hT S U hSU hx (hord4 x hx hxZ)
    have heA : e ∈ Sg ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨hZS e he, Subgroup.mem_centralizer_singleton_iff.mpr (hZcomm e he x hx).symm⟩
    have he2 : (φ ⟨e, heA⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨e, heA⟩ : (Sg ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) ^ 2 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact (hsqG e (hZS e he)).mpr he)
      rw [this, map_one]
    obtain ⟨v, hv⟩ := hC4 _ he2
    refine ⟨((φ.symm v : (Sg ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) : G),
      (φ.symm v).2.1, ?_⟩
    have h1 : (φ.symm v) ^ 2 = ⟨e, heA⟩ := by
      apply φ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hv]
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, sq] at h2
    exact h2
  ·
    intro c hc hcZ
    by_contra hall
    push Not at hall
    have hsub : ((Sg ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) ⊆
        (Z : Set G) ∪ (fun e => e * c) '' (Z : Set G) := by
      intro d hd
      obtain ⟨hdS, hdC⟩ := Subgroup.mem_inf.mp hd
      have hcd : c * d = d * c := (Subgroup.mem_centralizer_singleton_iff.mp hdC).symm
      by_cases hdZ : d ∈ Z
      · exact Or.inl hdZ
      · right
        have h := hall d hdS hcd hdZ
        refine ⟨d * c⁻¹, ?_, by group⟩
        have h' : (c * d⁻¹)⁻¹ ∈ Z := Z.inv_mem h
        have heq : (c * d⁻¹)⁻¹ = d * c⁻¹ := by group
        rw [heq] at h'
        exact h'
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hunion := Set.ncard_union_le (Z : Set G) ((fun e => e * c) '' (Z : Set G))
    have himg : ((fun e => e * c) '' (Z : Set G)).ncard = 4 := by
      rw [Set.ncard_image_of_injective _ (mul_left_injective c), ← Nat.card_coe_set_eq]
      exact hZcardG
    have hZn : (Z : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hZcardG
    have h16 : ((Sg ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]; exact hcent16 c hc hcZ
    omega

end SylowFacts

section Codimension

open CFSG.RankTwoShapes

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem finrank_inf_ker_add_finrank_inf_ker {k : Type*} [Field k] {V : Type*} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (hk : (2 : k) ≠ 0) (R : V →ₗ[k] V) (hR : R * R = 1)
    (K : Submodule k V) (hK : ∀ v ∈ K, R v ∈ K) :
    Module.finrank k (K ⊓ LinearMap.ker (R - 1) : Submodule k V) +
      Module.finrank k (K ⊓ LinearMap.ker (R + 1) : Submodule k V) = Module.finrank k K := by
  have hc := isCompl_ker_sub_one_ker_add_one hk R hR
  have hR' : ∀ v, R (R v) = v := fun v => by
    have := congrArg (fun f : V →ₗ[k] V => f v) hR
    simpa using this
  have hinf : (K ⊓ LinearMap.ker (R - 1)) ⊓ (K ⊓ LinearMap.ker (R + 1)) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    have := hc.disjoint.le_bot ⟨h1, h2⟩
    exact this
  have hsup : (K ⊓ LinearMap.ker (R - 1)) ⊔ (K ⊓ LinearMap.ker (R + 1)) = K := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro v hv
    have h2 : (2 : k)⁻¹ • (v + R v) + (2 : k)⁻¹ • (v - R v) = v := by
      rw [← smul_add, show v + R v + (v - R v) = (2 : k) • v by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [← h2]
    apply Submodule.add_mem_sup
    · refine ⟨K.smul_mem _ (K.add_mem hv (hK v hv)), ?_⟩
      show (2 : k)⁻¹ • (v + R v) ∈ LinearMap.ker (R - 1)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hR']
      rw [add_comm (R v) v, sub_self]
    · refine ⟨K.smul_mem _ (K.sub_mem hv (hK v hv)), ?_⟩
      show (2 : k)⁻¹ • (v - R v) ∈ LinearMap.ker (R + 1)
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hR']
      rw [← smul_add]
      simp
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ⊓ LinearMap.ker (R - 1))
    (K ⊓ LinearMap.ker (R + 1))
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h.symm

end Codimension

section Codimension2

open CFSG.RankTwoShapes

variable {G : Type} [Group G] [Finite G]

theorem four_dvd_finrank_of_central_signs {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    {k : Type*} [Field k] (hk : (2 : k) ≠ 0) {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : (S : Subgroup G) →* Module.End k V) (W : Submodule k V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hsignE : ∀ e ∈ Subgroup.center (S : Subgroup G),
      (∀ w ∈ W, ρ e w = w) ∨ (∀ w ∈ W, ρ e w = -w))
    {e₀ f : (S : Subgroup G)} (he₀ : e₀ ∈ Subgroup.center (S : Subgroup G)) (he₀1 : e₀ ≠ 1)
    (he₀W : ∀ w ∈ W, ρ e₀ w = w) (hf : f ∈ Subgroup.center (S : Subgroup G))
    (hfW : ∀ w ∈ W, ρ f w = -w) :
    4 ∣ Module.finrank k W := by
  classical
  obtain ⟨hcard, hcz, hsq1, -, -⟩ := unitary_four_sylow_structure hT S U hSU
  obtain ⟨-, hcomm, hsq, hcd⟩ := unitary_four_sylow_commutator_facts hT S U hSU
  set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  have hmemZ : ∀ p : (S : Subgroup G), (p : G) ∈ Z ↔ p ∈ Subgroup.center (S : Subgroup G) := by
    intro p
    constructor
    · rintro ⟨q, hq, hqp⟩
      have : q = p := Subtype.ext hqp
      rwa [← this]
    · intro hp; exact ⟨p, hp, rfl⟩
  have hrcommZ : ∀ a b : (S : Subgroup G), rcomm a b ∈ Subgroup.center (S : Subgroup G) := by
    intro a b
    rw [hcz, commutator_def]
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top a⁻¹) (Subgroup.mem_top b⁻¹)
    have heq : ⁅a⁻¹, b⁻¹⁆ = rcomm a b := by
      simp only [commutatorElement_def, rcomm, inv_inv]
    rwa [heq] at h
  have hcen : CentralCommutators (S : Subgroup G) := fun a b g =>
    (Subgroup.mem_center_iff.mp (hrcommZ a b) g).symm
  have hsign : ∀ a b : (S : Subgroup G),
      (∀ w ∈ W, ρ (rcomm a b) w = w) ∨ (∀ w ∈ W, ρ (rcomm a b) w = -w) :=
    fun a b => hsignE _ (hrcommZ a b)
  obtain ⟨c, hcS, hcc⟩ := hsq (e₀ : G) ((hmemZ e₀).mpr he₀) (fun h => he₀1 (Subtype.ext h))
  set c' : (S : Subgroup G) := ⟨c, hcS⟩ with hc'
  have hc'c' : c' * c' = e₀ := Subtype.ext hcc
  have hcZ : c ∉ Z := by
    intro h
    have hc1 : c' ^ 2 = 1 := (hsq1 c').mpr ((hmemZ c').mp h)
    apply he₀1
    rw [← hc'c', ← sq, hc1]
  have hfZ : (f : G) ∈ Z := (hmemZ f).mpr hf
  have hrc : ∀ (x : G) (hx : x ∈ (S : Subgroup G)) (s : G) (hs : s ∈ (S : Subgroup G)),
      s⁻¹ * x⁻¹ * s * x = f →
      rcomm (⟨s, hs⟩ : (S : Subgroup G)) ⟨x, hx⟩ = f := by
    intro x hx s hs h
    apply Subtype.ext
    simpa [rcomm] using h
  obtain ⟨s₁, hs₁S, hs₁⟩ := hcomm c hcS hcZ (f : G) hfZ
  obtain ⟨d, hdS, hcdc, hdZ, hcdZ⟩ := hcd c hcS hcZ
  obtain ⟨s₂, hs₂S, hs₂⟩ := hcomm d hdS hdZ (f : G) hfZ
  obtain ⟨s₃, hs₃S, hs₃⟩ := hcomm (c * d⁻¹)
    ((S : Subgroup G).mul_mem hcS ((S : Subgroup G).inv_mem hdS)) hcdZ (f : G) hfZ
  set d' : (S : Subgroup G) := ⟨d, hdS⟩ with hd'
  have hcd' : c' * d' = d' * c' := Subtype.ext hcdc
  have hcd'' : (⟨c * d⁻¹, (S : Subgroup G).mul_mem hcS ((S : Subgroup G).inv_mem hdS)⟩ :
      (S : Subgroup G)) = c' * d'⁻¹ := rfl
  apply four_dvd_finrank_of_sign_pattern hk hcen ρ W hW hsign hcd'
  · rw [hc'c']; exact he₀W
  · rw [hrc c hcS s₁ hs₁S hs₁]; exact hfW
  · rw [hrc d hdS s₂ hs₂S hs₂]; exact hfW
  · rw [← hcd'', hrc _ _ s₃ hs₃S hs₃]; exact hfW

theorem unitary_four_cross_characteristic_central_codimension {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    {k : Type*} [Field k] (hk : ringChar k ≠ 2) {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k (S : Subgroup G) V) :
    (∀ ε : Subgroup.center (S : Subgroup G) →* ℤˣ, ε ≠ 1 →
      4 ∣ Module.finrank k (⨅ e : Subgroup.center (S : Subgroup G),
        LinearMap.ker (ρ (e : (S : Subgroup G)) - (((ε e : ℤˣ) : ℤ) : k) • 1) :
          Submodule k V)) ∧
    4 ∣ Module.finrank k V - Module.finrank k (⨅ e : Subgroup.center (S : Subgroup G),
      LinearMap.ker (ρ (e : (S : Subgroup G)) - 1) : Submodule k V) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  obtain ⟨-, -, hsq1, -, hZcard⟩ := unitary_four_sylow_structure hT S U hSU
  have hcentral : ∀ e ∈ Subgroup.center (S : Subgroup G), ∀ g : (S : Subgroup G),
      ρ e * ρ g = ρ g * ρ e := by
    intro e he g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp he g)]
  have hexp : ∀ e ∈ Subgroup.center (S : Subgroup G), e * e = 1 := by
    intro e he; rw [← sq]; exact (hsq1 e).mpr he
  constructor
  · intro ε hε
    set W := ⨅ e : Subgroup.center (S : Subgroup G),
      LinearMap.ker (ρ (e : (S : Subgroup G)) - (((ε e : ℤˣ) : ℤ) : k) • 1) with hWdef
    have hmemW : ∀ w, w ∈ W ↔ ∀ e : Subgroup.center (S : Subgroup G),
        ρ (e : (S : Subgroup G)) w = (((ε e : ℤˣ) : ℤ) : k) • w := by
      intro w
      rw [hWdef, Submodule.mem_iInf]
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, sub_eq_zero]
    have hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W := by
      intro g w hw
      rw [hmemW] at hw ⊢
      intro e
      have hc := congrArg (fun F : Module.End k V => F w) (hcentral e e.2 g)
      simp only [Module.End.mul_apply] at hc
      rw [hc, hw e, map_smul]
    have hsignE : ∀ e ∈ Subgroup.center (S : Subgroup G),
        (∀ w ∈ W, ρ e w = w) ∨ (∀ w ∈ W, ρ e w = -w) := by
      intro e he
      rcases Int.units_eq_one_or (ε ⟨e, he⟩) with h | h
      · left; intro w hw
        rw [(hmemW w).mp hw ⟨e, he⟩, h]; simp
      · right; intro w hw
        rw [(hmemW w).mp hw ⟨e, he⟩, h]; simp
    obtain ⟨f, hf⟩ : ∃ f, ε f ≠ 1 := by
      by_contra h
      push Not at h
      exact hε (MonoidHom.ext h)
    have hf' : ε f = -1 := (Int.units_eq_one_or _).resolve_left hf
    have hfW : ∀ w ∈ W, ρ (f : (S : Subgroup G)) w = -w := by
      intro w hw; rw [(hmemW w).mp hw f, hf']; simp
    obtain ⟨u, huZ, hu1, huf⟩ := exists_third_mem_four hZcard (f : (S : Subgroup G))
    rcases Int.units_eq_one_or (ε ⟨u, huZ⟩) with hu | hu
    · exact four_dvd_finrank_of_central_signs hT S U hSU h2 ρ W hW hsignE huZ hu1
        (fun w hw => by rw [(hmemW w).mp hw ⟨u, huZ⟩, hu]; simp) f.2 hfW
    · have hufZ : u * f ∈ Subgroup.center (S : Subgroup G) := Subgroup.mul_mem _ huZ f.2
      have huf1 : u * f ≠ 1 := by
        intro h
        apply huf
        have hff := hexp f f.2
        calc u = u * f * f := by rw [mul_assoc, hff, mul_one]
          _ = f := by rw [h, one_mul]
      have hεuf : ε ⟨u * f, hufZ⟩ = 1 := by
        have : (⟨u * f, hufZ⟩ : Subgroup.center (S : Subgroup G)) = ⟨u, huZ⟩ * f := rfl
        rw [this, map_mul, hu, hf']; rfl
      exact four_dvd_finrank_of_central_signs hT S U hSU h2 ρ W hW hsignE hufZ huf1
        (fun w hw => by rw [(hmemW w).mp hw ⟨u * f, hufZ⟩, hεuf]; simp) f.2 hfW
  ·
    obtain ⟨e₁, he₁, he₁1, -⟩ := exists_third_mem_four hZcard (1 : (S : Subgroup G))
    obtain ⟨e₂, he₂, he₂1, he₂e₁⟩ := exists_third_mem_four hZcard e₁
    have hcases := mem_four_cases hZcard (fun e he => by rw [sq]; exact hexp e he) he₁ he₁1
      he₂ he₂1 he₂e₁
    set R₁ := ρ e₁ with hR₁
    set R₂ := ρ e₂ with hR₂
    have hR₁R₁ : R₁ * R₁ = 1 := by rw [hR₁, ← map_mul, hexp e₁ he₁, map_one]
    have hR₂R₂ : R₂ * R₂ = 1 := by rw [hR₂, ← map_mul, hexp e₂ he₂, map_one]
    have hρmul : ∀ (a b : (S : Subgroup G)) (v : V), ρ (a * b) v = ρ a (ρ b v) := by
      intro a b v; rw [map_mul]; rfl
    have hcomm' : ∀ e ∈ Subgroup.center (S : Subgroup G), ∀ g (v : V),
        ρ e (ρ g v) = ρ g (ρ e v) := by
      intro e he g v
      have := congrArg (fun F : Module.End k V => F v) (hcentral e he g)
      simpa [Module.End.mul_apply] using this
    set K₁ := LinearMap.ker (R₁ - 1) with hK₁
    set K₂ := LinearMap.ker (R₁ + 1) with hK₂
    set L₁ := LinearMap.ker (R₂ - 1) with hL₁
    set L₂ := LinearMap.ker (R₂ + 1) with hL₂
    have hmemK₁ : ∀ v, v ∈ K₁ ↔ R₁ v = v := fun v => by
      rw [hK₁, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hmemK₂ : ∀ v, v ∈ K₂ ↔ R₁ v = -v := fun v => by
      rw [hK₂, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg]
    have hmemL₁ : ∀ v, v ∈ L₁ ↔ R₂ v = v := fun v => by
      rw [hL₁, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hmemL₂ : ∀ v, v ∈ L₂ ↔ R₂ v = -v := fun v => by
      rw [hL₂, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg]
    have hV := Submodule.finrank_add_eq_of_isCompl (isCompl_ker_sub_one_ker_add_one h2 R₁ hR₁R₁)
    have hR₂K₁ : ∀ v ∈ K₁, R₂ v ∈ K₁ := by
      intro v hv; rw [hmemK₁] at hv ⊢; rw [hR₁, hR₂, hcomm' e₁ he₁, ← hR₁, hv]
    have hR₂K₂ : ∀ v ∈ K₂, R₂ v ∈ K₂ := by
      intro v hv; rw [hmemK₂] at hv ⊢; rw [hR₁, hR₂, hcomm' e₁ he₁, ← hR₁, hv, map_neg]
    have hK₁split := finrank_inf_ker_add_finrank_inf_ker h2 R₂ hR₂R₂ K₁ hR₂K₁
    have hK₂split := finrank_inf_ker_add_finrank_inf_ker h2 R₂ hR₂R₂ K₂ hR₂K₂
    have hfix : (⨅ e : Subgroup.center (S : Subgroup G),
        LinearMap.ker (ρ (e : (S : Subgroup G)) - 1) : Submodule k V) = K₁ ⊓ L₁ := by
      ext v
      rw [Submodule.mem_iInf, Submodule.mem_inf, hmemK₁, hmemL₁]
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      constructor
      · intro h; exact ⟨h ⟨e₁, he₁⟩, h ⟨e₂, he₂⟩⟩
      · rintro ⟨h1, h2'⟩ ⟨e, he⟩
        rcases hcases e he with rfl | rfl | rfl | rfl
        · simp
        · exact h1
        · exact h2'
        · rw [hρmul, ← hR₁, ← hR₂, h1, h2']
    have hpiece : ∀ σ₁ σ₂ : k, (σ₁ = 1 ∨ σ₁ = -1) → (σ₂ = 1 ∨ σ₂ = -1) →
        ¬ (σ₁ = 1 ∧ σ₂ = 1) → 4 ∣ Module.finrank k
          (LinearMap.ker (R₁ - σ₁ • 1) ⊓ LinearMap.ker (R₂ - σ₂ • 1) : Submodule k V) := by
      intro σ₁ σ₂ hσ₁ hσ₂ hσ
      set W' := LinearMap.ker (R₁ - σ₁ • 1) ⊓ LinearMap.ker (R₂ - σ₂ • 1) with hW'
      have hmem : ∀ v, v ∈ W' ↔ R₁ v = σ₁ • v ∧ R₂ v = σ₂ • v := by
        intro v
        rw [hW', Submodule.mem_inf]
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_eq_zero]
      have hinv : ∀ g, ∀ w ∈ W', ρ g w ∈ W' := by
        intro g w hw
        rw [hmem] at hw ⊢
        constructor
        · rw [hR₁, hcomm' e₁ he₁, ← hR₁, hw.1, map_smul]
        · rw [hR₂, hcomm' e₂ he₂, ← hR₂, hw.2, map_smul]
      have hsgn : ∀ σ : k, (σ = 1 ∨ σ = -1) → ∀ e : (S : Subgroup G),
          (∀ w ∈ W', ρ e w = σ • w) → (∀ w ∈ W', ρ e w = w) ∨ (∀ w ∈ W', ρ e w = -w) := by
        rintro σ (rfl | rfl) e h
        · left; intro w hw; rw [h w hw, one_smul]
        · right; intro w hw; rw [h w hw, neg_one_smul]
      have hsignE : ∀ e ∈ Subgroup.center (S : Subgroup G),
          (∀ w ∈ W', ρ e w = w) ∨ (∀ w ∈ W', ρ e w = -w) := by
        intro e he
        rcases hcases e he with rfl | rfl | rfl | rfl
        · left; intro w _; simp
        · exact hsgn σ₁ hσ₁ _ (fun w hw => ((hmem w).mp hw).1)
        · exact hsgn σ₂ hσ₂ _ (fun w hw => ((hmem w).mp hw).2)
        · apply hsgn (σ₂ * σ₁)
            (by rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl <;> simp)
          intro w hw
          rw [hρmul, ← hR₁, ← hR₂, ((hmem w).mp hw).1, map_smul, ((hmem w).mp hw).2, smul_smul,
            mul_comm]
      rcases hσ₁ with rfl | rfl
      · have hσ₂' : σ₂ = -1 := hσ₂.resolve_left (fun h => hσ ⟨rfl, h⟩)
        subst hσ₂'
        exact four_dvd_finrank_of_central_signs hT S U hSU h2 ρ W' hinv hsignE he₁ he₁1
          (fun w hw => by rw [← hR₁, ((hmem w).mp hw).1, one_smul]) he₂
          (fun w hw => by rw [← hR₂, ((hmem w).mp hw).2, neg_one_smul])
      · rcases hσ₂ with rfl | rfl
        · exact four_dvd_finrank_of_central_signs hT S U hSU h2 ρ W' hinv hsignE he₂ he₂1
            (fun w hw => by rw [← hR₂, ((hmem w).mp hw).2, one_smul]) he₁
            (fun w hw => by rw [← hR₁, ((hmem w).mp hw).1, neg_one_smul])
        · have he21 : e₂ * e₁ ≠ 1 := by
            intro h
            apply he₂e₁
            calc e₂ = e₂ * e₁ * e₁ := by rw [mul_assoc, hexp e₁ he₁, mul_one]
              _ = e₁ := by rw [h, one_mul]
          exact four_dvd_finrank_of_central_signs hT S U hSU h2 ρ W' hinv hsignE
            (Subgroup.mul_mem _ he₂ he₁) he21
            (fun w hw => by
              rw [hρmul, ← hR₁, ← hR₂, ((hmem w).mp hw).1, map_smul, ((hmem w).mp hw).2,
                smul_smul]
              norm_num) he₁
            (fun w hw => by rw [← hR₁, ((hmem w).mp hw).1, neg_one_smul])
    have hne1 : (-1 : k) ≠ 1 := by
      intro h
      apply h2
      calc (2 : k) = 1 + 1 := by norm_num
        _ = 1 + -1 := by rw [h]
        _ = 0 := by ring
    have hA : 4 ∣ Module.finrank k (K₁ ⊓ L₂ : Submodule k V) := by
      have := hpiece 1 (-1) (Or.inl rfl) (Or.inr rfl) (fun h => hne1 h.2)
      rwa [one_smul, neg_one_smul, sub_neg_eq_add] at this
    have hB : 4 ∣ Module.finrank k (K₂ ⊓ L₁ : Submodule k V) := by
      have := hpiece (-1) 1 (Or.inr rfl) (Or.inl rfl) (fun h => hne1 h.1)
      rwa [one_smul, neg_one_smul, sub_neg_eq_add] at this
    have hC : 4 ∣ Module.finrank k (K₂ ⊓ L₂ : Submodule k V) := by
      have := hpiece (-1) (-1) (Or.inr rfl) (Or.inr rfl) (fun h => hne1 h.1)
      rwa [neg_one_smul, sub_neg_eq_add, sub_neg_eq_add] at this
    have hV' : Module.finrank k K₁ + Module.finrank k K₂ = Module.finrank k V := hV
    have hK₁s : Module.finrank k (K₁ ⊓ L₁ : Submodule k V) +
        Module.finrank k (K₁ ⊓ L₂ : Submodule k V) = Module.finrank k K₁ := hK₁split
    have hK₂s : Module.finrank k (K₂ ⊓ L₁ : Submodule k V) +
        Module.finrank k (K₂ ⊓ L₂ : Submodule k V) = Module.finrank k K₂ := hK₂split
    rw [hfix]
    omega

end Codimension2

end CFSG.LyonsUnitaryFour
