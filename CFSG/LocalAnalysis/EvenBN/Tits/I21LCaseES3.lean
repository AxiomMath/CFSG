module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModE

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Data

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure E25Data (J : Subgroup (V ≃ₗ[ZMod 2] V)) (x : V ≃ₗ[ZMod 2] V)
    (K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V)) (V₁ V₂ : Submodule (ZMod 2) V) : Prop where
  dim : finrank (ZMod 2) V = 8
  card : Nat.card J = 25
  mem_x : x ∈ J
  pow_x : x ^ 5 = 1
  fix_x : ∀ v : V, x v = v → v = 0
  dim₁ : finrank (ZMod 2) V₁ = 4
  compl : IsCompl V₁ V₂
  stab : ∀ g ∈ J, Stable g V₁ ∧ Stable g V₂
  le₁ : K₁ ≤ J
  le₂ : K₂ ≤ J
  bot : K₁ ⊓ K₂ = ⊥
  sup : K₁ ⊔ K₂ = J
  card₁ : Nat.card K₁ = 5
  card₂ : Nat.card K₂ = 5
  fix₁ : ∀ v : V, v ∈ V₁ ↔ ∀ g ∈ K₁, g v = v
  fix₂ : ∀ v : V, v ∈ V₂ ↔ ∀ g ∈ K₂, g v = v

variable {J : Subgroup (V ≃ₗ[ZMod 2] V)} {x : V ≃ₗ[ZMod 2] V}
  {K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V)} {V₁ V₂ : Submodule (ZMod 2) V}

theorem E25Data.finite_dim (D : E25Data J x K₁ K₂ V₁ V₂) : Module.Finite (ZMod 2) V :=
  Module.finite_of_finrank_pos (by rw [D.dim]; norm_num)

theorem E25Data.dim₂ (D : E25Data J x K₁ K₂ V₁ V₂) : finrank (ZMod 2) V₂ = 4 := by
  haveI := D.finite_dim
  have h1 := Submodule.finrank_add_eq_of_isCompl D.compl
  have h2 := D.dim
  have h3 := D.dim₁
  omega

theorem E25Data.swap (D : E25Data J x K₁ K₂ V₁ V₂) : E25Data J x K₂ K₁ V₂ V₁ where
  dim := D.dim
  card := D.card
  mem_x := D.mem_x
  pow_x := D.pow_x
  fix_x := D.fix_x
  dim₁ := D.dim₂
  compl := D.compl.symm
  stab := fun g hg => ⟨(D.stab g hg).2, (D.stab g hg).1⟩
  le₁ := D.le₂
  le₂ := D.le₁
  bot := by rw [inf_comm]; exact D.bot
  sup := by rw [sup_comm]; exact D.sup
  card₁ := D.card₂
  card₂ := D.card₁
  fix₁ := D.fix₂
  fix₂ := D.fix₁

theorem E25Data.comm (D : E25Data J x K₁ K₂ V₁ V₂) : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : Nat.card J = 5 ^ 2 := by rw [D.card]; norm_num
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq h
  intro a ha b hb
  have := isMulCommutative_iff.mp this ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem E25Data.exists_prodHom (D : E25Data J x K₁ K₂ V₁ V₂) :
    ∃ ψ : K₁ × K₂ →* (V ≃ₗ[ZMod 2] V), (∀ p, ψ p = (p.1 : V ≃ₗ[ZMod 2] V) * p.2) ∧
      Function.Injective ψ ∧ ψ.range = J := by
  have hcomm : ∀ (m : K₁) (n : K₂), Commute (K₁.subtype m) (K₂.subtype n) :=
    fun m n => D.comm _ (D.le₁ m.2) _ (D.le₂ n.2)
  refine ⟨K₁.subtype.noncommCoprod K₂.subtype hcomm, fun p => rfl, ?_, ?_⟩
  · rw [MonoidHom.noncommCoprod_injective]
    refine ⟨K₁.subtype_injective, K₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact D.bot
  · rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact D.sup

theorem E25Data.decomp (D : E25Data J x K₁ K₂ V₁ V₂) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ J) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = g := by
  obtain ⟨ψ, hψ, -, hr⟩ := D.exists_prodHom
  have : g ∈ ψ.range := hr ▸ hg
  obtain ⟨⟨a, b⟩, hab⟩ := this
  exact ⟨a, a.2, b, b.2, by rw [← hab, hψ]⟩

theorem E25Data.equivProd (D : E25Data J x K₁ K₂ V₁ V₂) : Nonempty (J ≃* K₁ × K₂) := by
  obtain ⟨ψ, -, hinj, hr⟩ := D.exists_prodHom
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)).symm⟩

theorem caseES_mulEquiv_zmod_five {K : Type*} [Group K] (hK : Nat.card K = 5) :
    Nonempty (K ≃* Multiplicative (ZMod 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨mulEquivOfPrimeCardEq hK (by rw [Nat.card_eq_fintype_card]; exact ZMod.card 5)⟩

theorem E25Data.equivZMod (D : E25Data J x K₁ K₂ V₁ V₂) :
    Nonempty (J ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) := by
  obtain ⟨e⟩ := D.equivProd
  obtain ⟨e₁⟩ := caseES_mulEquiv_zmod_five D.card₁
  obtain ⟨e₂⟩ := caseES_mulEquiv_zmod_five D.card₂
  exact ⟨e.trans (MulEquiv.prodCongr e₁ e₂)⟩

end Data

section Stab

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {x : V ≃ₗ[ZMod 2] V}
  {K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V)} {V₁ V₂ : Submodule (ZMod 2) V}

theorem E25Data.mem_K₁ (D : E25Data J x K₁ K₂ V₁ V₂) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ J)
    (h1 : ∀ v ∈ V₁, g v = v) : g ∈ K₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.decomp hg
  have hb1 : ∀ v ∈ V₁, b v = v := by
    intro v hv
    have hbv : b v ∈ V₁ := (D.stab b (D.le₂ hb)).1 v hv
    have h2 : a (b v) = b v := (D.fix₁ _).mp hbv a ha
    have h3 : a (b v) = v := h1 v hv
    exact h2.symm.trans h3
  have hb2 : ∀ v ∈ V₂, b v = v := fun v hv => (D.fix₂ v).mp hv b hb
  have hb0 : b = 1 := by
    apply E25_eq_one_of_fix
    intro v
    have hv : v ∈ V₁ ⊔ V₂ := by rw [D.compl.sup_eq_top]; trivial
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hb1 m₁ hm₁, hb2 m₂ hm₂]
  rw [hb0, mul_one]
  exact ha

@[expose] def caseES_fixPair (V₁ V₂ : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {n | ∀ v : V, (n v ∈ V₁ ↔ v ∈ V₁) ∧ (n v ∈ V₂ ↔ v ∈ V₂)}
  mul_mem' := fun {a b} ha hb v => ⟨(ha (b v)).1.trans (hb v).1, (ha (b v)).2.trans (hb v).2⟩
  one_mem' := fun v => ⟨Iff.rfl, Iff.rfl⟩
  inv_mem' := by
    intro a ha v
    have h := ha (a.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact ⟨h.1.symm, h.2.symm⟩

theorem caseES_mem_fixPair {n : V ≃ₗ[ZMod 2] V} :
    n ∈ caseES_fixPair V₁ V₂ ↔ ∀ v : V, (n v ∈ V₁ ↔ v ∈ V₁) ∧ (n v ∈ V₂ ↔ v ∈ V₂) := Iff.rfl

theorem E25Data.conj_mem_K₁ (D : E25Data J x K₁ K₂ V₁ V₂) {n : V ≃ₗ[ZMod 2] V}
    (hnJ : ∀ h, h ∈ J ↔ n * h * n⁻¹ ∈ J) (hn : ∀ v : V, n v ∈ V₁ ↔ v ∈ V₁)
    {k : V ≃ₗ[ZMod 2] V} (hk : k ∈ K₁) : n * k * n⁻¹ ∈ K₁ := by
  refine D.mem_K₁ ((hnJ k).mp (D.le₁ hk)) fun v hv => ?_
  have hv' : n.symm v ∈ V₁ := by
    have h := hn (n.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.mp hv
  have h2 : k (n.symm v) = n.symm v := (D.fix₁ _).mp hv' k hk
  show n (k (n.symm v)) = v
  rw [h2]
  exact LinearEquiv.apply_symm_apply n v

theorem E25Data.mem_normalizer_K₁ (D : E25Data J x K₁ K₂ V₁ V₂) {n : V ≃ₗ[ZMod 2] V}
    (hnJ : n ∈ normalizer (J : Set (V ≃ₗ[ZMod 2] V))) (hn : ∀ v : V, n v ∈ V₁ ↔ v ∈ V₁) :
    n ∈ normalizer (K₁ : Set (V ≃ₗ[ZMod 2] V)) := by
  have hnJ' : n⁻¹ ∈ normalizer (J : Set (V ≃ₗ[ZMod 2] V)) := inv_mem hnJ
  have hn' : ∀ v : V, n⁻¹ v ∈ V₁ ↔ v ∈ V₁ := by
    intro v
    have h := hn (n.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => D.conj_mem_K₁ (mem_normalizer_iff.mp hnJ) hn hk, fun hk => ?_⟩
  have := D.conj_mem_K₁ (mem_normalizer_iff.mp hnJ') hn' hk
  simpa [mul_assoc] using this

end Stab

section Phi

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {x : V ≃ₗ[ZMod 2] V}
  {K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V)} {V₁ V₂ : Submodule (ZMod 2) V}

theorem caseES_mulAut_units_five {K : Type*} [Group K] (hK : Nat.card K = 5) :
    Nonempty (MulAut K ≃* (ZMod 5)ˣ) := by
  obtain ⟨e⟩ := caseES_mulEquiv_zmod_five hK
  exact ⟨(MulAut.congr e).trans ((MulAutMultiplicative (ZMod 5)).trans
    (ZMod.AddAutEquivUnits 5).toMultiplicative)⟩

theorem caseES_normalizerMonoidHom_eq_one_iff {G : Type*} [Group G] (K : Subgroup G)
    (m : ↥(normalizer (K : Set G))) :
    K.normalizerMonoidHom m = 1 ↔ (m : G) ∈ centralizer (K : Set G) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem E25Data.mem_centralizer_J (D : E25Data J x K₁ K₂ V₁ V₂) {n : V ≃ₗ[ZMod 2] V}
    (h₁ : n ∈ centralizer (K₁ : Set (V ≃ₗ[ZMod 2] V)))
    (h₂ : n ∈ centralizer (K₂ : Set (V ≃ₗ[ZMod 2] V))) :
    n ∈ centralizer (J : Set (V ≃ₗ[ZMod 2] V)) := by
  rw [mem_centralizer_iff] at h₁ h₂ ⊢
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := D.decomp hg
  calc a * b * n = a * (b * n) := mul_assoc _ _ _
    _ = a * (n * b) := by rw [h₂ b hb]
    _ = (a * n) * b := (mul_assoc _ _ _).symm
    _ = (n * a) * b := by rw [h₁ a ha]
    _ = n * (a * b) := mul_assoc _ _ _

theorem E25Data.exists_phi (D : E25Data J x K₁ K₂ V₁ V₂) :
    ∃ Φ : ↥(normalizer (J : Set (V ≃ₗ[ZMod 2] V)) ⊓ caseES_fixPair V₁ V₂) →* (ZMod 5)ˣ × (ZMod 5)ˣ,
      ∀ n, Φ n = 1 ↔ (n : V ≃ₗ[ZMod 2] V) ∈ centralizer (J : Set (V ≃ₗ[ZMod 2] V)) := by
  have hN₁ : normalizer (J : Set (V ≃ₗ[ZMod 2] V)) ⊓ caseES_fixPair V₁ V₂ ≤
      normalizer (K₁ : Set (V ≃ₗ[ZMod 2] V)) := fun n hn =>
    D.mem_normalizer_K₁ hn.1 fun v => ((caseES_mem_fixPair.mp hn.2) v).1
  have hN₂ : normalizer (J : Set (V ≃ₗ[ZMod 2] V)) ⊓ caseES_fixPair V₁ V₂ ≤
      normalizer (K₂ : Set (V ≃ₗ[ZMod 2] V)) := fun n hn =>
    D.swap.mem_normalizer_K₁ hn.1 fun v => ((caseES_mem_fixPair.mp hn.2) v).2
  obtain ⟨e₁⟩ := caseES_mulAut_units_five D.card₁
  obtain ⟨e₂⟩ := caseES_mulAut_units_five D.card₂
  let Φ₁ := K₁.normalizerMonoidHom.comp (Subgroup.inclusion hN₁)
  let Φ₂ := K₂.normalizerMonoidHom.comp (Subgroup.inclusion hN₂)
  refine ⟨(MulEquiv.prodCongr e₁ e₂).toMonoidHom.comp (Φ₁.prod Φ₂), fun n => ?_⟩
  have h1 : Φ₁ n = 1 ↔ (n : V ≃ₗ[ZMod 2] V) ∈ centralizer (K₁ : Set (V ≃ₗ[ZMod 2] V)) :=
    caseES_normalizerMonoidHom_eq_one_iff K₁ (Subgroup.inclusion hN₁ n)
  have h2 : Φ₂ n = 1 ↔ (n : V ≃ₗ[ZMod 2] V) ∈ centralizer (K₂ : Set (V ≃ₗ[ZMod 2] V)) :=
    caseES_normalizerMonoidHom_eq_one_iff K₂ (Subgroup.inclusion hN₂ n)
  have h3 : (MulEquiv.prodCongr e₁ e₂).toMonoidHom (Φ₁ n, Φ₂ n) = 1 ↔ (Φ₁ n, Φ₂ n) = 1 :=
    (MulEquiv.prodCongr e₁ e₂).map_eq_one_iff
  show (MulEquiv.prodCongr e₁ e₂).toMonoidHom (Φ₁ n, Φ₂ n) = 1 ↔ _
  rw [h3, Prod.mk_eq_one, h1, h2]
  exact ⟨fun h => D.mem_centralizer_J h.1 h.2, fun h => ⟨
    mem_centralizer_iff.mpr fun g hg => mem_centralizer_iff.mp h g (D.le₁ hg),
    mem_centralizer_iff.mpr fun g hg => mem_centralizer_iff.mp h g (D.le₂ hg)⟩⟩

end Phi

section Free

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {x : V ≃ₗ[ZMod 2] V}
  {K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V)} {V₁ V₂ : Submodule (ZMod 2) V}

theorem caseES_fixes_subspace [Module.Finite (ZMod 2) V] {x c : V ≃ₗ[ZMod 2] V}
    (hx : x ^ 5 = 1) (hxc : x * c = c * x) {U : Submodule (ZMod 2) V}
    (hU : finrank (ZMod 2) U = 4) (hUx : Stable x U) (hfix : ∀ u ∈ U, x u = u → u = 0) {u₀ : V}
    (hu₀ : u₀ ∈ U) (hu₀0 : u₀ ≠ 0) (hc : c u₀ = u₀) : ∀ u ∈ U, c u = u := by
  let W : Submodule (ZMod 2) V := U ⊓ fixSp c
  have hfs : ∀ w, w ∈ fixSp c ↔ c w = w := fun w => by
    rw [fixSp, LinearMap.mem_ker, nu_apply, sub_eq_zero]
  have hWx : Stable x W := by
    intro w hw
    refine ⟨hUx w hw.1, (hfs _).mpr ?_⟩
    have h1 : c w = w := (hfs w).mp hw.2
    calc c (x w) = (c * x) w := rfl
      _ = (x * c) w := by rw [hxc]
      _ = x (c w) := rfl
      _ = x w := by rw [h1]
  have hdvd : 4 ∣ finrank (ZMod 2) W :=
    four_dvd_finrank_of_stable hx hWx (fun u hu hxu => hfix u hu.1 hxu)
  have hle : finrank (ZMod 2) W ≤ 4 := hU ▸ Submodule.finrank_mono inf_le_left
  have hne : finrank (ZMod 2) W ≠ 0 := by
    intro h0
    have h1 : W = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hu : u₀ ∈ W := ⟨hu₀, (hfs u₀).mpr hc⟩
    rw [h1, Submodule.mem_bot] at hu
    exact hu₀0 hu
  have h4 : finrank (ZMod 2) W = 4 := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  have hWU : W = U := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h4, hU])
  intro u hu
  have : u ∈ W := hWU ▸ hu
  exact (hfs u).mp this.2

theorem E25Data.stable₁ (D : E25Data J x K₁ K₂ V₁ V₂) {a : V ≃ₗ[ZMod 2] V}
    (ha : a ∈ centralizer (J : Set (V ≃ₗ[ZMod 2] V))) : Stable a V₁ := by
  intro v hv
  refine (D.fix₁ _).mpr fun g hg => ?_
  have h1 : g * a = a * g := mem_centralizer_iff.mp ha g (D.le₁ hg)
  have h2 : g v = v := (D.fix₁ v).mp hv g hg
  calc g (a v) = (g * a) v := rfl
    _ = (a * g) v := by rw [h1]
    _ = a (g v) := rfl
    _ = a v := by rw [h2]

theorem E25Data.iff₁ (D : E25Data J x K₁ K₂ V₁ V₂) {a : V ≃ₗ[ZMod 2] V}
    (ha : a ∈ centralizer (J : Set (V ≃ₗ[ZMod 2] V))) (v : V) : a v ∈ V₁ ↔ v ∈ V₁ := by
  refine ⟨fun h => ?_, fun h => D.stable₁ ha v h⟩
  have := D.stable₁ (inv_mem ha) _ h
  simpa using this

theorem caseES_card_nonzero_four [Module.Finite (ZMod 2) V] (W : Submodule (ZMod 2) V)
    (hW : finrank (ZMod 2) W = 4) : Nat.card ↥((W : Set V) \ {0}) = 15 := by
  have h1 : Nat.card ↥W = 16 := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥W)
    rw [hW, Nat.card_zmod] at this
    simpa using this
  have h2 : (W : Set V).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact h1
  rw [Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem (by simp), h2]

theorem E25Data.card_centralizer_dvd (D : E25Data J x K₁ K₂ V₁ V₂) :
    Nat.card (centralizer (J : Set (V ≃ₗ[ZMod 2] V))) ∣ 225 := by
  haveI := D.finite_dim
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  set A := centralizer (J : Set (V ≃ₗ[ZMod 2] V))
  have hAx : ∀ a ∈ A, x * a = a * x := fun a ha => mem_centralizer_iff.mp ha x D.mem_x
  let X : SubMulAction A (V × V) :=
    { carrier := ((V₁ : Set V) \ {0}) ×ˢ ((V₂ : Set V) \ {0})
      smul_mem' := by
        rintro a ⟨v, w⟩ ⟨⟨hv, hv0⟩, ⟨hw, hw0⟩⟩
        refine ⟨⟨D.stable₁ a.2 v hv, ?_⟩, ⟨D.swap.stable₁ a.2 w hw, ?_⟩⟩
        · intro h
          apply hv0
          have h' : (a : V ≃ₗ[ZMod 2] V) v = 0 := h
          exact (map_eq_zero_iff _ (a : V ≃ₗ[ZMod 2] V).injective).mp h'
        · intro h
          apply hw0
          have h' : (a : V ≃ₗ[ZMod 2] V) w = 0 := h
          exact (map_eq_zero_iff _ (a : V ≃ₗ[ZMod 2] V).injective).mp h' }
  have hfree : ∀ b : X, MulAction.stabilizer A b = ⊥ := by
    intro b
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have hab : a • b = b := ha
    have hab' : a • (b : V × V) = b := congrArg Subtype.val hab
    have hv : (a : V ≃ₗ[ZMod 2] V) (b : V × V).1 = (b : V × V).1 := congrArg Prod.fst hab'
    have hw : (a : V ≃ₗ[ZMod 2] V) (b : V × V).2 = (b : V × V).2 := congrArg Prod.snd hab'
    have hb : (b : V × V) ∈ ((V₁ : Set V) \ {0}) ×ˢ ((V₂ : Set V) \ {0}) := b.2
    have hxa : x * (a : V ≃ₗ[ZMod 2] V) = (a : V ≃ₗ[ZMod 2] V) * x := hAx a a.2
    have h1 : ∀ u ∈ V₁, (a : V ≃ₗ[ZMod 2] V) u = u :=
      caseES_fixes_subspace D.pow_x hxa D.dim₁ (D.stab x D.mem_x).1
        (fun u _ hu => D.fix_x u hu) hb.1.1 hb.1.2 hv
    have h2 : ∀ u ∈ V₂, (a : V ≃ₗ[ZMod 2] V) u = u :=
      caseES_fixes_subspace D.pow_x hxa D.dim₂ (D.stab x D.mem_x).2
        (fun u _ hu => D.fix_x u hu) hb.2.1 hb.2.2 hw
    apply Subtype.ext
    apply E25_eq_one_of_fix
    intro v
    have hv : v ∈ V₁ ⊔ V₂ := by rw [D.compl.sup_eq_top]; trivial
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, h1 m₁ hm₁, h2 m₂ hm₂]
  have hcardX : Nat.card X = 225 := by
    have h : Nat.card ↥(((V₁ : Set V) \ {0}) ×ˢ ((V₂ : Set V) \ {0})) = 15 * 15 := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod, caseES_card_nonzero_four V₁ D.dim₁,
        caseES_card_nonzero_four V₂ D.dim₂]
    exact h
  have e := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree)
  rw [Nat.card_prod, hcardX] at e
  exact Dvd.intro_left _ e.symm

end Free

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
