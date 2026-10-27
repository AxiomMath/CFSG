module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InSinger
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open CFSG.ShultStronglyClosedTI.CyclicSemiregular CFSG.ShultStronglyClosedTI.LinearChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped IsMulCommutative

theorem card_twisted_fixed {k : Type*} [Field k] [Finite k] (hk2 : (2 : k) = 0) (σ : k ≃+* k)
    (hσσ : ∀ a, σ (σ a) = a) (θ : k) (hθ : σ θ ≠ θ) (c : k) (hc : c * σ c = 1) :
    Nat.card {a : k // c * σ a = a} ^ 2 = Nat.card k := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  let φ : k →+ k :=
    { toFun := fun a => c * σ a + a
      map_zero' := by simp
      map_add' := by intro a b; simp only [map_add, mul_add]; ring }
  have hneg : ∀ a : k, -a = a := by
    intro a
    have : a + a = 0 := by
      have : a + a = 2 * a := by ring
      rw [this, hk2, zero_mul]
    exact neg_eq_of_add_eq_zero_right this
  have hker : ∀ a, φ a = 0 ↔ c * σ a = a := by
    intro a
    show c * σ a + a = 0 ↔ _
    constructor
    · intro h
      have : c * σ a = -a := eq_neg_of_add_eq_zero_left h
      rw [this]; exact hneg a
    · intro h
      rw [h]
      have : a + a = 2 * a := by ring
      rw [this, hk2, zero_mul]
  have hφφ : ∀ a, φ (φ a) = 0 := by
    intro a
    show c * σ (c * σ a + a) + (c * σ a + a) = 0
    rw [map_add, map_mul, hσσ]
    linear_combination a * hc + (a + c * σ a) * hk2
  have hcardk := AddSubgroup.card_ker_mul_card_of_surjective φ.rangeRestrict_surjective
  rw [AddMonoidHom.ker_rangeRestrict] at hcardk
  have hrange_le : φ.range ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    exact (AddMonoidHom.mem_ker).2 (hφφ a)
  have hCker : Nat.card {a : k // c * σ a = a} = Nat.card φ.ker :=
    Nat.card_congr
      (Equiv.subtypeEquivRight (fun a => (hker a).symm.trans AddMonoidHom.mem_ker.symm))
  have hle1 : Nat.card k ≤ Nat.card φ.ker * Nat.card φ.ker := by
    rw [← hcardk]
    exact Nat.mul_le_mul_left _ (AddSubgroup.card_le_of_le hrange_le)
  have hkcard : 1 < Nat.card k := Finite.one_lt_card
  obtain ⟨a₀, ha₀C, ha₀⟩ : ∃ a₀ : k, c * σ a₀ = a₀ ∧ a₀ ≠ 0 := by
    by_contra hcon
    have hbot : φ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [AddSubgroup.mem_bot]
      by_contra hne
      exact hcon ⟨a, (hker a).1 ha, hne⟩
    rw [hbot, AddSubgroup.card_bot] at hle1
    omega
  have hσinv : ∀ a : k, c * σ a = a → σ a = a / c := by
    intro a h
    exact eq_div_of_mul_eq hc0 (by rw [mul_comm]; exact h)
  have hC_le : Nat.card {a : k // c * σ a = a} ≤ Nat.card {a : k // σ a = a} := by
    refine Nat.card_le_card_of_injective
      (fun a => (⟨a.1 / a₀, ?_⟩ : {a : k // σ a = a})) ?_
    · rw [map_div₀, hσinv a.1 a.2, hσinv a₀ ha₀C]
      field_simp
    · intro a b h
      have h1 : a.1 / a₀ = b.1 / a₀ := congrArg Subtype.val h
      exact Subtype.ext ((div_left_inj' ha₀).1 h1)
  have hS_sq : Nat.card {a : k // σ a = a} * Nat.card {a : k // σ a = a} ≤ Nat.card k := by
    have : Nat.card ({a : k // σ a = a} × {a : k // σ a = a}) ≤ Nat.card k := by
      refine Nat.card_le_card_of_injective (fun p => p.1.1 + p.2.1 * θ) ?_
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      simp only at h
      by_cases hbb : b = b'
      · subst hbb
        have : a = a' := by simpa using h
        subst this; rfl
      · exfalso
        apply hθ
        have hne : b - b' ≠ 0 := sub_ne_zero.2 hbb
        have hθ' : θ = (a' - a) / (b - b') := by
          field_simp
          linear_combination h
        rw [hθ', map_div₀, map_sub, map_sub, ha, ha', hb, hb']
    simpa [Nat.card_prod] using this
  have hup : Nat.card {a : k // c * σ a = a} * Nat.card {a : k // c * σ a = a} ≤ Nat.card k :=
    (Nat.mul_le_mul hC_le hC_le).trans hS_sq
  rw [sq]
  apply le_antisymm hup
  rw [hCker]
  exact hle1

section Singer

variable {G : Type} [Group G] [Finite G]

theorem singer_involution {Z D : Subgroup G} {e : ℕ} (he1 : 1 ≤ e)
    (hZ : IsElemAbelian 2 Z) (hZcard : Nat.card Z = 2 ^ e)
    (hDN : D ≤ Subgroup.normalizer (Z : Set G))
    (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDreg : ActsRegularlyOn D (nonIdentity Z))
    (hDcard : Nat.card D = 2 ^ e - 1) {t : G} (htt : t * t = 1)
    (htZ : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z)
    (htD : ∀ d ∈ D, ∃ d' ∈ D, ∀ z ∈ Z,
      (t * d * t⁻¹) * z * (t * d * t⁻¹)⁻¹ = d' * z * d'⁻¹) :
    (∀ z ∈ Z, t * z = z * t) ∨
      Nat.card (Z ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ^ 2 = Nat.card Z := by
  classical
  have hZc : IsMulCommutative Z := hZ.1
  let _ : Module (ZMod 2) (Additive Z) := AddCommGroup.zmodModule (n := 2) fun v => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hZ.2 _ v.toMul.2)
  have : Finite (Additive Z) := inferInstanceAs (Finite Z)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ1 : Z ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hZcard
    have : 2 ≤ 2 ^ e := Nat.le_self_pow (by omega) 2
    omega
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set N := Subgroup.normalizer (Z : Set G) with hNdef
  let ρ₀ : N →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) :=
    (mulAutGL 2 Z).comp Z.normalizerMonoidHom
  have hρ₀ : ∀ (n : N) (v : Additive Z),
      ((((ρ₀ n : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v).toMul : G) = (n : G) * (v.toMul : G) * (n : G)⁻¹ :=
    fun _ _ => rfl
  have hρ₀ker : ∀ n : N, ρ₀ n = 1 ↔ ∀ z ∈ Z, (n : G) * z = z * (n : G) := by
    intro n
    constructor
    · intro hn x hx
      have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) =>
        (((g : Module.End (ZMod 2) (Additive Z)) (Additive.ofMul ⟨x, hx⟩)).toMul : G)) hn
      simp only [hρ₀, toMul_ofMul, Units.val_one, Module.End.one_apply] at h1
      calc (n : G) * x = (n : G) * x * (n : G)⁻¹ * n := by group
        _ = x * n := by rw [h1]
    · intro hn
      apply Units.ext
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hρ₀]
      change (n : G) * (v.toMul : G) * (n : G)⁻¹ = (v.toMul : G)
      rw [hn _ v.toMul.2, mul_inv_cancel_right]
  have hρ₀eq : ∀ n₁ n₂ : N, (∀ z ∈ Z, (n₁ : G) * z * (n₁ : G)⁻¹ = (n₂ : G) * z * (n₂ : G)⁻¹) →
      ρ₀ n₁ = ρ₀ n₂ := by
    intro n₁ n₂ h
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hρ₀, hρ₀]
    exact h _ v.toMul.2
  have htN : t ∈ N := by
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact htZ z
    · intro hz
      have h := htZ _ hz
      have e' : t * (t * z * t⁻¹) * t⁻¹ = z := by
        rw [hti]
        calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
          _ = z := by rw [htt]; group
      rwa [e'] at h
  let τ : N := ⟨t, htN⟩
  have hττ : τ * τ = 1 := Subtype.ext htt
  let D' : Subgroup N := D.subgroupOf N
  let φD : D' →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) := ρ₀.comp D'.subtype
  have hφD_inj : Function.Injective φD := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hd' : (d : N).1 ∈ D := d.2
    have h1 : ρ₀ (d : N) = 1 := hd
    exact Subtype.ext (Subtype.ext (eq_one_of_centralizes_of_acts_regularly hZ1 hDreg hd'
      ((hρ₀ker _).1 h1)))
  set Dρ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) := φD.range with hDρ
  have hDρmem : ∀ x, x ∈ Dρ ↔ ∃ d : N, d.1 ∈ D ∧ ρ₀ d = x := by
    intro x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨(d : N), d.2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  have hDρcomm : ∀ a ∈ Dρ, ∀ b ∈ Dρ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d₁, hd₁, rfl⟩ := (hDρmem a).1 ha
    obtain ⟨d₂, hd₂, rfl⟩ := (hDρmem b).1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hDcomm _ hd₁ _ hd₂)
  set τh : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) := ρ₀ τ with hτh
  have hτhτh : τh * τh = 1 := by rw [hτh, ← map_mul, hττ, map_one]
  have hτhinv : τh⁻¹ = τh := inv_eq_of_mul_eq_one_right hτhτh
  have hτhN : τh ∈ Subgroup.normalizer (Dρ : Set _) := by
    have key : ∀ x ∈ Dρ, τh * x * τh⁻¹ ∈ Dρ := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := (hDρmem x).1 hx
      obtain ⟨d', hd', hdd'⟩ := htD d.1 hd
      have htdt : t * (d : G) * t⁻¹ ∈ N := N.mul_mem (N.mul_mem htN d.2) (N.inv_mem htN)
      have h1 : τh * ρ₀ d * τh⁻¹ = ρ₀ ⟨t * (d : G) * t⁻¹, htdt⟩ := by
        rw [hτh, ← map_inv, ← map_mul, ← map_mul]
        rfl
      have h2 : ρ₀ ⟨t * (d : G) * t⁻¹, htdt⟩ = ρ₀ ⟨d', hDN hd'⟩ :=
        hρ₀eq _ _ (fun z hz => hdd' z hz)
      rw [h1, h2]
      exact (hDρmem _).2 ⟨⟨d', hDN hd'⟩, hd', rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key x, fun hx => ?_⟩
    have h := key _ hx
    have e2 : τh * (τh * x * τh⁻¹) * τh⁻¹ = x := by
      rw [hτhinv]
      calc τh * (τh * x * τh) * τh = (τh * τh) * x * (τh * τh) := by group
        _ = x := by rw [hτhτh]; group
    rwa [e2] at h
  set Γ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :=
    Dρ ⊔ Subgroup.zpowers τh with hΓ
  have hDρΓ : Dρ ≤ Γ := le_sup_left
  have hΓnorm : Γ ≤ Subgroup.normalizer (Dρ : Set _) := by
    refine sup_le ?_ ?_
    · exact le_normalizer_of_commute hDρcomm
    · rw [Subgroup.zpowers_le]; exact hτhN
  let X : Subgroup Γ := Dρ.subgroupOf Γ
  have hXn : X.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hΓnorm g.2) _).1 hx
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hDρcomm a ha b hb)
  have hne : ∀ v : Additive Z, v ≠ 0 → (v.toMul : G) ∈ nonIdentity Z := fun v hv =>
    ⟨v.toMul.2, fun h => hv (congrArg Additive.ofMul (Subtype.ext h))⟩
  have hDρΓmem : ∀ d : N, d.1 ∈ D → ρ₀ d ∈ Γ := fun d hd =>
    hDρΓ ((hDρmem _).2 ⟨d, hd, rfl⟩)
  have htrans : ∀ v w : Additive Z, v ≠ 0 → w ≠ 0 → ∃ x ∈ X,
      ((Γ.subtype x : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v = w := by
    intro v w hv hw
    obtain ⟨b, hb, hbz⟩ := hDreg.2.1 _ (hne v hv) _ (hne w hw)
    refine ⟨⟨ρ₀ ⟨b⁻¹, hDN (D.inv_mem hb)⟩, hDρΓmem ⟨b⁻¹, hDN (D.inv_mem hb)⟩ (D.inv_mem hb)⟩,
      ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact (hDρmem _).2 ⟨⟨b⁻¹, hDN (D.inv_mem hb)⟩, D.inv_mem hb, rfl⟩
    · apply Additive.toMul.injective
      apply Subtype.ext
      change (((ρ₀ ⟨b⁻¹, hDN (D.inv_mem hb)⟩ :
        LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v).toMul.1 = w.toMul.1
      rw [hρ₀]
      simpa using hbz
  have hXinj : ∀ x ∈ X, Γ.subtype x = 1 → x = 1 := fun x _ h => Subtype.ext h
  have hXcard : Nat.card X = 2 ^ e - 1 := by
    have h1 : Nat.card X = Nat.card Dρ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDρΓ).toEquiv
    have h2 : Nat.card D' = Nat.card φD.range :=
      Nat.card_congr (MonoidHom.ofInjective hφD_inj).toEquiv
    have h3 : Nat.card D' = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv
    rw [h1, hDρ, ← h2, h3, hDcard]
  have hdim : Module.finrank (ZMod 2) (Additive Z) = e := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (Additive Z)
    have h2 : Nat.card (Additive Z) = Nat.card Z := rfl
    rw [h2, hZcard] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  obtain ⟨k₀, _, _, hk₀, ev, ι, hker, hcompat, -⟩ :=
    semilinear_of_transitive_commutative (B := Γ) (V := Additive Z) he1 hdim Γ.subtype
      (X := X) hXcomm htrans hXinj hXcard
  have hk₀2 : (2 : k₀) = 0 := by
    have : Fintype k₀ := Fintype.ofFinite k₀
    exact two_eq_zero_of_card (n := e) (by omega) (by rw [← Nat.card_eq_fintype_card]; exact hk₀)
  let γ₀ : Γ := ⟨τh, Subgroup.mem_sup_right (Subgroup.mem_zpowers τh)⟩
  have hγγ : γ₀ * γ₀ = 1 := Subtype.ext hτhτh
  have hιγ : ι γ₀ * ι γ₀ = 1 := by rw [← map_mul, hγγ, map_one]
  set c : k₀ˣ := (ι γ₀).left with hc
  set σ : RingAut k₀ := (ι γ₀).right with hσ
  have hσσ' : σ * σ = 1 := by
    have := congrArg SemidirectProduct.right hιγ
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at this
  have hσσ : ∀ a : k₀, σ (σ a) = a := fun a => by
    have := congrArg (fun f : RingAut k₀ => f a) hσσ'
    simpa using this
  have hcσ : (c : k₀) * σ (c : k₀) = 1 := by
    have := congrArg SemidirectProduct.left hιγ
    rw [SemidirectProduct.mul_left, SemidirectProduct.one_left] at this
    have h2 := congrArg (fun u : k₀ˣ => (u : k₀)) this
    simpa [coe_ringAutUnits_apply] using h2
  have hfixa : ∀ a : k₀, (((τh : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
      Module.End (ZMod 2) (Additive Z)) (ev a)) = ev ((c : k₀) * σ a) := fun a => hcompat γ₀ a
  by_cases hσ1 : σ = 1
  · left
    have hc1 : c = 1 := by
      have h1 : (c : k₀) * (c : k₀) = 1 := by
        rw [hσ1] at hcσ
        simpa using hcσ
      exact Units.ext (eq_one_of_sq_eq_one hk₀2 (by rw [sq]; exact h1))
    have hι1 : ι γ₀ = 1 :=
      SemidirectProduct.ext (by rw [SemidirectProduct.one_left]; exact hc1)
        (by rw [SemidirectProduct.one_right]; exact hσ1)
    have hγ1 : γ₀ = 1 := by
      have h1 : γ₀ ∈ ι.ker := hι1
      rw [hker, Subgroup.ker_subtype, Subgroup.mem_bot] at h1
      exact h1
    have hτ1 : ρ₀ τ = 1 := congrArg Subtype.val hγ1
    exact (hρ₀ker τ).1 hτ1
  · right
    obtain ⟨θ, hθ⟩ : ∃ θ : k₀, σ θ ≠ θ := by
      by_contra hcon
      apply hσ1
      ext a
      by_contra hne
      exact hcon ⟨a, by simpa using hne⟩
    have hcount := card_twisted_fixed hk₀2 σ hσσ θ hθ (c : k₀) hcσ
    have hfixiff : ∀ a : k₀, (c : k₀) * σ a = a ↔
        t * ((ev a).toMul : G) * t⁻¹ = ((ev a).toMul : G) := by
      intro a
      have h1 : (c : k₀) * σ a = a ↔ ev ((c : k₀) * σ a) = ev a := ev.injective.eq_iff.symm
      have h2 : ev ((c : k₀) * σ a) = ev a ↔ ((τh : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive Z)) : Module.End (ZMod 2) (Additive Z)) (ev a) = ev a := by
        rw [hfixa a]
      have h3 : ((τh : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
          Module.End (ZMod 2) (Additive Z)) (ev a) = ev a ↔
          t * ((ev a).toMul : G) * t⁻¹ = ((ev a).toMul : G) := by
        constructor
        · intro h
          have := congrArg (fun v : Additive Z => ((v.toMul : Z) : G)) h
          simpa [hτh, hρ₀] using this
        · intro h
          apply Additive.toMul.injective
          apply Subtype.ext
          rw [hτh, hρ₀]
          exact h
      rw [h1, h2, h3]
    have hg : ∀ a : {a : k₀ // (c : k₀) * σ a = a},
        ((ev a.1).toMul : G) ∈ (Z ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
      intro a
      refine ⟨(ev a.1).toMul.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h := (hfixiff a.1).1 a.2
      calc ((ev a.1).toMul : G) * t = (t * ((ev a.1).toMul : G) * t⁻¹) * t := by rw [h]
        _ = t * ((ev a.1).toMul : G) := by group
    let g : {a : k₀ // (c : k₀) * σ a = a} →
        (Z ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := fun a => ⟨_, hg a⟩
    have hg_inj : Function.Injective g := by
      intro a b hab
      have h1 : ((ev a.1).toMul : G) = ((ev b.1).toMul : G) :=
        congrArg (fun z : (Z ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) => (z : G)) hab
      have h2 : ev a.1 = ev b.1 := Additive.toMul.injective (Subtype.ext h1)
      exact Subtype.ext (ev.injective h2)
    have hg_surj : Function.Surjective g := by
      rintro ⟨z, hzZ, hzc⟩
      have hzc' := Subgroup.mem_centralizer_singleton_iff.1 hzc
      refine ⟨⟨ev.symm (Additive.ofMul ⟨z, hzZ⟩), ?_⟩, ?_⟩
      · rw [hfixiff, AddEquiv.apply_symm_apply]
        change t * z * t⁻¹ = z
        rw [mul_inv_eq_iff_eq_mul]
        exact hzc'.symm
      · apply Subtype.ext
        change (((ev (ev.symm (Additive.ofMul ⟨z, hzZ⟩))).toMul : Z) : G) = z
        rw [AddEquiv.apply_symm_apply]
        rfl
    have hcardeq : Nat.card (Z ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) =
        Nat.card {a : k₀ // (c : k₀) * σ a = a} :=
      (Nat.card_congr (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩)).symm
    rw [hcardeq, hcount, hk₀, hZcard]

end Singer

end CFSG.QuasithinUnique.Lin2
