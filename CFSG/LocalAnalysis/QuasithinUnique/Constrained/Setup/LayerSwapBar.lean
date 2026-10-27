module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBar

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender

variable {k : Type*} [Field k]
variable {X : Type*} [Group X]

theorem neg_eq_self_of_charTwo [CharP k 2] {M : Type*} [AddCommGroup M] [Module k M] (x : M) :
    -x = x := by
  have : x + x = 0 := by
    rw [← two_smul k x, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_smul]
  exact neg_eq_of_add_eq_zero_right this

section Card

variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

theorem natCard_map_equiv (e : M ≃ₗ[k] M) (S : Submodule k M) :
    Nat.card ↥(S.map (e : M →ₗ[k] M)) = Nat.card ↥S :=
  (Nat.card_congr (Submodule.equivMapOfInjective (e : M →ₗ[k] M) e.injective S).toEquiv).symm

theorem natCard_map_of_inf_ker_eq_bot (f : M →ₗ[k] N) (S : Submodule k M)
    (h : S ⊓ LinearMap.ker f = ⊥) : Nat.card ↥(S.map f) = Nat.card ↥S := by
  have hinj : Function.Injective (f.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx' : (x : M) ∈ S ⊓ LinearMap.ker f := ⟨x.2, by simpa using hx⟩
    rw [h] at hx'
    exact Subtype.ext (by simpa using hx')
  have hr : LinearMap.range (f.domRestrict S) = S.map f := by
    ext y
    simp only [LinearMap.mem_range, Submodule.mem_map, LinearMap.domRestrict_apply]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact (Nat.card_congr (LinearEquiv.ofInjective (f.domRestrict S) hinj).toEquiv).symm

theorem natCard_bot : Nat.card ↥(⊥ : Submodule k M) = 1 := Nat.card_unique

theorem two_le_natCard_of_ne_bot [Finite M] {S : Submodule k M} (h : S ≠ ⊥) :
    2 ≤ Nat.card ↥S := by
  have : 1 < Nat.card ↥S := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact Submodule.nontrivial_iff_ne_bot.2 h
  omega

end Card

section Swap

variable {M : Type*} [AddCommGroup M] [Module k M]

@[expose] def swapD (τ : X →* (M ≃ₗ[k] M)) (a : X) (S : Submodule k M) : Submodule k M :=
  S.map ((τ a : M →ₗ[k] M) - LinearMap.id)

theorem mem_swapD {τ : X →* (M ≃ₗ[k] M)} {a : X} {S : Submodule k M} {d : M} :
    d ∈ swapD τ a S ↔ ∃ y ∈ S, τ a y - y = d := by
  unfold swapD
  simp [Submodule.mem_map]

structure IsSwap (τ : X →* (M ≃ₗ[k] M)) (H A : Subgroup X) (a : X) (S : Submodule k M) : Prop where
  hAn : A ≤ Subgroup.normalizer (H : Set X)
  hHA : ⁅H, A⁆ = H
  ha : a ∈ A
  ha2 : a * a = 1
  comm : ∀ b ∈ A, a * b = b * a
  simple : IsSimpleSub τ H S
  nontriv : ¬ S ≤ fixSub τ H
  disj : S ⊓ S.map (τ a : M →ₗ[k] M) = ⊥
  fixD : ∀ b ∈ A, ∀ y ∈ S, τ b (τ a y - y) = τ a y - y

variable {τ : X →* (M ≃ₗ[k] M)} {H A : Subgroup X} {a : X} {S : Submodule k M}

theorem IsSwap.simple₂ (hS : IsSwap τ H A a S) :
    IsSimpleSub τ H (S.map (τ a : M →ₗ[k] M)) :=
  hS.simple.map (hS.hAn hS.ha)

theorem IsSwap.apply_apply (hS : IsSwap τ H A a S) (y : M) : τ a (τ a y) = y := by
  rw [← ρ_mul_apply, hS.ha2, map_one]; rfl

theorem IsSwap.mem_map_iff (hS : IsSwap τ H A a S) {y : M} :
    y ∈ S.map (τ a : M →ₗ[k] M) ↔ τ a y ∈ S := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    show τ a (τ a z) ∈ S
    rw [hS.apply_apply]; exact hz
  · intro h
    exact ⟨τ a y, h, hS.apply_apply y⟩

theorem IsSwap.map_map (hS : IsSwap τ H A a S) :
    (S.map (τ a : M →ₗ[k] M)).map (τ a : M →ₗ[k] M) = S := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    show τ a (τ a z) ∈ S
    rw [hS.apply_apply]; exact hz
  · intro hy
    exact ⟨τ a y, ⟨y, hy, rfl⟩, hS.apply_apply y⟩

theorem IsSwap.swapD_le (_hS : IsSwap τ H A a S) :
    swapD τ a S ≤ S ⊔ S.map (τ a : M →ₗ[k] M) := by
  intro d hd
  obtain ⟨y, hy, rfl⟩ := mem_swapD.1 hd
  rw [sub_eq_add_neg]
  exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y, hy, rfl⟩)
    (Submodule.neg_mem _ (Submodule.mem_sup_left hy))

theorem IsSwap.swapD_inf_left (hS : IsSwap τ H A a S) : swapD τ a S ⊓ S = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun d hd => ?_
  obtain ⟨y, hy, rfl⟩ := mem_swapD.1 hd.1
  have h1 : τ a y ∈ S := by
    have := S.add_mem hd.2 hy
    simpa using this
  have h2 : τ a y ∈ S ⊓ S.map (τ a : M →ₗ[k] M) := ⟨h1, ⟨y, hy, rfl⟩⟩
  rw [hS.disj] at h2
  have h3 : τ a y = 0 := by simpa using h2
  have h4 : y = 0 := by
    have : τ a (τ a y) = τ a 0 := by rw [h3]
    rw [hS.apply_apply, map_zero] at this
    exact this
  rw [h3, h4]; simp

theorem IsSwap.swapD_inf_right (hS : IsSwap τ H A a S) :
    swapD τ a S ⊓ S.map (τ a : M →ₗ[k] M) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun d hd => ?_
  obtain ⟨y, hy, rfl⟩ := mem_swapD.1 hd.1
  have h1 : y ∈ S.map (τ a : M →ₗ[k] M) := by
    have h2 : τ a y - y ∈ S.map (τ a : M →ₗ[k] M) := hd.2
    have h3 : τ a y ∈ S.map (τ a : M →ₗ[k] M) := ⟨y, hy, rfl⟩
    have := Submodule.sub_mem _ h3 h2
    simpa using this
  have h2 : y ∈ S ⊓ S.map (τ a : M →ₗ[k] M) := ⟨hy, h1⟩
  rw [hS.disj] at h2
  have h3 : y = 0 := by simpa using h2
  rw [h3]; simp

theorem IsSwap.natCard_swapD (hS : IsSwap τ H A a S) :
    Nat.card ↥(swapD τ a S) = Nat.card ↥S := by
  unfold swapD
  apply natCard_map_of_inf_ker_eq_bot
  refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
  have h0 : τ a y - y = 0 := by simpa using hy.2
  have h1 : τ a y = y := sub_eq_zero.1 h0
  have h2 : y ∈ S ⊓ S.map (τ a : M →ₗ[k] M) := ⟨hy.1, ⟨y, hy.1, h1⟩⟩
  rw [hS.disj] at h2
  simpa using h2

theorem IsSwap.natCard_sup [Finite M] (hS : IsSwap τ H A a S) :
    Nat.card ↥(S ⊔ S.map (τ a : M →ₗ[k] M)) = Nat.card ↥S * Nat.card ↥S := by
  have h := natCard_sup_mul_natCard_inf S (S.map (τ a : M →ₗ[k] M))
  rw [hS.disj, natCard_map_equiv] at h
  simpa using h

theorem IsSwap.fixD_swapD (hS : IsSwap τ H A a S) {b : X} (hb : b ∈ A) {d : M}
    (hd : d ∈ swapD τ a S) : τ b d = d := by
  obtain ⟨y, hy, rfl⟩ := mem_swapD.1 hd
  exact hS.fixD b hb y hy

theorem IsSwap.not_isInvariant_swapD (hS : IsSwap τ H A a S) :
    ¬ Offender.IsInvariant τ H (swapD τ a S) := by
  intro hinv
  let K : Subgroup X :=
    { carrier := {g | g ∈ H ∧ ∀ d ∈ swapD τ a S, τ g d = d}
      one_mem' := ⟨H.one_mem, fun d _ => by simp⟩
      mul_mem' := fun {g g'} hg hg' => ⟨H.mul_mem hg.1 hg'.1, fun d hd => by
        rw [map_mul, LinearEquiv.mul_apply, hg'.2 d hd, hg.2 d hd]⟩
      inv_mem' := fun {g} hg => ⟨H.inv_mem hg.1, fun d hd => by
        have := hg.2 d hd
        calc τ g⁻¹ d = τ g⁻¹ (τ g d) := by rw [this]
          _ = d := ρ_inv_apply τ g d⟩ }
  have hHK : H ≤ K := by
    refine le_trans (le_of_eq hS.hHA.symm) (Subgroup.commutator_le.2 fun h hh b hb => ?_)
    refine ⟨?_, fun d hd => ?_⟩
    · have : b * h⁻¹ * b⁻¹ ∈ H := conj_mem_of_mem_normalizer (hS.hAn hb) (H.inv_mem hh)
      rw [commutatorElement_def]
      have e : h * b * h⁻¹ * b⁻¹ = h * (b * h⁻¹ * b⁻¹) := by group
      rw [e]
      exact H.mul_mem hh this
    · rw [commutatorElement_def]
      have h1 : τ b⁻¹ d = d := by
        have := hS.fixD_swapD (A.inv_mem hb) hd
        exact this
      have h2 : τ h⁻¹ d ∈ swapD τ a S := hinv h⁻¹ (H.inv_mem hh) d hd
      have h3 : τ b (τ h⁻¹ d) = τ h⁻¹ d := hS.fixD_swapD hb h2
      calc τ (h * b * h⁻¹ * b⁻¹) d = τ h (τ b (τ h⁻¹ (τ b⁻¹ d))) := by
            simp only [map_mul, LinearEquiv.mul_apply]
        _ = d := by rw [h1, h3, ρ_apply_inv]
  apply hS.nontriv
  intro y hy h hh
  have hd : τ a y - y ∈ swapD τ a S := mem_swapD.2 ⟨y, hy, rfl⟩
  have h1 : τ h (τ a y - y) = τ a y - y := (hHK hh).2 _ hd
  have e1 : τ h y - y ∈ S := S.sub_mem (hS.simple.1 h hh y hy) hy
  have e2 : τ h (τ a y) - τ a y ∈ S.map (τ a : M →ₗ[k] M) := by
    have hy2 : τ a y ∈ S.map (τ a : M →ₗ[k] M) := ⟨y, hy, rfl⟩
    exact Submodule.sub_mem _ (hS.simple₂.1 h hh _ hy2) hy2
  have e3 : τ h (τ a y) - τ a y = τ h y - y := by
    rw [map_sub] at h1
    calc τ h (τ a y) - τ a y = (τ h (τ a y) - τ h y) - (τ a y - y) + (τ h y - y) := by abel
      _ = τ h y - y := by rw [h1, sub_self, zero_add]
  have e4 : τ h y - y ∈ S ⊓ S.map (τ a : M →ₗ[k] M) := ⟨e1, e3 ▸ e2⟩
  rw [hS.disj] at e4
  have : τ h y - y = 0 := by simpa using e4
  exact sub_eq_zero.1 this

theorem natCard_le_of_le' [Finite M] {P Q : Submodule k M} (h : P ≤ Q) :
    Nat.card ↥P ≤ Nat.card ↥Q :=
  Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le h)

theorem isInvariant_sup' {B : Subgroup X} {U U' : Submodule k M} (h : Offender.IsInvariant τ B U)
    (h' : Offender.IsInvariant τ B U') : Offender.IsInvariant τ B (U ⊔ U') := by
  intro b hb u hu
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add]
  exact Submodule.add_mem_sup (h b hb x hx) (h' b hb y hy)

theorem IsSwap.sup_le_of_invariant [Finite M] (hS : IsSwap τ H A a S) {Ubar : Submodule k M}
    (hinv : Offender.IsInvariant τ H Ubar) (hD : swapD τ a S ≤ Ubar)
    (hU : Ubar ≤ S ⊔ S.map (τ a : M →ₗ[k] M)) :
    S ⊔ S.map (τ a : M →ₗ[k] M) ≤ Ubar := by
  rcases hS.simple.inf_eq_bot_or_le hinv with h | h
  · exfalso
    have h1 := natCard_sup_mul_natCard_inf Ubar S
    rw [inf_comm, h, natCard_bot] at h1
    have h2 : Nat.card ↥(Ubar ⊔ S) ≤ Nat.card ↥(S ⊔ S.map (τ a : M →ₗ[k] M)) :=
      natCard_le_of_le' (sup_le hU le_sup_left)
    rw [hS.natCard_sup] at h2
    have hpos : 0 < Nat.card ↥S := Nat.card_pos
    have h3 : Nat.card ↥Ubar ≤ Nat.card ↥S := by
      rw [mul_one] at h1
      rw [h1] at h2
      exact Nat.le_of_mul_le_mul_right h2 hpos
    have h4 : swapD τ a S = Ubar :=
      submodule_eq_of_le_of_card_ge hD (by rw [hS.natCard_swapD]; exact h3)
    exact hS.not_isInvariant_swapD (h4 ▸ hinv)
  · refine sup_le h ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : τ a y - y ∈ Ubar := hD (mem_swapD.2 ⟨y, hy, rfl⟩)
    have h2 : y ∈ Ubar := h hy
    have := Ubar.add_mem h1 h2
    simpa using this

theorem IsSwap.fixed_mem_swapD [CharP k 2] (hS : IsSwap τ H A a S) {w : M}
    (hw : w ∈ S ⊔ S.map (τ a : M →ₗ[k] M)) (hfix : τ a w = w) : w ∈ swapD τ a S := by
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ S, y₂ = τ a z :=
    ⟨τ a y₂, hS.mem_map_iff.1 hy₂, (hS.apply_apply y₂).symm⟩
  rw [map_add, hS.apply_apply] at hfix
  have h1 : τ a z - τ a y₁ = z - y₁ := by
    calc τ a z - τ a y₁ = (y₁ + τ a z) - (τ a y₁ + z) + (z - y₁) := by abel
      _ = z - y₁ := by rw [← hfix, sub_self, zero_add]
  have h2 : z - y₁ ∈ S := S.sub_mem hz hy₁
  have h3 : τ a (z - y₁) = z - y₁ := by rw [map_sub, h1]
  have h4 : z - y₁ ∈ S ⊓ S.map (τ a : M →ₗ[k] M) := ⟨h2, ⟨z - y₁, h2, h3⟩⟩
  rw [hS.disj] at h4
  have h5 : z = y₁ := sub_eq_zero.1 (by simpa using h4)
  subst h5
  refine mem_swapD.2 ⟨z, hz, ?_⟩
  rw [sub_eq_add_neg, neg_eq_self_of_charTwo (k := k), add_comm]

theorem IsSwap.fixes_of_stabilizes (hS : IsSwap τ H A a S) {b : X} (hb : b ∈ A)
    (hstab : S.map (τ b : M →ₗ[k] M) = S) {w : M}
    (hw : w ∈ S ⊔ S.map (τ a : M →ₗ[k] M)) : τ b w = w := by
  have hcomm : ∀ y, τ b (τ a y) = τ a (τ b y) := by
    intro y
    rw [← ρ_mul_apply, ← ρ_mul_apply, (hS.comm b hb).symm]
  have hfixS : ∀ y ∈ S, τ b y = y := by
    intro y hy
    have hyb : τ b y ∈ S := by rw [← hstab]; exact ⟨y, hy, rfl⟩
    have hd := hS.fixD b hb y hy
    have hd' : τ a (τ b y) - τ b y = τ a y - y := by
      rw [← hcomm, ← map_sub]; exact hd
    have hu : τ b y - y ∈ S := S.sub_mem hyb hy
    have hu2 : τ a (τ b y - y) = τ b y - y := by
      rw [map_sub]
      calc τ a (τ b y) - τ a y = (τ a (τ b y) - τ b y) - (τ a y - y) + (τ b y - y) := by abel
        _ = τ b y - y := by rw [hd', sub_self, zero_add]
    have hu3 : τ b y - y ∈ S ⊓ S.map (τ a : M →ₗ[k] M) := ⟨hu, ⟨_, hu, hu2⟩⟩
    rw [hS.disj] at hu3
    exact sub_eq_zero.1 (by simpa using hu3)
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ S, y₂ = τ a z :=
    ⟨τ a y₂, hS.mem_map_iff.1 hy₂, (hS.apply_apply y₂).symm⟩
  rw [map_add, hfixS y₁ hy₁, hcomm, hfixS z hz]

theorem IsSwap.false_of_many [Finite M] (hS : IsSwap τ H A a S)
    (hinvA : Offender.IsInvariant τ A (S ⊔ S.map (τ a : M →ₗ[k] M)))
    {ι : Type*} [Fintype ι] (g : ι → X) (hgA : ∀ i, g i ∈ A)
    (hfree : ∀ i j, S.map (τ (g i) : M →ₗ[k] M) = S.map (τ (g j) : M →ₗ[k] M) → i = j)
    (hcard : Nat.card ↥S ≤ Fintype.card ι) : False := by
  have hq2 : 2 ≤ Nat.card ↥S := two_le_natCard_of_ne_bot hS.simple.2.1
  have hsimple_i : ∀ i, IsSimpleSub τ H (S.map (τ (g i) : M →ₗ[k] M)) := fun i =>
    hS.simple.map (hS.hAn (hgA i))
  obtain ⟨-, hcover⟩ := card_partition_of_orbit (S ⊔ S.map (τ a : M →ₗ[k] M))
    (fun i => S.map (τ (g i) : M →ₗ[k] M)) (swapD τ a S) (Nat.card ↥S) hq2 hS.natCard_sup
    (fun i => by
      rintro _ ⟨y, hy, rfl⟩
      exact hinvA (g i) (hgA i) y (Submodule.mem_sup_left hy))
    hS.swapD_le (fun i => natCard_map_equiv _ S) hS.natCard_swapD
    (fun i j hij => (hsimple_i i).inf_eq_bot_of_ne (hsimple_i j) fun h => hij (hfree i j h))
    (fun i => by
      refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
      obtain ⟨y, hy, rfl⟩ := hv.1
      have h1 : τ (g i) (τ (g i) y) = τ (g i) y := hS.fixD_swapD (hgA i) hv.2
      have h2 : τ (g i) y = y := (τ (g i)).injective h1
      have h3 : y ∈ swapD τ a S ⊓ S := ⟨by rw [← h2]; exact hv.2, hy⟩
      rw [hS.swapD_inf_left] at h3
      have : y = 0 := by simpa using h3
      show τ (g i) y = 0
      rw [h2, this])
    hcard
  apply hS.not_isInvariant_swapD
  intro h hh d hd
  have hT : Offender.IsInvariant τ H (S ⊔ S.map (τ a : M →ₗ[k] M)) :=
    isInvariant_sup' hS.simple.1 hS.simple₂.1
  have hdT : τ h d ∈ S ⊔ S.map (τ a : M →ₗ[k] M) := hT h hh d (hS.swapD_le hd)
  rcases hcover _ hdT with h1 | ⟨i, hi⟩
  · exact h1
  · have h2 : d ∈ S.map (τ (g i) : M →ₗ[k] M) := by
      have := (hsimple_i i).1 h⁻¹ (H.inv_mem hh) _ hi
      rwa [ρ_inv_apply] at this
    have h3 : d ∈ S.map (τ (g i) : M →ₗ[k] M) ⊓ swapD τ a S := ⟨h2, hd⟩
    have h4 : S.map (τ (g i) : M →ₗ[k] M) ⊓ swapD τ a S = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
      obtain ⟨y, hy, rfl⟩ := hv.1
      have h1 : τ (g i) (τ (g i) y) = τ (g i) y := hS.fixD_swapD (hgA i) hv.2
      have h2 : τ (g i) y = y := (τ (g i)).injective h1
      have h3 : y ∈ swapD τ a S ⊓ S := ⟨by rw [← h2]; exact hv.2, hy⟩
      rw [hS.swapD_inf_left] at h3
      have : y = 0 := by simpa using h3
      show τ (g i) y = 0
      rw [h2, this]
    rw [h4] at h3
    have : d = 0 := by simpa using h3
    rw [this, map_zero]
    exact (swapD τ a S).zero_mem

end Swap

end CFSG.QuasithinUnique.Setup.Layer
