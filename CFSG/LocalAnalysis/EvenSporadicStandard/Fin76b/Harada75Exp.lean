module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Lin

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Iter

variable {S : Type} [Group S]

@[expose] def dl (g : S) : ℕ → S → S
  | 0, y => y
  | n + 1, y => g * dl g n y * g⁻¹ * (dl g n y)⁻¹

theorem dl_succ (g : S) (n : ℕ) (y : S) :
    dl g (n + 1) y = g * dl g n y * g⁻¹ * (dl g n y)⁻¹ := rfl

theorem dl_succ_eq (g : S) (n : ℕ) (y : S) :
    dl g (n + 1) y = dl g n (g * y * g⁻¹ * y⁻¹) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [dl_succ g (n + 1) y, ih y, dl_succ g n]

theorem dl_one_apply (g u : S) : dl g 1 u = g * u * g⁻¹ * u⁻¹ := rfl

theorem dl_two_apply (g u : S) : dl g 2 u = dl g 1 (dl g 1 u) := rfl

theorem dl_one (g : S) (n : ℕ) : dl g n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dl_succ, ih]; group

theorem dl_mem (F : Subgroup S) (hFg : ∀ y ∈ F, ∀ s : S, s * y * s⁻¹ ∈ F) (g : S) (n : ℕ) :
    ∀ y ∈ F, dl g n y ∈ F := by
  induction n with
  | zero => intro y hy; exact hy
  | succ n ih =>
    intro y hy
    rw [dl_succ]
    exact F.mul_mem (hFg _ (ih y hy) g) (F.inv_mem (ih y hy))

end Iter

section Fixed

variable {S : Type} [Group S]

theorem exists_fixed_ne_one [Finite S] (hS : IsPGroup 2 S) (K : Subgroup S) (hK : K ≠ ⊥) (g : S)
    (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K) : ∃ z ∈ K, z ≠ 1 ∧ z * g = g * z := by
  have hgN : g ∈ Subgroup.normalizer (K : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hKg h hh, fun hh => ?_⟩
    let f : K → K := fun y => ⟨g * (y : S) * g⁻¹, hKg _ y.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hab' : g * (a : S) * g⁻¹ = g * (b : S) * g⁻¹ := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel hab'))
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨g * h * g⁻¹, hh⟩
    have hy' : g * (y : S) * g⁻¹ = g * h * g⁻¹ := congrArg Subtype.val hy
    have hyh : (y : S) = h := mul_left_cancel (mul_right_cancel hy')
    rw [← hyh]
    exact y.2
  have hgH : g ∈ K ⊔ Subgroup.zpowers g :=
    (le_sup_right : Subgroup.zpowers g ≤ K ⊔ Subgroup.zpowers g) (Subgroup.mem_zpowers g)
  have hHle : K ⊔ Subgroup.zpowers g ≤ Subgroup.normalizer (K : Set S) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hgN)
  set H : Subgroup S := K ⊔ Subgroup.zpowers g
  have hHp : IsPGroup 2 H := hS.to_subgroup H
  have : Group.IsNilpotent H := hHp.isNilpotent
  have hnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHle
  obtain ⟨k, hkK, hk1⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hK
  have hne : K.subgroupOf H ≠ ⊥ := by
    intro h0
    apply hk1
    have hkH : (⟨k, (le_sup_left : K ≤ H) hkK⟩ : H) ∈ K.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr hkK
    rw [h0, Subgroup.mem_bot] at hkH
    exact congrArg Subtype.val hkH
  have hcen : K.subgroupOf H ⊓ Subgroup.center H ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hcen
  have hwK : (w : S) ∈ K := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1
  have hwc : w ∈ Subgroup.center H := (Subgroup.mem_inf.mp hw).2
  have hw1S : (w : S) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hcomm : (w : S) * g = g * (w : S) := by
    have h := Subgroup.mem_center_iff.mp hwc ⟨g, hgH⟩
    exact (congrArg Subtype.val h).symm
  exact ⟨w, hwK, hw1S, hcomm⟩

end Fixed

section Claim

variable {S : Type} [Group S]

theorem dl_eq_one_of_card_le [Finite S] (hS : IsPGroup 2 S) (g : S) (n : ℕ) :
    ∀ K : Subgroup S, (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) → (∀ y ∈ K, g * y * g⁻¹ ∈ K) →
      Nat.card K ≤ 2 ^ n → ∀ y ∈ K, dl g n y = 1 := by
  induction n with
  | zero =>
    intro K _ _ hcard y hy
    have hK : K = ⊥ := by
      by_contra hne
      have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      rw [pow_zero] at hcard
      omega
    subst hK
    rw [Subgroup.mem_bot] at hy
    subst hy
    rfl
  | succ n ih =>
    intro K hKab hKg hcard y hy
    by_cases hK : K = ⊥
    · subst hK
      rw [Subgroup.mem_bot] at hy
      subst hy
      exact dl_one g (n + 1)
    · obtain ⟨z, hzK, hz1, hzg⟩ := exists_fixed_ne_one hS K hK g hKg
      have hzC : z ∈ K ⊓ Subgroup.centralizer ({g} : Set S) :=
        Subgroup.mem_inf.mpr ⟨hzK, Subgroup.mem_centralizer_singleton_iff.mpr hzg⟩
      have hC2 : 2 ≤ Nat.card (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) := by
        have hCne : (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) ≠ ⊥ := by
          intro h
          rw [h, Subgroup.mem_bot] at hzC
          exact hz1 hzC
        have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hCne
        omega
      have hcardK' : Nat.card (commSub K hKab g hKg) ≤ 2 ^ n := by
        have h := card_eq_fix_mul_comm K hKab g hKg
        have h1 : 2 * Nat.card (commSub K hKab g hKg) ≤ 2 ^ (n + 1) :=
          calc 2 * Nat.card (commSub K hKab g hKg)
              ≤ Nat.card (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) *
                  Nat.card (commSub K hKab g hKg) := Nat.mul_le_mul_right _ hC2
            _ = Nat.card K := h.symm
            _ ≤ 2 ^ (n + 1) := hcard
        rw [pow_succ] at h1
        linarith
      rw [dl_succ_eq g n y]
      exact ih (commSub K hKab g hKg)
        (fun x hx x' hx' => hKab x (commSub_le K hKab g hKg hx) x' (commSub_le K hKab g hKg hx'))
        (fun w hw => by
          obtain ⟨u, hu, rfl⟩ := (mem_commSub K hKab g hKg w).mp hw
          exact (mem_commSub K hKab g hKg _).mpr ⟨g * u * g⁻¹, hKg u hu, by group⟩)
        hcardK' _ ((mem_commSub K hKab g hKg _).mpr ⟨y, hy, rfl⟩)

end Claim

theorem pow_four_conj_eq {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {F : Subgroup S}
    (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hFexp : ∀ x ∈ F, x * x = 1)
    (hFg : ∀ y ∈ F, ∀ s : S, s * y * s⁻¹ ∈ F) (hF16 : Nat.card F ≤ 16) (g x : S) (hx : x ∈ F) :
    g ^ 4 * x * (g ^ 4)⁻¹ = x := by
  have hdl4 : ∀ y ∈ F, dl g 4 y = 1 :=
    dl_eq_one_of_card_le hS g 4 F hFab (fun y hy => hFg y hy g)
      (le_of_le_of_eq hF16 (by norm_num))
  have conj_eq : ∀ u : S, g * u * g⁻¹ = dl g 1 u * u := by
    intro u
    rw [dl_one_apply]
    group
  have hc2 : ∀ z ∈ F, g * (g * z * g⁻¹) * g⁻¹ = dl g 2 z * z := by
    intro z hz
    have hw : dl g 1 z ∈ F := dl_mem F hFg g 1 z hz
    have hww : dl g 1 z * dl g 1 z = 1 := hFexp _ hw
    calc g * (g * z * g⁻¹) * g⁻¹ = g * (dl g 1 z * z) * g⁻¹ := by rw [← conj_eq z]
      _ = (g * dl g 1 z * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (dl g 1 (dl g 1 z) * dl g 1 z) * (dl g 1 z * z) := by
        rw [conj_eq (dl g 1 z), conj_eq z]
      _ = dl g 1 (dl g 1 z) * (dl g 1 z * dl g 1 z) * z := by group
      _ = dl g 2 z * z := by rw [dl_two_apply, hww, mul_one]
  have hsplit : ∀ a b : S, g * (g * (a * b) * g⁻¹) * g⁻¹ =
      (g * (g * a * g⁻¹) * g⁻¹) * (g * (g * b * g⁻¹) * g⁻¹) := by
    intro a b
    group
  have hsq : ∀ z ∈ F, dl g 2 z * dl g 2 z = 1 := fun z hz => hFexp _ (dl_mem F hFg g 2 z hz)
  have hdl22 : dl g 2 (dl g 2 x) = 1 := hdl4 x hx
  have hg4 : g ^ 4 = g * g * g * g := by simp only [pow_succ, pow_zero, one_mul]
  calc g ^ 4 * x * (g ^ 4)⁻¹ = g * (g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹) * g⁻¹ := by
        rw [hg4]; group
    _ = g * (g * (dl g 2 x * x) * g⁻¹) * g⁻¹ := by rw [hc2 x hx]
    _ = (g * (g * dl g 2 x * g⁻¹) * g⁻¹) * (g * (g * x * g⁻¹) * g⁻¹) := hsplit _ _
    _ = (dl g 2 (dl g 2 x) * dl g 2 x) * (dl g 2 x * x) := by
        rw [hc2 _ (dl_mem F hFg g 2 x hx), hc2 x hx]
    _ = dl g 2 (dl g 2 x) * (dl g 2 x * dl g 2 x) * x := by group
    _ = x := by rw [hsq x hx, mul_one, hdl22, one_mul]

end CFSG.EvenSporadicStandard.Fin76b
