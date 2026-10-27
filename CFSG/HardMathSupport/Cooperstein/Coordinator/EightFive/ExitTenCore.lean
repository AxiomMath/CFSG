module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitCent
public import CFSG.Quasithin.Background.Harris.Ln2.PermRank
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOrbits
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NineCore

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm MulAction

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)}

omit [Finite V] in
theorem coe_eq_coe_of_apply_eq (hψ : Function.Injective ψ) {h₁ h₂ : ↥H} (h : ψ h₁ = ψ h₂) :
    (h₁ : MulAut V) = h₂ :=
  congrArg Subtype.val (hψ h)

theorem two_mul_card_fixV_lt_of_fpf (hV : ∀ v : V, v ^ 2 = 1) (hn : 9 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {a : ↥H} (ha2 : (a : MulAut V) ^ 2 = 1) (hfpf : ∀ i, ψ a i ≠ i) :
    2 * Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) < Nat.card V := by
  classical
  by_contra hcon
  push Not at hcon
  have hV8 := two_pow_eight_le_card hV hn hψ hA h3
  have hππ : ∀ i, ψ a (ψ a i) = i := fun i => by
    have := congrArg (fun τ : Perm (Fin n) => τ i) (apply_mul_apply_eq_one (ψ := ψ) ha2)
    simpa [Perm.mul_apply] using this
  set p₁ : Fin n := ⟨0, by omega⟩
  obtain ⟨p₃, hp₃⟩ := exists_notMem_of_card_lt ({p₁, ψ a p₁} : Finset (Fin n))
    (by have := Finset.card_le_two (a := p₁) (b := ψ a p₁); omega)
  obtain ⟨p₅, hp₅⟩ := exists_notMem_of_card_lt ({p₁, ψ a p₁, p₃, ψ a p₃} : Finset (Fin n))
    (by have := Finset.card_le_four (a := p₁) (b := ψ a p₁) (c := p₃) (d := ψ a p₃); omega)
  obtain ⟨u, hu⟩ := exists_notMem_of_card_lt
    ({p₁, ψ a p₁, p₃, ψ a p₃, p₅, ψ a p₅} : Finset (Fin n))
    (by
      have := Finset.card_le_six (a := p₁) (b := ψ a p₁) (c := p₃) (d := ψ a p₃) (e := p₅)
        (f := ψ a p₅)
      omega)
  obtain ⟨v, hv⟩ := exists_notMem_of_card_lt
    (insert u ({p₁, ψ a p₁, p₃, ψ a p₃, p₅, ψ a p₅} : Finset (Fin n)))
    (by
      have h1 := Finset.card_insert_le u ({p₁, ψ a p₁, p₃, ψ a p₃, p₅, ψ a p₅} : Finset (Fin n))
      have := Finset.card_le_six (a := p₁) (b := ψ a p₁) (c := p₃) (d := ψ a p₃) (e := p₅)
        (f := ψ a p₅)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₃ hp₅ hu hv
  obtain ⟨h31, h32⟩ := hp₃
  obtain ⟨h51, h52, h53, h54⟩ := hp₅
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ := hu
  obtain ⟨hvu, hv1, hv2, hv3, hv4, hv5, hv6⟩ := hv
  have inj : ∀ {i j}, ψ a i = ψ a j → i = j := fun h => (ψ a).injective h
  have q12 : p₁ ≠ ψ a p₁ := (hfpf p₁).symm
  have q13 : p₁ ≠ p₃ := fun h => h31 h.symm
  have q15 : p₁ ≠ p₅ := fun h => h51 h.symm
  have q35 : p₃ ≠ p₅ := fun h => h53 h.symm
  have r12 : ψ a p₁ ≠ ψ a p₃ := fun h => q13 (inj h)
  have r13 : ψ a p₁ ≠ ψ a p₅ := fun h => q15 (inj h)
  have r35 : ψ a p₃ ≠ ψ a p₅ := fun h => q35 (inj h)
  have s1 : ψ a p₃ ≠ p₁ := fun h => h32 (by rw [← h, hππ])
  have s2 : ψ a p₅ ≠ p₁ := fun h => h52 (by rw [← h, hππ])
  have s3 : ψ a p₅ ≠ p₃ := fun h => h54 (by rw [← h, hππ])
  have s4 : ψ a p₁ ≠ p₅ := fun h => h52 h.symm
  have s5 : ψ a p₁ ≠ p₃ := fun h => h32 h.symm
  have s6 : ψ a p₃ ≠ p₅ := fun h => h54 h.symm
  set ξ₁ := swap p₁ p₃ * swap p₁ p₅ with hξ₁
  have hξ₁3 : ξ₁.IsThreeCycle := isThreeCycle_swap_mul_swap_same q13 q15 q35
  have hξ₂ : ψ a * ξ₁ * (ψ a)⁻¹ = swap (ψ a p₁) (ψ a p₃) * swap (ψ a p₁) (ψ a p₅) :=
    conj_swap_mul_swap _ _ _ _
  set γ := swap (ψ a p₃) (ψ a p₅) * swap u v with hγ
  have hγA : γ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap r35, sign_swap (Ne.symm hvu)]
    decide
  obtain ⟨x₁, hx₁⟩ := hA hξ₁3.mem_alternatingGroup
  obtain ⟨g, hg⟩ := hA hγA
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ↥H, x₂ = a * x₁ * a⁻¹ := ⟨_, rfl⟩
  have hψx₂ : ψ x₂ = swap (ψ a p₁) (ψ a p₃) * swap (ψ a p₁) (ψ a p₅) := by
    rw [hx₂, map_mul, map_mul, map_inv, hx₁, hξ₂]
  have hξ₂3 : (ψ x₂).IsThreeCycle := by
    rw [hx₂, map_mul, map_mul, map_inv, hx₁]
    exact isThreeCycle_conj hξ₁3 _
  have hfix₂ : ∀ i, i ≠ ψ a p₁ → i ≠ ψ a p₃ → i ≠ ψ a p₅ → ψ x₂ i = i := fun i h1 h2 h3 => by
    rw [hψx₂, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
  have hfixγ : ∀ i, i ≠ ψ a p₃ → i ≠ ψ a p₅ → i ≠ u → i ≠ v → ψ g i = i := fun i h1 h2 h3 h4 => by
    rw [hg, hγ, Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
  have c₁₂ : (x₁ : MulAut V) * x₂ = x₂ * x₁ := by
    refine (coe_eq_coe_of_apply_eq hψ (h₁ := x₁ * x₂) (h₂ := x₂ * x₁) ?_)
    rw [map_mul, map_mul, hx₁]
    exact (commute_swap_mul_swap (hfix₂ p₁ q12 s1.symm s2.symm)
      (hfix₂ p₃ s5.symm (hfpf p₃).symm s3.symm) (hfix₂ p₅ s4.symm s6.symm (hfpf p₅).symm)).symm
  have g₁ : (g : MulAut V) * x₁ * (g : MulAut V)⁻¹ = x₁ := by
    refine (coe_eq_coe_of_apply_eq hψ (h₁ := g * x₁ * g⁻¹) (h₂ := x₁) ?_)
    rw [map_mul, map_mul, map_inv, hx₁]
    have hc := commute_swap_mul_swap (a := p₁) (b := p₃) (c := p₅)
      (hfixγ p₁ s1.symm s2.symm (Ne.symm hu1) (Ne.symm hv1))
      (hfixγ p₃ (hfpf p₃).symm s3.symm (Ne.symm hu3) (Ne.symm hv3))
      (hfixγ p₅ s6.symm (hfpf p₅).symm (Ne.symm hu5) (Ne.symm hv5))
    rw [hc, mul_inv_cancel_right]
  have g₂ : (g : MulAut V) * x₂ * (g : MulAut V)⁻¹ = (x₂ : MulAut V)⁻¹ := by
    refine (coe_eq_coe_of_apply_eq hψ (h₁ := g * x₂ * g⁻¹) (h₂ := x₂⁻¹) ?_)
    rw [map_mul, map_mul, map_inv, map_inv, hψx₂, conj_swap_mul_swap,
      hfixγ _ r12 r13 (Ne.symm hu2) (Ne.symm hv2), hg, hγ]
    simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne (Ne.symm hu4) (Ne.symm hv4), swap_apply_left,
      swap_apply_of_ne_of_ne (Ne.symm hu6) (Ne.symm hv6), swap_apply_right, mul_inv_rev, swap_inv,
      swap_inv]
  have h₁ : (x₁ : MulAut V) ^ 3 = 1 := by
    have : x₁ ^ 3 = 1 := hψ (by rw [map_pow, hx₁, map_one, ← hξ₁3.orderOf, pow_orderOf_eq_one])
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have h₂ : (x₂ : MulAut V) ^ 3 = 1 := by
    have : x₂ ^ 3 = 1 := hψ (by rw [map_pow, map_one, ← hξ₂3.orderOf, pow_orderOf_eq_one])
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have f₁ := h3 x₁ (hx₁ ▸ hξ₁3)
  have f₂ := h3 x₂ hξ₂3
  have hV1 : 1 < Nat.card V := by omega
  have hX₁ : (x₁ : MulAut V) ≠ 1 := ne_one_of_fixV_eq_bot hV1 f₁
  have hX₂ : (x₂ : MulAut V) ≠ 1 := ne_one_of_fixV_eq_bot hV1 f₂
  have hy₂ := notMem_zpowers_of_conj h₂ hX₂ g₁ g₂
  have hcard := card_eq_card_fixV_mul_card_fixV hV h₁ h₂ c₁₂ hX₁ hy₂ f₂
  have hconj : (g : MulAut V) * (x₁ * x₂) * (g : MulAut V)⁻¹ =
      (x₁ : MulAut V) * (x₂ : MulAut V) ^ 2 := by
    have hinv : (x₂ : MulAut V)⁻¹ = (x₂ : MulAut V) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', h₂]
    calc (g : MulAut V) * (x₁ * x₂) * (g : MulAut V)⁻¹ =
          ((g : MulAut V) * x₁ * (g : MulAut V)⁻¹) * ((g : MulAut V) * x₂ * (g : MulAut V)⁻¹) := by
          group
      _ = (x₁ : MulAut V) * (x₂ : MulAut V) ^ 2 := by rw [g₁, g₂, hinv]
  have hcc : Nat.card (fixV (Subgroup.zpowers ((x₁ : MulAut V) * (x₂ : MulAut V) ^ 2))) =
      Nat.card (fixV (Subgroup.zpowers ((x₁ : MulAut V) * (x₂ : MulAut V)))) := by
    rw [← hconj, card_fixV_zpowers_conj]
  rw [f₁, Subgroup.card_bot, one_mul, ← hcc] at hcard
  have hainv : (a : MulAut V)⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  have hprod : (x₁ : MulAut V) * (x₂ : MulAut V) ^ 2 =
      ((x₁ : MulAut V) * (a : MulAut V) * (x₁ : MulAut V)⁻¹) * (a : MulAut V) := by
    have hinv : (x₂ : MulAut V) ^ 2 = (x₂ : MulAut V)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, h₂]
    rw [hinv, hx₂]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, hainv]
    group
  rw [hprod] at hcard
  set y : MulAut V := (x₁ : MulAut V) * (a : MulAut V) * (x₁ : MulAut V)⁻¹ with hy
  have hle : fixV (Subgroup.zpowers (a : MulAut V)) ⊓ fixV (Subgroup.zpowers y) ≤
      fixV (Subgroup.zpowers (y * (a : MulAut V))) := fun w hw => by
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    rw [mem_fixV_zpowers_iff] at hw1 hw2 ⊢
    rw [MulAut.mul_apply, hw1, hw2]
  have hcy : Nat.card (fixV (Subgroup.zpowers y)) =
      Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) := card_fixV_zpowers_conj _ _
  have hsup := CFSG.Quasithin.card_sup_mul_card_inf (fixV (Subgroup.zpowers (a : MulAut V)))
    (fixV (Subgroup.zpowers y))
  have hsupV : Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V)) ⊔ fixV (Subgroup.zpowers y)) ≤
      Nat.card V := Subgroup.card_le_card_group _
  have hinf := Subgroup.card_le_of_le hle
  set c := Nat.card (fixV (Subgroup.zpowers (y * (a : MulAut V))))
  set ca := Nat.card (fixV (Subgroup.zpowers (a : MulAut V)))
  rw [hcy] at hsup
  have k1 : ca * ca ≤ c * Nat.card V := by
    calc ca * ca = Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V)) ⊔
            fixV (Subgroup.zpowers y)) *
          Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V)) ⊓ fixV (Subgroup.zpowers y)) :=
          hsup.symm
      _ ≤ Nat.card V * c := Nat.mul_le_mul hsupV hinf
      _ = c * Nat.card V := mul_comm _ _
  have k2 : Nat.card V * Nat.card V ≤ 4 * (c * Nat.card V) := by
    calc Nat.card V * Nat.card V ≤ (2 * ca) * (2 * ca) := Nat.mul_le_mul hcon hcon
      _ = 4 * (ca * ca) := by ring
      _ ≤ 4 * (c * Nat.card V) := Nat.mul_le_mul_left _ k1
  have k3 : Nat.card V ≤ 4 * c := by
    have : Nat.card V * Nat.card V ≤ (4 * c) * Nat.card V := by rw [mul_assoc]; exact k2
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have k4 : Nat.card V * Nat.card V ≤ 16 * Nat.card V := by
    calc Nat.card V * Nat.card V ≤ (4 * c) * (4 * c) := Nat.mul_le_mul k3 k3
      _ = 16 * (c * c) := by ring
      _ = 16 * Nat.card V := by rw [hcard]
  have k5 : Nat.card V ≤ 16 := Nat.le_of_mul_le_mul_right k4 (by omega)
  omega

theorem ten_core {ψ : ↥H →* Perm (Fin 10)} (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 10) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hel : IsElemAbelian2 B) {p q : Fin 10}
    (hpq : p ≠ q)
    (horb : ∀ b : ↥H, (b : MulAut V) ∈ B → ψ b p = p ∧ ψ b q = q ∨ ψ b p = q ∧ ψ b q = p)
    (hmin : ∀ i, ∃ b : ↥H, (b : MulAut V) ∈ B ∧ ψ b i ≠ i)
    (hτ : ∀ b : ↥H, (b : MulAut V) ∈ B → ψ b ≠ swap p q) :
    Nat.card B * Nat.card (fixV B) < Nat.card V := by
  classical
  by_contra hcon
  push Not at hcon
  have hV8 := two_pow_eight_le_card hV (by norm_num) hψ hA h3
  set E : Subgroup (Perm (Fin 10)) := (B.subgroupOf H).map ψ with hE_def
  have hcardE : Nat.card E = Nat.card B := by
    rw [hE_def, Subgroup.card_map_of_injective hψ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hmemE : ∀ e ∈ E, ∃ b : ↥H, (b : MulAut V) ∈ B ∧ ψ b = e := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, Subgroup.mem_subgroupOf.1 hb, rfl⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hel.1 _ ha _ hb))
  have hE2 : ∀ a ∈ E, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact apply_mul_apply_eq_one (hel.2 _ ha)
  have hEexp : CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender.IsExp2 E := hE2
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne_ne (m := 8) (by norm_num) hpq
  have hfixΓ : ∀ e ∈ E, (∀ i, e (ι i) = ι i) → e = 1 := by
    intro e he hfix
    obtain ⟨b, hb, rfl⟩ := hmemE e he
    have hst : ψ b ∈ permSetStab (Set.range ι) := mem_permSetStab_of_pair hι (horb b hb)
    rcases eq_one_or_eq_swap_of_range_ne_ne hpq hι hst hfix with h | h
    · exact h
    · exact absurd h (hτ b hb)
  have hB16 : Nat.card B ≤ 16 := by
    have hEΓ : E ≤ permSetStab (Set.range ι) := by
      intro e he
      obtain ⟨b, hb, rfl⟩ := hmemE e he
      exact mem_permSetStab_of_pair hι (horb b hb)
    set r := (restrictPerm ι).comp (Subgroup.inclusion hEΓ) with hr
    have hrinj : Function.Injective r := by
      refine (injective_iff_map_eq_one _).2 fun e he => ?_
      have h1 : (e : Perm (Fin 10)) = 1 := hfixΓ e e.2 fun i => by
        have := restrictPerm_apply_apply ι (Subgroup.inclusion hEΓ e) i
        rw [show restrictPerm ι (Subgroup.inclusion hEΓ e) = r e from rfl, he] at this
        exact this.symm
      exact Subtype.ext h1
    have h1 := CFSG.Quasithin.G11.Harris.Ln2.card_le_of_elemAbelian_perm (B := r.range)
      (by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg r (Subtype.ext (hEc _ a.2 _ b.2)))
      (by
        rintro _ ⟨a, rfl⟩
        rw [← map_mul]
        have : a * a = 1 := Subtype.ext (hE2 _ a.2)
        rw [this, map_one])
    rw [Fintype.card_fin, show (2 : ℕ) ^ (8 / 2) = 16 by norm_num] at h1
    have h2 : Nat.card r.range = Nat.card E :=
      Nat.card_congr (MonoidHom.ofInjective hrinj).toEquiv.symm
    rw [← hcardE, ← h2]
    exact h1
  by_cases hcase : ∃ t : ↥H, (t : MulAut V) ∈ B ∧ t ≠ 1 ∧ ψ t p = p
  ·
    obtain ⟨t, htB, ht1, htp⟩ := hcase
    obtain ⟨u, hu⟩ : ∃ u, ψ t u ≠ u := by
      by_contra h
      push Not at h
      exact ht1 (hψ (by rw [map_one]; exact Equiv.ext h))
    have htq : ψ t q = q := by
      rcases horb t htB with h | h
      · exact h.2
      · exact absurd (h.1.symm.trans htp) (Ne.symm hpq)
    have hup : u ≠ p := fun h => hu (h ▸ htp)
    have huq : u ≠ q := fun h => hu (h ▸ htq)
    have ht := card_fixV_sq_of_apply_ne hV hψ hA h3 (hel.2 _ htB) hu htp
    have hB16' : 16 ≤ Nat.card B := by
      set c := Nat.card (fixV (Subgroup.zpowers (t : MulAut V)))
      have hle : Nat.card (fixV B) ≤ c := Subgroup.card_le_of_le (fixV_zpowers_le htB)
      have hc16 : 16 ≤ c := by
        by_contra h
        have h1 : c ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      have h1 : c * c ≤ Nat.card B * c :=
        calc c * c = Nat.card V := by rw [← ht]; ring
          _ ≤ Nat.card B * Nat.card (fixV B) := hcon
          _ ≤ Nat.card B * c := Nat.mul_le_mul_left _ hle
      have h2 : c ≤ Nat.card B := Nat.le_of_mul_le_mul_right h1 (by omega)
      omega
    have hE16 : Nat.card E = 16 := by omega
    have horbu : Nat.card (orbit E u) ≤ 4 := by
      obtain ⟨k, hk⟩ := hEexp.card_orbit u
      have hsub : orbit E u ⊆ Set.range ι := by
        rintro _ ⟨e, rfl⟩
        obtain ⟨b, hb, hbe⟩ := hmemE e e.2
        have hst : ψ b ∈ permSetStab (Set.range ι) := mem_permSetStab_of_pair hι (horb b hb)
        have huΓ : u ∈ Set.range ι := (hι u).2 ⟨hup, huq⟩
        change (e : Perm (Fin 10)) u ∈ Set.range ι
        rw [← hbe]
        exact (hst u).2 huΓ
      have hΓ8 : (Set.range ι).ncard = 8 := by
        rw [Set.ncard_range_of_injective ι.injective, Nat.card_eq_fintype_card, Fintype.card_fin]
      have hle8 : Nat.card (orbit E u) ≤ 8 := by
        rw [Nat.card_coe_set_eq, ← hΓ8]
        exact Set.ncard_le_ncard hsub
      by_contra hgt
      have hk3 : 3 ≤ k := by
        by_contra h
        have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h8 : Nat.card (orbit E u) = 8 := by
        have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
        omega
      have heq : orbit E u = Set.range ι :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [hΓ8, ← Nat.card_coe_set_eq, h8])
      have hstab : stabilizer E u = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        rw [Subgroup.mem_bot]
        apply Subtype.ext
        refine hfixΓ _ g.2 fun i => ?_
        have hi : ι i ∈ orbit E u := heq ▸ ⟨i, rfl⟩
        exact hEexp.smul_eq_of_mem_stabilizer hi hg
      have h1 := Subgroup.card_mul_index (stabilizer E u)
      rw [index_stabilizer, hstab, Subgroup.card_bot, one_mul, ← Nat.card_coe_set_eq, h8,
        hE16] at h1
      omega
    have hpair : Nat.card ↥({p, q} : Set (Fin 10)) = 2 := by
      rw [Nat.card_coe_set_eq, Set.ncard_pair hpq]
    have hpq_mem : ∀ e ∈ E, e p ∈ ({p, q} : Set (Fin 10)) := fun e he => by
      obtain ⟨b, hb, rfl⟩ := hmemE e he
      rcases horb b hb with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    let f : ↥E → ↥(orbit E u) × ↥({p, q} : Set (Fin 10)) := fun e =>
      (⟨e • u, MulAction.mem_orbit u e⟩, ⟨(e : Perm (Fin 10)) p, hpq_mem e e.2⟩)
    have hlt : Fintype.card (↥(orbit E u) × ↥({p, q} : Set (Fin 10))) < Fintype.card ↥E := by
      rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card, hpair, hE16]
      omega
    obtain ⟨e₁, e₂, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
    have hfu : e₁ • u = e₂ • u := congrArg (fun z => (z.1 : Fin 10)) hf
    have hfp : (e₁ : Perm (Fin 10)) p = (e₂ : Perm (Fin 10)) p :=
      congrArg (fun z => (z.2 : Fin 10)) hf
    set e := e₁⁻¹ * e₂ with he
    have he1 : e ≠ 1 := fun h => hne (by rw [he] at h; exact (inv_mul_eq_one.1 h))
    have heu : (e : Perm (Fin 10)) u = u := by
      change ((e₁ : Perm (Fin 10))⁻¹ * e₂) u = u
      rw [Perm.mul_apply, ← show (e₁ : Perm (Fin 10)) u = (e₂ : Perm (Fin 10)) u from hfu,
        perm_inv_apply_apply]
    have hep : (e : Perm (Fin 10)) p = p := by
      change ((e₁ : Perm (Fin 10))⁻¹ * e₂) p = p
      rw [Perm.mul_apply, ← hfp, perm_inv_apply_apply]
    obtain ⟨b, hbB, hbe⟩ := hmemE e e.2
    have hb1 : b ≠ 1 := by
      rintro rfl
      apply he1
      apply Subtype.ext
      rw [← hbe, map_one]
      rfl
    exact false_of_core3 hV (by norm_num) hψ hA h3 hel hB16 hcon (t := t) (b := b) htB hbB hb1
      htp hu (by rw [hbe]; exact heu) (by rw [hbe]; exact hep)
  ·
    push Not at hcase
    obtain ⟨a, haB, hap⟩ := hmin p
    have hapq : ψ a p = q := by
      rcases horb a haB with h | h
      · exact absurd h.1 hap
      · exact h.1
    have haq : ψ a q = p := by
      rcases horb a haB with h | h
      · exact absurd h.1 hap
      · exact h.2
    have hBa : ∀ b : ↥H, (b : MulAut V) ∈ B → b = 1 ∨ b = a := by
      intro b hb
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      right
      have hbp : ψ b p = q := by
        rcases horb b hb with h | h
        · exact absurd h.1 (hcase b hb hb1)
        · exact h.1
      have hab : (a : MulAut V) * b ∈ B := B.mul_mem haB hb
      have hab1 : a * b = 1 := by
        by_contra hne
        apply hcase (a * b) hab hne
        rw [map_mul, Perm.mul_apply, hbp, haq]
      have ha2 : (a : MulAut V) ^ 2 = 1 := hel.2 _ haB
      have : (a : MulAut V) * a = 1 := by rw [← pow_two]; exact ha2
      have h1 : (b : MulAut V) = a := by
        have h2 : (a : MulAut V) * b = 1 := congrArg Subtype.val hab1
        calc (b : MulAut V) = (a : MulAut V) * a * b := by rw [this, one_mul]
          _ = a := by rw [mul_assoc, h2, mul_one]
      exact Subtype.ext h1
    have hfpf : ∀ i, ψ a i ≠ i := by
      intro i
      obtain ⟨b, hbB, hbi⟩ := hmin i
      rcases hBa b hbB with rfl | rfl
      · exact absurd (by rw [map_one]; rfl) hbi
      · exact hbi
    have hB2 : Nat.card B ≤ 2 := by
      have hle : B ≤ Subgroup.zpowers (a : MulAut V) := fun b hb => by
        rcases hBa ⟨b, hBH hb⟩ hb with h | h
        · rw [show b = 1 from congrArg Subtype.val h]
          exact Subgroup.one_mem _
        · rw [show b = (a : MulAut V) from congrArg Subtype.val h]
          exact Subgroup.mem_zpowers _
      calc Nat.card B ≤ Nat.card (Subgroup.zpowers (a : MulAut V)) := Subgroup.card_le_of_le hle
        _ = orderOf (a : MulAut V) := Nat.card_zpowers _
        _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (hel.2 _ haB)
    have hfixB : Nat.card (fixV B) ≤ Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) :=
      Subgroup.card_le_of_le (fixV_zpowers_le haB)
    have h1 := two_mul_card_fixV_lt_of_fpf hV (by norm_num) hψ hA h3 (hel.2 _ haB) hfpf
    have h2 : Nat.card B * Nat.card (fixV B) ≤
        2 * Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) := Nat.mul_le_mul hB2 hfixB
    omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
