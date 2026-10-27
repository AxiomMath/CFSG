module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPstd
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2U3

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaEnd CFSG.EvenSmallLie.UnitarySix.YamadaPar
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem lu_mul (a b f c d e a' b' f' c' d' e' : CFSG.Fischer.F4) :
    lu a b f c d e * lu a' b' f' c' d' e' =
      lu (a + a') (b + f * a' + b') (f + f') (c + d * a' + e * b' + c') (d + e * f' + d')
        (e + e') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_lu, coe_lu, coe_lu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem eq_lu_of_mem {y : SL(4, CFSG.Fischer.F4)} (hy : y ∈ pstd CFSG.Fischer.F4) :
    y = lu (y 1 0) (y 2 0) (y 2 1) (y 3 0) (y 3 1) (y 3 2) :=
  eq_lu_of_isLowerUni (mem_pstd_iff.mp hy)

theorem exists_lu_of_mem {y : SL(4, CFSG.Fischer.F4)} (hy : y ∈ pstd CFSG.Fischer.F4) :
    ∃ a b f c d e, y = lu a b f c d e := ⟨_, _, _, _, _, _, eq_lu_of_mem hy⟩

@[expose] noncomputable def radR : Subgroup SL(4, CFSG.Fischer.F4) :=
  pstd CFSG.Fischer.F4 ⊓ conjR (pstd CFSG.Fischer.F4)
    (sY CFSG.Fischer.F4 0 * sY CFSG.Fischer.F4 2)

theorem radR_le : radR ≤ pstd CFSG.Fischer.F4 := inf_le_left

theorem lu_mem_radR_iff (a b f c d e : CFSG.Fischer.F4) :
    lu a b f c d e ∈ radR ↔ a = 0 ∧ e = 0 := by
  rw [radR, Subgroup.mem_inf, lu_mem_conjR_u₀]
  exact ⟨fun h => h.2, fun h => ⟨lu_mem_pstd _ _ _ _ _ _, h⟩⟩

theorem card_radR : Nat.card radR = 2 ^ 8 := by
  rw [radR, card_pstd_inf_u₀, natCard_F4]; norm_num

@[expose] noncomputable def piR :
    pstd CFSG.Fischer.F4 →* Multiplicative (CFSG.Fischer.F4 × CFSG.Fischer.F4) where
  toFun x := Multiplicative.ofAdd (((x : SL(4, CFSG.Fischer.F4)) 1 0),
    ((x : SL(4, CFSG.Fischer.F4)) 3 2))
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' x y := by
    obtain ⟨a, b, f, c, d, e, hx⟩ := exists_lu_of_mem x.2
    obtain ⟨a', b', f', c', d', e', hy⟩ := exists_lu_of_mem y.2
    have hxy : ((x * y : pstd CFSG.Fischer.F4) : SL(4, CFSG.Fischer.F4)) =
        lu (a + a') (b + f * a' + b') (f + f') (c + d * a' + e * b' + c') (d + e * f' + d')
          (e + e') := by
      rw [Subgroup.coe_mul, hx, hy, lu_mul]
    rw [hxy, hx, hy]
    obtain ⟨h1, -, -, -, -, h6⟩ := lu_apply_entries (a + a') (b + f * a' + b') (f + f')
      (c + d * a' + e * b' + c') (d + e * f' + d') (e + e')
    obtain ⟨g1, -, -, -, -, g6⟩ := lu_apply_entries a b f c d e
    obtain ⟨k1, -, -, -, -, k6⟩ := lu_apply_entries a' b' f' c' d' e'
    rw [h1, h6, g1, g6, k1, k6]
    rfl

theorem piR_lu (a b f c d e : CFSG.Fischer.F4) :
    piR ⟨lu a b f c d e, lu_mem_pstd _ _ _ _ _ _⟩ = Multiplicative.ofAdd (a, e) := by
  obtain ⟨h1, -, -, -, -, h6⟩ := lu_apply_entries a b f c d e
  change Multiplicative.ofAdd ((lu a b f c d e : SL(4, CFSG.Fischer.F4)) 1 0,
    (lu a b f c d e : SL(4, CFSG.Fischer.F4)) 3 2) = _
  rw [h1, h6]

theorem piR_eq_one_iff (x : pstd CFSG.Fischer.F4) :
    piR x = 1 ↔ (x : SL(4, CFSG.Fischer.F4)) ∈ radR := by
  obtain ⟨a, b, f, c, d, e, hx⟩ := exists_lu_of_mem x.2
  have hx' : x = ⟨lu a b f c d e, lu_mem_pstd _ _ _ _ _ _⟩ := Subtype.ext hx
  rw [hx', piR_lu, lu_mem_radR_iff]
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, toAdd_one, Prod.mk_eq_zero] at this
    exact this
  · rintro ⟨rfl, rfl⟩
    rfl

theorem lu_comm_iff (b f c d a β φ γ δ ε : CFSG.Fischer.F4) :
    lu 0 b f c d 0 * lu a β φ γ δ ε = lu a β φ γ δ ε * lu 0 b f c d 0 ↔
      f * a = 0 ∧ d * a = ε * b ∧ ε * f = 0 := by
  rw [lu_mul, lu_mul]
  constructor
  · intro h
    obtain ⟨-, h2, -, h4, h5, -⟩ := lu_injective h
    refine ⟨?_, ?_, ?_⟩
    · linear_combination h2
    · linear_combination h4
    · linear_combination (-1 : CFSG.Fischer.F4) * h5
  · rintro ⟨h1, h2, h3⟩
    congr 1
    · ring
    · linear_combination h1
    · ring
    · linear_combination h2
    · linear_combination (-1 : CFSG.Fischer.F4) * h3
    · ring

theorem eq_lu_of_mem_radR {r : SL(4, CFSG.Fischer.F4)} (hr : r ∈ radR) :
    r = lu 0 (r 2 0) (r 2 1) (r 3 0) (r 3 1) 0 := by
  have h := eq_lu_of_mem (radR_le hr)
  have h' := hr
  rw [h, lu_mem_radR_iff] at h'
  rw [h'.1, h'.2] at h
  exact h

theorem card_F4_prod : Nat.card (CFSG.Fischer.F4 × CFSG.Fischer.F4) = 16 := by
  rw [Nat.card_prod, natCard_F4]

theorem card_F4_prod' :
    Nat.card (Multiplicative (CFSG.Fischer.F4 × CFSG.Fischer.F4)) = 16 := card_F4_prod

theorem card_cent_radR_le {E₀ : Subgroup SL(4, CFSG.Fischer.F4)} (hE₀ : E₀ ≤ radR)
    {e : SL(4, CFSG.Fischer.F4)} (he : e ∈ pstd CFSG.Fischer.F4) (heR : e ∉ radR)
    (hc : ∀ r ∈ E₀, r * e = e * r) : Nat.card E₀ ≤ 16 := by
  obtain ⟨a, β, φ, γ, δ, ε, rfl⟩ := exists_lu_of_mem he
  rw [lu_mem_radR_iff, not_and_or] at heR
  have key : ∀ r ∈ E₀, (r 2 1 = 0) ∧ r 3 1 * a = ε * r 2 0 ∧ (a = 0 → r 2 0 = 0) := by
    intro r hr
    have hcr := hc r hr
    rw [eq_lu_of_mem_radR (hE₀ hr), lu_comm_iff] at hcr
    obtain ⟨h1, h2, h3⟩ := hcr
    refine ⟨?_, h2, fun ha => ?_⟩
    · rcases heR with ha | hε
      · exact (mul_eq_zero.mp h1).resolve_right ha
      · exact (mul_eq_zero.mp h3).resolve_left hε
    · rw [ha, mul_zero] at h2
      exact (mul_eq_zero.mp h2.symm).resolve_left (heR.resolve_left (not_not.mpr ha))
  by_cases ha : a = 0
  · refine (Nat.card_le_card_of_injective (fun r : E₀ => ((r : SL(4, CFSG.Fischer.F4)) 3 0,
      (r : SL(4, CFSG.Fischer.F4)) 3 1)) fun r r' hrr => ?_).trans card_F4_prod.le
    obtain ⟨k1, k2, k3⟩ := key r r.2
    obtain ⟨k1', k2', k3'⟩ := key r' r'.2
    have e1 := congrArg Prod.fst hrr
    have e2 := congrArg Prod.snd hrr
    simp only at e1 e2
    apply Subtype.ext
    rw [eq_lu_of_mem_radR (hE₀ r.2), eq_lu_of_mem_radR (hE₀ r'.2), k1, k1', k3 ha, k3' ha, e1, e2]
  · refine (Nat.card_le_card_of_injective (fun r : E₀ => ((r : SL(4, CFSG.Fischer.F4)) 2 0,
      (r : SL(4, CFSG.Fischer.F4)) 3 0)) fun r r' hrr => ?_).trans card_F4_prod.le
    obtain ⟨k1, k2, -⟩ := key r r.2
    obtain ⟨k1', k2', -⟩ := key r' r'.2
    have e1 := congrArg Prod.fst hrr
    have e2 := congrArg Prod.snd hrr
    simp only at e1 e2
    have hd : (r : SL(4, CFSG.Fischer.F4)) 3 1 = (r' : SL(4, CFSG.Fischer.F4)) 3 1 := by
      have : (r : SL(4, CFSG.Fischer.F4)) 3 1 * a = (r' : SL(4, CFSG.Fischer.F4)) 3 1 * a := by
        rw [k2, k2', e1]
      exact mul_right_cancel₀ ha this
    apply Subtype.ext
    rw [eq_lu_of_mem_radR (hE₀ r.2), eq_lu_of_mem_radR (hE₀ r'.2), k1, k1', e1, e2, hd]

theorem card_cent_radR_le_four {E₀ : Subgroup SL(4, CFSG.Fischer.F4)} (hE₀ : E₀ ≤ radR)
    {β φ γ δ β' φ' γ' δ' : CFSG.Fischer.F4}
    (hc₁ : ∀ r ∈ E₀, r * lu 1 β φ γ δ 0 = lu 1 β φ γ δ 0 * r)
    (hc₂ : ∀ r ∈ E₀, r * lu 0 β' φ' γ' δ' 1 = lu 0 β' φ' γ' δ' 1 * r) : Nat.card E₀ ≤ 4 := by
  have key : ∀ r ∈ E₀, r 2 0 = 0 ∧ r 2 1 = 0 ∧ r 3 1 = 0 := by
    intro r hr
    have h1 := hc₁ r hr
    have h2 := hc₂ r hr
    rw [eq_lu_of_mem_radR (hE₀ hr), lu_comm_iff] at h1 h2
    obtain ⟨a1, a2, -⟩ := h1
    obtain ⟨-, b2, -⟩ := h2
    refine ⟨?_, ?_, ?_⟩
    · simpa using b2.symm
    · simpa using a1
    · simpa using a2
  refine (Nat.card_le_card_of_injective (fun r : E₀ => (r : SL(4, CFSG.Fischer.F4)) 3 0)
    fun r r' hrr => ?_).trans natCard_F4.le
  obtain ⟨k1, k2, k3⟩ := key r r.2
  obtain ⟨k1', k2', k3'⟩ := key r' r'.2
  apply Subtype.ext
  simp only at hrr
  rw [eq_lu_of_mem_radR (hE₀ r.2), eq_lu_of_mem_radR (hE₀ r'.2), k1, k2, k3, k1', k2', k3', hrr]

theorem card_le_card_mul_of_hom {A B : Type*} [Group A] [Group B] [Finite A] (g : A →* B) :
    Nat.card A = Nat.card g.range * Nat.card g.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]

theorem jUnique_pstd {E : Subgroup SL(4, CFSG.Fischer.F4)} (hE : E ≤ pstd CFSG.Fischer.F4)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : 2 ^ 8 ≤ Nat.card E) : E = radR := by
  set g : E →* Multiplicative (CFSG.Fischer.F4 × CFSG.Fischer.F4) :=
    piR.comp (Subgroup.inclusion hE) with hgdef
  have hgx : ∀ x : E, g x = piR ⟨x, hE x.2⟩ := fun x => rfl
  have hker : ∀ x : E, x ∈ g.ker ↔ (x : SL(4, CFSG.Fischer.F4)) ∈ radR := fun x => by
    rw [MonoidHom.mem_ker, hgx, piR_eq_one_iff]
  have hE' := card_le_card_mul_of_hom g
  set K₀ : Subgroup SL(4, CFSG.Fischer.F4) := g.ker.map E.subtype with hK₀
  have hK₀R : K₀ ≤ radR := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hker x).mp hx
  have hK₀card : Nat.card K₀ = Nat.card g.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hK₀E : K₀ ≤ E := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hrange : Nat.card g.range ≤ 16 := (Subgroup.card_le_card_group _).trans card_F4_prod'.le
  by_cases hbot : g.range = ⊥
  ·
    have hER : E ≤ radR := fun x hx => by
      have : g ⟨x, hx⟩ ∈ g.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (hker ⟨x, hx⟩).mp this
    exact Subgroup.eq_of_le_of_card_ge hER (by rw [card_radR]; exact hcard)
  · exfalso
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    obtain ⟨e, rfl⟩ := hy
    have heR : (e : SL(4, CFSG.Fischer.F4)) ∉ radR := by
      intro h
      apply hy1
      apply Subtype.ext
      exact (hker e).mpr h
    have hk16 : Nat.card g.ker ≤ 16 := by
      rw [← hK₀card]
      exact card_cent_radR_le hK₀R (hE e.2) heR fun r hr => hc r (hK₀E hr) e e.2
    have hle : Nat.card g.range * Nat.card g.ker ≤ 2 ^ 8 := by
      calc Nat.card g.range * Nat.card g.ker ≤ 16 * 16 := Nat.mul_le_mul hrange hk16
        _ = 2 ^ 8 := by norm_num
    have h256 : Nat.card g.range * Nat.card g.ker = 2 ^ 8 := le_antisymm hle (hE' ▸ hcard)
    have hr16 : Nat.card g.range = 16 := by
      by_contra hne
      have : Nat.card g.range ≤ 15 := by omega
      have := Nat.mul_le_mul this hk16
      omega
    have htop : g.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hr16, card_F4_prod'])
    obtain ⟨e₁, he₁⟩ : g.range.carrier (Multiplicative.ofAdd (1, 0)) := by
      rw [htop]; trivial
    obtain ⟨e₂, he₂⟩ : g.range.carrier (Multiplicative.ofAdd (0, 1)) := by
      rw [htop]; trivial
    have hl : ∀ x : E, ∀ p q : CFSG.Fischer.F4, g x = Multiplicative.ofAdd (p, q) →
        ∃ β φ γ δ, (x : SL(4, CFSG.Fischer.F4)) = lu p β φ γ δ q := by
      intro x p q hx
      obtain ⟨a, b, f, c, d, e', hxl⟩ := exists_lu_of_mem (hE x.2)
      have h' : g x = Multiplicative.ofAdd (a, e') := by
        rw [hgx]
        have : (⟨x, hE x.2⟩ : pstd CFSG.Fischer.F4) = ⟨lu a b f c d e', lu_mem_pstd _ _ _ _ _ _⟩ :=
          Subtype.ext hxl
        rw [this, piR_lu]
      rw [h'] at hx
      have := congrArg Multiplicative.toAdd hx
      simp only [toAdd_ofAdd, Prod.mk.injEq] at this
      exact ⟨b, f, c, d, by rw [hxl, this.1, this.2]⟩
    obtain ⟨β, φ, γ, δ, h₁⟩ := hl e₁ 1 0 he₁
    obtain ⟨β', φ', γ', δ', h₂⟩ := hl e₂ 0 1 he₂
    have hk4 : Nat.card g.ker ≤ 4 := by
      rw [← hK₀card]
      refine card_cent_radR_le_four hK₀R (β := β) (φ := φ) (γ := γ) (δ := δ) (β' := β')
        (φ' := φ') (γ' := γ') (δ' := δ') (fun r hr => ?_) (fun r hr => ?_)
      · rw [← h₁]; exact hc r (hK₀E hr) e₁ e₁.2
      · rw [← h₂]; exact hc r (hK₀E hr) e₂ e₂.2
    rw [hr16] at h256
    omega

theorem card_msigma_radR : Nat.card (msigma CFSG.Fischer.F4 ⊓ radR : Subgroup _) = 2 ^ 4 := by
  rw [radR, ← inf_assoc]
  exact card_msigma_inf_u₀ natCard_F4

theorem lu_mem_msigma_e {a b f c d e : CFSG.Fischer.F4}
    (h : lu a b f c d e ∈ msigma CFSG.Fischer.F4) :
    e = a ^ 2 := ((lu_mem_msigma_iff a b f c d e).mp h).2.1

theorem eq_zero_or_one_of_sq {c : CFSG.Fischer.F4} (h : c ^ 2 = c) : c = 0 ∨ c = 1 := by
  have : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem msigma_radR_entries {r : SL(4, CFSG.Fischer.F4)} (hr : r ∈ msigma CFSG.Fischer.F4)
    (hrR : r ∈ radR) : r 3 1 = r 2 0 ^ 2 ∧ (r 2 1 = 0 ∨ r 2 1 = 1) ∧ (r 3 0 = 0 ∨ r 3 0 = 1) := by
  have h := eq_lu_of_mem_radR hrR
  rw [h, lu_mem_msigma_iff] at hr
  obtain ⟨hd, -, -, -, hf, hc⟩ := hr
  refine ⟨by rw [hd]; ring, eq_zero_or_one_of_sq hf, eq_zero_or_one_of_sq ?_⟩
  simpa using hc

theorem eq_zero_or_eq_of_sq {a b : CFSG.Fischer.F4} (ha : a ≠ 0) (h : b ^ 2 * a = a ^ 2 * b) :
    b = 0 ∨ b = a := by
  have : b * (b - a) * a = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (sub_eq_zero.mp h2)
  · exact absurd h1 ha

theorem omega_ne_zero : CFSG.Fischer.F4.ω ≠ 0 := fun h => by
  have := congrArg CFSG.Fischer.F4.code h
  exact absurd this (by decide)

theorem omega_ne_one : CFSG.Fischer.F4.ω ≠ 1 := fun h => by
  have := congrArg CFSG.Fischer.F4.code h
  exact absurd this (by decide)

theorem jUnique_pSig {E : Subgroup SL(4, CFSG.Fischer.F4)}
    (hE : E ≤ msigma CFSG.Fischer.F4 ⊓ pstd CFSG.Fischer.F4)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : 2 ^ 4 ≤ Nat.card E) :
    E = msigma CFSG.Fischer.F4 ⊓ radR := by
  have hEP : E ≤ pstd CFSG.Fischer.F4 := hE.trans inf_le_right
  have hEσ : E ≤ msigma CFSG.Fischer.F4 := hE.trans inf_le_left
  set g : E →* Multiplicative (CFSG.Fischer.F4 × CFSG.Fischer.F4) :=
    piR.comp (Subgroup.inclusion hEP) with hgdef
  have hgx : ∀ x : E, g x = piR ⟨x, hEP x.2⟩ := fun x => rfl
  have hker : ∀ x : E, x ∈ g.ker ↔ (x : SL(4, CFSG.Fischer.F4)) ∈ radR := fun x => by
    rw [MonoidHom.mem_ker, hgx, piR_eq_one_iff]
  have hE' := card_le_card_mul_of_hom g
  have hl : ∀ x : E, ∃ a β φ γ δ, (x : SL(4, CFSG.Fischer.F4)) = lu a β φ γ δ (a ^ 2) ∧
      g x = Multiplicative.ofAdd (a, a ^ 2) := by
    intro x
    obtain ⟨a, b, f, c, d, e', hxl⟩ := exists_lu_of_mem (hEP x.2)
    have he' : e' = a ^ 2 := lu_mem_msigma_e (hxl ▸ hEσ x.2)
    subst he'
    refine ⟨a, b, f, c, d, hxl, ?_⟩
    rw [hgx]
    have : (⟨x, hEP x.2⟩ : pstd CFSG.Fischer.F4) =
        ⟨lu a b f c d (a ^ 2), lu_mem_pstd _ _ _ _ _ _⟩ := Subtype.ext hxl
    rw [this, piR_lu]
  set K₀ : Subgroup SL(4, CFSG.Fischer.F4) := g.ker.map E.subtype with hK₀
  have hK₀R : K₀ ≤ radR := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hker x).mp hx
  have hK₀E : K₀ ≤ E := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hK₀card : Nat.card K₀ = Nat.card g.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hfst : Function.Injective (fun y : g.range =>
      (Multiplicative.toAdd (y : Multiplicative (CFSG.Fischer.F4 × CFSG.Fischer.F4))).1) := by
    rintro ⟨y, x, rfl⟩ ⟨y', x', rfl⟩ h
    obtain ⟨a, -, -, -, -, -, ha⟩ := hl x
    obtain ⟨a', -, -, -, -, -, ha'⟩ := hl x'
    simp only [ha, ha', toAdd_ofAdd] at h
    apply Subtype.ext
    simp only [ha, ha', h]
  have hrange : Nat.card g.range ≤ 4 :=
    (Nat.card_le_card_of_injective _ hfst).trans natCard_F4.le
  by_cases hbot : g.range = ⊥
  · have hER : E ≤ msigma CFSG.Fischer.F4 ⊓ radR := fun x hx => by
      have : g ⟨x, hx⟩ ∈ g.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact ⟨hEσ hx, (hker ⟨x, hx⟩).mp this⟩
    exact Subgroup.eq_of_le_of_card_ge hER (by rw [card_msigma_radR]; exact hcard)
  · exfalso
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    obtain ⟨e, rfl⟩ := hy
    obtain ⟨a, β, φ, γ, δ, he, hge⟩ := hl e
    have ha : a ≠ 0 := by
      rintro rfl
      have h1 : g e = 1 := by rw [hge]; simp
      exact hy1 (Subtype.ext h1)
    have key : ∀ r ∈ K₀, r 2 1 = 0 ∧ (r 2 0 = 0 ∨ r 2 0 = a) ∧ (r 3 0 = 0 ∨ r 3 0 = 1) ∧
        r 3 1 = r 2 0 ^ 2 := by
      intro r hr
      have hrσ := hEσ (hK₀E hr)
      obtain ⟨hd, -, hc'⟩ := msigma_radR_entries hrσ (hK₀R hr)
      have hcomm := hc r (hK₀E hr) e e.2
      rw [eq_lu_of_mem_radR (hK₀R hr), he, lu_comm_iff] at hcomm
      obtain ⟨h1, h2, -⟩ := hcomm
      have hf : r 2 1 = 0 := (mul_eq_zero.mp h1).resolve_right ha
      refine ⟨hf, eq_zero_or_eq_of_sq ha ?_, hc', hd⟩
      rw [← hd]; exact h2
    have hk4 : Nat.card g.ker ≤ 4 := by
      rw [← hK₀card]
      classical
      refine (Nat.card_le_card_of_injective (fun r : K₀ =>
        (decide ((r : SL(4, CFSG.Fischer.F4)) 2 0 = 0),
          decide ((r : SL(4, CFSG.Fischer.F4)) 3 0 = 0))) fun r r' hrr => ?_).trans
        (by simp)
      simp only [Prod.mk.injEq, decide_eq_decide] at hrr
      obtain ⟨k1, k2, k3, k4⟩ := key r r.2
      obtain ⟨k1', k2', k3', k4'⟩ := key r' r'.2
      have hb : (r : SL(4, CFSG.Fischer.F4)) 2 0 = (r' : SL(4, CFSG.Fischer.F4)) 2 0 := by
        rcases k2 with h | h <;> rcases k2' with h' | h'
        · rw [h, h']
        · exact absurd (hrr.1.mp h) (by rw [h']; exact ha)
        · exact absurd (hrr.1.mpr h') (by rw [h]; exact ha)
        · rw [h, h']
      have hc0 : (r : SL(4, CFSG.Fischer.F4)) 3 0 = (r' : SL(4, CFSG.Fischer.F4)) 3 0 := by
        rcases k3 with h | h <;> rcases k3' with h' | h'
        · rw [h, h']
        · exact absurd (hrr.2.mp h) (by rw [h']; exact one_ne_zero)
        · exact absurd (hrr.2.mpr h') (by rw [h]; exact one_ne_zero)
        · rw [h, h']
      apply Subtype.ext
      rw [eq_lu_of_mem_radR (hK₀R r.2), eq_lu_of_mem_radR (hK₀R r'.2), k1, k1', k4, k4', hb, hc0]
    have hle : Nat.card g.range * Nat.card g.ker ≤ 2 ^ 4 := by
      calc Nat.card g.range * Nat.card g.ker ≤ 4 * 4 := Nat.mul_le_mul hrange hk4
        _ = 2 ^ 4 := by norm_num
    have h16 : Nat.card g.range * Nat.card g.ker = 2 ^ 4 := le_antisymm hle (hE' ▸ hcard)
    have hr4 : Nat.card g.range = 4 := by
      by_contra hne
      have : Nat.card g.range ≤ 3 := by omega
      have := Nat.mul_le_mul this hk4
      omega
    have hbij : Function.Bijective (fun y : g.range =>
        (Multiplicative.toAdd (y : Multiplicative (CFSG.Fischer.F4 × CFSG.Fischer.F4))).1) :=
      (Function.Injective.bijective_of_nat_card_le hfst (by rw [hr4, natCard_F4]))
    have hpt : ∀ p : CFSG.Fischer.F4, ∃ x : E, ∃ β φ γ δ,
        (x : SL(4, CFSG.Fischer.F4)) = lu p β φ γ δ (p ^ 2) := by
      intro p
      obtain ⟨⟨y, x, rfl⟩, hy⟩ := hbij.2 p
      obtain ⟨a', β', φ', γ', δ', hx, hgx'⟩ := hl x
      simp only [hgx', toAdd_ofAdd] at hy
      exact ⟨x, β', φ', γ', δ', by rw [hx, hy]⟩
    obtain ⟨x₁, β₁, φ₁, γ₁, δ₁, hx₁⟩ := hpt 1
    obtain ⟨x₂, β₂, φ₂, γ₂, δ₂, hx₂⟩ := hpt CFSG.Fischer.F4.ω
    have key₂ : ∀ r ∈ K₀, r 2 0 = 0 := by
      intro r hr
      have hrσ := hEσ (hK₀E hr)
      obtain ⟨hd, -, -⟩ := msigma_radR_entries hrσ (hK₀R hr)
      have hb : ∀ (p β φ γ δ : CFSG.Fischer.F4), p ≠ 0 →
          r * lu p β φ γ δ (p ^ 2) = lu p β φ γ δ (p ^ 2) * r → r 2 0 = 0 ∨ r 2 0 = p := by
        intro p β φ γ δ hp hcomm
        rw [eq_lu_of_mem_radR (hK₀R hr), lu_comm_iff] at hcomm
        exact eq_zero_or_eq_of_sq hp (by rw [← hd]; exact hcomm.2.1)
      have h1 := hb 1 β₁ φ₁ γ₁ δ₁ one_ne_zero (by rw [← hx₁]; exact hc r (hK₀E hr) x₁ x₁.2)
      have h2 := hb _ β₂ φ₂ γ₂ δ₂ omega_ne_zero (by rw [← hx₂]; exact hc r (hK₀E hr) x₂ x₂.2)
      rcases h1 with h1 | h1
      · exact h1
      · rcases h2 with h2 | h2
        · exact h2
        · exact absurd (h1.symm.trans h2) (Ne.symm omega_ne_one)
    have hk2 : Nat.card g.ker ≤ 2 := by
      rw [← hK₀card]
      classical
      refine (Nat.card_le_card_of_injective (fun r : K₀ =>
        decide ((r : SL(4, CFSG.Fischer.F4)) 3 0 = 0)) fun r r' hrr => ?_).trans (by simp)
      simp only [decide_eq_decide] at hrr
      obtain ⟨k1, -, k3, k4⟩ := key r r.2
      obtain ⟨k1', -, k3', k4'⟩ := key r' r'.2
      have hc0 : (r : SL(4, CFSG.Fischer.F4)) 3 0 = (r' : SL(4, CFSG.Fischer.F4)) 3 0 := by
        rcases k3 with h | h <;> rcases k3' with h' | h'
        · rw [h, h']
        · exact absurd (hrr.mp h) (by rw [h']; exact one_ne_zero)
        · exact absurd (hrr.mpr h') (by rw [h]; exact one_ne_zero)
        · rw [h, h']
      apply Subtype.ext
      rw [eq_lu_of_mem_radR (hK₀R r.2), eq_lu_of_mem_radR (hK₀R r'.2), k1, k1', k4, k4',
        key₂ r r.2, key₂ r' r'.2, hc0]
    rw [hr4] at h16
    omega

theorem comm_mem_radR {x y : SL(4, CFSG.Fischer.F4)} (hx : x ∈ pstd CFSG.Fischer.F4)
    (hy : y ∈ pstd CFSG.Fischer.F4) : x * y * x⁻¹ * y⁻¹ ∈ radR := by
  have h := (piR_eq_one_iff (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : pstd CFSG.Fischer.F4)⁻¹ *
    (⟨y, hy⟩ : pstd CFSG.Fischer.F4)⁻¹)).mp (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (piR ⟨x, hx⟩)]
      group)
  simpa using h

theorem sq_mem_radR {x : SL(4, CFSG.Fischer.F4)} (hx : x ∈ pstd CFSG.Fischer.F4) :
    x * x ∈ radR := by
  obtain ⟨a, b, f, c, d, e, rfl⟩ := exists_lu_of_mem hx
  rw [lu_mul, lu_mem_radR_iff]
  exact ⟨add_self_F4 a, add_self_F4 e⟩

theorem sq_sq_F4 (x : CFSG.Fischer.F4) : (x ^ 2) ^ 2 = x := CFSG.Fischer.F4.sq_sq x

theorem lu_diag_mem_msigma (a : CFSG.Fischer.F4) :
    lu a 0 0 0 0 (a ^ 2) ∈ msigma CFSG.Fischer.F4 := by
  rw [lu_mem_msigma_iff]
  refine ⟨by ring, rfl, sq_sq_F4 a, by ring, by ring, by ring⟩

theorem exists_msigma_of_sigma_mem_radR {x : SL(4, CFSG.Fischer.F4)}
    (hx : x ∈ pstd CFSG.Fischer.F4) (hσ : x * (sigmaSL CFSG.Fischer.F4 x)⁻¹ ∈ radR) :
    ∃ z ∈ msigma CFSG.Fischer.F4 ⊓ pstd CFSG.Fischer.F4, z⁻¹ * x ∈ radR := by
  obtain ⟨a, b, f, c, d, e, rfl⟩ := exists_lu_of_mem hx
  rw [sigmaSL_lu] at hσ
  have hπ := (piR_eq_one_iff (⟨lu a b f c d e, lu_mem_pstd _ _ _ _ _ _⟩ *
    (⟨_, lu_mem_pstd _ _ _ _ _ _⟩ : pstd CFSG.Fischer.F4)⁻¹)).mpr (by simpa using hσ)
  rw [map_mul, map_inv, piR_lu, piR_lu, mul_inv_eq_one] at hπ
  have h2 := congrArg Multiplicative.toAdd hπ
  simp only [toAdd_ofAdd, Prod.mk.injEq] at h2
  obtain ⟨-, he⟩ := h2
  refine ⟨lu a 0 0 0 0 (a ^ 2), ⟨lu_diag_mem_msigma a, lu_mem_pstd _ _ _ _ _ _⟩, ?_⟩
  have hinv := (piR_eq_one_iff ((⟨lu a 0 0 0 0 (a ^ 2), lu_mem_pstd _ _ _ _ _ _⟩ :
    pstd CFSG.Fischer.F4)⁻¹ * ⟨lu a b f c d e, lu_mem_pstd _ _ _ _ _ _⟩)).mp (by
      rw [map_mul, map_inv, piR_lu, piR_lu, inv_mul_eq_one, he])
  simpa using hinv

@[expose] def dgM (p q r s : CFSG.Fischer.F4) : Matrix (Fin 4) (Fin 4) CFSG.Fischer.F4 :=
  Matrix.diagonal ![p, q, r, s]

theorem det_dgM (p q r s : CFSG.Fischer.F4) : (dgM p q r s).det = p * q * r * s := by
  simp [dgM, Matrix.det_diagonal, Fin.prod_univ_four]

theorem omega_facts : CFSG.Fischer.F4.ω * CFSG.Fischer.F4.ω ^ 2 = 1 ∧
    CFSG.Fischer.F4.ω ^ 2 * CFSG.Fischer.F4.ω = 1 ∧
    CFSG.Fischer.F4.ω ^ 2 * CFSG.Fischer.F4.ω ^ 2 = CFSG.Fischer.F4.ω ∧
    CFSG.Fischer.F4.ω * CFSG.Fischer.F4.ω = CFSG.Fischer.F4.ω ^ 2 ∧
    CFSG.Fischer.F4.ω ^ 3 = 1 ∧ CFSG.Fischer.F4.ω ^ 2 ≠ 1 :=
  ⟨f4_ext (by decide), f4_ext (by decide), f4_ext (by decide), f4_ext (by decide),
    f4_ext (by decide), fun h => absurd (congrArg CFSG.Fischer.F4.code h) (by decide)⟩

@[expose] def dω : SL(4, CFSG.Fischer.F4) :=
  ⟨dgM CFSG.Fischer.F4.ω (CFSG.Fischer.F4.ω ^ 2) (CFSG.Fischer.F4.ω ^ 2) CFSG.Fischer.F4.ω, by
    rw [det_dgM]; exact f4_ext (by decide)⟩

@[expose] def dωi : SL(4, CFSG.Fischer.F4) :=
  ⟨dgM (CFSG.Fischer.F4.ω ^ 2) CFSG.Fischer.F4.ω CFSG.Fischer.F4.ω (CFSG.Fischer.F4.ω ^ 2), by
    rw [det_dgM]; exact f4_ext (by decide)⟩

theorem dω_mul_dωi : dω * dωi = 1 := by
  obtain ⟨c1, c2, -, -, -, -⟩ := omega_facts
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  simp only [dω, dωi, dgM, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [c1, c2]

theorem dω_inv : dω⁻¹ = dωi := (eq_inv_of_mul_eq_one_right dω_mul_dωi).symm

theorem dω_conj_lu (a b f c d e : CFSG.Fischer.F4) :
    dω * lu a b f c d e * dω⁻¹ =
      lu (CFSG.Fischer.F4.ω * a) (CFSG.Fischer.F4.ω * b) f c (CFSG.Fischer.F4.ω ^ 2 * d)
        (CFSG.Fischer.F4.ω ^ 2 * e) := by
  obtain ⟨c1, c2, c3, c4, -, -⟩ := omega_facts
  rw [dω_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_lu, coe_lu]
  simp only [dω, dωi, dgM]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination c1 | linear_combination c2
    | linear_combination a * c3 | linear_combination b * c3 | linear_combination f * c2
    | linear_combination c * c1 | linear_combination d * c4

theorem fieldAut_dω : fieldAutSL (frobeniusEquiv CFSG.Fischer.F4 2) 4 dω = dωi := by
  apply Subtype.ext
  rw [coe_fieldAutSL]
  simp only [dω, dωi, dgM]
  ext i j
  rw [Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp [frobeniusEquiv_apply, frobenius_def, sq_sq_F4]

theorem dωi_inv : dωi⁻¹ = dω := by rw [← dω_inv, inv_inv]

theorem invTranspose_dωi : invTransposeSL 4 dωi = dω := by
  apply Subtype.ext
  rw [coe_invTransposeSL, dωi_inv]
  simp only [dω, dgM, Matrix.diagonal_transpose]

theorem conjSL_dω :
    conjSL (antiDiag CFSG.Fischer.F4) (antiDiag CFSG.Fischer.F4)
      (antiDiag_mul_self CFSG.Fischer.F4) dω = dω := by
  apply Subtype.ext
  rw [coe_conjSL]
  ext a b
  rw [antiDiag, permMatrix_mul_mul_permMatrix_apply]
  simp only [dω, dgM]
  fin_cases a <;> fin_cases b <;> simp [Fin.revPerm, Fin.rev]

theorem dω_mem_msigma : dω ∈ msigma CFSG.Fischer.F4 := by
  change sigmaSL CFSG.Fischer.F4 dω = dω
  rw [sigmaSL_apply, fieldAut_dω, invTranspose_dωi, conjSL_dω]

theorem dω_pow_three : dω ^ 3 = 1 := by
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := omega_facts
  rw [pow_three]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  simp only [dω, dgM, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp
  · rw [c4, c1]
  · rw [c3, c2]
  · rw [c3, c2]
  · rw [c4, c1]

theorem dω_conj_mem_pstd {x : SL(4, CFSG.Fischer.F4)} (hx : x ∈ pstd CFSG.Fischer.F4) :
    dω * x * dω⁻¹ ∈ pstd CFSG.Fischer.F4 := by
  obtain ⟨a, b, f, c, d, e, rfl⟩ := exists_lu_of_mem hx
  rw [dω_conj_lu]
  exact lu_mem_pstd _ _ _ _ _ _

theorem dω_mem_normalizer : dω ∈ normalizer ((pstd CFSG.Fischer.F4 : Subgroup _) : Set _) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨dω_conj_mem_pstd, fun h => ?_⟩
  have h1 : dω * (dω * dω) = 1 := by rw [← pow_three]; exact dω_pow_three
  have e : x = dω * (dω * (dω * x * dω⁻¹) * dω⁻¹) * dω⁻¹ := by
    calc x = (dω * (dω * dω)) * x * (dω * (dω * dω))⁻¹ := by rw [h1]; group
      _ = dω * (dω * (dω * x * dω⁻¹) * dω⁻¹) * dω⁻¹ := by group
  rw [e]
  exact dω_conj_mem_pstd (dω_conj_mem_pstd h)

theorem mem_radR_of_dω {x : SL(4, CFSG.Fischer.F4)} (hx : x ∈ pstd CFSG.Fischer.F4)
    (h : dω * x * dω⁻¹ * x⁻¹ ∈ radR) : x ∈ radR := by
  obtain ⟨-, -, -, -, -, hω2⟩ := omega_facts
  obtain ⟨a, b, f, c, d, e, rfl⟩ := exists_lu_of_mem hx
  rw [dω_conj_lu] at h
  have hπ := (piR_eq_one_iff (⟨_, lu_mem_pstd _ _ _ _ _ _⟩ *
    (⟨lu a b f c d e, lu_mem_pstd _ _ _ _ _ _⟩ : pstd CFSG.Fischer.F4)⁻¹)).mpr (by simpa using h)
  rw [map_mul, map_inv, piR_lu, piR_lu, mul_inv_eq_one] at hπ
  have h2 := congrArg Multiplicative.toAdd hπ
  simp only [toAdd_ofAdd, Prod.mk.injEq] at h2
  obtain ⟨ha, he⟩ := h2
  rw [lu_mem_radR_iff]
  constructor
  · have : (CFSG.Fischer.F4.ω - 1) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr omega_ne_one)
  · have : (CFSG.Fischer.F4.ω ^ 2 - 1) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω2)

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
