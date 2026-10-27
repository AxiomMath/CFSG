module

public import CFSG.CharacterTheory.Wreathed.ConditionalExactOrderSum
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeWeighted
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeFamily

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.FlatComplete CFSG.Wreathed.FlatRelative
  CFSG.Wreathed.ConditionalGlobalDegrees CFSG.Wreathed.ConditionalExactOrder

namespace FlatEvery

theorem cubic_term {s f v d val dg : ℂ} (hs : s = 1 ∨ s = -1) (hf : f ≠ 0) (hd : d ≠ 0)
    (hval : val = -s * v) (hdg : dg = f * d) : -s * f * (val ^ 3 / dg) = v ^ 3 / d := by
  subst hval hdg
  rcases hs with rfl | rfl <;> field_simp

theorem no_recip_of_eq {mm f δ ε q : ℤ} (hmm : 16 ∣ mm) (hδ : δ = 1 ∨ δ = -1)
    (hε : ε = 1 ∨ ε = -1) (hq : Odd q)
    (h : mm * f = δ * (q ^ 2 + ε * q + 1) * (ε * q * mm - 2 * (q ^ 2 + 1))) : False := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨c, rfl⟩ := hmm
  have h16 : (16 : ℤ) ∣ 2 * δ * ((2 * k + 1) ^ 2 + ε * (2 * k + 1) + 1) * ((2 * k + 1) ^ 2 + 1) :=
    ⟨δ * ((2 * k + 1) ^ 2 + ε * (2 * k + 1) + 1) * ε * (2 * k + 1) * c - c * f, by
      linear_combination h⟩
  have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mpr h16
  push_cast at hcast
  have key : ∀ d e k' : ZMod 16, (d = 1 ∨ d = -1) → (e = 1 ∨ e = -1) →
      2 * d * ((2 * k' + 1) ^ 2 + e * (2 * k' + 1) + 1) * ((2 * k' + 1) ^ 2 + 1) ≠ 0 := by
    decide
  refine key (δ : ZMod 16) (ε : ZMod 16) (k : ZMod 16) ?_ ?_ hcast
  · rcases hδ with rfl | rfl <;> simp
  · rcases hε with rfl | rfl <;> simp

theorem vec_injective {ι : Type*} {a b c d : ι} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem vec_ne {ι : Type*} {a b c d x : ι} (ha : a ≠ x) (hb : b ≠ x) (hc : c ≠ x) (hd : d ≠ x)
    (l : Fin 4) : ![a, b, c, d] l ≠ x := by
  fin_cases l
  · exact ha
  · exact hb
  · exact hc
  · exact hd

theorem vec_disj {ι : Type*} {P Q : ℕ → Fin 2 → ι} {r t : ℕ} (hPP : ∀ e e', P r e ≠ P t e')
    (hQQ : ∀ e e', Q r e ≠ Q t e') (hPQ : ∀ e e', P r e ≠ Q t e') (hQP : ∀ e e', Q r e ≠ P t e')
    (l l' : Fin 4) : ![P r 0, Q r 0, P r 1, Q r 1] l ≠ ![P t 0, Q t 0, P t 1, Q t 1] l' := by
  fin_cases l <;> fin_cases l' <;> simp [hPP, hQQ, hPQ, hQP]

theorem image_vec {ι : Type*} (a b c d : ι) :
    ({a, b, c, d} : Finset ι) = Finset.univ.image ![a, b, c, d] := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
    true_and, Fin.exists_fin_succ, Fin.exists_fin_zero]
  simp [eq_comm]

theorem blockFamilies_of_distinct {ι : Type*} {m M : ℕ} {V : Finset (ZMod m × ZMod m)}
    {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι} {ψ : ZMod m × ZMod m → ι}
    (inj : Function.Injective ![χ₀, χ₁, χ₂, χ₃, χ₄])
    (ξinj : Set.InjOn ξ ((Finset.Ico 1 m).filter Odd))
    (PQinj : ∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, ∀ e e' : Fin 2,
      (P r e = P r' e' → r = r' ∧ e = e') ∧ (Q r e = Q r' e' → r = r' ∧ e = e') ∧ P r e ≠ Q r' e')
    (ψinj : Set.InjOn ψ V)
    (ξcore : ∀ h ∈ (Finset.Ico 1 m).filter Odd, ξ h ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι))
    (PQcore : ∀ r ∈ Finset.Ico 1 M, ∀ e, P r e ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι) ∧
      Q r e ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι) ∧ P r e ∉ ((Finset.Ico 1 m).filter Odd).image ξ ∧
      Q r e ∉ ((Finset.Ico 1 m).filter Odd).image ξ)
    (ψcore : ∀ I ∈ V, ψ I ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι) ∧
      ψ I ∉ ((Finset.Ico 1 m).filter Odd).image ξ ∧
      ψ I ∉ ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) :
    BlockFamilies χ₁ χ₀ χ₂ χ₃ χ₄ M ((Finset.Ico 1 m).filter Odd) ξ
      (fun r => ![P r 0, Q r 0, P r 1, Q r 1]) P Q ψ V := by
  have key : ∀ a b : Fin 5, a ≠ b → ![χ₀, χ₁, χ₂, χ₃, χ₄] a ≠ ![χ₀, χ₁, χ₂, χ₃, χ₄] b :=
    fun a b hab h => hab (inj h)
  have hP : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, ∀ e e', P r e = P t e' → r = t ∧ e = e' :=
    fun r hr t ht e e' => (PQinj r hr t ht e e').1
  have hQ : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, ∀ e e', Q r e = Q t e' → r = t ∧ e = e' :=
    fun r hr t ht e e' => (PQinj r hr t ht e e').2.1
  have hPQ : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, ∀ e e', P r e ≠ Q t e' :=
    fun r hr t ht e e' => (PQinj r hr t ht e e').2.2
  have hcoreP : ∀ r ∈ Finset.Ico 1 M, ∀ e, (P r e ≠ χ₀ ∧ P r e ≠ χ₁ ∧ P r e ≠ χ₂ ∧ P r e ≠ χ₃ ∧
      P r e ≠ χ₄) ∧ (Q r e ≠ χ₀ ∧ Q r e ≠ χ₁ ∧ Q r e ≠ χ₂ ∧ Q r e ≠ χ₃ ∧ Q r e ≠ χ₄) := by
    intro r hr e
    obtain ⟨h1, h2, -, -⟩ := PQcore r hr e
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
    exact ⟨h1, h2⟩
  refine
    { hAp := key 0 1 (by decide)
      hBp := key 2 1 (by decide)
      hDp := key 3 1 (by decide)
      hωp := key 4 1 (by decide)
      hBA := key 2 0 (by decide)
      hDA := key 3 0 (by decide)
      hωA := key 4 0 (by decide)
      hDB := key 3 2 (by decide)
      hωB := key 4 2 (by decide)
      hωD := key 4 3 (by decide)
      hχcore := fun j hj => ?_
      hχinj := ξinj
      γinj := fun r hr => ?_
      γcore := fun r hr l => ?_
      γodd := fun r hr l j hj => ?_
      disj := fun r hr t ht hrt l l' => ?_
      lab := fun r hr => image_vec _ _ _ _
      gen := fun I hI => ?_
      geninj := ψinj }
  · have h := ξcore j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · exact vec_injective (hPQ r hr r hr 0 0)
      (fun h => absurd (hP r hr r hr 0 1 h).2 (by decide)) (hPQ r hr r hr 0 1)
      (fun h => hPQ r hr r hr 1 0 h.symm) (fun h => absurd (hQ r hr r hr 0 1 h).2 (by decide))
      (hPQ r hr r hr 1 1)
  · obtain ⟨⟨p0, p1, p2, p3, p4⟩, ⟨q0, q1, q2, q3, q4⟩⟩ := hcoreP r hr 0
    obtain ⟨⟨p0', p1', p2', p3', p4'⟩, ⟨q0', q1', q2', q3', q4'⟩⟩ := hcoreP r hr 1
    exact ⟨vec_ne p1 q1 p1' q1' l, vec_ne p0 q0 p0' q0' l, vec_ne p2 q2 p2' q2' l,
      vec_ne p3 q3 p3' q3' l, vec_ne p4 q4 p4' q4' l⟩
  · have hξ : ∀ e, P r e ≠ ξ j ∧ Q r e ≠ ξ j := fun e =>
      ⟨fun he => (PQcore r hr e).2.2.1 (Finset.mem_image.mpr ⟨j, hj, he.symm⟩),
        fun he => (PQcore r hr e).2.2.2 (Finset.mem_image.mpr ⟨j, hj, he.symm⟩)⟩
    exact vec_ne (hξ 0).1 (hξ 0).2 (hξ 1).1 (hξ 1).2 l
  · exact vec_disj (fun e e' h => hrt (hP r hr t ht e e' h).1)
      (fun e e' h => hrt (hQ r hr t ht e e' h).1) (fun e e' => hPQ r hr t ht e e')
      (fun e e' h => hPQ t ht r hr e' e h.symm) l l'
  · obtain ⟨hc, hξ, hPQm⟩ := ψcore I hI
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    have hPQ' : ∀ r ∈ Finset.Ico 1 M, ∀ e, ψ I ≠ P r e ∧ ψ I ≠ Q r e := fun r hr e =>
      ⟨fun he => hPQm (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨(r, e), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, he.symm⟩))),
        fun he => hPQm (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨(r, e), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, he.symm⟩)))⟩
    refine ⟨hc.2.1, hc.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2,
      fun j hj he => hξ (Finset.mem_image.mpr ⟨j, hj, he.symm⟩), fun r hr l => ?_⟩
    exact fun h => vec_ne (hPQ' r hr 0).1.symm (hPQ' r hr 0).2.symm (hPQ' r hr 1).1.symm
      (hPQ' r hr 1).2.symm l h.symm

end FlatEvery

namespace FlatRelative.Support

variable {ι : Type*} {BB : Finset ι} {m M : ℕ} {V : Finset (ZMod m × ZMod m)}
  {X : ZMod m → ι → ℂ} {c : ZMod m → ZMod m → ι → ℂ} {δ₀ δ₁ δ₂ δ₃ δ₄ α γ : ℤ}
  {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι} {ψ : ZMod m × ZMod m → ι}
  {er : ℕ → Fin 2}
  (hS : Support BB m M V X c δ₀ δ₁ δ₂ δ₃ δ₄ α γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ er)
include hS

theorem blockFamilies : BlockFamilies χ₁ χ₀ χ₂ χ₃ χ₄ M ((Finset.Ico 1 m).filter Odd) ξ
    (fun r => ![P r 0, Q r 0, P r 1, Q r 1]) P Q ψ V :=
  FlatEvery.blockFamilies_of_distinct hS.inj hS.ξinj hS.PQinj hS.ψinj hS.ξcore hS.PQcore
    hS.ψcore

theorem sum_families
    (hBB : BB = {χ₀, χ₁, χ₂, χ₃, χ₄} ∪ ((Finset.Ico 1 m).filter Odd).image ξ ∪
      (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) ∪
      V.image ψ) (F : ι → ℂ) :
    ∑ φ ∈ BB, F φ = F χ₁ + F χ₀ + F χ₂ + F χ₃ + F χ₄ +
      ∑ j ∈ (Finset.Ico 1 m).filter Odd, F (ξ j) +
      ∑ re ∈ Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)), F (P re.1 re.2) +
      ∑ re ∈ Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)), F (Q re.1 re.2) +
      ∑ I ∈ V, F (ψ I) := by
  refine hS.blockFamilies.sum_union ?_ F
  rw [hBB, Finset.insert_comm χ₀ χ₁, ← Finset.union_assoc]

theorem cubic_sum_cubic
    (hBB : BB = {χ₀, χ₁, χ₂, χ₃, χ₄} ∪ ((Finset.Ico 1 m).filter Odd).image ξ ∪
      (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) ∪
      V.image ψ)
    {q : ℕ} (hq3 : 3 ≤ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (s₁ : δ₁ = 1 ∨ δ₁ = -1) {K : ℕ}
    (hK : 1 ≤ K) (hMK : M = 2 * K) (hJ : ((Finset.Ico 1 m).filter Odd).card = M)
    (hE : ((V.filter fun I => Even I.1.val ∧ Even I.2.val).card : ℂ) =
      (2 * K - 1) * (2 * K - 2) / 6)
    (hO : ((V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card : ℂ) =
      4 * K * (4 * K - 2) / 8)
    (deg : ι → ℤ) {D Δ : ℤ} (hf₁ : 0 < deg χ₁)
    (hdξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = D)
    (hdPQ : ∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = deg χ₂ ∧ deg (Q r er) = deg χ₃)
    (hdψ : ∀ I ∈ V, deg (ψ I) = Δ)
    (d₀ : deg χ₀ = (q : ℤ) ^ 3 * deg χ₁) (d₂ : deg χ₂ = ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁)
    (d₃ : deg χ₃ = q * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁)
    (d₄ : deg χ₄ = q * (q + ε) * deg χ₁) (e₀ : δ₀ = -(ε * δ₁)) (e₂ : δ₂ = δ₁)
    (e₃ : δ₃ = -(ε * δ₁)) (e₄ : δ₄ = -δ₁) (eα : α = ε * δ₁) (eγ : γ = ε * δ₁)
    (dD : D = ((q : ℤ) ^ 3 - ε) * deg χ₁)
    (dΔ : Δ = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁)
    (val : ι → ℂ) (v₀ : val χ₀ = δ₀ * ε * q) (v₁ : val χ₁ = -δ₁)
    (v₂ : val χ₂ = -(δ₂ * (2 + ε * q))) (v₃ : val χ₃ = δ₃ * (1 + 2 * ε * q))
    (v₄ : val χ₄ = δ₄ * (1 + ε * q))
    (vξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, val (ξ h) = -(α * (1 - ε * q)))
    (vPQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, val (P r e) = -(δ₂ * (1 + (-1) ^ r * (1 + ε * q))) ∧
      val (Q r e) = δ₃ * (-1 + (1 + (-1) ^ r) * (1 + ε * q)))
    (vψ : ∀ I ∈ V, val (ψ I) =
      -((1 + ε * q) * γ * (if Even I.1.val ∧ Even I.2.val then 3 else -1))) :
    ∑ φ ∈ BB, val φ ^ 3 / (deg φ : ℂ) = -δ₁ / deg χ₁ *
      (((4 * K : ℕ) : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2 / ((q : ℂ) ^ 2 + ε * q + 1)) := by
  have hs₁ : (δ₁ : ℂ) = 1 ∨ (δ₁ : ℂ) = -1 := cast_sign s₁
  have hεC : (ε : ℂ) = 1 ∨ (ε : ℂ) = -1 := cast_sign hε
  have hε2 : (ε : ℂ) ^ 2 = 1 := cast_sign_sq hε
  have hfb : (deg χ₁ : ℂ) ≠ 0 := by exact_mod_cast hf₁.ne'
  have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hQ : (q : ℂ) ^ 2 + ε * q + 1 ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) ^ 2 + ε * q + 1 := by rcases hε with h | h <;> rw [h] <;> nlinarith
    exact_mod_cast this.ne'
  have hqε : (q : ℂ) + ε ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) + ε := by rcases hε with h | h <;> rw [h] <;> omega
    exact_mod_cast this.ne'
  have hC : (q : ℂ) ^ 3 - ε ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) ^ 3 - ε := by rcases hε with h | h <;> rw [h] <;> nlinarith
    exact_mod_cast this.ne'
  have hq3C : (q : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 hq0
  have hqQ : (q : ℂ) * ((q : ℂ) ^ 2 + ε * q + 1) ≠ 0 := mul_ne_zero hq0 hQ
  have hqqε : (q : ℂ) * ((q : ℂ) + ε) ≠ 0 := mul_ne_zero hq0 hqε
  have hqεQ : ((q : ℂ) + ε) * ((q : ℂ) ^ 2 + ε * q + 1) ≠ 0 := mul_ne_zero hqε hQ
  have hδ : (δ₀ : ℂ) = -(ε * δ₁) ∧ (δ₂ : ℂ) = δ₁ ∧ (δ₃ : ℂ) = -(ε * δ₁) ∧ (δ₄ : ℂ) = -δ₁ ∧
      (α : ℂ) = ε * δ₁ ∧ (γ : ℂ) = ε * δ₁ := by
    subst e₀ e₂ e₃ e₄ eα eγ
    push_cast
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨c₀, c₂, c₃, c₄, cα, cγ⟩ := hδ
  have hv₀' : val χ₀ = -(δ₁ : ℂ) * q := by
    rw [v₀, c₀]
    linear_combination (-(δ₁ : ℂ) * q) * hε2
  have hv₃' : val χ₃ = -(δ₁ : ℂ) * (2 * q + ε) := by
    rw [v₃, c₃]
    linear_combination (-2 * (δ₁ : ℂ) * q) * hε2
  have hvξ' : ∀ j ∈ (Finset.Ico 1 m).filter Odd, val (ξ j) = -(δ₁ : ℂ) * (ε - q) := by
    intro j hj
    rw [vξ j hj, cα]
    linear_combination ((δ₁ : ℂ) * q) * hε2
  have key := hS.blockFamilies.cubic_sum (B := BB) (by rw [hBB, Finset.insert_comm χ₀ χ₁,
      ← Finset.union_assoc]) (fun φ => -(δ₁ : ℂ) * deg χ₁ * (val φ ^ 3 / (deg φ : ℂ)))
    hq0 hQ hqε hC rfl rfl hεC hK hMK hJ hE hO
    ((FlatEvery.cubic_term (v := 1) (d := 1) hs₁ hfb one_ne_zero (by rw [v₁]; ring)
      (by ring)).trans (by norm_num))
    (FlatEvery.cubic_term hs₁ hfb hq3C hv₀' (by rw [d₀]; push_cast; ring))
    (FlatEvery.cubic_term hs₁ hfb hQ (by rw [v₂, c₂]; ring) (by rw [d₂]; push_cast; ring))
    (FlatEvery.cubic_term hs₁ hfb hqQ hv₃' (by rw [d₃]; push_cast; ring))
    (FlatEvery.cubic_term hs₁ hfb hqqε (by rw [v₄, c₄]) (by rw [d₄]; push_cast; ring))
    (fun j hj => FlatEvery.cubic_term hs₁ hfb hC (hvξ' j hj)
      (by rw [hdξ j hj, dD]; push_cast; ring))
    (fun r hr e => by
      have hdP : (deg (P r e) : ℂ) = deg χ₁ * ((q : ℂ) ^ 2 + ε * q + 1) := by
        rw [(hdPQ r hr e).1, d₂]
        push_cast
        ring
      rcases Nat.even_or_odd r with hev | hod
      · rw [ite_eq_right (Nat.not_odd_iff_even.mpr hev)]
        refine FlatEvery.cubic_term hs₁ hfb hQ ?_ hdP
        rw [(vPQ r hr e).1, c₂, hev.neg_one_pow]
        ring
      · rw [ite_eq_left hod]
        refine FlatEvery.cubic_term hs₁ hfb hQ ?_ hdP
        rw [(vPQ r hr e).1, c₂, hod.neg_one_pow]
        ring)
    (fun r hr e => by
      have hdQ : (deg (Q r e) : ℂ) = deg χ₁ * ((q : ℂ) * ((q : ℂ) ^ 2 + ε * q + 1)) := by
        rw [(hdPQ r hr e).2, d₃]
        push_cast
        ring
      rcases Nat.even_or_odd r with hev | hod
      · rw [ite_eq_right (Nat.not_odd_iff_even.mpr hev)]
        refine FlatEvery.cubic_term hs₁ hfb hqQ ?_ hdQ
        rw [(vPQ r hr e).2, c₃, hev.neg_one_pow]
        linear_combination (-2 * (δ₁ : ℂ) * q) * hε2
      · rw [ite_eq_left hod]
        refine FlatEvery.cubic_term hs₁ hfb hqQ ?_ hdQ
        rw [(vPQ r hr e).2, c₃, hod.neg_one_pow]
        ring)
    (fun I hI => by
      have hdψ' : (deg (ψ I) : ℂ) = deg χ₁ * (((q : ℂ) + ε) * ((q : ℂ) ^ 2 + ε * q + 1)) := by
        rw [hdψ I hI, dΔ]
        push_cast
        ring
      by_cases hev : Even I.1.val ∧ Even I.2.val
      · rw [ite_eq_left hev]
        refine FlatEvery.cubic_term hs₁ hfb hqεQ ?_ hdψ'
        rw [vψ I hI, ite_eq_left hev, cγ]
        linear_combination (-3 * (δ₁ : ℂ) * q) * hε2
      · rw [ite_eq_right hev]
        refine FlatEvery.cubic_term hs₁ hfb hqεQ ?_ hdψ'
        rw [vψ I hI, ite_eq_right hev, cγ]
        linear_combination ((δ₁ : ℂ) * q) * hε2)
  rw [← key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  field_simp
  rcases hs₁ with h | h <;> rw [h] <;> ring

theorem cubic_sum_recip
    (hBB : BB = {χ₀, χ₁, χ₂, χ₃, χ₄} ∪ ((Finset.Ico 1 m).filter Odd).image ξ ∪
      (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) ∪
      V.image ψ)
    {q : ℕ} (hq3 : 3 ≤ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (s₁ : δ₁ = 1 ∨ δ₁ = -1) {K : ℕ}
    (hK : 1 ≤ K) (hMK : M = 2 * K) (hJ : ((Finset.Ico 1 m).filter Odd).card = M)
    (hE : ((V.filter fun I => Even I.1.val ∧ Even I.2.val).card : ℂ) =
      (2 * K - 1) * (2 * K - 2) / 6)
    (hO : ((V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card : ℂ) =
      4 * K * (4 * K - 2) / 8)
    (deg : ι → ℤ) {D Δ : ℤ} (hf₁ : 0 < deg χ₁)
    (hdξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = D)
    (hdPQ : ∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = deg χ₂ ∧ deg (Q r er) = deg χ₃)
    (hdψ : ∀ I ∈ V, deg (ψ I) = Δ)
    (d₀ : (q : ℤ) * deg χ₀ = deg χ₁) (d₂ : (q : ℤ) * deg χ₂ = deg χ₁) (d₃ : deg χ₃ = deg χ₁)
    (d₄ : (q : ℤ) * deg χ₄ = (q + ε) * deg χ₁) (e₀ : δ₀ = -(ε * δ₁)) (e₂ : δ₂ = -(ε * δ₁))
    (e₃ : δ₃ = δ₁) (e₄ : δ₄ = δ₁) (eα : α = -δ₁) (eγ : γ = -δ₁)
    (dD : (q : ℤ) * D = (q - ε) * deg χ₁) (dΔ : (q : ℤ) * Δ = (q + ε) * deg χ₁)
    (val : ι → ℂ) (v₀ : val χ₀ = δ₀ * ε * q) (v₁ : val χ₁ = -δ₁)
    (v₂ : val χ₂ = -(δ₂ * (2 + ε * q))) (v₃ : val χ₃ = δ₃ * (1 + 2 * ε * q))
    (v₄ : val χ₄ = δ₄ * (1 + ε * q))
    (vξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, val (ξ h) = -(α * (1 - ε * q)))
    (vPQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, val (P r e) = -(δ₂ * (1 + (-1) ^ r * (1 + ε * q))) ∧
      val (Q r e) = δ₃ * (-1 + (1 + (-1) ^ r) * (1 + ε * q)))
    (vψ : ∀ I ∈ V, val (ψ I) =
      -((1 + ε * q) * γ * (if Even I.1.val ∧ Even I.2.val then 3 else -1))) :
    ∑ φ ∈ BB, val φ ^ 3 / (deg φ : ℂ) = δ₁ / deg χ₁ *
      (((q : ℂ) + ε) ^ 2 * (ε * q * ((4 * K : ℕ) : ℂ) ^ 2 - 2 * ((q : ℂ) ^ 2 + 1))) := by
  have hs₁ : (δ₁ : ℂ) = 1 ∨ (δ₁ : ℂ) = -1 := cast_sign s₁
  have hεC : (ε : ℂ) = 1 ∨ (ε : ℂ) = -1 := cast_sign hε
  have hfb : (deg χ₁ : ℂ) ≠ 0 := by exact_mod_cast hf₁.ne'
  have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqε : (q : ℂ) + ε ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) + ε := by rcases hε with h | h <;> rw [h] <;> omega
    exact_mod_cast this.ne'
  have hqε' : (q : ℂ) - ε ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) - ε := by rcases hε with h | h <;> rw [h] <;> omega
    exact_mod_cast this.ne'
  have g₀ : (deg χ₀ : ℂ) = deg χ₁ / q := by
    rw [eq_div_iff hq0, mul_comm]
    exact_mod_cast d₀
  have g₂ : (deg χ₂ : ℂ) = deg χ₁ / q := by
    rw [eq_div_iff hq0, mul_comm]
    exact_mod_cast d₂
  have g₃ : (deg χ₃ : ℂ) = deg χ₁ := by exact_mod_cast d₃
  have g₄ : (deg χ₄ : ℂ) = ((q : ℂ) + ε) * deg χ₁ / q := by
    rw [eq_div_iff hq0, mul_comm]
    exact_mod_cast d₄
  have gD : (D : ℂ) = ((q : ℂ) - ε) * deg χ₁ / q := by
    rw [eq_div_iff hq0, mul_comm]
    exact_mod_cast dD
  have gΔ : (Δ : ℂ) = ((q : ℂ) + ε) * deg χ₁ / q := by
    rw [eq_div_iff hq0, mul_comm]
    exact_mod_cast dΔ
  rw [hS.sum_families hBB]
  have hξs : ∑ j ∈ (Finset.Ico 1 m).filter Odd, val (ξ j) ^ 3 / (deg (ξ j) : ℂ) =
      2 * K * ((-(α * (1 - ε * q))) ^ 3 / (D : ℂ)) := by
    rw [Finset.sum_congr rfl fun j hj => by rw [vξ j hj, hdξ j hj], Finset.sum_const, hJ, hMK,
      nsmul_eq_mul]
    push_cast
    ring
  subst hMK
  have hPs : ∑ re ∈ Finset.Ico 1 (2 * K) ×ˢ (Finset.univ : Finset (Fin 2)),
      val (P re.1 re.2) ^ 3 / (deg (P re.1 re.2) : ℂ) =
      2 * (K * ((-(δ₂ * (1 + (-1) * (1 + ε * q)))) ^ 3 / (deg χ₂ : ℂ)) +
        ((K : ℂ) - 1) * ((-(δ₂ * (1 + 1 * (1 + ε * q)))) ^ 3 / (deg χ₂ : ℂ))) := by
    rw [Finset.sum_congr rfl fun re hre => (by
      rw [(vPQ re.1 (Finset.mem_product.mp hre).1 re.2).1,
        (hdPQ re.1 (Finset.mem_product.mp hre).1 re.2).1]
      rcases Nat.even_or_odd re.1 with hev | hod
      · rw [hev.neg_one_pow, ite_eq_right (Nat.not_odd_iff_even.mpr hev)]
      · rw [hod.neg_one_pow, ite_eq_left hod] :
      val (P re.1 re.2) ^ 3 / (deg (P re.1 re.2) : ℂ) = if Odd re.1 then
        (-(δ₂ * (1 + (-1) * (1 + ε * q)))) ^ 3 / (deg χ₂ : ℂ) else
        (-(δ₂ * (1 + 1 * (1 + ε * q)))) ^ 3 / (deg χ₂ : ℂ))]
    exact ConditionalExactOrder.sum_labels_parity hK _ _ _ fun r e => rfl
  have hQs : ∑ re ∈ Finset.Ico 1 (2 * K) ×ˢ (Finset.univ : Finset (Fin 2)),
      val (Q re.1 re.2) ^ 3 / (deg (Q re.1 re.2) : ℂ) =
      2 * (K * ((δ₃ * (-1 + (1 + (-1)) * (1 + ε * q))) ^ 3 / (deg χ₃ : ℂ)) +
        ((K : ℂ) - 1) * ((δ₃ * (-1 + (1 + 1) * (1 + ε * q))) ^ 3 / (deg χ₃ : ℂ))) := by
    rw [Finset.sum_congr rfl fun re hre => (by
      rw [(vPQ re.1 (Finset.mem_product.mp hre).1 re.2).2,
        (hdPQ re.1 (Finset.mem_product.mp hre).1 re.2).2]
      rcases Nat.even_or_odd re.1 with hev | hod
      · rw [hev.neg_one_pow, ite_eq_right (Nat.not_odd_iff_even.mpr hev)]
      · rw [hod.neg_one_pow, ite_eq_left hod] :
      val (Q re.1 re.2) ^ 3 / (deg (Q re.1 re.2) : ℂ) = if Odd re.1 then
        (δ₃ * (-1 + (1 + (-1)) * (1 + ε * q))) ^ 3 / (deg χ₃ : ℂ) else
        (δ₃ * (-1 + (1 + 1) * (1 + ε * q))) ^ 3 / (deg χ₃ : ℂ))]
    exact ConditionalExactOrder.sum_labels_parity hK _ _ _ fun r e => rfl
  have hψs : ∑ I ∈ V, val (ψ I) ^ 3 / (deg (ψ I) : ℂ) =
      (2 * K - 1) * (2 * K - 2) / 6 * ((-((1 + ε * q) * γ * 3)) ^ 3 / (Δ : ℂ)) +
        4 * K * (4 * K - 2) / 8 * ((-((1 + ε * q) * γ * (-1))) ^ 3 / (Δ : ℂ)) := by
    rw [Finset.sum_congr rfl fun I hI => (by
      rw [vψ I hI, hdψ I hI]
      by_cases hev : Even I.1.val ∧ Even I.2.val
      · rw [ite_eq_left hev, ite_eq_left hev]
      · rw [ite_eq_right hev, ite_eq_right hev] :
      val (ψ I) ^ 3 / (deg (ψ I) : ℂ) = if Even I.1.val ∧ Even I.2.val then
        (-((1 + ε * q) * γ * 3)) ^ 3 / (Δ : ℂ) else
        (-((1 + ε * q) * γ * (-1))) ^ 3 / (Δ : ℂ)),
      Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hE, hO]
  rw [hξs, hPs, hQs, hψs, v₀, v₁, v₂, v₃, v₄, g₀, g₂, g₃, g₄, gD, gΔ]
  subst e₀ e₂ e₃ e₄ eα eγ
  push_cast
  field_simp
  rcases hs₁ with h | h <;> rcases hεC with h' | h' <;> rw [h, h'] <;> ring

theorem cubic_of_moment
    (hBB : BB = {χ₀, χ₁, χ₂, χ₃, χ₄} ∪ ((Finset.Ico 1 m).filter Odd).image ξ ∪
      (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) ∪
      V.image ψ)
    {q : ℕ} (hq3 : 3 ≤ q) (hqodd : Odd q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (s₁ : δ₁ = 1 ∨ δ₁ = -1) {K : ℕ} (hK : 1 ≤ K) (hMK : M = 2 * K)
    (hJ : ((Finset.Ico 1 m).filter Odd).card = M)
    (hE : ((V.filter fun I => Even I.1.val ∧ Even I.2.val).card : ℂ) =
      (2 * K - 1) * (2 * K - 2) / 6)
    (hO : ((V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card : ℂ) =
      4 * K * (4 * K - 2) / 8)
    (deg : ι → ℤ) {D Δ : ℤ} (hf₁ : 0 < deg χ₁)
    (hdξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = D)
    (hdPQ : ∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = deg χ₂ ∧ deg (Q r er) = deg χ₃)
    (hdψ : ∀ I ∈ V, deg (ψ I) = Δ)
    (val : ι → ℂ) (v₀ : val χ₀ = δ₀ * ε * q) (v₁ : val χ₁ = -δ₁)
    (v₂ : val χ₂ = -(δ₂ * (2 + ε * q))) (v₃ : val χ₃ = δ₃ * (1 + 2 * ε * q))
    (v₄ : val χ₄ = δ₄ * (1 + ε * q))
    (vξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, val (ξ h) = -(α * (1 - ε * q)))
    (vPQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, val (P r e) = -(δ₂ * (1 + (-1) ^ r * (1 + ε * q))) ∧
      val (Q r e) = δ₃ * (-1 + (1 + (-1) ^ r) * (1 + ε * q)))
    (vψ : ∀ I ∈ V, val (ψ I) =
      -((1 + ε * q) * γ * (if Even I.1.val ∧ Even I.2.val then 3 else -1)))
    (hX : Xor
      ((deg χ₀ = (q : ℤ) ^ 3 * deg χ₁ ∧ deg χ₂ = ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg χ₃ = q * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg χ₄ = q * (q + ε) * deg χ₁) ∧
        (δ₀ = -(ε * δ₁) ∧ δ₂ = δ₁ ∧ δ₃ = -(ε * δ₁) ∧ δ₄ = -δ₁ ∧ α = ε * δ₁ ∧ γ = ε * δ₁) ∧
        D = ((q : ℤ) ^ 3 - ε) * deg χ₁ ∧
        (∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = ((q : ℤ) ^ 3 - ε) * deg χ₁) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg (Q r er) = q * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁) ∧
        Δ = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
        ∀ I ∈ V, deg (ψ I) = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁)
      ((q : ℤ) ∣ deg χ₁ ∧
        (q * deg χ₀ = deg χ₁ ∧ q * deg χ₂ = deg χ₁ ∧ deg χ₃ = deg χ₁ ∧
          q * deg χ₄ = (q + ε) * deg χ₁) ∧
        (δ₀ = -(ε * δ₁) ∧ δ₂ = -(ε * δ₁) ∧ δ₃ = δ₁ ∧ δ₄ = δ₁ ∧ α = -δ₁ ∧ γ = -δ₁) ∧
        q * D = (q - ε) * deg χ₁ ∧
        (∀ h ∈ (Finset.Ico 1 m).filter Odd, q * deg (ξ h) = (q - ε) * deg χ₁) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ er, q * deg (P r er) = deg χ₁ ∧ deg (Q r er) = deg χ₁) ∧
        q * Δ = (q + ε) * deg χ₁ ∧ ∀ I ∈ V, q * deg (ψ I) = (q + ε) * deg χ₁))
    (hSB : ∑ φ ∈ BB, val φ ^ 3 / (deg φ : ℂ) =
      ((4 * K : ℕ) : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2 / ((q : ℂ) ^ 2 + ε * q + 1)) :
    ((deg χ₀ = (q : ℤ) ^ 3 * deg χ₁ ∧ deg χ₂ = ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg χ₃ = q * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg χ₄ = q * (q + ε) * deg χ₁) ∧
        (δ₀ = -(ε * δ₁) ∧ δ₂ = δ₁ ∧ δ₃ = -(ε * δ₁) ∧ δ₄ = -δ₁ ∧ α = ε * δ₁ ∧ γ = ε * δ₁) ∧
        D = ((q : ℤ) ^ 3 - ε) * deg χ₁ ∧
        (∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = ((q : ℤ) ^ 3 - ε) * deg χ₁) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg (Q r er) = q * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁) ∧
        Δ = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
        ∀ I ∈ V, deg (ψ I) = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁) ∧
      deg χ₁ = 1 ∧ δ₁ = -1 := by
  have hfb : (deg χ₁ : ℂ) ≠ 0 := by exact_mod_cast hf₁.ne'
  have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hQ : (q : ℂ) ^ 2 + ε * q + 1 ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) ^ 2 + ε * q + 1 := by rcases hε with h | h <;> rw [h] <;> nlinarith
    exact_mod_cast this.ne'
  have hqε : (q : ℂ) + ε ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) + ε := by rcases hε with h | h <;> rw [h] <;> omega
    exact_mod_cast this.ne'
  have h4K : ((4 * K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 4 * K ≠ 0 by omega)
  have hS0 : ((4 * K : ℕ) : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2 / ((q : ℂ) ^ 2 + ε * q + 1) ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero 2 h4K) (pow_ne_zero 2 hqε)) hQ
  rcases hX with ⟨hC, -⟩ | ⟨hR, -⟩
  · obtain ⟨⟨d₀, d₂, d₃, d₄⟩, ⟨e₀, e₂, e₃, e₄, eα, eγ⟩, dD, -, -, dΔ, -⟩ := id hC
    have h := hS.cubic_sum_cubic hBB hq3 hε s₁ hK hMK hJ hE hO deg hf₁ hdξ hdPQ hdψ d₀ d₂ d₃ d₄
      e₀ e₂ e₃ e₄ eα eγ dD dΔ val v₀ v₁ v₂ v₃ v₄ vξ vPQ vψ
    rw [hSB] at h
    have h2 : (-(δ₁ : ℂ) / deg χ₁ - 1) *
        (((4 * K : ℕ) : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2 / ((q : ℂ) ^ 2 + ε * q + 1)) = 0 := by
      linear_combination -h
    have h3 := (mul_eq_zero.mp h2).resolve_right hS0
    have h4 : ((deg χ₁ : ℤ) : ℂ) = ((-δ₁ : ℤ) : ℂ) := by
      push_cast
      field_simp at h3
      linear_combination -h3
    have h5 : deg χ₁ = -δ₁ := by exact_mod_cast h4
    have h6 : δ₁ = -1 := by omega
    exact ⟨hC, by rw [h5, h6]; rfl, h6⟩
  · exfalso
    obtain ⟨-, ⟨d₀, d₂, d₃, d₄⟩, ⟨e₀, e₂, e₃, e₄, eα, eγ⟩, dD, -, -, dΔ, -⟩ := hR
    have h := hS.cubic_sum_recip hBB hq3 hε s₁ hK hMK hJ hE hO deg hf₁ hdξ hdPQ hdψ d₀ d₂ d₃ d₄
      e₀ e₂ e₃ e₄ eα eγ dD dΔ val v₀ v₁ v₂ v₃ v₄ vξ vPQ vψ
    rw [hSB] at h
    have h2 : ((q : ℂ) + ε) ^ 2 * (((4 * K : ℕ) : ℂ) ^ 2 * deg χ₁ -
        δ₁ * ((q : ℂ) ^ 2 + ε * q + 1) * (ε * q * ((4 * K : ℕ) : ℂ) ^ 2 -
          2 * ((q : ℂ) ^ 2 + 1))) = 0 := by
      rw [div_eq_iff hQ] at h
      have h' : ((4 * K : ℕ) : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2 * deg χ₁ = δ₁ *
          (((q : ℂ) + ε) ^ 2 * (ε * q * ((4 * K : ℕ) : ℂ) ^ 2 - 2 * ((q : ℂ) ^ 2 + 1))) *
            ((q : ℂ) ^ 2 + ε * q + 1) := by
        rw [h]
        field_simp
      linear_combination h'
    have h3 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hqε)
    have h4 : ((((4 * K : ℕ) : ℤ) ^ 2 * deg χ₁ : ℤ) : ℂ) = ((δ₁ * ((q : ℤ) ^ 2 + ε * q + 1) *
        (ε * q * ((4 * K : ℕ) : ℤ) ^ 2 - 2 * ((q : ℤ) ^ 2 + 1)) : ℤ) : ℂ) := by
      push_cast at h3 ⊢
      linear_combination h3
    have h5 : ((4 * K : ℕ) : ℤ) ^ 2 * deg χ₁ = δ₁ * ((q : ℤ) ^ 2 + ε * q + 1) *
        (ε * q * ((4 * K : ℕ) : ℤ) ^ 2 - 2 * ((q : ℤ) ^ 2 + 1)) := by exact_mod_cast h4
    have h16 : (16 : ℤ) ∣ ((4 * K : ℕ) : ℤ) ^ 2 := ⟨(K : ℤ) ^ 2, by push_cast; ring⟩
    have hqodd' : Odd (q : ℤ) := by
      obtain ⟨k, hk⟩ := hqodd
      exact ⟨k, by rw [hk]; push_cast; ring⟩
    exact FlatEvery.no_recip_of_eq h16 s₁ hε hqodd' h5

end FlatRelative.Support

end CFSG.Wreathed
