module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SRed
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SOdd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SShape
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SWeights

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open scoped MatrixGroups
open Subgroup CFSG CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem card_le_of_shape_centralizer {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (e : K) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (S : Shape ↥(centralizer ({e} : Set K)) F₁ F₂) (h₁ : Odd (Nat.card F₁)) (h₂ : Odd (Nat.card F₂))
    (hp₁ : ringChar F₁ ≠ p) (hp₂ : ringChar F₂ ≠ p) (A : Subgroup K)
    (hA : A ≤ centralizer ({e} : Set K)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) : Nat.card ↥A ≤ p ^ 2 := by
  classical
  let A' : Subgroup ↥(centralizer ({e} : Set K)) := A.subgroupOf (centralizer ({e} : Set K))
  have hcard : Nat.card ↥A' = Nat.card ↥A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  rw [← hcard]
  refine shape_elemAb_card_le S h₁ h₂ hp2 hp₁ hp₂ A' ?_ ?_
  · intro a ha b hb
    apply Subtype.ext
    exact hcomm a.1 ha b.1 hb
  · intro a ha
    apply Subtype.ext
    exact hexp a.1 ha

theorem card_le_four_of_inverted {K : Type} [Group K] [Finite K] {u : K} (hu : u * u = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (hShape : ∀ e : K, e * e = 1 → e ≠ 1 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂)
      (_ : Finite F₁) (_ : Finite F₂) (_ : Shape ↥(centralizer ({e} : Set K)) F₁ F₂),
        Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ ringChar F₁ ≠ p ∧ ringChar F₂ ≠ p)
    {e : K} (he : e * e = 1) (he1 : e ≠ 1) (heu : e ≠ u) (hec : e * u = u * e)
    (W : Subgroup K) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWp : ∀ w ∈ W, w ^ p = 1)
    (hWe : ∀ w ∈ W, e * w * e⁻¹ ∈ W) (hWu : ∀ w ∈ W, u * w * u⁻¹ = w⁻¹) :
    Nat.card ↥W ≤ p ^ 4 := by
  classical
  have hpp : p.Prime := Fact.out
  have hue : (u * e) * (u * e) = 1 := by
    calc (u * e) * (u * e) = u * (e * u) * e := by group
      _ = u * (u * e) * e := by rw [hec]
      _ = (u * u) * (e * e) := by group
      _ = 1 := by rw [hu, he]; group
  have hue1 : u * e ≠ 1 := by
    intro h
    apply heu
    have : e = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (inv_eq_of_mul_eq_one_left hu).symm ▸ rfl
  obtain ⟨F₁, F₂, _, _, _, _, S₁, h₁o, h₂o, hc₁, hc₂⟩ := hShape e he he1
  obtain ⟨G₁, G₂, _, _, _, _, S₂, g₁o, g₂o, gc₁, gc₂⟩ := hShape (u * e) hue hue1
  let A₁ : Subgroup K := W ⊓ centralizer ({e} : Set K)
  let A₂ : Subgroup K := W ⊓ centralizer ({u * e} : Set K)
  have hA₁ : Nat.card ↥A₁ ≤ p ^ 2 :=
    card_le_of_shape_centralizer hp2 e S₁ h₁o h₂o hc₁ hc₂ A₁ inf_le_right
      (fun a ha b hb => hWc a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1)
      (fun a ha => hWp a (Subgroup.mem_inf.mp ha).1)
  have hA₂ : Nat.card ↥A₂ ≤ p ^ 2 :=
    card_le_of_shape_centralizer hp2 (u * e) S₂ g₁o g₂o gc₁ gc₂ A₂ inf_le_right
      (fun a ha b hb => hWc a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1)
      (fun a ha => hWp a (Subgroup.mem_inf.mp ha).1)
  have hsurj : Function.Surjective (fun x : ↥A₁ × ↥A₂ =>
      (⟨(x.1 : K) * (x.2 : K), W.mul_mem (Subgroup.mem_inf.mp x.1.2).1 (Subgroup.mem_inf.mp x.2.2).1⟩ : ↥W)) := by
    intro w
    obtain ⟨a, ha, b, hb, hae, hbe, hw⟩ := odd_abelian_split hp2 W hWc hWp e he hWe w.1 w.2
    have haA : a ∈ A₁ := by
      refine Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc a * e = (e * a * e⁻¹) * e := by rw [hae]
        _ = e * a := by group
    have hbA : b ∈ A₂ := by
      refine Subgroup.mem_inf.mpr ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : (u * e) * b * (u * e)⁻¹ = b := by
        calc (u * e) * b * (u * e)⁻¹ = u * (e * b * e⁻¹) * u⁻¹ := by group
          _ = u * b⁻¹ * u⁻¹ := by rw [hbe]
          _ = (u * b * u⁻¹)⁻¹ := by group
          _ = (b⁻¹)⁻¹ := by rw [hWu b hb]
          _ = b := inv_inv b
      calc b * (u * e) = ((u * e) * b * (u * e)⁻¹) * (u * e) := by rw [h1]
        _ = (u * e) * b := by group
    exact ⟨(⟨a, haA⟩, ⟨b, hbA⟩), Subtype.ext hw.symm⟩
  have hcard : Nat.card ↥W ≤ Nat.card (↥A₁ × ↥A₂) := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod] at hcard
  calc Nat.card ↥W ≤ Nat.card ↥A₁ * Nat.card ↥A₂ := hcard
    _ ≤ p ^ 2 * p ^ 2 := Nat.mul_le_mul hA₁ hA₂
    _ = p ^ 4 := by ring


theorem cross_char_core {K : Type} [Group K] [Finite K] {u : K} (hu : u * u = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (hodd : ∀ N : Subgroup K, N ≤ centralizer ({u} : Set K) →
      (∀ c ∈ centralizer ({u} : Set K), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card ↥N) → N = ⊥)
    (hShape : ∀ e : K, e * e = 1 → e ≠ 1 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂)
      (_ : Finite F₁) (_ : Finite F₂) (_ : Shape ↥(centralizer ({e} : Set K)) F₁ F₂),
        Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ ringChar F₁ ≠ p ∧ ringChar F₂ ≠ p)
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (S : Shape ↥(centralizer ({u} : Set K)) F₁ F₂) (hSz : (S.z : K) = u)
    (h₁ : Odd (Nat.card F₁)) (h5 : 5 ≤ Nat.card F₁) (hp₁ : ringChar F₁ ≠ p)
    {X : Subgroup K} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hN : centralizer ({u} : Set K) ≤ normalizer (X : Set K)) :
    ∃ d : ℕ, d ≤ 4 ∧ (Nat.card F₁ - 1) / 2 ≤ d ∧
      p ^ d * Nat.card ↥(centralizer ({u} : Set K)) ∣ Nat.card K := by
  classical
  have hpp : p.Prime := Fact.out
  obtain ⟨W, hW1, hWc, hWp, hWinv, hWu⟩ := exists_inverted_elemAb hu hp2 hodd hX hX1 hN
  have hWpg : IsPGroup p ↥W := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hWp g.1 g.2)⟩
  obtain ⟨d, hd⟩ := hWpg.exists_card_eq
  set e : K := ((S.t : ↥(centralizer ({u} : Set K))) : K) with hedef
  have he : e * e = 1 := by
    have := congrArg Subtype.val S.t_sq
    simpa using this
  have hmemD : e ∈ centralizer ({u} : Set K) := S.t.2
  have hec : e * u = u * e := Subgroup.mem_centralizer_singleton_iff.mp hmemD
  have he1 : e ≠ 1 := by
    intro h
    apply S.t_not_mem
    have : S.t = 1 := Subtype.ext h
    rw [this]
    exact Subgroup.one_mem _
  have heu : e ≠ u := by
    intro h
    apply S.t_not_mem
    have : S.t = S.z := Subtype.ext (h.trans hSz.symm)
    rw [this]
    exact Subgroup.mem_sup_left S.z_mem₁
  have hShape' : ∀ e : K, e * e = 1 → e ≠ 1 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂)
      (_ : Finite F₁) (_ : Finite F₂) (_ : Shape ↥(centralizer ({e} : Set K)) F₁ F₂),
        Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ ringChar F₁ ≠ p ∧ ringChar F₂ ≠ p := hShape
  have hrank : Nat.card ↥W ≤ p ^ 4 :=
    card_le_four_of_inverted hu hp2 hShape' he he1 heu hec W hWc hWp
      (fun w hw => hWinv e hmemD w hw) hWu
  have hd4 : d ≤ 4 := by
    rw [hd] at hrank
    exact (Nat.pow_le_pow_iff_right hpp.one_lt).mp hrank
  have hDW : centralizer ({u} : Set K) ≤ normalizer (W : Set K) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hWinv c hc h hh
    · intro hh
      have hc' : c⁻¹ ∈ centralizer ({u} : Set K) := inv_mem hc
      have := hWinv c⁻¹ hc' _ hh
      simpa [mul_assoc] using this
  have hWD : W ⊓ centralizer ({u} : Set K) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwD⟩ := Subgroup.mem_inf.mp hw
    have h1 : w * u = u * w := Subgroup.mem_centralizer_singleton_iff.mp hwD
    have h2 : w⁻¹ = w := by
      calc w⁻¹ = u * w * u⁻¹ := (hWu w hwW).symm
        _ = w * u * u⁻¹ := by rw [← h1]
        _ = w := by group
    exact Subgroup.mem_bot.mpr (eq_one_of_inv_eq hp2 hpp (hWp w hwW) h2)
  let ρD : ↥(centralizer ({u} : Set K)) →* MulAut ↥W :=
    (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hDW)
  let ρ : SL(2, F₁) →* MulAut ↥W := ρD.comp (S.I₁.subtype.comp S.e₁.symm.toMonoidHom)
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hker
    have hneg := sl2_normal_neg_one_mem h₁ h5 (MonoidHom.ker ρ) hker
    have hρ1 : ρ (-1) = 1 := MonoidHom.mem_ker.mp hneg
    have hz : S.e₁.symm (-1) = (⟨S.z, S.z_mem₁⟩ : ↥S.I₁) := by
      rw [← S.e₁_z]; simp
    obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW1
    have h3 := congrArg (fun a : MulAut ↥W => ((a ⟨w, hwW⟩ : ↥W) : K)) hρ1
    simp only [ρ, ρD, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_subtype, Subgroup.coe_inclusion, MulAut.one_apply, MulEquiv.coe_toMonoidHom] at h3
    have hzK : (((S.e₁.symm (-1) : ↥S.I₁) : ↥(centralizer ({u} : Set K))) : K) = u := by
      rw [hz]; exact hSz
    have h4 : u * w * u⁻¹ = w := by
      rw [hzK] at h3
      exact h3
    rw [hWu w hwW] at h4
    exact hw1 (Subtype.ext (eq_one_of_inv_eq hp2 hpp (hWp w hwW) h4))
  let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with
    mul_comm := fun a b => Subtype.ext (hWc a.1 a.2 b.1 b.2) }
  have hexp : ∀ w : ↥W, w ^ p = 1 := fun w => Subtype.ext (hWp w.1 w.2)
  have hweights : (Nat.card F₁ - 1) / 2 ≤ d :=
    sl2_faithful_weights h₁ hp₁ hexp hd ρ hρ
  refine ⟨d, hd4, hweights, ?_⟩
  have hdiv := card_mul_dvd_of_normalizes W (centralizer ({u} : Set K)) hDW hWD
  rw [hd] at hdiv
  exact hdiv

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
