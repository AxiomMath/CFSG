module

public import CFSG.GH74.GLS.Stage2.Local.IVK33B
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Lift
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Main CFSG.GH74.GLS.Stage2.Final.L26

section Q8

def q8Ev (p q : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => p ^ k.val
  | .xa k => q * p ^ k.val

abbrev Q8Cyc (f : QuaternionGroup 2 → QuaternionGroup 2) : Prop :=
  (∀ x y, f (x * y) = f x * f y) ∧ (∀ x, f (f (f x)) = x) ∧ ∃ x, f x ≠ x

abbrev Q8Quat (f : QuaternionGroup 2 → QuaternionGroup 2) (x : QuaternionGroup 2) : Prop :=
  x * x = .a 2 ∧ f x * f x = .a 2 ∧ f x * x = .a 2 * (x * f x) ∧ f (f x) = x * f x

theorem q8_core : ∀ p q : QuaternionGroup 2, Q8Cyc (q8Ev p q) → ∃ x, Q8Quat (q8Ev p q) x := by
  decide

theorem q8_hom_eq (f : QuaternionGroup 2 →* QuaternionGroup 2) (x : QuaternionGroup 2) :
    f x = q8Ev (f (.a 1)) (f (.xa 0)) x := by
  cases x with
  | a k =>
    have : (QuaternionGroup.a k : QuaternionGroup 2) = (QuaternionGroup.a 1) ^ k.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow]
    simp [q8Ev]
  | xa k =>
    have : (QuaternionGroup.xa k : QuaternionGroup 2) =
        QuaternionGroup.xa 0 * (QuaternionGroup.a 1) ^ k.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a, zero_add]
    rw [this, map_mul, map_pow]
    simp [q8Ev]

theorem q8_center_one_or_two : ∀ g : QuaternionGroup 2, (∀ h, h * g = g * h) → g = 1 ∨ g = .a 2 := by
  decide

theorem q8_two_central : ∀ h : QuaternionGroup 2, h * .a 2 = .a 2 * h := by
  decide

theorem q8_distinct : (.a 1 : QuaternionGroup 2) ≠ 1 ∧ (.xa 0 : QuaternionGroup 2) ≠ 1 ∧
    (.a 1 : QuaternionGroup 2) ≠ .xa 0 := by
  decide

theorem exists_cycle_q8 {K : Type} [Group K] (e : K ≃* QuaternionGroup 2) (α : K →* K)
    (h3 : ∀ k, α (α (α k)) = k) (hne : ∃ k, α k ≠ k) :
    ∃ x : K, x * x = e.symm (.a 2) ∧ α x * α x = e.symm (.a 2) ∧
      α x * x = e.symm (.a 2) * (x * α x) ∧ α (α x) = x * α x := by
  let f : QuaternionGroup 2 →* QuaternionGroup 2 := e.toMonoidHom.comp (α.comp e.symm.toMonoidHom)
  have hf : ∀ q, f q = e (α (e.symm q)) := fun q => rfl
  have hα : ∀ q, α (e.symm q) = e.symm (f q) := fun q => by rw [hf, e.symm_apply_apply]
  have hfe : ∀ k, f (e k) = e (α k) := fun k => by rw [hf, e.symm_apply_apply]
  have hcore : Q8Cyc f := by
    refine ⟨fun x y => map_mul f x y, fun x => ?_, ?_⟩
    · obtain ⟨k, rfl⟩ := e.surjective x
      rw [hfe, hfe, hfe, h3]
    · obtain ⟨k, hk⟩ := hne
      exact ⟨e k, by rw [hfe]; exact fun h => hk (e.injective h)⟩
  have hfun : (⇑f : QuaternionGroup 2 → QuaternionGroup 2) = q8Ev (f (.a 1)) (f (.xa 0)) :=
    funext (q8_hom_eq f)
  have hcore' : Q8Cyc (q8Ev (f (.a 1)) (f (.xa 0))) := by
    rw [← hfun]
    exact hcore
  obtain ⟨x', hx'⟩ := q8_core _ _ hcore'
  rw [← hfun] at hx'
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx'
  refine ⟨e.symm x', ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hx1]
  · rw [hα, ← map_mul, hx2]
  · rw [hα, ← map_mul, ← map_mul, ← map_mul, hx3]
  · rw [hα, hα, ← map_mul, hx4]

theorem q8_central_eq {K : Type} [Group K] (e : K ≃* QuaternionGroup 2) {c : K}
    (hc : c ∈ Subgroup.center K) (hc1 : c ≠ 1) {g : K} (hg : g ∈ Subgroup.center K) :
    g = 1 ∨ g = c := by
  have hcen : ∀ {k : K}, k ∈ Subgroup.center K → e k = 1 ∨ e k = QuaternionGroup.a 2 := by
    intro k hk
    apply q8_center_one_or_two
    intro h
    obtain ⟨k', rfl⟩ := e.surjective h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hk k']
  have hc' : e c = QuaternionGroup.a 2 := by
    rcases hcen hc with h | h
    · exact absurd (e.injective (h.trans e.map_one.symm)) hc1
    · exact h
  rcases hcen hg with h | h
  · exact Or.inl (e.injective (h.trans e.map_one.symm))
  · exact Or.inr (e.injective (h.trans hc'.symm))

theorem q8_two_eq {K : Type} [Group K] (e : K ≃* QuaternionGroup 2) {c : K}
    (hc : c ∈ Subgroup.center K) (hc1 : c ≠ 1) : e.symm (.a 2) = c := by
  have hz : e.symm (QuaternionGroup.a 2) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact q8_two_central (e k)
  rcases q8_central_eq e hc hc1 hz with h | h
  · exfalso
    have h1 : e (e.symm (QuaternionGroup.a 2)) = e 1 := by rw [h]
    rw [e.apply_symm_apply, map_one] at h1
    exact absurd h1 (by decide)
  · exact h

end Q8

section Product

variable {Y : Type} [Group Y]

def conjHomOf (t : Y) (Q : Subgroup Y) (hn : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q) : ↥Q →* ↥Q :=
  MonoidHom.mk' (fun x => ⟨t * x * t⁻¹, hn x x.2⟩) (by
    intro x y
    apply Subtype.ext
    show t * (↑x * ↑y) * t⁻¹ = (t * ↑x * t⁻¹) * (t * ↑y * t⁻¹)
    group)

theorem exists_cycle_of_q8_prod {Q₁ Q₂ : Subgroup Y} (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hcard : Nat.card ↥(Q₁ ⊓ Q₂) = 2) (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2)
    {t : Y} (ht3 : t ^ 3 = 1) (hn₁ : ∀ x ∈ Q₁, t * x * t⁻¹ ∈ Q₁) (hn₂ : ∀ x ∈ Q₂, t * x * t⁻¹ ∈ Q₂)
    (hne₁ : ∃ x ∈ Q₁, t * x * t⁻¹ ≠ x) (hne₂ : ∃ x ∈ Q₂, t * x * t⁻¹ ≠ x) :
    ∃ v₁ v₂ : Y, v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧
      t * v₁ * t⁻¹ = v₂ ∧ t * v₂ * t⁻¹ = v₁ * v₂ ∧ v₁ ∈ Q₁ ⊔ Q₂ ∧ v₂ ∈ Q₁ ⊔ Q₂ := by
  classical
  obtain ⟨c, hc₁, hc₂, hc1, hcc, hsq, hz₁, hz₂⟩ := exists_inf_central hcomm hcard
  have hc1₁ : (⟨c, hc₁⟩ : ↥Q₁) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hc1₂ : (⟨c, hc₂⟩ : ↥Q₂) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have ht3' : t * t * t = 1 := by
    have : t ^ 3 = t * t * t := by simp [pow_succ]
    rw [← this]
    exact ht3
  have hcube : ∀ x : Y, t * (t * (t * x * t⁻¹) * t⁻¹) * t⁻¹ = x := by
    intro x
    calc t * (t * (t * x * t⁻¹) * t⁻¹) * t⁻¹ = (t * t * t) * x * (t * t * t)⁻¹ := by group
      _ = x := by rw [ht3', inv_one, one_mul, mul_one]
  obtain ⟨x₁, hx₁a, hx₁b, hx₁c, hx₁d⟩ := exists_cycle_q8 e₁ (conjHomOf t Q₁ hn₁)
    (fun k => Subtype.ext (hcube k)) (by
      obtain ⟨x, hx, hxne⟩ := hne₁
      exact ⟨⟨x, hx⟩, fun h => hxne (congrArg Subtype.val h)⟩)
  obtain ⟨x₂, hx₂a, hx₂b, hx₂c, hx₂d⟩ := exists_cycle_q8 e₂ (conjHomOf t Q₂ hn₂)
    (fun k => Subtype.ext (hcube k)) (by
      obtain ⟨x, hx, hxne⟩ := hne₂
      exact ⟨⟨x, hx⟩, fun h => hxne (congrArg Subtype.val h)⟩)
  rw [q8_two_eq e₁ hz₁ hc1₁] at hx₁a hx₁b hx₁c
  rw [q8_two_eq e₂ hz₂ hc1₂] at hx₂a hx₂b hx₂c
  obtain ⟨v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    exists_cycle_of_quat_pair hcomm hsq hc₁ hc₂ hcc hc1 (a₁ := x₁) (b₁ := conjHomOf t Q₁ hn₁ x₁)
      (a₂ := x₂) (b₂ := conjHomOf t Q₂ hn₂ x₂) (w := t) hx₁a hx₁b hx₁c hx₂a hx₂b hx₂c rfl rfl
      (congrArg Subtype.val hx₁d) (congrArg Subtype.val hx₂d)
  exact ⟨v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem mem_snd_of_comm_central_prod {Q₁ Q₂ : Subgroup Y} (hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hcard : Nat.card ↥(Q₁ ⊓ Q₂) = 2) (e₁ : ↥Q₁ ≃* QuaternionGroup 2) {x : Y} (hx : x ∈ Q₁ ⊔ Q₂)
    (hxc : ∀ q ∈ Q₁, q * x = x * q) : x ∈ Q₂ := by
  obtain ⟨c, hc₁, hc₂, hc1, -, -, hz₁, -⟩ := exists_inf_central hcomm hcard
  have hc1₁ : (⟨c, hc₁⟩ : ↥Q₁) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hx
  have hcent : (⟨q₁, hq₁⟩ : ↥Q₁) ∈ Subgroup.center ↥Q₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Y) * q₁ = q₁ * g
    have h1 := hxc g g.2
    have h2 := hcomm g g.2 q₂ hq₂
    calc (g : Y) * q₁ = (g * (q₁ * q₂)) * q₂⁻¹ := by group
      _ = ((q₁ * q₂) * g) * q₂⁻¹ := by rw [h1]
      _ = q₁ * (q₂ * g * q₂⁻¹) := by group
      _ = q₁ * g := by rw [← h2]; group
  rcases q8_central_eq e₁ hz₁ hc1₁ hcent with h | h
  · have h' : q₁ = 1 := congrArg Subtype.val h
    rw [h', one_mul]
    exact hq₂
  · have h' : q₁ = c := congrArg Subtype.val h
    rw [h']
    exact Q₂.mul_mem hc₂ hq₂

end Product

section M12

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem prop21h_of_m12 (hz : z * z = 1) (h : Stage1M12 G z S) : Prop21h z := by
  classical
  obtain ⟨Q₁, Q₂, hprod, ⟨e₁⟩, ⟨e₂⟩, hQ₁n⟩ := h.W_shape
  obtain ⟨T, ⟨eT⟩, hLeq, hres, -, -, hfix⟩ := h.L_shape
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hWQ₁ : Q₁ ≤ WBar z := hsup ▸ le_sup_left
  have hWQ₂ : Q₂ ≤ WBar z := hsup ▸ le_sup_right
  have hLW : WBar z ≤ LBar z := by
    rw [hLeq, hres]
    exact le_sup_left
  have hWn : (WBar z).Normal := WBar_normal z
  set t₀ : ↥T := eT.symm (Multiplicative.ofAdd (1 : ZMod 3)) with ht₀
  set t : CentralizerBar z := (t₀ : CentralizerBar z) with ht
  have ht3 : t ^ 3 = 1 := by
    have h1 : t₀ ^ 3 = 1 := by
      rw [ht₀, ← map_pow]
      have : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide
      rw [this, map_one]
    exact congrArg Subtype.val h1
  have hmult : ∀ m : Multiplicative (ZMod 3),
      ∃ n : Fin 3, m = Multiplicative.ofAdd (1 : ZMod 3) ^ (n : ℕ) := by
    decide
  have hTpow : ∀ a ∈ T, ∃ n : ℕ, a = t ^ n := by
    intro a ha
    obtain ⟨n, hn⟩ := hmult (eT ⟨a, ha⟩)
    refine ⟨n, ?_⟩
    have : (⟨a, ha⟩ : ↥T) = t₀ ^ (n : ℕ) := by
      apply eT.injective
      rw [hn, map_pow, ht₀, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val this
  have hn₁ : ∀ x ∈ Q₁, t * x * t⁻¹ ∈ Q₁ := fun x hx => hQ₁n.conj_mem x hx t
  have hn₂ : ∀ x ∈ Q₂, t * x * t⁻¹ ∈ Q₂ := by
    intro x hx
    refine mem_snd_of_comm_central_prod hcomm hcard e₁ (x := t * x * t⁻¹) ?_ ?_
    · rw [hsup]
      exact hWn.conj_mem x (hWQ₂ hx) t
    · intro q hq
      have hq' : t⁻¹ * q * t ∈ Q₁ := by simpa using hQ₁n.conj_mem q hq t⁻¹
      have hcm := hcomm _ hq' x hx
      calc q * (t * x * t⁻¹) = t * ((t⁻¹ * q * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * q * t)) * t⁻¹ := by rw [hcm]
        _ = (t * x * t⁻¹) * q := by group
  have hbar : ∀ g ∈ barOf z (zpowers z), ∀ g' ∈ barOf z (zpowers z), g = 1 ∨ g' = 1 ∨ g = g' := by
    rintro g ⟨c, hc, rfl⟩ g' ⟨c', hc', rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers_sq hz (Subgroup.mem_subgroupOf.1 hc) with h1 | h1
    · left
      have e1 : c = 1 := Subtype.ext h1
      rw [e1, map_one]
    rcases eq_one_or_eq_of_mem_zpowers_sq hz (Subgroup.mem_subgroupOf.1 hc') with h2 | h2
    · right
      left
      have e2 : c' = 1 := Subtype.ext h2
      rw [e2, map_one]
    · right
      right
      have e3 : c = c' := Subtype.ext (h1.trans h2.symm)
      rw [e3]
  have hne : ∀ (Q : Subgroup (CentralizerBar z)) (e : ↥Q ≃* QuaternionGroup 2), Q ≤ WBar z →
      ∃ x ∈ Q, t * x * t⁻¹ ≠ x := by
    intro Q e hQ
    by_contra hcon
    push Not at hcon
    have hmem : ∀ x ∈ Q, x ∈ barOf z (zpowers z) := by
      intro x hx
      apply hfix x (hQ hx)
      intro a ha
      obtain ⟨n, rfl⟩ := hTpow a ha
      have htx : t * x = x * t := by
        calc t * x = (t * x * t⁻¹) * t := by group
          _ = x * t := by rw [hcon x hx]
      exact (show Commute t x from htx).pow_left n
    obtain ⟨h1, h2, h12⟩ := q8_distinct
    have hx₁ := hmem _ (e.symm (.a 1)).2
    have hx₂ := hmem _ (e.symm (.xa 0)).2
    rcases hbar _ hx₁ _ hx₂ with h | h | h
    · exact h1 (by
        have : e.symm (.a 1) = 1 := Subtype.ext h
        simpa using congrArg e this)
    · exact h2 (by
        have : e.symm (.xa 0) = 1 := Subtype.ext h
        simpa using congrArg e this)
    · exact h12 (by
        have : e.symm (.a 1) = e.symm (.xa 0) := Subtype.ext h
        simpa using congrArg e this)
  obtain ⟨v₁, v₂, hv₁, hv₂, hc, h₁, h₂, h₁₂, hw₁, hw₂, hm₁, hm₂⟩ :=
    exists_cycle_of_q8_prod hcomm hcard e₁ e₂ ht3 hn₁ hn₂ (hne Q₁ e₁ hWQ₁) (hne Q₂ e₂ hWQ₂)
  rw [hsup] at hm₁ hm₂
  exact prop21h_of_cycle hv₁ hv₂ hc h₁ h₂ h₁₂ hw₁ hw₂ (hLW hm₁) (hLW hm₂)

end M12

end CFSG.GH74.GLS.Stage2.Local
