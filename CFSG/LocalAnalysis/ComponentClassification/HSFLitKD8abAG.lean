module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AP
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7Basic

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Pointwise

namespace KD8ab

open KD7 Sec8

section Generic

variable {X : Type} [Group X] [Finite X]

theorem exists_centralizer_mul_mem_normalizer {R P : Subgroup X} {g : X}
    (hPN : P ≤ normalizer (centralizer (R : Set X) : Set X)) (hP : IsPGroup 2 P)
    (hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → P ≤ Q → Q ≤ centralizer (R : Set X) ⊔ P → Q = P)
    (hg : P.map (MulAut.conj g).toMonoidHom ≤ centralizer (R : Set X) ⊔ P) :
    ∃ c ∈ centralizer (R : Set X), c * g ∈ normalizer (P : Set X) := by
  obtain ⟨k, hk, hkP⟩ := exists_conj_of_max le_sup_right hg hP (hP.map _) hmax
    (card_map_of_injective (MulAut.conj g).injective)
  have hk' : k ∈ ((centralizer (R : Set X) : Set X) * (P : Set X)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hPN]; exact hk
  obtain ⟨c, hc, s, hs, rfl⟩ := hk'
  refine ⟨c⁻¹, inv_mem hc, Sec7.mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge ?_ ?_)⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : g * x * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    have h2 := (hkP _).mp h1
    have h3 := mul_mem (mul_mem hs h2) (inv_mem hs)
    rwa [show s * ((c * s)⁻¹ * (g * x * g⁻¹) * (c * s)) * s⁻¹ =
      c⁻¹ * g * x * (c⁻¹ * g)⁻¹ by group] at h3
  · rw [card_map_of_injective (MulAut.conj _).injective]

omit [Finite X] in
theorem conj_centralizer_mul {R : Subgroup X} {c g : X} (hc : c ∈ centralizer (R : Set X))
    (hgR : ∀ τ ∈ R, g * τ * g⁻¹ ∈ R) {τ : X} (hτ : τ ∈ R) :
    (c * g) * τ * (c * g)⁻¹ = g * τ * g⁻¹ := by
  have h := mem_centralizer_iff.mp hc _ (hgR τ hτ)
  calc (c * g) * τ * (c * g)⁻¹ = c * (g * τ * g⁻¹) * c⁻¹ := by group
    _ = g * τ * g⁻¹ := by rw [← h, mul_inv_cancel_right]

theorem exists_odd_pow_two_elt (g : X) : ∃ m : ℕ, Odd m ∧ ∃ a : ℕ, (g ^ m) ^ 2 ^ a = 1 := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨m, hm, a, ?_⟩
  rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]

omit [Finite X] in
theorem commutator_eq_top [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) :
    commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX
    apply hab
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ commutator X :=
      commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot] at h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · exact h

theorem false_of_transfer' [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) {t : X}
    (ht : orderOf t = 2) {P Q : Subgroup X} (hP : IsPGroup 2 P)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → P ≤ R → R = P) (hQP : Q ≤ P)
    (hindex : Q.relIndex P = 2) (hQ : ∀ m ∈ Q, ¬ ConjTo t m) : False := by
  obtain ⟨N, hN, hsq, htN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal
    (sylowOfMax hP fun R hR hle => hmax R hR hle) hQP hindex ht
    (fun x hx => hQ _ hx ⟨x⁻¹, by group⟩)
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · obtain ⟨a, b, hab⟩ := hX
    have hsq' : ∀ y : X, y * y = 1 := fun y => by
      have := hsq y
      rwa [h, mem_bot, pow_two] at this
    apply hab
    calc a * b = a * (a * b * (a * b)) * b := by rw [hsq', mul_one]
      _ = (a * a) * b * (a * (b * b)) := by group
      _ = b * a := by rw [hsq', hsq', one_mul, mul_one]
  · exact htN (h ▸ mem_top _)

end Generic

section L2

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : L2Data t L)

theorem card_le_T {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hQt : Q ≤ centralizer ({t} : Set X)) :
    Nat.card Q ≤ Nat.card A.T := by
  obtain ⟨h, -, hh⟩ := L2K.exists_conj_le_T (A := A) hQ hQt
  calc Nat.card Q = Nat.card (Q.map (MulAut.conj h).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj h).injective).symm
    _ ≤ Nat.card A.T := Subgroup.card_le_of_le hh

theorem eq_of_conj {P T' : Subgroup X} (hT'P : T' ≤ P)
    (hT' : T' ≤ centralizer ({t} : Set X)) (hcard : Nat.card A.T ≤ Nat.card T')
    (hconj : ∀ Q : Subgroup X, IsPGroup 2 Q → P ≤ Q → ∀ h ∈ Q, h ∈ normalizer (P : Set X) →
      ∃ g ∈ P, h * t * h⁻¹ = g * t * g⁻¹)
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hPQ : P ≤ Q) : Q = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨h, hhQ, hhN, hhP⟩ : ∃ h ∈ Q, h ∈ normalizer (P : Set X) ∧ h ∉ P := by
    set I := P.subgroupOf Q with hI
    have hIne : I ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm (fun x hx => ?_) hPQ
      have : (⟨x, hx⟩ : Q) ∈ I := by rw [htop]; trivial
      exact this
    have hnil : Group.IsNilpotent Q := hQ.isNilpotent
    have hlt : I < normalizer (I : Set Q) :=
      Group.normalizerCondition_of_isNilpotent I (lt_of_le_of_ne le_top hIne)
    obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨x, x.2, ?_, fun h => hxI h⟩
    have hxsub : x ∈ (normalizer (P : Set X)).subgroupOf Q := by
      rw [subgroupOf_normalizer_eq hPQ]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  obtain ⟨g, hgP, hg⟩ := hconj Q hQ hPQ h hhQ hhN
  set c := g⁻¹ * h with hc
  have hcQ : c ∈ Q := mul_mem (inv_mem (hPQ hgP)) hhQ
  have hct : c ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have : c * t * c⁻¹ = t := by
      rw [hc, show g⁻¹ * h * t * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * t * h⁻¹) * g by group, hg]; group
    calc c * t = (c * t * c⁻¹) * c := by group
      _ = t * c := by rw [this]
  have hle : T' ⊔ zpowers c ≤ centralizer ({t} : Set X) := sup_le hT' (zpowers_le.mpr hct)
  have hQ' : IsPGroup 2 (T' ⊔ zpowers c : Subgroup X) :=
    hQ.to_le (sup_le (hT'P.trans hPQ) (zpowers_le.mpr hcQ))
  have heq : T' = T' ⊔ zpowers c := Subgroup.eq_of_le_of_card_ge le_sup_left
    ((card_le_T A hQ' hle).trans hcard)
  have hcT' : c ∈ T' := heq ▸ mem_sup_right (mem_zpowers c)
  apply hhP
  rw [show h = g * c by rw [hc]; group]
  exact mul_mem hgP (hT'P hcT')

theorem central_H8 : ∀ (u : (ZMod 8)ˣ) (b : ZMod 8), ∀ b₁ ∈ [(2 : ZMod 8), 6],
    ∀ e ∈ [(0 : ZMod 8), 2, 4, 6],
    (aff8 u b * aff8 1 b₁ = aff8 1 b₁ * aff8 u b ∧ aff8 u b * aff8 (-1) e = aff8 (-1) e * aff8 u b ∧
      aff8 u b * k8 = k8 * aff8 u b ∧ aff8 u b * d8 = d8 * aff8 u b) →
    aff8 u b = 1 ∨ aff8 u b = z8 := by decide

theorem even_mem : ∀ e : ZMod 8, dbit8 e = 0 → e ∈ [(0 : ZMod 8), 2, 4, 6] := by decide

variable {C : A.CaseKD} (S : KDBase A C)

include S in
theorem sq_of_central {g : X} (hg : g ∈ A.T) (hc : ∀ h ∈ A.T, g * h = h * g) : g ^ 2 = 1 := by
  obtain ⟨b, hb, hx⟩ := ψX_x S
  obtain ⟨e, he, hy⟩ := (isRefl_y S).ψX
  have hψ : ∀ h ∈ A.T, L2K.ψX A g * L2K.ψX A h = L2K.ψX A h * L2K.ψX A g := fun h hh => by
    rw [← L2K.ψX_mul hg hh, ← L2K.ψX_mul hh hg, hc h hh]
  have h1 := hψ _ (x_mem_T S)
  have h2 := hψ _ (y_mem_T S)
  have h3 := hψ _ C.k_mem
  have h4 := hψ _ C.d_mem
  rw [hx] at h1
  rw [hy] at h2
  rw [L2KD.ψX_k C] at h3
  rw [L2KD.ψX_d C] at h4
  obtain ⟨u, b', hub⟩ : ∃ u b', aff8 u b' = L2K.ψX A g := by
    rw [L2K.ψX_of_mem hg]; exact A.ψ_mem_H8 _
  rw [← hub] at h1 h2 h3 h4
  have hzz : S.z * S.z = 1 := zz S
  have hzt : S.z * t = t * S.z := (z_comm_T S A.t_mem_T).symm
  have hb' : b ∈ [(2 : ZMod 8), 6] := by rcases hb with rfl | rfl <;> simp
  rcases central_H8 u b' b hb' e (even_mem e he) ⟨h1, h2, h3, h4⟩ with h | h
  · have hK : g ∈ A.K := by rw [← L2K.ψX_eq_one_iff hg, ← hub, h]
    rcases L2KD.eq_one_or_eq_t_of_mem_K C hK with rfl | rfl
    · exact one_pow 2
    · exact L2K.t_sq (A := A)
  · have hzg : S.z * g ∈ A.T := mul_mem (z_mem_T S) hg
    have hK : S.z * g ∈ A.K := by
      rw [← L2K.ψX_eq_one_iff hzg, L2K.ψX_mul (z_mem_T S) hg, ψX_z S, ← hub, h]
      decide
    have hg' : g = S.z * (S.z * g) := by rw [← mul_assoc, hzz, one_mul]
    rcases L2KD.eq_one_or_eq_t_of_mem_K C hK with h' | h' <;> rw [hg', h', pow_two]
    · rw [mul_one, hzz]
    · calc S.z * t * (S.z * t) = S.z * (t * S.z) * t := by group
        _ = 1 := by rw [← hzt, ← mul_assoc, hzz, one_mul, tt (A := A)]

include S in
theorem not_conjTo_of_center {g q : X} {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hQg : Q ≤ centralizer ({g} : Set X)) (hcard : Nat.card A.T ≤ Nat.card Q) (hq : q ∈ Q)
    (hqc : ∀ x ∈ Q, q * x = x * q) (hq2 : q ^ 2 ≠ 1) : ¬ ConjTo t g := by
  rintro ⟨c, hc⟩
  set f : X →* X := ((MulAut.conj c⁻¹).toMonoidHom) with hf
  have hfinj : Function.Injective f := (MulAut.conj c⁻¹).injective
  have hQ't : Q.map f ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hag := mem_centralizer_singleton_iff.mp (hQg ha)
    rw [← hc] at hag
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * a * c * t = c⁻¹ * (a * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * a) * c := by rw [hag]
      _ = t * (c⁻¹ * a * c) := by group
  obtain ⟨h, -, hh⟩ := L2K.exists_conj_le_T (A := A) (hQ.map f) hQ't
  set f' : X →* X := (MulAut.conj h).toMonoidHom with hf'
  have hf'inj : Function.Injective f' := (MulAut.conj h).injective
  have heq : (Q.map f).map f' = A.T := Subgroup.eq_of_le_of_card_ge hh (by
    rw [card_map_of_injective hf'inj, card_map_of_injective hfinj]; exact hcard)
  have hq'T : f' (f q) ∈ A.T := heq ▸ ⟨f q, ⟨q, hq, rfl⟩, rfl⟩
  have hcen : ∀ x ∈ A.T, f' (f q) * x = x * f' (f q) := by
    intro x hx
    rw [← heq] at hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hqc y hy]
  have h2 := sq_of_central A S hq'T hcen
  apply hq2
  rw [← map_pow, ← map_pow] at h2
  exact hfinj (hf'inj (by rw [h2, map_one, map_one]))

end L2

end KD8ab

end CFSG.ComponentClassification.HSFLit
