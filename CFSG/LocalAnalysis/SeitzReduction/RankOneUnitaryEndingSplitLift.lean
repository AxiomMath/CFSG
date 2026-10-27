module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingDecompLift

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_product_of_comm [Finite G] {U R A J₁ J₂ : Subgroup G} {t d e : G} {o : ℕ}
    (hUR : ∀ x ∈ U, ∀ r ∈ R, x * r = r * x) (hU' : ⁅U, U⁆ = R) (hsq : ∀ r ∈ R, r ^ 2 = 1)
    (hJ : J₁ ⊔ J₂ = U) (hJinf : J₁ ⊓ J₂ = R)
    (htt : t * t = 1) (ht₁ : ∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) (ht₂ : ∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁)
    (hA : ∀ r ∈ R, r * t = t * r → r ∈ A) (hAt : ∀ a ∈ A, a * t = t * a)
    (hRA : ¬ R ≤ A) (hdA : d ∈ normalizer (A : Set G)) (hdJ₁ : d ∈ normalizer (J₁ : Set G))
    (hX₁ : ∀ X : Subgroup G, X ≤ A → d ∈ normalizer (X : Set G) → X = ⊥ ∨ A ≤ X)
    (hX₂ : ∀ X : Subgroup G, A ≤ X → X ≤ R → d ∈ normalizer (X : Set G) → X ≤ A ∨ R ≤ X)
    (hc12 : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a)
    (heJ₁ : ∀ x ∈ J₁, e * x * e⁻¹ ∈ J₁) (heR : ∀ r ∈ R, e * r * e⁻¹ = r) (ho : Odd o)
    (heo : e ^ o = 1) (hefpf : ∀ x ∈ J₁, e * x * e⁻¹ * x⁻¹ ∈ R → x ∈ R)
    (hJ' : ⁅J₁, J₁⁆ ≠ R) :
    ∃ Y₁ Y₂ : Subgroup G, Y₁ ⊔ Y₂ = U ∧ Y₁ ⊓ Y₂ = ⊥ ∧ (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) ∧
      (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) ∧ (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htt' : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := fun x => by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt, inv_one, one_mul, mul_one]
  have hRJ₁ : R ≤ J₁ := hJinf ▸ inf_le_left
  have hRJ₂ : R ≤ J₂ := hJinf ▸ inf_le_right
  have hJ₁U : J₁ ≤ U := hJ ▸ le_sup_left
  have hJ₂U : J₂ ≤ U := hJ ▸ le_sup_right
  have hRU : R ≤ U := hRJ₁.trans hJ₁U
  have htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := fun r hr => by
    rw [← hJinf] at hr ⊢
    obtain ⟨h1, h2⟩ := mem_inf.mp hr
    exact mem_inf.mpr ⟨ht₂ r h2, ht₁ r h1⟩
  set Z₁ := ⁅J₁, J₁⁆ with hZ₁
  set Z₂ := ⁅J₂, J₂⁆ with hZ₂
  have hZ₁R : Z₁ ≤ R := hU' ▸ commutator_mono hJ₁U hJ₁U
  have hZ₂R : Z₂ ≤ R := hU' ▸ commutator_mono hJ₂U hJ₂U
  have htZ₁ : ∀ z ∈ Z₁, t * z * t⁻¹ ∈ Z₂ := conj_mem_commutator_of_conj ht₁
  have htZ₂ : ∀ z ∈ Z₂, t * z * t⁻¹ ∈ Z₁ := conj_mem_commutator_of_conj ht₂
  have hRZ : R ≤ Z₁ ⊔ Z₂ := by
    rw [← hU', commutator_le]
    intro x hx y hy
    rw [← hJ] at hx hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hc12 hx
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hc12 hy
    have hX : b * b' * b⁻¹ ∈ J₂ := mul_mem (mul_mem hb hb') (inv_mem hb)
    have hX' : b * b' * b⁻¹ * b'⁻¹ ∈ J₂ := mul_mem hX (inv_mem hb')
    have e : ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
      simp only [commutatorElement_def]
      calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹ =
          a * (b * a') * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by group
        _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by rw [← hc12 a' ha' b hb]
        _ = a * a' * (b * b' * b⁻¹ * a⁻¹) * b'⁻¹ * a'⁻¹ := by group
        _ = a * a' * (a⁻¹ * (b * b' * b⁻¹)) * b'⁻¹ * a'⁻¹ := by
            rw [← hc12 a⁻¹ (inv_mem ha) _ hX]
        _ = a * a' * a⁻¹ * (b * b' * b⁻¹ * b'⁻¹ * a'⁻¹) := by group
        _ = a * a' * a⁻¹ * (a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹)) := by
            rw [← hc12 a'⁻¹ (inv_mem ha') _ hX']
        _ = a * a' * a⁻¹ * a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left (commutator_mem_commutator ha ha'))
      (mem_sup_right (commutator_mem_commutator hb hb'))
  have hdZ₁ : d ∈ normalizer (Z₁ : Set G) := mem_normalizer_commutator hdJ₁
  have hD : Z₁ ⊓ A = ⊥ := by
    have hdD : d ∈ normalizer ((Z₁ ⊓ A : Subgroup G) : Set G) := by
      refine mem_normalizer_iff.mpr fun z => ?_
      exact and_congr (mem_normalizer_iff.mp hdZ₁ z) (mem_normalizer_iff.mp hdA z)
    rcases hX₁ (Z₁ ⊓ A) inf_le_right hdD with h | h
    · exact h
    · exfalso
      have hAZ : A ≤ Z₁ := h.trans inf_le_left
      rcases hX₂ Z₁ hAZ hZ₁R hdZ₁ with h' | h'
      · apply hRA
        have hZ₂A : Z₂ ≤ A := by
          intro z hz
          have h1 : t * z * t⁻¹ ∈ A := h' (htZ₂ z hz)
          have h2 := hAt _ h1
          have e : z = t * z * t⁻¹ := by
            calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
              _ = t⁻¹ * (t * (t * z * t⁻¹)) := by rw [mul_assoc, h2]
              _ = t * z * t⁻¹ := by group
          rw [e]
          exact h1
        exact hRZ.trans (sup_le h' hZ₂A)
      · exact hJ' (le_antisymm hZ₁R h')
  have hRab : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := fun r hr r' hr' => hUR r (hRU hr) r' hr'
  have hZ : Z₁ ⊓ Z₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz₁, hz₂⟩ := mem_inf.mp hz
    have hzR : z ∈ R := hZ₁R hz₁
    have hz' : t * z * t⁻¹ ∈ Z₁ := htZ₂ z hz₂
    have hz'R : t * z * t⁻¹ ∈ R := hZ₁R hz'
    have hwt : z * (t * z * t⁻¹) * t = t * (z * (t * z * t⁻¹)) := by
      calc z * (t * z * t⁻¹) * t = z * t * z := by group
        _ = (t * t) * z * t⁻¹ * z := by rw [htt, htinv]; group
        _ = t * ((t * z * t⁻¹) * z) := by group
        _ = t * (z * (t * z * t⁻¹)) := by rw [hRab z hzR _ hz'R]
    have hwA : z * (t * z * t⁻¹) ∈ A := hA _ (mul_mem hzR hz'R) hwt
    have hw1 : z * (t * z * t⁻¹) = 1 := by
      have := mem_inf.mpr ⟨mul_mem hz₁ hz', hwA⟩
      rw [hD] at this
      exact mem_bot.mp this
    have hz2 : z * z = 1 := by
      have := hsq z hzR
      rwa [sq] at this
    have htz : t * z * t⁻¹ = z := by
      rw [eq_inv_of_mul_eq_one_right hw1, inv_eq_of_mul_eq_one_right hz2]
    have hzt : z * t = t * z := by
      calc z * t = t * z * t⁻¹ * t := by rw [htz]
        _ = t * z := by group
    have := mem_inf.mpr ⟨hz₁, hA z hzR hzt⟩
    rw [hD] at this
    exact this
  have hJ₁R : ∀ x ∈ J₁, ∀ r ∈ R, x * r = r * x := fun x hx r hr => hUR x (hJ₁U hx) r hr
  have hJ₁Z : ∀ x ∈ J₁, ∀ y ∈ J₁, x * y * x⁻¹ * y⁻¹ ∈ Z₁ := fun x hx y hy => by
    have := commutator_mem_commutator hx hy
    rwa [commutatorElement_def] at this
  obtain ⟨Y₁, hY₁J, hZY₁, hY₁R, hY₁sur⟩ :=
    exists_complement_of_fpf hZ₁R hRJ₁ hJ₁R hJ₁Z hsq heJ₁ heR ho heo hefpf
  set Y₂ := Y₁.map (MulAut.conj t).toMonoidHom with hY₂
  have hmemY₂ : ∀ b, b ∈ Y₂ ↔ ∃ a ∈ Y₁, t * a * t⁻¹ = b := by
    intro b
    simp [hY₂, MulAut.conj_apply]
  have hY₂J : Y₂ ≤ J₂ := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (hmemY₂ b).mp hb
    exact ht₁ a (hY₁J ha)
  refine ⟨Y₁, Y₂, ?_, ?_, fun a ha b hb => hc12 a (hY₁J ha) b (hY₂J hb),
    fun a ha => (hmemY₂ _).mpr ⟨a, ha, rfl⟩, ?_⟩
  · apply le_antisymm (sup_le (hY₁J.trans hJ₁U) (hY₂J.trans hJ₂U))
    have hZ₂Y₂ : Z₂ ≤ Y₂ := fun z hz => (hmemY₂ z).mpr ⟨t * z * t⁻¹, hZY₁ (htZ₂ z hz), htt' z⟩
    have hRY : R ≤ Y₁ ⊔ Y₂ := hRZ.trans (sup_le_sup hZY₁ hZ₂Y₂)
    rw [← hJ]
    apply sup_le
    · intro x hx
      obtain ⟨y, hy, r, hr, rfl⟩ := hY₁sur x hx
      exact mul_mem (mem_sup_left hy) (hRY hr)
    · intro x hx
      obtain ⟨y, hy, r, hr, hxyr⟩ := hY₁sur _ (ht₂ x hx)
      have e : x = (t * y * t⁻¹) * (t * r * t⁻¹) := by
        calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
          _ = t⁻¹ * (y * r) * t := by rw [hxyr]
          _ = (t⁻¹ * y * t) * (t⁻¹ * r * t) := by group
          _ = (t * y * t⁻¹) * (t * r * t⁻¹) := by rw [htinv]
      rw [e]
      exact mul_mem (mem_sup_right ((hmemY₂ _).mpr ⟨y, hy, rfl⟩)) (hRY (htR r hr))
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
    obtain ⟨a, ha, rfl⟩ := (hmemY₂ _).mp hx₂
    have hxR : t * a * t⁻¹ ∈ R := by
      rw [← hJinf]
      exact mem_inf.mpr ⟨hY₁J hx₁, hY₂J hx₂⟩
    have haR : a ∈ R := by
      have := htR _ hxR
      rwa [htt'] at this
    have haZ : a ∈ Z₁ := hY₁R (mem_inf.mpr ⟨ha, haR⟩)
    have hxZ₁ : t * a * t⁻¹ ∈ Z₁ := hY₁R (mem_inf.mpr ⟨hx₁, hxR⟩)
    have := mem_inf.mpr ⟨hxZ₁, htZ₁ a haZ⟩
    rw [hZ] at this
    exact this
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := (hmemY₂ b).mp hb
    rwa [htt']

end CFSG.SeitzReduction.RankOne
