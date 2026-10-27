module

public import CFSG.CGT.T75M.StageA1
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement Pointwise

@[expose] def SzTriangleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (T T₁ : Subgroup G) (a : ℕ), SzData T T₁ a →
      ∀ c ∈ Subgroup.normalizer (T : Set G), conjSubgroup c (normIn T T₁) = normIn T T₁ →
        IsElemAbelian 2 (normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T)) →
        (∀ y ∈ T ⊔ T₁ ⊔ conjSubgroup c T₁,
          ∀ n ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T),
            y * n * y⁻¹ ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T)) →
        conjSubgroup c T₁ ≤ T ⊔ T₁

section Basic

variable {G : Type} [Group G]

theorem isElemAbelian_of_le' {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A) (hBA : B ≤ A) :
    IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hA hBA

end Basic


section Tri

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {a : ℕ}

omit [Finite G] in
theorem szData_conj_normalizer (hD : SzData T T₁ a) {c : G}
    (hc : c ∈ Subgroup.normalizer (T : Set G)) : SzData T (conjSubgroup c T₁) a := by
  have := hD.conj c
  rwa [mem_normalizer_iff_conjSubgroup_eq.1 hc] at this

theorem p2_of_normalizes (hD : SzData T T₁ a) {c : G}
    (hc : c ∈ Subgroup.normalizer (T : Set G))
    (hN : ∀ x ∈ normIn T₁ T, x ∈ Subgroup.normalizer ((conjSubgroup c T₁ : Subgroup G) : Set G)) :
    ∀ x ∈ normIn T₁ T, (∀ z ∈ T ⊔ conjSubgroup c T₁, ⁅x, z⁆ ∈ cfgM T (conjSubgroup c T₁)) ∧
      ∀ m ∈ cfgM T (conjSubgroup c T₁), m * x = x * m := by
  have hD₂ := szData_conj_normalizer hD hc
  intro x hx
  have hxN := hN x hx
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hx).2
  have hx2 : x * x = 1 := elemAbelian_mul_self hD.sec3.cfg.wc₁.1 (normIn_le _ _ hx)
  by_cases hx1 : x = 1
  · subst hx1
    exact ⟨fun z _ => by simp [commutatorElement_def], fun m _ => by simp⟩
  · have hidx : Nat.card T ≤
        2 ^ (2 * a + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [inf_centralizer_eq_normIn hD.sec3.cfg hx hx1, hD.card_eq_mul, mul_comm]
    exact hD₂.centralizes_of_normalizes hxT hxN hx2 hidx

theorem conj_normIn_eq_of_p2 (hD : SzData T T₁ a) {c : G}
    (hc : c ∈ Subgroup.normalizer (T : Set G))
    (hP2 : ∀ x ∈ normIn T₁ T, ∀ m ∈ cfgM T (conjSubgroup c T₁), m * x = x * m) :
    conjSubgroup c (normIn T T₁) = normIn T T₁ := by
  have hcfg := hD.sec3.cfg
  have hcT : conjSubgroup c T = T := mem_normalizer_iff_conjSubgroup_eq.1 hc
  have hL₂ : conjSubgroup c (normIn T T₁) = normIn T (conjSubgroup c T₁) := by
    have := normIn_conj c T T₁
    rw [hcT] at this
    exact this.symm
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hle : conjSubgroup c (normIn T T₁) ≤ normIn T T₁ := by
    intro l hl
    have hlT : l ∈ T := by rw [hL₂] at hl; exact normIn_le _ _ hl
    have hlM₂ : l ∈ cfgM T (conjSubgroup c T₁) := by
      rw [hL₂] at hl; exact Cfg.normIn_le_cfgM_left T _ hl
    have hcomm := hP2 x₀ hx₀ l hlM₂
    rw [← inf_centralizer_eq_normIn hcfg hx₀ hx₀1']
    exact ⟨hlT, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem p1_of_p2 (hD : SzData T T₁ a) {c : G}
    (hc : c ∈ Subgroup.normalizer (T : Set G))
    (hP2 : ∀ x ∈ normIn T₁ T, ∀ m ∈ cfgM T (conjSubgroup c T₁), m * x = x * m) :
    ∀ u ∈ conjSubgroup c (normIn T₁ T),
      u ∈ Subgroup.normalizer (T₁ : Set G) ∧ ∀ m ∈ cfgM T T₁, m * u = u * m := by
  have hcfg := hD.sec3.cfg
  have hcT : conjSubgroup c T = T := mem_normalizer_iff_conjSubgroup_eq.1 hc
  have hLL := conj_normIn_eq_of_p2 hD hc hP2
  have hL₁₂ : conjSubgroup c (normIn T₁ T) = normIn (conjSubgroup c T₁) T := by
    have := normIn_conj c T₁ T
    rw [hcT] at this
    exact this.symm
  have hL₂ : conjSubgroup c (normIn T T₁) = normIn T (conjSubgroup c T₁) := by
    have := normIn_conj c T T₁
    rw [hcT] at this
    exact this.symm
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  intro u hu
  have huM₂ : u ∈ cfgM T (conjSubgroup c T₁) := by
    rw [hL₁₂] at hu; exact Cfg.normIn_le_cfgM_right T _ hu
  have hux : ∀ x ∈ normIn T₁ T, u * x = x * u := fun x hx => hP2 x hx u huM₂
  refine ⟨hcfg.wc₁.centralizer_le_normalizer (normIn_le _ _ hx₀) hx₀1'
    (Subgroup.mem_centralizer_singleton_iff.2 (hux x₀ hx₀)), fun m hm => ?_⟩
  obtain ⟨l, hl, x, hx, rfl⟩ := hcfg.mem_cfgM_iff.1 hm
  have hlu : l * u = u * l := by
    by_cases hu1 : u = 1
    · rw [hu1]; simp
    · have hs : c⁻¹ * u * c ∈ normIn T₁ T := mem_conjSubgroup.1 hu
      have hs1 : c⁻¹ * u * c ≠ 1 := fun h => hu1 (by
        have e : u = c * (c⁻¹ * u * c) * c⁻¹ := by group
        rw [e, h]; group)
      have heq : c * (c⁻¹ * u * c) * c⁻¹ = u := by group
      have h1 := inf_centralizer_conj hcfg hs hs1 hc
      rw [heq, hLL] at h1
      have h2 : l ∈ T ⊓ Subgroup.centralizer ({u} : Set G) := by rw [h1]; exact hl
      exact Subgroup.mem_centralizer_singleton_iff.1 h2.2
  have hxu : x * u = u * x := (hux x hx).symm
  calc l * x * u = l * (x * u) := by rw [mul_assoc]
    _ = l * (u * x) := by rw [hxu]
    _ = (l * u) * x := by rw [mul_assoc]
    _ = (u * l) * x := by rw [hlu]
    _ = u * (l * x) := by rw [mul_assoc]


omit [Finite G] in
theorem normalizes_of_p1 (hD : SzData T T₁ a) {c : G} (hc : c ∈ Subgroup.normalizer (T : Set G))
    (hP1 : ∀ u ∈ conjSubgroup c (normIn T₁ T),
      u ∈ Subgroup.normalizer (T₁ : Set G) ∧ ∀ m ∈ cfgM T T₁, m * u = u * m) :
    ∀ x ∈ normIn T₁ T, x ∈ Subgroup.normalizer ((conjSubgroup c T₁ : Subgroup G) : Set G) := by
  have hcfg := hD.sec3.cfg
  have hcT : conjSubgroup c T = T := mem_normalizer_iff_conjSubgroup_eq.1 hc
  have hL₁₂ : conjSubgroup c (normIn T₁ T) = normIn (conjSubgroup c T₁) T := by
    have := normIn_conj c T₁ T
    rw [hcT] at this
    exact this.symm
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hu₀ : c * x₀ * c⁻¹ ∈ conjSubgroup c (normIn T₁ T) := by
    rw [mem_conjSubgroup]
    have e : c⁻¹ * (c * x₀ * c⁻¹) * c = x₀ := by group
    rw [e]; exact hx₀
  have hu₀1 : c * x₀ * c⁻¹ ≠ 1 := fun h => hx₀1' (by
    have e : x₀ = c⁻¹ * (c * x₀ * c⁻¹) * c := by group
    rw [e, h]; group)
  have hu₀T₂ : c * x₀ * c⁻¹ ∈ conjSubgroup c T₁ := normIn_le _ _ (hL₁₂ ▸ hu₀)
  intro x hx
  have h1 := (hP1 _ hu₀).2 x (Cfg.normIn_le_cfgM_right T T₁ hx)
  exact (hcfg.wc₁.conj c).centralizer_le_normalizer hu₀T₂ hu₀1
    (Subgroup.mem_centralizer_singleton_iff.2 h1)

theorem conj_le_of_p1 (hKL : SzTriangleInput)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hD : SzData T T₁ a) {c : G}
    (hc : c ∈ Subgroup.normalizer (T : Set G))
    (hP1 : ∀ u ∈ conjSubgroup c (normIn T₁ T),
      u ∈ Subgroup.normalizer (T₁ : Set G) ∧ ∀ m ∈ cfgM T T₁, m * u = u * m) :
    conjSubgroup c T₁ ≤ T ⊔ T₁ := by
  classical
  have hS := hD.sec3
  have hcfg := hS.cfg
  have hcT : conjSubgroup c T = T := mem_normalizer_iff_conjSubgroup_eq.1 hc
  set T₂ : Subgroup G := conjSubgroup c T₁ with hT₂
  have hD₂ : SzData T T₂ a := szData_conj_normalizer hD hc
  have hS₂ := hD₂.sec3
  have hL₁₂ : conjSubgroup c (normIn T₁ T) = normIn T₂ T := by
    have := normIn_conj c T₁ T
    rw [hcT] at this
    exact this.symm
  have hL₂ : conjSubgroup c (normIn T T₁) = normIn T T₂ := by
    have := normIn_conj c T T₁
    rw [hcT] at this
    exact this.symm
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hu₀ : c * x₀ * c⁻¹ ∈ conjSubgroup c (normIn T₁ T) := by
    rw [mem_conjSubgroup]
    have e : c⁻¹ * (c * x₀ * c⁻¹) * c = x₀ := by group
    rw [e]; exact hx₀
  have hu₀1 : c * x₀ * c⁻¹ ≠ 1 := fun h => hx₀1' (by
    have e : x₀ = c⁻¹ * (c * x₀ * c⁻¹) * c := by group
    rw [e, h]; group)
  have hu₀T₂ : c * x₀ * c⁻¹ ∈ T₂ := normIn_le _ _ (hL₁₂ ▸ hu₀)
  have hN : ∀ x ∈ normIn T₁ T, x ∈ Subgroup.normalizer (T₂ : Set G) := by
    intro x hx
    have h1 := (hP1 _ hu₀).2 x (Cfg.normIn_le_cfgM_right T T₁ hx)
    exact (hcfg.wc₁.conj c).centralizer_le_normalizer hu₀T₂ hu₀1
      (Subgroup.mem_centralizer_singleton_iff.2 h1)
  have hP2 := p2_of_normalizes hD hc hN
  have hLL : conjSubgroup c (normIn T T₁) = normIn T T₁ :=
    conj_normIn_eq_of_p2 hD hc (fun x hx => (hP2 x hx).2)
  have hLeq : normIn T T₂ = normIn T T₁ := hL₂.symm.trans hLL
  have hUX : ∀ u ∈ conjSubgroup c (normIn T₁ T), ∀ z ∈ T ⊔ T₁, ⁅u, z⁆ ∈ cfgM T T₁ := by
    intro u hu z hz
    by_cases hu1 : u = 1
    · subst hu1
      simp [commutatorElement_def]
    · have hx : c⁻¹ * u * c ∈ normIn T₁ T := mem_conjSubgroup.1 hu
      have hx1 : c⁻¹ * u * c ≠ 1 := fun h => hu1 (by
        have e : u = c * (c⁻¹ * u * c) * c⁻¹ := by group
        rw [e, h]; group)
      have heq : c * (c⁻¹ * u * c) * c⁻¹ = u := by group
      have huT : u ∈ Subgroup.normalizer (T : Set G) := by
        have h1 : c * (c⁻¹ * u * c) * c⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
          (Subgroup.normalizer (T : Set G)).mul_mem
            ((Subgroup.normalizer (T : Set G)).mul_mem hc (mem_normIn.1 hx).2)
            ((Subgroup.normalizer (T : Set G)).inv_mem hc)
        rwa [heq] at h1
      have huT₂ : u ∈ T₂ := normIn_le _ _ (hL₁₂ ▸ hu)
      have hu2 : u * u = 1 :=
        elemAbelian_mul_self (isElemAbelian_conjSubgroup hcfg.wc₁.1 c) huT₂
      have hidx : Nat.card T ≤
          2 ^ (2 * a + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G)) := by
        rw [← heq, card_inf_centralizer_conj hcfg hx hx1 hc, hD.card_eq_mul, mul_comm]
      exact (hD.centralizes_of_normalizes huT (hP1 u hu).1 hu2 hidx).1 z hz
  have hL₁'el : IsElemAbelian 2 (conjSubgroup c (normIn T₁ T)) :=
    isElemAbelian_conjSubgroup (isElemAbelian_of_le' hcfg.wc₁.1 (normIn_le T₁ T)) c
  have hNel : IsElemAbelian 2
      (normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T)) :=
    isElemAbelian_sup_of_commute hcfg.isElemAbelian_cfgM hL₁'el
      (fun m hm u hu => (hP1 u hu).2 m hm)
  set N : Subgroup G := normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup c (normIn T₁ T) with hNdef
  have hMN : ∀ m ∈ cfgM T T₁, m ∈ N := fun m hm => Subgroup.mem_sup_left hm
  have hL₁'N : ∀ u ∈ conjSubgroup c (normIn T₁ T), u ∈ N := fun u hu => Subgroup.mem_sup_right hu
  have hsplit : ∀ n ∈ N, ∃ m ∈ cfgM T T₁, ∃ u ∈ conjSubgroup c (normIn T₁ T), n = m * u :=
    fun n hn => exists_mul_of_mem_sup_of_commute (A := cfgM T T₁)
      (fun m hm u hu => (hP1 u hu).2 m hm) hn
  have hnorm_of : ∀ y : G, (∀ m ∈ cfgM T T₁, y * m * y⁻¹ ∈ N) →
      (∀ u ∈ conjSubgroup c (normIn T₁ T), y * u * y⁻¹ ∈ N) →
      y ∈ Subgroup.normalizer (N : Set G) := by
    intro y h1 h2
    rw [mem_normalizer_iff_conjSubgroup_eq]
    refine conjSubgroup_eq_of_le fun n hn => ?_
    rw [mem_conjSubgroup] at hn
    obtain ⟨m, hm, u, hu, hmu⟩ := hsplit _ hn
    have : n = (y * m * y⁻¹) * (y * u * y⁻¹) := by
      have e : n = y * (y⁻¹ * n * y) * y⁻¹ := by group
      rw [e, hmu]; group
    rw [this]
    exact N.mul_mem (h1 m hm) (h2 u hu)
  have hTle : T ≤ Subgroup.normalizer (N : Set G) := by
    intro y hy
    refine hnorm_of y (fun m hm => hMN _ (hcfg.conj_mem_cfgM (Subgroup.mem_sup_left hy) hm))
      (fun u hu => ?_)
    have hu' : u ∈ normIn T₂ T := hL₁₂ ▸ hu
    have h1 : ⁅y, u⁆ ∈ normIn T T₂ := hS₂.cfg.comm_mem_normIn hy hu'
    rw [hLeq] at h1
    have h2 : y * u * y⁻¹ = ⁅y, u⁆ * u := by simp only [commutatorElement_def]; group
    rw [h2]
    exact N.mul_mem (hMN _ (Cfg.normIn_le_cfgM_left T T₁ h1)) (hL₁'N u hu)
  have hT₁le : T₁ ≤ Subgroup.normalizer (N : Set G) := by
    intro y hy
    refine hnorm_of y (fun m hm => hMN _ (hcfg.conj_mem_cfgM (Subgroup.mem_sup_right hy) hm))
      (fun u hu => ?_)
    have h1 : ⁅y, u⁆ ∈ cfgM T T₁ := by
      have := (cfgM T T₁).inv_mem (hUX u hu y (Subgroup.mem_sup_right hy))
      rwa [commutatorElement_inv] at this
    have h2 : ⁅y, u⁆ ∈ T₁ := by
      have e : ⁅y, u⁆ = y * (u * y⁻¹ * u⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact T₁.mul_mem hy (conj_mem_of_mem_normalizer (hP1 u hu).1 (T₁.inv_mem hy))
    have h3 : ⁅y, u⁆ ∈ normIn T₁ T := by rw [← hcfg.inf_cfgM_right]; exact ⟨h2, h1⟩
    have h4 : y * u * y⁻¹ = ⁅y, u⁆ * u := by simp only [commutatorElement_def]; group
    rw [h4]
    exact N.mul_mem (hMN _ (Cfg.normIn_le_cfgM_right T T₁ h3)) (hL₁'N u hu)
  have hT₂le : T₂ ≤ Subgroup.normalizer (N : Set G) := by
    intro y hy
    have hT₂ab := isElemAbelian_conjSubgroup hcfg.wc₁.1 c
    refine hnorm_of y (fun m hm => ?_) (fun u hu => ?_)
    · obtain ⟨l, hl, x, hx, rfl⟩ := hcfg.mem_cfgM_iff.1 hm
      have hl' : l ∈ normIn T T₂ := by rw [hLeq]; exact hl
      have e1 : ⁅y, l⁆ ∈ normIn T₂ T := hS₂.cfg.symm.comm_mem_normIn hy hl'
      rw [← hL₁₂] at e1
      have hxN := hN x hx
      have h2 := (hP2 x hx).1
      have e2 : ⁅y, x⁆ ∈ normIn T₂ T := by
        have h3 : ⁅y, x⁆ ∈ cfgM T T₂ := by
          have := (cfgM T T₂).inv_mem (h2 y (Subgroup.mem_sup_right hy))
          rwa [commutatorElement_inv] at this
        have h4 : ⁅y, x⁆ ∈ T₂ := by
          have e : ⁅y, x⁆ = y * (x * y⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
          rw [e]
          exact T₂.mul_mem hy (conj_mem_of_mem_normalizer hxN (T₂.inv_mem hy))
        rw [← hS₂.cfg.inf_cfgM_right]; exact ⟨h4, h3⟩
      rw [← hL₁₂] at e2
      have e : y * (l * x) * y⁻¹ = (⁅y, l⁆ * l) * (⁅y, x⁆ * x) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem
        (N.mul_mem (hL₁'N _ e1) (hMN _ (Cfg.normIn_le_cfgM_left T T₁ hl)))
        (N.mul_mem (hL₁'N _ e2) (hMN _ (Cfg.normIn_le_cfgM_right T T₁ hx)))
    · have huT₂ : u ∈ T₂ := normIn_le _ _ (hL₁₂ ▸ hu)
      have hcomm : y * u = u * y := elemAbelian_mul_comm hT₂ab hy huT₂
      have : y * u * y⁻¹ = u := by rw [hcomm]; group
      rw [this]
      exact hL₁'N u hu
  have hle : T ⊔ T₁ ⊔ T₂ ≤ Subgroup.normalizer (N : Set G) := sup_le (sup_le hTle hT₁le) hT₂le
  exact hKL G hnab T T₁ a hD c hc hLL hNel (fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.1 (hle hy) n).1 hn)

end Tri

end CFSG.CGT.T75M
