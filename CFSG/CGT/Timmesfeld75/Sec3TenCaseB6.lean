module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB5
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB2

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a : G}

namespace SecB6

variable (h : SecB6 T T₁ S a)

include h

theorem conj_eq_of_fixed [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {u : G}
    (hu : u ∈ normIn T T₁) (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u)
    (hL8 : 8 ≤ Nat.card (normIn T T₁)) {g : G} (hg : g ∈ T₁ ⊔ conjSubgroup a T₁)
    (hfix : ∀ v ∈ conjSubgroup g T₁, ∃ v' ∈ conjSubgroup g T₁,
      ∃ n ∈ cfgM T₁ (conjSubgroup a T₁), a * v * a⁻¹ = v' * n) :
    conjSubgroup g T₁ = T := by
  have hS2 := h.sec₂ h214 hInv
  have hwcU : IsWC (conjSubgroup g T₁) := h.sec.cfg.wc₁.conj g
  have hUX : conjSubgroup g T₁ ≤ T₁ ⊔ conjSubgroup a T₁ :=
    conjSubgroup_le_of_le_of_mem le_sup_left hg
  have hUp : IsPGroup 2 (conjSubgroup g T₁) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup h.sec.cfg.wc₁.1 g)
  have hNp : IsPGroup 2 (cfgM T₁ (conjSubgroup a T₁)) :=
    isPGroup_two_of_isElemAbelian hS2.cfg.isElemAbelian_cfgM
  have hV : IsPGroup 2 ↥(conjSubgroup g T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)) :=
    hUp.to_sup_of_normal_right' hNp (hUX.trans hS2.cfg.le_normalizer_cfgM)
  have haU : conjSubgroup a (conjSubgroup g T₁) = conjSubgroup g T₁ := by
    refine eq_of_conj_le_pGroup hwcU hV le_sup_left ?_
    refine conjSubgroup_le_of_forall_mem fun v hv => ?_
    obtain ⟨v', hv', n, hn, e⟩ := hfix v hv
    rw [e]
    exact (conjSubgroup g T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)).mul_mem
      (Subgroup.mem_sup_left hv') (Subgroup.mem_sup_right hn)
  have hNg : conjSubgroup g (cfgM T₁ (conjSubgroup a T₁)) = cfgM T₁ (conjSubgroup a T₁) :=
    mem_normalizer_iff_conjSubgroup_eq.1 (hS2.cfg.le_normalizer_cfgM hg)
  have hNa : conjSubgroup a (cfgM T₁ (conjSubgroup a T₁)) = cfgM T₁ (conjSubgroup a T₁) :=
    mem_normalizer_iff_conjSubgroup_eq.1 h.mem_normalizer_cfgM
  set W : Subgroup G := conjSubgroup g T₁ ⊓ cfgM T₁ (conjSubgroup a T₁) with hWdef
  have hWeq : W = conjSubgroup g (normIn T₁ T) := by
    calc W = conjSubgroup g T₁ ⊓ conjSubgroup g (cfgM T₁ (conjSubgroup a T₁)) := by
          rw [hWdef, hNg]
      _ = conjSubgroup g (T₁ ⊓ cfgM T₁ (conjSubgroup a T₁)) := (conjSubgroup_inf g _ _).symm
      _ = conjSubgroup g (normIn T₁ (conjSubgroup a T₁)) := by rw [hS2.cfg.inf_cfgM]
      _ = conjSubgroup g (normIn T₁ T) := by rw [h.normIn_conj_eq h214 hInv]
  have hWcard : Nat.card W = Nat.card (normIn T T₁) := by
    rw [hWeq, card_conjSubgroup]
    exact h.sec.card_normIn_swap
  have hWab : IsElemAbelian 2 W := isElemAbelian_of_le
    (isElemAbelian_conjSubgroup h.sec.cfg.wc₁.1 g) inf_le_left
  have hWa : ∀ w ∈ W, a * w * a⁻¹ ∈ W := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [← haU]
      exact conj_mem_conjSubgroup a hw.1
    · rw [← hNa]
      exact conj_mem_conjSubgroup a hw.2
  have hsq := card_le_sq_centralizer hWab h.haa hWa
  have hC3 : 3 ≤ Nat.card ↥(W ⊓ Subgroup.centralizer ({a} : Set G)) := by
    by_contra hlt
    have hle : Nat.card ↥(W ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 2 := by omega
    have : Nat.card ↥(W ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 ≤ 2 ^ 2 :=
      Nat.pow_le_pow_left hle 2
    omega
  obtain ⟨w, hwV, hw1, hwT⟩ := h.exists_ne_one_centralizes h214 hInv hu hvals
    (V := W ⊓ Subgroup.centralizer ({a} : Set G))
    (fun w hw => hw.1.2)
    (fun w hw => by
      have := Subgroup.mem_centralizer_singleton_iff.1 hw.2
      calc a * w * a⁻¹ = (w * a) * a⁻¹ := by rw [← this]
        _ = w := by group)
    hC3
  have hTN : T ≤ Subgroup.normalizer (conjSubgroup g T₁ : Set G) := fun t ht =>
    hwcU.centralizer_le_normalizer hwV.1.1 hw1
      (Subgroup.mem_centralizer_singleton_iff.2 (hwT t ht))
  obtain ⟨x₀, -, hx₀⟩ := h.sec.conj
  have hconj : ∃ k : G, T = conjSubgroup k (conjSubgroup g T₁) :=
    ⟨(g * x₀)⁻¹, by
      rw [hx₀, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
        show (g * x₀)⁻¹ * g * x₀ = 1 by group, conjSubgroup_one]⟩
  exact (eq_of_le_normalizer_of_isWC hwcU hconj hTN).symm
theorem false_of_inputs [Finite G] [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput) (hnab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : Odd n) (hn3 : 3 < n) (hD : Sec3Dih T T₁ n) {u : G}
    (hu : u ∈ normIn T T₁) (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u)
    (hL8 : 8 ≤ Nat.card (normIn T T₁)) (hnc : ∃ l ∈ normIn T T₁, a * l ≠ l * a) : False := by
  have hS2 := h.sec₂ h214 hInv
  have hNorm := hS2.normal_cfgM_subgroupOf
  have haX := h.mem_normalizer_sup
  have haN := h.mem_normalizer_cfgM
  have hpair := Sec3.sylowInner_map h214 hSz hnab hS2
  have hT₁X : T₁ ≤ T₁ ⊔ conjSubgroup a T₁ := le_sup_left
  obtain ⟨g, hg, hgfix⟩ := hpair.exists_fixed_conj_of_involution hT₁X h.haa haX haN
  have hgT : conjSubgroup g T₁ = T := h.conj_eq_of_fixed h214 hInv hu hvals hL8 hg hgfix
  have hTX : T ≤ T₁ ⊔ conjSubgroup a T₁ := hgT ▸ conjSubgroup_le_of_le_of_mem hT₁X hg
  have hpairT : SylowInner (↥(T₁ ⊔ conjSubgroup a T₁) ⧸
      (cfgM T₁ (conjSubgroup a T₁)).subgroupOf (T₁ ⊔ conjSubgroup a T₁))
      ((T.subgroupOf (T₁ ⊔ conjSubgroup a T₁)).map
        (QuotientGroup.mk' ((cfgM T₁ (conjSubgroup a T₁)).subgroupOf
          (T₁ ⊔ conjSubgroup a T₁)))) := by
    have := hpair.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥(T₁ ⊔ conjSubgroup a T₁)))
    rw [conjSubgroup_map_subgroupOf] at this
    rwa [← hgT]
  obtain ⟨t, htT, htN, hb⟩ := hpairT.exists_inner_of_unique_fixed (cfgM_le_sup _ _) hTX h.haa haX
    haN h.haN fun g' hg' hfix' => by
      have hgg : g' * g ∈ T₁ ⊔ conjSubgroup a T₁ := (T₁ ⊔ conjSubgroup a T₁).mul_mem hg' hg
      have e : conjSubgroup g' T = conjSubgroup (g' * g) T₁ := by
        rw [← hgT, conjSubgroup_conjSubgroup]
      rw [e] at hfix' ⊢
      exact h.conj_eq_of_fixed h214 hInv hu hvals hL8 hgg hfix'
  have hti : t⁻¹ = t := elemAbelian_inv h.sec.cfg.wc.1 htT
  have hκT₁ : conjSubgroup (t⁻¹ * a) T₁ = T₁ := by
    have hV₀ : IsPGroup 2 ↥(T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)) :=
      (isPGroup_two_of_isElemAbelian h.sec.cfg.wc₁.1).to_sup_of_normal_right'
        (isPGroup_two_of_isElemAbelian hS2.cfg.isElemAbelian_cfgM)
        (le_sup_left.trans hS2.cfg.le_normalizer_cfgM)
    refine eq_of_conj_le_pGroup h.sec.cfg.wc₁ hV₀ le_sup_left ?_
    refine conjSubgroup_le_of_forall_mem fun v hv => ?_
    have h1 := hb v (hT₁X hv)
    have e : (t⁻¹ * a) * v * (t⁻¹ * a)⁻¹ =
        ((t⁻¹ * a) * v * (t⁻¹ * a)⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact (T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)).mul_mem (Subgroup.mem_sup_right h1)
      (Subgroup.mem_sup_left hv)
  have hκN : t⁻¹ * a ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem
      (Subgroup.le_normalizer htT)) h.haN
  have hcomm_κ : ∀ t' ∈ T, ⁅t', t⁻¹ * a⁆ = ⁅t', a⁆ := by
    intro t' ht'
    have htt' : t' * t⁻¹ = t⁻¹ * t' := by
      rw [hti]
      exact elemAbelian_mul_comm h.sec.cfg.wc.1 ht' htT
    have hL : ⁅t', a⁆ ∈ normIn T T₁ := by
      rcases hvals t' ht' with h0 | h0
      · rw [h0]
        exact (normIn T T₁).one_mem
      · rw [h0]
        exact hu
    have hct : ⁅t', a⁆ * t = t * ⁅t', a⁆ :=
      elemAbelian_mul_comm h.sec.cfg.wc.1 (normIn_le T T₁ hL) htT
    calc ⁅t', t⁻¹ * a⁆ = (t' * t⁻¹) * a * t'⁻¹ * a⁻¹ * t := by
          simp only [commutatorElement_def]
          group
      _ = (t⁻¹ * t') * a * t'⁻¹ * a⁻¹ * t := by rw [htt']
      _ = t⁻¹ * (⁅t', a⁆ * t) := by
          simp only [commutatorElement_def]
          group
      _ = t⁻¹ * (t * ⁅t', a⁆) := by rw [hct]
      _ = ⁅t', a⁆ := by group
  have hvalsκ : ∀ t' ∈ T, ⁅t', t⁻¹ * a⁆ = 1 ∨ ⁅t', t⁻¹ * a⁆ = u := fun t' ht' => by
    rw [hcomm_κ t' ht']
    exact hvals t' ht'
  have hLκ : ∀ t' ∈ T, ⁅t', t⁻¹ * a⁆ ∈ normIn T T₁ := fun t' ht' => by
    rw [hcomm_κ t' ht']
    rcases hvals t' ht' with h0 | h0
    · rw [h0]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact hu
  have hncκ : ∃ l ∈ normIn T T₁, (t⁻¹ * a) * l ≠ l * (t⁻¹ * a) := by
    obtain ⟨l, hl, hne⟩ := hnc
    refine ⟨l, hl, fun heq => hne ?_⟩
    have htl : t * l = l * t := elemAbelian_mul_comm h.sec.cfg.wc.1 htT (normIn_le T T₁ hl)
    calc a * l = t * ((t⁻¹ * a) * l) := by group
      _ = t * (l * (t⁻¹ * a)) := by rw [heq]
      _ = (t * l) * (t⁻¹ * a) := by group
      _ = (l * t) * (t⁻¹ * a) := by rw [htl]
      _ = l * a := by group
  exact Sec3.false_of_conj_eq h.sec hn hn3 hD hκN hκT₁ hLκ hvalsκ hncκ

end SecB6

end CFSG.CGT.Timmesfeld75
