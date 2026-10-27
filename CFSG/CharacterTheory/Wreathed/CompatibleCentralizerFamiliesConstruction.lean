module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesSpecial

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

universe u

variable {G : Type u} [Group G]

structure IsInvariant (J J₁ : G) (lam : Subgroup.centralizer {J} →* ℂˣ) : Prop where
  two : ∀ v ∈ Subgroup.centralizer {J}, IsPGroup 2 (Subgroup.zpowers v) → extend _ lam v = 1
  conj : ∀ h ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G),
    ∀ c ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G),
      extend _ lam (h⁻¹ * c * h) = extend _ lam c

@[expose] def IsSpecialFamily (J J₁ : G) (lam : Subgroup.centralizer {J} →* ℂˣ)
    (ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ) : Prop :=
  ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≠ ⊥ → ∃ k : G,
    IsSpecial J (Subgroup.closure {J, J₁}) (Q.map (MulAut.conj k⁻¹).toMonoidHom) ∧
      ∀ g : Subgroup.centralizer (Q : Set G), ψ Q g = extend _ lam (k⁻¹ * g * k)

@[expose] def conjChar (N : Subgroup G) (lam : N →* ℂˣ) (Q : Subgroup G) (k : G)
    (hk : Subgroup.centralizer (Q.map (MulAut.conj k⁻¹).toMonoidHom : Set G) ≤ N) :
    Subgroup.centralizer (Q : Set G) →* ℂˣ where
  toFun g := extend N lam (k⁻¹ * g * k)
  map_one' := by
    rw [OneMemClass.coe_one, mul_one, inv_mul_cancel, extend_of_mem N.one_mem]
    exact map_one lam
  map_mul' g g' := by
    have hg := hk (conj_mem_centralizer_conj g.2)
    have hg' := hk (conj_mem_centralizer_conj g'.2)
    have h : k⁻¹ * ((g * g' : Subgroup.centralizer (Q : Set G)) : G) * k =
        (k⁻¹ * g * k) * (k⁻¹ * g' * k) := by
      rw [Subgroup.coe_mul]
      group
    rw [h]
    exact extend_mul hg hg'

theorem conjChar_apply (N : Subgroup G) (lam : N →* ℂˣ) (Q : Subgroup G) (k : G)
    (hk : Subgroup.centralizer (Q.map (MulAut.conj k⁻¹).toMonoidHom : Set G) ≤ N)
    (g : Subgroup.centralizer (Q : Set G)) :
    conjChar N lam Q k hk g = extend N lam (k⁻¹ * g * k) := rfl

namespace LocalConfig

variable {J J₁ η : G} (cfg : LocalConfig J J₁ η) {lam : Subgroup.centralizer {J} →* ℂˣ}
  (hlam : IsInvariant J J₁ lam)
include cfg hlam

omit cfg hlam in
theorem centralizer_le_of_isSpecial {Q : Subgroup G}
    (hsp : IsSpecial J (Subgroup.closure {J, J₁}) Q) :
    Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer {J} :=
  hsp.centralizer_le mem_left

omit hlam in
theorem exists_isSpecialFamily [Finite G] : ∃ ψ, IsSpecialFamily J J₁ lam ψ := by
  classical
  have hex : ∀ Q : Subgroup G, ∃ k : G, IsPGroup 2 Q ∧ Q ≠ ⊥ →
      IsSpecial J (Subgroup.closure {J, J₁}) (Q.map (MulAut.conj k⁻¹).toMonoidHom) := by
    intro Q
    by_cases hQ : IsPGroup 2 Q ∧ Q ≠ ⊥
    · obtain ⟨k, hk⟩ := cfg.exists_isSpecial_conj hQ.1 hQ.2
      exact ⟨k, fun _ => hk⟩
    · exact ⟨1, fun h => absurd h hQ⟩
  choose k hk using hex
  refine ⟨fun Q => if hQ : IsPGroup 2 Q ∧ Q ≠ ⊥ then
    conjChar _ lam Q (k Q) ((hk Q hQ).centralizer_le mem_left) else 1, ?_⟩
  intro Q hQ hQ1
  refine ⟨k Q, hk Q ⟨hQ, hQ1⟩, fun g => ?_⟩
  beta_reduce
  rw [dite_eq_left (show IsPGroup 2 Q ∧ Q ≠ ⊥ from ⟨hQ, hQ1⟩)]
  rfl

variable {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
  (hψ : IsSpecialFamily J J₁ lam ψ)
include hψ

theorem apply_eq [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) {l : G}
    (hsp : IsSpecial J (Subgroup.closure {J, J₁}) (Q.map (MulAut.conj l⁻¹).toMonoidHom))
    (g : Subgroup.centralizer (Q : Set G)) : ψ Q g = extend _ lam (l⁻¹ * g * l) := by
  obtain ⟨k, hk, hkψ⟩ := hψ Q hQ hQ1
  rw [hkψ]
  have hsp' : IsSpecial J (Subgroup.closure {J, J₁})
      ((Q.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj (k⁻¹ * l)⁻¹).toMonoidHom) := by
    rw [map_conj_map_conj, mul_inv_cancel_left]
    exact hsp
  have h := cfg.extend_conj_eq hlam.conj hk hsp' (conj_mem_centralizer_conj g.2)
  rw [← h]
  congr 1
  group

theorem apply_eq_of_isSpecial [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hsp : IsSpecial J (Subgroup.closure {J, J₁}) Q) (g : Subgroup.centralizer (Q : Set G)) :
    ψ Q g = extend _ lam g := by
  rw [cfg.apply_eq hlam hψ hQ hQ1 (l := 1) (by rw [map_conj_one]; exact hsp)]
  congr 1
  group

omit cfg in
theorem apply_center [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (z : Subgroup.centralizer (Q : Set G)) (hz : (z : G) ∈ Q) : ψ Q z = 1 := by
  obtain ⟨k, hk, hkψ⟩ := hψ Q hQ hQ1
  rw [hkψ]
  apply hlam.two _ (centralizer_le_of_isSpecial hk (conj_mem_centralizer_conj z.2))
  exact (conj_isPGroup hQ k).to_le (Subgroup.zpowers_le.mpr (conj_mem_conj hz))

theorem apply_conj [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) (h : G)
    (g : Subgroup.centralizer (Q : Set G))
    (g' : Subgroup.centralizer (Q.map (MulAut.conj h⁻¹).toMonoidHom : Set G))
    (hg' : (g' : G) = h⁻¹ * g * h) :
    ψ (Q.map (MulAut.conj h⁻¹).toMonoidHom) g' = ψ Q g := by
  obtain ⟨l, hl, hlψ⟩ := hψ _ (conj_isPGroup hQ h) (conj_ne_bot hQ1 h)
  rw [hlψ, hg']
  rw [map_conj_map_conj] at hl
  rw [cfg.apply_eq hlam hψ hQ hQ1 hl g]
  congr 1
  group

theorem apply_of_le_centralizer [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hQC : Q ≤ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G))
    (g : Subgroup.centralizer (Q : Set G))
    (hgC : (g : G) ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G)) :
    ψ Q g = extend _ lam g := by
  by_cases hsp : IsSpecial J (Subgroup.closure {J, J₁}) Q
  · exact cfg.apply_eq_of_isSpecial hlam hψ hQ hQ1 hsp g
  · obtain ⟨j, hj⟩ := cfg.exists_isSpecial_eta_conj hQ hQ1 hQC hsp
    rw [cfg.apply_eq hlam hψ hQ hQ1 hj g]
    exact hlam.conj _ (Subgroup.pow_mem _ cfg.eta_mem j) _ hgC

theorem apply_of_le_isSpecial [Finite G] {Q Q₁ : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hQQ₁ : Q ≤ Q₁) (hsp₁ : IsSpecial J (Subgroup.closure {J, J₁}) Q₁)
    (g : Subgroup.centralizer (Q : Set G))
    (hg : (g : G) ∈ Subgroup.centralizer (Q₁ : Set G)) : ψ Q g = extend _ lam g := by
  by_cases hsp : IsSpecial J (Subgroup.closure {J, J₁}) Q
  · exact cfg.apply_eq_of_isSpecial hlam hψ hQ hQ1 hsp g
  rcases hsp₁ with ⟨hJ₁, -⟩ | h4
  ·
    obtain ⟨y, hyZ, hy2, hyJ⟩ := exists_center_involution_ne hQ hQ1 hsp
    have hQ₁N : Q₁ ≤ Subgroup.centralizer {J} := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hJ₁.2 q hq
    have hyN : y ∈ Subgroup.centralizer {J} := hQ₁N (hQQ₁ hyZ.1)
    obtain ⟨c, hcN, hc⟩ := cfg.conj_eq₁ y hyN hy2 hyJ
    have hcJ : c⁻¹ * J * c = J := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hcN
      rw [mul_assoc, ← h, inv_mul_cancel_left]
    have hcent : ∀ z : G, z * J = J * z → z * y = y * z →
        c⁻¹ * z * c ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) := by
      intro z hzJ hzy
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with ht | ht <;> rw [ht]
      · rw [← hcJ]
        calc c⁻¹ * J * c * (c⁻¹ * z * c) = c⁻¹ * (J * z) * c := by group
          _ = c⁻¹ * (z * J) * c := by rw [hzJ]
          _ = c⁻¹ * z * c * (c⁻¹ * J * c) := by group
      · rw [← hc]
        calc c⁻¹ * y * c * (c⁻¹ * z * c) = c⁻¹ * (y * z) * c := by group
          _ = c⁻¹ * (z * y) * c := by rw [hzy]
          _ = c⁻¹ * z * c * (c⁻¹ * y * c) := by group
    have hQ'C : Q.map (MulAut.conj c⁻¹).toMonoidHom ≤
        Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      change c⁻¹ * q * c⁻¹⁻¹ ∈ _
      rw [inv_inv]
      exact hcent q (Subgroup.mem_centralizer_singleton_iff.mp (hQ₁N (hQQ₁ hq)))
        (Subgroup.mem_centralizer_iff.mp hyZ.2 q hq)
    have hgJ : (g : G) * J = J * g := (Subgroup.mem_centralizer_iff.mp hg J hJ₁.1).symm
    have hgy : (g : G) * y = y * g :=
      (Subgroup.mem_centralizer_iff.mp hg y (hQQ₁ hyZ.1)).symm
    let g' : Subgroup.centralizer (Q.map (MulAut.conj c⁻¹).toMonoidHom : Set G) :=
      ⟨c⁻¹ * g * c, conj_mem_centralizer_conj g.2⟩
    rw [← cfg.apply_conj hlam hψ hQ hQ1 c g g' rfl,
      cfg.apply_of_le_centralizer hlam hψ (conj_isPGroup hQ c) (conj_ne_bot hQ1 c) hQ'C g'
        (hcent g hgJ hgy)]
    exact extend_conj hcN (Subgroup.mem_centralizer_singleton_iff.mpr hgJ)
  ·
    exact cfg.apply_of_le_centralizer hlam hψ hQ hQ1
      (hQQ₁.trans (le_centralizer_of_le_center h4)) g (centralizer_le_of_le_center h4 hg)

theorem apply_restrict [Finite G] {Q Q₁ : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hQ₁ : IsPGroup 2 Q₁) (hQQ₁ : Q ≤ Q₁) (g : Subgroup.centralizer (Q₁ : Set G))
    (g' : Subgroup.centralizer (Q : Set G)) (hg' : (g' : G) = g) : ψ Q g' = ψ Q₁ g := by
  have hQ₁1 : Q₁ ≠ ⊥ := fun h => hQ1 (le_bot_iff.mp (h ▸ hQQ₁))
  obtain ⟨k, hk⟩ := cfg.exists_isSpecial_conj hQ₁ hQ₁1
  let g₀ : Subgroup.centralizer (Q₁.map (MulAut.conj k⁻¹).toMonoidHom : Set G) :=
    ⟨k⁻¹ * g * k, conj_mem_centralizer_conj g.2⟩
  let g₀' : Subgroup.centralizer (Q.map (MulAut.conj k⁻¹).toMonoidHom : Set G) :=
    ⟨k⁻¹ * g * k, conj_mem_centralizer_conj (by rw [← hg']; exact g'.2)⟩
  rw [← cfg.apply_conj hlam hψ hQ hQ1 k g' g₀' (by rw [hg']),
    ← cfg.apply_conj hlam hψ hQ₁ hQ₁1 k g g₀ rfl,
    cfg.apply_of_le_isSpecial hlam hψ (conj_isPGroup hQ k) (conj_ne_bot hQ1 k)
      (conj_le_conj hQQ₁ k) hk g₀' g₀.2,
    cfg.apply_eq_of_isSpecial hlam hψ (conj_isPGroup hQ₁ k) (conj_ne_bot hQ₁1 k) hk g₀]

end LocalConfig

end CFSG.Wreathed.CompatibleFamilies
