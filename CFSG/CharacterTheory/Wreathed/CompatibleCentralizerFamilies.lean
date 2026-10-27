module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesExtension
public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionExistence
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesConfig

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure
open CFSG.TwoRankLowerBound.Helpers
open scoped Classical

universe u

variable {G : Type u} [Group G]

section Assembly

variable [Finite G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem exists_center_mul_oddCore (hn : 2 ≤ n)
    (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    ∃ z ∈ modelCenter S e, ∃ y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)),
      (c : G) = z * y := by
  obtain ⟨d, hd⟩ := (sylow_and_base_four_group_centralizer_structure n hn S e).centralizer_direct
  refine ⟨((d.symm c).1 : G), (d.symm c).1.2, (d.symm c).2, ?_⟩
  rw [← hd, MulEquiv.apply_symm_apply]

theorem compatible_of_isSpecialFamily (hn : 2 ≤ n) {J J₁ η : G}
    (cfg : LocalConfig J J₁ η) {lam : Subgroup.centralizer {J} →* ℂˣ}
    (hlam : IsInvariant J J₁ lam)
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : IsSpecialFamily J J₁ lam ψ) (hsp : IsSpecial J (Subgroup.closure {J, J₁}) S)
    (hSN : (S : Subgroup G) ≤ Subgroup.centralizer {J})
    (χ : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) → ℂ)
    (hlamE : ∀ (v : Subgroup.centralizer {J})
      (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        (v : G) = y → (lam v : ℂ) = χ y)
    (hlamS : ∀ v : Subgroup.centralizer {J}, (v : G) ∈ (S : Subgroup G) → lam v = 1)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        z ∈ modelCenter S e → (c : G) = z * y → θt c = χ y) :
    CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := by
  refine ⟨fun Q hQ hQ1 z hz => LocalConfig.apply_center hlam hψ hQ hQ1 z hz,
    fun Q hQ hQ1 h g g' hg' => cfg.apply_conj hlam hψ hQ hQ1 h g g' hg',
    fun Q Q₁ hQ hQ1 hQ₁ hQQ₁ g g' hg' => cfg.apply_restrict hlam hψ hQ hQ1 hQ₁ hQQ₁ g g' hg',
    ?_⟩
  intro g
  have hS1 : (S : Subgroup G) ≠ ⊥ := by
    intro h
    have := hsp.mem (Subgroup.subset_closure (Set.mem_insert _ _))
    rw [h, Subgroup.mem_bot] at this
    exact cfg.ne_one this
  rw [cfg.apply_eq_of_isSpecial hlam hψ S.isPGroup' hS1 hsp g]
  obtain ⟨z, hz, y, hzy⟩ := exists_center_mul_oddCore S e hn g
  rw [hθt g z y hz hzy]
  have hzS : z ∈ (S : Subgroup G) := modelCenter_le_sylow S e hz
  have hJS : J ∈ (S : Subgroup G) := hsp.mem (Subgroup.subset_closure (Set.mem_insert _ _))
  have hyN : (y : G) ∈ Subgroup.centralizer {J} :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hJS) (ambientOddCore_le _ y.2)
  rw [hzy, extend_mul (hSN hzS) hyN, extend_of_mem (hSN hzS), hlamS _ hzS, one_mul,
    extend_of_mem hyN]
  exact hlamE _ y rfl

end Assembly

theorem compatible_centralizer_families_and_invariant_local_extensions [Fintype G]
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eb : FiniteIrreducibleCharacterBasis
      (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)))) :
    let s := wreathModelHom S e (Original.s (2 ^ n))
    let t := wreathModelHom S e (Original.t (2 ^ n))
    let U := Subgroup.closure {s, t}
    let a := s * t
    let x := a ^ (2 ^ n / 2)
    let x₂ := s ^ (2 ^ n / 2)
    let T := Subgroup.closure {x, x₂}
    let N := Subgroup.centralizer {x}
    let C := Subgroup.centralizer (T : Set G)
    let Z := Subgroup.zpowers a
    let E := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))
    let special : Subgroup G → Prop := fun Q₀ =>
      (x ∈ Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G) ∧
        ∀ y ∈ Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G), orderOf y = 2 → y = x) ∨
      T ≤ Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G)
    (∃ η : G, ∃ hη : η ∈ Subgroup.normalizer (U : Set G),
      orderOf (U.normalizerMonoidHom ⟨η, hη⟩) = 3) ∧
    ∀ (η : G) (hη : η ∈ Subgroup.normalizer (U : Set G)),
      orderOf (U.normalizerMonoidHom ⟨η, hη⟩) = 3 → ∀ θ : eb.index,
      let χ := (eb.representation θ).character
      let IsExtension : (N →* ℂˣ) → Prop := fun lam =>
        (∀ (v : N) (y : E), (v : G) = y → (lam v : ℂ) = χ y) ∧
        (∀ v : N, (v : G) ∈ (S : Subgroup G) → lam v = 1) ∧
        ∀ c c' : N, (c : G) ∈ C → (c' : G) = η⁻¹ * c * η → lam c' = lam c
      (∃ θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ,
        ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G) (y : E),
          z ∈ Z → (c : G) = z * y → θt c = χ y) ∧
      ∀ θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ,
        (∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G) (y : E),
          z ∈ Z → (c : G) = z * y → θt c = χ y) →
        ((∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ) ↔
          ∃ lam, IsExtension lam) ∧
        ((∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ) →
          χ 1 = 1 ∧ Module.finrank ℂ (eb.representation θ).vector = 1) ∧
        ∀ lam : N →* ℂˣ, IsExtension lam →
          (∀ Q : Subgroup G, IsPGroup 2 Q → Q ≠ ⊥ →
            ∃ k : G, special (Q.map (MulAut.conj k⁻¹).toMonoidHom)) ∧
          (∀ Q₀ : Subgroup G, special Q₀ → Subgroup.centralizer (Q₀ : Set G) ≤ N) ∧
          (∀ (Q : Subgroup G) (k l g : G), IsPGroup 2 Q → Q ≠ ⊥ →
            special (Q.map (MulAut.conj k⁻¹).toMonoidHom) →
            special (Q.map (MulAut.conj l⁻¹).toMonoidHom) →
            g ∈ Subgroup.centralizer (Q : Set G) → ∀ v v' : N,
              (v : G) = k⁻¹ * g * k → (v' : G) = l⁻¹ * g * l → lam v = lam v') ∧
          (∃ ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ,
            ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≠ ⊥ → ∃ k : G,
              special (Q.map (MulAut.conj k⁻¹).toMonoidHom) ∧
              ∀ (g : Subgroup.centralizer (Q : Set G)) (v : N),
                (v : G) = k⁻¹ * g * k → ψ Q g = lam v) ∧
          ∀ ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ,
            (∀ Q : Subgroup G, IsPGroup 2 Q → Q ≠ ⊥ → ∃ k : G,
              special (Q.map (MulAut.conj k⁻¹).toMonoidHom) ∧
              ∀ (g : Subgroup.centralizer (Q : Set G)) (v : N),
                (v : G) = k⁻¹ * g * k → ψ Q g = lam v) →
            CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := by
  intro s t U a x x₂ T N C Z E special
  have hU : U = modelBase S e := (modelBase_eq_actual_generated S e).symm
  have ha : a = wreathModelHom S e (Original.a (2 ^ n)) := by
    rw [Original.a, map_mul]
  have hx : x = wreathModelHom S e (Original.x (2 ^ n)) := by
    change a ^ (2 ^ n / 2) = _
    rw [ha, Original.x, map_pow]
  have hx₂ : x₂ = wreathModelHom S e (Original.x2 (2 ^ n)) := by
    change s ^ (2 ^ n / 2) = _
    rw [Original.x2, map_pow]
  clear_value x x₂ a U
  subst hU ha hx hx₂
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, υ, g, hA⟩ := AdaptedBaseFusion.exists_isAdaptedBase S e hnonab hn
    exact ⟨g, hA.mem_normalizer, hA.orderOf_conj⟩
  intro η hη hord θ χ IsExtension
  have hSN : (S : Subgroup G) ≤ N := sylow_le_centralizer_x S e hn
  have hZ : ∀ z, z ∈ Z → z ∈ modelCenter S e := by
    intro z hz
    rw [modelCenter_eq_zpowers]
    exact hz
  have cfg := localConfig S e hnonab hn hη hord
  have hEC : E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := ambientOddCore_le _
  have hsp := isSpecial_sylow S e hn
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨d, hd⟩ :=
      (sylow_and_base_four_group_centralizer_structure n hn S e).centralizer_direct
    refine ⟨fun c => χ (d.symm c).2, ?_⟩
    intro c z y hz hc
    have hdc : d.symm c = (⟨z, hZ z hz⟩, y) := by
      apply d.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hd]
      exact hc
    change χ (d.symm c).2 = χ y
    rw [hdc]
  intro θt hθt
  have hcomp : ∀ lam : N →* ℂˣ, IsExtension lam →
      ∀ ψ, IsSpecialFamily (wreathModelHom S e (Original.x (2 ^ n)))
        (wreathModelHom S e (Original.x2 (2 ^ n))) lam ψ →
        CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := by
    intro lam hext ψ hψ
    obtain ⟨h1, h2, h3⟩ := hext
    have hlam := isInvariant S e hn hη hord h2 h3
    exact compatible_of_isSpecialFamily S e hn cfg hlam hψ hsp hSN χ h1 h2 θt
      (fun c z y hz hc => hθt c z y (by rw [modelCenter_eq_zpowers] at hz; exact hz) hc)
  have hab : (∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ) →
      ∃ lam, IsExtension lam := by
    rintro ⟨ψ, hψ⟩
    exact exists_extension_of_family hnonab S e hn hη hEC χ θt
      (fun c y hcy => hθt c 1 y (Subgroup.one_mem _) (by rw [one_mul]; exact hcy)) hψ
  refine ⟨⟨hab, fun ⟨lam, hlam⟩ => ?_⟩, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := cfg.exists_isSpecialFamily (lam := lam)
    exact ⟨ψ, hcomp lam hlam ψ hψ⟩
  ·
    intro hfam
    obtain ⟨lam, h1, -, -⟩ := hab hfam
    have h := h1 1 1 rfl
    rw [map_one, Units.val_one] at h
    refine ⟨h.symm, ?_⟩
    have hc := Representation.char_one (eb.representation θ).representation
    have h' : ((Module.finrank ℂ (eb.representation θ).vector : ℕ) : ℂ) = 1 := by
      rw [← hc]
      exact h.symm
    exact_mod_cast h'
  ·
    intro lam hext
    obtain ⟨h1, h2, h3⟩ := hext
    have hlam := isInvariant S e hn hη hord h2 h3
    refine ⟨fun Q hQ hQ1 => cfg.exists_isSpecial_conj hQ hQ1,
      fun Q₀ hQ₀ => LocalConfig.centralizer_le_of_isSpecial hQ₀, ?_, ?_, ?_⟩
    ·
      intro Q k l g hQ hQ1 hk hl hg v v' hv hv'
      have hsp' : IsSpecial (wreathModelHom S e (Original.x (2 ^ n))) T
          ((Q.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj (k⁻¹ * l)⁻¹).toMonoidHom) := by
        rw [map_conj_map_conj, mul_inv_cancel_left]
        exact hl
      have h := cfg.extend_conj_eq hlam.conj hk hsp' (conj_mem_centralizer_conj hg)
      rw [show (k⁻¹ * l)⁻¹ * (k⁻¹ * g * k) * (k⁻¹ * l) = l⁻¹ * g * l by group, ← hv', ← hv,
        extend_coe, extend_coe] at h
      exact h.symm
    ·
      obtain ⟨ψ, hψ⟩ := cfg.exists_isSpecialFamily (lam := lam)
      refine ⟨ψ, fun Q hQ hQ1 => ?_⟩
      obtain ⟨k, hk, hkψ⟩ := hψ Q hQ hQ1
      refine ⟨k, hk, fun g v hv => ?_⟩
      rw [hkψ, ← hv, extend_coe]
    ·
      intro ψ hψ
      apply hcomp lam ⟨h1, h2, h3⟩ ψ
      intro Q hQ hQ1
      obtain ⟨k, hk, hkψ⟩ := hψ Q hQ hQ1
      refine ⟨k, hk, fun g => ?_⟩
      have hmem : k⁻¹ * g * k ∈ N :=
        LocalConfig.centralizer_le_of_isSpecial hk (conj_mem_centralizer_conj g.2)
      rw [hkψ g ⟨_, hmem⟩ rfl, extend_of_mem hmem]

end CFSG.Wreathed.CompatibleFamilies
