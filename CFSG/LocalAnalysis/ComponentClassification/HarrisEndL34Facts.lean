module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndL34Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndPermModel
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42C

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

theorem le_card_of_lieModel_psl2 {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (h : Blueprint.LieModel Z .PSL 2 p m) : 168 ≤ Nat.card Z :=
  CFSG.ComponentClassification.HarrisLit.Hin.le_card_of_lieModel_psl2_sixteen hp2 h16 h

theorem layerIn_eq_self_of_isSimpleGroup {G : Type*} [Group G] [Finite G] {F : Subgroup G}
    [IsSimpleGroup ↥F] (hne : GSThmB.layerIn F ≠ ⊥) : GSThmB.layerIn F = F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥F 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pLayer ↥F 2) with h | h
  · exact absurd (by rw [GSThmB.layerIn, h, Subgroup.map_bot]) hne
  · rw [GSThmB.layerIn, h, ← MonoidHom.range_eq_map, range_subtype]

variable {Y : Type} [Group Y]

theorem nonempty_l34Model (hY : Blueprint.LieModel Y .PSL 3 2 2) :
    Nonempty (PermAutModel Y S R) := by
  obtain ⟨θ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  obtain ⟨e, he, -⟩ := full_automorphism_action
  exact nonempty_permAutModel θ S_le_R e he

theorem nonempty_centralizer_conj_equiv {x r c : Equiv.Perm (Fin 42)} (hc : c ∈ R)
    (hx : x = c * r * c⁻¹) :
    Nonempty (↥(centralizer {x} ⊓ S) ≃* ↥(centralizer {r} ⊓ S)) :=
  nonempty_centralizer_conj_equiv' (R_le_normalizer hc) hx

theorem card_centralizer_conj_r₂R (c : R) :
    Nat.card (centralizer ({c * r₂R * c⁻¹} : Set R)) = 672 := by
  rw [← card_centralizer_r₂R, ← map_conj_centralizer (G := R) c r₂R]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem card_le_32_of_dvd {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hdvd : Nat.card P ∣ 672) : Nat.card P ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at hdvd ⊢
  have hc : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left _ (by norm_num)
  have h1 : 2 ^ k ∣ 32 := hc.dvd_of_dvd_mul_right (by simpa using hdvd)
  exact Nat.le_of_dvd (by norm_num) h1

theorem nonempty_quaternion_of_equiv_C₄ {A : Type*} [Group A] [Finite A] (ψ : A ≃* ↥C₄)
    (P : Sylow 2 A) : Nonempty (QuaternionGroup 2 ≃* ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : Function.Surjective (ψ : A →* ↥C₄) := ψ.surjective
  obtain ⟨e⟩ := nonempty_quaternion_sylow_C₄ (P.mapSurjective hs)
  exact ⟨e.trans ((MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _)).trans
    ((P : Subgroup A).equivMapOfInjective (ψ : A →* ↥C₄) ψ.injective).symm)⟩

theorem l34_outer_facts [Finite Y] (hY : Blueprint.LieModel Y .PSL 3 2 2) {τ : MulAut Y}
    (hτ2 : orderOf τ = 2) (hout : τ ∉ innAut Y) {p m : ℕ} (hp2 : p ≠ 2)
    (h16 : 16 ∣ p ^ (2 * m) - 1)
    (hK : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    (GSThmB.layerIn (fixedPoints τ) = fixedPoints τ ∧ Nat.card ↥(fixedPoints τ) = 168) ∧
    (∀ y : Y, (MulAut.conj y * τ) ^ 2 = 1 →
      ∃ g : Y, MulAut.conj g * τ * (MulAut.conj g)⁻¹ = MulAut.conj y * τ) ∧
    (∀ P : Subgroup (MulAut Y), P ≤ centralizer {τ} → IsPGroup 2 P → Nat.card P ≤ 32) ∧
    ∀ σ : MulAut Y, σ ^ 2 = 1 → σ * τ = τ * σ → σ ∉ innAut Y → σ * τ ∉ innAut Y →
      ((IsSimpleGroup ↥(fixedPoints σ) ∧ (∃ a b : ↥(fixedPoints σ), a * b ≠ b * a) ∧
            Nat.card ↥(fixedPoints σ) = 60) ∧
          ∀ P : Sylow 2 ↥(fixedPoints (σ * τ)), Nonempty (QuaternionGroup 2 ≃* ↥P)) ∨
        ((IsSimpleGroup ↥(fixedPoints (σ * τ)) ∧ (∃ a b : ↥(fixedPoints (σ * τ)), a * b ≠ b * a) ∧
            Nat.card ↥(fixedPoints (σ * τ)) = 60) ∧
          ∀ P : Sylow 2 ↥(fixedPoints σ), Nonempty (QuaternionGroup 2 ≃* ↥P)) := by
  obtain ⟨M⟩ := nonempty_l34Model hY
  set r := M.Φ τ with hr
  have hr2 : orderOf r = 2 := by rw [hr, MulEquiv.orderOf_eq]; exact hτ2
  have hrS : (r : Equiv.Perm (Fin 42)) ∉ S := fun h => hout ((M.mem_innAut_iff τ).mpr h)
  have hK168 : 168 ≤ Nat.card ↥(fixedPoints τ) :=
    (le_card_of_lieModel_psl2 hp2 h16 hK).trans (Subgroup.card_le_of_le (map_subtype_le _))
  obtain ⟨φ⟩ := M.nonempty_fixedPoints_equiv τ
  obtain ⟨c, hc, hrc⟩ : ∃ c ∈ R, (r : Equiv.Perm (Fin 42)) = c * r₂ * c⁻¹ := by
    rcases (orderOf_eq_two_iff r).mp hr2 with h | h | h | h
    · exact absurd (mem_S_of_isConj₁ h) hrS
    · exact eq_conj_of_isConj h
    · exfalso
      obtain ⟨c, hc, hrc⟩ := eq_conj_of_isConj h
      obtain ⟨ψ⟩ := nonempty_centralizer_conj_equiv hc hrc
      have h60 : Nat.card ↥(fixedPoints τ) = 60 := by
        rw [Nat.card_congr (φ.trans ψ).toEquiv]
        exact card_C₃
      omega
    · exfalso
      obtain ⟨c, hc, hrc⟩ := eq_conj_of_isConj h
      obtain ⟨ψ⟩ := nonempty_centralizer_conj_equiv hc hrc
      have h72 : Nat.card ↥(fixedPoints τ) = 72 := by
        rw [Nat.card_congr (φ.trans ψ).toEquiv]
        exact card_C₄
      omega
  obtain ⟨ψ₂⟩ := nonempty_centralizer_conj_equiv hc hrc
  have hR : ∀ g : R, (g : Equiv.Perm (Fin 42)) ∈ R := fun g => g.2
  have hrR : (r : Equiv.Perm (Fin 42)) ∈ R := r.2
  have hr2' : (r : Equiv.Perm (Fin 42)) * r = 1 := by
    have h := pow_orderOf_eq_one r
    rw [hr2, pow_two] at h
    exact congrArg Subtype.val h
  have hr1 : (r : Equiv.Perm (Fin 42)) ≠ 1 := fun h => hrS (h ▸ one_mem _)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have : IsSimpleGroup ↥(centralizer {r₂} ⊓ S) := isSimpleGroup_C₂
    have : IsSimpleGroup ↥(fixedPoints τ) := (φ.trans ψ₂).isSimpleGroup
    have hne : GSThmB.layerIn (fixedPoints τ) ≠ ⊥ := by
      intro h
      have := le_card_of_lieModel_psl2 hp2 h16 hK
      rw [h, card_bot] at this
      omega
    refine ⟨layerIn_eq_self_of_isSimpleGroup hne, ?_⟩
    rw [Nat.card_congr (φ.trans ψ₂).toEquiv]
    exact card_C₂
  ·
    intro y hy
    set s' := M.Φ (MulAut.conj y * τ) with hs'
    have hs'v : (s' : Equiv.Perm (Fin 42)) = (M.θ y : Equiv.Perm (Fin 42)) * r := by
      rw [hs', map_mul, Subgroup.coe_mul, M.conj]
    have hs'2 : (s' : Equiv.Perm (Fin 42)) * s' = 1 := by
      have h : s' ^ 2 = 1 := by rw [hs', ← map_pow, hy, map_one]
      rw [pow_two] at h
      exact congrArg Subtype.val h
    have hs'S : (s' : Equiv.Perm (Fin 42)) ∉ S := by
      intro h
      apply hout
      have h1 : MulAut.conj y * τ ∈ innAut Y := (M.mem_innAut_iff _).mpr h
      have h2 : (MulAut.conj y)⁻¹ * (MulAut.conj y * τ) ∈ innAut Y :=
        mul_mem (inv_mem ⟨y, rfl⟩) h1
      rwa [inv_mul_cancel_left] at h2
    have hs'1 : (s' : Equiv.Perm (Fin 42)) ≠ 1 := fun h => hs'S (h ▸ one_mem _)
    have hmem : (r : Equiv.Perm (Fin 42))⁻¹ * s' ∈ S := by
      rw [hs'v, ← mul_assoc]
      have := conj_mem_S (inv_mem hrR) (M.θ y).2
      rwa [inv_inv] at this
    obtain ⟨g, hg, hgr⟩ := CatFactsL4U4.conj_of_mul_mem_S hrR s'.2 hr2' hs'2 hr1 hs'1 hmem
    refine ⟨M.θ.symm ⟨g, hg⟩, M.Φ.injective (Subtype.ext ?_)⟩
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, M.conj,
      MulEquiv.apply_symm_apply, ← hr, hgr]
  ·
    intro P hP hP2
    have hc' : r = ⟨c, hc⟩ * r₂R * ⟨c, hc⟩⁻¹ := Subtype.ext hrc
    have hle : P.map M.Φ.toMonoidHom ≤ centralizer ({r} : Set R) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have h := mem_centralizer_singleton_iff.mp (hP hx)
      rw [hr, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, h]
    have hdvd : Nat.card (P.map M.Φ.toMonoidHom) ∣ 672 := by
      rw [← card_centralizer_conj_r₂R ⟨c, hc⟩, ← hc']
      exact Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective M.Φ.injective] at hdvd
    exact card_le_32_of_dvd hP2 hdvd
  ·
    intro σ hσ2 hστ hσout hστout
    set s := M.Φ σ with hsdef
    have hsR : (s : Equiv.Perm (Fin 42)) ∈ R := s.2
    have hs2 : (s : Equiv.Perm (Fin 42)) * s = 1 := by
      have h : s ^ 2 = 1 := by rw [hsdef, ← map_pow, hσ2, map_one]
      rw [pow_two] at h
      exact congrArg Subtype.val h
    have hsr : (s : Equiv.Perm (Fin 42)) * r = r * s := by
      have h : s * r = r * s := by rw [hsdef, hr, ← map_mul, ← map_mul, hστ]
      exact congrArg Subtype.val h
    have hsS : (s : Equiv.Perm (Fin 42)) ∉ S := fun h => hσout ((M.mem_innAut_iff σ).mpr h)
    have hsrS : (s : Equiv.Perm (Fin 42)) * r ∉ S := by
      intro h
      apply hστout
      rw [M.mem_innAut_iff, map_mul, Subgroup.coe_mul]
      exact h
    set s₀ := c⁻¹ * s * c with hs₀
    have hs₀R : s₀ ∈ R := mul_mem (mul_mem (inv_mem hc) hsR) hc
    have hs₀2 : s₀ * s₀ = 1 := by
      rw [hs₀, show c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c by group, hs2]
      group
    have hg₅ : r₂ = c⁻¹ * r * c := by rw [hrc]; group
    have hs₀c : s₀ * g₅ = g₅ * s₀ := by
      change s₀ * r₂ = r₂ * s₀
      rw [hg₅, hs₀, show c⁻¹ * s * c * (c⁻¹ * r * c) = c⁻¹ * (s * r) * c by group, hsr]
      group
    have hs₀S : s₀ ∉ S := fun h => hsS (by
      have := conj_mem_S hc h
      rwa [hs₀, show c * (c⁻¹ * s * c) * c⁻¹ = s by group] at this)
    have hs₀g : g₅⁻¹ * s₀ ∉ S := by
      intro h
      apply hsrS
      have h1 := conj_mem_S hc h
      have h2 : c * (g₅⁻¹ * s₀) * c⁻¹ =
          (r : Equiv.Perm (Fin 42))⁻¹ * (s : Equiv.Perm (Fin 42)) := by
        change c * (r₂⁻¹ * s₀) * c⁻¹ = _
        rw [hg₅, hs₀]
        group
      rw [h2] at h1
      have h3 := conj_mem_S hrR h1
      have hri : (r : Equiv.Perm (Fin 42))⁻¹ = r := inv_eq_of_mul_eq_one_right hr2'
      rwa [show (r : Equiv.Perm (Fin 42)) * ((r : Equiv.Perm (Fin 42))⁻¹ *
          (s : Equiv.Perm (Fin 42))) * (r : Equiv.Perm (Fin 42))⁻¹ =
          (s : Equiv.Perm (Fin 42)) * r by rw [hri, ← mul_assoc, hr2', one_mul]] at h3
    have hfix : ∀ (x : MulAut Y) (ri y : Equiv.Perm (Fin 42)), y ∈ R →
        ((M.Φ x : R) : Equiv.Perm (Fin 42)) = (c * y) * ri * (c * y)⁻¹ →
        Nonempty (↥(fixedPoints x) ≃* ↥(centralizer {ri} ⊓ S)) := by
      intro x ri y hy hx
      obtain ⟨φx⟩ := M.nonempty_fixedPoints_equiv x
      obtain ⟨ψx⟩ := nonempty_centralizer_conj_equiv (mul_mem hc hy) hx
      exact ⟨φx.trans ψx⟩
    have hsv : ∀ y, y * r₃ * y⁻¹ = s₀ ∨ y * r₄ * y⁻¹ = s₀ →
        (s : Equiv.Perm (Fin 42)) = (c * y) * (y⁻¹ * s₀ * y) * (c * y)⁻¹ := by
      intro y _
      rw [hs₀]
      group
    have hσv : ∀ (ri y : Equiv.Perm (Fin 42)), y * ri * y⁻¹ = s₀ →
        ((M.Φ σ : R) : Equiv.Perm (Fin 42)) = (c * y) * ri * (c * y)⁻¹ := by
      intro ri y hy
      rw [← hsdef, show (c * y) * ri * (c * y)⁻¹ = c * (y * ri * y⁻¹) * c⁻¹ by group, hy, hs₀]
      group
    have hστv : ∀ (ri y : Equiv.Perm (Fin 42)), y * ri * y⁻¹ = s₀ * g₅ →
        ((M.Φ (σ * τ) : R) : Equiv.Perm (Fin 42)) = (c * y) * ri * (c * y)⁻¹ := by
      intro ri y hy
      rw [map_mul, Subgroup.coe_mul, ← hsdef, ← hr,
        show (c * y) * ri * (c * y)⁻¹ = c * (y * ri * y⁻¹) * c⁻¹ by group, hy, hs₀]
      change _ = c * (c⁻¹ * ↑s * c * r₂) * c⁻¹
      rw [hg₅]
      group
    rcases conj_r₃_r₄_of_comm_g₅ hs₀R hs₀2 hs₀c hs₀S hs₀g with
      ⟨⟨y, hy, hy3⟩, ⟨y', hy', hy4⟩⟩ | ⟨⟨y, hy, hy4⟩, ⟨y', hy', hy3⟩⟩
    · left
      obtain ⟨φ₃⟩ := hfix σ r₃ y (S_le_R hy) (hσv r₃ y hy3)
      obtain ⟨φ₄⟩ := hfix (σ * τ) r₄ y' (S_le_R hy') (hστv r₄ y' hy4)
      have : IsSimpleGroup ↥(centralizer {r₃} ⊓ S) := isSimpleGroup_C₃
      obtain ⟨a, b, hab⟩ : ∃ a b : ↥(centralizer {r₃} ⊓ S), a * b ≠ b * a := exists_mul_ne_C₃
      refine ⟨⟨φ₃.isSimpleGroup, ⟨φ₃.symm a, φ₃.symm b, fun h => hab (by
        simpa using congrArg φ₃ h)⟩, ?_⟩, nonempty_quaternion_of_equiv_C₄ φ₄⟩
      rw [Nat.card_congr φ₃.toEquiv]
      exact card_C₃
    · right
      obtain ⟨φ₄⟩ := hfix σ r₄ y (S_le_R hy) (hσv r₄ y hy4)
      obtain ⟨φ₃⟩ := hfix (σ * τ) r₃ y' (S_le_R hy') (hστv r₃ y' hy3)
      have : IsSimpleGroup ↥(centralizer {r₃} ⊓ S) := isSimpleGroup_C₃
      obtain ⟨a, b, hab⟩ : ∃ a b : ↥(centralizer {r₃} ⊓ S), a * b ≠ b * a := exists_mul_ne_C₃
      refine ⟨⟨φ₃.isSimpleGroup, ⟨φ₃.symm a, φ₃.symm b, fun h => hab (by
        simpa using congrArg φ₃ h)⟩, ?_⟩, nonempty_quaternion_of_equiv_C₄ φ₄⟩
      rw [Nat.card_congr φ₃.toEquiv]
      exact card_C₃

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
