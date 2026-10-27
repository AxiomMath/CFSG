module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Faithful
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Balance

variable {G : Type*} [Group G]

theorem gLAPPrimeCoreOf_inf_centralizer_le [Finite G] (C : Subgroup G) (e : G) :
    GLAPPrimeCoreOf 3 C ⊓ Subgroup.centralizer {e} ≤
      GLAPPrimeCoreOf 3 (C ⊓ Subgroup.centralizer {e}) := by
  refine le_gLAPPrimeCoreOf_of_normal' ?_ ?_ ?_
  · exact inf_le_inf_right _ (gLAPPrimeCoreOf_le_self' C)
  · intro g hg x hx
    refine ⟨gLAPPrimeCoreOf_conj_mem' g (Subgroup.mem_inf.1 hg).1 x hx.1, ?_⟩
    exact (Subgroup.centralizer {e}).mul_mem ((Subgroup.centralizer {e}).mul_mem
      (Subgroup.mem_inf.1 hg).2 hx.2) ((Subgroup.centralizer {e}).inv_mem (Subgroup.mem_inf.1 hg).2)
  · exact (coprime_card_gLAPPrimeCoreOf' Nat.prime_three C).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)

theorem centralizer_inv_singleton (e : G) :
    Subgroup.centralizer ({e⁻¹} : Set G) = Subgroup.centralizer {e} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * e = e * (e⁻¹ * x) * e := by group
      _ = e * (x * e⁻¹) * e := by rw [h]
      _ = e * x := by group
  · intro h
    calc x * e⁻¹ = e⁻¹ * (e * x) * e⁻¹ := by group
      _ = e⁻¹ * (x * e) * e⁻¹ := by rw [h]
      _ = e⁻¹ * x := by group

theorem gLAPPrimeCoreOf_eq_bot_of_four [Finite G] {C : Subgroup G} {α β : G} (hα : α ∈ C)
    (hβ : β ∈ C) (hαβ : α * β = β * α) (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1)
    (hinj : ∀ a b : ZMod 3, α ^ a.val * β ^ b.val = 1 → a = 0 ∧ b = 0)
    (h1 : GLAPPrimeCoreOf 3 (C ⊓ Subgroup.centralizer {α}) = ⊥)
    (h2 : GLAPPrimeCoreOf 3 (C ⊓ Subgroup.centralizer {β}) = ⊥)
    (h3 : GLAPPrimeCoreOf 3 (C ⊓ Subgroup.centralizer {α * β}) = ⊥)
    (h4 : GLAPPrimeCoreOf 3 (C ⊓ Subgroup.centralizer {α * β ^ 2}) = ⊥) :
    GLAPPrimeCoreOf 3 C = ⊥ := by
  set N := GLAPPrimeCoreOf 3 C with hN
  set φ := MonoidHom.noncommCoprod (CFSG.RankThree.CentralCover.zmodPowHom α hα3)
    (CFSG.RankThree.CentralCover.zmodPowHom β hβ3) fun x y => Commute.pow_pow hαβ _ _ with hφ
  have hφapp : ∀ a b : ZMod 3, φ (.ofAdd a, .ofAdd b) = α ^ a.val * β ^ b.val := fun _ _ => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have := hinj (Multiplicative.toAdd x) (Multiplicative.toAdd y) hxy
    exact Prod.ext (by simpa using this.1) (by simpa using this.2)
  set E := φ.range with hE
  have hcardE : Nat.card E = 3 ^ 2 := by
    rw [hE, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, Nat.card_prod]
    simp
  have hEC : E ≤ C := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact C.mul_mem (C.pow_mem hα _) (C.pow_mem hβ _)
  have hpow : ∀ m : E, m ^ 3 = 1 := by
    rintro ⟨_, ⟨⟨x, y⟩, rfl⟩⟩
    refine Subtype.ext ?_
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    have h3' : ∀ z : Multiplicative (ZMod 3), z ^ 3 = 1 := by decide
    have : (x, y) ^ 3 = 1 := Prod.ext (h3' x) (h3' y)
    rw [this, map_one]
  have hcop : ¬ 3 ∣ Nat.card N := fun h =>
    absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_gLAPPrimeCoreOf' Nat.prime_three C) h)
      (by norm_num)
  have hnorm : E ≤ Subgroup.normalizer (N : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => gLAPPrimeCoreOf_conj_mem' e (hEC he) x hx
    · intro hx
      have := gLAPPrimeCoreOf_conj_mem' e⁻¹ (C.inv_mem (hEC he)) _ hx
      simpa [mul_assoc] using this
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three E N hpow hcardE hcop hnorm
  rw [hgen]
  refine eq_bot_iff.2 (iSup₂_le fun m hm => ?_)
  obtain ⟨⟨x, y⟩, hxy⟩ := m.2
  have hm' : (m : G) = α ^ (Multiplicative.toAdd x).val * β ^ (Multiplicative.toAdd y).val := by
    rw [← hxy]
    rfl
  have hne : ¬ (Multiplicative.toAdd x = 0 ∧ Multiplicative.toAdd y = 0) := by
    rintro ⟨hx0, hy0⟩
    apply hm
    refine Subtype.ext ?_
    rw [hm', hx0, hy0]
    simp
  have hc : Commute α β := hαβ
  have e2 : β ^ 2 = β⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hβ3]
  have ea2 : α ^ 2 = α⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hα3]
  have e21 : α ^ 2 * β ^ 1 = (α * β ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, pow_one]
    calc α ^ 2 * β * (α * β ^ 2) = α ^ 2 * (β * α) * β ^ 2 := by group
      _ = α ^ 2 * (α * β) * β ^ 2 := by rw [hc.eq]
      _ = α ^ 3 * β ^ 3 := by group
      _ = 1 := by rw [hα3, hβ3, one_mul]
  have e22 : α ^ 2 * β ^ 2 = (α * β)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc α ^ 2 * β ^ 2 * (α * β) = α ^ 2 * (β ^ 2 * α) * β := by group
      _ = α ^ 2 * (α * β ^ 2) * β := by rw [(hc.pow_right 2).eq]
      _ = α ^ 3 * β ^ 3 := by group
      _ = 1 := by rw [hα3, hβ3, one_mul]
  have hbot : GLAPPrimeCoreOf 3 (C ⊓ Subgroup.centralizer {(m : G)}) = ⊥ := by
    rw [hm']
    have hi3 : (Multiplicative.toAdd x).val < 3 := ZMod.val_lt _
    have hj3 : (Multiplicative.toAdd y).val < 3 := ZMod.val_lt _
    have hne' : ¬ ((Multiplicative.toAdd x).val = 0 ∧ (Multiplicative.toAdd y).val = 0) :=
      fun h => hne ⟨(ZMod.val_eq_zero _).1 h.1, (ZMod.val_eq_zero _).1 h.2⟩
    generalize (Multiplicative.toAdd x).val = i at hi3 hne'
    generalize (Multiplicative.toAdd y).val = j at hj3 hne'
    interval_cases i <;> interval_cases j
    · exact absurd ⟨rfl, rfl⟩ hne'
    · rw [pow_zero, one_mul, pow_one]; exact h2
    · rw [pow_zero, one_mul, e2, centralizer_inv_singleton]; exact h2
    · rw [pow_one, pow_zero, mul_one]; exact h1
    · rw [pow_one, pow_one]; exact h3
    · rw [pow_one]; exact h4
    · rw [pow_zero, mul_one, ea2, centralizer_inv_singleton]; exact h1
    · rw [e21, centralizer_inv_singleton]; exact h4
    · rw [e22, centralizer_inv_singleton]; exact h3
  rw [← hbot]
  exact gLAPPrimeCoreOf_inf_centralizer_le C (m : G)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
