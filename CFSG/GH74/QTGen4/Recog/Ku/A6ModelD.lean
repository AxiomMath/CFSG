module

public import CFSG.Quasithin.Recognition.HSTypeS6
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.GH74.QTGen4.Ku.A6

open CFSG.Quasithin.HSType

variable {G : Type} [Group G]

structure CoordHyp (E : Subgroup G) (ω : G → G → ZMod 2) (Φ : SpV → G) : Prop where
  mem : ∀ v, Φ v ∈ E
  inj : Function.Injective Φ
  add : ∀ v w, Φ (v + w) = Φ v * Φ w
  surj : ∀ x ∈ E, ∃ v, Φ v = x
  form : ∀ u v, ω (Φ u) (Φ v) = spForm u v
  inv : ∀ n ∈ Subgroup.normalizer (E : Set G), ∀ x ∈ E, ∀ y ∈ E,
    ω (n * x * n⁻¹) (n * y * n⁻¹) = ω x y
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  cent : Subgroup.centralizer (E : Set G) ≤ E

namespace CoordHyp

variable {E : Subgroup G} {ω : G → G → ZMod 2} {Φ : SpV → G}

theorem perm_eq_of_conj (hΦ : CoordHyp E ω Φ) {σ τ : Equiv.Perm (Fin 6)}
    (h : ∀ v, Φ (actS6 σ v) = Φ (actS6 τ v)) : σ = τ :=
  actS6_injective fun v => hΦ.inj (h v)

theorem exists_perm_conj (hΦ : CoordHyp E ω Φ) {n : G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ v, n * Φ v * n⁻¹ = Φ (actS6 σ v) := by
  have hmem : ∀ v, n * Φ v * n⁻¹ ∈ E := fun v =>
    (Subgroup.mem_normalizer_iff.mp hn (Φ v)).mp (hΦ.mem v)
  choose T hT using fun v => hΦ.surj _ (hmem v)
  have hadd : ∀ v w, T (v + w) = T v + T w := by
    intro v w
    apply hΦ.inj
    simp only [hT, hΦ.add]
    group
  have hform : ∀ u v, spForm (T u) (T v) = spForm u v := by
    intro u v
    calc spForm (T u) (T v) = ω (Φ (T u)) (Φ (T v)) := (hΦ.form _ _).symm
      _ = ω (n * Φ u * n⁻¹) (n * Φ v * n⁻¹) := by rw [hT, hT]
      _ = ω (Φ u) (Φ v) := hΦ.inv n hn _ (hΦ.mem u) _ (hΦ.mem v)
      _ = spForm u v := hΦ.form u v
  obtain ⟨σ, hσ⟩ := exists_actS6_of_isometry T hadd hform
  exact ⟨σ, fun v => by rw [← hT v, hσ v]⟩

noncomputable def permOf (hΦ : CoordHyp E ω Φ) (n : ↥(Subgroup.normalizer (E : Set G))) :
    Equiv.Perm (Fin 6) :=
  Classical.choose (hΦ.exists_perm_conj n.2)

theorem permOf_spec (hΦ : CoordHyp E ω Φ) (n : ↥(Subgroup.normalizer (E : Set G))) (v : SpV) :
    (n : G) * Φ v * (n : G)⁻¹ = Φ (actS6 (permOf hΦ n) v) :=
  Classical.choose_spec (hΦ.exists_perm_conj n.2) v

theorem permOf_mul (hΦ : CoordHyp E ω Φ) (n m : ↥(Subgroup.normalizer (E : Set G))) :
    permOf hΦ (n * m) = permOf hΦ n * permOf hΦ m := by
  apply perm_eq_of_conj hΦ
  intro v
  rw [actS6_mul, ← permOf_spec hΦ n, ← permOf_spec hΦ m, ← permOf_spec hΦ (n * m)]
  simp only [Subgroup.coe_mul]
  group

noncomputable def permHom (hΦ : CoordHyp E ω Φ) :
    ↥(Subgroup.normalizer (E : Set G)) →* Equiv.Perm (Fin 6) :=
  MonoidHom.mk' (permOf hΦ) (permOf_mul hΦ)

theorem permHom_eq_one_iff (hΦ : CoordHyp E ω Φ) (n : ↥(Subgroup.normalizer (E : Set G))) :
    permHom hΦ n = 1 ↔ (n : G) ∈ E := by
  constructor
  · intro h
    have h1 : permOf hΦ n = 1 := h
    apply hΦ.cent
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := hΦ.surj x hx
    have hv := permOf_spec hΦ n v
    rw [h1, actS6_one] at hv
    calc Φ v * (n : G) = (n : G) * Φ v * (n : G)⁻¹ * (n : G) := by rw [hv]
      _ = (n : G) * Φ v := by group
  · intro hn
    have hcomm : ∀ v, (n : G) * Φ v * (n : G)⁻¹ = Φ v := by
      intro v
      rw [hΦ.comm _ hn _ (hΦ.mem v)]
      group
    show permOf hΦ n = 1
    apply actS6_injective
    intro v
    rw [actS6_one]
    apply hΦ.inj
    rw [← permOf_spec hΦ n v, hcomm v]

theorem ker_permHom (hΦ : CoordHyp E ω Φ) :
    (permHom hΦ).ker = E.subgroupOf (Subgroup.normalizer (E : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, permHom_eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_range_permHom (hΦ : CoordHyp E ω Φ)
    (hN : Nat.card ↥(Subgroup.normalizer (E : Set G)) = 5760) (hE : Nat.card E = 16) :
    Nat.card (permHom hΦ).range = 360 := by
  have hEN : E ≤ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (permHom hΦ).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (permHom hΦ)).toEquiv,
    ker_permHom hΦ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hE, hN] at h1
  omega

end CoordHyp

theorem eq_alternatingGroup_of_card {R : Subgroup (Equiv.Perm (Fin 6))}
    (hR : Nat.card R = 360) : R = alternatingGroup (Fin 6) := by
  have hf : (6 : ℕ).factorial = 720 := rfl
  have hidx : R.index = 2 := by
    have h := R.card_mul_index
    have h6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_perm, Nat.card_fin, hf]
    rw [h6, hR] at h
    omega
  have : R.Normal := Subgroup.normal_of_index_eq_two hidx
  have hsq : ∀ x : Equiv.Perm (Fin 6), x ^ 2 ∈ R := by
    intro x
    have h : (x : Equiv.Perm (Fin 6) ⧸ R) ^ Nat.card (Equiv.Perm (Fin 6) ⧸ R) = 1 :=
      pow_card_eq_one'
    have hcard2 : Nat.card (Equiv.Perm (Fin 6) ⧸ R) = 2 := hidx
    rw [hcard2] at h
    have hx2 : ((x ^ 2 : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 6) ⧸ R) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact h
    exact (QuotientGroup.eq_one_iff (x ^ 2)).mp hx2
  have hcyc : ∀ c : Equiv.Perm (Fin 6), c.IsThreeCycle → c ∈ R := by
    intro c hc
    have h3 : c ^ 3 = 1 := by
      have := pow_orderOf_eq_one c
      rwa [Equiv.Perm.IsThreeCycle.orderOf hc] at this
    have h4 : (c ^ 2) ^ 2 = c := by
      calc (c ^ 2) ^ 2 = c ^ 3 * c := by group
        _ = c := by rw [h3, one_mul]
    rw [← h4]
    exact hsq (c ^ 2)
  have hle : alternatingGroup (Fin 6) ≤ R := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro c hc
    exact hcyc c hc
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  exact (Subgroup.eq_of_le_of_card_ge hle (hR.trans hA.symm).le).symm

namespace CoordHyp

variable {E : Subgroup G} {ω : G → G → ZMod 2} {Φ : SpV → G}

theorem range_permHom (hΦ : CoordHyp E ω Φ)
    (hN : Nat.card ↥(Subgroup.normalizer (E : Set G)) = 5760) (hE : Nat.card E = 16) :
    (permHom hΦ).range = alternatingGroup (Fin 6) :=
  eq_alternatingGroup_of_card (card_range_permHom hΦ hN hE)

theorem exists_perm_model (hΦ : CoordHyp E ω Φ)
    (hN : Nat.card ↥(Subgroup.normalizer (E : Set G)) = 5760) (hE : Nat.card E = 16) :
    ∃ π : ↥(Subgroup.normalizer (E : Set G)) →* Equiv.Perm (Fin 6),
      (∀ n, π n ∈ alternatingGroup (Fin 6)) ∧
      (∀ σ ∈ alternatingGroup (Fin 6), ∃ n, π n = σ) ∧
      (∀ n, π n = 1 ↔ (n : G) ∈ E) ∧
      (∀ (n : ↥(Subgroup.normalizer (E : Set G))) (v : SpV),
        (n : G) * Φ v * (n : G)⁻¹ = Φ (actS6 (π n) v)) := by
  have hR := range_permHom hΦ hN hE
  refine ⟨permHom hΦ, fun n => ?_, fun σ hσ => ?_, fun n => permHom_eq_one_iff hΦ n,
    fun n v => permOf_spec hΦ n v⟩
  · rw [← hR]
    exact MonoidHom.mem_range.mpr ⟨n, rfl⟩
  · rw [← hR] at hσ
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hσ
    exact ⟨n, hn⟩

end CoordHyp

end CFSG.GH74.QTGen4.Ku.A6

end
