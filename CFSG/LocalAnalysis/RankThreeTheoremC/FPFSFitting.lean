module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FPFS

theorem inv_mul_aut_mem_centralizer {M : Type*} [Group M] (F : Subgroup M) [F.Normal]
    (β : MulAut M) (hβF : ∀ f ∈ F, β f = f) (g : M) :
    g⁻¹ * β g ∈ Subgroup.centralizer (F : Set M) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h1 : β (g * f * g⁻¹) = g * f * g⁻¹ := hβF _ (Subgroup.Normal.conj_mem ‹F.Normal› f hf g)
  rw [map_mul, map_mul, map_inv, hβF f hf] at h1
  have h2 : β g * f = g * f * g⁻¹ * β g := by
    calc β g * f = (β g * f * (β g)⁻¹) * β g := by group
      _ = g * f * g⁻¹ * β g := by rw [h1]
  calc f * (g⁻¹ * β g) = g⁻¹ * (g * f * g⁻¹ * β g) := by group
    _ = g⁻¹ * (β g * f) := by rw [h2]
    _ = g⁻¹ * β g * f := by group

theorem aut_eq_one_of_fixes_selfCentralizing {M : Type*} [Group M] [Finite M] (F : Subgroup M)
    [F.Normal] (hC : Subgroup.centralizer (F : Set M) ≤ F) (β : MulAut M)
    (hβF : ∀ f ∈ F, β f = f) {p : ℕ} [Fact p.Prime] (hβp : β ^ p = 1)
    (hp : ¬ p ∣ Nat.card M) : β = 1 := by
  ext g
  have hφF : g⁻¹ * β g ∈ F := hC (inv_mul_aut_mem_centralizer F β hβF g)
  have hfix : β (g⁻¹ * β g) = g⁻¹ * β g := hβF _ hφF
  have hpow : ∀ k : ℕ, (β ^ k) g = g * (g⁻¹ * β g) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, pow_succ', ← mul_assoc,
        mul_inv_cancel_left]
  have hp1 : (g⁻¹ * β g) ^ p = 1 := by
    have h := hpow p
    rw [hβp, MulAut.one_apply] at h
    exact mul_left_cancel (h.symm.trans (mul_one g).symm)
  have hord : orderOf (g⁻¹ * β g) = 1 := by
    have hd1 : orderOf (g⁻¹ * β g) ∣ p := orderOf_dvd_of_pow_eq_one hp1
    have hd2 : orderOf (g⁻¹ * β g) ∣ Nat.card M := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd1 with h | h
    · exact h
    · exact absurd (h ▸ hd2) hp
  have h1 : g⁻¹ * β g = 1 := orderOf_eq_one_iff.mp hord
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp h1).symm

def conjAut {G₀ : Type*} [Group G₀] (Γ : Subgroup G₀) (x : G₀)
    (hx : x ∈ Subgroup.normalizer (Γ : Set G₀)) : MulAut Γ where
  toFun g := ⟨x * g * x⁻¹, (Subgroup.mem_set_normalizer_iff.mp hx g).mp g.2⟩
  invFun g := ⟨x⁻¹ * g * x, (Subgroup.mem_set_normalizer_iff''.mp hx g).mp g.2⟩
  left_inv g := by ext; simp [mul_assoc]
  right_inv g := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem coe_conjAut {G₀ : Type*} [Group G₀] (Γ : Subgroup G₀) (x : G₀)
    (hx : x ∈ Subgroup.normalizer (Γ : Set G₀)) (g : Γ) :
    ((conjAut Γ x hx g : Γ) : G₀) = x * g * x⁻¹ := by
  rfl

theorem coe_conjAut_pow {G₀ : Type*} [Group G₀] (Γ : Subgroup G₀) (x : G₀)
    (hx : x ∈ Subgroup.normalizer (Γ : Set G₀)) (k : ℕ) (g : Γ) :
    ((((conjAut Γ x hx) ^ k) g : Γ) : G₀) = x ^ k * g * (x ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, coe_conjAut, ih, pow_succ']
    simp [mul_assoc]

theorem conjAut_pow_eq_one {G₀ : Type*} [Group G₀] (Γ : Subgroup G₀) (x : G₀)
    (hx : x ∈ Subgroup.normalizer (Γ : Set G₀)) {p : ℕ} (hxp : x ^ p = 1) :
    conjAut Γ x hx ^ p = 1 := by
  ext g
  rw [coe_conjAut_pow, hxp]
  simp

theorem aut_mem_of_characteristic {G : Type*} [Group G] (H : Subgroup G) [H.Characteristic]
    (β : MulAut G) {s : G} (hs : s ∈ H) : β s ∈ H :=
  (Subgroup.characteristic_iff_map_le.mp inferInstance β)
    (Subgroup.mem_map_of_mem β.toMonoidHom hs)

def fixedSubgroup {M : Type*} [Group M] (β : MulAut M) : Subgroup M where
  carrier := {g | β g = g}
  one_mem' := map_one β
  mul_mem' {a b} (ha : β a = a) (hb : β b = b) :=
    show β (a * b) = a * b by rw [map_mul, ha, hb]
  inv_mem' {a} (ha : β a = a) :=
    show β a⁻¹ = a⁻¹ by rw [map_inv, ha]

theorem pCore_le_fixedSubgroup_conjAut {G₀ : Type*} [Group G₀] {Γ : Subgroup G₀}
    (hO2 : CFSG.pCore 2 Γ = ⊥) {x : G₀} (hx : x ∈ Subgroup.normalizer (Γ : Set G₀)) {p : ℕ}
    (hpΓ : ¬ p ∣ Nat.card Γ)
    (hKL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ S : Subgroup G₀, S ≤ Γ → IsPGroup q S →
      x ∈ Subgroup.normalizer (S : Set G₀) → ∀ s ∈ S, x * s = s * x)
    {q : ℕ} (hq : q.Prime) (hqΓ : q ∣ Nat.card Γ) :
    CFSG.pCore q Γ ≤ fixedSubgroup (conjAut Γ x hx) := by
  intro s hs
  by_cases hq2 : q = 2
  · subst hq2
    rw [hO2, Subgroup.mem_bot] at hs
    subst hs
    exact map_one _
  · have hqp : q ≠ p := fun h => hpΓ (h ▸ hqΓ)
    have hSΓ : (CFSG.pCore q Γ).map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
    have hSq : IsPGroup q ((CFSG.pCore q Γ).map Γ.subtype) :=
      CFSG.pCore_isPGroup.map Γ.subtype
    have hxS : x ∈ Subgroup.normalizer (((CFSG.pCore q Γ).map Γ.subtype : Subgroup G₀) :
        Set G₀) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro h
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨conjAut Γ x hx t, aut_mem_of_characteristic _ _ ht, rfl⟩
      · rintro ⟨t, ht, hth⟩
        refine ⟨(conjAut Γ x hx).symm t, aut_mem_of_characteristic _ _ ht, ?_⟩
        show x⁻¹ * (t : G₀) * x = h
        rw [show (t : G₀) = x * h * x⁻¹ from hth]
        group
    have hcomm := hKL q hq hq2 hqp _ hSΓ hSq hxS (s : G₀) ⟨s, hs, rfl⟩
    apply Subtype.ext
    show x * (s : G₀) * x⁻¹ = s
    rw [hcomm, mul_inv_cancel_right]

theorem fitting_le_fixedSubgroup_conjAut {G₀ : Type*} [Group G₀] [Finite G₀] {Γ : Subgroup G₀}
    (hO2 : CFSG.pCore 2 Γ = ⊥) {x : G₀} (hx : x ∈ Subgroup.normalizer (Γ : Set G₀)) {p : ℕ}
    (hpΓ : ¬ p ∣ Nat.card Γ)
    (hKL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ S : Subgroup G₀, S ≤ Γ → IsPGroup q S →
      x ∈ Subgroup.normalizer (S : Set G₀) → ∀ s ∈ S, x * s = s * x) :
    CFSG.fittingSubgroup Γ ≤ fixedSubgroup (conjAut Γ x hx) := by
  rw [CFSG.fitting_eq_sup_pCore]
  refine iSup_le fun q => ?_
  have hq := Nat.mem_primeFactors.mp q.1.2
  exact pCore_le_fixedSubgroup_conjAut hO2 hx hpΓ hKL hq.1 hq.2.1

theorem centralizes_of_pCores {G₀ : Type*} [Group G₀] [Finite G₀] {Γ : Subgroup G₀}
    (hsolv : Group.IsSolvable Γ) (hO2 : CFSG.pCore 2 Γ = ⊥) {x : G₀}
    (hx : x ∈ Subgroup.normalizer (Γ : Set G₀)) {p : ℕ} [Fact p.Prime] (hxp : x ^ p = 1)
    (hpΓ : ¬ p ∣ Nat.card Γ)
    (hKL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ S : Subgroup G₀, S ≤ Γ → IsPGroup q S →
      x ∈ Subgroup.normalizer (S : Set G₀) → ∀ s ∈ S, x * s = s * x) :
    ∀ g ∈ Γ, x * g = g * x := by
  have hβ : conjAut Γ x hx = 1 :=
    aut_eq_one_of_fixes_selfCentralizing (CFSG.fittingSubgroup Γ)
      (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv) (conjAut Γ x hx)
      (fun f hf => fitting_le_fixedSubgroup_conjAut hO2 hx hpΓ hKL hf)
      (conjAut_pow_eq_one Γ x hx hxp) hpΓ
  intro g hg
  have h : conjAut Γ x hx ⟨g, hg⟩ = ⟨g, hg⟩ := by rw [hβ]; rfl
  have h' : x * g * x⁻¹ = g := congrArg Subtype.val h
  exact mul_inv_eq_iff_eq_mul.mp h'

end CFSG.LocalAnalysis.RankThreeTheoremC.FPFS
