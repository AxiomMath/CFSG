module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.PGroup

public section

open scoped commutatorElement Pointwise

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.BlocksAux

section Basic
variable {X : Type*} [Group X]

theorem odd_trivial {z : X} (hz : Odd (orderOf z)) {P Q : Subgroup X} (hP : IsPGroup 2 ↥P)
    (hQP : Q ≤ P) (hzQ : ∀ q ∈ Q, z * q * z⁻¹ = q)
    (hzPQ : ∀ x ∈ P, ⁅z, x⁆ ∈ Q) : ∀ x ∈ P, z * x * z⁻¹ = x := by
  intro x hx
  have hcQ : ⁅z, x⁆ ∈ Q := hzPQ x hx
  have hzx : z * x * z⁻¹ = ⁅z, x⁆ * x := by
    simp only [commutatorElement_def]; group
  have hzc : z * ⁅z, x⁆ * z⁻¹ = ⁅z, x⁆ := hzQ _ hcQ
  have key : ∀ n : ℕ, z ^ n * x * (z ^ n)⁻¹ = ⁅z, x⁆ ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : z ^ (n + 1) * x * (z ^ (n + 1))⁻¹ = z * (z ^ n * x * (z ^ n)⁻¹) * z⁻¹ := by
        rw [pow_succ']; group
      rw [h1, ih]
      have h2 : z * (⁅z, x⁆ ^ n * x) * z⁻¹ = (z * ⁅z, x⁆ * z⁻¹) ^ n * (z * x * z⁻¹) := by
        have := (MulAut.conj z).map_mul (⁅z, x⁆ ^ n) x
        have h3 := map_pow (MulAut.conj z) ⁅z, x⁆ n
        simpa [MulAut.conj_apply, h3] using this
      rw [h2, hzc, hzx, pow_succ, mul_assoc]
  have hm : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have hc1 : ⁅z, x⁆ ^ orderOf z = 1 := by
    have := key (orderOf z)
    rw [hm] at this
    simp only [one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.1 this.symm)
  have hcP : ⁅z, x⁆ ∈ P := hQP hcQ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨⁅z, x⁆, hcP⟩
  have hord : orderOf ⁅z, x⁆ = 2 ^ k := by
    rw [← hk, Subgroup.orderOf_mk]
  have hdvd : orderOf ⁅z, x⁆ ∣ orderOf z := orderOf_dvd_of_pow_eq_one hc1
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf ⁅z, x⁆ := by
      rw [hord]; exact dvd_pow_self 2 hne
    have := (h2.trans hdvd)
    exact (Nat.not_even_iff_odd.2 hz) (even_iff_two_dvd.2 this)
  have hone : ⁅z, x⁆ = 1 := by
    rw [← orderOf_eq_one_iff, hord, hk0, pow_zero]
  rw [hzx, hone, one_mul]

theorem eq_one_of_odd_of_mem {P : Subgroup X} (hP : IsPGroup 2 ↥P) {z : X} (hz : z ∈ P)
    (hodd : Odd (orderOf z)) : z = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨z, hz⟩
  have hord : orderOf z = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf z := by rw [hord]; exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [← orderOf_eq_one_iff, hord, hk0, pow_zero]

theorem comm_eq_bot_of_perfect {K A : Subgroup X} (hK : ⁅K, K⁆ = K) (h : ⁅⁅A, K⁆, K⁆ = ⊥) :
    ⁅A, K⁆ = ⊥ := by
  have h1 : ⁅⁅K, A⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm K A]; exact h
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := A) h1 h
  rw [hK] at h3
  rw [Subgroup.commutator_comm A K]
  exact h3

theorem commutatorElement_mul_left (a b c : X) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]; group


theorem le_normalizer_commutator {G A B : Subgroup X} (hA : G ≤ Subgroup.normalizer (A : Set X))
    (hB : G ≤ Subgroup.normalizer (B : Set X)) :
    G ≤ Subgroup.normalizer (⁅A, B⁆ : Subgroup X) := by
  rw [Subgroup.commutator_def, Subgroup.le_normalizer_closure_iff]
  rintro g hg _ ⟨a, ha, b, hb, rfl⟩
  have h1 : g * a * g⁻¹ ∈ A := Subgroup.le_normalizer_iff.1 hA g hg a ha
  have h2 : g * b * g⁻¹ ∈ B := Subgroup.le_normalizer_iff.1 hB g hg b hb
  have h3 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := conjugate_commutatorElement a b g
  rw [h3]
  exact Subgroup.subset_closure ⟨_, h1, _, h2, rfl⟩

theorem three_subgroups_mod {X' Y Z N : Subgroup X}
    (hX : X' ≤ Subgroup.normalizer (N : Set X)) (hY : Y ≤ Subgroup.normalizer (N : Set X))
    (hZ : Z ≤ Subgroup.normalizer (N : Set X)) (h1 : ⁅⁅X', Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X'⁆ ≤ N) :
    ⁅⁅Z, X'⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set X)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup X, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup X, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X' Y Z hX hY hZ] at h1
  rw [key Y Z X' hY hZ hX] at h2
  rw [key Z X' Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem comm_le_comm_comm {G K A : Subgroup X} (hK : ⁅K, K⁆ = K) (hKG : K ≤ G) (hAG : A ≤ G)
    (hGK : G ≤ Subgroup.normalizer (K : Set X)) (hGA : G ≤ Subgroup.normalizer (A : Set X)) :
    ⁅K, A⁆ ≤ ⁅⁅A, K⁆, K⁆ := by
  have hGAK : G ≤ Subgroup.normalizer (⁅A, K⁆ : Subgroup X) := le_normalizer_commutator hGA hGK
  have hGN : G ≤ Subgroup.normalizer (⁅⁅A, K⁆, K⁆ : Subgroup X) :=
    le_normalizer_commutator hGAK hGK
  have h1 : ⁅⁅K, A⁆, K⁆ ≤ ⁅⁅A, K⁆, K⁆ := by
    rw [Subgroup.commutator_comm K A]
  have h3 := three_subgroups_mod (X' := K) (Y := A) (Z := K) (N := ⁅⁅A, K⁆, K⁆)
    (hKG.trans hGN) (hAG.trans hGN) (hKG.trans hGN) h1 le_rfl
  rwa [hK] at h3


theorem le_normalizer_of_commute {H L : Subgroup X} (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) :
    H ≤ Subgroup.normalizer (L : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh l hl
  rw [hc h hh l hl, mul_assoc, mul_inv_cancel, mul_one]
  exact hl

theorem mem_sup_of_commute {H L : Subgroup X} (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) {x : X}
    (hx : x ∈ H ⊔ L) : ∃ h ∈ H, ∃ l ∈ L, x = h * l := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H L (le_normalizer_of_commute hc)
  have hx' : x ∈ (H : Set X) * (L : Set X) := by rw [← hset]; exact hx
  obtain ⟨h, hh, l, hl, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨h, hh, l, hl, rfl⟩

theorem card_sup_mul_card_inf_of_commute [Finite X] {H L : Subgroup X}
    (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) :
    Nat.card ↥(H ⊔ L) * Nat.card ↥(H ⊓ L) = Nat.card ↥H * Nat.card ↥L := by
  let μ : ↥H × ↥L →* X := MonoidHom.noncommCoprod H.subtype L.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : ↥H × ↥L, μ x = (x.1 : X) * x.2 := fun _ => rfl
  have hrange : μ.range = H ⊔ L := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card ↥(H ⊓ L) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : X), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : X)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact L.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

theorem exists_hom_of_prod {M : Type*} [Group M] {U Y V' : Subgroup X}
    (hYU : Y ≤ U) (hVU : V' ≤ U) (hdec : ∀ u ∈ U, ∃ y ∈ Y, ∃ v ∈ V', u = y * v)
    (hc : ∀ y ∈ Y, ∀ v ∈ V', y * v = v * y) (θ : ↥Y →* M)
    (hθ : ∀ y : ↥Y, (y : X) ∈ V' → θ y = 1) :
    ∃ Φ : ↥U →* M, (∀ y : ↥Y, Φ (Subgroup.inclusion hYU y) = θ y) ∧
      ∀ v : ↥V', Φ (Subgroup.inclusion hVU v) = 1 := by
  classical
  have hwd : ∀ y y' : ↥Y, ∀ v v' : ↥V', (y : X) * v = (y' : X) * v' → θ y = θ y' := by
    intro y y' v v' hyv
    have h1 : (y' : X)⁻¹ * y = v' * (v : X)⁻¹ := by
      calc (y' : X)⁻¹ * y = (y' : X)⁻¹ * (y * v) * (v : X)⁻¹ := by group
        _ = (y' : X)⁻¹ * (y' * v') * (v : X)⁻¹ := by rw [hyv]
        _ = v' * (v : X)⁻¹ := by group
    have h2 : θ (y'⁻¹ * y) = 1 := hθ _ (by
      show ((y'⁻¹ * y : ↥Y) : X) ∈ V'
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h1]
      exact V'.mul_mem v'.2 (V'.inv_mem v.2))
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2.symm
  let ψ : ↥U → ↥Y := fun u =>
    ⟨(hdec u u.2).choose, (hdec u u.2).choose_spec.1⟩
  let ψv : ∀ u : ↥U, ↥V' := fun u =>
    ⟨(hdec u u.2).choose_spec.2.choose, (hdec u u.2).choose_spec.2.choose_spec.1⟩
  have hψ : ∀ u : ↥U, (u : X) = (ψ u : X) * (ψv u : X) := fun u =>
    (hdec u u.2).choose_spec.2.choose_spec.2
  have hψ' : ∀ (u : ↥U) (y : ↥Y) (v : ↥V'), (u : X) = (y : X) * v → θ (ψ u) = θ y := by
    intro u y v huv
    exact hwd _ _ (ψv u) v ((hψ u).symm.trans huv)
  refine ⟨
    { toFun := fun u => θ (ψ u)
      map_one' := ?_
      map_mul' := ?_ }, ?_, ?_⟩
  · have := hψ' 1 1 1 (by simp)
    rw [this, map_one]
  · intro u u'
    have e1 : ((u * u' : ↥U) : X) = ((ψ u * ψ u' : ↥Y) : X) * ((ψv u * ψv u' : ↥V') : X) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hψ u, hψ u']
      have := hc (ψ u') (ψ u').2 (ψv u) (ψv u).2
      calc (ψ u : X) * ψv u * ((ψ u' : X) * ψv u') = (ψ u : X) * ((ψv u : X) * (ψ u' : X)) * ψv u' := by
            group
        _ = (ψ u : X) * (((ψ u' : X) * (ψv u : X))) * ψv u' := by rw [this]
        _ = _ := by group
    have := hψ' (u * u') (ψ u * ψ u') (ψv u * ψv u') e1
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, this, map_mul]
  · intro y
    have := hψ' (Subgroup.inclusion hYU y) y 1 (by simp)
    simpa using this
  · intro v
    have := hψ' (Subgroup.inclusion hVU v) 1 v (by simp)
    simpa using this

end Basic

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.BlocksAux
