module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreOrth
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance QuadraticMap Matrix

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem gLAPPrimeCoreOf_eq_bot_of_framework_pp_H (hZ : Subgroup.center G = ⊥) {p : ℕ}
    (hp : p.Prime)
    (g : G) (Gen T : Set G)
    (h1 : ∀ q ∈ Gen ∪ T, g * q = q * g)
    (hT : ∀ s q, s * g = g * s → q ∈ T → s * q = q * s)
    (hGen : ∀ s q, s * g = g * s → q ∈ Gen → s * q * s⁻¹ ∈ Gen)
    (hp3 : ∀ q ∈ Gen, ∀ q' ∈ Gen, ∃ k : ℕ, (q' * q⁻¹) ^ p ^ k = 1)
    (H : Subgroup (MulAut G)) (hH : innerAut G ≤ H)
    (huniq : ∀ α ∈ H, (orderOf α).Coprime p → (∀ q ∈ Gen ∪ T, α q = q) → α = 1)
    (x : MulAut G) (hx : x = MulAut.conj g) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut G))) = ⊥ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set X := H ⊓ Subgroup.centralizer ({x} : Set (MulAut G)) with hX
  have hmemX : ∀ q ∈ Gen ∪ T, (MulAut.conj q : MulAut G) ∈ X := by
    intro q hq
    refine ⟨hH ⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hx, ← map_mul, ← map_mul, h1 q hq]
  have hcop : ∀ d ∈ GLAPPrimeCoreOf p X, (orderOf d).Coprime p := fun d hd =>
    CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hd
  have hcoreX : ∀ d ∈ GLAPPrimeCoreOf p X, d ∈ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have stageA : ∀ s : G, (MulAut.conj s : MulAut G) ∈ GLAPPrimeCoreOf p X →
      (MulAut.conj s : MulAut G) = 1 := by
    intro s hs
    have hsX : (MulAut.conj s : MulAut G) ∈ X := hcoreX _ hs
    have hsg : s * g = g * s := by
      have h := (Subgroup.mem_centralizer_singleton_iff.1 hsX.2)
      rw [hx, ← map_mul, ← map_mul] at h
      exact hinj h
    have hfix : ∀ q ∈ Gen, s * q = q * s := by
      intro q hq
      have hq' : s * q * s⁻¹ ∈ Gen := hGen s q hsg hq
      have hcq := hmemX q (Or.inl hq)
      have h2 : (MulAut.conj q : MulAut G) * (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹ ∈
          GLAPPrimeCoreOf p X := by
        have := conj_mem_gLAPPrimeCoreOf (inv_mem hs) hcq
        simpa [mul_assoc] using this
      have h3 := mul_mem hs h2
      have he : (MulAut.conj s : MulAut G) * ((MulAut.conj q : MulAut G) *
          (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹) = MulAut.conj ((s * q * s⁻¹) * q⁻¹) := by
        simp only [map_mul, map_inv, mul_assoc]
      rw [he] at h3
      have hord := hcop _ h3
      obtain ⟨k, hk⟩ := hp3 q hq _ hq'
      have hpow : ((MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G)) ^ p ^ k = 1 := by
        rw [← map_pow, hk, map_one]
      have hdvd : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) ∣ p ^ k :=
        orderOf_dvd_of_pow_eq_one hpow
      have h1' : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hord) hdvd
      have h4 : (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 := orderOf_eq_one_iff.1 h1'
      have h5 : (s * q * s⁻¹) * q⁻¹ = 1 := hinj (by rw [h4, map_one])
      have h6 : s * q * s⁻¹ = q := by simpa [mul_inv_eq_one] using h5
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6
    refine huniq _ (hsX.1) (hcop _ hs) ?_
    rintro q (hq | hq)
    · simp [MulAut.conj_apply, hfix q hq]
    · simp [MulAut.conj_apply, hT s q hsg hq]
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  refine huniq α (hcoreX α hα).1 (hcop α hα) ?_
  intro q hq
  have hcq := hmemX q hq
  have h2 : (MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹ ∈ GLAPPrimeCoreOf p X := by
    have := conj_mem_gLAPPrimeCoreOf (inv_mem hα) hcq
    simpa [mul_assoc] using this
  have h3 := mul_mem hα h2
  have he : α * ((MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹) =
      MulAut.conj (α q * q⁻¹) := by
    have := mul_conj_mul_inv_eq α q
    rw [map_mul, map_inv, ← this]
    group
  rw [he] at h3
  have h4 := stageA _ h3
  have h5 : α q * q⁻¹ = 1 := hinj (by rw [h4, map_one])
  simpa [mul_inv_eq_one] using h5

theorem fixes_centralizer_of_mem_core (hZ : Subgroup.center G = ⊥) {p : ℕ} (hp : p.Prime)
    (g : G) (H : Subgroup (MulAut G)) (hH : innerAut G ≤ H)
    (hin : GLAPPrimeCoreOf p (innerAut G ⊓ Subgroup.centralizer ({MulAut.conj g} : Set (MulAut G))) = ⊥)
    {α : MulAut G}
    (hα : α ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj g} : Set (MulAut G)))) :
    ∀ s : G, s * g = g * s → α s = s := by
  intro s hs
  set M := H ⊓ Subgroup.centralizer ({MulAut.conj g} : Set (MulAut G)) with hM
  set K := innerAut G ⊓ Subgroup.centralizer ({MulAut.conj g} : Set (MulAut G)) with hK
  have hKM : K ≤ M := inf_le_inf_right _ hH
  have hKn : (K.subgroupOf M).Normal := by
    refine ⟨fun k hk m => ?_⟩
    have hk' := Subgroup.mem_subgroupOf.1 hk
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · obtain ⟨t, ht⟩ := hk'.1
      refine ⟨(m : MulAut G) t, ?_⟩
      have := mul_conj_mul_inv_eq (m : MulAut G) t
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← ht, ← this]
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have hm : Commute (MulAut.conj g) (m : MulAut G) :=
        (Subgroup.mem_centralizer_singleton_iff.1 (m.2.2)).symm
      have hkc : Commute (MulAut.conj g) k := (Subgroup.mem_centralizer_singleton_iff.1 hk'.2).symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ((hm.mul_right hkc).mul_right hm.inv_right).eq.symm
  have hsn : IsSubnormal K M := IsSubnormal.step hKM hKn (IsSubnormal.refl M)
  have hinf := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn
  have hcs : (MulAut.conj s : MulAut G) ∈ K := by
    refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, hs]
  have hcsM : (MulAut.conj s : MulAut G) ∈ M := hKM hcs
  have hβ : MulAut.conj s * α * (MulAut.conj s)⁻¹ * α⁻¹ ∈ GLAPPrimeCoreOf p M := by
    have h1 := conj_mem_gLAPPrimeCoreOf hα hcsM
    exact mul_mem h1 (inv_mem hα)
  have e1 : α * (MulAut.conj s)⁻¹ * α⁻¹ = (MulAut.conj (α s))⁻¹ := by
    rw [← mul_conj_mul_inv_eq α s]; group
  have hβ2 : MulAut.conj s * α * (MulAut.conj s)⁻¹ * α⁻¹ = MulAut.conj (s * (α s)⁻¹) := by
    calc MulAut.conj s * α * (MulAut.conj s)⁻¹ * α⁻¹
        = MulAut.conj s * (α * (MulAut.conj s)⁻¹ * α⁻¹) := by group
      _ = MulAut.conj s * (MulAut.conj (α s))⁻¹ := by rw [e1]
      _ = MulAut.conj (s * (α s)⁻¹) := by simp
  have hβK : MulAut.conj s * α * (MulAut.conj s)⁻¹ * α⁻¹ ∈ K ⊓ GLAPPrimeCoreOf p M := by
    refine ⟨⟨⟨s * (α s)⁻¹, hβ2.symm⟩, ?_⟩, hβ⟩
    have hβM : MulAut.conj s * α * (MulAut.conj s)⁻¹ * α⁻¹ ∈ M := by
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hβ
      rw [← hy]; exact y.2
    exact hβM.2
  rw [hinf, hin, Subgroup.mem_bot, hβ2] at hβK
  have hinj := conj_injective_of_center_eq_bot hZ
  have h0 : s * (α s)⁻¹ = 1 := hinj (by rw [hβK, map_one])
  rw [mul_inv_eq_one] at h0
  exact h0.symm

end Abstract

namespace Orth

section ModelThmH

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Orth

theorem uniq_of_fix_gen {S : Type} [Group S] [Finite S]
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {d : ℕ} (hd : 5 ≤ d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (e : S ≃* matrixProjectiveDerived Q) (g : S) {s0 : matrixDerived Q} {c : K}
    (hcc : c * c = 1) (hg0 : e g = matrixProjectiveProjection Q s0)
    (hG : gEnd s0 c ^ p = 1) (hG1 : gEnd s0 c ≠ 1)
    (α : MulAut S) (hαE : MulAut.congr e α ∈ matrixProjectiveImage Q)
    (hcop : (orderOf α).Coprime p)
    (hfix : ∀ q ∈ {q' | e q' ∈ genSet Q p s0 c} ∪ {q' | e q' ∈ tSet Q p s0 c ∨ q' = g},
      α q = q) : α = 1 := by
  have : NeZero d := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hcop' : (orderOf (MulAut.congr e α)).Coprime p := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hcop
  have hαg : α g = g := hfix g (Or.inr (Or.inr rfl))
  have h1 : MulAut.congr e α = 1 := by
    refine uniq_orth hnd hd h2 hp2 hab hcc hG hG1 hαE hcop' ?_ ?_ ?_
    · rw [← hg0, MulAut.congr_apply]
      simp [hαg]
    · intro q0 hq0
      have hmem : e.symm q0 ∈ {q' | e q' ∈ genSet Q p s0 c} := by simpa using hq0
      have := hfix _ (Or.inl hmem)
      change e (α (e.symm q0)) = q0
      rw [this]; simp
    · intro q0 hq0
      have hmem : e.symm q0 ∈ {q' | e q' ∈ tSet Q p s0 c ∨ q' = g} := Or.inl (by simpa using hq0)
      have := hfix _ (Or.inr hmem)
      change e (α (e.symm q0)) = q0
      rw [this]; simp
  exact (MulAut.congr e).injective (by rw [h1, map_one])

theorem inner_mem_matrixProjectiveImage {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (t : matrixProjectiveDerived Q) :
    (MulAut.conj t : MulAut (matrixProjectiveDerived Q)) ∈ matrixProjectiveImage Q := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q t
  refine (mem_matrixProjectiveImage_iff Q _).2 ⟨matrixDerivedInclusion Q A, MulEquiv.ext fun y => ?_⟩
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q y
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem orthModel_framework_data {S : Type} [Group S] [Finite S]
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {d : ℕ} [NeZero d] (Q : QuadraticForm K (Fin d → K))
    (e : S ≃* matrixProjectiveDerived Q) (g : S) {s0 : matrixDerived Q} {c : K}
    (hcc : c * c = 1) (hg0 : e g = matrixProjectiveProjection Q s0)
    (hG : gEnd s0 c ^ p = 1) (h2 : (2 : K) ≠ 0) :
    (∀ q ∈ {q' | e q' ∈ genSet Q p s0 c} ∪ {q' | e q' ∈ tSet Q p s0 c ∨ q' = g}, g * q = q * g) ∧
    (∀ s q, s * g = g * s → q ∈ {q' | e q' ∈ tSet Q p s0 c ∨ q' = g} → s * q = q * s) ∧
    (∀ s q, s * g = g * s → q ∈ {q' | e q' ∈ genSet Q p s0 c} → s * q * s⁻¹ ∈
      {q' | e q' ∈ genSet Q p s0 c}) ∧
    (∀ q ∈ {q' | e q' ∈ genSet Q p s0 c}, ∀ q' ∈ {q' | e q' ∈ genSet Q p s0 c},
      ∃ k : ℕ, (q' * q⁻¹) ^ p ^ k = 1) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro q' (hq' | hq')
    · apply e.injective
      rw [map_mul, map_mul, hg0]
      exact genSet_commute h2 hodd hcc hG hq'
    · rcases hq' with hq' | hq'
      · apply e.injective
        rw [map_mul, map_mul, hg0]
        exact tSet_commute hcc hG hq'
      · rw [hq']
  · intro s q' hs hq'
    have hs' : e s * matrixProjectiveProjection Q s0 = matrixProjectiveProjection Q s0 * e s := by
      rw [← hg0, ← map_mul, ← map_mul, hs]
    rcases hq' with hq' | hq'
    · apply e.injective
      rw [map_mul, map_mul]
      exact tSet_central hcc hG hs' hq'
    · rw [hq']; exact hs
  · intro s q' hs hq'
    have hs' : e s * matrixProjectiveProjection Q s0 = matrixProjectiveProjection Q s0 * e s := by
      rw [← hg0, ← map_mul, ← map_mul, hs]
    have := genSet_conj hcc hG hs' hq'
    show e (s * q' * s⁻¹) ∈ genSet Q p s0 c
    rw [map_mul, map_mul, map_inv]
    exact this
  · intro q' hq' q'' hq''
    obtain ⟨k, hk⟩ := genSet_pow h2 hodd hcc hG hq' hq''
    refine ⟨k, e.injective ?_⟩
    rw [map_pow, map_mul, map_inv, map_one]
    exact hk

theorem innerCoreFree_of_orthModel_inner {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {d : ℕ} (hd : 5 ≤ d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (polarBilin Q).Nondegenerate) (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (e : S ≃* matrixProjectiveDerived Q) :
    ∀ x ∈ innerAut S, orderOf x = p →
      GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro x hx hxo
  have : NeZero d := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = p := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (e g) = p := by rw [MulEquiv.orderOf_eq e g]; exact hord
  obtain ⟨s0, c, hcc, hg0, hG, hG1⟩ := exists_lift hQ hp2 (e g) hord0
  obtain ⟨hA, hB, hC, hD⟩ := orthModel_framework_data hp2 Q e g hcc hg0 hG h2
  refine gLAPPrimeCoreOf_eq_bot_of_framework_pp_H hZ hp g
    {q' | e q' ∈ genSet Q p s0 c} {q' | e q' ∈ tSet Q p s0 c ∨ q' = g} hA hB hC hD
    (innerAut S) le_rfl ?_ _ rfl
  intro α hα hcop hfix
  obtain ⟨t, rfl⟩ := hα
  have hαE : MulAut.congr e (MulAut.conj t) ∈ matrixProjectiveImage Q := by
    have : MulAut.congr e (MulAut.conj t) = MulAut.conj (e t) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [this]
    exact inner_mem_matrixProjectiveImage Q (e t)
  exact uniq_of_fix_gen hp2 hd Q hnd hab e g hcc hg0 hG hG1 _ hαE hcop hfix

theorem orthModel_rigid_of_image {S : Type} [Group S] [Finite S] {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {d : ℕ} (hd : 5 ≤ d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (polarBilin Q).Nondegenerate) (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (e : S ≃* matrixProjectiveDerived Q) (g : S) (hord : orderOf g = p)
    (α : MulAut S) (hαE : MulAut.congr e α ∈ matrixProjectiveImage Q)
    (hcop : (orderOf α).Coprime p) (hfix : ∀ s : S, s * g = g * s → α s = s) : α = 1 := by
  have : NeZero d := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hord0 : orderOf (e g) = p := by rw [MulEquiv.orderOf_eq e g]; exact hord
  obtain ⟨s0, c, hcc, hg0, hG, hG1⟩ := exists_lift hQ hp2 (e g) hord0
  obtain ⟨hA, -, -, -⟩ := orthModel_framework_data hp2 Q e g hcc hg0 hG h2
  refine uniq_of_fix_gen hp2 hd Q hnd hab e g hcc hg0 hG hG1 α hαE hcop fun q hq => ?_
  exact hfix q (hA q hq).symm

end ModelThmH

end Orth

section DFour

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedOmega
  StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.HardMathSupport.Solomon.LocalBalance Orth

@[expose] def DFourPrimeCentralizerInImage : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], p ≠ 2 →
    ∀ g : matrixProjectiveDerived (coordinateQuadPlus 4 K), orderOf g = p →
      ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
        (orderOf α).Coprime p → (∀ s, s * g = g * s → α s = s) →
          α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)

theorem innerCoreFree_POmegaPlus_four (hres : DFourPrimeCentralizerInImage)
    {T : Type} [Group T] [Finite T] (hS : IsSimpleGroup T)
    (hnab : ∃ a b : T, a * b ≠ b * a) {ℓ f : ℕ}
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel T
      CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus 4 ℓ f) (hℓ2 : ℓ ≠ 2) :
    ∀ x ∈ innerAut T, orderOf x = ℓ → ∀ H : Subgroup (MulAut T), innerAut T ≤ H →
      CFSG.Open.GLAPPrimeCoreOf ℓ (H ⊓ Subgroup.centralizer ({x} : Set (MulAut T))) = ⊥ := by
  intro x hx hxo H hH
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fact ℓ.Prime := ⟨hm.1.1⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound T CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus
    (.inr (.inl rfl)) 4 ℓ f hm K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_plus hm K hK e
  have : CharP K ℓ := by
    have := ringChar.charP K
    rw [hchar] at this
    exact this
  have hQ := exists_nonzero_value _ (coordinate_model_intrinsic_plus hm K hK e).1
  have hab' := exists_two_pow_card_abelianization (plusIndexEquiv 4) (quadPlus 4 K) hab
  set e' := coordinatePlusWitnessEquiv K e with he'
  have hZ : Subgroup.center T = ⊥ := center_eq_bot_of_simple hS hnab
  have hin := innerCoreFree_of_orthModel_inner hS hnab hℓ2 (d := 2 * 4) (by omega) _ hnd hQ hab' e'
    x hx hxo
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = ℓ := by
    rw [← orderOf_injective (MulAut.conj : T →* MulAut T) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  have hfix := fixes_centralizer_of_mem_core hZ (Fact.out : ℓ.Prime) g H hH hin hα
  have hcop := CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf
    (Fact.out : ℓ.Prime) hα
  have hαE : MulAut.congr e' α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    refine hres K ℓ hℓ2 (e' g) (by rw [MulEquiv.orderOf_eq e' g]; exact hord) _ ?_ ?_
    · rw [MulEquiv.orderOf_eq (MulAut.congr e') α]; exact hcop
    · intro s hs
      have hs' : e'.symm s * g = g * e'.symm s := by
        apply e'.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hs
      have := hfix _ hs'
      show e' (α (e'.symm s)) = s
      rw [this, MulEquiv.apply_symm_apply]
  exact orthModel_rigid_of_image hℓ2 (d := 2 * 4) (by omega) _ hnd hQ hab' e' g hord α hαE hcop hfix

theorem defCharInnerCoreFreeFamDFour_of_image (hres : DFourPrimeCentralizerInImage) :
    DefCharInnerCoreFreeFamDFour := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hSe
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv e
  subst hpq
  exact innerCoreFree_POmegaPlus_four hres hS hnab hm hp2 x hx hxo H hH

end DFour

end CFSG.HardMathSupport.Timmesfeld.DefChar
