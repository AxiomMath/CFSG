module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77Stab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec7E16Act (N B : Subgroup G) (φ : (Fin 5 → ZMod 2) → G) : Prop where
  le : B ≤ N
  elem : IsElemAb2 B 4
  cent : N ⊓ centralizer (B : Set G) ≤ B
  perm : IsPermModuleVia IsEvenVec φ B N ⊤

variable {N B : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem Sec7E16Act.add (h : Sec7E16Act N B φ) {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : φ (v + w) = φ v * φ w :=
  h.perm.1 v w hv hw

theorem Sec7E16Act.inj (h : Sec7E16Act N B φ) {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) (hvw : φ v = φ w) : v = w :=
  h.perm.2.1 v w hv hw hvw

theorem Sec7E16Act.mem_iff (h : Sec7E16Act N B φ) (x : G) :
    x ∈ B ↔ ∃ v, IsEvenVec v ∧ φ v = x :=
  h.perm.2.2.1 x

theorem Sec7E16Act.phi_zero (h : Sec7E16Act N B φ) : φ 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h1 := h.add h0 h0
  rw [add_zero] at h1
  exact mul_eq_left.mp h1.symm

theorem Sec7E16Act.phi_mem (h : Sec7E16Act N B φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ v ∈ B :=
  (h.mem_iff _).mpr ⟨v, hv, rfl⟩

theorem Sec7E16Act.exists_act (h : Sec7E16Act N B φ) {x : G} (hx : x ∈ N) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) := by
  obtain ⟨σ, -, hσ⟩ := h.perm.2.2.2.1 x hx
  exact ⟨σ, hσ⟩

theorem Sec7E16Act.exists_elt (h : Sec7E16Act N B φ) (σ : Equiv.Perm (Fin 5)) :
    ∃ x ∈ N, ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) :=
  h.perm.2.2.2.2 σ (Subgroup.mem_top σ)

theorem Sec7E16Act.conj_mem_B (h : Sec7E16Act N B φ) {x : G} (hx : x ∈ N) {b : G} (hb : b ∈ B) :
    x * b * x⁻¹ ∈ B := by
  obtain ⟨σ, hσ⟩ := h.exists_act hx
  obtain ⟨v, hv, rfl⟩ := (h.mem_iff b).mp hb
  rw [hσ v hv]
  exact h.phi_mem (sec7l77_even_permVec σ hv)

theorem Sec7E16Act.act_unique (h : Sec7E16Act N B φ) {x : G} {σ σ' : Equiv.Perm (Fin 5)}
    (hσ : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hσ' : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ' v)) : σ = σ' := by
  have h1 : σ'⁻¹ * σ = 1 := by
    refine sec7l77_perm_triv _ fun v hv => ?_
    have h2 : permVec σ v = permVec σ' v :=
      h.inj (sec7l77_even_permVec σ hv) (sec7l77_even_permVec σ' hv)
        ((hσ v hv).symm.trans (hσ' v hv))
    rw [← sec7l77_permVec_mul, h2, sec7l77_permVec_mul, inv_mul_cancel, sec7l77_permVec_one]
  exact (inv_mul_eq_one.mp h1).symm

theorem Sec7E16Act.cent_N (h : Sec7E16Act N B φ) {b : G} (hb : b ∈ B)
    (hc : ∀ x ∈ N, x * b = b * x) : b = 1 := by
  obtain ⟨v, hv, rfl⟩ := (h.mem_iff b).mp hb
  have hv0 : v = 0 := by
    refine sec7l78_fix_all v hv fun σ => ?_
    obtain ⟨x, hx, hxσ⟩ := h.exists_elt σ
    have h1 : x * φ v * x⁻¹ = φ v := by rw [hc x hx]; group
    exact (h.inj (sec7l77_even_permVec σ hv) hv ((hxσ v hv).symm.trans h1))
  rw [hv0]
  exact h.phi_zero

noncomputable def Sec7E16Act.rho (h : Sec7E16Act N B φ) : ↥N →* Equiv.Perm (Fin 5) where
  toFun x := Classical.choose (h.exists_act x.2)
  map_one' := by
    refine h.act_unique (x := ((1 : ↥N) : G)) (Classical.choose_spec (h.exists_act (1 : ↥N).2)) ?_
    intro v hv
    simp [sec7l77_permVec_one]
  map_mul' x y := by
    refine h.act_unique (x := ((x * y : ↥N) : G))
      (Classical.choose_spec (h.exists_act (x * y : ↥N).2)) ?_
    intro v hv
    have hy := Classical.choose_spec (h.exists_act y.2) v hv
    have hy' := sec7l77_even_permVec (Classical.choose (h.exists_act y.2)) hv
    have hx := Classical.choose_spec (h.exists_act x.2) _ hy'
    calc ((x * y : ↥N) : G) * φ v * ((x * y : ↥N) : G)⁻¹
        = (x : G) * ((y : G) * φ v * (y : G)⁻¹) * (x : G)⁻¹ := by
          simp only [Subgroup.coe_mul]; group
      _ = φ (permVec (Classical.choose (h.exists_act x.2) *
            Classical.choose (h.exists_act y.2)) v) := by
          rw [hy, hx, sec7l77_permVec_mul]

theorem Sec7E16Act.rho_spec (h : Sec7E16Act N B φ) (x : ↥N) {v : Fin 5 → ZMod 2}
    (hv : IsEvenVec v) : (x : G) * φ v * (x : G)⁻¹ = φ (permVec (h.rho x) v) :=
  Classical.choose_spec (h.exists_act x.2) v hv

theorem Sec7E16Act.rho_surjective (h : Sec7E16Act N B φ) : Function.Surjective h.rho := by
  intro σ
  obtain ⟨x, hx, hxσ⟩ := h.exists_elt σ
  exact ⟨⟨x, hx⟩, h.act_unique (x := x) (fun v hv => h.rho_spec ⟨x, hx⟩ hv) hxσ⟩

theorem Sec7E16Act.mem_ker_rho (h : Sec7E16Act N B φ) (x : ↥N) :
    x ∈ h.rho.ker ↔ (x : G) ∈ B := by
  constructor
  · intro hx
    have hx1 : h.rho x = 1 := hx
    refine h.cent ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    obtain ⟨v, hv, rfl⟩ := (h.mem_iff b).mp hb
    have h1 := h.rho_spec x hv
    rw [hx1, sec7l77_permVec_one] at h1
    calc φ v * (x : G) = ((x : G) * φ v * (x : G)⁻¹) * (x : G) := by rw [h1]
      _ = (x : G) * φ v := by group
  · intro hx
    have : h.rho x = 1 := by
      refine h.act_unique (x := (x : G)) (fun v hv => h.rho_spec x hv) ?_
      intro v hv
      have hc : (x : G) * φ v = φ v * (x : G) := by
        have := h.elem.1.1.is_comm.comm ⟨(x : G), hx⟩ ⟨φ v, h.phi_mem hv⟩
        exact congrArg Subtype.val this
      rw [hc, sec7l77_permVec_one]
      group
    exact this

theorem Sec7E16Act.pow_act (h : Sec7E16Act N B φ) {x : G} {σ : Equiv.Perm (Fin 5)}
    (hσ : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) (k : ℕ) :
    ∀ v, IsEvenVec v → x ^ k * φ v * (x ^ k)⁻¹ = φ (permVec (σ ^ k) v) := by
  induction k with
  | zero => intro v _; simp [sec7l77_permVec_one]
  | succ k ih =>
    intro v hv
    have hk := sec7l77_even_permVec (σ ^ k) hv
    calc x ^ (k + 1) * φ v * (x ^ (k + 1))⁻¹
        = x * (x ^ k * φ v * (x ^ k)⁻¹) * x⁻¹ := by group
      _ = x * φ (permVec (σ ^ k) v) * x⁻¹ := by rw [ih v hv]
      _ = φ (permVec σ (permVec (σ ^ k) v)) := hσ _ hk
      _ = φ (permVec (σ ^ (k + 1)) v) := by rw [sec7l77_permVec_mul, ← pow_succ']

theorem Sec7E16Act.exists_lift3 (h : Sec7E16Act N B φ) {τ : Equiv.Perm (Fin 5)} (hτ : τ ^ 3 = 1) :
    ∃ ν ∈ N, ν ^ 3 = 1 ∧ ∀ v, IsEvenVec v → ν * φ v * ν⁻¹ = φ (permVec τ v) := by
  obtain ⟨x, hx, hxτ⟩ := h.exists_elt τ
  have hx3 : x ^ 3 ∈ B := by
    refine h.cent ⟨N.pow_mem hx 3, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    obtain ⟨v, hv, rfl⟩ := (h.mem_iff b).mp hb
    have h1 := h.pow_act hxτ 3 v hv
    rw [hτ, sec7l77_permVec_one] at h1
    calc φ v * x ^ 3 = (x ^ 3 * φ v * (x ^ 3)⁻¹) * x ^ 3 := by rw [h1]
      _ = x ^ 3 * φ v := by group
  have hx6 : x ^ 6 = 1 := by
    have h2 := h.elem.1.2 (x ^ 3) hx3
    rw [← pow_mul] at h2
    exact h2
  refine ⟨x ^ 4, N.pow_mem hx 4, ?_, ?_⟩
  · calc (x ^ 4) ^ 3 = (x ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hx6, one_pow]
  · intro v hv
    have h1 := h.pow_act hxτ 4 v hv
    have h4 : τ ^ 4 = τ := by rw [show 4 = 3 + 1 from rfl, pow_succ, hτ, one_mul]
    rwa [h4] at h1

theorem Sec7E16Act.card_N [Finite G] (h : Sec7E16Act N B φ) : Nat.card N = 1920 := by
  have h1 : h.rho.ker.index = 120 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ h.rho_surjective,
      Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h2 : Nat.card h.rho.ker = 16 := by
    have hker : h.rho.ker = B.subgroupOf N := by
      ext x
      rw [h.mem_ker_rho x]
      rfl
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, h.elem.2]
    norm_num
  have h3 := Subgroup.index_mul_card h.rho.ker
  rw [h1, h2] at h3
  omega

theorem Sec7E16Act.card_sylow [Finite G] (h : Sec7E16Act N B φ) {P : Subgroup G}
    (hP : IsSylow2Of P N) : Nat.card P = 2 ^ 7 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hp, hnd⟩ := hP
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hmul := Subgroup.relIndex_mul_card (H := P) (K := N)
  rw [inf_eq_left.mpr hle, h.card_N, hk] at hmul
  have hdvd : 2 ^ k ∣ 1920 := Dvd.intro_left _ hmul
  have hk11 : k < 11 := by
    by_contra hlt
    have h1 : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hlt)
    have h2 : 2 ^ k ≤ 1920 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hk7 : k = 7 := by
    interval_cases k <;> norm_num at hmul hnd <;> omega
  rw [hk, hk7]

end CFSG.OddStandard.SmallF3.Omega
