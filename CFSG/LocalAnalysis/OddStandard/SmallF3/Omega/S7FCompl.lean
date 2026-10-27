module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FKer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFam

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace S7FFrame

variable {t : G} {B E H : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem kap_zpow (F : S7FFrame t B E H φ) (k : ℤ) : s7fKap t (t ^ k) = 1 := by
  unfold s7fKap
  group

theorem s7fU_inf (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E)
    (hκu : ∀ i, s7fKap t (u i) = φ (wvec i)) : zpowers t ⊓ s7fU B u = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxU⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
  have ht1 : t ≠ 1 := fun h => F.t_not_mem (h ▸ B.one_mem)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact F.t_sq) ht1
  have hmod : t ^ (k % 2) = t ^ k := by
    simpa [hord] using zpow_mod_orderOf t k
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [Subgroup.mem_bot, ← hmod, h0, zpow_zero]
  · exfalso
    have hkB : t ^ k ∈ B := F.s7fU_ker hu hκu _ hxU (F.kap_zpow k)
    rw [← hmod, h1, zpow_one] at hkB
    exact F.t_not_mem hkB

theorem s7fU_kap_surj (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E)
    (hκu : ∀ i, s7fKap t (u i) = φ (wvec i)) :
    ∀ x ∈ B, ∃ y ∈ s7fU B u, s7fKap t y = x := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := F.mem_B_iff.mp hx
  obtain ⟨a, b, c, d, rfl⟩ := even_eq_four_wvec hv
  refine ⟨(u a * u b) * (u c * u d),
    (s7fU B u).mul_mem (mul_mem_s7fU B u a b) (mul_mem_s7fU B u c d), ?_⟩
  rw [F.kap_mul (E.mul_mem (hu a) (hu b)) (E.mul_mem (hu c) (hu d)), F.kap_mul (hu a) (hu b),
    F.kap_mul (hu c) (hu d), hκu, hκu, hκu, hκu,
    F.perm.1 _ _ (wvec_add_even a b) (wvec_add_even c d),
    F.perm.1 _ _ (wvec_even a) (wvec_even b), F.perm.1 _ _ (wvec_even c) (wvec_even d)]

theorem s7fU_sup (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E)
    (hκu : ∀ i, s7fKap t (u i) = φ (wvec i)) : zpowers t ⊔ s7fU B u = E := by
  apply le_antisymm
  · exact sup_le (Subgroup.zpowers_le.mpr F.t_mem) (F.s7fU_le hu)
  · intro e he
    obtain ⟨x, hx, hκx⟩ := F.s7fU_kap_surj hu hκu (s7fKap t e) (F.kap_mem e he)
    have hxE := F.s7fU_le hu hx
    have hκ : s7fKap t (x⁻¹ * e) = 1 := by
      rw [F.kap_inv_mul hxE he, hκx, inv_mul_cancel]
    rcases F.kap_ker _ (E.mul_mem (E.inv_mem hxE) he) hκ with hb | hb
    · have e' : e = x * (x⁻¹ * e) := by group
      rw [e']
      exact Subgroup.mem_sup_right ((s7fU B u).mul_mem hx (le_s7fU B u hb))
    · have hx' : t * x * t⁻¹ ∈ s7fU B u :=
        F.conj_mem_of_B_le (F.s7fU_le hu) (le_s7fU B u) F.t_mem hx
      have e' : e = t⁻¹ * ((t * x * t⁻¹) * (t * (x⁻¹ * e))) := by group
      rw [e']
      exact Subgroup.mul_mem_sup ((zpowers t).inv_mem (Subgroup.mem_zpowers t))
        ((s7fU B u).mul_mem hx' (le_s7fU B u hb))

theorem card_s7fU [Finite G] (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E)
    (hκu : ∀ i, s7fKap t (u i) = φ (wvec i)) : Nat.card (s7fU B u) = 2 ^ 8 := by
  set U := s7fU B u with hU
  have hUE : U ≤ E := F.s7fU_le hu
  let f : ↥U →* ↥B :=
    { toFun := fun x => ⟨s7fKap t (x : G), F.kap_mem _ (hUE x.2)⟩
      map_one' := by
        apply Subtype.ext
        change s7fKap t (1 : G) = 1
        unfold s7fKap
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        change s7fKap t ((x : G) * (y : G)) = s7fKap t (x : G) * s7fKap t (y : G)
        exact F.kap_mul (hUE x.2) (hUE y.2) }
  have hsurj : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨y, hy, hκy⟩ := F.s7fU_kap_surj hu hκu b hb
    exact ⟨⟨y, hy⟩, Subtype.ext hκy⟩
  have hker : f.ker = B.subgroupOf U := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : s7fKap t (x : G) = 1 := congrArg Subtype.val hx
      exact F.s7fU_ker hu hκu _ x.2 hx'
    · intro hx
      exact Subtype.ext (F.kap_B hx)
  have h1 : Nat.card (↥U ⧸ f.ker) = Nat.card B :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have h2 : Nat.card f.ker = Nat.card B := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_s7fU B u)).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, h1, h2, F.card_B]
  norm_num

theorem s7fU_normalized (F : S7FFrame t B E H φ) {u : Fin 5 → G} (hu : ∀ i, u i ∈ E)
    (hκu : ∀ i, s7fKap t (u i) = φ (wvec i))
    (heven : ∀ h ∈ H, ∀ σ ∈ alternatingGroup (Fin 5), s7fActs φ h σ →
      ∀ i, (u (σ i))⁻¹ * (h * u i * h⁻¹) ∈ B) :
    ∀ h ∈ H, ∀ x ∈ s7fU B u, h * x * h⁻¹ ∈ s7fU B u := by
  intro h hh x hx
  obtain ⟨σ, hσ⟩ := F.acts hh
  let P : Subgroup G := (s7fU B u).comap (MulAut.conj h).toMonoidHom
  have hP : ∀ y, y ∈ P ↔ h * y * h⁻¹ ∈ s7fU B u := fun y => Iff.rfl
  have hle : s7fU B u ≤ P := by
    rw [s7fU, Subgroup.closure_le]
    rintro y (hy | ⟨i, j, rfl⟩)
    · exact (hP y).mpr (le_s7fU B u (F.H_B hh hy))
    · refine (hP _).mpr ?_
      set di := (u (σ i))⁻¹ * (h * u i * h⁻¹) with hdi
      set dj := (u (σ j))⁻¹ * (h * u j * h⁻¹) with hdj
      have hdiE : di ∈ E := E.mul_mem (E.inv_mem (hu _)) (F.H_E h hh _ (hu i))
      have hdjE : dj ∈ E := E.mul_mem (E.inv_mem (hu _)) (F.H_E h hh _ (hu j))
      have hodd : di⁻¹ * dj ∈ B := F.family_odd hu hκu heven h hh σ hσ i j
      have hdd : di * dj ∈ B := by
        have e : di * dj = (di * di) * (di⁻¹ * dj) := by group
        rw [e]
        exact B.mul_mem (F.sq_mem di hdiE) hodd
      have hc : (u (σ j) * di)⁻¹ * (di * u (σ j)) ∈ B := F.comm_mod (hu _) hdiE
      set c := (u (σ j) * di)⁻¹ * (di * u (σ j)) with hcdef
      have key : h * (u i * u j) * h⁻¹ = (u (σ i) * u (σ j)) * (di * c * dj) := by
        rw [hcdef, hdi, hdj]
        group
      have hdcd : di * c * dj ∈ B := by
        have e : di * c * dj = (di * dj) * c := by
          rw [mul_assoc, ← F.comm_B dj hdjE c hc, ← mul_assoc]
        rw [e]
        exact B.mul_mem hdd hc
      rw [key]
      exact (s7fU B u).mul_mem (mul_mem_s7fU B u _ _) (le_s7fU B u hdcd)
  exact (hP x).mp (hle hx)

theorem exists_compl [Finite G] (F : S7FFrame t B E H φ) :
    ∃ U : Subgroup G, U ≤ E ∧ B ≤ U ∧ Nat.card U = 2 ^ 8 ∧ zpowers t ⊔ U = E ∧
      zpowers t ⊓ U = ⊥ ∧ ∀ h ∈ H, ∀ x ∈ U, h * x * h⁻¹ ∈ U := by
  obtain ⟨u, hu, hκu, heven⟩ := F.exists_family
  exact ⟨s7fU B u, F.s7fU_le hu, le_s7fU B u, F.card_s7fU hu hκu, F.s7fU_sup hu hκu,
    F.s7fU_inf hu hκu, F.s7fU_normalized hu hκu heven⟩

end S7FFrame

end CFSG.OddStandard.SmallF3.Omega
