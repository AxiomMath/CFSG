module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnC
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnStmt

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup Equiv CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.IVK.Lifted

section Twist

variable {H : Type} [Group H] {K : Subgroup H} {n : ℕ}

theorem conj_of_mem_center {G : Type*} [Group G] {c : G} (hc : c ∈ center G) (g : G) : g * c * g⁻¹ = c := by
  rw [mem_center_iff] at hc
  rw [hc g, mul_inv_cancel_right]

theorem twist_ker (R : PermRep K n) (a : ↥K) :
    (R.π.comp (MulAut.conj a⁻¹).toMonoidHom).ker = R.π.ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    have hc : (MulAut.conj a⁻¹) x ∈ center ↥K := R.cover.ker_le_center h
    have h2 := conj_of_mem_center hc a
    have h3 : a * ((MulAut.conj a⁻¹) x) * a⁻¹ = x := by
      rw [MulAut.conj_apply]; group
    rw [h3] at h2
    rw [h2]
    exact h
  · intro h
    have hc : x ∈ center ↥K := R.cover.ker_le_center h
    rw [MulAut.conj_apply, conj_of_mem_center hc]
    exact h

@[expose] def twist (R : PermRep K n) (a : ↥K) : PermRep K n where
  π := R.π.comp (MulAut.conj a⁻¹).toMonoidHom
  ρ := R.ρ.comp (MulAut.conj (a : H)⁻¹).toMonoidHom
  cover :=
    ⟨R.cover.surj.comp (MulAut.conj a⁻¹).surjective, by rw [twist_ker]; exact R.cover.ker_le_center,
      by rw [twist_ker]; exact R.cover.card_ker, R.cover.perfect⟩
  ρ_K := by
    intro k
    have h := R.ρ_K ((MulAut.conj a⁻¹) k)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← h]
    congr 1
  ker_ρ := by
    intro x hx
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hx
    obtain ⟨k0, hk0, hπ⟩ := R.ker_ρ _ hx
    refine ⟨a * k0 * a⁻¹, ?_, ?_⟩
    · rw [MulAut.conj_apply] at hk0
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hk0 ⊢
      rw [hk0]; group
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have : a⁻¹ * (a * k0 * a⁻¹) * a⁻¹⁻¹ = k0 := by group
      rw [this]
      exact hπ

theorem twist_rho_apply (R : PermRep K n) (a : ↥K) (h : H) :
    (twist R a).ρ h = R.ρ ((a : H)⁻¹ * h * (a : H)) := by
  show R.ρ ((MulAut.conj (a : H)⁻¹) h) = _
  rw [MulAut.conj_apply, inv_inv]

theorem twist_kerData {R : PermRep K n} {z : H} (hz : R.KerData z) (a : ↥K) :
    (twist R a).KerData z where
  ne_one := hz.ne_one
  sq := hz.sq
  central := hz.central
  ρ_z := by
    rw [twist_rho_apply]
    have : (a : H)⁻¹ * z * (a : H) = z := by
      rw [hz.central (a : H)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact hz.ρ_z
  ker := by
    intro x hx
    rw [twist_rho_apply] at hx
    rcases hz.ker _ hx with h | h
    · left
      calc x = (a : H) * ((a : H)⁻¹ * x * (a : H)) * (a : H)⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc x = (a : H) * ((a : H)⁻¹ * x * (a : H)) * (a : H)⁻¹ := by group
        _ = (a : H) * z * (a : H)⁻¹ := by rw [h]
        _ = z := by rw [hz.central (a : H), mul_assoc, mul_inv_cancel, mul_one]

variable {m : ℕ}

@[expose] def Lifts.conj {R : PermRep K (m + 1)} (L : Lifts R) (a : ↥K) : Lifts (twist R a) where
  u := (a : H) * L.u * (a : H)⁻¹
  v := (a : H) * L.v * (a : H)⁻¹
  x1 := (a : H) * L.x1 * (a : H)⁻¹
  x2 := (a : H) * L.x2 * (a : H)⁻¹
  g := (a : H) * L.g * (a : H)⁻¹
  c := (a : H) * L.c * (a : H)⁻¹
  hu := by
    rw [twist_rho_apply]
    have : (a : H)⁻¹ * ((a : H) * L.u * (a : H)⁻¹) * (a : H) = L.u := by group
    rw [this]; exact L.hu
  hv := by
    rw [twist_rho_apply]
    have : (a : H)⁻¹ * ((a : H) * L.v * (a : H)⁻¹) * (a : H) = L.v := by group
    rw [this]; exact L.hv
  hx1 := by
    rw [twist_rho_apply]
    have : (a : H)⁻¹ * ((a : H) * L.x1 * (a : H)⁻¹) * (a : H) = L.x1 := by group
    rw [this]; exact L.hx1
  hx2 := by
    rw [twist_rho_apply]
    have : (a : H)⁻¹ * ((a : H) * L.x2 * (a : H)⁻¹) * (a : H) = L.x2 := by group
    rw [this]; exact L.hx2
  hg := by
    rw [twist_rho_apply]
    have : (a : H)⁻¹ * ((a : H) * L.g * (a : H)⁻¹) * (a : H) = L.g := by group
    rw [this]; exact L.hg
  hc := by
    rw [twist_rho_apply]
    have : (a : H)⁻¹ * ((a : H) * L.c * (a : H)⁻¹) * (a : H) = L.c := by group
    rw [this]; exact L.hc
  hc3 := by
    rw [conj_pow, L.hc3]; group

theorem Lifts.conj_t {R : PermRep K (m + 1)} (L : Lifts R) (a : ↥K) :
    (L.conj a).t = (a : H) * L.t * (a : H)⁻¹ := by
  simp only [Lifts.t, Lifts.conj]
  group

end Twist

section Entry

variable {H : Type} [Group H] [Finite H] {K : Subgroup H} {m : ℕ}

omit [Finite H] in
theorem z_mem_ZK {R : PermRep K (m + 1)} {z : H} (hz : R.KerData z) : z ∈ ZK K := by
  have hzK : z ∈ K := R.mem_K_of_sign z (by rw [hz.ρ_z]; simp)
  refine ⟨⟨z, hzK⟩, ?_, rfl⟩
  show (⟨z, hzK⟩ : ↥K) ∈ center ↥K
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  exact hz.central (g : H)

theorem exists_cfg (hH : Hyp5B H K (m + 1)) {t : H} (ht : t ∈ K) (ht2 : orderOf t = 2) (htz : t ∉ ZK K) :
    ∃ (R : PermRep K (m + 1)) (z : H) (Γ : Cfg R z), Γ.t = t := by
  obtain ⟨R⟩ := exists_permRep hH
  obtain ⟨z, hz⟩ := R.exists_kerData
  have h7 : 7 ≤ m := by have := hH.n_ge; omega
  have h10 : m ≤ 10 := by have := hH.n_le; omega
  obtain ⟨L⟩ := exists_lifts hz h7 h10
  have hzZ : z ∈ ZK K := z_mem_ZK hz
  have ht_sq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have hσ2 : R.ρ t ^ 2 = 1 := by rw [← map_pow, pow_two, ht_sq, map_one]
  have hσsign : Perm.sign (R.ρ t) = 1 := R.sign_of_mem_K t ht
  have hσne : R.ρ t ≠ 1 := by
    intro h
    rcases hz.ker t h with h1 | h1
    · rw [h1] at ht2; simp at ht2
    · exact htz (h1 ▸ hzZ)
  have hct : (R.ρ t).cycleType = {2, 2, 2, 2} := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hrep := Perm.cycleType_of_pow_prime_eq_one hσ2
    obtain ⟨j, hj⟩ : ∃ j, (R.ρ t).cycleType = Multiset.replicate j 2 := ⟨_, hrep⟩
    have hsum := Perm.sum_cycleType (R.ρ t)
    rw [hj, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hsupp : (R.ρ t).support.card ≤ m + 1 := by
      simpa using Finset.card_le_univ (R.ρ t).support
    have hj5 : j ≤ 5 := by omega
    have hsgn := Perm.sign_of_cycleType (R.ρ t)
    rw [hj, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, hσsign] at hsgn
    interval_cases j
    · exfalso
      apply hσne
      exact Perm.cycleType_eq_zero.mp (by rw [hj]; rfl)
    · exfalso
      revert hsgn
      decide
    · exfalso
      have hcy : (R.ρ t).cycleType = {2, 2} := by rw [hj]; rfl
      have := hz.sq_double (by omega) hcy
      rw [ht_sq] at this
      exact hz.ne_one this.symm
    · exfalso
      revert hsgn
      decide
    · rw [hj]; rfl
    · exfalso
      revert hsgn
      decide
  obtain ⟨g, hgA, hg⟩ := exists_conj_tb m h7 h10 (R.ρ t) hct
  have hgs : Perm.sign g = 1 := Perm.mem_alternatingGroup.mp hgA
  obtain ⟨a0, ha0⟩ := R.lift_even hgs
  have ha0K : a0 ∈ K := R.mem_K_of_sign a0 (by rw [ha0]; exact hgs)
  have hρt' : R.ρ (a0 * t * a0⁻¹) = R.ρ L.t := by
    rw [map_mul, map_mul, map_inv, ha0, L.rho_t h7 h10]; exact hg
  have hgK : L.g ∈ K :=
    R.mem_K_of_sign L.g (by
      rw [L.hg]; exact PermRep.sign_eq_one_of_cycleType_two_two (ct_sg m h7 h10))
  obtain ⟨a, hat⟩ : ∃ a : ↥K, t = (a : H) * L.t * (a : H)⁻¹ := by
    rcases conj_mem_ker hz hρt' with h | h
    · refine ⟨⟨a0⁻¹, K.inv_mem ha0K⟩, ?_⟩
      show t = a0⁻¹ * L.t * a0⁻¹⁻¹
      rw [← h]; group
    · refine ⟨⟨a0⁻¹ * L.g, K.mul_mem (K.inv_mem ha0K) hgK⟩, ?_⟩
      show t = a0⁻¹ * L.g * L.t * (a0⁻¹ * L.g)⁻¹
      have h2 := L.conj_g_t hz h7 h10
      calc t = a0⁻¹ * (a0 * t * a0⁻¹) * a0 := by group
        _ = a0⁻¹ * (L.g * L.t * L.g⁻¹) * a0 := by rw [h, h2]
        _ = a0⁻¹ * L.g * L.t * (a0⁻¹ * L.g)⁻¹ := by group
  refine ⟨twist R a, z, ⟨L.conj a, twist_kerData hz a, h7, h10⟩, ?_⟩
  show (L.conj a).t = t
  rw [Lifts.conj_t]
  exact hat.symm

end Entry

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
