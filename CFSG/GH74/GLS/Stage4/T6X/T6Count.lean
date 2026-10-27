module

public import CFSG.GH74.GLS.Stage4.T6X.T6Z

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6X

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem t6_isKleinFour {z u : G} (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hne : z ≠ u) : IsKleinFour ↥(t2U z u) := by
  have hmem := fun x : G => t2U_mem hz2 hu2 hzu (x := x)
  have hzu1 : z * u ≠ 1 := by
    intro h
    exact hne (mul_eq_one_iff_eq_inv.1 h |>.trans (inv_eq_of_mul_eq_one_right hu2))
  have hzuz : z * u ≠ z := by
    intro h
    apply hu1
    simpa using h
  have hzuu : z * u ≠ u := by
    intro h
    apply hz1
    simpa using h
  have hset : (t2U z u : Set G) = {1, z, u, z * u} := by
    ext x
    simp only [SetLike.mem_coe, hmem, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hcard : Nat.card ↥(t2U z u) = 4 := by
    have h1 : Nat.card ↥(t2U z u) = (t2U z u : Set G).ncard := Nat.card_coe_set_eq (t2U z u : Set G)
    rw [h1, hset]
    have n1 : (1 : G) ∉ ({z, u, z * u} : Set G) := by simp [hz1.symm, hu1.symm, hzu1.symm]
    have n2 : z ∉ ({u, z * u} : Set G) := by simp [hne, hzuz.symm]
    have n3 : u ∉ ({z * u} : Set G) := by simp [hzuu.symm]
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_insert_of_notMem n3,
      Set.ncard_singleton]
  refine ⟨hcard, ?_⟩
  have hsq : ∀ x : ↥(t2U z u), x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    have hx := (hmem x).1 x.2
    show (x : G) ^ 2 = 1
    rcases hx with h | h | h | h <;> rw [h]
    · simp
    · rw [pow_two]; exact hz2
    · rw [pow_two]; exact hu2
    · rw [pow_two]
      calc z * u * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [← hzu]
        _ = (z * z) * (u * u) := by group
        _ = 1 := by rw [hz2, hu2, one_mul]
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with h | h
  · have : Subsingleton ↥(t2U z u) := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : ↥(t2U z u))
    omega
  · exact h

theorem zu_facts {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) :
    N.z * N.z = 1 ∧ u * u = 1 ∧ N.z * u = u * N.z ∧ N.z ≠ 1 ∧ u ≠ 1 ∧ N.z ≠ u := by
  have hu2 : u * u = 1 := by
    have h1 := pow_orderOf_eq_one u
    rw [h.sec5.loc.u_ord, pow_two] at h1
    exact h1
  refine ⟨h.ctx.zz, hu2, h.sec5.loc.u_comm.symm, h.ctx.z_ne, ?_, h.sec5.loc.u_ne.symm⟩
  intro h1
  have := h.sec5.loc.u_ord
  rw [h1, orderOf_one] at this
  omega

theorem U_le_M₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : t2U N.z u ≤ M₂ N := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  intro g hg
  rcases (t2U_mem hz2 hu2 hzu).1 hg with rfl | rfl | rfl | rfl
  · exact (M₂ N).one_mem
  · exact z_mem_M₂ h
  · exact u_mem_M₂ h
  · exact (M₂ N).mul_mem (z_mem_M₂ h) (u_mem_M₂ h)

theorem R₂_inf_cent_z {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) :
    R₂ N p ⊓ Subgroup.centralizer {N.z} = N.X₂ := by
  apply le_antisymm
  · rintro y ⟨hyR, hyz⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 hyz
    refine R₂_Cz h y hyR ?_
    calc N.z * y * N.z⁻¹ = (y * N.z) * N.z⁻¹ := by rw [this]
      _ = y := by group
  · intro x hx
    refine ⟨X₂_le_R₂ h hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hxK : x ∈ N.K₂ := by rw [h.sec5.loc.K₂_eq]; exact Subgroup.mem_sup_left hx
    exact h.ctx.C.zc₂ x hxK

theorem card_four_decomp {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {K : Subgroup G}
    (hXK : N.X₂ ≤ K) (hKR : K ≤ R₂ N p)
    (hKU : ∀ g ∈ t2U N.z u, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    Nat.card ↥K = N.q₂ * Nat.card ↥(K ⊓ Subgroup.centralizer {u}) *
      Nat.card ↥(K ⊓ Subgroup.centralizer {N.z * u}) := by
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  have := t6_isKleinFour hz2 hu2 hzu hz1 hu1 hne
  have hpg := R₂_pGroup N h.prime
  have hKodd : Odd (Nat.card ↥K) := by
    have : Fact p.Prime := ⟨h.prime⟩
    obtain ⟨k, hk⟩ := ((hpg.to_le hKR : IsPGroup p ↥K)).exists_card_eq
    rw [hk]
    exact (h.prime.odd_of_ne_two h.p_ne_two).pow
  have hTK : t2U N.z u ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype (fun n hn => hKU g hg n hn)
  have hz : N.z ∈ t2U N.z u := Subgroup.subset_closure (by simp)
  have hu : u ∈ t2U N.z u := Subgroup.subset_closure (by simp)
  have hbw := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq hKodd hTK hz hu hz1 hu1 hne
  have hbot : K ⊓ Subgroup.centralizer (t2U N.z u : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxC⟩
    rw [Subgroup.mem_bot]
    have hxz : N.z * x = x * N.z := Subgroup.mem_centralizer_iff.1 hxC N.z hz
    have hxu : u * x = x * u := Subgroup.mem_centralizer_iff.1 hxC u hu
    have hxX : x ∈ N.X₂ := by
      refine R₂_Cz h x (hKR hxK) ?_
      calc N.z * x * N.z⁻¹ = (x * N.z) * N.z⁻¹ := by rw [hxz]
        _ = x := by group
    have h1 := h.sec5.loc.u_inv_X₂ x hxX
    have h2 : u * x * u⁻¹ = x := by
      calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [hxu]
        _ = x := by group
    have h3 : x * x = 1 := by
      have : x = x⁻¹ := by rw [← h1, h2]
      calc x * x = x * x⁻¹ := by rw [← this]
        _ = 1 := by group
    have hodd := t6_odd_of_pGroup h.prime h.p_ne_two hpg (hKR hxK)
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
    · exact orderOf_eq_one_iff.1 h4
    · rw [h4] at hodd; exact absurd hodd (by decide)
  have hKz : K ⊓ Subgroup.centralizer {N.z} = N.X₂ := by
    apply le_antisymm
    · rintro y ⟨hyK, hyz⟩
      have hyR : y ∈ R₂ N p ⊓ Subgroup.centralizer {N.z} := ⟨hKR hyK, hyz⟩
      rwa [R₂_inf_cent_z h] at hyR
    · intro x hx
      refine ⟨hXK hx, ?_⟩
      have hxR : x ∈ R₂ N p ⊓ Subgroup.centralizer {N.z} := by rw [R₂_inf_cent_z h]; exact hx
      exact hxR.2
  rw [hbot, hKz, Subgroup.card_bot, h.sec5.loc.card_X₂] at hbw
  simpa using hbw

omit [Finite G] in
theorem t6_card_cent_conj {R : Subgroup G} {w : G} (hR : ∀ r ∈ R, w * r * w⁻¹ ∈ R)
    (hR' : ∀ r ∈ R, w⁻¹ * r * w ∈ R) (a : G) :
    Nat.card ↥(R ⊓ Subgroup.centralizer {a}) = Nat.card ↥(R ⊓ Subgroup.centralizer {w * a * w⁻¹}) := by
  have hmap : (R ⊓ Subgroup.centralizer {a}).map (MulAut.conj w).toMonoidHom =
      R ⊓ Subgroup.centralizer {w * a * w⁻¹} := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, ⟨hyR, hya⟩, rfl⟩
      refine ⟨hR y hyR, ?_⟩
      show (w * y * w⁻¹) * (w * a * w⁻¹) = (w * a * w⁻¹) * (w * y * w⁻¹)
      calc (w * y * w⁻¹) * (w * a * w⁻¹) = w * (y * a) * w⁻¹ := by group
        _ = w * (a * y) * w⁻¹ := by rw [hya]
        _ = (w * a * w⁻¹) * (w * y * w⁻¹) := by group
    · rintro ⟨hxR, hxa⟩
      refine ⟨w⁻¹ * x * w, ⟨hR' x hxR, ?_⟩, ?_⟩
      · have : (w⁻¹ * x * w) * a = a * (w⁻¹ * x * w) := by
          calc (w⁻¹ * x * w) * a = w⁻¹ * (x * (w * a * w⁻¹)) * w := by group
            _ = w⁻¹ * ((w * a * w⁻¹) * x) * w := by rw [hxa]
            _ = a * (w⁻¹ * x * w) := by group
        exact this
      · show w * (w⁻¹ * x * w) * w⁻¹ = x
        group
  rw [← hmap]
  exact (Subgroup.card_map_of_injective (MulAut.conj w).injective).symm

end CFSG.GH74.GLS.Stage4.Rest.T6X
