module

public import CFSG.GH74.GLS.IVK.Lifted.Alt51Idx
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol
public import CFSG.GH74.Uniqueness.SU.SU13TA1Basic

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Equiv CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.Uniqueness.SU.SU13.TA

structure PermRep {H : Type} [Group H] (K : Subgroup H) (n : ℕ) where
  π : ↥K →* alternatingGroup (Fin n)
  ρ : H →* Perm (Fin n)
  cover : TwoCover π
  ρ_K : ∀ k : ↥K, ρ (k : H) = ((π k : alternatingGroup (Fin n)) : Perm (Fin n))
  ker_ρ : ∀ x : H, ρ x = 1 → ∃ k : ↥K, (k : H) = x ∧ π k = 1

section Construction

variable {H : Type} [Group H] [Finite H]

theorem exists_permRep {K : Subgroup H} {n : ℕ} (hH : Hyp5B H K n) : Nonempty (PermRep K n) := by
  classical
  have hn5 : 5 ≤ n := by have := hH.n_ge; omega
  have hn6 : n ≠ 6 := by have := hH.n_ge; omega
  obtain ⟨hKq, hZ, ⟨e⟩⟩ := hH.cover
  have hKn : K.Normal := hH.normal
  have hperf : commutator ↥K = ⊤ := by
    have := hKq.1
    exact Group.IsPerfect.commutator_eq_top
  let π : ↥K →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥K))
  have hker : π.ker = center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e ((QuotientGroup.mk' (center ↥K)) x) = 1 := hx
      exact (QuotientGroup.eq_one_iff x).mp ((map_eq_one_iff e e.injective).mp h1)
    · intro hx
      have h1 : (QuotientGroup.mk' (center ↥K)) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show e ((QuotientGroup.mk' (center ↥K)) x) = 1
      rw [h1, map_one]
  have hπ : TwoCover π :=
    ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, by rw [hker]; exact hZ, hKq.1⟩
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  let c : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hbij
  let ψ : H →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr e).toMonoidHom.comp
      ((autQuotCenter ↥K).comp (MulAut.conjNormal : H →* MulAut ↥K))
  let ρ : H →* Perm (Fin n) := c.symm.toMonoidHom.comp ψ
  have hρψ : ∀ h : H, MulAut.conjNormal (ρ h) = ψ h := fun h => c.apply_symm_apply (ψ h)
  have hψπ : ∀ (h : H) (k : ↥K), ψ h (π k) = π (MulAut.conjNormal h k) := by
    intro h k
    show (MulAut.congr e) (autQuotCenter ↥K (MulAut.conjNormal h)) (e (QuotientGroup.mk k)) =
      e (QuotientGroup.mk (MulAut.conjNormal h k))
    rw [MulAut.congr_apply]
    simp [autQuotCenter_mk]
  have hρK : ∀ k : ↥K, ρ (k : H) = ((π k : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro k
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
    rw [hρψ]
    refine MulEquiv.ext (fun a => ?_)
    obtain ⟨k', rfl⟩ := hπ.surj a
    rw [hψπ]
    have h1 : MulAut.conjNormal (k : H) k' = k * k' * k⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    rw [h1, map_mul, map_mul, map_inv]
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
  have hker_ρ : ∀ x : H, ρ x = 1 → ∃ k : ↥K, (k : H) = x ∧ π k = 1 := by
    intro x hx
    have hψ1 : ψ x = 1 := by rw [← hρψ, hx, map_one]
    have hθ : autQuotCenter ↥K (MulAut.conjNormal x) = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one]
      exact hψ1
    obtain ⟨k, hk, rfl⟩ := exists_central_of_autQuot_eq_one hperf hH.cent hθ
    exact ⟨k, rfl, by rw [← MonoidHom.mem_ker, hker]; exact hk⟩
  exact ⟨⟨π, ρ, hπ, hρK, hker_ρ⟩⟩

end Construction

section Main

variable {H : Type} [Group H] {K : Subgroup H} {n : ℕ}

namespace PermRep

theorem sign_of_mem_K (R : PermRep K n) (k : H) (hk : k ∈ K) : Perm.sign (R.ρ k) = 1 := by
  have h := R.ρ_K ⟨k, hk⟩
  rw [show ((⟨k, hk⟩ : ↥K) : H) = k from rfl] at h
  rw [h]
  exact Perm.mem_alternatingGroup.mp (R.π ⟨k, hk⟩).2

theorem mem_K_of_sign (R : PermRep K n) (x : H) (hx : Perm.sign (R.ρ x) = 1) : x ∈ K := by
  obtain ⟨k, hk⟩ := R.cover.surj ⟨R.ρ x, Perm.mem_alternatingGroup.2 hx⟩
  have hk' : R.ρ (k : H) = R.ρ x := by rw [R.ρ_K, hk]
  obtain ⟨k₀, hk₀, -⟩ := R.ker_ρ ((k : H)⁻¹ * x)
    (by rw [map_mul, map_inv, hk']; exact inv_mul_cancel _)
  have : x = (k : H) * k₀ := by rw [hk₀]; group
  rw [this]
  exact K.mul_mem k.2 k₀.2

end PermRep

theorem exists_involution_of_permRep (hn : 8 ≤ n) (R : PermRep K n) {h₀ : H} (hh₀ : h₀ ∉ K) :
    ∃ h : H, h ∉ K ∧ orderOf h = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzc, hz1, hz2, hzk⟩ := R.cover.exists_z
  have hzker : z ∈ R.π.ker := by
    have hne : R.π.ker ≠ ⊥ := by
      intro h
      have := R.cover.card_ker
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    rcases hzk (a : ↥K) a.2 with h1 | h1
    · exact absurd (Subtype.ext h1) ha
    · rw [← h1]
      exact a.2
  have hρz : R.ρ (z : H) = 1 := by
    rw [R.ρ_K]
    have : R.π z = 1 := hzker
    rw [this]
    rfl
  have hker2 : ∀ x : H, R.ρ x = 1 → x = 1 ∨ x = (z : H) := by
    intro x hx
    obtain ⟨k, rfl, hk⟩ := R.ker_ρ x hx
    rcases hzk k hk with h1 | h1
    · left
      rw [h1]
      rfl
    · right
      rw [h1]
  have hzH1 : (z : H) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzcen : ∀ g : H, g * (z : H) = (z : H) * g := by
    intro g
    have h1 : R.ρ (g * (z : H) * g⁻¹) = 1 := by
      rw [map_mul, map_mul, hρz, mul_one, map_inv, mul_inv_cancel]
    rcases hker2 _ h1 with h | h
    · exfalso
      apply hzH1
      have : (z : H) = g⁻¹ * (g * (z : H) * g⁻¹) * g := by group
      rw [this, h]
      group
    · calc g * (z : H) = (g * (z : H) * g⁻¹) * g := by group
        _ = (z : H) * g := by rw [h]
  have hzsq : (z : H) * (z : H) = 1 := by
    have := congrArg Subtype.val (show z * z = 1 by rw [← pow_two]; exact hz2)
    simpa using this
  have hnotK : ∀ (h : H) (a b : Fin n), a ≠ b → R.ρ h = swap a b → h ∉ K := by
    intro h a b hab hρ hK
    have := R.sign_of_mem_K h hK
    rw [hρ, Perm.sign_swap hab] at this
    exact absurd this (by decide)
  have hodd : Perm.sign (R.ρ h₀) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (R.ρ h₀)) with h | h
    · exact absurd (R.mem_K_of_sign h₀ h) hh₀
    · exact h
  have hsurj : Function.Surjective R.ρ := by
    intro σ
    rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
    · obtain ⟨k, hk⟩ := R.cover.surj ⟨σ, Perm.mem_alternatingGroup.2 h1⟩
      exact ⟨k, by rw [R.ρ_K, hk]⟩
    · have h2 : Perm.sign (σ * (R.ρ h₀)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, hodd]
        decide
      obtain ⟨k, hk⟩ := R.cover.surj ⟨σ * (R.ρ h₀)⁻¹, Perm.mem_alternatingGroup.2 h2⟩
      refine ⟨k * h₀, ?_⟩
      rw [map_mul, R.ρ_K, hk]
      group
  have dsq : ∀ (u v : H) (a b c d : Fin n), [a, b, c, d].Nodup → R.ρ u = swap a b →
      R.ρ v = swap c d → (u * v) * (u * v) = (z : H) := by
    intro u v a b c d hnd hu hv
    have hab : a ≠ b := by
      intro h
      simp [h] at hnd
    have hcd : c ≠ d := by
      intro h
      simp [h] at hnd
    have hw : u * v ∈ K := R.mem_K_of_sign _ (by
      rw [map_mul, hu, hv, map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      decide)
    have hcyc : ((R.π ⟨u * v, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType =
        {2, 2} := by
      rw [← R.ρ_K ⟨u * v, hw⟩]
      show (R.ρ (u * v)).cycleType = {2, 2}
      rw [map_mul, hu, hv]
      exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd
    obtain ⟨hsqk, hsq1⟩ := R.cover.sq_mem_ker_ne_one_of_cycleType_two_two (by omega) hcyc
    rcases hzk _ hsqk with h | h
    · exact absurd h hsq1
    · have := congrArg Subtype.val h
      simpa [pow_two] using this
  have anti : ∀ (u v : H) (a b c d : Fin n), [a, b, c, d].Nodup → R.ρ u = swap a b →
      R.ρ v = swap c d → u * u = (z : H) → v * v = (z : H) → u⁻¹ * v * u = (z : H) * v := by
    intro u v a b c d hnd hu hv hu2 hv2
    have hww := dsq u v a b c d hnd hu hv
    have hcomm : R.ρ (u⁻¹ * v * u * v⁻¹) = 1 := by
      have hc : Commute (swap a b) (swap c d) := (Equiv.Perm.disjoint_swap_swap hnd).commute
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu, hv, swap_inv, swap_inv]
      calc swap a b * swap c d * swap a b * swap c d = (swap a b * swap c d) * (swap a b * swap c d) := by
            rw [mul_assoc]
        _ = (swap a b * swap a b) * (swap c d * swap c d) := by
            rw [mul_assoc, ← mul_assoc (swap c d) (swap a b) (swap c d), ← hc.eq, mul_assoc, mul_assoc]
        _ = 1 := by rw [swap_mul_self, swap_mul_self, mul_one]
    have hkv : u⁻¹ * v * u = (u⁻¹ * v * u * v⁻¹) * v := by group
    have hexp : (u * v) * (u * v) = (u * u) * (u⁻¹ * v * u * v⁻¹) * (v * v) := by
      calc (u * v) * (u * v) = u * (u * (u⁻¹ * v * u)) * v := by group
        _ = u * (u * ((u⁻¹ * v * u * v⁻¹) * v)) * v := by rw [← hkv]
        _ = (u * u) * (u⁻¹ * v * u * v⁻¹) * (v * v) := by group
    rcases hker2 _ hcomm with hk | hk
    · exfalso
      rw [hk, hu2, hv2, mul_one, hzsq] at hexp
      rw [hww] at hexp
      exact hzH1 hexp
    · rw [hkv, hk]
  obtain ⟨p, hp⟩ : ∃ p : Fin 8 → Fin n, Function.Injective p :=
    ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩
  have hne : ∀ i j : Fin 8, i ≠ j → p i ≠ p j := fun i j h => hp.ne h
  obtain ⟨h₁, hh₁⟩ := hsurj (swap (p 0) (p 1))
  have hh₁K : h₁ ∉ K := hnotK h₁ _ _ (hne 0 1 (by decide)) hh₁
  have hh₁1 : h₁ ≠ 1 := fun h => hh₁K (h ▸ K.one_mem)
  by_cases hsq : h₁ * h₁ = 1
  · exact ⟨h₁, hh₁K, orderOf_eq_prime (by rw [pow_two]; exact hsq) hh₁1⟩
  have h1sq : h₁ * h₁ = (z : H) := by
    rcases hker2 (h₁ * h₁) (by rw [map_mul, hh₁]; exact swap_mul_self _ _) with h | h
    · exact absurd h hsq
    · exact h
  obtain ⟨g₂, hg₂⟩ := hsurj (swap (p 0) (p 2) * swap (p 1) (p 3))
  obtain ⟨g₃, hg₃⟩ := hsurj (swap (p 0) (p 4) * swap (p 1) (p 5))
  have hσ₂0 : (swap (p 0) (p 2) * swap (p 1) (p 3)) (p 0) = p 2 := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne 0 1 (by decide)) (hne 0 3 (by decide)),
      swap_apply_left]
  have hσ₂1 : (swap (p 0) (p 2) * swap (p 1) (p 3)) (p 1) = p 3 := by
    rw [Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (hne 3 0 (by decide)) (hne 3 2 (by decide))]
  have hσ₃0 : (swap (p 0) (p 4) * swap (p 1) (p 5)) (p 0) = p 4 := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne 0 1 (by decide)) (hne 0 5 (by decide)),
      swap_apply_left]
  have hσ₃1 : (swap (p 0) (p 4) * swap (p 1) (p 5)) (p 1) = p 5 := by
    rw [Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (hne 5 0 (by decide)) (hne 5 4 (by decide))]
  have hρ₂ : R.ρ (g₂ * h₁ * g₂⁻¹) = swap (p 2) (p 3) := by
    rw [map_mul, map_mul, map_inv, hg₂, hh₁, ← swap_apply_apply, hσ₂0, hσ₂1]
  have hρ₃ : R.ρ (g₃ * h₁ * g₃⁻¹) = swap (p 4) (p 5) := by
    rw [map_mul, map_mul, map_inv, hg₃, hh₁, ← swap_apply_apply, hσ₃0, hσ₃1]
  have hsq₂ : (g₂ * h₁ * g₂⁻¹) * (g₂ * h₁ * g₂⁻¹) = (z : H) := by
    calc (g₂ * h₁ * g₂⁻¹) * (g₂ * h₁ * g₂⁻¹) = g₂ * (h₁ * h₁) * g₂⁻¹ := by group
      _ = g₂ * (z : H) * g₂⁻¹ := by rw [h1sq]
      _ = (z : H) := by rw [hzcen g₂]; group
  have hsq₃ : (g₃ * h₁ * g₃⁻¹) * (g₃ * h₁ * g₃⁻¹) = (z : H) := by
    calc (g₃ * h₁ * g₃⁻¹) * (g₃ * h₁ * g₃⁻¹) = g₃ * (h₁ * h₁) * g₃⁻¹ := by group
      _ = g₃ * (z : H) * g₃⁻¹ := by rw [h1sq]
      _ = (z : H) := by rw [hzcen g₃]; group
  set h₂ : H := g₂ * h₁ * g₂⁻¹ with hh₂
  set h₃ : H := g₃ * h₁ * g₃⁻¹ with hh₃
  have hnd12 : [p 0, p 1, p 2, p 3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact ⟨⟨hne 0 1 (by decide), hne 0 2 (by decide), hne 0 3 (by decide)⟩,
      ⟨hne 1 2 (by decide), hne 1 3 (by decide)⟩, hne 2 3 (by decide)⟩
  have hnd13 : [p 0, p 1, p 4, p 5].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact ⟨⟨hne 0 1 (by decide), hne 0 4 (by decide), hne 0 5 (by decide)⟩,
      ⟨hne 1 4 (by decide), hne 1 5 (by decide)⟩, hne 4 5 (by decide)⟩
  have hnd23 : [p 2, p 3, p 4, p 5].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact ⟨⟨hne 2 3 (by decide), hne 2 4 (by decide), hne 2 5 (by decide)⟩,
      ⟨hne 3 4 (by decide), hne 3 5 (by decide)⟩, hne 4 5 (by decide)⟩
  have h12 : h₁⁻¹ * h₂ * h₁ = (z : H) * h₂ := anti h₁ h₂ _ _ _ _ hnd12 hh₁ hρ₂ h1sq hsq₂
  have h13 : h₁⁻¹ * h₃ * h₁ = (z : H) * h₃ := anti h₁ h₃ _ _ _ _ hnd13 hh₁ hρ₃ h1sq hsq₃
  have hmsq : (h₂ * h₃) * (h₂ * h₃) = (z : H) := dsq h₂ h₃ _ _ _ _ hnd23 hρ₂ hρ₃
  have hcm : h₁ * (h₂ * h₃) = (h₂ * h₃) * h₁ := by
    have h1 : h₁⁻¹ * (h₂ * h₃) * h₁ = h₂ * h₃ := by
      calc h₁⁻¹ * (h₂ * h₃) * h₁ = (h₁⁻¹ * h₂ * h₁) * (h₁⁻¹ * h₃ * h₁) := by group
        _ = ((z : H) * h₂) * ((z : H) * h₃) := by rw [h12, h13]
        _ = ((z : H) * (z : H)) * (h₂ * h₃) := by
          calc ((z : H) * h₂) * ((z : H) * h₃) = (z : H) * (h₂ * (z : H)) * h₃ := by group
            _ = (z : H) * ((z : H) * h₂) * h₃ := by rw [← hzcen h₂]
            _ = ((z : H) * (z : H)) * (h₂ * h₃) := by group
        _ = h₂ * h₃ := by rw [hzsq, one_mul]
    calc h₁ * (h₂ * h₃) = h₁ * (h₁⁻¹ * (h₂ * h₃) * h₁) := by rw [h1]
      _ = (h₂ * h₃) * h₁ := by group
  have hnK : h₁ * (h₂ * h₃) ∉ K := by
    intro hK
    have h1 := R.sign_of_mem_K _ hK
    simp only [map_mul, hh₁, hρ₂, hρ₃, Perm.sign_swap (hne 0 1 (by decide)),
      Perm.sign_swap (hne 2 3 (by decide)), Perm.sign_swap (hne 4 5 (by decide))] at h1
    exact absurd h1 (by decide)
  refine ⟨h₁ * (h₂ * h₃), hnK, orderOf_eq_prime ?_ (fun h1 => hnK (h1 ▸ K.one_mem))⟩
  calc (h₁ * (h₂ * h₃)) ^ 2 = h₁ * (h₂ * h₃) * (h₁ * (h₂ * h₃)) := by rw [pow_two]
    _ = h₁ * ((h₂ * h₃) * h₁) * (h₂ * h₃) := by group
    _ = h₁ * (h₁ * (h₂ * h₃)) * (h₂ * h₃) := by rw [← hcm]
    _ = (h₁ * h₁) * ((h₂ * h₃) * (h₂ * h₃)) := by group
    _ = 1 := by rw [h1sq, hmsq, hzsq]

end Main

theorem ivk_5_1d : IVK_5_1d := by
  intro H _ _ K n hH hidx
  obtain ⟨R⟩ := exists_permRep hH
  have : ∃ h₀ : H, h₀ ∉ K := by
    by_contra h
    push Not at h
    have hK : K = ⊤ := eq_top_iff.2 (fun x _ => h x)
    rw [hK, Subgroup.index_top] at hidx
    omega
  obtain ⟨h₀, hh₀⟩ := this
  exact exists_involution_of_permRep hH.n_ge R hh₀

end CFSG.GH74.GLS.IVK.Lifted
