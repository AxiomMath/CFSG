module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralRotationInvolutionStructure

public section

namespace CFSG.Semidihedral.Principal

open CFSG.GorensteinWalter

theorem dihedral_subgroup_shapes {S : Type*} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* S)) :
    (∀ T : Subgroup S, IsCyclic T ∨
      ∃ m : ℕ, 2 ≤ m ∧ m ≤ n ∧ Nonempty (T ≃* DihedralGroup (2 ^ (m - 1)))) ∧
    ∀ E : Subgroup S, (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 4 := by
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  have : Finite S := Finite.of_equiv _ hS.some.toEquiv
  obtain ⟨⟨r, s, hr, hs, hrel, hgen⟩, hall⟩ := dihedral_rotation_involution_structure hn hS
  obtain ⟨-, hAindex, -, ⟨-, hzord, hzuniq⟩, hinvol, -, -, -, hcentx, -⟩ :=
    hall r s hr hs hrel hgen
  have hinv : ∀ x : S, x ∉ Subgroup.zpowers r → ∀ a ∈ Subgroup.zpowers r,
      x * a * x⁻¹ = a⁻¹ := by
    intro x hx a ha
    have hxa : x * a ∉ Subgroup.zpowers r := fun h => hx (by
      simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ ha))
    have h1 : (x * a) * (x * a) = 1 := by
      rw [← pow_two, ← hinvol _ hxa, pow_orderOf_eq_one]
    have hx2 : x * x = 1 := by rw [← pow_two, ← hinvol _ hx, pow_orderOf_eq_one]
    rw [inv_eq_of_mul_eq_one_right hx2]
    calc x * a * x = x * a * x * (a * a⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = ((x * a) * (x * a)) * a⁻¹ := by group
      _ = a⁻¹ := by rw [h1, one_mul]
  refine ⟨fun T => ?_, fun E hE => ?_⟩
  · by_cases hTA : T ≤ Subgroup.zpowers r
    · exact Or.inl (Subgroup.isCyclic_of_le hTA)
    obtain ⟨x, hxT, hxA⟩ : ∃ x ∈ T, x ∉ Subgroup.zpowers r := by
      by_contra h
      push Not at h
      exact hTA h
    have hBcyc : IsCyclic ((Subgroup.zpowers r).subgroupOf T) :=
      isCyclic_of_injective
        ((T.subtype.comp ((Subgroup.zpowers r).subgroupOf T).subtype).codRestrict
          (Subgroup.zpowers r) fun w => w.2) (fun a b hab => by
          have h := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext h))
    obtain ⟨g, hg⟩ := hBcyc.exists_generator
    have hmem : ∀ w : T, w ∈ Subgroup.zpowers (g : T) ↔ (w : S) ∈ Subgroup.zpowers r := by
      intro w
      constructor
      · intro hw
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact Subgroup.mem_subgroupOf.mp (Subgroup.zpow_mem _ g.2 k)
      · intro hw
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, Subgroup.mem_subgroupOf.mpr hw⟩)
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
    let σ : T := ⟨x, hxT⟩
    have hσA : σ ∉ Subgroup.zpowers (g : T) := fun h => hxA ((hmem σ).mp h)
    have hgen' : (⊤ : Subgroup T) = Subgroup.zpowers (g : T) ⊔ Subgroup.zpowers σ := by
      refine (eq_top_iff.mpr fun w _ => ?_).symm
      by_cases hw : (w : S) ∈ Subgroup.zpowers r
      · exact Subgroup.mem_sup_left ((hmem w).mpr hw)
      · have hwx : w * σ⁻¹ ∈ Subgroup.zpowers (g : T) :=
          (hmem _).mpr ((Subgroup.mul_mem_iff_of_index_two hAindex).mpr (by simp [σ, hw, hxA]))
        rw [show w = (w * σ⁻¹) * σ by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwx)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
    have hx2 : x ^ 2 = 1 := (hinvol x hxA) ▸ pow_orderOf_eq_one x
    have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simp [σ, hx2])
    have hbA : ((g : T) : S) ∈ Subgroup.zpowers r := (hmem _).mp (Subgroup.mem_zpowers _)
    have hrel' : σ * (g : T) * σ⁻¹ = (g : T)⁻¹ :=
      Subtype.ext (by simpa [σ] using hinv x hxA _ hbA)
    have he := dihedral_of_generators_of_not_mem (g : T) σ hgen' hσ2 hrel' hσA
    have hbdvd : orderOf (g : T) ∣ 2 ^ (n - 1) := by
      rw [← Subgroup.orderOf_coe, ← hr]
      exact orderOf_dvd_of_mem_zpowers hbA
    obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hbdvd
    rw [hbj] at he
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero] at he
      exact Or.inl ((MulEquiv.isCyclic he.some).mpr (DihedralGroup.isCyclic_iff.mpr rfl))
    · exact Or.inr ⟨j + 1, by omega, by omega, by simpa using he⟩
  ·
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hE a ha])
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hE b hb])
      have hab' : (a * b)⁻¹ = a * b :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two, hE _ (E.mul_mem ha hb)])
      rw [← hab', mul_inv_rev, ha', hb']
    by_cases hEA : E ≤ Subgroup.zpowers r
    · have hEz : E ≤ Subgroup.zpowers (r ^ 2 ^ (n - 2)) := by
        intro a ha
        by_cases ha1 : a = 1
        · rw [ha1]
          exact Subgroup.one_mem _
        · rw [hzuniq a (hEA ha) (orderOf_eq_prime (hE a ha) ha1)]
          exact Subgroup.mem_zpowers _
      calc Nat.card E ≤ Nat.card (Subgroup.zpowers (r ^ 2 ^ (n - 2))) := Subgroup.card_le_of_le hEz
        _ = 2 := by rw [Nat.card_zpowers, hzord]
        _ ≤ 4 := by norm_num
    · obtain ⟨x, hxE, hxA⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers r := by
        by_contra h
        push Not at h
        exact hEA h
      have hEC : E ≤ Subgroup.centralizer {x} := fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm a ha x hxE)
      obtain ⟨hC, hK4⟩ := hcentx x hxA
      calc Nat.card E ≤ Nat.card (Subgroup.centralizer {x}) := Subgroup.card_le_of_le hEC
        _ = 4 := by rw [hC]; exact hK4.card_four

theorem sylow_dihedral_two_subgroup_shapes {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {n : ℕ} (hn : 2 ≤ n) (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup G))) :
    (∀ T : Subgroup G, IsPGroup 2 T → IsCyclic T ∨
      ∃ m : ℕ, 2 ≤ m ∧ m ≤ n ∧ Nonempty (T ≃* DihedralGroup (2 ^ (m - 1)))) ∧
    (∀ E : Subgroup G, (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 4) ∧
    ¬ ∃ E : Subgroup G, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 8 := by
  obtain ⟨e₀⟩ := hS
  have hP : ∀ P : Sylow 2 G, Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (P : Subgroup G)) :=
    fun P => ⟨e₀.trans (Sylow.equiv S P)⟩
  have hE4 : ∀ E : Subgroup G, (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 4 := by
    intro E hE
    have hEp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE g g.2)⟩
    obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
    have h := (dihedral_subgroup_shapes hn (hP P)).2 (E.subgroupOf P)
      (fun x hx => Subtype.ext (by simpa using hE (x : G) hx))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv] at h
  refine ⟨fun T hT => ?_, hE4, fun ⟨E, hE, hcard⟩ => ?_⟩
  · obtain ⟨P, hTP⟩ := hT.exists_le_sylow
    have eT : T.subgroupOf P ≃* T := Subgroup.subgroupOfEquivOfLe hTP
    rcases (dihedral_subgroup_shapes hn (hP P)).1 (T.subgroupOf P) with hc | ⟨m, hm2, hmn, ⟨f⟩⟩
    · exact Or.inl ((MulEquiv.isCyclic eT).mp hc)
    · exact Or.inr ⟨m, hm2, hmn, ⟨eT.symm.trans f⟩⟩
  · have := hE4 E hE
    omega

end CFSG.Semidihedral.Principal
