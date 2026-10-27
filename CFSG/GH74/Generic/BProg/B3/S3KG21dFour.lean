module

public import CFSG.GH74.Generic.BProg.B3.S3KG21dPGL
public import CFSG.GH74.Generic.BProg.B3.S3KG21dDesc
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension

public section

namespace CFSG.GH74.Generic.BProg.B3.S3KG

open Matrix Subgroup CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

theorem eq_of_mul_self_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {a b : C}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite C
  by_contra hab
  have hcard := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) two_pos
  have hsub : ({1, a, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [sq, ha, hb]
  have h3 : ({1, a, b} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

theorem exists_ne_ne_one {G : Type*} [Group G] [Finite G] (h : 4 ≤ Nat.card G) :
    ∃ a b : G, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have := Fintype.ofFinite G
  by_contra hcon
  push Not at hcon
  rw [Nat.card_eq_fintype_card] at h
  by_cases hex : ∃ a : G, a ≠ 1
  · obtain ⟨a, ha⟩ := hex
    have hsub : (Finset.univ : Finset G) ⊆ {1, a} := by
      intro x _
      by_cases hx : x = 1
      · simp [hx]
      · simp [hcon x a hx ha]
    have := Finset.card_le_card hsub
    have h2 := Finset.card_le_two (a := (1 : G)) (b := a)
    rw [Finset.card_univ] at this
    omega
  · push Not at hex
    have : Fintype.card G ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun x y => by rw [hex x, hex y]
    omega

theorem isCyclic_ringAut : IsCyclic (F ≃+* F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hcardN : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨σ, -, -, htop, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      n.pos hcardN
  exact ⟨σ, fun x => by rw [← Subgroup.mem_zpowers_iff, htop]; exact Subgroup.mem_top x⟩

theorem finite_pGammaL2 : Finite (PGammaL2 F) := by
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective
  have : Finite (PGL2 F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F → PGL2 F)
      Matrix.ProjGenLinGroup.mk_surjective
  exact Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right))
    fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

omit [Finite F] in
theorem mul_left_of_right_eq_one {a b : PGammaL2 F} (ha : a.right = 1) :
    (a * b).left = a.left * b.left := by
  rw [SemidirectProduct.mul_left, ha, map_one, MulAut.one_apply]

theorem exists_mem_psl (hF : ringChar F ≠ 2) (U : Subgroup (PGammaL2 F))
    (hU : ∀ u ∈ U, u * u = 1) (h4 : 4 ≤ Nat.card U) :
    ∃ u ∈ U, u ≠ 1 ∧ u.right = 1 ∧ u.left ∈ pslRange F := by
  classical
  have : IsCyclic (F ≃+* F) := isCyclic_ringAut
  have : Finite (PGammaL2 F) := finite_pGammaL2
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective
  have hidx := pgl2_psl2Range_index_eq_two F (isOddPrimePower_card hF)
  by_contra hcon
  push Not at hcon
  have hinv : ∀ u ∈ U, u.right * u.right = 1 := fun u hu => by
    have h := congrArg SemidirectProduct.right (hU u hu)
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at h
  obtain ⟨a, b, ha1, hb1, hab⟩ := exists_ne_ne_one h4
  have hab1 : (a : PGammaL2 F) * b ≠ 1 := by
    intro h
    apply hab
    have hb := hU b b.2
    apply Subtype.ext
    calc (a : PGammaL2 F) = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := (mul_assoc _ _ _).symm
      _ = b := by rw [h, one_mul]
  have ha1' : (a : PGammaL2 F) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : PGammaL2 F) ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨u₁, hu₁U, hu₁1, hu₁r⟩ : ∃ u₁ ∈ U, u₁ ≠ 1 ∧ u₁.right = 1 := by
    by_cases har : (a : PGammaL2 F).right = 1
    · exact ⟨a, a.2, ha1', har⟩
    by_cases hbr : (b : PGammaL2 F).right = 1
    · exact ⟨b, b.2, hb1', hbr⟩
    refine ⟨a * b, mul_mem a.2 b.2, hab1, ?_⟩
    rw [SemidirectProduct.mul_right,
      eq_of_mul_self_of_isCyclic (hinv a a.2) (hinv b b.2) har hbr, hinv b b.2]
  have hu₁H := hcon u₁ hu₁U hu₁1 hu₁r
  by_cases hall : ∀ u ∈ U, u.right = 1
  ·
    have haH := hcon a a.2 ha1' (hall a a.2)
    have hbH := hcon b b.2 hb1' (hall b b.2)
    apply hcon (a * b) (mul_mem a.2 b.2) hab1
    · rw [SemidirectProduct.mul_right, hall a a.2, hall b b.2, one_mul]
    · rw [mul_left_of_right_eq_one (hall a a.2), Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false haH hbH
  push Not at hall
  obtain ⟨u₂, hu₂U, hu₂r⟩ := hall
  have key : ∃ w ∈ U, w.right ≠ 1 ∧ w.left ∉ pslRange F := by
    by_cases hu₂H : u₂.left ∈ pslRange F
    · refine ⟨u₁ * u₂, mul_mem hu₁U hu₂U, ?_, ?_⟩
      · rw [SemidirectProduct.mul_right, hu₁r, one_mul]
        exact hu₂r
      · rw [mul_left_of_right_eq_one hu₁r, Subgroup.mul_mem_iff_of_index_two hidx]
        exact fun h => hu₁H (h.mpr hu₂H)
    · exact ⟨u₂, hu₂U, hu₂r, hu₂H⟩
  obtain ⟨w, hwU, hwr, hwH⟩ := key
  exact hwH (left_mem_of_mul_self hF (hU w hwU) hwr)

theorem exists_inner_of_three_lt (hF : ringChar F ≠ 2) (h3 : 3 < Nat.card F)
    (V : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 2) F))) (hV : ∀ v ∈ V, v * v = 1)
    (h4 : 4 ≤ Nat.card V) :
    ∃ v ∈ V, v ≠ 1 ∧ ∃ s : Matrix.SpecialLinearGroup (Fin 2) F, v = MulAut.conj s := by
  have : Fintype F := Fintype.ofFinite F
  have hK := isOddPrimePower_card hF
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  have hKcard : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hsurj := pGammaL2ToMulAutPSL2_surjective F hKcard hK h3
  set Φ := pGammaL2EquivMulAutPSL2 F hK h3 hsurj with hΦ
  let ψ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) →* PGammaL2 F :=
    Φ.symm.toMonoidHom.comp descend
  have hψ : Function.Injective ψ := Φ.symm.injective.comp (descend_injective hF)
  have hU : ∀ u ∈ V.map ψ, u * u = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, hV v hv, map_one]
  have hU4 : 4 ≤ Nat.card (V.map ψ) := by rw [Subgroup.card_map_of_injective hψ]; exact h4
  obtain ⟨_, ⟨v, hv, rfl⟩, hu1, hur, y, hy⟩ := exists_mem_psl hF (V.map ψ) hU hU4
  refine ⟨v, hv, fun h => hu1 (by rw [h, map_one]), ?_⟩
  apply exists_conj_of_descend hF (x := y)
  have h1 : ψ v = SemidirectProduct.inl (ψ v).left :=
    SemidirectProduct.ext rfl (by rw [SemidirectProduct.right_inl]; exact hur)
  have h2 : pGammaL2ToMulAutPSL2 F hK h3 (ψ v) = descend v := Φ.apply_symm_apply (descend v)
  rw [← h2, h1, pGammaL2ToMulAutPSL2_inl, ← hy, pgl2InnerAutPSL2_toPGL]

end CFSG.GH74.Generic.BProg.B3.S3KG
