module

public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace FiveExIn

section Group

variable {G : Type*} [Group G]

theorem card_le_card_fixedPoints_of_sq {A B : Subgroup G} [Finite A] (S : G →* G)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hSA : ∀ y ∈ A, S y ∈ A)
    (hS2 : ∀ y ∈ A, S (S y) = y) (hBA : B ≤ A) (hB2 : ∀ y ∈ B, y * y = 1)
    (hBsq : ∀ y ∈ B, ∃ z ∈ A, z * z = y) :
    Nat.card B ≤ Nat.card (A ⊓ S.eqLocus (MonoidHom.id G) : Subgroup G) := by
  classical
  set C := A ⊓ S.eqLocus (MonoidHom.id G) with hC
  have hmemC : ∀ y : G, y ∈ C ↔ y ∈ A ∧ S y = y := fun y => Iff.rfl
  have : Finite B := Finite.of_injective _ (Subgroup.inclusion_injective hBA)
  have hCA : C ≤ A := inf_le_left
  have : Finite C := Finite.of_injective _ (Subgroup.inclusion_injective hCA)
  let φ : B →* G :=
    { toFun := fun y => (y : G) * S y
      map_one' := by simp
      map_mul' := fun y₁ y₂ => by
        change ((y₁ : G) * y₂) * S ((y₁ : G) * y₂) = ((y₁ : G) * S y₁) * ((y₂ : G) * S y₂)
        rw [map_mul]
        have h := hcomm _ (hBA y₂.2) _ (hSA _ (hBA y₁.2))
        calc (y₁ : G) * y₂ * (S y₁ * S y₂) = y₁ * (y₂ * S y₁) * S y₂ := by group
          _ = y₁ * (S y₁ * y₂) * S y₂ := by rw [h]
          _ = _ := by group }
  let s : C →* G :=
    { toFun := fun y => (y : G) * y
      map_one' := by simp
      map_mul' := fun y₁ y₂ => by
        change ((y₁ : G) * y₂) * ((y₁ : G) * y₂) = ((y₁ : G) * y₁) * ((y₂ : G) * y₂)
        have h := hcomm _ (hCA y₂.2) _ (hCA y₁.2)
        calc (y₁ : G) * y₂ * (y₁ * y₂) = y₁ * (y₂ * y₁) * y₂ := by group
          _ = y₁ * (y₁ * y₂) * y₂ := by rw [h]
          _ = _ := by group }
  have hrange : φ.range ≤ s.range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hzA, hzy⟩ := hBsq y y.2
    have hSz : S z ∈ A := hSA z hzA
    have hw : z * S z ∈ C := by
      refine (hmemC _).2 ⟨A.mul_mem hzA hSz, ?_⟩
      rw [map_mul, hS2 z hzA]
      exact hcomm _ hSz _ hzA
    refine ⟨⟨_, hw⟩, ?_⟩
    change (z * S z) * (z * S z) = (y : G) * S y
    rw [← hzy, map_mul]
    have h := hcomm _ hSz _ hzA
    calc z * S z * (z * S z) = z * (S z * z) * S z := by group
      _ = z * (z * S z) * S z := by rw [h]
      _ = _ := by group
  have hSu : ∀ u : φ.ker, S (u.1 : G) = u.1 := fun u => by
    have h1 : (u.1 : G) * S u.1 = 1 := u.2
    have h2 : (u.1 : G) * u.1 = 1 := hB2 _ u.1.2
    rw [eq_inv_of_mul_eq_one_right h1]
    exact (eq_inv_of_mul_eq_one_left h2).symm
  let ι : φ.ker → s.ker := fun u =>
    ⟨⟨u.1.1, (hmemC _).2 ⟨hBA u.1.2, hSu u⟩⟩, hB2 _ u.1.2⟩
  have hι : Function.Injective ι := fun u v h => by
    have h' := congrArg (fun w : s.ker => ((w : C) : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hker : Nat.card φ.ker ≤ Nat.card s.ker := Nat.card_le_card_of_injective ι hι
  have : Finite s.range := Finite.of_surjective _ s.rangeRestrict_surjective
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have h2 := Subgroup.card_mul_index s.ker
  rw [Subgroup.index_ker] at h2
  have h3 : Nat.card φ.range ≤ Nat.card s.range := Subgroup.card_le_of_le hrange
  calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card s.ker * Nat.card s.range := Nat.mul_le_mul hker h3
    _ = Nat.card C := h2

end Group

section FourDiag

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_pow_eq_one {n : ℕ} {b : Fin τ.rank → Lˣ} (hb : ∀ i, b i ^ n = 1)
    (u : Fin τ.rank → ℤ) : rootChar b u ^ n = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

variable (τ L) in
@[expose] noncomputable def fourDiagGroup : Subgroup (ModGL τ L) :=
  ((rootDiagUnitHom τ L).comp
    (MonoidHom.compLeft (rootsOfUnity 4 L).subtype (Fin τ.rank))).range

theorem mem_fourDiagGroup {y : ModGL τ L} :
    y ∈ fourDiagGroup τ L ↔ ∃ b : Fin τ.rank → Lˣ, (∀ i, b i ^ 4 = 1) ∧ rootDiagUnit τ b = y := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => (c i : Lˣ), fun i => (mem_rootsOfUnity 4 _).1 (c i).2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨fun i => ⟨b i, (mem_rootsOfUnity 4 _).2 (hb i)⟩, rfl⟩

theorem finite_fourDiagGroup : Finite (fourDiagGroup τ L) :=
  Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem fourDiagGroup_comm {y y' : ModGL τ L} (hy : y ∈ fourDiagGroup τ L)
    (hy' : y' ∈ fourDiagGroup τ L) : y * y' = y' * y := by
  obtain ⟨b, -, rfl⟩ := mem_fourDiagGroup.1 hy
  obtain ⟨b', -, rfl⟩ := mem_fourDiagGroup.1 hy'
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem pow_four_of_mem_fourDiagGroup {y : ModGL τ L} (hy : y ∈ fourDiagGroup τ L) :
    y ^ 4 = 1 := by
  obtain ⟨b, hb, rfl⟩ := mem_fourDiagGroup.1 hy
  have h : rootDiagUnit τ b ^ 4 = rootDiagUnit τ (b ^ 4) :=
    (map_pow (rootDiagUnitHom τ L) b 4).symm
  rw [h, ← rootDiagUnit_one]
  congr 1
  funext i
  rw [Pi.pow_apply, hb, Pi.one_apply]

theorem signDiagGroup_le_fourDiagGroup : signDiagGroup τ L ≤ fourDiagGroup τ L := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := mem_signDiagGroup.1 hy
  exact mem_fourDiagGroup.2 ⟨b, fun i => by rw [show 4 = 2 * 2 by rfl, pow_mul, hb, one_pow], rfl⟩

theorem exists_mul_self_eq_of_mem_signDiagGroup [IsAlgClosed L] {y : ModGL τ L}
    (hy : y ∈ signDiagGroup τ L) : ∃ z ∈ fourDiagGroup τ L, z * z = y := by
  obtain ⟨b, hb, rfl⟩ := mem_signDiagGroup.1 hy
  have hroot : ∀ i, ∃ c : Lˣ, c ^ 2 = b i := fun i => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (b i : L) (n := 2) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact (b i).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose c hc using hroot
  refine ⟨rootDiagUnit τ c, mem_fourDiagGroup.2 ⟨c, fun i => ?_, rfl⟩, ?_⟩
  · rw [show 4 = 2 * 2 by rfl, pow_mul, hc, hb]
  · rw [← rootDiagUnit_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← sq, hc]

theorem canonicalRep_conj_mem_fourDiagGroup
    (w : WeylGroup τ) {y : ModGL τ L}
    (hy : y ∈ fourDiagGroup τ L) :
    canonicalRep (coxeterSystem τ) L w * y * (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈
      fourDiagGroup τ L := by
  obtain ⟨b, hb, rfl⟩ := mem_fourDiagGroup.1 hy
  rw [canonicalRep_conj_rootDiagUnit]
  exact mem_fourDiagGroup.2 ⟨_, fun i => rootChar_pow_eq_one hb _, rfl⟩

theorem entrywiseFrobGL_of_mem_fourDiagGroup (p : ℕ) [Fact p.Prime] [CharP L p] (e : ℕ)
    {y : ModGL τ L} (hy : y ∈ fourDiagGroup τ L) :
    entrywiseFrobGL τ L p e y = y ^ (p ^ e) := by
  obtain ⟨b, -, rfl⟩ := mem_fourDiagGroup.1 hy
  have h : entrywiseFrobGL τ L p e (rootDiagUnit τ b) =
      rootDiagUnit τ fun i => Units.map (iterateFrobenius L p e).toMonoidHom (b i) :=
    Units.ext (by rw [Units.coe_map]; exact entrywise_rootDiag _ b)
  have h2 : rootDiagUnit τ b ^ (p ^ e) = rootDiagUnit τ (b ^ (p ^ e)) :=
    (map_pow (rootDiagUnitHom τ L) b _).symm
  rw [h, h2]
  congr 1

theorem fourDiagGroup_le_toralCentralizer
    [IsAlgClosed L] (a : Fin τ.rank → Lˣ) :
    fourDiagGroup τ L ≤ toralCentralizer τ L a := by
  intro y hy
  obtain ⟨b, -, rfl⟩ := mem_fourDiagGroup.1 hy
  exact mem_toralCentralizer.2
    ⟨(exceptional_Lang_adjoint_diagonal_lift τ L b).1, rootDiagUnit_conj_rootDiagUnit a b⟩

theorem pow_eq_self_of_mem_fourDiagGroup {y : ModGL τ L} (hy : y ∈ fourDiagGroup τ L) {n : ℕ}
    (hn : n % 4 = 1) : y ^ n = y := by
  rw [← Nat.div_add_mod n 4, hn, pow_add, pow_mul, pow_four_of_mem_fourDiagGroup hy, one_pow,
    one_mul, pow_one]

theorem sq_mod_four_of_odd {q : ℕ} (hq : Odd q) : (q ^ 2) % 4 = 1 := by
  obtain ⟨r, rfl⟩ := hq
  have : (2 * r + 1) ^ 2 = 4 * (r * r + r) + 1 := by ring
  rw [this]
  omega

theorem one_le_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hK : Nat.card K = p ^ f) :
    1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · rw [h0, pow_zero] at hK
    exact absurd hK (Finite.one_lt_card).ne'
  · exact h0

theorem odd_card {K : Type} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Odd (Nat.card K) := by
  rw [hK]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

end FourDiag

end FiveExIn

end CFSG.SeitzReduction.RankOne
