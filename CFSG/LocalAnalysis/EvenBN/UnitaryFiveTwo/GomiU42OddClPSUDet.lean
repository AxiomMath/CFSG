module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSUCount

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p f n : ℕ} {K : Type} [Field K]

theorem u42_mem_fixedSubgroup' {G : Type} [Group G] {σ : MulAut G} {x : G} :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

theorem u42_card_eq_ker_mul_range {G H : Type} [Group G] [Group H] [Finite G] (φ : G →* H) :
    Nat.card G = Nat.card φ.ker * Nat.card φ.range := by
  rw [← φ.ker.card_mul_index, Subgroup.index_ker]

theorem u42_scalar_mem_U (h : UnitaryFieldData p f K) {c : Kˣ} (hc : h.norm (c : K) = 1) :
    (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) := by
  rw [UnitaryHigher.mem_primeFormUnitary, GeneralLinearGroup.coe_scalar,
    scalar_barTranspose_mul_mul, hc, one_smul]

@[expose] noncomputable def u42DetU (h : UnitaryFieldData p f K) (n : ℕ) :
    ↥(primeFormUnitary h (idGram K n)) →* Kˣ :=
  GeneralLinearGroup.det.comp (primeFormUnitary h (idGram K n)).subtype

theorem u42DetU_apply (h : UnitaryFieldData p f K) (x : ↥(primeFormUnitary h (idGram K n))) :
    u42DetU h n x = GeneralLinearGroup.det (x : GL (Fin n) K) := rfl

theorem u42_unitaryDet_toLinU (h : UnitaryFieldData p f K) (x : ↥(primeFormUnitary h (idGram K n))) :
    CFSG.LinearGroups.unitaryDet (idForm h n) ⟨toLinU h n x, toLinU_mem x⟩ = u42DetU h n x := by
  apply Units.ext
  rw [CFSG.LinearGroups.unitaryDet_apply, u42DetU_apply, GeneralLinearGroup.val_det_apply]
  change LinearMap.det (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = _
  rw [LinearMap.det_toLin']


@[expose] noncomputable def u42DetOn (h : UnitaryFieldData p f K) (n : ℕ)
    (Cm : Subgroup ↥(primeFormUnitary h (idGram K n))) : ↥Cm →* Kˣ :=
  (u42DetU h n).comp Cm.subtype

theorem u42_fixed_iff (h : UnitaryFieldData p f K) (A : ↥(primeFormUnitary h (idGram K n)))
    (x : ↥(gramSU h (idGram K n))) :
    x ∈ fixedSubgroup (primeFormConjSU h (idGram K n) A : MulAut ↥(gramSU h (idGram K n))) ↔
      (x : GL (Fin n) K) * (A : GL (Fin n) K) = (A : GL (Fin n) K) * (x : GL (Fin n) K) := by
  rw [u42_mem_fixedSubgroup', Subtype.ext_iff]
  change (A : GL (Fin n) K) * x * (A : GL (Fin n) K)⁻¹ = x ↔ _
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem u42_card_fixedSubgroup_conjSU (h : UnitaryFieldData p f K)
    (A : ↥(primeFormUnitary h (idGram K n))) :
    Nat.card ↥(fixedSubgroup (primeFormConjSU h (idGram K n) A :
        MulAut ↥(gramSU h (idGram K n)))) =
      Nat.card ↥(u42DetOn h n (Subgroup.centralizer ({A} : Set _))).ker := by
  have hker : ∀ y : ↥(primeFormUnitary h (idGram K n)),
      y ∈ Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h (idGram K n))) →
      u42DetU h n y = 1 → (y : GL (Fin n) K) ∈ gramSU h (idGram K n) := by
    intro y hy hd
    refine ⟨y.2, ?_⟩
    have h1 := congrArg Units.val hd
    rw [u42DetU_apply, GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    exact h1
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨⟨(x.1 : GL (Fin n) K), x.1.2.1⟩, ?_⟩, ?_⟩
      invFun := fun y => ⟨⟨(y.1.1 : GL (Fin n) K), hker y.1.1 y.1.2 y.2⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext ((u42_fixed_iff h A x.1).1 x.2))
  · rw [MonoidHom.mem_ker]
    apply Units.ext
    change ((x.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1
    exact x.1.2.2
  · rw [u42_fixed_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.1.2)


theorem u42_scalar_injective' (hn : 1 ≤ n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
  intro c d hcd
  have h1 : (GeneralLinearGroup.scalar (Fin n) (c * d⁻¹) : GL (Fin n) K) = 1 := by
    rw [map_mul, map_inv, hcd, mul_inv_cancel]
  have := (scalar_eq_one_iff hn).mp h1
  exact mul_inv_eq_one.mp this

theorem u42_N₁ (h : UnitaryFieldData p f K) (hn : 1 ≤ n) :
    (∀ c : Kˣ, c ∈ (CFSG.LinearGroups.unitaryDet (idForm h n)).range ↔ h.norm (c : K) = 1) ∧
      Nat.card (CFSG.LinearGroups.unitaryDet (idForm h n)).range = p ^ f + 1 := by
  have : Finite K := h.finite
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  obtain ⟨-, -, h3, h4, -⟩ := CFSG.LinearGroups.unitary_full_group_order h (idForm_isSymm h n)
    (idForm_separatingLeft h n) hdim hn
  exact ⟨h3, h4⟩


theorem u42_card_ker_pow (h : UnitaryFieldData p f K) (hn : 1 ≤ n) :
    Nat.card ((powMonoidHom n : Kˣ →* Kˣ).comp
      (CFSG.LinearGroups.unitaryDet (idForm h n)).range.subtype).ker = Nat.gcd n (p ^ f + 1) := by
  obtain ⟨hmem, -⟩ := u42_N₁ h hn
  rw [← CFSG.RankThree.Classical.card_normOneScalars_one h hn]
  refine Nat.card_congr (Equiv.ofBijective (fun c => ⟨⟨GeneralLinearGroup.scalar (Fin n) c.1.1,
    scalar_mem_gramSU hn ((hmem _).1 c.1.2) ?_⟩, ⟨c.1.1, (hmem _).1 c.1.2, ?_, rfl⟩⟩) ⟨?_, ?_⟩)
  · exact c.2
  · exact c.2
  · intro c d hcd
    have h1 := congrArg (fun z => ((z.1 : ↥(gramSU h (idGram K n))) : GL (Fin n) K)) hcd
    exact Subtype.ext (Subtype.ext (u42_scalar_injective' hn h1))
  · rintro ⟨z, c, hcN, hcn, hc⟩
    exact ⟨⟨⟨c, (hmem c).2 hcN⟩, hcn⟩, Subtype.ext (Subtype.ext hc.symm)⟩


theorem u42_det_range_index (h : UnitaryFieldData p f K) (hn : 1 ≤ n)
    (Cm : Subgroup ↥(primeFormUnitary h (idGram K n)))
    (hsc : ∀ (c : Kˣ) (hc : h.norm (c : K) = 1),
      (⟨GeneralLinearGroup.scalar (Fin n) c, u42_scalar_mem_U h hc⟩ :
        ↥(primeFormUnitary h (idGram K n))) ∈ Cm) :
    ∃ k e' : ℕ, Nat.card (u42DetOn h n Cm).range * e' = p ^ f + 1 ∧
      k * e' = Nat.gcd n (p ^ f + 1) := by
  have : Finite K := h.finite
  obtain ⟨hmem, hcardN⟩ := u42_N₁ h hn
  set N₁ := (CFSG.LinearGroups.unitaryDet (idForm h n)).range with hN₁
  set φ₁ : ↥N₁ →* Kˣ := (powMonoidHom n : Kˣ →* Kˣ).comp N₁.subtype with hφ₁
  set D := (u42DetOn h n Cm).range with hD
  have hDN : D ≤ N₁ := by
    rintro _ ⟨x, rfl⟩
    rw [show u42DetOn h n Cm x = u42DetU h n x.1 from rfl, ← u42_unitaryDet_toLinU h x.1]
    exact ⟨_, rfl⟩
  have hG₂D : φ₁.range ≤ D := by
    rintro _ ⟨c, rfl⟩
    have hc : h.norm ((c : Kˣ) : K) = 1 := (hmem _).1 c.2
    refine ⟨⟨⟨GeneralLinearGroup.scalar (Fin n) (c : Kˣ), u42_scalar_mem_U h hc⟩, hsc _ hc⟩, ?_⟩
    change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) (c : Kˣ)) = _
    rw [GeneralLinearGroup.det_scalar]
    simp [hφ₁, powMonoidHom, Fintype.card_fin]
  have h1 : Nat.card N₁ = Nat.card φ₁.ker * Nat.card φ₁.range := u42_card_eq_ker_mul_range φ₁
  have hker : Nat.card φ₁.ker = Nat.gcd n (p ^ f + 1) := u42_card_ker_pow h hn
  rw [hcardN, hker] at h1
  have hd1 : Nat.card φ₁.range ∣ Nat.card D := Subgroup.card_dvd_of_le hG₂D
  have hd2 : Nat.card D ∣ Nat.card N₁ := Subgroup.card_dvd_of_le hDN
  obtain ⟨k, hk⟩ := hd1
  obtain ⟨e', he'⟩ := hd2
  rw [hcardN] at he'
  refine ⟨k, e', he'.symm, ?_⟩
  have hpos : 0 < Nat.card φ₁.range := Nat.card_pos
  rw [hk] at he'
  have h3 : Nat.card φ₁.range * (k * e') = Nat.card φ₁.range * Nat.gcd n (p ^ f + 1) := by
    calc Nat.card φ₁.range * (k * e') = Nat.card φ₁.range * k * e' := by ring
      _ = p ^ f + 1 := he'.symm
      _ = Nat.card φ₁.range * Nat.gcd n (p ^ f + 1) := by linarith [h1]
  exact Nat.eq_of_mul_eq_mul_left hpos h3


theorem u42_card_subgroup_le_two {G : Type} [Group G] [Finite G] (R : Subgroup G)
    (h : ∀ x ∈ R, ∀ y ∈ R, x = 1 ∨ y = 1 ∨ x = y) : Nat.card R ≤ 2 := by
  by_cases hR : R = ⊥
  · rw [hR, Subgroup.card_bot]
    norm_num
  · obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hR
    have hx : (x : G) ∈ R := x.2
    have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hsub : (R : Set G) ⊆ {1, (x : G)} := by
      intro y hy
      rcases h y hy x hx with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd h1 hx1'
      · exact Or.inr h1
    have h2 : (R : Set G).ncard ≤ ({1, (x : G)} : Set G).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({1, (x : G)} : Set G).ncard ≤ 2 := by
      calc ({1, (x : G)} : Set G).ncard ≤ ({(x : G)} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [← Nat.card_coe_set_eq] at h2 h3
    exact h2.trans h3


theorem u42_psu_inner_eq (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (A : ↥(primeFormUnitary h (idGram K n)))
    (hAA : ∃ c : Kˣ, (A : GL (Fin n) K) * A = GeneralLinearGroup.scalar (Fin n) c) :
    ∃ ε k : ℕ, (ε = 1 ∨ ε = 2) ∧ k ∣ Nat.gcd n (p ^ f + 1) ∧
      Nat.card ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A)) * k * (p ^ f + 1) =
        ε * Nat.card ↥(Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h (idGram K n)))) := by
  have : Finite K := h.finite
  obtain ⟨c₀, hc₀⟩ := hAA
  obtain ⟨R, hRZ, hRg, hcount⟩ := u42_count_fixed (normOneScalars h (gramSU h (idGram K n)) n)
    (normOneScalars_le_center h _ n) (primeFormConjSU h (idGram K n) A)
    (primeFormConjHom h (idGram K n) A) (fun g => primeFormConjHom_mk h _ A g)
  have hψ_fix : ∀ r ∈ normOneScalars h (gramSU h (idGram K n)) n,
      primeFormConjSU h (idGram K n) A r = r := by
    rintro r ⟨c, -, -, hr⟩
    apply Subtype.ext
    change (A : GL (Fin n) K) * (r : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = r
    rw [hr, (commute_scalar c (A : GL (Fin n) K)).eq, mul_inv_cancel_right]
  have hψ2 : ∀ g, primeFormConjSU h (idGram K n) A (primeFormConjSU h (idGram K n) A g) = g := by
    intro g
    apply Subtype.ext
    change (A : GL (Fin n) K) * ((A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹) *
      (A : GL (Fin n) K)⁻¹ = g
    have e1 : (A : GL (Fin n) K) * ((A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹) *
        (A : GL (Fin n) K)⁻¹ = ((A : GL (Fin n) K) * A) * g * ((A : GL (Fin n) K) * A)⁻¹ := by
      group
    rw [e1, hc₀, ← (commute_scalar c₀ (g : GL (Fin n) K)).eq, mul_inv_cancel_right]
  have hr_sq : ∀ r ∈ R, r * r = 1 := by
    intro r hr
    obtain ⟨g, hg⟩ := hRg r hr
    have h1 : g = primeFormConjSU h (idGram K n) A (primeFormConjSU h (idGram K n) A g) :=
      (hψ2 g).symm
    rw [hg, map_mul, hψ_fix r (hRZ hr), hg, ← mul_assoc] at h1
    exact mul_eq_right.mp h1.symm
  have hsc : ∀ r ∈ R, ∃ c : Kˣ, (r : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c ∧
      ((c : K) = 1 ∨ (c : K) = -1) := by
    intro r hr
    obtain ⟨c, -, -, hc⟩ := hRZ hr
    refine ⟨c, hc, ?_⟩
    have h1 := congrArg Subtype.val (hr_sq r hr)
    rw [Subgroup.coe_mul, hc, ← map_mul, Subgroup.coe_one] at h1
    have h2 : c * c = 1 := (scalar_eq_one_iff (by omega)).mp h1
    have h3 : (c : K) * (c : K) = 1 := by
      have := congrArg Units.val h2
      simpa using this
    exact mul_self_eq_one_iff.mp h3
  have hle : Nat.card R ≤ 2 := by
    apply u42_card_subgroup_le_two
    intro x hx y hy
    obtain ⟨c₁, hc₁, hc₁'⟩ := hsc x hx
    obtain ⟨c₂, hc₂, hc₂'⟩ := hsc y hy
    rcases hc₁' with h1 | h1
    · left
      apply Subtype.ext
      rw [hc₁, show c₁ = 1 from Units.ext h1, map_one]
      rfl
    · rcases hc₂' with h2 | h2
      · right
        left
        apply Subtype.ext
        rw [hc₂, show c₂ = 1 from Units.ext h2, map_one]
        rfl
      · right
        right
        apply Subtype.ext
        rw [hc₁, hc₂, show c₁ = c₂ from Units.ext (h1.trans h2.symm)]
  have hεpos : 0 < Nat.card R := Nat.card_pos
  have hZcard : Nat.card (normOneScalars h (gramSU h (idGram K n)) n) = Nat.gcd n (p ^ f + 1) :=
    CFSG.RankThree.Classical.card_normOneScalars_one h (by omega)
  have hfix := u42_card_fixedSubgroup_conjSU h A
  have hCm := u42_card_eq_ker_mul_range
    (u42DetOn h n (Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h (idGram K n)))))
  obtain ⟨k, e', hidx, hk⟩ := u42_det_range_index h (by omega)
    (Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h (idGram K n)))) (fun c hc => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext ((commute_scalar c (A : GL (Fin n) K)).eq.symm))
  refine ⟨Nat.card R, k, by omega, ⟨e', hk.symm⟩, ?_⟩
  rw [hZcard, ← hk, hfix] at hcount
  calc Nat.card ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A)) * k * (p ^ f + 1)
      = Nat.card ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A)) * k *
          (Nat.card (u42DetOn h n (Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h
            (idGram K n))))).range * e') := by rw [hidx]
    _ = (Nat.card ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A)) * (k * e')) *
          Nat.card (u42DetOn h n (Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h
            (idGram K n))))).range := by ring
    _ = (Nat.card R * Nat.card (u42DetOn h n (Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h
            (idGram K n))))).ker) *
          Nat.card (u42DetOn h n (Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h
            (idGram K n))))).range := by rw [hcount]
    _ = _ := by rw [hCm]; ring

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
