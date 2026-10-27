module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC6
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC8
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC2

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 GL42

namespace UTSylow

variable {X : Type} [Group X] [Finite X] (D : UTSylow X)

@[expose] def psiS : Sylow 2 D.psi.range :=
  (D.T.subtype D.T_le_normalizer).mapSurjective D.psi.rangeRestrict_surjective

theorem mem_psiS {x : D.psi.range} :
    x ∈ D.psiS ↔ ∃ t : normalizer (D.E : Set X), (t : X) ∈ (D.T : Subgroup X) ∧
      D.psi.rangeRestrict t = x := by
  change x ∈ (D.psiS : Subgroup _) ↔ _
  rw [psiS, Sylow.coe_mapSurjective, mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    have h : t ∈ ((D.T.subtype D.T_le_normalizer : Sylow 2 _) : Subgroup _) := ht
    rwa [Sylow.coe_subtype, mem_subgroupOf] at h
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    rwa [Sylow.coe_subtype, mem_subgroupOf]

@[expose] def sylE0 : SylE0 D.psi.range where
  ρ := D.psi.range.subtype
  inj := D.psi.range.subtype_injective
  S := D.psiS
  hS := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, ht, rfl⟩ := D.mem_psiS.mp hx
      obtain ⟨u, hu⟩ := D.exists_toX ht
      have htu : t = ⟨D.toX u, D.T_le_normalizer (D.toX_mem u)⟩ := Subtype.ext hu.symm
      subst htu
      exact ⟨e0 u.b.a u.b.b, e0_mem _ _, (D.psi_toX u).symm⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨p, q, rfl⟩ := exists_e0 c hc
      exact ⟨D.psi.rangeRestrict ⟨D.toX ⟨0, ⟨p, q⟩, 0⟩, D.T_le_normalizer (D.toX_mem _)⟩,
        D.mem_psiS.mpr ⟨_, D.toX_mem _, rfl⟩, D.psi_toX ⟨0, ⟨p, q⟩, 0⟩⟩

theorem sylE0_not_normal (hn : ∃ n ∈ normalizer (D.E : Set X), ∃ t ∈ (D.T : Subgroup X),
      n * t * n⁻¹ ∉ (D.T : Subgroup X) ⊔ centralizer (D.E : Set X)) :
    ∃ h : D.psi.range, ∃ x ∈ D.sylE0.S, h * x * h⁻¹ ∉ D.sylE0.S := by
  obtain ⟨n, hn, t, ht, hnt⟩ := hn
  refine ⟨D.psi.rangeRestrict ⟨n, hn⟩, D.psi.rangeRestrict ⟨t, D.T_le_normalizer ht⟩,
    D.mem_psiS.mpr ⟨_, ht, rfl⟩, fun hmem => hnt ?_⟩
  change _ ∈ D.psiS at hmem
  rw [← map_inv, ← map_mul, ← map_mul] at hmem
  obtain ⟨t', ht', heq⟩ := D.mem_psiS.mp hmem
  have heq' : D.psi t' = D.psi (⟨n, hn⟩ * ⟨t, D.T_le_normalizer ht⟩ * ⟨n, hn⟩⁻¹) := by
    have h3 := congrArg Subtype.val heq
    simpa only [MonoidHom.coe_rangeRestrict] using h3
  have h2 : D.psi (t'⁻¹ * (⟨n, hn⟩ * ⟨t, D.T_le_normalizer ht⟩ * ⟨n, hn⟩⁻¹)) = 1 := by
    rw [map_mul, map_inv, heq', inv_mul_cancel]
  have hc := (D.psi_eq_one_iff _).mp h2
  rw [show n * t * n⁻¹ = (t' : X) * ((t' : X)⁻¹ * (n * t * n⁻¹)) by group]
  exact mul_mem (le_sup_left (a := (D.T : Subgroup X)) ht')
    (le_sup_right (a := (D.T : Subgroup X)) hc)

omit [Finite X] in
theorem mem_normalizer_of_normal (hEn : D.E.Normal) (x : X) : x ∈ normalizer (D.E : Set X) :=
  (normalizer_eq_top_iff.mpr hEn) ▸ mem_top x

@[expose] def theta (hEn : D.E.Normal) : X →* D.psi.range :=
  D.psi.rangeRestrict.comp ((MonoidHom.id X).codRestrict _ (D.mem_normalizer_of_normal hEn))

omit [Finite X] in
theorem theta_surjective (hEn : D.E.Normal) : Function.Surjective (D.theta hEn) := by
  rintro ⟨_, n, rfl⟩
  refine ⟨n, Subtype.ext ?_⟩
  change D.psi ⟨(n : X), _⟩ = D.psi n
  rfl

theorem ker_theta (hO : pPrimeCore 2 X = ⊥) (hEn : D.E.Normal) : (D.theta hEn).ker = D.E := by
  ext x
  rw [MonoidHom.mem_ker]
  change D.psi.rangeRestrict ⟨x, _⟩ = 1 ↔ _
  have hC := D.centralizer_E_eq hO hEn
  constructor
  · intro h
    have h1 := (D.psi_eq_one_iff _).mp (congrArg Subtype.val h)
    rw [hC] at h1
    exact h1
  · intro h
    refine Subtype.ext ((D.psi_eq_one_iff _).mpr ?_)
    rw [hC]
    exact h

@[expose] def quotEquiv (hO : pPrimeCore 2 X = ⊥) (hEn : D.E.Normal) : X ⧸ D.E ≃* D.psi.range :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_theta hO hEn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (D.theta_surjective hEn))

theorem T_sup_centralizer (hO : pPrimeCore 2 X = ⊥) (hEn : D.E.Normal) :
    (D.T : Subgroup X) ⊔ centralizer (D.E : Set X) = D.T := by
  rw [D.centralizer_E_eq hO hEn]
  exact sup_eq_left.mpr D.E_le_T

omit [Finite X] in
theorem le_T_of_normal {P : Subgroup X} (hPn : P.Normal) (hP : IsPGroup 2 P) :
    P ≤ (D.T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 (((D.T : Subgroup X) ⊔ P : Subgroup X)) :=
    IsPGroup.to_sup_of_normal_right D.T.isPGroup' hP
  exact sup_eq_left.mp (D.T.is_maximal' hsup le_sup_left)

omit [Finite X] in
theorem E_le_pCore (hEn : D.E.Normal) : D.E ≤ pCore 2 X :=
  le_sSup ⟨hEn, D.T.isPGroup'.to_le D.E_le_T⟩

theorem caseB
    (hO : pPrimeCore 2 X = ⊥) (hEn : D.E.Normal) (hTn : ¬ (D.T : Subgroup X).Normal) :
    pCore 2 X = D.E ∧
      (Nonempty (X ⧸ D.E ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (X ⧸ D.E ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) ∧
      ∀ u ∈ D.E, ∀ v ∈ D.E, u ≠ 1 → v ≠ 1 → ∃ g : X, g⁻¹ * u * g = v := by
  have hn : ∃ n ∈ normalizer (D.E : Set X), ∃ t ∈ (D.T : Subgroup X),
      n * t * n⁻¹ ∉ (D.T : Subgroup X) ⊔ centralizer (D.E : Set X) := by
    by_contra hcon
    push Not at hcon
    apply hTn
    constructor
    intro t ht n
    have h := hcon n (D.mem_normalizer_of_normal hEn n) t ht
    rwa [D.T_sup_centralizer hO hEn] at h
  have htr : ∀ e ∈ D.E, e ≠ 1 → ∃ n : X, n * D.toX ⟨0, 0, 1⟩ * n⁻¹ = e := fun e he he1 => by
    obtain ⟨n, -, hn'⟩ := D.exists_conj_eq_of_not_mem hn he he1
    exact ⟨n, hn'⟩
  refine ⟨le_antisymm (fun t ht => ?_) (D.E_le_pCore hEn), ?_, ?_⟩
  ·
    have htT : t ∈ (D.T : Subgroup X) := D.le_T_of_normal pCore_normal pCore_isPGroup ht
    rw [← D.centralizer_E_eq hO hEn]
    refine mem_centralizer_iff.mpr fun e he => ?_
    by_cases he1 : e = 1
    · rw [he1, one_mul, mul_one]
    obtain ⟨n, rfl⟩ := htr e he he1
    have h1 : n⁻¹ * t * n⁻¹⁻¹ ∈ pCore 2 X := (pCore_normal (p := 2) (G := X)).conj_mem _ ht _
    have h2 := D.Z_comm (D.toX_mem_Z_iff.mpr ⟨rfl, rfl⟩ : D.toX ⟨0, 0, 1⟩ ∈ D.Z)
      (D.le_T_of_normal pCore_normal pCore_isPGroup h1)
    calc n * D.toX ⟨0, 0, 1⟩ * n⁻¹ * t =
        n * (D.toX ⟨0, 0, 1⟩ * (n⁻¹ * t * n⁻¹⁻¹)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * t * n⁻¹⁻¹) * D.toX ⟨0, 0, 1⟩) * n⁻¹ := by rw [h2]
      _ = t * (n * D.toX ⟨0, 0, 1⟩ * n⁻¹) := by group
  · rcases (D.sylE0).iso_a5 (D.sylE0_not_normal hn) with h | h
    · obtain ⟨e⟩ := h
      exact Or.inl ⟨(D.quotEquiv hO hEn).trans e⟩
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨(D.quotEquiv hO hEn).trans e⟩
  · intro u hu v hv hu1 hv1
    obtain ⟨n₁, rfl⟩ := htr u hu hu1
    obtain ⟨n₂, rfl⟩ := htr v hv hv1
    exact ⟨n₁ * n₂⁻¹, by group⟩

end UTSylow

end CFSG.ComponentClassification.GHarris.ThmC
