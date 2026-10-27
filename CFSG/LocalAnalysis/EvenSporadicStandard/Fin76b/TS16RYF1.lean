module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYDih

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem s16F1_of_data {M : Type} [Group M] [Finite M] {P R : Subgroup M} (hPR : P ≤ R)
    (e : ↥R ≃* MulAut ↥P)
    (he : ∀ (x : ↥R) (p : ↥P), (((e x) p : ↥P) : M) = (x : M) * (p : M) * (x : M)⁻¹)
    {τ0 : M} {m : ℕ} (hm : Odd m)
    (hcent : Nat.card ↥(P ⊓ centralizer ({τ0} : Set M)) = 16 * m)
    (hall : ∀ ρ ∈ R, ρ * ρ = 1 → ρ ∉ P → ∃ g ∈ P, ρ = g * τ0 * g⁻¹)
    {a b : M} (ha : a ∈ P) (hb : b ∈ P) (haτ : a * τ0 = τ0 * a) (hbτ : b * τ0 = τ0 * b)
    (ha8 : a ^ 8 = 1) (hb2 : b * b = 1) (hba : b * a * b⁻¹ = a⁻¹)
    (hcard : Nat.card ↥(closure ({a, b} : Set M)) = 16) :
    ∀ r : MulAut ↥P, r * r = 1 → ¬ IsInnerAut r →
      ∃ V0 : Subgroup ↥P, V0 ≤ fixedSub r ∧ Nonempty (↥V0 ≃* DihedralGroup 8) ∧
        ∃ m' : ℕ, Odd m' ∧ Nat.card ↥(fixedSub r) = 16 * m' := by
  classical
  intro r hr2 hrinn
  set ρ' : ↥R := e.symm r with hρ'
  have hρ'r : e ρ' = r := by rw [hρ']; simp
  set ρ : M := (ρ' : M) with hρ
  have hρR : ρ ∈ R := ρ'.2
  have hρ2 : ρ * ρ = 1 := by
    have h1 : e (ρ' * ρ') = e 1 := by rw [map_mul, hρ'r, hr2, map_one]
    have h2 := e.injective h1
    exact congrArg Subtype.val h2
  have hρP : ρ ∉ P := by
    intro hρP
    apply hrinn
    refine ⟨⟨ρ, hρP⟩, ?_⟩
    rw [← hρ'r]
    have := real_conj hPR e he hρP
    rw [← this]
  obtain ⟨g, hgP, hρg⟩ := hall ρ hρR hρ2 hρP
  have hρapp : ∀ p : ↥P, ((r p : ↥P) : M) = ρ * p * ρ⁻¹ := by
    intro p
    rw [← hρ'r]
    exact he ρ' p
  have hfix : (fixedSub r).map P.subtype = P ⊓ centralizer ({ρ} : Set M) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      show (p : M) ∈ centralizer ({ρ} : Set M)
      rw [mem_centralizer_singleton_iff]
      have h1 : ρ * (p : M) * ρ⁻¹ = p := by
        rw [← hρapp]
        exact congrArg Subtype.val hp
      calc (p : M) * ρ = (ρ * p * ρ⁻¹) * ρ := by rw [h1]
        _ = ρ * p := by group
    · rintro ⟨hyP, hyc⟩
      refine ⟨⟨y, hyP⟩, ?_, rfl⟩
      show r ⟨y, hyP⟩ = ⟨y, hyP⟩
      apply Subtype.ext
      rw [hρapp]
      have := mem_centralizer_singleton_iff.1 hyc
      calc ρ * y * ρ⁻¹ = (y * ρ) * ρ⁻¹ := by rw [this]
        _ = y := by group
  let φ : M ≃* M := MulAut.conj g
  have hφP : P.map φ.toMonoidHom = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨p, hp, rfl⟩
      exact mul_mem (mul_mem hgP hp) (inv_mem hgP)
    · rw [Subgroup.card_map_of_injective φ.injective]
  have hcentρ : (P ⊓ centralizer ({τ0} : Set M)).map φ.toMonoidHom =
      P ⊓ centralizer ({ρ} : Set M) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hpP, hpc⟩ := Subgroup.mem_inf.1 hp
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgP hpP) (inv_mem hgP), ?_⟩
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 hpc
      show g * p * g⁻¹ * ρ = ρ * (g * p * g⁻¹)
      rw [hρg]
      calc g * p * g⁻¹ * (g * τ0 * g⁻¹) = g * (p * τ0) * g⁻¹ := by group
        _ = g * (τ0 * p) * g⁻¹ := by rw [this]
        _ = g * τ0 * g⁻¹ * (g * p * g⁻¹) := by group
    · intro hy
      obtain ⟨hyP, hyc⟩ := Subgroup.mem_inf.1 hy
      refine ⟨g⁻¹ * y * g, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
      · exact mul_mem (mul_mem (inv_mem hgP) hyP) hgP
      · rw [mem_centralizer_singleton_iff]
        have := mem_centralizer_singleton_iff.1 hyc
        rw [hρg] at this
        show g⁻¹ * y * g * τ0 = τ0 * (g⁻¹ * y * g)
        calc g⁻¹ * y * g * τ0 = g⁻¹ * (y * (g * τ0 * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * τ0 * g⁻¹) * y) * g := by rw [this]
          _ = τ0 * (g⁻¹ * y * g) := by group
      · show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hfixcard : Nat.card ↥(fixedSub r) = 16 * m := by
    calc Nat.card ↥(fixedSub r) = Nat.card ↥((fixedSub r).map P.subtype) :=
          (Subgroup.card_map_of_injective P.subtype_injective).symm
      _ = Nat.card ↥(P ⊓ centralizer ({ρ} : Set M)) := by rw [hfix]
      _ = Nat.card ↥((P ⊓ centralizer ({τ0} : Set M)).map φ.toMonoidHom) := by rw [hcentρ]
      _ = 16 * m := by
        rw [Subgroup.card_map_of_injective φ.injective]
        exact hcent
  obtain ⟨e8, -, -⟩ := exists_dihedral8_equiv ha8 hb2 hba hcard
  set H : Subgroup M := (closure ({a, b} : Set M)).map φ.toMonoidHom with hH
  have hHle : H ≤ P ⊓ centralizer ({ρ} : Set M) := by
    rw [← hcentρ]
    apply Subgroup.map_mono
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨ha, mem_centralizer_singleton_iff.2 haτ⟩
    · exact ⟨hb, mem_centralizer_singleton_iff.2 hbτ⟩
  have hHP : H ≤ P := hHle.trans inf_le_left
  refine ⟨H.subgroupOf P, ?_, ?_, m, hm, hfixcard⟩
  · intro v hv
    have hvH : (v : M) ∈ H := Subgroup.mem_subgroupOf.1 hv
    have hvc := (hHle hvH).2
    show r v = v
    apply Subtype.ext
    rw [hρapp]
    have := mem_centralizer_singleton_iff.1 hvc
    calc ρ * (v : M) * ρ⁻¹ = ((v : M) * ρ) * ρ⁻¹ := by rw [this]
      _ = v := by group
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hHP).trans
      (((closure ({a, b} : Set M)).equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e8)⟩

end CFSG.EvenSporadicStandard.Fin76b
