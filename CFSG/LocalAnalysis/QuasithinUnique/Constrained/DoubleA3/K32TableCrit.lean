module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL2Core

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GorensteinWalter

section Index

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem k32_relIndex_centralizer_le_two {V R : Subgroup Γ} (hV : IsKleinFour ↥V)
    (hRV : R ≤ Subgroup.normalizer (V : Set Γ)) (hR : IsPGroup 2 ↥R) :
    (Subgroup.centralizer (V : Set Γ)).relIndex R ≤ 2 := by
  let ψ : ↥R →* MulAut ↥V := k32ActHom V R hRV
  have hrange : Nat.card ψ.range ≤ 2 := by
    have hr2 : IsPGroup 2 ↥ψ.range :=
      hR.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hd6 : Nat.card ψ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card ψ.range
      rwa [kleinFourAut_card ↥V] at this
    obtain ⟨n, hn⟩ := hr2.exists_card_eq
    rw [hn] at hd6 ⊢
    have hn1 : n ≤ 1 := by
      by_contra hcon
      have h4 : 4 ∣ 2 ^ n := by
        have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        simpa using this
      have := h4.trans hd6
      omega
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  have hker : ψ.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact k32ActHom_eq_one_iff V R hRV r
  have h1 := Subgroup.index_ker ψ
  rw [hker] at h1
  show ((Subgroup.centralizer (V : Set Γ)).subgroupOf R).index ≤ 2
  rw [h1]
  exact hrange

theorem k32_relIndex_centralizer_le_four {A V Q : Subgroup Γ} {ω : Γ} (hA : IsA4Block A V)
    (hω : ω ∈ A) (hQA : Q ≤ Subgroup.normalizer (A : Set Γ))
    (hQV : Q ≤ Subgroup.centralizer (V : Set Γ)) :
    (Subgroup.centralizer ({ω} : Set Γ)).relIndex Q ≤ 4 := by
  have hAV : A ≤ Subgroup.normalizer (V : Set Γ) := hA.le_normalizer'
  have hωV : ∀ u ∈ V, ω * u * ω⁻¹ ∈ V := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hAV hω) u).mp hu
  have hmem : ∀ r ∈ Q, ω⁻¹ * (r * ω * r⁻¹) ∈ V := by
    intro r hr
    have hrA : r * ω * r⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hQA hr) ω).mp hω
    have hg : ω⁻¹ * (r * ω * r⁻¹) ∈ A := A.mul_mem (A.inv_mem hω) hrA
    refine hA.mem_of_centralizes hg fun u hu => ?_
    have hru : u * r = r * u := Subgroup.mem_centralizer_iff.mp (hQV hr) u hu
    have hu₁ : ω * u * ω⁻¹ ∈ V := hωV u hu
    have hru₁ : (ω * u * ω⁻¹) * r = r * (ω * u * ω⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hQV hr) _ hu₁
    have e1 : r⁻¹ * u = u * r⁻¹ := by
      calc r⁻¹ * u = r⁻¹ * (u * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * u) * r⁻¹ := by rw [hru]
        _ = u * r⁻¹ := by group
    have h1 : r * ω * r⁻¹ * u = (ω * u * ω⁻¹) * (r * ω * r⁻¹) := by
      calc r * ω * r⁻¹ * u = r * ω * (r⁻¹ * u) := by group
        _ = r * ω * (u * r⁻¹) := by rw [e1]
        _ = r * (ω * u) * r⁻¹ := by group
        _ = r * ((ω * u * ω⁻¹) * ω) * r⁻¹ := by group
        _ = (r * (ω * u * ω⁻¹)) * ω * r⁻¹ := by group
        _ = ((ω * u * ω⁻¹) * r) * ω * r⁻¹ := by rw [hru₁]
        _ = (ω * u * ω⁻¹) * (r * ω * r⁻¹) := by group
    calc ω⁻¹ * (r * ω * r⁻¹) * u = ω⁻¹ * (r * ω * r⁻¹ * u) := by group
      _ = ω⁻¹ * ((ω * u * ω⁻¹) * (r * ω * r⁻¹)) := by rw [h1]
      _ = u * (ω⁻¹ * (r * ω * r⁻¹)) := by group
  let φ : ↥Q →* ↥V :=
    { toFun := fun r => ⟨ω⁻¹ * ((r : Γ) * ω * (r : Γ)⁻¹), hmem r r.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro r s
        apply Subtype.ext
        have hvs : ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹) ∈ V := hmem s s.2
        have hrv : (r : Γ) * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹)) * (r : Γ)⁻¹ =
            ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹) := by
          have := Subgroup.mem_centralizer_iff.mp (hQV r.2) _ hvs
          calc (r : Γ) * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹)) * (r : Γ)⁻¹
              = ((r : Γ) * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹))) * (r : Γ)⁻¹ := rfl
            _ = ((ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹)) * (r : Γ)) * (r : Γ)⁻¹ := by rw [← this]
            _ = ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹) := by group
        have hsω : (s : Γ) * ω * (s : Γ)⁻¹ = ω * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹)) := by group
        show ω⁻¹ * (((r * s : ↥Q) : Γ) * ω * ((r * s : ↥Q) : Γ)⁻¹) =
          ω⁻¹ * ((r : Γ) * ω * (r : Γ)⁻¹) * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹))
        calc ω⁻¹ * (((r * s : ↥Q) : Γ) * ω * ((r * s : ↥Q) : Γ)⁻¹)
            = ω⁻¹ * (r : Γ) * ((s : Γ) * ω * (s : Γ)⁻¹) * (r : Γ)⁻¹ := by
              simp only [Subgroup.coe_mul, mul_inv_rev]; group
          _ = ω⁻¹ * (r : Γ) * (ω * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹))) * (r : Γ)⁻¹ := by
              rw [← hsω]
          _ = ω⁻¹ * ((r : Γ) * ω * (r : Γ)⁻¹) *
                ((r : Γ) * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹)) * (r : Γ)⁻¹) := by group
          _ = ω⁻¹ * ((r : Γ) * ω * (r : Γ)⁻¹) * (ω⁻¹ * ((s : Γ) * ω * (s : Γ)⁻¹)) := by
              rw [hrv] }
  have hker : φ.ker = (Subgroup.centralizer ({ω} : Set Γ)).subgroupOf Q := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : ω⁻¹ * ((r : Γ) * ω * (r : Γ)⁻¹) = 1 := congrArg Subtype.val h
      have h'' : (r : Γ) * ω * (r : Γ)⁻¹ = ω := by
        calc (r : Γ) * ω * (r : Γ)⁻¹ = ω * (ω⁻¹ * ((r : Γ) * ω * (r : Γ)⁻¹)) := by group
          _ = ω := by rw [h', mul_one]
      calc (r : Γ) * ω = ((r : Γ) * ω * (r : Γ)⁻¹) * (r : Γ) := by group
        _ = ω * (r : Γ) := by rw [h'']
    · intro h
      apply Subtype.ext
      have : ω⁻¹ * ((r : Γ) * ω * (r : Γ)⁻¹) = 1 := by
        rw [h]
        group
      exact this
  have h1 := Subgroup.index_ker φ
  rw [hker] at h1
  show ((Subgroup.centralizer ({ω} : Set Γ)).subgroupOf Q).index ≤ 4
  rw [h1]
  calc Nat.card φ.range ≤ Nat.card ↥V := Subgroup.card_le_card_group _
    _ = 4 := hA.card_U

end Index

section Crit

variable {K : Type} [Group K] [Finite K]

theorem k32_crit {X P R A V : Subgroup (MulAut K)} (hd : K32Datum K X P R A V) :
    ∃ ω ∈ A, orderOf ω = 3 ∧ ∃ W : Subgroup (MulAut K), W ≤ innAut K ∧ IsPGroup 2 ↥W ∧
      W ≤ Subgroup.centralizer ({ω} : Set (MulAut K)) ∧ twoPart (innAut K) ≤ 16 * Nat.card ↥W := by
  obtain ⟨c, hcA, hc3, -⟩ := hd.a4.exists_c
  refine ⟨c, hcA, hc3, ?_⟩
  have hJn : (innAut K).Normal := innAut_normal K
  have hXJ : X ≤ Subgroup.normalizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.normalizer_eq_top (innAut K)]
    exact le_top
  have hPJ : IsSylowTwoOf (P ⊓ innAut K) (innAut K) :=
    A4.isSylowTwoOf_inf_normal hd.sylow hd.inn_le hXJ
  set R₀ := R ⊓ innAut K with hR₀
  have hR₀R : R₀ ≤ R := inf_le_left
  have hR₀P : R₀ ≤ P := hR₀R.trans hd.R_le
  have hR₀2 : IsPGroup 2 ↥R₀ := hd.sylow.2.1.to_le hR₀P
  have hPJcard : Nat.card ↥(P ⊓ innAut K) ≤ 2 * Nat.card ↥R₀ := by
    have hne : R.relIndex P ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    have h1 : R.relIndex (P ⊓ innAut K) ≤ 2 :=
      le_trans (Subgroup.relIndex_le_of_le_right inf_le_left hne) hd.idx
    have h2 := Subgroup.relIndex_mul_card R (P ⊓ innAut K)
    have h3 : R ⊓ (P ⊓ innAut K) = R₀ := by
      rw [← inf_assoc, inf_eq_left.mpr hd.R_le]
    rw [h3] at h2
    calc Nat.card ↥(P ⊓ innAut K) = R.relIndex (P ⊓ innAut K) * Nat.card ↥R₀ := h2.symm
      _ ≤ 2 * Nat.card ↥R₀ := Nat.mul_le_mul_right _ h1
  have hV4 : IsKleinFour ↥V := hd.a4.isKleinFour_U
  have hR₀V : R₀ ≤ Subgroup.normalizer (V : Set (MulAut K)) := hR₀R.trans hd.R_normV
  have hQ2 := k32_relIndex_centralizer_le_two hV4 hR₀V hR₀2
  set Q := Subgroup.centralizer (V : Set (MulAut K)) ⊓ R₀ with hQ
  have hQR₀ : Q ≤ R₀ := inf_le_right
  have hQA : Q ≤ Subgroup.normalizer (A : Set (MulAut K)) := hQR₀.trans (hR₀R.trans hd.R_norm)
  have hQV : Q ≤ Subgroup.centralizer (V : Set (MulAut K)) := inf_le_left
  have hW4 := k32_relIndex_centralizer_le_four hd.a4 hcA hQA hQV
  set W := Subgroup.centralizer ({c} : Set (MulAut K)) ⊓ Q with hW
  have hWQ : W ≤ Q := inf_le_right
  refine ⟨W, (hWQ.trans hQR₀).trans inf_le_right, hd.sylow.2.1.to_le ((hWQ.trans hQR₀).trans hR₀P),
    inf_le_left, ?_⟩
  have e1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (V : Set (MulAut K))) R₀
  have e2 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({c} : Set (MulAut K))) Q
  have hR₀Q : Nat.card ↥R₀ ≤ 2 * Nat.card ↥Q := by
    calc Nat.card ↥R₀ = (Subgroup.centralizer (V : Set (MulAut K))).relIndex R₀ * Nat.card ↥Q :=
          e1.symm
      _ ≤ 2 * Nat.card ↥Q := Nat.mul_le_mul_right _ hQ2
  have hQW : Nat.card ↥Q ≤ 4 * Nat.card ↥W := by
    calc Nat.card ↥Q = (Subgroup.centralizer ({c} : Set (MulAut K))).relIndex Q * Nat.card ↥W :=
          e2.symm
      _ ≤ 4 * Nat.card ↥W := Nat.mul_le_mul_right _ hW4
  have hcard := hPJ.card_eq
  omega

end Crit

end CFSG.QuasithinUnique.DoubleA3
