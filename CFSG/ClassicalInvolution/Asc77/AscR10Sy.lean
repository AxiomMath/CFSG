module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Asc77.R10

variable {G : Type} [Group G]

theorem r_conj_eq_iff {b s s' : G} :
    s * b * s⁻¹ = s' * b * s'⁻¹ ↔ s⁻¹ * s' ∈ Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc s⁻¹ * s' * b = s⁻¹ * (s' * b * s'⁻¹) * s' := by group
      _ = s⁻¹ * (s * b * s⁻¹) * s' := by rw [h]
      _ = b * (s⁻¹ * s') := by group
  · intro h
    calc s * b * s⁻¹ = s * (b * (s⁻¹ * s')) * s'⁻¹ := by group
      _ = s * (s⁻¹ * s' * b) * s'⁻¹ := by rw [h]
      _ = s' * b * s'⁻¹ := by group

variable [Finite G]

theorem r_relIndex_le_card {S : Subgroup G} {b : G} {F : Finset G}
    (hF : ∀ s ∈ S, s * b * s⁻¹ ∈ F) :
    (Subgroup.centralizer ({b} : Set G)).relIndex S ≤ F.card := by
  classical
  set H : Subgroup ↥S := (Subgroup.centralizer ({b} : Set G)).subgroupOf S with hH
  let f : ↥S ⧸ H → G := Quotient.lift (fun s : ↥S => (s : G) * b * (s : G)⁻¹) (by
    intro x y hxy
    have h1 : x⁻¹ * y ∈ H := QuotientGroup.leftRel_apply.mp hxy
    have h2 : (x : G)⁻¹ * (y : G) ∈ Subgroup.centralizer ({b} : Set G) := h1
    exact r_conj_eq_iff.mpr h2)
  have hinj : Function.Injective f := by
    intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn with | _ x => ?_
    induction q₂ using Quotient.inductionOn with | _ y => ?_
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    exact r_conj_eq_iff.mp h
  let g : ↥S ⧸ H → F := fun q => ⟨f q, by
    induction q using Quotient.inductionOn with | _ x => exact hF x x.2⟩
  have hginj : Function.Injective g := by
    intro q₁ q₂ h
    exact hinj (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective g hginj
  rw [Nat.card_eq_fintype_card (α := F), Fintype.card_coe] at this
  exact this


theorem r_card_le_relIndex {S : Subgroup G} {b : G} {F : Finset G}
    (hF : ∀ y ∈ F, ∃ s ∈ S, s * b * s⁻¹ = y) :
    F.card ≤ (Subgroup.centralizer ({b} : Set G)).relIndex S := by
  classical
  set H : Subgroup ↥S := (Subgroup.centralizer ({b} : Set G)).subgroupOf S with hH
  choose! σ hσS hσ using hF
  let g : F → ↥S ⧸ H := fun y => QuotientGroup.mk ⟨σ y.1, hσS y.1 y.2⟩
  have hginj : Function.Injective g := by
    intro y₁ y₂ h
    have h1 : (⟨σ y₁.1, hσS y₁.1 y₁.2⟩ : ↥S)⁻¹ * ⟨σ y₂.1, hσS y₂.1 y₂.2⟩ ∈ H :=
      QuotientGroup.eq.mp h
    have h2 : (σ y₁.1)⁻¹ * σ y₂.1 ∈ Subgroup.centralizer ({b} : Set G) := h1
    have h3 := r_conj_eq_iff.mpr h2
    apply Subtype.ext
    rw [← hσ y₁.1 y₁.2, ← hσ y₂.1 y₂.2]
    exact h3
  have := Nat.card_le_card_of_injective g hginj
  rw [Nat.card_eq_fintype_card (α := F), Fintype.card_coe] at this
  exact this

theorem r_relIndex_eq_pow {S : Subgroup G} (hS : IsPGroup 2 S) (b : G) :
    ∃ m : ℕ, (Subgroup.centralizer ({b} : Set G)).relIndex S = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hS.index ((Subgroup.centralizer ({b} : Set G)).subgroupOf S)

theorem r_exists_conj_le_sylow {P : Subgroup G} (hP : IsPGroup 2 P) (S : Sylow 2 G) :
    ∃ g : G, ∀ x ∈ P, g⁻¹ * x * g ∈ (S : Subgroup G) := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
    rw [hg]
    exact hPQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  simpa [MulAut.smul_def] using hxQ


theorem r_card_le_of_isPGroup {S : Sylow 2 G} {b : G} (hb2 : b * b = 1) {m : ℕ}
    (hup : (Subgroup.centralizer ({b} : Set G)).relIndex (S : Subgroup G) ≤ m)
    (hlow : ∀ x : G, x⁻¹ * b * x ∈ (S : Subgroup G) →
      m ≤ (Subgroup.centralizer ({x⁻¹ * b * x} : Set G)).relIndex (S : Subgroup G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ Subgroup.centralizer ({b} : Set G)) :
    Nat.card P ≤ Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (S : Subgroup G)) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbz : IsPGroup 2 (Subgroup.zpowers b) := by
    have h1 : orderOf b ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hb2)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hPN : P ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    intro x hx
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)
    have hcomm : ∀ y ∈ Subgroup.zpowers b, x * y * x⁻¹ = y := by
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : x * b * x⁻¹ = b := by rw [hxb]; group
      rw [← conj_zpow, this]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm y hy]
      exact hy
    · intro hy
      have h3 := hcomm _ hy
      have h4 : x * y * x⁻¹ = y := by
        have e1 : x * (x * y * x⁻¹ * x⁻¹) = x * (y * x⁻¹) := by
          calc x * (x * y * x⁻¹ * x⁻¹) = x * (x * y * x⁻¹) * x⁻¹ := by group
            _ = x * y * x⁻¹ := h3
            _ = x * (y * x⁻¹) := by group
        exact mul_right_cancel (mul_left_cancel e1)
      rw [← h4]
      exact hy
  have hP₂ : IsPGroup 2 (P ⊔ Subgroup.zpowers b : Subgroup G) :=
    hP.to_sup_of_normal_right' hbz hPN
  obtain ⟨g, hg⟩ := r_exists_conj_le_sylow hP₂ S
  have hbS : g⁻¹ * b * g ∈ (S : Subgroup G) :=
    hg b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hle1 : Nat.card P ≤ Nat.card ↥(Subgroup.centralizer ({g⁻¹ * b * g} : Set G) ⊓
      (S : Subgroup G)) := by
    let φ : ↥P → ↥(Subgroup.centralizer ({g⁻¹ * b * g} : Set G) ⊓ (S : Subgroup G)) := fun x =>
      ⟨g⁻¹ * x.1 * g, Subgroup.mem_inf.mpr ⟨by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxb : x.1 * b = b * x.1 := Subgroup.mem_centralizer_singleton_iff.mp (hPC x.2)
        calc g⁻¹ * x.1 * g * (g⁻¹ * b * g) = g⁻¹ * (x.1 * b) * g := by group
          _ = g⁻¹ * (b * x.1) * g := by rw [hxb]
          _ = g⁻¹ * b * g * (g⁻¹ * x.1 * g) := by group,
        hg x.1 (Subgroup.mem_sup_left x.2)⟩⟩
    have hφ : Function.Injective φ := by
      intro x y h
      have h1 : g⁻¹ * x.1 * g = g⁻¹ * y.1 * g := congrArg Subtype.val h
      apply Subtype.ext
      have h2 := mul_right_cancel h1
      exact mul_left_cancel h2
    exact Nat.card_le_card_of_injective φ hφ
  have hidx := hlow g hbS
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({g⁻¹ * b * g} : Set G))
    (S : Subgroup G)
  have h3 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({b} : Set G)) (S : Subgroup G)
  have hSpos : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
  have hbpos : 0 < (Subgroup.centralizer ({b} : Set G)).relIndex (S : Subgroup G) := by
    rcases Nat.eq_zero_or_pos ((Subgroup.centralizer ({b} : Set G)).relIndex
      (S : Subgroup G)) with h | h
    · rw [h, zero_mul] at h3
      omega
    · exact h
  have hle2 : Nat.card ↥(Subgroup.centralizer ({g⁻¹ * b * g} : Set G) ⊓ (S : Subgroup G)) ≤
      Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (S : Subgroup G)) := by
    refine le_of_mul_le_mul_left ?_ hbpos
    calc (Subgroup.centralizer ({b} : Set G)).relIndex (S : Subgroup G) *
          Nat.card ↥(Subgroup.centralizer ({g⁻¹ * b * g} : Set G) ⊓ (S : Subgroup G))
        ≤ (Subgroup.centralizer ({g⁻¹ * b * g} : Set G)).relIndex (S : Subgroup G) *
          Nat.card ↥(Subgroup.centralizer ({g⁻¹ * b * g} : Set G) ⊓ (S : Subgroup G)) :=
          Nat.mul_le_mul_right _ (hup.trans hidx)
      _ = Nat.card (S : Subgroup G) := h1
      _ = _ := h3.symm
  exact hle1.trans hle2


theorem r_exists_conj_into_sylow {S : Sylow 2 G} {b : G} (hb2 : b * b = 1) {m : ℕ}
    (hup : (Subgroup.centralizer ({b} : Set G)).relIndex (S : Subgroup G) ≤ m)
    (hlow : ∀ x : G, x⁻¹ * b * x ∈ (S : Subgroup G) →
      m ≤ (Subgroup.centralizer ({x⁻¹ * b * x} : Set G)).relIndex (S : Subgroup G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ Subgroup.centralizer ({b} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({b} : Set G), ∀ x ∈ P, c⁻¹ * x * c ∈ (S : Subgroup G) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set Q' : Subgroup ↥C := (S : Subgroup G).subgroupOf C with hQ'
  have hQ'2 : IsPGroup 2 Q' := S.isPGroup'.comap_subtype
  have hmax : ∀ P' : Subgroup ↥C, IsPGroup 2 P' → Nat.card P' ≤ Nat.card Q' := by
    intro P' hP'
    have hP'G : IsPGroup 2 (P'.map C.subtype) := hP'.map _
    have hle : P'.map C.subtype ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have h1 := r_card_le_of_isPGroup hb2 hup hlow hP'G hle
    have e1 : Nat.card ↥(P'.map C.subtype) = Nat.card P' :=
      (Nat.card_congr (Subgroup.equivMapOfInjective P' C.subtype C.subtype_injective).toEquiv).symm
    have e2 : Nat.card Q' = Nat.card ↥(C ⊓ (S : Subgroup G)) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype (S : Subgroup G) C]
      exact Nat.card_congr (Subgroup.equivMapOfInjective Q' C.subtype C.subtype_injective).toEquiv
    rw [← e1, e2]
    exact h1
  obtain ⟨P₀, hQP₀⟩ := hQ'2.exists_le_sylow
  have hP₀card : Nat.card (P₀ : Subgroup ↥C) ≤ Nat.card Q' := hmax _ P₀.isPGroup'
  have hP₀eq : Q' = (P₀ : Subgroup ↥C) := Subgroup.eq_of_le_of_card_ge hQP₀ hP₀card
  have hP'' : IsPGroup 2 (P.subgroupOf C) := hP.comap_subtype
  obtain ⟨P₁, hP''P₁⟩ := hP''.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C P₀ P₁
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hx1 : (⟨x, hPC hx⟩ : ↥C) ∈ (P₁ : Subgroup ↥C) := hP''P₁ hx
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx1
  have hx2 : (MulAut.conj c)⁻¹ • (⟨x, hPC hx⟩ : ↥C) ∈ Q' := hP₀eq ▸ hx1
  simpa [hQ', Subgroup.mem_subgroupOf, MulAut.smul_def] using hx2

end CFSG.ClassicalInvolution.Asc77.R10
