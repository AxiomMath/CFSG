module

public import CFSG.GH74.Uniqueness.Section173Basic
public import CFSG.GH74.Uniqueness.Section174Core

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem BenderSub.exists_conj_of_mem_borel
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) (Q : Sylow 2 (↥F ⧸ center ↥F)) :
    ∃ y ∈ F, ∀ x : ↥F, (QuotientGroup.mk x : ↥F ⧸ center ↥F) ∈ Bender.borel (Q : Subgroup _) →
      (x : X) ∈ conjugate M y := by
  obtain ⟨T₀, hT₀⟩ := hB.borel
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥F ⧸ center ↥F) T₀ Q
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨(g₀ : X)⁻¹, F.inv_mem g₀.2, fun x hx => ?_⟩
  set g' : ↥F ⧸ center ↥F := QuotientGroup.mk g₀ with hg'
  have hxN : g'⁻¹ * QuotientGroup.mk x * g' ∈
      normalizer ((T₀ : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) := by
    change QuotientGroup.mk x ∈
      normalizer ((Q : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) at hx
    rw [← hg, Sylow.coe_subgroup_smul] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key := (Subgroup.mem_normalizer_iff.mp hx) (g' * h * g'⁻¹)
    simp only [Subgroup.mem_smul_pointwise_iff_exists, MulAut.smul_def, MulAut.conj_apply] at key
    constructor
    · intro hh
      obtain ⟨b, hb, hbe⟩ := key.mp ⟨h, hh, rfl⟩
      have : b = g'⁻¹ * QuotientGroup.mk x * g' * h * (g'⁻¹ * QuotientGroup.mk x * g')⁻¹ := by
        have := congrArg (fun z => g'⁻¹ * z * g') hbe
        rw [show g'⁻¹ * (g' * b * g'⁻¹) * g' = b by group] at this
        rw [this]
        group
      rw [← this]
      exact hb
    · intro hh
      obtain ⟨b, hb, hbe⟩ := key.mpr ⟨_, hh, by group⟩
      have : b = h := by
        have := congrArg (fun z => g'⁻¹ * z * g') hbe
        rwa [show g'⁻¹ * (g' * b * g'⁻¹) * g' = b by group,
          show g'⁻¹ * (g' * h * g'⁻¹) * g' = h by group] at this
      rw [← this]
      exact hb
  rw [← hT₀] at hxN
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hxN
  have hmM : ((m : ↥F) : X) ∈ M := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hm)).1
  have hz : m⁻¹ * (g₀⁻¹ * x * g₀) ∈ center ↥F := by
    rw [← QuotientGroup.eq]
    rw [QuotientGroup.mk'_apply] at hmx
    rw [hmx]
    simp [hg']
  have hzM := hB.center_le S _ hz
  rw [mem_conjugate_iff, inv_inv]
  have h1 := M.mul_mem hmM hzM
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at h1
  exact h1

theorem BenderSub.false_of_pair
    (S : ZDSetup X Z M) (h311 : Lemma311BenderStmt) {F : Subgroup X}
    {n e : ℕ} (hB : BenderSub Z M F n 3 e) {A : Subgroup X} (hAF : A ≤ F)
    (hA : Odd (Nat.card A)) {s : X} (hsF : s ∈ F) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ A) (hpts : ∀ y ∈ F, ¬ A ≤ conjugate M y)
    (hN : ∀ x ∈ F, (∀ a ∈ A, x * a * x⁻¹ ∈ A) → x ∈ A ∨ x * s ∈ A)
    (hc1 : (centralizer ({s} : Set X)).relIndex A ≡ 1 [MOD 2 ^ n])
    (hc2 : (centralizer ({s} : Set X)).relIndex A ≠ 1) : False := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hZodd := hB.odd_card_center
  have hN2 : ∀ x ∈ F, Odd (orderOf x) → (∀ a ∈ A, x * a * x⁻¹ ∈ A) → x ∈ A := by
    intro x hxF hodd hx
    rcases hN x hxF hx with h | h
    · exact h
    · have hxx : x * x ∈ A := by
        have h1 := A.mul_mem h (hsA _ h)
        rwa [hsi, show x * s * (s * (x * s) * s) = x * (s * s) * x * (s * s) by group, hs2,
          mul_one, mul_one] at h1
      exact Bender.mem_of_mul_self_mem_of_odd hodd hxx
  have hZo : ∀ z ∈ center ↥F, Odd (orderOf z) := fun z hz =>
    Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard _ hz)
  have hZA : ∀ z ∈ center ↥F, (z : X) ∈ A := by
    intro z hz
    have hcomm : ∀ y ∈ F, (z : X) * y = y * z := fun y hy =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm
    refine hN2 z z.2 (by rw [Subgroup.orderOf_coe]; exact hZo z hz) fun a ha => ?_
    rw [hcomm a (hAF ha), mul_assoc, mul_inv_cancel, mul_one]
    exact ha
  set φ : ↥F →* ↥F ⧸ center ↥F := QuotientGroup.mk' (center ↥F) with hφ
  set A₁ : Subgroup ↥F := A.subgroupOf F with hA₁
  set s₁ : ↥F := ⟨s, hsF⟩ with hs₁
  have hs₁2 : s₁ * s₁ = 1 := Subtype.ext hs2
  have hs₁i : s₁⁻¹ = s₁ := inv_eq_of_mul_eq_one_right hs₁2
  have hA₁card : Nat.card A₁ = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF).toEquiv
  have hAbarodd : Odd (Nat.card ↥(A₁.map φ)) :=
    Odd.of_dvd_nat (by rw [hA₁card]; exact hA) (Subgroup.card_map_dvd A₁ φ)
  have hsbar2 : φ s₁ * φ s₁ = 1 := by rw [← map_mul, hs₁2, map_one]
  have hsbar1 : φ s₁ ≠ 1 := by
    intro h
    have hmem : s₁ ∈ center ↥F := by
      rw [← QuotientGroup.ker_mk' (center ↥F)]
      exact MonoidHom.mem_ker.mpr h
    have h2 : orderOf s₁ = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs₁2) (fun h => hs1 (congrArg Subtype.val h))
    have h3 := hZo s₁ hmem
    rw [h2] at h3
    exact absurd h3 (by decide)
  have hsAbar : ∀ a ∈ A₁.map φ, φ s₁ * a * (φ s₁)⁻¹ ∈ A₁.map φ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨s₁ * a * s₁⁻¹, Subgroup.mem_subgroupOf.mpr (hsA _ (Subgroup.mem_subgroupOf.mp ha)),
      by rw [map_mul, map_mul, map_inv]⟩
  have hborel : ∀ Q : Sylow 2 (↥F ⧸ center ↥F),
      ¬ A₁.map φ ≤ Bender.borel (Q : Subgroup (↥F ⧸ center ↥F)) := by
    intro Q hQ
    obtain ⟨y, hyF, hy⟩ := hB.exists_conj_of_mem_borel S Q
    apply hpts y hyF
    intro a ha
    exact hy ⟨a, hAF ha⟩ (hQ ⟨⟨a, hAF ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
  have hNbar : ∀ x : ↥F ⧸ center ↥F, (∀ a ∈ A₁.map φ, x * a * x⁻¹ ∈ A₁.map φ) →
      x ∈ A₁.map φ ∨ x * φ s₁ ∈ A₁.map φ := by
    intro x hx
    obtain ⟨x₁, rfl⟩ : ∃ x₁, φ x₁ = x := QuotientGroup.mk'_surjective (center ↥F) x
    have hx₁A : ∀ a ∈ A, (x₁ : X) * a * (x₁ : X)⁻¹ ∈ A := by
      intro a ha
      have h1 := hx (φ ⟨a, hAF ha⟩) ⟨⟨a, hAF ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.mp h1
      have hz : b⁻¹ * (x₁ * ⟨a, hAF ha⟩ * x₁⁻¹) ∈ center ↥F := by
        rw [← QuotientGroup.eq]
        exact hbe
      have h2 := A.mul_mem (Subgroup.mem_subgroupOf.mp hb) (hZA _ hz)
      simpa using h2
    rcases hN x₁ x₁.2 hx₁A with h | h
    · exact Or.inl ⟨x₁, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    · exact Or.inr ⟨x₁ * s₁, Subgroup.mem_subgroupOf.mpr h, by rw [map_mul]⟩
  have hcomap : (centralizer ({φ s₁} : Set (↥F ⧸ center ↥F))).comap φ =
      centralizer ({s₁} : Set ↥F) := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hw : x * s₁ * x⁻¹ * s₁⁻¹ ∈ center ↥F := by
        rw [← QuotientGroup.ker_mk' (center ↥F), MonoidHom.mem_ker]
        change φ (x * s₁ * x⁻¹ * s₁⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
        group
      set w := x * s₁ * x⁻¹ * s₁⁻¹ with hwdef
      have hw1 : s₁ * w * s₁⁻¹ = w := by
        rw [(Subgroup.mem_center_iff.mp hw s₁), mul_assoc, mul_inv_cancel, mul_one]
      have hw2 : s₁ * w * s₁⁻¹ = w⁻¹ := by
        rw [hwdef, hs₁i]
        calc s₁ * (x * s₁ * x⁻¹ * s₁) * s₁ = s₁ * x * s₁ * x⁻¹ * (s₁ * s₁) := by group
          _ = s₁ * x * s₁ * x⁻¹ := by rw [hs₁2, mul_one]
          _ = (x * s₁ * x⁻¹ * s₁)⁻¹ := by
            rw [show (x * s₁ * x⁻¹ * s₁)⁻¹ = s₁⁻¹ * x * s₁⁻¹ * x⁻¹ by group, hs₁i]
      have hww : w * w = 1 := by
        have h3 : w = w⁻¹ := hw1.symm.trans hw2
        calc w * w = w * w⁻¹ := by rw [← h3]
          _ = 1 := mul_inv_cancel w
      have hw0 : w = 1 := Sec172.eq_one_of_sq hww (hZo w hw)
      calc x * s₁ = (x * s₁ * x⁻¹ * s₁⁻¹) * s₁ * x := by group
        _ = s₁ * x := by rw [← hwdef, hw0, one_mul]
    · intro h
      rw [← map_mul, ← map_mul, h]
  have hcent : centralizer ({s₁} : Set ↥F) = (centralizer ({s} : Set X)).subgroupOf F := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hc : (centralizer ({φ s₁} : Set (↥F ⧸ center ↥F))).relIndex (A₁.map φ) =
      (centralizer ({s} : Set X)).relIndex A := by
    rw [← Subgroup.relIndex_comap, hcomap, hcent, hA₁]
    exact Subgroup.relIndex_subgroupOf hAF
  exact Sec174.false_of_unitary h311 hB.bender hAbarodd hsbar2 hsbar1 hsAbar hborel hNbar
    (by rw [hc]; exact hc1) (by rw [hc]; exact hc2)

end CFSG.GH74.Uniqueness
