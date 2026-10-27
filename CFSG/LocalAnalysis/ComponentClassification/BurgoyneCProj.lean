module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProj

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement

theorem commute_commutatorElement_of_central {G : Type*} [Group G] {A B₁ B₂ z₁ z₂ : G}
    (hz₁ : z₁ ∈ center G) (hz₂ : z₂ ∈ center G) (h₁ : B₁ * A * B₁⁻¹ = z₁ * A)
    (h₂ : B₂ * A * B₂⁻¹ = z₂ * A) : ⁅B₁, B₂⁆ * A = A * ⁅B₁, B₂⁆ := by
  have hc : ∀ (g : G) {z : G}, z ∈ center G → MulAut.conj g z = z := by
    intro g z hz
    rw [MulAut.conj_apply, mem_center_iff.1 hz g, mul_inv_cancel_right]
  have hinv : ∀ {B z : G}, z ∈ center G → B * A * B⁻¹ = z * A → MulAut.conj B⁻¹ A = z⁻¹ * A := by
    intro B z hz h
    rw [MulAut.conj_apply, inv_inv]
    have e : A = z⁻¹ * (B * A * B⁻¹) := by rw [h, inv_mul_cancel_left]
    calc B⁻¹ * A * B = B⁻¹ * (z⁻¹ * (B * A * B⁻¹)) * B := by rw [← e]
      _ = (B⁻¹ * z⁻¹) * B * A := by group
      _ = z⁻¹ * A := by rw [mem_center_iff.1 (inv_mem hz) B⁻¹, inv_mul_cancel_right]
  have e₁ : MulAut.conj B₁ A = z₁ * A := h₁
  have e₂ : MulAut.conj B₂ A = z₂ * A := h₂
  have e₁' := hinv hz₁ h₁
  have e₂' := hinv hz₂ h₂
  have c₂ : ∀ g, MulAut.conj g z₂ = z₂ := fun g => hc g hz₂
  have c₁' : ∀ g, MulAut.conj g z₁⁻¹ = z₁⁻¹ := fun g => hc g (inv_mem hz₁)
  have c₂' : ∀ g, MulAut.conj g z₂⁻¹ = z₂⁻¹ := fun g => hc g (inv_mem hz₂)
  have key : MulAut.conj ⁅B₁, B₂⁆ A = A := by
    simp only [commutatorElement_def, map_mul, MulAut.mul_apply, e₂', e₁', e₂, e₁, c₂, c₁', c₂']
    have hzz : z₁ * z₂ = z₂ * z₁ := mem_center_iff.1 hz₂ z₁
    calc z₂⁻¹ * (z₁⁻¹ * (z₂ * (z₁ * A))) = (z₂⁻¹ * (z₁⁻¹ * z₂) * z₁) * A := by group
      _ = A := by
        rw [show z₁⁻¹ * z₂ = z₂ * z₁⁻¹ from by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hzz, mul_assoc, mul_inv_cancel, mul_one]]
        group
  calc ⁅B₁, B₂⁆ * A = MulAut.conj ⁅B₁, B₂⁆ A * ⁅B₁, B₂⁆ := by
        rw [MulAut.conj_apply, inv_mul_cancel_right]
    _ = A * ⁅B₁, B₂⁆ := by rw [key]

theorem conj_mem_centralizer_of_central {G : Type*} [Group G] {A B m z : G} (hz : z ∈ center G)
    (hBz : B * A * B⁻¹ = z * A) (hm : m * A = A * m) : B * m * B⁻¹ * A = A * (B * m * B⁻¹) := by
  have hBi : B⁻¹ * A * B = z⁻¹ * A := by
    have e : A = z⁻¹ * (B * A * B⁻¹) := by rw [hBz, inv_mul_cancel_left]
    calc B⁻¹ * A * B = B⁻¹ * (z⁻¹ * (B * A * B⁻¹)) * B := by rw [← e]
      _ = (B⁻¹ * z⁻¹) * B * A := by group
      _ = z⁻¹ * A := by rw [mem_center_iff.1 (inv_mem hz) B⁻¹, inv_mul_cancel_right]
  have hzm : m * z⁻¹ = z⁻¹ * m := mem_center_iff.1 (inv_mem hz) m
  have hzB : B * z⁻¹ = z⁻¹ * B := mem_center_iff.1 (inv_mem hz) B
  calc B * m * B⁻¹ * A = B * m * (B⁻¹ * A * B) * B⁻¹ := by group
    _ = B * (m * z⁻¹) * A * B⁻¹ := by rw [hBi]; group
    _ = B * z⁻¹ * (m * A) * B⁻¹ := by rw [hzm]; group
    _ = z⁻¹ * (B * A * B⁻¹) * (B * m * B⁻¹) := by rw [hm, hzB]; group
    _ = A * (B * m * B⁻¹) := by rw [hBz, inv_mul_cancel_left]


section Quot

variable {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]

theorem exists_central_of_commute_mk (hZ : Z ≤ center G) {A B : G}
    (h : QuotientGroup.mk' Z B * QuotientGroup.mk' Z A =
      QuotientGroup.mk' Z A * QuotientGroup.mk' Z B) :
    ∃ z ∈ center G, B * A * B⁻¹ = z * A := by
  have h1 : (QuotientGroup.mk' Z (B * A * B⁻¹) : G ⧸ Z) = QuotientGroup.mk' Z A := by
    rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  have hw : (B * A * B⁻¹)⁻¹ * A ∈ center G := hZ (QuotientGroup.eq.1 h1)
  refine ⟨((B * A * B⁻¹)⁻¹ * A)⁻¹, inv_mem hw, ?_⟩
  have e1 : ((B * A * B⁻¹)⁻¹ * A)⁻¹ * A = A * ((B * A * B⁻¹)⁻¹ * A)⁻¹ :=
    (mem_center_iff.1 (inv_mem hw) A).symm
  rw [e1]
  group

theorem commutator_centralizer_le_mk (hZ : Z ≤ center G) (A : G) :
    ⁅centralizer ({QuotientGroup.mk' Z A} : Set (G ⧸ Z)),
        centralizer ({QuotientGroup.mk' Z A} : Set (G ⧸ Z))⁆ ≤
      (centralizer ({A} : Set G)).map (QuotientGroup.mk' Z) := by
  rw [commutator_le]
  intro h₁ hh₁ h₂ hh₂
  obtain ⟨B₁, rfl⟩ := QuotientGroup.mk'_surjective Z h₁
  obtain ⟨B₂, rfl⟩ := QuotientGroup.mk'_surjective Z h₂
  obtain ⟨z₁, hz₁, e₁⟩ := exists_central_of_commute_mk hZ (mem_centralizer_singleton_iff.1 hh₁)
  obtain ⟨z₂, hz₂, e₂⟩ := exists_central_of_commute_mk hZ (mem_centralizer_singleton_iff.1 hh₂)
  refine ⟨⁅B₁, B₂⁆, mem_centralizer_singleton_iff.2 ?_, map_commutatorElement _ _ _⟩
  exact commute_commutatorElement_of_central hz₁ hz₂ e₁ e₂

theorem le_map_commutator_of_perfect_mk (hZ : Z ≤ center G) (A : G) {L : Subgroup (G ⧸ Z)}
    (hL : L ≤ centralizer ({QuotientGroup.mk' Z A} : Set (G ⧸ Z))) (hperf : ⁅L, L⁆ = L) :
    L ≤ ⁅centralizer ({A} : Set G), centralizer ({A} : Set G)⁆.map (QuotientGroup.mk' Z) := by
  have h1 : L ≤ (centralizer ({A} : Set G)).map (QuotientGroup.mk' Z) := by
    rw [← hperf]
    exact (commutator_mono hL hL).trans (commutator_centralizer_le_mk hZ A)
  rw [map_commutator, ← hperf]
  exact commutator_mono h1 h1

theorem isSubnormal_map_mk (hZ : Z ≤ center G) (A : G) {M : Subgroup G}
    (hM : M ≤ centralizer ({A} : Set G))
    (hn : ∀ B ∈ centralizer ({A} : Set G), ∀ m ∈ M, B * m * B⁻¹ ∈ M) :
    M.map (QuotientGroup.mk' Z) ≤ centralizer ({QuotientGroup.mk' Z A} : Set (G ⧸ Z)) ∧
      ((M.map (QuotientGroup.mk' Z)).subgroupOf
        (centralizer ({QuotientGroup.mk' Z A} : Set (G ⧸ Z)))).IsSubnormal := by
  set C := centralizer ({QuotientGroup.mk' Z A} : Set (G ⧸ Z)) with hCdef
  have hCA : (centralizer ({A} : Set G)).map (QuotientGroup.mk' Z) ≤ C := by
    rintro _ ⟨m, hm, rfl⟩
    rw [hCdef, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 hm]
  have hnorm : (((centralizer ({A} : Set G)).map (QuotientGroup.mk' Z)).subgroupOf C).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨m, hm, hma⟩ := ha
    obtain ⟨B, hB⟩ := QuotientGroup.mk'_surjective Z (b : G ⧸ Z)
    obtain ⟨z, hz, hBz⟩ := exists_central_of_commute_mk hZ (A := A) (B := B)
      (by rw [hB]; exact mem_centralizer_singleton_iff.1 b.2)
    refine ⟨B * m * B⁻¹, mem_centralizer_singleton_iff.2
      (conj_mem_centralizer_of_central hz hBz (mem_centralizer_singleton_iff.1 hm)), ?_⟩
    rw [map_mul, map_mul, map_inv, hB, hma]
    rfl
  refine ⟨(map_mono hM).trans hCA,
    PSL.isSubnormal_subgroupOf_of_normalizes (map_mono hM) ?_ (Normal.isSubnormal hnorm)⟩
  rintro _ ⟨B, hB, rfl⟩ _ ⟨m, hm, rfl⟩
  exact ⟨B * m * B⁻¹, hn B hB m hm, by simp only [map_mul, map_inv]⟩

end Quot

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H₀ : Subgroup (GL ι K)}

theorem exists_central_of_commute {A B : H₀}
    (h : projH H₀ B * projH H₀ A = projH H₀ A * projH H₀ B) :
    ∃ z ∈ center H₀, B * A * B⁻¹ = z * A := by
  have h1 : projH H₀ (B * A * B⁻¹) = projH H₀ A := by
    rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  rw [projH_eq_projH_iff] at h1
  obtain ⟨w, hw⟩ : ∃ w, w = (B * A * B⁻¹)⁻¹ * A := ⟨_, rfl⟩
  have hwc : w ∈ center H₀ := by rw [hw]; exact scalars_subgroupOf_le_center h1
  refine ⟨w⁻¹, inv_mem hwc, ?_⟩
  have e1 : w⁻¹ * A = A * w⁻¹ := (mem_center_iff.1 (inv_mem hwc) A).symm
  rw [e1, hw]
  group

theorem commutator_centralizer_le (A : H₀) :
    ⁅centralizer ({projH H₀ A} : Set (StatedProj H₀)),
        centralizer ({projH H₀ A} : Set (StatedProj H₀))⁆ ≤
      (centralizer ({A} : Set H₀)).map (projH H₀) := by
  rw [commutator_le]
  intro h₁ hh₁ h₂ hh₂
  obtain ⟨B₁, rfl⟩ := projH_surjective h₁
  obtain ⟨B₂, rfl⟩ := projH_surjective h₂
  obtain ⟨z₁, hz₁, e₁⟩ := exists_central_of_commute (mem_centralizer_singleton_iff.1 hh₁)
  obtain ⟨z₂, hz₂, e₂⟩ := exists_central_of_commute (mem_centralizer_singleton_iff.1 hh₂)
  refine ⟨⁅B₁, B₂⁆, mem_centralizer_singleton_iff.2 ?_, map_commutatorElement _ _ _⟩
  exact commute_commutatorElement_of_central hz₁ hz₂ e₁ e₂

theorem le_map_commutator_of_perfect (A : H₀) {L : Subgroup (StatedProj H₀)}
    (hL : L ≤ centralizer ({projH H₀ A} : Set (StatedProj H₀))) (hperf : ⁅L, L⁆ = L) :
    L ≤ ⁅centralizer ({A} : Set H₀), centralizer ({A} : Set H₀)⁆.map (projH H₀) := by
  have h1 : L ≤ (centralizer ({A} : Set H₀)).map (projH H₀) := by
    rw [← hperf]
    exact (commutator_mono hL hL).trans (commutator_centralizer_le A)
  rw [map_commutator]
  rw [← hperf]
  exact commutator_mono h1 h1

theorem normal_map_of_normalizes (A : H₀) {M : Subgroup H₀}
    (hM : M ≤ centralizer ({A} : Set H₀))
    (hn : ∀ B : H₀, (∃ z ∈ center H₀, B * A * B⁻¹ = z * A) → ∀ m ∈ M, B * m * B⁻¹ ∈ M) :
    M.map (projH H₀) ≤ centralizer ({projH H₀ A} : Set (StatedProj H₀)) ∧
      ((M.map (projH H₀)).subgroupOf
        (centralizer ({projH H₀ A} : Set (StatedProj H₀)))).Normal := by
  have hle : M.map (projH H₀) ≤ centralizer ({projH H₀ A} : Set (StatedProj H₀)) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (mem_centralizer_singleton_iff.1 (hM hm))]
  refine ⟨hle, ⟨fun a ha b => ?_⟩⟩
  rw [mem_subgroupOf] at ha ⊢
  obtain ⟨m, hm, hma⟩ := ha
  obtain ⟨B, hB⟩ := projH_surjective (b : StatedProj H₀)
  have hBc := exists_central_of_commute (A := A) (B := B)
    (by rw [hB]; exact mem_centralizer_singleton_iff.1 b.2)
  refine ⟨B * m * B⁻¹, hn B hBc m hm, ?_⟩
  rw [map_mul, map_mul, map_inv, hB, hma]
  rfl

end CFSG.ComponentClassification.Burgoyne.C
