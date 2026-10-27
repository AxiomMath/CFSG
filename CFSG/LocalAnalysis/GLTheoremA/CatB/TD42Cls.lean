module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.Monster.B.Co2

namespace TD42

section Generic

variable {G : Type*} [Group G]

theorem centralizer_conj (g s : G) :
    Subgroup.centralizer ({g * s * g⁻¹} : Set G) =
      (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g⁻¹ * z * g, ?_, by simp [MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : g⁻¹ * (z * (g * s * g⁻¹)) * g = g⁻¹ * ((g * s * g⁻¹) * z) * g := by rw [h]
    calc g⁻¹ * z * g * s = g⁻¹ * (z * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * z) * g := this
      _ = s * (g⁻¹ * z * g) := by group
  · rintro ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    show (MulAut.conj g) w * (g * s * g⁻¹) = (g * s * g⁻¹) * (MulAut.conj g) w
    simp only [MulAut.conj_apply]
    calc g * w * g⁻¹ * (g * s * g⁻¹) = g * (w * s) * g⁻¹ := by group
      _ = g * (s * w) * g⁻¹ := by rw [hw]
      _ = g * s * g⁻¹ * (g * w * g⁻¹) := by group

theorem card_centralizer_conj (g s : G) :
    Nat.card (Subgroup.centralizer ({g * s * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  rw [centralizer_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem centralizer_pow_two_eq {x : G} (hx : x ^ 3 = 1) :
    Subgroup.centralizer ({x ^ 2} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have hx4 : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
    rw [hx4]
    exact (Commute.pow_left (show Commute (x ^ 2) z from hz.symm) 2).eq.symm
  · intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact (Commute.pow_right (show Commute z x from hz) 2).eq

theorem centralizer_pow_eq {x : G} (hx : x ^ 3 = 1) {e : ℕ} (he : e = 1 ∨ e = 2) :
    Subgroup.centralizer ({x ^ e} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · exact centralizer_pow_two_eq hx

theorem centralizer_inv (s : G) :
    Subgroup.centralizer ({s⁻¹} : Set G) = Subgroup.centralizer ({s} : Set G) := by
  ext z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact show Commute z s⁻¹ ↔ Commute z s from Commute.inv_right_iff

end Generic

section PModel


theorem map_centralizer_rho (hT : Nat.card lineGroup = 211341312) (s : lineGroup) :
    (Subgroup.centralizer ({s} : Set lineGroup)).map d4Rho =
      Subgroup.centralizer ({d4Rho s} : Set (Equiv.Perm (Fin 2457))) ⊓ d4P := by
  ext p
  rw [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, d4Rho_mem g⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [← map_mul, ← map_mul, hg]
  · rintro ⟨hp, hpP⟩
    rw [← d4Rho_range] at hpP
    obtain ⟨g, rfl⟩ := hpP
    refine ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply d4Rho_injective hT
    rw [map_mul, map_mul]
    exact hp

theorem card_centralizer_rho (hT : Nat.card lineGroup = 211341312) (s : lineGroup) :
    Nat.card (Subgroup.centralizer ({s} : Set lineGroup)) =
      Nat.card (Subgroup.centralizer ({d4Rho s} : Set (Equiv.Perm (Fin 2457))) ⊓ d4P : Subgroup _) := by
  rw [← map_centralizer_rho hT s]
  exact (Subgroup.card_map_of_injective (d4Rho_injective hT)).symm

end PModel

section Classes

theorem exists_class
    (hT : Nat.card lineGroup = 211341312) (s : lineGroup) (hs : orderOf s = 3) :
    ∃ g : lineGroup, ∃ c e : ℕ, c < 2 ∧ (e = 1 ∨ e = 2) ∧ d4Rho (g * s * g⁻¹) = d4X c ^ e := by
  have hxo : orderOf (d4Rho s) = 3 := by rw [orderOf_injective d4Rho (d4Rho_injective hT) s, hs]
  obtain ⟨k, hk, j, hj, e, he, hvk⟩ := exists_conj_rep d4Q_le card_d4Q
    (fun j => permOfArr 2457 d4Lines[j]!) (fun c => permOfArr 2457 d4Lines[c]!)
    (fun j => permOfArr 2457 d4Trans[j]!) (fun j => d4Rec.getD j 0) (r := 31)
    (fun g hg hg3 => d4_lines hg hg3) (fun j hj => d4_trans hj) (d4Rho_mem s) hxo
  have hrec : d4Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec d4_lines_check.2.2.2 hj)
  rw [← d4Rho_range] at hk
  obtain ⟨g₀, rfl⟩ := hk
  refine ⟨g₀⁻¹, d4Rec.getD j 0, e, hrec, he, ?_⟩
  have hvk' : d4Rho s = d4Rho g₀ * d4X (d4Rec.getD j 0) ^ e * (d4Rho g₀)⁻¹ := hvk
  rw [map_mul, map_mul, map_inv, inv_inv, hvk']
  group

@[expose] def Is3A (s : lineGroup) : Prop :=
  ∃ g : lineGroup, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ d4Rho (g * s * g⁻¹) = d4X 0 ^ e

theorem card_centralizer_d4X {c : ℕ}
    (hc : c < 2) {e : ℕ} (he : e = 1 ∨ e = 2) :
    Nat.card (Subgroup.centralizer ({d4X c ^ e} : Set (Equiv.Perm (Fin 2457))) ⊓ d4P : Subgroup _) =
      if c = 0 then 1512 else 648 := by
  rw [centralizer_pow_eq (d4X_cube (by omega)) he]
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · rw [← d4_caseA.1]
    simpa using d4_caseA.2
  · rw [← d4_caseB.1]
    simpa using d4_caseB.2

theorem card_centralizer_of_class
    (hT : Nat.card lineGroup = 211341312) {s g : lineGroup}
    {c e : ℕ} (hc : c < 2) (he : e = 1 ∨ e = 2) (h : d4Rho (g * s * g⁻¹) = d4X c ^ e) :
    Nat.card (Subgroup.centralizer ({s} : Set lineGroup)) = if c = 0 then 1512 else 648 := by
  rw [← card_centralizer_conj g s, card_centralizer_rho hT, h]
  exact card_centralizer_d4X hc he

theorem card_centralizer_of_is3A
    (hT : Nat.card lineGroup = 211341312) {s : lineGroup}
    (h : Is3A s) : Nat.card (Subgroup.centralizer ({s} : Set lineGroup)) = 1512 := by
  obtain ⟨g, e, he, hg⟩ := h
  simpa using card_centralizer_of_class hT (c := 0) (by norm_num) he hg

theorem is3A_or_card648
    (hT : Nat.card lineGroup = 211341312) (s : lineGroup)
    (hs : orderOf s = 3) :
    Is3A s ∨ Nat.card (Subgroup.centralizer ({s} : Set lineGroup)) = 648 := by
  obtain ⟨g, c, e, hc, he, h⟩ := exists_class hT s hs
  have hcard := card_centralizer_of_class hT hc he h
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · exact Or.inl ⟨g, e, he, h⟩
  · right
    simpa using hcard

theorem exists_conj_of_is3A
    (hT : Nat.card lineGroup = 211341312) {s s' : lineGroup} (h : Is3A s) (h' : Is3A s') :
    ∃ g : lineGroup, g * s' * g⁻¹ = s ∨ g * s' * g⁻¹ = s⁻¹ := by
  obtain ⟨g₁, e₁, he₁, h₁⟩ := h
  obtain ⟨g₂, e₂, he₂, h₂⟩ := h'
  have hinj := d4Rho_injective hT
  have hx3 : d4X 0 ^ 3 = 1 := d4X_cube (by norm_num)
  have hx2 : d4X 0 ^ 2 = (d4X 0)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx3)
  have key : ∀ {a b : lineGroup}, d4Rho a = d4Rho b → a = b := fun h => hinj h
  have same : d4Rho (g₁ * s * g₁⁻¹) = d4Rho (g₂ * s' * g₂⁻¹) →
      ∃ g : lineGroup, g * s' * g⁻¹ = s := by
    intro h
    have := key h
    refine ⟨g₁⁻¹ * g₂, ?_⟩
    calc g₁⁻¹ * g₂ * s' * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * s' * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * (g₁ * s * g₁⁻¹) * g₁ := by rw [this]
      _ = s := by group
  have opp : d4Rho (g₁ * s * g₁⁻¹) = (d4Rho (g₂ * s' * g₂⁻¹))⁻¹ →
      ∃ g : lineGroup, g * s' * g⁻¹ = s⁻¹ := by
    intro h
    rw [← map_inv] at h
    have := key h
    refine ⟨g₁⁻¹ * g₂, ?_⟩
    have h2 : g₂ * s' * g₂⁻¹ = (g₁ * s * g₁⁻¹)⁻¹ := by rw [this]; group
    calc g₁⁻¹ * g₂ * s' * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * s' * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * (g₁ * s * g₁⁻¹)⁻¹ * g₁ := by rw [h2]
      _ = s⁻¹ := by group
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · obtain ⟨g, hg⟩ := same (by rw [h₁, h₂])
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨g, hg⟩ := opp (by rw [h₁, h₂, hx2, inv_inv, pow_one])
    exact ⟨g, Or.inr hg⟩
  · obtain ⟨g, hg⟩ := opp (by rw [h₁, h₂, hx2, pow_one])
    exact ⟨g, Or.inr hg⟩
  · obtain ⟨g, hg⟩ := same (by rw [h₁, h₂])
    exact ⟨g, Or.inl hg⟩

end Classes

end TD42

end CFSG.LocalAnalysis.GLTheoremA

end
