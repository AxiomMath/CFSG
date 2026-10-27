module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem inv_comm_eq {X : Type*} [Group X] {x y c : X} (hc : ∀ g, g * c = c * g)
    (h : x * y * x⁻¹ * y⁻¹ = c) : x⁻¹ * y⁻¹ * x * y = c := by
  have hxy : x * y = c * (y * x) := by
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = c * (y * x) := by rw [h]
  calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by group
    _ = x⁻¹ * y⁻¹ * (c * (y * x)) := by rw [hxy]
    _ = x⁻¹ * y⁻¹ * ((y * x) * c) := by rw [hc (y * x)]
    _ = c := by group

theorem exists_uIdx
    {U : Subgroup (Equiv.Perm (Fin 42))}
    (hU : U = U1 ∨ U = U2) : ∃ I ∈ uIdx, (∀ t ∈ U, ∃ k ∈ I, wordPerm (tg k) = t) ∧
      ∀ k ∈ I, k < 64 ∧ wordPerm (tg k) ∈ U := by
  rcases hU with rfl | rfl
  · refine ⟨List.range 16, by simp [uIdx], fun t ht => ?_, fun k hk => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := mem_U1_iff.1 ht
      exact ⟨k, List.mem_range.2 hk, rfl⟩
    · have hk' := List.mem_range.1 hk
      exact ⟨by omega, tg_mem_U1 hk'⟩
  · refine ⟨(List.range 16).map (4 * ·), by simp [uIdx], fun t ht => ?_, fun k hk => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := mem_U2_iff.1 ht
      exact ⟨4 * k, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, rfl⟩
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
      have hk'' := List.mem_range.1 hk'
      exact ⟨by omega, tg_mem_U2 hk''⟩

variable {G : Type} [Group G] {J P : Subgroup G}

theorem exists_U
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hPJ : P ≤ J)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) {E : Subgroup G}
    (hEP : E ≤ P) (h2 : ∀ {y : G} (hy : y ∈ E),
      q (jq J ⟨y, hPJ (hEP hy)⟩) * q (jq J ⟨y, hPJ (hEP hy)⟩) = 1) :
    ∃ U : Subgroup (Equiv.Perm (Fin 42)), (U = U1 ∨ U = U2) ∧
      ∀ {y : G} (hy : y ∈ E), q (jq J ⟨y, hPJ (hEP hy)⟩) ∈ U := by
  have hTE : ∀ {y : G} (hy : y ∈ E), q (jq J ⟨y, hPJ (hEP hy)⟩) ∈ T0 := fun hy =>
    (hT _).2 ⟨_, hEP hy, _, rfl⟩
  have hmul : ∀ {u v : G} (hu : u ∈ E) (hv : v ∈ E),
      q (jq J ⟨u * v, hPJ (hEP (E.mul_mem hu hv))⟩) =
        q (jq J ⟨u, hPJ (hEP hu)⟩) * q (jq J ⟨v, hPJ (hEP hv)⟩) := fun hu hv => by
    rw [← map_mul, ← map_mul]
    rfl
  by_cases h1 : ∀ {y : G} (hy : y ∈ E), q (jq J ⟨y, hPJ (hEP hy)⟩) ∈ U1
  · exact ⟨U1, Or.inl rfl, h1⟩
  · push Not at h1
    obtain ⟨u₁, hu₁, hn1⟩ := h1
    have hu₁2 := (involution_mem_U (hTE hu₁) (h2 hu₁)).resolve_left hn1
    refine ⟨U2, Or.inr rfl, fun {u} hu => ?_⟩
    by_contra hn2
    have hu1 := (involution_mem_U (hTE hu) (h2 hu)).resolve_right hn2
    have hprod := involution_mem_U (hTE (E.mul_mem hu₁ hu)) (h2 (E.mul_mem hu₁ hu))
    rw [hmul hu₁ hu] at hprod
    rcases hprod with hp1 | hp2
    · exact hn1 (by simpa using U1.mul_mem hp1 (U1.inv_mem hu1))
    · exact hn2 (by simpa using U2.mul_mem (U2.inv_mem hu₁2) hp2)

namespace IsQSetting

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem exists_transv
    (h : IsQSetting q l)
    [Finite E] (hcyc : IsCyclic q.ker) (h4 : Nat.card q.ker = 4) {ζ : E} (hζk : ζ ∈ q.ker)
    (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) {I : List ℕ} (hI : I ∈ uIdx) {k₁ k₂ : ℕ} (hk₁ : k₁ ∈ I)
    (hk₂ : k₂ ∈ I) (h₁0 : k₁ ≠ 0) (h₂0 : k₂ ≠ 0) (h₁₂ : k₁ ≠ k₂) {y₁ y₂ : E}
    (hy₁ : q y₁ = wordPerm (tg k₁)) (hy₂ : q y₂ = wordPerm (tg k₂)) (f₁ f₂ : Bool) :
    ∃ w ∈ I, y₁ * l (cv (tw w)) * y₁⁻¹ * (l (cv (tw w)))⁻¹ = (if f₁ then ζ else 1) ∧
      y₂ * l (cv (tw w)) * y₂⁻¹ * (l (cv (tw w)))⁻¹ = (if f₂ then ζ else 1) := by
  obtain ⟨κ, hκ⟩ := h.exists_kclass hcyc h4 hζk hζ1 hζ2
  obtain ⟨w, hw, hb₁, hb₂⟩ := exists_trans hκ.mem hI hk₁ hk₂ h₁0 h₂0 h₁₂ f₁ f₂
  have hk64 : ∀ {k : ℕ}, k ∈ I → k < 64 := by
    intro k hk
    simp only [uIdx, List.mem_cons, List.mem_nil_iff, or_false] at hI
    rcases hI with rfl | rfl
    · have := List.mem_range.1 hk
      omega
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
      have := List.mem_range.1 hk'
      omega
  have key : ∀ {k : ℕ} {y : E} {f : Bool}, k ∈ I → q y = wordPerm (tg k) →
      commBit κ k w f = true →
      y * l (cv (tw w)) * y⁻¹ * (l (cv (tw w)))⁻¹ = (if f then ζ else 1) := by
    intro k y f hk hy hb
    have h1 := h.lift_comm_of_bit hκ hζ2 hb
    have hz : (l (cv (tw k)))⁻¹ * y ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h.q_lift (hk64 hk), hy, inv_mul_cancel]
    have hzc := mem_center_iff.mp (h.ker_le hz)
    have hy' : y = l (cv (tw k)) * ((l (cv (tw k)))⁻¹ * y) := by group
    rw [hy', ← h1]
    generalize (l (cv (tw k)))⁻¹ * y = z at hzc
    generalize l (cv (tw k)) = x
    generalize l (cv (tw w)) = p
    calc x * z * p * (x * z)⁻¹ * p⁻¹ = x * (z * p) * z⁻¹ * x⁻¹ * p⁻¹ := by group
      _ = x * (p * z) * z⁻¹ * x⁻¹ * p⁻¹ := by rw [hzc p]
      _ = x * p * x⁻¹ * p⁻¹ := by group
  exact ⟨w, hw, key hk₁ hy₁ hb₁, key hk₂ hy₂ hb₂⟩

end IsQSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
