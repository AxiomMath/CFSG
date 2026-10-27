module

public import CFSG.GH74.BNPair.Building

public noncomputable section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {S : Finset (WeylGroup B N)} {a b : WeylGroup B N} {n : ℕ}

theorem rankTwoAction_vtx (g : X) (i : Bool) (x : X) :
    rankTwoAction B N a b g (vtx B N a b i x) = vtx B N a b i (x * g⁻¹) := by
  refine Subtype.ext ?_
  show ((pgen B N a b i : Subgroup X) : Set X) * {x} * {g⁻¹} =
    ((pgen B N a b i : Subgroup X) : Set X) * {x * g⁻¹}
  rw [mul_assoc, Set.singleton_mul_singleton]

theorem mem_action_iff {g z : X} {u : rankTwoVertices B N a b} :
    z ∈ ((rankTwoAction B N a b g u : rankTwoVertices B N a b) : Set X) ↔
      z * g ∈ (u : Set X) := by
  show z ∈ (u : Set X) * {g⁻¹} ↔ _
  rw [Set.mem_mul]
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, y, rfl, rfl⟩
    simpa using hp
  · intro h
    exact ⟨z * g, h, g⁻¹, rfl, by simp⟩

theorem rankTwoAction_adj (g : X) (u v : rankTwoVertices B N a b) :
    (buildingGraph B N a b).Adj (rankTwoAction B N a b g u) (rankTwoAction B N a b g v) ↔
      (buildingGraph B N a b).Adj u v := by
  constructor
  · rintro ⟨hne, z, hz1, hz2⟩
    refine ⟨fun h => hne (by rw [h]), z * g, mem_action_iff.1 hz1, mem_action_iff.1 hz2⟩
  · rintro ⟨hne, z, hz1, hz2⟩
    refine ⟨fun h => hne ((rankTwoAction B N a b g).injective h), z * g⁻¹, ?_, ?_⟩
    · exact mem_action_iff.2 (by simpa using hz1)
    · exact mem_action_iff.2 (by simpa using hz2)

namespace Rank2

variable (R : Rank2 B N S a b n)
include R

theorem vtype_action (g : X) (u : rankTwoVertices B N a b) :
    vtype B N a b (rankTwoAction B N a b g u) = vtype B N a b u := by
  obtain ⟨i, x, rfl⟩ := exists_vtx u
  rw [rankTwoAction_vtx, R.vtype_vtx, R.vtype_vtx]

theorem exists_action_adj {u v u' v' : rankTwoVertices B N a b}
    (h : (buildingGraph B N a b).Adj u v) (h' : (buildingGraph B N a b).Adj u' v')
    (ht : vtype B N a b u = vtype B N a b u') :
    ∃ g : X, rankTwoAction B N a b g u = u' ∧ rankTwoAction B N a b g v = v' := by
  obtain ⟨z, hzu, hzv⟩ := h.2
  obtain ⟨z', hzu', hzv'⟩ := h'.2
  have e1 := R.eq_vtx_of_mem hzu
  have e2 := R.eq_vtx_not_of_adj h hzv
  have e3 := R.eq_vtx_of_mem hzu'
  have e4 := R.eq_vtx_not_of_adj h' hzv'
  rw [← ht] at e3 e4
  refine ⟨z'⁻¹ * z, ?_, ?_⟩
  · rw [e1, rankTwoAction_vtx, e3]
    congr 1
    group
  · rw [e2, rankTwoAction_vtx, e4]
    congr 1
    group

theorem exists_action_vtx {u u' : rankTwoVertices B N a b}
    (ht : vtype B N a b u = vtype B N a b u') :
    ∃ g : X, rankTwoAction B N a b g u = u' := by
  obtain ⟨i, x, rfl⟩ := exists_vtx u
  obtain ⟨i', x', rfl⟩ := exists_vtx u'
  rw [R.vtype_vtx, R.vtype_vtx] at ht
  subst ht
  refine ⟨x'⁻¹ * x, ?_⟩
  rw [rankTwoAction_vtx]
  congr 1
  group

theorem path_eq_of_chambers {f₁ f₂ : ℕ → rankTwoVertices B N a b} {m : ℕ} (hm : m + 1 ≤ n)
    (hadj₁ : ∀ i, i < m + 1 → (buildingGraph B N a b).Adj (f₁ i) (f₁ (i + 1)))
    (hnb₁ : ∀ i, i + 2 ≤ m + 1 → f₁ i ≠ f₁ (i + 2))
    (hadj₂ : ∀ i, i < m + 1 → (buildingGraph B N a b).Adj (f₂ i) (f₂ (i + 1)))
    (hnb₂ : ∀ i, i + 2 ≤ m + 1 → f₂ i ≠ f₂ (i + 2))
    (ht : vtype B N a b (f₁ 0) = vtype B N a b (f₂ 0))
    {x₁ x₂ y₁ y₂ : X} (hx₁0 : x₁ ∈ (f₁ 0 : Set X)) (hx₁1 : x₁ ∈ (f₁ 1 : Set X))
    (hx₂0 : x₂ ∈ (f₂ 0 : Set X)) (hx₂1 : x₂ ∈ (f₂ 1 : Set X)) (hxx : x₂ * x₁⁻¹ ∈ B)
    (hy₁0 : y₁ ∈ (f₁ m : Set X)) (hy₁1 : y₁ ∈ (f₁ (m + 1) : Set X))
    (hy₂0 : y₂ ∈ (f₂ m : Set X)) (hy₂1 : y₂ ∈ (f₂ (m + 1) : Set X)) (hyy : y₂ * y₁⁻¹ ∈ B) :
    ∀ i, i ≤ m + 1 → f₁ i = f₂ i := by
  have hpar₁ := R.vtype_path hadj₁
  have hpar₂ := R.vtype_path hadj₂
  have hty : ∀ i, i ≤ m + 1 → vtype B N a b (f₁ i) = vtype B N a b (f₂ i) := by
    intro i hi
    rw [hpar₁ i hi, hpar₂ i hi, ht]
  have hclaim : ∀ d, d ≤ m → ∀ c₁ c₂ : X, c₁ ∈ (f₁ (m - d) : Set X) → c₁ ∈ (f₁ (m - d + 1) : Set X) →
      c₂ ∈ (f₂ (m - d) : Set X) → c₂ ∈ (f₂ (m - d + 1) : Set X) → c₂ * c₁⁻¹ ∈ B := by
    intro d
    induction d with
    | zero =>
      intro _ c₁ c₂ hc₁0 hc₁1 hc₂0 hc₂1
      simp only [Nat.sub_zero] at hc₁0 hc₁1 hc₂0 hc₂1
      have h1 : y₁ * c₁⁻¹ ∈ B := R.chamber_unique (hadj₁ m (by omega)) hc₁0 hc₁1 hy₁0 hy₁1
      have h2 : c₂ * y₂⁻¹ ∈ B := R.chamber_unique (hadj₂ m (by omega)) hy₂0 hy₂1 hc₂0 hc₂1
      have : c₂ * c₁⁻¹ = (c₂ * y₂⁻¹) * (y₂ * y₁⁻¹) * (y₁ * c₁⁻¹) := by group
      rw [this]
      exact B.mul_mem (B.mul_mem h2 hyy) h1
    | succ d ih =>
      intro hd c₁ c₂ hc₁0 hc₁1 hc₂0 hc₂1
      set i := m - (d + 1) with hi
      have hi1 : i + 1 = m - d := by omega
      obtain ⟨d₁, hd₁0, hd₁1⟩ := (hadj₁ (i + 1) (by omega)).2
      obtain ⟨d₂, hd₂0, hd₂1⟩ := (hadj₂ (i + 1) (by omega)).2
      have hdd : d₂ * d₁⁻¹ ∈ B := by
        refine ih (by omega) d₁ d₂ ?_ ?_ ?_ ?_
        · rw [← hi1]; exact hd₁0
        · rw [← hi1]; exact hd₁1
        · rw [← hi1]; exact hd₂0
        · rw [← hi1]; exact hd₂1
      have hg₁ := R.gallery f₁ (m + 1) (by omega) hadj₁ hnb₁
      have hg₂ := R.gallery f₂ (m + 1) (by omega) hadj₂ hnb₂
      have hc₁' := hg₁ i (by omega) x₁ c₁ hx₁0 hx₁1 hc₁0 hc₁1
      have hd₁' := hg₁ (i + 1) (by omega) x₁ d₁ hx₁0 hx₁1 hd₁0 hd₁1
      have hc₂' := hg₂ i (by omega) x₂ c₂ hx₂0 hx₂1 hc₂0 hc₂1
      have hx₁₂ : x₁ * x₂⁻¹ ∈ B := by simpa using B.inv_mem hxx
      rw [← ht] at hc₂'
      have hc₂'' := hc₂'.congr_left hx₁₂
      have hs := R.gen_mem (vtype B N a b (f₁ (i + 1)))
      have hpar := hpar₁ (i + 1) (by omega)
      generalize vtype B N a b (f₁ 0) = t at hc₁' hd₁' hc₂'' hpar
      have hlet : gen a b (vtype B N a b (f₁ (i + 1))) *
          altWord (gen a b (!t)) (gen a b t) i = altWord (gen a b (!t)) (gen a b t) (i + 1) := by
        rw [altWord_succ_left, hpar]
        by_cases he : Even i <;> simp [he, Nat.even_add_one]
      have hss := R.tits.mul_self_gen hs
      have hlet' : gen a b (vtype B N a b (f₁ (i + 1))) *
          altWord (gen a b (!t)) (gen a b t) (i + 1) = altWord (gen a b (!t)) (gen a b t) i := by
        rw [← hlet, ← mul_assoc, hss, one_mul]
      have hlen : wordLength (S : Set (WeylGroup B N))
          (gen a b (vtype B N a b (f₁ (i + 1))) * altWord (gen a b (!t)) (gen a b t) (i + 1)) <
          wordLength (S : Set (WeylGroup B N)) (altWord (gen a b (!t)) (gen a b t) (i + 1)) := by
        rw [hlet']
        have h5 := R.ell_alt (!t) (j := i) (by omega)
        have h6 := R.ell_alt (!t) (j := i + 1) (by omega)
        rw [Bool.not_not] at h5 h6
        omega
      have hP : ∀ {c d : X}, c ∈ (f₁ (i + 1) : Set X) → d ∈ (f₁ (i + 1) : Set X) →
          c * d⁻¹ ∈ pgen B N a b (vtype B N a b (f₁ (i + 1))) := by
        intro c d hc hd
        have e := R.eq_vtx_of_mem hd
        have : c ∈ ((vtx B N a b (vtype B N a b (f₁ (i + 1))) d : rankTwoVertices B N a b) :
            Set X) := by rw [← e]; exact hc
        exact mem_vtx.1 this
      have hz : c₁ * d₁⁻¹ ∈ pgen B N a b (vtype B N a b (f₁ (i + 1))) := hP hc₁1 hd₁0
      have hz' : c₂ * d₁⁻¹ ∈ pgen B N a b (vtype B N a b (f₁ (i + 1))) := by
        have h2 : c₂ * d₂⁻¹ ∈ pgen B N a b (vtype B N a b (f₂ (i + 1))) := by
          have e := R.eq_vtx_of_mem hd₂0
          have : c₂ ∈ ((vtx B N a b (vtype B N a b (f₂ (i + 1))) d₂ :
              rankTwoVertices B N a b) : Set X) := by rw [← e]; exact hc₂1
          exact mem_vtx.1 this
        rw [← hty (i + 1) (by omega)] at h2
        have := (pgen B N a b _).mul_mem h2 (R.B_le_pgen _ hdd)
        simpa [mul_assoc] using this
      exact WPos.panel_unique R.tits hs hlen hz hz' (x := x₁) (by rw [hlet']; exact hc₁')
        (by rw [hlet']; exact hc₂'')
  intro i hi
  by_cases him : i ≤ m
  · obtain ⟨c₁, hc₁0, hc₁1⟩ := (hadj₁ i (by omega)).2
    obtain ⟨c₂, hc₂0, hc₂1⟩ := (hadj₂ i (by omega)).2
    have hB : c₂ * c₁⁻¹ ∈ B := by
      refine hclaim (m - i) (by omega) c₁ c₂ ?_ ?_ ?_ ?_ <;>
        rw [show m - (m - i) = i by omega] <;> assumption
    calc f₁ i = vtx B N a b (vtype B N a b (f₁ i)) c₁ := R.eq_vtx_of_mem hc₁0
      _ = vtx B N a b (vtype B N a b (f₁ i)) c₂ := (vtx_eq_vtx (R.B_le_pgen _ hB)).symm
      _ = vtx B N a b (vtype B N a b (f₂ i)) c₂ := by rw [hty i hi]
      _ = f₂ i := (R.eq_vtx_of_mem hc₂0).symm
  · have him' : i = m + 1 := by omega
    subst him'
    obtain ⟨c₁, hc₁0, hc₁1⟩ := (hadj₁ m (by omega)).2
    obtain ⟨c₂, hc₂0, hc₂1⟩ := (hadj₂ m (by omega)).2
    have hB : c₂ * c₁⁻¹ ∈ B := by
      refine hclaim 0 (Nat.zero_le _) c₁ c₂ ?_ ?_ ?_ ?_ <;> simpa using ‹_›
    calc f₁ (m + 1) = vtx B N a b (!vtype B N a b (f₁ m)) c₁ :=
          R.eq_vtx_not_of_adj (hadj₁ m (by omega)) hc₁1
      _ = vtx B N a b (!vtype B N a b (f₁ m)) c₂ := (vtx_eq_vtx (R.B_le_pgen _ hB)).symm
      _ = vtx B N a b (!vtype B N a b (f₂ m)) c₂ := by rw [hty m (by omega)]
      _ = f₂ (m + 1) := (R.eq_vtx_not_of_adj (hadj₂ m (by omega)) hc₂1).symm

theorem exists_action_path {f₁ f₂ : ℕ → rankTwoVertices B N a b} {m : ℕ} (hm : m + 1 ≤ n)
    (hadj₁ : ∀ i, i < m + 1 → (buildingGraph B N a b).Adj (f₁ i) (f₁ (i + 1)))
    (hnb₁ : ∀ i, i + 2 ≤ m + 1 → f₁ i ≠ f₁ (i + 2))
    (hadj₂ : ∀ i, i < m + 1 → (buildingGraph B N a b).Adj (f₂ i) (f₂ (i + 1)))
    (hnb₂ : ∀ i, i + 2 ≤ m + 1 → f₂ i ≠ f₂ (i + 2))
    (ht : vtype B N a b (f₁ 0) = vtype B N a b (f₂ 0)) :
    ∃ g : X, ∀ i, i ≤ m + 1 → rankTwoAction B N a b g (f₁ i) = f₂ i := by
  obtain ⟨x₁, hx₁0, hx₁1⟩ := (hadj₁ 0 (by omega)).2
  obtain ⟨x₂, hx₂0, hx₂1⟩ := (hadj₂ 0 (by omega)).2
  obtain ⟨y₁, hy₁0, hy₁1⟩ := (hadj₁ m (by omega)).2
  obtain ⟨y₂, hy₂0, hy₂1⟩ := (hadj₂ m (by omega)).2
  have hg₁ := R.gallery f₁ (m + 1) (by omega) hadj₁ hnb₁ m (by omega) x₁ y₁ hx₁0 hx₁1 hy₁0 hy₁1
  have hg₂ := R.gallery f₂ (m + 1) (by omega) hadj₂ hnb₂ m (by omega) x₂ y₂ hx₂0 hx₂1 hy₂0 hy₂1
  rw [← ht] at hg₂
  obtain ⟨g, hg1, hg2⟩ := exists_translate hg₁ hg₂
  have hadj₁' : ∀ i, i < m + 1 → (buildingGraph B N a b).Adj
      (rankTwoAction B N a b g (f₁ i)) (rankTwoAction B N a b g (f₁ (i + 1))) :=
    fun i hi => (rankTwoAction_adj g _ _).2 (hadj₁ i hi)
  have hnb₁' : ∀ i, i + 2 ≤ m + 1 →
      rankTwoAction B N a b g (f₁ i) ≠ rankTwoAction B N a b g (f₁ (i + 2)) :=
    fun i hi h => hnb₁ i hi ((rankTwoAction B N a b g).injective h)
  have ht' : vtype B N a b (rankTwoAction B N a b g (f₁ 0)) = vtype B N a b (f₂ 0) := by
    rw [R.vtype_action]; exact ht
  refine ⟨g, fun i hi => ?_⟩
  exact R.path_eq_of_chambers (f₁ := fun i => rankTwoAction B N a b g (f₁ i)) hm hadj₁' hnb₁'
    hadj₂ hnb₂ ht' (x₁ := x₁ * g⁻¹) (x₂ := x₂) (y₁ := y₁ * g⁻¹) (y₂ := y₂)
    (mem_action_iff.2 (by simpa using hx₁0)) (mem_action_iff.2 (by simpa using hx₁1)) hx₂0 hx₂1
    (by simpa using B.inv_mem hg1)
    (mem_action_iff.2 (by simpa using hy₁0)) (mem_action_iff.2 (by simpa using hy₁1)) hy₂0 hy₂1
    (by simpa using B.inv_mem hg2) i hi

end Rank2

end CFSG.GH74.BNPair
