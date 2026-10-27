module

public import CFSG.GH74.BNPair.Basic
public import CFSG.GroupActions.SplitBNPair

public section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {G : Type*} [Group G] {B N U : Subgroup G} {I : Type*} {n : I → N}

theorem SplitBN.isTitsSystem [Finite I] [hN : (cartan B N).Normal]
    (h : CFSG.GroupActions.SplitBN B N U n) :
    ∃ S : Finset (WeylGroup B N), IsTitsSystem B N S ∧
      (S : Set (WeylGroup B N)) = Set.range fun i => ((n i : N) : WeylGroup B N) := by
  obtain ⟨_, hgen, _, hord, hclos, hmul, hne, -⟩ := h
  have hfin : (Set.range fun i => ((n i : N) : WeylGroup B N)).Finite := Set.finite_range _
  refine ⟨hfin.toFinset, ?_, by simp⟩
  have hS : ∀ s : WeylGroup B N, s ∈ hfin.toFinset ↔ ∃ i, ((n i : N) : WeylGroup B N) = s := by
    intro s; simp
  have key : ∀ n' : N, ((n' : N) : WeylGroup B N) ∈ hfin.toFinset →
      ∃ (i : I) (h' : G), h' ∈ B ∧ (n' : G) = (n i : G) * h' := by
    intro n' hn'
    obtain ⟨i, hi⟩ := (hS _).1 hn'
    refine ⟨i, (n i : G)⁻¹ * n', mk_eq_mk_iff.1 hi, by simp⟩
  refine ⟨hgen, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, rfl⟩ := (hS s).1 hs
    exact hord i
  · rw [Set.Finite.coe_toFinset]
    exact hclos
  · intro n' m hn'
    obtain ⟨i, h', hh', e⟩ := key n' hn'
    obtain ⟨j, hj⟩ := (hS _).1 hn'
    have hmk : ((n i : N) : WeylGroup B N) = (n' : WeylGroup B N) := by
      obtain ⟨j', hj'⟩ := (hS _).1 hn'
      exact mk_eq_mk_iff.2 (by
        have : (n i : G)⁻¹ * (n' : G) = h' := by rw [e]; simp
        rw [this]; exact hh')
    rintro x ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩
    have hx : (n' : G) * b * (m : G) ∈
        ({((n i : N) : G)} : Set G) * (B : Set G) * {(m : G)} := by
      refine Set.mem_mul.2 ⟨(n i : G) * (h' * b), Set.mem_mul.2 ⟨n i, rfl, h' * b,
        B.mul_mem hh' hb, rfl⟩, m, rfl, ?_⟩
      rw [e]; simp [mul_assoc]
    rcases hmul i (m : G) m.2 hx with h1 | h1
    · left
      obtain ⟨b₁, hb₁, b₂, hb₂, hx1⟩ := mem_dcoset_iff.1 h1
      refine (mem_dc_of_lift (n := n i * m) ?_).2 ⟨b₁, hb₁, b₂, hb₂, ?_⟩
      · rw [QuotientGroup.mk_mul, hmk]
      · have hx2 : (n' : G) * b * (m : G) = b₁ * ((n i : G) * m) * b₂ := hx1
        show (n' : G) * b * (m : G) = _
        rw [hx2]; simp
    · right
      obtain ⟨b₁, hb₁, b₂, hb₂, hx1⟩ := mem_dcoset_iff.1 h1
      exact (mem_dc_of_lift (n := m) rfl).2 ⟨b₁, hb₁, b₂, hb₂, hx1⟩
  · intro n' hn' heq
    obtain ⟨i, h', hh', e⟩ := key n' hn'
    have hmk : ((n i : N) : WeylGroup B N) = (n' : WeylGroup B N) := by
      exact mk_eq_mk_iff.2 (by
        have : (n i : G)⁻¹ * (n' : G) = h' := by rw [e]; simp
        rw [this]; exact hh')
    have hsq : (n' : G) * n' ∈ B := by
      have h2 := hord i
      have h3 : ((n i : N) : WeylGroup B N) * (n i : N) = 1 := by
        have := pow_orderOf_eq_one ((n i : N) : WeylGroup B N)
        rw [h2, sq] at this
        exact this
      rw [hmk] at h3
      have : ((n' * n' : N) : WeylGroup B N) = 1 := by rw [QuotientGroup.mk_mul]; exact h3
      simpa using mk_eq_one_iff.1 this
    refine hne i ?_
    rintro x ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩
    have hc : h'⁻¹ * b * h' ∈ B := B.mul_mem (B.mul_mem (B.inv_mem hh') hb) hh'
    have h4 : (n' : G) * (h'⁻¹ * b * h') * n' ∈ (B : Set G) := by
      rw [← heq]
      exact Set.mem_mul.2 ⟨n' * (h'⁻¹ * b * h'), Set.mem_mul.2 ⟨n', rfl, _, hc, rfl⟩, n', rfl, rfl⟩
    have h5 : (n i : G) * b * ((n i : G))⁻¹ = ((n' : G) * (h'⁻¹ * b * h') * n') * ((n' : G) * n')⁻¹ := by
      have : (n i : G) = n' * h'⁻¹ := by rw [e]; simp
      rw [this]; group
    show (n i : G) * b * ((n i : G))⁻¹ ∈ B
    rw [h5]
    exact B.mul_mem h4 (B.inv_mem hsq)

end CFSG.GH74.BNPair
