module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Final
public import CFSG.CGT.PushingUpLit.LIT.A4.L34Star

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.RankThree.PartOne.SolD3 (Blk3)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def blocksOf (M X : Subgroup G) : Set (Subgroup G) := {Y | ∃ m ∈ M, Y = conjSub m X}

variable [Finite G] {M X : Subgroup G}

namespace L34

theorem comm_conj (c : A4Cfg G M X) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M)
    (hne : conjSub m X ≠ conjSub m' X) :
    ∀ x ∈ conjSub m X, ∀ y ∈ conjSub m' X, x * y = y * x := by
  intro x hx y hy
  have hk : m⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hm) hm'
  have hne' : conjSub (m⁻¹ * m') X ≠ X := by
    intro e
    apply hne
    calc conjSub m X = conjSub m (conjSub (m⁻¹ * m') X) := by rw [e]
      _ = conjSub m' X := by
          rw [conjSub_conjSub]
          congr 1
          group
  have hcomm := c.commutator_conj_eq_bot hk hne'
  have hx' : m⁻¹ * x * m ∈ X := mem_conjSub_iff.1 hx
  have hy' : m⁻¹ * y * m ∈ conjSub (m⁻¹ * m') X := by
    have h1 : m'⁻¹ * y * m' ∈ X := mem_conjSub_iff.1 hy
    have h2 := conj_mem_conjSub (g := m⁻¹ * m') h1
    have e : (m⁻¹ * m') * (m'⁻¹ * y * m') * (m⁻¹ * m')⁻¹ = m⁻¹ * y * m := by group
    rwa [e] at h2
  have h3 : ⁅m⁻¹ * x * m, m⁻¹ * y * m⁆ ∈ ⁅X, conjSub (m⁻¹ * m') X⁆ :=
    Subgroup.commutator_mem_commutator hx' hy'
  rw [hcomm] at h3
  have h4 := commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 h3)
  calc x * y = m * ((m⁻¹ * x * m) * (m⁻¹ * y * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * y * m) * (m⁻¹ * x * m)) * m⁻¹ := by rw [h4]
    _ = y * x := by group

theorem fam_of_a4cfg (c : A4Cfg G M X) (hnn : ∃ m ∈ M, conjSub m X ≠ X) :
    Fam M (blocksOf M X) where
  blk := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.SolD3.exists_blk3 c.short c.nat
    exact ⟨m * a * m⁻¹, Blk3.conj ha m⟩
  le := by
    rintro _ ⟨m, hm, rfl⟩
    exact c.conj_le hm
  comm := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ hne x hx y hy
    exact comm_conj c hm hm' hne x hx y hy
  perm := by
    rintro k hk _ ⟨m, hm, rfl⟩
    exact ⟨k * m, M.mul_mem hk hm, conjSub_conjSub k m X⟩
  conj_le := by
    rintro _ ⟨m, hm, rfl⟩ g hg
    rw [conjSub_conjSub] at hg
    exact (M.mul_mem_cancel_right hm).1 (c.mem_of_conj_le hg)
  cent := by
    rintro z hz1 hz2 ⟨_, ⟨m, hm, rfl⟩, hz⟩
    exact cent_of_a4cfg c hz1 hz2 hm hz
  two := by
    obtain ⟨m, hm, hne⟩ := hnn
    exact ⟨X, ⟨1, M.one_mem, (conjSub_one X).symm⟩, conjSub m X, ⟨m, hm, rfl⟩, hne.symm⟩

end L34

end CFSG.CGT.PushingUpLit.A4
