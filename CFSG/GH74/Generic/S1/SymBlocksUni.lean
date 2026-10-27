module

public import CFSG.GH74.Generic.S1.BlkOps
public import CFSG.GH74.Generic.S1.SymBlocksUniOps
public import CFSG.GH74.Generic.S1.FrameNormUni

public section

namespace CFSG.GH74.Generic.S1

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution

@[expose] noncomputable def uniBlockOps {q : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) : BlockOps F (StatedSU 4 q F) where
  blk := SymBlocksUni.uniBlk F q
  blk_symm := SymBlocksUni.uniBlk_symm F q
  perfect a b hab := by
    obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨h.prime⟩
    have : CharP F p := h.charP
    have hq5 : 5 ≤ p ^ f := by
      have := h.one_lt_pow
      omega
    exact SymBlocksUni.uniBlk_perfect hF hq5 hab
  commute a b c d _ _ hac had hbc hbd g hg h hh := SymBlocksUni.uniBlk_commute hac had hbc hbd hg hh
  comm_refl a b c _ hca hcb g hg := SymBlocksUni.uniBlk_comm_refl hca hcb hg
  perfect_le a b c d hab hac had hbc hbd hcd P hP hperf := by
    obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨h.prime⟩
    have : CharP F p := h.charP
    exact SymBlocksUni.uniBlk_perfect_le hF hp2 hab hac had hbc hbd hcd P hP hperf

theorem uniBlockOps_blk {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (a b : Fin 4) :
    (uniBlockOps hF hq).blk a b = SymBlocksUni.uniBlk F q a b := rfl

theorem uni_blk_equiv {q p f : ℕ} {F : Type} [Field F] [Finite F] [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (hqpf : q = p ^ f) :
    ∀ a b : Fin 4, a ≠ b → Nonempty (Phan.Su F p f 2 ≃* ↥((uniBlockOps hF hq).blk a b)) := by
  subst hqpf
  intro a b hab
  exact SymBlocksUni.nonempty_equiv_uniBlk hF hab

theorem uni_std {q p f : ℕ} {F : Type} [Field F] [Finite F] [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (hqpf : q = p ^ f) :
    ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ W : Subgroup ↥(StatedSU 4 q F), Phan.UnitaryBlockStandardPair F p f W
        ((uniBlockOps hF hq).blk a b) ((uniBlockOps hF hq).blk b c) := by
  subst hqpf
  intro a b c hab hac hbc
  exact SymBlocksUni.uni_std_pf hF hab hac hbc

theorem uni_chain {q p f : ℕ} {F : Type} [Field F] [Finite F] [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (hqpf : q = p ^ f) :
    ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSU 4 q F), Phan.WeakPhanA F p f 3
      (fun i : Fin 3 => (uniBlockOps hF hq).blk (Fin.castSucc i) (Fin.succ i)) W := by
  subst hqpf
  have hq2 : p ^ f ≠ 2 := by omega
  exact SymBlocksUni.uni_chain_pf hF hq2

theorem uni_blk_center {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) :
    ∃ z ∈ (uniBlockOps hF hq).blk 0 1, orderOf z = 2 ∧
      ∀ g ∈ (uniBlockOps hF hq).blk 0 1, g * z = z * g := by
  obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hne : (0 : Fin 4) ≠ 1 := by decide
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  refine ⟨SymBlocksUni.uniEmb hF hne (L5U5.negSu hF), ?_, ?_, ?_⟩
  · rw [uniBlockOps_blk, ← SymBlocksUni.range_uniEmb hF hne]
    exact ⟨_, rfl⟩
  · rw [orderOf_injective _ (SymBlocksUni.uniEmb_injective hF hne)]
    exact L5U5.orderOf_negSu hF h2
  · intro g hg
    rw [uniBlockOps_blk, ← SymBlocksUni.range_uniEmb hF hne] at hg
    obtain ⟨A, rfl⟩ := hg
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, L5U5.coe_negSu]
    simp

end CFSG.GH74.Generic.S1
