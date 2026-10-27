module

public import CFSG.CGT.Timmesfeld75.Sec4TwoBasic

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.inf_sec4N_eq_bot_of_not_normalizer
    (h : Sec4Hyp T T₁ a T₂) {x : G} (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxN : x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hxnN : x ∉ sec4N T T₁ T₂)
    (hxnT : x ∉ T) {y : G} (hy : y ∈ sec4Y T T₁ T₂)
    (hxy : x ∉ Subgroup.normalizer (conjSubgroup y T : Set G)) {Tx : Subgroup G}
    (hTx : ∃ g : G, Tx = conjSubgroup g T) (hxTx : x ∈ Tx) :
    Tx ⊓ sec4N T T₁ T₂ = ⊥ := by
  classical
  have hNab := h.isElemAbelian_sec4N
  obtain ⟨g, hg⟩ := hTx
  have hTxWC : IsWC Tx := hg ▸ h.pair.wc.conj g
  have hTxne : T ≠ Tx := fun h' => hxnT (h' ▸ hxTx)
  by_contra hne
  obtain ⟨⟨α, hα⟩, hα1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hαTx : α ∈ Tx := hα.1
  have hαN : α ∈ sec4N T T₁ T₂ := hα.2
  have hα1' : α ≠ 1 := fun h' => hα1 (Subtype.ext h')
  have hNTx : ∀ n ∈ sec4N T T₁ T₂, n ∈ Subgroup.normalizer (Tx : Set G) := fun n hn =>
    hTxWC.centralizer_le_normalizer hαTx hα1'
      (Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_mul_comm hNab hn hαN))
  have hcomm : ∀ n ∈ sec4N T T₁ T₂, n * x * n⁻¹ * x⁻¹ ∈ Tx ⊓ sec4N T T₁ T₂ := by
    intro n hn
    refine ⟨?_, ?_⟩
    · exact Tx.mul_mem (conj_mem_of_mem_normalizer (hNTx n hn) hxTx) (Tx.inv_mem hxTx)
    · have e : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
      rw [e]
      exact (sec4N T T₁ T₂).mul_mem hn
        (conj_mem_of_mem_normalizer hxN ((sec4N T T₁ T₂).inv_mem hn))
  set K : Subgroup G := conjSubgroup y (normIn T T₁) with hK
  have hKN : ∀ u ∈ K, u ∈ sec4N T T₁ T₂ := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := hu
    have hl' : l ∈ sec4N T T₁ T₂ := normIn_le_sec4N_left hl
    simpa [MulAut.conj_apply] using
      conj_mem_of_mem_normalizer (h.sec4Y_le_normalizer hy) hl'
  have hKC : K ≤ conjSubgroup y T := conjSubgroup_mono (normIn_le T T₁)
  let f : ↥K → ↥(Tx ⊓ sec4N T T₁ T₂) := fun u => ⟨(u : G) * x * (u : G)⁻¹ * x⁻¹, hcomm _ (hKN _ u.2)⟩
  have hfinj : Function.Injective f := by
    intro u v huv
    have h1 : (u : G) * x * (u : G)⁻¹ * x⁻¹ = (v : G) * x * (v : G)⁻¹ * x⁻¹ :=
      congrArg Subtype.val huv
    have h2 : (u : G) * x * (u : G)⁻¹ = (v : G) * x * (v : G)⁻¹ := mul_right_cancel h1
    set w : G := (v : G)⁻¹ * (u : G) with hw
    have hwK : w ∈ K := K.mul_mem (K.inv_mem v.2) u.2
    have hwx : w * x * w⁻¹ = x := by
      calc w * x * w⁻¹ = (v : G)⁻¹ * ((u : G) * x * (u : G)⁻¹) * (v : G) := by rw [hw]; group
        _ = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * (v : G) := by rw [h2]
        _ = x := by group
    by_cases hw1 : w = 1
    · apply Subtype.ext
      have : (u : G) = (v : G) := by
        calc (u : G) = (v : G) * ((v : G)⁻¹ * (u : G)) := by group
          _ = (v : G) := by rw [← hw, hw1, mul_one]
      exact this
    · exfalso
      refine hxy ((h.pair.wc.conj y).centralizer_le_normalizer (hKC hwK) hw1
        (Subgroup.mem_centralizer_singleton_iff.2 ?_))
      rw [mul_inv_eq_iff_eq_mul] at hwx
      exact hwx.symm
  have hcard1 : Nat.card (normIn T T₁) ≤ Nat.card ↥(Tx ⊓ sec4N T T₁ T₂) := by
    have := Nat.card_le_card_of_injective f hfinj
    rwa [hK, card_conjSubgroup] at this
  have hle : Tx ⊓ sec4N T T₁ T₂ ≤ normIn Tx T :=
    inf_le_inf_left Tx sec4N_le_normalizer_left
  have hcard2 : Nat.card (normIn Tx T) ≤ Nat.card (normIn T T₁) :=
    h.pair.card_normIn_le ⟨g, hg⟩ ⟨1, (conjSubgroup_one T).symm⟩ hTxne
  have heq : Tx ⊓ sec4N T T₁ T₂ = normIn Tx T :=
    Subgroup.eq_of_le_of_card_ge hle (hcard2.trans hcard1)
  have hxmem : x ∈ normIn Tx T := mem_normIn.2 ⟨hxTx, hxT⟩
  rw [← heq] at hxmem
  exact hxnN hxmem.2

end CFSG.CGT.T75B
