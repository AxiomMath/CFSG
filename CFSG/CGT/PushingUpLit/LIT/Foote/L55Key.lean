module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L53C
public import CFSG.CGT.PushingUpLit.LIT.Foote.Statements
public import CFSG.CGT.PushingUpLit.LIT.Foote.L55Group

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def ConjIn (M J X : Subgroup G) : Prop := ∃ m ∈ M, X = rightConjugate J m

omit [Finite G] in
theorem ZData.rightConj {J : Subgroup G} {z₀ : G} (hz : ZData J z₀) (m : G) :
    ZData (rightConjugate J m) (m⁻¹ * z₀ * m) where
  mem := by
    rw [mem_rightConjugate_iff]
    have e : m * (m⁻¹ * z₀ * m) * m⁻¹ = z₀ := by group
    rw [e]
    exact hz.mem
  central := by
    intro j hj
    rw [mem_rightConjugate_iff] at hj
    have h1 := hz.central _ hj
    calc m⁻¹ * z₀ * m * j = m⁻¹ * (z₀ * (m * j * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * j * m⁻¹) * z₀) * m := by rw [h1]
      _ = j * (m⁻¹ * z₀ * m) := by group
  sq := by
    calc m⁻¹ * z₀ * m * (m⁻¹ * z₀ * m) = m⁻¹ * (z₀ * z₀) * m := by group
      _ = 1 := by rw [hz.sq]; group
  ne_one := by
    intro h
    apply hz.ne_one
    have : z₀ = m * (m⁻¹ * z₀ * m) * m⁻¹ := by group
    rw [this, h]
    group

omit [Finite G] in
theorem fourGroupMeet_of_conj {M J : Subgroup G} {m : G} (hm : m ∈ M) {h : G} (hh : h ∉ M)
    {W : Subgroup G}
    (hW : W ≤ rightConjugate (rightConjugate J m) h ⊓
      Subgroup.normalizer (rightConjugate J m : Set G))
    (hW2 : CFSG.Open.IsElemAbelian 2 W) (hW4 : Nat.card W = 4) : FourGroupMeet M J := by
  refine ⟨m * h * m⁻¹, fun hmem => hh ?_, rightConjugate W m⁻¹, ?_, ?_, ?_⟩
  · have := M.mul_mem (M.mul_mem (M.inv_mem hm) hmem) hm
    simpa [mul_assoc] using this
  · intro x hx
    rw [mem_rightConjugate_iff] at hx
    have hw := Subgroup.mem_inf.1 (hW hx)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hw1 := (mem_rightConjugate_iff _ _ _).1 hw.1
      have hw1' := (mem_rightConjugate_iff _ _ _).1 hw1
      rw [mem_rightConjugate_iff]
      have e : m * h * m⁻¹ * x * (m * h * m⁻¹)⁻¹ =
          m * (h * (m⁻¹ * x * m⁻¹⁻¹) * h⁻¹) * m⁻¹ := by group
      rw [e]
      exact hw1'
    · have hw2 := mem_normalizer_rightConjugate.1 hw.2
      have e : m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x := by group
      rwa [e] at hw2
  · have : rightConjugate W m⁻¹ = W.map (MulAut.conj m).toMonoidHom := by
      simp [rightConjugate]
    rw [this]
    exact isElemAbelian_map hW2 (MulAut.conj m)
  · rw [rightConjugate_card]
    exact hW4

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem orb_ce {X : Subgroup G} (hX : ConjIn M J X) : CE G M X := by
  obtain ⟨m, hm, rfl⟩ := hX
  exact c.conj hm

theorem fourGroupMeet_of_involution (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀)
    {X K : Subgroup G} (hX : ConjIn M J X) (hK : ConjIn M J K) {t y : G} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htN : t ∈ Subgroup.normalizer (X : Set G))
    (htK : t ∈ rightConjugate K y) (hy : y ∉ M) : FourGroupMeet M J := by
  obtain ⟨m, hm, rfl⟩ := hX
  obtain ⟨k, hk, rfl⟩ := hK
  have c₀ := c.conj hm
  have cK := c.conj hk
  have hz := hz₀.rightConj m
  have hV : CFSG.Open.IsElemAbelian 2 (blockU (rightConjugate J m)) := c₀.block.isElemAbelian_blockU
  have h8 := c₀.block.eight_le_card_blockU
  obtain ⟨E, hEV, hE, hE4, hEt⟩ := exists_fourGroup_centralizer hV ht2
    (fun v hv => conj_mem_blockU htN hv) h8
  have hEM : ∀ e ∈ E, y * e * y⁻¹ ∈ M := by
    intro e he
    have hmem : e ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hEt e he)
    have := cK.centralizer_le_conj htK ⟨1, by rw [pow_one, pow_two]; exact ht2⟩ ht1 hmem
    exact (mem_rightConjugate_iff M y e).1 this
  have hhy : y⁻¹ ∉ M := fun h => hy (by simpa using M.inv_mem h)
  have hWle : rightConjugate E y⁻¹ ≤ rightConjugate (rightConjugate J m) y⁻¹ ⊓ M := by
    intro x hx
    have hx' := (mem_rightConjugate_iff _ _ _).1 hx
    have hxe : y⁻¹ * x * y ∈ E := by simpa using hx'
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      have := blockU_le _ (hEV hxe)
      simpa using this
    · have := hEM _ hxe
      have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
      rwa [e] at this
  have hWab : CFSG.Open.IsElemAbelian 2 (rightConjugate E y⁻¹) := by
    have : rightConjugate E y⁻¹ = E.map (MulAut.conj y).toMonoidHom := by
      simp [rightConjugate]
    rw [this]
    exact isElemAbelian_map hE (MulAut.conj y)
  have hW4 : Nat.card (rightConjugate E y⁻¹) = 4 := by
    rw [rightConjugate_card]
    exact hE4
  have hWN := c₀.normalizes_of_le_conj hA hz hhy hWle hWab hW4
  exact fourGroupMeet_of_conj hm hhy (le_inf (hWle.trans inf_le_left) hWN) hWab hW4

theorem mem_of_normalizes_inf {X : Subgroup G} (hX : ConjIn M J X) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hUS : blockU X ≤ S) {b : G} (hbS : b ∈ S)
    (hb : b ∈ Subgroup.normalizer ((X ⊓ S : Subgroup G) : Set G)) : b ∈ M := by
  have cX := c.orb_ce hX
  have hA : X ⊓ S ≠ ⊥ := fun h => blockU_ne_bot_of_short cX.block.short
    (le_bot_iff.1 (by rw [← h]; exact le_inf (blockU_le X) hUS))
  have hTS : X ⊓ S ⊔ Subgroup.zpowers b ≤ S :=
    sup_le inf_le_right (Subgroup.zpowers_le.2 hbS)
  have hTN : X ⊓ S ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer ((X ⊓ S : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hb)
  obtain ⟨x, hxA, hx1, hxc⟩ := exists_ne_one_commute_of_normal (hS.to_le hTS) le_sup_left
    (fun t ht x hx => (Subgroup.mem_normalizer_iff.1 (hTN ht) x).1 hx) hA
  have hxX : x ∈ X := (Subgroup.mem_inf.1 hxA).1
  have hxS : x ∈ S := (Subgroup.mem_inf.1 hxA).2
  have h2 : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hS ⟨x, hxS⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  apply cX.centralizer_le_of_mem hxX h2 hx1
  exact Subgroup.mem_centralizer_singleton_iff.2
    (hxc b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))

theorem mem_normalizer_of_mem {X : Subgroup G} (hX : ConjIn M J X) {S : Subgroup G}
    (hUS : blockU X ≤ S) {b : G} (hbM : b ∈ M)
    (hb : b ∈ Subgroup.normalizer ((X ⊓ S : Subgroup G) : Set G)) :
    b ∈ Subgroup.normalizer (X : Set G) := by
  obtain ⟨m, hm, rfl⟩ := hX
  by_contra hnot
  have hne : rightConjugate (rightConjugate J m) b ≠ rightConjugate J m := fun h =>
    hnot ((rightConjugate_eq_self_iff _ _).1 h)
  rw [rightConjugate_mul] at hne
  have hcomm := c.commutator_conj_conj_eq_bot hm (M.mul_mem hm hbM) (Ne.symm hne)
  have hU : blockU (rightConjugate J m) ≤ rightConjugate J (m * b) := by
    intro u hu
    rw [← rightConjugate_mul, mem_rightConjugate_iff]
    have hA : u ∈ rightConjugate J m ⊓ S := Subgroup.mem_inf.2 ⟨blockU_le _ hu, hUS hu⟩
    exact (Subgroup.mem_inf.1 ((Subgroup.mem_normalizer_iff.1 hb u).1 hA)).1
  have h1 : ⁅blockU (rightConjugate J m), rightConjugate J m⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅blockU (rightConjugate J m), rightConjugate J m⁆
        ≤ ⁅rightConjugate J (m * b), rightConjugate J m⁆ := Subgroup.commutator_mono hU le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm
  have hK := c.block.conj m
  rw [hK.blockU_stable] at h1
  exact blockU_ne_bot_of_short hK.short h1

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
