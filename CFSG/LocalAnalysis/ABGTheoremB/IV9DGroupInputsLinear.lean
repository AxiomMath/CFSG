module

public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupInputsGroup

public section

namespace CFSG.ABGTheoremB.IV9DGroups

open CFSG.QuasiDihedralFusion CFSG.ABGDGroups
open CFSG.GorensteinWalter (PGammaL2)

variable {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F]
  {ι : Q →* PGammaL2 F} {L E : Subgroup Q} {S : Sylow 2 Q}

namespace LinearDecomposition

omit [Finite Q] in
theorem odd_card_field (hd : IsLinearDecomposition ι L E S) : Odd (Nat.card F) := by
  obtain ⟨p, f, -, hpodd, -, hq⟩ := hd.isOddPrimePower_card
  rw [hq]
  exact hpodd.pow

theorem mem_linearCore_of_odd (hd : IsLinearDecomposition ι L E S) {a : Q} (ha : a ∈ L)
    (hao : Odd (orderOf a)) : a ∈ linearCore ι := by
  have hn : ((linearCore ι).subgroupOf L).Normal := hd.linearCore_normal.subgroupOf L
  have hidx : ∃ k : ℕ, ((linearCore ι).subgroupOf L).index = 2 ^ k := by
    rcases hd.relIndex_linearCore with h | h
    · exact ⟨0, by rw [← Subgroup.relIndex, h, pow_zero]⟩
    · exact ⟨1, by rw [← Subgroup.relIndex, h, pow_one]⟩
  have hodd : Odd (Nat.card (Subgroup.zpowers (⟨a, ha⟩ : L))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact hao
  exact le_of_odd_of_two_pow_index _ hidx _ hodd (Subgroup.mem_zpowers (⟨a, ha⟩ : L))

theorem mul_comm_of_odd (hd : IsLinearDecomposition ι L E S) {x : Q} (hx : orderOf x = 2)
    {a b : Q} (ha : a ∈ L ⊓ Subgroup.centralizer ({x} : Set Q))
    (hb : b ∈ L ⊓ Subgroup.centralizer ({x} : Set Q)) (hao : Odd (orderOf a))
    (hbo : Odd (orderOf b)) : a * b = b * a := by
  have haL := mem_linearCore_of_odd hd ha.1 hao
  have hbL := mem_linearCore_of_odd hd hb.1 hbo
  have hε : ∃ ε : ℤ, (Nat.card F : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
    obtain ⟨k, hk⟩ := odd_card_field hd
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨1, ?_, Or.inl rfl⟩
      rw [hk, hj, Int.ModEq]
      push_cast
      omega
    · refine ⟨-1, ?_, Or.inr rfl⟩
      rw [hk, hj, Int.ModEq]
      push_cast
      omega
  obtain ⟨ε, hε, hε1⟩ := hε
  have he : ∃ m : ℕ, Nonempty (↥(linearCore ι ⊓ Subgroup.centralizer ({x} : Set Q)) ≃*
      DihedralGroup m) := by
    by_cases hxL : x ∈ linearCore ι
    · obtain ⟨m, -, he⟩ := hd.centralizer_dihedral_of_mem_linearCore hε hε1 hx hxL
      exact ⟨m, he⟩
    · obtain ⟨m, -, he⟩ := hd.centralizer_dihedral_of_not_mem_linearCore hε hε1 hx hxL
      exact ⟨m, he⟩
  obtain ⟨m, ⟨e⟩⟩ := he
  set a' : ↥(linearCore ι ⊓ Subgroup.centralizer ({x} : Set Q)) := ⟨a, haL, ha.2⟩
  set b' : ↥(linearCore ι ⊓ Subgroup.centralizer ({x} : Set Q)) := ⟨b, hbL, hb.2⟩
  have hrot : ∀ c : ↥(linearCore ι ⊓ Subgroup.centralizer ({x} : Set Q)),
      Odd (orderOf (c : Q)) → ∃ i : ZMod m, e c = DihedralGroup.r i := by
    intro c hc
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e] at hc
    rcases h : e c with i | i
    · exact ⟨i, rfl⟩
    · rw [h, DihedralGroup.orderOf_sr] at hc
      exact absurd hc (by decide)
  obtain ⟨i, hi⟩ := hrot a' hao
  obtain ⟨j, hj⟩ := hrot b' hbo
  have hab : a' * b' = b' * a' := by
    apply e.injective
    rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  exact congrArg Subtype.val hab

theorem exists_odd_normal_of_le_centralizer (hd : IsLinearDecomposition ι L E S) {x : Q}
    (hx : orderOf x = 2) {C : Subgroup Q} (hCx : C ≤ Subgroup.centralizer ({x} : Set Q))
    (hEC : E ≤ C) (P : Sylow 2 C)
    (hEP : E ≤ Subgroup.centralizer (((P : Subgroup C).map C.subtype : Subgroup Q) : Set Q)) :
    ∃ W : Subgroup Q, Odd (Nat.card W) ∧ W ≤ C ∧ C ≤ Subgroup.normalizer (W : Set Q) ∧
      ∀ Z : Subgroup Q, Odd (Nat.card Z) → Z ≤ C → Z ≤ W := by
  set N : Subgroup C := L.subgroupOf C
  set E' : Subgroup C := E.subgroupOf C
  have hNn : N.Normal := hd.normal.subgroupOf C
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, Odd (orderOf a) → Odd (orderOf b) → a * b = b * a := by
    intro a ha b hb hao hbo
    rw [← Subgroup.orderOf_coe] at hao hbo
    exact Subtype.ext (mul_comm_of_odd hd hx ⟨ha, hCx a.2⟩ ⟨hb, hCx b.2⟩ hao hbo)
  have hΩn : (oddElements N hcomm).Normal := oddElements_normal hNn
  have hNE : N ⊔ E' = ⊤ := by
    rw [eq_top_iff]
    intro c _
    have hc : (c : Q) ∈ ((L ⊔ E : Subgroup Q) : Set Q) := by
      rw [hd.sup_eq_top]
      exact Subgroup.mem_top _
    have : L.Normal := hd.normal
    rw [Subgroup.normal_mul] at hc
    obtain ⟨l, hl, e, he, hle⟩ := hc
    have heC : e ∈ C := hEC he
    have hlC : l ∈ C := by
      have h1 := C.mul_mem c.2 (C.inv_mem heC)
      rwa [← hle, mul_inv_cancel_right] at h1
    have h1 : c = ⟨l, hlC⟩ * ⟨e, heC⟩ := Subtype.ext hle.symm
    rw [h1]
    exact Subgroup.mul_mem_sup (show (⟨l, hlC⟩ : C) ∈ N from hl)
      (show (⟨e, heC⟩ : C) ∈ E' from he)
  have hdisj : Disjoint N E' := by
    rw [Subgroup.disjoint_def]
    intro g hgN hgE
    have hg : (g : Q) ∈ L ⊓ E := ⟨hgN, hgE⟩
    rw [hd.inf_eq_bot, Subgroup.mem_bot] at hg
    exact Subtype.ext hg
  have hE' : Odd (Nat.card E') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]
    exact hd.odd_card
  have hEP' : E' ≤ Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEP he) p ⟨p, hp, rfl⟩)
  obtain ⟨hWn, hWodd, hWle⟩ := normal_odd_of_centralizes_sylow hNE hdisj hE'
    oddElements_le odd_card_oddElements (fun n hn => exists_pow_two_pow_mem_oddElements hn) P
    hEP'
  refine ⟨(oddElements N hcomm ⊔ E').map C.subtype, ?_, Subgroup.map_subtype_le _,
    CFSG.ABGTheoremB.le_normalizer_map_subtype C _, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hWodd
  · intro Z hZ hZC
    have hZ' : Odd (Nat.card (Z.subgroupOf C)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv]
      exact hZ
    intro z hz
    exact ⟨⟨z, hZC hz⟩, hWle _ hZ' hz, rfl⟩

end LinearDecomposition

end CFSG.ABGTheoremB.IV9DGroups
