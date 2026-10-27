module

public import CFSG.LargeExtraspecial.S97RQuasi
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.LargeExtraspecial.S97RZStar

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.Open

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem isTI_subgroupOf {T N : Subgroup K}
    (hTI : ∀ g : K, T ⊓ conjSubgroup g T = ⊥ ∨ T ⊓ conjSubgroup g T = T) (g : N) :
    T.subgroupOf N ⊓ conjSubgroup g (T.subgroupOf N) = ⊥ ∨
      T.subgroupOf N ⊓ conjSubgroup g (T.subgroupOf N) = T.subgroupOf N := by
  have hmem : ∀ x : N, x ∈ conjSubgroup g (T.subgroupOf N) ↔
      (x : K) ∈ conjSubgroup (g : K) T := fun x => by
    rw [mem_conjSubgroup, mem_conjSubgroup, mem_subgroupOf]
    simp
  rcases hTI g with h | h
  · refine Or.inl (eq_bot_iff.mpr fun x hx => ?_)
    have hx' : (x : K) ∈ T ⊓ conjSubgroup (g : K) T :=
      ⟨mem_subgroupOf.mp (mem_inf.mp hx).1, (hmem x).mp (mem_inf.mp hx).2⟩
    rw [h, mem_bot] at hx'
    exact (mem_bot).mpr (Subtype.ext hx')
  · refine Or.inr (inf_eq_left.mpr fun x hx => ?_)
    rw [hmem]
    have hx' : (x : K) ∈ T ⊓ conjSubgroup (g : K) T := by
      rw [h]
      exact mem_subgroupOf.mp hx
    exact hx'.2

omit [Finite K] in
theorem isElemAbelian_subgroupOf {T N : Subgroup K} (hT : IsElemAbelian 2 T) :
    IsElemAbelian 2 (T.subgroupOf N) := CFSG.Open.IsElemAbelian.subgroupOf hT N

theorem quasisimple_normalClosure (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) {T : Subgroup K} (hT : IsWC T) (h4 : 4 ≤ Nat.card T)
    (hTI : ∀ g : K, T ⊓ conjSubgroup g T = ⊥ ∨ T ⊓ conjSubgroup g T = T)
    (hO2 : ∀ P : Subgroup K, P.Normal → IsPGroup 2 P → P = ⊥) :
    commutator (normalClosure (T : Set K)) = ⊤ ∧
      IsSimpleGroup (↥(normalClosure (T : Set K)) ⧸ center ↥(normalClosure (T : Set K))) := by
  have hTN : T ≤ normalClosure (T : Set K) := le_normalClosure
  have hO2N : ∀ P : Subgroup (normalClosure (T : Set K)), P.Normal → IsPGroup 2 P → P = ⊥ :=
    fun P hP hP2 => eq_bot_of_normal_subgroup hO2 P hP hP2
  rcases form2_core_of_simpleCase hS h215 hI (isWC_subgroupOf_normalClosure hT)
    (normalClosure_subgroupOf_eq_top hT) hO2N with hZ | ⟨-, hcomm, -, hsimp, -⟩
  · refine absurd hZ (not_zStarCase (isElemAbelian_subgroupOf hT.1) ?_ (isTI_subgroupOf hTI)
      hO2N)
    rw [Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv]
    exact h4
  · exact ⟨hcomm, hsimp⟩

omit [Finite K] in
theorem forall_comm_of_quasisimple {N Nb : Subgroup K} [N.Normal] [Nb.Normal]
    (hc : commutator Nb = ⊤) (hs : IsSimpleGroup (↥Nb ⧸ center ↥Nb)) (hle : ¬ Nb ≤ N) :
    ∀ m ∈ N ⊓ Nb, ∀ y ∈ Nb, m * y = y * m := by
  have hnorm : ((N ⊓ Nb).subgroupOf Nb).Normal := inferInstance
  have hne : (N ⊓ Nb).subgroupOf Nb ≠ ⊤ := fun h => hle fun y hy => by
    have hy' : (⟨y, hy⟩ : Nb) ∈ (N ⊓ Nb).subgroupOf Nb := h ▸ mem_top _
    exact (mem_subgroupOf.mp hy').1
  have hcen := le_center_of_normal_of_ne_top hc hs hne
  intro m hm y hy
  have := mem_center_iff.mp (hcen (mem_subgroupOf.mpr hm : (⟨m, hm.2⟩ : Nb) ∈ _)) ⟨y, hy⟩
  exact (congrArg Subtype.val this).symm

omit [Finite K] in
theorem commutator_self_eq_of_perfect {N : Subgroup K} (hc : commutator N = ⊤) : ⁅N, N⁆ = N := by
  have h := congrArg (Subgroup.map N.subtype) hc
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

theorem normalClosure_eq_top_of_pair (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) {T Tb : Subgroup K} (hsup : T ⊔ Tb = ⊤) (hT : IsWC T)
    (hTb : IsWC Tb) (h4 : 4 ≤ Nat.card T) (h4b : 4 ≤ Nat.card Tb)
    (hTI : ∀ g : K, T ⊓ conjSubgroup g T = ⊥ ∨ T ⊓ conjSubgroup g T = T)
    (hTIb : ∀ g : K, Tb ⊓ conjSubgroup g Tb = ⊥ ∨ Tb ⊓ conjSubgroup g Tb = Tb)
    (hO2 : ∀ P : Subgroup K, P.Normal → IsPGroup 2 P → P = ⊥) :
    normalClosure (T : Set K) = ⊤ := by
  set N := normalClosure (T : Set K) with hN
  set Nb := normalClosure (Tb : Set K) with hNb
  obtain ⟨hNc, hNs⟩ := quasisimple_normalClosure hS h215 hI hT h4 hTI hO2
  obtain ⟨hNbc, hNbs⟩ := quasisimple_normalClosure hS h215 hI hTb h4b hTIb hO2
  have hTN : T ≤ N := le_normalClosure
  have hTbNb : Tb ≤ Nb := le_normalClosure
  have hT2 : IsPGroup 2 T := fun x => ⟨1, Subtype.ext (by simpa using hT.1.2 x x.2)⟩
  have hTb2 : IsPGroup 2 Tb := fun x => ⟨1, Subtype.ext (by simpa using hTb.1.2 x x.2)⟩
  have hTne : T ≠ ⊥ := fun h => by rw [h, card_bot] at h4; omega
  by_cases hle : Nb ≤ N
  · exact eq_top_iff.mpr (hsup ▸ sup_le hTN (hTbNb.trans hle))
  exfalso
  have hMb := forall_comm_of_quasisimple hNbc hNbs hle
  by_cases hle' : N ≤ Nb
  · have hNbtop : Nb = ⊤ := eq_top_iff.mpr (hsup ▸ sup_le (hTN.trans hle') hTbNb)
    have hTn : T.Normal := ⟨fun t ht x => by
      have hc := hMb t ⟨hTN ht, hle' (hTN ht)⟩ x (by rw [← hNb, hNbtop]; exact mem_top x)
      rw [← hc, mul_inv_cancel_right]
      exact ht⟩
    exact hTne (hO2 T hTn hT2)
  · have hMN := forall_comm_of_quasisimple hNc hNs hle'
    have hcomm : ⁅N, Nb⁆ = ⊥ := by
      have h1 : ⁅⁅N, Nb⁆, N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr fun m hm =>
        mem_centralizer_iff.mpr fun y hy =>
          (hMN m ⟨(commutator_le_inf N Nb hm).2, (commutator_le_inf N Nb hm).1⟩ y hy).symm
      have h2 : ⁅⁅Nb, N⁆, N⁆ = ⊥ := by rw [commutator_comm Nb N]; exact h1
      have h3 := commutator_commutator_eq_bot_of_rotate (H₁ := N) (H₂ := N) (H₃ := Nb) h1 h2
      rwa [commutator_self_eq_of_perfect hNc] at h3
    have hTTb : T ≤ normalizer (Tb : Set K) := fun t ht =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb =>
        (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm (hTN ht)) b
          (hTbNb hb)))
    have h2 : IsPGroup 2 ↥(T ⊔ Tb) := hT2.to_sup_of_normal_right' hTb2 hTTb
    rw [hsup] at h2
    have htop := hO2 ⊤ inferInstance h2
    exact hTne (eq_bot_iff.mpr fun x _ => htop ▸ mem_top x)

end CFSG.LargeExtraspecial.S9
