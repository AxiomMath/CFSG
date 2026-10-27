module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped commutatorElement

section Action

variable {G : Type} [Group G]

@[expose] def InducesInner (z : G) (L : Subgroup G) : Prop :=
  ∃ l ∈ L, ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l

@[expose] def InducesTwoCentralInner (z : G) (L : Subgroup G) : Prop :=
  ∃ l ∈ L, (∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) ∧ (∃ x ∈ L, z⁻¹ * x * z ≠ x) ∧
    ∃ P : Subgroup G, IsSylowTwoOf P L ∧ ∀ p ∈ P, ⁅p, l⁆ ∈ Subgroup.centralizer (L : Set G)

@[expose] def InducesPermAction {n : ℕ} (z : G) (L : Subgroup G)
    (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ x ∈ L, z⁻¹ * x * z ∈ L) ∧
    ∀ x y : L, (y : G) = z⁻¹ * (x : G) * z →
      ((φ (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ⁻¹ * ((φ (QuotientGroup.mk x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ

theorem InducesInner.of_mem {z : G} {L : Subgroup G} (hz : z ∈ L) : InducesInner z L :=
  ⟨z, hz, fun _ _ => rfl⟩

theorem InducesTwoCentralInner.of_mem {z : G} {L P : Subgroup G} (hz : z ∈ L)
    (hP : IsSylowTwoOf P L) (hzP : z ∈ Subgroup.centralizer (P : Set G))
    (hnc : ∃ x ∈ L, z⁻¹ * x * z ≠ x) : InducesTwoCentralInner z L := by
  refine ⟨z, hz, fun _ _ => rfl, hnc, P, hP, fun p hp => ?_⟩
  have hcomm : p * z = z * p := Subgroup.mem_centralizer_iff.mp hzP p hp
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
  exact Subgroup.one_mem _

theorem InducesPermAction.of_alternatingGroup {n : ℕ} (hn : 4 ≤ n) (σ : Equiv.Perm (Fin n)) :
    ∃ φ : (alternatingGroup (Fin n) ⧸ Subgroup.center (alternatingGroup (Fin n))) ≃*
        alternatingGroup (Fin n),
      InducesPermAction σ (alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))) φ σ := by
  have hc : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using hn)
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot, ?_, ?_⟩
  · intro x hx
    simpa using (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem x hx σ⁻¹
  · intro x y hxy
    exact hxy

end Action

section Models

@[expose] def SQTKCharTwoLie (X : Type) [Group X] : Prop :=
  ((∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel X .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel X .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel X .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel X .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel X 2 f)) ∨
    ReeTitsModel X .Tits 2 1) ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel X .PSL n 2 1)

@[expose] def IsL34OrG24 (X : Type) [Group X] : Prop :=
  StatedClassicalModel X .PSL 3 2 2 ∨ ChevalleyExceptionalModel X .G2 2 2

@[expose] def IsFermatOrMersennePrime (p : ℕ) : Prop :=
  p.Prime ∧ ((∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1))

@[expose] def IsLemma115SporadicName (s : TauCeti.SporadicName) : Prop :=
  s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨
    s = .He ∨ s = .Ru

end Models

end CFSG.QuasithinUnique.Ch1

namespace CFSG.QuasithinUnique

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique.Ch1

section Cases

variable {G : Type} [Group G]

@[expose] def Lemma115LieCharTwo (X : Type) [Group X] : Prop :=
  SQTKCharTwoLie X ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel X .PSU 3 3 1

@[expose] def Lemma115CaseA (L : Subgroup G) (z : G) : Prop :=
  IsSimpleGroup L ∧ Lemma115LieCharTwo L ∧ InducesInner z L

@[expose] def Lemma115CaseB (L : Subgroup G) (z : G) : Prop :=
  Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
    IsL34OrG24 (L ⧸ CFSG.pCore 2 L) ∧ InducesInner z L

@[expose] def Lemma115CaseC (L : Subgroup G) (z : G) : Prop :=
  ∃ (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6)) (σ : Equiv.Perm (Fin 6)),
    (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3) ∧ σ.IsSwap ∧
      InducesPermAction z L φ σ

@[expose] def Lemma115CaseD (L : Subgroup G) (z : G) : Prop :=
  ∃ (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) (σ : Equiv.Perm (Fin 7)),
    (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3) ∧
      σ.cycleType = {2, 2, 2} ∧ InducesPermAction z L φ σ

@[expose] def Lemma115CaseE (L : Subgroup G) (z : G) : Prop :=
  (StatedClassicalModel L .PSL 3 3 1 ∨
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel L .PSL 2 p 1) ∧ InducesInner z L

@[expose] def Lemma115CaseF (L : Subgroup G) (z : G) : Prop :=
  (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧
    Nonempty ((L ⧸ CFSG.pCore 2 L) ≃* NativeSporadic.Carrier s)) ∧ InducesTwoCentralInner z L

@[expose] def Lemma115Cases (L : Subgroup G) (z : G) : Prop :=
  Lemma115CaseA L z ∨ Lemma115CaseB L z ∨ Lemma115CaseC L z ∨ Lemma115CaseD L z ∨
    Lemma115CaseE L z ∨ Lemma115CaseF L z

end Cases

@[expose] def Lemma115_3_List : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.QuasithinUnique.QTKECore G →
    ∀ (H S M : Subgroup G) (z : G), Lemma115Hyp H S M z →
      ∀ L : Subgroup G, IsComponentIn L H → Lemma115Cases L z

theorem Lemma115_3_List.component_cases (hlist : Lemma115_3_List) {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.QTKECore G) {H S M : Subgroup G} {z : G}
    (h : Lemma115Hyp H S M z) {L : Subgroup G} (hL : IsComponentIn L H) :
    z ∈ Subgroup.normalizer (L : Set G) ∧ ⁅L, Subgroup.zpowers z⁆ = L ∧ ¬ L ≤ M ∧
      Lemma115Cases L z :=
  let hc := h.component_action hL
  ⟨hc.1, hc.2.1, hc.2.2.1, hlist G hsimple hnonab hqtke H S M z h L hL⟩

theorem lemma115CaseC_symmetric_six :
    Lemma115CaseC (alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))) (Equiv.swap 0 1) := by
  obtain ⟨φ, hφ⟩ := InducesPermAction.of_alternatingGroup (n := 6) (by norm_num) (Equiv.swap 0 1)
  refine ⟨φ, Equiv.swap 0 1, Or.inl ?_, ⟨0, 1, by decide, rfl⟩, hφ⟩
  rw [alternatingGroup.center_eq_bot (by simp)]
  simp

private theorem cycleType_three_swaps :
    (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 * Equiv.swap 4 5).cycleType = {2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) (Equiv.swap 4 5) :=
    Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
  rw [hd.cycleType_mul, Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide),
    Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))]
  rfl

theorem lemma115CaseD_symmetric_seven :
    Lemma115CaseD (alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7)))
      (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5) := by
  obtain ⟨φ, hφ⟩ := InducesPermAction.of_alternatingGroup (n := 7) (by norm_num)
    (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5)
  refine ⟨φ, Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5, Or.inl ?_, cycleType_three_swaps, hφ⟩
  rw [alternatingGroup.center_eq_bot (by simp)]
  simp

end CFSG.QuasithinUnique
