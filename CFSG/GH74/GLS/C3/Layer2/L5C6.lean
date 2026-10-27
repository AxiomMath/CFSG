module

public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open CFSG.Open
open scoped commutatorElement

theorem quasisimple_of_simple_nonabelian {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : CFSG.Open.IsQuasisimple L := by
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem goldschmidtLayer_top_of_simple_nonabelian {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : goldschmidtLayer Q = ⊤ := by
  have hsimple : IsSimpleGroup ↥(⊤ : Subgroup Q) := Subgroup.topEquiv.isSimpleGroup
  have hnab : ∃ a b : ↥(⊤ : Subgroup Q), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hQ
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  exact eq_top_iff.2
    (le_sSup ⟨le_rfl, IsSubnormal.refl _, quasisimple_of_simple_nonabelian hnab⟩)

theorem goldschmidtOddCore_bot_of_simple_even {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h2 : 2 ∣ Nat.card Q) : goldschmidtOddCore Q = ⊥ := by
  refine sSup_eq_bot.2 fun N hN => ?_
  obtain ⟨hNn, hodd⟩ := hN
  have := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hodd
    exact hodd.not_two_dvd_nat h2

theorem involution_mem_of_goldschmidt_clause_b {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (h2 : 2 ∣ Nat.card G) (S A M : Subgroup G) (hM : M = ⊤)
    (hb : (A.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) =
      CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure
        {t | t ∈ (S.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) ⊓
          goldschmidtLayer (M ⧸ goldschmidtOddCore M) ∧ t ^ 2 = 1}) :
    ∀ t ∈ S, t ^ 2 = 1 → t ∈ A := by
  have hMtop : ∀ g : G, g ∈ M := fun g => by rw [hM]; exact Subgroup.mem_top g
  let eM : ↥M ≃* G :=
    MulEquiv.ofBijective M.subtype ⟨M.subtype_injective, fun g => ⟨⟨g, hMtop g⟩, rfl⟩⟩
  have hsimM : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hnabM : ∃ a b : ↥M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, hMtop a⟩, ⟨b, hMtop b⟩, fun h => hab (congrArg Subtype.val h)⟩
  have h2M : 2 ∣ Nat.card ↥M := by
    rw [Nat.card_congr eM.toEquiv]
    exact h2
  have hO : goldschmidtOddCore ↥M = ⊥ := goldschmidtOddCore_bot_of_simple_even h2M
  have hπ : Function.Injective (QuotientGroup.mk' (goldschmidtOddCore M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  let eQ : ↥M ≃* (↥M ⧸ goldschmidtOddCore M) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (goldschmidtOddCore M))
      ⟨hπ, QuotientGroup.mk'_surjective _⟩
  have hsimQ : IsSimpleGroup (↥M ⧸ goldschmidtOddCore M) := eQ.symm.isSimpleGroup
  have hnabQ : ∃ a b : ↥M ⧸ goldschmidtOddCore M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabM
    exact ⟨eQ a, eQ b, fun h =>
      hab (eQ.injective ((map_mul eQ a b).symm.trans (h.trans (map_mul eQ b a))))⟩
  have hL : goldschmidtLayer (↥M ⧸ goldschmidtOddCore M) = ⊤ :=
    goldschmidtLayer_top_of_simple_nonabelian hnabQ
  intro t htS ht2
  have hmem : QuotientGroup.mk' (goldschmidtOddCore M) ⟨t, hMtop t⟩ ∈
      Subgroup.closure
        {x | x ∈ (S.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) ⊓
          goldschmidtLayer (↥M ⧸ goldschmidtOddCore M) ∧ x ^ 2 = 1} := by
    refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (show (⟨t, hMtop t⟩ : ↥M) ∈ S.subgroupOf M from htS)
    · rw [hL]
      exact Subgroup.mem_top _
    · have hsq : (⟨t, hMtop t⟩ : ↥M) ^ 2 = 1 := Subtype.ext ht2
      rw [← map_pow, hsq, map_one]
  obtain ⟨a, ha, hπa⟩ : QuotientGroup.mk' (goldschmidtOddCore M) ⟨t, hMtop t⟩ ∈
      (A.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) := by
    rw [hb]
    exact Subgroup.mem_sup_right hmem
  have hat : a = ⟨t, hMtop t⟩ := hπ hπa
  rw [hat] at ha
  exact Subgroup.mem_subgroupOf.1 ha

theorem goldschmidt_cor
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) (A : Subgroup G)
    (hAS : A ≤ (S : Subgroup G)) (hab : IsMulCommutative A) (hA : A ≠ ⊥)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A) :
    ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∈ A := by
  have := hs
  have hM : Subgroup.normalClosure (A : Set G) = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.normalClosure (A : Set G)) with h | h
    · exfalso
      have hle : A ≤ Subgroup.normalClosure (A : Set G) := Subgroup.le_normalClosure
      exact hA (le_bot_iff.1 (h ▸ hle))
    · exact h
  have h2 : 2 ∣ Nat.card G := by
    have hS1 : Nat.card (S : Subgroup G) ≠ 1 := fun h =>
      hA (le_bot_iff.1 ((Subgroup.card_eq_one.1 h) ▸ hAS))
    rcases S.isPGroup'.card_eq_or_dvd with h | h
    · exact absurd h hS1
    · exact h.trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨-, hb, -⟩ :=
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian G S A hAS hab hcl
  exact involution_mem_of_goldschmidt_clause_b hnab h2 (S : Subgroup G) A _ hM hb

end CFSG.GH74.GLS.C3.Layer2.L5
