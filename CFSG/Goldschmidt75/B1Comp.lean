module

public import CFSG.Goldschmidt.Steps.Red1
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup
open scoped commutatorElement

@[expose] noncomputable def quotCenterHom (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ center K) where
  toFun α := QuotientGroup.congr (center K) (center K) α (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem quotCenterHom_mk {K : Type*} [Group K] (α : MulAut K) (x : K) :
    quotCenterHom K α (x : K ⧸ center K) = ((α x : K) : K ⧸ center K) := rfl

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q] [Group.IsPerfect Q] :
    center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · have : IsMulCommutative Q := ⟨⟨fun a b => mem_center_iff.mp (h ▸ mem_top b) a⟩⟩
    have : Subsingleton Q := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact absurd this (not_subsingleton Q)

theorem isGoldTypeI_quotient_center {K : Type*} [Group K] (hI : IsGoldTypeI K)
    (hZ : center (K ⧸ center K) = ⊥) : IsGoldTypeI (K ⧸ center K) := by
  let eQ : (K ⧸ center K) ⧸ center (K ⧸ center K) ≃* K ⧸ center K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n, hn, ⟨eQ.trans e⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨eQ.trans e⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨eQ.trans e⟩⟩)

variable {H : Type} [Group H] [Finite H]

theorem exists_mem_inf_not_mem_centralizer (S : Sylow 2 H) {A : Subgroup H}
    (hcore : CoreHyp H S A) {K : Subgroup H} (hK : IsComponentOf K ⊤)
    (hcov : ∀ a ∈ A, ∃ x ∈ A ⊓ K, ∀ y ∈ K, a⁻¹ * y * a = x⁻¹ * y * x) :
    ∃ x ∈ A, x ∈ K ∧ x ∉ centralizer (K : Set H) := by
  obtain ⟨-, hKA⟩ := N19 H S A hcore.le hcore.comm hcore.closed hcore.gen K hK
  have ha : ∃ a ∈ A, a ∉ centralizer (K : Set H) := by
    by_contra hcon
    apply hKA
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    intro a haA
    by_contra hna
    exact hcon ⟨a, haA, hna⟩
  obtain ⟨a, haA, haC⟩ := ha
  obtain ⟨x, hx, hax⟩ := hcov a haA
  refine ⟨x, (mem_inf.mp hx).1, (mem_inf.mp hx).2, fun hxC => haC ?_⟩
  rw [mem_centralizer_iff] at hxC ⊢
  intro y hy
  have h1 := hax y hy
  have h2 : x⁻¹ * y * x = y := by
    rw [mul_assoc, hxC y hy]
    group
  rw [h2] at h1
  calc y * a = a * (a⁻¹ * y * a) := by group
    _ = a * y := by rw [h1]

end CFSG.Goldschmidt75
