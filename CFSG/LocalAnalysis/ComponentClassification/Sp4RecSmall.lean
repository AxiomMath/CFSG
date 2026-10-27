module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open GSThmB (IsSmallAltOrL2)

theorem alternating_seven_nonabelian :
    ∃ u v : alternatingGroup (Fin 7), u * v ≠ v * u := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, ?_⟩
  intro h
  have := congrArg (fun w : alternatingGroup (Fin 7) => (w : Equiv.Perm (Fin 7)) 0) h
  revert this
  decide

theorem isSimpleGroup_of_isSmallAltOrL2 {Y : Type} [Group Y] (h : IsSmallAltOrL2 Y) :
    IsSimpleGroup Y ∧ ∃ u v : Y, u * v ≠ v * u := by
  have hL : ∀ {Y' : Type} [Group Y'] {p f : ℕ}, LieModel Y' .PSL 2 p f →
      IsSimpleGroup Y' ∧ ∃ u v : Y', u * v ≠ v * u := fun hL =>
    ⟨HarrisLit.isSimpleGroup_of_lieModel_psl2 hL, HarrisLit.nonabelian_of_lieModel_psl2 hL⟩
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨p, f, -, -, -, -, h⟩
  · rcases hn with rfl | rfl | rfl
    · exact hL (Or.inl ⟨by decide,
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five Y ⟨e⟩⟩)
    · exact hL (Or.inl ⟨by decide,
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six Y ⟨e⟩⟩)
    · have h5 : 5 ≤ Nat.card (Fin 7) := by rw [Nat.card_fin]; omega
      have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup h5
      obtain ⟨u, v, huv⟩ := alternating_seven_nonabelian
      exact ⟨e.isSimpleGroup, e.symm u, e.symm v, fun h => huv (by simpa using congrArg e h)⟩
  · exact hL h

theorem center_eq_bot_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (h : ∃ u v : Y, u * v ≠ v * u) : center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨u, v, huv⟩ := h
    exact huv (mem_center_iff.mp (h1 ▸ mem_top v) u)

theorem normal_le_center_or_eq_top {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) (N : Subgroup Q)
    [N.Normal] : N ≤ center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (center Q) with hπ
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hNZ : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (center Q), MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hnq,
        inv_mul_cancel]
    have htop : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      rw [← _root_.commutator_def]
      exact (@Group.IsPerfect.commutator_eq_top Q _ hperf).symm
    rw [eq_top_iff, htop, commutator_le]
    intro x _ y _
    obtain ⟨n₁, hn₁, hz₁⟩ := hNZ x
    obtain ⟨n₂, hn₂, hz₂⟩ := hNZ y
    have hx : x = n₁ * (n₁⁻¹ * x) := by group
    have hy : y = n₂ * (n₂⁻¹ * y) := by group
    set z₁ := n₁⁻¹ * x
    set z₂ := n₂⁻¹ * y
    have c₁ := mem_center_iff.mp hz₁
    have c₂ := mem_center_iff.mp hz₂
    rw [hx, hy, commutatorElement_def]
    have e : n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
      calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
          = n₁ * (z₁ * (n₂ * z₂) * z₁⁻¹) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by group
        _ = n₁ * (n₂ * z₂) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by
            rw [← c₁ (n₂ * z₂), mul_assoc _ z₁, mul_inv_cancel, mul_one]
        _ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by group
        _ = n₁ * n₂ * (n₁⁻¹ * z₂) * z₂⁻¹ * n₂⁻¹ := by rw [← c₂ n₁⁻¹]
        _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)

theorem center_eq_pPrimeCore {L : Type*} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L)) (hnab : ∃ u v : L ⧸ pPrimeCore 2 L, u * v ≠ v * u) :
    center L = pPrimeCore 2 L := by
  apply le_antisymm
  ·
    intro z hz
    have hZ := center_eq_bot_of_simple hnab
    have : (QuotientGroup.mk' (pPrimeCore 2 L) z) ∈ center (L ⧸ pPrimeCore 2 L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz g)]
    rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · rcases normal_le_center_or_eq_top hq (pPrimeCore 2 L) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hnab
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
      apply huv
      rw [(QuotientGroup.eq_one_iff u).mpr (h ▸ mem_top u),
        (QuotientGroup.eq_one_iff v).mpr (h ▸ mem_top v)]

theorem smallType_of_isQuasisimple {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hs : IsSmallAltOrL2 (L ⧸ pPrimeCore 2 L)) : ExcSelector.SmallType L := by
  obtain ⟨hsimple, hnab⟩ := isSimpleGroup_of_isSmallAltOrL2 hs
  have hZ := center_eq_pPrimeCore hq hsimple hnab
  have e : L ⧸ center L ≃* L ⧸ pPrimeCore 2 L := QuotientGroup.quotientMulEquivOfEq hZ
  have hodd : Odd (Nat.card (center L)) := by
    rw [hZ]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 (pPrimeCore_coprime_card (p := 2)))
  rcases hs with ⟨n, hn, ⟨e'⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · rcases hn with rfl | rfl | rfl
    · exact .inl ⟨5, 1, Nat.prime_five, by decide, le_rfl, by norm_num, Or.inl ⟨by decide,
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _
          ⟨e.trans e'⟩⟩, hodd⟩
    · exact .inl ⟨3, 2, Nat.prime_three, by decide, by norm_num, by norm_num, Or.inl ⟨by decide,
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
          ⟨e.trans e'⟩⟩, hodd⟩
    · exact .inr (.inl ⟨⟨e.trans e'⟩, hodd⟩)
  · exact .inl ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL, hodd⟩

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem isQuasisimple_J_of_fixed {M : Type} [Group M] [Finite M]
    (θ : ↥(generalizedFitting H) ≃* M)
    (hQ : ∀ α : MulAut M, α ^ 2 = 1 → α ≠ 1 →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup α), IsPComponent 2 L →
        IsQuasisimple L) : IsQuasisimple c.J := by
  obtain ⟨α, hα2, hα1, L, hLF, hLpc, ⟨eL⟩⟩ := c.exists_fixed_component θ
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr
    ((subgroupOfEquivOfLe hLF).trans eL)).1 (hQ α hα2 hα1 _ hLpc)

theorem isComponentOf_J (hq : IsQuasisimple c.J) :
    CFSG.Assembly.IsComponentOf c.J (centralizer ({c.a} : Set H)) := by
  obtain ⟨-, -, hs, -, -⟩ := id c.isPComponent_J
  exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf c.J_le).mpr
    ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe c.J_le)).2 hq, hs⟩

theorem smallType_J (hq : IsQuasisimple c.J) : ExcSelector.SmallType c.J :=
  smallType_of_isQuasisimple hq c.type_J

end Config

end CFSG.ComponentClassification.Sp4Rec
