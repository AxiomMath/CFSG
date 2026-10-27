module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78

structure Fi24OutLocalData (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H)
    (huN : u ∈ normalizer (L : Set H)) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥L
  odd : Odd (Nat.card ↥(center ↥L))
  u_sq : u * u = 1
  K_le : K ≤ L
  K_quasisimple : CFSG.IsQuasisimple ↥K
  K_comm_u : ∀ k ∈ K, k * u = u * k
  facts : Fi24OutFacts (↥L ⧸ center ↥L) (normalizerAction L ⟨u, huN⟩)
  bar_eq : bar (K.subgroupOf L) = fixSubgroup (normalizerAction L ⟨u, huN⟩)

namespace Fi24OutLocalData

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
  {huN : u ∈ normalizer (L : Set H)} (D : Fi24OutLocalData H L K u huN)
include D

@[expose] noncomputable def fK : ↥K →* ↥L ⧸ center ↥L :=
  (QuotientGroup.mk' (center ↥L)).comp (Subgroup.inclusion D.K_le)

theorem fK_range : (D.fK).range = fixSubgroup (normalizerAction L ⟨u, huN⟩) := by
  rw [← D.bar_eq]
  simp [fK, MonoidHom.range_comp, Subgroup.inclusion_range]

theorem fK_mem_fix (k : ↥K) : D.fK k ∈ fixSubgroup (normalizerAction L ⟨u, huN⟩) := by
  rw [← D.fK_range]
  exact ⟨k, rfl⟩

theorem fK_ker : (D.fK).ker = center ↥K := by
  ext x
  constructor
  · intro hx
    have hx' : (⟨(x : H), D.K_le x.2⟩ : ↥L) ∈ center ↥L := by
      have := (QuotientGroup.eq_one_iff _).1 hx
      exact this
    rw [Subgroup.mem_center_iff]
    intro k
    have := Subgroup.mem_center_iff.1 hx' ⟨(k : H), D.K_le k.2⟩
    exact Subtype.ext (congrArg (fun z : ↥L => (z : H)) this)
  · intro hx
    rw [MonoidHom.mem_ker]
    have hy : D.fK x ∈ fixSubgroup (normalizerAction L ⟨u, huN⟩) := D.fK_mem_fix x
    have hc : (⟨D.fK x, hy⟩ : ↥(fixSubgroup (normalizerAction L ⟨u, huN⟩))) ∈
        center ↥(fixSubgroup (normalizerAction L ⟨u, huN⟩)) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨z, hz⟩
      rw [← D.fK_range] at hz
      obtain ⟨k, rfl⟩ := hz
      refine Subtype.ext ?_
      show D.fK k * D.fK x = D.fK x * D.fK k
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx k]
    rw [D.facts.center_bot, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc

@[expose] noncomputable def kQuotEquiv :
    ↥K ⧸ center ↥K ≃* ↥(fixSubgroup (normalizerAction L ⟨u, huN⟩)) :=
  (QuotientGroup.quotientMulEquivOfEq D.fK_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange D.fK).trans
      (MulEquiv.subgroupCongr D.fK_range))

theorem kAllInner (α : MulAut ↥K) : ∃ c ∈ K, ∀ k : ↥K, ((α k : ↥K) : H) = c * (k : H) * c⁻¹ := by
  have hperf : Group.IsPerfect ↥K := D.K_quasisimple.1
  have hinn : AllInner (↥K ⧸ center ↥K) := AllInner.of_mulEquiv D.kQuotEquiv.symm D.facts.allInner
  obtain ⟨c, hc⟩ := exists_inner_of_perfect_of_quotient_inner (K := ↥K)
    (fun β => by
      obtain ⟨x, hx⟩ := hinn β
      exact ⟨x, fun y => by rw [hx, MulAut.conj_apply]⟩) α
  refine ⟨(c : H), c.2, fun k => ?_⟩
  rw [hc k]
  simp

theorem central_inv : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u := by
  intro z hz hzz
  left
  obtain ⟨hzK, hzc⟩ := mem_center_map_iff.1 hz
  have hzK' : (⟨z, hzK⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hzc k k.2).symm
  have h1 : (⟨z, D.K_le hzK⟩ : ↥L) ∈ center ↥L := by
    have : (⟨z, hzK⟩ : ↥K) ∈ (D.fK).ker := by rw [D.fK_ker]; exact hzK'
    exact (QuotientGroup.eq_one_iff _).1 this
  have h2 : (⟨z, D.K_le hzK⟩ : ↥L) * ⟨z, D.K_le hzK⟩ = 1 := Subtype.ext hzz
  have h3 := Closing.eq_one_of_sq_eq_one_of_odd_center D.odd h1 h2
  exact congrArg Subtype.val h3

theorem generate (hu2 : orderOf u = 2) : Sol78Generate L K u := by
  have hK' := commutator_subgroupOf_eq_self D.K_le D.K_quasisimple
  have hX : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    have := Group.isPerfect_def.1 D.quasisimple.1
    rwa [_root_.commutator_def] at this
  refine sol78Generate_of_gen (mem_centralizer_iff.2 D.K_comm_u) hu2 D.central_inv ?_
  intro l hl hne
  have hne' : (K.subgroupOf L).map (MulAut.conj (⟨l, hl⟩ : ↥L)).toMonoidHom ≠
      K.subgroupOf L := by
    intro heq
    apply hne
    have := congrArg (Subgroup.map L.subtype) heq
    rw [map_subtype_map_conj, Subgroup.map_subgroupOf_eq_of_le D.K_le] at this
    exact this
  have hgenY : ∀ y : ↥L ⧸ center ↥L,
      (bar (K.subgroupOf L)).map (MulAut.conj y).toMonoidHom ≠ bar (K.subgroupOf L) →
        bar (K.subgroupOf L) ⊔ (bar (K.subgroupOf L)).map (MulAut.conj y).toMonoidHom =
          (⊤ : Subgroup (↥L ⧸ center ↥L)) := by
    intro y hy
    rw [D.bar_eq] at hy ⊢
    set KY : Subgroup (↥L ⧸ center ↥L) := fixSubgroup (normalizerAction L ⟨u, huN⟩) with hKY
    have hco : IsCoatom KY := D.facts.coatom
    rcases hco.le_iff.1 (le_sup_left : KY ≤ KY ⊔ KY.map (MulAut.conj y).toMonoidHom) with h | h
    · exact h
    · exfalso
      apply hy
      have hle2 : KY.map (MulAut.conj y).toMonoidHom ≤ KY :=
        calc KY.map (MulAut.conj y).toMonoidHom ≤ KY ⊔ KY.map (MulAut.conj y).toMonoidHom :=
              le_sup_right
          _ = KY := h
      exact Subgroup.eq_of_le_of_card_ge hle2
        (by rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  have htop := sup_conj_eq_top hK' hX hgenY hne'
  have := congrArg (Subgroup.map L.subtype) htop
  rw [Subgroup.map_sup, map_subtype_map_conj, Subgroup.map_subgroupOf_eq_of_le D.K_le,
    Subgroup.map_top, Subgroup.range_subtype] at this
  exact this

omit D in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup H} {g : H} (hK : K.map (conjHom g) = K) :
    g ∈ normalizer (K : Set H) := by
  refine mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · have : g * h * g⁻¹ ∈ K.map (conjHom g) := Subgroup.mem_map_of_mem (conjHom g) hh
    rwa [hK] at this
  · have : g * h * g⁻¹ ∈ K.map (conjHom g) := by rwa [hK]
    obtain ⟨h₀, hh₀, he⟩ := this
    have : h₀ = h := conjHom_injective g (by simpa [conjHom_apply] using he)
    exact this ▸ hh₀

theorem fusion39 (h35 : K = componentProduct K u) : Sol78Fusion39 L K u := by
  refine sol78Fusion39_of_induced D.K_comm_u (fun g hg => ?_)
    (inducedByCentralizer_of_allInner D.K_le D.K_comm_u fun α => D.kAllInner α)
  exact mem_normalizer_of_map_conj_eq (map_conj_eq_of_hyp35 h35 hg).2

end Fi24OutLocalData

end CFSG.EvenSporadicStandard.Induction
