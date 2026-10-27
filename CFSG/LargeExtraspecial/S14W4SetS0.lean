module

public import CFSG.LargeExtraspecial.S14W4SetBasic
import CFSG.Adapters.WholeGroupLayer
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

namespace W4Hyp

variable {S : Setting G} {g : G} {t : S.O} {c : Config} (h : W4Hyp S g t c)
include h

omit h in
@[expose] noncomputable def toCt (h : W4Hyp S g t c) :
    ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S))) →* ↥(Ct S t) :=
  h.ιK.codRestrict (Ct S t) h.ιK_mem_Ct

theorem toCt_injective : Function.Injective h.toCt := by
  intro x y hxy
  apply h.ιK_injective
  exact congrArg (fun z : ↥(Ct S t) => (z : S.O)) hxy

theorem exists_ιK_conj (x : ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S)))) {c : S.O}
    (hc : c ∈ Ct S t) : ∃ x' : ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S))),
      h.ιK x' = c * h.ιK x * c⁻¹ := by
  obtain ⟨hcM, hct'⟩ := hc
  have hct : Commute c t := mem_centralizer_singleton_iff.mp hct'
  have hx0 : ((x : ↥(Mbar0 S)) : S.Mbar) ∈ Mbar0 S := (x : ↥(Mbar0 S)).2
  have hmem : (⟨c, hcM⟩ : S.Mbar) * ((x : ↥(Mbar0 S)) : S.Mbar) * (⟨c, hcM⟩ : S.Mbar)⁻¹ ∈
      Mbar0 S := (CFSG.LargeExtraspecial.timmesfeldFStar_normal S.Mbar).conj_mem _ hx0 _
  have hx' : ι S ⟨_, hmem⟩ = c * h.ιK x * c⁻¹ := rfl
  have hxt : Commute (h.ιK x) t := h.ιK_commute x
  have hcomm : ι S ⟨_, hmem⟩ * t = t * ι S ⟨_, hmem⟩ := by
    rw [hx']
    exact ((hct.mul_left hxt).mul_left hct.inv_left).eq
  exact ⟨⟨⟨_, hmem⟩, h.mem_centralizer_t₀_iff.mpr hcomm⟩, hx'⟩

theorem range_toCt_normal : h.toCt.range.Normal := by
  constructor
  intro y hy c
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  have hc2 : (c : S.O) ∈ Ct S t := c.2
  have e := h.exists_ιK_conj x hc2
  exact MonoidHom.mem_range.mpr ⟨e.choose, Subtype.ext e.choose_spec⟩

omit h in
theorem pCore_le_FStar_Ct : CFSG.pCore 2 ↥(Ct S t) ≤ timmesfeldFStar ↥(Ct S t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_sup_of_le_left (le_sSup ⟨CFSG.pCore_normal, CFSG.pCore_isPGroup.isNilpotent⟩)

theorem le_Q₀_of_normal (P : Subgroup ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S))))
    (hP : P.Normal) (h2 : IsPGroup 2 P) : P ≤ h.Q₀ := by
  intro x hx
  have hPO : P ≤ CFSG.pCore 2 ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S))) :=
    le_sSup (show P ∈ {K : Subgroup _ | K.Normal ∧ IsPGroup 2 K} from ⟨hP, h2⟩)
  have h1 : h.toCt x ∈ CFSG.pCore 2 ↥(Ct S t) :=
    CFSG.ABGLocalTools.map_pCore_le_of_injective_of_normal (p := 2) h.toCt
      h.toCt_injective h.range_toCt_normal (Subgroup.mem_map_of_mem h.toCt (hPO hx))
  have h3 : ((h.toCt x : Ct S t) : S.O) ∈ FCt S t :=
    Subgroup.mem_map_of_mem (Ct S t).subtype (pCore_le_FStar_Ct h1)
  exact h.fstar.le h3

theorem commute_of_mem_centralizer {x : ↥(centralizer ({h.t₀} : Set ↥(Mbar0 S)))}
    (hx : x ∈ centralizer (h.Q₀ : Set _)) {f : S.O} (hfN : f ∈ Nbar S g t) :
    f * h.ιK x = h.ιK x * f := by
  have hr : f ∈ h.ιK.range := h.Nbar_le_range_ιK hfN
  have hm : ∃ q, h.ιK q = f := MonoidHom.mem_range.mp hr
  cases hm with
  | intro q hq =>
    subst hq
    have hqx := mem_centralizer_iff.mp hx q hfN
    simpa only [map_mul] using congrArg h.ιK hqx

theorem centralizer_Q₀_le : centralizer (h.Q₀ : Set _) ≤ h.Q₀ := by
  intro x hx
  have hc : h.toCt x ∈ centralizer (timmesfeldFStar ↥(Ct S t) : Set ↥(Ct S t)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    have hfN : (f : S.O) ∈ Nbar S g t :=
      h.fstar.le (Subgroup.mem_map_of_mem (Ct S t).subtype hf)
    exact Subtype.ext (h.commute_of_mem_centralizer hx hfN)
  have h1 := CFSG.Adapters.centralizer_timmesfeldFStar_le _ hc
  have h3 : ((h.toCt x : Ct S t) : S.O) ∈ FCt S t :=
    Subgroup.mem_map_of_mem (Ct S t).subtype h1
  exact h.fstar.le h3

omit h in
@[expose] noncomputable def S₀ (h : W4Hyp S g t c) : Setting ↥(Mbar0 S) where
  z := h.t₀
  orderOf_z := h.orderOf_t₀
  Q := h.Q₀
  normal := h.Q₀_normal
  extraspecial := h.Q₀_extraspecial
  centralizer_le := h.centralizer_Q₀_le
  le_of_normal := fun P hP h2 => h.le_Q₀_of_normal P hP h2

theorem mem_S₀_M {x : ↥(Mbar0 S)} : x ∈ h.S₀.M ↔ ι S x * t = t * ι S x :=
  h.mem_centralizer_t₀_iff

theorem mem_S₀_QG {x : ↥(Mbar0 S)} : x ∈ h.S₀.QG ↔ ι S x ∈ Nbar S g t := by
  constructor
  · intro hx
    have hx' : ∃ hM : x ∈ h.S₀.M, (⟨x, hM⟩ : h.S₀.M) ∈ h.S₀.Q := h.S₀.mem_QG_iff.mp hx
    cases hx' with
    | intro hM hQ => exact hQ
  · intro hx
    have hM : x ∈ h.S₀.M :=
      h.mem_S₀_M.mpr (commute_of_mem_Rbar h.haQ (Nbar_le_Rbar hx))
    exact h.S₀.mem_QG_iff.mpr ⟨hM, hx⟩

theorem width_S₀ : h.S₀.width = 4 := by
  refine h.S₀.width_eq ?_
  have hN : Nat.card (Nbar S g t) = 2 ^ 9 := by
    rcases h.hc with rfl | rfl <;> exact h.occ.2.2
  change Nat.card h.Q₀ = 2 ^ (1 + 2 * 4)
  rw [h.card_Q₀, hN]

end W4Hyp

end CFSG.LargeExtraspecial.S14
