module

public import CFSG.Quasithin.Background.B6Defs
import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type*} [Group G]

theorem pCoreOf_map_mk'_eq_of_le [Finite G] {p : ℕ} [Fact p.Prime] {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ center G) (hZp : Nat.Coprime (Nat.card Z) p) {P : Subgroup G} (hZP : Z ≤ P) :
    pCoreOf p (P.map (QuotientGroup.mk' Z)) = (pCoreOf p P).map (QuotientGroup.mk' Z) :=
  le_antisymm (by simpa only [comap_map_eq_self ((QuotientGroup.ker_mk' Z).le.trans hZP)] using
    LieType.BorelTits.pCoreOf_le_map_pCoreOf_comap Z hZ hZp (P.map (QuotientGroup.mk' Z)))
    (LieType.BorelTits.map_pCoreOf_le _ P)

theorem twoResidual_le_ker_of_isPGroup_map {G' : Type*} [Group G'] (f : G →* G')
    {H : Subgroup G} (h : IsPGroup 2 (H.map f)) : twoResidual H ≤ f.ker := by
  refine (twoResidual_le_of_isTwoQuotient (N := H ⊓ f.ker) inf_le_left
    (fun x hx => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hx, by rw [normalizer_eq_top f.ker]; exact mem_top x⟩)
    fun y hy => ?_).trans inf_le_right
  obtain ⟨k, hk⟩ := h ⟨f y, mem_map_of_mem f hy⟩
  refine ⟨k, mem_inf.2 ⟨pow_mem hy _, ?_⟩⟩
  rw [MonoidHom.mem_ker, map_pow]
  simpa using congrArg Subtype.val hk

theorem twoResidual_centralizer_le_of_isPGroup_centralizer_map (Z : Subgroup G) [Z.Normal]
    {Q : Subgroup G}
    (h : IsPGroup 2
      (centralizer ((Q.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)))) :
    twoResidual (centralizer (Q : Set G)) ≤ Z :=
  (twoResidual_le_ker_of_isPGroup_map _ (h.to_le (by
    rw [coe_map]; exact map_centralizer_le_centralizer_image _ _))).trans
      (QuotientGroup.ker_mk' Z).le

end CFSG.GroupTheory
