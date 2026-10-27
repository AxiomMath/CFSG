module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FG
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5BS331

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem le_or_le_ch615_F4 (h331 : Stmt3_3_1_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {A B : Subgroup (MulAut (IntMod (UX615 T L H) hU))}
    (hA : A ≤ autI hU (oTwoUpper H)) (hB : B ≤ autI hU (oTwoUpper H))
    (hTA : autI hU T ≤ Subgroup.normalizer (A : Set (MulAut (IntMod (UX615 T L H) hU))))
    (hTB : autI hU T ≤ Subgroup.normalizer (B : Set (MulAut (IntMod (UX615 T L H) hU))))
    (hK : ∀ k ∈ autI hU (oTwoUpper H), ∃ a ∈ A, ∃ b ∈ B, a * b = k) :
    autI hU (oTwoUpper H) ≤ A ∨ autI hU (oTwoUpper H) ≤ B := by
  classical
  have hmp := c.toCx615.minParabolic_F4 h331
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_right.trans hXN
  have hTH : T ≤ H := c.hH.1.1
  have hT2 := c.isPGroup_autI_ch615 hU
  have key : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      autI hU T ≤ Subgroup.normalizer (C : Set (MulAut _)) →
      H ≤ preI615 hU (C ⊔ autI hU T) → autI hU (oTwoUpper H) ≤ C := by
    intro C hTC hHC
    refine autI_le_of_le_preI615 ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hxH, hxodd⟩
    have hxN := hHN hxH
    obtain ⟨y, hy, hyx⟩ := hHC hxH
    have hy' : y = ⟨x, hxN⟩ := Subtype.ext hyx
    rw [hy'] at hy
    refine mem_preI615 hxN (mem_of_odd_of_mem_sup_ch615 hT2 hTC hy ?_)
    have := orderOf_map_dvd (convI hU) ⟨x, hxN⟩
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hxodd this
  by_contra hno
  obtain ⟨hnA, hnB⟩ := not_or.mp hno
  have hT_le : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      T ≤ H ⊓ preI615 hU (C ⊔ autI hU T) := fun C t ht =>
    ⟨hTH ht, mem_preI615 (hHN (hTH ht))
      (Subgroup.mem_sup_right (convI_mem_autI hU ht (hHN (hTH ht))))⟩
  have hle_M : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      autI hU T ≤ Subgroup.normalizer (C : Set (MulAut _)) → ¬ autI hU (oTwoUpper H) ≤ C →
      H ⊓ preI615 hU (C ⊔ autI hU T) ≤ H ⊓ M := by
    intro C hTC hnC
    have hlt : H ⊓ preI615 hU (C ⊔ autI hU T) < H := by
      exact lt_of_le_of_ne inf_le_left fun h => hnC (key C hTC fun x hx => (h.ge hx).2)
    obtain ⟨N, hN, hYN⟩ := exists_isMaxSubgroupIn hlt
    rw [← hmp.eq_of_maximal hN ((hT_le C).trans hYN)]
    exact hYN
  have hYA := hle_M A hTA hnA
  have hYB := hle_M B hTB hnB
  have hHle : H ≤ (H ⊓ preI615 hU (A ⊔ autI hU T)) ⊔ (H ⊓ preI615 hU (B ⊔ autI hU T)) := by
    have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
    rw [twoResidual_eq_oTwoUpper'] at hsup
    intro x hx
    have hx' : x ∈ T ⊔ oTwoUpper H := by rw [hsup]; exact hx
    refine (sup_le ((hT_le A).trans le_sup_left) fun k hk => ?_) hx'
    have hkH : k ∈ H := oTwoUpper_le H hk
    have hkN := hHN hkH
    obtain ⟨a, ha, b, hb, hab⟩ := hK _ (convI_mem_autI hU hk hkN)
    obtain ⟨ka, hka, hkae⟩ := (mem_autI hU).mp (hA ha)
    obtain ⟨kb, hkb, hkbe⟩ := (mem_autI hU).mp (hB hb)
    have hkaA : convI hU ka ∈ A ⊔ autI hU T := by rw [hkae]; exact Subgroup.mem_sup_left ha
    have hkbB : convI hU kb ∈ B ⊔ autI hU T := by rw [hkbe]; exact Subgroup.mem_sup_left hb
    have hkaY : (ka : G) ∈ H ⊓ preI615 hU (A ⊔ autI hU T) :=
      ⟨oTwoUpper_le H hka, mem_preI615 ka.2 hkaA⟩
    have hkbY : (kb : G) ∈ H ⊓ preI615 hU (B ⊔ autI hU T) :=
      ⟨oTwoUpper_le H hkb, mem_preI615 kb.2 hkbB⟩
    set r : ↥(Subgroup.normalizer (UX615 T L H : Set G)) := ⟨k, hkN⟩ * (ka * kb)⁻¹ with hr
    have hr1 : convI hU r = 1 := by
      rw [hr, map_mul, map_inv, map_mul, hkae, hkbe, hab, mul_inv_cancel]
    have hrA : convI hU r ∈ A ⊔ autI hU T := by rw [hr1]; exact Subgroup.one_mem _
    have hrH : (r : G) ∈ H :=
      H.mul_mem hkH (H.inv_mem (H.mul_mem (oTwoUpper_le H hka) (oTwoUpper_le H hkb)))
    have hrY : (r : G) ∈ H ⊓ preI615 hU (A ⊔ autI hU T) := ⟨hrH, mem_preI615 r.2 hrA⟩
    have e : k = (r : G) * ka * kb := by
      rw [hr]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hrY)
      (Subgroup.mem_sup_left hkaY)) (Subgroup.mem_sup_right hkbY)
  exact c.hH.2.1 ((hHle.trans (sup_le hYA hYB)).trans inf_le_right)

end Cx615C

end CFSG.Quasithin.H13
