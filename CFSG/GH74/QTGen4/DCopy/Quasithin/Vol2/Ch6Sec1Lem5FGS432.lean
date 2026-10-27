module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FD
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FA

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {w : IntMod (UX615 T L H) hU} (hw1 : w ≠ 1)
    (hwT : ∀ t ∈ autI hU T, t w = w) (hwK : ∀ k ∈ autI hU (oTwoUpper H), k w = w)
    {δ : MulAut (IntMod (UX615 T L H) hU)} (hδ : δ ∈ autI hU D) (hδ1 : δ ≠ 1)
    (hδw : δ w = w) : False := by
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUT : UX615 T L H ≤ T :=
    c.U_red_ch615.1.trans (F7.isSylowTwoOf_pCoreOf_le (c.hyp.toHyp5_0_1.isSylowTwoOf hTX))
  set z := w.val with hz
  have hzU : z ∈ UX615 T L H := w.val_mem
  have hfix : ∀ g (hg : g ∈ Subgroup.normalizer (UX615 T L H : Set G)),
      convI hU ⟨g, hg⟩ w = w → g * z * g⁻¹ = z := fun g hg h => by
    have := congrArg IntMod.val h
    rwa [convI_apply_val] at this
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := Subgroup.mem_centralizer_iff.mpr fun t ht => by
    have htN := hXN (hTX ht)
    have h1 := hfix t htN (hwT _ (convI_mem_autI hU ht htN))
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [h1]
  have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hU.2 z hzU
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUT hzU, hzC, hz2⟩
  have hz1 : z ≠ 1 := fun h => hw1 (IntMod.val_injective (by rw [← hz, h, IntMod.val_one]))
  have hKz : oTwoUpper H ≤ Subgroup.centralizer ({z} : Set G) := fun k hk => by
    have hkN := hXN (Subgroup.mem_sup_right (oTwoUpper_le H hk))
    have h1 := hfix k hkN (hwK _ (convI_mem_autI hU hk hkN))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    calc z * k = k * z * k⁻¹ * k := by rw [h1]
      _ = k * z := by group
  obtain ⟨⟨d, hdN⟩, hdD, rfl⟩ := (mem_autI hU).mp hδ
  have hd1 : d ≠ 1 := fun h => hδ1 (by
    have : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (UX615 T L H : Set G))) = 1 := Subtype.ext h
    rw [this, map_one])
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hdD)
  exact false_of_centralizes_ch615_F4 h432 c hzZ hz1 hKz (hD.1 hdD) hdodd hd1 (hfix d hdN hδw)

end Cx615C

end CFSG.Quasithin.H13
