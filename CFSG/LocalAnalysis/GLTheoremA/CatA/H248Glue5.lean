module

public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open
open scoped Pointwise

theorem glaPLayer_eq_self_of_component {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X K : Subgroup G} (hK : GLAPComponent p X K) : GLAPLayer p K = K := by
  have hQK : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  obtain ⟨hLcomp, -, hbar⟩ := CFSG.LocalAnalysis.GLTheoremA.glaPLayer_of_isQuasisimple
    (Y := K) hQK
  obtain ⟨hKX, hKsn, -, hKmin⟩ := hK
  set L : Subgroup G := GLAPLayer p K with hLdef
  obtain ⟨hLK, hLsn, -⟩ := hLcomp
  by_contra hne
  have hlt : L < K := lt_of_le_of_ne hLK hne
  have hLX : IsSubnormal L X := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_trans' hLsn hKsn
  apply hKmin L hlt hLX
  have hcore : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p X := by
    have h := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hKsn
    rw [← h]
    exact inf_le_right
  apply le_antisymm
  · exact Subgroup.map_mono (fun y hy => Subgroup.mem_subgroupOf.mpr (hLK (Subgroup.mem_subgroupOf.mp hy)))
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxK : (x : G) ∈ K := hx
    set xK : ↥K := ⟨(x : G), hxK⟩ with hxKdef
    have hbar' : (L.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) = ⊤ := hbar
    have hbarmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥K) xK : ↥K ⧸ GLAPPrimeCore p ↥K) ∈
        (L.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) := by
      rw [hbar']
      exact Subgroup.mem_top _
    obtain ⟨l, hl, hleq⟩ := Subgroup.mem_map.mp hbarmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hleq
    have hn : l⁻¹ * xK ∈ GLAPPrimeCore p ↥K := QuotientGroup.eq.mp hleq
    have hnK : ((l⁻¹ * xK : ↥K) : G) ∈ GLAPPrimeCoreOf p K :=
      Subgroup.mem_map.mpr ⟨l⁻¹ * xK, hn, rfl⟩
    obtain ⟨nX, hnX, hnXeq⟩ := Subgroup.mem_map.mp (hcore hnK)
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hlX : (l : G) ∈ X := hKX (hLK hlL)
    set lX : ↥X := ⟨(l : G), hlX⟩ with hlXdef
    have hnXeq' : (nX : G) = ((l⁻¹ * xK : ↥K) : G) := hnXeq
    have hxeq : x = lX * nX := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hnXeq']
      simp only [hlXdef, hxKdef, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      group
    have hm : (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) nX = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff nX).mpr hnX
    refine Subgroup.mem_map.mpr ⟨lX, Subgroup.mem_subgroupOf.mpr hlL, ?_⟩
    rw [hxeq, map_mul, hm, mul_one]

end CFSG.LocalAnalysis.GLTheoremA.H248
