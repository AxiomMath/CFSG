module

public import CFSG.GH74.Generic.S1.LayerPair
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem orderOf_odd_of_mem_pPrimeCore {w : G} {u : ↥(centralizer ({w} : Set G))}
    (hu : u ∈ pPrimeCore 2 ↥(centralizer ({w} : Set G))) : Odd (orderOf u) := by
  have hdvd : orderOf u ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({w} : Set G))) :=
    Subgroup.orderOf_dvd_natCard _ hu
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(centralizer ({w} : Set G)))) :=
    pPrimeCore_coprime_card
  exact Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd)

theorem growth_abstract (ops : BlockOps F S) (hpf : PairFacts ops)
    (hblkq : ∀ a b : Fin 4, a ≠ b → IsQuasisimple ↥(ops.blk a b))
    {x v w : G} (hv : orderOf v = 2) (hvw : v ∈ centralizer ({w} : Set G))
    (hvx : v ∈ centralizer ({x} : Set G)) (hwx : w ∈ centralizer ({x} : Set G))
    (hwv : w ∈ centralizer ({v} : Set G))
    (Dx : LayerData x S) (Dv : LayerData v S) {z0 : ↥S} (hz0 : z0 ∈ ops.blk 0 1) (hz0sq : z0 * z0 = 1)
    (hz01 : z0 ≠ 1) (hcent : ∀ g ∈ ops.blk 0 1, g * z0 = z0 * g)
    (hwDx : Dx.ι z0 = w) (hwDv : Dv.ι z0 = w)
    {s : ↥S} (hsc : s ∈ Subgroup.center ↥S) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsv : Dv.ι s = v)
    (hvK : barOf hvx ∉ Dx.K) :
    ¬ layer (CentralizerBar w) ≤
      S45.barSub w ((ops.blk 2 3).map Dx.ι ⊔ (ops.blk 0 1).map Dx.ι) := by
  intro hle
  have hPv := layerPair_isPCompIn ops hpf hblkq Dv (a := 2) (b := 3) (c := 0) (d := 1) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hz0sq hz01 hcent
  rw [hwDv] at hPv
  have hB'le : S45.barSub w ((ops.blk 2 3).map Dv.ι) ≤ layer (CentralizerBar w) :=
    barSub_le_layer_of_isPCompIn hv hvw hPv.1
  have hwvmem : w * v ∈ (ops.blk 2 3).map Dv.ι := by
    refine ⟨s * z0, hpf.neg_mul 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) s hsc hs2 hs1 z0 hz0 hz0sq hz01, ?_⟩
    rw [map_mul, hsv, hwDv]
    exact (mem_centralizer_singleton_iff.1 hwv).symm
  have hwvC : w * v ∈ centralizer ({w} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : w * v = v * w := mem_centralizer_singleton_iff.1 hwv
    calc w * v * w = w * (v * w) := by rw [mul_assoc]
      _ = w * (w * v) := by rw [h1]
  have hbar : S45.barSub w ((ops.blk 2 3).map Dv.ι) ≤
      S45.barSub w ((ops.blk 2 3).map Dx.ι ⊔ (ops.blk 0 1).map Dx.ι) := hB'le.trans hle
  have hmem : proj w ⟨w * v, hwvC⟩ ∈ S45.barSub w ((ops.blk 2 3).map Dv.ι) :=
    S45.mem_barSub.2 ⟨w * v, hwvC, hwvmem, rfl⟩
  obtain ⟨g, hg, hgB, hgproj⟩ := S45.mem_barSub.1 (hbar hmem)
  have hker : (⟨g, hg⟩ : ↥(centralizer ({w} : Set G)))⁻¹ * ⟨w * v, hwvC⟩ ∈
      pPrimeCore 2 ↥(centralizer ({w} : Set G)) := (QuotientGroup.eq).1 hgproj
  have hodd := orderOf_odd_of_mem_pPrimeCore hker
  rw [← Subgroup.map_sup] at hgB
  obtain ⟨s', -, rfl⟩ := hgB
  set ug : ↥(centralizer ({x} : Set G)) := Dx.ιC s' with hug
  set uw : ↥(centralizer ({x} : Set G)) := ⟨w, hwx⟩ with huw
  set uv : ↥(centralizer ({x} : Set G)) := ⟨v, hvx⟩ with huv
  set o' : ↥(centralizer ({x} : Set G)) := ug⁻¹ * (uw * uv) with ho'
  have hug_val : ((ug : ↥(centralizer ({x} : Set G))) : G) = Dx.ι s' := rfl
  have ho'val : ((o' : ↥(centralizer ({x} : Set G))) : G) = (Dx.ι s')⁻¹ * (w * v) := rfl
  have hord : orderOf o' = orderOf ((⟨Dx.ι s', hg⟩ : ↥(centralizer ({w} : Set G)))⁻¹ * ⟨w * v, hwvC⟩) := by
    rw [← Subgroup.orderOf_coe o', ← Subgroup.orderOf_coe]
    rfl
  have hodd' : Odd (orderOf o') := by rw [hord]; exact hodd
  have hpg : proj x ug = ((Dx.iso.symm s' : ↥Dx.K) : CentralizerBar x) := Dx.proj_ιC s'
  have hpw : proj x uw = ((Dx.iso.symm z0 : ↥Dx.K) : CentralizerBar x) := by
    have : uw = Dx.ιC z0 := Subtype.ext hwDx.symm
    rw [this]
    exact Dx.proj_ιC z0
  have hpv : proj x uv = barOf hvx := rfl
  have hv2 : uv * uv = 1 := by
    apply Subtype.ext
    change v * v = 1
    rw [← sq, ← hv]
    exact pow_orderOf_eq_one v
  have hn := Dx.normal
  set vbar : CentralizerBar x := barOf hvx with hvbar
  set obar : CentralizerBar x := proj x o' with hobar
  have hvo : vbar = ((Dx.iso.symm z0 : ↥Dx.K) : CentralizerBar x)⁻¹ *
      ((Dx.iso.symm s' : ↥Dx.K) : CentralizerBar x) * obar := by
    rw [hobar, ho', map_mul, map_mul, map_inv, hpg, hpw, hpv]
    group
  have hmk : (QuotientGroup.mk vbar : CentralizerBar x ⧸ Dx.K) = QuotientGroup.mk obar := by
    rw [hvo]
    have h1 : (QuotientGroup.mk (((Dx.iso.symm z0 : ↥Dx.K) : CentralizerBar x)⁻¹ *
        ((Dx.iso.symm s' : ↥Dx.K) : CentralizerBar x)) : CentralizerBar x ⧸ Dx.K) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact Dx.K.mul_mem (Dx.K.inv_mem (Dx.iso.symm z0).2) (Dx.iso.symm s').2
    rw [QuotientGroup.mk_mul, h1, one_mul]
  have hsqv : (QuotientGroup.mk vbar : CentralizerBar x ⧸ Dx.K) ^ 2 = 1 := by
    have : vbar * vbar = 1 := by
      rw [← hpv, ← map_mul, hv2, map_one]
    rw [pow_two, ← QuotientGroup.mk_mul, this, QuotientGroup.mk_one]
  have hodd'' : Odd (orderOf obar) := by
    refine Odd.of_dvd_nat hodd' ?_
    rw [hobar]
    exact orderOf_map_dvd _ _
  have hpowo : (QuotientGroup.mk vbar : CentralizerBar x ⧸ Dx.K) ^ (orderOf obar) = 1 := by
    rw [hmk, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hgcd := pow_gcd_eq_one.2 ⟨hsqv, hpowo⟩
  have hgcd1 : Nat.gcd 2 (orderOf obar) = 1 := (Nat.coprime_two_left.2 hodd'')
  rw [hgcd1, pow_one] at hgcd
  exact hvK ((QuotientGroup.eq_one_iff _).1 hgcd)

end CFSG.GH74.Generic.S1
