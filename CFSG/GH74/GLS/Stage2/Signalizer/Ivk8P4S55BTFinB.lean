module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLinkZ
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRk
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrImg

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

theorem cellV_of_finCellB (hInv : InvSec) {F : (Y : Type) → [Group Y] → Prop}
    (hF : ∀ (k : Kind), IsClassicalKind k → ∀ (Y : Type) [Group Y] [Finite Y],
      IsSimpleGroup Y → F Y → ¬ KindFactorAll k Y ∧ FinCellB Y) : CellV F := by
  intro G _ _ z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hFJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', hM, -, hL⟩ := hB
  have hJ : IsComponent J := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hJ, _⟩ := hL
    exact hJ
  have hs : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  obtain ⟨hbad, hfin⟩ := hF k hd.u.kind _ hs hFJ
  obtain ⟨hJn, hJC, -⟩ := EL3.hbarComp_of_bad hInv h.ctx H hJ hbad
  have hZ : center ↥J = ⊥ := EL3.center_eq_bot_of_centralizer_eq_bot hJC
  have hp : p.Prime := prime h
  have hpf : Fact p.Prime := ⟨hp⟩
  have hgH : g ∈ H := g_mem_H h
  set ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hν
  set φ : HBar H →* MulAut (↥J ⧸ center ↥J) := actYHom (K := J) with hφ
  have hφi : Function.Injective φ := actYHom_injective hJC hZ
  have : K.Normal := hM.normal
  obtain ⟨e, he⟩ := hL.exists_equiv hM.quasi
  have hh : ν ⟨g, hgH⟩ ∈ normalizer (J : Set (HBar H)) := by
    rw [normalizer_eq_top_iff.mpr hJn]
    exact mem_top _
  obtain ⟨γ, -, hγa, hγ⟩ := he ⟨g, hgH⟩ hh
  have hγ' : γ = a := hγa rfl
  rw [hγ'] at hγ
  set b : MulAut (↥J ⧸ center ↥J) := φ (ν ⟨g, hgH⟩) with hb
  have hbβ : ∀ y, e (b y) = actYHom (K := K) a (e y) := by
    intro y
    rw [hb, hφ, actYHom_eq_actJ _ hh]
    exact hγ y
  have hβo : orderOf (actYHom (K := K) a) = p := orderOf_eq_prime hM.actYHom_pow hM.actYHom_ne_one
  have hbo : orderOf b = p := by
    rw [← MulEquiv.orderOf_eq (MulAut.congr e) b, congr_eq_of_conj e hbβ, hβo]
  have hUH : L52Two.U4 z t ≤ H := U_le_H h hd.u
  have hIH : I ≤ H := hd.i.good.le_H
  have hQH : Q₁ ≤ H := hd.Q₁_le.trans hIH
  have hUf := isFourSubgroup_map_barIn hd.u.four hUH hφi
  have hQf := isFourSubgroup_map_barIn hd.Q₁_four hQH hφi
  have hQI : (barIn H Q₁).map φ ≤ (barIn H I).map φ := map_mono (L52Two.barIn_mono hd.Q₁_le)
  have hUQ : (barIn H (L52Two.U4 z t)).map φ ⊓ (barIn H Q₁).map φ = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ φ hφi, barIn_inf_eq_bot hd.u.four hd.Q₁_four
      (fun u hu w hw => (Subgroup.mem_centralizer_iff.mp (Q₁_le_centralizer hd hw) u hu))
      (inf_Q₁ hd), Subgroup.map_bot]
  have hIperf := commutator_map_barIn hIH hd.i.perf φ
  have hIU : (barIn H I).map φ ≤
      centralizer (((barIn H (L52Two.U4 z t)).map φ : Subgroup _) : Set (MulAut _)) := by
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hc : u * i = i * u := Subtype.ext (hd.i.good.comm _ hi _ hu)
    simp only [← map_mul, hc]
  have hUX : (barIn H (L52Two.U4 z t)).map φ ≤
      normalizer (((barIn H P).map φ : Subgroup _) : Set (MulAut _)) := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact mem_normalizer_map_br φ (mem_normalizer_map_br ν
      (mem_normalizer_subgroupOf ((hd.u.U_le_T.trans (T_norm h)) hu)))
  have hIX : (barIn H I).map φ ≤
      normalizer (((barIn H P).map φ : Subgroup _) : Set (MulAut _)) := by
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact mem_normalizer_map_br φ (mem_normalizer_map_br ν
      (mem_normalizer_subgroupOf (hd.i.norm_P hi)))
  have hXp : IsPGroup p ↥((barIn H P).map φ) := (map_isPGroup ν (P_pgroup h)).map φ
  have hbX : b ∈ (barIn H P).map φ :=
    ⟨ν ⟨g, hgH⟩, ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr (g_mem h), rfl⟩, rfl⟩
  obtain ⟨r, hobs⟩ := hfin p hp (odd h) _ _ _ _ hXp hUf hQf hQI hUQ hIperf hIU hUX hIX b hbX hbo
  have hobs' := HHObsAt.of_conj e hbβ hobs
  rw [← bAut_eq_actYHom] at hobs'
  have hZK : Odd (Nat.card ↥(center ↥K)) :=
    hL.odd_center hM.quasi (by rw [hZ, card_bot]; exact odd_one)
  exact hM.false_of_hhobsAt (fun _ h2 => (Nat.not_even_iff_odd.mpr hZK) (even_iff_two_dvd.mpr h2))
    hobs'

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
