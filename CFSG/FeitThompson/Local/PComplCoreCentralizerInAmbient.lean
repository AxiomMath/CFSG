module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
import CFSG.FeitThompson.Local.PSubgroupCentralizersLiftQuotient
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup

variable {G : Type*} [Group G] {p : ℕ}

theorem mem_normalizer_sup {g : G} {H K : Subgroup G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem eq_bot_of_le_normalizer_of_pComplCore_eq_bot [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hG : pComplCore p G = ⊥) {R D : Subgroup G} (hR : IsPGroup p R)
    (hDC : D ≤ centralizer (R : Set G))
    (hCD : centralizer (R : Set G) ≤ normalizer (D : Set G))
    (hDp : ¬ p ∣ Nat.card D) : D = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hTnormal : (pCore p G).Normal := pCore_normal p G
  set T := pCore p G with hTdef
  set V := R ⊔ T with hVdef
  have hVp : IsPGroup p V := hR.to_sup_of_normal_right (isPGroup_pCore hp G)
  have hRV : R ≤ V := le_sup_left
  have hTV : T ≤ V := le_sup_right
  have hcopD : (p : ℕ).Coprime (Nat.card D) := (Nat.Prime.coprime_iff_not_dvd hp).2 hDp
  obtain ⟨k, hk⟩ := hVp.exists_card_eq
  have hcop : (Nat.card D).Coprime (Nat.card V) := by
    rw [hk]; exact (hcopD.pow_left k).symm
  have hinf : V ⊓ D = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop.symm).eq_bot
  have hDV : D ≤ normalizer (V : Set G) := by
    intro d hd
    refine mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (hDC hd)) ?_
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top d
  set φ : D →* MulAut V := (V.normalizerMonoidHom).comp (Subgroup.inclusion hDV) with hφ
  have hφapply : ∀ (d : D) (v : V), ((φ d v : V) : G) = (d : G) * (v : G) * (d : G)⁻¹ := by
    intro d v
    simp [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  set F := FixedPoints.subgroup φ.range V with hF
  have hmemF : ∀ v : V, v ∈ F ↔ ∀ d ∈ D, (d : G) * (v : G) * (d : G)⁻¹ = (v : G) := by
    intro v
    rw [hF, mem_fixedPoints_range_iff]
    refine ⟨fun h d hd => ?_, fun h d => Subtype.ext (by rw [hφapply]; exact h (d : G) d.2)⟩
    have := congrArg (fun x : V => (x : G)) (h ⟨d, hd⟩)
    simpa [hφapply] using this
  have hRF : R.subgroupOf V ≤ F := by
    intro r hr
    rw [Subgroup.mem_subgroupOf] at hr
    rw [hmemF]
    intro d hd
    have h := (Subgroup.mem_centralizer_iff.1 (hDC hd)) (r : G) hr
    rw [← h]; group
  have hself : centralizer (F : Set V) ≤ F := by
    intro x hx
    have hxR : centralizer (F : Set V) ≤ centralizer ((R.subgroupOf V : Subgroup V) : Set V) :=
      Subgroup.centralizer_le (by exact_mod_cast hRF)
    have hxc : (x : G) ∈ centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hmem : (⟨r, hRV hr⟩ : V) ∈ R.subgroupOf V := by
        rw [Subgroup.mem_subgroupOf]; exact hr
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hxR hx) _ hmem)
    rw [hmemF]
    intro d hd
    have hxD : (x : G) ∈ normalizer (D : Set G) := hCD hxc
    have h1 : (x : G)⁻¹ * (d : G)⁻¹ * (x : G) * (d : G) ∈ D := by
      have hconj : (x : G)⁻¹ * (d : G)⁻¹ * (x : G) ∈ D := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxD)) (d : G)⁻¹
        simpa using this.1 (D.inv_mem hd)
      simpa [mul_assoc] using D.mul_mem hconj hd
    have h2 : (x : G)⁻¹ * (d : G)⁻¹ * (x : G) * (d : G) ∈ V := by
      have hxv : (d : G)⁻¹ * (x : G) * (d : G) ∈ V := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hDV hd))) (x : G)
        simpa using this.1 x.2
      simpa [mul_assoc] using V.mul_mem (V.inv_mem x.2) hxv
    have hone : (x : G)⁻¹ * (d : G)⁻¹ * (x : G) * (d : G) = 1 := by
      have hmem : (x : G)⁻¹ * (d : G)⁻¹ * (x : G) * (d : G) ∈ V ⊓ D := ⟨h2, h1⟩
      rw [hinf] at hmem
      simpa using hmem
    have h3 : (d : G)⁻¹ * (x : G) * (d : G) = (x : G) := by
      rw [show (x : G)⁻¹ * (d : G)⁻¹ * (x : G) * (d : G)
          = (x : G)⁻¹ * ((d : G)⁻¹ * (x : G) * (d : G)) by group] at hone
      exact (inv_mul_eq_one.1 hone).symm
    calc (d : G) * (x : G) * (d : G)⁻¹
        = (d : G) * ((d : G)⁻¹ * (x : G) * (d : G)) * (d : G)⁻¹ := by rw [h3]
      _ = (x : G) := by group
  have htop : F = ⊤ := fixedPoints_range_eq_top_of_coprime_of_centralizer_le hp hVp φ hcop hself
  have hDT : D ≤ centralizer (T : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hmem : (⟨t, hTV ht⟩ : V) ∈ F := htop ▸ Subgroup.mem_top _
    have h := (hmemF _).1 hmem d hd
    simp only at h
    calc t * d = ((d : G) * t * (d : G)⁻¹) * d := by rw [h]
      _ = d * t := by group
  have hDle : D ≤ T := hDT.trans (centralizer_pCore_le_pCore hp hG)
  have hDeq : D = V ⊓ D := (inf_eq_right.2 (hDle.trans hTV)).symm
  rw [hDeq, hinf]

theorem le_pComplCore_of_le_normalizer [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    {R D : Subgroup G} (hR : IsPGroup p R) (hDC : D ≤ centralizer (R : Set G))
    (hCD : centralizer (R : Set G) ≤ normalizer (D : Set G)) (hDp : ¬ p ∣ Nat.card D) :
    D ≤ pComplCore p G := by
  have : Fact p.Prime := ⟨hp⟩
  set N := pComplCore p G with hN
  have hNcop : (Nat.card N).Coprime p :=
    ((hp.coprime_iff_not_dvd).2 (not_dvd_natCard_pComplCore hp G)).symm
  have hquot : pComplCore p (G ⧸ N) = ⊥ := pComplCore_quotient_pComplCore p G
  have hRbar : IsPGroup p (R.map (mk' N)) := hR.map _
  have hCbar : centralizer ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (centralizer (R : Set G)).map (mk' N) := centralizer_map_mk'_eq hNcop hR
  have hDbar : D.map (mk' N) = ⊥ := by
    refine eq_bot_of_le_normalizer_of_pComplCore_eq_bot hp hquot hRbar ?_ ?_ ?_
    · rw [hCbar]; exact Subgroup.map_mono hDC
    · rw [hCbar]; exact (Subgroup.map_mono hCD).trans (Subgroup.le_normalizer_map _)
    · exact fun h => hDp (h.trans (Subgroup.card_map_dvd D _))
  rw [Subgroup.map_eq_bot_iff, ker_mk'] at hDbar
  exact hDbar

theorem pComplCore_centralizer_map_subtype_le_pComplCore [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) {R : Subgroup G} (hR : IsPGroup p R) :
    ((pComplCore p (centralizer (R : Set G))).map (centralizer (R : Set G)).subtype)
      ≤ pComplCore p G := by
  set C := centralizer (R : Set G) with hC
  set D : Subgroup G := (pComplCore p C).map C.subtype with hD
  have hDC : D ≤ C := Subgroup.map_subtype_le _
  have hCD : C ≤ normalizer (D : Set G) := by
    have h : (D.subgroupOf C).Normal := by
      rw [hD, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    exact Subgroup.le_normalizer_of_normal_subgroupOf hDC
  have hDp : ¬ p ∣ Nat.card D := by
    rw [hD, Subgroup.card_map_of_injective C.subtype_injective]
    exact not_dvd_natCard_pComplCore hp _
  exact le_pComplCore_of_le_normalizer hp hR hDC hCD hDp

theorem pComplCore_centralizer_le_subgroupOf [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    {R : Subgroup G} (hR : IsPGroup p R) :
    pComplCore p (centralizer (R : Set G))
      ≤ (pComplCore p G).subgroupOf (centralizer (R : Set G)) := by
  rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap]
  exact pComplCore_centralizer_map_subtype_le_pComplCore hp hR

theorem mem_pComplCore_of_mem_pComplCore_centralizer [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) {R : Subgroup G} (hR : IsPGroup p R)
    {x : centralizer (R : Set G)} (hx : x ∈ pComplCore p (centralizer (R : Set G))) :
    (x : G) ∈ pComplCore p G :=
  Subgroup.mem_subgroupOf.1 (pComplCore_centralizer_le_subgroupOf hp hR hx)

theorem pComplCore_centralizer_le_pComplCore_of_card_eq_pow [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) {R : Subgroup G} {n : ℕ} (hR : Nat.card R = p ^ n) :
    ((pComplCore p (centralizer (R : Set G))).map (centralizer (R : Set G)).subtype)
      ≤ pComplCore p G :=
  have : Fact p.Prime := ⟨hp⟩
  pComplCore_centralizer_map_subtype_le_pComplCore hp
    ((IsPGroup.iff_card (p := p) (G := R)).2 ⟨n, hR⟩)

end

end CFSG.FeitThompson
