module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29I1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 Subgroup
open scoped commutatorElement MatrixGroups

namespace S3T3

variable {G : Type} [Group G] [Finite G]

theorem eq_of_barMk_eq {u s t : G} {T : Subgroup G} (hT : IsPGroup 2 ↥T) (hs : s ∈ T)
    (ht : t ∈ T) (hsu : s ∈ centralizer ({u} : Set G)) (htu : t ∈ centralizer ({u} : Set G))
    (h : barMk ↥(centralizer ({u} : Set G)) ⟨s, hsu⟩ =
      barMk ↥(centralizer ({u} : Set G)) ⟨t, htu⟩) : s = t := by
  set c : ↥(centralizer ({u} : Set G)) := ⟨s * t⁻¹, mul_mem hsu (inv_mem htu)⟩ with hc
  have hc1 : barMk ↥(centralizer ({u} : Set G)) c = 1 := by
    have e : c = ⟨s, hsu⟩ * ⟨t, htu⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, h, mul_inv_cancel]
  have hmem : c ∈ pPrimeCore 2 ↥(centralizer ({u} : Set G)) := (QuotientGroup.eq_one_iff c).1 hc1
  have h2 : ∃ n : ℕ, orderOf c = 2 ^ n := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨s * t⁻¹, T.mul_mem hs (T.inv_mem ht)⟩
    refine ⟨n, ?_⟩
    rw [hc, Subgroup.orderOf_mk, ← hn, Subgroup.orderOf_mk]
  have h3 := S3Sec29I1.eq_one_of_mem_pPrimeCore hmem h2
  exact mul_inv_eq_one.1 (congrArg Subtype.val h3)

omit [Finite G] in
theorem perfect_subgroupOf {X : Type*} [Group X] {H K : Subgroup X} (hHK : H ≤ K)
    (hH : ⁅H, H⁆ = H) : ⁅H.subgroupOf K, H.subgroupOf K⁆ = H.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHK, hH]

omit [Finite G] in
theorem invol_eq_of_le_sl2 {X : Type*} {F : Type} [Group X] [Field F] (h2 : (2 : F) ≠ 0)
    {S W : Subgroup X} (e : ↥S ≃* SL(2, F)) {z : X}
    (hcomm : ∀ a ∈ centralizer ({z} : Set X), ∀ b ∈ centralizer ({z} : Set X), ⁅a, b⁆ ∈ S)
    (hW : ⁅W, W⁆ = W) (hWz : W ≤ centralizer ({z} : Set X)) {a b : X} (ha : a ∈ W)
    (hb : b ∈ W) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) : a = b := by
  have hWS : W ≤ S :=
    calc W = ⁅W, W⁆ := hW.symm
      _ ≤ S := Subgroup.commutator_le.2 fun c hc d hd => hcomm c (hWz hc) d (hWz hd)
  have key : ∀ c (hc : c ∈ W), c * c = 1 → c ≠ 1 → e ⟨c, hWS hc⟩ = -1 := by
    intro c hc hc2 hc1
    have hsq : (⟨c, hWS hc⟩ : ↥S) * ⟨c, hWS hc⟩ = 1 := Subtype.ext hc2
    rcases S3Sec29D1.sl2_invol h2 (e ⟨c, hWS hc⟩) (by rw [← map_mul, hsq, map_one]) with h | h
    · exfalso
      apply hc1
      have h1 : (⟨c, hWS hc⟩ : ↥S) = 1 := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val h1
    · exact h
  have h1 := e.injective ((key a ha ha2 ha1).trans (key b hb hb2 hb1).symm)
  exact congrArg Subtype.val h1

theorem not_bar_le {J Λ M : Subgroup G} {u y : G} (hJ : IsA7Bar J) (hΛJ : Λ ≤ J)
    (hperf : ⁅Λ, Λ⁆ = Λ) (hne : Λ ≠ ⊥) (hΛu : Λ ≤ centralizer ({u} : Set G))
    (hΛy : Λ ≤ centralizer ({y} : Set G))
    (hM : IsPCompIn 2 (centralizer ({u} : Set G)) M) (h3 : QShape3 (↥M ⧸ pPrimeCore 2 ↥M))
    (hyM : y ∈ M) (hy : orderOf y = 2) :
    ¬ PumpCalc.bar u Λ ≤ PumpCalc.bar u M := by
  intro hle
  obtain ⟨hcen, hmodel⟩ := S3Ctx29K26.model_centerless_of_ctx hM h3
  obtain ⟨F, hF, hFin, S, hS, hcomm, -⟩ := S3Sec29C.exists_layerHyp_comm hM hyM hy hcen hmodel
  obtain ⟨e⟩ := hS.equiv
  have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hS.odd
  have hbX : PumpCalc.bar u Λ ≤ S3.imgBar u M := hle
  have hperfb : ⁅PumpCalc.bar u Λ, PumpCalc.bar u Λ⁆ = PumpCalc.bar u Λ := by
    show ⁅(Λ.subgroupOf (centralizer ({u} : Set G))).map (barMk ↥(centralizer ({u} : Set G))),
      (Λ.subgroupOf (centralizer ({u} : Set G))).map (barMk ↥(centralizer ({u} : Set G)))⁆ =
      (Λ.subgroupOf (centralizer ({u} : Set G))).map (barMk ↥(centralizer ({u} : Set G)))
    rw [← Subgroup.map_commutator, perfect_subgroupOf hΛu hperf]
  have hyC : y ∈ centralizer ({u} : Set G) := hM.1 hyM
  have hWc : ∀ a ∈ (PumpCalc.bar u Λ).subgroupOf (S3.imgBar u M),
      a ∈ centralizer ({S3L3Lift.yK u hM.1 hyM} : Set ↥(S3.imgBar u M)) := by
    intro a ha
    obtain ⟨g, hg, hga⟩ := Subgroup.mem_subgroupOf.1 ha
    have hgΛ : (g : G) ∈ Λ := Subgroup.mem_subgroupOf.1 hg
    have hgy : (g : G) * y = y * g := Subgroup.mem_centralizer_singleton_iff.1 (hΛy hgΛ)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, S3L3Lift.yK_coe, piC_of_mem u hyC, ← hga]
    show barMk ↥(centralizer ({u} : Set G)) g * barMk ↥(centralizer ({u} : Set G)) ⟨y, hyC⟩ =
      barMk ↥(centralizer ({u} : Set G)) ⟨y, hyC⟩ * barMk ↥(centralizer ({u} : Set G)) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgy
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 Λ
  obtain ⟨s, hsT, t, htT, hs1, ht1, hst, hs2, ht2⟩ :=
    S3Sec29I1.two_invol_of_A7 hJ hΛJ hperf hne hT
  have hTu : T ≤ centralizer ({u} : Set G) := hT.le.trans hΛu
  have hmem : ∀ g (hg : g ∈ T),
      barMk ↥(centralizer ({u} : Set G)) ⟨g, hTu hg⟩ ∈ PumpCalc.bar u Λ := fun g hg =>
    ⟨⟨g, hTu hg⟩, Subgroup.mem_subgroupOf.2 (hT.le hg), rfl⟩
  have hσ2 : ∀ g (hg : g ∈ T), g * g = 1 →
      (⟨_, hbX (hmem g hg)⟩ : ↥(S3.imgBar u M)) * ⟨_, hbX (hmem g hg)⟩ = 1 := by
    intro g hg hg2
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← map_mul]
    show barMk ↥(centralizer ({u} : Set G)) ⟨g * g, _⟩ = 1
    simp only [hg2]
    exact map_one _
  have hσ1 : ∀ g (hg : g ∈ T), g ≠ 1 → (⟨_, hbX (hmem g hg)⟩ : ↥(S3.imgBar u M)) ≠ 1 := by
    intro g hg hg1 h
    have h1 : barMk ↥(centralizer ({u} : Set G)) ⟨g, hTu hg⟩ = 1 := congrArg Subtype.val h
    have hb1 : barMk ↥(centralizer ({u} : Set G)) ⟨g, hTu hg⟩ =
        barMk ↥(centralizer ({u} : Set G)) ⟨1, one_mem _⟩ := by
      rw [h1]
      exact (map_one _).symm
    exact hg1 (eq_of_barMk_eq hT.isPGroup hg (one_mem _) _ _ hb1)
  have h := invol_eq_of_le_sl2 h2F e hcomm (perfect_subgroupOf hbX hperfb) hWc
    (Subgroup.mem_subgroupOf.2 (hmem s hsT)) (Subgroup.mem_subgroupOf.2 (hmem t htT))
    (hσ2 s hsT hs2) (hσ1 s hsT hs1) (hσ2 t htT ht2) (hσ1 t htT ht1)
  exact hst (eq_of_barMk_eq hT.isPGroup hsT htT _ _ (congrArg Subtype.val h))

end S3T3

end CFSG.GH74.Generic.BProg.B3
