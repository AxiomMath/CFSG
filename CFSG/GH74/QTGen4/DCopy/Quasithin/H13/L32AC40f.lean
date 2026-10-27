module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A5Props
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC40c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC40e
public import CFSG.Quasithin.H13.L32A71
public import CFSG.Quasithin.H13.L32AC40d
public import CFSG.Quasithin.H13.L32AC40e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]

theorem false_of_two_factors_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h38 : Lemma14_7_38_F4) (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K) (hHKT : H = K ⊔ T)
    (hA5 : IsAlt 5 (cStar K)) (hl1K : l1 T L V ≤ K)
    {Y Z : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (hYZ : Y ≤ Z)
    (hY : ∀ l ∈ (K.subgroupOf H).map (phiU hF), ∀ y ∈ Y, l y ∈ Y)
    (hZ : ∀ l ∈ (K.subgroupOf H).map (phiU hF), ∀ z ∈ Z, l z ∈ Z)
    (hntY : ∃ l ∈ (K.subgroupOf H).map (phiU hF), ∃ y ∈ Y, l y * y⁻¹ ≠ 1)
    (hntZ : ∃ l ∈ (K.subgroupOf H).map (phiU hF), ∃ z ∈ Z, l z * z⁻¹ ∉ Y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := hK₀ ▸ hF.K₀_normal
  set Φ := phiU hF with hΦ
  have hker := phiU_eq_one_iff hF
  obtain ⟨eL⟩ := nonempty_cStar_equiv_map Φ hker hF.K_cComp
  obtain ⟨eA⟩ := hA5
  let e : ↥((K.subgroupOf H).map Φ) ≃* alternatingGroup (Fin 5) := eL.symm.trans eA
  obtain ⟨-, hRK, hR4⟩ := s5_of_F4 h1222 h1332 h1334 S hF hK₀ hHKT ⟨eA⟩ hl1K

  have hF98 := hF.toHypF98
  obtain ⟨γ, γ', g, s⟩ := hF98.exists_F8Setup
  obtain ⟨δ, δ', gk, hh, N⟩ := exists_not1471 hF98 s (h38 G T L V H S γ γ' g s)
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hUα := N.uα_le hF98
  rw [hl1eq] at hUα
  obtain ⟨hcrit, heq⟩ := hF98.F916_2_aux N.setup N.pos N.le
  obtain ⟨hUH, hUab, hUQ, -, hc⟩ := hcrit
  set Uγ := F8.Uγ V H (gk : G) with hUγ
  have hhH : (hh : G) ∈ H := N.mem

  have ha4 : (pCoreOf 2 H).relIndex Uγ ≤ 4 := by
    have hQ : CFSG.Quasithin.conjSub (hh : G) (pCoreOf 2 H) = pCoreOf 2 H := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hhH) q).mp hq
        simpa [MulAut.conj_apply] using this
      · intro hy
        refine ⟨(hh : G)⁻¹ * y * (hh : G), ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hhH)) y).mp hy
        simpa using this
    calc (pCoreOf 2 H).relIndex Uγ
        = (pCoreOf 2 H).relIndex (CFSG.Quasithin.conjSub (hh : G) Uγ) := by
          conv_rhs => rw [← hQ]
          rw [F9.relIndex_conjSub]
      _ ≤ (pCoreOf 2 H).relIndex (pCoreOf 2 (l1 T L V ⊔ T)) :=
          Subgroup.relIndex_le_of_le_right hUα (by exact Subgroup.index_ne_zero_of_finite)
      _ = 4 := hR4

  obtain ⟨x, hxU, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hUQ
  have hxH : x ∈ H := hUH hxU
  have hxR : (hh : G) * x * (hh : G)⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) :=
    hUα ⟨x, hxU, by simp [MulAut.conj_apply]⟩
  obtain ⟨k₀, hk₀, hq⟩ := hRK _ hxR
  have hk₁ : (hh : G)⁻¹ * k₀ * (hh : G) ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (hKnH (H.inv_mem hhH)) k₀).mp hk₀
    simpa using this
  have hq' : ((hh : G)⁻¹ * k₀ * (hh : G))⁻¹ * x ∈ pCoreOf 2 H := by
    have e1 : ((hh : G)⁻¹ * k₀ * (hh : G))⁻¹ * x =
        (hh : G)⁻¹ * (k₀⁻¹ * ((hh : G) * x * (hh : G)⁻¹)) * ((hh : G)⁻¹)⁻¹ := by group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hhH)) _).mp hq
  have hΦx : Φ ⟨x, hxH⟩ ∈ (K.subgroupOf H).map Φ := by
    refine ⟨⟨_, hKH hk₁⟩, hk₁, ?_⟩
    have h1 := (hker (⟨_, hKH hk₁⟩⁻¹ * ⟨x, hxH⟩)).mpr (by simpa using hq')
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hx2 : Φ ⟨x, hxH⟩ * Φ ⟨x, hxH⟩ = 1 := by
    rw [← map_mul]
    have h2 : x ^ 2 = 1 := hUab.2 x hxU
    rw [show (⟨x, hxH⟩ : ↥H) * ⟨x, hxH⟩ = 1 from Subtype.ext (by rw [← pow_two]; exact h2),
      map_one]
  have hx1 : Φ ⟨x, hxH⟩ ≠ 1 := fun h => hxQ ((hker _).mp h)

  have hW2 : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure V H)), w * w = 1 := by
    intro w
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H))).2 w w.2
    simpa [pow_two] using this
  have h16 := A5Mod.sixteen_le_card_range hW2 e hYZ hY hZ hntY hntZ hΦx hx2 hx1
  rw [card_range_commHom_phiU hF ⟨x, hxH⟩] at h16
  simp only at h16

  have hcx : (centralizerMod (fsuV1 T V) (conjClosure V H) (Subgroup.zpowers x)).relIndex
      (conjClosure V H) ≤
      (centralizerMod (fsuV1 T V) (conjClosure V H) Uγ).relIndex (conjClosure V H) := by
    refine Subgroup.relIndex_le_of_le_left (fun a ha => ⟨ha.1, ha.2.1, fun u hu =>
      ha.2.2 u ((Subgroup.zpowers_le.mpr hxU) hu)⟩) (by exact Subgroup.index_ne_zero_of_finite)
  have ha' : (Uγ ⊓ pCoreOf 2 H).relIndex Uγ = (pCoreOf 2 H).relIndex Uγ := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [ha'] at hc
  have hc16 : (centralizerMod (fsuV1 T V) (conjClosure V H) Uγ).relIndex (conjClosure V H) =
      16 := by nlinarith
  have ha4' : (pCoreOf 2 H).relIndex Uγ = 4 := by nlinarith

  have hUp : IsPGroup 2 Uγ := isPGroup_of_isElemAbelian hUab
  have hUHp : IsPGroup 2 (conjClosure V H) := isPGroup_of_isElemAbelian hF98.F911_3
  have hm1 : mIdx Uγ (F8.Dγ V (fsuV1 T V) H (gk : G)) = 2 := by
    have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.Dγ V (fsuV1 T V) H (gk : G)) hUp
    rw [hF98.Dγ_eq_inf_pCoreOf N.setup] at h1 ⊢
    rw [ha', ha4'] at h1
    exact Nat.pow_right_injective le_rfl (h1.symm.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
  have hm2 : mIdx (conjClosure V H) (centralizerMod (fsuV1 T V) (conjClosure V H) Uγ) = 4 := by
    have h1 := HypF98.relIndex_eq_two_pow_mIdx
      (Y := centralizerMod (fsuV1 T V) (conjClosure V H) Uγ) hUHp
    rw [hc16] at h1
    exact Nat.pow_right_injective le_rfl (h1.symm.trans (by norm_num : (16 : ℕ) = 2 ^ 4))
  obtain ⟨hmDH, -, hcomm, hA₁, -, -⟩ := heq (by rw [hm1, hm2])

  have hDH4 : (F8.DH V (fsuV1 T V) H (gk : G)).relIndex (conjClosure V H) = 4 := by
    have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.DH V (fsuV1 T V) H (gk : G)) hUHp
    rw [h1, ← hmDH, hm1]
    norm_num
  have hUN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H)
  have hD' : ((tildeOf (fsuV1 T V) (F8.DH V (fsuV1 T V) H (gk : G))).subgroupOf
      (tildeOf (fsuV1 T V) (conjClosure V H))).index = 4 := by
    rw [← hDH4]
    exact relIndex_secImg (V₁_le_DH_F4 h1332 h1334 S hF N.setup) (centralizerMod_le_left _ _ _) hUN
  have h8 := card_range_le_index_mul (A5Mod.commHom (Φ ⟨x, hxH⟩))
    ((tildeOf (fsuV1 T V) (F8.DH V (fsuV1 T V) H (gk : G))).subgroupOf
      (tildeOf (fsuV1 T V) (conjClosure V H)))
  rw [hD', card_range_commHom_phiU hF ⟨x, hxH⟩] at h8
  simp only at h8
  have h2 := card_map_commHom_DH_le hF hcomm hA₁ (x := ⟨x, hxH⟩) hxU
  rw [← hΦ] at h2
  omega

end CFSG.Quasithin.H13.L32A.C
