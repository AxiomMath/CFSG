module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.GH74.QTGen4.Leaves.FiveFixed
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.H13.A5S1327a

public section

namespace CFSG.GH74.QTGen4.A5

open CFSG.GH74 CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

theorem res1328aSym_gen4 {G : Type} [Group G] [Finite G] (hG : Gen4 G) {T L V : Subgroup G}
    (S : CFSG.Quasithin.H13.A5.Setting G T L V) {H K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    rw [hHK]
    refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, cComp_subset_lFamily hH.1.1 hKc,
      (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2, by rw [← hHK]; exact hH.1.2⟩
  have hKf : quasithinIsFaithfulLocal T K :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hKloc hZK
  obtain ⟨φ, hφs, hφk⟩ := S.h13.a5 S.a5 K hKf
  have hker2 : ∀ k : K, φ k = 1 → ∃ n : ℕ, orderOf k = 2 ^ n := by
    intro k hk
    have hkp : k ∈ CFSG.pCore 2 K := by
      rw [← hφk]
      exact MonoidHom.mem_ker.2 hk
    have hP : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨k, hkp⟩
    exact ⟨n, (Subgroup.orderOf_coe (⟨k, hkp⟩ : CFSG.pCore 2 K)).trans hn⟩
  have hFH : CharTwo H := S.charTwo_of_inH hH.1
  have hTH : IsSylowTwoOf T H := by
    rw [hHK]
    exact isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hZW : quasithinOmegaOneCenter T ≤ conjClosure (quasithinOmegaOneCenter T) H :=
    le_conjClosure _ _
  obtain ⟨hWle, hWel, hWtr⟩ :=
    conjClosure_isTwoReducedIn_of_charTwo hTH hFH (le_refl (quasithinOmegaOneCenter T))
  generalize conjClosure (quasithinOmegaOneCenter T) H = W at hZW hWle hWel hWtr
  have hKH : K ≤ H := by
    rw [hHK]
    exact le_sup_left
  have hPK : pCoreOf 2 K ≤ pCoreOf 2 H :=
    pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hKc)
  have hkerC : ∀ k : K, φ k = 1 → ∀ w ∈ W, w * (k : G) = (k : G) * w := by
    intro k hk w hw
    have hkp : (k : G) ∈ pCoreOf 2 K := by
      rw [CFSG.Quasithin.C2A3Orbits.pCoreOf_eq_map_pCore K]
      refine Subgroup.mem_map.2 ⟨k, ?_, rfl⟩
      rw [← hφk]
      exact MonoidHom.mem_ker.2 hk
    have hwc : w ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      (Subgroup.mem_inf.1 (hWle hw)).2
    exact (Subgroup.mem_centralizer_iff.1 hwc (k : G) (hPK hkp)).symm
  have hKW : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    intro k hk w hw
    exact (Subgroup.mem_normalizer_iff.1 (hWtr.2.1 (hKH hk)) w).1 hw
  have hnt : ∃ k ∈ K, ∃ w ∈ W, w * k ≠ k * w := by
    by_contra hcon
    push Not at hcon
    apply hZK
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun z hz =>
      Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    exact (hcon k hk z (hZW hz)).symm
  obtain ⟨x, hxK, hx5, w₀, hw₀, hxw⟩ :=
    CFSG.GH74.QTGen4.Leaves.exists_five_acting K W φ hφs hker2 hkerC hKW hnt
  rw [eq_bot_iff]
  rintro ζ hζ
  obtain ⟨hζΩ, hζC⟩ := Subgroup.mem_inf.1 hζ
  rw [Subgroup.mem_bot]
  have hζW : ζ ∈ W := hZW hζΩ
  have hfix : x * ζ * x⁻¹ = ζ := by
    rw [Subgroup.mem_centralizer_iff.1 hζC x hxK, mul_inv_cancel_right]
  exact CFSG.GH74.QTGen4.Leaves.five_fixed hG W hWel x hx5 (hKW x hxK) ⟨w₀, hw₀, hxw⟩ ζ hζW hfix

theorem res1328aSym_finite4 {G : Type} [Group G] [Finite4 G] {T L V : Subgroup G}
    (S : CFSG.Quasithin.H13.A5.Setting G T L V) {H K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
  res1328aSym_gen4 Finite4.gen4 S hH hHZ hKc hHK

end CFSG.GH74.QTGen4.A5
