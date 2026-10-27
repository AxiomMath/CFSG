module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.Background.C126Split2
public import CFSG.Quasithin.H13.A5W1617c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model B2F E2
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem not_le_centralizer_z_of_plus_eq_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ : Subgroup G} (hK₀im : autOn K₀ (S.WK K) = S.plus K) :
    ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G) := by
  intro hK₀z
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  apply S.not_le_centralizer_z_of_inYz hK hT
  intro k hk
  have hkW := hKW hk
  have hkp : conjAct (S.WK K) ⟨k, hkW⟩ ∈ autOn K₀ (S.WK K) := by
    rw [hK₀im]; exact Setup.mem_autOn_iff.2 ⟨⟨k, hkW⟩, hk, rfl⟩
  obtain ⟨⟨k₀, hk₀N⟩, hk₀, hk₀e⟩ := Setup.mem_autOn_iff.1 hkp
  have hc : k₀⁻¹ * k ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
    have h1 : conjAct (S.WK K) ((⟨k₀, hk₀N⟩ :
        ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G)))⁻¹ * ⟨k, hkW⟩) = 1 := by
      rw [map_mul, map_inv, hk₀e, inv_mul_cancel]
    exact A4.conjAct_eq_one_iff.mp h1
  have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have h1 : k₀⁻¹ * k ∈ Subgroup.centralizer ({S.z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc _ hzW).symm
  have e : k = k₀ * (k₀⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hK₀z hk₀) h1

theorem e23_cases_F4 (h23 : E2.E23Statement) (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ M : Subgroup G} (hK₀K : K₀ ≤ K) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hK₀im : autOn K₀ (S.WK K) = S.plus K) (hmp : MinParabolic (K₀ ⊔ S.Tv) S.Tv M) :
    ∃ hV : IsElemAbelian 2 (conjClosure S.V1 (K₀ ⊔ S.Tv)),
      IsTwoReducedIn (K₀ ⊔ S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)) ∧
      (C126.NatCase (K₀ ⊔ S.Tv) S.Tv (conjClosure S.V1 (K₀ ⊔ S.Tv)) hV ∨
        C126.A5Case (K₀ ⊔ S.Tv) S.Tv (conjClosure S.V1 (K₀ ⊔ S.Tv)) hV) := by
  set H := K₀ ⊔ S.Tv with hHdef
  set V' := conjClosure S.V1 H with hV'def
  have hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₀K.trans hK.1
  have hsylTv := S.isSylowTwoOf_Tv_F4 h1222 h517
  have hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  have hHchar : CharTwo H := C1GN.charTwo_of_le hF hsylTv le_sup_right hHG
  have hsylH : IsSylowTwoOf S.Tv H := hmp.isSylow
  have hred : IsTwoReducedIn H V' :=
    isTwoReducedIn_conjClosure_of_sylowIn hsylH.1 hsylH.2.1 hsylH.2.2 hHchar S.V1_le_omega_Tv
  have hV : IsElemAbelian 2 V' := hred.2.2.1
  refine ⟨hV, hred, ?_⟩

  have hvT : S.v12 ∈ S.Tv :=
    ⟨S.V_le_T S.v12_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hO : pCoreOf 2 H ≠ ⊥ := by
    have hle : Subgroup.zpowers S.v12 ≤ H := (Subgroup.zpowers_le.mpr hvT).trans le_sup_right
    have hN : H ≤ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hg
      have hgG : g ∈ Subgroup.centralizer ({S.v12} : Set G) := hHG hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    intro h
    have hvO := le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
    rw [h, Subgroup.mem_bot] at hvO
    exact S.v12_ne_one hvO
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hO

  have hz := S.not_le_centralizer_z_of_plus_eq_F4 h1222 h517 hF hK hT hK₀im
  have hzV : S.z ∈ V' := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hK₀V : ¬ K₀ ≤ Subgroup.centralizer (V' : Set G) := fun h =>
    hz fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h hk) _ hzV).symm

  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hHK : H ≤ S.HK K := sup_le (hK₀K.trans (le_sup_left.trans le_sup_left)) (S.Tv_le_HK K)
  have hVW : V' ≤ S.WK K := by
    rw [S.WK_eq hT]
    exact conjClosure_mono le_rfl hHK
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  have hK₀W := hK₀K.trans hKW
  have hJW : thompsonJ S.Tv ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (B6.thompsonJ_le S.Tv).trans ((S.Tv_le_HK K).trans hR.2.1)
  have hJ : ¬ thompsonJ S.Tv ≤ Subgroup.centralizer (V' : Set G) := by
    intro hJV
    apply hK₀V
    have hJV' : ⁅thompsonJ S.Tv, V'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJV
    have hVK : ⁅V', K₀⁆ ≤ V' := by
      rw [Subgroup.commutator_le]
      intro w hw k hk
      have hkN : k ∈ Subgroup.normalizer (V' : Set G) :=
        hred.2.1 (Subgroup.mem_sup_left hk)
      have h1 : k * w⁻¹ * k⁻¹ ∈ V' :=
        (Subgroup.mem_normalizer_iff.mp hkN _).mp (V'.inv_mem hw)
      have e2 : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e2]
      exact V'.mul_mem hw h1
    have h3 : ⁅⁅K₀, thompsonJ S.Tv⁆, V'⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [hJV', Subgroup.commutator_bot_left]
      · refine le_bot_iff.mp ((Subgroup.commutator_mono hVK le_rfl).trans ?_)
        rw [Subgroup.commutator_comm, hJV']
    have hcV : ⁅K₀, thompsonJ S.Tv⁆ ≤ Subgroup.centralizer (V' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
    have hKJ : autOn ⁅K₀, thompsonJ S.Tv⁆ (S.WK K) = S.plus K := by
      rw [CFSG.Quasithin.H13.A5.autOn_commutator hK₀W hJW, hK₀im]
      exact S.plus_eq_commutator_F4 h1222 h517 hF hK hT
    intro k hk
    have hkN := hK₀W hk
    have hkp : conjAct (S.WK K) ⟨k, hkN⟩ ∈ autOn ⁅K₀, thompsonJ S.Tv⁆ (S.WK K) := by
      rw [hKJ, ← hK₀im]; exact Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hk, rfl⟩
    obtain ⟨⟨c, hcN⟩, hc, hce⟩ := Setup.mem_autOn_iff.1 hkp
    have hcW : c⁻¹ * k ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
      have h1 : conjAct (S.WK K) ((⟨c, hcN⟩ :
          ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G)))⁻¹ * ⟨k, hkN⟩) = 1 := by
        rw [map_mul, map_inv, hce, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have e : k = c * (c⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hcV hc) (Subgroup.centralizer_le hVW hcW)
  have hc := h23 G H S.Tv M V' hV hmp hSQ hHchar hred hJ
  rcases C126.case_split hV S.Tv hred.2.1 hc with hs | hn | ha
  · exfalso
    apply hK₀V
    exact (le_perfectCore_of_perfect le_sup_left (perfect_of_mem_cComp hK₀)).trans hs
  · exact Or.inl hn
  · exact Or.inr ha

end Setting

end CFSG.Quasithin.H13.A5
