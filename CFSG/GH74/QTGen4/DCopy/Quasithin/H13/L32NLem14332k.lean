module

public import CFSG.Quasithin.H13.L32NLem14332k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332j

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement MatrixGroups

namespace L14332

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)} {K : Subgroup G}

theorem fsuU_le_commutator_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V)) :
    fsuU T V ≤ ⁅fsuU T V, K⁆ := by
  have := finite_linearEquiv D
  obtain ⟨_, S⟩ := exists_setting_F4 h1332 h1334 h1222 C.hyp C.plane
  have hN := le_normalizer_commutator (le_normalizer_cComp hii hQ hK)
  set U₀ := ⁅fsuU T V, K⁆ with hU₀

  obtain ⟨z, -, b, hz, hz1, -, -, hbV, hbV₂⟩ := S.exists_basis_F4
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := C.plane.2 hz
  have haV : a ∈ V := C.plane.1.1 C.aV₂
  obtain ⟨x, hxL, hx3, hxz, hxa, hxb⟩ := S.exists_rot_F4 hzV haV hbV
    (fun h => C.a1 (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => C.a1 (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ C.aV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ C.aV₂))
  have hxH : x ∈ l32nH T V := S.mem_g1_F4 hz hz1 hxz
  have hxK : x ∈ K := mem_cComp_of_odd hii hQ hK hxH (by decide : Odd 3) hx3
  have hbU : b ∈ fsuU T V := C.V_U hbV

  have ha : a ∈ U₀ := by
    have h1 : ⁅b, x⁆ ∈ U₀ := Subgroup.commutator_mem_commutator hbU hxK
    have e : ⁅b, x⁆ = a⁻¹ := by
      rw [commutatorElement_def, show b * x * b⁻¹ * x⁻¹ = b * (x * b * x⁻¹)⁻¹ by group, hxb]
      group
    rw [e] at h1
    simpa using U₀.inv_mem h1
  have hb : b ∈ U₀ := by
    have h1 : ⁅a, x⁆ ∈ U₀ := Subgroup.commutator_mem_commutator C.aU hxK
    have e : ⁅a, x⁆ = a * b⁻¹ := by
      rw [commutatorElement_def, show a * x * a⁻¹ * x⁻¹ = a * (x * a * x⁻¹)⁻¹ by group, hxa]
    rw [e] at h1
    have := U₀.mul_mem (U₀.inv_mem h1) ha
    simpa [mul_assoc] using this

  have hz0 : z ∈ U₀ := by
    have haZ : a ∉ centerOf (fsuU T V) := fun hm =>
      C.pi_ne ((L128A.HatU.π_eq_zero_iff D C.aU).mpr hm)
    obtain ⟨u, huU, hua⟩ : ∃ u ∈ fsuU T V, u * a ≠ a * u := by
      by_contra hne
      push Not at hne
      exact haZ (Subgroup.mem_inf.mpr ⟨C.aU, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        hne u hu⟩)
    have hne1 : ⁅u, a⁆ ≠ 1 := by
      rw [Ne, commutatorElement_eq_one_iff_mul_comm]
      exact hua
    have hcz : ⁅u, a⁆ = z := (S.eq_of_mem_V1_F4 hz hz1 (C.comm u huU a C.aU)).resolve_left hne1
    have h1 : u * a * u⁻¹ ∈ U₀ := (Subgroup.mem_normalizer_iff.mp (hN (C.U_le huU)) a).mp ha
    rw [← hcz, commutatorElement_def]
    exact U₀.mul_mem h1 (U₀.inv_mem ha)

  have hV : V ≤ U₀ := by
    have hV1 : ∀ c ∈ fsuV1 T V, c ∈ U₀ := fun c hc => by
      rcases S.eq_of_mem_V1_F4 hz hz1 hc with rfl | rfl
      · exact U₀.one_mem
      · exact hz0
    have hV₂ : ∀ w ∈ V₂, w ∈ U₀ := by
      intro w hw
      rcases C.V₂_cases w hw with hw1 | ⟨c, hc, rfl⟩
      · exact hV1 w hw1
      · exact U₀.mul_mem ha (hV1 c hc)
    intro v hv
    rcases S.mem_V_F4 hbV hbV₂ hv with hv2 | hv2
    · exact hV₂ v hv2
    · have := U₀.mul_mem (U₀.inv_mem hb) (hV₂ _ hv2)
      simpa using this
  exact conjClosure_le fun h hh v hv => (Subgroup.mem_normalizer_iff.mp (hN hh) v).mp (hV hv)

theorem fsuU_eq_commutator_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h14323 : Lemma14323Rest_F4) (C : Ctx14332 G T L V V₂ g a D)
    (hii : Case14323ii T V g D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hQT : pCoreOf 2 (l32nH T V) ≤ T)
    (hK : K ∈ cComp (l32nH T V)) : fsuU T V = ⁅pCoreOf 2 K, K⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hKn := le_normalizer_cComp hii hQ hK
  have hUU₀ := fsuU_le_commutator_F4 h1332 h1334 h1222 C hii hQ hK
  have hUK : fsuU T V ≤ K := hUU₀.trans (Subgroup.commutator_le.mpr fun u hu k hk => by
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hKn (C.U_le hu)) k).mp hk) (inv_mem hk))
  have hUO : fsuU T V ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUK
      (hKH.trans (l32nH_le_normalizer_fsuU T V)) C.U2
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 (l32nH T V) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  apply le_antisymm (hUU₀.trans (Subgroup.commutator_mono hUO le_rfl))
  calc ⁅pCoreOf 2 K, K⁆ ≤ ⁅pCoreOf 2 (l32nH T V), K⁆ := Subgroup.commutator_mono hOQ le_rfl
    _ = ⁅K, pCoreOf 2 (l32nH T V)⁆ := Subgroup.commutator_comm _ _
    _ ≤ fsuU T V := commutator_K_Q_le_F4 h1222 h12213 h14323 C hii hd hQ hQT hK

end L14332

end CFSG.Quasithin.H13
