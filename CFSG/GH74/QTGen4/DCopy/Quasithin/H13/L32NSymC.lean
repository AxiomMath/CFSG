module

public import CFSG.Quasithin.H13.L32NSymC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A58S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

open L32NSym in

theorem lemma14_5_8Sym_of_inputs_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : Lemma14_5_8Sym_F4 := by
  intro G _ _ T L V V₂ Y K hyp hV2 _ hYG1 _ _ hYM hO2 hKc hKf hHKT _ hO2K _ hVH hnatK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := L₁Of L V₂ ⊔ Y ⊔ T with hHdef
  set VH := conjClosure (fsuV1 T V) H with hVHdef
  obtain ⟨_, hnat⟩ := hnatK
  have : IsMulCommutative ↥V := (stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V hyp.hyp
    hyp.fsu).1.1
  have S' := hyp.set14_F4 h1222 h1332 h1334 hV2
  have hT := hyp.hyp.h13.sylow
  have hT2 : IsPGroup 2 T := hT.1
  have hTH : T ≤ H := le_sup_right
  have hTLT : T ≤ L ⊔ T := le_sup_right
  obtain ⟨Ts, hTs⟩ := exists_sylow_of_quasithinIsSylowTwo hT

  have hL13 := h1332 G T L hyp.hyp.h13 L hyp.hyp.h13.faithful
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hL13.2.1.1

  obtain ⟨z, -, -, hz, hz1, -, -, -, -⟩ := S'.exists_basis_F4
  have hV8 : Nat.card V = 8 := S'.card_V_F4
  have hVLT : V ≤ L ⊔ T := S'.VT_F4.trans le_sup_right
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S'.LV_F4 S'.TV_F4
  have hVel : IsElemAbelian 2 V :=
    ⟨inferInstance, fun v hv => S'.sq_V_F4 hv⟩
  have htopV : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One S'.h1281_F4
  have htransV : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ x ∈ L, x * v * x⁻¹ = w :=
    fun v hv w hw hv1 hw1 => exists_conj_eq (fun u hu => S'.sq_V_F4 hu) htopV hv hw hv1 hw1

  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hV1T : fsuV1 T V ≤ T := fun x hx => S'.VT_F4 (Subgroup.mem_inf.mp hx).1
  have hVHH : VH ≤ H := conjClosure_le fun h hh v hv => H.mul_mem (H.mul_mem hh (hTH (hV1T hv)))
    (H.inv_mem hh)
  have hHVH : H ≤ Subgroup.normalizer (VH : Set G) := le_normalizer_conjClosure _ _
  have hKH : K ≤ H := hHKT ▸ le_sup_left
  have hVH8 : Nat.card VH = 8 := card_of_natural hnat
  have hVHsq := sq_of_natural hnat
  have hVHel : IsElemAbelian 2 VH := ⟨inferInstance, hVHsq⟩
  have htopVH : autOn K VH = ⊤ := autOn_eq_top hnat
  have htransVH : ∀ v ∈ VH, ∀ w ∈ VH, v ≠ 1 → w ≠ 1 → ∃ x ∈ K, x * v * x⁻¹ = w :=
    fun v hv w hw hv1 hw1 => exists_conj_eq hVHsq htopVH hv hw hv1 hw1
  have hzVH : z ∈ VH := le_conjClosure _ _ hz

  set G₀ := (L ⊔ T) ⊔ H with hG₀
  have hO2G₀ : pCoreOf 2 G₀ = ⊥ := by
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 G₀ : Set G)) :=
      ⟨_, hne, pCoreOf_isPGroup 2 G₀, rfl⟩
    obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge hloc
    have hG₀N := le_normalizer_pCoreOf 2 G₀
    have hMeq := hL13.2.1.2.2.2 M hM ((le_sup_left.trans hG₀N).trans hle)
    apply hYM
    exact (((le_sup_right.trans (le_sup_left : L₁Of L V₂ ⊔ Y ≤ H)).trans le_sup_right).trans
      (hG₀N.trans hle)).trans hMeq.le

  have hcharLT : CharTwo (L ⊔ T) := by
    refine charTwo_of_inH hyp.hyp.h13.qtke.2.1 Ts ⟨hTs ▸ hTLT, fun h => ?_⟩
    have hVle : V ≤ pCoreOf 2 (L ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 hVLT hLTV
        (fun v => ⟨1, Subtype.ext (by simpa using S'.sq_V_F4 v.2)⟩)
    rw [h] at hVle
    have := Subgroup.card_le_of_le hVle
    rw [hV8, Subgroup.card_bot] at this
    omega
  have hcharH : CharTwo H := charTwo_of_inH hyp.hyp.h13.qtke.2.1 Ts ⟨hTs ▸ hTH, hO2⟩
  have hA1 : AmalgamHyp G₀ (L ⊔ T) H T :=
    ⟨rfl, hcharLT, isSylowTwoOf_of_quasithinIsSylowTwo hT hTLT,
      isSylowTwoOf_of_quasithinIsSylowTwo hT hTH, hO2G₀⟩
  have hA2 : AmalgamHyp G₀ H (L ⊔ T) T :=
    ⟨sup_comm _ _, hcharH, isSylowTwoOf_of_quasithinIsSylowTwo hT hTH,
      isSylowTwoOf_of_quasithinIsSylowTwo hT hTLT, hO2G₀⟩
  have hredV : IsTwoReducedIn (L ⊔ T) V :=
    isTwoReducedIn_of_trans hVLT hLTV hVel le_sup_left (by rw [hV8]; norm_num) htransV
  have hredVH : IsTwoReducedIn H VH :=
    isTwoReducedIn_of_trans hVHH hHVH hVHel hKH (by rw [hVH8]; norm_num) htransVH
  have hC2V : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := S'.isPGroup_cent_sup_F4
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (h1332 G T L hyp.hyp.h13 K hKf).2.1.1
  have hC2VH : IsPGroup 2 ↥(H ⊓ Subgroup.centralizer (VH : Set G)) := by
    have hK2 : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (VH : Set G)) := by
      rw [← hO2K]
      exact pCoreOf_isPGroup 2 K
    rw [hHKT]
    exact isPGroup_inf_centralizer hT2 hTK hK2
  have h1 : AmalgamHypV G₀ (L ⊔ T) H T V := amalgamHypV_of hA1 hredV hC2V
  have h2 : AmalgamHypV G₀ H (L ⊔ T) T VH := amalgamHypV_of hA2 hredVH hC2VH
  have hC₁ : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ H :=
    (le_of_isPGroup_normal hA1.sylow₁ inf_le_left (le_normalizer_inf_centralizer' hLTV)
      hC2V).trans hTH
  have hC₂ : H ⊓ Subgroup.centralizer (VH : Set G) ≤ L ⊔ T :=
    (le_of_isPGroup_normal hA2.sylow₁ inf_le_left (le_normalizer_inf_centralizer' hHVH)
      hC2VH).trans hTLT

  set U := fsuU T V with hUdef
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hyp.abelian.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hG₁U : A6.g1 T V ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ _
  have hzG₁ : ∀ c : G, c * z * c⁻¹ = z → c ∈ A6.g1 T V := fun c hc => S'.mem_g1_F4 hz hz1 hc
  have hVU : V ≤ U := le_conjClosure _ _
  have hVHU : VH ≤ U := by
    rw [hVH]
    exact conjClosure_mono S'.hV2.2.1 hYG1
  have htV : ∀ v ∈ V, v ≠ 1 → ∃ x ∈ L, x * v * x⁻¹ = z := fun v hv hv1 =>
    htransV v hv z hzV hv1 hz1
  have htVH : ∀ v ∈ VH, v ≠ 1 → ∃ x ∈ K, x * v * x⁻¹ = z := fun v hv hv1 =>
    htransVH v hv z hzVH hv1 hz1
  have hcomm : ∀ (A B : Subgroup G), (A = V ∨ A = VH) → (B = V ∨ B = VH) → ∀ g g' u : G,
      u ∈ CFSG.Quasithin.conjSub g A → u ∈ CFSG.Quasithin.conjSub g' B → u ≠ 1 →
        ∀ a ∈ CFSG.Quasithin.conjSub g A, ∀ b ∈ CFSG.Quasithin.conjSub g' B,
          a * b = b * a := by
    intro A B hA hB g g' u huA huB hu1
    simp only [conjSub_eq_conjugate] at huA huB ⊢
    have hdata : ∀ C : Subgroup G, (C = V ∨ C = VH) → ∃ X : Subgroup G, C ≤ U ∧
        X ≤ Subgroup.normalizer (C : Set G) ∧ ∀ v ∈ C, v ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = z := by
      rintro C (rfl | rfl)
      · exact ⟨L, hVU, S'.LV_F4, htV⟩
      · exact ⟨K, hVHU, hKH.trans hHVH, htVH⟩
    obtain ⟨X, hAU, hXA, htA⟩ := hdata A hA
    obtain ⟨Y', hBU, hYB, htB⟩ := hdata B hB
    intro a ha b hb
    exact comm_of_inf_ne_bot hUc hG₁U hzG₁ hAU hBU hXA hYB htA htB huA huB hu1 a ha b hb
  have hV0 : V ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hV8
    omega
  have hVH0 : VH ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hVH8
    omega
  exact false_of_two_amalgams h1 h2 hV0 hVH0 hC₁ hC₂ hcomm

end CFSG.Quasithin.H13
