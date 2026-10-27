module

public import CFSG.Quasithin.H13.L32NItems144CTL
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144CTL4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144CTL7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144CTL8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144CTL9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1445a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem false_of_conj_F4 (h331 : Stmt3_3_1_F4) (h12213 : Stmt12_2_13_F4) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4)
    (h1434 : Lemma1434One_F4) {σ h t d : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hσT : σ ∈ T) (hhH : h ∈ l32nH T V)
    (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V)) (htT : t ∈ T)
    (htZ : t ∈ Subgroup.centralizer (T : Set G)) (ht1 : t ≠ 1)
    (hdD : d ∈ T ⊓ Subgroup.centralizer (L : Set G)) (htd : t = S.cfg.z * d)
    (hj : h⁻¹ * t * h ∈ T ⊓ Subgroup.centralizer (L : Set G)) : False := by
  have htL : L.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 := Subgroup.mem_centralizer_iff.mp hj.2 l hl
    calc h * l * h⁻¹ * t = h * (l * (h⁻¹ * t * h)) * h⁻¹ := by group
      _ = h * (h⁻¹ * t * h * l) * h⁻¹ := by rw [h1]
      _ = t * (h * l * h⁻¹) := by group
  obtain ⟨K₀, hK₀, hLK⟩ := exists_cComp_F4 S h37 h39 hRest hσW hσQ hσ2 hhH hσh hσT htT htZ ht1 htL
  have hK₀f := isFaithfulLocal_K₀_F4 S h12213 h13322 hV hhH htT htZ ht1 hK₀ hLK
  have hTK := (h13322 G T L S.hyp.hyp.h13 K₀ hK₀f).1
  have heq := inf_pCoreOf_eq S hLK (card_quot_le (h1434 G T L S.hyp.hyp K₀ hK₀f))
  have hhM := mem_M_of_conj_F4 S h331 h13322 (T_le_normalizer_V₀ S hhH hTK heq)

  have htD := (Subgroup.mem_normalizer_iff.mp (M_le_normalizer S hhM) _).mp hj
  rw [show h * (h⁻¹ * t * h) * h⁻¹ = t by group] at htD
  apply z_not_mem_centralizer_F4 S h12213 h13322 hV
  have hz : S.cfg.z = t * d⁻¹ := by rw [htd]; group
  rw [hz]
  exact (Subgroup.centralizer _).mul_mem htD.2 ((Subgroup.centralizer _).inv_mem hdD.2)

theorem false_of_swap_F4 (h331 : Stmt3_3_1_F4) (h12213 : Stmt12_2_13_F4) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4)
    (h1434 : Lemma1434One_F4)
    (hK9 : Nat.card ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) = 9)
    (hD : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {σ : G}
    (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g) (hσQ : σ ∉ pCoreOf 2 (l32nH T V))
    (hσ2 : σ * σ = 1) (hσT : σ ∈ T) (h12 : ∀ q ∈ Q₁, σ * q * σ⁻¹ ∈ Q₂)
    (h21 : ∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁) : False := by
  obtain ⟨c, hcK, -, hcfpf, hσc⟩ := S.exists_c0 hK9 (S.Wg_le_H hσW) hσ2 h12 h21
  have hcH : c ∈ l32nH T V := oTwoUpper_le _ hcK

  obtain ⟨⟨d, hdD, hdT, hdZ⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_center_ne_bot' S.hyp.fsu.sylow.1 inf_le_left (T_le_normalizer S) hD)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  obtain ⟨j, hj⟩ := exists_conj_mem_F4 S h12213 h13322 hV hσW hσ2 h21 hcK hcfpf hσc hdD hd1'
  have hzT : S.cfg.z ∈ T := S.QT (S.U_le_Q (V_le_U (z_mem_V1 S).1))
  have hzZ : S.cfg.z ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun s hs => comm_z S (S.TH hs)
  refine false_of_conj_F4 S h331 h12213 h13322 hV h37 h39 hRest h1434 hσW hσQ hσ2 hσT
    ((l32nH T V).pow_mem hcH j) (Setup3.comm_pow_mem_Q hcH hσc j) (T.mul_mem hzT hdT)
    ((Subgroup.centralizer _).mul_mem hzZ hdZ) (fun h1 => ?_) hdD rfl hj
  apply z_not_mem_centralizer_F4 S h12213 h13322 hV
  rw [eq_inv_of_mul_eq_one_left h1]
  exact (Subgroup.centralizer _).inv_mem hdD.2

end Setup

end L1444CTL

open L1444 L1444CTL in

theorem lemma1444CTL_holds_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest_F4) (h331 : Stmt3_3_1_F4) (h1352 : A6.Stmt13_5_2_F4) (h1381 : Stmt13_8_1_F4) :
    Lemma1444CTL_F4 := by
  intro G _ _ T L V h hext h32 hG2
  by_contra hD
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  obtain ⟨D, Q₁, Q₂, S⟩ :=
    exists_setup4_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2 hV₂ hgP hgH
  obtain ⟨-, hK9⟩ :=
    lemma1444One_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h hext h32 hG2
  obtain ⟨_, S'⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
  obtain ⟨x, hxW, hxQ⟩ := exists_mem_Wg_not_mem_Q S
  have hxU : ∀ q ∈ Q₁ ⊔ Q₂, x * q * x⁻¹ ∈ Q₁ ⊔ Q₂ := fun q hq => by
    rw [S.sup] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp
      (L14332.l32nH_le_normalizer_fsuU T V (S.Wg_le_H hxW)) q).mp hq
  rcases S.cfg.map_conj_cases hxU with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact false_of_normalizes_F4 S h12213 h13322 hV hD hxW hxQ
      (Q8SqE9.mem_normalizer_of_map_eq h1) (Q8SqE9.mem_normalizer_of_map_eq h2)
  · obtain ⟨σ, hσW, hσQ, hσ2, h12, h21⟩ := exists_swap_invol S hxW hxQ h1 h2
    exact false_of_swap_F4 S h331 h12213 h13322 hV h37 h39 hRest
      (lemma1434One_of_inputs_F4 h1332 h1352 h1381) hK9 hD hσW hσQ hσ2
      (S.Wg_le_T_F4 S.hyp.fsu.sylow S' hσW) h12 h21

end CFSG.Quasithin.H13
