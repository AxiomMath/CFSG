module

public import CFSG.Quasithin.H13.L32NItems144CTL8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144CTL1

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

theorem z_not_mem_centralizer_F4 (h12213 : Stmt12_2_13_F4) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) : S.cfg.z ∉ Subgroup.centralizer (L : Set G) := by
  intro hz
  have hV1T : fsuV1 T V ≤ T := fun v hv => S.QT (S.U_le_Q (V_le_U hv.1))
  have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
    have h2 := S.card2
    rw [h, Subgroup.card_bot] at h2
    omega
  have hL : L ≤ Subgroup.normalizer (fsuV1 T V : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => by
      have hv' : v ∈ centerOf (fsuU T V) := by rwa [S.zU]
      rcases S.mem_center_iff.mp hv' with rfl | rfl
      · simp
      · exact (Subgroup.mem_centralizer_iff.mp hz l hl).symm)
  exact lemma12_8_3_four_F4 h12213 (S.hyp.hyp1281One_F4 h13322 hV) (S.hyp.isTSub_fsuV1_F4 hV)
    (normalizer_le_M_F4 S h13322 hV1 (S.hyp.fsu.sylow.1.to_le hV1T) (sup_le hL S.TH))

theorem isFaithfulLocal_K₀_F4 (h12213 : Stmt12_2_13_F4) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) {h t : G} {K₀ : Subgroup G} (hhH : h ∈ l32nH T V) (htT : t ∈ T)
    (htZ : t ∈ Subgroup.centralizer (T : Set G)) (ht1 : t ≠ 1)
    (hK₀ : K₀ ∈ cComp (Subgroup.centralizer ({t} : Set G)))
    (hLK : L.map (MulAut.conj h).toMonoidHom ≤ K₀) : quasithinIsFaithfulLocal T K₀ := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.hyp.fsu.sylow
  have hTX : T ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htZ x hx)
  have htp : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    S.hyp.fsu.sylow.1.to_le (Subgroup.zpowers_le.mpr htT)
  have hO : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ := fun hb =>
    ht1 (by have := mem_pCoreOf_centralizer htp; rwa [hb, Subgroup.mem_bot] at this)
  have hH : InH (P : Subgroup G) (Subgroup.centralizer ({t} : Set G)) := ⟨hP ▸ hTX, hO⟩
  have hchar := charTwo_of_inH S.hyp.fsu.qtke.2.1 P hH
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo
    (isSylowTwoOf_of_sylow_le P hH.1) hchar (le_refl _)
  rw [← hP]
  refine isFaithfulLocal_of_commutator_ne_bot S.hyp.fsu.qtke.2.1 P hH hK₀ hred fun h0 => ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0

  apply z_not_mem_centralizer_F4 S h12213 h13322 hV
  have hzΩ : S.cfg.z ∈ quasithinOmegaOneCenter (P : Subgroup G) := hP ▸ (z_mem_V1 S).2
  have hzK : S.cfg.z ∈ Subgroup.centralizer (K₀ : Set G) := h0 (le_conjClosure _ _ hzΩ)
  have hz' : h⁻¹ * S.cfg.z * h = S.cfg.z := by
    rw [mul_assoc, ← comm_z S hhH]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := Subgroup.mem_centralizer_iff.mp hzK _ (hLK ⟨l, hl, rfl⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  calc l * S.cfg.z = h⁻¹ * ((h * l * h⁻¹) * S.cfg.z) * h := by
        rw [show h⁻¹ * ((h * l * h⁻¹) * S.cfg.z) * h = l * (h⁻¹ * S.cfg.z * h) by group, hz']
    _ = h⁻¹ * (S.cfg.z * (h * l * h⁻¹)) * h := by rw [h1]
    _ = (h⁻¹ * S.cfg.z * h) * l := by group
    _ = S.cfg.z * l := by rw [hz']

end Setup

end L1444CTL

end CFSG.Quasithin.H13
