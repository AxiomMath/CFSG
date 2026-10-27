module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2q

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K H : Subgroup G}

theorem L2Red.inf_centralizer_qh_F4 (hD36 : D36) (hD37 : D37)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4) (h33 : Lemma14_7_33_F4)
    (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h13314 : A6.Stmt13_3_14_F4)
    (R : L2Red G T L V K) (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hcase : L2CaseOne G T L V) :
    conjClosure V (A6.g1 T V) ⊓ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) =
      fsuV1 T V := by
  have hV1U : fsuV1 T V ≤ conjClosure V (A6.g1 T V) :=
    hF.toHypF91.V₁_le_V.trans (le_conjClosure V _)
  have hle : fsuV1 T V ≤
      conjClosure V (A6.g1 T V) ⊓ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) :=
    le_inf hV1U fun v hv => Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer (pCoreOf_le 2 _ hq)) v hv).symm
  have hUN : A6.g1 T V ≤ Subgroup.normalizer (conjClosure V (A6.g1 T V) : Set G) :=
    le_normalizer_conjClosure V _
  have hQN : A6.g1 T V ≤ Subgroup.normalizer (pCoreOf 2 (A6.g1 T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hN : A6.g1 T V ≤ Subgroup.normalizer ((conjClosure V (A6.g1 T V) ⊓
      Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_of_forall_conj
      (R := conjClosure V (A6.g1 T V) ⊓ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G))
      (fun k hk x hx => Subgroup.mem_inf.mpr ⟨
      (Subgroup.mem_normalizer_iff.mp (hUN hk) x).mp hx.1,
      Subgroup.mem_centralizer_iff.mpr fun q hq => by
        have hq' : k⁻¹ * q * k ∈ pCoreOf 2 (A6.g1 T V) := by
          have := (Subgroup.mem_normalizer_iff.mp (hQN (inv_mem hk)) q).mp hq
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hq'
        calc q * (k * x * k⁻¹) = k * ((k⁻¹ * q * k) * x) * k⁻¹ := by group
          _ = k * (x * (k⁻¹ * q * k)) * k⁻¹ := by rw [h1]
          _ = k * x * k⁻¹ * q := by group⟩) hg
  rcases L2Red.irred_F4 hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334 R hF hcase hle
      inf_le_left hN with h | h
  · exact h
  · exfalso
    have h13322 := stmt13_3_2_two_of_F4 h1332
    have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
    obtain ⟨V₂, hV2⟩ := R.S.hyp.exists_V2_F4 h13322 hMod h1222
    have h741 := lemma14_7_4_one_F4 R.S.hyp h13322 hMod h13314 hV2
    have hV2C : V₂ ≤ Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) := by
      intro v hv
      have : v ∈ conjClosure V (A6.g1 T V) ⊓
          Subgroup.centralizer (pCoreOf 2 (A6.g1 T V) : Set G) := by
        rw [h]
        exact le_conjClosure V _ (hV2.2.1 hv)
      exact this.2
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hV2C] at h741
    have := hF.card_V₁
    rw [← h741, Subgroup.card_bot] at this
    omega

end CFSG.Quasithin.H13.L32A.L2
