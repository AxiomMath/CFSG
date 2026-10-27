module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321E

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace L3321

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem step3_3_21e_of_F4 (h5 : Stmt3_3_5) (h14 : Stmt3_3_14_F4) (hGA : GriessAllModelsStatement)
    (hd : Step3_3_21d_F4) : Step3_3_21e_F4 := by
  intro G _ _ T M L D h ⟨e⟩ hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  by_contra hne
  obtain ⟨⟨z, hzZ, hzL⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hz1 : z ≠ 1 := fun h1 => hz1' (Subtype.ext h1)
  have hz2 : IsPGroup 2 (Subgroup.zpowers (z : G)) := by
    have hzT : (z : G) ∈ T := L3317.omegaOneCenter_le T hzZ
    exact h.sylow.1.to_le ((Subgroup.zpowers_le).2 hzT)
  have hzc : ∀ g ∈ Subgroup.centralizer ({(z : G)} : Set G),
      g ∈ Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [MonoidHom.map_zpowers]
    congr 1
    show g * z * g⁻¹ = z
    rw [hg, mul_inv_cancel_right]
  have hzM : Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) ≤ M := by
    refine L3322.normalizer_le_M h5 h hML ?_ hz2 ?_
    · intro hb
      apply hz1
      have : (z : G) ∈ Subgroup.zpowers (z : G) := Subgroup.mem_zpowers _
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · refine sup_le (fun l hl => hzc l ?_) (fun t ht => hzc t ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hzL l hl
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := conj_omegaOneCenter ht hzZ
        calc t * z = (t * z * t⁻¹) * t := by group
          _ = z * t := by rw [h1]
  have hCM : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M := fun g hg =>
    hzM (hzc g (Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg z hzZ).symm))
  obtain ⟨α₀, hα₀s, hα₀k, -⟩ := Ln2.exists_modO2Surj h hGA hTL (K := ZMod 2) (Nat.card_zmod 2)
    le_rfl (by norm_num) e
  obtain ⟨α, hαs, hαk, hαU⟩ := Ln2.exists_unitriangular (L3317.isSylowTwoOf_inf h hTL)
    (by norm_num) hα₀s hα₀k
  have hθ : thetaOf (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
      thetaOf (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) (thetaOf_mono inf_le_right)
    rintro x ⟨hx, hx3⟩
    have hxL : x ∈ L := mem_of_orderOf_three hαs hαk h.maxM.1 h.LM h.qtke.2.2 (hCM hx)
      (hMN (hCM hx)) hx3
    exact Subgroup.subset_closure ⟨⟨hxL, hx⟩, hx3⟩
  have hOT : (CFSG.pCore 2 ↥L).map L.subtype ≤ T := by
    have h1 := EscapingLocal.pCoreOf_le_of_isSylowTwoOf (L3317.isSylowTwoOf_inf h hTL)
    rw [← A7.pCoreOf_eq_map_cfsgPCore]
    exact h1.trans inf_le_left
  have hTX : T ⊓ L ≤ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun t ht => ⟨ht.2, CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht.1⟩
  have hsup : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T =
      thetaOf (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T :=
    le_antisymm (sup_le (le_thetaOf_sup hαk hαU hOT inf_le_left hTX) le_sup_right)
      (sup_le_sup_right (thetaOf_le_self _) T)
  have hDR : D ≤ Subgroup.normalizer ((pCoreOf 2
      (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T)) : Set G) := by
    intro d hdD
    have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
    have hdZ : d ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      A4.normalizer_le_normalizer_omegaOneCenterOf T hdT
    have hdC : d ∈ Subgroup.normalizer
        (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) : Set G) :=
      mem_normalizer_centralizer hdZ
    have hdθ := mem_normalizer_thetaOf hdC
    rw [hθ] at hdθ
    rw [hsup]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (L3312.mem_normalizer_sup' hdθ hdT)
  exact Hyp331.not_D_le h (hDR.trans (hd G T M L D h ⟨e⟩ hmod))

end L3321

end CFSG.Quasithin.H13
