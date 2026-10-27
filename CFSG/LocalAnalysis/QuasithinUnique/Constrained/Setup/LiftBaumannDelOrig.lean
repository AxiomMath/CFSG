module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftVleS

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open scoped Pointwise

section Main

variable {G : Type} [Group G] [Finite G]

theorem even_SL2_deleted_baumann
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc)
    (hdel : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V) :
    DeletedBaumannCore R V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata := deleted_original_data hS hLc hdel
  have hred := hS.reduced
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have := hVn
  have := hVe.1
  obtain ⟨-, hCR, -, -, hVR⟩ := even_SL2_setting_basic hS
  obtain ⟨l, hlL, hlgen, hlcodim⟩ := hdata.l_gen
  obtain ⟨hPS, hEsplit, hSyl⟩ := baumann_apply hS hLc hlL hlgen hlcodim
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set J := thompsonJ R with hJ
  have hJC : ∀ j ∈ J, ∀ c ∈ V ⊓ Subgroup.centralizer (L : Set G), j * c = c * j := by
    intro j hj c hc
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hdata.J_C hj
    exact (Subgroup.mem_centralizer_iff.1 h1 c hc).symm
  have hCA : V ⊓ Subgroup.centralizer (L : Set G) ≤ V ⊓ Subgroup.centralizer (J : Set G) :=
    fun c hc => ⟨hc.1, Subgroup.mem_centralizer_iff.2 fun j hj => hJC j hj c hc⟩
  have hAE : V ⊓ Subgroup.centralizer (J : Set G) ≤ omegaOneCenterOf J := fun v hv =>
    mem_omegaOneCenter_of_centralizes hVR hVe hv.1 fun j hj =>
      Subgroup.mem_centralizer_iff.1 hv.2 j hj
  have hQ : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.centralizer (V : Set G)) := by
    refine isSylowTwoOf_of_isSylowOf ?_
    exact (isSylowOf_two_of hS.sylow).inf_of_le_normalizer le_top
      (by rw [Subgroup.normalizer_eq_top])
  have hsylowC := (hSyl hQ).1
  have hnormLS : (L ⊔ baum R).Normal := normal_L_sup_baum hS
  have hVS : V ≤ baum R :=
    V_le_baum_of_data hVR
      (fun a ha b hb => congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      hEsplit hAE hdata.V_span
  have hCSeq : baum R ⊓ Subgroup.centralizer (V : Set G) =
      pCoreOf 2 (⊤ : Subgroup G) ⊓ (L ⊔ baum R) := by
    apply le_antisymm
    · intro x hx
      refine ⟨?_, Subgroup.mem_sup_right hx.1⟩
      rw [← hCR]
      exact ⟨(inf_le_left : baum R ≤ R) hx.1, hx.2⟩
    · intro x hx
      have hxQ : x ∈ R ⊓ Subgroup.centralizer (V : Set G) := by rw [hCR]; exact hx.1
      have hU : omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) ≤
          Subgroup.centralizer ((L ⊔ baum R : Subgroup G) : Set G) := by
        intro u hu
        have hLle : L ⊔ baum R ≤ Subgroup.centralizer ({u} : Set G) := by
          refine sup_le (fun k hk => ?_) (fun s hs => ?_)
          · rw [Subgroup.mem_centralizer_iff]
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact (Subgroup.mem_centralizer_iff.1 hu.2 k hk).symm
          · rw [Subgroup.mem_centralizer_iff]
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact Subgroup.mem_centralizer_iff.1 hs.2 u hu.1
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.1 (hLle hz) u (Set.mem_singleton u)).symm
      have hxE : x ∈ Subgroup.centralizer (omegaOneCenterOf J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        rw [hEsplit] at he
        have hesplit : omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) ⊔
            V ⊓ Subgroup.centralizer (J : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
          refine sup_le (fun u hu => ?_) (fun a ha => ?_)
          · rw [Subgroup.mem_centralizer_iff]
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact Subgroup.mem_centralizer_iff.1 (hU hu) x hx.2
          · rw [Subgroup.mem_centralizer_iff]
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact (Subgroup.mem_centralizer_iff.1 hxQ.2 a ha.1).symm
        exact (Subgroup.mem_centralizer_iff.1 (hesplit he) x (Set.mem_singleton x)).symm
      exact ⟨⟨hxQ.1, hxE⟩, hxQ.2⟩
  have hCU : V ⊓ Subgroup.centralizer (L : Set G) ≤
      omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) :=
    fun c hc => ⟨hAE (hCA hc), hc.2⟩
  have hVle : V ≤ ⁅V, L⁆ ⊔ (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) := by
    calc V = ⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) := hdata.V_split
      _ ≤ ⁅V, L⁆ ⊔ (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) :=
        sup_le_sup_left hCU _
  have hcommV : ⁅V, L⁆ ≤ V := Subgroup.commutator_le.2 fun v hv l' _ => by
    have h1 : (l' : G) * v⁻¹ * l'⁻¹ ∈ V := hVn.conj_mem _ (V.inv_mem hv) l'
    have h2 := V.mul_mem hv h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hClosure : (⨆ l' ∈ L, cj (omegaOneCenterOf J) l') =
      ⁅V, L⁆ ⊔ (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) := by
    apply le_antisymm
    · refine iSup₂_le fun l' hl' => ?_
      have hcjE : cj (omegaOneCenterOf J) l' =
          cj (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) l' ⊔
            cj (V ⊓ Subgroup.centralizer (J : Set G)) l' := by
        rw [← cj_sup, ← hEsplit]
      rw [hcjE]
      refine sup_le ?_ ?_
      · intro y hy
        have hy' : (l' : G) * y * (l' : G)⁻¹ ∈
            omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) := mem_cj.1 hy
        have h3 := Subgroup.mem_centralizer_iff.1 hy'.2 l' hl'
        have h4 : (l' : G) * y * (l' : G)⁻¹ = y := by
          have h5 : (l' : G) * ((l' : G) * y * (l' : G)⁻¹) =
              (l' : G) * y * (l' : G)⁻¹ * l' := h3
          calc (l' : G) * y * (l' : G)⁻¹
              = (l' : G)⁻¹ * ((l' : G) * ((l' : G) * y * (l' : G)⁻¹)) := by group
            _ = (l' : G)⁻¹ * ((l' : G) * y * (l' : G)⁻¹ * l') := by rw [h5]
            _ = y := by group
        have h6 : y ∈ omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) := by
          have := hy'
          rwa [h4] at this
        exact Subgroup.mem_sup_right h6
      · intro y hy
        have hy' : (l' : G) * y * (l' : G)⁻¹ ∈ V ⊓ Subgroup.centralizer (J : Set G) :=
          mem_cj.1 hy
        have hyV : (l' : G) * y * (l' : G)⁻¹ ∈ V := hy'.1
        have h2 := hVn.conj_mem _ hyV (l' : G)⁻¹
        have h6 : y ∈ V := by simpa [mul_assoc] using h2
        exact hVle h6
    · refine sup_le ?_ ?_
      · calc ⁅V, L⁆ ≤ V := hcommV
          _ = ⨆ l' ∈ L, cj (V ⊓ Subgroup.centralizer (J : Set G)) l' := hdata.V_span.symm
          _ ≤ ⨆ l' ∈ L, cj (omegaOneCenterOf J) l' :=
            iSup₂_mono fun l' _ => Subgroup.map_mono hAE
      · refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
        rw [cj_one]
        exact inf_le_left
  exact ⟨hdata.baum_eq, hPS, hnormLS, hVS, hEsplit, hAE, hdata.V_span, hClosure, hdata.J_C,
    hCSeq, hsylowC⟩

theorem delBaumannProp
    : DelBaumannProp := by
  intro G _ _ R M V n F _ r Lc ctx
  exact even_SL2_deleted_baumann ctx.setting ctx.comps ctx.deleted

end Main

end CFSG.QuasithinUnique.Setup.Lift
