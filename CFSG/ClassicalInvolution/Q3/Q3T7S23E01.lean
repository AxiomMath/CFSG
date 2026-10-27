module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23A04
public import CFSG.ClassicalInvolution.Q3.Q3T7S23ECore

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

namespace T7Z

theorem twin_commutes (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hex : ExactMembers Ω) :
    Commutes K K' := by
  have d := Q3T8.Asc77.ExactD.TwinPair.of_twinSet hs.stand.hyp hs.stand.mem hs.hz hs.hK'
    hs.hne.symm
  have h := d.comm_le
  rw [oddCoreOf_eq_bot_of_exact hex hs.stand.mem, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem g_comm_e' (hd : Hyp23bData Ω K K' W z u e g) : g * e = e * g :=
  T7K.comm_e hd (T7K.g_mem_normalizer hd)

theorem conjSub_le_centralizer_e' (hd : Hyp23bData Ω K K' W z u e g) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({e} : Set G)) :
    conjSub g L ≤ Subgroup.centralizer ({e} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (g⁻¹ * x * g) * e = e * (g⁻¹ * x * g) := Subgroup.mem_centralizer_singleton_iff.mp
    (hL hx)
  have h2 := g_comm_e' hd
  calc x * e = g * ((g⁻¹ * x * g) * e) * g⁻¹ := by
        have : g * ((g⁻¹ * x * g) * e) * g⁻¹ = x * (g * e * g⁻¹) := by group
        rw [this, h2]; group
    _ = g * (e * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = e * x := by
        have : g * (e * (g⁻¹ * x * g)) * g⁻¹ = (g * e * g⁻¹) * x := by group
        rw [this, h2]; group

theorem t_ne_z (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    u * e ≠ z := by
  intro h
  apply Q3T8.Asc77.T7K.e_not_mem_sup hs hd
  have he : e = u * z := by
    calc e = u * (u * e) := by
          have := hd.hu2
          calc e = (u * u) * e := by rw [this, one_mul]
            _ = u * (u * e) := by group
      _ = u * z := by rw [h]
  rw [he]
  exact Subgroup.mul_mem _ hd.hu (Subgroup.mem_sup_left hs.hz.mem)

theorem not_commutes_of_involution (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) {L : Subgroup G}
    {t : G} (hLΩ : L ∈ Ω) (htL : IsUniqueInvolution L t) (htz : t ≠ z) :
    K ≠ L ∧ ¬ Commutes K L := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hne : K ≠ L := by
    rintro rfl
    exact htz (htL.eq hs.hz)
  refine ⟨hne, fun h => ?_⟩
  have hmem : L ∈ omegaNbr Ω K := MuTab.mem_omegaNbr_of_commutes hLΩ hne.symm h
  have hperp : L ∈ KPerp Ω K := Or.inr hmem
  rw [hs.perp] at hperp
  rcases hperp with rfl | rfl
  · exact hne rfl
  · exact htz (htL.eq hzK')

end T7Z

namespace B3C

theorem alphaOf_ze_eq_bot3 [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    alphaOf (Subgroup.closure ({e, z} : Set G)) = ⊥ := by
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have hze : z ≠ e := fun h => Q3T8.Asc77.T7K.e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left
      hs.hz.mem)
  have hA : IsElemAbelian2 (Subgroup.closure ({z, e} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hs.hz.sq hd.he2 hs.hz.ne_one hd.he1 hze
      (T7K.comm_e_of_mem_W hd hd.hzW)
  have hAB : Subgroup.closure ({z, e} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hzB
    · exact heB
  obtain ⟨-, halpha⟩ := Q3T8.Asc77.T7K.c23_5X_one_proved hs hd
  have hαA : alphaOf (Subgroup.closure ({z, e} : Set G)) = ⊥ := (halpha _ hAB hA).trans hα
  rwa [Set.pair_comm]

theorem exactMembers_of_twin_layer {K M : Subgroup G} {c : G} (hst : Q3T8.Asc77.AscStand Ω K)
    (hMΩ : M ∈ Ω) (hzM : IsUniqueInvolution M z)
    (hMtq : M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hc2 : c * c = 1)
    (hα : alphaOf (Subgroup.closure ({c, z} : Set G)) = ⊥)
    (hOc : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) = ⊥) {d : ℕ}
    {ε : Bool} (hY : Q3T8.Asc77.LayerOrthType Ω c d ε) : ExactMembers Ω := by
  classical
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  obtain ⟨z', hz'⟩ := hΩ.classical M hMΩ
  have hz'z : z' = z := by
    have hsq : z' * z' = 1 := by
      have h2 := pow_orderOf_eq_one z'
      rw [hz'.orderOf_eq_two] at h2
      simpa [sq] using h2
    rcases hzM.unique z' hz'.mem hsq with h | h
    · exfalso
      have h2 := hz'.orderOf_eq_two
      rw [h, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact h
  have hz : Q3T8.Generic.IsClassicalMember M z := hz'z ▸ hz'
  have hzA : z ∈ Subgroup.closure ({c, z} : Set G) := Subgroup.subset_closure (by simp)
  have hcA : c ∈ Subgroup.closure ({c, z} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm :=
    CFSG.ClassicalInvolution.Asc77.ExactD.commutator_oddCore_centralizer_le_alphaOf hzM.ne_one
      (Subgroup.closure ({c, z} : Set G)) hzA
  rw [hα] at hcomm
  have hOJ : ∀ n ∈ oddCoreOf M, n * c = c * n := by
    intro n hn
    have hn' : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
      CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hz.subnormal hn
    have h1 : ⁅n, c⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({z} : Set G)),
        Subgroup.closure ({c, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn' hcA
    have h2 : ⁅n, c⁆ = 1 := Subgroup.mem_bot.mp (hcomm h1)
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hOe := Q3T8.Asc77.T7Z.oddCore_exactCore_eq_bot hΩ hc2 hOc hY hMtq
  have hK3 : Q3.IsClassicalMember3 M z := hz.toQ3 (by norm_num)
  have hO0 : oddCoreOf M = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hOJ x hx
    have hxK : x ∈ Q3T8.Asc77.ExactLayer.exactCore c M :=
      ⟨CFSG.ClassicalInvolution.Balance.oddCoreIn_le M hx, hxc⟩
    have hx' : x ∈ Q3T8.Asc77.ExactLayer.exactCore c M ⊓
        CFSG.ClassicalInvolution.Balance.oddCoreIn M := ⟨hxK, hx⟩
    rw [← Q3NL.oddCoreIn_exactCore3 hK3 hc2' hMtq.2] at hx'
    have h2 : CFSG.ClassicalInvolution.Balance.oddCoreIn
        (Q3T8.Asc77.ExactLayer.exactCore c M) = ⊥ := by
      show (classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactCore c M)).map
        (Q3T8.Asc77.ExactLayer.exactCore c M).subtype = ⊥
      rw [hOe, Subgroup.map_bot]
    rw [h2] at hx'
    exact hx'
  have hO : classicalInvolutionOddCore ↥M = ⊥ := by
    have h3 : (classicalInvolutionOddCore ↥M).map M.subtype = ⊥ := hO0
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h3
  exact CFSG.ClassicalInvolution.Balance.exactMembers_of_oddCore_eq_bot
    ⟨K, hst.mem, fun L hL => by
      obtain ⟨g, hg⟩ := hst.trans L hL
      exact ⟨g, hg.symm⟩⟩ hMΩ hO

theorem eSideU3
    [IsSimpleGroup G]
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hOE : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥)
    (hE : Q3T8.Asc77.LayerOrthType Ω e 6 false) :
    ExactMembers Ω ∧
      (∃ W', UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W' K (conjSub g K)) ∧
      (∃ W', UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W' K (conjSub g K')) ∧
      Q3T8.Asc77.ExactLayer.exactLayer Ω e ≤ conjSub g K' ⊔ K ⊔ conjSub g K ∧
      K ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e ∧
      conjSub g K ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e ∧
      conjSub g K' ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e ∧
      Commutes (conjSub g K) (conjSub g K') := by
  classical
  have hst := hs.stand
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hKΩ hs.hz hR hRN
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hK'Ω hzK' hR' hR'N
  have hKtq : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω e :=
    Q3NL.mem_tqMembers3_of_le_centralizer hKΩ hKe
  have hex : ExactMembers Ω :=
    B3C.exactMembers_of_twin_layer hst hKΩ hs.hz hKtq hd.he2
      (B3C.alphaOf_ze_eq_bot3 hs hd hα) hOE hE
  have hJΩ : conjSub g K ∈ Ω := hst.hyp.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hst.hyp.conjInvariant g K' hK'Ω
  have hJe := Q3T8.Asc77.T7Z.conjSub_le_centralizer_e' hd hKe
  have hJ'e := Q3T8.Asc77.T7Z.conjSub_le_centralizer_e' hd hK'e
  have hKΦ : K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hKΩ hKe
  have hK'Φ : K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hK'Ω hK'e
  have hJΦ : conjSub g K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hJΩ hJe
  have hJ'Φ : conjSub g K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω e :=
    Q3NL.mem_exactFamily3_of_le_centralizer hJ'Ω hJ'e
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have htz := Q3T8.Asc77.T7Z.t_ne_z hs hd
  obtain ⟨hKJ, hKJc⟩ := Q3T8.Asc77.T7Z.not_commutes_of_involution hs hJΩ htJ htz
  obtain ⟨hKJ', hKJc'⟩ := Q3T8.Asc77.T7Z.not_commutes_of_involution hs hJ'Ω htJ' htz
  obtain ⟨P⟩ := Q3T8.Asc77.C22N.nonempty_psuLayer_of_layerOrth hOE hE
  have hLayer := Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω e
  have hKle : K ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := le_omegaGen hKΦ
  have hK'le : K' ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := le_omegaGen hK'Φ
  have hJle : conjSub g K ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := le_omegaGen hJΦ
  have hJ'le : conjSub g K' ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) :=
    le_omegaGen hJ'Φ
  have heΦ : e ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := by
    have hue : u ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := sup_le hKle hK'le hd.hu
    have ht : u * e ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e) := hJle htJ.mem
    have key : e = u * (u * e) := by
      have := hd.hu2
      calc e = (u * u) * e := by rw [this, one_mul]
        _ = u * (u * e) := by group
    have h := Subgroup.mul_mem _ hue ht
    rwa [← key] at h
  have hecen : ∀ y ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω e), e * y = y * e := by
    intro y hy
    have hy' : y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω e := hLayer ▸ hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω e hy')).symm
  have htab : u * e = a * b * e := by rw [hu]
  have hcomm : Commutes K K' := Q3T8.Asc77.T7Z.twin_commutes hs hex
  have haK : a ∈ K := hR.1 haR
  have hbK' : b ∈ K' := hR'.1 hbR'
  obtain ⟨hpJ, hpJ', hgen⟩ := Q3T7S23.eSide_core3 P hKΦ hK'Φ hJΦ hJ'Φ hs.hz htJ htJ' haK hbK' haa
    hcomm (hcomm.conjSub g) heΦ hecen htab hKJ hKJc hKJ' hKJc'
  refine ⟨hex, hpJ, hpJ', hLayer.le.trans hgen.ge, hKle.trans hLayer.ge,
    hJle.trans hLayer.ge, hJ'le.trans hLayer.ge, hcomm.conjSub g⟩

end B3C

end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
