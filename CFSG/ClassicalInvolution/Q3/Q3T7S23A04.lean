module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2214
public import CFSG.ClassicalInvolution.Q3.Q3T7S23A03

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

theorem c23_GammaU_proved : Q3T8.Asc77.C23_GammaU :=
  Q3T8.Asc77.c23_GammaU_of_e4 Q3T8.Asc77.e4TwinGen3_proved
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace T7Y
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7Y
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}
theorem sup_centralizer_eq_top
    [IsSimpleGroup G] (hE : Q3T7E.ThmEWithSylow3) (htr :
    Q3T8.Asc77.C23_2_trans)
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ := by
  have hstd : StdCent Ω K
      (Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G)) z :=
    hs.stdCent_of_twin le_sup_right fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨c, hcz, hcu⟩ := Q3T8.Asc77.c23_2_fuse G Ω K K' z hs W hd.hW hd.hzW u hd.hu hd.huW
          hd.hu1
        hd.huz hd.hu2 L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      intro a ha
      have ha' : a * (x * y) = (x * y) * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      have hu' : u = c⁻¹ * (x * y) * c := by rw [← hcu]; group
      have hcomm : (c⁻¹ * a * c) * u = u * (c⁻¹ * a * c) := by
        have e1 : c⁻¹ * (a * (x * y)) * c = c⁻¹ * ((x * y) * a) * c := by rw [ha']
        calc (c⁻¹ * a * c) * u = c⁻¹ * (a * (x * y)) * c := by rw [hu']; group
          _ = c⁻¹ * ((x * y) * a) * c := e1
          _ = u * (c⁻¹ * a * c) := by rw [hu']; group
      have hcH : c ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_right hcz
      have ha'H : c⁻¹ * a * c ∈
          Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
      have : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH ha'H) (Subgroup.inv_mem _ hcH)
  exact Q3T8.Asc77.thmE_apply hE hs.stand hs.hz hs.hK' hs.hne hstd
    (htr G Ω K K' z hs W hd.hW hd.hzW u hd.hu hd.huW hd.hu1 hd.huz hd.hu2)

theorem alphaOf_eq_bot [IsSimpleGroup G]
    (hG : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤)
    (hΓu : Subgroup.centralizer ({u} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)))
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ := by
  obtain ⟨hodd, halpha⟩ := Q3T8.Asc77.T7K.c23_5X_one_proved hs hd
  have hΓz := Q3T8.Asc77.T7K.centralizer_z_le_gamma2 hs hd
  have hN : Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hG]
    exact sup_le (hΓu.trans (gamma2_le_normalizer_alphaOf halpha _))
      (hΓz.trans (gamma2_le_normalizer_alphaOf halpha _))
  exact T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard hs.hz)

theorem le_centralizer_e [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    {L : Subgroup G} (hLΩ : L ∈ Ω) (hzL : IsUniqueInvolution L z) {R : Subgroup G}
    (hR : IsSylow2In R L) (hRN : R ≤ Subgroup.normalizer (W : Set G)) :
    L ≤ Subgroup.centralizer ({e} : Set G) := by
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hcl : Q3T8.Generic.IsClassicalMember L z := Q3T8.Asc77.isClassicalMember_of_twin hΩ hLΩ hzL
  have he2 : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one hd.he2 hd.he1
  have hetq : e ∈ trivialOnQuot L :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ he2 hLΩ).mpr
      ⟨R, hR, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e hd (hRN hr))⟩
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
  intro ℓ hℓ
  obtain ⟨i, hi, n, hn, rfl⟩ := Q3T8.Asc77.ExactLayer.exactCore_cover hcl he2 hetq ℓ hℓ
  refine Subgroup.mul_mem _ (Q3T8.Asc77.ExactLayer.exactCore_le_centralizer e L hi) ?_
  have hnO : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
    oddCoreIn_le_of_isSubnormal (Q3T8.Asc77.T7A.isSubnormal_centralizer hΩ hLΩ hzL) hn
  have hnz : n * e = e * n :=
    commute_of_alphaOf_eq_bot (Subgroup.subset_closure (by simp)) hs.hz.ne_one hαA hnO
      (Subgroup.subset_closure (by simp))
  exact Subgroup.mem_centralizer_singleton_iff.mpr hnz

theorem exists_mul_centralizer_u [IsSimpleGroup G] (htcf : Q3T8.Asc77.TwinCentralFact3)
    (hgen : Q3T8.Asc77.E4TwinGen3) (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K'
        W z u e g)
    {h : G} (hh : h ∈ Subgroup.centralizer ({u} : Set G)) :
    ∃ y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u, ∃ c ∈ Subgroup.centralizer ({u} : Set G) ⊓
      Subgroup.centralizer ({u * e} : Set G), h = y * c := by
  classical
  have hst := hs.stand
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := hst.below
  obtain ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, hv'z, hS, hlt, T, hconj⟩ :=
      Q3T8.Asc77.T7L.layer_u_frame hs hd
  obtain ⟨-, hCI⟩ := Q3T8.Asc77.T7L.twinSection_gen_conj htcf hgen hBelow hlt hS T
  have hBel := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ huB heB
  have sq : ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G), x * x = 1 := fun x hx => by
    have := hBel.2 x hx
    rwa [pow_two] at this
  obtain ⟨⟨ht1, htu⟩, -⟩ := Q3T8.Asc77.T7L.B_ne hs hd
  have hYH : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({u} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
  obtain ⟨B₀, hB₀, hmem, huniq⟩ := hconj h hh
  obtain ⟨yb, hyb⟩ := hCI B₀ hB₀ _ huniq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hcongr := T7L.mem_oddCore_of_mk_conj htY hmem y hyb
  exact T7L.eq_mul_of_conj_mod hYH (oddCoreIn_le _) (oddCoreOf_odd_natCard _)
    (fun y hy => normalizer_oddCoreIn _ hy) htY (sq _ htB) ht1 hh y.2 hcongr
end T7Y
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace T7Y
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7Y
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z u e g : G}
section Basic
omit [IsSimpleGroup G] in

theorem exists_noncomm
    (hst : Q3T8.Asc77.AscStand Ω K) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hst.hyp.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hst.mem hV)).exists_not_commute
  exact ⟨x, y, hxy⟩
end Basic

theorem not_mem_zStar (htcf : Q3T8.Asc77.TwinCentralFact3) (hgen : Q3T8.Asc77.E4TwinGen3)
    (hG : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤)
    (hΓu : Subgroup.centralizer ({u} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)))
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    u * e ∉ zStarOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) := by
  intro htZ
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hα := Q3T8.Asc77.T7Y.alphaOf_eq_bot hG hΓu hs hd
  obtain ⟨-, halpha⟩ := Q3T8.Asc77.T7K.c23_5X_one_proved hs hd
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have hBel := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ huB heB
  have sq : ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G), x * x = 1 := fun x hx => by
    have := hBel.2 x hx
    rwa [pow_two] at this
  obtain ⟨⟨ht1, htu⟩, -⟩ := Q3T8.Asc77.T7L.B_ne hs hd
  have ht2 : (u * e) * (u * e) = 1 := sq _ htB
  have hcomm := T7A.commutes_closure (Q3T8.Asc77.T7K.comm_gen hs hd)
  have hut : u * (u * e) = (u * e) * u := hcomm u huB (u * e) htB
  have hA : IsElemAbelian2 (Subgroup.closure ({u, u * e} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hd.hu2 ht2 hd.hu1 ht1 (Ne.symm htu) hut
  have hAB : Subgroup.closure ({u, u * e} : Set G) ≤
      Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huB
    · exact htB
  have hαA : alphaOf (Subgroup.closure ({u, u * e} : Set G)) = ⊥ := (halpha _ hAB hA).trans hα

  have hBN : ∀ b ∈ Subgroup.centralizer ({u} : Set G),
      b ∈ Subgroup.normalizer (oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) : Set G) := fun b
          hb =>
    T7L.mem_normalizer_oddCoreOf (Q3T8.Asc77.T7Y.mem_normalizer_exactLayer hΩ.conjInvariant hb)
  have hOY : oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω u) ≤ oddCoreOf (Subgroup.centralizer
      ({u} : Set G)) :=
    le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans
        (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u)) hBN
      (oddCoreOf_odd_natCard _)

  obtain ⟨x₀, hx₀, hx₀t⟩ := Subgroup.mem_map.mp htZ
  have htY : u * e ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u := hx₀t ▸ x₀.2
  have hYt : ∀ y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u, y * (u * e) = (u * e) * y := by
    intro y hy
    set N₀ := classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) with hN₀
    have hcen := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hx₀)
      (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)
    have hx₀' : x₀ = ⟨u * e, htY⟩ := Subtype.ext hx₀t
    rw [hx₀'] at hcen
    have hmk : QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ *
        QuotientGroup.mk' N₀ ⟨u * e, htY⟩ *
        (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)⁻¹ =
        QuotientGroup.mk' N₀ ⟨u * e, htY⟩ := by
      rw [hcen, mul_inv_cancel_right]
    have ho := T7L.mem_oddCore_of_mk_conj htY htY ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ hmk
    simp only [inv_inv] at ho
    set o : G := (u * e)⁻¹ * (y * (u * e) * y⁻¹) with hodef
    have hoN : o ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G)) := hOY ho
    have hot : o * (u * e) = (u * e) * o :=
      commute_of_alphaOf_eq_bot (Subgroup.subset_closure (by simp)) hd.hu1 hαA hoN
        (Subgroup.subset_closure (by simp))
    have hyt : y * (u * e) * y⁻¹ = (u * e) * o := by simp only [hodef]; group
    have hsq : ((u * e) * o) * ((u * e) * o) = 1 := by
      rw [← hyt]
      calc (y * (u * e) * y⁻¹) * (y * (u * e) * y⁻¹) = y * ((u * e) * (u * e)) * y⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hoo : o * o = 1 := by
      have h1 : ((u * e) * o) * ((u * e) * o) = o * o := by
        calc ((u * e) * o) * ((u * e) * o) = (u * e) * (o * (u * e)) * o := by group
          _ = (u * e) * ((u * e) * o) * o := by rw [hot]
          _ = ((u * e) * (u * e)) * (o * o) := by group
          _ = o * o := by rw [ht2, one_mul]
      exact h1.symm.trans hsq
    have ho1 : o = 1 := eq_one_of_sq_eq_one_of_mem_odd (oddCoreOf_odd_natCard _) ho hoo
    rw [ho1, mul_one] at hyt
    exact mul_inv_eq_iff_eq_mul.mp hyt

  have hCue : ∀ h ∈ Subgroup.centralizer ({u} : Set G), h * e = e * h := by
    intro h hh
    obtain ⟨y, hy, c, hc, rfl⟩ := Q3T8.Asc77.T7Y.exists_mul_centralizer_u htcf hgen hs hd hh
    have hct : c * (u * e) = (u * e) * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hyt := hYt y hy
    have hht : (y * c) * (u * e) = (u * e) * (y * c) := by
      calc (y * c) * (u * e) = y * (c * (u * e)) := mul_assoc _ _ _
        _ = y * ((u * e) * c) := by rw [hct]
        _ = (y * (u * e)) * c := (mul_assoc _ _ _).symm
        _ = ((u * e) * y) * c := by rw [hyt]
        _ = (u * e) * (y * c) := mul_assoc _ _ _
    have hhu : (y * c) * u = u * (y * c) := Subgroup.mem_centralizer_singleton_iff.mp hh
    exact comm_e_of_comm_u_ue hd.hu2 hhu hht

  obtain ⟨R, R', hR, hR', -, hRN, hR'N⟩ := Q3T8.Asc77.T7K.exists_sylow_D hs hd
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hKe := Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hst.mem hs.hz hR hRN
  have hK'e := Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hs.hK'.1 hzK' hR' hR'N
  have hCze : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c * e = e * c := by
    intro c hc
    obtain ⟨r, hr, c₀, hc₀, hcm, rfl⟩ :=
      Q3T8.Asc77.T7K.centralizer_eq_sup_mul hs hd.hu hd.hu1 hd.huz hd.hu2 hc
    have hre : r * e = e * r := Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hKe hK'e) hr)
    have hc₀e : c₀ * e = e * c₀ := hCue c₀ (Subgroup.mem_centralizer_singleton_iff.mpr hcm)
    calc (r * c₀) * e = r * (c₀ * e) := mul_assoc _ _ _
      _ = r * (e * c₀) := by rw [hc₀e]
      _ = (r * e) * c₀ := (mul_assoc _ _ _).symm
      _ = (e * r) * c₀ := by rw [hre]
      _ = e * (r * c₀) := mul_assoc _ _ _
  refine hd.he1 (T7B.eq_one_of_central (Q3T8.Asc77.T7Y.exists_noncomm hst) (fun x => ?_))
  have hle : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ({e} : Set G) :=
    sup_le (fun h hh => Subgroup.mem_centralizer_singleton_iff.mpr (hCue h hh))
      (fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr (hCze c hc))
  have hx : x ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
    hG ▸ Subgroup.mem_top x
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem sup_layers_eq_top (htcf : Q3T8.Asc77.TwinCentralFact3) (hgen : Q3T8.Asc77.E4TwinGen3)
    (hG : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤)
    (hΓu : Subgroup.centralizer ({u} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)))
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤ := by
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hα := Q3T8.Asc77.T7Y.alphaOf_eq_bot hG hΓu hs hd
  obtain ⟨R, R', hR, hR', -, hRN, hR'N⟩ := Q3T8.Asc77.T7K.exists_sylow_D hs hd
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'

  have hLE : ∀ {L : Subgroup G} {R₀ : Subgroup G}, L ∈ Ω → IsUniqueInvolution L z →
      IsSylow2In R₀ L → R₀ ≤ Subgroup.normalizer (W : Set G) → L ≤ Q3T8.Asc77.ExactLayer.exactLayer
          Ω e := by
    intro L R₀ hLΩ hzL hR₀ hR₀N
    have hLe : L ≤ Subgroup.centralizer ({e} : Set G) :=
      Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hLΩ hzL hR₀ hR₀N
    have hLt : L ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω e := ⟨hLΩ, mem_trivialOnQuot_of_le_centralizer
        hLe⟩
    have h1 := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hLt
    rwa [(Q3T8.Asc77.ExactLayer.exactCore_def e L).trans (inf_eq_left.mpr hLe)] at h1
  have hKE : K ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e := hLE hst.mem hs.hz hR hRN
  have hK'E : K' ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω e := hLE hs.hK'.1 hzK' hR' hR'N
  set E := Q3T8.Asc77.ExactLayer.exactLayer Ω e with hEdef
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hYdef

  have hCu : ∀ h ∈ Subgroup.centralizer ({u} : Set G),
      h ∈ Subgroup.normalizer ((E ⊔ Y : Subgroup G) : Set G) := by
    intro h hh
    obtain ⟨y, hy, c, hc, rfl⟩ := Q3T8.Asc77.T7Y.exists_mul_centralizer_u htcf hgen hs hd hh
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer ((le_sup_right : Y ≤ E ⊔ Y) hy)) ?_
    have hce : c ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_e_of_comm_u_ue hd.hu2 (Subgroup.mem_centralizer_singleton_iff.mp hc.1)
          (Subgroup.mem_centralizer_singleton_iff.mp hc.2))
    exact Subgroup.inf_normalizer_le_normalizer_sup E Y
      ⟨Q3T8.Asc77.T7Y.mem_normalizer_exactLayer hΩ.conjInvariant hce,
        Q3T8.Asc77.T7Y.mem_normalizer_exactLayer hΩ.conjInvariant hc.1⟩

  have hCz : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      c ∈ Subgroup.normalizer ((E ⊔ Y : Subgroup G) : Set G) := by
    intro c hc
    obtain ⟨r, hr, c₀, hc₀, hcm, rfl⟩ :=
      Q3T8.Asc77.T7K.centralizer_eq_sup_mul hs hd.hu hd.hu1 hd.huz hd.hu2 hc
    refine Subgroup.mul_mem _ ?_ (hCu c₀ (Subgroup.mem_centralizer_singleton_iff.mpr hcm))
    exact Subgroup.le_normalizer ((le_sup_left : E ≤ E ⊔ Y) (sup_le hKE hK'E hr))
  have hN : Subgroup.normalizer ((E ⊔ Y : Subgroup G) : Set G) = ⊤ := by
    rw [eq_top_iff, ← hG]
    exact sup_le hCu hCz
  have hnormal : (E ⊔ Y).Normal := Subgroup.normalizer_eq_top_iff.mp hN
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exfalso
    have hzE : z ∈ E ⊔ Y := (le_sup_left : E ≤ E ⊔ Y) (hKE hs.hz.mem)
    rw [h] at hzE
    exact hs.hz.ne_one (Subgroup.mem_bot.mp hzE)
  · exact h
end T7Y
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution

theorem c23_9_noZX_of (hE : Q3T7E.ThmEWithSylow3) : Q3T8.Asc77.C23_9_noZX := by
  intro G _ _ _ Ω K K' W z u e g hs hd _
  exact Q3T8.Asc77.T7Y.not_mem_zStar Q3T8.Asc77.twinCentralFact3_proved Q3T8.Asc77.e4TwinGen3_proved
    (Q3T8.Asc77.T7Y.sup_centralizer_eq_top hE (Q3T8.Asc77.c23_2_trans_proved) hs hd)
    (Q3T8.Asc77.c23_GammaU_proved G Ω K K' W z u e g hs hd) hs hd

theorem c23_9_genX_of (hE : Q3T7E.ThmEWithSylow3) : Q3T8.Asc77.C23_9_genX := by
  intro G _ _ _ Ω K K' W z u e g hs hd _ _
  exact Q3T8.Asc77.T7Y.sup_layers_eq_top Q3T8.Asc77.twinCentralFact3_proved
      Q3T8.Asc77.e4TwinGen3_proved
    (Q3T8.Asc77.T7Y.sup_centralizer_eq_top hE (Q3T8.Asc77.c23_2_trans_proved) hs hd)
    (Q3T8.Asc77.c23_GammaU_proved G Ω K K' W z u e g hs hd) hs hd

theorem c23_9_noZX_proved [Fact Q3T7E.ThmEWithSylow3] : Q3T8.Asc77.C23_9_noZX :=
  Q3T8.Asc77.c23_9_noZX_of (Fact.out : Q3T7E.ThmEWithSylow3)

theorem c23_9_genX_proved [Fact Q3T7E.ThmEWithSylow3] : Q3T8.Asc77.C23_9_genX :=
  Q3T8.Asc77.c23_9_genX_of (Fact.out : Q3T7E.ThmEWithSylow3)
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
