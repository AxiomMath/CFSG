module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf4Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf10Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf28O2Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf4Layer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf8Class
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Generic

theorem oddCoreIn_le_of_inO2_gen {G : Type} [Group G] [Finite G] {z u : G}
    (hz2 : IsPGroup 2 (Subgroup.zpowers z)) (hzu : z * u = u * z) (hB : InO2C z u)
    (N : Subgroup G) (hNH : N ≤ Subgroup.centralizer ({u} : Set G))
    (hNz : N ≤ Subgroup.centralizer ({z} : Set G))
    (hnorm : ∀ h ∈ Subgroup.centralizer ({u} : Set G), h ∈ Subgroup.centralizer ({z} : Set G) →
      ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) :
    N ≤ oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) with hH
  have hNH : N ≤ H := hNH
  have hzH : z ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hzu
  set zH : ↥H := ⟨z, hzH⟩ with hzHdef
  obtain ⟨P, hPH, hPn, hP2, hzP⟩ := hB
  set O : Subgroup ↥H := classicalInvolutionOddCore ↥H with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hOnd : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hOq : classicalInvolutionOddCore (↥H ⧸ O) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥H
  set Pb : Subgroup (↥H ⧸ O) := (P.subgroupOf H).map π with hPb
  have hPbn : Pb.Normal := hPn.map π (QuotientGroup.mk'_surjective O)
  have hPb2 : IsPGroup 2 Pb :=
    (hP2.comap_subtype).of_surjective (π.subgroupMap (P.subgroupOf H)) (π.subgroupMap_surjective _)
  have hzPb : π zH ∈ Pb := ⟨zH, Subgroup.mem_subgroupOf.mpr hzP, rfl⟩
  have h35 := oddCoreIn_centralizer_eq_bot_of_mem_normal hOq hPbn hPb2 hzPb
  have hQ : IsPGroup 2 (Subgroup.zpowers zH) := by
    refine hz2.of_injective
      ((H.subtype.comp (Subgroup.zpowers zH).subtype).codRestrict (Subgroup.zpowers z) ?_) ?_
    · rintro ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hcent := GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 2) (N := O) hOnd hQ
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at hcent
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  set Nb : Subgroup (↥H ⧸ O) := N'.map π with hNb
  have hNbC : Nb ≤ Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)) := by
    rintro _ ⟨n', hn', rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have hc : (n' : G) * z = z * n' := Subgroup.mem_centralizer_singleton_iff.mp (hNz hn)
    have : n' * zH = zH * n' := Subtype.ext hc
    rw [← map_mul, ← map_mul, this]
  have hfwd : ∀ g ∈ Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)), ∀ x ∈ Nb, g * x * g⁻¹ ∈ Nb := by
    intro g hg x hx
    rw [hcent] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨n', hn', rfl⟩ := hx
    have hhC : (h : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hh))
    have hn : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have h1 : (h : G) * n' * (h : G)⁻¹ ∈ N := hnorm h h.2 hhC n' hn
    refine ⟨h * n' * h⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hNbN : Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)) ≤ Subgroup.normalizer (Nb : Set (↥H ⧸ O)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hfwd g hg x hx, fun hx => ?_⟩
    have := hfwd g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    simpa [mul_assoc] using this
  have hN'odd : Odd (Nat.card N') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hodd
  have hNbodd : Odd (Nat.card Nb) :=
    Odd.of_dvd_nat hN'odd (CFSG.card_dvd_of_surjective (π.subgroupMap N') (π.subgroupMap_surjective _))
  have hNbO := le_oddCoreIn_of_normalizes hNbC hNbN hNbodd
  rw [h35, le_bot_iff] at hNbO
  intro n hn
  have hn' : (⟨n, hNH hn⟩ : ↥H) ∈ N' := Subgroup.mem_subgroupOf.mpr hn
  have h1 : π ⟨n, hNH hn⟩ ∈ Nb := ⟨_, hn', rfl⟩
  rw [hNbO, Subgroup.mem_bot] at h1
  exact ⟨⟨n, hNH hn⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩



end Generic

section Basic

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_eq_bot_of_isPGroup' {K : Subgroup G} (hK : IsPGroup 2 ↥K) : oddCoreIn K = ⊥ := by
  have h1 : IsPGroup 2 ↥(oddCoreIn K) := hK.to_le (oddCoreIn_le K)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp h1)
  have hodd := odd_card_oddCoreIn K
  rw [hm] at hodd
  have hm0 : m = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hm, hm0]; simp)

theorem commute_of_trivialOnQuot {K : Subgroup G} (hK : IsPGroup 2 ↥K) {a : G}
    (ha : a ∈ trivialOnQuot K) {x : G} (hx : x ∈ K) : a * x = x * a := by
  have h := ha.2 x hx
  rw [oddCoreIn_eq_bot_of_isPGroup' hK, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

end Basic

section Odd



section Lifts

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem inO2C_u_t (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) : InO2C (u₁ * u₂) t := by
  have hΩ := d.hyp
  refine ⟨TwinSecXg.twinJoin (CoreAssembly.conjClass (tightCore R)) K,
    TwinSecXg.twinJoin_le_centralizer d.hz, ?_, TwinSecXg.twinJoin_isPGroup hΩ h2g d.hz, ?_⟩
  · refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact TwinSecXg.twinJoin_normalized hΩ d.hz (g : Y) g.2 (x : Y) hx
  · exact Subgroup.mul_mem _ (TwinSecXg.le_twinJoin ⟨d.mem, t, d.hz, d.hz⟩ d.hu₁.1)
      (TwinSecXg.le_twinJoin d.hK' d.hu₂.1)

theorem t_mem_cu (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃) :
    t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  symm
  calc u₁ * u₂ * t = u₁ * (u₂ * t) := by group
    _ = u₁ * (t * u₂) := by rw [← d.comm_z₂]
    _ = (u₁ * t) * u₂ := by group
    _ = (t * u₁) * u₂ := by rw [← d.comm_z₁]
    _ = t * (u₁ * u₂) := by group

theorem oddCoreIn_cu_eq_bot (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({u₁ * u₂} : Set Y)) = ⊥ := by
  have hut : (u₁ * u₂) * t = t * (u₁ * u₂) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (t_mem_cu d)).symm
  have hcomm : oddCoreIn (Subgroup.centralizer ({u₁ * u₂} : Set Y)) ≤
      Subgroup.centralizer ({t} : Set Y) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact TwinDisc.oddCore_comm_of_alpha hα (Subgroup.subset_closure (by simp)) d.mul_ne_one
      (Subgroup.subset_closure (by simp)) hn
  have h := oddCoreIn_le_of_inO2_gen
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12) hut
    (inO2C_u_t d h2g) (oddCoreIn (Subgroup.centralizer ({u₁ * u₂} : Set Y))) hcomm
    (oddCoreIn_le _) (fun h _ hh' n hn => conj_mem_oddCoreIn hh' hn) (odd_card_oddCoreIn _)
  rw [TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore hodd] at h
  exact le_bot_iff.mp h

theorem oddCoreIn_ctcu_eq_bot (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y)) = ⊥ := by
  have hut : (u₁ * u₂) * t = t * (u₁ * u₂) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (t_mem_cu d)).symm
  have h := oddCoreIn_le_of_inO2_gen
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12) hut
    (inO2C_u_t d h2g)
    (oddCoreIn (Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y)))
    ((oddCoreIn_le _).trans inf_le_left) ((oddCoreIn_le _).trans inf_le_right)
    (fun h hh hh' n hn => conj_mem_oddCoreIn (Subgroup.mem_inf.mpr ⟨hh, hh'⟩) hn)
    (odd_card_oddCoreIn _)
  rw [TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore hodd] at h
  exact le_bot_iff.mp h

set_option maxHeartbeats 1600000 in
theorem section_lifts (hPb : TL4.TightBelowRPlus 3 n) (hP : PerpHypS n Y R S t)
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hK₄ : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K')
    (h43 : K₄ ≠ K₃) (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hno : SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :
    ∃ M M' : Subgroup Y,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({u₁ * u₂} : Set Y)) M t ∧
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({u₁ * u₂} : Set Y)) M' t ∧
      K₃ ≤ M ∧ K₄ ≤ M' ∧ (∀ a ∈ M, ∀ b ∈ M', a * b = b * a) ∧
      oddCoreIn M = ⊥ ∧ oddCoreIn M' = ⊥ := by
  have hΩ := d.hyp
  have hcc : (u₁ * u₂) * (u₁ * u₂) = 1 := d.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet d.hz hK₄
  have hmem := tq_of_hyp22G d
  have hmem4 : K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    refine ⟨hK₄.1, ?_⟩
    have t14 : u₁ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.mem hK₄.1 h41.symm d.hz hz4 d.hu₁.1
    have t24 : u₂ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h42.symm d.hzK' hz4 d.hu₂.1
    exact (trivialOnQuot K₄).mul_mem t14 t24
  have hS := layer_q8Section hP d.sq_12
  have hlt := card_layer_lt hP d.mul_ne_one
  have hlf := And.intro (secMemberLifted_of_noExit hPb hlt hS hno hmem)
    (secMemberLifted_of_noExit hPb hlt hS hno hmem4)
  have htc := t_mem_cu d
  have hu₂c : u₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * u₂ = (u₂ * u₁) * u₂ := by rw [d.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have hcm : ∀ {J : Subgroup Y}, u₂ ∈ trivialOnQuot J → u₂ ∈ centralizerModOdd ⊤ J := fun h =>
    ⟨Subgroup.mem_top _, h.1, Asc77.mem_normalizer_oddCore_of_mem_normalizer h.1,
      fun l hl => h.2 l hl⟩
  have t23 : u₂ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' d.hzK₃ d.hu₂.1
  have t24 : u₂ ∈ trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h42.symm d.hzK' hz4 d.hu₂.1
  obtain ⟨M, M', hM, hM', hne, hcomm, hcM, hcM', hmM, hmM'⟩ :=
    liftPair_of_twins hΩ hc2 hS hmem hmem4 h43 d.hzK₃ hz4 htc hlf hu₂c (hcm t23) (hcm t24)
  have hω := oddCoreIn_cu_eq_bot d h2g hα hodd
  have hcore : componentClassificationOddCore ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hω
  have hinj : ∀ a b : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y)),
      oddQuotMk (u₁ * u₂) a = oddQuotMk (u₁ * u₂) b → a = b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ componentClassificationOddCore ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y)) :=
      (QuotientGroup.eq).mp hab
    rw [hcore, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1)
  have hxcore : ∀ (J : Subgroup Y) (hJ : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      IsPGroup 2 ↥J → ∀ x ∈ J, x ∈ TwinADescent.coreAt (u₁ * u₂) J := by
    intro J hJ hJ2 x hx
    have hxC : x ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_trivialOnQuot hJ2 hJ.2 hx).symm
    have hle : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
      Subgroup.zpowers_le.mpr ⟨hx, hxC⟩
    have h2x : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      hJ2.to_le (Subgroup.zpowers_le.mpr hx)
    exact le_tightCore_of_isPGroup hle h2x (Subgroup.mem_zpowers x)
  have hK₃M : K₃ ≤ M := fun x hx =>
    hmM x (hxcore K₃ hmem (h2g K₃ d.hK₃.1) x hx) (d.hzK₃.commute_of_mem hx).symm
  have hK₄M' : K₄ ≤ M' := fun x hx =>
    hmM' x (hxcore K₄ hmem4 (h2g K₄ hK₄.1) x hx) (hz4.commute_of_mem hx).symm
  have hbot := oddCoreIn_ctcu_eq_bot d h2g hodd
  refine ⟨M, M', hM, hM', hK₃M, hK₄M', ?_, ?_, ?_⟩
  · intro a ha b hb
    have haC : a ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := hM.le ha
    have hbC : b ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := hM'.le hb
    have := hcomm (oddQuotMk (u₁ * u₂) ⟨a, haC⟩) ⟨⟨a, haC⟩, ha, rfl⟩
      (oddQuotMk (u₁ * u₂) ⟨b, hbC⟩) ⟨⟨b, hbC⟩, hb, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (hinj _ _ this)
  · have := Balance.oddCoreIn_le_of_isSubnormal hM.subnormal
    rw [hbot] at this
    exact le_bot_iff.mp this
  · have := Balance.oddCoreIn_le_of_isSubnormal hM'.subnormal
    rw [hbot] at this
    exact le_bot_iff.mp this

end Lifts

variable {n : ℕ}

end Odd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
