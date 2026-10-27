module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Sec
public import CFSG.ClassicalInvolution.Q3.TL4SepDefs
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAEQ

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

theorem odd_natCard_oddCore_layerY :
    Odd (Nat.card (classicalInvolutionOddCore ↥(layerY Ω x))) :=
  CFSG.ComponentClassification.OddCore.odd_card _

theorem mem_layerY_of_isUniqueInvolution (h : TypeRFam r Ω) {L : Subgroup G} (hL : XMem Ω x L)
    {z : G} (hz : IsUniqueInvolution L z) : z ∈ layerY Ω x :=
  coreAt_le_layerY hL (isUniqueInvolution_coreAt h hL hz).mem

theorem isUniqueInvolution_secImg (h : TypeRFam r Ω) {L : Subgroup G} (hL : XMem Ω x L)
    {z : G} (hz : IsUniqueInvolution L z) :
    IsUniqueInvolution (secImg Ω x L)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))
        ⟨z, mem_layerY_of_isUniqueInvolution h hL hz⟩) :=
  isUniqueInvolution_map_mk_of_odd (odd_natCard_inf odd_natCard_oddCore_layerY _)
    (isUniqueInvolution_subgroupOf (isUniqueInvolution_coreAt h hL hz) (coreAt_le_layerY hL))

omit [Finite G] in
theorem conjSub_secImg (y : ↥(layerY Ω x)) (L : Subgroup G) :
    conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) y) (secImg Ω x L) =
      secImg Ω x (conjSub (y : G) L) := by
  unfold secImg
  rw [← AscQuot.map_conjSub, conjSub_subgroupOf,
    conjSub_coreAt x (layerY_le_centralizer y.2)]

omit [Finite G] in
theorem secImg_conj_of_mem {ν : ↥(layerY Ω x)} (hν : ν ∈ classicalInvolutionOddCore ↥(layerY Ω x))
    (L : Subgroup G) : secImg Ω x (conjSub (ν : G) L) = secImg Ω x L := by
  have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) ν = 1 :=
    (QuotientGroup.eq_one_iff ν).mpr hν
  rw [← conjSub_secImg, h1, conjSub_one]

theorem secImg_ne (h : TypeRFam r Ω) {L M : Subgroup G} (hL : XMem Ω x L) (hM : XMem Ω x M)
    {z y : G} (hz : IsUniqueInvolution L z) (hy : IsUniqueInvolution M y) (hzy : z * y = y * z)
    (hne : z ≠ y) : secImg Ω x L ≠ secImg Ω x M := by
  intro heq
  have h1 := isUniqueInvolution_secImg h hL hz
  have h2 := isUniqueInvolution_secImg h hM hy
  rw [heq] at h1
  have he := h1.eq h2
  set z' : ↥(layerY Ω x) := ⟨z, mem_layerY_of_isUniqueInvolution h hL hz⟩
  set y' : ↥(layerY Ω x) := ⟨y, mem_layerY_of_isUniqueInvolution h hM hy⟩
  have hmem : z' * y' ∈ classicalInvolutionOddCore ↥(layerY Ω x) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    have e2 : (QuotientGroup.mk z' : SecQuot Ω x) = QuotientGroup.mk y' := he
    rw [e2, ← QuotientGroup.mk_mul]
    have : y' * y' = 1 := Subtype.ext hy.sq
    rw [this, QuotientGroup.mk_one]
  have hsq : (z' * y') * (z' * y') = 1 := by
    apply Subtype.ext
    show z * y * (z * y) = 1
    calc z * y * (z * y) = z * (y * z) * y := by group
      _ = z * (z * y) * y := by rw [hzy]
      _ = (z * z) * (y * y) := by group
      _ = 1 := by rw [hz.sq, hy.sq]; group
  have h2el : IsPGroup 2 (Subgroup.zpowers (z' * y')) :=
    isPGroup_zpowers_of_sq hsq
  have h3 := eq_one_of_isPGroup_of_mem_odd odd_natCard_oddCore_layerY hmem h2el
  apply hne
  have h4 : z * y = 1 := congrArg Subtype.val h3
  calc z = z * (y * y) := by rw [hy.sq, mul_one]
    _ = (z * y) * y := by group
    _ = y := by rw [h4, one_mul]

theorem secImg_mem_omegaNbr {L M : Subgroup G} (hL : XMem Ω x L) (hM : XMem Ω x M)
    {P : Subgroup G} (hP : IsSylow2In P M) (hPx : P ≤ Subgroup.centralizer ({x} : Set G))
    (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hne : secImg Ω x L ≠ secImg Ω x M) :
    secImg Ω x M ∈ omegaNbr (secFam Ω x) (secImg Ω x L) := by
  have hPC : IsSylow2In P (coreAt x M) := (isSylow2In_coreAt_iff hM).mpr ⟨hP, hPx⟩
  have hPY : P ≤ layerY Ω x := hPC.1.trans (coreAt_le_layerY hM)
  have hP' : IsSylow2In (P.subgroupOf (layerY Ω x)) ((coreAt x M).subgroupOf (layerY Ω x)) :=
    hPC.subgroupOf (coreAt_le_layerY hM)
  refine ⟨secImg_mem hM, hne.symm, (P.subgroupOf (layerY Ω x)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))),
    mem_RSet_of_isSylow2In (secImg_mem hM) (isSylow2In_map_mk odd_natCard_oddCore_layerY hP'),
    Subgroup.map_mono hP'.1, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hp' : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hpN : (p : G) ∈ Subgroup.normalizer (coreAt x L : Set G) :=
    mem_normalizer_coreAt x (hPN hp') (hPx hp')
  exact mk_mem_normalizer_map ((mem_normalizer_subgroupOf_iff (coreAt_le_layerY hL)).mp hpN)

theorem exists_conj_of_secImg_eq (h : TypeRFam r Ω) {L M : Subgroup G} (hL : XMem Ω x L)
    (hM : XMem Ω x M) (heq : secImg Ω x L = secImg Ω x M) :
    ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
      M = conjSub (ν : G) L := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL.1
  obtain ⟨y, hy⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hM.1
  have h1 := isUniqueInvolution_secImg h hL hz
  have h2 := isUniqueInvolution_secImg h hM hy
  rw [heq] at h1
  obtain ⟨ν, hν, hνy⟩ := exists_conj_eq_of_map_eq odd_natCard_oddCore_layerY
    (Subtype.ext hz.sq) (Subtype.ext hy.sq) (h1.eq h2)
  have hνy' : (ν : G) * y * (ν : G)⁻¹ = z := congrArg Subtype.val hνy
  refine ⟨ν⁻¹, (classicalInvolutionOddCore _).inv_mem hν, ?_⟩
  have hy' : IsUniqueInvolution (conjSub ((ν⁻¹ : ↥(layerY Ω x)) : G) L) y := by
    have := hz.conj ((ν⁻¹ : ↥(layerY Ω x)) : G)
    have e : ((ν⁻¹ : ↥(layerY Ω x)) : G) * z * ((ν⁻¹ : ↥(layerY Ω x)) : G)⁻¹ = y := by
      rw [← hνy']
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at this
  have hL' := h.hyp.conjInvariant ((ν⁻¹ : ↥(layerY Ω x)) : G) L hL.1
  exact h.noTwins _ hL' M ⟨hM.1, y, hy', hy⟩

theorem mem_USet_of_mem_USet_coreFam {U : Subgroup G} (hU : U ∈ USet (coreFam Ω x)) :
    U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨C, ⟨L, hL, rfl⟩, hRC⟩ := exists_isSylow2In_of_mem_RSet hR
  exact ⟨R, mem_RSet_of_isSylow2In hL.1 ((isSylow2In_coreAt_iff hL).mp hRC).1, hUR, hcyc, hidx⟩

theorem exists_conj_omegaStarNbr_of_secImg (h : TypeRFam r Ω) {L M : Subgroup G}
    (hL : XMem Ω x L) (hM : XMem Ω x M)
    (hst : secImg Ω x M ∈ omegaStarNbr (secFam Ω x) (secImg Ω x L)) :
    ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
      M ∈ omegaStarNbr Ω (conjSub (ν : G) L) := by
  obtain ⟨n, hn, hpair⟩ := Q3T7.exists_conj_omegaStarNbr3 (h.pairFam (x := x)).hyp
    (h.secFam (x := x)).hyp odd_natCard_oddCore_layerY (subgroupOf_mem_pairFam hL)
    (subgroupOf_mem_pairFam hM) hst
  refine ⟨n, hn, ?_⟩
  have hnx : (n : G) ∈ Subgroup.centralizer ({x} : Set G) := layerY_le_centralizer n.2
  have hLn : XMem Ω x (conjSub (n : G) L) := XMem.conj' h.hyp.conjInvariant hL hnx
  rw [conjSub_subgroupOf, conjSub_coreAt x hnx] at hpair
  obtain ⟨-, hne, U', hU', hUM, hUN⟩ := hpair
  refine ⟨hM.1, fun e => hne (by rw [e]), U'.map (layerY Ω x).subtype,
    mem_USet_of_mem_USet_coreFam (map_mem_USet_restrict hU'), ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact coreAt_le x M (Subgroup.mem_subgroupOf.mp (hUM hu))
  · obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hLn.1
    have hzC := isUniqueInvolution_coreAt h hLn hz
    rintro _ ⟨u, hu, rfl⟩
    have hu1 : (u : G) ∈ Subgroup.normalizer (coreAt x (conjSub (n : G) L) : Set G) :=
      (mem_normalizer_subgroupOf_iff (coreAt_le_layerY hLn)).mpr (hUN hu)
    have hcz : (u : G) * z * (u : G)⁻¹ = z := hzC.conj_eq (mem_normalizer_iff_conjSub_eq.mp hu1)
    refine h.tight _ hLn.1 z hz (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc (u : G) * z = ((u : G) * z * (u : G)⁻¹) * (u : G) := by group
      _ = z * (u : G) := by rw [hcz]

theorem exists_conj_mem_dstarComp_of_conn (h : TypeRFam r Ω) {K : Subgroup G}
    (hK : XMem Ω x K) (hconn : T3.DStarConnected (secFam Ω x)) {L : Subgroup G}
    (hL : XMem Ω x L) :
    ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
      conjSub (ν : G) L ∈ dstarComp Ω K := by
  have hcl := h.hyp.conjInvariant
  have key : ∀ b, Relation.ReflTransGen (dstarAdj (secFam Ω x)) (secImg Ω x K) b →
      b ∈ secFam Ω x ∧ ∀ M, XMem Ω x M → secImg Ω x M = b →
        ∃ ν : ↥(layerY Ω x), ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) ∧
          conjSub (ν : G) M ∈ dstarComp Ω K := by
    intro b hb
    induction hb with
    | refl =>
      refine ⟨secImg_mem hK, fun M hM hMb => ?_⟩
      obtain ⟨ν, hν, hνK⟩ := exists_conj_of_secImg_eq h hK hM hMb.symm
      refine ⟨ν⁻¹, (classicalInvolutionOddCore _).inv_mem hν, ?_⟩
      rw [hνK, Subgroup.coe_inv, conjSub_inv_conjSub]
      exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      obtain ⟨hbΦ, hPb⟩ := ih
      obtain ⟨hcΦ, hadj⟩ := hbc
      refine ⟨hcΦ, fun M hM hMc => ?_⟩
      obtain ⟨M₁, hM₁, rfl⟩ := mem_secFam_iff.mp hbΦ
      obtain ⟨ν₁, hν₁, hM₂⟩ := hPb M₁ hM₁ rfl
      have hν₁x : (ν₁ : G) ∈ Subgroup.centralizer ({x} : Set G) :=
        layerY_le_centralizer ν₁.2
      have hM₂X : XMem Ω x (conjSub (ν₁ : G) M₁) := XMem.conj' hcl hM₁ hν₁x
      have hM₂b : secImg Ω x (conjSub (ν₁ : G) M₁) = secImg Ω x M₁ := secImg_conj_of_mem hν₁ M₁
      rcases hadj with h1 | h2
      · rw [← hM₂b, ← hMc] at h1
        obtain ⟨m, hm, hmn⟩ := exists_conj_omegaStarNbr_of_secImg h hM₂X hM h1
        refine ⟨m⁻¹, (classicalInvolutionOddCore _).inv_mem hm, ?_⟩
        have h3 := omegaStarNbr_conj hcl hmn ((m : G)⁻¹)
        rw [conjSub_inv_conjSub] at h3
        rw [Subgroup.coe_inv]
        exact Relation.ReflTransGen.tail hM₂ ⟨hcl _ M hM.1, Or.inl h3⟩
      · rw [← hM₂b, ← hMc] at h2
        obtain ⟨m, hm, hmn⟩ := exists_conj_omegaStarNbr_of_secImg h hM hM₂X h2
        exact ⟨m, hm, Relation.ReflTransGen.tail hM₂ ⟨hcl _ M hM.1, Or.inr hmn⟩⟩
  exact (key _ (hconn _ (secImg_mem hK) _ (secImg_mem hL))).2 L hL rfl

theorem layerY_le_sigmaNorm_of_conn (h : TypeRFam r Ω) {K : Subgroup G} (hK : XMem Ω x K)
    (hcomp : dComp Ω K = dstarComp Ω K) (hconn : T3.DStarConnected (secFam Ω x))
    (hO : oddCoreOf (layerY Ω x) ≤ sigmaNorm Ω K) : layerY Ω x ≤ sigmaNorm Ω K := by
  have hcl := h.hyp.conjInvariant
  refine iSup₂_le fun C hC => ?_
  obtain ⟨L, hL, rfl⟩ := hC
  obtain ⟨ν, hν, hνL⟩ := exists_conj_mem_dstarComp_of_conn h hK hconn hL
  rw [← hcomp] at hνL
  have hνN : (ν : G) ∈ sigmaNorm Ω K := hO ⟨ν, hν, rfl⟩
  have hle : conjSub (ν : G) L ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hcl hK.1 hνL)
  intro c hc
  have h1 : (ν : G) * c * (ν : G)⁻¹ ∈ sigmaNorm Ω K :=
    hle (mem_conjSub_iff.mpr (by simpa [mul_assoc] using coreAt_le x L hc))
  have h2 := (sigmaNorm Ω K).mul_mem ((sigmaNorm Ω K).mul_mem
    ((sigmaNorm Ω K).inv_mem hνN) h1) hνN
  simpa [mul_assoc] using h2

theorem mem_omegaNbr_of_commutes {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    {K J : Subgroup X} (hJ : J ∈ Φ) (hne : J ≠ K) (hc : Commutes K J) : J ∈ omegaNbr Φ K := by
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := J) (IsPGroup.of_bot (p := 2)) bot_le
  refine ⟨hJ, hne, P, mem_RSet_of_isSylow2In hJ hP, hP.1, fun p hp => ?_⟩
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [mem_conjSub_iff] at hy
    have hcomm : (p⁻¹ * y * p) * p = p * (p⁻¹ * y * p) := hc _ hy _ (hP.1 hp)
    have e : y = p⁻¹ * y * p := by
      calc y = p * (p⁻¹ * y * p) * p⁻¹ := by group
        _ = (p⁻¹ * y * p) * p * p⁻¹ := by rw [hcomm]
        _ = p⁻¹ * y * p := by group
    rw [e]
    exact hy
  · intro y hy
    rw [mem_conjSub_iff]
    have hcomm : y * p = p * y := hc _ hy _ (hP.1 hp)
    have e : p⁻¹ * y * p = y := by
      calc p⁻¹ * y * p = p⁻¹ * (y * p) := by group
        _ = p⁻¹ * (p * y) := by rw [hcomm]
        _ = y := by group
    rw [e]
    exact hy

theorem centralizer_le_sigmaNorm_of_layerY_le (h : TypeRFam r Ω) {n : ℕ} (hT4 : Thm4RBelow r n)
    (hn : Nat.card (SecQuot Ω x) < n) {K : Subgroup G} (hK : XMem Ω x K)
    (hcomp : dComp Ω K = dstarComp Ω K) (hY : layerY Ω x ≤ sigmaNorm Ω K) :
    Subgroup.centralizer ({x} : Set G) ≤ sigmaNorm Ω K := by
  have hcl := h.hyp.conjInvariant
  have hΦ := h.secFam (x := x)
  have hT : T4Hyp r (SecQuot Ω x) (secFam Ω x) :=
    { hyp := hΦ.hyp
      twoGroup := hΦ.twoGroup
      quat := hΦ.quat
      tight := hΦ.tight
      noTwins := fun J hJ J' hJ' u hu hu' => (hΦ.noTwins J hJ J' ⟨hJ', u, hu, hu'⟩).symm
      aEmpty := aEmpty_secFam h
      odd := secQuot_oddCore_eq_bot }
  intro c hc
  have hKc : XMem Ω x (conjSub c K) := XMem.conj' hcl hK hc
  rw [mem_sigmaNorm_iff hcl hK.1]
  by_cases hconj : ∃ g : SecQuot Ω x, conjSub g (secImg Ω x K) = secImg Ω x (conjSub c K)
  · obtain ⟨gb, hgb⟩ := hconj
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have e1 : secImg Ω x (conjSub (g : G) K) = secImg Ω x (conjSub c K) := by
      rw [← conjSub_secImg]
      exact hgb
    have hKg : XMem Ω x (conjSub (g : G) K) :=
      XMem.conj' hcl hK (layerY_le_centralizer g.2)
    obtain ⟨ν, -, hν⟩ := exists_conj_of_secImg_eq h hKg hKc e1
    rw [hν, ← conjSub_mul]
    have hy : (ν : G) * (g : G) ∈ sigmaNorm Ω K :=
      (sigmaNorm Ω K).mul_mem (hY ν.2) (hY g.2)
    exact (mem_sigmaNorm_iff hcl hK.1).mp hy
  · have hc' := hT4 (SecQuot Ω x) hn (secFam Ω x) hT (secImg Ω x K) (secImg_mem hK)
      (secImg Ω x (conjSub c K)) (secImg_mem hKc) hconj
    have hne : secImg Ω x (conjSub c K) ≠ secImg Ω x K := fun e =>
      hconj ⟨1, by rw [conjSub_one, e]⟩
    have hnbr := mem_omegaNbr_of_commutes (secImg_mem hKc) hne hc'
    have hst := Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ.hyp _ hnbr
    obtain ⟨m, hm, hmn⟩ := exists_conj_omegaStarNbr_of_secImg h hK hKc hst
    have hmK : conjSub (m : G) K ∈ dComp Ω K := (mem_sigmaNorm_iff hcl hK.1).mp (hY m.2)
    rw [hcomp] at hmK ⊢
    exact Relation.ReflTransGen.tail hmK ⟨hcl c K hK.1, Or.inl hmn⟩

end CFSG.ClassicalInvolution.Q3.TL4
