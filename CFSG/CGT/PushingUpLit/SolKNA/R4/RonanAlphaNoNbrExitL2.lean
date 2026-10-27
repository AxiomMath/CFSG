module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrL2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Z
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Mk
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2)
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open scoped commutatorElement Pointwise

section Cert


variable {r n : ℕ}

theorem l2_klein_cent {T : Type} [Group T] [Finite T] {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : T ≃* PSL2 K) {a z x : T} (ha2 : a * a = 1)
    (hz2 : z * z = 1) (haz : a * z = z * a) (ha1 : a ≠ 1) (hz1 : z ≠ 1) (hne : a ≠ z)
    (hxa : x * a = a * x) (hxz : x * z = z * x) : x * x = 1 := by
  classical
  set V : Subgroup T := Subgroup.closure ({a, z} : Set T) with hV
  have hcard : Nat.card ↥V = 4 :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.card_closure_pair_eq_four ha2 hz2 ha1 hz1 hne haz
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    rcases TypeCSetup.mem_closure_pair ha2 hz2 haz hv with h | h | h | h
    · rw [h]; simp
    · rw [h, pow_two, ha2]
    · rw [h, pow_two, hz2]
    · rw [h, pow_two]
      calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [haz]
        _ = a * a * (z * z) := by group
        _ = 1 := by rw [ha2, hz2, one_mul]
  have hKl : IsKleinFour V := by
    haveI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
    refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
    intro v hv
    apply orderOf_eq_prime
    · exact Subtype.ext (hsq v v.property)
    · exact hv
  have hKl' : IsKleinFour (V.map e.toMonoidHom) :=
    GorensteinWalter.isKleinFour_map_of_injective V hKl e.toMonoidHom e.injective
  have hC := GorensteinWalter.psl2_kleinFour_centralizer_eq_self K hK _ hKl'
  have hxC : e x ∈ Subgroup.centralizer ((V.map e.toMonoidHom : Subgroup (PSL2 K)) : Set (PSL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hc : x * v = v * x := by
      have hle : V ≤ Subgroup.centralizer ({x} : Set T) := by
        rw [hV, Subgroup.closure_le]
        intro w hw
        rcases hw with rfl | hw
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hxa.symm
        · rw [Set.mem_singleton_iff.mp hw]
          exact Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
    show e v * e x = e x * e v
    rw [← map_mul, ← map_mul, ← hc]
  rw [hC] at hxC
  obtain ⟨w, hw, hwx⟩ := hxC
  have hxw : x = w := e.injective hwx.symm
  rw [hxw, ← pow_two]
  exact hsq w hw

@[expose] def ExitL2Facts {X : Type} [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop :=
  Subgroup.center X = ⊥ ∧ IsSimpleGroup ↥(genFittingFStar X) ∧
    (genFittingFStar X).index ≤ 2 ∧
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
      CFSG.Blueprint.LieModel (FStarQuot X) .PSL 2 p f) ∧
    (∀ M ∈ Φ, omegaStarNbr Φ M = ∅)

theorem exitL2_fstar (hr : 4 ≤ r) {X : Type} [Group X] [Finite X] {z : X}
    {L : Subgroup X} [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    (hLC : Subgroup.centralizer (L : Set X) = Subgroup.center X)
    (hZ : Subgroup.center X = ⊥) (hzn : z ∉ Subgroup.center X)
    (hL2 : SmallL2 ↥(socleOf L))
    (hTC : Subgroup.centralizer ((socleOf L : Subgroup (X ⧸ Subgroup.center X)) :
      Set (X ⧸ Subgroup.center X)) = ⊥)
    {u b : X} (hou : orderOf u = 2 ^ (r - 1)) (hbu : b * u * b⁻¹ = u⁻¹)
    (hbb : b * b = u ^ 2 ^ (r - 2)) (hzu : u ^ 2 ^ (r - 2) = z) :
    genFittingFStar X = L ∧ IsSimpleGroup ↥L ∧
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
        CFSG.Blueprint.LieModel (FStarQuot X) .PSL 2 p f) := by
  classical
  have hZL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := (mem_center_subtype_iff hLC x).mp hx
    rw [hZ, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have eL : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZL.symm)
  haveI hsimp : IsSimpleGroup ↥L := by
    haveI := hLq.2.1
    exact eL.isSimpleGroup
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLq.2.2
    exact ⟨eL.symm a, eL.symm b, fun h => hab (by simpa using congrArg eL h)⟩
  have hCL : Subgroup.centralizer (L : Set X) = ⊥ := by rw [hLC, hZ]
  have hFL : genFittingFStar X = L := genFittingFStar_eq_of_normal_simple L hnab hCL
  obtain ⟨hxo, hbx, hbb', hxz⟩ := quatPair_mk hr hzn hou hbu hbb hzu
  obtain ⟨p, f, K, _, _, hp, hp2, hKcard, hfe, h13, ⟨eT⟩⟩ :=
    l2_data_even hr (socleOf L) hL2 hTC hxo hbx hbb' hxz
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h13
    · exact h
  have hLM : CFSG.Blueprint.LieModel ↥(socleOf L) .PSL 2 p f :=
    Or.inl ⟨by decide, ⟨⟨hp, hf1, le_refl 2, fun h => by
        have := congrArg Prod.snd h
        simp only at this
        omega, fun h => by
        have := congrArg Prod.snd h
        simp only at this
        omega⟩, K, inferInstance, inferInstance, hKcard,
      ⟨eT.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩⟩
  let eF1 : ↥(genFittingFStar X) ≃* ↥L := MulEquiv.subgroupCongr hFL
  have hZF : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxL : eF1 x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro l
      obtain ⟨y, rfl⟩ := eF1.surjective l
      rw [← map_mul, ← map_mul, hx y]
    rw [hZL, Subgroup.mem_bot] at hxL
    exact Subgroup.mem_bot.mpr (eF1.injective (hxL.trans (map_one eF1).symm))
  let eFQ : FStarQuot X ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZF).trans (QuotientGroup.quotientBot.trans eF1)
  obtain ⟨e⟩ := nonempty_socle_equiv hLC
  have eS : ↥(socleOf L) ≃* ↥L := e.trans eL.symm
  exact ⟨hFL, hsimp, p, f, hp, hp2, hfe, by omega,
    LieType.CurtisTits.lieModel_of_mulEquiv (eS.trans eFQ.symm) hLM⟩

theorem two_elt_mem_of_sylow {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 ↥R}
    {H : Subgroup X} [H.Normal] (hS : ∀ s ∈ (S : Subgroup R).map R.subtype, s ∈ H) {k : X}
    (hkR : k ∈ R) {a : ℕ} (hka : k ^ 2 ^ a = 1) : k ∈ H := by
  classical
  obtain ⟨k', hk'⟩ : ∃ k' : ↥R, (k' : X) = k := ⟨⟨k, hkR⟩, rfl⟩
  have hk'pow : k' ^ 2 ^ a = 1 := Subtype.ext (by simpa [hk'] using hka)
  have hfin : IsPGroup 2 (Subgroup.zpowers k') :=
    IsPGroup.of_card_dvd_pow (n := a) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk'pow)
  obtain ⟨Q, hQ⟩ := hfin.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥R) S Q
  have hmem : k' ∈ (g • S : Sylow 2 ↥R) := by
    rw [hg]; exact hQ (Subgroup.mem_zpowers k')
  have hmem1 : k' ∈ MulAut.conj g • (S : Subgroup R) := by
    rw [← Sylow.coe_subgroup_smul]; exact hmem
  have hmem2 : (MulAut.conj g)⁻¹ • k' ∈ (S : Subgroup R) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hmem1
  have hconj : (MulAut.conj g)⁻¹ • k' = g⁻¹ * k' * g := MulAut.conj_inv_apply g k'
  rw [hconj] at hmem2
  have hs : (g : X)⁻¹ * k * (g : X) ∈ (S : Subgroup R).map R.subtype := by
    rw [← hk']
    exact Subgroup.mem_map_of_mem R.subtype hmem2
  have hsH := hS _ hs
  have h3 := Subgroup.Normal.conj_mem ‹H.Normal› _ hsH (g : X)
  rwa [show (g : X) * ((g : X)⁻¹ * k * (g : X)) * (g : X)⁻¹ = k by group] at h3

theorem exitL2_index (hr : 4 ≤ r) {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam r Φ) {A : Subgroup X} (hA : A ∈ Φ) {S : Sylow 2 ↥A} {L : Subgroup X}
    [L.Normal] (hcomm : ∀ x y : X, ⁅x, y⁆ ∈ L) (hgen : (⨆ g : X, conjSub g A) = ⊤) {u b : X}
    (huS : u ∈ sylowSet S) (hbS : b ∈ sylowSet S) (huL : u ∈ L) (hbL : b ∉ L)
    (hou : orderOf u = 2 ^ (r - 1)) (hbb : b * b = u ^ 2 ^ (r - 2)) : L.index ≤ 2 := by
  classical
  set H : Subgroup X := L ⊔ Subgroup.zpowers b with hHdef
  have hHn : H.Normal := by
    refine ⟨fun h hh g => ?_⟩
    have e : g * h * g⁻¹ = ⁅g, h⁆ * h := by
      rw [commutatorElement_def]; group
    rw [e]
    exact H.mul_mem (Subgroup.mem_sup_left (hcomm g h)) hh
  have hbz : b ∉ Subgroup.zpowers u := fun h => hbL ((Subgroup.zpowers_le.mpr huL) h)
  have hcard : Nat.card ↥((S : Subgroup A).map A.subtype) = 2 * orderOf u := by
    obtain ⟨e⟩ := hΦ.quat A hA _ (isSylow2In_map_subtype A S)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, hou]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, pow_succ]
    ring
  have hcos := mem_zpowers_or_coset hcard huS hbS hbz
  have hSH : ∀ s ∈ (S : Subgroup A).map A.subtype, s ∈ H := by
    intro s hs
    rcases hcos s hs with h1 | h2
    · exact Subgroup.mem_sup_left ((Subgroup.zpowers_le.mpr huL) h1)
    · have h3 : b⁻¹ * s ∈ H := Subgroup.mem_sup_left ((Subgroup.zpowers_le.mpr huL) h2)
      have h4 : b ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
      have := H.mul_mem h4 h3
      rwa [mul_inv_cancel_left] at this
  have hAH : A ≤ H := by
    have hcl := hΦ.closure_twoElts hA
    rw [← hcl, Subgroup.closure_le]
    intro x ⟨hxA, hx2⟩
    obtain ⟨n, hn⟩ := hx2 ⟨x, Subgroup.mem_zpowers x⟩
    have hxn : x ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    exact two_elt_mem_of_sylow hSH hxA hxn
  have hTop : H = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun g => ?_
    intro y hy
    have hy' : g⁻¹ * y * g ∈ A := mem_conjSub_iff.mp hy
    have h5 := Subgroup.Normal.conj_mem hHn _ (hAH hy') g
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h5
  have hb2 : b * b ∈ L := by
    rw [hbb]
    exact L.pow_mem huL _
  have hsurj : ∀ x : X, x ∈ L ∨ b⁻¹ * x ∈ L := by
    intro x
    have hx : x ∈ H := by rw [hTop]; exact Subgroup.mem_top x
    obtain ⟨k, hk, l, hl, hkl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    have hbm : b ^ m = b ^ (m % 2) * (b * b) ^ (m / 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv m 2, zpow_add, zpow_mul]
      rw [zpow_two]
    have hq : (b * b) ^ (m / 2) ∈ L := L.zpow_mem hb2 _
    rcases Int.emod_two_eq_zero_or_one m with h0 | h1
    · left
      rw [h0, zpow_zero, one_mul] at hbm
      rw [← hkl, hbm]
      exact L.mul_mem hk hq
    · right
      rw [h1, zpow_one] at hbm
      have h5 : b⁻¹ * x = (b⁻¹ * k * b⁻¹⁻¹) * (b * b) ^ (m / 2) := by
        rw [← hkl, hbm]; group
      rw [h5]
      exact L.mul_mem (Subgroup.Normal.conj_mem ‹L.Normal› k hk b⁻¹) hq
  have hsurj' : Function.Surjective
      (fun c : Bool => (QuotientGroup.mk (cond c b 1) : X ⧸ L)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rcases hsurj x with h | h
    · exact ⟨false, QuotientGroup.eq.mpr (by simpa using h)⟩
    · exact ⟨true, QuotientGroup.eq.mpr h⟩
  have h2 := Nat.card_le_card_of_surjective _ hsurj'
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
  exact h2

theorem exitL2_dstar (hr : 4 ≤ r) {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam r Φ) {L : Subgroup X} {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : ↥L ≃* PSL2 K) (hLX : ∀ x : X, x * x ∈ L)
    (hinv : ∀ M ∈ Φ, ∀ m : X, IsUniqueInvolution M m → m ∈ L) :
    ∀ M ∈ Φ, omegaStarNbr Φ M = ∅ := by
  classical
  intro M hM
  rw [Set.eq_empty_iff_forall_notMem]
  rintro N ⟨hNΦ, hNM, U, hU, hUN, hUM⟩
  obtain ⟨R, -, J, hJ, hRJ, hUR, hcyc, hcard, h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΦ.hyp hU
  obtain ⟨eR⟩ := hΦ.quat J hJ R hRJ
  have hRcard : Nat.card ↥R = 2 ^ r := by
    rw [Nat.card_congr eR.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  have hUcard : Nat.card ↥U = 2 ^ (r - 1) := by
    have h2 : 2 * Nat.card ↥U = 2 * 2 ^ (r - 1) := by
      rw [← hcard, hRcard, ← pow_succ']
      congr 1
      omega
    omega
  obtain ⟨u, hu⟩ := hcyc.exists_generator
  have hou : orderOf (u : X) = 2 ^ (r - 1) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu, hUcard]
  set v : X := (u : X) with hv
  have hvU : v ∈ U := u.2
  set zU : X := v ^ 2 ^ (r - 2) with hzU
  have hzUU : zU ∈ U := U.pow_mem hvU _
  have hk : 2 ^ (r - 2) + 2 ^ (r - 2) = 2 ^ (r - 1) := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  have hzU2 : zU * zU = 1 := by
    rw [hzU, ← pow_add, hk, ← hou]
    exact pow_orderOf_eq_one v
  have hzU1 : zU ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hou] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ (r - 2) < 2 ^ (r - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨zN, hzN⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hNΦ
  obtain ⟨zM, hzM⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hM
  have hzUN : zU = zN := (hzN.unique zU (hUN hzUU) hzU2).resolve_left hzU1
  have hvz : Commute v zM := Subgroup.mem_centralizer_singleton_iff.mp
    (S1916.normalizer_le_centralizer_of_isUniqueInvolution hzM (hUM hvU))
  have hzML : zM ∈ L := hinv M hM zM hzM
  have hzNL : zN ∈ L := hinv N hNΦ zN hzN
  have hv2 : v * v ∈ L := hLX v
  have hne : zM ≠ zN := by
    intro h
    apply hNM
    refine hΦ.noTwins M hM N ⟨hNΦ, zM, hzM, ?_⟩
    rw [h]
    exact hzN
  have hxz : Commute (v * v) zN := by
    rw [← hzUN, hzU]
    exact Commute.mul_left (Commute.self_pow v _) (Commute.self_pow v _)
  have hxa : Commute (v * v) zM := hvz.mul_left hvz
  have haz : Commute zM zN := by
    rw [← hzUN, hzU]
    exact (hvz.pow_left _).symm
  have h1 := l2_klein_cent hK e (a := ⟨zM, hzML⟩) (z := ⟨zN, hzNL⟩) (x := ⟨v * v, hv2⟩)
    (Subtype.ext hzM.sq) (Subtype.ext hzN.sq) (Subtype.ext haz.eq) (fun h => hzM.ne_one
      (congrArg Subtype.val h)) (fun h => hzN.ne_one (congrArg Subtype.val h))
    (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hxa.eq) (Subtype.ext hxz.eq)
  have h2 : v * v * (v * v) = 1 := congrArg Subtype.val h1
  have h3 : v ^ 4 = 1 := by
    calc v ^ 4 = v ^ 2 * v ^ 2 := by rw [← pow_add]
      _ = v * v * (v * v) := by rw [pow_two]
      _ = 1 := h2
  have h4' := orderOf_dvd_of_pow_eq_one h3
  rw [hou] at h4'
  have h5 := Nat.le_of_dvd (by norm_num) h4'
  have h6 : 2 ^ 3 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exitL2_psl (hr : 4 ≤ r) {X : Type} [Group X] [Finite X] {z : X}
    {L : Subgroup X} [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    (hLC : Subgroup.centralizer (L : Set X) = Subgroup.center X)
    (hZ : Subgroup.center X = ⊥) (hzn : z ∉ Subgroup.center X)
    (hL2 : SmallL2 ↥(socleOf L))
    (hTC : Subgroup.centralizer ((socleOf L : Subgroup (X ⧸ Subgroup.center X)) :
      Set (X ⧸ Subgroup.center X)) = ⊥)
    {u b : X} (hou : orderOf u = 2 ^ (r - 1)) (hbu : b * u * b⁻¹ = u⁻¹)
    (hbb : b * b = u ^ 2 ^ (r - 2)) (hzu : u ^ 2 ^ (r - 2) = z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      IsOddPrimePower (Nat.card K) ∧ Nonempty (↥L ≃* PSL2 K) := by
  classical
  have hZL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := (mem_center_subtype_iff hLC x).mp hx
    rw [hZ, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have eL : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZL.symm)
  obtain ⟨hxo, hbx, hbb', hxz⟩ := quatPair_mk hr hzn hou hbu hbb hzu
  obtain ⟨p, f, K, _, _, hp, hp2, hKcard, hfe, h13, ⟨eT⟩⟩ :=
    l2_data_even hr (socleOf L) hL2 hTC hxo hbx hbb' hxz
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h13
    · exact h
  obtain ⟨e⟩ := nonempty_socle_equiv hLC
  have eS : ↥(socleOf L) ≃* ↥L := e.trans eL.symm
  exact ⟨K, inferInstance, inferInstance, ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hKcard⟩,
    ⟨eS.symm.trans eT⟩⟩

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
