module

public import CFSG.LocalAnalysis.GLTheoremA.S8.I1425ONNative
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.A6Leaf
public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.HardMathSupport.Dickson.I271

section Native




variable {Y : Type} [Group Y] [Finite Y] (e : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan)

include e in
theorem unique_component_centralizer_ON {d : Y} (hd : orderOf d = 3) :
    ∃ A : Subgroup Y, GLAPComponent 3 (Subgroup.centralizer ({d} : Set Y)) A ∧
      (∀ I : Subgroup Y, GLAPComponent 3 (Subgroup.centralizer ({d} : Set Y)) I → I = A) ∧
      Nonempty (A ≃* alternatingGroup (Fin 6)) ∧
      GLAPPrimeCore 3 ↥(Subgroup.centralizer ({d} : Set Y)) = ⊥ := by
  set C := Subgroup.centralizer ({d} : Set Y)
  obtain ⟨E, hn, ⟨eE⟩, hidx⟩ := alt6_normal_centralizer_ON e hd
  obtain ⟨hZ, -, hdec⟩ := alt6_split eE hidx
  set A : Subgroup Y := E.map C.subtype
  have eA : A ≃* alternatingGroup (Fin 6) :=
    (E.equivMapOfInjective _ C.subtype_injective).symm.trans eE
  have hAC : A ≤ C := Subgroup.map_subtype_le E
  have hAn : ∀ g ∈ C, ∀ l ∈ A, g * l * g⁻¹ ∈ A := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hn.conj_mem x hx ⟨g, hg⟩, rfl⟩
  have hAq : CFSG.Open.IsQuasisimple ↥A := isQuasisimple_of_equiv_alt6 eA
  have hpA : 3 ∣ Nat.card ↥A := by
    rw [Nat.card_congr eA.toEquiv]; exact three_dvd_card_alt6
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (A : Set Y)) := by
    have hle : C ⊓ Subgroup.centralizer (A : Set Y) ≤ centerIn C := by
      rintro z ⟨hzC, hzA⟩
      show z ∈ (Subgroup.center C).map C.subtype
      refine ⟨⟨z, hzC⟩, ?_, rfl⟩
      show _ ∈ Subgroup.center C
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨z₀, hz₀, x, hx, rfl⟩ := hdec c
      have h1 : ((x : C) : Y) * z = z * x :=
        (Subgroup.mem_centralizer_iff.mp hzA) _ ⟨x, hx, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have h2 : ((z₀ : C) : Y) * z = z * z₀ :=
        congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz₀) ⟨z, hzC⟩).symm
      rw [mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
    have hp9 : IsPGroup 3 (centerIn C) := IsPGroup.of_card (n := 2) (by
      show Nat.card ((Subgroup.center C).map C.subtype) = _
      rw [Subgroup.card_map_of_injective C.subtype_injective, hZ]; norm_num)
    exact hp9.to_le hle
  have hcore := glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three hAC hAn hAq hpA hcent
  exact ⟨A, glaPComponent_of_normal_quasisimple hAC hAn hAq hcore,
    fun I hI => eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three hAC hAn hAq hcore hcent hI,
    ⟨eA⟩, hcore⟩


end Native

section Transfer

variable {G : Type} [Group G] [Finite G]




theorem catalogIs_isA6_of_equiv {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 6)) :
    catalogIs S isA6 := by
  have h6 : 5 ≤ 6 := by norm_num
  refine ⟨TauCeti.CFSGIndex.alternating 6 h6, Or.inl rfl, ⟨?_⟩⟩
  exact e.trans (MulEquiv.refl _)

theorem barX_inf_centralizer {L A : Subgroup G} (hAL : A ≤ L) (hA : IsPGroup 3 A) :
    barX 3 L (L ⊓ Subgroup.centralizer (A : Set G)) =
      Subgroup.centralizer ((barX 3 L A : Subgroup (PQuot 3 L)) : Set (PQuot 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := by
    have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at h
  have hA' : IsPGroup 3 (A.subgroupOf L) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm
  have hsub : (L ⊓ Subgroup.centralizer (A : Set G)).subgroupOf L =
      Subgroup.centralizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨-, h⟩ a ha
      exact Subtype.ext (h _ ha)
    · intro h
      refine ⟨x.2, fun a ha => ?_⟩
      exact congrArg Subtype.val (h ⟨a, hAL ha⟩ ha)
  unfold barX
  rw [hsub]
  exact CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 _ hN _ hA'

noncomputable def barOfEquivAlt6 {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q} (e : J ≃* alternatingGroup (Fin 6)) :
    CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 J ≃* alternatingGroup (Fin 6) :=
  ((QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_three_eq_bot_of_equiv_alt6 e)).trans
    QuotientGroup.quotientBot).trans e

theorem uniqA6_of_quot {L A : Subgroup G} (hAL : A ≤ L) (hA : IsPGroup 3 A)
    (hU : ∃ J' : Subgroup (PQuot 3 L),
      GLAPComponent 3 (Subgroup.centralizer ((barX 3 L A : Subgroup (PQuot 3 L)) : Set (PQuot 3 L))) J' ∧
      (∀ I : Subgroup (PQuot 3 L), GLAPComponent 3
        (Subgroup.centralizer ((barX 3 L A : Subgroup (PQuot 3 L)) : Set (PQuot 3 L))) I → I = J') ∧
      Nonempty (J' ≃* alternatingGroup (Fin 6))) :
    UniqA6 (L ⊓ Subgroup.centralizer (A : Set G)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set H := L ⊓ Subgroup.centralizer (A : Set G) with hHdef
  have hHL : H ≤ L := inf_le_left
  obtain ⟨J', hJ', huniq, ⟨eJ'⟩⟩ := hU
  rw [← barX_inf_centralizer hAL hA] at hJ' huniq
  obtain ⟨J, hJ, hJbar, ⟨eJ⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_lift hHL hJ'
  have eQ : PQuot 3 J ≃* alternatingGroup (Fin 6) := eJ.trans (barOfEquivAlt6 eJ')
  have hZ : Subgroup.center (PQuot 3 J) = ⊥ := by
    rw [← Subgroup.map_center_eq eQ.symm, alt6_center_eq_bot, Subgroup.map_bot]
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)
  have hker : ∀ S : Subgroup ↥L, Nat.Coprime 3 (Nat.card ↥(S ⊓ π.ker)) := by
    intro S
    have h1 : Nat.card ↥(S ⊓ π.ker) ∣ Nat.card ↥(GLAPPrimeCore 3 ↥L) := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_right h1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L)
  have hbar : ∀ K : Subgroup G, GLAPComponent 3 H K → barX 3 L K = J' := fun K hK =>
    huniq _ (glaPComponent_map hp π (hker _) (glaPComponent_subgroupOf hp hHL hK))
  refine ⟨J, hJ, fun J₂ hJ₂ => ?_, ⟨catalogIs_isA6_of_equiv
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eQ), ?_⟩, ?_⟩
  ·
    have h1 := glaPComponent_subgroupOf hp hHL hJ
    have h2 := glaPComponent_subgroupOf hp hHL hJ₂
    have heq : barX 3 L J₂ = barX 3 L J := (hbar J₂ hJ₂).trans (hbar J hJ).symm
    have hb : barX 3 (H.subgroupOf L) (J₂.subgroupOf L) = barX 3 (H.subgroupOf L) (J.subgroupOf L) := by
      apply Subgroup.map_injective (f := lcMonoidHom hp π (H.subgroupOf L) (hker _))
        (lcEquiv hp π (H.subgroupOf L) (hker _)).injective
      rw [lcEquiv_barX hp π _ (hker _) h2.1, lcEquiv_barX hp π _ (hker _) h1.1]
      have heq' : (J₂.subgroupOf L).map π = (J.subgroupOf L).map π := heq
      rw [heq']
    have hs := glaPComponent_unique h2 h1 hb
    have hJ₂L : J₂ ≤ L := hJ₂.1.trans hHL
    have hJL : J ≤ L := hJ.1.trans hHL
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hJ₂L, inf_eq_left.mpr hJL] at hs
    exact hs
  · rw [hZ, Subgroup.card_bot]
  · rw [Nat.card_congr eQ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl




theorem centralizer_zpowers_eq_singleton {Q : Type*} [Group Q] (g : Q) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup Q) : Set Q) =
      Subgroup.centralizer ({g} : Set Q) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers g))
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hc).symm n).eq


theorem i1425At_holds
    (G : Type) [Group G] [Finite G] : I1425At G := by
  intro X L hL hTW F hFL hF hFc
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.card_eq_one.mp hTW.2
  obtain ⟨e⟩ := nonempty_pquot_equiv_ON hTW.1 hZ
  have e' : PQuot 3 L ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan := e
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := by
    have h := not_dvd_card_glaPPrimeCoreOf hp3 L
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at h
  set π : ↥L →* PQuot 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hπ
  set F' : Subgroup ↥L := F.subgroupOf L
  have hF'p : IsPGroup 3 F' := fun g => ⟨1, Subtype.ext (Subtype.ext (by simpa using hF.2 _ g.2))⟩
  have hinj := injOn_mk_of_isPGroup hp3 (GLAPPrimeCore 3 ↥L) hN hF'p
  have hFb : Nat.card (F'.map π) = 27 := by
    have h := Nat.card_image_of_injOn hinj
    rw [← Subgroup.coe_map] at h
    have h' : Nat.card (F'.map π) = Nat.card F' := h
    rw [h', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFL).toEquiv, hFc]
    norm_num
  obtain ⟨db, hdb, hdbF⟩ := exists_plane_le_of_card e' (hF'p.map π) hFb
  set D₀' : Subgroup ↥L := F' ⊓ (plane db).comap π
  set D₀ : Subgroup G := D₀'.map L.subtype
  have hD₀F : D₀ ≤ F := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hx.1
  have hD₀L : D₀ ≤ L := Subgroup.map_subtype_le _
  have hD₀sub : D₀.subgroupOf L = D₀' :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hD₀bar : D₀'.map π = plane db := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := hdbF hz
      exact ⟨x, ⟨hx, hz⟩, rfl⟩
  have hbarD : barX 3 L D₀ = plane db := by
    unfold barX
    rw [hD₀sub, hD₀bar]
  have hD₀p : IsPGroup 3 D₀ := hF'p.map _ |>.to_le (by
    rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx.1, rfl⟩)
  have hD₀c : Nat.card D₀ = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    have hinj' : Set.InjOn π (D₀' : Set ↥L) := hinj.mono (fun x hx => hx.1)
    have h := Nat.card_image_of_injOn hinj'
    rw [← Subgroup.coe_map] at h
    have h' : Nat.card (D₀'.map π) = Nat.card D₀' := h
    rw [← h', hD₀bar, (plane_facts e' hdb).2.1]
    norm_num
  refine ⟨D₀, hD₀F, hD₀c, ?_, fun d hdD hd1 => ?_⟩
  ·
    refine uniqA6_of_quot hD₀L hD₀p ?_
    rw [hbarD, centralizer_plane e' hdb]
    obtain ⟨A, hA, hAu, hAe, -⟩ := unique_component_centralizer_ON e' hdb
    exact ⟨A, hA, hAu, hAe⟩
  ·
    have hdL : d ∈ L := hD₀L hdD
    have hd3 : d ^ 3 = 1 := hF.2 d (hD₀F hdD)
    have hzp : IsPGroup 3 (Subgroup.zpowers d) := fun g => ⟨1, by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hd3, one_zpow]
      rfl⟩
    have hzL : Subgroup.zpowers d ≤ L := Subgroup.zpowers_le.mpr hdL
    have hcx : L ⊓ cx d = L ⊓ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
      rw [cx, centralizer_zpowers_eq_singleton]
    rw [hcx]
    refine uniqA6_of_quot hzL hzp ?_
    set y : ↥L := ⟨d, hdL⟩
    have hbz : barX 3 L (Subgroup.zpowers d) = Subgroup.zpowers (π y) := by
      unfold barX
      have : (Subgroup.zpowers d).subgroupOf L = Subgroup.zpowers y := by
        apply Subgroup.map_injective L.subtype_injective
        rw [MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hzL]
        rfl
      rw [this, MonoidHom.map_zpowers]
    rw [hbz, centralizer_zpowers_eq_singleton]
    have hy1 : π y ≠ 1 := by
      intro h
      apply hd1
      have hyF : y ∈ F' := Subgroup.mem_subgroupOf.mpr (hD₀F hdD)
      have := hinj hyF F'.one_mem (h.trans (map_one π).symm)
      exact congrArg Subtype.val this
    have hy3 : orderOf (π y) = 3 := orderOf_eq_prime (by
      rw [← map_pow]
      have : y ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, map_one]) hy1
    obtain ⟨A, hA, hAu, hAe, -⟩ := unique_component_centralizer_ON e' hy3
    exact ⟨A, hA, hAu, hAe⟩


end Transfer

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
