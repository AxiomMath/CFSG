module

public import CFSG.Assembly.OddCoreEliminationStatements
public import CFSG.Assembly.OddCoreElimination.RankOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type*} [Group G]

private theorem isElemAbelian_of_le {p : ℕ} {E X : Subgroup G} (hE : IsElemAbelian p E)
    (hXE : X ≤ E) : IsElemAbelian p X := CFSG.Open.IsElemAbelian.mono hE hXE

private theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (K : Subgroup G)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE K

private theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

private theorem mem_sylow_of_commute {X : Type*} [Group X] {z : X}
    (hz : ∀ g : X, Commute g z) (hzo : orderOf z = 2) (T : Sylow 2 X) : z ∈ T := by
  have : (Subgroup.zpowers z).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((hz g).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers z k⟩
  have hP : IsPGroup 2 (Subgroup.zpowers z) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, hzo]
  exact hP.le_sylow_of_normal T (Subgroup.mem_zpowers z)

private theorem mem_sylow_centralizer {t : G}
    (T : Sylow 2 (Subgroup.centralizer ({t} : Set G))) (ht : orderOf t = 2) :
    (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({t} : Set G)) ∈ T :=
  mem_sylow_of_commute (fun g => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2))
    ((Subgroup.orderOf_coe _).symm.trans ht) T

private theorem pullback_facts {C X : Type*} [Group C] [Group X] (π : C →* X)
    (T : Subgroup C) (hinj : ∀ x ∈ T, ∀ y ∈ T, π x = π y → x = y) (Y : Subgroup X)
    (hY : Y ≤ T.map π) :
    (Y.comap π ⊓ T).map π = Y ∧ Nat.card (Y.comap π ⊓ T : Subgroup C) = Nat.card Y ∧
      (IsElemAbelian 2 Y → IsElemAbelian 2 (Y.comap π ⊓ T)) := by
  have hmap : (Y.comap π ⊓ T).map π = Y := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le π Y)
    · intro y hy
      obtain ⟨x, hxT, rfl⟩ := hY hy
      exact ⟨x, ⟨hy, hxT⟩, rfl⟩
  have hφ : Function.Injective (π.comp (Y.comap π ⊓ T).subtype) := fun a b hab =>
    Subtype.ext (hinj a a.2.2 b b.2.2 hab)
  have hrange : (π.comp (Y.comap π ⊓ T).subtype).range = Y := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  refine ⟨hmap, (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).trans (by rw [hrange]),
    fun hYe => ⟨⟨⟨fun a b => hφ ?_⟩⟩, fun x hx => ?_⟩⟩
  · rw [map_mul, map_mul]
    exact congrArg (fun y : Y => (y : X)) (hYe.1.is_comm.comm ⟨π a, a.2.1⟩ ⟨π b, b.2.1⟩)
  · apply hinj _ (T.pow_mem hx.2 2) 1 T.one_mem
    rw [map_pow, map_one]
    exact hYe.2 (π x) hx.1

private theorem centralizer_conj_eq (g t : G) :
    Subgroup.centralizer ({g * t * g⁻¹} : Set G) =
      (Subgroup.centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * x) * g := by rw [h]
      _ = t * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * t * g⁻¹) = g * (g⁻¹ * x * g * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * x := by group

private theorem centralizer_le_normalizer_of_sylow_le
    (hcov : PerfectInvolutionCoverageStatement) {G : Type} [Group G] [Finite G]
    (hperf : commutator G = ⊤) (hrank : 3 ≤ twoRank G) (hcomp : ¬ IsComponentType G)
    (S : Sylow 2 G) (W : Subgroup G) (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G))
    (hspan : ∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 → oddCoreSpan V = W)
    (t : G) (ht : orderOf t = 2) (T : Subgroup G)
    (hTC : T ≤ Subgroup.centralizer ({t} : Set G)) (hTS : T ≤ S)
    (hTcard : Nat.card T =
      2 ^ (Nat.card (Subgroup.centralizer ({t} : Set G))).factorization 2) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  set M := Subgroup.normalizer (W : Set G) with hMdef
  have hWM : W ≤ M := Subgroup.le_normalizer
  set TC : Subgroup C := T.subgroupOf C with hTCdef
  have hTCcard : Nat.card TC = 2 ^ (Nat.card C).factorization 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv).trans hTcard
  let TS : Sylow 2 C := Sylow.ofCard TC hTCcard
  have htT : t ∈ T := mem_sylow_centralizer TS ht
  have htS : t ∈ (S : Subgroup G) := hTS htT
  set O := oddCore C with hOdef
  have hOodd : Odd (Nat.card O) := odd_card_oddCore C
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hTO : Disjoint TC O := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hTCcard]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hOodd)
  have hinj : ∀ x ∈ TC, ∀ y ∈ TC, π x = π y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ O := QuotientGroup.eq.mp hxy
    exact inv_mul_eq_one.mp
      (Subgroup.disjoint_def.mp hTO (TC.mul_mem (TC.inv_mem hx) hy) hmem)
  have hchar : dichotomyCharP 2 (C ⧸ O) :=
    (CFSG.Milestones.cls_component_free_centralizer_quotient_characteristic_two G hcomp t ht).1
  obtain ⟨E, hE, hE8, htE⟩ := hcov G hperf hrank t ht
  have hEC : E ≤ C := by
    intro e he
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun x : E => (x : G)) (hE.1.is_comm.comm ⟨e, he⟩ ⟨t, htE⟩)
  have hrankq : 3 ≤ twoRank (C ⧸ O) := by
    have hq := CFSG.SectionRank.pRank_quotient_eq (p := 2) O
      (fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h))
    have hE'card : Nat.card (E.subgroupOf C) = 2 ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hE8]
      norm_num
    have h3 : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup C) :=
      CFSG.SectionRank.le_pRank one_lt_two le_top (isElemAbelian_subgroupOf C hE) hE'card
    change 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (C ⧸ O))
    rw [hq]
    exact h3
  have hQrank : 2 ≤ pRank 2 (pCore 2 (C ⧸ O)) := two_le_pRank_pCore_of_charP_two _ hchar hrankq
  set Q := pCore 2 (C ⧸ O) with hQdef
  have hQn : Q.Normal := by rw [hQdef]; infer_instance
  have hQp : IsPGroup 2 Q := by rw [hQdef]; exact CFSG.pCore_isPGroup
  obtain ⟨Vb, hVbQ, hVb, hVb4⟩ : ∃ Vb : Subgroup (C ⧸ O), Vb ≤ Q ∧ IsElemAbelian 2 Vb ∧
      Nat.card Vb = 4 := by
    obtain ⟨E', hE'Q, hE', hE'card⟩ := CFSG.SectionRank.exists_pRank one_lt_two Q
    obtain ⟨K, hK4, -, hKE'⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
      (n := 2) (H := ⊥) (L := E') (by simp) (by rw [hE'card]; exact pow_dvd_pow 2 hQrank)
      bot_le
    exact ⟨K, hKE'.trans hE'Q, isElemAbelian_of_le hE' hKE', by rw [hK4]; norm_num⟩
  have hQle : Q ≤ TC.map π := hQp.le_sylow_of_normal (TS.mapSurjective hπ)
  obtain ⟨-, hRcard, -⟩ := pullback_facts π TC hinj Q hQle
  obtain ⟨-, hVcard, hVel⟩ := pullback_facts π TC hinj Vb (hVbQ.trans hQle)
  set F : Subgroup C := Q.comap π with hFdef
  set R : Subgroup C := F ⊓ TC with hRdef
  set VC : Subgroup C := Vb.comap π ⊓ TC with hVCdef
  have hVCR : VC ≤ R := inf_le_inf_right TC (Subgroup.comap_mono hVbQ)
  have hRT : R.map C.subtype ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  set VG : Subgroup G := VC.map C.subtype with hVGdef
  have hVG : IsElemAbelian 2 VG := CFSG.SectionRank.isElemAbelian_map (hVel hVb) C.subtype
  have hVG4 : Nat.card VG = 4 := by
    rw [hVGdef, Subgroup.card_map_of_injective C.subtype_injective, hVcard, hVb4]
  have hVGS : VG ≤ S := (Subgroup.map_mono hVCR).trans (hRT.trans hTS)
  obtain ⟨Vt, hVtS, hVt, hVt4, htVt⟩ : ∃ Vt : Subgroup G, Vt ≤ S ∧ IsElemAbelian 2 Vt ∧
      Nat.card Vt = 4 ∧ t ∈ Vt := by
    have hnot : ¬ VG ≤ Subgroup.zpowers t := by
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [hVG4, Nat.card_zpowers, ht] at this
      omega
    obtain ⟨v, hvVG, hvt⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    have hv1 : v ≠ 1 := fun h => hvt (h ▸ Subgroup.one_mem _)
    have hv : orderOf v = 2 := orderOf_eq_prime (hVG.2 v hvVG) hv1
    have hvC : v ∈ C := Subgroup.map_subtype_le VC hvVG
    have hcomm : Subgroup.zpowers t ≤ Subgroup.centralizer (Subgroup.zpowers v : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      have hvt' : Commute v t := Subgroup.mem_centralizer_singleton_iff.mp hvC
      exact (hvt'.zpow_left k).eq
    obtain ⟨Vt, htle, -, hVt, hVt4, hVtle⟩ :=
      CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
        (firstRank := 1) (secondRank := 1) (Subgroup.zpowers t) (Subgroup.zpowers v)
        (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary t ht)
        (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary v hv)
        (by rw [Nat.card_zpowers, ht, pow_one]) (by rw [Nat.card_zpowers, hv, pow_one]) hcomm
        (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint _ v hv hvt)
    refine ⟨Vt, hVtle.trans (sup_le ?_ ?_), hVt, by rw [hVt4]; norm_num,
      htle (Subgroup.mem_zpowers t)⟩
    · exact Subgroup.zpowers_le.mpr htS
    · exact Subgroup.zpowers_le.mpr (hVGS hvVG)
  have hOW : O.map C.subtype ≤ W := by
    have h := involutionOddCore_le_span Vt htVt (fun h1 => by
      rw [h1, orderOf_one] at ht
      exact absurd ht (by decide))
    rw [hspan Vt hVtS hVt hVt4] at h
    exact h
  have hFM : F ≤ M.comap C.subtype := by
    intro f hf
    obtain ⟨x, hxT, hx⟩ := hQle hf
    have hxf : x⁻¹ * f ∈ O := QuotientGroup.eq.mp hx
    have hmem := M.mul_mem (hSW (hTS hxT)) (hWM (hOW ⟨_, hxf, rfl⟩))
    show (f : G) ∈ M
    simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      mul_inv_cancel_left] using hmem
  have hNM : Subgroup.normalizer (R : Set C) ≤ M.comap C.subtype := by
    intro h hh
    have hconjS : VG.map (MulAut.conj (h : G)⁻¹).toMonoidHom ≤ S := by
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have hvR : h⁻¹ * v * h ∈ R := (Subgroup.mem_normalizer_iff''.mp hh v).mp (hVCR hv)
      have hmem := hTS (hRT ⟨_, hvR, rfl⟩)
      simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmem
    have hconj4 : Nat.card (VG.map (MulAut.conj (h : G)⁻¹).toMonoidHom) = 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hVG4]
    have hW := hspan _ hconjS (CFSG.SectionRank.isElemAbelian_map hVG _) hconj4
    rw [oddCoreSpan_conj, hspan VG hVGS hVG hVG4] at hW
    have hinv : (h : G)⁻¹ ∈ M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
        simpa only [MulEquiv.toMonoidHom_eq_coe] using hW)
    exact M.inv_mem_iff.mp hinv
  have hFn : F.Normal := hQn.comap π
  have hRF : R ≤ F := inf_le_left
  have hRp : IsPGroup 2 (R.subgroupOf F) := (TS.isPGroup'.to_le inf_le_right).comap_subtype
  have hRidx : ¬ 2 ∣ (R.subgroupOf F).index := by
    have h1 := Subgroup.card_mul_index (R.subgroupOf F)
    have hRF' : Nat.card (R.subgroupOf F) = Nat.card Q :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv).trans hRcard
    have hFcard : Nat.card F = Nat.card O * Nat.card Q :=
      QuotientGroup.card_preimage_mk O (Q : Set (C ⧸ O))
    rw [hRF', hFcard, mul_comm (Nat.card O)] at h1
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h1]
    exact fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  let RS : Sylow 2 F := hRp.toSylow hRidx
  have hfr := Sylow.normalizer_sup_eq_top RS
  have hRS : (RS : Subgroup F).map F.subtype = R := by
    change (R.subgroupOf F).map F.subtype = R
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hRF]
  rw [hRS] at hfr
  have htop : (⊤ : Subgroup C) ≤ M.comap C.subtype := hfr ▸ sup_le hNM hFM
  intro c hc
  exact htop (Subgroup.mem_top (⟨c, hc⟩ : C))

private theorem centralizer_le_normalizer_of_involution
    (hcov : PerfectInvolutionCoverageStatement) {G : Type} [Group G] [Finite G]
    (hperf : commutator G = ⊤) (hrank : 3 ≤ twoRank G) (hcomp : ¬ IsComponentType G)
    (S : Sylow 2 G) (W : Subgroup G) (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G))
    (hspan : ∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 → oddCoreSpan V = W)
    (hfusion : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (W : Set G) → IsPGroup 2 P →
      ∀ g : G, P.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.normalizer (W : Set G) →
      ∃ m ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ P, g⁻¹ * x * g = m⁻¹ * x * m)
    (t : G) (htM : t ∈ Subgroup.normalizer (W : Set G)) (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  set M := Subgroup.normalizer (W : Set G) with hMdef
  obtain ⟨T0⟩ : Nonempty (Sylow 2 C) := inferInstance
  set T₁ : Subgroup G := (T0 : Subgroup C).map C.subtype with hT₁def
  have hT₁card : Nat.card T₁ = 2 ^ (Nat.card C).factorization 2 := by
    rw [hT₁def, Subgroup.card_map_of_injective C.subtype_injective]
    exact T0.card_eq_multiplicity
  have htT₁ : t ∈ T₁ := ⟨_, mem_sylow_centralizer T0 ht, rfl⟩
  obtain ⟨S', hS'⟩ := (T0.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have hmapS : ∀ x ∈ (S' : Subgroup G), g * x * g⁻¹ ∈ (S : Subgroup G) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    have hmem := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S' : Subgroup G) hx
    rwa [MulAut.smul_def, MulAut.conj_apply] at hmem
  have ht' : orderOf (g * t * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hC' := centralizer_conj_eq g t
  have hC'M : Subgroup.centralizer ({g * t * g⁻¹} : Set G) ≤ M := by
    apply centralizer_le_normalizer_of_sylow_le hcov hperf hrank hcomp S W hSW hspan
      (g * t * g⁻¹) ht' (T₁.map (MulAut.conj g).toMonoidHom)
    · rw [hC']
      exact Subgroup.map_mono (Subgroup.map_subtype_le _)
    · rintro _ ⟨x, hx, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmapS x (hS' hx)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hT₁card, hC',
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hPM : Subgroup.zpowers t ≤ M := Subgroup.zpowers_le.mpr htM
  have hPp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hPmap : (Subgroup.zpowers t).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ M := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    apply hSW
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      hmapS t (hS' htT₁)
  obtain ⟨m, hmM, hm⟩ := hfusion _ hPM hPp g⁻¹ hPmap
  have htm : g * t * g⁻¹ = m⁻¹ * t * m := by
    simpa only [inv_inv] using hm t (Subgroup.mem_zpowers t)
  intro c hc
  have hc' : m⁻¹ * c * m ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, htm]
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc m⁻¹ * c * m * (m⁻¹ * t * m) = m⁻¹ * (c * t) * m := by group
      _ = m⁻¹ * (t * c) * m := by rw [hct]
      _ = m⁻¹ * t * m * (m⁻¹ * c * m) := by group
  have hmem := M.mul_mem (M.mul_mem hmM (hC'M hc')) (M.inv_mem hmM)
  have hc'' : m * (m⁻¹ * c * m) * m⁻¹ = c := by group
  rwa [hc''] at hmem

theorem commonSpanStrongEmbedding_of_coverage (hcov : PerfectInvolutionCoverageStatement) :
    CommonSpanStrongEmbeddingStatement := by
  intro G _ _ hperf hrank hcomp S W hSW hMtop hspan hfusion
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (W : Set G) with hMdef
  have hcent : ∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≤ M :=
    fun t htM ht => centralizer_le_normalizer_of_involution hcov hperf hrank hcomp S W hSW
      hspan hfusion t htM ht
  refine ⟨hcent, hMtop, ?_, ?_⟩
  ·
    have h3 : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := hrank
    obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two (⊤ : Subgroup G)
    have h2G : 2 ∣ Nat.card G := by
      have h1 : 2 ∣ Nat.card E := by
        rw [hEcard]
        exact dvd_pow_self 2 (by omega)
      exact h1.trans (Subgroup.card_subgroup_dvd_card E)
    exact even_iff_two_dvd.mpr
      ((S.dvd_card_of_dvd_card h2G).trans (Subgroup.card_dvd_of_le hSW))
  ·
    intro g hg
    by_contra hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    have hxo : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have hxM : (x : G) ∈ M := x.2.1
    have hxMg : (x : G) ∈ M.map (MulAut.conj g⁻¹).toMonoidHom := x.2.2
    set u := g * (x : G) * g⁻¹ with hudef
    have huM : u ∈ M := by
      have hmem := Subgroup.mem_map_equiv.mp hxMg
      rwa [MulAut.conj_symm_apply, inv_inv] at hmem
    have hu : orderOf u = 2 := by
      rw [hudef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hxo]
    have hPM : Subgroup.zpowers u ≤ M := Subgroup.zpowers_le.mpr huM
    have hPp : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
    have hux : g⁻¹ * u * g = x := by rw [hudef]; group
    have hPmap : (Subgroup.zpowers u).map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv, hux]
      exact hxM
    obtain ⟨m, hmM, hm⟩ := hfusion _ hPM hPp g hPmap
    have hgm : g * m⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
      have h := hm u (Subgroup.mem_zpowers u)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * m⁻¹ * u = g * (m⁻¹ * u * m) * m⁻¹ := by group
        _ = g * (g⁻¹ * u * g) * m⁻¹ := by rw [h]
        _ = u * (g * m⁻¹) := by group
    have hmem := M.mul_mem (hcent u huM hu hgm) hmM
    rw [inv_mul_cancel_right] at hmem
    exact hg hmem

end CFSG.Assembly.Dichotomy
