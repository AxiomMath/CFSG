module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.CenterCyclic
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212Layer
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212Diag
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup
open CFSG.PreuniquenessRankFour.Helpers
  (odd_pGroup_invariant_noncyclic_pSubgroup_has_invariant_elementary_rank_two)

variable {X : Type} [Group X] [Finite X] {n p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}

theorem mem_pCore_of_mem_center_component [Fact p.Prime]
    (hcore : primeComplementCore (G := X) p = ⊥) {K : Subgroup X} (hK : IsComponentOf K ⊤) {c : X}
    (hcK : c ∈ K) (hcc : ∀ g ∈ K, g * c = c * g) : c ∈ CFSG.pCore p X := by
  have hK' : CFSG.IsComponent K := (CFSG.isComponent_iff_open K).2 hK
  have hc : c ∈ (center K).map K.subtype :=
    (CFSG.LocalCores.mem_map_center_iff K).2 ⟨hcK, mem_centralizer_iff.2 hcc⟩
  exact CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot p hcore
    (CFSG.LocalCores.center_component_le_center_layer hK' hc)

theorem isPGroup_center_component [Fact p.Prime] (hcore : primeComplementCore (G := X) p = ⊥)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : IsPGroup p (center K) := fun g => by
  have hmem : ((g : K) : X) ∈ CFSG.pCore p X :=
    mem_pCore_of_mem_center_component hcore hK (g : K).2 fun w hw =>
      congrArg Subtype.val (mem_center_iff.1 g.2 ⟨w, hw⟩)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := X)) ⟨((g : K) : X), hmem⟩
  have h1 : ((g : K) : X) ^ p ^ k = 1 := by
    simpa using congrArg (Subtype.val : ↥(CFSG.pCore p X) → X) hk
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa using h1))⟩

theorem mem_of_pow_mem_of_pow_prime_eq_one [Fact p.Prime] {u : X} (hup : u ^ p = 1) {b : ℕ}
    (hb : ¬ p ∣ b) {W : Subgroup X} (hW : u ^ b ∈ W) : u ∈ W := by
  have hb0 : (b : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h1 : u = (u ^ b) ^ (((b : ZMod p)⁻¹).val) := by
    rw [← pow_mul]
    refine (pow_one u).symm.trans (pow_eq_pow_of_natCast_eq_of_pow_eq_one hup ?_)
    rw [Nat.cast_one, Nat.cast_mul, ZMod.natCast_zmod_val]
    exact (mul_inv_cancel₀ hb0).symm
  rw [h1]
  exact pow_mem hW _

theorem exists_conj_eq_mul_pow_of_isElemAbelian [Fact p.Prime] {U : Subgroup X}
    (hU : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) {z : X} (hzU : z ∈ U) (hz1 : z ≠ 1)
    {t : X} (ht : ∃ k : ℕ, t ^ p ^ k = 1) (htU : t ∈ normalizer (U : Set X))
    (htz : t * z = z * t) {u : X} (hu : u ∈ U) (huz : u ∉ zpowers z) :
    ∃ b : ℕ, t * u * t⁻¹ = u * z ^ b := by
  have hup : u ^ p = 1 := hU.2 u hu
  have hcu : u * z = z * u := congrArg Subtype.val (hU.1.is_comm.comm ⟨u, hu⟩ ⟨z, hzU⟩)
  obtain ⟨a, b, hab⟩ := exists_pow_mul_pow_of_mem_plane hU hUc hzU hz1 hu huz
    ((mem_normalizer_iff.1 htU u).1 hu)
  obtain ⟨k, hk⟩ := ht
  have ha : (a : ZMod p) = 1 := by
    obtain ⟨β, hβ⟩ := exists_conj_pow_eq_pow_mul_pow hcu htz hab (p ^ k)
    rw [hk, inv_one, mul_one, one_mul] at hβ
    have h1 := natCast_eq_one_of_eq_pow_mul_pow hup huz hβ
    rwa [Nat.cast_pow, ZMod.pow_card_pow] at h1
  exact ⟨b, conj_eq_mul_pow_of_natCast_eq_one hup hab ha⟩

theorem exists_ne_one_mem_centralizer_of_le_normalizer [Fact p.Prime] {U : Subgroup X}
    (hUp : IsPGroup p U) (hUne : U ≠ ⊥) (hDp : IsPGroup p D)
    (hDU : D ≤ normalizer (U : Set X)) :
    ∃ y ∈ U, y ≠ 1 ∧ y ∈ centralizer (D : Set X) := by
  have hB : IsPGroup p (↥(U ⊔ D)) := hUp.to_sup_of_normal_left' hDp hDU
  have hBN : U ⊔ D ≤ normalizer (U : Set X) := sup_le le_normalizer hDU
  haveI : (U.subgroupOf (U ⊔ D)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 hBN
  haveI : Group.IsNilpotent ↥(U ⊔ D) := hB.isNilpotent
  have hne : U.subgroupOf (U ⊔ D) ≠ ⊥ := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    intro hbot
    apply hu1
    have hmem : (⟨u, Subgroup.mem_sup_left u.2⟩ : ↥(U ⊔ D)) ∈ U.subgroupOf (U ⊔ D) := u.2
    rw [hbot, mem_bot] at hmem
    have h2 : ((⟨u, Subgroup.mem_sup_left u.2⟩ : ↥(U ⊔ D)) : X) = ((1 : ↥(U ⊔ D)) : X) :=
      congrArg Subtype.val hmem
    exact Subtype.ext h2
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  refine ⟨(((a : ↥(U.subgroupOf (U ⊔ D) ⊓ center ↥(U ⊔ D))) : ↥(U ⊔ D)) : X), a.2.1, ?_, ?_⟩
  · intro h1
    apply ha1
    exact Subtype.ext (Subtype.ext h1)
  · refine mem_centralizer_iff.2 fun w hw => ?_
    exact congrArg Subtype.val (mem_center_iff.1 a.2.2 ⟨w, Subgroup.mem_sup_right hw⟩)

namespace Lemma212ConfigGe

theorem eq_zpowers_of_ne (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) {T : Subgroup X}
    (hTD : T ≤ D) (hzT : z ∈ T) (hne : T ≠ D) : T = zpowers z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, h.ord]
  have hdvd : Nat.card T ∣ p ^ 2 := h.card ▸ card_dvd_of_le hTD
  obtain ⟨i, hi, hTi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hlt : i < 2 := by
    by_contra hi2
    have h2 : i = 2 := by omega
    exact hne (eq_of_le_of_card_ge hTD (by rw [h.card, hTi, h2]))
  have hle : Nat.card T ≤ Nat.card (zpowers z) := by
    rw [hTi, hcardz]
    calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  exact (eq_of_le_of_card_ge (zpowers_le.2 hzT) hle).symm

theorem inf_pCore_eq_zpowers (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    (hcore : primeComplementCore (G := X) p = ⊥) (hz : z ∈ CFSG.pCore p X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : D ⊓ CFSG.pCore p X = zpowers z := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine h.eq_zpowers_of_ne hp inf_le_left ⟨h.mem, hz⟩ fun hDO => ?_
  have hDle : D ≤ CFSG.pCore p X := hDO ▸ inf_le_right
  obtain ⟨x, hxK, ⟨k, hxk⟩, g0, hg0, hg0x⟩ := (exists_pElement_not_central hp hcore hK).2
  have hxL : x ∈ CFSG.ComponentClassification.Layer.subgroup X :=
    CFSG.ComponentClassification.Layer.component_le hK hxK
  have hxD : x ∈ centralizer (D : Set X) :=
    mem_centralizer_iff.2 fun w hw => (commute_of_mem_pCore_of_mem_layer (hDle hw) hxL).symm
  have hxD' : x ∈ D := h.mem_of_pElement_mem_centralizer hp hxD ⟨k, hxk⟩
  exact hg0x (commute_of_mem_pCore_of_mem_layer (hDle hxD')
    (CFSG.ComponentClassification.Layer.component_le hK hg0))

theorem mem_normalizer_of_mem (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    (hcore : primeComplementCore (G := X) p = ⊥) (hz : z ∈ CFSG.pCore p X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) {w : X} (hw : w ∈ D) : w ∈ normalizer (K : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hwK
  have hwp : w ^ p = 1 := h.elem.2 w hw
  obtain ⟨x, hxK, ⟨k, hxk⟩, g0, hg0, hg0x⟩ := (exists_pElement_not_central hp hcore hK).2
  obtain ⟨y, hyL, hwy, hypow, hycent⟩ := exists_diagonal_of_not_mem_normalizer hp hwp hK hwK hxK
  have hLz : ∀ g ∈ CFSG.ComponentClassification.Layer.subgroup X, g * z = z * g :=
    fun g hg => commute_of_mem_pCore_of_mem_layer hz hg
  have hzC : z ∈ centralizer (K : Set X) :=
    mem_centralizer_iff.2 fun g hg =>
      hLz g (CFSG.ComponentClassification.Layer.component_le hK hg)
  have hzN : z ∈ normalizer (K : Set X) := by
    apply centralizer_le_normalizer
    exact hzC
  have hwz : w ∉ zpowers z := fun hmem => hwK (zpowers_le.2 hzN hmem)
  have hwy' : Commute w y := mul_inv_eq_iff_eq_mul.1 hwy
  have hyz' : Commute y z := hLz y hyL
  have hyD : y ∈ centralizer (D : Set X) := by
    refine mem_centralizer_iff.2 fun v hv => ?_
    obtain ⟨s, t, rfl⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hw hwz hv
    exact ((hwy'.pow_left s).mul_left (hyz'.symm.pow_left t)).eq
  have hyD' : y ∈ D := h.mem_of_pElement_mem_centralizer hp hyD ⟨k, hypow _ hxk⟩
  have hLN : CFSG.ComponentClassification.Layer.subgroup X ≤ normalizer (K : Set X) :=
    (normal_subgroupOf_iff_le_normalizer
      (CFSG.ComponentClassification.Layer.component_le hK)).mp
      (CFSG.ComponentClassification.Layer.normal_component hK)
  obtain ⟨s, t, hyst⟩ :=
    exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hw hwz hyD'
  have hws : w ^ s ∈ normalizer (K : Set X) := by
    rw [(mul_inv_eq_iff_eq_mul.2 hyst).symm]
    exact mul_mem (hLN hyL) (inv_mem (pow_mem hzN t))
  have hs : p ∣ s := by
    by_contra hs
    refine zpow_notMem_normalizer_of_not_dvd hp hwp hwK (s := (s : ℤ)) (by exact_mod_cast hs) ?_
    rwa [zpow_natCast]
  have hws1 : w ^ s = 1 := by
    obtain ⟨m, rfl⟩ := hs
    rw [pow_mul, hwp, one_pow]
  have hyz : y = z ^ t := by rw [hyst, hws1, one_mul]
  have hyc : ∀ g ∈ K, g * y * g⁻¹ = y := by
    intro g hg
    rw [hyz]
    exact mul_inv_eq_iff_eq_mul.2
      ((Commute.pow_right (hLz g (CFSG.ComponentClassification.Layer.component_le hK hg)) t).eq)
  exact hg0x (mul_inv_eq_iff_eq_mul.1 (hycent g0 hg0 (hyc g0 hg0)))

theorem omega_center_le_zpowers (hp : p.Prime) (hp2 : p ≠ 2) (h : Lemma212ConfigGe n p P z D)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections X)
    (hK78 : GL83PElementCentralizesOmegaCenterAt p) (hcore : primeComplementCore (G := X) p = ⊥)
    (hz : z ∈ CFSG.pCore p X) {K : Subgroup X} (hK : IsComponentOf K ⊤) {c : X} (hcK : c ∈ K)
    (hcc : ∀ g ∈ K, g * c = c * g) (hcp : c ^ p = 1) : c ∈ zpowers z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcD : c ∈ centralizer (D : Set X) := by
    refine mem_centralizer_iff.2 fun w hw => ?_
    have hwp : ∃ k : ℕ, w ^ p ^ k = 1 := ⟨1, by simpa using h.elem.2 w hw⟩
    exact mul_inv_eq_iff_eq_mul.1
      (hK78 X hcat K w hp hp2 hK (h.mem_normalizer_of_mem hp hcore hz hK hw) hwp c hcK hcc
        hcp)
  have hcD' : c ∈ D := h.mem_of_pElement_mem_centralizer hp hcD ⟨1, by simpa using hcp⟩
  have hcO : c ∈ CFSG.pCore p X := mem_pCore_of_mem_center_component hcore hK hcK hcc
  have hmem : c ∈ D ⊓ CFSG.pCore p X := ⟨hcD', hcO⟩
  rwa [h.inf_pCore_eq_zpowers hp hcore hz hK] at hmem

theorem mem_center_of_isComponentOf (hp : p.Prime) (hp2 : p ≠ 2) (h : Lemma212ConfigGe n p P z D)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections X)
    (hK78 : GL83PElementCentralizesOmegaCenterAt p) (hcore : primeComplementCore (G := X) p = ⊥)
    (hz : z ∈ CFSG.pCore p X) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    z ∈ K ∧ ∀ g ∈ K, g * z = z * g := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZne := h.center_ne_bot_of_isComponentOf hp hcore hz hK
  have hZp : IsPGroup p (center K) := isPGroup_center_component hcore hK
  haveI : Nontrivial (center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hZne
  obtain ⟨m, hm, hmcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card (center K) := hmcard ▸ dvd_pow_self p hm.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center K) p hdvd
  set u : X := (((c : center K) : K) : X)
  have hu_ord : orderOf u = p :=
    (Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe _).trans hc)
  have hup : u ^ p = 1 := by
    rw [← hu_ord]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu_ord
    exact hp.one_lt.ne hu_ord
  have huK : u ∈ K := ((c : center K) : K).2
  have hucc : ∀ g ∈ K, g * u = u * g := fun g hg =>
    congrArg Subtype.val (mem_center_iff.1 c.2 ⟨g, hg⟩)
  have hmem : u ∈ zpowers z :=
    h.omega_center_le_zpowers hp hp2 hcat hK78 hcore hz hK huK hucc hup
  have heq : zpowers u = zpowers z :=
    zpowers_eq_of_mem_zpowers hup h.z_pow_eq_one hu1 (h.ne_one hp) hmem
  have hzu : z ∈ zpowers u := by
    rw [heq]
    exact mem_zpowers z
  refine ⟨zpowers_le.2 huK hzu, fun g hg => ?_⟩
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hzu
  rw [← hj]
  exact (Commute.zpow_right (show Commute g u from hucc g hg) j).eq

theorem not_le_component (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    (hcore : primeComplementCore (G := X) p = ⊥) {K K' : Subgroup X} (hK : IsComponentOf K ⊤)
    (hK' : IsComponentOf K' ⊤) (hne : K' ≠ K) : ¬ D ≤ K := by
  intro hDK
  obtain ⟨x, hxK', ⟨k, hxk⟩, g0, hg0, hg0x⟩ := (exists_pElement_not_central hp hcore hK').2
  have hcent : K' ≤ centralizer (K : Set X) := commutator_eq_bot_iff_le_centralizer.1
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K hK' hK hne)
  have hxD : x ∈ centralizer (D : Set X) :=
    mem_centralizer_iff.2 fun w hw => mem_centralizer_iff.1 (hcent hxK') w (hDK hw)
  have hxK : x ∈ K := hDK (h.mem_of_pElement_mem_centralizer hp hxD ⟨k, hxk⟩)
  exact hg0x (mem_centralizer_iff.1 (hcent hg0) x hxK).symm

theorem mem_zpowers_of_mem_centralizer (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    {K : Subgroup X} (hzK : z ∈ K) (hDK : ¬ D ≤ K) {u : X} (huK : u ∈ K)
    (huc : u ∈ centralizer (D : Set X)) (hup : ∃ k : ℕ, u ^ p ^ k = 1) : u ∈ zpowers z := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra huz
  have huD : u ∈ D := h.mem_of_pElement_mem_centralizer hp huc hup
  apply hDK
  intro v hv
  obtain ⟨s, t, rfl⟩ :=
    exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) huD huz hv
  exact mul_mem (pow_mem huK s) (pow_mem hzK t)

theorem exists_pElement_transvected (hp : p.Prime) (hp2 : p ≠ 2) (h : Lemma212ConfigGe n p P z D)
    (hcore : primeComplementCore (G := X) p = ⊥) (hz : z ∈ CFSG.pCore p X) {K K' : Subgroup X}
    (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤) (hne : K' ≠ K) (hzK : z ∈ K) {d : X}
    (hd : d ∈ D) (hdz : d ∉ zpowers z) :
    ∃ u ∈ K, u ∉ zpowers z ∧ u ^ p = 1 ∧ ∃ b : ℕ, ¬ p ∣ b ∧ d * u * d⁻¹ = u * z ^ b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hDK : ¬ D ≤ K := h.not_le_component hp hcore hK hK' hne
  have hLz : ∀ g ∈ CFSG.ComponentClassification.Layer.subgroup X, g * z = z * g :=
    fun g hg => commute_of_mem_pCore_of_mem_layer hz hg
  have hKL : K ≤ CFSG.ComponentClassification.Layer.subgroup X :=
    CFSG.ComponentClassification.Layer.component_le hK
  set Q : Subgroup X := (P : Subgroup X) ⊓ K
  have hQp : IsPGroup p Q := P.isPGroup'.to_inf_left
  have hDQ : D ≤ normalizer (Q : Set X) := by
    intro w hw
    have hwP : w ∈ (P : Subgroup X) := h.le hw
    have hwK := h.mem_normalizer_of_mem hp hcore hz hK hw
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨hgP, hgK⟩
      refine ⟨(P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hwP hgP)
        ((P : Subgroup X).inv_mem hwP), (mem_normalizer_iff.mp hwK g).mp hgK⟩
    · rintro ⟨hgP, hgK⟩
      refine ⟨?_, (mem_normalizer_iff.mp hwK g).mpr hgK⟩
      have h1 : g = w⁻¹ * (w * g * w⁻¹) * w := by group
      rw [h1]
      exact (P : Subgroup X).mul_mem
        ((P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem hwP) hgP) hwP
  have hQnc : ¬ IsCyclic Q := by
    have hPS : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup X) ⊤ :=
      (CFSG.ABGLocalTools.isSylowOf_iff).2
        ⟨le_top, P.isPGroup', by simpa [Subgroup.relIndex_top_right] using P.not_dvd_index⟩
    haveI : (CFSG.ComponentClassification.Layer.subgroup X).Normal :=
      CFSG.ComponentClassification.Layer.normal X
    have hS1 := hPS.inf_of_le_normalizer (N := CFSG.ComponentClassification.Layer.subgroup X)
      le_top le_normalizer_of_normal
    have hLN : CFSG.ComponentClassification.Layer.subgroup X ≤ normalizer (K : Set X) :=
      (normal_subgroupOf_iff_le_normalizer hKL).mp
        (CFSG.ComponentClassification.Layer.normal_component hK)
    have hS2 := hS1.inf_of_le_normalizer (N := K) hKL hLN
    rw [inf_assoc, inf_eq_right.2 hKL] at hS2
    obtain ⟨S, hS⟩ := hS2.exists_sylow_eq_subgroupOf
    have hzc : (⟨z, hzK⟩ : K) ∈ center K :=
      mem_center_iff.2 fun g => Subtype.ext (hLz g (hKL g.2))
    have hnc : ¬ IsCyclic (S : Subgroup K) :=
      not_isCyclic_sylow_of_isPerfect ⟨hK.2.2.1⟩ S hzc
        (fun h1 => h.ne_one hp (congrArg Subtype.val h1)) (Subtype.ext h.z_pow_eq_one)
    intro hcyc
    apply hnc
    rw [hS]
    exact (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ≤ K)).isCyclic.mpr hcyc
  obtain ⟨U, hUQ, hDU, hUe, hUc⟩ :=
    odd_pGroup_invariant_noncyclic_pSubgroup_has_invariant_elementary_rank_two
      p hp2 D Q h.isPGroup hQp hDQ hQnc
  have hUp : IsPGroup p U := IsPGroup.of_card hUc
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hUc
    nlinarith [hp.one_lt]
  obtain ⟨y, hyU, hy1, hyC⟩ :=
    exists_ne_one_mem_centralizer_of_le_normalizer (D := D) hUp hUne h.isPGroup hDU
  have hyK : y ∈ K := (hUQ hyU).2
  have hyz : y ∈ zpowers z :=
    h.mem_zpowers_of_mem_centralizer hp hzK hDK hyK hyC ⟨1, by simpa using hUe.2 y hyU⟩
  have hzU : z ∈ U := by
    have heq : zpowers y = zpowers z :=
      zpowers_eq_of_mem_zpowers (hUe.2 y hyU) h.z_pow_eq_one hy1 (h.ne_one hp) hyz
    have hzy : z ∈ zpowers y := by
      rw [heq]
      exact mem_zpowers z
    exact zpowers_le.2 hyU hzy
  obtain ⟨u, huU, huz⟩ : ∃ u ∈ U, u ∉ zpowers z := by
    by_contra hno
    push Not at hno
    have hcard := card_le_of_le (show U ≤ zpowers z from fun x hx => hno x hx)
    rw [hUc, Nat.card_zpowers, h.ord] at hcard
    nlinarith [hp.two_le]
  have hdz' : d * z = z * d :=
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨d, hd⟩ ⟨z, h.mem⟩)
  obtain ⟨b, hb⟩ := exists_conj_eq_mul_pow_of_isElemAbelian hUe hUc hzU (h.ne_one hp)
    ⟨1, by simpa using h.elem.2 d hd⟩ (hDU hd) hdz' huU huz
  have huK : u ∈ K := (hUQ huU).2
  refine ⟨u, huK, huz, hUe.2 u huU, b, ?_, hb⟩
  intro hdvd
  apply huz
  have hzb : z ^ b = 1 := by
    obtain ⟨m, rfl⟩ := hdvd
    rw [pow_mul, h.z_pow_eq_one, one_pow]
  rw [hzb, mul_one] at hb
  refine h.mem_zpowers_of_mem_centralizer hp hzK hDK huK ?_ ⟨1, by simpa using hUe.2 u huU⟩
  refine mem_centralizer_iff.2 fun v hv => ?_
  obtain ⟨s, t, rfl⟩ :=
    exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hd hdz hv
  have hud : Commute d u := mul_inv_eq_iff_eq_mul.1 hb
  have huz' : Commute z u := (hLz u (hKL huK)).symm
  exact ((hud.pow_left s).mul_left (huz'.pow_left t)).eq

theorem false_of_two_components (hp : p.Prime) (hp2 : p ≠ 2) (h : Lemma212ConfigGe n p P z D)
    (hcore : primeComplementCore (G := X) p = ⊥) (hz : z ∈ CFSG.pCore p X)
    (hΩ : ∀ K : Subgroup X, IsComponentOf K ⊤ → ∀ c ∈ K, (∀ g ∈ K, g * c = c * g) →
      c ^ p = 1 → c ∈ zpowers z)
    (hzK : ∀ K : Subgroup X, IsComponentOf K ⊤ → z ∈ K) {K₁ K₂ : Subgroup X}
    (hK₁ : IsComponentOf K₁ ⊤) (hK₂ : IsComponentOf K₂ ⊤) (hne : K₁ ≠ K₂) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hdz⟩ := h.exists_mem_notMem_zpowers hp
  obtain ⟨u₁, hu₁K, hu₁z, hu₁p, b₁, -, hdu₁⟩ :=
    h.exists_pElement_transvected hp hp2 hcore hz hK₁ hK₂ hne.symm (hzK K₁ hK₁) hd hdz
  obtain ⟨u₂, hu₂K, -, hu₂p, b₂, hb₂, hdu₂⟩ :=
    h.exists_pElement_transvected hp hp2 hcore hz hK₂ hK₁ hne (hzK K₂ hK₂) hd hdz
  have hDK₁ : ¬ D ≤ K₁ := h.not_le_component hp hcore hK₁ hK₂ hne.symm
  have hLz : ∀ g ∈ CFSG.ComponentClassification.Layer.subgroup X, g * z = z * g :=
    fun g hg => commute_of_mem_pCore_of_mem_layer hz hg
  have hu₁z' : Commute u₁ z :=
    hLz u₁ (CFSG.ComponentClassification.Layer.component_le hK₁ hu₁K)
  have hu₂z' : Commute u₂ z :=
    hLz u₂ (CFSG.ComponentClassification.Layer.component_le hK₂ hu₂K)
  have hc12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K₁ K₂ hK₁ hK₂ hne) ha) b
      hb).symm
  have hu₁u₂ : Commute u₁ u₂ := hc12 u₁ hu₁K u₂ hu₂K
  set e : X := z ^ (b₁ * b₂)
  have hA : d * u₁ ^ b₂ * d⁻¹ = u₁ ^ b₂ * e := by
    rw [← conj_pow, hdu₁, (hu₁z'.pow_right b₁).mul_pow, ← pow_mul]
  have hB : d * u₂ ^ b₁ * d⁻¹ = u₂ ^ b₁ * e := by
    rw [← conj_pow, hdu₂, (hu₂z'.pow_right b₂).mul_pow, ← pow_mul, mul_comm b₂ b₁]
  set a : X := u₁ ^ b₂ * (u₂ ^ b₁)⁻¹ with ha
  have hda : d * a * d⁻¹ = a := by
    have h1 : d * a * d⁻¹ = (d * u₁ ^ b₂ * d⁻¹) * (d * u₂ ^ b₁ * d⁻¹)⁻¹ := by
      simp only [ha]; group
    rw [h1, hA, hB, ha]
    group
  have haz : Commute a z := (hu₁z'.pow_left b₂).mul_left (hu₂z'.pow_left b₁).inv_left
  have hacent : a ∈ centralizer (D : Set X) := by
    refine mem_centralizer_iff.2 fun v hv => ?_
    obtain ⟨s, t, rfl⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hd hdz hv
    have hda' : Commute d a := mul_inv_eq_iff_eq_mul.1 hda
    exact ((hda'.pow_left s).mul_left (haz.symm.pow_left t)).eq
  have hcomm : Commute (u₁ ^ b₂) (u₂ ^ b₁)⁻¹ := (hu₁u₂.pow_pow b₂ b₁).inv_right
  have hap : a ^ p = 1 := by
    rw [ha, hcomm.mul_pow, inv_pow, ← pow_mul, mul_comm b₂ p, pow_mul, hu₁p, one_pow, ← pow_mul,
      mul_comm b₁ p, pow_mul, hu₂p, one_pow, inv_one, mul_one]
  have haD : a ∈ D := h.mem_of_pElement_mem_centralizer hp hacent ⟨1, by simpa using hap⟩
  by_cases haz' : a ∈ zpowers z
  · have hAK₂ : u₁ ^ b₂ ∈ K₂ := by
      have h1 : u₁ ^ b₂ = a * u₂ ^ b₁ := by simp [ha]
      rw [h1]
      exact mul_mem (zpowers_le.2 (hzK K₂ hK₂) haz') (pow_mem hu₂K b₁)
    have hAK₁ : u₁ ^ b₂ ∈ K₁ := pow_mem hu₁K b₂
    have hAp : (u₁ ^ b₂) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu₁p, one_pow]
    have hAz : u₁ ^ b₂ ∈ zpowers z :=
      hΩ K₁ hK₁ _ hAK₁ (fun g hg => hc12 g hg _ hAK₂) hAp
    exact hu₁z (mem_of_pow_mem_of_pow_prime_eq_one hu₁p hb₂ hAz)
  · apply hu₁z
    refine h.mem_zpowers_of_mem_centralizer hp (hzK K₁ hK₁) hDK₁ hu₁K ?_ ⟨1, by simpa using hu₁p⟩
    refine mem_centralizer_iff.2 fun v hv => ?_
    obtain ⟨s, t, rfl⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) haD haz' hv
    have hu₁a : Commute u₁ a :=
      ((Commute.refl u₁).pow_right b₂).mul_right ((hu₁u₂.pow_right b₁).inv_right)
    exact ((hu₁a.symm.pow_left s).mul_left (hu₁z'.symm.pow_left t)).eq

theorem exists_component (hp : p.Prime) (hp2 : p ≠ 2) (h : Lemma212ConfigGe n p P z D)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections X)
    (hK78 : GL83PElementCentralizesOmegaCenterAt p) (hcore : primeComplementCore (G := X) p = ⊥)
    (hnc : ¬ ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set X) ≤ Q)
    (hpc : CFSG.pCore p X ≠ ⊥) :
    ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ L.Normal ∧
      (∀ K : Subgroup X, IsComponentOf K ⊤ → K = L) ∧ z ∈ L ∧ (∀ g ∈ L, g * z = z * g) ∧
      D ≤ normalizer (L : Set X) ∧ center L ≠ ⊥ ∧ IsPGroup p (center L) ∧ IsCyclic (center L) ∧
      (∀ c ∈ L, (∀ g ∈ L, g * c = c * g) → c ^ p = 1 → c ∈ zpowers z) ∧
      ∀ x ∈ L ⊓ centralizer (D : Set X), (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ D := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : z ∈ CFSG.pCore p X := h.mem_pCore_of_pCore_ne_bot hp hpc
  obtain ⟨L, hL⟩ := exists_isComponentOf_of_layer_ne_bot
    (layer_ne_bot_of_not_exists_selfCentralizing hcore hnc)
  have hΩ : ∀ K : Subgroup X, IsComponentOf K ⊤ → ∀ c ∈ K, (∀ g ∈ K, g * c = c * g) →
      c ^ p = 1 → c ∈ zpowers z := fun K hK c hcK hcc hcp =>
    h.omega_center_le_zpowers hp hp2 hcat hK78 hcore hz hK hcK hcc hcp
  have hzK : ∀ K : Subgroup X, IsComponentOf K ⊤ → z ∈ K ∧ ∀ g ∈ K, g * z = z * g :=
    fun K hK => h.mem_center_of_isComponentOf hp hp2 hcat hK78 hcore hz hK
  have huniq : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = L := fun K hK => by
    by_contra hne
    exact h.false_of_two_components hp hp2 hcore hz hΩ (fun K' hK' => (hzK K' hK').1) hK hL hne
  have hLn : L.Normal := by
    refine normal_iff_map_conj_eq.2 fun g => ?_
    exact huniq _ (isComponentOf_map_conj g hL)
  refine ⟨L, hL, hLn, huniq, (hzK L hL).1, (hzK L hL).2,
    fun w hw => h.mem_normalizer_of_mem hp hcore hz hL hw,
    h.center_ne_bot_of_isComponentOf hp hcore hz hL, isPGroup_center_component hcore hL, ?_,
    hΩ L hL, fun x hx hxp => h.mem_of_pElement_mem_centralizer hp hx.2 hxp⟩
  by_contra hnc'
  obtain ⟨B, hB, hBc⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (hp.odd_of_ne_two hp2) (isPGroup_center_component hcore hL) hnc'
  haveI := hB
  have hf : ∀ b : B, (((b : center L) : L) : X) ∈ zpowers z := fun b => by
    refine hΩ L hL _ ((b : center L) : L).2
      (fun g hg => congrArg Subtype.val (mem_center_iff.1 (b : center L).2 ⟨g, hg⟩)) ?_
    have h1 : b ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p B) b
    simpa using congrArg (fun x : B => (((x : center L) : L) : X)) h1
  let f : B → zpowers z := fun b => ⟨(((b : center L) : L) : X), hf b⟩
  have hfi : Function.Injective f := fun b₁ b₂ h12 => by
    have h2 : (((b₁ : center L) : L) : X) = (((b₂ : center L) : L) : X) :=
      congrArg (Subtype.val : ↥(zpowers z) → X) h12
    exact Subtype.ext (Subtype.ext (Subtype.ext h2))
  have hcard := Nat.card_le_card_of_injective f hfi
  rw [hBc, Nat.card_zpowers, h.ord] at hcard
  nlinarith [hp.two_le]

section CertificateInstances

theorem exists_component_of_five_le (hp : p.Prime) (hp5 : 5 ≤ p) (h : Lemma212ConfigGe n p P z D)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections X)
    (hcore : primeComplementCore (G := X) p = ⊥)
    (hnc : ¬ ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set X) ≤ Q)
    (hpc : CFSG.pCore p X ≠ ⊥) :
    ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ L.Normal ∧
      (∀ K : Subgroup X, IsComponentOf K ⊤ → K = L) ∧ z ∈ L ∧ (∀ g ∈ L, g * z = z * g) ∧
      D ≤ normalizer (L : Set X) ∧ center L ≠ ⊥ ∧ IsPGroup p (center L) ∧ IsCyclic (center L) ∧
      (∀ c ∈ L, (∀ g ∈ L, g * c = c * g) → c ^ p = 1 → c ∈ zpowers z) ∧
      ∀ x ∈ L ⊓ centralizer (D : Set X), (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ D :=
  h.exists_component hp (by omega) hcat (gl83PElementCentralizesOmegaCenterAt_of_five_le hp5)
    hcore hnc hpc

end CertificateInstances

end Lemma212ConfigGe

end CFSG.LocalAnalysis.RankFourTheoremC
