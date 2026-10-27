module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Transfer
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Exp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_PComp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_J0
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux2
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Eighteen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup Equiv
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactZJFactorizationGe : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
    CFSG.AGLEmbedding.CatalogSimpleSections X →
    centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    ∀ K : Subgroup X, K.Normal → CFSG.IsPComponent p K →
    (∃ T : Sylow 2 X, K ⊔ (T : Subgroup X) = ⊤) →
    ¬ 3 ∣ Nat.card (⁅K, (CFSG.pPrimeCore p K).map K.subtype⁆ : Subgroup X) →
    (∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal) →
    ∀ S : Subgroup X, IsPGroup 2 S → CFSG.pCore 2 X ≤ S →
    (∀ Z : Subgroup X, Z ≤ S → Z ≠ ⊥ → (Z.subgroupOf S).Characteristic →
      ¬ K ≤ normalizer (Z : Set X) ⊔ CFSG.pPrimeCore p X) →
    IsChevTwo ((↥K ⧸ CFSG.pPrimeCore p ↥K) ⧸ center (↥K ⧸ CFSG.pPrimeCore p ↥K)) ∨
      ∃ n : ℕ, Nonempty ((↥K ⧸ CFSG.pPrimeCore p ↥K) ⧸ center (↥K ⧸ CFSG.pPrimeCore p ↥K) ≃*
        alternatingGroup (Fin n))

structure ZJFrameGe (p : ℕ) {Y : Type} [Group Y] [Finite Y] (K D V : Subgroup Y) [K.Normal] :
    Prop where
  pre : ThompsonPreFrame p K D
  exists_component : ∃ L : Subgroup (Y ⧸ K), CFSG.IsComponent L ∧
    p ∣ Nat.card (L ⧸ center L) ∧ IsCatalogGroup (L ⧸ center L)
  sections : CFSG.AGLEmbedding.CatalogSimpleSections Y
  three : 5 ≤ p → ∀ Q : Subgroup Y, IsPGroup 3 Q → D ≤ normalizer (Q : Set Y) →
    D ⊓ centralizer (Q : Set Y) = ⊥ →
    ¬ p ∣ Nat.card (invariantTwoJoinIn D (normalizer (Q : Set Y)))
  charTwo : centralizer (CFSG.pCore 2 Y : Set Y) ≤ CFSG.pCore 2 Y
  sylow2 : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 Y) K
  V_two : IsPGroup 2 V
  D_norm : D ≤ normalizer (V : Set Y)
  core_le : CFSG.pCore 2 Y ≤ V
  noncover : ∀ Z : Subgroup Y, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
    ¬ p ∣ Nat.card (invariantTwoJoinIn D (normalizer (Z : Set Y)))
  exp : NormalizerExponent p D

theorem zj_applyGe {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hK1 : KFactZJFactorizationGe) (hsec : CFSG.AGLEmbedding.CatalogSimpleSections Y)
    (hcharTwo : centralizer (CFSG.pCore 2 Y : Set Y) ≤ CFSG.pCore 2 Y)
    (hrkp : ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E ≤ p ^ 2)
    (hsylow : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 Y) (CFSG.pPrimeCore p Y))
    {J V : Subgroup Y} (hJn : J.Normal) (hJc : CFSG.IsPComponent p J)
    {L : Subgroup (Y ⧸ CFSG.pPrimeCore p Y)} (hLs : IsSimpleGroup L)
    (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hLn : L.Normal) (hLc : centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) = ⊥)
    (hJL : J.map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = L)
    (hJp : pElementSubgroup p J = J) (hV : IsPGroup 2 V) (hcore : CFSG.pCore 2 Y ≤ V)
    (hJ0 : ¬ 3 ∣ Nat.card (⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ : Subgroup Y))
    (hnc : ∀ Z : Subgroup Y, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
      ¬ J ≤ normalizer (Z : Set Y) ⊔ CFSG.pPrimeCore p Y) :
    IsChevTwo L ∨ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n)) := by
  have _ := hJc
  have : Fact p.Prime := ⟨hp⟩
  have : J.Normal := hJn
  have : IsSimpleGroup L := hLs
  obtain ⟨W, hW⟩ : ∃ W : Subgroup Y, J ⊔ V = W := ⟨_, rfl⟩
  have hJW : J ≤ W := hW ▸ le_sup_left
  have hVW : V ≤ W := hW ▸ le_sup_right
  have hRW : CFSG.pCore 2 Y ≤ W := hcore.trans hVW
  have hpL : p ∣ Nat.card L := zja_dvd_card hp hLnab hJL hJp
  have hpc : CFSG.pCore 2 W = (CFSG.pCore 2 Y).subgroupOf W :=
    zja_pCore_eq hp hp2 hsylow hLs hLn hLc hpL hJL hJW
  have hPle : (CFSG.pPrimeCore p W).map W.subtype ≤ CFSG.pPrimeCore p Y :=
    zja_map_subtype_le hp hLs hLn hLc hpL hJL hJW (N := CFSG.pPrimeCore p W)
      CFSG.pPrimeCore_coprime_card
  have hcharW : centralizer (CFSG.pCore 2 W : Set W) ≤ CFSG.pCore 2 W := by
    rw [hpc]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hcharTwo
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨r, hRW hr⟩ hr)
  have h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p W),
      (T₂ : Subgroup (CFSG.pPrimeCore p W)).Normal :=
    fun T₂ => zja_sylow_normal hsylow hPle T₂
  have hKn : (J.subgroupOf W).Normal := inferInstance
  have hKp : pElementSubgroup p (J.subgroupOf W) = J.subgroupOf W :=
    zja_pElementSubgroup_subgroupOf hJW hJp
  obtain ⟨e₂⟩ := zja_exists_equiv_image hp hLs hLn hLc hpL hJL hJW
  have hcomp : CFSG.IsComponent
      ((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))) := by
    refine ⟨?_, ?_⟩
    · have : IsSimpleGroup
          ↥((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))) :=
        e₂.isSimpleGroup
      refine zja_isQuasisimple_of_simple ?_
      obtain ⟨a, b, hab⟩ := hLnab
      exact ⟨e₂.symm a, e₂.symm b, fun h => hab (by simpa using congrArg e₂ h)⟩
    · exact Subgroup.Normal.isSubnormal
        (Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _))
  have hPC : CFSG.IsPComponent p (J.subgroupOf W) :=
    isPComponent_of_normal hp hKn hKp hcomp rfl
  have hS2 : IsPGroup 2 (V.subgroupOf W) := hV.comap_subtype
  have hKS : J.subgroupOf W ⊔ V.subgroupOf W = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJW,
      Subgroup.map_subgroupOf_eq_of_le hVW, hW, Subgroup.map_top, Subgroup.range_subtype]
  have hT : ∃ T : Sylow 2 W, J.subgroupOf W ⊔ (T : Subgroup W) = ⊤ := by
    obtain ⟨T, hT⟩ := hS2.exists_le_sylow
    exact ⟨T, eq_top_iff.mpr (hKS.ge.trans (sup_le_sup_left hT _))⟩
  have h3 : ¬ 3 ∣ Nat.card (⁅J.subgroupOf W,
      (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map (J.subgroupOf W).subtype⁆ : Subgroup W) := by
    let ι : ↥(J.subgroupOf W) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJW
    have hcore' : (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map ι.toMonoidHom =
        CFSG.pPrimeCore p ↥J := CFSG.pPrimeCore_map_iso p ι
    have hhom : W.subtype.comp (J.subgroupOf W).subtype = J.subtype.comp ι.toMonoidHom := by
      ext x
      rfl
    have himg : ((CFSG.pPrimeCore p ↥(J.subgroupOf W)).map (J.subgroupOf W).subtype).map
        W.subtype = (CFSG.pPrimeCore p ↥J).map J.subtype := by
      rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hcore']
    have hcomm : (⁅J.subgroupOf W, (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map
        (J.subgroupOf W).subtype⁆ : Subgroup W).map W.subtype =
        ⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJW, himg]
    have hcard := Subgroup.card_map_of_injective
      (K := (⁅J.subgroupOf W, (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map
        (J.subgroupOf W).subtype⁆ : Subgroup W)) W.subtype_injective
    rw [hcomm] at hcard
    rw [← hcard]
    exact hJ0
  have hnc' : ∀ Z' : Subgroup W, Z' ≤ V.subgroupOf W → Z' ≠ ⊥ →
      (Z'.subgroupOf (V.subgroupOf W)).Characteristic →
      ¬ J.subgroupOf W ≤ normalizer (Z' : Set W) ⊔ CFSG.pPrimeCore p W := by
    intro Z' hZ'S hZ'1 hZ'c hcover
    have hZV : Z'.map W.subtype ≤ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZ'S hz
    have hZ1 : Z'.map W.subtype ≠ ⊥ := fun h =>
      hZ'1 ((Subgroup.map_eq_bot_iff_of_injective Z' W.subtype_injective).mp h)
    have hZc : ((Z'.map W.subtype).subgroupOf V).Characteristic := by
      let e : ↥(V.subgroupOf W) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVW
      have hchar := zja_characteristic_map e hZ'c
      have heq : (Z'.subgroupOf (V.subgroupOf W)).map e.toMonoidHom =
          (Z'.map W.subtype).subgroupOf V := by
        ext x
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact ⟨s, hs, rfl⟩
        · intro hx
          obtain ⟨z, hz, hzx⟩ := hx
          exact ⟨⟨z, hZ'S hz⟩, hz, Subtype.ext hzx⟩
      rw [← heq]
      exact hchar
    refine hnc _ hZV hZ1 hZc ?_
    have h1 : (J.subgroupOf W).map W.subtype ≤
        (normalizer (Z' : Set W) ⊔ CFSG.pPrimeCore p W).map W.subtype :=
      Subgroup.map_mono hcover
    rw [Subgroup.map_subgroupOf_eq_of_le hJW, Subgroup.map_sup] at h1
    refine h1.trans (sup_le_sup ?_ hPle)
    rintro _ ⟨g, hg, rfl⟩
    exact thg_mem_normalizer_map hg
  have hcoreS : CFSG.pCore 2 W ≤ V.subgroupOf W := by
    rw [hpc]
    exact Subgroup.comap_mono hcore
  have hrkpW : ∀ E : Subgroup W, IsElemAbelian p E → Nat.card E ≤ p ^ 2 := fun E hE => by
    have h := hrkp (E.map W.subtype) (thr_isElemAbelian_map hE)
    rwa [Subgroup.card_map_of_injective W.subtype_injective] at h
  have key := hK1 p hp hp2 (↥W) (hsec.subgroup W) hcharW hrkpW (J.subgroupOf W) hKn hPC hT
    h3 h2cl (V.subgroupOf W) hS2 hcoreS hnc'
  have hLcen : center L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : Y ⧸ CFSG.pPrimeCore p Y) ∈
        centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨h, hh⟩)
    rw [hLc, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (Subtype.ext hz')
  let ψ₀ : ↥(J.subgroupOf W) →* Y ⧸ CFSG.pPrimeCore p Y :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore p Y)).comp W.subtype).comp (J.subgroupOf W).subtype
  have hψ₀L : ∀ x : ↥(J.subgroupOf W), ψ₀ x ∈ L := by
    intro x
    rw [← hJL]
    exact Subgroup.mem_map_of_mem _ x.2
  let ψ : ↥(J.subgroupOf W) →* ↥L := ψ₀.codRestrict L hψ₀L
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hJL] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact ⟨⟨⟨j, hJW hj⟩, hj⟩, rfl⟩
  have hker : p.Coprime (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (W.subtype.comp (J.subgroupOf W).subtype) ≤ CFSG.pPrimeCore p Y := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : ψ₀ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp hx1
    have hinj : Function.Injective (W.subtype.comp (J.subgroupOf W).subtype) :=
      W.subtype_injective.comp (J.subgroupOf W).subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  obtain ⟨e⟩ := zja_quotient_equiv hp (G := ↥(J.subgroupOf W)) (M := ↥L) hpL hLcen ψ hψ hker
  exact zja_chevTwo_or_alt_of_mulEquiv e key

theorem zj_J0Ge {p : ℕ} {Y : Type} [Group Y] [Finite Y] {K D V J : Subgroup Y} [K.Normal]
    (hZ : ZJFrameGe p K D V) {L : Subgroup (Y ⧸ K)} (hLs : IsSimpleGroup L)
    (hLc : centralizer (L : Set (Y ⧸ K)) = ⊥) (hJn : J.Normal)
    (hJL : J.map (QuotientGroup.mk' K) = L) (hJp : pElementSubgroup p J = J)
    (hJJ : ⁅J, J⁆ = J) (hJK : (CFSG.pPrimeCore p ↥J).map J.subtype = J ⊓ K)
    (hjoin : p ∣ Nat.card (invariantTwoJoinIn (D.map (QuotientGroup.mk' K)) L)) :
    ¬ 3 ∣ Nat.card (⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ : Subgroup Y) := by
  classical
  have hp := hZ.pre.prime
  have hp2 := hZ.pre.odd
  rw [hJK]
  intro h3
  set R : Subgroup Y := J ⊓ K with hR
  have hRJ : R ≤ J := inf_le_left
  have hRK : R ≤ K := inf_le_right
  have hRn : R.Normal := inferInstance
  have hRcop : p.Coprime (Nat.card R) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hRK) hZ.pre.coprime
  have hJ0R : ⁅J, R⁆ ≤ R := Subgroup.commutator_le_right J R
  have hJ0cop : p.Coprime (Nat.card (⁅J, R⁆ : Subgroup Y)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hJ0R) hRcop
  have hp3 : p ≠ 3 := by
    rintro rfl
    have := Nat.Coprime.eq_one_of_dvd hJ0cop h3
    omega
  have hp5 : 5 ≤ p := by
    by_contra hlt
    push Not at hlt
    interval_cases p <;> simp_all <;> exact absurd hp (by norm_num)
  have hDp : IsPGroup p D := IsPGroup.of_card hZ.pre.card
  have hDN : D ≤ normalizer ((⁅J, R⁆ : Subgroup Y) : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨Y₃, hY₃, hDY₃⟩ :=
    zjo_exists_isSylowOf_normalized (q := p) (r := 3) hp Nat.prime_three hDp hDN hJ0cop
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ0J : ⁅J, R⁆ ≤ J := Subgroup.commutator_le_left J R
  have hJ0K : ⁅J, R⁆ ≤ K := hJ0R.trans hRK
  have hfrat : ∀ j ∈ J, ∃ n ∈ J ⊓ normalizer (Y₃ : Set Y), ∃ k ∈ (⁅J, R⁆ : Subgroup Y),
      n * k = j := by
    intro j hj
    obtain ⟨Q, hQ⟩ := hY₃
    have h := Sylow.normalizer_sup_eq_top Q
    have hQ' : (Q : Subgroup ↥(⁅J, R⁆ : Subgroup Y)).map (⁅J, R⁆ : Subgroup Y).subtype = Y₃ := hQ
    rw [hQ'] at h
    have hj' : j ∈ normalizer (Y₃ : Set Y) ⊔ (⁅J, R⁆ : Subgroup Y) := by rw [h]; exact trivial
    obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hj'
    refine ⟨n, ⟨?_, hn⟩, k, hk, rfl⟩
    have := J.mul_mem hj (J.inv_mem (hJ0J hk))
    simpa using this
  have hcover : ∀ l ∈ L, ∃ n ∈ J ⊓ normalizer (Y₃ : Set Y), QuotientGroup.mk' K n = l := by
    intro l hl
    rw [← hJL] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    obtain ⟨n, hn, k, hk, rfl⟩ := hfrat j hj
    refine ⟨n, hn, ?_⟩
    have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr (hJ0K hk)
    rw [map_mul, hk1, mul_one]
  have hKsolv : Group.IsSolvable K := zjo_solvable_of_normal_sylow_two hZ.sylow2
  have hRs : Group.IsSolvable R :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hRK)
  have hJR : ⁅J, J⁆ ⊔ R = J := by
    rw [hJJ]
    exact sup_eq_left.mpr hRJ
  have hnot := eighteen_ten_solvable hp Nat.prime_three hRJ hJn hRn hRcop hRs hJp hJR hY₃ h3
  have hfaith : D ⊓ centralizer (Y₃ : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro d ⟨hdD, hdC⟩
    rw [Subgroup.mem_bot]
    by_contra hd1
    have hdK : d ∉ K := by
      intro hdK
      have h1 : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one (hZ.pre.elem.2 d hdD)
      have h2 : orderOf d ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hdK
      have h3 := Nat.eq_one_of_dvd_coprimes hZ.pre.coprime h1 h2
      exact hd1 (orderOf_eq_one_iff.mp h3)
    have hdbar : QuotientGroup.mk' K d ≠ 1 := fun h => hdK ((QuotientGroup.eq_one_iff d).mp h)
    have hnc : QuotientGroup.mk' K d ∉ centralizer (L : Set (Y ⧸ K)) := by
      rw [hLc]
      exact hdbar
    rw [mem_centralizer_iff] at hnc
    push Not at hnc
    obtain ⟨l, hlL, hl⟩ := hnc
    obtain ⟨n, hnJ, hnN⟩ := hcover l hlL
    have := hLs
    set C : Subgroup Y := centralizer (Y₃ : Set Y) ⊓ J with hC
    set T : Subgroup (Y ⧸ K) := C.map (QuotientGroup.mk' K) with hT
    have hTL : T ≤ L := by
      rw [← hJL]
      exact Subgroup.map_mono inf_le_right
    have hconj : ∀ m ∈ J ⊓ normalizer (Y₃ : Set Y), ∀ c ∈ C, m * c * m⁻¹ ∈ C := by
      intro m hm c hc
      refine ⟨?_, J.mul_mem (J.mul_mem hm.1 hc.2) (J.inv_mem hm.1)⟩
      show m * c * m⁻¹ ∈ centralizer (Y₃ : Set Y)
      rw [mem_centralizer_iff]
      intro y hy
      have hzmem : m⁻¹ * y * m ∈ Y₃ := by
        simpa using (mem_normalizer_iff.mp (inv_mem hm.2) y).mp hy
      have hz := mem_centralizer_iff.mp (show c ∈ centralizer (Y₃ : Set Y) from hc.1) _ hzmem
      calc y * (m * c * m⁻¹) = m * ((m⁻¹ * y * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * y * m)) * m⁻¹ := by rw [hz]
        _ = m * c * m⁻¹ * y := by group
    have hTn : (T.subgroupOf L).Normal := by
      refine ⟨fun t ht g => ?_⟩
      obtain ⟨c, hcC, hct⟩ := ht
      obtain ⟨m, hmJ, hmg⟩ := hcover g.1 g.2
      refine ⟨m * c * m⁻¹, hconj m hmJ c hcC, ?_⟩
      show QuotientGroup.mk' K (m * c * m⁻¹) = (g : Y ⧸ K) * (t : Y ⧸ K) * (g : Y ⧸ K)⁻¹
      rw [map_mul, map_mul, map_inv, hct, hmg]
      rfl
    have hcC : d⁻¹ * (n⁻¹ * d * n) ∈ C := by
      refine ⟨?_, ?_⟩
      · show d⁻¹ * (n⁻¹ * d * n) ∈ centralizer (Y₃ : Set Y)
        rw [mem_centralizer_iff]
        intro y hy
        have hz : n * y * n⁻¹ ∈ Y₃ := (mem_normalizer_iff.mp hnJ.2 y).mp hy
        have hdC' : d ∈ centralizer (Y₃ : Set Y) := hdC
        have h1 := mem_centralizer_iff.mp hdC' y hy
        have h2 := mem_centralizer_iff.mp hdC' _ hz
        have hdy : y * d⁻¹ = d⁻¹ * y := by
          calc y * d⁻¹ = d⁻¹ * (d * y) * d⁻¹ := by group
            _ = d⁻¹ * (y * d) * d⁻¹ := by rw [h1]
            _ = d⁻¹ * y := by group
        have hnd : y * (n⁻¹ * d * n) = (n⁻¹ * d * n) * y := by
          calc y * (n⁻¹ * d * n) = n⁻¹ * ((n * y * n⁻¹) * d) * n := by group
            _ = n⁻¹ * (d * (n * y * n⁻¹)) * n := by rw [h2]
            _ = (n⁻¹ * d * n) * y := by group
        calc y * (d⁻¹ * (n⁻¹ * d * n)) = (y * d⁻¹) * (n⁻¹ * d * n) := by group
          _ = d⁻¹ * (y * (n⁻¹ * d * n)) := by rw [hdy]; group
          _ = d⁻¹ * ((n⁻¹ * d * n) * y) := by rw [hnd]
          _ = d⁻¹ * (n⁻¹ * d * n) * y := by group
      · have h1 : d⁻¹ * n⁻¹ * d ∈ J := by
          have := hJn.conj_mem n⁻¹ (J.inv_mem hnJ.1) d⁻¹
          simpa using this
        have := J.mul_mem h1 hnJ.1
        simpa [mul_assoc] using this
    have hne : T.subgroupOf L ≠ ⊥ := by
      intro hbot
      have hmem : (⟨QuotientGroup.mk' K (d⁻¹ * (n⁻¹ * d * n)), hTL ⟨_, hcC, rfl⟩⟩ : ↥L) ∈
          T.subgroupOf L := ⟨_, hcC, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : QuotientGroup.mk' K (d⁻¹ * (n⁻¹ * d * n)) = 1 := congrArg Subtype.val hmem
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hnN] at h1
      apply hl
      have h2 : l⁻¹ * QuotientGroup.mk' K d * l = QuotientGroup.mk' K d := by
        rw [inv_mul_eq_one] at h1
        exact h1.symm
      have h3 : QuotientGroup.mk' K d * l = l * QuotientGroup.mk' K d := by
        calc QuotientGroup.mk' K d * l = l * (l⁻¹ * QuotientGroup.mk' K d * l) := by group
          _ = l * QuotientGroup.mk' K d := by rw [h2]
      exact h3.symm
    have := hTn
    have htop : T.subgroupOf L = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf L)).resolve_left hne
    have hLT : L ≤ T := fun x hx => by
      have : (⟨x, hx⟩ : ↥L) ∈ T.subgroupOf L := by rw [htop]; trivial
      exact this
    refine hnot (fun j hj => ?_)
    have hjL : QuotientGroup.mk' K j ∈ L := by
      rw [← hJL]
      exact ⟨j, hj, rfl⟩
    obtain ⟨c, hcC', hcj⟩ := hLT hjL
    have hmem : c⁻¹ * j ∈ R := by
      refine ⟨J.mul_mem (J.inv_mem hcC'.2) hj, ?_⟩
      have h1 : QuotientGroup.mk' K (c⁻¹ * j) = 1 := by
        rw [map_mul, map_inv, hcj, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hjeq : j = c * (c⁻¹ * j) := by group
    rw [hjeq]
    exact Subgroup.mul_mem_sup hcC' hmem
  have hLN : L ≤ (normalizer (Y₃ : Set Y)).map (QuotientGroup.mk' K) := by
    intro l hl
    obtain ⟨n, hn, hnl⟩ := hcover l hl
    exact ⟨n, hn.2, hnl⟩
  exact zj_not_covers hp hp2 hZ.pre.coprime hDp hjoin hDY₃
    (hZ.three hp5 Y₃ hY₃.isPGroup hDY₃ hfaith) hLN

theorem ZJFrameGe.exists_alt {p : ℕ} {Y : Type} [Group Y] [Finite Y] {K D V : Subgroup Y}
    [K.Normal] (hK1 : KFactZJFactorizationGe) (hK2 : KFactAlmostSimpleRankTwo)
    (hZ : ZJFrameGe p K D V) :
    ∃ L : Subgroup (Y ⧸ K), CFSG.IsComponent L ∧
      ∃ n : ℕ, Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) := by
  classical
  have hp := hZ.pre.prime
  have hp2 := hZ.pre.odd
  have hKcop := hZ.pre.coprime
  have hF := hZ.pre.quotient
  obtain ⟨L, hL, hpL, hcat⟩ := hZ.exists_component
  obtain ⟨hLn, hLz, hLc, hLs, hLnab⟩ := hF.component_data hL
  let q1 : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hLz).trans QuotientGroup.quotientBot
  by_cases halt : ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))
  · obtain ⟨n, ⟨e⟩⟩ := halt
    exact ⟨L, hL, n, ⟨q1.trans e⟩⟩
  · exfalso
    have hcatL : IsCatalogGroup L := CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv q1.symm hcat
    have hK2' := hK2 p hp hp2 (Y ⧸ K) L hLs hLnab hcatL halt hLc hF.rank_le
    obtain ⟨hcl, hchev⟩ := hK2'
    have hjoin : p ∣ Nat.card (invariantTwoJoinIn (D.map (QuotientGroup.mk' K)) L) :=
      hF.dvd_card_join_of_pClosed hLn hcl
    have hKeq : CFSG.pPrimeCore p Y = K := hZ.pre.pPrimeCore_eq
    subst hKeq
    have hpL' : p ∣ Nat.card L := by
      rw [← Nat.card_congr q1.toEquiv]
      exact hpL
    obtain ⟨J, hJn, hJc, hJL, hJp, hJJ, hJK⟩ := exists_pComponent_normal hp hL hLn hLz hpL'
    have hJ0 := zj_J0Ge hZ hLs hLc hJn hJL hJp hJJ hJK hjoin
    have hDp : IsPGroup p D := IsPGroup.of_card hZ.pre.card
    have hnc : ∀ Z : Subgroup Y, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
        ¬ J ≤ normalizer (Z : Set Y) ⊔ CFSG.pPrimeCore p Y := by
      intro Z hZV hZ1 hZc hJZ
      have hDZ : D ≤ normalizer (Z : Set Y) := hZ.D_norm.trans (zjq_normalizer_le hZV hZc)
      refine zj_not_covers hp hp2 hKcop hDp hjoin hDZ (hZ.noncover Z hZV hZ1 hZc) ?_
      rw [← hJL]
      refine (Subgroup.map_mono hJZ).trans ?_
      rw [Subgroup.map_sup]
      have : (CFSG.pPrimeCore p Y).map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = ⊥ :=
        (QuotientGroup.map_mk'_self _)
      rw [this, sup_bot_eq]
    rcases zj_applyGe hp hp2 hK1 hZ.sections hZ.charTwo hZ.pre.rank_le hZ.sylow2 hJn hJc hLs
        hLnab hLn hLc hJL hJp hZ.V_two hZ.core_le hJ0 hnc with hchevL | ⟨n, hn⟩
    · exact hchev hchevL (D.map (QuotientGroup.mk' _)) hF
        (NormalizerExponent.quotient hp hKcop hDp hZ.exp) hjoin
    · exact halt ⟨n, hn⟩

end CFSG.LocalAnalysis.RankFourTheoremC
