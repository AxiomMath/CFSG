module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Sec

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem isSec82LType_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {p f : ℕ}
    (h : IsSec82LType Y p f) : IsSec82LType Y' p f := by
  rcases h with h | h | ⟨⟨e10⟩⟩
  · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · exact Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr ⟨e.symm.trans e10⟩)

theorem isSec8JType_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {p f : ℕ}
    (h : IsSec8JType Y p f) : IsSec8JType Y' p f := by
  rcases h with h | ⟨hp, hf, ⟨e6⟩⟩
  · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · exact Or.inr ⟨hp, hf, ⟨e.symm.trans e6⟩⟩

theorem comm_mem_oddCoreIn_of_central {M K : Subgroup X} (hMperf : Group.IsPerfect ↥M)
    (hKN : K ≤ normalizer (M : Set X)) (hMK : ∀ c ∈ K, ∀ w ∈ M, w * c * w⁻¹ ∈ K)
    (hcen : ∀ z ∈ K ⊓ M, ∀ v ∈ M, z * v * z⁻¹ * v⁻¹ ∈ oddCoreIn M) {c w : X} (hc : c ∈ K)
    (hw : w ∈ M) : c * w * c⁻¹ * w⁻¹ ∈ oddCoreIn M := by
  set N := normalizer (M : Set X) with hN
  have hMN : M ≤ N := le_normalizer
  have hON : ((oddCoreIn M).subgroupOf N).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hMN)).mpr ?_
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M (pPrimeCore 2 M)
  set O := (oddCoreIn M).subgroupOf N with hO
  set π := QuotientGroup.mk' O with hπ
  have hπ1 : ∀ n : ↥N, π n = 1 ↔ (n : X) ∈ oddCoreIn M := fun n => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_subgroupOf]
  set Yh := (M.subgroupOf N).map π with hYh
  set Kh := (K.subgroupOf N).map π with hKh
  have : Group.IsPerfect ↥(M.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hMN).symm.surjective
  have hYperf : Group.IsPerfect ↥Yh := Group.IsPerfect.map π
  have hle : ⁅Yh, Kh⁆ ≤ centralizer (Yh : Set (↥N ⧸ O)) := by
    rw [commutator_le]
    rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨c₁, hc₁, rfl⟩
    rw [← map_commutatorElement, mem_centralizer_iff]
    rintro _ ⟨v₁, hv₁, rfl⟩
    have hw₁M : (w₁ : X) ∈ M := mem_subgroupOf.mp hw₁
    have hc₁K : (c₁ : X) ∈ K := mem_subgroupOf.mp hc₁
    have hv₁M : (v₁ : X) ∈ M := mem_subgroupOf.mp hv₁
    set z : X := (w₁ : X) * c₁ * (w₁ : X)⁻¹ * (c₁ : X)⁻¹ with hz
    have hzK : z ∈ K := mul_mem (hMK _ hc₁K _ hw₁M) (inv_mem hc₁K)
    have hzM : z ∈ M := by
      have h1 : (c₁ : X) * (w₁ : X)⁻¹ * (c₁ : X)⁻¹ ∈ M :=
        (mem_normalizer_iff.mp (hKN hc₁K) _).mp (inv_mem hw₁M)
      rw [hz, show (w₁ : X) * c₁ * (w₁ : X)⁻¹ * (c₁ : X)⁻¹ =
        w₁ * ((c₁ : X) * (w₁ : X)⁻¹ * (c₁ : X)⁻¹) by group]
      exact mul_mem hw₁M h1
    have h2 := inv_mem (hcen z (mem_inf.mpr ⟨hzK, hzM⟩) _ hv₁M)
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, hπ1]
    convert h2 using 1
    simp only [commutatorElement_def, coe_mul, coe_inv, hz]
    group
  have hbot : ⁅Yh, Kh⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hYperf
    (commutator_eq_bot_iff_le_centralizer.mpr hle)
  have h1 : π ⁅(⟨w, hMN hw⟩ : ↥N), ⟨c, hKN hc⟩⁆ = 1 := by
    rw [map_commutatorElement]
    have h3 := commutator_mem_commutator
      (mem_map_of_mem π (show (⟨w, hMN hw⟩ : ↥N) ∈ M.subgroupOf N from hw))
      (mem_map_of_mem π (show (⟨c, hKN hc⟩ : ↥N) ∈ K.subgroupOf N from hc))
    rwa [hbot, mem_bot] at h3
  rw [hπ1] at h1
  have h4 : c * w * c⁻¹ * w⁻¹ = (w * c * w⁻¹ * c⁻¹)⁻¹ := by group
  rw [h4]
  exact inv_mem (by simpa only [commutatorElement_def, coe_mul, coe_inv] using h1)

theorem center_oddBar_eq_bot_of_inner (hCov : CF82Cover) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {M J₀ : Subgroup X} (hq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M))
    (htype : IsSec82LType ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) p f)
    {a : X} (ha : a * a = 1) (haM : a ∈ normalizer (M : Set X)) {m : X} (hm : m ∈ M)
    (hinn : ∀ w ∈ M, (a * w * a⁻¹)⁻¹ * (m * w * m⁻¹) ∈ oddCoreIn M)
    (hJ0 : J₀ ≤ M ⊓ centralizer ({a} : Set X))
    (hJ0pc : IsPComponent 2 (J₀.subgroupOf (M ⊓ centralizer ({a} : Set X))))
    (hJt : IsSec8JType (↥J₀ ⧸ pPrimeCore 2 ↥J₀) p f) :
    center (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hZM
  set N := normalizer (M : Set X) with hN
  have hMN : M ≤ N := le_normalizer
  have hON : (oddCoreIn M).subgroupOf N |>.Normal := by
    refine (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hMN)).mpr ?_
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M (pPrimeCore 2 M)
  set O := (oddCoreIn M).subgroupOf N with hO
  set π := QuotientGroup.mk' O with hπ
  have hkerπ : ¬ 2 ∣ Nat.card π.ker := by
    have hle : oddCoreIn M ≤ N := (map_subtype_le _).trans hMN
    rw [hπ, QuotientGroup.ker_mk', hO, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      oddCoreIn, card_map_of_injective M.subtype_injective]
    intro h2
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2
      (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  set Yh := (M.subgroupOf N).map π with hYh
  let α : ↥M →* ↥Yh := (π.comp (inclusion hMN)).codRestrict Yh fun m =>
    mem_map_of_mem π (show inclusion hMN m ∈ M.subgroupOf N from m.2)
  have hα : Function.Surjective α := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hkerα : α.ker = pPrimeCore 2 ↥M := by
    ext m
    rw [MonoidHom.mem_ker]
    constructor
    · intro hm
      have h1 : π (inclusion hMN m) = 1 := congrArg Subtype.val hm
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_subgroupOf] at h1
      obtain ⟨m', hm', hmm'⟩ := mem_map.mp h1
      rwa [show m' = m from Subtype.ext hmm'] at hm'
    · intro hm
      apply Subtype.ext
      change π (inclusion hMN m) = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_subgroupOf]
      exact mem_map_of_mem _ hm
  let e : ↥Yh ≃* ↥M ⧸ pPrimeCore 2 ↥M := Seven.equivOfKerEq α (QuotientGroup.mk' _) hα
    (QuotientGroup.mk'_surjective _) (by rw [hkerα, QuotientGroup.ker_mk'])
  have hqY : IsQuasisimple ↥Yh := (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq
  have hZY : center ↥Yh ≠ ⊥ := by
    intro h1
    apply hZM
    rw [← Subgroup.card_eq_one] at h1 ⊢
    rw [← h1]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  have htypeY : IsSec82LType (↥Yh ⧸ center ↥Yh) p f :=
    isSec82LType_of_mulEquiv (GorensteinWalter.FieldTransport.quotientCenterMulEquiv e).symm htype
  set t := π ⟨a, haM⟩ with ht_def
  have ht : t * t = 1 := by
    rw [ht_def, ← map_mul, show (⟨a, haM⟩ : ↥N) * ⟨a, haM⟩ = 1 from Subtype.ext ha, map_one]
  have hYn : Yh.Normal := (normal_in_normalizer (H := M)).map π (QuotientGroup.mk'_surjective _)
  have htN : t ∈ normalizer (Yh : Set (↥N ⧸ O)) := by
    rw [normalizer_eq_top_iff.mpr hYn]
    exact mem_top t
  have hinnY : ∃ y₀ ∈ Yh, ∀ w ∈ Yh, t * w * t⁻¹ = y₀ * w * y₀⁻¹ := by
    refine ⟨π ⟨m, hMN hm⟩, mem_map_of_mem π (show (⟨m, hMN hm⟩ : ↥N) ∈ M.subgroupOf N from hm),
      ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have key : ((⟨a, haM⟩ : ↥N) * w * (⟨a, haM⟩ : ↥N)⁻¹)⁻¹ *
        ((⟨m, hMN hm⟩ : ↥N) * w * (⟨m, hMN hm⟩ : ↥N)⁻¹) ∈ O := by
      rw [hO, mem_subgroupOf]
      simpa only [coe_mul, coe_inv] using hinn w (mem_subgroupOf.mp hw)
    have h1 := (QuotientGroup.eq (s := O)).mpr key
    simpa only [ht_def, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      using h1
  have hJ0N : J₀ ≤ N := (hJ0.trans inf_le_left).trans hMN
  have hE2 : IsPGroup 2 (zpowers (⟨a, haM⟩ : ↥N)) := by
    intro w
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp w.2
    apply Subtype.ext
    have ha2 : (⟨a, haM⟩ : ↥N) ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext ha
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hk]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2, one_zpow]
  have hMn : (M.subgroupOf N).Normal := normal_in_normalizer
  have hEY : zpowers (⟨a, haM⟩ : ↥N) ≤ normalizer ((M.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [normalizer_eq_top_iff.mpr hMn]
    exact le_top
  have hcent : Yh ⊓ centralizer ({t} : Set (↥N ⧸ O)) =
      ((M ⊓ centralizer ({a} : Set X)).subgroupOf N).map π := by
    have h1 : ((M.subgroupOf N) ⊓ centralizer ({(⟨a, haM⟩ : ↥N)} : Set ↥N)).map π =
        Yh ⊓ centralizer ({t} : Set (↥N ⧸ O)) := by
      have h2 := OddQuot.map_inf_centralizer π hE2 hEY
        (OddQuot.not_two_dvd_card_ker_domRestrict π hkerπ _)
      simp only [MonoidHom.map_zpowers, centralizer_zpowers_eq] at h2
      exact h2
    rw [← h1]
    congr 1
    ext w
    simp only [mem_inf, mem_subgroupOf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => ⟨fun h2 => congrArg Subtype.val h2,
      fun h2 => Subtype.ext h2⟩
  set M' := (J₀.subgroupOf N).map π with hM'
  have hJsub : J₀.subgroupOf N ≤ (M ⊓ centralizer ({a} : Set X)).subgroupOf N := fun w hw =>
    mem_subgroupOf.mpr (hJ0 (mem_subgroupOf.mp hw))
  have hJpcN : IsPComponent 2 ((J₀.subgroupOf N).subgroupOf
      ((M ⊓ centralizer ({a} : Set X)).subgroupOf N)) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (inf_le_left.trans hMN) 2
      Nat.prime_two).mpr hJ0pc
  have hM'pc := OddQuot.isPComponent_map π hkerπ hJsub hJpcN
  rw [← hcent] at hM'pc
  have hM'le : M' ≤ Yh ⊓ centralizer ({t} : Set (↥N ⧸ O)) := by
    rw [hcent]
    exact map_mono hJsub
  have hM'J : IsSec8JType (↥M' ⧸ pPrimeCore 2 ↥M') p f := by
    obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hkerπ (J₀.subgroupOf N)
    let e2 := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJ0N)
    exact isSec8JType_of_mulEquiv (e2.symm.trans e1) hJt
  exact hCov _ p f hp hp2 hf Yh hqY hZY htypeY t ht htN hinnY M' hM'le hM'pc hM'J

namespace Setting0

variable (s : Setting0 X)

theorem nf58 : NF58Setting X s.h :=
  ⟨s.isSimpleGroup, s.nonab, s.kProper, s.unbal, s.notU, s.maxTriple, s.isoAt, s.notB1, s.notB2a⟩

theorem kappaAt_of_cover (h81 : Lemma81StatementK) (inner : CF82Inner) (cover : CF82Cover)
    (hW : s.h.NoFusionW) : s.KappaAt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := s.isSimpleGroup
  obtain ⟨k₀, ha, -, -, -, -, -, hP, -, -, -, -, eJ, eK, hconj, -, -, -⟩ :=
    s.secCond.exists_hyp59_subQuot_of_T_eq s.J_normal s.S_sylow.2 s.NP_eq.1 hW
  obtain ⟨eJ'⟩ := eJ s.center_J
  have hL := h81 _ k₀ (s.isKGroupCat_or_simple k₀) (s.sec8Case_of k₀ eJ eK hconj)
    (s.eight_le_card_of_le hP)
  obtain ⟨p, f, hp, hp2, hf, htype, hJt⟩ := s.exists_params k₀ ⟨eJ'⟩ hL
  obtain ⟨haF, -, -⟩ := s.inner_of_sec inner k₀ ha hP hp hp2 hf htype hJt
  obtain ⟨M, hMC, hM, ⟨eM⟩⟩ :=
    s.secCond.exists_isPComponent_centralizer_of_sub k₀ (MulEquiv.refl _)
  have hLM : s.h.secL0 s.y = M := Hyp52.layerIn_centralizer_eq_sub k₀ hMC hM
  have hq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMC).mp hM).2.2
  have hMH : M ≤ s.h.secSub s.y := Hyp52.SubQAux.le_secSub_of_isPComponent hMC hM
  have hHN : s.h.secSub s.y ≤ normalizer (M : Set X) := by
    rw [← hLM]
    exact (s.h.secSub_le_G0 s.y).trans (s.h.G0_le_normalizer_secL0 s.y)
  obtain ⟨hFeq, -, -, hcomp, -⟩ := Hyp59.generalizedFitting_simple k₀
  have hMθ := Hyp52.subQ_map_eq k₀ hMC hM
  rw [ha, hFeq, ← hMθ] at haF
  obtain ⟨m', hm'M, hm'⟩ := mem_map.mp haF
  set m : X := (m' : X) with hmdef
  have hm : m ∈ M := mem_subgroupOf.mp hm'M
  set Kθ : Subgroup X := (s.h.subQ s.y).ker.map (s.h.secSub s.y).subtype with hKθ
  have hKH : Kθ ≤ s.h.secSub s.y := map_subtype_le _
  have hk : m⁻¹ * s.h.a ∈ Kθ := by
    have h1 : m'⁻¹ * ⟨s.h.a, s.secCond.a_mem_secSub⟩ ∈ (s.h.subQ s.y).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hm', inv_mul_cancel]
    exact mem_map.mpr ⟨_, h1, rfl⟩
  have hMK : ∀ c ∈ Kθ, ∀ w ∈ M, w * c * w⁻¹ ∈ Kθ := by
    intro c hc w hw
    obtain ⟨c', hc', rfl⟩ := mem_map.mp hc
    have h1 : ⟨w, hMH hw⟩ * c' * ⟨w, hMH hw⟩⁻¹ ∈ (s.h.subQ s.y).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.mp hc', mul_one, map_inv,
        mul_inv_cancel]
    exact mem_map.mpr ⟨_, h1, rfl⟩
  have hcen : ∀ z ∈ Kθ ⊓ M, ∀ v ∈ M, z * v * z⁻¹ * v⁻¹ ∈ oddCoreIn M := by
    set N₁ : Subgroup ↥M := Kθ.subgroupOf M with hN₁
    have hN₁n : N₁.Normal := ⟨fun n hn g => by
      rw [hN₁, mem_subgroupOf] at hn ⊢
      exact hMK _ hn _ g.2⟩
    have hNbn : (N₁.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).Normal :=
      hN₁n.map _ (QuotientGroup.mk'_surjective _)
    rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hNbn with htop | hZ1
    ·
      exfalso
      have hOM : oddCoreIn M ≤ M := map_subtype_le _
      have hle : (M.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ≤
          ((oddCoreIn M).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) := by
        rintro _ ⟨w, hw, rfl⟩
        have hwM : (w : X) ∈ M := mem_subgroupOf.mp hw
        have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨w, hwM⟩ ∈
            N₁.map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) := htop ▸ mem_top _
        obtain ⟨n, hn, hnw⟩ := mem_map.mp h1
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnw
        obtain ⟨n', hn', hn'n⟩ := mem_map.mp (show (n : X) ∈ Kθ from hn)
        set o : ↥M := n⁻¹ * ⟨w, hwM⟩ with ho_def
        refine ⟨⟨o, hMH o.2⟩, mem_subgroupOf.mpr (mem_map_of_mem M.subtype hnw), ?_⟩
        have hw' : w = n' * ⟨o, hMH o.2⟩ := by
          apply Subtype.ext
          rw [coe_mul, show ((n' : ↥(s.h.secSub s.y)) : X) = (n : X) from hn'n]
          simp [ho_def]
        rw [hw', map_mul, MonoidHom.mem_ker.mp hn', one_mul]
      have heven : Even (Nat.card ↥((M.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y))) := by
        rw [hMθ]
        exact even_card_of_isQuasisimple' hcomp.1
      have h3 : Nat.card ↥(((oddCoreIn M).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y)) ∣
          Nat.card (pPrimeCore 2 ↥M) := by
        have h4 := Subgroup.card_map_dvd ((oddCoreIn M).subgroupOf (s.h.secSub s.y))
          (s.h.subQ s.y)
        rwa [Nat.card_congr (subgroupOfEquivOfLe (hOM.trans hMH)).toEquiv, oddCoreIn,
          card_map_of_injective M.subtype_injective] at h4
      exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl
        ((even_iff_two_dvd.mp heven).trans ((card_dvd_of_le hle).trans h3))
        (pPrimeCore_coprime_card (p := 2) (G := ↥M))
    · intro z hz v hv
      obtain ⟨hzK, hzM⟩ := mem_inf.mp hz
      have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨z, hzM⟩ ∈ center (↥M ⧸ pPrimeCore 2 ↥M) :=
        hZ1 (mem_map_of_mem _ (show (⟨z, hzM⟩ : ↥M) ∈ N₁ from hzK))
      have h2 := mem_center_iff.mp h1 (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hv⟩)
      have h3 : QuotientGroup.mk' (pPrimeCore 2 ↥M)
          ((⟨z, hzM⟩ : ↥M) * ⟨v, hv⟩ * (⟨z, hzM⟩ : ↥M)⁻¹ * (⟨v, hv⟩ : ↥M)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
        group
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact mem_map_of_mem M.subtype h3
  have hinn : ∀ w ∈ M, (s.h.a * w * s.h.a⁻¹)⁻¹ * (m * w * m⁻¹) ∈ oddCoreIn M := by
    intro w hw
    have h1 := comm_mem_oddCoreIn_of_central (B5a.isPerfect_of_isPComponent_subgroupOf hMC hM)
      (hKH.trans hHN) hMK hcen hk (inv_mem hw)
    have hmO : m ∈ normalizer (oddCoreIn M : Set X) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M (pPrimeCore 2 M)
        (le_normalizer hm)
    have h2 := (mem_normalizer_iff.mp hmO _).mp h1
    convert h2 using 1
    group
  have haM : s.h.a ∈ normalizer (M : Set X) := hHN s.secCond.a_mem_secSub
  have hLM' : Seven.Lay s.h s.y = M := hLM
  have hJ0M : Seven.J0 s.h s.y ≤ M ⊓ centralizer ({s.h.a} : Set X) :=
    le_inf (hLM' ▸ Seven.J0_le_Lay s.h s.y)
      (((GSLit.fixedLayer_le_inf _ _).trans inf_le_left).trans s.h.J_le)
  have hJ0pc : IsPComponent 2 ((Seven.J0 s.h s.y).subgroupOf
      (M ⊓ centralizer ({s.h.a} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0M
      (fun w hw => mem_inf.mpr ⟨(mem_inf.mp hw).2, hMC (mem_inf.mp hw).1⟩)
      (Hyp52.isPComponent_secJ0 (h := s.h) (y := s.y))
  have hJ0t : IsSec8JType (↥(Seven.J0 s.h s.y) ⧸ pPrimeCore 2 ↥(Seven.J0 s.h s.y)) p f := by
    obtain ⟨e0⟩ := Hyp52.nonempty_secJ0_equiv (h := s.h) (y := s.y)
    exact isSec8JType_of_mulEquiv (eJ'.trans e0.symm) hJt
  have htype' : IsSec82LType ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) p f :=
    isSec82LType_of_mulEquiv (eM.symm.trans (oddBarCenterEquiv ↥M).symm) htype
  have hZ := center_oddBar_eq_bot_of_inner cover hp hp2 hf hq htype' (Six.a_mul_a_self s.h) haM
    hm hinn hJ0M hJ0pc hJ0t
  refine s.secCond.kappa_of_secL0_inf_eq_bot ?_
  rw [hLM, eq_bot_iff]
  intro b hb
  obtain ⟨hbM, hbB⟩ := mem_inf.mp hb
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hbM⟩ ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (hMC g.2) b hbB).symm
  rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 : (⟨b, hbM⟩ : ↥M) ∈ (s.h.secB0 s.y).subgroupOf M ⊓ pPrimeCore 2 ↥M :=
    mem_inf.mpr ⟨hbB, h1⟩
  have hB2 : IsPGroup 2 ((s.h.secB0 s.y).subgroupOf M) := (s.h.isPGroup_secB0 s.y).comap_subtype
  rw [OddQuot.inf_pPrimeCore_eq_bot hB2, mem_bot] at h2
  exact mem_bot.mpr (congrArg Subtype.val h2)

end Setting0

end Eight2

end CFSG.ComponentClassification.GSThmB
