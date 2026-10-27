module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28L45
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVOuter
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ThreeProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def l28ivZ (P : Sylow 3 G) (x : G) (J : Subgroup G) : Subgroup G :=
  (((P : Subgroup G).subgroupOf (centralizer ({x} : Set G))) ⊓ (l34Hom x J).ker).map
    (centralizer ({x} : Set G)).subtype

theorem mem_l28ivZ {P : Sylow 3 G} {x : G} {J : Subgroup G} {z : G} :
    z ∈ l28ivZ P x J ↔ ∃ hz : z ∈ centralizer ({x} : Set G), z ∈ (P : Subgroup G) ∧
      l34Hom x J ⟨z, hz⟩ = 1 := by
  constructor
  · rintro ⟨c, ⟨hcP, hck⟩, rfl⟩
    exact ⟨c.2, mem_subgroupOf.mp hcP, hck⟩
  · rintro ⟨hz, hzP, h1⟩
    exact ⟨⟨z, hz⟩, ⟨mem_subgroupOf.mpr hzP, h1⟩, rfl⟩

theorem l28iv_eq_one_of_mk_eq_one {P : Sylow 3 G} {x : G} (c : ↥(centralizer ({x} : Set G)))
    (hcP : (c : G) ∈ (P : Subgroup G))
    (h1 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c = 1) :
    c = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcO : c ∈ primeComplementCore (G := centralizer ({x} : Set G)) 3 :=
    (QuotientGroup.eq_one_iff c).mp h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨(c : G), hcP⟩
  have hk' : orderOf c = 3 ^ k := by
    rw [← hk, Subgroup.orderOf_mk (c : G) hcP, Subgroup.orderOf_coe]
  have h2 : orderOf c ∣ Nat.card (primeComplementCore (G := centralizer ({x} : Set G)) 3) :=
    Subgroup.orderOf_dvd_natCard _ hcO
  have h3 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (primeComplementCore_coprime 3)) (dvd_of_eq hk') h2
  exact orderOf_eq_one_iff.mp h3

theorem l28iv_hom_eq_one_iff {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL28Normal M x J)
    (c : ↥(centralizer ({x} : Set G))) :
    l34Hom x J c = 1 ↔
      QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
        reducedCentralizerOfJ x J := by
  have hDn := l28_reducedCentralizer_normal hJ
  change QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore _ = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self]

theorem l28iv_Z_facts (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    l28ivZ P x J ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
      x ∈ l28ivZ P x J ∧
      ((P : Subgroup G) ⊓ J) ⊓ l28ivZ P x J = ⊥ ∧
      (∀ t ∈ (P : Subgroup G) ⊓ J, ∀ z ∈ l28ivZ P x J, t * z = z * t) ∧
      IsCyclic ↥(l28ivZ P x J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC := hJ.le_centralizer
  set ρ : C →* GenericReduced 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hρ
  have hker := (l28_T_data hS hU0 hK1 hp hM hgen hJ).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzC, hzP, -⟩ := mem_l28ivZ.mp hz
    exact ⟨hzP, hzC⟩
  · exact mem_l28ivZ.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, hgen.1,
      l28_hom_x hS hU0 hp hM hgen hJ⟩
  · refine eq_bot_iff.mpr fun g hg => ?_
    obtain ⟨hgC, -, h1⟩ := mem_l28ivZ.mp hg.2
    have := hker ⟨g, hgC⟩ hg.1 h1
    exact mem_bot.mpr (congrArg Subtype.val this)
  · intro t ht z hz
    obtain ⟨hzC, hzP, h1⟩ := mem_l28ivZ.mp hz
    set tc : C := ⟨t, hJC ht.2⟩ with htc
    set zc : C := ⟨z, hzC⟩ with hzc
    have hzD : ρ zc ∈ reducedCentralizerOfJ x J := (l28iv_hom_eq_one_iff hJ zc).mp h1
    have htJ : ρ tc ∈ r1sBar x J := ⟨tc, mem_subgroupOf.mpr ht.2, rfl⟩
    have hcomm : ρ tc * ρ zc = ρ zc * ρ tc :=
      mem_centralizer_iff.mp (by rw [← r1s_reducedCentralizerOfJ_eq]; exact hzD) _ htJ
    have hw : tc * zc * tc⁻¹ * zc⁻¹ = 1 := by
      refine l28iv_eq_one_of_mk_eq_one (P := P) _ ?_ ?_
      · exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem
          ((P : Subgroup G).mul_mem ht.1 hzP) ((P : Subgroup G).inv_mem ht.1))
          ((P : Subgroup G).inv_mem hzP)
      · have key : ρ tc * ρ zc * (ρ tc)⁻¹ * (ρ zc)⁻¹ = 1 := by
          rw [hcomm]
          group
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        exact key
    have hw' : t * z * t⁻¹ * z⁻¹ = 1 := congrArg Subtype.val hw
    calc t * z = (t * z * t⁻¹ * z⁻¹) * (z * t) := by group
      _ = z * t := by rw [hw', one_mul]
  ·
    set H : Subgroup C := ((P : Subgroup G).subgroupOf C) ⊓ (l34Hom x J).ker with hH
    have hinj : Function.Injective (ρ.comp H.subtype) := by
      rw [injective_iff_map_eq_one]
      intro h hh
      exact Subtype.ext (l28iv_eq_one_of_mk_eq_one (P := P) (h : C)
        (mem_subgroupOf.mp h.2.1) hh)
    have hrange : (ρ.comp H.subtype).range ≤ reducedCentralizerOfJ x J := by
      rintro _ ⟨h, rfl⟩
      exact (l28iv_hom_eq_one_iff hJ (h : C)).mp h.2.2
    have hDc : IsCyclic ↥(reducedCentralizerOfJ x J) :=
      l28_reducedCentralizer_isCyclic hS hU0 hp hM hgen hJ
    have hRc : IsCyclic ↥((ρ.comp H.subtype).range) := by
      have : IsCyclic ↥(((ρ.comp H.subtype).range).subgroupOf (reducedCentralizerOfJ x J)) :=
        inferInstance
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hrange).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hrange).surjective
    have hHc : IsCyclic ↥H :=
      isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
        (MonoidHom.ofInjective hinj).symm.surjective
    exact isCyclic_of_surjective (H.equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
      (H.equivMapOfInjective C.subtype C.subtype_injective).surjective

theorem l28iv_card_le (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    Nat.card ↥((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ≤
      3 * Nat.card ↥(((P : Subgroup G) ⊓ J) ⊔ l28ivZ P x J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  obtain ⟨-, -, hTZ, hcomm, -⟩ := l28iv_Z_facts hS hU0 hK1 hp hM hgen hJ
  have hTc : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2 :=
    (l28_T_data hS hU0 hK1 hp hM hgen hJ).2.2
  set Q' : Subgroup C := (P : Subgroup G).subgroupOf C with hQ'
  set π : C →* L34Quot x J := l34Hom x J with hπ
  have hcardQ : Nat.card ↥((P : Subgroup G) ⊓ C) = Nat.card Q' := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective C.subtype_injective]
  have hcardZ : Nat.card ↥(l28ivZ P x J) = Nat.card ↥(π.ker ⊓ Q') := by
    rw [l28ivZ, Subgroup.card_map_of_injective C.subtype_injective, inf_comm]
  have hsplit : Nat.card Q' = Nat.card (Q'.map π) * Nat.card ↥(π.ker ⊓ Q') := by
    have e1 := Subgroup.relIndex_mul_card π.ker Q'
    rw [Subgroup.relIndex_ker] at e1
    exact e1.symm
  obtain ⟨hKn, hKc, hKL⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  set K : Subgroup (L34Quot x J) := l34Img x J J with hK
  have : K.Normal := hKn
  set χ : L34Quot x J →* MulAut ↥K := MulAut.conjNormal with hχ
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hac : a ∈ centralizer (K : Set (L34Quot x J)) := by
      rw [mem_centralizer_iff]
      intro k hk
      have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : L34Quot x J)) ha
      simp only [hχ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc k * a = (a * k * a⁻¹) * a := by rw [h1]
        _ = a * k := by group
    rw [hKc] at hac
    exact mem_bot.mp hac
  have hAp : IsPGroup 3 (Q'.map π) := (P.isPGroup'.comap_subtype).map π
  have himg : Nat.card (Q'.map π) ≤ 27 := by
    have hcardA : Nat.card (MulAut ↥K) = 1512 := l28m_card_mulAut hKL
    obtain ⟨k, hk⟩ := (hAp.map χ).exists_card_eq
    have hdvd : 3 ^ k ∣ 1512 := by
      rw [← hk, ← hcardA]
      exact Subgroup.card_subgroup_dvd_card _
    have hk3 : k ≤ 3 := by
      by_contra hk4
      push Not at hk4
      have : 3 ^ 4 ∣ 1512 := (Nat.pow_dvd_pow 3 hk4).trans hdvd
      norm_num at this
    rw [← Subgroup.card_map_of_injective hχinj, hk]
    calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 27 := by norm_num
  have hTN : (P : Subgroup G) ⊓ J ≤ normalizer ((l28ivZ P x J : Subgroup G) : Set G) := by
    intro t ht
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz => ?_)
    exact (hcomm t ht z hz).symm
  have hsup := e9_card_sup_mul_card_inf hTN
  rw [hTZ, Subgroup.card_bot, mul_one, hTc] at hsup
  rw [hcardQ, hsplit, hsup, ← hcardZ]
  calc Nat.card (Q'.map π) * Nat.card ↥(l28ivZ P x J) ≤ 27 * Nat.card ↥(l28ivZ P x J) :=
        Nat.mul_le_mul_right _ himg
    _ = 3 * (3 ^ 2 * Nat.card ↥(l28ivZ P x J)) := by ring

theorem l28iv_mem_sup_of_hom_mem (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    {c : ↥(centralizer ({x} : Set G))} (hcP : (c : G) ∈ (P : Subgroup G))
    (hcK : l34Hom x J c ∈ l34Img x J J) :
    (c : G) ∈ ((P : Subgroup G) ⊓ J) ⊔ l28ivZ P x J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hsyl, -, -⟩ := l28_T_data hS hU0 hK1 hp hM hgen hJ
  have hTA : l34Img x J ((P : Subgroup G) ⊓ J) ≤
      ((P : Subgroup G).subgroupOf (centralizer ({x} : Set G))).map (l34Hom x J) ⊓
        l34Img x J J := by
    refine le_inf (Subgroup.map_mono fun t ht => ?_) (Subgroup.map_mono fun t ht => ?_)
    · exact mem_subgroupOf.mpr (mem_subgroupOf.mp ht).1
    · exact mem_subgroupOf.mpr (mem_subgroupOf.mp ht).2
  have hAp : IsPGroup 3 ↥(((P : Subgroup G).subgroupOf (centralizer ({x} : Set G))).map
      (l34Hom x J) ⊓ l34Img x J J) :=
    ((P.isPGroup'.comap_subtype).map (l34Hom x J)).to_le inf_le_left
  have heq := hsyl.eq_of_le hTA inf_le_right hAp
  have hcA : l34Hom x J c ∈ ((P : Subgroup G).subgroupOf (centralizer ({x} : Set G))).map
      (l34Hom x J) ⊓ l34Img x J J := ⟨⟨c, mem_subgroupOf.mpr hcP, rfl⟩, hcK⟩
  rw [heq] at hcA
  obtain ⟨t, ht, htc⟩ := hcA
  have htT : (t : G) ∈ (P : Subgroup G) ⊓ J := mem_subgroupOf.mp ht
  have hw1 : l34Hom x J (t⁻¹ * c) = 1 := by rw [map_mul, map_inv, htc, inv_mul_cancel]
  have hw : ((t⁻¹ * c : ↥(centralizer ({x} : Set G))) : G) ∈ l28ivZ P x J :=
    mem_l28ivZ.mpr ⟨(t⁻¹ * c).2, (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem htT.1) hcP,
      hw1⟩
  have e : (c : G) = (t : G) * ((t⁻¹ * c : ↥(centralizer ({x} : Set G))) : G) := by
    change (c : G) = (t : G) * ((t : G)⁻¹ * c)
    group
  rw [e]
  exact Subgroup.mul_mem_sup htT hw

theorem l28iv_outerOn_of_not_mem (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) {q : G}
    (hqP : q ∈ (P : Subgroup G)) (hqC : q ∈ centralizer ({x} : Set G))
    (hq : q ∉ ((P : Subgroup G) ⊓ J) ⊔ l28ivZ P x J) : L28OuterOn J q := by
  rintro ⟨j, hj, hjj⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC := hJ.le_centralizer
  set ρ : C →* GenericReduced 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hρ
  have hker := ker_r1sHom_l28 hJ
  have hOJ : rankThreePrimeCore 3 J ≤ J := sSup_le fun _ hN => hN.1
  set qc : C := ⟨q, hqC⟩ with hqc
  set jc : C := ⟨j, hJC hj⟩ with hjc
  have hconj : ∀ j'c : C, (j'c : G) ∈ J → ρ (qc * j'c * qc⁻¹) = ρ (jc * j'c * jc⁻¹) := by
    intro j'c hj'
    have hw := hjj (j'c : G) hj'
    have hwJ := hOJ hw
    have h1 : ρ (Subgroup.inclusion hJC ⟨_, hwJ⟩) = 1 := by
      have hmem : (⟨_, hwJ⟩ : ↥J) ∈ (r1sHom x hJC).ker := by
        rw [hker]
        exact mem_subgroupOf.mpr hw
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
    have h2 : Subgroup.inclusion hJC ⟨_, hwJ⟩ = (qc * j'c * qc⁻¹)⁻¹ * (jc * j'c * jc⁻¹) :=
      Subtype.ext rfl
    rw [h2, map_mul, map_inv] at h1
    exact inv_mul_eq_one.mp h1
  have hD : (ρ jc)⁻¹ * ρ qc ∈ reducedCentralizerOfJ x J := by
    rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
    rintro _ ⟨j'c, hj', rfl⟩
    have h := hconj j'c (mem_subgroupOf.mp hj')
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at h
    calc ρ j'c * ((ρ jc)⁻¹ * ρ qc) = (ρ jc)⁻¹ * (ρ jc * ρ j'c * (ρ jc)⁻¹) * ρ qc := by group
      _ = (ρ jc)⁻¹ * (ρ qc * ρ j'c * (ρ qc)⁻¹) * ρ qc := by rw [h]
      _ = ((ρ jc)⁻¹ * ρ qc) * ρ j'c := by group
  have h1 : l34Hom x J (jc⁻¹ * qc) = 1 :=
    (l28iv_hom_eq_one_iff hJ (jc⁻¹ * qc)).mpr (by rw [map_mul, map_inv]; exact hD)
  have hπ : l34Hom x J qc = l34Hom x J jc := by
    rw [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.mp h1).symm
  have hqK : l34Hom x J qc ∈ l34Img x J J := by
    rw [hπ]
    exact ⟨jc, mem_subgroupOf.mpr hj, rfl⟩
  exact hq (l28iv_mem_sup_of_hom_mem hS hU0 hK1 hp hM hgen hJ (c := qc) hqP hqK)

theorem l28iv_exists_moved (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) {q : G}
    (hqP : q ∈ (P : Subgroup G)) (hqC : q ∈ centralizer ({x} : Set G))
    (hq : q ∉ ((P : Subgroup G) ⊓ J) ⊔ l28ivZ P x J) :
    ∃ t ∈ (P : Subgroup G) ⊓ J, q * t * q⁻¹ ≠ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  obtain ⟨hsyl, -, -⟩ := l28_T_data hS hU0 hK1 hp hM hgen hJ
  obtain ⟨hKn, hKc, hKL⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  set K : Subgroup (L34Quot x J) := l34Img x J J with hK
  have : K.Normal := hKn
  set qc : C := ⟨q, hqC⟩ with hqc
  have hqK : l34Hom x J qc ∉ K := fun h =>
    hq (l28iv_mem_sup_of_hom_mem hS hU0 hK1 hp hM hgen hJ (c := qc) hqP h)
  set a : L34Quot x J := l34Hom x J qc with ha
  set α : MulAut ↥K := MulAut.conjNormal a with hα
  obtain ⟨mq, hmq⟩ := P.isPGroup' ⟨q, hqP⟩
  have hq3 : q ^ (3 ^ mq) = 1 := congrArg Subtype.val hmq
  have hα3 : α ^ (3 ^ mq) = 1 := by
    have h3 : a ^ (3 ^ mq) = 1 := by
      rw [ha, ← map_pow, show qc ^ (3 ^ mq) = 1 from Subtype.ext (by simpa using hq3), map_one]
    rw [hα, ← map_pow, h3, map_one]
  have hout : ∀ k : ↥K, MulAut.conj k ≠ α := by
    intro k hk
    apply hqK
    have hc : (k : L34Quot x J)⁻¹ * a ∈ centralizer (K : Set (L34Quot x J)) := by
      rw [mem_centralizer_iff]
      intro k' hk'
      have h1 : (k : L34Quot x J) * k' * (k : L34Quot x J)⁻¹ = a * k' * a⁻¹ := by
        have := congrArg (fun φ : MulAut ↥K => ((φ ⟨k', hk'⟩ : ↥K) : L34Quot x J)) hk
        simpa [hα, MulAut.conjNormal_apply] using this
      calc k' * ((k : L34Quot x J)⁻¹ * a)
          = (k : L34Quot x J)⁻¹ * ((k : L34Quot x J) * k' * (k : L34Quot x J)⁻¹) * a := by group
        _ = (k : L34Quot x J)⁻¹ * (a * k' * a⁻¹) * a := by rw [h1]
        _ = (k : L34Quot x J)⁻¹ * a * k' := by group
    rw [hKc, mem_bot, inv_mul_eq_one] at hc
    rw [← hc]
    exact k.2
  obtain ⟨S, hS'⟩ := hsyl
  obtain ⟨s, hs, hαs⟩ := l28m_outer_moves_sylow' hKL S hα3 hout
  have hsT : (s : L34Quot x J) ∈ l34Img x J ((P : Subgroup G) ⊓ J) := by
    rw [← hS']
    exact ⟨s, hs, rfl⟩
  obtain ⟨tc, htc, htcs⟩ := hsT
  refine ⟨tc, mem_subgroupOf.mp htc, fun heq => hαs (Subtype.ext ?_)⟩
  rw [hα, MulAut.conjNormal_apply]
  rw [← htcs, ha, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext heq

theorem l28iv_T_cyclic (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    ∃ t₀ : G, (P : Subgroup G) ⊓ J = zpowers t₀ ∧ orderOf t₀ = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hsyl, -, hTc⟩ := l28_T_data hS hU0 hK1 hp hM hgen hJ
  obtain ⟨-, -, hKL⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨S, hS'⟩ := hsyl
  have hScyc := l28m_sylow_isCyclic hKL S
  obtain ⟨s, hs⟩ := hScyc.exists_generator
  have hScard : Nat.card (S : Subgroup ↥(l34Img x J J)) = 9 := by
    rw [l28m_card_sylow hKL S]
    norm_num
  have hso : orderOf (((s : ↥(l34Img x J J)) : L34Quot x J)) = 9 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ← hScard]
    exact orderOf_eq_card_of_forall_mem_zpowers hs
  have hsT : ((s : ↥(l34Img x J J)) : L34Quot x J) ∈ l34Img x J ((P : Subgroup G) ⊓ J) := by
    rw [← hS']
    exact ⟨s, s.2, rfl⟩
  obtain ⟨tc, htc, htcs⟩ := hsT
  have htT : (tc : G) ∈ (P : Subgroup G) ⊓ J := mem_subgroupOf.mp htc
  have hord : orderOf (tc : G) = 9 := by
    have h1 : orderOf (l34Hom x J tc) ∣ orderOf tc := orderOf_map_dvd _ tc
    rw [htcs, hso, ← Subgroup.orderOf_coe] at h1
    have h2 : orderOf (tc : G) ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard _ htT
      rwa [hTc] at this
    exact Nat.dvd_antisymm h2 h1
  refine ⟨tc, ?_, hord⟩
  exact (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htT)
    (by rw [Nat.card_zpowers, hord, hTc]; norm_num)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
