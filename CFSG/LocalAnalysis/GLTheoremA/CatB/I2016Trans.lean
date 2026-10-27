module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mk_eq_of_mem_glaPPrimeCoreOf {J : Subgroup G} {a b : ↥J}
    (h : (a : G)⁻¹ * (b : G) ∈ GLAPPrimeCoreOf 3 J) :
    (QuotientGroup.mk a : PQ 3 J) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq]
  obtain ⟨n, hn, hnv⟩ := Subgroup.mem_map.1 h
  have : (a⁻¹ * b : ↥J) = n := Subtype.ext (by simpa using hnv.symm)
  rw [this]
  exact hn

theorem sigmaHom_eq_conj {J : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (hgJ : g ∈ J) :
    sigmaHom 3 J ⟨g, hg⟩ = MulAut.conj (QuotientGroup.mk ⟨g, hgJ⟩ : PQ 3 J) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H j =>
    show sigmaQ 3 J g hg (QuotientGroup.mk j) = _
    rw [sigmaQ_mk, MulAut.conj_apply]
    congr 1

theorem conj_mem_glaPPrimeCoreOf {J : Subgroup G} {l u : G} (hl : l ∈ J)
    (hu : u ∈ GLAPPrimeCoreOf 3 J) : l * u * l⁻¹ ∈ GLAPPrimeCoreOf 3 J := by
  haveI : (CFSG.pPrimeCore 3 ↥J).Normal := CFSG.pPrimeCore_normal
  obtain ⟨n, hn, hnv⟩ := Subgroup.mem_map.1 hu
  have hc : (⟨l, hl⟩ : ↥J) * n * (⟨l, hl⟩ : ↥J)⁻¹ ∈ CFSG.pPrimeCore 3 ↥J :=
    Subgroup.Normal.conj_mem inferInstance n hn ⟨l, hl⟩
  refine Subgroup.mem_map.2 ⟨(⟨l, hl⟩ : ↥J) * n * (⟨l, hl⟩ : ↥J)⁻¹, hc, ?_⟩
  subst hnv
  rfl

theorem sigma_eq_conj_of_induces {J : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (J : Set G))
    (hi : InducesInnerMod 3 J t) :
    ∃ x : PQ 3 J, sigmaHom 3 J ⟨t, ht⟩ = MulAut.conj x := by
  obtain ⟨l, hlJ, hl⟩ := hi
  refine ⟨QuotientGroup.mk ⟨l, hlJ⟩, ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H j =>
    have hz : t * j * t⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 ht j).1 j.2
    have hla : l⁻¹ * (t * j * t⁻¹) * l ∈ J :=
      J.mul_mem (J.mul_mem (J.inv_mem hlJ) hz) hlJ
    set a : ↥J := ⟨l⁻¹ * (t * j * t⁻¹) * l, hla⟩ with ha
    have key := hl (t * j * t⁻¹) hz
    have hcomm : t⁻¹ * (t * j * t⁻¹) * t = (j : G) := by group
    rw [hcomm] at key
    have hmk : (QuotientGroup.mk a : PQ 3 J) = QuotientGroup.mk j :=
      mk_eq_of_mem_glaPPrimeCoreOf key
    show sigmaQ 3 J t ht (QuotientGroup.mk j) = _
    rw [sigmaQ_mk, MulAut.conj_apply]
    have e1 : (QuotientGroup.mk ⟨l, hlJ⟩ : PQ 3 J) * QuotientGroup.mk a *
        (QuotientGroup.mk ⟨l, hlJ⟩)⁻¹ = QuotientGroup.mk (conjJ J t ht j) := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp [conjJ_val, ha, mul_assoc]
    rw [hmk] at e1
    exact e1.symm

theorem mem_centModSubgroup_of_sigma_eq_one {J : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (J : Set G)) (h1 : sigmaHom 3 J ⟨t, ht⟩ = 1) :
    t ∈ centModSubgroup 3 J := by
  refine ⟨ht, fun l hl => ?_⟩
  have hlJ : l ∈ J := hl
  have hfix := congrArg (fun φ : MulAut (PQ 3 J) => φ (QuotientGroup.mk ⟨l, hlJ⟩)) h1
  simp only [MulAut.one_apply] at hfix
  have hfix' : sigmaQ 3 J t ht (QuotientGroup.mk ⟨l, hlJ⟩) = QuotientGroup.mk ⟨l, hlJ⟩ := hfix
  rw [sigmaQ_mk] at hfix'
  have hm := QuotientGroup.eq.1 hfix'
  have hu : ((t * l * t⁻¹)⁻¹ * l : G) ∈ GLAPPrimeCoreOf 3 J :=
    Subgroup.mem_map_of_mem J.subtype hm
  have hu' := conj_mem_glaPPrimeCoreOf hlJ hu
  have heq : l * ((t * l * t⁻¹)⁻¹ * l) * l⁻¹ = ⁅l, t⁆ := by
    rw [commutatorElement_def]
    group
  rw [← heq]
  exact hu'

theorem fixSub_sigma_eq {J : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (J : Set G))
    (hy3 : y ^ 3 = 1) :
    fixSub (sigmaHom 3 J ⟨y, hy⟩) =
      ((J ⊓ Subgroup.centralizer ({y} : Set G)).comap J.subtype).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) q
    have hfix : sigmaQ 3 J y hy (QuotientGroup.mk j) = QuotientGroup.mk j := hq
    obtain ⟨x, hxj, hxy⟩ := exists_fixed_in_fiber J y hy hy3 j hfix
    refine Subgroup.mem_map.2 ⟨x, ?_, hxj⟩
    rw [Subgroup.mem_comap, Subgroup.mem_inf]
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hv := congrArg Subtype.val hxy
    rw [conjJ_val] at hv
    calc h * (x : G) = (h * x * h⁻¹) * h := by group
      _ = x * h := by rw [hv]
  · intro hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
    rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hx
    have hcomm : y * (x : G) * y⁻¹ = x := by
      have hc' : y * (x : G) = (x : G) * y := hx.2 y (Set.mem_singleton y)
      calc y * (x : G) * y⁻¹ = (x * y) * y⁻¹ := by rw [hc']
        _ = x := by group
    show sigmaQ 3 J y hy (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [sigmaQ_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ_val, hcomm]

theorem isSubnormal_image_fixSub {J I : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (J : Set G)) (hy3 : y ^ 3 = 1)
    (hI : CFSG.Open.IsSubnormal I (J ⊓ Subgroup.centralizer ({y} : Set G))) :
    CFSG.Open.IsSubnormal ((I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)))
      (fixSub (sigmaHom 3 J ⟨y, hy⟩)) := by
  rw [fixSub_sigma_eq hy hy3]
  exact CFSG.Open.IsSubnormal.map _ (CFSG.Open.IsSubnormal.comap J.subtype hI)

theorem catalogIs_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs S Q) : catalogIs S' Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem isTypeWithCenter_of_quotEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : (X ⧸ CFSG.pPrimeCore 3 X) ≃* (Y ⧸ CFSG.pPrimeCore 3 Y)) {Q : TauCeti.CFSGIndex → Prop}
    {z : ℕ} (h : catalogIs ((X ⧸ CFSG.pPrimeCore 3 X) ⧸
        Subgroup.center (X ⧸ CFSG.pPrimeCore 3 X)) Q ∧
      Nat.card (Subgroup.center (X ⧸ CFSG.pPrimeCore 3 X)) = z) :
    catalogIs ((Y ⧸ CFSG.pPrimeCore 3 Y) ⧸ Subgroup.center (Y ⧸ CFSG.pPrimeCore 3 Y)) Q ∧
      Nat.card (Subgroup.center (Y ⧸ CFSG.pPrimeCore 3 Y)) = z := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · exact catalogIs_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e
        (Subgroup.map_center_eq e)) h1
  · rw [← h2, ← Subgroup.map_center_eq e]
    exact (Nat.card_congr ((Subgroup.center _).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm

@[expose] noncomputable def TH (J : Subgroup G) {T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (J : Set G)) : Subgroup (MulAut (PQ 3 J)) :=
  ((sigmaHom 3 J).comp (Subgroup.inclusion hT : ↥T →* ↥(Subgroup.normalizer (J : Set G)))).range

theorem mem_TH {J : Subgroup G} {T : Subgroup G} {hT : T ≤ Subgroup.normalizer (J : Set G)}
    {h : MulAut (PQ 3 J)} :
    h ∈ TH J hT ↔ ∃ t : ↥T, sigmaHom 3 J (Subgroup.inclusion hT t) = h :=
  MonoidHom.mem_range

theorem isPGroup_TH {J : Subgroup G} {T : Subgroup G} (hT : T ≤ Subgroup.normalizer (J : Set G))
    (hT2 : IsPGroup 2 T) : IsPGroup 2 (TH J hT) := by
  unfold TH
  exact hT2.of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem inner_of_TH {J : Subgroup G} {T : Subgroup G} (hT : T ≤ Subgroup.normalizer (J : Set G))
    (hinner : ∀ t ∈ T, InducesInnerMod 3 J t) :
    ∀ h ∈ TH J hT, ∃ x : PQ 3 J, MulAut.conj x = h := by
  intro h hh
  obtain ⟨t, rfl⟩ := mem_TH.1 hh
  obtain ⟨x, hx⟩ := sigma_eq_conj_of_induces (t := (t : G)) (hT t.2) (hinner t t.2)
  exact ⟨x, hx.symm⟩

theorem TH_ne_bot {J : Subgroup G} {T : Subgroup G} (hT : T ≤ Subgroup.normalizer (J : Set G))
    (hfaith : T ⊓ centModSubgroup 3 J = ⊥) (hT1 : T ≠ ⊥) : TH J hT ≠ ⊥ := by
  intro hbot
  apply hT1
  rw [eq_bot_iff]
  intro t ht
  have htT : (⟨t, ht⟩ : ↥T) ∈ (⊤ : Subgroup ↥T) := Subgroup.mem_top _
  have h1 : sigmaHom 3 J (Subgroup.inclusion hT ⟨t, ht⟩) ∈ TH J hT :=
    mem_TH.2 ⟨⟨t, ht⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have hc := mem_centModSubgroup_of_sigma_eq_one (hT ht) h1
  have hm : t ∈ T ⊓ centModSubgroup 3 J := ⟨ht, hc⟩
  rw [hfaith, Subgroup.mem_bot] at hm
  rw [Subgroup.mem_bot, hm]

theorem sigma_conj_eq {J : Subgroup G} {g t : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (ht : t ∈ Subgroup.normalizer (J : Set G)) :
    sigmaHom 3 J ⟨g, hg⟩ * sigmaHom 3 J ⟨t, ht⟩ * (sigmaHom 3 J ⟨g, hg⟩)⁻¹ =
      sigmaHom 3 J ⟨g * t * g⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg ht)
        (Subgroup.inv_mem _ hg)⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem TH_conj_iff {J : Subgroup G} {T : Subgroup G} (hT : T ≤ Subgroup.normalizer (J : Set G))
    {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) (hgT : g ∈ Subgroup.normalizer (T : Set G))
    (h : MulAut (PQ 3 J)) :
    h ∈ TH J hT ↔ sigmaHom 3 J ⟨g, hg⟩ * h * (sigmaHom 3 J ⟨g, hg⟩)⁻¹ ∈ TH J hT := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hg
  have hginvT : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := Subgroup.inv_mem _ hgT
  constructor
  · intro hh
    obtain ⟨t, rfl⟩ := mem_TH.1 hh
    rw [mem_TH]
    refine ⟨⟨g * (t : G) * g⁻¹, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hgT t).1 t.2
    · show sigmaHom 3 J ⟨g * (t : G) * g⁻¹, _⟩ =
        sigmaHom 3 J ⟨g, hg⟩ * sigmaHom 3 J ⟨(t : G), hT t.2⟩ * (sigmaHom 3 J ⟨g, hg⟩)⁻¹
      exact (sigma_conj_eq hg (hT t.2)).symm
  · intro hh
    obtain ⟨t, ht⟩ := mem_TH.1 hh
    rw [mem_TH]
    refine ⟨⟨g⁻¹ * (t : G) * g, ?_⟩, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hginvT t).1 t.2
      simpa using this
    · have hh' : h = (sigmaHom 3 J ⟨g, hg⟩)⁻¹ * (sigmaHom 3 J (Subgroup.inclusion hT t)) *
          sigmaHom 3 J ⟨g, hg⟩ := by
        rw [ht]
        group
      rw [hh']
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1

@[expose] noncomputable def KphiQ (J K : Subgroup G) : ↥(K.comap J.subtype) →* PQ 3 J :=
  (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)).comp (K.comap J.subtype).subtype

theorem mem_pPrimeCore_of_mem_glaPPrimeCoreOf {J K : Subgroup G} (hKJ : K ≤ J) {x : ↥K}
    (hx : (x : G) ∈ GLAPPrimeCoreOf 3 J) : x ∈ CFSG.pPrimeCore 3 ↥K := by
  classical
  let W : Subgroup ↥K := (GLAPPrimeCoreOf 3 J).comap K.subtype
  haveI hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ GLAPPrimeCoreOf 3 J := hn
    have hgJ : (g : G) ∈ J := hKJ g.2
    have := conj_mem_glaPPrimeCoreOf hgJ hn'
    exact this
  have hWc : Nat.Coprime 3 (Nat.card W) := by
    have hinj : Function.Injective K.subtype := Subtype.val_injective
    have h1 : Nat.card (W.map K.subtype) = Nat.card W := Subgroup.card_map_of_injective hinj
    have h2 : W.map K.subtype ≤ GLAPPrimeCoreOf 3 J := by
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h3 : Nat.card (W.map K.subtype) ∣ Nat.card (GLAPPrimeCoreOf 3 J) :=
      Subgroup.card_dvd_of_le h2
    have h4 : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 J)) := by
      have hJ : Nat.card (GLAPPrimeCoreOf 3 J) = Nat.card (CFSG.pPrimeCore 3 ↥J) :=
        Subgroup.card_map_of_injective Subtype.val_injective
      rw [hJ]
      exact CFSG.pPrimeCore_coprime_card
    rw [← h1]
    exact Nat.Coprime.coprime_dvd_right h3 h4
  have hWle : W ≤ CFSG.pPrimeCore 3 ↥K :=
    CFSG.le_pPrimeCore_of_normal_coprime hWn hWc
  exact hWle (show x ∈ W from hx)

theorem hasA6Quot_KphiQ {J K : Subgroup G} (hKJ : K ≤ J)
    (hKt : catalogIs (PSimple 3 K) S8.isA6) :
    ∃ (A₀ : Subgroup (PQ 3 J)) (S : Type) (_ : Group S) (f : ↥A₀ →* S),
      A₀ ≤ (KphiQ J K).range ∧ catalogIs S S8.isA6 ∧ Function.Surjective f := by
  classical
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  haveI : (Subgroup.center (PQ 3 J)).Normal := inferInstance
  let ρ : ↥(K.comap J.subtype) →* ↥K :=
    { toFun := fun k => ⟨k.1.1, k.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let ψ0 : ↥(K.comap J.subtype) →* PQuot 3 K :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp ρ
  let ψ : ↥(K.comap J.subtype) →* PSimple 3 K :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 K))).comp ψ0
  have hle : (KphiQ J K).ker ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have hkG : ((k : ↥(K.comap J.subtype)) : ↥J) ∈ (K.comap J.subtype) := k.2
    have hmem : (ρ k : G) ∈ GLAPPrimeCoreOf 3 J := by
      have hk' : (QuotientGroup.mk (k.1) : PQ 3 J) = 1 := hk
      rw [QuotientGroup.eq_one_iff] at hk'
      exact Subgroup.mem_map_of_mem J.subtype hk'
    have hO : ρ k ∈ CFSG.pPrimeCore 3 ↥K := mem_pPrimeCore_of_mem_glaPPrimeCoreOf hKJ hmem
    have h0 : ψ0 k = 1 := by
      show (QuotientGroup.mk (ρ k) : PQuot 3 K) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hO
    show (QuotientGroup.mk (ψ0 k) : PSimple 3 K) = 1
    rw [h0, QuotientGroup.eq_one_iff]
    exact Subgroup.one_mem _
  have hψs : Function.Surjective ψ := by
    intro s
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 K)) s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) c
    have hxJ : (x : G) ∈ J := hKJ x.2
    exact ⟨⟨⟨x.1, hxJ⟩, x.2⟩, rfl⟩
  let L := QuotientGroup.lift (KphiQ J K).ker ψ hle
  have hLs : Function.Surjective L := by
    intro s
    obtain ⟨k, hk⟩ := hψs s
    exact ⟨QuotientGroup.mk k, hk⟩
  let f : ↥((KphiQ J K).range) →* PSimple 3 K :=
    L.comp (QuotientGroup.quotientKerEquivRange (KphiQ J K)).symm.toMonoidHom
  refine ⟨(KphiQ J K).range, PSimple 3 K, inferInstance, f, le_rfl, hKt, ?_⟩
  exact hLs.comp (QuotientGroup.quotientKerEquivRange (KphiQ J K)).symm.surjective

end CFSG.LocalAnalysis.GLTheoremA.I2016
