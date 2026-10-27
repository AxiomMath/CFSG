module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Pumpdown
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem mem_centralizerResidual_of_two_pow {K : Subgroup X} {t : X}
    (htN : t ∈ normalizer (K : Set X)) (ht2 : IsPGroup 2 (zpowers t))
    (hperf : Group.IsPerfect (Bar K)) (htriv : barAction K ⟨t, htN⟩ = 1) {w : X}
    (hwK : w ∈ K) (hwt : w ∈ centralizer {t}) {n : ℕ} (hwn : w ^ 2 ^ n = 1) :
    w ∈ centralizerResidual K t := by
  set C := K ⊓ centralizer ({t} : Set X) with hC
  set J := centralizerResidual K t with hJ
  have hsurj := range_barMap_centralizerResidual htN ht2 hperf htriv
  obtain ⟨j, hj⟩ : (QuotientGroup.mk ⟨w, hwK⟩ : Bar K) ∈
      (barMap K (centralizerResidual_le_left (g := t))).range := hsurj ▸ mem_top _
  have hjC : (j : X) ∈ C := centralizerResidual_le j.2
  have ho : (j : X)⁻¹ * w ∈ (pPrimeCore 2 ↥K).map K.subtype := by
    have h1 : (QuotientGroup.mk ⟨(j : X), hjC.1⟩ : Bar K) = QuotientGroup.mk ⟨w, hwK⟩ := hj
    rw [QuotientGroup.eq] at h1
    exact ⟨_, h1, rfl⟩
  set O := (pPrimeCore 2 ↥K).map K.subtype ⊓ centralizer ({t} : Set X) with hO
  have hOC : O ≤ C := fun x hx => ⟨map_subtype_le _ hx.1, hx.2⟩
  have hOnorm : (O.subgroupOf C).Normal := by
    rw [normal_subgroupOf_iff hOC]
    intro a c ha hc
    have hct : c ∈ centralizer ({t} : Set X) := (mem_inf.mp hc).2
    have hat : a ∈ centralizer ({t} : Set X) := (mem_inf.mp ha).2
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hct hat) (inv_mem hct)⟩
    have hcN : c ∈ normalizer (((pPrimeCore 2 ↥K).map K.subtype : Subgroup X) : Set X) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 ↥K)
        (le_normalizer hc.1)
    exact (mem_normalizer_iff.mp hcN a).mp (mem_inf.mp ha).1
  have hOodd : Odd (Nat.card ↥(O.subgroupOf C)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOC).toEquiv]
    have hdvd : Nat.card ↥O ∣ Nat.card ↥((pPrimeCore 2 ↥K).map K.subtype) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hdvd
    exact (odd_card_pPrimeCore_two ↥K).of_dvd_nat hdvd
  have hJC : J ≤ C := centralizerResidual_le
  have hJn : (J.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJC).mpr le_normalizer_centralizerResidual
  have hwC : w ∈ C := ⟨hwK, hwt⟩
  have hmem : (⟨w, hwC⟩ : ↥C) ∈ J.subgroupOf C ⊔ O.subgroupOf C := by
    have hw : (⟨w, hwC⟩ : ↥C) = ⟨(j : X), hjC⟩ * ⟨(j : X)⁻¹ * w, mul_mem (inv_mem hjC) hwC⟩ :=
      Subtype.ext (by simp)
    rw [hw]
    exact mul_mem (mem_sup_left (show (⟨(j : X), hjC⟩ : ↥C) ∈ J.subgroupOf C from j.2))
      (mem_sup_right (show (⟨(j : X)⁻¹ * w, _⟩ : ↥C) ∈ O.subgroupOf C from
        mem_inf.mpr ⟨ho, mul_mem (inv_mem (mem_inf.mp hjC).2) hwt⟩))
  have hNA : O.subgroupOf C ≤ normalizer ((J.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    rw [normalizer_eq_top_iff.mpr hJn]
    exact le_top
  have hwn' : (⟨w, hwC⟩ : ↥C) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hwn)
  exact T23.mem_of_mem_sup_of_pow_two_pow hNA hOodd hmem hwn'

theorem isTwoComponentIn_map_bar {t : X} (ht : orderOf t = 2) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer {t})) :
    IsTwoComponentIn (J.map (QuotientGroup.mk' (pPrimeCore 2 X)))
        (centralizer {(QuotientGroup.mk t : X ⧸ pPrimeCore 2 X)}) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 X))) ⧸
        pPrimeCore 2 ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 X)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X)
  set C := centralizer ({t} : Set X)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hodd := odd_card_pPrimeCore_two X
  have hCmap : C.map π = centralizer {(QuotientGroup.mk t : X ⧸ pPrimeCore 2 X)} :=
    map_centralizer_eq hodd htt
  set C' := centralizer ({(QuotientGroup.mk t : X ⧸ pPrimeCore 2 X)} : Set (X ⧸ pPrimeCore 2 X))
  let φ : ↥C →* ↥C' := (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 X := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 X) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨hbij, -, hiso⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  have hJp : IsPComponent 2 (J.subgroupOf C) := (isTwoComponentIn_iff hJ.1).mp hJ
  have hJ'p : IsPComponent 2 ((J.subgroupOf C).map φ) := hbij.mapsTo hJp
  have hJle : J.map π ≤ C' := by
    rw [← hCmap]
    exact map_mono hJ.1
  have heq : (J.subgroupOf C).map φ = (J.map π).subgroupOf C' := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hJ.1 hx⟩, hx, rfl⟩
  refine ⟨(isTwoComponentIn_iff hJle).mpr (heq ▸ hJ'p), ?_⟩
  obtain ⟨e, -⟩ := hiso _ hJp
  let e₁ : ↥(J.subgroupOf C) ≃* ↥J := subgroupOfEquivOfLe hJ.1
  let e₂ : ↥((J.subgroupOf C).map φ) ≃* ↥(J.map π) :=
    (MulEquiv.subgroupCongr heq).trans (subgroupOfEquivOfLe hJle)
  exact ⟨((QuotientGroup.congr _ _ e₁.symm (pPrimeCore_map_iso 2 e₁.symm)).trans e).trans
    (QuotientGroup.congr _ _ e₂ (pPrimeCore_map_iso 2 e₂))⟩

theorem subgroupOf_pPrimeCore_le {Y : Type*} [Group Y] [Finite Y] (J : Subgroup Y) :
    (pPrimeCore 2 Y).subgroupOf J ≤ pPrimeCore 2 ↥J := by
  have hN : ((pPrimeCore 2 Y).subgroupOf J).Normal := Subgroup.Normal.subgroupOf inferInstance J
  have hdvd : Nat.card ↥((pPrimeCore 2 Y).subgroupOf J) ∣ Nat.card ↥(pPrimeCore 2 Y) := by
    rw [← Subgroup.card_map_of_injective J.subtype_injective, subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcop := Nat.Coprime.coprime_dvd_right hdvd (pPrimeCore_coprime_card (p := 2) (G := Y))
  exact le_sSup (s := {K : Subgroup ↥J | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}) ⟨hN, hcop⟩

theorem false_of_lemma51e (h51e : Harris82Lemma51e) {Y : Type} [Group Y] [Finite Y]
    (hY : IsTwoQuasisimple Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hch : IsSimpleChevalleyOver p (Y ⧸ Open.fusionZStar Y)) {t : Y} (ht : orderOf t = 2)
    (htZ : (QuotientGroup.mk t : Y ⧸ pPrimeCore 2 Y) ∉ center (Y ⧸ pPrimeCore 2 Y))
    {J : Subgroup Y} (hJ : IsTwoComponentIn J (centralizer {t})) (htJ : t ∈ J) {r : ℕ}
    (h5 : 5 ≤ p ^ r) (hcov : IsCoverOf .POmegaOdd 3 p r 2 (↥J ⧸ pPrimeCore 2 ↥J)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 Y) with hρ
  set σ := QuotientGroup.mk' (center (Y ⧸ pPrimeCore 2 Y)) with hσ
  set π : Y →* (Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y) := σ.comp ρ with hπ
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hq := hY.2
  have : IsSimpleGroup ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) := hq.2.1
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv Y
  have hchY : IsSimpleChevalleyOver p ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) := by
    obtain ⟨τ, n, f, hm⟩ := hch
    exact ⟨τ, n, f, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩
  have hπ1 : ∀ y : Y, π y = 1 ↔ ρ y ∈ center (Y ⧸ pPrimeCore 2 Y) := fun y =>
    QuotientGroup.eq_one_iff (ρ y)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hπt : orderOf (π t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, sq, htt, map_one]
    · exact fun h1 => htZ ((hπ1 t).mp h1)
  have hOJ := odd_card_pPrimeCore_two ↥J
  have htJc : (⟨t, htJ⟩ : ↥J) ∈ center ↥J := mem_center_of_le_centralizer hJ.1 htJ
  have ht' : orderOf (⟨t, htJ⟩ : ↥J) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have htbar1 : (QuotientGroup.mk (⟨t, htJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) ≠ 1 := fun h1 => by
    have h2 := orderOf_mk_eq_two hOJ ht'
    rw [QuotientGroup.mk'_apply, h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have htbarc : (QuotientGroup.mk (⟨t, htJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) ∈
      center (↥J ⧸ pPrimeCore 2 ↥J) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp htJc g]
  set Jt := J.map π with hJt
  let φ : ↥J →* ↥Jt := (π.comp J.subtype).codRestrict Jt (fun x => mem_map_of_mem π x.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    intro h2
    obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 2 h2
    set x : ↥J := (i : ↥J) with hx
    have hx2 : orderOf x = 2 := by rw [hx, Subgroup.orderOf_coe]; exact hi
    have hπx : π (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp i.2)
    have hρx := (hπ1 _).mp hπx
    have hxc : (QuotientGroup.mk x : ↥J ⧸ pPrimeCore 2 ↥J) ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply subgroupOf_pPrimeCore_le
      rw [mem_subgroupOf]
      have hcen : ρ (m : Y) * ρ (x : Y) = ρ (x : Y) * ρ (m : Y) := mem_center_iff.mp hρx (ρ m)
      have h1 : ρ (((m * x : ↥J)⁻¹ * (x * m) : ↥J) : Y) = 1 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        rw [hcen, inv_mul_cancel]
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
    have hx1 : (QuotientGroup.mk x : ↥J ⧸ pPrimeCore 2 ↥J) ≠ 1 := fun h1 => by
      have h2 := orderOf_mk_eq_two hOJ hx2
      rw [QuotientGroup.mk'_apply, h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hZ2 : Nat.card ↥(center (↥J ⧸ pPrimeCore 2 ↥J)) = 2 := hcov.2.1
    have hxt := T23.eq_of_ne_one_of_card_two hZ2 (a := ⟨_, hxc⟩) (b := ⟨_, htbarc⟩)
      (fun h => hx1 (congrArg Subtype.val h)) (fun h => htbar1 (congrArg Subtype.val h))
    have hxt' : (QuotientGroup.mk x : ↥J ⧸ pPrimeCore 2 ↥J) = QuotientGroup.mk ⟨t, htJ⟩ :=
      congrArg Subtype.val hxt
    rw [QuotientGroup.eq] at hxt'
    have hπo : π (((x⁻¹ * ⟨t, htJ⟩ : ↥J)) : Y) = π t := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hπx, inv_one, one_mul]
    have hodd : Odd (orderOf (π t)) := by
      rw [← hπo]
      have h1 : orderOf (π (((x⁻¹ * ⟨t, htJ⟩ : ↥J)) : Y)) ∣
          orderOf (((x⁻¹ * ⟨t, htJ⟩ : ↥J)) : Y) := orderOf_map_dvd π _
      have h2 : orderOf (((x⁻¹ * ⟨t, htJ⟩ : ↥J)) : Y) ∣ Nat.card ↥(pPrimeCore 2 ↥J) := by
        rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk _ hxt']
        exact orderOf_dvd_natCard _
      exact hOJ.of_dvd_nat (h1.trans h2)
    rw [hπt] at hodd
    exact absurd hodd (by norm_num)
  obtain ⟨eJ⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective φ hφ hφk
  have hJq : IsTwoQuasisimple ↥Jt := by
    have : Group.IsPerfect ↥J := hJ.2.2.1
    exact ⟨Group.IsPerfect.ofSurjective (f := φ) hφ,
      LocalCores.isQuasisimple_of_mulEquiv eJ hJ.2.2.2⟩
  let C := centralizer ({t} : Set Y)
  let Ct := centralizer ({π t} : Set ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)))
  have hC0 : C.map π ≤ Ct := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    change π c ∈ centralizer ({π t} : Set _)
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']
  have hCρ : C.map ρ = centralizer {ρ t} := map_centralizer_eq (odd_card_pPrimeCore_two Y) htt
  have hC0n : ((C.map π).subgroupOf Ct).Normal := by
    rw [normal_subgroupOf_iff hC0]
    rintro _ b ⟨c, hc, rfl⟩ hb
    obtain ⟨y, rfl⟩ := hπs b
    have hb' : π y * π t = π t * π y := mem_centralizer_singleton_iff.mp hb
    have hn : (ρ y * ρ t)⁻¹ * (ρ t * ρ y) ∈ center (Y ⧸ pPrimeCore 2 Y) := by
      have h1 : σ (ρ y * ρ t) = σ (ρ t * ρ y) := by
        simpa only [hπ, MonoidHom.comp_apply, map_mul] using hb'
      exact QuotientGroup.eq.mp h1
    set n := (ρ y * ρ t)⁻¹ * (ρ t * ρ y) with hndef
    have hnc : ∀ g, g * n = n * g := fun g => mem_center_iff.mp hn g
    have hc' : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    have hct : ρ c * ρ t = ρ t * ρ c := by
      rw [← map_mul, ← map_mul, hc']
    have hty : ρ t * ρ y = ρ y * ρ t * n := by rw [hndef]; group
    have hyt : (ρ y)⁻¹ * ρ t = ρ t * n * (ρ y)⁻¹ := by
      calc (ρ y)⁻¹ * ρ t = (ρ y)⁻¹ * (ρ t * ρ y) * (ρ y)⁻¹ := by group
        _ = (ρ y)⁻¹ * (ρ y * ρ t * n) * (ρ y)⁻¹ := by rw [hty]
        _ = ρ t * n * (ρ y)⁻¹ := by group
    have hd : ρ y * ρ c * (ρ y)⁻¹ ∈ centralizer {ρ t} := by
      rw [mem_centralizer_singleton_iff]
      calc ρ y * ρ c * (ρ y)⁻¹ * ρ t = ρ y * ρ c * ((ρ y)⁻¹ * ρ t) := by group
        _ = ρ y * ρ c * (ρ t * n * (ρ y)⁻¹) := by rw [hyt]
        _ = ρ y * (ρ c * ρ t) * n * (ρ y)⁻¹ := by group
        _ = ρ y * (ρ t * ρ c) * n * (ρ y)⁻¹ := by rw [hct]
        _ = ρ y * ρ t * (ρ c * n) * (ρ y)⁻¹ := by group
        _ = ρ y * ρ t * n * ρ c * (ρ y)⁻¹ := by rw [hnc (ρ c)]; group
        _ = ρ t * ρ y * ρ c * (ρ y)⁻¹ := by rw [← hty]
        _ = ρ t * (ρ y * ρ c * (ρ y)⁻¹) := by group
    rw [← hCρ] at hd
    obtain ⟨c', hc', hc'eq⟩ := hd
    refine ⟨c', hc', ?_⟩
    change σ (ρ c') = π y * π c * (π y)⁻¹
    rw [show ρ c' = ρ y * ρ c * (ρ y)⁻¹ from hc'eq]
    simp only [hπ, MonoidHom.comp_apply, map_mul, map_inv]
  let γ : ↥C →* ↥Ct := (π.comp C.subtype).codRestrict Ct (fun c => hC0 (mem_map_of_mem π c.2))
  have hγr : γ.range = (C.map π).subgroupOf Ct := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, hcy⟩
      exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hγn : γ.range.Normal := by rw [hγr]; exact hC0n
  have hJle : Jt ≤ Ct := (map_mono hJ.1).trans hC0
  have hsub : (Jt.subgroupOf Ct).IsSubnormal := by
    have h1 := isSubnormal_map_of_range_normal γ hγn hJ.2.1
    convert h1 using 1
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hJ.1 hx⟩, hx, rfl⟩
    · rintro ⟨c, hc, hcy⟩
      exact ⟨c, hc, congrArg Subtype.val hcy⟩
  exact h51e _ p hp hp2 hchY (π t) hπt Jt ⟨hJle, hsub, hJq⟩ ⟨t, htJ, rfl⟩ r h5
    (isCoverOf_of_mulEquiv eJ hcov)

end CFSG.ComponentClassification.HarrisLit.T1
