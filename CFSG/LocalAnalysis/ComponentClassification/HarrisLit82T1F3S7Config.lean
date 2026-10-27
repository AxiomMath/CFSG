module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Config
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Z
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Spin

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups commutatorElement

structure S7Inputs : Prop where
  known : KnownRow
  fourGroup : Harris82FourGroupThree
  l58 : Harris82Lemma58bThree
  l51e : Harris82Lemma51eOdd
  u1 : Harris82Lemma411U1Three
  u4 : Harris82Lemma411U4Three
  l57 : Harris82Lemma57SpinThree
  solomon : Solomon74SpinSevenAsUsedThree

structure S7Config (G : Type) [Group G] [Finite G] (z : G) (L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : Assembly.KProper Blueprint.Catalog G
  notCat : ¬ Blueprint.Catalog G
  hz : orderOf z = 2
  hL : IsTwoComponentIn L (centralizer {z})
  hzL : z ∈ L
  hcov : IsCoverOf .POmegaOdd 3 3 1 2 (↥L ⧸ pPrimeCore 2 ↥L)
  hM : IsMTypeSchur 3 ↥L

variable {G : Type} [Group G] [Finite G]

theorem F3S7.nonempty_equiv_sl23 {Y : Type} [Group Y] (h : IsSLTwoOver 3 Y) :
    Nonempty (Y ≃* SL(2, ZMod 3)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact ⟨e.trans (LieType.HighestRoot.slEquivSL23 (by rw [Nat.card_eq_fintype_card, hF]))⟩

omit [Finite G] in
theorem F3S7.isTwoComponentIn_top_subgroupOf {L M : Subgroup G} (hL : IsTwoComponentIn L M) :
    IsTwoComponentIn (L.subgroupOf M) (⊤ : Subgroup ↥M) :=
  ⟨le_top, hL.2.1.comap _, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hL.1).symm hL.2.2⟩

omit [Finite G] in
theorem F3S7.isSolvableTwoComponentIn_subgroupOf {J A M : Subgroup G} (hJA : J ≤ A)
    (hAM : A ≤ M) (h : IsSolvableTwoComponentIn J A) :
    IsSolvableTwoComponentIn (J.subgroupOf M) (A.subgroupOf M) := by
  have hJM : J ≤ M := hJA.trans hAM
  let eA : ↥(A.subgroupOf M) ≃* ↥A := subgroupOfEquivOfLe hAM
  let eJ : ↥(J.subgroupOf M) ≃* ↥J := subgroupOfEquivOfLe hJM
  refine ⟨fun x hx => hJA hx, ?_, ?_, ?_⟩
  · have hmap : (J.subgroupOf A).map eA.symm.toMonoidHom =
        (J.subgroupOf M).subgroupOf (A.subgroupOf M) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨eA x, hx, eA.symm_apply_apply x⟩
    rw [← hmap]
    exact h.2.1.map eA.symm.surjective
  · apply map_injective M.subtype_injective
    rw [map_map, map_map]
    have h1 : M.subtype.comp (J.subgroupOf M).subtype = J.subtype.comp eJ.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    have h2 : M.subtype.comp (A.subgroupOf M).subtype = A.subtype.comp eA.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [h1, h2, ← map_map, ← map_map, pPrimeCore_map_iso 2 eJ, pPrimeCore_map_iso 2 eA]
    exact h.2.2.1
  · rcases h.2.2.2 with h1 | h1
    · obtain ⟨e⟩ := h1
      exact .inl ⟨(QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans e⟩
    · obtain ⟨e⟩ := h1
      exact .inr ⟨(QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans e⟩

theorem F3S7.oPrimeResidual_map_equiv {A B : Type*} [Group A] [Group B] (p : ℕ) (e : A ≃* B) :
    (GH74.GLS.oPrimeResidual p A).map e.toMonoidHom = GH74.GLS.oPrimeResidual p B := by
  unfold GH74.GLS.oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, hk, map_one]

omit [Finite G] in
theorem F3S7.map_oPrimeResidualOf_subgroupOf {J M : Subgroup G} (hJM : J ≤ M) :
    (GH74.GLS.oPrimeResidualOf 2 (J.subgroupOf M)).map M.subtype =
      GH74.GLS.oPrimeResidualOf 2 J := by
  let eJ : ↥(J.subgroupOf M) ≃* ↥J := subgroupOfEquivOfLe hJM
  unfold GH74.GLS.oPrimeResidualOf
  rw [map_map]
  have h1 : M.subtype.comp (J.subgroupOf M).subtype = J.subtype.comp eJ.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [h1, ← map_map, F3S7.oPrimeResidual_map_equiv 2 eJ]

omit [Finite G] in
theorem F3S7.map_pPrimeCore_subgroupOf {L M : Subgroup G} (hLM : L ≤ M) :
    ((pPrimeCore 2 ↥(L.subgroupOf M)).map (L.subgroupOf M).subtype).map M.subtype =
      (pPrimeCore 2 ↥L).map L.subtype := by
  let e : ↥(L.subgroupOf M) ≃* ↥L := subgroupOfEquivOfLe hLM
  rw [map_map]
  have h1 : M.subtype.comp (L.subgroupOf M).subtype = L.subtype.comp e.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [h1, ← map_map, pPrimeCore_map_iso 2 e]

theorem F3S7.lemma221_solvable {w v : G} (hv2 : orderOf v = 2)
    (hvM : v ∈ centralizer {w}) {J : Subgroup G}
    (hJ : IsSolvableTwoComponentIn J (centralizer {w} ⊓ centralizer {v})) (hvJ : v ∈ J)
    {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {w}))
    (hcov : IsCoverOf .POmegaOdd 3 3 1 2 (↥L ⧸ pPrimeCore 2 ↥L))
    (hJN : J ≤ normalizer (L : Set G) ∨ ∀ l ∈ L, v * l * v⁻¹ * l⁻¹ ∈
      (pPrimeCore 2 ↥(centralizer ({w} : Set G))).map (centralizer {w}).subtype) :
    GH74.GLS.oPrimeResidualOf 2 J ≤ L ∨ J ≤ coreActionKernel L := by
  set M := centralizer ({w} : Set G) with hMdef
  set v' : ↥M := ⟨v, hvM⟩ with hv'def
  have hv'2 : orderOf v' = 2 := by rw [hv'def, Subgroup.orderOf_mk]; exact hv2
  have hCv : centralizer ({v'} : Set ↥M) =
      (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf M := by
    ext x
    rw [mem_subgroupOf, mem_inf]
    constructor
    · intro h
      have h' : x * v' = v' * x := mem_centralizer_singleton_iff.mp h
      exact ⟨x.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h')⟩
    · rintro ⟨-, h⟩
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp h))
  have hJ' : IsSolvableTwoComponentIn (J.subgroupOf M) (centralizer {v'}) := by
    rw [hCv]
    exact F3S7.isSolvableTwoComponentIn_subgroupOf hJ.1 inf_le_left hJ
  have hJM : J ≤ M := hJ.1.trans inf_le_left
  let eL : ↥(L.subgroupOf M) ≃* ↥L := subgroupOfEquivOfLe hL.1
  have hcov' : IsCoverOf .POmegaOdd 3 3 1 2
      (↥(L.subgroupOf M) ⧸ pPrimeCore 2 ↥(L.subgroupOf M)) :=
    isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eL.symm (pPrimeCore_map_iso 2 eL.symm)) hcov
  have hJN' : J.subgroupOf M ≤ normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) ∨
      ∀ l ∈ L.subgroupOf M, v' * l * v'⁻¹ * l⁻¹ ∈ pPrimeCore 2 ↥M := by
    rcases hJN with h | h
    · left
      intro x hx
      rw [mem_normalizer_iff]
      intro y
      have h1 := mem_normalizer_iff.mp (h (mem_subgroupOf.mp hx)) (y : G)
      simpa only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h1
    · right
      intro l hl
      obtain ⟨y, hy, hyl⟩ := h l (mem_subgroupOf.mp hl)
      have hy' : y = v' * l * v'⁻¹ * l⁻¹ := Subtype.ext hyl
      rw [← hy']
      exact hy
  rcases F3L221.lemma221_spinThree hv'2 (F3S7.isTwoComponentIn_top_subgroupOf hL) hcov' hJ'
      hvJ hJN' with h1 | h1
  ·
    right
    have key : ∀ x ∈ J, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := by
      intro x hx l hl
      have hx' : (⟨x, hJM hx⟩ : ↥M) ∈ J.subgroupOf M := hx
      have hl' : (⟨l, hL.1 hl⟩ : ↥M) ∈ L.subgroupOf M := hl
      have hc := mem_map_of_mem M.subtype (h1 (commutator_mem_commutator hx' hl'))
      rw [F3S7.map_pPrimeCore_subgroupOf hL.1] at hc
      simpa [commutatorElement_def] using hc
    have hOL : (pPrimeCore 2 ↥L).map L.subtype ≤ L := map_subtype_le _
    intro x hx
    refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h2 := hOL (key x hx y hy)
        have h3 : x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y := by group
        rw [h3]
        exact mul_mem h2 hy
      · intro hy
        have h2 := hOL (key x⁻¹ (inv_mem hx) _ hy)
        have h3 : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ * (x * y * x⁻¹)⁻¹ * (x * y * x⁻¹) := by group
        rw [h3]
        exact mul_mem h2 hy
    · have h2 := inv_mem (key x⁻¹ (inv_mem hx) j⁻¹ (inv_mem hj))
      have h3 : j⁻¹ * x⁻¹ * j * x = (x⁻¹ * j⁻¹ * x⁻¹⁻¹ * j⁻¹⁻¹)⁻¹ := by group
      rw [h3]
      exact h2
  ·
    left
    rw [← F3S7.map_oPrimeResidualOf_subgroupOf hJM, ← map_subgroupOf_eq_of_le hL.1]
    exact map_mono h1

theorem F3S7.false_of_lemma51eOdd (h51e : Harris82Lemma51eOdd) {Y : Type} [Group Y] [Finite Y]
    (hY : IsTwoQuasisimple Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hch : IsSimpleChevalleyOver p (Y ⧸ Open.fusionZStar Y)) {t : Y} (ht : orderOf t = 2)
    (htZ : (QuotientGroup.mk t : Y ⧸ pPrimeCore 2 Y) ∉ center (Y ⧸ pPrimeCore 2 Y))
    {J : Subgroup Y} (hJ : IsTwoComponentIn J (centralizer {t})) (htJ : t ∈ J) {r : ℕ}
    (hr : 1 ≤ r) (hcov : IsCoverOf .POmegaOdd 3 p r 2 (↥J ⧸ pPrimeCore 2 ↥J)) : False := by
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
  exact h51e _ p hp hp2 hchY (π t) hπt Jt ⟨hJle, hsub, hJq⟩ ⟨t, htJ, rfl⟩ r hr
    (isCoverOf_of_mulEquiv eJ hcov)

variable {z : G} {L : Subgroup G}

theorem S7Config.pumpdown_Q (h : S7Config G z L) {τ : G} (hτ : orderOf τ = 2)
    (hτQ : τ ∈ coreActionKernel L) :
    IsTwoComponentIn (centralizerResidual L τ) (centralizer {z} ⊓ centralizer {τ}) ∧
      Nonempty (↥(centralizerResidual L τ) ⧸ pPrimeCore 2 ↥(centralizerResidual L τ) ≃* Bar L) ∧
      ∀ w ∈ L, w ∈ centralizer {τ} → (∃ n : ℕ, w ^ 2 ^ n = 1) → w ∈ centralizerResidual L τ := by
  have htN : τ ∈ normalizer (L : Set G) := (mem_coreActionKernel.mp hτQ).1
  have htriv : barAction L ⟨τ, htN⟩ = 1 :=
    MonoidHom.mem_ker.mp ((mem_ker_barAction L ⟨τ, htN⟩).mpr hτQ)
  have ht2 : IsPGroup 2 (zpowers τ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ, pow_one])
  obtain ⟨hJ, he⟩ := pumpdown h.hL htN ht2 htriv
  exact ⟨hJ, he, fun w hwL hwτ ⟨n, hn⟩ =>
    mem_centralizerResidual_of_two_pow htN ht2 h.hL.2.2.2.1 htriv hwL hwτ hn⟩

theorem S7Config.mem_pumpdown_Q (h : S7Config G z L) {τ : G} (hτ : orderOf τ = 2)
    (hτQ : τ ∈ coreActionKernel L) (hτz : τ ∈ centralizer {z}) : z ∈ centralizerResidual L τ :=
  (h.pumpdown_Q hτ hτQ).2.2 z h.hzL
    (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hτz).symm)
    ⟨1, by rw [pow_one, ← h.hz, pow_orderOf_eq_one]⟩

section CertifiedSmall


theorem S7Config.step1 (hI : S7Inputs) (h : S7Config G z L) {τ : G} (hτ : orderOf τ = 2)
    (hτz : τ ∈ centralizer {z}) (hτQ : τ ∈ coreActionKernel L) :
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {τ}) ∧ centralizerResidual L τ ≤ K ∧
      ∃ hzK : z ∈ K, (QuotientGroup.mk ⟨z, hzK⟩ : Bar K) ∈ center (Bar K) := by
  have := h.simple
  obtain ⟨hJ, ⟨e⟩, -⟩ := h.pumpdown_Q hτ hτQ
  have hzJ := h.mem_pumpdown_Q hτ hτQ hτz
  set J := centralizerResidual L τ with hJdef
  have hzτ : z ∈ centralizer ({τ} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hτz).symm
  have hJ' : IsTwoComponentIn J (centralizer {τ} ⊓ centralizer {z}) :=
    inf_comm (centralizer {z}) (centralizer {τ}) ▸ hJ
  obtain ⟨K₀, hK₀, -, -, hJK⟩ := T23.exists_pumpup_of_mem h.hz hzτ hJ' hzJ
  set K := K₀.map (centralizer {τ}).subtype with hKdef
  have hKc : IsTwoComponentIn K (centralizer {τ}) := T23.isTwoComponentIn_map_subtype hK₀
  have hJKle : J ≤ K := by
    intro x hx
    have hx' : (⟨x, (hJ'.1 hx).1⟩ : ↥(centralizer ({τ} : Set G))) ∈ J.subgroupOf _ := hx
    exact ⟨⟨x, (hJ'.1 hx).1⟩, (hJK.1 hx').1, rfl⟩
  have hzK : z ∈ K := hJKle hzJ
  refine ⟨K, hKc, hJKle, hzK, ?_⟩
  by_contra hZ
  have hle : K ⊓ centralizer {z} ≤ centralizer {τ} ⊓ centralizer {z} := inf_le_inf_right _ hKc.1
  have hJK' : IsTwoComponentIn J (K ⊓ centralizer {z}) :=
    ⟨le_inf hJKle (hJ'.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hJ'.2.1,
      hJ'.2.2⟩
  have hKtop : K ≠ ⊤ := fun ht =>
    centralizer_ne_top_of_simple h.nonab hτ (top_unique (ht ▸ hKc.1))
  have hMJ : IsMTypeSchur 3 ↥J := isMTypeSchur_of_bar_equiv h.hM hJ.2.2 e.symm
  have hcovJ : IsCoverOf .POmegaOdd 3 3 1 2 (↥J ⧸ pPrimeCore 2 ↥J) :=
    isCoverOf_of_mulEquiv e.symm h.hcov
  have hIJ : InductionTypeField 3 ↥J := ⟨1, le_rfl, .inl hcovJ⟩
  have hch := isSimpleChevalleyOver_of_knownRow hI.known h.kProper hKtop hKc.2.2 hzK h.hz hJK'
    hzJ Nat.prime_three (by norm_num) hMJ hIJ
  have hz' : orderOf (⟨z, hzK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  let eJ : ↥(J.subgroupOf K) ≃* ↥J := subgroupOfEquivOfLe hJKle
  exact F3S7.false_of_lemma51eOdd hI.l51e hKc.2.2 Nat.prime_three (by norm_num) hch hz' hZ
    (isTwoComponentIn_subgroupOf_inf hzK hJK') hzJ le_rfl
    (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)) hcovJ)

end CertifiedSmall

theorem F3S7.false_of_fourGroupThree (hI : S7Inputs) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G) {z₁ z₂ : G} (hz₁ : orderOf z₁ = 2) (hz₂ : orderOf z₂ = 2)
    (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) {L₁ L₂ : Subgroup G}
    (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hL₂ : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₁L : z₁ ∈ L₁)
    (hz₂L : z₂ ∈ L₂) (e₁ : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) {r : ℕ} (hr : 1 ≤ r)
    (hcov₂ : IsCoverOf .POmegaOdd 3 3 r 2 (↥L₂ ⧸ pPrimeCore 2 ↥L₂)) : False := by
  obtain ⟨K, hKc, hO₁, hO₂, hN, hch, hz₂K, hz₂Z⟩ := hI.fourGroup G hnonab hK hcat z₁ z₂ hz₁ hz₂
    hne hc L₁ L₂ hL₁ (.inl hL₂) hz₁L hz₂L ⟨e₁⟩ (.inl ⟨r, hr, .inl hcov₂⟩)
  exact (hI.l58 G z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ (.inl hL₂) hz₁L hz₂L ⟨e₁⟩ hKc hO₁ hO₂ hN hz₂K
    hz₂Z hch).2.2.2 r hcov₂

theorem S7Config.false_of_slTwo (hI : S7Inputs) (h : S7Config G z L) {j : G}
    (hj : orderOf j = 2) (hjz : j ∈ centralizer {z}) (hjL : j ∉ L) {J : Subgroup G}
    (hJ : IsSolvableTwoComponentIn J (centralizer {z} ⊓ centralizer {j})) (hjJ : j ∈ J)
    (e : ↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3))
    (hJN : J ≤ normalizer (L : Set G) ∨ ∀ l ∈ L, j * l * j⁻¹ * l⁻¹ ∈
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype) : False := by
  have := h.simple
  rcases F3S7.lemma221_solvable hj hjz hJ hjJ h.hL h.hcov hJN with hle | hle
  · exact hjL (hle (F3.mem_oPrimeResidualOf hjJ hj))
  · have hjQ : j ∈ coreActionKernel L := hle hjJ
    obtain ⟨hJ', ⟨e'⟩, -⟩ := h.pumpdown_Q hj hjQ
    have hzJ' := h.mem_pumpdown_Q hj hjQ hjz
    have hzj : j * z = z * j := mem_centralizer_singleton_iff.mp hjz
    have hne : j ≠ z := fun he => hjL (he ▸ h.hzL)
    exact F3S7.false_of_fourGroupThree hI h.nonab h.kProper h.notCat hj h.hz hne hzj
      (inf_comm (centralizer {z}) (centralizer {j}) ▸ hJ)
      (inf_comm (centralizer {z}) (centralizer {j}) ▸ hJ') hjJ hzJ' e le_rfl
      (isCoverOf_of_mulEquiv e'.symm h.hcov)

theorem S7Config.eq_of_isCoverOf (hI : S7Inputs) (h : S7Config G z L) {L' : Subgroup G}
    (hL' : IsTwoComponentIn L' (centralizer {z}))
    (hcov' : IsCoverOf .POmegaOdd 3 3 1 2 (↥L' ⧸ pPrimeCore 2 ↥L')) : L' = L := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomp, -, ⟨E⟩⟩ := hatIn_spec hL'
  have hcovh : IsCoverOf .POmegaOdd 3 3 1 2 ↥(hatIn z L') := isCoverOf_of_mulEquiv E hcov'
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinSeven_three (by norm_num) hcovh
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  obtain ⟨-, hz1, hzc, htt, ht1, htc, -, -, -, -⟩ :=
    spinZ_facts Nat.prime_three (by norm_num) hK'
  set û : MBar z := ((e₁.symm (tSeven K) : ↥(hatIn z L')) : MBar z) with hû
  have hûL' : û ∈ hatIn z L' := (e₁.symm (tSeven K)).2
  have hû2' : orderOf (⟨û, hûL'⟩ : ↥(hatIn z L')) = 2 := by
    rw [show (⟨û, hûL'⟩ : ↥(hatIn z L')) = e₁.symm (tSeven K) from rfl, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hû2 : orderOf û = 2 := by rw [← Subgroup.orderOf_mk û hûL']; exact hû2'
  have hûZ : (⟨û, hûL'⟩ : ↥(hatIn z L')) ∉ center ↥(hatIn z L') := fun hc => htc (by
    have h1 := (mem_center_mulEquiv_iff e₁ (e₁.symm (tSeven K))).mpr hc
    rwa [MulEquiv.apply_symm_apply] at h1)
  have hwc : e₁.symm (spinZ K) ∈ center ↥(hatIn z L') := by
    rw [← mem_center_mulEquiv_iff e₁, MulEquiv.apply_symm_apply]
    exact hzc
  have hw1 : e₁.symm (spinZ K) ≠ 1 := fun h1 => hz1 (by
    rw [← MulEquiv.apply_symm_apply e₁ (spinZ K), h1, map_one])
  obtain ⟨-, hc1, -, hc3⟩ := lemma410c_three (by norm_num) hcovh hwc hw1 hû2' hûZ
  obtain ⟨Y, hY, -, hûY⟩ := hc3 ⟨û, hûL'⟩ (Or.inr (Or.inl rfl))
  have hslY := (hc1 Y hY).1
  rw [pow_one] at hslY
  obtain ⟨eY⟩ := F3S7.nonempty_equiv_sl23 hslY
  obtain ⟨hYle, hYs⟩ :=
    F3.map_inf_subnormal (le_top : hatIn z L' ≤ ⊤) hcomp.1.subgroupOf ⟨û, hûL'⟩ hY.1 hY.2.1
  rw [top_inf_eq] at hYle hYs
  let eY' : ↥Y ≃* ↥(Y.map (hatIn z L').subtype) :=
    Y.equivMapOfInjective _ (hatIn z L').subtype_injective
  have eŶ : ↥(Y.map (hatIn z L').subtype) ⧸ pPrimeCore 2 ↥(Y.map (hatIn z L').subtype) ≃*
      SL(2, ZMod 3) :=
    (QuotientGroup.congr _ _ eY'.symm (pPrimeCore_map_iso 2 eY'.symm)).trans eY
  obtain ⟨u', hu'2, hu'1, hu'mk⟩ := T23.exists_involution_lift (H := ↥(centralizer ({z} : Set G)))
    (a := û) (by have h1 := pow_orderOf_eq_one û; rwa [hû2, sq] at h1)
    (fun h1 => by rw [h1, orderOf_one] at hû2; exact absurd hû2 (by norm_num))
  have hu : orderOf (u' : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hu'2]) hu'1
  have huz : (u' : G) ∈ centralizer ({z} : Set G) := u'.2
  have hûmk : (QuotientGroup.mk ⟨(u' : G), huz⟩ : MBar z) = û := hu'mk
  have huL : (u' : G) ∉ L := by
    intro huL
    have hûL : û ∈ hatIn z L := hûmk ▸ mk_mem_hatIn huL huz
    apply hûZ
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hatIn_commute h.hL hL' (Ne.symm hne) hûL g.2).symm
  have hYle' : Y.map (hatIn z L').subtype ≤
      centralizer {(QuotientGroup.mk ⟨(u' : G), huz⟩ : MBar z)} := by
    rw [hûmk]
    exact hYle
  have hYs' : ((Y.map (hatIn z L').subtype).subgroupOf
      (centralizer {(QuotientGroup.mk ⟨(u' : G), huz⟩ : MBar z)})).IsSubnormal := by
    rw [hûmk]
    exact hYs
  obtain ⟨J, hJ, ⟨eJ⟩, hmem⟩ := F3.lift_solvable huz hu hYle' hYs' eŶ
  have huJ : (u' : G) ∈ J := hmem _ huz (mem_centralizer_singleton_iff.mpr rfl)
    (by rw [hûmk]; exact ⟨⟨û, hûL'⟩, hûY, rfl⟩)
  have hcomm : ∀ l ∈ L, (u' : G) * l * (u' : G)⁻¹ * l⁻¹ ∈
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype := by
    intro l hl
    have hlz : l ∈ centralizer ({z} : Set G) := h.hL.1 hl
    have h1 := hatIn_commute h.hL hL' (Ne.symm hne) (mk_mem_hatIn hl hlz) hûL'
    rw [← hûmk] at h1
    have h2 : (QuotientGroup.mk ((⟨(u' : G), huz⟩ : ↥(centralizer ({z} : Set G))) *
        ⟨l, hlz⟩ * ⟨(u' : G), huz⟩⁻¹ * ⟨l, hlz⟩⁻¹) : MBar z) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, ← h1]
      group
    rw [QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  exact h.false_of_slTwo hI hu huz huL hJ huJ eJ (.inr hcomm)

theorem S7Config.normal (hI : S7Inputs) (h : S7Config G z L) :
    (L.subgroupOf (centralizer {z})).Normal := by
  rw [normal_subgroupOf_iff h.hL.1]
  intro l g hl hg
  have hgz : g * z * g⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have h2 : (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom = centralizer {z} := by
    rw [map_centralizer_singleton_mulEquiv, MulAut.conj_apply, hgz]
  have hLg : IsTwoComponentIn (L.map (MulAut.conj g).toMonoidHom) (centralizer {z}) := by
    have h1 := L35.isTwoComponentIn_map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective h.hL
    rwa [h2] at h1
  let eg : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj g).injective
  have heq := h.eq_of_isCoverOf hI hLg
    (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eg (pPrimeCore_map_iso 2 eg)) h.hcov)
  rw [← heq]
  exact ⟨l, hl, rfl⟩

theorem S7Config.characteristic (hI : S7Inputs) (h : S7Config G z L) :
    (L.subgroupOf (centralizer {z})).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro φ
  have hL'c : IsTwoComponent (L.subgroupOf (centralizer {z})) :=
    (isTwoComponent_iff_isPComponent _).mpr ((isTwoComponentIn_iff h.hL.1).mp h.hL)
  have hφc : IsTwoComponent ((L.subgroupOf (centralizer {z})).map φ.toMonoidHom) :=
    ⟨Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hL'c.1,
      isTwoQuasisimple_of_mulEquiv
        ((L.subgroupOf (centralizer {z})).equivMapOfInjective _ φ.injective) hL'c.2⟩
  have hG : IsTwoComponentIn (((L.subgroupOf (centralizer {z})).map φ.toMonoidHom).map
      (centralizer {z}).subtype) (centralizer {z}) :=
    T23.isTwoComponentIn_map_subtype hφc
  let ε : ↥L ≃* ↥(((L.subgroupOf (centralizer {z})).map φ.toMonoidHom).map
      (centralizer {z}).subtype) :=
    ((subgroupOfEquivOfLe h.hL.1).symm.trans
      ((L.subgroupOf (centralizer {z})).equivMapOfInjective _ φ.injective)).trans
      (((L.subgroupOf (centralizer {z})).map φ.toMonoidHom).equivMapOfInjective _
        (centralizer {z}).subtype_injective)
  have heq := h.eq_of_isCoverOf hI hG
    (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ ε (pPrimeCore_map_iso 2 ε)) h.hcov)
  apply map_injective (centralizer ({z} : Set G)).subtype_injective
  rw [heq, subgroupOf_map_subtype, inf_eq_left.mpr h.hL.1]

end CFSG.ComponentClassification.HarrisLit.T1
