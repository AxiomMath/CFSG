module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Config
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem F3S7.spinSeven_conj_of_involution_three {L : Subgroup G}
    (hcov : IsCoverOf .POmegaOdd 3 3 1 2 (↥L ⧸ pPrimeCore 2 ↥L)) {u v : G} (huL : u ∈ L)
    (hvL : v ∈ L) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∉
      center (↥L ⧸ pPrimeCore 2 ↥L))
    (hvZ : (QuotientGroup.mk (⟨v, hvL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∉
      center (↥L ⧸ pPrimeCore 2 ↥L)) :
    ∃ x ∈ L, x * u * x⁻¹ = v := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinSeven_three (by norm_num) hcov
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have hOodd := odd_card_pPrimeCore_two ↥L
  have h2u : orderOf (e₁ (QuotientGroup.mk (⟨u, huL⟩ : ↥L))) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_eq_two hOodd (by rw [Subgroup.orderOf_mk]; exact hu)
  have h2v : orderOf (e₁ (QuotientGroup.mk (⟨v, hvL⟩ : ↥L))) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_eq_two hOodd (by rw [Subgroup.orderOf_mk]; exact hv)
  obtain ⟨g₁, hg₁⟩ := spinSeven_lemma410b_odd hodd h2u
    (by rw [mem_center_mulEquiv_iff]; exact huZ)
  obtain ⟨g₂, hg₂⟩ := spinSeven_lemma410b_odd hodd h2v
    (by rw [mem_center_mulEquiv_iff]; exact hvZ)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e₁.symm (g₂ * g₁⁻¹))
  have hconj : (QuotientGroup.mk (⟨v, hvL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      (QuotientGroup.mk g : ↥L ⧸ pPrimeCore 2 ↥L) * QuotientGroup.mk ⟨u, huL⟩ *
        (QuotientGroup.mk g : ↥L ⧸ pPrimeCore 2 ↥L)⁻¹ := by
    apply e₁.injective
    rw [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply, ← hg₁, ← hg₂]
    group
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hv' : orderOf (⟨v, hvL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hv
  have huu : (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 := by
    rw [← pow_two, ← hu', pow_orderOf_eq_one]
  have hvv : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := by
    rw [← pow_two, ← hv', pow_orderOf_eq_one]
  obtain ⟨x, hx⟩ := exists_conj_of_mk_conj hOodd hvv huu hconj
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

omit [Finite G] in
theorem F3S7.map_subnormal_centralizer {A : Subgroup G} (x : ↥A) {J : Subgroup ↥A}
    (hJ : J ≤ centralizer {x}) (hJs : (J.subgroupOf (centralizer {x})).IsSubnormal) :
    J.map A.subtype ≤ A ⊓ centralizer {(x : G)} ∧
      ((J.map A.subtype).subgroupOf (A ⊓ centralizer {(x : G)})).IsSubnormal := by
  set C := centralizer ({x} : Set ↥A) with hC
  have hCA : C.map A.subtype = A ⊓ centralizer {(x : G)} := map_subtype_centralizer_mem x
  let eC : ↥C ≃* ↥(C.map A.subtype) := C.equivMapOfInjective A.subtype A.subtype_injective
  have hmap : (J.subgroupOf C).map eC.toMonoidHom =
      (J.map A.subtype).subgroupOf (C.map A.subtype) := by
    ext y
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, hwy⟩
      exact ⟨⟨w, hJ hw⟩, hw, Subtype.ext hwy⟩
  have h1 : ((J.map A.subtype).subgroupOf (C.map A.subtype)).IsSubnormal :=
    hmap ▸ hJs.map eC.surjective
  rw [hCA] at h1
  exact ⟨hCA ▸ map_mono hJ, h1⟩

omit [Finite G] in
theorem F3S7.isSubnormal_inf_of_subnormal {L A J : Subgroup G} (hLA : L ≤ A)
    (hL : (L.subgroupOf A).IsSubnormal) (C : Subgroup G) (hJ : J ≤ L ⊓ C)
    (hJs : (J.subgroupOf (L ⊓ C)).IsSubnormal) :
    J ≤ A ⊓ C ∧ (J.subgroupOf (A ⊓ C)).IsSubnormal := by
  have hle : L ⊓ C ≤ A ⊓ C := inf_le_inf_right C hLA
  have h1 : ((L ⊓ C).subgroupOf (A ⊓ C)).IsSubnormal := by
    have h := hL.comap (inclusion (inf_le_left : A ⊓ C ≤ A))
    convert h using 1
    ext x
    simp only [mem_subgroupOf, mem_inf, mem_comap, coe_inclusion]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  exact ⟨hJ.trans hle, CFSG.GroupTheory.isSubnormal_subgroupOf_trans hJ hle hJs h1⟩

theorem F3S7.exists_lift_section_bar {X : Type} [Group X] [Finite X] {u : X}
    (hu : orderOf u = 2) {Y : Subgroup (X ⧸ pPrimeCore 2 X)}
    (hYle : Y ≤ centralizer {(QuotientGroup.mk u : X ⧸ pPrimeCore 2 X)})
    (hYs : (Y.subgroupOf (centralizer {(QuotientGroup.mk u : X ⧸ pPrimeCore 2 X)})).IsSubnormal) :
    ∃ P : Subgroup X, P ≤ centralizer {u} ∧ (P.subgroupOf (centralizer {u})).IsSubnormal ∧
      (∀ w ∈ centralizer ({u} : Set X), (QuotientGroup.mk w : X ⧸ pPrimeCore 2 X) ∈ Y →
        w ∈ P) ∧
      Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 X)
  let C := centralizer ({u} : Set X)
  have hu2 : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
  have hCmap : C.map π = centralizer {(QuotientGroup.mk u : X ⧸ pPrimeCore 2 X)} :=
    map_centralizer_eq (odd_card_pPrimeCore_two X) hu2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk u : X ⧸ pPrimeCore 2 X)} :
      Set (X ⧸ pPrimeCore 2 X))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
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
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two X)) (even_iff_two_dvd.mpr
      (h2.trans hc))
  let P₀ := (Y.subgroupOf (centralizer {(QuotientGroup.mk u : X ⧸ pPrimeCore 2 X)})).comap φ
  have hP₀s : P₀.IsSubnormal := hYs.comap φ
  let g : ↥P₀ →* ↥Y := ((centralizer ({(QuotientGroup.mk u : X ⧸ pPrimeCore 2 X)} :
    Set (X ⧸ pPrimeCore 2 X))).subtype.comp (φ.comp P₀.subtype)).codRestrict Y (fun x => x.2)
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ := hφs ⟨y, hYle hy⟩
    have hcP : c ∈ P₀ := by
      change φ c ∈ Y.subgroupOf _
      rw [hc]
      exact hy
    refine ⟨⟨c, hcP⟩, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hc
    exact h1
  have hgk : ¬ 2 ∣ Nat.card g.ker := by
    have hle : g.ker.map P₀.subtype ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : g x = 1 := hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h2 := congrArg Subtype.val hx'
      exact h2
    have hc : Nat.card g.ker ∣ Nat.card φ.ker := by
      rw [← Subgroup.card_map_of_injective P₀.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h2 => hφk (h2.trans hc)
  obtain ⟨e₀⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hgs hgk
  have hPsub : (P₀.map C.subtype).subgroupOf C = P₀ :=
    comap_map_eq_self_of_injective C.subtype_injective _
  let eP : ↥P₀ ≃* ↥(P₀.map C.subtype) := P₀.equivMapOfInjective C.subtype C.subtype_injective
  refine ⟨P₀.map C.subtype, map_subtype_le _, by rw [hPsub]; exact hP₀s, ?_,
    ⟨(QuotientGroup.congr _ _ eP.symm (pPrimeCore_map_iso 2 eP.symm)).trans e₀⟩⟩
  intro w hw hwY
  have hwP : (⟨w, hw⟩ : ↥C) ∈ P₀ := hwY
  exact ⟨⟨w, hw⟩, hwP, rfl⟩

theorem F3S7.spinSeven_lift_three_three {z u : G} {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hcov : IsCoverOf .POmegaOdd 3 3 1 2 (↥L ⧸ pPrimeCore 2 ↥L)) (huL : u ∈ L)
    (hu : orderOf u = 2)
    (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∉
      center (↥L ⧸ pPrimeCore 2 ↥L))
    {e : G} (he : e = z ∨ e = u ∨ e = z * u) :
    ∃ J : Subgroup G, IsSolvableTwoComponentIn J (centralizer {z} ⊓ centralizer {u}) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) ∧ e ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd := odd_card_pPrimeCore_two ↥L
  have hz'c := mem_center_of_le_centralizer hL.1 hzL
  have hz' : orderOf (⟨z, hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hzc := mk_mem_center_of_mem_center (N := pPrimeCore 2 ↥L) hz'c
  have hz1 := mk_ne_one_of_orderOf_two hz'
  have hū2 : orderOf (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = 2 :=
    orderOf_mk_eq_two hOodd hu'
  obtain ⟨-, hc1, -, hc3⟩ := lemma410c_three (by norm_num) hcov hzc hz1 hū2 huZ
  have heL : e ∈ L := by
    rcases he with rfl | rfl | rfl
    · exact hzL
    · exact huL
    · exact mul_mem hzL huL
  have hē : (QuotientGroup.mk (⟨e, heL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
      ({QuotientGroup.mk ⟨z, hzL⟩, QuotientGroup.mk ⟨u, huL⟩,
        QuotientGroup.mk ⟨z, hzL⟩ * QuotientGroup.mk ⟨u, huL⟩} : Set (↥L ⧸ pPrimeCore 2 ↥L)) := by
    rcases he with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨Y, hY, -, heY⟩ := hc3 _ hē
  have hslY := (hc1 Y hY).1
  rw [pow_one] at hslY
  obtain ⟨eY⟩ := F3S7.nonempty_equiv_sl23 hslY
  obtain ⟨P, hPle, hPs, hmem, ⟨eP⟩⟩ := F3S7.exists_lift_section_bar hu' hY.1 hY.2.1
  obtain ⟨h1, h2⟩ := F3S7.map_subnormal_centralizer ⟨u, huL⟩ hPle hPs
  obtain ⟨h3, h4⟩ := F3S7.isSubnormal_inf_of_subnormal hL.1 hL.2.1 (centralizer {u}) h1 h2
  let eJ : ↥P ≃* ↥(P.map L.subtype) := P.equivMapOfInjective L.subtype L.subtype_injective
  obtain ⟨hJ, hJe⟩ := F3.isSolvableTwoComponentIn_sup h3 h4
    ((QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)).trans (eP.trans eY))
  refine ⟨_, hJ, hJe, mem_sup_left ⟨⟨e, heL⟩, hmem _ ?_ heY, rfl⟩⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hzu : z * u = u * z := mem_centralizer_singleton_iff.mp (hL.1 huL) |>.symm
  rcases he with rfl | rfl | rfl
  · exact hzu
  · rfl
  · change z * u * u = u * (z * u)
    calc z * u * u = u * z * u := by rw [hzu]
      _ = u * (z * u) := mul_assoc u z u

variable {z : G} {L : Subgroup G}

section Certified


theorem S7Config.false_of_nonSL (hI : S7Inputs) (h : S7Config G z L) {τ : G}
    (hτ : orderOf τ = 2) (hτz : τ ∈ centralizer {z}) (hτL : τ ∉ L) {K : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {τ})) (hτK : τ ∈ K) (eK : Bar K ≃* Bar L)
    {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer {z} ⊓ centralizer {τ}))
    (hzJ : z ∈ J) (hJL : J ≤ L) : False := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzτ : z ∈ centralizer ({τ} : Set G) := mem_centralizer_comm hτz
  have hJ' : IsTwoComponentIn J (centralizer {τ} ⊓ centralizer {z}) :=
    inf_comm (centralizer {z}) (centralizer {τ}) ▸ hJ
  have hcovK : IsCoverOf .POmegaOdd 3 3 1 2 (Bar K) := isCoverOf_of_mulEquiv eK.symm h.hcov
  have hτ2 := isPGroup_zpowers_of_orderOf_two hτ
  have hz2 := isPGroup_zpowers_of_orderOf_two h.hz
  have hττ : τ ^ 2 ^ 1 = 1 := by rw [pow_one, ← hτ, pow_orderOf_eq_one]
  obtain ⟨Y₀, hY₀, -, -, hJY⟩ := T23.exists_pumpup_of_mem h.hz hzτ hJ' hzJ
  set Y := Y₀.map (centralizer {τ}).subtype with hYdef
  have hYc : IsTwoComponentIn Y (centralizer {τ}) := T23.isTwoComponentIn_map_subtype hY₀
  have hJY' : J ≤ Y := by
    intro x hx
    have hx' : (⟨x, (hJ'.1 hx).1⟩ : ↥(centralizer ({τ} : Set G))) ∈ J.subgroupOf _ := hx
    exact ⟨⟨x, (hJ'.1 hx).1⟩, (hJY.1 hx').1, rfl⟩
  by_cases hYK : Y = K
  · have hJK : J ≤ K := hYK ▸ hJY'
    have hzK : z ∈ K := hJK hzJ
    have hzN : z ∈ normalizer (K : Set G) := le_normalizer hzK
    by_cases hc : (QuotientGroup.mk ⟨z, hzK⟩ : Bar K) ∈ center (Bar K)
    ·
      have htriv : barAction K ⟨z, hzN⟩ = 1 := barAction_eq_one_of_mem_center (t := ⟨z, hzK⟩) hc hzN
      obtain ⟨hX, -⟩ := pumpdown hK hzN hz2 htriv
      have hτX : τ ∈ centralizerResidual K z :=
        mem_centralizerResidual_of_two_pow hzN hz2 hK.2.2.2.1 htriv hτK hτz hττ
      have hJX : J ≤ centralizerResidual K z :=
        le_perfectResidual_map (le_inf hJK (hJ.1.trans inf_le_left)) hJ.2.2.1
      have heq := eq_of_le_of_isTwoComponentIn hJ' hX hJX
      exact hτL (hJL (heq ▸ hτX))
    ·
      have hle : K ⊓ centralizer {z} ≤ centralizer {τ} ⊓ centralizer {z} :=
        inf_le_inf_right _ hK.1
      have hJK' : IsTwoComponentIn J (K ⊓ centralizer {z}) :=
        ⟨le_inf hJK (hJ.1.trans inf_le_left), L219.isSubnormal_subgroupOf_of_le hle hJ'.2.1,
          hJ.2.2⟩
      have hz' : orderOf (⟨z, hzK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
      obtain ⟨hJbar, -⟩ :=
        isTwoComponentIn_map_bar hz' (isTwoComponentIn_subgroupOf_inf hzK hJK')
      have hτc : (⟨τ, hτK⟩ : ↥K) ∈ center ↥K := mem_center_of_le_centralizer hK.1 hτK
      have hτ' : orderOf (⟨τ, hτK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hτ
      obtain ⟨c0, -, -, -⟩ := lemma410c_three (by norm_num) hcovK
        (mk_mem_center_of_mem_center hτc) (mk_ne_one_of_orderOf_two hτ')
        (orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥K) hz') hc
      exact c0 _ hJbar
  ·
    have hzQ : z ∈ coreActionKernel K := le_coreActionKernel_of_ne hYc hK hYK (hJY' hzJ)
    have hzN : z ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp hzQ).1
    have htriv : barAction K ⟨z, hzN⟩ = 1 :=
      MonoidHom.mem_ker.mp ((mem_ker_barAction K ⟨z, hzN⟩).mpr hzQ)
    obtain ⟨hX, ⟨eX⟩⟩ := pumpdown hK hzN hz2 htriv
    set X := centralizerResidual K z with hXdef
    have hτX : τ ∈ X := mem_centralizerResidual_of_two_pow hzN hz2 hK.2.2.2.1 htriv hτK hτz hττ
    have hX' : IsTwoComponentIn X (centralizer {z} ⊓ centralizer {τ}) :=
      inf_comm (centralizer {τ}) (centralizer {z}) ▸ hX
    have heK : ↥X ⧸ pPrimeCore 2 ↥X ≃* Bar L := eX.trans eK
    have hcovX : IsCoverOf .POmegaOdd 3 3 1 2 (↥X ⧸ pPrimeCore 2 ↥X) :=
      isCoverOf_of_mulEquiv heK.symm h.hcov
    obtain ⟨Y₁, hY₁, -, -, hXY⟩ := T23.exists_pumpup_of_mem hτ hτz hX' hτX
    set 𝒴 := Y₁.map (centralizer {z}).subtype with h𝒴def
    have h𝒴c : IsTwoComponentIn 𝒴 (centralizer {z}) := T23.isTwoComponentIn_map_subtype hY₁
    have hX𝒴 : X ≤ 𝒴 := by
      intro x hx
      have hx' : (⟨x, (hX'.1 hx).1⟩ : ↥(centralizer ({z} : Set G))) ∈ X.subgroupOf _ := hx
      exact ⟨⟨x, (hX'.1 hx).1⟩, (hXY.1 hx').1, rfl⟩
    have hτ𝒴 : τ ∈ 𝒴 := hX𝒴 hτX
    by_cases h𝒴L : 𝒴 = L
    · exact hτL (h𝒴L ▸ hτ𝒴)
    · have hτN : τ ∈ normalizer (𝒴 : Set G) := le_normalizer hτ𝒴
      by_cases hc : (QuotientGroup.mk ⟨τ, hτ𝒴⟩ : Bar 𝒴) ∈ center (Bar 𝒴)
      ·
        have htriv' : barAction 𝒴 ⟨τ, hτN⟩ = 1 :=
          barAction_eq_one_of_mem_center (t := ⟨τ, hτ𝒴⟩) hc hτN
        obtain ⟨hX'', ⟨eX''⟩⟩ := pumpdown h𝒴c hτN hτ2 htriv'
        have hXX'' : X ≤ centralizerResidual 𝒴 τ :=
          le_perfectResidual_map (le_inf hX𝒴 (hX'.1.trans inf_le_right)) hX.2.2.1
        have heq := eq_of_le_of_isTwoComponentIn hX' hX'' hXX''
        let eY : ↥X ≃* ↥(centralizerResidual 𝒴 τ) := MulEquiv.subgroupCongr heq
        exact h𝒴L (h.eq_of_isCoverOf hI h𝒴c (isCoverOf_of_mulEquiv
          ((QuotientGroup.congr _ _ eY (pPrimeCore_map_iso 2 eY)).trans eX'') hcovX))
      ·
        have h𝒴top : 𝒴 ≠ ⊤ := fun ht =>
          centralizer_ne_top_of_simple h.nonab h.hz (top_unique (ht ▸ h𝒴c.1))
        have hle : 𝒴 ⊓ centralizer {τ} ≤ centralizer {z} ⊓ centralizer {τ} :=
          inf_le_inf_right _ h𝒴c.1
        have hX𝒴' : IsTwoComponentIn X (𝒴 ⊓ centralizer {τ}) :=
          ⟨le_inf hX𝒴 (hX'.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hX'.2.1,
            hX'.2.2⟩
        have hMX := isMTypeSchur_of_bar_equiv h.hM hX.2.2 heK.symm
        have hIX : InductionTypeField 3 ↥X := ⟨1, le_rfl, .inl hcovX⟩
        have hch := isSimpleChevalleyOver_of_knownRow hI.known h.kProper h𝒴top h𝒴c.2.2 hτ𝒴 hτ
          hX𝒴' hτX Nat.prime_three (by norm_num) hMX hIX
        have hτ' : orderOf (⟨τ, hτ𝒴⟩ : ↥𝒴) = 2 := by rw [Subgroup.orderOf_mk]; exact hτ
        let eX𝒴 : ↥(X.subgroupOf 𝒴) ≃* ↥X := subgroupOfEquivOfLe hX𝒴
        exact F3S7.false_of_lemma51eOdd hI.l51e h𝒴c.2.2 Nat.prime_three (by norm_num) hch hτ'
          hc (isTwoComponentIn_subgroupOf_inf hτ𝒴 hX𝒴') hτX le_rfl
          (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eX𝒴.symm (pPrimeCore_map_iso 2 eX𝒴.symm))
            hcovX)

theorem S7Config.mem_of_intrinsic (hI : S7Inputs) (h : S7Config G z L) {τ : G}
    (hτ : orderOf τ = 2) (hτz : τ ∈ centralizer {z}) {K : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {τ})) (hτK : τ ∈ K) (eK : Bar K ≃* Bar L)
    (hKn : (K.subgroupOf (centralizer {τ})).Normal) : τ ∈ L := by
  by_contra hτL
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzτ : z ∈ centralizer ({τ} : Set G) := mem_centralizer_comm hτz
  have hcovK : IsCoverOf .POmegaOdd 3 3 1 2 (Bar K) := isCoverOf_of_mulEquiv eK.symm h.hcov
  have hz2 := isPGroup_zpowers_of_orderOf_two h.hz
  have hττ : τ ^ 2 ^ 1 = 1 := by rw [pow_one, ← hτ, pow_orderOf_eq_one]
  have hτsq : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hLn := h.normal hI
  have hLhn : (hatIn z L).Normal := hLn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hcompL, -, ⟨EL⟩⟩ := hatIn_spec h.hL
  have hcovLh : IsCoverOf .POmegaOdd 3 3 1 2 ↥(hatIn z L) := isCoverOf_of_mulEquiv EL h.hcov
  set zh : MBar z := QuotientGroup.mk ⟨z, hzH⟩ with hzh
  have hzhL : zh ∈ hatIn z L := mk_mem_hatIn h.hzL hzH
  have hzhc : (⟨zh, hzhL⟩ : ↥(hatIn z L)) ∈ center ↥(hatIn z L) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (g : MBar z)
    change (g : MBar z) * zh = zh * (g : MBar z)
    rw [← hg', hzh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp g'.2)
  have hz' : orderOf (⟨z, hzH⟩ : ↥(centralizer ({z} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact h.hz
  have hzh1 : zh ≠ 1 := mk_ne_one_of_orderOf_two hz'
  have hzh1' : (⟨zh, hzhL⟩ : ↥(hatIn z L)) ≠ 1 := fun h1 => hzh1 (congrArg Subtype.val h1)
  set τh : MBar z := QuotientGroup.mk ⟨τ, hτz⟩ with hτh
  have hτh2 : τh * τh = 1 := by
    have h1 : (⟨τ, hτz⟩ : ↥(centralizer ({z} : Set G))) * ⟨τ, hτz⟩ = 1 := Subtype.ext hτsq
    rw [hτh, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one]
  set α : MulAut ↥(hatIn z L) := MulAut.conjNormal τh with hα
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hτh2, map_one]
  have hαapp : ∀ y : ↥(hatIn z L), ((α y : ↥(hatIn z L)) : MBar z) = τh * y * τh⁻¹ :=
    fun y => MulAut.conjNormal_apply τh y
  have hfix : (fixedSubgroup α).map (hatIn z L).subtype = hatIn z L ⊓ centralizer {τh} := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine mem_inf.mpr ⟨y.2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : ((α y : ↥(hatIn z L)) : MBar z) = y :=
        congrArg Subtype.val (mem_fixedSubgroup.mp hy)
      rw [hαapp] at h1
      calc (y : MBar z) * τh = τh * y * τh⁻¹ * τh := by rw [h1]
        _ = τh * y := by group
    · rintro ⟨hyL, hyτ⟩
      refine ⟨⟨y, hyL⟩, mem_fixedSubgroup.mpr (Subtype.ext ?_), rfl⟩
      rw [hαapp]
      have h1 : y * τh = τh * y := mem_centralizer_singleton_iff.mp hyτ
      calc τh * y * τh⁻¹ = y * τh * τh⁻¹ := by rw [h1]
        _ = y := by group
  have toC : ∀ {Y : Subgroup (MBar z)}, IsTwoComponentIn Y (hatIn z L ⊓ centralizer {τh}) →
      IsTwoComponentIn Y (centralizer {τh}) := fun hY => by
    have h1 := isTwoComponentIn_inf_of_subnormal (le_top : hatIn z L ≤ ⊤) hcompL.1.subgroupOf
      (centralizer {τh}) hY
    rwa [top_inf_eq] at h1
  rcases hI.u1 ↥(hatIn z L) 3 1 Nat.prime_three (by norm_num) hcovLh ⟨zh, hzhL⟩ hzhc hzh1' α
      hαα with ⟨x, hx2, hxZ, hαx⟩ | ⟨J', hJ', hzJ', -⟩
  ·
    have hx1 : x ≠ 1 := fun h1 => hxZ (h1 ▸ one_mem _)
    have hxo' : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
    have hαx' : ∀ y : ↥(hatIn z L), ((α y : ↥(hatIn z L)) : MBar z) =
        (x : MBar z) * y * (x : MBar z)⁻¹ := fun y => by rw [hαx]; rfl
    have hCC : hatIn z L ⊓ centralizer {(x : MBar z)} = hatIn z L ⊓ centralizer {τh} := by
      ext y
      constructor
      · rintro ⟨hyL, hyx⟩
        refine mem_inf.mpr ⟨hyL, ?_⟩
        have h1 := hαx' ⟨y, hyL⟩
        rw [hαapp] at h1
        have hyx' : y * (x : MBar z) = (x : MBar z) * y := mem_centralizer_singleton_iff.mp hyx
        have h2 : τh * y * τh⁻¹ = y := by rw [h1, ← hyx', mul_inv_cancel_right]
        rw [mem_centralizer_singleton_iff]
        calc y * τh = τh * y * τh⁻¹ * τh := by rw [h2]
          _ = τh * y := by group
      · rintro ⟨hyL, hyτ⟩
        refine mem_inf.mpr ⟨hyL, ?_⟩
        have h1 := hαx' ⟨y, hyL⟩
        rw [hαapp] at h1
        have hyτ' : y * τh = τh * y := mem_centralizer_singleton_iff.mp hyτ
        have h2 : (x : MBar z) * y * (x : MBar z)⁻¹ = y := by
          rw [← h1, ← hyτ', mul_inv_cancel_right]
        rw [mem_centralizer_singleton_iff]
        calc y * (x : MBar z) = (x : MBar z) * y * (x : MBar z)⁻¹ * (x : MBar z) := by rw [h2]
          _ = (x : MBar z) * y := by group
    obtain ⟨-, hc1, -, hc3⟩ := lemma410c_three (by norm_num) hcovLh hzhc hzh1' hxo' hxZ
    obtain ⟨Y, hY, -, hzY⟩ := hc3 ⟨zh, hzhL⟩ (Or.inl rfl)
    have hslY := (hc1 Y hY).1
    rw [pow_one] at hslY
    obtain ⟨eY⟩ := F3S7.nonempty_equiv_sl23 hslY
    obtain ⟨h1, h2⟩ := F3S7.map_subnormal_centralizer x hY.1 hY.2.1
    rw [hCC] at h1 h2
    obtain ⟨h3, h4⟩ := F3S7.isSubnormal_inf_of_subnormal (le_top : hatIn z L ≤ ⊤)
      hcompL.1.subgroupOf (centralizer {τh}) h1 h2
    rw [top_inf_eq] at h3 h4
    let eY' : ↥Y ≃* ↥(Y.map (hatIn z L).subtype) :=
      Y.equivMapOfInjective _ (hatIn z L).subtype_injective
    obtain ⟨J, hJ, ⟨eJ⟩, hmem⟩ := F3.lift_solvable hτz hτ h3 h4
      ((QuotientGroup.congr _ _ eY'.symm (pPrimeCore_map_iso 2 eY'.symm)).trans eY)
    have hzJ : z ∈ J := hmem z hzH hzτ ⟨⟨zh, hzhL⟩, hzY, rfl⟩
    have hne : z ≠ τ := fun he => hτL (he ▸ h.hzL)
    have hzτc : z * τ = τ * z := mem_centralizer_singleton_iff.mp hzτ
    by_cases hzQK : z ∈ coreActionKernel K
    ·
      have hzN : z ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp hzQK).1
      have htriv : barAction K ⟨z, hzN⟩ = 1 :=
        MonoidHom.mem_ker.mp ((mem_ker_barAction K ⟨z, hzN⟩).mpr hzQK)
      obtain ⟨hX, ⟨eX⟩⟩ := pumpdown hK hzN hz2 htriv
      have hτX := mem_centralizerResidual_of_two_pow hzN hz2 hK.2.2.2.1 htriv hτK hτz hττ
      have hX' : IsTwoComponentIn (centralizerResidual K z) (centralizer {z} ⊓ centralizer {τ}) :=
        inf_comm (centralizer {τ}) (centralizer {z}) ▸ hX
      exact F3S7.false_of_fourGroupThree hI h.nonab h.kProper h.notCat h.hz hτ hne hzτc hJ hX'
        hzJ hτX eJ le_rfl (isCoverOf_of_mulEquiv (eX.trans eK).symm h.hcov)
    ·
      have hJ' : IsSolvableTwoComponentIn J (centralizer {τ} ⊓ centralizer {z}) :=
        inf_comm (centralizer {z}) (centralizer {τ}) ▸ hJ
      have hJN : J ≤ normalizer (K : Set G) := (hJ'.1.trans inf_le_left).trans
        ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKn)
      rcases F3S7.lemma221_solvable h.hz hzτ hJ' hzJ hK hcovK (.inl hJN) with hJK | hJK
      · have hzK : z ∈ K := hJK (F3.mem_oPrimeResidualOf hzJ h.hz)
        have hzZ : (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : Bar K) ∉ center (Bar K) := fun hc =>
          hzQK ((mem_ker_barAction K ⟨z, le_normalizer hzK⟩).mp (MonoidHom.mem_ker.mpr
            (barAction_eq_one_of_mem_center (t := ⟨z, hzK⟩) hc (le_normalizer hzK))))
        obtain ⟨J₁, hJ₁, ⟨e₁⟩, hτJ₁⟩ :=
          F3S7.spinSeven_lift_three_three hK hτK hτ hcovK hzK h.hz hzZ (e := τ) (Or.inl rfl)
        exact h.false_of_slTwo hI hτ hτz hτL (inf_comm (centralizer {τ}) (centralizer {z}) ▸ hJ₁)
          hτJ₁ e₁ (.inl (hJ₁.1.trans (inf_le_right.trans
            ((normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn))))
      · exact hzQK (hJK hzJ)
  ·
    have hJh : IsTwoComponentIn (J'.map (hatIn z L).subtype) (hatIn z L ⊓ centralizer {τh}) := by
      have h1 := L35.isTwoComponentIn_map_of_injective (hatIn z L).subtype
        (hatIn z L).subtype_injective hJ'
      rwa [hfix] at h1
    obtain ⟨J, hJ, hmem, hgen, -⟩ := lift_twoComponent hτz hτ (toC hJh)
    have hzJ : z ∈ J := hmem z hzH hzτ ⟨1, by rw [pow_one]; exact h.hz⟩ ⟨_, hzJ', rfl⟩
    have hJL : J ≤ L := lift_le_of_le_hatIn h.hL (map_subtype_le J') hgen
    exact h.false_of_nonSL hI hτ hτz hτL hK hτK eK hJ hzJ hJL

theorem S7Config.conj_mem (hI : S7Inputs) (h : S7Config G z L) (g : G)
    (hg : g * z * g⁻¹ ∈ centralizer {z}) : g * z * g⁻¹ ∈ L := by
  have hmap : (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer {g * z * g⁻¹} := by
    rw [map_centralizer_singleton_mulEquiv, MulAut.conj_apply]
  have hK : IsTwoComponentIn (L.map (MulAut.conj g).toMonoidHom) (centralizer {g * z * g⁻¹}) :=
    hmap ▸ L35.isTwoComponentIn_map_of_injective _ (MulAut.conj g).injective h.hL
  let eg : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj g).injective
  have hτ : orderOf (g * z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz
  have hKn : ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
      (centralizer {g * z * g⁻¹})).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hK.1, ← hmap]
    rintro _ ⟨c, hc, rfl⟩
    have hcN : c ∈ normalizer (L : Set G) :=
      (normal_subgroupOf_iff_le_normalizer h.hL.1).mp (h.normal hI) hc
    have hφc : (MulAut.conj g).toMonoidHom c = g * c * g⁻¹ := rfl
    rw [hφc, mem_normalizer_iff]
    intro y
    rw [mem_map_equiv, mem_map_equiv, MulAut.conj_symm_apply, MulAut.conj_symm_apply]
    have h1 := (mem_normalizer_iff.mp hcN) (g⁻¹ * y * g)
    rw [show g⁻¹ * (g * c * g⁻¹ * y * (g * c * g⁻¹)⁻¹) * g = c * (g⁻¹ * y * g) * c⁻¹ by group]
    exact h1
  exact h.mem_of_intrinsic hI hτ hg hK ⟨z, h.hzL, rfl⟩
    (QuotientGroup.congr _ _ eg (pPrimeCore_map_iso 2 eg)).symm hKn

end Certified

theorem S7Config.eq_of_mk_mem_center (h : S7Config G z L) {u : G} (huL : u ∈ L)
    (hu : orderOf u = 2) (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∈ center (Bar L)) :
    u = z := by
  have hOodd := odd_card_pPrimeCore_two ↥L
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hZ2 : Nat.card ↥(center (Bar L)) = 2 := h.hcov.2.1
  have heq := T23.eq_of_ne_one_of_card_two hZ2 (a := ⟨_, huZ⟩)
    (b := ⟨_, mk_mem_center_of_mem_center hzc⟩)
    (fun h1 => mk_ne_one_of_orderOf_two hu' (congrArg Subtype.val h1))
    (fun h1 => mk_ne_one_of_orderOf_two hz' (congrArg Subtype.val h1))
  have heq' : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) = QuotientGroup.mk ⟨z, h.hzL⟩ :=
    congrArg Subtype.val heq
  rw [QuotientGroup.eq] at heq'
  have huu : (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
  have hzz : (⟨z, h.hzL⟩ : ↥L) * ⟨z, h.hzL⟩ = 1 := by rw [← sq, ← hz', pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := exists_conj_of_inv_mul_mem hOodd huu hzz heq'
  have h1 : (⟨u, huL⟩ : ↥L) = ⟨z, h.hzL⟩ := by
    calc (⟨u, huL⟩ : ↥L) = c⁻¹ * (c * ⟨u, huL⟩ * c⁻¹) * c := by group
      _ = c⁻¹ * ⟨z, h.hzL⟩ * c := by rw [hc]
      _ = ⟨z, h.hzL⟩ := by rw [mul_assoc, ← mem_center_iff.mp hzc c, inv_mul_cancel_left]
  exact congrArg Subtype.val h1

theorem S7Config.exists_conj_ne (h : S7Config G z L) :
    ∃ g : G, g * z * g⁻¹ ∈ centralizer {z} ∧ g * z * g⁻¹ ≠ z := by
  have := h.simple
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite G
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.hz
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hzz : z * z = 1 := by rw [← sq, ← h.hz, pow_orderOf_eq_one]
  obtain ⟨N, hN, hNodd, hNz⟩ := ZStar.glauberman_zStar G z hz1 hzz
    (fun g hg => hcon g (mem_centralizer_singleton_iff.mpr hg))
  have hNbot : N = ⊥ := by
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · exact h1
    · exfalso
      have hzN : z ∈ N := h1 ▸ mem_top z
      have hdvd := orderOf_dvd_natCard (⟨z, hzN⟩ : N)
      rw [Subgroup.orderOf_mk, h.hz] at hdvd
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)
  have hZ : center G = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonab
  have hzc : z ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h1 := hNz g
    rw [hNbot, mem_bot] at h1
    calc g * z = g * z * g⁻¹ * z⁻¹ * (z * g) := by group
      _ = z * g := by rw [h1, one_mul]
  rw [hZ, mem_bot] at hzc
  exact hz1 hzc

section Certified


theorem S7Config.exists_conj (hI : S7Inputs) (h : S7Config G z L) {u : G} (huL : u ∈ L)
    (hu : orderOf u = 2) : ∃ g : G, g * z * g⁻¹ = u := by
  by_cases huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∈ center (Bar L)
  · exact ⟨1, by rw [h.eq_of_mk_mem_center huL hu huZ]; group⟩
  · obtain ⟨g₀, hg₀C, hg₀ne⟩ := h.exists_conj_ne
    have hvL := h.conj_mem hI g₀ hg₀C
    have hv : orderOf (g₀ * z * g₀⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz
    have hvZ : (QuotientGroup.mk (⟨_, hvL⟩ : ↥L) : Bar L) ∉ center (Bar L) := fun hc =>
      hg₀ne (h.eq_of_mk_mem_center hvL hv hc)
    obtain ⟨x, -, hx⟩ := F3S7.spinSeven_conj_of_involution_three h.hcov hvL huL hv hu hvZ huZ
    exact ⟨x * g₀, by rw [← hx]; group⟩

theorem S7Config.conj_iff (hI : S7Inputs) (h : S7Config G z L) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) :
    (∃ g : G, g * z * g⁻¹ = x) ↔ (x ∈ L ∧ orderOf x = 2) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨h.conj_mem hI g hx, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz⟩
  · rintro ⟨hxL, hx2⟩
    exact h.exists_conj hI hxL hx2

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
