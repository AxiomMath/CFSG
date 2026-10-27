module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaOrbCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step46
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cent

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.Blueprint.NativeSporadic HeSylow Hexa CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag

namespace Hexa

theorem hexaOrb_facts (hc : hexaCheck = true) (ho : hexaOrbCheck = true) :
    ∀ t ∈ hexaT, t ≠ 1 → ∃ m ∈ hexaM, m * t * m⁻¹ = hexaT0P ∨ m * t * m⁻¹ ∈ hexaR0 := by
  obtain ⟨hT, hM, -, -, hR0, hvt0, -⟩ := hexaCheck_parts hc
  intro t ht ht1
  obtain ⟨a, ha, hra⟩ := (mem_grpN_iff hT).1 ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hc1 := List.all_eq_true.1 ho i (List.mem_range.2 hi)
  rw [getElem!_pos _ i hi] at hc1
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc1
  rcases hc1 with hc1 | ⟨hw, hc1⟩
  · exact absurd ((eqA_iff hra rep_idA).1 hc1) ht1
  · have hmm := List.getElem_mem hw
    rw [getElem!_pos (eltsN 64 hexaMGens) _ hw] at hc1
    have hvm := validA_of_mem_elts hM hmm
    refine ⟨permOfArr 64 _, (mem_grpN_iff hM).2 ⟨_, hmm, rep_of_validA hvm⟩, ?_⟩
    have hr := rep_conjA hvm hra
    rcases hc1 with hc1 | hc1
    · exact Or.inl ((eqA_iff hr (rep_of_validA hvt0)).1 hc1)
    · exact Or.inr (mem_of_inLN hR0 hc1 hr)

end Hexa

variable {G : Type} [Group G] [Finite G]

section Inv

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem mem_or_mem_of_mul_self_eq_one (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hRA : R ≤ A) {x : G} (hx : x ∈ E ⊔ F) (hx2 : x * x = 1) : x ∈ E ∨ x ∈ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hR := hF.sylowR
  obtain ⟨cv⟩ := exists_l34Cover hstd.1.1 hL hstd.1.2 (sq_eq_one_of_mem_center hR hF.elemR)
  have hO := oddCore_le_center hstd.1.1 hstd.1.2
  have : Finite cv.k := Nat.finite_of_card_ne_zero (by rw [cv.card_k]; omega)
  have hAR : A ⊔ R = A := sup_eq_left.mpr hRA
  have hEA : E ≤ A := hAR ▸ hF.E_le
  have hFA : F ≤ A := hAR ▸ hF.F_le
  have hEFA : E ⊔ F ≤ A := sup_le hEA hFA
  have hEF2 : IsPGroup 2 (E ⊔ F : Subgroup G) := hF.sylow.isPGroup
  obtain ⟨T, hT⟩ := (hEF2.comap_subtype (K := A)).exists_le_sylow
  obtain ⟨φ, -, hφk, hφT⟩ := cv.exists_std hO T
  have hcR : ∀ c : ↥A, c ∈ center ↥A → c * c = 1 → (c : G) ∈ R := by
    intro c hc hcc
    have hcK : (c : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun a ha =>
      congrArg Subtype.val (mem_center_iff.mp hc ⟨a, ha⟩)
    refine mem_of_mem_centralizer_of_isPGroup hR c.2 hcK
      (AS76b.isPGroup_zpowers_of_pow_eq_one (n := 1) ?_)
    rw [pow_one, pow_two]
    exact congrArg Subtype.val hcc
  have himg : ∀ Y : Subgroup G, Y ≤ A → IsElemAbelian 2 Y → Nat.card Y = 64 → R ≤ Y →
      Y ≤ E ⊔ F → ∃ i : Fin 2, (Y.subgroupOf A).map φ = projRad cv.k i := by
    intro Y hYA hYe hY64 hRY hYEF
    have hYK : Y ⊓ centralizer (A : Set G) = R :=
      hR.eq_of_le (le_inf hRY hR.le) inf_le_right
        ((isPGroup_two_of_isElemAbelian hYe).to_le inf_le_left)
    have h16 : Nat.card ((Y.subgroupOf A).map φ) = 16 := by
      have h1 := card_eq_card_inf_ker_mul_card_map φ (Y.subgroupOf A)
      rw [hφk, Nat.card_congr (subgroupOfEquivOfLe hYA).toEquiv] at h1
      have h2 : Nat.card (Y.subgroupOf A ⊓ center ↥A : Subgroup ↥A) = 4 := by
        rw [← card_map_of_injective A.subtype_injective, map_subgroupOf_inf_center hYA, hYK,
          hF.cardR]
      rw [h2, hY64] at h1
      omega
    have hU : (Y.subgroupOf A).map φ ≤ projUnip cv.k :=
      hφT ▸ map_mono (le_trans (show Y.subgroupOf A ≤ (E ⊔ F).subgroupOf A from
        fun y hy => hYEF hy) hT)
    have h2 : ∀ v ∈ (Y.subgroupOf A).map φ, v ^ 2 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, show y ^ 2 = 1 from
        Subtype.ext (by simpa using hYe.2 _ (mem_subgroupOf.mp hy)), map_one]
    rcases eq_projRad_of_le_projUnip cv.card_k hU h2 h16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  obtain ⟨iE, hiE⟩ := himg E hEA hF.elemE hF.cardE hF.R_le_E le_sup_left
  obtain ⟨iF, hiF⟩ := himg F hFA hF.elemF hF.cardF hF.R_le_F le_sup_right
  have hlift : ∀ {Y Z : Subgroup G}, Y ≤ A → Z ≤ A → R ≤ Z → (∀ y ∈ Y, y * y = 1) →
      (∀ w ∈ Z, w * w = 1) → ∀ y : ↥A, (y : G) ∈ Y → φ y ∈ (Z.subgroupOf A).map φ →
        (y : G) ∈ Z := by
    intro Y Z hYA hZA hRZ hY2 hZ2 y hy hφy
    obtain ⟨w, hw, hwy⟩ := hφy
    have hc : w⁻¹ * y ∈ center ↥A := by
      rw [← hφk, MonoidHom.mem_ker, map_mul, map_inv, hwy, inv_mul_cancel]
    have hcc : (w⁻¹ * y) * (w⁻¹ * y) = 1 := by
      have hcomm : (w⁻¹ * y) * w = w * (w⁻¹ * y) := (mem_center_iff.mp hc w).symm
      have hy2 : y * y = 1 := Subtype.ext (hY2 _ hy)
      have hw2 : w * w = 1 := Subtype.ext (hZ2 _ (mem_subgroupOf.mp hw))
      have h3 : y * y = w * w * ((w⁻¹ * y) * (w⁻¹ * y)) := by
        calc y * y = w * (w⁻¹ * y) * (w * (w⁻¹ * y)) := by group
          _ = w * ((w⁻¹ * y) * w) * (w⁻¹ * y) := by group
          _ = w * (w * (w⁻¹ * y)) * (w⁻¹ * y) := by rw [hcomm]
          _ = w * w * ((w⁻¹ * y) * (w⁻¹ * y)) := by group
      rw [hy2, hw2, one_mul] at h3
      exact h3.symm
    have h1 := hcR _ hc hcc
    rw [show (y : G) = w * (w⁻¹ * y : ↥A) by simp]
    exact Z.mul_mem (mem_subgroupOf.mp hw) (hRZ h1)
  have hE2 : ∀ y ∈ E, y * y = 1 := fun y hy => by rw [← pow_two]; exact hF.elemE.2 y hy
  have hF2 : ∀ y ∈ F, y * y = 1 := fun y hy => by rw [← pow_two]; exact hF.elemF.2 y hy
  have hne : iE ≠ iF := by
    intro h
    apply hF.ne
    refine Subgroup.eq_of_le_of_card_ge (fun e he => ?_) (by rw [hF.cardE, hF.cardF])
    have hφe : φ ⟨e, hEA he⟩ ∈ (F.subgroupOf A).map φ := by
      rw [hiF, ← h, ← hiE]
      exact ⟨⟨e, hEA he⟩, he, rfl⟩
    exact hlift hEA hFA hF.R_le_F hE2 hF2 ⟨e, hEA he⟩ he hφe
  have hxU : φ ⟨x, hEFA hx⟩ ∈ projUnip cv.k :=
    hφT ▸ ⟨⟨x, hEFA hx⟩, hT (show (⟨x, hEFA hx⟩ : ↥A) ∈ (E ⊔ F).subgroupOf A from hx), rfl⟩
  have hx2' : (φ ⟨x, hEFA hx⟩) ^ 2 = 1 := by
    rw [← map_pow, show (⟨x, hEFA hx⟩ : ↥A) ^ 2 = 1 from Subtype.ext (by rw [pow_two]; exact hx2),
      map_one]
  have hxS : ∀ {Z : Subgroup G}, Z ≤ A → R ≤ Z → (∀ w ∈ Z, w * w = 1) →
      φ ⟨x, hEFA hx⟩ ∈ (Z.subgroupOf A).map φ → x ∈ Z := by
    intro Z hZA hRZ hZ2 hφx
    have := hlift (Y := zpowers x) (zpowers_le.mpr (hEFA hx)) hZA hRZ (fun y hy => by
      obtain ⟨k, rfl⟩ := hy
      rw [← zpow_add, ← two_mul, zpow_mul, show x ^ (2 : ℤ) = 1 by
        rw [zpow_two]; exact hx2, one_zpow]) hZ2 ⟨x, hEFA hx⟩ (mem_zpowers x) hφx
    exact this
  rcases mem_projRad_of_sq_eq_one cv.card_k hxU hx2' with h0 | h1
  · rcases Fin.eq_zero_or_eq_succ iE with hE0 | ⟨j, hj⟩
    · exact Or.inl (hxS hEA hF.R_le_E hE2 (by rw [hiE, hE0]; exact h0))
    · have hF0 : iF = 0 := by
        rcases Fin.eq_zero_or_eq_succ iF with h | ⟨j', hj'⟩
        · exact h
        · exfalso
          apply hne
          rw [hj, hj', Fin.fin_one_eq_zero j, Fin.fin_one_eq_zero j']
      exact Or.inr (hxS hFA hF.R_le_F hF2 (by rw [hiF, hF0]; exact h0))
  · rcases Fin.eq_zero_or_eq_succ iE with hE0 | ⟨j, hj⟩
    · have hF1 : iF = 1 := by
        rcases Fin.eq_zero_or_eq_succ iF with h | ⟨j', hj'⟩
        · exact absurd (hE0.trans h.symm) hne
        · rw [hj', Fin.fin_one_eq_zero j']
          rfl
      exact Or.inr (hxS hFA hF.R_le_F hF2 (by rw [hiF, hF1]; exact h1))
    · have hE1 : iE = 1 := by rw [hj, Fin.fin_one_eq_zero j]; rfl
      exact Or.inl (hxS hEA hF.R_le_E hE2 (by rw [hiE, hE1]; exact h1))

end Inv

section Fusion

variable {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G} {z : G}

theorem conj_z_or_mem_of_mem (hF : HexaFacts)
    (horb : ∀ t ∈ hexaT, t ≠ 1 → ∃ m ∈ hexaM, m * t * m⁻¹ = hexaT0P ∨ m * t * m⁻¹ ∈ hexaR0)
    (hNX : Sec4NXModel) (hQ : Sec4Q G A R g E F S₁ Q z)
    (hcent : ∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z) {X : Subgroup G}
    (hX : X = E ∨ X = F) (hQX : Nat.card (Q ⊓ X : Subgroup G) = 16) {x : G} (hx : x ∈ X)
    (hx1 : x ≠ 1) : (∃ h : G, h⁻¹ * x * h = z) ∨ ∃ h : G, h⁻¹ * x * h ∈ R := by
  have hset := hQ.setting
  have hEF := sup_le_of_isSylowOf_normalizer hset hQ.sylowN
  have hXS : X ≤ S₁ := by
    rcases hX with rfl | rfl
    exacts [le_sup_left.trans hEF, le_sup_right.trans hEF]
  have hQN : Q ≤ normalizer (X : Set G) := by
    rcases hX with rfl | rfl
    exacts [hQ.normE, hQ.normF]
  have hzX : z ∈ X := z_mem_of_card hQ hQN hQX
  have hLN : AS76b.oUpperTwoPrime (normalizer (X : Set G)) ≤ normalizer (X : Set G) :=
    oUpper_le' _
  have hQL : Q ≤ AS76b.oUpperTwoPrime (normalizer (X : Set G)) := le_oUpper_of_card hQN hQ.card
  obtain ⟨ι, ψ, hψs, hψk, hψe, hιR⟩ := hNX G A R g E F hset X (by
    rcases hX with rfl | rfl <;> simp)
  have hd0 : NXDatum X _ (hexaT.subtype.comp ι.toMonoidHom) (hexaM.subtype.comp ψ) :=
    { inj := hexaT.subtype_injective.comp ι.injective
      rangeι := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
          ← MonoidHom.range_eq_map, range_subtype]
      rangeψ := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψs, ← MonoidHom.range_eq_map,
          range_subtype]
      ker := by
        rw [← hψk]
        ext ℓ
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype,
          OneMemClass.coe_eq_one]
      equiv := fun ℓ x y hy => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype]
        exact hψe ℓ x y hy }
  set ι₀ := hexaT.subtype.comp ι.toMonoidHom with hι₀
  set ψ₀ := hexaM.subtype.comp ψ with hψ₀
  obtain ⟨hV1, hV2, hV3, hV4, -⟩ := hd0.image_Q hQ hQL hLN hzX hXS hQX hcent
  have ht1 : ι₀ ⟨z, hzX⟩ ≠ 1 := by
    intro h
    rw [← map_one ι₀] at h
    exact hQ.z_ne_one (congrArg Subtype.val (hd0.inj h))
  obtain ⟨m, hm, hmt⟩ := hF.orbit _ (hd0.iota_mem _) ht1 _ hV1 hV3 hV2 (by rw [hV4]; norm_num)
  have hxt1 : ι₀ ⟨x, hx⟩ ≠ 1 := by
    intro h
    rw [← map_one ι₀] at h
    exact hx1 (congrArg Subtype.val (hd0.inj h))
  obtain ⟨m', hm', hcase⟩ := horb _ (hd0.iota_mem _) hxt1
  have hm'r : m' ∈ ψ₀.range := hd0.rangeψ ▸ hm'
  obtain ⟨ℓ', rfl⟩ := hm'r
  have hy : (ℓ' : G) * x * (ℓ' : G)⁻¹ ∈ X := (mem_normalizer_iff.mp (hLN ℓ'.2) x).mp hx
  have he' := hd0.equiv ℓ' ⟨x, hx⟩ ⟨_, hy⟩ rfl
  rcases hcase with hc | hc
  ·
    left
    have hmr : m ∈ ψ₀.range := hd0.rangeψ ▸ hm
    obtain ⟨ℓ, rfl⟩ := hmr
    have hz' : (ℓ : G) * z * (ℓ : G)⁻¹ ∈ X := (mem_normalizer_iff.mp (hLN ℓ.2) z).mp hzX
    have he := hd0.equiv ℓ ⟨z, hzX⟩ ⟨_, hz'⟩ rfl
    have hinj : (⟨_, hy⟩ : ↥X) = ⟨_, hz'⟩ := hd0.inj (by rw [he', he, hc, hmt])
    have h1 : (ℓ' : G) * x * (ℓ' : G)⁻¹ = (ℓ : G) * z * (ℓ : G)⁻¹ := congrArg Subtype.val hinj
    refine ⟨(ℓ' : G)⁻¹ * ℓ, ?_⟩
    calc ((ℓ' : G)⁻¹ * ℓ)⁻¹ * x * ((ℓ' : G)⁻¹ * ℓ) =
        (ℓ : G)⁻¹ * ((ℓ' : G) * x * (ℓ' : G)⁻¹) * ℓ := by group
      _ = z := by rw [h1]; group
  ·
    right
    refine ⟨(ℓ' : G)⁻¹, ?_⟩
    have hR' : ((ι ⟨_, hy⟩ : ↥hexaT) : Equiv.Perm (Fin 64)) ∈ hexaR0 := by
      have : ι₀ ⟨_, hy⟩ = ((ι ⟨_, hy⟩ : ↥hexaT) : Equiv.Perm (Fin 64)) := rfl
      rw [← this, he']
      exact hc
    have := (hιR ⟨_, hy⟩).2 hR'
    simpa using this

end Fusion

theorem sec4FusionEF_of_check
    (ho : hexaOrbCheck = true) (h16 : Step16) (h44 : Step44ii) (hNX : Sec4NXModel) :
    Sec4FusionEF := by
  intro G _ _ A R g E F S₁ Q z hQ x hx hx2
  have hset := hQ.setting
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hRA : R ≤ A := (h16 G A R g E F hset.frame hset.even).1
  obtain ⟨hQE, hQF, hcent, -⟩ := sec4Q_qe h44 hQ
  have horb := Hexa.hexaOrb_facts hexa_check ho
  rcases mem_or_mem_of_mul_self_eq_one hset.frame hset.type hRA hx hxx with hxE | hxF
  · exact conj_z_or_mem_of_mem hexaFacts horb hNX hQ hcent (Or.inl rfl) hQE hxE hx1
  · exact conj_z_or_mem_of_mem hexaFacts horb hNX hQ hcent (Or.inr rfl) hQF hxF hx1

theorem sec4FusionEF_of
    (h16 : Step16) (h44 : Step44ii) (hNX : Sec4NXModel) :
    Sec4FusionEF :=
  sec4FusionEF_of_check Hexa.hexaOrb_check h16 h44 hNX

end CFSG.ComponentClassification.AS81
