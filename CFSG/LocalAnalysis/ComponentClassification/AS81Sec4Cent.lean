module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz2

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subgroupOf_inf_center {A H : Subgroup G} (hHA : H ≤ A) :
    (H.subgroupOf A ⊓ center ↥A).map A.subtype = H ⊓ centralizer (A : Set G) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyH, hyZ⟩, rfl⟩
    refine ⟨mem_subgroupOf.mp hyH, mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp hyZ ⟨a, ha⟩)
  · rintro ⟨hxH, hxC⟩
    refine ⟨⟨x, hHA hxH⟩, ⟨mem_subgroupOf.mpr hxH, mem_center_iff.mpr fun a => ?_⟩, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp hxC a a.2)

theorem exists_mem_inv_mul_mem_centralizer_of_cover {A H : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥A) (cv : L34Cover ↥A) (hHA : H ≤ A) (hH : IsElemAbelian 2 H)
    (hH16 : Nat.card H = 16 * Nat.card (H ⊓ centralizer (A : Set G) : Subgroup G)) {c : G}
    (hcA : c ∈ normalizer (A : Set G)) (hcH : ∀ h ∈ H, c * h * c⁻¹ = h) :
    ∃ h ∈ H, h⁻¹ * c ∈ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := oddCore_le_center hq.1 hq.2
  have : Finite cv.k := Nat.finite_of_card_ne_zero (by rw [cv.card_k]; omega)
  have : CharP cv.k 2 := charP_two_of_card cv.card_k
  have hH₀ : IsPGroup 2 (H.subgroupOf A) := (isPGroup_two_of_isElemAbelian hH).comap_subtype
  obtain ⟨T, hT⟩ := hH₀.exists_le_sylow
  obtain ⟨φ, hφs, hφk, hφT⟩ := cv.exists_std hO T
  have hH₀2 : ∀ x ∈ (H.subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hH.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card ((H.subgroupOf A).map φ) = 16 := by
    have h1 := card_eq_card_inf_ker_mul_card_map φ (H.subgroupOf A)
    rw [hφk, Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv] at h1
    have h2 : Nat.card (H.subgroupOf A ⊓ center ↥A : Subgroup ↥A) =
        Nat.card (H ⊓ centralizer (A : Set G) : Subgroup G) := by
      rw [← map_subgroupOf_inf_center hHA, card_map_of_injective A.subtype_injective]
    rw [h2, hH16] at h1
    have hpos : 0 < Nat.card (H ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
    have := Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (mul_comm _ _))
    omega
  have hH₀U : (H.subgroupOf A).map φ ≤ projUnip cv.k := hφT ▸ map_mono hT
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (H.subgroupOf A).map φ = projRad cv.k i := by
    rcases eq_projRad_of_le_projUnip cv.card_k hH₀U hH₀2 hH₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  set σ := normalizerConj hcA with hσdef
  have hσ : φ.ker.map (σ : ↥A →* ↥A) = φ.ker := by
    rw [hφk]
    exact Subgroup.map_center_eq σ
  have hα : ∀ x ∈ projRad cv.k i, descendAut φ hφs σ hσ x = x := by
    intro x hx
    rw [← hi] at hx
    obtain ⟨h₀, hh₀, rfl⟩ := hx
    rw [descendAut_apply]
    congr 1
    apply Subtype.ext
    rw [hσdef, coe_normalizerConj_apply]
    exact hcH _ (mem_subgroupOf.mp hh₀)
  obtain ⟨r, hr, hαr⟩ := exists_eq_conj_of_fix_projRad i hα
  rw [← hi] at hr
  obtain ⟨h₁, hh₁, rfl⟩ := hr
  refine ⟨h₁, mem_subgroupOf.mp hh₁, mem_centralizer_of_conj_mem_center hq.1 fun a ha => ?_⟩
  have h1 : φ (σ ⟨a, ha⟩) = φ (h₁ * ⟨a, ha⟩ * h₁⁻¹) := by
    rw [← descendAut_apply φ hφs σ hσ, hαr, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set z : ↥A := (h₁ * ⟨a, ha⟩ * h₁⁻¹)⁻¹ * σ ⟨a, ha⟩ with hz
  have hzk : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, h1, inv_mul_cancel]
  rw [hφk] at hzk
  have hzc : ∀ b ∈ A, (z : G) * b = b * z := fun b hb =>
    congrArg Subtype.val (mem_center_iff.mp hzk ⟨b, hb⟩).symm
  refine ⟨z, z.2, hzc, ?_⟩
  have hσa : ((σ ⟨a, ha⟩ : ↥A) : G) = (h₁ : G) * a * (h₁ : G)⁻¹ * z := by
    rw [hz]
    simp only [coe_mul, coe_inv]
    group
  have hcac : c * a * c⁻¹ = (h₁ : G) * a * (h₁ : G)⁻¹ * z := by
    rw [← hσa, hσdef, coe_normalizerConj_apply]
  have hz1 : (z : G) * (h₁ : G) = h₁ * z := hzc _ h₁.2
  calc (h₁ : G)⁻¹ * c * a * ((h₁ : G)⁻¹ * c)⁻¹ = (h₁ : G)⁻¹ * (c * a * c⁻¹) * h₁ := by group
    _ = (h₁ : G)⁻¹ * ((h₁ : G) * a * (h₁ : G)⁻¹ * z) * h₁ := by rw [hcac]
    _ = a * ((h₁ : G)⁻¹ * ((z : G) * h₁)) := by group
    _ = a * z := by rw [hz1]; group
    _ = z * a := (hzc a ha).symm

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem centralizer_eq_sup_oddCoreIn_of_le (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hRA : R ≤ A) :
    centralizer (A : Set G) = R ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_sup_oddCoreIn_of_central hR.isPGroup hR.le ?_ ?_
  · intro r hr
    rw [mem_centralizer_iff]
    intro k hk
    exact (mem_centralizer_iff.mp hk r (hRA hr)).symm
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (isSylowOf_iff.mp hR).2.2)

theorem centralizer_eq_sup_of_le (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hRA : R ≤ A) {X : Subgroup G} (hX : X = E ∨ X = F) :
    centralizer (X : Set G) = X ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  obtain ⟨cv⟩ := exists_l34Cover hstd.1.1 hL hstd.1.2 (sq_eq_one_of_mem_center hR hF.elemR)
  have hAR : A ⊔ R = A := sup_eq_left.mpr hRA
  obtain ⟨hXA, hRX, hXe, hX64⟩ : X ≤ A ∧ R ≤ X ∧ IsElemAbelian 2 X ∧ Nat.card X = 64 := by
    rcases hX with rfl | rfl
    · exact ⟨hAR ▸ hF.E_le, hF.R_le_E, hF.elemE, hF.cardE⟩
    · exact ⟨hAR ▸ hF.F_le, hF.R_le_F, hF.elemF, hF.cardF⟩
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hXe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hXC : X ≤ centralizer (X : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  have hXK : X ⊓ centralizer (A : Set G) = R :=
    hR.eq_of_le (le_inf hRX hR.le) inf_le_right
      ((isPGroup_two_of_isElemAbelian hXe).to_le inf_le_left)
  have hH16 : Nat.card X = 16 * Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) := by
    rw [hXK, hF.cardR, hX64]
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hR hKte.1
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hCN : ∀ c ∈ centralizer (X : Set G), c ∈ normalizer (A : Set G) := fun c hc => by
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKte (hR.le hr) hr1'
      (hF.elemR.2 r hr) (mem_centralizer_iff.mp hc r (hRX hr)).symm
  have hK := centralizer_eq_sup_oddCoreIn_of_le hR hRA
  refine le_antisymm (fun c hc => ?_) (sup_le hXC fun o ho => ?_)
  · obtain ⟨h, hh, hd⟩ := exists_mem_inv_mul_mem_centralizer_of_cover hstd.1 cv hXA hXe hH16
      (hCN c hc) fun h hh => mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hc h hh).symm
    rw [hK] at hd
    rw [show c = h * (h⁻¹ * c) by group]
    refine mul_mem (mem_sup_left hh) ?_
    exact (sup_le_sup_right hRX _ : R ⊔ _ ≤ X ⊔ _) hd
  · have hoK := AS76b.oddCoreIn_le (centralizer (A : Set G)) ho
    exact mem_centralizer_iff.mpr fun x hx => (mem_centralizer_iff.mp hoK x (hXA hx))

end Frame

end CFSG.ComponentClassification.AS81
