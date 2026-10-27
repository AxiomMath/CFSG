module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Gamma
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDichotomy
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Dich

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3 JData)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section C

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem g2N_v_split
    (D E F : K) :
    g2N 0 0 0 D E F = pinnedX .G2 K g2v D * g2N 0 0 0 0 E F := by
  rw [pinnedX_v_eq_g2N, g2N_zero_mul_g2N_zero]
  exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)

omit [Finite K] in
theorem conj_ru_v_one
    (y z : K) :
    pinnedX .G2 K g2r y * pinnedX .G2 K g2u z * pinnedX .G2 K g2v 1 *
      (pinnedX .G2 K g2r y * pinnedX .G2 K g2u z)⁻¹ = g2N 0 0 0 1 y z := by
  rw [mul_inv_rev, pinnedX_inv_eq, pinnedX_inv_eq,
    show pinnedX .G2 K g2r y * pinnedX .G2 K g2u z * pinnedX .G2 K g2v 1 *
        (pinnedX .G2 K g2u z * pinnedX .G2 K g2r y) =
      pinnedX .G2 K g2r y * (pinnedX .G2 K g2u z * pinnedX .G2 K g2v 1 *
        pinnedX .G2 K g2u z) * pinnedX .G2 K g2r y by group,
    pinnedX_v_eq_g2N, conj_u_radical, conj_r_radical]
  exact g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)

omit [Finite K] in
theorem conj_nr_v_one :
    pinnedX .G2 K g2nr 1 * pinnedX .G2 K g2v 1 * (pinnedX .G2 K g2nr 1)⁻¹ =
      pinnedX .G2 K g2a 1 * g2N 0 0 0 1 0 1 := by
  have h := conj_nr_av (K := K) 1 0 1
  rw [pinnedX_inv_eq, pinnedX_v_eq_g2N, h, pinnedX_a_eq_g2N, g2N_zero_mul_g2N_zero]
  exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)

omit [Finite K] in
theorem conj_wnr_v_one :
    weylElt .G2 K g2ia 1 * pinnedX .G2 K g2nr 1 * pinnedX .G2 K g2v 1 *
      (weylElt .G2 K g2ia 1 * pinnedX .G2 K g2nr 1)⁻¹ =
      pinnedX .G2 K g2na 1 * g2N 0 0 0 1 1 0 := by
  rw [mul_inv_rev,
    show weylElt .G2 K g2ia 1 * pinnedX .G2 K g2nr 1 * pinnedX .G2 K g2v 1 *
        ((pinnedX .G2 K g2nr 1)⁻¹ * (weylElt .G2 K g2ia 1)⁻¹) =
      weylElt .G2 K g2ia 1 * (pinnedX .G2 K g2nr 1 * pinnedX .G2 K g2v 1 *
        (pinnedX .G2 K g2nr 1)⁻¹) * (weylElt .G2 K g2ia 1)⁻¹ by group,
    conj_nr_v_one,
    show weylElt .G2 K g2ia 1 * (pinnedX .G2 K g2a 1 * g2N 0 0 0 1 0 1) *
        (weylElt .G2 K g2ia 1)⁻¹ =
      (weylElt .G2 K g2ia 1 * pinnedX .G2 K g2a 1 * (weylElt .G2 K g2ia 1)⁻¹) *
        (weylElt .G2 K g2ia 1 * g2N 0 0 0 1 0 1 * (weylElt .G2 K g2ia 1)⁻¹) by group,
    ← pinnedX_na_eq, weylElt_a_conj_g2N]
  exact congrArg _ (g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring))

theorem eq_pinnedX_v_of_commute
    {c : ModGL .G2 K} (hc : c ∈ adjointGroup .G2 K)
    (hbc : ∀ y z : K, Commute c (g2N 0 0 0 1 y z))
    (ha : Commute c (pinnedX .G2 K g2a 1 * g2N 0 0 0 1 0 1))
    (hna : Commute c (pinnedX .G2 K g2na 1 * g2N 0 0 0 1 1 0)) :
    ∃ x : K, c = pinnedX .G2 K g2v x := by
  obtain ⟨-, -, -, -, hset, -⟩ := even_G2_highest_short_root_centralizer K
  have hv : Commute c (pinnedX .G2 K g2v 1) := by
    have h := hbc 0 0
    rwa [← pinnedX_v_eq_g2N] at h
  have hcS : c ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} :
      Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) :=
    mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hv.eq⟩
  rw [hset] at hcS
  obtain ⟨q, hq, l, hl, rfl⟩ := hcS
  have hlbc : ∀ y z : K, Commute l (g2N 0 0 0 0 y z) := by
    intro y z
    have h1 : Commute (q * l) (g2N 0 0 0 0 y z) := by
      have h2 := hv.inv_right.mul_right (hbc y z)
      rwa [g2N_v_split, inv_mul_cancel_left] at h2
    have hq' : Commute q (g2N 0 0 0 0 y z) :=
      commute_of_mem_g2ShortRadical hq (g2N_mem_g2ShortRadical 0 y z)
    have h3 := hq'.inv_left.mul_left h1
    rwa [inv_mul_cancel_left] at h3
  have hl1 : l = 1 := by
    have hspec := shAction_spec ⟨l, hl⟩
    have hid : shAction ⟨l, hl⟩ = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      have h1 := hspec.2.2 y
      rw [(hlbc (y 0) (y 1)).eq, mul_inv_cancel_right] at h1
      obtain ⟨-, -, -, -, h0, h1'⟩ := g2N_injective h1
      funext i
      fin_cases i
      · exact h0.symm
      · exact h1'.symm
    have h1 : shActionHom ⟨l, hl⟩ = 1 := Units.ext hid
    exact congrArg Subtype.val ((injective_iff_map_eq_one _).1 shActionHom_injective _ h1)
  subst hl1
  simp only [mul_one] at ha hna ⊢
  obtain ⟨D, E, F, rfl⟩ := hq
  have hE : E = 0 := by
    have hw : Commute (g2N 0 0 0 D E F) (g2N 0 0 0 1 0 1) :=
      commute_of_mem_g2ShortRadical (g2N_mem_g2ShortRadical _ _ _) (g2N_mem_g2ShortRadical _ _ _)
    have h1 := ha.mul_right hw.inv_right
    rw [mul_inv_cancel_right] at h1
    have h2 : pinnedX .G2 K g2a 1 * g2N 0 0 0 D E F * pinnedX .G2 K g2a 1 = g2N 0 0 0 D E F := by
      rw [← h1.eq, mul_assoc, pinnedX_mul_self, mul_one]
    rw [conj_a] at h2
    obtain ⟨-, -, -, -, -, hF⟩ := g2N_injective h2
    linear_combination hF
  subst hE
  have hF : F = 0 := by
    have hw : Commute (g2N 0 0 0 D 0 F) (g2N 0 0 0 1 1 0) :=
      commute_of_mem_g2ShortRadical (g2N_mem_g2ShortRadical _ _ _) (g2N_mem_g2ShortRadical _ _ _)
    have h1 := hna.mul_right hw.inv_right
    rw [mul_inv_cancel_right] at h1
    obtain ⟨hv', -, hT⟩ := actsOnShort_pinnedX_na (K := K) 1
    have h2 : pinnedX .G2 K g2na 1 * g2N 0 0 0 0 0 F * (pinnedX .G2 K g2na 1)⁻¹ =
        g2N 0 0 0 0 F F := by
      have h := hT ![0, F]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
      rw [h]
      refine g2N_eq_g2N rfl rfl rfl rfl ?_ ?_ <;> simp [shSwap, shMa]
    have h3 : pinnedX .G2 K g2na 1 * g2N 0 0 0 D 0 F * (pinnedX .G2 K g2na 1)⁻¹ =
        g2N 0 0 0 D 0 F := by
      rw [← h1.eq, mul_inv_cancel_right]
    rw [g2N_v_split,
      show pinnedX .G2 K g2na 1 * (pinnedX .G2 K g2v D * g2N 0 0 0 0 0 F) *
          (pinnedX .G2 K g2na 1)⁻¹ =
        (pinnedX .G2 K g2na 1 * pinnedX .G2 K g2v D * (pinnedX .G2 K g2na 1)⁻¹) *
          (pinnedX .G2 K g2na 1 * g2N 0 0 0 0 0 F * (pinnedX .G2 K g2na 1)⁻¹) by group,
      (hv' D).eq, mul_inv_cancel_right, h2] at h3
    obtain ⟨-, -, -, -, hE', -⟩ := g2N_injective (mul_left_cancel h3)
    exact hE'
  subst hF
  exact ⟨D, by rw [← pinnedX_v_eq_g2N]⟩

end C

section Coord

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] in
theorem commute_of_mem_of_sq_eq_one
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {d b : G} (hd : d ∈ A) (hb : b ∈ A) (hb2 : b ^ 2 = 1)
    (hc : d * b * d⁻¹ * b⁻¹ ∈ centralizer (A : Set G)) : d * b = b * d := by
  set c := d * b * d⁻¹ * b⁻¹ with hcdef
  have hcA : c ∈ A := mul_mem (mul_mem (mul_mem hd hb) (inv_mem hd)) (inv_mem hb)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb2])
  have hcb : Commute c b := (mem_centralizer_iff.1 hc b hb).symm
  have h1 : d * b * d⁻¹ = c * b := by
    rw [hcdef, hbi, mul_assoc _ b b, ← sq, hb2, mul_one]
  have hsq : c ^ 2 = 1 := by
    have h2 : (c * b) ^ 2 = 1 := by rw [← h1, conj_pow, hb2, mul_one, mul_inv_cancel]
    rwa [hcb.mul_pow, hb2, mul_one] at h2
  have h3 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZ (mem_inf.2 ⟨hcA, hc⟩)) (k := 1)
    (by rw [pow_one]; exact hsq)
  calc d * b = c * (b * d) := by rw [hcdef]; group
    _ = b * d := by rw [h3, one_mul]

omit [Finite G] [Finite K] [CharP K 2] in
theorem commute_of_psi_commute
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {d b : G} (hd : d ∈ A) (hb : b ∈ A) (hb2 : b ^ 2 = 1)
    (h : ψ ⟨d, le_normalizer hd⟩ * ψ ⟨b, le_normalizer hb⟩ =
      ψ ⟨b, le_normalizer hb⟩ * ψ ⟨d, le_normalizer hd⟩) : d * b = b * d := by
  have hN : d * b * d⁻¹ * b⁻¹ ∈ normalizer (A : Set G) :=
    le_normalizer (mul_mem (mul_mem (mul_mem hd hb) (inv_mem hd)) (inv_mem hb))
  refine commute_of_mem_of_sq_eq_one hZ hd hb hb2 ((hψ.eq_one_iff ⟨_, hN⟩).1 ?_)
  have e : (⟨d * b * d⁻¹ * b⁻¹, hN⟩ : normalizer (A : Set G)) =
      ⟨d, le_normalizer hd⟩ * ⟨b, le_normalizer hb⟩ * ⟨d, le_normalizer hd⟩⁻¹ *
        ⟨b, le_normalizer hb⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

omit [Finite G] [Finite K] [CharP K 2] in
theorem exists_coord_v
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {b : G} (hb : b ∈ twoLift ψ (rootSubgroup .G2 K g2v)) :
    ∃ (s : K) (hbA : b ∈ A), ψ ⟨b, le_normalizer hbA⟩ = MulAut.conj (g2Xc g2v s) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  obtain ⟨hbA, -, x, hx, hxU⟩ := (mem_twoLift hψ hZ (rootSubgroup_comm g2v)).1 hb
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hxU
  exact ⟨s, hbA, by rw [hx]; congr 1; exact Subtype.ext hs.symm⟩

omit [Finite G] in
theorem exists_scalar_v
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {a : G} (ha : a ∈ A)
    (haZ : a ∈ normalizer (twoLift ψ (rootSubgroup .G2 K g2v) : Set G)) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ s, ψ ⟨a, le_normalizer ha⟩ (g2Xc g2v s) = g2Xc g2v (μ * s) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  obtain ⟨d, hd⟩ := hψ.map_mem a ha
  obtain ⟨z₁, hz₁, hz₁A, hz₁ψ⟩ := exists_mem_twoLift hψ hZ (rootSubgroup_sq g2v) (g2Xc g2v 1)
    (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have hz₂ : a * z₁ * a⁻¹ ∈ twoLift ψ (rootSubgroup .G2 K g2v) :=
    (mem_normalizer_iff.1 haZ z₁).1 hz₁
  obtain ⟨μ, hz₂A, hz₂ψ⟩ := exists_coord_v hZA hψ hz₂
  have h1 := psi_conj_eq_conj (le_normalizer ha) hz₁A hz₁ψ hz₂A
  rw [hz₂ψ] at h1
  have h2 : ψ ⟨a, le_normalizer ha⟩ (g2Xc g2v 1) = g2Xc g2v μ := (hinj h1).symm
  rw [← hd, MulAut.conj_apply] at h2
  have h3 : (d : ModGL .G2 K) * pinnedX .G2 K g2v 1 * (d : ModGL .G2 K)⁻¹ =
      pinnedX .G2 K g2v μ := congrArg Subtype.val h2
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at h3
    have h4 : pinnedX .G2 K g2v 1 = pinnedX .G2 K g2v 0 := by
      rw [pinnedX_zero]
      calc pinnedX .G2 K g2v 1 =
          (d : ModGL .G2 K)⁻¹ * ((d : ModGL .G2 K) * pinnedX .G2 K g2v 1 *
            (d : ModGL .G2 K)⁻¹) * d := by group
        _ = 1 := by rw [h3]; group
    exact one_ne_zero (pinnedX_injective .G2 K g2v h4)
  refine ⟨μ, hμ, fun s => ?_⟩
  rw [← hd, MulAut.conj_apply]
  exact Subtype.ext (g2_conj_v_eq d.2 hμ h3 s)

omit [Finite G] [Finite K] [CharP K 2] in
theorem mem_centralizer_of_fix_v
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {a : G} (ha : a ∈ A) (hfix : ∀ s, ψ ⟨a, le_normalizer ha⟩ (g2Xc g2v s) = g2Xc g2v s) :
    a ∈ centralizer (twoLift ψ (rootSubgroup .G2 K g2v) : Set G) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  rw [mem_centralizer_iff]
  intro z hz
  obtain ⟨s, hzA, hzψ⟩ := exists_coord_v hZA hψ hz
  have hzA' : a * z * a⁻¹ ∈ A := mul_mem (mul_mem ha hzA) (inv_mem ha)
  have h1 := psi_conj_eq_conj (le_normalizer ha) hzA hzψ hzA'
  rw [hfix] at h1
  have hz2 := sq_eq_one_of_mem_twoLift hψ hZ (rootSubgroup_comm g2v) hz
  have h2 : a * z * a⁻¹ = z := eq_of_sq_eq_one hψ hZ hzA' hzA
    (by rw [conj_pow, hz2, mul_one, mul_inv_cancel]) hz2 (h1.trans hzψ.symm)
  calc z * a = a * z * a⁻¹ * a := by rw [h2]
    _ = a * z := by group

omit [Finite G] [Finite K] [CharP K 2] in
theorem torus_mem_normalizer
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {a : G} (ha : a ∈ A) {t : Kˣ}
    (haψ : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj (g2TorusHomR K t)) :
    a ∈ normalizer (twoLift ψ (rootSubgroup .G2 K g2v) : Set G) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  refine mem_normalizer_twoLift hψ hZ (rootSubgroup_comm g2v) (le_normalizer ha) fun x => ?_
  rw [haψ]
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx
    have hx' : x = g2Xc g2v s := Subtype.ext hs.symm
    rw [hx', g2TorusHomR_conj]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · intro hx
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx
    have h1 : MulAut.conj (g2TorusHomR K t⁻¹) (MulAut.conj (g2TorusHomR K t) x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        MulAut.one_apply]
    have hx' : MulAut.conj (g2TorusHomR K t) x = g2Xc g2v s := Subtype.ext hs.symm
    rw [← h1, hx', g2TorusHomR_conj]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩

omit [Finite G] [CharP K 2] in
theorem commute_conj_of_forall
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {p x : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1) {y₁ : ↥(adjointGroup .G2 K)}
    (hpψ : ψ ⟨p, le_normalizer hpA⟩ = MulAut.conj y₁) (hxA : x ∈ A)
    (hx : ∀ b ∈ A, Commute (b * p * b⁻¹) p → x ∈ centralizer ({b * p * b⁻¹} : Set G))
    {c : ↥(adjointGroup .G2 K)} (hc : ψ ⟨x, le_normalizer hxA⟩ = MulAut.conj c)
    (d : ↥(adjointGroup .G2 K)) (hd : Commute (d * y₁ * d⁻¹) y₁) :
    Commute c (d * y₁ * d⁻¹) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  obtain ⟨b, hb, hbψ⟩ := hψ.exists_eq (MulAut.conj d) ⟨d, rfl⟩
  have hbp : b * p * b⁻¹ ∈ A := mul_mem (mul_mem hb hpA) (inv_mem hb)
  have hψbp : ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ = MulAut.conj (d * y₁ * d⁻¹) := by
    rw [psi_conj_eq_conj (le_normalizer hb) hpA hpψ hbp, hbψ, MulAut.conj_apply]
  have hbp2 : (b * p * b⁻¹) ^ 2 = 1 := by rw [conj_pow, hp2, mul_one, mul_inv_cancel]
  have hcomm : Commute (b * p * b⁻¹) p := by
    refine commute_of_psi_commute hZ hψ hbp hpA hp2 ?_
    rw [hψbp, hpψ, ← map_mul, ← map_mul, hd.eq]
  have h1 := mem_centralizer_iff.1 (hx b hb hcomm) (b * p * b⁻¹) (Set.mem_singleton _)
  have h2 : ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ * ψ ⟨x, le_normalizer hxA⟩ =
      ψ ⟨x, le_normalizer hxA⟩ * ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext h1)
  rw [hψbp, hc, ← map_mul, ← map_mul] at h2
  exact (hinj h2).symm

end Coord

section Main

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

theorem jData_g2v
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTp : G2Pinned ψ T g2v) (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    ∃ p y : G, JData A R T p (twoLift ψ (rootSubgroup .G2 K g2v)) y := by
  classical
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hUc := rootSubgroup_comm (K := K) g2v
  have hU2 := rootSubgroup_sq (K := K) g2v
  set Z := twoLift ψ (rootSubgroup .G2 K g2v) with hZdef
  obtain ⟨t₀, ht₀, ht₀1, ht₀N, y₁, hy₁, hψt₀⟩ := hTp
  obtain ⟨p, hpA, hp⟩ := hc.exists_aPart h32 h4 h34 ht₀
  have hpart : ∀ t ∈ T, ∀ (htN : t ∈ normalizer (A : Set G)) (p' : G) (hp'A : p' ∈ A),
      t⁻¹ * p' ∈ R → ψ ⟨p', le_normalizer hp'A⟩ = ψ ⟨t, htN⟩ ∧ p' ^ 2 = 1 := by
    intro t ht htN p' hp'A hp'
    refine ⟨?_, ?_⟩
    · have h1 : ψ ⟨t⁻¹ * p', mul_mem (inv_mem htN) (le_normalizer hp'A)⟩ = 1 :=
        (hψ.eq_one_iff _).2 (hc.sylowR.le hp')
      rw [psi_mul (inv_mem htN) (le_normalizer hp'A), psi_inv htN, inv_mul_eq_one] at h1
      exact h1.symm
    · have htr : Commute t (t⁻¹ * p') :=
        (mem_centralizer_iff.1 (hc.le_centralizer ht) (t⁻¹ * p') hp').symm
      have e : p' = t * (t⁻¹ * p') := by group
      rw [e, htr.mul_pow, (hc.elemT h32).2 t ht, (hc.elemR h32).2 _ hp', one_mul]
  obtain ⟨hpψ', hp2⟩ := hpart t₀ ht₀ ht₀N p hpA hp
  have hpψ : ψ ⟨p, le_normalizer hpA⟩ = MulAut.conj y₁ := hpψ'.trans hψt₀
  have hy₁U : (y₁ : ModGL .G2 K) ∈ rootSubgroup .G2 K g2v := by
    rw [hy₁]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have hpZ : p ∈ Z := mem_twoLift_of hpA hp2 hpψ hy₁U
  have hp1 : p ≠ 1 := by
    rintro rfl
    apply ht₀1
    have h1 : t₀⁻¹ ∈ R := by simpa using hp
    have h2 : t₀ ∈ R ⊓ T := mem_inf.2 ⟨by simpa using inv_mem h1, ht₀⟩
    rwa [hc.inf_eq_bot, mem_bot] at h2
  have hcent1 : ∀ d : ↥(adjointGroup .G2 K), d * y₁ = y₁ * d →
      ∀ s, MulAut.conj d (g2Xc g2v s) = g2Xc g2v s := by
    intro d hd s
    have hdS : (d : ModGL .G2 K) ∈ g2ShortCent K := by
      refine mem_inf.2 ⟨d.2, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := congrArg Subtype.val hd
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hy₁] at h1
      exact h1
    refine Subtype.ext ?_
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    change (d : ModGL .G2 K) * pinnedX .G2 K g2v s * (d : ModGL .G2 K)⁻¹ = pinnedX .G2 K g2v s
    rw [g2_commute_v_of_mem hdS s, mul_inv_cancel_right]
  have hZcoord : ∀ j ∈ Z, j ≠ 1 → ∃ (s : K) (hjA : j ∈ A), s ≠ 0 ∧
      ψ ⟨j, le_normalizer hjA⟩ = MulAut.conj (g2Xc g2v s) := by
    intro j hj hj1
    obtain ⟨s, hjA, hjψ⟩ := exists_coord_v hZA hψ hj
    refine ⟨s, hjA, fun hs => hj1 ?_, hjψ⟩
    refine eq_of_mem_twoLift hψ hZ hUc hj (one_mem _) ?_
    rw [hjψ, hs]
    have h0 : g2Xc g2v (0 : K) = 1 := Subtype.ext (pinnedX_zero .G2 K g2v)
    rw [h0, map_one]
    exact (map_one ψ).symm
  obtain ⟨t₁, ht₁⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨y₀, hy₀, hy₀ψ⟩ := hψ.exists_eq (MulAut.conj (g2TorusHomR K t₁)) ⟨_, rfl⟩
  have hy₀N := le_normalizer hy₀
  have hy₀Z : y₀ ∈ normalizer (Z : Set G) := torus_mem_normalizer hZA hψ hy₀ hy₀ψ
  have hpow : ∀ μ : K, μ ≠ 0 → ∃ k : ℕ, ((t₁ ^ k : Kˣ) : K) = μ := by
    intro μ hμ
    have h1 := ht₁ (Units.mk0 μ hμ)
    rw [← mem_powers_iff_mem_zpowers] at h1
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, by rw [show t₁ ^ k = Units.mk0 μ hμ from hk, Units.val_mk0]⟩
  have hfixk : ∀ (a : G) (ha : a ∈ A) (k : ℕ),
      (∀ s, ψ ⟨a, le_normalizer ha⟩ (g2Xc g2v s) = g2Xc g2v (((t₁ ^ k : Kˣ) : K) * s)) →
        (y₀ ^ k)⁻¹ * a ∈ centralizer (Z : Set G) := by
    intro a ha k hak
    have hA : (y₀ ^ k)⁻¹ * a ∈ A := mul_mem (inv_mem (pow_mem hy₀ k)) ha
    refine mem_centralizer_of_fix_v hZA hψ hA fun s => ?_
    have e : (⟨(y₀ ^ k)⁻¹ * a, le_normalizer hA⟩ : normalizer (A : Set G)) =
        (⟨y₀, hy₀N⟩ ^ k)⁻¹ * ⟨a, le_normalizer ha⟩ := rfl
    rw [e, map_mul, map_inv, map_pow, hy₀ψ, MulAut.mul_apply, hak, ← map_pow, ← map_pow,
      ← map_inv, ← map_inv, g2TorusHomR_conj, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul]
  refine ⟨p, y₀,
    { le := twoLift_le
      mem := hpZ
      ne_one := hp1
      aPart_mem := ⟨t₀, ht₀, hp⟩
      aPart_le := ?_
      le_centralizer := ?_
      le_normalizer := ?_
      trans := ?_
      free := ?_
      y_mem := mem_inf.2 ⟨hy₀, hy₀Z⟩
      odd := ?_
      cyclic := ?_
      sylow := ?_ }⟩
  · intro t ht p' hp'A hp'
    have htN := hc.le_normalizer ht
    obtain ⟨hp'ψ, hp'2⟩ := hpart t ht htN p' hp'A hp'
    obtain ⟨x, hx⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht htN
    exact mem_twoLift_of hp'A hp'2 (hp'ψ.trans hx) (hTv t ht htN x hx)
  · intro b hb hcomm z hz
    obtain ⟨d, hd⟩ := hψ.map_mem b hb
    have hbp : b * p * b⁻¹ ∈ A := mul_mem (mul_mem hb hpA) (inv_mem hb)
    have hψbp : ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ = MulAut.conj (d * y₁ * d⁻¹) := by
      rw [psi_conj_eq_conj (le_normalizer hb) hpA hpψ hbp, ← hd, MulAut.conj_apply]
    have hw : d * y₁ * d⁻¹ * y₁ = y₁ * (d * y₁ * d⁻¹) := by
      have h1 : ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ * ψ ⟨p, le_normalizer hpA⟩ =
          ψ ⟨p, le_normalizer hpA⟩ * ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext hcomm.eq)
      rw [hψbp, hpψ, ← map_mul, ← map_mul] at h1
      exact hinj h1
    obtain ⟨s, hzA, hzψ⟩ := exists_coord_v hZA hψ hz
    have hz2 := sq_eq_one_of_mem_twoLift hψ hZ hUc hz
    rw [mem_centralizer_iff]
    intro w hw'
    rw [Set.mem_singleton_iff] at hw'
    subst hw'
    have hbp2 : (b * p * b⁻¹) ^ 2 = 1 := by rw [conj_pow, hp2, mul_one, mul_inv_cancel]
    refine commute_of_psi_commute hZ hψ hbp hzA hz2 ?_
    rw [hψbp, hzψ, ← map_mul, ← map_mul]
    congr 1
    have h1 := hcent1 (d * y₁ * d⁻¹) hw s
    rw [MulAut.conj_apply] at h1
    calc d * y₁ * d⁻¹ * g2Xc g2v s = d * y₁ * d⁻¹ * g2Xc g2v s * (d * y₁ * d⁻¹)⁻¹ *
          (d * y₁ * d⁻¹) := by group
      _ = g2Xc g2v s * (d * y₁ * d⁻¹) := by rw [h1]
  · intro a ha
    obtain ⟨haA, hap⟩ := mem_inf.1 ha
    obtain ⟨d, hd⟩ := hψ.map_mem a haA
    have hdy : d * y₁ = y₁ * d := by
      have h1 : ψ ⟨a, le_normalizer haA⟩ * ψ ⟨p, le_normalizer hpA⟩ =
          ψ ⟨p, le_normalizer hpA⟩ * ψ ⟨a, le_normalizer haA⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.1 hap))
      rw [← hd, hpψ, ← map_mul, ← map_mul] at h1
      exact hinj h1
    refine centralizer_le_normalizer _ (mem_centralizer_of_fix_v hZA hψ haA fun s => ?_)
    rw [← hd]
    exact hcent1 d hdy s
  · intro j hj hj1 j' hj' hj'1
    obtain ⟨s, hjA, hs, hjψ⟩ := hZcoord j hj hj1
    obtain ⟨s', hj'A, hs', hj'ψ⟩ := hZcoord j' hj' hj'1
    set u : Kˣ := Units.mk0 s' hs' * (Units.mk0 s hs)⁻¹ with hu
    obtain ⟨a, ha, haψ⟩ := hψ.exists_eq (MulAut.conj (g2TorusHomR K u)) ⟨_, rfl⟩
    have haZ := torus_mem_normalizer hZA hψ ha haψ
    refine ⟨a, mem_inf.2 ⟨ha, haZ⟩, ?_⟩
    have hmem : a * j * a⁻¹ ∈ Z := (mem_normalizer_iff.1 haZ j).1 hj
    refine eq_of_mem_twoLift hψ hZ hUc hmem hj' ?_
    have e : (u : K) * s = s' := by
      rw [hu, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    rw [psi_conj_eq_conj (le_normalizer ha) hjA hjψ (twoLift_le hmem), haψ, g2TorusHomR_conj,
      hj'ψ, e]
  · intro a ha j hj hj1 haj
    obtain ⟨haA, haZ⟩ := mem_inf.1 ha
    obtain ⟨μ, hμ, hμs⟩ := exists_scalar_v hZA hψ haA haZ
    obtain ⟨s, hjA, hs, hjψ⟩ := hZcoord j hj hj1
    have h1 := psi_conj_eq_conj (le_normalizer haA) hjA hjψ (by rw [haj]; exact hjA)
    have h2 : ψ ⟨a * j * a⁻¹, le_normalizer (by rw [haj]; exact hjA)⟩ =
        ψ ⟨j, le_normalizer hjA⟩ := by
      congr 1
      exact Subtype.ext haj
    rw [h1, hjψ, hμs] at h2
    have h3 : μ * s = s := pinnedX_injective .G2 K g2v (congrArg Subtype.val (hinj h2))
    have hμ1 : μ = 1 := by
      have h4 : (μ - 1) * s = 0 := by rw [sub_mul, h3, one_mul, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right hs)
    refine mem_centralizer_of_fix_v hZA hψ haA fun s' => ?_
    rw [hμs, hμ1, one_mul]
  · have hq : Odd (Nat.card K - 1) := by
      rw [hK]
      exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).2 even_two) odd_one
    have ht₁q : t₁ ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    have hy : y₀ ^ (Nat.card K - 1) ∈ A ⊓ centralizer (A : Set G) := by
      refine mem_inf.2 ⟨pow_mem hy₀ _, (hψ.eq_one_iff ⟨_, pow_mem hy₀N _⟩).1 ?_⟩
      have e : (⟨y₀ ^ (Nat.card K - 1), pow_mem hy₀N _⟩ : normalizer (A : Set G)) =
          ⟨y₀, hy₀N⟩ ^ (Nat.card K - 1) := rfl
      rw [e, map_pow, hy₀ψ, ← map_pow, ← map_pow, ht₁q, map_one, map_one]
    have h1 : (y₀ ^ (Nat.card K - 1)) ^ Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hy)
    rw [← pow_mul] at h1
    exact (Nat.odd_mul.2 ⟨hq, hZ⟩).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · intro a ha
    obtain ⟨haA, haZ⟩ := mem_inf.1 ha
    obtain ⟨μ, hμ, hμs⟩ := exists_scalar_v hZA hψ haA haZ
    obtain ⟨k, hk⟩ := hpow μ hμ
    exact ⟨k, hfixk a haA k fun s => by rw [hμs, hk]⟩
  · intro x hx hxc hx2
    obtain ⟨hxA, -⟩ := mem_inf.1 hx
    obtain ⟨c, hc'⟩ := hψ.map_mem x hxA
    have key : ∀ (e : ModGL .G2 K) (he : e ∈ adjointGroup .G2 K),
        Commute (e * pinnedX .G2 K g2v 1 * e⁻¹) (pinnedX .G2 K g2v 1) →
        Commute (c : ModGL .G2 K) (e * pinnedX .G2 K g2v 1 * e⁻¹) := by
      intro e he hcom
      have hd : (⟨e, he⟩ : ↥(adjointGroup .G2 K)) * y₁ * (⟨e, he⟩ : ↥(adjointGroup .G2 K))⁻¹ *
          y₁ = y₁ * ((⟨e, he⟩ : ↥(adjointGroup .G2 K)) * y₁ *
            (⟨e, he⟩ : ↥(adjointGroup .G2 K))⁻¹) := by
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy₁]
        exact hcom.eq
      have h1 := commute_conj_of_forall hZA hψ hpA hp2 hpψ hxA hxc hc'.symm ⟨e, he⟩ hd
      have h2 := congrArg Subtype.val h1.eq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy₁] at h2
      exact h2
    have hv1 : pinnedX .G2 K g2v 1 ∈ g2ShortRadical K := pinnedX_v_mem_g2ShortRadical 1
    have hbc : ∀ y z : K, Commute (c : ModGL .G2 K) (g2N 0 0 0 1 y z) := by
      intro y z
      have h := key (pinnedX .G2 K g2r y * pinnedX .G2 K g2u z)
        (mul_mem (pinnedX_mem_adjointGroup g2r y) (pinnedX_mem_adjointGroup g2u z)) (by
          rw [conj_ru_v_one]
          exact commute_of_mem_g2ShortRadical (g2N_mem_g2ShortRadical _ _ _) hv1)
      rwa [conj_ru_v_one] at h
    have ha' : Commute (c : ModGL .G2 K) (pinnedX .G2 K g2a 1 * g2N 0 0 0 1 0 1) := by
      have h := key (pinnedX .G2 K g2nr 1) (pinnedX_mem_adjointGroup g2nr 1) (by
          rw [conj_nr_v_one]
          exact (commute_a_v 1 1).mul_left
            (commute_of_mem_g2ShortRadical (g2N_mem_g2ShortRadical _ _ _) hv1))
      rwa [conj_nr_v_one] at h
    have hna' : Commute (c : ModGL .G2 K) (pinnedX .G2 K g2na 1 * g2N 0 0 0 1 1 0) := by
      have h := key (weylElt .G2 K g2ia 1 * pinnedX .G2 K g2nr 1)
        (mul_mem (weylElt_mem_adjointGroup g2ia 1) (pinnedX_mem_adjointGroup g2nr 1)) (by
          rw [conj_wnr_v_one]
          exact ((actsOnShort_pinnedX_na (K := K) 1).1 1).mul_left
            (commute_of_mem_g2ShortRadical (g2N_mem_g2ShortRadical _ _ _) hv1))
      rwa [conj_wnr_v_one] at h
    obtain ⟨x₀, hx₀⟩ := eq_pinnedX_v_of_commute c.2 hbc ha' hna'
    have hx2' : x ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := hx2
      have hsq : x ^ 2 ∈ A ⊓ centralizer (A : Set G) := by
        refine mem_inf.2 ⟨pow_mem hxA 2, (hψ.eq_one_iff ⟨_, pow_mem (le_normalizer hxA) 2⟩).1 ?_⟩
        have e : (⟨x ^ 2, pow_mem (le_normalizer hxA) 2⟩ : normalizer (A : Set G)) =
            ⟨x, le_normalizer hxA⟩ ^ 2 := rfl
        rw [e, map_pow, ← hc', ← map_pow]
        have hc2 : c ^ 2 = 1 := by
          refine Subtype.ext ?_
          rw [Subgroup.coe_pow, hx₀, sq, pinnedX_mul_self]
          rfl
        rw [hc2, map_one]
      refine RankTwoL3Even.eq_one_of_odd_of_pow_two (RankTwoL3Even.odd_orderOf_of_mem hZ hsq)
        (k := k) ?_
      rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
    refine mem_twoLift_of hxA hx2' hc'.symm ?_
    rw [hx₀]
    exact mem_rootSubgroup.2 ⟨x₀, rfl⟩

end Main

section Transport

variable {G : Type} [Group G]

theorem _root_.CFSG.ComponentClassification.RankTwoClassical.JData.of_aParts
    {A R T T₁ J : Subgroup G} {p y : G} (hJ : JData A R T p J y)
    (h1 : ∃ t ∈ T₁, t⁻¹ * p ∈ R) (h2 : ∀ t ∈ T₁, ∀ p' ∈ A, t⁻¹ * p' ∈ R → p' ∈ J) :
    JData A R T₁ p J y :=
  { hJ with aPart_mem := h1, aPart_le := h2 }

theorem _root_.CFSG.ComponentClassification.RankTwoClassical.JData.map_mulEquiv
    {A R T J : Subgroup G} {p y : G} (hJ : JData A R T p J y)
    (φ : G ≃* G) (hA : ∀ a, φ a ∈ A ↔ a ∈ A) (hR : ∀ r, φ r ∈ R ↔ r ∈ R) :
    JData A R (T.map φ.toMonoidHom) (φ p) (J.map φ.toMonoidHom) (φ y) := by
  have hmem : ∀ (Q : Subgroup G) (z : G), z ∈ Q.map φ.toMonoidHom ↔ φ.symm z ∈ Q := fun Q z =>
    mem_map_equiv
  have hA' : ∀ a, φ.symm a ∈ A ↔ a ∈ A := fun a => by
    rw [← hA, MulEquiv.apply_symm_apply]
  have hN : ∀ (Q : Subgroup G) (a : G),
      a ∈ normalizer (Q.map φ.toMonoidHom : Set G) ↔ φ.symm a ∈ normalizer (Q : Set G) := by
    intro Q a
    simp only [mem_normalizer_iff, hmem, map_mul, map_inv]
    constructor
    · intro h z
      have := h (φ z)
      simpa using this
    · intro h z
      exact h (φ.symm z)
  have hC : ∀ (Q : Subgroup G) (a : G),
      a ∈ centralizer (Q.map φ.toMonoidHom : Set G) ↔ φ.symm a ∈ centralizer (Q : Set G) := by
    intro Q a
    simp only [mem_centralizer_iff, SetLike.mem_coe, hmem]
    constructor
    · intro h z hz
      have := congrArg φ.symm (h (φ z) (by simpa using hz))
      simpa using this
    · intro h z hz
      have := congrArg φ (h (φ.symm z) hz)
      simpa using this
  have hCs : ∀ (u a : G),
      a ∈ centralizer ({φ u} : Set G) ↔ φ.symm a ∈ centralizer ({u} : Set G) := by
    intro u a
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg φ.symm h
      simpa using this
    · intro h
      have := congrArg φ h
      simpa using this
  have hconj : ∀ b : G, b * φ p * b⁻¹ = φ (φ.symm b * p * (φ.symm b)⁻¹) := fun b => by
    simp [map_mul, map_inv]
  refine
    { le := fun z hz => (hA' z).1 (hJ.le ((hmem J z).1 hz))
      mem := (hmem J _).2 (by simpa using hJ.mem)
      ne_one := fun h => hJ.ne_one (φ.injective (h.trans (map_one φ).symm))
      aPart_mem := ?_
      aPart_le := ?_
      le_centralizer := ?_
      le_normalizer := ?_
      trans := ?_
      free := ?_
      y_mem := ?_
      odd := ?_
      cyclic := ?_
      sylow := ?_ }
  · obtain ⟨t, ht, htp⟩ := hJ.aPart_mem
    refine ⟨φ t, (hmem T _).2 (by simpa using ht), ?_⟩
    rw [← map_inv, ← map_mul]
    exact (hR _).2 htp
  · intro t ht p' hp'A hp'
    rw [hmem] at ht ⊢
    refine hJ.aPart_le _ ht _ ((hA' p').2 hp'A) ((hR _).1 ?_)
    simpa [map_mul, map_inv] using hp'
  · intro b hb hcomm z hz
    rw [hconj b] at hcomm ⊢
    rw [hCs]
    have hb' : φ.symm b ∈ A := (hA' b).2 hb
    have hcomm' : Commute (φ.symm b * p * (φ.symm b)⁻¹) p := by
      have := hcomm.map φ.symm.toMonoidHom
      simpa using this
    exact hJ.le_centralizer _ hb' hcomm' ((hmem J z).1 hz)
  · intro a ha
    obtain ⟨haA, hap⟩ := mem_inf.1 ha
    rw [hN]
    refine hJ.le_normalizer (mem_inf.2 ⟨(hA' a).2 haA, ?_⟩)
    have := (hCs p a).1 hap
    exact this
  · intro j hj hj1 j' hj' hj'1
    rw [hmem] at hj hj'
    obtain ⟨a, ha, haj⟩ := hJ.trans _ hj (fun h => hj1 (by simpa using congrArg φ h)) _ hj'
      (fun h => hj'1 (by simpa using congrArg φ h))
    obtain ⟨haA, haJ⟩ := mem_inf.1 ha
    refine ⟨φ a, mem_inf.2 ⟨(hA a).2 haA, (hN J _).2 (by simpa using haJ)⟩, ?_⟩
    have := congrArg φ haj
    simpa [map_mul, map_inv] using this
  · intro a ha j hj hj1 haj
    obtain ⟨haA, haJ⟩ := mem_inf.1 ha
    rw [hmem] at hj
    rw [hN] at haJ
    rw [hC]
    refine hJ.free _ (mem_inf.2 ⟨(hA' a).2 haA, haJ⟩) _ hj
      (fun h => hj1 (by simpa using congrArg φ h)) ?_
    have := congrArg φ.symm haj
    simpa [map_mul, map_inv] using this
  · obtain ⟨hyA, hyJ⟩ := mem_inf.1 hJ.y_mem
    exact mem_inf.2 ⟨(hA y).2 hyA, (hN J _).2 (by simpa using hyJ)⟩
  · rw [MulEquiv.orderOf_eq]
    exact hJ.odd
  · intro a ha
    obtain ⟨haA, haJ⟩ := mem_inf.1 ha
    rw [hN] at haJ
    obtain ⟨k, hk⟩ := hJ.cyclic _ (mem_inf.2 ⟨(hA' a).2 haA, haJ⟩)
    refine ⟨k, (hC J _).2 ?_⟩
    simpa [map_mul, map_inv, map_pow] using hk
  · intro z hz hzc hz2
    obtain ⟨hzA, hzp⟩ := mem_inf.1 hz
    rw [hmem]
    refine hJ.sylow _ (mem_inf.2 ⟨(hA' z).2 hzA, (hCs p z).1 hzp⟩) (fun b hb hcomm => ?_) ?_
    · have hb' : φ b ∈ A := (hA b).2 hb
      have hcomm' : Commute (φ b * φ p * (φ b)⁻¹) (φ p) := by
        have := hcomm.map φ.toMonoidHom
        simpa using this
      have h1 := hzc (φ b) hb' hcomm'
      have h2 : φ b * φ p * (φ b)⁻¹ = φ (b * p * b⁻¹) := by simp [map_mul, map_inv]
      rw [h2, hCs] at h1
      exact h1
    · obtain ⟨k, hk⟩ := hz2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem _root_.CFSG.ComponentClassification.RankTwoClassical.JData.rightConjugate
    {A R T J : Subgroup G} {p y : G} (hJ : JData A R T p J y)
    (hRA : R ≤ centralizer (A : Set G)) {x : G} (hx : x ∈ A) :
    JData A R (rightConjugate T x) (x⁻¹ * p * x) (rightConjugate J x) (x⁻¹ * y * x) := by
  have hA : ∀ a, MulAut.conj x⁻¹ a ∈ A ↔ a ∈ A := fun a => by
    rw [MulAut.conj_apply, inv_inv]
    constructor
    · intro h
      have := mul_mem (mul_mem hx h) (inv_mem hx)
      simpa [mul_assoc] using this
    · intro h
      exact mul_mem (mul_mem (inv_mem hx) h) hx
  have hR : ∀ r, MulAut.conj x⁻¹ r ∈ R ↔ r ∈ R := fun r => by
    rw [MulAut.conj_apply, inv_inv]
    constructor
    · intro h
      have hc : x * (x⁻¹ * r * x) = (x⁻¹ * r * x) * x := (mem_centralizer_iff.1 (hRA h) x hx)
      have e : r = x⁻¹ * r * x := by
        calc r = x * (x⁻¹ * r * x) * x⁻¹ := by group
          _ = (x⁻¹ * r * x) * x * x⁻¹ := by rw [hc]
          _ = x⁻¹ * r * x := by group
      rw [e]
      exact h
    · intro h
      have hc : x * r = r * x := mem_centralizer_iff.1 (hRA h) x hx
      have e : x⁻¹ * r * x = r := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
      rw [e]
      exact h
  have h := hJ.map_mulEquiv (MulAut.conj x⁻¹) hA hR
  simp only [MulAut.conj_apply, inv_inv] at h
  exact h

end Transport

section General

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] [Finite K] [CharP K 2] in
theorem actsIn_rightConjugate_of_conj
    {U : Subgroup (ModGL .G2 K)} (hT : ActsIn ψ T U) {a : G} (ha : a ∈ A)
    {h : ↥(adjointGroup .G2 K)} (haψ : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj h)
    (hU : ∀ x : ↥(adjointGroup .G2 K), (x : ModGL .G2 K) ∈ U →
      ((h⁻¹ * x * h : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈ U) :
    ActsIn ψ (rightConjugate T a) U := by
  intro u hu huN y hy
  rw [mem_rightConjugate_iff] at hu
  have haN := le_normalizer ha
  have htN : a * u * a⁻¹ ∈ normalizer (A : Set G) := mul_mem (mul_mem haN huN) (inv_mem haN)
  have e : (⟨a * u * a⁻¹, htN⟩ : normalizer (A : Set G)) =
      ⟨a, haN⟩ * ⟨u, huN⟩ * ⟨a, haN⟩⁻¹ := rfl
  have h1 : ψ ⟨a * u * a⁻¹, htN⟩ = MulAut.conj (h * y * h⁻¹) := by
    rw [e, map_mul, map_mul, map_inv, haψ, hy, ← map_inv, ← map_mul, ← map_mul]
  have h2 := hT _ hu htN _ h1
  have h3 := hU _ h2
  rwa [show h⁻¹ * (h * y * h⁻¹) * h = y by group] at h3

theorem jData_of_actsIn
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    ∃ p y : G, JData A R T p (twoLift ψ (rootSubgroup .G2 K g2v)) y := by
  classical
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc.T_ne_bot
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have ht₀N := hc.le_normalizer ht₀
  obtain ⟨x, hx⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht₀ ht₀N
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 (hTv t₀ ht₀ ht₀N x hx)
  have hxs : x = g2Xc g2v s := Subtype.ext hs.symm
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply not_mem_centralizer_of_sec3 hc h32 ht₀ ht₀1'
    refine (hψ.eq_one_iff ⟨t₀, ht₀N⟩).1 ?_
    rw [hx, hxs]
    have h0 : g2Xc g2v (0 : K) = 1 := Subtype.ext (pinnedX_zero .G2 K g2v)
    rw [h0, map_one]
  set u : Kˣ := Units.mk0 s hs0 with hu
  obtain ⟨a, ha, haψ⟩ := hψ.exists_eq (MulAut.conj (g2TorusHomR K u)) ⟨_, rfl⟩
  have hconj : ∀ s' : K, ((g2TorusHomR K u)⁻¹ * g2Xc g2v s' * g2TorusHomR K u :
      ↥(adjointGroup .G2 K)) = g2Xc g2v (s⁻¹ * s') := by
    intro s'
    have h1 := g2TorusHomR_conj (K := K) u⁻¹ s'
    rw [MulAut.conj_apply, map_inv, inv_inv] at h1
    rw [h1, Units.val_inv_eq_inv_val, hu, Units.val_mk0]
  have hc' := sec3_conj hc ha
  have hTv' : ActsIn ψ (rightConjugate T a) (rootSubgroup .G2 K g2v) := by
    refine actsIn_rightConjugate_of_conj hTv ha haψ fun y hy => ?_
    obtain ⟨s', hs'⟩ := mem_rootSubgroup.1 hy
    have hy' : y = g2Xc g2v s' := Subtype.ext hs'.symm
    rw [hy', hconj]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hTp' : G2Pinned ψ (rightConjugate T a) g2v := by
    have haN := le_normalizer ha
    have hmem : a⁻¹ * t₀ * a ∈ rightConjugate T a := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ht₀
    have hN : a⁻¹ * t₀ * a ∈ normalizer (A : Set G) :=
      mul_mem (mul_mem (inv_mem haN) ht₀N) haN
    refine ⟨a⁻¹ * t₀ * a, hmem, fun h => ht₀1' ?_, hN, g2Xc g2v 1, rfl, ?_⟩
    · calc t₀ = a * (a⁻¹ * t₀ * a) * a⁻¹ := by group
        _ = 1 := by rw [h]; group
    · have e : (⟨a⁻¹ * t₀ * a, hN⟩ : normalizer (A : Set G)) =
          ⟨a, haN⟩⁻¹ * ⟨t₀, ht₀N⟩ * ⟨a, haN⟩ := rfl
      rw [e, map_mul, map_mul, map_inv, haψ, hx, hxs, ← map_inv, ← map_mul, ← map_mul, hconj,
        inv_mul_cancel₀ hs0]
  obtain ⟨p, y, hJ⟩ := jData_g2v hf hK h4 h32 hc' hZA hψ hTp' hTv'
  have hJ' := hJ.rightConjugate (hc.sylowR.le) (inv_mem ha)
  have hZa : rightConjugate (twoLift ψ (rootSubgroup .G2 K g2v)) a⁻¹ =
      twoLift ψ (rootSubgroup .G2 K g2v) :=
    (rightConjugate_eq_self_iff _ _).2 (inv_mem (torus_mem_normalizer hZA hψ ha haψ))
  rw [RankTwoClassical.rightConjugate_rightConjugate_inv, hZa, inv_inv] at hJ'
  exact ⟨_, _, hJ'⟩

theorem exists_jData_of_nolong
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) (h184s : G2Centr184s)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c)) :
    ∃ (p y : G) (J : Subgroup G), JData A R T p J y ∧ Nat.card J = Nat.card K ∧
      IsElemAbelian 2 J := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨a, ha, hlong | hshort⟩ := g2_exists_pinned h4 h32 h184 h184s hc hOut hK4 hψ
  · exact absurd ⟨_, _, sec3_conj hc ha, hlong.1, hlong.2⟩ hnolong
  obtain ⟨p, y, hJ⟩ := jData_of_actsIn hf hK h4 h32 (sec3_conj hc ha) hZA hψ hshort.2
  have hJ' := hJ.rightConjugate (hc.sylowR.le) (inv_mem ha)
  rw [RankTwoClassical.rightConjugate_rightConjugate_inv] at hJ'
  refine ⟨_, _, _, hJ', ?_, ?_⟩
  · rw [rightConjugate_card, card_twoLift hψ hZ (rootSubgroup_comm g2v) (rootSubgroup_sq g2v) hZC,
      card_rootSubgroup_subgroupOf]
  · exact isElemAbelian_rightConjugate (isElemAbelian_twoLift hψ hZ (rootSubgroup_comm g2v)) _

end General

end CFSG.ComponentClassification.RankTwoExceptional
