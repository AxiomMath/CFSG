module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcLineSplit
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcResCent
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcEleven
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseB

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3 JData)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

section Descent

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

theorem eq_lift2_of_inf_ne_bot (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) {reps : List C}
    (hcover : ClassesCover reps)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z)
    (hact : ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' → ∀ t ∈ T', t ≠ 1 →
      ∀ (htN : t ∈ normalizer (A : Set G)) (x : C), ψ ⟨t, htN⟩ = MulAut.conj x →
        ActsIn ψ T' (zx x))
    {t : G} (ht : t ∈ T) (htA : t ∈ A) (ht1 : t ≠ 1) {x : C}
    (hx : ψ ⟨t, le_normalizer htA⟩ = MulAut.conj x) :
    T = lift2 ψ (zx x) := by
  obtain ⟨p, û, hJd⟩ := exists_jData hZC hψ h4 h32 h34 hc hZA hcover hJ ht ht1
    (le_normalizer htA) hx (hact R T g hc t ht ht1 (le_normalizer htA) x hx)
  rcases main_of_reps hZC hψ h4 h32 h34 hc hZA hcover hJ hact with ⟨h1, -⟩ | ⟨h1, -, -⟩
  · exact h1.trans (hc.inf_sec3V_eq h32 h4 h34 hJd)
  · exfalso
    have hTAg := hc.T_inf_conj hZA
    have htAg : t ∈ rightConjugate A g := by
      have hmem : t ∈ sec3V R T ⊓ A := by
        obtain ⟨xT, hxT, -⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
        exact mem_inf.2 ⟨le_sec3V_of ⟨xT, hxT⟩ (mem_sup_right ht), htA⟩
      rw [h1] at hmem
      exact (mem_inf.1 hmem).2
    have : t ∈ T ⊓ rightConjugate A g := mem_inf.2 ⟨ht, htAg⟩
    rw [hTAg, mem_bot] at this
    exact ht1 this

omit [Finite G] in
theorem exists_splitData_of_lineSplit (hZA : Odd (Nat.card (center A))) {Z : Subgroup C}
    {F : Type} [Field F] [CharP F 2] {ι₁ ι₂ : F → C} {P : C → Prop}
    (hs : LineSplit Z F ι₁ ι₂ P) (hT : T = lift2 ψ Z) :
    ∃ κ₁ κ₂ : F → G, RankTwoClassical.SplitData A T
      (fun s => ∃ (hsA : s ∈ A) (y : C), ψ ⟨s, le_normalizer hsA⟩ = MulAut.conj y ∧ P y)
      (fun s => ∃ (hsA : s ∈ A) (y : C), ψ ⟨s, le_normalizer hsA⟩ = MulAut.conj y ∧ P y)
      F κ₁ κ₂ := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hc₁ : ∀ x y, Commute (ι₁ x) (ι₁ y) := fun x y => by
    rw [Commute, SemiconjBy, ← hs.map_add₁, ← hs.map_add₁, add_comm]
  have hc₂ : ∀ x y, Commute (ι₂ x) (ι₂ y) := fun x y => by
    rw [Commute, SemiconjBy, ← hs.map_add₂, ← hs.map_add₂, add_comm]
  have hUc : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u := by
    intro u hu v hv
    obtain ⟨d, rfl⟩ := (hs.mem_iff u).1 hu
    obtain ⟨d', rfl⟩ := (hs.mem_iff v).1 hv
    exact (((hc₁ d d').mul_right (hs.comm d d')).mul_left
      (((hs.comm d' d).symm).mul_right (hc₂ d d'))).eq
  have hlift : ∀ y : C, y * y = 1 →
      ∃ a : G, ∃ ha : a ∈ A, a ^ 2 = 1 ∧ ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y :=
    fun y hy => exists_sq_eq_one_of_sq' hψ hZ y (by rw [sq]; exact hy)
  choose κ₁ hκ₁A hκ₁2 hκ₁ψ using fun d => hlift (ι₁ d) (hs.mul_self₁ d)
  choose κ₂ hκ₂A hκ₂2 hκ₂ψ using fun d => hlift (ι₂ d) (hs.mul_self₂ d)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hprod2 : ∀ {a b : G} (ha : a ∈ A) (hb : b ∈ A), a ^ 2 = 1 → b ^ 2 = 1 →
      ∀ {y z : C}, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y →
        ψ ⟨b, le_normalizer hb⟩ = MulAut.conj z → y * z = z * y →
          a * b ∈ A ∧ (a * b) ^ 2 = 1 ∧
            ψ ⟨a * b, le_normalizer (mul_mem ha hb)⟩ = MulAut.conj (y * z) := by
    intro a b ha hb ha2 hb2 y z hay hbz hyz
    have hab : a * b = b * a := commute_of_conj_commute hψ hZ ha hb hb2 hay hbz hyz
    refine ⟨mul_mem ha hb, ?_, ?_⟩
    · rw [(Commute.mul_pow hab 2 : (a * b) ^ 2 = a ^ 2 * b ^ 2), ha2, hb2, one_mul]
    · have e : (⟨a * b, le_normalizer (mul_mem ha hb)⟩ : normalizer (A : Set G)) =
          ⟨a, le_normalizer ha⟩ * ⟨b, le_normalizer hb⟩ := rfl
      rw [e, map_mul, hay, hbz, map_mul]
  refine ⟨κ₁, κ₂, ?_⟩
  refine
    { map_add₁ := fun x y => ?_
      map_add₂ := fun x y => ?_
      inj₁ := fun x hx => ?_
      inj₂ := fun x hx => ?_
      mem₁ := hκ₁A
      mem₂ := hκ₂A
      comm := fun x y => ?_
      inf := fun x y hxy => ?_
      mem_iff := fun j => ?_
      prop₁ := fun x hx => ⟨hκ₁A x, ι₁ x, hκ₁ψ x, hs.prop₁ x hx⟩
      prop₂ := fun x hx => ⟨hκ₂A x, ι₂ x, hκ₂ψ x, hs.prop₂ x hx⟩
      scalar := fun c hc => ?_ }
  ·
    obtain ⟨hA', h2', hψ'⟩ := hprod2 (hκ₁A x) (hκ₁A y) (hκ₁2 x) (hκ₁2 y) (hκ₁ψ x) (hκ₁ψ y)
      (hc₁ x y).eq
    refine eq_of_sq_eq_one' hψ hZ (hκ₁A _) hA' (hκ₁2 _) h2' ?_
    rw [hκ₁ψ, hψ', hs.map_add₁]
  · obtain ⟨hA', h2', hψ'⟩ := hprod2 (hκ₂A x) (hκ₂A y) (hκ₂2 x) (hκ₂2 y) (hκ₂ψ x) (hκ₂ψ y)
      (hc₂ x y).eq
    refine eq_of_sq_eq_one' hψ hZ (hκ₂A _) hA' (hκ₂2 _) h2' ?_
    rw [hκ₂ψ, hψ', hs.map_add₂]
  ·
    refine hs.inj₁ x (hinj ?_)
    rw [← hκ₁ψ x, map_one]
    have e : (⟨κ₁ x, le_normalizer (hκ₁A x)⟩ : normalizer (A : Set G)) = 1 := Subtype.ext hx
    rw [e, map_one]
  · refine hs.inj₂ x (hinj ?_)
    rw [← hκ₂ψ x, map_one]
    have e : (⟨κ₂ x, le_normalizer (hκ₂A x)⟩ : normalizer (A : Set G)) = 1 := Subtype.ext hx
    rw [e, map_one]
  ·
    exact commute_of_conj_commute hψ hZ (hκ₁A x) (hκ₂A y) (hκ₂2 y) (hκ₁ψ x) (hκ₂ψ y)
      (hs.comm x y).eq
  ·
    refine hs.inf x y (hinj ?_)
    rw [← hκ₁ψ x, ← hκ₂ψ y]
    congr 1
    exact Subtype.ext hxy
  ·
    have hZ2 : ∀ u ∈ Z, u ^ 2 = 1 := fun u hu => by
      obtain ⟨d, rfl⟩ := (hs.mem_iff u).1 hu
      rw [sq]
      calc ι₁ d * ι₂ d * (ι₁ d * ι₂ d) = ι₁ d * (ι₂ d * ι₁ d) * ι₂ d := by group
        _ = ι₁ d * (ι₁ d * ι₂ d) * ι₂ d := by rw [(hs.comm d d).eq]
        _ = (ι₁ d * ι₁ d) * (ι₂ d * ι₂ d) := by group
        _ = 1 := by rw [hs.mul_self₁, hs.mul_self₂, one_mul]
    constructor
    · intro hj
      rw [hT] at hj
      obtain ⟨hjA, hj2, z, hz, hjz⟩ := (mem_lift2 hψ hZ hUc).1 hj
      obtain ⟨d, rfl⟩ := (hs.mem_iff z).1 hz
      refine ⟨d, ?_⟩
      obtain ⟨hA', h2', hψ'⟩ := hprod2 (hκ₁A d) (hκ₂A d) (hκ₁2 d) (hκ₂2 d) (hκ₁ψ d) (hκ₂ψ d)
        (hs.comm d d).eq
      exact eq_of_sq_eq_one' hψ hZ hjA hA' hj2 h2' (by rw [hjz, hψ'])
    · rintro ⟨d, rfl⟩
      obtain ⟨hA', h2', hψ'⟩ := hprod2 (hκ₁A d) (hκ₂A d) (hκ₁2 d) (hκ₂2 d) (hκ₁ψ d) (hκ₂ψ d)
        (hs.comm d d).eq
      rw [hT]
      exact mem_lift2_of hA' h2' ((hs.mem_iff _).2 ⟨d, rfl⟩) hψ'
  ·
    obtain ⟨a, ha⟩ := hs.scalar c hc
    obtain ⟨â, hâ, hâψ⟩ := hψ.exists_eq (MulAut.conj a) ⟨a, rfl⟩
    refine ⟨â, hâ, fun x => ⟨?_, ?_⟩⟩
    · have hmA : â⁻¹ * κ₁ x * â ∈ A := mul_mem (mul_mem (inv_mem hâ) (hκ₁A x)) hâ
      refine eq_of_sq_eq_one' hψ hZ hmA (hκ₁A x) ?_ (hκ₁2 x) ?_
      · rw [sq, show â⁻¹ * κ₁ x * â * (â⁻¹ * κ₁ x * â) = â⁻¹ * (κ₁ x * κ₁ x) * â by
          group, ← sq, hκ₁2, mul_one, inv_mul_cancel]
      · have e : (⟨â⁻¹ * κ₁ x * â, le_normalizer hmA⟩ : normalizer (A : Set G)) =
            (⟨â, le_normalizer hâ⟩ : normalizer (A : Set G))⁻¹ * ⟨κ₁ x, le_normalizer (hκ₁A x)⟩ *
              ⟨â, le_normalizer hâ⟩ := rfl
        rw [e, map_mul, map_mul, map_inv, hâψ, hκ₁ψ, ← map_inv, ← map_mul, ← map_mul,
          (ha x).1]
    · have hmA : â⁻¹ * κ₂ x * â ∈ A := mul_mem (mul_mem (inv_mem hâ) (hκ₂A x)) hâ
      refine eq_of_sq_eq_one' hψ hZ hmA (hκ₂A (c * x)) ?_ (hκ₂2 (c * x)) ?_
      · rw [sq, show â⁻¹ * κ₂ x * â * (â⁻¹ * κ₂ x * â) = â⁻¹ * (κ₂ x * κ₂ x) * â by
          group, ← sq, hκ₂2, mul_one, inv_mul_cancel]
      · have e : (⟨â⁻¹ * κ₂ x * â, le_normalizer hmA⟩ : normalizer (A : Set G)) =
            (⟨â, le_normalizer hâ⟩ : normalizer (A : Set G))⁻¹ * ⟨κ₂ x, le_normalizer (hκ₂A x)⟩ *
              ⟨â, le_normalizer hâ⟩ := rfl
        rw [e, map_mul, map_mul, map_inv, hâψ, hκ₂ψ, hκ₂ψ, ← map_inv, ← map_mul, ← map_mul,
          (ha x).2]

theorem false_of_splitData (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) {reps : List C}
    (hcover : ClassesCover reps)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z)
    (hact : ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' → ∀ t ∈ T', t ≠ 1 →
      ∀ (htN : t ∈ normalizer (A : Set G)) (x : C), ψ ⟨t, htN⟩ = MulAut.conj x →
        ActsIn ψ T' (zx x))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) {P₁ P₂ : G → Prop}
    {ι₁ ι₂ : F → G} (hsd : RankTwoClassical.SplitData A T P₁ P₂ F ι₁ ι₂)
    (hP : ∀ s, P₁ s ∨ P₂ s → ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' → s ∈ T' → s = 1) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have hcardF : 1 < ((Finset.univ.erase (0 : F)).erase 1).card := by
    have h1 : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
    rw [Finset.card_erase_of_mem (by simp), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, h1]
    omega
  obtain ⟨e₁, he₁, e₂, he₂, he₁₂⟩ := Finset.one_lt_card.mp hcardF
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at he₁ he₂
  obtain ⟨a₁, ha₁A, ha₁⟩ := hsd.scalar e₁ he₁.2
  obtain ⟨a₂, ha₂A, ha₂⟩ := hsd.scalar e₂ he₂.2
  have hTA : T ≤ A := fun j hj => by
    obtain ⟨d, rfl⟩ := (hsd.mem_iff j).1 hj
    exact mul_mem (hsd.mem₁ d) (hsd.mem₂ d)
  have hTbot := hc.T_inf_conj hZA
  have hT1 : T ≠ ⊥ := hc.T_ne_bot
  have hRA := hc.R_inf_A hZA
  have hfacts : ∀ (e : F) (a : G), e ≠ 1 →
      (∀ x, a⁻¹ * ι₁ x * a = ι₁ x ∧ a⁻¹ * ι₂ x * a = ι₂ (e * x)) →
      rightConjugate T a ≤ centralizer (T : Set G) ∧ T ⊓ rightConjugate T a = ⊥ ∧
        rightConjugate T a ≠ T ∧ rightConjugate T a ≤ A := by
    intro e a he ha
    have hcen : rightConjugate T a ≤ centralizer (T : Set G) := by
      intro v hv
      rw [mem_centralizer_iff]
      intro u hu
      obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha).mp hv
      obtain ⟨d', rfl⟩ := (hsd.mem_iff u).mp hu
      exact (hsd.commute_mul d' d' d (e * d)).eq
    have hinf : T ⊓ rightConjugate T a = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hv1, hv2⟩ := mem_inf.mp hv
      obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha).mp hv2
      obtain ⟨d', hd'⟩ := (hsd.mem_iff_one _).mp hv1
      have h0 := hsd.eq_zero_of_mul_eq he hd'
      rw [h0, mul_zero, hsd.map_zero₁, hsd.map_zero₂, mul_one]
      exact one_mem _
    refine ⟨hcen, hinf, fun heq => hT1 ?_, ?_⟩
    · rw [← inf_idem T]
      conv_lhs => rw [show T ⊓ T = T ⊓ rightConjugate T a by rw [heq]]
      exact hinf
    · intro v hv
      obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha).mp hv
      exact mul_mem (hsd.mem₁ d) (hsd.mem₂ _)
  obtain ⟨hcen₁, -, hne₁, hA₁⟩ := hfacts e₁ a₁ he₁.1 ha₁
  obtain ⟨hcen₂, -, hne₂, hA₂⟩ := hfacts e₂ a₂ he₂.1 ha₂
  obtain ⟨w, hw, -⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hcov : ∃ (a : G) (e : F), e ≠ 1 ∧
      (∀ x, a⁻¹ * ι₁ x * a = ι₁ x ∧ a⁻¹ * ι₂ x * a = ι₂ (e * x)) ∧ a ∈ A ∧
      rightConjugate T a ≤ centralizer (T : Set G) ∧ rightConjugate T a ≠ T ∧
      ∀ v ∈ sec3V (rightConjugate T g⁻¹) (rightConjugate T (a * g⁻¹)), v ∉ A →
        ∃ x : G, rightConjugate (rightConjugate T g⁻¹) x ≤
            sec3V (rightConjugate T g⁻¹) (rightConjugate T (a * g⁻¹)) ∧
          v ∈ rightConjugate (rightConjugate T g⁻¹) x := by
    have hle : ∀ a : G, rightConjugate T (a * g⁻¹) ≤ A →
        rightConjugate T a ≤ rightConjugate A g := by
      intro a h
      rw [← rightConjugate_mul] at h
      have h' := (RankTwoClassical.rightConjugate_le_rightConjugate_iff (x := g)).mpr h
      rwa [RankTwoClassical.rightConjugate_inv_rightConjugate] at h'
    rcases main_of_reps hZC hψ h4 h32 h34 (hc.derived hcen₁ hne₁) hZA hcover hJ hact with
      ⟨h1, -⟩ | ⟨-, h2, -⟩
    · rcases main_of_reps hZC hψ h4 h32 h34 (hc.derived hcen₂ hne₂) hZA hcover hJ hact with
        ⟨h1', -⟩ | ⟨-, h2', -⟩
      · exfalso
        have hle₁ := hle a₁ (fun u hu => (mem_inf.1 (h1 ▸ hu)).2)
        have hle₂ := hle a₂ (fun u hu => (mem_inf.1 (h1' ▸ hu)).2)
        apply hT1
        rw [eq_bot_iff, ← hTbot]
        intro j hj
        refine mem_inf.2 ⟨hj, ?_⟩
        obtain ⟨d, rfl⟩ := (hsd.mem_iff j).1 hj
        have he : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr he₁₂
        set x := (d - e₂ * d) / (e₁ - e₂) with hx
        set y := d - x with hy
        have hxy : x + y = d := by rw [hy]; ring
        have hexy : e₁ * x + e₂ * y = d := by
          have h3 : (e₁ - e₂) * x = d - e₂ * d := by rw [hx]; field_simp
          rw [hy]
          linear_combination h3
        have hm₁ : ι₁ x * ι₂ (e₁ * x) ∈ rightConjugate T a₁ :=
          (hsd.mem_rightConjugate_iff ha₁).mpr ⟨x, rfl⟩
        have hm₂ : ι₁ y * ι₂ (e₂ * y) ∈ rightConjugate T a₂ :=
          (hsd.mem_rightConjugate_iff ha₂).mpr ⟨y, rfl⟩
        have hprod : ι₁ x * ι₂ (e₁ * x) * (ι₁ y * ι₂ (e₂ * y)) = ι₁ d * ι₂ d := by
          rw [hsd.mul_mul, hxy, hexy]
        rw [← hprod]
        exact mul_mem (hle₁ hm₁) (hle₂ hm₂)
      · refine ⟨a₂, e₂, he₂.1, ha₂, ha₂A, hcen₂, hne₂, fun v hv hvA => ?_⟩
        obtain ⟨x, hx, hvx, -⟩ := (h2' v hv).1 hvA
        exact ⟨x, hx, hvx⟩
    · refine ⟨a₁, e₁, he₁.1, ha₁, ha₁A, hcen₁, hne₁, fun v hv hvA => ?_⟩
      obtain ⟨x, hx, hvx, -⟩ := (h2 v hv).1 hvA
      exact ⟨x, hx, hvx⟩
  obtain ⟨a, e, he, ha, haA, hcen, hne, hcover'⟩ := hcov
  have hTaA : rightConjugate T a ≤ A := by
    intro v hv
    obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha).mp hv
    exact mul_mem (hsd.mem₁ d) (hsd.mem₂ _)
  have hout : ∃ s : G, s ∉ rightConjugate A g ∧ s ∈ T ⊔ rightConjugate T a ∧ s ≠ 1 ∧
      (P₁ s ∨ P₂ s) ∧ s ∈ A := by
    by_contra hno
    push Not at hno
    apply hT1
    rw [eq_bot_iff, ← hTbot]
    intro j hj
    refine mem_inf.mpr ⟨hj, ?_⟩
    obtain ⟨d, rfl⟩ := (hsd.mem_iff j).mp hj
    have h1 : ∀ x : F, ι₁ x ∈ rightConjugate A g := by
      intro x
      by_cases hx : x = 0
      · rw [hx, hsd.map_zero₁]
        exact one_mem _
      by_contra hx'
      have hmem : ι₁ x ∈ T ⊔ rightConjugate T a := by
        have := hsd.mem_sup he ha x 0
        rwa [hsd.map_zero₂, mul_one] at this
      exact hno (ι₁ x) hx' hmem (hsd.ne_one₁ hx) (Or.inl (hsd.prop₁ x hx)) (hsd.mem₁ x)
    have h2 : ∀ x : F, ι₂ x ∈ rightConjugate A g := by
      intro x
      by_cases hx : x = 0
      · rw [hx, hsd.map_zero₂]
        exact one_mem _
      by_contra hx'
      have hmem : ι₂ x ∈ T ⊔ rightConjugate T a := by
        have := hsd.mem_sup he ha 0 x
        rwa [hsd.map_zero₁, one_mul] at this
      exact hno (ι₂ x) hx' hmem (hsd.ne_one₂ hx) (Or.inr (hsd.prop₂ x hx)) (hsd.mem₂ x)
    exact mul_mem (h1 d) (h2 d)
  obtain ⟨s, hsAg, hsV, hs1, hsP, hsA⟩ := hout
  set R'' := rightConjugate T g⁻¹ with hR''
  set T'' := rightConjugate T (a * g⁻¹) with hT''
  set v := g * s * g⁻¹ with hvdef
  have hT''eq : T'' = rightConjugate R'' (g * a * g⁻¹) := by
    rw [hT'', hR'', rightConjugate_mul]
    congr 1
    group
  have hvV : v ∈ sec3V R'' T'' := by
    refine le_sec3V_of ⟨g * a * g⁻¹, hT''eq⟩ ?_
    have hmap : rightConjugate (T ⊔ rightConjugate T a) g⁻¹ = R'' ⊔ T'' := by
      rw [hR'', hT'', ← rightConjugate_mul]
      exact Subgroup.map_sup _ _ _
    rw [← hmap, mem_rightConjugate_iff, hvdef, inv_inv]
    simpa [mul_assoc] using hsV
  have hvA : v ∉ A := by
    intro hvA
    apply hsAg
    rw [mem_rightConjugate_iff]
    exact hvA
  obtain ⟨x, hxV, hvx⟩ := hcover' v hvV hvA
  have hR''w : R'' = rightConjugate R (w * g⁻¹) := by rw [hR'', hw, rightConjugate_mul]
  have hR₁ : rightConjugate R g⁻¹ = rightConjugate R'' (g * w⁻¹ * g⁻¹) := by
    rw [hR''w, rightConjugate_mul]
    congr 1
    group
  have hTaR : rightConjugate T a ≤ centralizer (R : Set G) := fun u hu =>
    mem_centralizer_iff.2 fun r hr =>
      (mem_centralizer_iff.1 (hc.sylowR.le hr) u (hTaA hu)).symm
  have hR₁C : rightConjugate R g⁻¹ ≤ centralizer ((R'' ⊔ T'' : Subgroup G) : Set G) := by
    refine AS76b.le_centralizer_sup ?_ ?_
    · rw [hR'', centralizer_rightConjugate]
      exact map_mono (le_centralizer_iff.1 hc.le_centralizer)
    · rw [hT'', ← rightConjugate_mul, centralizer_rightConjugate]
      exact map_mono (le_centralizer_iff.1 hTaR)
  have hR₁W : rightConjugate R g⁻¹ ≤ sec3W R'' T'' := by
    rw [hR₁] at hR₁C ⊢
    exact le_sec3W hR₁C
  have hQC : rightConjugate R'' x ≤ centralizer (rightConjugate R g⁻¹ : Set G) :=
    hxV.trans ((sec3V_le_centralizer R'' T'').trans (centralizer_le hR₁W))
  set y₃ := w * g⁻¹ * x * g with hy₃
  have hQ₃ : rightConjugate (rightConjugate R'' x) g = rightConjugate R y₃ := by
    rw [hR''w, rightConjugate_mul, rightConjugate_mul, hy₃, mul_assoc (w * g⁻¹) x g]
  have hsQ₃ : s ∈ rightConjugate R y₃ := by
    rw [← hQ₃, mem_rightConjugate_iff]
    exact hvx
  have hQ₃C : rightConjugate R y₃ ≤ centralizer (R : Set G) := by
    rw [← hQ₃]
    have h1 := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hQC
    change rightConjugate (rightConjugate R'' x) g ≤
      rightConjugate (centralizer (rightConjugate R g⁻¹ : Set G)) g at h1
    rwa [← centralizer_rightConjugate, RankTwoClassical.rightConjugate_inv_rightConjugate] at h1
  have hne₃ : rightConjugate R y₃ ≠ R := by
    intro h
    rw [h] at hsQ₃
    have hmem : s ∈ R ⊓ A := mem_inf.2 ⟨hsQ₃, hsA⟩
    rw [hRA, mem_bot] at hmem
    exact hs1 hmem
  exact hs1 (hP s hsP R (rightConjugate R y₃) y₃
    (sec3_of_conj_ne hc.hyp hc.sylowR hQ₃C hne₃) hsQ₃)

theorem inf_eq_bot_of_split (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z)
    (hact : ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' → ∀ t ∈ T', t ≠ 1 →
      ∀ (htN : t ∈ normalizer (A : Set G)) (x : C), ψ ⟨t, htN⟩ = MulAut.conj x →
        ActsIn ψ T' (zx x))
    (hsplit : ∀ y ∈ reps, ResidualMem y ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (_ : CharP F 2) (ι₁ ι₂ : F → C), 4 ≤ Nat.card F ∧ LineSplit (zx y) F ι₁ ι₂ ResidualMem) :
    T ⊓ A = ⊥ := by
  by_contra hTA
  obtain ⟨y, hy, a, ha, t, -, -, ht1, hc', hmem, haA, _hN, hψa⟩ :=
    exists_pinned_of_inf_ne_bot hZC hψ h4 h32 h34 hc hcover hTA
  have hat1 : a * t * a⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  rcases hsplit y hy with hR | ⟨F, _, _, _, ι₁, ι₂, hF, hs⟩
  · exact hat1 (eq_one_of_residualMem hZC hψ h4 h32 h34 hc' hOut hZA hmem haA hψa hR)
  have hT' := eq_lift2_of_inf_ne_bot hZC hψ h4 h32 h34 hc' hZA hcover hJ hact hmem haA hat1 hψa
  obtain ⟨κ₁, κ₂, hsd⟩ := exists_splitData_of_lineSplit hZC hψ hZA hs hT'
  refine false_of_splitData hZC hψ h4 h32 h34 hc' hZA hcover hJ hact hF hsd ?_
  rintro s (⟨hsA, z, hsz, hz⟩ | ⟨hsA, z, hsz, hz⟩) R' T' g' hc'' hs'
  · exact eq_one_of_residualMem hZC hψ h4 h32 h34 hc'' hOut hZA hs' hsA hsz hz
  · exact eq_one_of_residualMem hZC hψ h4 h32 h34 hc'' hOut hZA hs' hsA hsz hz

end Descent

end CFSG.ComponentClassification.RankTwoExceptional.Exc
