module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicLinear
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma34
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec3

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite G] in
theorem isElemAbelian_map {H : Type*} [Group H] (φ : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.map φ) := CFSG.SectionRank.isElemAbelian_map hE _

theorem card_le_card_inf_centralizer_mul {V : Subgroup G} (hV : IsMulCommutative V) {w : G}
    (hwV : w ∈ normalizer (V : Set G)) :
    Nat.card V ≤ Nat.card (V ⊓ centralizer ({w} : Set G) : Subgroup G) *
      Nat.card (⁅V, zpowers w⁆ : Subgroup G) := by
  classical
  have hc : ∀ v ∈ V, w * v * w⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.mp hwV v).mp hv
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hV.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let φ : V →* V :=
    { toFun := fun v => ⟨v * (w * v * w⁻¹)⁻¹, mul_mem v.2 (inv_mem (hc v v.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have ha := inv_mem (hc x x.2)
        have hb := inv_mem (hc y y.2)
        have h1 : (w * ((x : G) * y) * w⁻¹)⁻¹ = (w * y * w⁻¹)⁻¹ * (w * x * w⁻¹)⁻¹ := by group
        show (x : G) * y * (w * ((x : G) * y) * w⁻¹)⁻¹ =
          (x : G) * (w * x * w⁻¹)⁻¹ * ((y : G) * (w * y * w⁻¹)⁻¹)
        rw [h1]
        set a := (w * (x : G) * w⁻¹)⁻¹
        set b := (w * (y : G) * w⁻¹)⁻¹
        have hab : b * a = a * b := hcomm b hb a ha
        have hya : (y : G) * a = a * y := hcomm _ y.2 a ha
        calc (x : G) * y * (b * a) = x * y * (a * b) := by rw [hab]
          _ = x * (y * a) * b := by simp only [mul_assoc]
          _ = x * (a * y) * b := by rw [hya]
          _ = x * a * (y * b) := by simp only [mul_assoc]) }
  have hφ : ∀ v : V, (φ v : G) = v * (w * v * w⁻¹)⁻¹ := fun _ => rfl
  have hker : ∀ v : V, φ v = 1 → (v : G) ∈ centralizer ({w} : Set G) := by
    intro v hv
    have h1 : (v : G) * (w * v * w⁻¹)⁻¹ = 1 := by rw [← hφ, hv, coe_one]
    rw [mul_inv_eq_one] at h1
    rw [mem_centralizer_singleton_iff]
    calc (v : G) * w = w * v * w⁻¹ * w := by rw [← h1]
      _ = w * v := by group
  have hrange : ∀ v : V, (φ v : G) ∈ (⁅V, zpowers w⁆ : Subgroup G) := by
    intro v
    rw [hφ, show (v : G) * (w * v * w⁻¹)⁻¹ = ⁅(v : G), w⁆ by rw [commutatorElement_def]; group]
    exact commutator_mem_commutator v.2 (mem_zpowers w)
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.ker ≤ Nat.card (V ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun v => ⟨v.1.1, v.1.2, hker v.1 v.2⟩) ?_
    intro v v' hvv
    have h := congrArg Subtype.val hvv
    exact Subtype.ext (Subtype.ext h)
  have h3 : Nat.card φ.range ≤ Nat.card (⁅V, zpowers w⁆ : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun u => ⟨u.1.1, ?_⟩) ?_
    · obtain ⟨v, hv⟩ := u.2
      rw [← hv]
      exact hrange v
    · intro u u' huu
      have h := congrArg Subtype.val huu
      exact Subtype.ext (Subtype.ext h)
  calc Nat.card V = Nat.card φ.range * Nat.card φ.ker := h1
    _ ≤ Nat.card (⁅V, zpowers w⁆ : Subgroup G) *
        Nat.card (V ⊓ centralizer ({w} : Set G) : Subgroup G) := Nat.mul_le_mul h3 h2
    _ = _ := mul_comm _ _

namespace Sec3

variable {L T : Subgroup G}

theorem mem_normalizer_T₁ (h : Sec3 G L T) {w : G} (hw : w ∈ T) :
    w ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  mem_normalizer_inf (le_normalizer hw) (h.sylow.le hw)

theorem not_mem_sup_of_not_mem (h : Sec3 G L T) {w : G} (hw : w ∈ T)
    (hwV : w ∉ (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G))) : w ∉ L ⊔ centralizer (L : Set G) :=
  fun hLK => hwV (h.inf_sup_eq ▸ mem_inf.mpr ⟨hw, hLK⟩)

theorem inf_sup_eq_of_le (h : Sec3 G L T) {E : Subgroup G} (hET : E ≤ T) :
    E ⊓ (L ⊔ centralizer (L : Set G)) = E ⊓ ((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G))) := by
  rw [← h.inf_sup_eq, ← inf_assoc, inf_eq_left.mpr hET]

theorem eight_le_card_T₁ (h : Sec3 G L T) :
    8 ≤ Nat.card (T ⊓ L : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := h.isSylowOf_T₁
  rw [← hQ, card_map_of_injective L.subtype_injective]
  exact h.hyp.eight_le_card_sylow Q

section L2

variable {f : ℕ}

theorem isElemAbelian_sup_of_psl2
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) :
    IsElemAbelian 2 ((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G))) := by
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  exact isElemAbelian_sup (isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁)
    (h.isElemAbelian_T₀ hF)
    (fun t ht => mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp ht.2 x hx.2)

theorem two_mul_card_lt_of_psl2 (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {w : G} (hw : w ∈ T) (hww : w * w = 1)
    (hwV : w ∉ (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G))) :
    2 * Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) <
      Nat.card (T ⊓ L : Subgroup G) := by
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hsq := card_centralizer_sq_le_of_psl2 h.hyp.standard.1.1 hZ (by omega) e h.isSylowOf_T₁
    (h.sylow.le hw) hww (fun x hx => (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hw) x).mp hx)
    (h.not_mem_sup_of_not_mem hw hwV)
  have h8 := h.eight_le_card_T₁
  by_contra hle
  push Not at hle
  nlinarith

theorem eq_of_psl2 (h : Sec3 G L T)
    (hF : Foundation) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    {E : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 2 E)
    (hcard : Nat.card ((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) ≤ Nat.card E) :
    E = (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) := by
  set K := centralizer (L : Set G) with hKdef
  set V := (T ⊓ L) ⊔ (T ⊓ K) with hVdef
  have hVel := h.isElemAbelian_sup_of_psl2 hF hf e
  have hB := (rankTwoBenderType_iff.mp h.hyp.bender).fusionIsBenderGroup
  have h2 := card_le_two_mul_inf h.hyp.standard.1.1 hB (hET.trans h.sylow.le) hE
  rw [h.inf_sup_eq_of_le hET] at h2
  by_cases hle : E ≤ V
  · exact eq_of_le_of_card_ge hle hcard
  exfalso
  obtain ⟨w, hwE, hwV⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hww : w * w = 1 := by rw [← sq]; exact hE.2 w hwE
  have hlt := h.two_mul_card_lt_of_psl2 hf e (hET hwE) hww hwV
  set X := V ⊓ centralizer ({w} : Set G) with hXdef
  have hEVX : E ⊓ V ≤ X := fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2,
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hE.1.is_comm.comm ⟨x, (mem_inf.mp hx).1⟩ ⟨w, hwE⟩))⟩
  have hX : Nat.card V ≤ 2 * Nat.card X :=
    hcard.trans (h2.trans (Nat.mul_le_mul_left 2 (card_le_of_le hEVX)))
  have hT₁V : T ⊓ L ≤ V := le_sup_left
  have hT₁X : X ⊓ (T ⊓ L) = T ⊓ L ⊓ centralizer ({w} : Set G) := by
    rw [hXdef, inf_comm, ← inf_assoc, inf_eq_left.mpr hT₁V]
  have hT₁N : T ⊓ L ≤ normalizer (X : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc : t * x = x * t := congrArg Subtype.val
        (hVel.1.is_comm.comm ⟨t, hT₁V ht⟩ ⟨x, (mem_inf.mp hx).1⟩)
      rwa [hc, mul_inv_cancel_right]
    · intro hx
      have hxV : x ∈ V := by
        have := mul_mem (mul_mem (inv_mem (hT₁V ht)) (mem_inf.mp hx).1) (hT₁V ht)
        simpa [mul_assoc] using this
      have hc : t * x = x * t := congrArg Subtype.val
        (hVel.1.is_comm.comm ⟨t, hT₁V ht⟩ ⟨x, hxV⟩)
      rwa [hc, mul_inv_cancel_right] at hx
  have hprod := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hT₁N
  rw [hT₁X] at hprod
  have hsupV : Nat.card (X ⊔ (T ⊓ L) : Subgroup G) ≤ Nat.card V :=
    card_le_of_le (sup_le inf_le_left hT₁V)
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have key : Nat.card X * Nat.card (T ⊓ L : Subgroup G) ≤
      Nat.card X * (2 * Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G)) := by
    calc Nat.card X * Nat.card (T ⊓ L : Subgroup G)
        = Nat.card (X ⊔ (T ⊓ L) : Subgroup G) *
            Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) := hprod.symm
      _ ≤ Nat.card V * Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hsupV
      _ ≤ 2 * Nat.card X * Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hX
      _ = Nat.card X * (2 * Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G)) := by
          ring
  have := Nat.le_of_mul_le_mul_left key hXpos
  omega

theorem normalizer_le_of_psl2
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) :
    normalizer (T : Set G) ≤
      normalizer (((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  intro y hy
  set V := (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) with hVdef
  have hVT : V ≤ T := sup_le inf_le_left inf_le_left
  have hET : V.map (MulAut.conj y).toMonoidHom ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_normalizer_iff.mp hy v).mp (hVT hv)
  have hcard : Nat.card V ≤ Nat.card (V.map (MulAut.conj y).toMonoidHom) :=
    (card_map_of_injective (MulAut.conj y).injective).ge
  rw [mem_normalizer_iff_map_conj_eq]
  exact h.eq_of_psl2 hF hf e hET (isElemAbelian_map _ (h.isElemAbelian_sup_of_psl2 hF hf e)) hcard

end L2

theorem le_sup_of_sz (h : Sec3 G L T) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) : T ≤ L ⊔ centralizer (L : Set G) := by
  intro t ht
  obtain ⟨k, hk⟩ := h.sylow.isPGroup ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact mem_sup_centralizer_of_sz h.hyp.standard.1.1 ha e (h.sylow.le ht) htk

theorem eq_sup_of_sz (h : Sec3 G L T) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) : T = (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) := by
  rw [← h.inf_sup_eq, inf_eq_left.mpr (h.le_sup_of_sz ha e)]

theorem normalizer_le_of_sz (h : Sec3 G L T) {a : ℕ} (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) :
    normalizer (T : Set G) ≤
      normalizer (((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  rw [← h.eq_sup_of_sz ha e]

end Sec3

end CFSG.ComponentClassification.GMS78
