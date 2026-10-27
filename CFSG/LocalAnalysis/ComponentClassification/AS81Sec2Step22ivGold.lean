module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.ComponentClassification.AS81.Sec2

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_of_isElemAbelian {p : ℕ} {W : Subgroup G} (hW : IsElemAbelian p W) {a b : G}
    (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hW ha hb

theorem card_le_card_commutator_mul [Finite G] {p : ℕ} {W : Subgroup G} (hW : IsElemAbelian p W)
    {x : G} (hx : x ∈ normalizer (W : Set G)) :
    Nat.card W ≤ Nat.card (⁅W, zpowers x⁆ : Subgroup G) *
      Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have hy : ∀ v ∈ W, x * v⁻¹ * x⁻¹ ∈ W := fun v hv =>
    (mem_normalizer_iff.mp hx _).mp (W.inv_mem hv)
  have hcw : ∀ v : G, ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := fun v => by
    rw [commutatorElement_def]
    group
  have hmem : ∀ v ∈ W, ⁅v, x⁆ ∈ W := fun v hv => by
    rw [hcw]
    exact W.mul_mem hv (hy v hv)
  let φ : ↥W →* ↥W :=
    { toFun := fun v => ⟨⁅(v : G), x⁆, hmem v v.2⟩
      map_one' := Subtype.ext (by simp [commutatorElement_def])
      map_mul' := fun a b => Subtype.ext (by
        show ⁅(a : G) * b, x⁆ = ⁅(a : G), x⁆ * ⁅(b : G), x⁆
        rw [hcw, hcw, hcw]
        have hab : x * ((a : G) * b)⁻¹ * x⁻¹ = (x * (b : G)⁻¹ * x⁻¹) * (x * (a : G)⁻¹ * x⁻¹) := by
          group
        rw [hab]
        have hya := hy a a.2
        have hyb := hy b b.2
        generalize x * (a : G)⁻¹ * x⁻¹ = ya at hya ⊢
        generalize x * (b : G)⁻¹ * x⁻¹ = yb at hyb ⊢
        have h1 := comm_of_isElemAbelian hW hyb hya
        have h2 := comm_of_isElemAbelian hW b.2 hya
        calc (a : G) * b * (yb * ya) = a * (b * (yb * ya)) := by group
          _ = a * (b * (ya * yb)) := by rw [h1]
          _ = a * ((b * ya) * yb) := by group
          _ = a * ((ya * b) * yb) := by rw [h2]
          _ = a * ya * (b * yb) := by group) }
  have hcent : ∀ v : ↥φ.ker, ((v : ↥W) : G) ∈ centralizer ({x} : Set G) := by
    intro v
    have h1 : ⁅((v : ↥W) : G), x⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp v.2)
    rw [mem_centralizer_singleton_iff]
    rw [commutatorElement_def] at h1
    calc ((v : ↥W) : G) * x = (((v : ↥W) : G) * x * ((v : ↥W) : G)⁻¹ * x⁻¹) * x *
          ((v : ↥W) : G) := by group
      _ = x * ((v : ↥W) : G) := by rw [h1, one_mul]
  have hker : Nat.card φ.ker ≤ Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun v => ⟨((v : ↥W) : G), (v : ↥W).2, hcent v⟩)
      fun v w h => ?_
    have h' := congrArg Subtype.val h
    dsimp only at h'
    exact Subtype.ext (Subtype.ext h')
  have hcomm : ∀ r : ↥φ.range, ((r : ↥W) : G) ∈ (⁅W, zpowers x⁆ : Subgroup G) := by
    intro r
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp r.2
    rw [← hv]
    exact commutator_mem_commutator v.2 (mem_zpowers x)
  have hrange : Nat.card φ.range ≤ Nat.card (⁅W, zpowers x⁆ : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun r => ⟨((r : ↥W) : G), hcomm r⟩) fun r s h => ?_
    have h' := congrArg Subtype.val h
    dsimp only at h'
    exact Subtype.ext (Subtype.ext h')
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  exact Nat.mul_le_mul hrange hker

section Count

variable {W R : Subgroup G}

theorem mem_of_mem_sup_of_conj
    (hRWc : ∀ x ∈ R ⊔ W, x ∉ W → x ^ 2 = 1 → ∃ r ∈ R, ∃ g : G, x = g * r * g⁻¹)
    (hRG : ∀ r ∈ R, r ≠ 1 → ∀ g : G, g * r * g⁻¹ ∉ W) {x : G} (hx : x ∈ R ⊔ W)
    (hx2 : x ^ 2 = 1) {w g : G} (hw : w ∈ W) (hxw : x = g * w * g⁻¹) : x ∈ W := by
  by_contra hxW
  obtain ⟨r, hr, h, rfl⟩ := hRWc x hx hxW hx2
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hxW (by simp)
  apply hRG r hr hr1 (g⁻¹ * h)
  have e : g⁻¹ * h * r * (g⁻¹ * h)⁻¹ = w := by
    calc g⁻¹ * h * r * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * r * h⁻¹) * g := by group
      _ = g⁻¹ * (g * w * g⁻¹) * g := by rw [hxw]
      _ = w := by group
  rw [e]
  exact hw

variable {T₁ : Subgroup G}

theorem card_mul_card_le [Finite G] (hWT : W ≤ T₁) (hT₁N : T₁ ≤ normalizer (W : Set G))
    (hRT : R ≤ T₁) (hRW1 : R ⊓ W = ⊥) {X : Subgroup G} (hXT : X ≤ T₁)
    (hXRW : ∀ x ∈ X, x ∈ R ⊔ W → x ∈ W) :
    Nat.card W * Nat.card X * Nat.card R ≤ Nat.card T₁ * Nat.card (X ⊓ W : Subgroup G) := by
  have hXN : X ≤ normalizer (W : Set G) := hXT.trans hT₁N
  have hM := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hXN
  rw [sup_comm, inf_comm] at hM
  have hMR : ∀ m ∈ X ⊔ W, m ∈ R → m = 1 := by
    intro m hm hmR
    have hm' : m ∈ ((X ⊔ W : Subgroup G) : Set G) := hm
    rw [coe_mul_of_left_le_normalizer_right X W hXN] at hm'
    obtain ⟨x, hx, w, hw, rfl⟩ := hm'
    have hxRW : x ∈ R ⊔ W := by
      have e : x = (x * w) * w⁻¹ := by group
      rw [e]
      exact (R ⊔ W).mul_mem (mem_sup_left hmR) (mem_sup_right (W.inv_mem hw))
    have hxw : x * w ∈ R ⊓ W := ⟨hmR, W.mul_mem (hXRW x hx hxRW) hw⟩
    rwa [hRW1, mem_bot] at hxw
  have hMT : X ⊔ W ≤ T₁ := sup_le hXT hWT
  let f : ↥(X ⊔ W) × ↥R → ↥T₁ := fun p => ⟨p.1 * p.2, T₁.mul_mem (hMT p.1.2) (hRT p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨m, r⟩ ⟨m', r'⟩ h
    have h' : (m : G) * r = m' * r' := congrArg Subtype.val h
    have h1 : (m' : G)⁻¹ * m = r' * (r : G)⁻¹ := by
      calc (m' : G)⁻¹ * m = (m' : G)⁻¹ * (m * r) * (r : G)⁻¹ := by group
        _ = (m' : G)⁻¹ * (m' * r') * (r : G)⁻¹ := by rw [h']
        _ = r' * (r : G)⁻¹ := by group
    have h2 : (m' : G)⁻¹ * m = 1 := hMR _ ((X ⊔ W).mul_mem ((X ⊔ W).inv_mem m'.2) m.2)
      (h1 ▸ R.mul_mem r'.2 (R.inv_mem r.2))
    have hm : (m : G) = m' := (inv_mul_eq_one.mp h2).symm
    have hr : (r : G) = r' := by
      rw [h2] at h1
      exact (mul_inv_eq_one.mp h1.symm).symm
    exact Prod.ext (Subtype.ext hm) (Subtype.ext hr)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  calc Nat.card W * Nat.card X * Nat.card R
      = Nat.card (X ⊔ W : Subgroup G) * Nat.card (X ⊓ W : Subgroup G) * Nat.card R := by rw [hM]
    _ = Nat.card (X ⊔ W : Subgroup G) * Nat.card R * Nat.card (X ⊓ W : Subgroup G) := by ring
    _ ≤ Nat.card T₁ * Nat.card (X ⊓ W : Subgroup G) := Nat.mul_le_mul_right _ hcard

end Count

section Closure

variable [Finite G] {W T₁ R : Subgroup G} (hW : IsElemAbelian 2 W) (hW256 : Nat.card W = 256)
  (hWT : W ≤ T₁) (hT₁ : IsSylowOf 2 T₁ (normalizer (W : Set G))) (h32 : Nat.card T₁ ≤ 32 * 256)
  (hRT : R ≤ T₁) (hR4 : Nat.card R = 4) (hRW1 : R ⊓ W = ⊥)
  (hC : ∀ x ∈ T₁, x ∉ W → x ^ 2 = 1 →
    Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 16)
  (hRWc : ∀ x ∈ R ⊔ W, x ∉ W → x ^ 2 = 1 → ∃ r ∈ R, ∃ g : G, x = g * r * g⁻¹)
  (hRG : ∀ r ∈ R, r ≠ 1 → ∀ g : G, g * r * g⁻¹ ∉ W)

include hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hRWc hRG in
theorem card_le_eight_mul {U : Subgroup G} (hUW : U ≤ W) (h : G) (hXT : rightConjugate U h ≤ T₁) :
    Nat.card (rightConjugate U h) ≤ 8 * Nat.card (rightConjugate U h ⊓ W : Subgroup G) := by
  set X := rightConjugate U h
  have hXRW : ∀ x ∈ X, x ∈ R ⊔ W → x ∈ W := by
    intro x hx hxRW
    have hxU : h * x * h⁻¹ ∈ U := (mem_rightConjugate_iff U h x).mp hx
    have hx2 : x ^ 2 = 1 := by
      have h2 := hW.2 _ (hUW hxU)
      have e : (h * x * h⁻¹) ^ 2 = h * x ^ 2 * h⁻¹ := by
        rw [sq, sq]
        group
      rw [e] at h2
      have e' : x ^ 2 = h⁻¹ * (h * x ^ 2 * h⁻¹) * h := by group
      rw [e', h2]
      group
    exact mem_of_mem_sup_of_conj hRWc hRG hxRW hx2 (hUW hxU) (g := h⁻¹) (by group)
  have hle := card_mul_card_le hWT hT₁.le hRT hRW1 hXT hXRW
  rw [hW256, hR4] at hle
  have hT := Nat.mul_le_mul_right (Nat.card (X ⊓ W : Subgroup G)) h32
  nlinarith

include hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hC hRWc hRG in
theorem rightConjugate_eq_of_le (g : G) (hg : rightConjugate W g ≤ T₁) :
    rightConjugate W g = W := by
  by_contra hne
  set X := rightConjugate W g with hXdef
  have hX : Nat.card X = 256 := (rightConjugate_card W g).trans hW256
  have hXW : ¬ X ≤ W := fun hle => hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hX, hW256]))
  obtain ⟨x, hxX, hxW⟩ := IsConcreteLE.not_le_iff_exists.mp hXW
  have hxg : g * x * g⁻¹ ∈ W := (mem_rightConjugate_iff W g x).mp hxX
  have hXcomm : ∀ y ∈ X, x * y = y * x := by
    intro y hy
    have hyg : g * y * g⁻¹ ∈ W := (mem_rightConjugate_iff W g y).mp hy
    have h1 := comm_of_isElemAbelian hW hxg hyg
    calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = y * x := by group
  have hx2 : x ^ 2 = 1 := by
    have h2 := hW.2 _ hxg
    have e : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
      rw [sq, sq]
      group
    rw [e] at h2
    have e' : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
    rw [e', h2]
    group
  have hCx := hC x (hg hxX) hxW hx2
  have hXWle : X ⊓ W ≤ W ⊓ centralizer ({x} : Set G) := fun y hy =>
    ⟨hy.2, mem_centralizer_singleton_iff.mpr (hXcomm y hy.1).symm⟩
  have h16 : Nat.card (X ⊓ W : Subgroup G) ≤ 16 := (Subgroup.card_le_of_le hXWle).trans hCx
  have h8 := card_le_eight_mul hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hRWc hRG le_rfl g hg
  rw [← hXdef, hX] at h8
  have hpos : 0 < Nat.card (X ⊓ W : Subgroup G) := Nat.card_pos
  omega

include hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hC hRWc hRG in
theorem exists_sylow_eq : ∃ P : Sylow 2 G, (P : Subgroup G) = T₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT₁.isPGroup.exists_le_sylow
  refine ⟨P, ?_⟩
  by_contra hne
  set H := T₁.subgroupOf (P : Subgroup G)
  have hHtop : H ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm (fun y hy => ?_) hP
    have : (⟨y, hy⟩ : ↥(P : Subgroup G)) ∈ H := h ▸ mem_top _
    exact this
  have : Group.IsNilpotent ↥(P : Subgroup G) := IsPGroup.isNilpotent P.isPGroup'
  have hlt := Group.normalizerCondition_of_isNilpotent H (lt_top_iff_ne_top.mpr hHtop)
  obtain ⟨s, hsN, hsH⟩ := IsConcreteLE.exists_of_lt hlt
  have hsT : ∀ t ∈ T₁, (s : G) * t * (s : G)⁻¹ ∈ T₁ := by
    intro t ht
    have ht' : (⟨t, hP ht⟩ : ↥(P : Subgroup G)) ∈ H := ht
    exact ((mem_normalizer_iff.mp hsN _).mp ht')
  have hsW : (s : G) ∈ normalizer (W : Set G) := by
    have hle : rightConjugate W (s : G)⁻¹ ≤ T₁ := by
      intro y hy
      have hy' : (s : G)⁻¹ * y * (s : G) ∈ W := by
        simpa using (mem_rightConjugate_iff W (s : G)⁻¹ y).mp hy
      have e : y = (s : G) * ((s : G)⁻¹ * y * (s : G)) * (s : G)⁻¹ := by group
      rw [e]
      exact hsT _ (hWT hy')
    have h := rightConjugate_eq_of_le hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hC hRWc hRG _ hle
    exact (normalizer (W : Set G)).inv_mem_iff.mp ((rightConjugate_eq_self_iff W _).mp h)
  have hle : T₁ ⊔ zpowers (s : G) ≤ (P : Subgroup G) := sup_le hP (zpowers_le.mpr s.2)
  have heq := hT₁.eq_of_le le_sup_left (sup_le hT₁.le (zpowers_le.mpr hsW))
    (P.isPGroup'.to_le hle)
  have hsT₁ : (s : G) ∈ T₁ := heq ▸ mem_sup_right (mem_zpowers (s : G))
  exact hsH (mem_subgroupOf.mpr hsT₁)

include hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hC hRWc hRG in
theorem false_of_not_stronglyClosed_elem256
    (hns : ∃ w ∈ W, ∃ g : G, g * w * g⁻¹ ∈ T₁ ∧ g * w * g⁻¹ ∉ W) : False := by
  obtain ⟨P, hP⟩ := exists_sylow_eq hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hC hRWc hRG
  have hwc : ∀ h : G, rightConjugate W h ≤ P → rightConjugate W h = W := fun h hh =>
    rightConjugate_eq_of_le hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hC hRWc hRG h (hP ▸ hh)
  have hnsc : ∃ v ∈ W, ∃ h : G, h⁻¹ * v * h ∈ (P : Subgroup G) ∧ h⁻¹ * v * h ∉ W := by
    obtain ⟨w, hw, g, hgT, hgW⟩ := hns
    exact ⟨w, hw, g⁻¹, by simpa [hP] using hgT, by simpa using hgW⟩
  obtain ⟨U, hUW, h, hXP, hXW, hXc⟩ := GoldschmidtFour.goldschmidt_theorem_four_holds G P W
    (hP ▸ hWT) hW hwc hnsc
  set X := rightConjugate U h
  have hXT : X ≤ T₁ := hP ▸ hXP
  obtain ⟨x, hxX, hxW⟩ := IsConcreteLE.not_le_iff_exists.mp hXW
  have hxU : h * x * h⁻¹ ∈ U := (mem_rightConjugate_iff U h x).mp hxX
  have hx2 : x ^ 2 = 1 := by
    have h2 := hW.2 _ (hUW hxU)
    have e : (h * x * h⁻¹) ^ 2 = h * x ^ 2 * h⁻¹ := by
      rw [sq, sq]
      group
    rw [e] at h2
    have e' : x ^ 2 = h⁻¹ * (h * x ^ 2 * h⁻¹) * h := by group
    rw [e', h2]
    group
  have h1 := card_le_card_commutator_mul hW (hT₁.le (hXT hxX))
  have h2 := hC x (hXT hxX) hxW hx2
  rw [hW256] at h1
  have h3 := hXc x hxX
  have h4 := Subgroup.relIndex_mul_card W X
  have h8 : Nat.card X ≤ 8 * Nat.card (X ⊓ W : Subgroup G) :=
    card_le_eight_mul hW hW256 hWT hT₁ h32 hRT hR4 hRW1 hRWc hRG hUW h hXT
  rw [inf_comm] at h4
  have hpos : 0 < Nat.card (X ⊓ W : Subgroup G) := Nat.card_pos
  have hc16 : 16 ≤ Nat.card (⁅W, zpowers x⁆ : Subgroup G) := by
    nlinarith [Nat.mul_le_mul_left (Nat.card (⁅W, zpowers x⁆ : Subgroup G)) h2]
  have h16 : 16 * Nat.card (X ⊓ W : Subgroup G) ≤ Nat.card X := by
    rw [← h4]
    exact Nat.mul_le_mul_right _ (hc16.trans h3)
  omega

end Closure

end CFSG.ComponentClassification.AS81.Sec2
