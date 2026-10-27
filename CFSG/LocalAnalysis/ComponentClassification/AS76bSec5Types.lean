module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Coord
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

variable {V : Type} [AddCommGroup V] {X : Type} [Group X] [DistribMulAction X V]

section Img

theorem mem_img {x : X} {T : AddSubgroup V} {v : V} : v ∈ img x T ↔ ∃ t ∈ T, x • t = v := by
  simp [img, AddSubgroup.mem_map]

theorem smul_mem_img {x : X} {T : AddSubgroup V} {t : V} (ht : t ∈ T) : x • t ∈ img x T :=
  mem_img.2 ⟨t, ht, rfl⟩

theorem mem_img_iff_inv_smul {x : X} {T : AddSubgroup V} {v : V} :
    v ∈ img x T ↔ x⁻¹ • v ∈ T := by
  rw [mem_img]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · intro hv
    exact ⟨x⁻¹ • v, hv, by simp⟩

theorem img_mul (x y : X) (T : AddSubgroup V) : img (x * y) T = img x (img y T) := by
  ext v
  simp only [mem_img_iff_inv_smul, mul_inv_rev, mul_smul]

theorem img_one (T : AddSubgroup V) : img (1 : X) T = T := by
  ext v
  simp [mem_img_iff_inv_smul]

theorem img_inv_img (x : X) (T : AddSubgroup V) : img x⁻¹ (img x T) = T := by
  rw [← img_mul, inv_mul_cancel, img_one]

theorem img_img_inv (x : X) (T : AddSubgroup V) : img x (img x⁻¹ T) = T := by
  rw [← img_mul, mul_inv_cancel, img_one]

theorem img_le_img {x : X} {S T : AddSubgroup V} (hST : S ≤ T) : img x S ≤ img x T :=
  AddSubgroup.map_mono hST

theorem img_le_img_iff {x : X} {S T : AddSubgroup V} : img x S ≤ img x T ↔ S ≤ T :=
  ⟨fun hST => by simpa [img_inv_img] using img_le_img (x := x⁻¹) hST, img_le_img⟩

theorem img_inf (x : X) (S T : AddSubgroup V) : img x (S ⊓ T) = img x S ⊓ img x T := by
  ext v
  simp only [mem_img_iff_inv_smul, AddSubgroup.mem_inf]

theorem img_sup (x : X) (S T : AddSubgroup V) : img x (S ⊔ T) = img x S ⊔ img x T :=
  AddSubgroup.map_sup _ _ _

theorem img_bot (x : X) : img x (⊥ : AddSubgroup V) = ⊥ :=
  AddSubgroup.map_bot _

theorem img_injective (x : X) : Function.Injective (img (V := V) x) := fun S T hST => by
  rw [← img_inv_img x S, hST, img_inv_img]

theorem card_img (x : X) (T : AddSubgroup V) : Nat.card (img x T) = Nat.card T :=
  AddSubgroup.card_map_of_injective (f := DistribSMul.toAddMonoidHom V x)
    (fun a b hab => by simpa using hab)

theorem img_eq_self_of_fix {x : X} {T : AddSubgroup V} (hx : ∀ t ∈ T, x • t = t) :
    img x T = T := by
  ext v
  rw [mem_img]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rwa [hx t ht]
  · intro hv
    exact ⟨v, hv, hx v hv⟩

end Img

section Members

variable {R : AddSubgroup V}

theorem self_mem_members : R ∈ members X R := ⟨1, img_one R⟩

theorem img_mem_members {T : AddSubgroup V} (hT : T ∈ members X R) (x : X) :
    img x T ∈ members X R := by
  obtain ⟨y, rfl⟩ := hT
  exact ⟨x * y, img_mul x y R⟩

theorem card_of_mem_members {T : AddSubgroup V} (hT : T ∈ members X R) :
    Nat.card T = Nat.card R := by
  obtain ⟨x, rfl⟩ := hT
  exact card_img x R

theorem mem_fused_iff {v : V} : v ∈ fused X R ↔ v ≠ 0 ∧ ∃ T ∈ members X R, v ∈ T := by
  constructor
  · rintro ⟨x, r, hr, hr0, rfl⟩
    refine ⟨fun h0 => hr0 ?_, img x R, ⟨x, rfl⟩, smul_mem_img hr⟩
    simpa using congrArg (x⁻¹ • ·) h0
  · rintro ⟨hv, T, ⟨x, rfl⟩, hvT⟩
    obtain ⟨r, hr, rfl⟩ := mem_img.1 hvT
    exact ⟨x, r, hr, fun h0 => hv (by rw [h0, smul_zero]), rfl⟩

theorem smul_mem_fused {v : V} (hv : v ∈ fused X R) (x : X) : x • v ∈ fused X R := by
  obtain ⟨y, r, hr, hr0, rfl⟩ := hv
  exact ⟨x * y, r, hr, hr0, mul_smul x y r⟩

theorem mem_fused_of_mem {r : V} (hr : r ∈ R) (h0 : r ≠ 0) : r ∈ fused X R :=
  ⟨1, r, hr, h0, one_smul X r⟩

end Members

theorem not_mem_of_inf_eq_bot {S T : AddSubgroup V} (hST : T ⊓ S = ⊥) {t : V} (ht : t ∈ T)
    (ht0 : t ≠ 0) : t ∉ S := fun htS => by
  have hmem : t ∈ T ⊓ S := AddSubgroup.mem_inf.2 ⟨ht, htS⟩
  rw [hST, AddSubgroup.mem_bot] at hmem
  exact ht0 hmem

theorem add_eq_add_swap (two : ∀ v : V, v + v = 0) {a b c d : V} (h : a + b = c + d) :
    b + d = a + c := by
  have hneg : -a = a := neg_eq_of_add_eq_zero_left (two a)
  calc b + d = (a + b) - a + d := by abel
    _ = (c + d) - a + d := by rw [h]
    _ = c - a + (d + d) := by abel
    _ = a + c := by rw [two d, add_zero, sub_eq_add_neg, hneg, add_comm]

theorem eq_of_add_eq_zero (two : ∀ v : V, v + v = 0) {a b : V} (h : a + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_left h, neg_eq_of_add_eq_zero_left (two b)]

theorem card_eq_two_pow [Finite V] (two : ∀ v : V, v + v = 0) (H : AddSubgroup V) :
    ∃ k : ℕ, Nat.card H = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Multiplicative H) := inferInstanceAs (Finite H)
  have hp : IsPGroup 2 (Multiplicative H) := by
    refine fun g => ⟨1, ?_⟩
    rw [pow_one, sq]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact Subtype.ext (two _)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  exact ⟨n, hn⟩

theorem four_dvd_of_two_pow {n k : ℕ} (hn : n = 2 ^ k) (h2 : 2 < n) : 4 ∣ n := by
  subst hn
  rcases k with _ | _ | k
  · simp at h2
  · simp at h2
  · exact ⟨2 ^ k, by ring⟩

namespace Hyp51

variable {A B : Subgroup X} {R U W : AddSubgroup V} (h : Hyp51 X A B R U W)
include h

theorem inf_eq_bot {S T : AddSubgroup V} (hS : S ∈ members X R) (hT : T ∈ members X R)
    (hST : S ≠ T) : S ⊓ T = ⊥ := by
  obtain ⟨x, rfl⟩ := hS
  have h1 : img x⁻¹ T ∈ members X R := img_mem_members hT x⁻¹
  have h2 : img x⁻¹ T ≠ R := fun he => hST (by rw [← he, img_img_inv])
  have h4 := congrArg (img x) (h.one _ h1 h2).1
  rw [img_inf, img_img_inv, img_bot] at h4
  rw [inf_comm]
  exact h4

theorem eq_of_mem_of_mem {S T : AddSubgroup V} (hS : S ∈ members X R) (hT : T ∈ members X R)
    {v : V} (hvS : v ∈ S) (hvT : v ∈ T) (hv : v ≠ 0) : S = T := by
  by_contra hne
  exact not_mem_of_inf_eq_bot (h.inf_eq_bot hS hT hne) hvS hv hvT

theorem eq_of_add_eq_zero' {a b : V} (hab : a + b = 0) : a = b :=
  eq_of_add_eq_zero h.two hab

theorem A_smul {a : X} (ha : a ∈ A) (v : V) :
    a • v = (h.decomp.cR v : V) + h.decomp.cU v + a • (h.decomp.cW v : V) := by
  conv_lhs => rw [← h.decomp.coord_sum v]
  rw [smul_add, h.A_fix a ha _ (AddSubgroup.add_mem_sup (h.decomp.cR v).2 (h.decomp.cU v).2)]

theorem B_smul {b : X} (hb : b ∈ B) (v : V) :
    b • v = (h.decomp.cR v : V) + b • (h.decomp.cU v : V) + h.decomp.cW v := by
  conv_lhs => rw [← h.decomp.coord_sum v, add_right_comm]
  rw [smul_add, h.B_fix b hb _ (AddSubgroup.add_mem_sup (h.decomp.cR v).2 (h.decomp.cW v).2),
    add_right_comm]

theorem AB_smul {a b : X} (ha : a ∈ A) (hb : b ∈ B) (v : V) :
    (a * b) • v = (h.decomp.cR v : V) + b • (h.decomp.cU v : V) + a • (h.decomp.cW v : V) := by
  have hbU : b • (h.decomp.cU v : V) ∈ U := h.B_U b hb _ (h.decomp.cU v).2
  rw [mul_smul, h.B_smul hb v, smul_add, smul_add,
    h.A_fix a ha _ (AddSubgroup.mem_sup_left (h.decomp.cR v).2),
    h.A_fix a ha _ (AddSubgroup.mem_sup_right hbU)]

theorem cR_AB_smul {a b : X} (ha : a ∈ A) (hb : b ∈ B) (v : V) :
    (h.decomp.cR ((a * b) • v) : V) = h.decomp.cR v := by
  rw [h.AB_smul ha hb v]
  exact h.decomp.cR_sum (h.decomp.cR v).2 (h.B_U b hb _ (h.decomp.cU v).2)
    (h.A_W a ha _ (h.decomp.cW v).2)

theorem cU_AB_smul {a b : X} (ha : a ∈ A) (hb : b ∈ B) (v : V) :
    (h.decomp.cU ((a * b) • v) : V) = b • (h.decomp.cU v : V) := by
  rw [h.AB_smul ha hb v]
  exact h.decomp.cU_sum (h.decomp.cR v).2 (h.B_U b hb _ (h.decomp.cU v).2)
    (h.A_W a ha _ (h.decomp.cW v).2)

theorem cW_AB_smul {a b : X} (ha : a ∈ A) (hb : b ∈ B) (v : V) :
    (h.decomp.cW ((a * b) • v) : V) = a • (h.decomp.cW v : V) := by
  rw [h.AB_smul ha hb v]
  exact h.decomp.cW_sum (h.decomp.cR v).2 (h.B_U b hb _ (h.decomp.cU v).2)
    (h.A_W a ha _ (h.decomp.cW v).2)

variable [Finite V]

theorem four_dvd_card_R : 4 ∣ Nat.card R := by
  obtain ⟨k, hk⟩ := card_eq_two_pow h.two R
  exact four_dvd_of_two_pow hk h.two_lt

theorem card_R_le_card_U : Nat.card R ≤ Nat.card U := by
  obtain ⟨T, hT, -, -, hTW⟩ := h.three
  rw [← card_of_mem_members hT]
  refine Nat.card_le_card_of_injective (fun t : T => h.decomp.cU t) fun t t' htt' => ?_
  have htt'' : h.decomp.cU t = h.decomp.cU t' := htt'
  have hsum : h.decomp.cU ((t : V) + t') = 0 := by
    rw [h.decomp.cU_add, htt'']
    exact Subtype.ext (h.two _)
  rw [h.decomp.cU_eq_zero_iff] at hsum
  have hmem : (t : V) + t' ∈ T ⊓ (R ⊔ W) := AddSubgroup.mem_inf.2 ⟨T.add_mem t.2 t'.2, hsum⟩
  rw [hTW, AddSubgroup.mem_bot] at hmem
  exact Subtype.ext (h.eq_of_add_eq_zero' hmem)

theorem two_lt_card_U : 2 < Nat.card U := lt_of_lt_of_le h.two_lt h.card_R_le_card_U

theorem two_lt_card_W : 2 < Nat.card W := h.card_eq ▸ h.two_lt_card_U

theorem four_dvd_card_U : 4 ∣ Nat.card U := by
  obtain ⟨k, hk⟩ := card_eq_two_pow h.two U
  exact four_dvd_of_two_pow hk h.two_lt_card_U

omit [Finite V] in
theorem cU_cW_ne_zero {T : AddSubgroup V} (hTU : T ⊓ (R ⊔ U) = ⊥) (hTW : T ⊓ (R ⊔ W) = ⊥)
    {y : V} (hy : y ∈ T) (hy0 : y ≠ 0) : h.decomp.cU y ≠ 0 ∧ h.decomp.cW y ≠ 0 :=
  ⟨fun h0 => not_mem_of_inf_eq_bot hTW hy hy0 ((h.decomp.cU_eq_zero_iff y).1 h0),
    fun h0 => not_mem_of_inf_eq_bot hTU hy hy0 ((h.decomp.cW_eq_zero_iff y).1 h0)⟩

theorem le_UW {T : AddSubgroup V} (hT : T ∈ members X R) (hTU : T ⊓ (R ⊔ U) = ⊥)
    (hTW : T ⊓ (R ⊔ W) = ⊥) {t : V} (ht : t ∈ T) (ht0 : t ≠ 0) (htUW : t ∈ U ⊔ W) :
    T ≤ U ⊔ W := by
  set hd := h.decomp
  by_contra hle
  obtain ⟨s, hs, hsUW⟩ := IsConcreteLE.not_le_iff_exists.1 hle
  have hs0 : s ≠ 0 := fun h0 => hsUW (h0 ▸ zero_mem _)
  have hst : s + t ∈ T := T.add_mem hs ht
  have hst0 : s + t ≠ 0 := fun h0 => hsUW (h.eq_of_add_eq_zero' h0 ▸ htUW)
  obtain ⟨hsU, hsW⟩ := h.cU_cW_ne_zero hTU hTW hs hs0
  obtain ⟨hstU, hstW⟩ := h.cU_cW_ne_zero hTU hTW hst hst0
  obtain ⟨b, hb, hbs⟩ := h.B_trans _ (hd.cU s).2 _ (hd.cU (s + t)).2
    (by simpa using hsU) (by simpa using hstU)
  obtain ⟨a, ha, has⟩ := h.A_trans _ (hd.cW s).2 _ (hd.cW (s + t)).2
    (by simpa using hsW) (by simpa using hstW)
  have hRt : hd.cR t = 0 := (hd.cR_eq_zero_iff t).2 htUW
  have hgs : (a * b) • s = s + t := by
    rw [h.AB_smul ha hb s, hbs, has]
    conv_rhs => rw [← hd.coord_sum (s + t)]
    rw [hd.cR_add, hRt, add_zero]
  have hstg : s + t ∈ img (a * b) T := by
    rw [← hgs]
    exact smul_mem_img hs
  have hgT : img (a * b) T = T := h.eq_of_mem_of_mem (img_mem_members hT _) hT hstg hst hst0
  have hgTmem : ∀ y ∈ T, (a * b) • y ∈ T := fun y hy => by
    rw [← hgT]
    exact smul_mem_img hy
  have hfix : ∀ y ∈ T, (a * b) • y = y → y = 0 := by
    intro y hy hgy
    by_contra hy0
    obtain ⟨hyU, hyW⟩ := h.cU_cW_ne_zero hTU hTW hy hy0
    have hU' : b • (hd.cU y : V) = hd.cU y := by
      rw [← h.cU_AB_smul ha hb y, hgy]
    have hW' : a • (hd.cW y : V) = hd.cW y := by
      rw [← h.cW_AB_smul ha hb y, hgy]
    have hafix := h.A_free a ha _ (hd.cW y).2 (by simpa using hyW) hW'
    have hbfix := h.B_free b hb _ (hd.cU y).2 (by simpa using hyU) hU'
    have hss : (a * b) • s = s := by
      rw [h.AB_smul ha hb s, hafix _ (hd.cW s).2, hbfix _ (hd.cU s).2, hd.coord_sum]
    rw [hgs] at hss
    exact ht0 (by simpa using hss)
  let τ : T → T := fun y => ⟨y + (a * b) • (y : V), T.add_mem y.2 (hgTmem _ y.2)⟩
  have hτ : Function.Injective τ := by
    intro y₁ y₂ he
    have he' : (y₁ : V) + (a * b) • (y₁ : V) = y₂ + (a * b) • (y₂ : V) :=
      congrArg Subtype.val he
    have hfixed : (a * b) • ((y₁ : V) + y₂) = y₁ + y₂ := by
      rw [smul_add]
      exact add_eq_add_swap h.two he'
    exact Subtype.ext (h.eq_of_add_eq_zero' (hfix _ (T.add_mem y₁.2 y₂.2) hfixed))
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hτ ⟨s, hs⟩
  apply hsUW
  have hsy : s = y + (a * b) • (y : V) := (congrArg Subtype.val hy).symm
  rw [hsy, ← hd.cR_eq_zero_iff, hd.cR_add]
  have hR : hd.cR ((a * b) • (y : V)) = hd.cR y := Subtype.ext (h.cR_AB_smul ha hb y)
  rw [hR]
  exact Subtype.ext (h.two _)

theorem member_cases {T : AddSubgroup V} (hT : T ∈ members X R) :
    T = R ∨ T = U ∨ T = W ∨ (T ≤ R ⊔ U ∧ T ⊓ R = ⊥ ∧ T ⊓ U = ⊥) ∨
      (T ≤ R ⊔ W ∧ T ⊓ R = ⊥ ∧ T ⊓ W = ⊥) ∨
      (T ≤ U ⊔ W ∧ T ⊓ (R ⊔ U) = ⊥ ∧ T ⊓ (R ⊔ W) = ⊥) ∨
      (T ⊓ (U ⊔ W) = ⊥ ∧ T ⊓ (R ⊔ U) = ⊥ ∧ T ⊓ (R ⊔ W) = ⊥) := by
  by_cases hR : T = R
  · exact Or.inl hR
  obtain ⟨hTR, hcase⟩ := h.one T hT hR
  rcases hcase with hU | hW | ⟨hTU, hTW⟩
  · rcases h.twoU T hT hU with ⟨rfl, -⟩ | hTU
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hU, hTR, hTU⟩)))
  · rcases h.twoW T hT hW with ⟨rfl, -⟩ | hTW
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hW, hTR, hTW⟩))))
  · rcases (T ⊓ (U ⊔ W)).bot_or_exists_ne_zero with hUW | ⟨t, htUW, ht0⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hUW, hTU, hTW⟩)))))
    · obtain ⟨ht, htUW⟩ := AddSubgroup.mem_inf.1 htUW
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h.le_UW hT hTU hTW ht ht0 htUW, hTU, hTW⟩)))))

theorem pat_uniform {T : AddSubgroup V} (hT : T ∈ members X R) :
    ∃ p, ∀ t ∈ T, t ≠ 0 → h.decomp.pat t = p := by
  set hd := h.decomp
  have key : ∀ (P₁ P₂ P₃ : Prop) (_ : ∀ t ∈ T, t ≠ 0 →
      ((hd.cR t ≠ 0 ↔ P₁) ∧ (hd.cU t ≠ 0 ↔ P₂) ∧ (hd.cW t ≠ 0 ↔ P₃))),
      ∃ p, ∀ t ∈ T, t ≠ 0 → hd.pat t = p := by
    intro P₁ P₂ P₃ hP
    classical
    refine ⟨(decide P₁, decide P₂, decide P₃), fun t ht ht0 => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hP t ht ht0
    simp only [Decomp.pat, Prod.mk.injEq, nz, decide_eq_decide]
    exact ⟨h1, h2, h3⟩
  have hR0 : ∀ t : V, t ≠ 0 → hd.cU t = 0 → hd.cW t = 0 → hd.cR t ≠ 0 := by
    intro t ht0 h2 h3 h1
    exact ht0 (by rw [← hd.coord_sum t, h1, h2, h3]; simp)
  have hU0 : ∀ t : V, t ≠ 0 → hd.cR t = 0 → hd.cW t = 0 → hd.cU t ≠ 0 := by
    intro t ht0 h1 h3 h2
    exact ht0 (by rw [← hd.coord_sum t, h1, h2, h3]; simp)
  have hW0 : ∀ t : V, t ≠ 0 → hd.cR t = 0 → hd.cU t = 0 → hd.cW t ≠ 0 := by
    intro t ht0 h1 h2 h3
    exact ht0 (by rw [← hd.coord_sum t, h1, h2, h3]; simp)
  rcases h.member_cases hT with rfl | rfl | rfl | ⟨hle, hTR, hTU⟩ | ⟨hle, hTR, hTW⟩ |
      ⟨hle, hTU, hTW⟩ | ⟨hUW, hTU, hTW⟩
  · refine key True False False fun t ht ht0 => ?_
    obtain ⟨h2, h3⟩ := (hd.mem_R_iff t).1 ht
    exact ⟨iff_true_intro (hR0 t ht0 h2 h3), by simp [h2], by simp [h3]⟩
  · refine key False True False fun t ht ht0 => ?_
    obtain ⟨h1, h3⟩ := (hd.mem_U_iff t).1 ht
    exact ⟨by simp [h1], iff_true_intro (hU0 t ht0 h1 h3), by simp [h3]⟩
  · refine key False False True fun t ht ht0 => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_W_iff t).1 ht
    exact ⟨by simp [h1], by simp [h2], iff_true_intro (hW0 t ht0 h1 h2)⟩
  · refine key True True False fun t ht ht0 => ?_
    have h3 : hd.cW t = 0 := (hd.cW_eq_zero_iff t).2 (hle ht)
    have hnU := not_mem_of_inf_eq_bot hTU ht ht0
    have hnR := not_mem_of_inf_eq_bot hTR ht ht0
    refine ⟨iff_true_intro fun h1 => hnU ((hd.mem_U_iff t).2 ⟨h1, h3⟩),
      iff_true_intro fun h2 => hnR ((hd.mem_R_iff t).2 ⟨h2, h3⟩), by simp [h3]⟩
  · refine key True False True fun t ht ht0 => ?_
    have h2 : hd.cU t = 0 := (hd.cU_eq_zero_iff t).2 (hle ht)
    have hnW := not_mem_of_inf_eq_bot hTW ht ht0
    have hnR := not_mem_of_inf_eq_bot hTR ht ht0
    refine ⟨iff_true_intro fun h1 => hnW ((hd.mem_W_iff t).2 ⟨h1, h2⟩), by simp [h2],
      iff_true_intro fun h3 => hnR ((hd.mem_R_iff t).2 ⟨h2, h3⟩)⟩
  · refine key False True True fun t ht ht0 => ?_
    have h1 : hd.cR t = 0 := (hd.cR_eq_zero_iff t).2 (hle ht)
    obtain ⟨h2, h3⟩ := h.cU_cW_ne_zero hTU hTW ht ht0
    exact ⟨by simp [h1], iff_true_intro h2, iff_true_intro h3⟩
  · refine key True True True fun t ht ht0 => ?_
    obtain ⟨h2, h3⟩ := h.cU_cW_ne_zero hTU hTW ht ht0
    exact ⟨iff_true_intro fun h1 => not_mem_of_inf_eq_bot hUW ht ht0
      ((hd.cR_eq_zero_iff t).1 h1), iff_true_intro h2, iff_true_intro h3⟩

end Hyp51

end CFSG.ComponentClassification.AS76b.Sec5
