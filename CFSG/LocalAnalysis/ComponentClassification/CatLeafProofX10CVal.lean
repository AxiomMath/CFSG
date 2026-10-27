module

public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.ClassicalInvolution.SL2Facts

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10CV

open CFSG Subgroup
open scoped commutatorElement

section Val

variable (p : ℕ) [Fact p.Prime]

theorem padicValNat_le_of_dvd' {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← padicValNat_dvd_iff_le hb]
    exact pow_padicValNat_dvd.trans h

variable {G : Type*} [Group G] [Finite G]

theorem nu_le_of_le {X Y : Subgroup G} (h : X ≤ Y) :
    padicValNat p (Nat.card X) ≤ padicValNat p (Nat.card Y) :=
  padicValNat_le_of_dvd' p Nat.card_pos.ne' (card_dvd_of_le h)

theorem nu_sup_add_nu_inf {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) :
    padicValNat p (Nat.card (A ⊔ B : Subgroup G)) +
        padicValNat p (Nat.card (A ⊓ B : Subgroup G)) =
      padicValNat p (Nat.card A) + padicValNat p (Nat.card B) := by
  have h := RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hB
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne',
    ← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h]

theorem nu_add_le {A X M : Subgroup G} (hMAX : M ≤ A ⊔ X)
    (hMN : M ≤ normalizer (X : Set G)) :
    padicValNat p (Nat.card M) + padicValNat p (Nat.card X) ≤
      padicValNat p (Nat.card (A ⊔ X : Subgroup G)) +
        padicValNat p (Nat.card (M ⊓ X : Subgroup G)) := by
  have h1 := nu_sup_add_nu_inf p hMN
  have h3 := nu_le_of_le p (sup_le le_sup_right hMAX : X ⊔ M ≤ A ⊔ X)
  rw [inf_comm] at h1
  omega

theorem nu_map_le {G' : Type*} [Group G'] (f : G →* G') (X : Subgroup G) :
    padicValNat p (Nat.card (X.map f)) ≤ padicValNat p (Nat.card X) :=
  padicValNat_le_of_dvd' p (Nat.card_pos (α := X)).ne' (card_map_dvd X f)

omit [Fact p.Prime] [Finite G] in
theorem nu_map_conj (g : G) (X : Subgroup G) :
    padicValNat p (Nat.card (X.map (MulAut.conj g).toMonoidHom)) =
      padicValNat p (Nat.card X) := by
  rw [card_map_of_injective (MulAut.conj g).injective]

end Val

section Diagonal

variable {G : Type*} [Group G]

theorem conj_mem_map_conj {W : Subgroup G} {t x : G} (hx : x ∈ W) :
    t * x * t⁻¹ ∈ W.map (MulAut.conj t).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem map_conj_map_conj {t : G} (ht : t * t = 1) (W : Subgroup G) :
    (W.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = W := by
  rw [map_map]
  have h : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
    ext x
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht]; group
  rw [h, map_id]

theorem map_conj_eq_of_mem_normalizer {W : Subgroup G} {g : G}
    (hg : g ∈ normalizer (W : Set G)) : W.map (MulAut.conj g).toMonoidHom = W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    rwa [inv_inv] at this

@[expose] def diagHom (t : G) {W : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x) : W →* G where
  toFun x := (x : G) * (t * x * t⁻¹)
  map_one' := by simp
  map_mul' x y := by
    have h1 := hc y y.2 (t * x * t⁻¹) (conj_mem_map_conj x.2)
    simp only [Subgroup.coe_mul]
    calc (x : G) * y * (t * (x * y) * t⁻¹)
        = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
      _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [h1]
      _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group

theorem diagHom_apply (t : G) {W : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x) (x : W) :
    diagHom t hc x = (x : G) * (t * x * t⁻¹) := rfl

theorem exists_eq_mul_diag {t : G} (ht : t * t = 1) {W : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x) {m : G}
    (hmW : m ∈ W ⊔ W.map (MulAut.conj t).toMonoidHom) (hmt : t * m = m * t) :
    ∃ w : W, ∃ c ∈ W ⊓ W.map (MulAut.conj t).toMonoidHom, m = c * diagHom t hc w := by
  set W' := W.map (MulAut.conj t).toMonoidHom with hW'
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcomm : ∀ (x : W) (y : W'), Commute ((W.subtype) x) ((W'.subtype) y) := fun x y =>
    hc x x.2 y y.2
  have hrange := MonoidHom.noncommCoprod_range W.subtype W'.subtype hcomm
  rw [range_subtype, range_subtype] at hrange
  rw [← hrange] at hmW
  obtain ⟨⟨w, w'⟩, hww⟩ := hmW
  simp only [MonoidHom.noncommCoprod_apply, coe_subtype] at hww
  have hu : t * (w : G) * t⁻¹ ∈ W' := conj_mem_map_conj w.2
  have hu' : t * (w' : G) * t⁻¹ ∈ W := by
    have h1 : t * (w' : G) * t⁻¹ ∈ W'.map (MulAut.conj t).toMonoidHom := conj_mem_map_conj w'.2
    have h2 : W'.map (MulAut.conj t).toMonoidHom = W := map_conj_map_conj ht W
    rwa [h2] at h1
  have hfix : (t * (w : G) * t⁻¹) * (t * (w' : G) * t⁻¹) = w * w' := by
    rw [hww]
    calc (t * (w : G) * t⁻¹) * (t * (w' : G) * t⁻¹) = t * (w * w') * t⁻¹ := by group
      _ = t * m * t⁻¹ := by rw [hww]
      _ = m := by rw [hmt]; group
  have hswap := hc _ hu' _ hu
  have hfix' : (t * (w' : G) * t⁻¹) * (t * (w : G) * t⁻¹) = w * w' := by rw [hswap]; exact hfix
  set c := (w : G)⁻¹ * (t * (w' : G) * t⁻¹) with hcdef
  have hc2 : c = (w' : G) * (t * (w : G) * t⁻¹)⁻¹ := by
    calc c = (w : G)⁻¹ * ((t * (w' : G) * t⁻¹) * (t * (w : G) * t⁻¹)) *
            (t * (w : G) * t⁻¹)⁻¹ := by rw [hcdef]; group
      _ = (w : G)⁻¹ * (w * w') * (t * (w : G) * t⁻¹)⁻¹ := by rw [hfix']
      _ = (w' : G) * (t * (w : G) * t⁻¹)⁻¹ := by group
  have hcW : c ∈ W := mul_mem (inv_mem w.2) hu'
  have hcW' : c ∈ W' := by rw [hc2]; exact mul_mem w'.2 (inv_mem hu)
  refine ⟨w, c, mem_inf.mpr ⟨hcW, hcW'⟩, ?_⟩
  rw [diagHom_apply, ← hww]
  have hwc := hc w w.2 c hcW'
  calc (w : G) * w' = w * (c * (t * (w : G) * t⁻¹)) := by rw [hc2]; group
    _ = (w * c) * (t * (w : G) * t⁻¹) := by group
    _ = (c * w) * (t * (w : G) * t⁻¹) := by rw [hwc]
    _ = c * ((w : G) * (t * w * t⁻¹)) := by group

theorem commutatorElement_mul_mul {a b c d : G} (h1 : c * a = a * c) (h2 : c * b = b * c)
    (h3 : c * d = d * c) (h4 : d * a = a * d) (h5 : d * b = b * d) :
    ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have k1 : (c * a) * (d * b) = (a * b) * (c * d) := by
    calc c * a * (d * b) = c * (a * d) * b := by group
      _ = c * (d * a) * b := by rw [h4]
      _ = c * d * (a * b) := by group
      _ = c * (d * a) * b := by group
      _ = c * (a * d) * b := by rw [h4]
      _ = (c * a) * (d * b) := by group
      _ = (a * c) * (d * b) := by rw [h1]
      _ = a * (c * d) * b := by group
      _ = a * (d * c) * b := by rw [h3]
      _ = a * d * (c * b) := by group
      _ = a * d * (b * c) := by rw [h2]
      _ = a * (d * b) * c := by group
      _ = a * (b * d) * c := by rw [h5]
      _ = a * b * (d * c) := by group
      _ = (a * b) * (c * d) := by rw [h3]
  have k2 : (d * b) * (c * a) = (b * a) * (d * c) := by
    calc d * b * (c * a) = d * (b * c) * a := by group
      _ = d * (c * b) * a := by rw [h2]
      _ = (d * c) * (b * a) := by group
      _ = (c * d) * (b * a) := by rw [h3]
      _ = c * (d * b) * a := by group
      _ = c * (b * d) * a := by rw [h5]
      _ = (c * b) * (d * a) := by group
      _ = (b * c) * (d * a) := by rw [h2]
      _ = b * (c * d) * a := by group
      _ = b * (d * c) * a := by rw [h3]
      _ = b * d * (c * a) := by group
      _ = b * d * (a * c) := by rw [h1]
      _ = b * (d * a) * c := by group
      _ = b * (a * d) * c := by rw [h4]
      _ = (b * a) * (d * c) := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc c * a * (d * b) * (c * a)⁻¹ * (d * b)⁻¹ =
        ((c * a) * (d * b)) * ((d * b) * (c * a))⁻¹ := by group
    _ = ((a * b) * (c * d)) * ((b * a) * (d * c))⁻¹ := by rw [k1, k2]
    _ = (a * b) * ((c * d) * (d * c)⁻¹) * (b * a)⁻¹ := by group
    _ = (a * b) * (b * a)⁻¹ := by rw [h3, mul_inv_cancel, mul_one]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem le_range_diagHom {t : G} (ht : t * t = 1) {W M : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hMt : M ≤ centralizer ({t} : Set G))
    (hMW : M ≤ W ⊔ W.map (MulAut.conj t).toMonoidHom) (hMp : ⁅M, M⁆ = M) :
    M ≤ (diagHom t hc).range := by
  set W' := W.map (MulAut.conj t).toMonoidHom with hW'
  have hcent : ∀ c ∈ W ⊓ W', ∀ x : W, c * diagHom t hc x = diagHom t hc x * c := by
    intro c hc' x
    obtain ⟨hcW, hcW'⟩ := mem_inf.mp hc'
    rw [diagHom_apply]
    have h1 := hc x x.2 c hcW'
    have h2 := hc c hcW (t * x * t⁻¹) (conj_mem_map_conj x.2)
    calc c * ((x : G) * (t * x * t⁻¹)) = (c * x) * (t * x * t⁻¹) := by group
      _ = (x * c) * (t * x * t⁻¹) := by rw [h1]
      _ = x * (c * (t * x * t⁻¹)) := by group
      _ = x * ((t * x * t⁻¹) * c) := by rw [h2]
      _ = (x : G) * (t * x * t⁻¹) * c := by group
  have hcc : ∀ c ∈ W ⊓ W', ∀ c' ∈ W ⊓ W', c * c' = c' * c := fun c hc' c' hc'' =>
    hc c (mem_inf.mp hc').1 c' (mem_inf.mp hc'').2
  rw [← hMp, commutator_le]
  intro m₁ hm₁ m₂ hm₂
  have hfix : ∀ m ∈ M, t * m = m * t := fun m hm =>
    (mem_centralizer_singleton_iff.mp (hMt hm)).symm
  obtain ⟨w₁, c₁, hc₁, rfl⟩ := exists_eq_mul_diag ht hc (hMW hm₁) (hfix _ hm₁)
  obtain ⟨w₂, c₂, hc₂, rfl⟩ := exists_eq_mul_diag ht hc (hMW hm₂) (hfix _ hm₂)
  refine ⟨⁅w₁, w₂⁆, ?_⟩
  rw [map_commutatorElement]
  set d₁ := diagHom t hc w₁
  set d₂ := diagHom t hc w₂
  have e1 := hcent c₁ hc₁ w₁
  have e2 := hcent c₁ hc₁ w₂
  have e3 := hcent c₂ hc₂ w₁
  have e4 := hcent c₂ hc₂ w₂
  have e5 := hcc c₁ hc₁ c₂ hc₂
  exact (commutatorElement_mul_mul e1 e2 e5 e3 e4).symm

theorem nu_le_of_diag [Finite G] (p : ℕ) [Fact p.Prime] {t : G} {W M : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hM : M ≤ (diagHom t hc).range) :
    padicValNat p (Nat.card M) ≤ padicValNat p (Nat.card W) :=
  padicValNat_le_of_dvd' p Nat.card_pos.ne'
    ((card_dvd_of_le hM).trans (card_range_dvd (diagHom t hc)))

theorem commute_of_mem_inf {t : G} {W M X : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hM : M ≤ (diagHom t hc).range) (hMW : M ≤ W ⊔ W.map (MulAut.conj t).toMonoidHom)
    (hXW : X ≤ centralizer (W : Set G)) (hWX : W.map (MulAut.conj t).toMonoidHom ≤ X)
    {m : G} (hm : m ∈ M ⊓ X) {m' : G} (hm' : m' ∈ M) : m * m' = m' * m := by
  obtain ⟨hmM, hmX⟩ := mem_inf.mp hm
  obtain ⟨w, hw⟩ := hM hmM
  rw [diagHom_apply] at hw
  have hwX : (w : G) ∈ X := by
    have h1 : (w : G) = m * (t * w * t⁻¹)⁻¹ := by rw [← hw]; group
    rw [h1]
    exact mul_mem hmX (inv_mem (hWX (conj_mem_map_conj w.2)))
  have hwc : ∀ y ∈ W, (w : G) * y = y * w := fun y hy =>
    (mem_centralizer_iff.mp (hXW hwX) y hy).symm
  have hC : W ⊔ W.map (MulAut.conj t).toMonoidHom ≤ centralizer ({m} : Set G) := by
    refine sup_le (fun y hy => ?_) ?_
    · rw [mem_centralizer_singleton_iff, ← hw]
      have h1 := hc y hy (t * w * t⁻¹) (conj_mem_map_conj w.2)
      calc y * ((w : G) * (t * w * t⁻¹)) = (y * w) * (t * w * t⁻¹) := by group
        _ = (w * y) * (t * w * t⁻¹) := by rw [hwc y hy]
        _ = w * (y * (t * w * t⁻¹)) := by group
        _ = w * ((t * w * t⁻¹) * y) := by rw [h1]
        _ = (w : G) * (t * w * t⁻¹) * y := by group
    · rintro _ ⟨y, hy, rfl⟩
      show t * y * t⁻¹ ∈ centralizer ({m} : Set G)
      rw [mem_centralizer_singleton_iff, ← hw]
      have h1 := hc w w.2 (t * y * t⁻¹) (conj_mem_map_conj hy)
      have h2 : (t * w * t⁻¹) * (t * y * t⁻¹) = (t * y * t⁻¹) * (t * w * t⁻¹) := by
        calc (t * (w : G) * t⁻¹) * (t * y * t⁻¹) = t * (w * y) * t⁻¹ := by group
          _ = t * (y * w) * t⁻¹ := by rw [hwc y hy]
          _ = (t * y * t⁻¹) * (t * w * t⁻¹) := by group
      calc t * y * t⁻¹ * ((w : G) * (t * w * t⁻¹))
          = ((t * y * t⁻¹) * w) * (t * w * t⁻¹) := by group
        _ = (w * (t * y * t⁻¹)) * (t * w * t⁻¹) := by rw [h1]
        _ = w * ((t * y * t⁻¹) * (t * w * t⁻¹)) := by group
        _ = w * ((t * w * t⁻¹) * (t * y * t⁻¹)) := by rw [h2]
        _ = (w : G) * (t * w * t⁻¹) * (t * y * t⁻¹) := by group
  exact (mem_centralizer_singleton_iff.mp (hC (hMW hm'))).symm

end Diagonal

section Center

theorem nu_center_le_one {J : Type*} [Group J] [Finite J] {K : Type*} [Field K] [Finite K]
    (e : J ⧸ pPrimeCore 2 J ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    padicValNat 2 (Nat.card (center J)) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : J →* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 J)) with hφ
  have hφs : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  set ψ := φ.subgroupMap (center J) with hψ
  have h1 := card_ker_mul_card_of_surjective (φ.subgroupMap_surjective (center J))
  have hker : padicValNat 2 (Nat.card ψ.ker) = 0 := by
    let ι : ψ.ker →* pPrimeCore 2 J :=
      { toFun := fun x => ⟨((x : center J) : J), by
          have hx : ψ (x : center J) = 1 := MonoidHom.mem_ker.mp x.2
          have hx2 : e (QuotientGroup.mk' (pPrimeCore 2 J) ((x : center J) : J)) = 1 := by
            have h := congrArg Subtype.val hx
            exact h
          rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx2
          exact hx2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y hxy => by
      have h1 : ((ι x : pPrimeCore 2 J) : J) = ι y := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    have hdvd := card_dvd_of_injective ι hι
    have hodd : ¬ 2 ∣ Nat.card ψ.ker := fun h2 =>
      (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := J))
        (h2.trans hdvd)
    exact padicValNat.eq_zero_of_not_dvd hodd
  have himg : (center J).map φ ≤ zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) K) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzc : φ z ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hφs g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) x]
    rcases (ClassicalInvolution.mem_center_sl2_iff (φ z)).mp hzc with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  have hord : Nat.card (zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) K)) ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two, neg_mul_neg, mul_one])
  have h2 : padicValNat 2 (Nat.card ((center J).map φ)) ≤ 1 := by
    have h3 := padicValNat_le_of_dvd' 2 (by norm_num) ((card_dvd_of_le himg).trans hord)
    rwa [padicValNat_self] at h3
  rw [← h1, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hker, zero_add]
  exact h2

end Center

end CFSG.ComponentClassification.CatLeafProof.X10CV
