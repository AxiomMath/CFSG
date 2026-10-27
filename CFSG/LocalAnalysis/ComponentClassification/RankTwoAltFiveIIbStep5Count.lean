module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep56
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbX

public section

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace IIbSyl

@[expose] def elems : List IIbSyl :=
  ((List.finRange 4 ×ˢ List.finRange 4) ×ˢ ((List.finRange 2 ×ˢ List.finRange 2) ×ˢ
    List.finRange 2)).map fun x =>
      ⟨⟨Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2.1⟩, Multiplicative.ofAdd x.2.2⟩

theorem mem_elems (s : IIbSyl) : s ∈ elems :=
  List.mem_map.mpr ⟨(((Multiplicative.toAdd s.left.left).1, (Multiplicative.toAdd s.left.left).2),
    (((Multiplicative.toAdd s.left.right).1, (Multiplicative.toAdd s.left.right).2),
      Multiplicative.toAdd s.right)),
    List.mem_product.mpr ⟨List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩,
      List.mem_product.mpr ⟨List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩,
        List.mem_finRange _⟩⟩, rfl⟩

@[expose] def checkCentE1 : Bool :=
  elems.all fun m => decide (chi m = 1 → m * vv = vv * m → m * c1 = c1 * m →
    m ∈ [1, z0, vv, z0 * vv, c1, z0 * c1, vv * c1, z0 * vv * c1])

theorem checkCentE1_eq : checkCentE1 = true := by
  decide +kernel

@[expose] def checkConjVV : Bool :=
  elems.all fun m => decide (chi m = 1 → m * vv ≠ c1 * m ∧ m * vv ≠ z0 * c1 * m)

theorem checkConjVV_eq : checkConjVV = true := by
  decide +kernel

theorem mem_of_centE1 {m : IIbSyl} (h1 : chi m = 1) (h2 : m * vv = vv * m)
    (h3 : m * c1 = c1 * m) : m ∈ [1, z0, vv, z0 * vv, c1, z0 * c1, vv * c1, z0 * vv * c1] :=
  of_decide_eq_true (List.all_eq_true.mp checkCentE1_eq m (mem_elems m)) h1 h2 h3

theorem conj_vv_ne {m : IIbSyl} (h1 : chi m = 1) : m * vv ≠ c1 * m ∧ m * vv ≠ z0 * c1 * m :=
  of_decide_eq_true (List.all_eq_true.mp checkConjVV_eq m (mem_elems m)) h1

theorem step5_rels : z0 * z0 = 1 ∧ vv * vv = 1 ∧ c1 * c1 = 1 ∧ z0 * vv = vv * z0 ∧
    z0 * c1 = c1 * z0 ∧ vv * c1 = c1 * vv ∧ z0 ≠ 1 ∧ vv ≠ 1 ∧ vv ≠ z0 ∧ c1 ≠ 1 ∧ c1 ≠ z0 ∧
    c1 ≠ vv ∧ c1 ≠ z0 * vv ∧ sigma * z0 = z0 * sigma ∧ sigma * vv = vv * sigma ∧
    chi c1 = 1 := by
  decide

end IIbSyl

section Count

variable {G : Type*} [Group G]

theorem card_le_length_mul_card_inf_centralizer {K : Subgroup G} {y : G} {l : List G}
    (hl : ∀ k ∈ K, k * y * k⁻¹ ∈ l) :
    Nat.card K ≤ l.length * Nat.card ↥(K ⊓ centralizer ({y} : Set G)) := by
  classical
  let _ : MulAction K G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp K.subtype)
  have hsmul : ∀ (x : K) (u : G), x • u = (x : G) * u * (x : G)⁻¹ := fun x u =>
    ConjAct.toConjAct_smul (x : G) u
  have hstab : MulAction.stabilizer K y = (centralizer {y}).subgroupOf K := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
  have horb : MulAction.orbit K y ⊆ (l.toFinset : Set G) := by
    rintro _ ⟨x, rfl⟩
    change x • y ∈ _
    rw [hsmul, Finset.mem_coe, List.mem_toFinset]
    exact hl x x.2
  have h := (MulAction.stabilizer K y).index_mul_card
  rw [MulAction.index_stabilizer, hstab, ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  rw [← h]
  refine Nat.mul_le_mul_right _ ((Set.ncard_le_ncard horb (Finset.finite_toSet _)).trans ?_)
  rw [Set.ncard_coe_finset]
  exact List.toFinset_card_le l

theorem card_le_length {H : Subgroup G} {l : List G} (hl : ∀ y ∈ H, y ∈ l) :
    Nat.card H ≤ l.length := by
  classical
  rw [show Nat.card H = (H : Set G).ncard from Nat.card_coe_set_eq _]
  refine (Set.ncard_le_ncard (t := (l.toFinset : Set G)) (fun y hy => ?_)
    (Finset.finite_toSet _)).trans ?_
  · rw [Finset.mem_coe, List.mem_toFinset]
    exact hl y hy
  · rw [Set.ncard_coe_finset]
    exact List.toFinset_card_le l

theorem eq_of_conj_eq_of_commute {k u y : G} (hku : k * u = u * k) (e : k * y * k⁻¹ = u) :
    y = u :=
  calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
    _ = k⁻¹ * u * k := by rw [e]
    _ = u := by rw [mul_assoc, ← hku, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_normalizer_centralizer {E : Subgroup G} {h : G}
    (hh : h ∈ normalizer (E : Set G)) : h ∈ normalizer (centralizer (E : Set G) : Set G) := by
  rw [mem_normalizer_iff] at hh ⊢
  intro y
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hy e he
    have h1 := hy (h⁻¹ * e * h) ((hh _).mpr (by rwa [show h * (h⁻¹ * e * h) * h⁻¹ = e by group]))
    calc e * (h * y * h⁻¹) = h * ((h⁻¹ * e * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * e * h)) * h⁻¹ := by rw [h1]
      _ = h * y * h⁻¹ * e := by group
  · intro hy e he
    have h1 := hy (h * e * h⁻¹) ((hh e).mp he)
    calc e * y = h⁻¹ * ((h * e * h⁻¹) * (h * y * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * y * h⁻¹) * (h * e * h⁻¹)) * h := by rw [h1]
      _ = y * e := by group

end Count

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_le_of_le_of_le_normalizer {L H : Subgroup G} (hLH : L ≤ H)
    (hHL : H ≤ normalizer (L : Set G)) : oddCoreIn L ≤ oddCoreIn H := by
  have hOH : oddCoreIn L ≤ H := (oddCoreIn_le L).trans hLH
  have hle := le_assemblyOddCore ((normal_subgroupOf_iff_le_normalizer hOH).mpr
    (hHL.trans (normalizer_le_normalizer_oddCoreIn L)))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hOH).toEquiv]; exact odd_card_oddCoreIn L)
  intro x hx
  exact ⟨⟨x, hOH hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

end OddCore

section E₁

variable {G : Type*} [Group G]

structure E₁Gens (V₀ : Subgroup G) (z₀ v c₁ : G) : Prop where
  z_mem : z₀ ∈ V₀
  v_mem : v ∈ V₀
  cases : ∀ e ∈ V₀, e = 1 ∨ e = z₀ ∨ e = v ∨ e = z₀ * v
  z_sq : z₀ * z₀ = 1
  v_sq : v * v = 1
  c_sq : c₁ * c₁ = 1
  zv : z₀ * v = v * z₀
  zc : z₀ * c₁ = c₁ * z₀
  vc : v * c₁ = c₁ * v
  z_ne : z₀ ≠ 1
  v_ne : v ≠ 1 ∧ v ≠ z₀
  c_ne : c₁ ≠ 1 ∧ c₁ ≠ z₀ ∧ c₁ ≠ v ∧ c₁ ≠ z₀ * v

namespace E₁Gens

variable {V₀ : Subgroup G} {z₀ v c₁ : G} (h : E₁Gens V₀ z₀ v c₁)
include h

theorem c_mem_centralizer : c₁ ∈ centralizer (V₀ : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  rcases h.cases e he with rfl | rfl | rfl | rfl
  · simp
  · exact h.zc
  · exact h.vc
  · rw [mul_assoc, h.vc, ← mul_assoc, h.zc, mul_assoc]

theorem mem_cases {y : G} (hy : y ∈ V₀ ⊔ zpowers c₁) :
    y = 1 ∨ y = z₀ ∨ y = v ∨ y = z₀ * v ∨ y = c₁ ∨ y = z₀ * c₁ ∨ y = v * c₁ ∨
      y = z₀ * v * c₁ := by
  have hle : zpowers c₁ ≤ normalizer (V₀ : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ h.c_mem_centralizer)
  have hy' : y ∈ ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left _ _ hle] at hy'
  obtain ⟨e, he, c, hc, rfl⟩ := hy'
  rcases eq_one_or_eq_of_mem_zpowers_of_sq h.c_sq hc with rfl | rfl <;>
    rcases h.cases e he with rfl | rfl | rfl | rfl <;> simp

theorem mem_of_mem_list {y : G}
    (hy : y ∈ [1, z₀, v, z₀ * v, c₁, z₀ * c₁, v * c₁, z₀ * v * c₁]) : y ∈ V₀ ⊔ zpowers c₁ := by
  have hz : z₀ ∈ V₀ ⊔ zpowers c₁ := mem_sup_left h.z_mem
  have hv : v ∈ V₀ ⊔ zpowers c₁ := mem_sup_left h.v_mem
  have hc : c₁ ∈ V₀ ⊔ zpowers c₁ := mem_sup_right (mem_zpowers c₁)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hz
  · exact hv
  · exact mul_mem hz hv
  · exact hc
  · exact mul_mem hz hc
  · exact mul_mem hv hc
  · exact mul_mem (mul_mem hz hv) hc

theorem mem_centralizer_of {k : G} (hz : k * z₀ = z₀ * k) (hv : k * v = v * k)
    (hc : k * c₁ = c₁ * k) : k ∈ centralizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) := by
  have hle : V₀ ⊔ zpowers c₁ ≤ centralizer ({k} : Set G) := by
    refine sup_le (fun e he => ?_) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hc.symm))
    rw [mem_centralizer_singleton_iff]
    rcases h.cases e he with rfl | rfl | rfl | rfl
    · simp
    · exact hz.symm
    · exact hv.symm
    · rw [mul_assoc, ← hv, ← mul_assoc, ← hz, mul_assoc]
  exact mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)

theorem le_centralizer :
    V₀ ⊔ zpowers c₁ ≤ centralizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) := by
  have hz := h.mem_centralizer_of rfl h.zv h.zc
  have hv := h.mem_centralizer_of h.zv.symm rfl h.vc
  have hc := h.mem_centralizer_of h.zc.symm h.vc.symm rfl
  refine sup_le (fun e he => ?_) (zpowers_le.mpr hc)
  rcases h.cases e he with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hz
  · exact hv
  · exact mul_mem hz hv

theorem card_le : Nat.card (V₀ ⊔ zpowers c₁ : Subgroup G) ≤ 8 :=
  card_le_length (l := [1, z₀, v, z₀ * v, c₁, z₀ * c₁, v * c₁, z₀ * v * c₁]) fun y hy => by
    rcases h.mem_cases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem conj_v_mem {k : G} (hk : k ∈ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G))
    (hkz : k * z₀ = z₀ * k) :
    k * v * k⁻¹ ∈ [v, z₀ * v, c₁, z₀ * c₁, v * c₁, z₀ * v * c₁] := by
  rcases h.mem_cases ((mem_normalizer_iff.mp hk v).mp (mem_sup_left h.v_mem)) with
    e | e | e | e | e | e | e | e <;> rw [e]
  · exact absurd (eq_of_conj_eq_of_commute (by simp) e) h.v_ne.1
  · exact absurd (eq_of_conj_eq_of_commute hkz e) h.v_ne.2
  all_goals simp

theorem conj_c_mem {k : G} (hk : k ∈ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G))
    (hkz : k * z₀ = z₀ * k) (hkv : k * v = v * k) :
    k * c₁ * k⁻¹ ∈ [c₁, z₀ * c₁, v * c₁, z₀ * v * c₁] := by
  have hkzv : k * (z₀ * v) = z₀ * v * k := by
    rw [← mul_assoc, hkz, mul_assoc, hkv, ← mul_assoc]
  rcases h.mem_cases ((mem_normalizer_iff.mp hk c₁).mp (mem_sup_right (mem_zpowers c₁))) with
    e | e | e | e | e | e | e | e <;> rw [e]
  · exact absurd (eq_of_conj_eq_of_commute (by simp) e) h.c_ne.1
  · exact absurd (eq_of_conj_eq_of_commute hkz e) h.c_ne.2.1
  · exact absurd (eq_of_conj_eq_of_commute hkv e) h.c_ne.2.2.1
  · exact absurd (eq_of_conj_eq_of_commute hkzv e) h.c_ne.2.2.2
  all_goals simp

theorem card_le_of_le_normalizer [Finite G] {K : Subgroup G}
    (hKN : K ≤ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G))
    (hKz : K ≤ centralizer ({z₀} : Set G))
    (hKC : K ⊓ centralizer ({v} : Set G) ⊓ centralizer ({c₁} : Set G) ≤ V₀ ⊔ zpowers c₁) :
    Nat.card K ≤ 192 := by
  have h1 : Nat.card K ≤ 6 * Nat.card ↥(K ⊓ centralizer ({v} : Set G)) :=
    card_le_length_mul_card_inf_centralizer fun k hk =>
      h.conj_v_mem (hKN hk) (mem_centralizer_singleton_iff.mp (hKz hk))
  have h2 : Nat.card ↥(K ⊓ centralizer ({v} : Set G)) ≤
      4 * Nat.card ↥(K ⊓ centralizer ({v} : Set G) ⊓ centralizer ({c₁} : Set G)) :=
    card_le_length_mul_card_inf_centralizer (K := K ⊓ centralizer ({v} : Set G)) fun k hk =>
      h.conj_c_mem (hKN hk.1) (mem_centralizer_singleton_iff.mp (hKz hk.1))
        (mem_centralizer_singleton_iff.mp hk.2)
  have h3 := (card_le_of_le hKC).trans h.card_le
  calc Nat.card K ≤ 6 * Nat.card ↥(K ⊓ centralizer ({v} : Set G)) := h1
    _ ≤ 6 * (4 * 8) := Nat.mul_le_mul_left 6 (h2.trans (Nat.mul_le_mul_left 4 h3))

end E₁Gens

end E₁

namespace IIbData

variable {G : Type} [Group G] [Finite G] {A R T V₀ P : Subgroup G} {g t z₀ a σ c₁ : G}

omit [Finite G] in
theorem e₁Gens_of_emb {f : IIbSyl →* G} (hfinj : Function.Injective f)
    (hfV0 : IIbSyl.V0.map f = V₀) (hfz : f IIbSyl.z0 = z₀) (hfc : f IIbSyl.c1 = c₁) :
    E₁Gens V₀ z₀ (f IIbSyl.vv) c₁ := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, -, -, -⟩ := IIbSyl.step5_rels
  subst hfz hfc
  have hne : ∀ {x y : IIbSyl}, x ≠ y → f x ≠ f y := fun hxy e => hxy (hfinj e)
  have hne1 : ∀ {x : IIbSyl}, x ≠ 1 → f x ≠ 1 := fun hx e => hx (hfinj (e.trans (map_one f).symm))
  refine ⟨?_, ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne1 r7, ⟨hne1 r8, hne r9⟩,
    ⟨hne1 r10, hne r11, hne r12, ?_⟩⟩
  · rw [← hfV0]
    exact mem_map_of_mem f ⟨_, IIbSyl.z0_eq⟩
  · rw [← hfV0]
    exact mem_map_of_mem f ⟨_, IIbSyl.vv_eq⟩
  · rw [← hfV0] at he
    obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := he
    rcases IIbSyl.v0Hom_cases w with e | e | e | e <;> rw [e]
    · exact Or.inl (map_one f)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (map_mul f _ _)))
  · rw [← map_mul, r1, map_one]
  · rw [← map_mul, r2, map_one]
  · rw [← map_mul, r3, map_one]
  · rw [← map_mul, r4, map_mul]
  · rw [← map_mul, r5, map_mul]
  · rw [← map_mul, r6, map_mul]
  · rw [← map_mul]
    exact hne r13

omit [Finite G] in
theorem le_centralizer_z₀ (hD : IIbData A R T V₀ P t z₀ a σ c₁) :
    P ⊔ zpowers t ≤ centralizer ({z₀} : Set G) := by
  refine sup_le (fun p hp => ?_)
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hD.outer.z_comm))
  have hpC : p ∈ centralizer (V₀ : Set G) := (mem_transvGroup.mp (hD.sylowP.le hp)).2.1
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hpC z₀ hD.outer.z_mem).symm

theorem centralizer_E₁_le (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (hO : AS76b.oddCoreIn (centralizer ({z₀} : Set G)) = ⊥)
    (hN : centralizer ({z₀} : Set G) ≤ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G)) :
    rankTwoX A ⊓ centralizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ≤ V₀ ⊔ zpowers c₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfinj, hfrange, hfS0, -, hfV0, -, -, hfz, -, -, hfc⟩ := hD.emb
  have hE := e₁Gens_of_emb hfinj hfV0 hfz hfc
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  set E := V₀ ⊔ zpowers c₁ with hEdef
  set L := rankTwoX A ⊓ centralizer (E : Set G) with hL
  set H := centralizer ({z₀} : Set G) with hH
  have hLH : L ≤ H := fun y hy => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hy.2 z₀ (mem_sup_left hE.z_mem)).symm
  have hHL : H ≤ normalizer (L : Set G) := fun h hh =>
    mem_normalizer_inf (by rw [normalizer_eq_top_iff.mpr hXn]; exact mem_top h)
      (mem_normalizer_centralizer (hN hh))
  have hcX : c₁ ∈ (P ⊔ zpowers t) ⊓ rankTwoX A := by
    rw [← hfS0, ← hfc]
    exact mem_map_of_mem f (MonoidHom.mem_ker.mpr IIbSyl.step5_rels.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hES : E ≤ P ⊔ zpowers t := by
    refine sup_le ?_ (zpowers_le.mpr hcX.1)
    rw [← hfV0, ← hfrange]
    exact map_le_range f _
  have hEX : E ≤ rankTwoX A := sup_le (hS.V₀_le_A.trans le_normalClosure) (zpowers_le.mpr hcX.2)
  have hS₁L : (P ⊔ zpowers t) ⊓ L = E := by
    refine le_antisymm ?_ (le_inf hES (le_inf hEX hE.le_centralizer))
    rintro y ⟨hyS, hyX, hyC⟩
    have hy0 : y ∈ IIbSyl.S0.map f := by
      rw [hfS0]
      exact ⟨hyS, hyX⟩
    obtain ⟨m, hm, rfl⟩ := hy0
    have hmv : m * IIbSyl.vv = IIbSyl.vv * m := hfinj (by
      rw [map_mul, map_mul]
      exact (mem_centralizer_iff.mp hyC _ (mem_sup_left hE.v_mem)).symm)
    have hmc : m * IIbSyl.c1 = IIbSyl.c1 * m := hfinj (by
      rw [map_mul, map_mul, hfc]
      exact (mem_centralizer_iff.mp hyC _ (mem_sup_right (mem_zpowers c₁))).symm)
    have h1 := List.mem_map_of_mem (f := f) (IIbSyl.mem_of_centE1 (MonoidHom.mem_ker.mp hm) hmv hmc)
    simp only [List.map_cons, List.map_nil, map_one, map_mul, hfz, hfc] at h1
    exact hE.mem_of_mem_list h1
  have hsylL := (hD.sylow.of_le (hD.le_centralizer_z₀) le_top).inf_of_le_normalizer hLH hHL
  rw [hS₁L, isSylowOf_iff] at hsylL
  obtain ⟨hEL, hE2, hEidx⟩ := hsylL
  have hLeq := AS81.eq_sup_oddCoreIn_of_central hE2 hEL (le_centralizer_iff.mp inf_le_right)
    (Nat.not_even_iff_odd.mp fun he => hEidx he.two_dvd)
  have hOL : oddCoreIn L = ⊥ :=
    le_bot_iff.mp ((oddCoreIn_le_of_le_of_le_normalizer hLH hHL).trans hO.le)
  rw [hOL, sup_bot_eq] at hLeq
  exact hLeq.le

theorem card_le_192 (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (hN : centralizer ({z₀} : Set G) ≤ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G))
    (hC : rankTwoX A ⊓ centralizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ≤ V₀ ⊔ zpowers c₁) :
    Nat.card ↥(rankTwoX A ⊓ centralizer ({z₀} : Set G)) ≤ 192 := by
  obtain ⟨f, hfinj, -, -, -, hfV0, -, -, hfz, -, -, hfc⟩ := hD.emb
  have hE := e₁Gens_of_emb hfinj hfV0 hfz hfc
  refine hE.card_le_of_le_normalizer (K := rankTwoX A ⊓ centralizer ({z₀} : Set G))
    (fun k hk => hN hk.2) (fun k hk => hk.2) fun k hk => hC ⟨hk.1.1.1, ?_⟩
  exact hE.mem_centralizer_of (mem_centralizer_singleton_iff.mp hk.1.1.2)
    (mem_centralizer_singleton_iff.mp hk.1.2) (mem_centralizer_singleton_iff.mp hk.2)

omit [Finite G] in
theorem sixtyFour_dvd_card (hD : IIbData A R T V₀ P t z₀ a σ c₁) :
    64 ∣ Nat.card ↥(rankTwoX A ⊓ centralizer ({z₀} : Set G)) := by
  obtain ⟨f, hfinj, -, hfS0, -⟩ := hD.emb
  have h64 : Nat.card IIbSyl.S0 = 64 := by
    have := IIbSyl.S0.card_mul_index
    rw [IIbSyl.index_S0, IIbSyl.card_IIbSyl] at this
    omega
  have hle : IIbSyl.S0.map f ≤ rankTwoX A ⊓ centralizer ({z₀} : Set G) := by
    rw [hfS0]
    exact fun y hy => ⟨hy.2, hD.le_centralizer_z₀ hy.1⟩
  have := card_dvd_of_le hle
  rwa [card_map_of_injective hfinj, h64] at this

theorem not_isPGroup (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (hA : ∃ x : G, rightConjugate V₀ x = ptOf z₀ c₁) :
    ¬ IsPGroup 2 ↥(rankTwoX A ⊓ centralizer ({z₀} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfinj, hfrange, hfS0, -, hfV0, -, -, hfz, -, hfσ, hfc⟩ := hD.emb
  have hE := e₁Gens_of_emb hfinj hfV0 hfz hfc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, rσz, rσv, -⟩ := IIbSyl.step5_rels
  set v := f IIbSyl.vv with hv
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  obtain ⟨x, hx⟩ := hA
  obtain ⟨eA⟩ := hS.equiv
  obtain ⟨y, -, hyN, -, hk3, -⟩ := exists_klein_three eA hS.loc.sylowV₀.le hS.card_V₀
  have hzW : z₀ ∈ rightConjugate V₀ x := by
    rw [hx]
    exact mem_sup_left (mem_zpowers z₀)
  have hw : x * z₀ * x⁻¹ ∈ V₀ := (mem_rightConjugate_iff V₀ x z₀).mp hzW
  obtain ⟨n, hn⟩ := hk3 z₀ hE.z_mem _ hw hE.z_ne fun h1 => hE.z_ne (conj_eq_one_iff.mp h1)
  set b := y ^ n with hb
  have hbN : b ∈ normalizer (V₀ : Set G) := pow_mem hyN n
  set k₀ := x⁻¹ * b⁻¹ with hk₀
  have hk₀z : k₀ * z₀ = z₀ * k₀ :=
    calc x⁻¹ * b⁻¹ * z₀ = x⁻¹ * (b⁻¹ * z₀ * b) * b⁻¹ := by group
      _ = x⁻¹ * (x * z₀ * x⁻¹) * b⁻¹ := by rw [hn]
      _ = z₀ * (x⁻¹ * b⁻¹) := by group
  have hk₀v : k₀ * v * k₀⁻¹ = c₁ ∨ k₀ * v * k₀⁻¹ = z₀ * c₁ := by
    have h1 : b⁻¹ * v * b ∈ V₀ := by
      have := (mem_normalizer_iff.mp (inv_mem hbN) v).mp hE.v_mem
      rwa [inv_inv] at this
    have h2 : k₀ * v * k₀⁻¹ ∈ ptOf z₀ c₁ := by
      rw [← hx, mem_rightConjugate_iff,
        show x * (k₀ * v * k₀⁻¹) * x⁻¹ = b⁻¹ * v * b by rw [hk₀]; group]
      exact h1
    rcases (mem_ptOf hE.z_sq hE.c_sq hE.zc).mp h2 with e | e | e | e
    · exact absurd (eq_of_conj_eq_of_commute (by simp) e) hE.v_ne.1
    · exact absurd (eq_of_conj_eq_of_commute hk₀z e) hE.v_ne.2
    · exact Or.inl e
    · exact Or.inr e
  have hσX : σ ∉ rankTwoX A := by
    intro hσ
    have h1 : σ ∈ (P ⊔ zpowers t) ⊓ rankTwoX A := ⟨by rw [← hfrange]; exact ⟨_, hfσ⟩, hσ⟩
    rw [← hfS0, ← hfσ, mem_map_iff_mem hfinj] at h1
    exact IIbSyl.chi_sigma (MonoidHom.mem_ker.mp h1)
  have hσz : σ * z₀ = z₀ * σ := by rw [← hfσ, ← hfz, ← map_mul, rσz, map_mul]
  have hσv : σ * v * σ⁻¹ = v := by
    rw [← hfσ, hv, ← map_mul, rσv, map_mul, mul_inv_cancel_right]
  obtain ⟨k₁, hk₁K, hk₁v⟩ : ∃ k ∈ rankTwoX A ⊓ centralizer ({z₀} : Set G),
      k * v * k⁻¹ = c₁ ∨ k * v * k⁻¹ = z₀ * c₁ := by
    by_cases hk₀X : k₀ ∈ rankTwoX A
    · exact ⟨k₀, mem_inf.mpr ⟨hk₀X, mem_centralizer_singleton_iff.mpr hk₀z⟩, hk₀v⟩
    · refine ⟨k₀ * σ, mem_inf.mpr ⟨hS.mul_mem_X_of_not_mem hD.outer hk₀X hσX, ?_⟩, ?_⟩
      · rw [mem_centralizer_singleton_iff, mul_assoc, hσz, ← mul_assoc, hk₀z, mul_assoc]
      · rwa [show k₀ * σ * v * (k₀ * σ)⁻¹ = k₀ * (σ * v * σ⁻¹) * k₀⁻¹ by group, hσv]
  intro hK2
  have hsylX : IsSylowOf 2 ((P ⊔ zpowers t) ⊓ rankTwoX A) (rankTwoX A) :=
    hD.sylow.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hXn).ge
  have hKeq := hsylX.eq_of_le (Q := rankTwoX A ⊓ centralizer ({z₀} : Set G))
    (fun y hy => ⟨hy.2, hD.le_centralizer_z₀ hy.1⟩) inf_le_left hK2
  have h1 : k₁ ∈ IIbSyl.S0.map f := by
    rw [hfS0, ← hKeq]
    exact hk₁K
  obtain ⟨m, hm, rfl⟩ := h1
  obtain ⟨hm1, hm2⟩ := IIbSyl.conj_vv_ne (MonoidHom.mem_ker.mp hm)
  rcases hk₁v with e | e
  · exact hm1 (hfinj (by rw [map_mul, map_mul, hfc, ← e, ← hv]; group))
  · exact hm2 (hfinj (by rw [map_mul, map_mul, map_mul, hfz, hfc, ← e, ← hv]; group))

theorem step5_of_normal (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (hA : ∃ x : G, rightConjugate V₀ x = ptOf z₀ c₁)
    (hO : AS76b.oddCoreIn (centralizer ({z₀} : Set G)) = ⊥)
    (hN : centralizer ({z₀} : Set G) ≤ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G)) :
    rankTwoX A ⊓ centralizer ({z₀} : Set G) ≤ normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ∧
      rankTwoX A ⊓ centralizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ≤ V₀ ⊔ zpowers c₁ ∧
      Nat.card ↥(rankTwoX A ⊓ centralizer ({z₀} : Set G)) = 192 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := hD.centralizer_E₁_le hS hO hN
  refine ⟨fun k hk => hN hk.2, hC, ?_⟩
  have hle := hD.card_le_192 hN hC
  obtain ⟨j, hj⟩ := hD.sixtyFour_dvd_card
  have hpos : 0 < Nat.card ↥(rankTwoX A ⊓ centralizer ({z₀} : Set G)) := Nat.card_pos
  have hj3 : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj3 with rfl | rfl | rfl
  · exact absurd (IsPGroup.of_card (n := 6) (by rw [hj]; norm_num)) (hD.not_isPGroup hS hA)
  · exact absurd (IsPGroup.of_card (n := 7) (by rw [hj]; norm_num)) (hD.not_isPGroup hS hA)
  · rw [hj]

end IIbData

end CFSG.ComponentClassification.RankTwoAltFive
