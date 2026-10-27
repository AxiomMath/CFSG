module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpCoprime

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] {a z : G}

private theorem mul_self_eq_one_of_orderOf_eq_two {X : Type*} [Group X] {x : X}
    (h : orderOf x = 2) : x * x = 1 := by
  have hpow := pow_orderOf_eq_one x
  rw [h, pow_two] at hpow
  exact hpow

private theorem ne_one_of_orderOf_eq_two {X : Type*} [Group X] {x : X}
    (h : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  omega

private theorem mem_closure_pair_comm {X : Type*} [Group X] {a b x : X}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    x ∈ Subgroup.closure ({a, b} : Set X) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by
    rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private theorem card_closure_pair_comm {X : Type*} [Group X] {a b : X}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set X)) = 4 := by
  have hab_ne_one : a * b ≠ 1 := by
    intro h
    refine hab1 ?_
    have hb_eq : b = a := by
      calc b = a⁻¹ * (a * b) := (inv_mul_cancel_left a b).symm
        _ = a⁻¹ * 1 := by rw [h]
        _ = a := by rw [mul_one, inv_eq_of_mul_eq_one_right ha]
    exact hb_eq.symm
  have hab_ne_a : a * b ≠ a := by
    intro h
    refine hb1 ?_
    calc b = a⁻¹ * (a * b) := (inv_mul_cancel_left a b).symm
      _ = a⁻¹ * a := by rw [h]
      _ = 1 := inv_mul_cancel a
  have hab_ne_b : a * b ≠ b := by
    intro h
    refine ha1 ?_
    calc a = (a * b) * b⁻¹ := (mul_inv_cancel_right a b).symm
      _ = b * b⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel b
  have hset : ((Subgroup.closure ({a, b} : Set X)) : Set X) = {1, a, b, a * b} := by
    ext x
    change x ∈ Subgroup.closure ({a, b} : Set X) ↔ x ∈ ({1, a, b, a * b} : Set X)
    rw [mem_closure_pair_comm ha hb hab]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1 : (1 : X) ∉ ({a, b, a * b} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hb1.symm, hab_ne_one.symm⟩
  have h2 : a ∉ ({b, a * b} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hab1, hab_ne_a.symm⟩
  have h3 : b ∉ ({a * b} : Set X) := by
    simp only [Set.mem_singleton_iff]
    exact hab_ne_b.symm
  calc Nat.card (Subgroup.closure ({a, b} : Set X))
      = ((Subgroup.closure ({a, b} : Set X)) : Set X).ncard := Nat.card_coe_set_eq _
    _ = ({1, a, b, a * b} : Set X).ncard := by rw [hset]
    _ = 4 := by
        rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
          Set.ncard_insert_of_notMem h3, Set.ncard_singleton]

private theorem five_E_shape_setup {X : Type*} [Group X] (hsh : IsShapeFiveCubeByTwoTwo X) :
    ∃ (N : Subgroup X) (_ : N.Normal), IsPGroup 5 N ∧ Nat.card N = 5 ^ 3 ∧
      Nonempty (X ⧸ N ≃* Elem2 2) ∧ Nat.card X = 500 := by
  obtain ⟨N, hN, hNp, hNcard, he⟩ := hsh
  refine ⟨N, hN, hNp, hNcard, he, ?_⟩
  haveI := hN
  have hq : Nat.card (X ⧸ N) = 4 := by
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Elem2 2) = 4
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hq, hNcard]
  norm_num

private theorem five_E_V_data {X : Type*} [Group X] {t t' : X} (ht : orderOf t = 2)
    (ht' : orderOf t' = 2) (hcomm : t * t' = t' * t) (hne : t ≠ t') :
    Nat.card (Subgroup.closure ({t, t'} : Set X)) = 4 ∧
      IsPGroup 2 (Subgroup.closure ({t, t'} : Set X)) := by
  have hcard : Nat.card (Subgroup.closure ({t, t'} : Set X)) = 4 :=
    card_closure_pair_comm (mul_self_eq_one_of_orderOf_eq_two ht)
      (mul_self_eq_one_of_orderOf_eq_two ht') hcomm (ne_one_of_orderOf_eq_two ht)
      (ne_one_of_orderOf_eq_two ht') hne
  refine ⟨hcard, ?_⟩
  apply IsPGroup.of_card (n := 2)
  rw [hcard]
  norm_num

theorem cp_five_E_cover (h : F5Std a z) {x t t' : G} (hx : x ∈ orb5E a a)
    (ht : t ∈ InvIn (Gxy a x)) (ht' : t' ∈ InvIn (Gxy a x)) (hcomm : t * t' = t' * t)
    (hne : t ≠ t') :
    ∀ s ∈ InvIn (Gxy a x),
      ConjIn (Gxy a x) t s ∨ ConjIn (Gxy a x) t' s ∨ ConjIn (Gxy a x) (t * t') s := by
  haveI hfinG : Finite G := h.finite
  let X : Subgroup G := Gxy a x
  let t₀ : X := ⟨t, ht.1⟩
  let t₀' : X := ⟨t', ht'.1⟩
  let V : Subgroup X := Subgroup.closure ({t₀, t₀'} : Set X)
  have ht0ord : orderOf t₀ = 2 := by
    change orderOf (⟨t, ht.1⟩ : X) = 2
    rw [Subgroup.orderOf_mk, ht.2]
  have ht0'ord : orderOf t₀' = 2 := by
    change orderOf (⟨t', ht'.1⟩ : X) = 2
    rw [Subgroup.orderOf_mk, ht'.2]
  have hcomm0 : t₀ * t₀' = t₀' * t₀ := Subtype.ext hcomm
  have hne0 : t₀ ≠ t₀' := fun hh => hne (congrArg Subtype.val hh)
  have hVcard : Nat.card V = 4 := (five_E_V_data ht0ord ht0'ord hcomm0 hne0).1
  obtain ⟨-, -, -, -, -, hXcard⟩ := five_E_shape_setup (h.loc.five.self.five_E x hx)
  have hfac : (Nat.card ↥X).factorization 2 = 2 := by
    rw [show Nat.card ↥X = 500 from hXcard,
      show (500 : ℕ) = 2 ^ 2 * 5 ^ 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 5 ^ 3)]
  let hVsyl : Sylow 2 ↥X := Sylow.ofCard V (by rw [hVcard, hfac]; norm_num)
  intro s hs
  let s₀ : X := ⟨s, hs.1⟩
  have hs0ord : orderOf s₀ = 2 := by
    change orderOf (⟨s, hs.1⟩ : X) = 2
    rw [Subgroup.orderOf_mk, hs.2]
  have hspg : IsPGroup 2 (Subgroup.zpowers s₀) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hs0ord]
    norm_num
  obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow hspg
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q hVsyl
  have hmem : MulAut.conj g • s₀ ∈ V := by
    have h1 : s₀ ∈ (Q : Subgroup X) := hQle (Subgroup.mem_zpowers s₀)
    have h2 : MulAut.conj g • s₀ ∈ MulAut.conj g • (Q : Subgroup X) :=
      Subgroup.smul_mem_pointwise_smul s₀ (MulAut.conj g) (Q : Subgroup X) h1
    have h3 : MulAut.conj g • (Q : Subgroup X) = V := by
      rw [← Sylow.pointwise_smul_def]
      rw [show MulAut.conj g • Q = hVsyl from by rw [← Sylow.smul_def]; exact hg]
      rfl
    rw [h3] at h2
    exact h2
  have hv : g * s₀ * g⁻¹ ∈ V := by simpa [MulAut.conj_apply] using hmem
  have hvord : orderOf (g * s₀ * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply]
    exact (MulEquiv.orderOf_eq (MulAut.conj g) s₀).trans hs0ord
  have hcases := (mem_closure_pair_comm (mul_self_eq_one_of_orderOf_eq_two ht0ord)
    (mul_self_eq_one_of_orderOf_eq_two ht0'ord) hcomm0).1 hv
  rcases hcases with h1 | h1 | h1 | h1
  · exfalso
    rw [h1, orderOf_one] at hvord
    omega
  · left
    refine ⟨(g⁻¹ : X), (g⁻¹).2, ?_⟩
    have h1G : (g : G) * s * (g : G)⁻¹ = t := by
      simpa using congrArg Subtype.val h1
    have hco : ((g⁻¹ : X) : G) = (g : G)⁻¹ := map_inv X.subtype g
    rw [hco, inv_inv, ← h1G]
    group
  · right; left
    refine ⟨(g⁻¹ : X), (g⁻¹).2, ?_⟩
    have h1G : (g : G) * s * (g : G)⁻¹ = t' := by
      simpa using congrArg Subtype.val h1
    have hco : ((g⁻¹ : X) : G) = (g : G)⁻¹ := map_inv X.subtype g
    rw [hco, inv_inv, ← h1G]
    group
  · right; right
    refine ⟨(g⁻¹ : X), (g⁻¹).2, ?_⟩
    have h1G : (g : G) * s * (g : G)⁻¹ = t * t' := by
      simpa using congrArg Subtype.val h1
    have hco : ((g⁻¹ : X) : G) = (g : G)⁻¹ := map_inv X.subtype g
    rw [hco, inv_inv, ← h1G]
    group

theorem cp_five_E_gen (h : F5Std a z) {x t t' : G} (hx : x ∈ orb5E a a)
    (ht : t ∈ InvIn (Gxy a x)) (ht' : t' ∈ InvIn (Gxy a x)) (hcomm : t * t' = t' * t)
    (hne : t ≠ t') :
    Gxy a x ≤ Subgroup.closure ((Gxyz a t x : Set G) ∪ (Gxyz a t' x : Set G) ∪
      (Gxyz a (t * t') x : Set G)) := by
  haveI hfinG : Finite G := h.finite
  let X : Subgroup G := Gxy a x
  let C : Subgroup G := Subgroup.closure ((Gxyz a t x : Set G) ∪ (Gxyz a t' x : Set G) ∪
    (Gxyz a (t * t') x : Set G))
  change X ≤ C
  let t₀ : X := ⟨t, ht.1⟩
  let t₀' : X := ⟨t', ht'.1⟩
  let V : Subgroup X := Subgroup.closure ({t₀, t₀'} : Set X)
  have ht0ord : orderOf t₀ = 2 := by
    change orderOf (⟨t, ht.1⟩ : X) = 2
    rw [Subgroup.orderOf_mk, ht.2]
  have ht0'ord : orderOf t₀' = 2 := by
    change orderOf (⟨t', ht'.1⟩ : X) = 2
    rw [Subgroup.orderOf_mk, ht'.2]
  have hcomm0 : t₀ * t₀' = t₀' * t₀ := Subtype.ext hcomm
  have hne0 : t₀ ≠ t₀' := fun hh => hne (congrArg Subtype.val hh)
  obtain ⟨hVcard, hVp⟩ := five_E_V_data ht0ord ht0'ord hcomm0 hne0
  obtain ⟨N, hNnorm, hNp, hNcard, ⟨e⟩, hXcard⟩ :=
    five_E_shape_setup (h.loc.five.self.five_E x hx)
  haveI hNnormI : N.Normal := hNnorm
  have hquotcard : Nat.card (X ⧸ N) = 4 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Elem2 2) = 4
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  let S : Set X := {n : X | n ∈ N ∧
    (t₀ * n = n * t₀ ∨ t₀' * n = n * t₀' ∨ t₀ * t₀' * n = n * (t₀ * t₀'))}
  haveI hfive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hNgen : N ≤ Subgroup.closure S :=
    cp_klein_gen hNnorm (p := 5) (by norm_num) hNp ht0ord ht0'ord hcomm0
  have hN_le : N.map X.subtype ≤ C := by
    have h1 : N.map X.subtype ≤ (Subgroup.closure S).map X.subtype :=
      Subgroup.map_mono hNgen
    rw [MonoidHom.map_closure] at h1
    refine h1.trans ?_
    rw [Subgroup.closure_le]
    rintro y ⟨n, hn, rfl⟩
    have hna : (n : G) ∈ Gx a := (mem_Gxy.mp n.2).1
    have hnx : (n : G) ∈ Gx x := (mem_Gxy.mp n.2).2
    rcases hn.2 with hc | hc | hc
    · have hnt : (n : G) ∈ Gx t := mem_Gx.mpr (by simpa using congrArg Subtype.val hc)
      exact Subgroup.subset_closure (Or.inl (Or.inl (mem_Gxyz.mpr ⟨hna, hnt, hnx⟩)))
    · have hnt : (n : G) ∈ Gx t' := mem_Gx.mpr (by simpa using congrArg Subtype.val hc)
      exact Subgroup.subset_closure (Or.inl (Or.inr (mem_Gxyz.mpr ⟨hna, hnt, hnx⟩)))
    · have hnt : (n : G) ∈ Gx (t * t') := mem_Gx.mpr (by simpa using congrArg Subtype.val hc)
      exact Subgroup.subset_closure (Or.inr (mem_Gxyz.mpr ⟨hna, hnt, hnx⟩))
  have hV_le : V.map X.subtype ≤ C := by
    have hVmap : V.map X.subtype = Subgroup.closure ({t, t'} : Set G) := by
      change (Subgroup.closure ({t₀, t₀'} : Set X)).map X.subtype =
        Subgroup.closure ({t, t'} : Set G)
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨v, hv, rfl⟩
        rcases hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨t₀, Or.inl rfl, rfl⟩
        · exact ⟨t₀', Or.inr rfl, rfl⟩
    rw [hVmap, Subgroup.closure_le]
    intro y hy
    have hy' : y = t ∨ y = t' := by simpa using hy
    rcases hy' with hy1 | hy1
    · rw [hy1]
      exact Subgroup.subset_closure (Or.inl (Or.inl (mem_Gxyz.mpr
        ⟨(mem_Gxy.mp ht.1).1, self_mem_Gx t, (mem_Gxy.mp ht.1).2⟩)))
    · rw [hy1]
      exact Subgroup.subset_closure (Or.inl (Or.inl (mem_Gxyz.mpr
        ⟨(mem_Gxy.mp ht'.1).1, mem_Gx.mpr hcomm, (mem_Gxy.mp ht'.1).2⟩)))
  have hNVdisj : Disjoint N V :=
    IsPGroup.disjoint_of_coprime hNp hVp (by norm_num : Nat.Coprime 5 2)
  have hsup : N ⊔ V = ⊤ := by
    let φ : V → X ⧸ N := fun v => QuotientGroup.mk (v : X)
    have hφinj : Function.Injective φ := by
      intro v w h
      have hd : (v : X) * (w : X)⁻¹ ∈ N := by
        have hrel := QuotientGroup.eq_iff_div_mem.mp h
        simpa [div_eq_mul_inv] using hrel
      have hdV : (v : X) * (w : X)⁻¹ ∈ V := V.mul_mem v.2 (V.inv_mem w.2)
      have h1 : (v : X) * (w : X)⁻¹ = 1 := (Subgroup.disjoint_def.mp hNVdisj) hd hdV
      exact Subtype.ext (eq_of_mul_inv_eq_one h1)
    have hφbij : Function.Bijective φ :=
      (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [hVcard, hquotcard]⟩
    refine le_antisymm le_top ?_
    intro g _
    obtain ⟨v, hv⟩ := hφbij.2 (QuotientGroup.mk g)
    have hd : (v : X) * g⁻¹ ∈ N := by
      have hrel := QuotientGroup.eq_iff_div_mem.mp hv
      simpa [div_eq_mul_inv] using hrel
    have hgeq : g = ((v : X) * g⁻¹)⁻¹ * (v : X) := by group
    rw [hgeq]
    exact (N ⊔ V).mul_mem (Subgroup.mem_sup_left (N.inv_mem hd))
      (Subgroup.mem_sup_right v.2)
  have hmap_top : (⊤ : Subgroup X).map X.subtype = X := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype X
  have htop : (⊤ : Subgroup X) ≤ C.comap X.subtype := by
    rw [← hsup]
    exact sup_le (Subgroup.map_le_iff_le_comap.mp hN_le)
      (Subgroup.map_le_iff_le_comap.mp hV_le)
  have hmap : (⊤ : Subgroup X).map X.subtype ≤ C :=
    Subgroup.map_le_iff_le_comap.mpr htop
  exact hmap_top ▸ hmap

end CFSG.EvenSporadicStandard.HNRecog.Section4
