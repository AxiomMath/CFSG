module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.ReflectionFourGroup
import CFSG.GroupTheory.ABGLocalTools.ReflectionOrderEight
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

section General

variable {G : Type u} [Group G]

private theorem conj_mem_of_mem_normalizer {X : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ X) : g * x * g⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

private theorem mem_normalizer_of_conj_mem [Finite G] {K : Subgroup G} {x : G}
    (h : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

private theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

private theorem isSolvable_solvRadIn [Finite G] (H : Subgroup G) :
    Group.IsSolvable (solvRadIn H) := by
  have : Group.IsSolvable (CFSG.solvableRadical H) := solvableRadical_isSolvable
  exact Group.isSolvable_of_surjective
    (f := ((CFSG.solvableRadical H).equivMapOfInjective H.subtype
      H.subtype_injective).toMonoidHom)
    ((CFSG.solvableRadical H).equivMapOfInjective H.subtype H.subtype_injective).surjective

private theorem le_solvRadIn {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hK : Group.IsSolvable K) :
    K ≤ solvRadIn H := by
  have hnormal : (K.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (Subgroup.mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hsolv : Group.IsSolvable (K.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKH).injective
  have hle : K.subgroupOf H ≤ CFSG.solvableRadical H := le_sSup ⟨hnormal, hsolv⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

private theorem le_normalizer_solvRadIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((solvRadIn H : Subgroup G) : Set G) :=
  have : (CFSG.solvableRadical H).Normal := solvableRadical_normal
  le_normalizer_map_subtype H (CFSG.solvableRadical H)

private theorem le_solvRadIn_of_pow_mem [Finite G] {r : ℕ} (hr : r.Prime) {H Z : Subgroup G}
    (hZH : Z ≤ H) (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hpow : ∀ g ∈ Z, g ^ r ∈ solvRadIn H) : Z ≤ solvRadIn H := by
  have : Fact r.Prime := ⟨hr⟩
  apply le_solvRadIn hZH hHZ
  set S := solvRadIn H with hS
  have hHS := le_normalizer_solvRadIn H
  set N : Subgroup Z := (Z ⊓ S).subgroupOf Z with hN
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnZ, hnS⟩ := hn
    refine ⟨Z.mul_mem (Z.mul_mem g.2 hnZ) (Z.inv_mem g.2), ?_⟩
    exact conj_mem_of_mem_normalizer (hHS (hZH g.2)) hnS
  have hNs : Group.IsSolvable N := by
    have hle : Z ⊓ S ≤ S := inf_le_right
    have : Group.IsSolvable S := isSolvable_solvRadIn H
    have : Group.IsSolvable (Z ⊓ S : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ⊓ S ≤ Z)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ⊓ S ≤ Z)).injective
  have hQp : IsPGroup r (Z ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    exact ⟨Z.pow_mem g.2 r, by simpa using hpow g g.2⟩
  have : Group.IsNilpotent (Z ⧸ N) := hQp.isNilpotent
  exact Group.isSolvable_of_subgroup_quotient N

private theorem mem_map_conj_iff {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hw
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem isSylowOf_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) K := by
  refine isSylowOf_of_card (fun y hy => ?_) ?_
  · rw [mem_map_conj_iff] at hy
    have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mp (hP.le hy)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]

private theorem exists_mem_normalizer_mul_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (hP : IsSylowOf p P K) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), ∃ k ∈ K, x = n * k := by
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj (isSylowOf_map_conj hP (inv_mem hx))
  refine ⟨x * k, ?_, k⁻¹, inv_mem hk, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h := hconj (k * y * k⁻¹)
  rw [mem_map_conj_iff, inv_inv, show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h
  rw [show x * k * y * (x * k)⁻¹ = x * (k * y * k⁻¹) * x⁻¹ by group]
  exact h.symm

private theorem mem_solvRadIn_of_scalar [Finite G] {K W : Subgroup G}
    (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hCW : K ⊓ Subgroup.centralizer (W : Set G) ≤ solvRadIn K) {y : G} (hyK : y ∈ K)
    (hy : (∀ w ∈ W, y * w * y⁻¹ = w) ∨ (∀ w ∈ W, y * w * y⁻¹ = w⁻¹)) : y ∈ solvRadIn K := by
  have hinvconj : ∀ g w : G, g * w⁻¹ * g⁻¹ = (g * w * g⁻¹)⁻¹ := fun g w => by group
  let Z : Subgroup G :=
    { carrier := {g | g ∈ K ∧ ((∀ w ∈ W, g * w * g⁻¹ = w) ∨ (∀ w ∈ W, g * w * g⁻¹ = w⁻¹))}
      one_mem' := ⟨K.one_mem, Or.inl fun w _ => by group⟩
      mul_mem' := by
        rintro g h ⟨hgK, hg⟩ ⟨hhK, hh⟩
        refine ⟨K.mul_mem hgK hhK, ?_⟩
        have e : ∀ w : G, g * h * w * (g * h)⁻¹ = g * (h * w * h⁻¹) * g⁻¹ := fun w => by group
        rcases hg with hg | hg <;> rcases hh with hh | hh
        · exact Or.inl fun w hw => by
            rw [e, hh w hw, hg w hw]
        · exact Or.inr fun w hw => by
            rw [e, hh w hw, hinvconj, hg w hw]
        · exact Or.inr fun w hw => by
            rw [e, hh w hw, hg w hw]
        · exact Or.inl fun w hw => by
            rw [e, hh w hw, hinvconj, hg w hw, inv_inv]
      inv_mem' := by
        rintro g ⟨hgK, hg⟩
        refine ⟨K.inv_mem hgK, ?_⟩
        have hw' : ∀ w ∈ W, g⁻¹ * w * g⁻¹⁻¹ ∈ W := fun w hw =>
          conj_mem_of_mem_normalizer (hKW (K.inv_mem hgK)) hw
        have e : ∀ w : G, g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ = w := fun w => by group
        rcases hg with hg | hg
        · refine Or.inl fun w hw => ?_
          have h := hg _ (hw' w hw)
          rw [e] at h
          exact h.symm
        · refine Or.inr fun w hw => ?_
          have h := hg _ (hw' w hw)
          rw [e] at h
          exact inv_eq_iff_eq_inv.mp h.symm }
  have hZK : Z ≤ K := fun g hg => hg.1
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) := by
    intro k hk
    apply mem_normalizer_of_conj_mem
    rintro g ⟨hgK, hg⟩
    refine ⟨K.mul_mem (K.mul_mem hk hgK) (K.inv_mem hk), ?_⟩
    have hw' : ∀ w ∈ W, k⁻¹ * w * k⁻¹⁻¹ ∈ W := fun w hw =>
      conj_mem_of_mem_normalizer (hKW (K.inv_mem hk)) hw
    have e : ∀ w : G, k * g * k⁻¹ * w * (k * g * k⁻¹)⁻¹ =
        k * (g * (k⁻¹ * w * k⁻¹⁻¹) * g⁻¹) * k⁻¹ := fun w => by group
    have e' : ∀ w : G, k * (k⁻¹ * w * k⁻¹⁻¹) * k⁻¹ = w := fun w => by group
    rcases hg with hg | hg
    · exact Or.inl fun w hw => by rw [e, hg _ (hw' w hw), e']
    · exact Or.inr fun w hw => by rw [e, hg _ (hw' w hw), hinvconj, e']
  have hpow : ∀ g ∈ Z, g ^ 2 ∈ solvRadIn K := by
    rintro g ⟨hgK, hg⟩
    refine hCW ⟨K.pow_mem hgK 2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hgw : g * w * g⁻¹ ∈ W := conj_mem_of_mem_normalizer (hKW hgK) hw
    have e : g ^ 2 * w * (g ^ 2)⁻¹ = g * (g * w * g⁻¹) * g⁻¹ := by
      rw [pow_two]
      group
    have h2 : g ^ 2 * w * (g ^ 2)⁻¹ = w := by
      rw [e]
      rcases hg with hg | hg
      · rw [hg w hw, hg w hw]
      · rw [hg w hw, hinvconj, hg w hw, inv_inv]
    calc w * g ^ 2 = g ^ 2 * w * (g ^ 2)⁻¹ * g ^ 2 := by rw [h2]
      _ = g ^ 2 * w := by group
  exact le_solvRadIn_of_pow_mem Nat.prime_two hZK hKZ hpow ⟨hyK, hy⟩

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] {σ : Setting G}

private theorem exists_mul_of_mem_N {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) {g : G}
    (hg : g ∈ σ.N) : ∃ k ∈ Subgroup.normalizer (d.R : Set G), ∃ o ∈ σ.ON, g = k * o := by
  have : Fact r.Prime := ⟨hr.prime⟩
  exact exists_mem_normalizer_mul_of_isSylowOf d.R_sylow (σ.N_le_normalizer_ON hg)

private theorem solvRadIn_inf_N_le {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) :
    solvRadIn (Subgroup.normalizer (d.R : Set G)) ⊓ σ.N ≤ solvRadIn σ.N := by
  set K := Subgroup.normalizer (d.R : Set G) with hK
  set Y := solvRadIn K ⊓ σ.N with hY
  set X := σ.ON ⊔ Y with hX
  have hYN : Y ≤ σ.N := inf_le_right
  have hXN : X ≤ σ.N := sup_le σ.ON_le_N hYN
  have hOX : σ.ON ≤ X := le_sup_left
  have hYX : Y ≤ X := le_sup_right
  have hnorm : σ.N ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_N hr d hg
    have hoN : o ∈ σ.N := σ.ON_le_N ho
    have hkN : k ∈ σ.N := by
      have e : k = k * o * o⁻¹ := by group
      rw [e]
      exact σ.N.mul_mem hg (σ.N.inv_mem hoN)
    refine Subgroup.mul_mem _ (mem_normalizer_sup (σ.N_le_normalizer_ON hkN) ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_solvRadIn K hk, Subgroup.le_normalizer hkN⟩
    · apply mem_normalizer_of_conj_mem
      intro x hx
      have hxN : x ∈ σ.N := hXN hx
      have h1 : o * (x * o⁻¹ * x⁻¹) ∈ σ.ON :=
        σ.ON.mul_mem ho
          (conj_mem_of_mem_normalizer (σ.N_le_normalizer_ON hxN) (σ.ON.inv_mem ho))
      have e : o * x * o⁻¹ = o * (x * o⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact X.mul_mem (hOX h1) hx
  have hsolv : Group.IsSolvable X := by
    have hON : (σ.ON.subgroupOf X).Normal := by
      constructor
      intro a ha b
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact conj_mem_of_mem_normalizer (σ.N_le_normalizer_ON (hXN b.2)) ha
    have h1 : Group.IsSolvable (σ.ON.subgroupOf X) := by
      have : Group.IsSolvable σ.ON := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreIn σ.N)
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hOX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hOX).injective
    have h2 : Group.IsSolvable (X ⧸ σ.ON.subgroupOf X) := by
      have : Group.IsSolvable (solvRadIn K) := isSolvable_solvRadIn K
      have : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_left : Y ≤ solvRadIn K))
        (Subgroup.inclusion_injective _)
      let ψ : Y →* X ⧸ σ.ON.subgroupOf X :=
        (QuotientGroup.mk' (σ.ON.subgroupOf X)).comp (Subgroup.inclusion hYX)
      refine Group.isSolvable_of_surjective (f := ψ) ?_
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
      have hx : (x : G) ∈ ((σ.ON ⊔ Y : Subgroup G) : Set G) := x.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (hYN.trans σ.N_le_normalizer_ON)] at hx
      obtain ⟨o, ho, y, hy, hoy⟩ := Set.mem_mul.mp hx
      refine ⟨⟨y, hy⟩, ?_⟩
      change (QuotientGroup.mk (Subgroup.inclusion hYX ⟨y, hy⟩) :
        X ⧸ σ.ON.subgroupOf X) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      change y⁻¹ * (x : G) ∈ σ.ON
      rw [← hoy]
      have := conj_mem_of_mem_normalizer
        (σ.N_le_normalizer_ON (σ.N.inv_mem (hYN hy))) ho
      simpa [mul_assoc] using this
    exact Group.isSolvable_of_subgroup_quotient (σ.ON.subgroupOf X)
  exact hYX.trans (le_solvRadIn hXN hnorm hsolv)

private theorem x_not_mem_ON (hσ : σ.IsValid) : σ.x ∉ σ.ON := by
  intro h
  have hdvd : orderOf σ.x ∣ Nat.card σ.ON := Subgroup.orderOf_dvd_natCard σ.ON h
  rw [hσ.x_order] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn σ.N)) (even_iff_two_dvd.mpr hdvd)

private theorem eq_one_of_mem_ON_of_pow {o : G} (ho : o ∈ σ.ON) {k : ℕ} (hk : o ^ 2 ^ k = 1) :
    o = 1 := by
  have h1 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : Odd (orderOf o) :=
    (odd_card_oddCoreIn σ.N).of_dvd_nat (Subgroup.orderOf_dvd_natCard σ.ON ho)
  have hcop : Nat.Coprime (orderOf o) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr h2)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h1)

private theorem exists_of_mem_ON_sup_center (hσ : σ.IsValid)
    (hZ : centerOf (σ.S : Subgroup G) ≤ Subgroup.zpowers σ.x) {y : G}
    (hy : y ∈ σ.ON ⊔ centerOf (σ.S : Subgroup G)) : ∃ o ∈ σ.ON, y = o ∨ y = o * σ.x := by
  have hle : σ.ON ⊔ centerOf (σ.S : Subgroup G) ≤ σ.ON ⊔ Subgroup.zpowers σ.x :=
    sup_le_sup_left hZ _
  have hy' : y ∈ ((σ.ON ⊔ Subgroup.zpowers σ.x : Subgroup G) : Set G) := hle hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (Subgroup.zpowers_le.mpr (σ.N_le_normalizer_ON σ.x_mem_N))] at hy'
  obtain ⟨o, ho, z, hz, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨o, ho, ?_⟩
  rw [← zpow_mod_orderOf, hσ.x_order]
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero, mul_one]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

private theorem eq_one_or_eq_x_of_mem (hσ : σ.IsValid)
    (hZ : centerOf (σ.S : Subgroup G) ≤ Subgroup.zpowers σ.x) {y : G}
    (hy : y ∈ σ.ON ⊔ centerOf (σ.S : Subgroup G)) {k : ℕ} (hk : y ^ 2 ^ k = 1) :
    y = 1 ∨ y = σ.x := by
  obtain ⟨o, ho, rfl | rfl⟩ := exists_of_mem_ON_sup_center hσ hZ hy
  · exact Or.inl (eq_one_of_mem_ON_of_pow ho hk)
  · have hcomm : Commute o σ.x := (σ.mem_N_iff o).mp (σ.ON_le_N ho)
    rw [hcomm.mul_pow] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, pow_one, pow_one] at hk
      exact absurd (show σ.x ∈ σ.ON by
        rw [eq_inv_of_mul_eq_one_right hk]; exact σ.ON.inv_mem ho) (x_not_mem_ON hσ)
    · have hx : σ.x ^ 2 ^ k = 1 := by
        obtain ⟨m, hm⟩ : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0.ne'
        rw [hm, pow_mul, ← hσ.x_order, pow_orderOf_eq_one, one_pow]
      rw [hx, mul_one] at hk
      rw [eq_one_of_mem_ON_of_pow ho hk, one_mul]
      exact Or.inr rfl

private theorem mem_ON_of_mem_of_odd (hσ : σ.IsValid)
    (hZ : centerOf (σ.S : Subgroup G) ≤ Subgroup.zpowers σ.x) {y : G}
    (hy : y ∈ σ.ON ⊔ centerOf (σ.S : Subgroup G)) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) :
    y ∈ σ.ON := by
  obtain ⟨o, ho, rfl | rfl⟩ := exists_of_mem_ON_sup_center hσ hZ hy
  · exact ho
  · have hcomm : Commute o σ.x := (σ.mem_N_iff o).mp (σ.ON_le_N ho)
    rw [hcomm.mul_pow] at hym
    have hx : σ.x ^ m = σ.x := by
      obtain ⟨j, rfl⟩ := hm
      rw [pow_succ, pow_mul, ← hσ.x_order, pow_orderOf_eq_one, one_pow, one_mul]
    rw [hx] at hym
    exact absurd (show σ.x ∈ σ.ON by
      rw [eq_inv_of_mul_eq_one_right hym]; exact σ.ON.inv_mem (σ.ON.pow_mem ho m))
      (x_not_mem_ON hσ)

omit [Finite G] in
private theorem exists_pow_mul_eq {a c : G} (ha : a ∈ σ.N) (hc : c ∈ σ.ON) (n : ℕ) :
    ∃ c' ∈ σ.ON, (a * c) ^ n = a ^ n * c' := by
  induction n with
  | zero => exact ⟨1, σ.ON.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨a⁻¹ * c' * a * c, σ.ON.mul_mem ?_ hc, ?_⟩
    · have := conj_mem_of_mem_normalizer (σ.N_le_normalizer_ON (σ.N.inv_mem ha)) hc'
      simpa using this
    · rw [pow_succ, h, pow_succ]
      group

theorem reflection_element_of_commutator (hσ : σ.IsValid) (hN : σ.NStructure)
    (hZ : centerOf (σ.S : Subgroup G) ≤ Subgroup.zpowers σ.x) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) {W : Subgroup G}
    (hKW : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hCW : Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
      solvRadIn (Subgroup.normalizer (d.R : Set G)))
    (hrefl : (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r) (hbig : r ^ 2 < Nat.card W)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsr : s ≠ r) {g : G} (hg : g ∈ σ.N)
    (hgs : (σ.x₂ * g * σ.x₂⁻¹ * g⁻¹) ^ s ∈ σ.ON) (hg1 : σ.x₂ * g * σ.x₂⁻¹ * g⁻¹ ∉ σ.ON) :
    ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
      u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
      u ∉ Subgroup.centralizer (W : Set G) ∧
      σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (W : Set G) ∧
      ∃ a ∈ W ⊓ Subgroup.centralizer {σ.x₂}, a ≠ 1 ∧ u * a = a * u := by
  set K := Subgroup.normalizer (d.R : Set G) with hK
  have hx₂D : σ.x₂ ∈ σ.D := σ.T_le_D hσ σ.x₂_mem_T
  have hx₂K : σ.x₂ ∈ K := d.R_D hx₂D
  have hx₂N : σ.x₂ ∈ σ.N := σ.D_le_N hσ hx₂D
  have hx₂x₂ : σ.x₂ * σ.x₂ = 1 := by rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]
  have hx₂inv : σ.x₂⁻¹ = σ.x₂ := inv_eq_of_mul_eq_one_right hx₂x₂
  obtain ⟨k, hkK, o, ho, rfl⟩ := exists_mul_of_mem_N hr d hg
  have hkN : k ∈ σ.N := by
    have e : k = k * o * o⁻¹ := by group
    rw [e]
    exact σ.N.mul_mem hg (σ.N.inv_mem (σ.ON_le_N ho))
  set ρ := σ.x₂ * k * σ.x₂⁻¹ * k⁻¹ with hρ
  have hρK : ρ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hx₂K hkK) (K.inv_mem hx₂K)) (K.inv_mem hkK)
  have hρN : ρ ∈ σ.N :=
    σ.N.mul_mem (σ.N.mul_mem (σ.N.mul_mem hx₂N hkN) (σ.N.inv_mem hx₂N)) (σ.N.inv_mem hkN)
  have hρinv : σ.x₂ * ρ * σ.x₂⁻¹ = ρ⁻¹ := by
    have e1 : σ.x₂ * ρ * σ.x₂⁻¹ = σ.x₂ * σ.x₂ * k * σ.x₂⁻¹ * k⁻¹ * σ.x₂⁻¹ := by
      rw [hρ]
      group
    have e2 : ρ⁻¹ = k * σ.x₂ * k⁻¹ * σ.x₂⁻¹ := by
      rw [hρ]
      group
    rw [e1, e2, hx₂x₂, hx₂inv, one_mul]
  obtain ⟨c, hcON, hceq⟩ : ∃ c ∈ σ.ON,
      σ.x₂ * (k * o) * σ.x₂⁻¹ * (k * o)⁻¹ = ρ * c := by
    refine ⟨k * (σ.x₂ * o * σ.x₂⁻¹ * o⁻¹) * k⁻¹, ?_, by rw [hρ]; group⟩
    have h1 : σ.x₂ * o * σ.x₂⁻¹ ∈ σ.ON :=
      conj_mem_of_mem_normalizer (σ.N_le_normalizer_ON hx₂N) ho
    exact conj_mem_of_mem_normalizer (σ.N_le_normalizer_ON hkN)
      (σ.ON.mul_mem h1 (σ.ON.inv_mem ho))
  rw [hceq] at hgs hg1
  have hρs : ρ ^ s ∈ σ.ON := by
    obtain ⟨c', hc', h⟩ := exists_pow_mul_eq hρN hcON s
    rw [h] at hgs
    have e : ρ ^ s = ρ ^ s * c' * c'⁻¹ := by group
    rw [e]
    exact σ.ON.mul_mem hgs (σ.ON.inv_mem hc')
  have hρ1 : ρ ∉ σ.ON := fun h => hg1 (σ.ON.mul_mem h hcON)
  obtain ⟨j, o', hso', hon⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := σ.ON)).ne' s hs.one_lt.ne'
  set u := ρ ^ o' with hu
  have huK : u ∈ K := K.pow_mem hρK o'
  have huN : u ∈ σ.N := σ.N.pow_mem hρN o'
  have hupow : u ^ (s ^ (j + 1)) = 1 := by
    rw [hu, ← pow_mul]
    have e : o' * s ^ (j + 1) = s * Nat.card σ.ON := by
      rw [hon, pow_succ]
      ring
    rw [e, pow_mul]
    have h : (⟨ρ ^ s, hρs⟩ : σ.ON) ^ Nat.card σ.ON = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hmodd : Odd (s ^ (j + 1)) := (hs.odd_of_ne_two hs2).pow
  have hunot : u ∉ Subgroup.centralizer (W : Set G) := by
    intro huC
    have huSN : u ∈ solvRadIn σ.N := solvRadIn_inf_N_le hr d ⟨hCW ⟨huK, huC⟩, huN⟩
    rw [hN.N_solvRad] at huSN
    have huON : u ∈ σ.ON := mem_ON_of_mem_of_odd hσ hZ huSN hmodd hupow
    apply hρ1
    have hcop : Nat.Coprime s o' := (Nat.Prime.coprime_iff_not_dvd hs).mpr hso'
    have hb := Nat.gcd_eq_gcd_ab s o'
    rw [hcop.gcd_eq_one, Nat.cast_one] at hb
    have e : ρ ^ ((s : ℤ) * Nat.gcdA s o' + (o' : ℤ) * Nat.gcdB s o') = ρ := by
      rw [← hb, zpow_one]
    rw [← e, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    exact σ.ON.mul_mem (σ.ON.zpow_mem hρs _) (σ.ON.zpow_mem huON _)
  have huinv : σ.x₂ * u * σ.x₂⁻¹ = u⁻¹ := by rw [hu, ← conj_pow, hρinv, inv_pow]
  have hu2 : σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (W : Set G) := by
    rw [huinv, inv_mul_cancel]
    exact Subgroup.one_mem _
  set x' := u * σ.x₂ * u⁻¹ with hx'
  have hWu : W.map (MulAut.conj u).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKW huK)
  have hCx' : W ⊓ Subgroup.centralizer {x'} =
      (W ⊓ Subgroup.centralizer {σ.x₂}).map (MulAut.conj u).toMonoidHom := by
    ext w
    rw [mem_map_conj_iff, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hw, hwx⟩
      refine ⟨by simpa using conj_mem_of_mem_normalizer (hKW (K.inv_mem huK)) hw, ?_⟩
      calc u⁻¹ * w * u * σ.x₂ = u⁻¹ * (w * x') * u := by rw [hx']; group
        _ = u⁻¹ * (x' * w) * u := by rw [hwx]
        _ = σ.x₂ * (u⁻¹ * w * u) := by rw [hx']; group
    · rintro ⟨hw, hwx⟩
      refine ⟨by simpa [mul_assoc] using conj_mem_of_mem_normalizer (hKW huK) hw, ?_⟩
      calc w * x' = u * (u⁻¹ * w * u * σ.x₂) * u⁻¹ := by rw [hx']; group
        _ = u * (σ.x₂ * (u⁻¹ * w * u)) * u⁻¹ := by rw [hwx]
        _ = x' * w := by rw [hx']; group
  have hrefl' : (W ⊓ Subgroup.centralizer {x'}).relIndex W = r := by
    have h := Subgroup.relIndex_map_map_of_injective (W ⊓ Subgroup.centralizer {σ.x₂}) W
      (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
    rw [hWu] at h
    rw [hCx', h, hrefl]
  set V₀ := (W ⊓ Subgroup.centralizer {σ.x₂}) ⊓ (W ⊓ Subgroup.centralizer {x'}) with hV₀
  have hV₀W : V₀ ≤ W := inf_le_left.trans inf_le_left
  have hidx : V₀.relIndex W ≤ r * r := by
    have h := Subgroup.relIndex_inf_le (H := W ⊓ Subgroup.centralizer {σ.x₂})
      (K := W ⊓ Subgroup.centralizer {x'}) (L := W)
    rwa [hrefl, hrefl'] at h
  have hV₀ne : V₀ ≠ ⊥ := by
    intro h
    have hm := Subgroup.relIndex_mul_card V₀ W
    rw [inf_of_le_left hV₀W, h, Subgroup.card_bot, mul_one] at hm
    rw [h] at hidx
    rw [hm] at hidx
    rw [sq] at hbig
    omega
  obtain ⟨⟨a, haV⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀ne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hax₂ : Commute a σ.x₂ := Subgroup.mem_centralizer_singleton_iff.mp haV.1.2
  have hax' : Commute a x' := Subgroup.mem_centralizer_singleton_iff.mp haV.2.2
  have hprod : σ.x₂ * x' = u⁻¹ * u⁻¹ := by
    calc σ.x₂ * x' = σ.x₂ * u * σ.x₂⁻¹ * (σ.x₂ * σ.x₂) * u⁻¹ := by rw [hx']; group
      _ = u⁻¹ * u⁻¹ := by rw [huinv, hx₂x₂, mul_one]
  have hcomm2 : Commute a (u ^ 2) := by
    have h := (hprod ▸ hax₂.mul_right hax').inv_right
    rwa [mul_inv_rev, inv_inv, ← pow_two] at h
  have hcommu : Commute a u := by
    obtain ⟨m, hm⟩ := hmodd
    have e : u = (u ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = s ^ (j + 1) + 1 by omega, pow_succ, hupow, one_mul]
    rw [e]
    exact hcomm2.pow_right _
  refine ⟨u, huK, s, j + 1, hs, hs2, hsr, ?_, hunot, hu2, a, haV.1, ha1', hcommu.eq.symm⟩
  rw [hupow]
  exact Subgroup.one_mem _

theorem sq_lt_card_of_reflection (hσ : σ.IsValid) (hN : σ.NStructure)
    (hZ : centerOf (σ.S : Subgroup G) ≤ Subgroup.zpowers σ.x) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) {W : Subgroup G} (hWR : W ≤ d.R)
    (hKW : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWr : ∀ w ∈ W, w ^ r = 1)
    (hCW : Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
      solvRadIn (Subgroup.normalizer (d.R : Set G)))
    (hrefl : (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r)
    {v : G} (hvD : v ∈ σ.D) (hv2 : v * v = σ.x) (hvinv : σ.x₂ * v * σ.x₂⁻¹ = v⁻¹) :
    r ^ 2 < Nat.card W := by
  by_contra hle
  push Not at hle
  set K := Subgroup.normalizer (d.R : Set G) with hK
  have hx₂D : σ.x₂ ∈ σ.D := σ.T_le_D hσ σ.x₂_mem_T
  have hx₂K : σ.x₂ ∈ K := d.R_D hx₂D
  have hx₂N : σ.x₂ ∈ σ.N := σ.D_le_N hσ hx₂D
  have hx₂x₂ : σ.x₂ * σ.x₂ = 1 := by rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]
  have hx₂inv : σ.x₂⁻¹ = σ.x₂ := inv_eq_of_mul_eq_one_right hx₂x₂
  have hxx : σ.x * σ.x = 1 := by rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]
  have hx1 : σ.x ≠ 1 := fun h => by
    have := hσ.x_order
    rw [h, orderOf_one] at this
    omega
  have hvK : v ∈ K := d.R_D hvD
  have hvN : v ∈ σ.N := σ.D_le_N hσ hvD
  have hxC : σ.x ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (σ.mem_N_iff w).mp (σ.ON_le_N (d.R_sylow.le (hWR hw)))
  have hr2 : r ≠ 2 := fun h => by
    have hdvd := hr.dvd_ON
    rw [h] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn σ.N)) (even_iff_two_dvd.mpr hdvd)
  have hvv : σ.x₂ * v * σ.x₂⁻¹ * v ∈ Subgroup.centralizer (W : Set G) := by
    rw [hvinv, inv_mul_cancel]
    exact Subgroup.one_mem _
  obtain ⟨y, hy, hyact⟩ := exists_scalar_of_reflection_four_group hr.prime hr2 hWab hWr
    (hKW hx₂K) (hKW hvK) hx₂x₂ (by rw [hv2]; exact hxC) hvv hrefl hle
  have hx₂vv : σ.x₂ * v * (σ.x₂ * v) = 1 := by
    calc σ.x₂ * v * (σ.x₂ * v) = σ.x₂ * v * σ.x₂⁻¹ * v := by rw [hx₂inv]; group
      _ = 1 := by rw [hvinv, inv_mul_cancel]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  have hyK : y ∈ K := by
    rcases hy with hy | hy | hy <;> subst y
    · exact hx₂K
    · exact hvK
    · exact K.mul_mem hx₂K hvK
  have hyN : y ∈ σ.N := by
    rcases hy with hy | hy | hy <;> subst y
    · exact hx₂N
    · exact hvN
    · exact σ.N.mul_mem hx₂N hvN
  have hsq : (y ^ 2) ^ 2 = 1 := by
    rcases hy with hy | hy | hy <;> subst y
    · rw [sq σ.x₂, hx₂x₂, one_pow]
    · rw [sq v, hv2, sq, hxx]
    · rw [sq (σ.x₂ * v), hx₂vv, one_pow]
  have hy4 : y ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hsq]
  have hyS : y ∈ solvRadIn K := mem_solvRadIn_of_scalar hKW hCW hyK hyact
  have hySN : y ∈ σ.ON ⊔ centerOf (σ.S : Subgroup G) := by
    rw [← hN.N_solvRad]
    exact solvRadIn_inf_N_le hr d ⟨hyS, hyN⟩
  have key := eq_one_or_eq_x_of_mem hσ hZ hySN hy4
  rcases hy with hy | hy | hy <;> subst y <;> rcases key with h | h
  · have := hσ.x₂_order
    rw [h, orderOf_one] at this
    omega
  · exact hσ.x_ne_x₂ h.symm
  · rw [h, one_mul] at hv2
    exact hx1 hv2.symm
  · rw [h, hxx] at hv2
    exact hx1 hv2.symm
  · have hv : v = σ.x₂ := by
      rw [← inv_mul_cancel_left σ.x₂ v, h, mul_one, hx₂inv]
    rw [hv, hx₂x₂] at hv2
    exact hx1 hv2.symm
  · have hv : v = σ.x₂ * σ.x := by
      rw [← inv_mul_cancel_left σ.x₂ v, h, hx₂inv]
    have hcomm : σ.x₂ * σ.x = σ.x * σ.x₂ := hσ.commute.symm
    have : v * v = 1 := by
      rw [hv]
      calc σ.x₂ * σ.x * (σ.x₂ * σ.x) = σ.x₂ * (σ.x * σ.x₂) * σ.x := by group
        _ = σ.x₂ * (σ.x₂ * σ.x) * σ.x := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, hx₂x₂, one_mul, hxx]
    rw [hv2] at this
    exact hx1 this

theorem false_of_order_sixteen (hσ : σ.IsValid) (hN : σ.NStructure)
    (hZ : centerOf (σ.S : Subgroup G) ≤ Subgroup.zpowers σ.x) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) {W : Subgroup G} (hWR : W ≤ d.R)
    (hKW : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWr : ∀ w ∈ W, w ^ r = 1)
    (hCW : Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
      solvRadIn (Subgroup.normalizer (d.R : Set G)))
    (hrefl : (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r) (hr35 : r = 3 ∨ r = 5)
    {ρ : G} (hρK : ρ ∈ Subgroup.normalizer (d.R : Set G)) (hρN : ρ ∈ σ.N)
    (hρinv : σ.x₂ * ρ * σ.x₂⁻¹ * ρ = 1 ∨ σ.x₂ * ρ * σ.x₂⁻¹ * ρ = σ.x) (hρ8 : ρ ^ 8 = σ.x)
    (hρ4 : orderOf (ρ ^ 4) = 4) : False := by
  set K := Subgroup.normalizer (d.R : Set G) with hK
  have hx₂D : σ.x₂ ∈ σ.D := σ.T_le_D hσ σ.x₂_mem_T
  have hx₂K : σ.x₂ ∈ K := d.R_D hx₂D
  have hx₂x₂ : σ.x₂ * σ.x₂ = 1 := by rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]
  have hxC : σ.x ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (σ.mem_N_iff w).mp (σ.ON_le_N (d.R_sylow.le (hWR hw)))
  have hr2 : r ≠ 2 := by rcases hr35 with rfl | rfl <;> decide
  have hinvC : σ.x₂ * ρ * σ.x₂⁻¹ * ρ ∈ Subgroup.centralizer (W : Set G) := by
    rcases hρinv with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact hxC
  have h8C : ρ ^ 8 ∈ Subgroup.centralizer (W : Set G) := by
    rw [hρ8]
    exact hxC
  have h4C : ρ ^ 4 ∉ Subgroup.centralizer (W : Set G) := by
    intro h
    have hS : ρ ^ 4 ∈ solvRadIn K := hCW ⟨K.pow_mem hρK 4, h⟩
    have hSN : ρ ^ 4 ∈ σ.ON ⊔ centerOf (σ.S : Subgroup G) := by
      rw [← hN.N_solvRad]
      exact solvRadIn_inf_N_le hr d ⟨hS, σ.N.pow_mem hρN 4⟩
    have hpow : (ρ ^ 4) ^ 2 ^ 2 = 1 := by
      have h' := pow_orderOf_eq_one (ρ ^ 4)
      rw [hρ4] at h'
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact h'
    rcases eq_one_or_eq_x_of_mem hσ hZ hSN hpow with h1 | h1
    · rw [h1, orderOf_one] at hρ4
      omega
    · rw [h1, hσ.x_order] at hρ4
      omega
  obtain ⟨α, hα⟩ := exists_two_mul_sq_eq_one_of_reflection hr.prime hr2 hWab hWr (hKW hx₂K)
    (hKW hρK) hx₂x₂ hrefl hinvC h8C h4C
  rcases hr35 with rfl | rfl
  · have key : ∀ β : ZMod 3, 2 * β ^ 2 ≠ 1 := by decide
    exact key α hα
  · have key : ∀ β : ZMod 5, 2 * β ^ 2 ≠ 1 := by decide
    exact key α hα

end Setting

end CFSG.ABGTheoremB
