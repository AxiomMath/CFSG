module

public import CFSG.LargeExtraspecial.BridgeNat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Subgroup CFSG.Open

theorem le_timmesfeldFStar_of_normal {H : Type*} [Group H] {A : Subgroup H} (hA : A.Normal)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A ≤ timmesfeldFStar H := by
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
  exact le_sup_of_le_left (le_sSup ⟨hA, CommGroup.isNilpotent⟩)

theorem eq_one_or_eq_of_centralizes_fstar {H : Type*} [Group H]
    (hZ : Nat.card (center (timmesfeldFStar H)) = 2) {t : H} (htZ : t ∈ center H) (ht1 : t ≠ 1)
    {A : Subgroup H} (hA : A.Normal) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {s : H}
    (hs : s ∈ A) (hsc : ∀ x ∈ timmesfeldFStar H, x * s = s * x) : s = 1 ∨ s = t := by
  have htF : t ∈ timmesfeldFStar H :=
    le_timmesfeldFStar_of_normal (center H).normal_of_characteristic
      (fun a _ b hb => (mem_center_iff.mp hb a)) htZ
  have hsF : s ∈ timmesfeldFStar H := le_timmesfeldFStar_of_normal hA hAc hs
  set F := timmesfeldFStar H
  have htZ' : (⟨t, htF⟩ : F) ∈ center F :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp htZ g)
  have hsZ' : (⟨s, hsF⟩ : F) ∈ center F :=
    mem_center_iff.mpr fun g => Subtype.ext (hsc g g.2)
  by_contra hne
  obtain ⟨hs1, hst⟩ := not_or.mp hne
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : center F)).mp hZ
  have h1 := huniq ⟨⟨t, htF⟩, htZ'⟩ fun h => ht1 (congrArg (fun x : center F => (x : H)) h)
  have h2 := huniq ⟨⟨s, hsF⟩, hsZ'⟩ fun h => hs1 (congrArg (fun x : center F => (x : H)) h)
  exact hst (congrArg (fun x : center F => (x : H)) (h2.trans h1.symm))

theorem eq_bot_of_isPGroup_of_perfect {G : Type*} [Group G] {R : Subgroup G} [Finite R]
    (hR : IsPGroup 2 R) (hperf : ⁅R, R⁆ = R) : R = ⊥ := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries R).1 hR.isNilpotent
  have h : ∀ k, R.lowerCentralSeries k = R := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, hperf]
  rw [← h n, hn]

section AxisGroup

variable {G : Type*} [Group G] {R : Type*} [Ring R] (φ : G →* R)

theorem sub_one_mul_map_of_mem {t : G} (c : centralizer ({t} : Set G)) :
    (φ t - 1) * φ c = φ c * (φ t - 1) := by
  have h : φ (c : G) * φ t = φ t * φ c := by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp c.2]
  rw [sub_mul, mul_sub, one_mul, mul_one, h]

theorem mul_eq_zero_of_factor {D X Y P Q : R} (hD : D * D = 0) (hP : P = D * X)
    (hQ : Q = Y * D) : Q * P = 0 := by
  rw [hP, hQ, mul_assoc, ← mul_assoc D, hD, zero_mul, mul_zero]

@[expose] def axisGroupOf (t : G) (hD : (φ t - 1) * (φ t - 1) = 0) :
    Subgroup (centralizer ({t} : Set G)) where
  carrier := {c | (∃ X, φ c - 1 = (φ t - 1) * X) ∧ ∃ Y, φ c - 1 = Y * (φ t - 1)}
  mul_mem' := by
    rintro a b ⟨⟨Xa, hXa⟩, ⟨Ya, hYa⟩⟩ ⟨⟨Xb, hXb⟩, ⟨Yb, hYb⟩⟩
    have h0 := mul_eq_zero_of_factor hD hXb hYa
    have e : φ ((a * b : centralizer ({t} : Set G)) : G) - 1 =
        (φ a - 1) + (φ b - 1) + (φ a - 1) * (φ b - 1) := by
      rw [Subgroup.coe_mul, map_mul]
      noncomm_ring
    refine ⟨⟨Xa + Xb, ?_⟩, ⟨Ya + Yb, ?_⟩⟩
    · rw [e, h0, add_zero, mul_add, ← hXa, ← hXb]
    · rw [e, h0, add_zero, add_mul, ← hYa, ← hYb]
  one_mem' := ⟨⟨0, by rw [Subgroup.coe_one, map_one, sub_self, mul_zero]⟩,
    ⟨0, by rw [Subgroup.coe_one, map_one, sub_self, zero_mul]⟩⟩
  inv_mem' := by
    rintro a ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩
    have h0 := mul_eq_zero_of_factor hD hX hY
    have hinv : φ ((a⁻¹ : centralizer ({t} : Set G)) : G) = 1 - (φ a - 1) := by
      have e : φ (a : G) * (1 - (φ a - 1)) = 1 - (φ a - 1) * (φ a - 1) := by noncomm_ring
      rw [h0, sub_zero] at e
      have h1 : φ ((a⁻¹ : centralizer ({t} : Set G)) : G) * φ a = 1 := by
        rw [← map_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, map_one]
      calc φ ((a⁻¹ : centralizer ({t} : Set G)) : G) =
            φ ((a⁻¹ : centralizer ({t} : Set G)) : G) * (φ a * (1 - (φ a - 1))) := by
              rw [e, mul_one]
        _ = 1 - (φ a - 1) := by rw [← mul_assoc, h1, one_mul]
    refine ⟨⟨-X, ?_⟩, ⟨-Y, ?_⟩⟩
    · rw [hinv, sub_sub_cancel_left, hX, mul_neg]
    · rw [hinv, sub_sub_cancel_left, hY, neg_mul]

theorem mem_axisGroupOf {t : G} {hD : (φ t - 1) * (φ t - 1) = 0}
    {c : centralizer ({t} : Set G)} :
    c ∈ axisGroupOf φ t hD ↔ (∃ X, φ c - 1 = (φ t - 1) * X) ∧ ∃ Y, φ c - 1 = Y * (φ t - 1) :=
  Iff.rfl

theorem axisGroupOf_normal (t : G) (hD : (φ t - 1) * (φ t - 1) = 0) :
    (axisGroupOf φ t hD).Normal := by
  refine ⟨fun a ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ g => ?_⟩
  have hgg : φ (g : G) * φ ((g⁻¹ : centralizer ({t} : Set G)) : G) = 1 := by
    rw [← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one]
  have e : φ ((g * a * g⁻¹ : centralizer ({t} : Set G)) : G) - 1 =
      φ g * (φ a - 1) * φ (g⁻¹ : centralizer ({t} : Set G)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, mul_sub, sub_mul, mul_one, hgg]
  refine ⟨⟨φ g * X * φ (g⁻¹ : centralizer ({t} : Set G)), ?_⟩,
    ⟨φ g * Y * φ (g⁻¹ : centralizer ({t} : Set G)), ?_⟩⟩
  · rw [e, hX, ← mul_assoc, ← sub_one_mul_map_of_mem, mul_assoc, mul_assoc, mul_assoc]
  · rw [e, hY, mul_assoc, mul_assoc, sub_one_mul_map_of_mem, ← mul_assoc, ← mul_assoc]

theorem axisGroupOf_comm (hφ : Function.Injective φ) (t : G)
    (hD : (φ t - 1) * (φ t - 1) = 0) :
    ∀ a ∈ axisGroupOf φ t hD, ∀ b ∈ axisGroupOf φ t hD, a * b = b * a := by
  rintro a ⟨⟨Xa, hXa⟩, ⟨Ya, hYa⟩⟩ b ⟨⟨Xb, hXb⟩, ⟨Yb, hYb⟩⟩
  have h1 := mul_eq_zero_of_factor hD hXb hYa
  have h2 := mul_eq_zero_of_factor hD hXa hYb
  apply Subtype.ext
  apply hφ
  have e1 : φ (a : G) * φ b = 1 + (φ a - 1) + (φ b - 1) + (φ a - 1) * (φ b - 1) := by
    noncomm_ring
  have e2 : φ (b : G) * φ a = 1 + (φ a - 1) + (φ b - 1) + (φ b - 1) * (φ a - 1) := by
    noncomm_ring
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, e1, e2, h1, h2]

end AxisGroup

theorem exists_ne_zero_forall_eq {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : P →* Module.End K V) {U : Submodule K V} (hU : U ≠ ⊥)
    (hρU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) : ∃ u ∈ U, u ≠ 0 ∧ ∀ g, ρ g u = u := by
  let _ : MulAction P U :=
    { smul := fun g u => ⟨ρ g u, hρU g u u.2⟩
      one_smul := fun u => Subtype.ext (by
        change ρ 1 u = u
        rw [map_one, Module.End.one_apply])
      mul_smul := fun g h u => Subtype.ext (by
        change ρ (g * h) u = ρ g (ρ h u)
        rw [map_mul, Module.End.mul_apply]) }
  have : Finite V := Module.finite_of_finite K
  have : Fintype K := Fintype.ofFinite K
  have hK : 2 ∣ Nat.card K := by
    obtain ⟨k, -, hk⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hk]
    exact dvd_pow_self 2 k.ne_zero
  have hcard : 2 ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := K)]
    exact hK.trans (dvd_pow_self _ fun h => hU (Submodule.finrank_eq_zero.mp h))
  have h0 : (0 : U) ∈ MulAction.fixedPoints P U := fun g =>
    Subtype.ext (show ρ g 0 = 0 from map_zero _)
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hcard h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun g => ?_⟩
  exact congrArg Subtype.val (hb g)

@[expose] def Conclusion (Y : Type*) [Group Y] (y : Y) : Prop :=
  timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({y} : Set Y))) →
    Nat.card (timmesfeldFStar (centralizer ({y} : Set Y))) = 2 ^ 17 →
    ∀ K : Subgroup (centralizer ({y} : Set Y)), K.Normal → ⁅K, K⁆ = K →
      timmesfeldFStar (centralizer ({y} : Set Y)) ≤ K → 2 ^ 45 ∣ Nat.card K

theorem timmesfeldIsExtraspecial_fstar_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X)
    (h : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({x} : Set X)))) :
    timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({e x} : Set Y))) :=
  Bridge.timmesfeldIsExtraspecial_of_mulEquiv (Bridge.equivOfMapEq _
    (Bridge.timmesfeldFStar_map (CFSG.Monster.GMS.centralizerMulEquiv e x))) h

theorem Conclusion.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X}
    (h : Conclusion Y (e x)) : Conclusion X x := by
  intro hext hcard K hK hperf hN
  set c := CFSG.Monster.GMS.centralizerMulEquiv e x
  have hF := Bridge.timmesfeldFStar_map c
  have f := Bridge.equivOfMapEq c hF
  have hK' : (K.map c.toMonoidHom).Normal := hK.map _ c.surjective
  have hperf' : ⁅K.map c.toMonoidHom, K.map c.toMonoidHom⁆ = K.map c.toMonoidHom := by
    rw [← map_commutator, hperf]
  have hN' : timmesfeldFStar (centralizer ({e x} : Set Y)) ≤ K.map c.toMonoidHom := by
    rw [← hF]
    exact map_mono hN
  have := h (Bridge.timmesfeldIsExtraspecial_of_mulEquiv f hext)
    (by rw [← hcard]; exact Nat.card_congr f.toEquiv.symm) _ hK' hperf' hN'
  rwa [card_map_of_injective c.injective] at this

end CFSG.LargeExtraspecial.S14.PSLPSU10
