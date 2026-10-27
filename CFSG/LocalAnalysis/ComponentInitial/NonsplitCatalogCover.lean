module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalogModel
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalogRadical
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverRadical
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherField

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthogonalTail NormTail
open scoped commutatorElement Pointwise

section Generic

variable {E X : Type*} [Group E] [Group X] {θ : E →* X} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

include hθ in
theorem comap_le_of_le_closure {S : Set X} {H : Subgroup X} (hH : H ≤ Subgroup.closure S)
    {P : Subgroup E} (hker : θ.ker ≤ P) (hS : ∀ e, θ e ∈ S → e ∈ P) : H.comap θ ≤ P := by
  have hle : Subgroup.closure S ≤ P.map θ := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨e, rfl⟩ := hθ x
    exact ⟨e, hS e hx, rfl⟩
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hle (hH hx)
  have hk : p⁻¹ * x ∈ P := hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel])
  have h := P.mul_mem hp hk
  rwa [mul_inv_cancel_left] at h

include hC in
theorem comm_eq_of_map_eq {x x' y y' : E} (hx : θ x = θ x') (hy : θ y = θ y') :
    ⁅x, y⁆ = ⁅x', y'⁆ :=
  LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq θ (fun _ hz => hC hz) hx hy

theorem exists_pow_conj_eq {g m c w : E} {W : Subgroup E} (hc : c ∈ Subgroup.center E)
    (hW : ∀ v ∈ W, g * v * g⁻¹ ∈ W) (hw : w ∈ W) (h : g * m * g⁻¹ = c * w * m) (n : ℕ) :
    ∃ v ∈ W, g ^ n * m * (g ^ n)⁻¹ = c ^ n * v * m := by
  induction n with
  | zero => exact ⟨1, W.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨v, hv, hn⟩ := ih
    refine ⟨g * v * g⁻¹ * w, W.mul_mem (hW v hv) hw, ?_⟩
    have hcn : c ^ n ∈ Subgroup.center E := Subgroup.pow_mem _ hc n
    calc g ^ (n + 1) * m * (g ^ (n + 1))⁻¹ = g * (g ^ n * m * (g ^ n)⁻¹) * g⁻¹ := by group
      _ = g * c ^ n * v * m * g⁻¹ := by rw [hn]; group
      _ = c ^ n * g * v * m * g⁻¹ := by rw [Subgroup.mem_center_iff.mp hcn g]
      _ = c ^ n * (g * v * g⁻¹) * (g * m * g⁻¹) := by group
      _ = c ^ n * ((g * v * g⁻¹) * c) * w * m := by rw [h]; group
      _ = c ^ n * (c * (g * v * g⁻¹)) * w * m := by
          rw [Subgroup.mem_center_iff.mp hc (g * v * g⁻¹)]
      _ = c ^ (n + 1) * (g * v * g⁻¹ * w) * m := by rw [pow_succ]; group

omit [Group X] in
theorem eq_one_of_pow_eq_one {X : Type*} [Group X] {θ : E →* X} (h2 : IsPGroup 2 θ.ker)
    {c : E} (hc : θ c = 1) {n : ℕ} (hn : Odd n) (hcn : c ^ n = 1) : c = 1 := by
  obtain ⟨k, hk⟩ := h2 ⟨c, hc⟩
  have hk' : c ^ 2 ^ k = 1 := by
    simpa using congrArg (fun w : θ.ker => (w : E)) hk
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_of_pow_eq_one hcn))

variable (θ) in
@[expose] def conjComm (V : Subgroup X) (g₀ : E) (hg₀ : ∀ y, θ y ∈ V → θ (g₀ * y * g₀⁻¹) ∈ V)
    (hV : ∀ x y, θ x ∈ V → θ y ∈ V → x * y = y * x) : Subgroup E where
  carrier := {x | ∃ y, θ y ∈ V ∧ x = g₀ * y * g₀⁻¹ * y⁻¹}
  one_mem' := ⟨1, by rw [map_one]; exact one_mem _, by group⟩
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨y * y', by rw [map_mul]; exact mul_mem hy hy', ?_⟩
    have h1 := hV (g₀ * y' * g₀⁻¹) y⁻¹ (hg₀ y' hy') (by rw [map_inv]; exact inv_mem hy)
    have h2 := hV y y' hy hy'
    calc g₀ * y * g₀⁻¹ * y⁻¹ * (g₀ * y' * g₀⁻¹ * y'⁻¹)
        = g₀ * y * g₀⁻¹ * (y⁻¹ * (g₀ * y' * g₀⁻¹)) * y'⁻¹ := by group
      _ = g₀ * y * g₀⁻¹ * ((g₀ * y' * g₀⁻¹) * y⁻¹) * y'⁻¹ := by rw [h1]
      _ = g₀ * (y * y') * g₀⁻¹ * (y' * y)⁻¹ := by group
      _ = g₀ * (y * y') * g₀⁻¹ * (y * y')⁻¹ := by rw [h2]
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y⁻¹, by rw [map_inv]; exact inv_mem hy, ?_⟩
    have h1 := hV y (g₀ * y⁻¹ * g₀⁻¹) hy (hg₀ y⁻¹ (by rw [map_inv]; exact inv_mem hy))
    calc (g₀ * y * g₀⁻¹ * y⁻¹)⁻¹ = y * (g₀ * y⁻¹ * g₀⁻¹) := by group
      _ = g₀ * y⁻¹ * g₀⁻¹ * y := h1
      _ = g₀ * y⁻¹ * g₀⁻¹ * y⁻¹⁻¹ := by rw [inv_inv]

end Generic

section Radical

variable {K F : Type} [Field K] [Field F] [Algebra K F] [CharP K 2] [Finite K]
  {T : NormTailData K F} {r : ℕ} {E : Type*} [Group E] {θ : E →* G0 T r}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem lift_zRt_commute_lift_xRt {s : Kˣ} (hs : (s : K) ≠ 1) {i j k : Fin r} (hij : i ≠ j)
    {e e' : E} {a : K} {z : F} (he : θ e = zRt T i j a) (he' : θ e' = xRt T k z) :
    e * e' = e' * e := by
  obtain ⟨m, hmij, hmk⟩ : ∃ m, (m = i ∨ m = j) ∧ m ≠ k := by
    by_cases hki : k = i
    · subst hki
      exact ⟨j, Or.inr rfl, Ne.symm hij⟩
    · exact ⟨i, Or.inl rfl, Ne.symm hki⟩
  refine LinearCover.lift_mul_comm_of_torus θ (fun _ hz => hC hz) hθ (x := zRt T i j)
    (y := fun b : K => xRt T k (b • z)) (zRt_add T i j)
    (fun _ _ => radTau_mul_comm T _ (xRt_mem_radN T k _))
    (t := torusE T r (Pi.mulSingle m s)) (r := (s : K)) hs (fun c => ?_) (fun c => ?_) he
    (b := 1) (by rw [he', one_smul])
  · rw [torusE_conj_zRt]
    congr 1
    rcases hmij with rfl | rfl
    · simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]
    · simp [Pi.mulSingle_eq_of_ne hij]
  · rw [torusE_conj_xRt, Pi.mulSingle_eq_of_ne (Ne.symm hmk), Units.val_one, one_smul]

include hθ hC in
theorem commute_of_mem_preV {s : Kˣ} (hs : (s : K) ≠ 1) (hF : Module.finrank K F = 2)
    {t m : E} (ht : θ t ∈ (radTau T r).range) (hm : θ m ∈ radN T r) : t * m = m * t := by
  have hroot : ∀ e, θ e ∈ {g | ∃ k z, xRt T k z = g} → e ∈ Subgroup.centralizer {t} := by
    rintro e ⟨k, z, hez⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hT : ((radTau T r).range).comap θ ≤ Subgroup.centralizer {e} :=
      comap_le_of_le_closure hθ (range_radTau_le_closure T)
        (fun c hc => Subgroup.center_le_centralizer _ (hC hc)) fun e' he' => by
          obtain ⟨i, j, a, hij, he'⟩ := he'
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact lift_zRt_commute_lift_xRt hθ hC hs hij.ne he'.symm hez.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hT ht)).symm
  have hM := comap_le_of_le_closure hθ (radN_le_closure T hF)
    (fun c hc => Subgroup.center_le_centralizer _ (hC hc)) hroot hm
  exact (Subgroup.mem_centralizer_singleton_iff.mp hM).symm

include hθ hC in
theorem lift_xRt_commute [Finite E] (hF : Module.finrank K F = 2) {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (h2 : IsPGroup 2 θ.ker) {k : Fin r} {e e' : E}
    {z w : F} (he : θ e = xRt T k z) (he' : θ e' = xRt T k w) : e * e' = e' * e := by
  have : Module.Finite K F := Module.finite_of_finrank_pos (by omega)
  have : Finite F := Module.finite_of_finite K
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  have hcardF : Nat.card F = 2 ^ (2 * f) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hF, hcard, ← pow_mul, mul_comm]
  have : Fintype F := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq hle
    exact ⟨t, ht⟩
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have : Group.IsPerfect (rhoG T k).range := Group.IsPerfect.range _
  set Fk := ⁅(rhoG T k).range.comap θ, (rhoG T k).range.comap θ⁆ with hFk
  obtain ⟨θF, hθF, hθFι⟩ :=
    SymplecticSixCover.exists_derivedComap_cover hθ (rhoG T k) (rhoG_injective T k)
  have hker : ∀ x : Fk, θF x = 1 ↔ θ x = 1 := fun x => by
    rw [← hθFι, ← map_one (rhoG T k)]
    exact (rhoG_injective T k).eq_iff.symm
  have : Group.IsPerfect Fk := SymplecticSixCover.isPerfect_derivedComap hθ hC _
  have hcen : θF.ker ≤ Subgroup.center Fk := fun x hx => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hker x).mp hx)) g)
  have h2F : IsPGroup 2 θF.ker := fun x => by
    obtain ⟨n, hn⟩ := h2 ⟨(x : Fk), (hker x).mp x.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  have hbot := CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot
    (2 * f) (by omega) hcardF θF hθF hcen h2F
  have hmapF : ∀ g ∈ (rhoG T k).range, ∃ y ∈ Fk, θ y = g := fun g hg => by
    rw [← SymplecticSixCover.map_derivedComap hθ (rhoG T k).range] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨y, hy, rfl⟩
  obtain ⟨y, hy, hye⟩ := hmapF (θ e) (by rw [he]; exact ⟨upperSL F z, rfl⟩)
  obtain ⟨y', hy', hye'⟩ := hmapF (θ e') (by rw [he']; exact ⟨upperSL F w, rfl⟩)
  have hyy : ⁅y, y'⁆ ∈ Fk := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
  have h1 : θ ⁅y, y'⁆ = 1 := by
    rw [map_commutatorElement, hye, hye', he, he', commutatorElement_eq_one_iff_mul_comm]
    exact (xRt_commute T k z w).eq
  have h3 : (⟨⁅y, y'⁆, hyy⟩ : Fk) ∈ θF.ker := (hker _).mpr h1
  rw [hbot, Subgroup.mem_bot] at h3
  have h4 : ⁅e, e'⁆ = 1 := by
    rw [comm_eq_of_map_eq hC hye.symm hye'.symm]
    exact congrArg Subtype.val h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h4

end Radical

section Tilde

variable {K F : Type} [Field K] [Field F] [Algebra K F] [CharP K 2] [Finite K]
  {T : NormTailData K F} {r : ℕ} {E : Type*} [Group E] {θ : E →* G0 T r}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

theorem torusE_conj_mem_range_radTau (a : Fin r → Kˣ) {g : G0 T r}
    (hg : g ∈ (radTau T r).range) :
    torusE T r a * g * (torusE T r a)⁻¹ ∈ (radTau T r).range := by
  obtain ⟨hN, hπ⟩ := torusE_conj_mem_radN T a (range_radTau_le T hg)
  refine (radCoord_eq_zero_iff T hN).1 ?_
  rw [hπ, (radCoord_eq_zero_iff T (range_radTau_le T hg)).2 hg]
  funext j
  simp

include hC in
theorem eq_one_of_mem_conjComm (h2 : IsPGroup 2 θ.ker) {s : Kˣ} {t₀ : E}
    (ht₀ : θ t₀ = torusE T r (fun _ => s)) {V : Subgroup (G0 T r)}
    {hg₀ : ∀ y, θ y ∈ V → θ (t₀ * y * t₀⁻¹) ∈ V} {hV : ∀ x y, θ x ∈ V → θ y ∈ V → x * y = y * x}
    {x : E} (hx : x ∈ conjComm θ V t₀ hg₀ hV) (hθx : θ x = 1) : x = 1 := by
  obtain ⟨y, -, rfl⟩ := hx
  have hxc := hC hθx
  have hconj : t₀ * y * t₀⁻¹ = (t₀ * y * t₀⁻¹ * y⁻¹) * 1 * y := by group
  obtain ⟨v, hv, hn⟩ := exists_pow_conj_eq hxc (W := ⊥)
    (fun v hv => by rw [Subgroup.mem_bot.mp hv, mul_one, mul_inv_cancel]; exact one_mem _)
    (one_mem _) hconj (Nat.card Kˣ)
  have hgm : θ (t₀ ^ Nat.card Kˣ) = 1 := by
    rw [map_pow, ht₀, ← map_pow]
    have h1 : (fun _ : Fin r => s) ^ Nat.card Kˣ = 1 := by
      funext i
      exact pow_card_eq_one'
    rw [h1, map_one]
  have hcen := hC hgm
  rw [Subgroup.mem_bot.mp hv, mul_one, ← Subgroup.mem_center_iff.mp hcen y,
    mul_inv_cancel_right] at hn
  exact eq_one_of_pow_eq_one h2 hθx SymplecticSixCover.odd_card_units_of_charTwo
    (mul_eq_right.mp hn.symm)

include hθ in
theorem exists_mem_conjComm {s : Kˣ} (hs : (s : K) ≠ 1) {t₀ : E}
    (ht₀ : θ t₀ = torusE T r (fun _ => s))
    {hg₀ : ∀ y, θ y ∈ (radTau T r).range → θ (t₀ * y * t₀⁻¹) ∈ (radTau T r).range}
    {hV : ∀ x y, θ x ∈ (radTau T r).range → θ y ∈ (radTau T r).range → x * y = y * x}
    (B : OrthogonalSplit.altSubgroup r K) :
    ∃ x ∈ conjComm θ (radTau T r).range t₀ hg₀ hV, θ x = radTau T r (Multiplicative.ofAdd B) := by
  have hc : (s : K) * s - 1 ≠ 0 := sub_ne_zero.mpr (LinearCover.mul_self_ne_one hs)
  set B' : OrthogonalSplit.altSubgroup r K :=
    ⟨((s : K) * s - 1)⁻¹ • (B : Matrix (Fin r) (Fin r) K),
      OrthogonalSplit.smul_mem_altSubgroup _ B.2⟩ with hB'
  obtain ⟨y, hy⟩ := hθ (radTau T r (Multiplicative.ofAdd B'))
  refine ⟨t₀ * y * t₀⁻¹ * y⁻¹, ⟨y, ⟨_, hy.symm⟩, rfl⟩, ?_⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ht₀, hy, torusE_const_conj_radTau, ← map_inv,
    ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change ((s : K) * s) • (((s : K) * s - 1)⁻¹ • (B : Matrix (Fin r) (Fin r) K)) +
    -(((s : K) * s - 1)⁻¹ • (B : Matrix (Fin r) (Fin r) K)) = B
  rw [smul_smul, ← sub_eq_add_neg, ← sub_smul, ← sub_one_mul, mul_inv_cancel₀ hc, one_smul]

omit [CharP K 2] [Finite K] in
include hC in
theorem conj_mem_conjComm {t₀ g : E} {V : Subgroup (G0 T r)}
    {hg₀ : ∀ y, θ y ∈ V → θ (t₀ * y * t₀⁻¹) ∈ V} {hV : ∀ x y, θ x ∈ V → θ y ∈ V → x * y = y * x}
    (hgt : θ g * θ t₀ = θ t₀ * θ g) (hgV : ∀ y, θ y ∈ V → θ (g * y * g⁻¹) ∈ V) {x : E}
    (hx : x ∈ conjComm θ V t₀ hg₀ hV) : g * x * g⁻¹ ∈ conjComm θ V t₀ hg₀ hV := by
  obtain ⟨y, hy, rfl⟩ := hx
  set k := t₀⁻¹ * g * t₀ * g⁻¹ with hk
  have hkc : k ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, hk, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (θ g),
      hgt]
    group)
  have hg : g * t₀ = t₀ * k * g := by rw [hk]; group
  refine ⟨g * y * g⁻¹, hgV y hy, ?_⟩
  have hkz : k * (g * y * g⁻¹) * k⁻¹ = g * y * g⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hkc (g * y * g⁻¹), mul_inv_cancel_right]
  calc g * (t₀ * y * t₀⁻¹ * y⁻¹) * g⁻¹ = (g * t₀) * y * (g * t₀)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
    _ = (t₀ * k * g) * y * (t₀ * k * g)⁻¹ * (g * y * g⁻¹)⁻¹ := by rw [hg]
    _ = t₀ * (k * (g * y * g⁻¹) * k⁻¹) * t₀⁻¹ * (g * y * g⁻¹)⁻¹ := by group
    _ = t₀ * (g * y * g⁻¹) * t₀⁻¹ * (g * y * g⁻¹)⁻¹ := by rw [hkz]

include hθ hC in
theorem conj_mul_inv_mem_conjComm {s : Kˣ} (hs : (s : K) ≠ 1) {t₀ g : E}
    (ht₀ : θ t₀ = torusE T r (fun _ => s))
    {hg₀ : ∀ y, θ y ∈ (radTau T r).range → θ (t₀ * y * t₀⁻¹) ∈ (radTau T r).range}
    {hV : ∀ x y, θ x ∈ (radTau T r).range → θ y ∈ (radTau T r).range → x * y = y * x}
    (hgt : θ g * θ t₀ = θ t₀ * θ g)
    (hgV : ∀ y, θ y ∈ (radTau T r).range → θ (g * y * g⁻¹) ∈ (radTau T r).range) {v : E}
    (hv : θ v ∈ (radTau T r).range) :
    g * v * g⁻¹ * v⁻¹ ∈ conjComm θ (radTau T r).range t₀ hg₀ hV := by
  obtain ⟨B, hB⟩ := hv
  obtain ⟨x, hx, hxB⟩ := exists_mem_conjComm hθ hs ht₀ (hg₀ := hg₀) (hV := hV) B.toAdd
  rw [ofAdd_toAdd] at hxB
  have hc : x⁻¹ * v ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxB, hB, inv_mul_cancel])
  have hcg : (x⁻¹ * v) * g⁻¹ * (x⁻¹ * v)⁻¹ = g⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hc g⁻¹, mul_inv_cancel_right]
  have heq : g * v * g⁻¹ * v⁻¹ = (g * x * g⁻¹) * x⁻¹ := by
    calc g * v * g⁻¹ * v⁻¹ = g * x * ((x⁻¹ * v) * g⁻¹ * (x⁻¹ * v)⁻¹) * x⁻¹ := by group
      _ = (g * x * g⁻¹) * x⁻¹ := by rw [hcg]
  rw [heq]
  exact mul_mem (conj_mem_conjComm hC hgt hgV hx) (inv_mem hx)

include hθ hC in
theorem commutatorElement_mem_conjComm [Finite E] (hF : Module.finrank K F = 2) {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (h2 : IsPGroup 2 θ.ker) {s : Kˣ}
    (hs : (s : K) ≠ 1) {t₀ : E} (ht₀ : θ t₀ = torusE T r (fun _ => s))
    {hg₀ : ∀ y, θ y ∈ (radTau T r).range → θ (t₀ * y * t₀⁻¹) ∈ (radTau T r).range}
    {hV : ∀ x y, θ x ∈ (radTau T r).range → θ y ∈ (radTau T r).range → x * y = y * x}
    {m m' : E} (hm : θ m ∈ radN T r) (hm' : θ m' ∈ radN T r) :
    ⁅m, m'⁆ ∈ conjComm θ (radTau T r).range t₀ hg₀ hV := by
  set Vt := conjComm θ (radTau T r).range t₀ hg₀ hV with hVt
  have hTc : ∀ {v x : E}, θ v ∈ (radTau T r).range → θ x ∈ radN T r → v * x = x * v :=
    fun hv hx => commute_of_mem_preV hθ hC hs hF hv hx
  have hcommT : ∀ {x y : E}, θ x ∈ radN T r → θ y ∈ radN T r →
      θ ⁅x, y⁆ ∈ (radTau T r).range := fun hx hy => by
    rw [map_commutatorElement]
    exact commutatorElement_mem_range_radTau T hx hy
  have hcen : ∀ {x y : E}, θ x ∈ radN T r → θ y ∈ radN T r → ∀ {z : E}, θ z ∈ radN T r →
      z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := fun hx hy z hz => by
    rw [← hTc (hcommT hx hy) hz, mul_inv_cancel_right]
  have hgen : ∀ {e e' : E} {i j : Fin r} {z w : F}, θ e = xRt T i z → θ e' = xRt T j w →
      ⁅e, e'⁆ ∈ Vt := by
    intro e e' i j z w he he'
    by_cases hij : i = j
    · subst hij
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (lift_xRt_commute hθ hC hF hcard hf h2 he he')]
      exact one_mem _
    · obtain ⟨t₁, ht₁⟩ := hθ (torusE T r (Pi.mulSingle i s))
      choose ℓ hℓ using fun a : K => hθ (xRt T i (a • z))
      have hℓN : ∀ a, θ (ℓ a) ∈ radN T r := fun a => by rw [hℓ]; exact xRt_mem_radN T i _
      have he'N : θ e' ∈ radN T r := by rw [he']; exact xRt_mem_radN T j w
      have hcT : ∀ a, θ ⁅ℓ a, e'⁆ ∈ (radTau T r).range := fun a => hcommT (hℓN a) he'N
      have hadd : ∀ a b, ⁅ℓ (a + b), e'⁆ = ⁅ℓ a, e'⁆ * ⁅ℓ b, e'⁆ := by
        intro a b
        have h1 : ⁅ℓ (a + b), e'⁆ = ⁅ℓ a * ℓ b, e'⁆ := comm_eq_of_map_eq hC
          (by rw [hℓ, map_mul, hℓ, hℓ, add_smul, xRt_add]) rfl
        have hid : ⁅ℓ a * ℓ b, e'⁆ = ℓ a * ⁅ℓ b, e'⁆ * (ℓ a)⁻¹ * ⁅ℓ a, e'⁆ := by
          simp only [commutatorElement_def]
          group
        rw [h1, hid, hcen (hℓN b) he'N (hℓN a)]
        exact hTc (hcT b) (range_radTau_le T (hcT a))
      have hgt : θ t₁ * θ t₀ = θ t₀ * θ t₁ := by
        rw [ht₁, ht₀]
        exact (torusE_commute T _ _).eq
      have hgV : ∀ y, θ y ∈ (radTau T r).range → θ (t₁ * y * t₁⁻¹) ∈ (radTau T r).range :=
        fun y hy => by
          rw [map_mul, map_mul, map_inv, ht₁]
          exact torusE_conj_mem_range_radTau _ hy
      have hinv : ∀ a, ⁅ℓ (s * a), e'⁆ * ⁅ℓ a, e'⁆⁻¹ ∈ Vt := by
        intro a
        have h1 : t₁ * ⁅ℓ a, e'⁆ * t₁⁻¹ = ⁅ℓ (s * a), e'⁆ := by
          have h0 : t₁ * ⁅ℓ a, e'⁆ * t₁⁻¹ = ⁅t₁ * ℓ a * t₁⁻¹, t₁ * e' * t₁⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
          rw [h0]
          refine comm_eq_of_map_eq hC ?_ ?_
          · rw [map_mul, map_mul, map_inv, ht₁, hℓ, torusE_conj_xRt, hℓ, Pi.mulSingle_eq_same,
              smul_smul]
          · rw [map_mul, map_mul, map_inv, ht₁, he', torusE_conj_xRt,
              Pi.mulSingle_eq_of_ne (Ne.symm hij), Units.val_one, one_smul]
        rw [← h1]
        exact conj_mul_inv_mem_conjComm hθ hC hs ht₀ hgt hgV (hcT a)
      have hfin : ∀ a, ⁅ℓ a, e'⁆ ∈ Vt := by
        intro a
        have hs1 : (s : K) - 1 ≠ 0 := sub_ne_zero.mpr hs
        have h1 := hinv (((s : K) - 1)⁻¹ * a)
        rwa [show (s : K) * (((s : K) - 1)⁻¹ * a) = a + ((s : K) - 1)⁻¹ * a by
          field_simp; ring, hadd, mul_inv_cancel_right] at h1
      rw [comm_eq_of_map_eq hC (x' := ℓ 1) (by rw [he, hℓ, one_smul]) rfl]
      exact hfin 1
  have hsecond : ∀ {e : E} {i : Fin r} {z : F}, θ e = xRt T i z → ∀ {y : E},
      θ y ∈ radN T r → ⁅e, y⁆ ∈ Vt := by
    intro e i z he
    have heN : θ e ∈ radN T r := by rw [he]; exact xRt_mem_radN T i z
    let P : Subgroup E :=
      { carrier := {y | θ y ∈ radN T r ∧ ⁅e, y⁆ ∈ Vt}
        one_mem' := ⟨by rw [map_one]; exact one_mem _, by
          rw [commutatorElement_one_right]; exact one_mem _⟩
        mul_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨by rw [map_mul]; exact mul_mem hx hy, ?_⟩
          have hid : ⁅e, x * y⁆ = ⁅e, x⁆ * (x * ⁅e, y⁆ * x⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [hid, hcen heN hy hx]
          exact mul_mem hx' hy'
        inv_mem' := by
          rintro x ⟨hx, hx'⟩
          have hxi : θ x⁻¹ ∈ radN T r := by rw [map_inv]; exact inv_mem hx
          refine ⟨hxi, ?_⟩
          have hid : ⁅e, x⁻¹⁆ = (x⁻¹ * ⁅e, x⁆ * x⁻¹⁻¹)⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [hid, hcen heN hx hxi]
          exact inv_mem hx' }
    have hle : (radN T r).comap θ ≤ P := comap_le_of_le_closure hθ (radN_le_closure T hF)
      (fun c hc => ⟨by rw [hc]; exact one_mem _, by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hC hc) e)]
        exact one_mem _⟩)
      (fun e' ⟨j, w, he'⟩ => ⟨by rw [← he']; exact xRt_mem_radN T j w, hgen he he'.symm⟩)
    exact fun y hy => (hle hy).2
  let P : Subgroup E :=
    { carrier := {x | θ x ∈ radN T r ∧ ∀ y, θ y ∈ radN T r → ⁅x, y⁆ ∈ Vt}
      one_mem' := ⟨by rw [map_one]; exact one_mem _, fun y _ => by
        rw [commutatorElement_one_left]; exact one_mem _⟩
      mul_mem' := by
        rintro x x' ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨by rw [map_mul]; exact mul_mem hx hy, fun y hyN => ?_⟩
        have hid : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [hid, hcen hy hyN hx]
        exact mul_mem (hy' y hyN) (hx' y hyN)
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        have hxi : θ x⁻¹ ∈ radN T r := by rw [map_inv]; exact inv_mem hx
        refine ⟨hxi, fun y hyN => ?_⟩
        have hid : ⁅x⁻¹, y⁆ = (x⁻¹ * ⁅x, y⁆ * x⁻¹⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [hid, hcen hx hyN hxi]
        exact inv_mem (hx' y hyN) }
  have hle : (radN T r).comap θ ≤ P := comap_le_of_le_closure hθ (radN_le_closure T hF)
    (fun c hc => ⟨by rw [hc]; exact one_mem _, fun y _ => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hC hc) y).symm]
      exact one_mem _⟩)
    (fun e ⟨i, z, he⟩ => ⟨by rw [← he]; exact xRt_mem_radN T i z,
      fun y hy => hsecond he.symm hy⟩)
  exact (hle hm).2 m' hm'

end Tilde

section Complement

variable {K F : Type} [Field K] [Field F] [Algebra K F] [CharP K 2] [Finite K]
  {T : NormTailData K F} {r : ℕ} {E : Type*} [Group E] {θ : E →* G0 T r}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

variable (θ) in
@[expose] def radComplement (t₀ : E) (W : Subgroup E)
    (hM : ∀ m, θ m ∈ radN T r → θ (t₀ * m * t₀⁻¹) ∈ radN T r)
    (hWc : ∀ v ∈ W, ∀ m, θ m ∈ radN T r → v * m = m * v)
    (hcomm : ∀ m m', θ m ∈ radN T r → θ m' ∈ radN T r → ⁅m, m'⁆ ∈ W) : Subgroup E where
  carrier := {x | ∃ m, θ m ∈ radN T r ∧ ∃ v ∈ W, x = t₀ * m * t₀⁻¹ * m⁻¹ * v}
  one_mem' := ⟨1, by rw [map_one]; exact one_mem _, 1, W.one_mem, by group⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm, v, hv, rfl⟩ ⟨m', hm', v', hv', rfl⟩
    have hδ : θ (t₀ * m' * t₀⁻¹ * m'⁻¹) ∈ radN T r := by
      rw [map_mul, map_inv]
      exact mul_mem (hM m' hm') (inv_mem hm')
    have hδi : θ (t₀ * m' * t₀⁻¹ * m'⁻¹)⁻¹ ∈ radN T r := by rw [map_inv]; exact inv_mem hδ
    refine ⟨m * m', by rw [map_mul]; exact mul_mem hm hm',
      ⁅m, (t₀ * m' * t₀⁻¹ * m'⁻¹)⁻¹⁆ * v * v',
      mul_mem (mul_mem (hcomm _ _ hm hδi) hv) hv', ?_⟩
    have hvc := hWc v hv _ hδ
    calc t₀ * m * t₀⁻¹ * m⁻¹ * v * (t₀ * m' * t₀⁻¹ * m'⁻¹ * v')
        = t₀ * m * t₀⁻¹ * m⁻¹ * (v * (t₀ * m' * t₀⁻¹ * m'⁻¹)) * v' := by group
      _ = t₀ * m * t₀⁻¹ * m⁻¹ * ((t₀ * m' * t₀⁻¹ * m'⁻¹) * v) * v' := by rw [hvc]
      _ = t₀ * (m * m') * t₀⁻¹ * (m * m')⁻¹ * (⁅m, (t₀ * m' * t₀⁻¹ * m'⁻¹)⁻¹⁆ * v * v') := by
          simp only [commutatorElement_def]
          group
  inv_mem' := by
    rintro _ ⟨m, hm, v, hv, rfl⟩
    have hmi : θ m⁻¹ ∈ radN T r := by rw [map_inv]; exact inv_mem hm
    have hδ : θ (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹) ∈ radN T r := by
      rw [map_mul, map_inv]
      exact mul_mem (hM _ hmi) (inv_mem hmi)
    have hδi : θ (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹)⁻¹ ∈ radN T r := by rw [map_inv]; exact inv_mem hδ
    refine ⟨m⁻¹, hmi, v⁻¹ * ⁅m, (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹)⁻¹⁆⁻¹,
      mul_mem (inv_mem hv) (inv_mem (hcomm _ _ hm hδi)), ?_⟩
    have hvc := hWc v⁻¹ (inv_mem hv) _ hδ
    calc (t₀ * m * t₀⁻¹ * m⁻¹ * v)⁻¹
        = v⁻¹ * (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹) * ⁅m, (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹)⁻¹⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹) * v⁻¹ * ⁅m, (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹)⁻¹⁆⁻¹ := by rw [hvc]
      _ = t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹ * (v⁻¹ * ⁅m, (t₀ * m⁻¹ * t₀⁻¹ * m⁻¹⁻¹)⁻¹⁆⁻¹) := by group

omit [CharP K 2] [Finite K] in
theorem map_mem_radN_of_mem_radComplement {t₀ : E} {W : Subgroup E}
    {hM : ∀ m, θ m ∈ radN T r → θ (t₀ * m * t₀⁻¹) ∈ radN T r}
    {hWc : ∀ v ∈ W, ∀ m, θ m ∈ radN T r → v * m = m * v}
    {hcomm : ∀ m m', θ m ∈ radN T r → θ m' ∈ radN T r → ⁅m, m'⁆ ∈ W}
    (hWN : ∀ v ∈ W, θ v ∈ radN T r) {x : E} (hx : x ∈ radComplement θ t₀ W hM hWc hcomm) :
    θ x ∈ radN T r := by
  obtain ⟨m, hm, v, hv, rfl⟩ := hx
  rw [map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (hM m hm) (inv_mem hm)) (hWN v hv)

include hθ in
theorem exists_mem_radComplement {s : Kˣ} (hs : (s : K) ≠ 1) {t₀ : E}
    (ht₀ : θ t₀ = torusE T r (fun _ => s)) {W : Subgroup E}
    {hM : ∀ m, θ m ∈ radN T r → θ (t₀ * m * t₀⁻¹) ∈ radN T r}
    {hWc : ∀ v ∈ W, ∀ m, θ m ∈ radN T r → v * m = m * v}
    {hcomm : ∀ m m', θ m ∈ radN T r → θ m' ∈ radN T r → ⁅m, m'⁆ ∈ W}
    (hWV : ∀ g ∈ (radTau T r).range, ∃ v ∈ W, θ v = g) {n : G0 T r} (hn : n ∈ radN T r) :
    ∃ x ∈ radComplement θ t₀ W hM hWc hcomm, θ x = n := by
  have hs1 : (s : K) - 1 ≠ 0 := sub_ne_zero.mpr hs
  obtain ⟨n₁, hn₁, hπ₁⟩ := exists_radCoord T (fun j => ((s : K) - 1)⁻¹ • radCoord T r n j)
  obtain ⟨m, rfl⟩ := hθ n₁
  set δ := t₀ * m * t₀⁻¹ * m⁻¹ with hδ
  have hconjN := torusE_conj_mem_radN T (fun _ => s) hn₁
  have hδN : θ δ ∈ radN T r := by
    rw [hδ, map_mul, map_mul, map_mul, map_inv, map_inv, ht₀]
    exact mul_mem hconjN.1 (inv_mem hn₁)
  have hπδ : radCoord T r (θ δ) = radCoord T r n := by
    rw [hδ, map_mul, map_mul, map_mul, map_inv, map_inv, ht₀,
      radCoord_mul T hconjN.1 (inv_mem hn₁), hconjN.2, radCoord_inv T hn₁, hπ₁]
    funext j
    simp only [Pi.add_apply, Pi.neg_apply, smul_smul]
    rw [← sub_eq_add_neg, ← sub_smul, ← sub_one_mul, mul_inv_cancel₀ hs1, one_smul]
  have hrest : (θ δ)⁻¹ * n ∈ (radTau T r).range := by
    have hN : (θ δ)⁻¹ * n ∈ radN T r := mul_mem (inv_mem hδN) hn
    refine (radCoord_eq_zero_iff T hN).1 ?_
    rw [radCoord_mul T (inv_mem hδN) hn, radCoord_inv T hδN, hπδ, neg_add_cancel]
  obtain ⟨v, hv, hθv⟩ := hWV _ hrest
  refine ⟨δ * v, ⟨m, hn₁, v, hv, rfl⟩, ?_⟩
  rw [map_mul, hθv, mul_inv_cancel_left]

include hC in
theorem eq_one_of_mem_radComplement (h2 : IsPGroup 2 θ.ker) {s : Kˣ} {t₀ : E}
    (ht₀ : θ t₀ = torusE T r (fun _ => s)) {W : Subgroup E}
    {hM : ∀ m, θ m ∈ radN T r → θ (t₀ * m * t₀⁻¹) ∈ radN T r}
    {hWc : ∀ v ∈ W, ∀ m, θ m ∈ radN T r → v * m = m * v}
    {hcomm : ∀ m m', θ m ∈ radN T r → θ m' ∈ radN T r → ⁅m, m'⁆ ∈ W}
    (hWt : ∀ v ∈ W, t₀ * v * t₀⁻¹ ∈ W) (hWC : ∀ v ∈ W, θ v = 1 → v = 1) {x : E}
    (hx : x ∈ radComplement θ t₀ W hM hWc hcomm) (hθx : θ x = 1) : x = 1 := by
  obtain ⟨m, -, v, hv, rfl⟩ := hx
  set c := t₀ * m * t₀⁻¹ * m⁻¹ * v with hc
  have hcc := hC hθx
  have hconj : t₀ * m * t₀⁻¹ = c * v⁻¹ * m := by rw [hc]; group
  obtain ⟨w, hw, hn⟩ := exists_pow_conj_eq hcc hWt (inv_mem hv) hconj (Nat.card Kˣ)
  have hgm : θ (t₀ ^ Nat.card Kˣ) = 1 := by
    rw [map_pow, ht₀, ← map_pow]
    have h1 : (fun _ : Fin r => s) ^ Nat.card Kˣ = 1 := by
      funext i
      exact pow_card_eq_one'
    rw [h1, map_one]
  rw [← Subgroup.mem_center_iff.mp (hC hgm) m, mul_inv_cancel_right] at hn
  have hcw : c ^ Nat.card Kˣ * w = 1 := mul_eq_right.mp hn.symm
  have hcn : c ^ Nat.card Kˣ = w⁻¹ := eq_inv_of_mul_eq_one_left hcw
  have hθcn : θ (c ^ Nat.card Kˣ) = 1 := by rw [map_pow, hθx, one_pow]
  have h1 : c ^ Nat.card Kˣ = 1 := by
    rw [hcn] at hθcn ⊢
    exact hWC _ (inv_mem hw) hθcn
  exact eq_one_of_pow_eq_one h2 hθx SymplecticSixCover.odd_card_units_of_charTwo h1

omit [CharP K 2] [Finite K] in
include hC in
theorem conj_mem_radComplement {t₀ u : E} {W : Subgroup E}
    {hM : ∀ m, θ m ∈ radN T r → θ (t₀ * m * t₀⁻¹) ∈ radN T r}
    {hWc : ∀ v ∈ W, ∀ m, θ m ∈ radN T r → v * m = m * v}
    {hcomm : ∀ m m', θ m ∈ radN T r → θ m' ∈ radN T r → ⁅m, m'⁆ ∈ W}
    (hut : θ u * θ t₀ = θ t₀ * θ u) (huN : ∀ m, θ m ∈ radN T r → θ (u * m * u⁻¹) ∈ radN T r)
    (huW : ∀ v ∈ W, u * v * u⁻¹ ∈ W) {x : E} (hx : x ∈ radComplement θ t₀ W hM hWc hcomm) :
    u * x * u⁻¹ ∈ radComplement θ t₀ W hM hWc hcomm := by
  obtain ⟨m, hm, v, hv, rfl⟩ := hx
  set k := t₀⁻¹ * u * t₀ * u⁻¹ with hk
  have hkc : k ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, hk, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (θ u),
      hut]
    group)
  have hu : u * t₀ = t₀ * k * u := by rw [hk]; group
  refine ⟨u * m * u⁻¹, huN m hm, u * v * u⁻¹, huW v hv, ?_⟩
  have hkz : k * (u * m * u⁻¹) * k⁻¹ = u * m * u⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hkc (u * m * u⁻¹), mul_inv_cancel_right]
  calc u * (t₀ * m * t₀⁻¹ * m⁻¹ * v) * u⁻¹
      = (u * t₀) * m * (u * t₀)⁻¹ * (u * m * u⁻¹)⁻¹ * (u * v * u⁻¹) := by group
    _ = (t₀ * k * u) * m * (t₀ * k * u)⁻¹ * (u * m * u⁻¹)⁻¹ * (u * v * u⁻¹) := by rw [hu]
    _ = t₀ * (k * (u * m * u⁻¹) * k⁻¹) * t₀⁻¹ * (u * m * u⁻¹)⁻¹ * (u * v * u⁻¹) := by group
    _ = t₀ * (u * m * u⁻¹) * t₀⁻¹ * (u * m * u⁻¹)⁻¹ * (u * v * u⁻¹) := by rw [hkz]

end Complement

section Levi

variable {K F : Type} [Field K] [Field F] [Algebra K F] [CharP K 2] [Finite K]
  {T : NormTailData K F} {r : ℕ} {E : Type*} [Group E] {θ : E →* G0 T r}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem liftConj_torusE_mem (t : Fin r → Kˣ) {x : E}
    (hx : x ∈ ⁅(psiG T (r := r)).range.comap θ, (psiG T (r := r)).range.comap θ⁆) :
    BinarySymplecticSix.liftConj hθ hC (torusE T r t) x ∈
      ⁅(psiG T (r := r)).range.comap θ, (psiG T (r := r)).range.comap θ⁆ := by
  set H := (psiG T (r := r)).range.comap θ
  set α := BinarySymplecticSix.liftConj hθ hC (torusE T r t)
  have hαH : H.map α.toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    change θ (α y) ∈ (psiG T).range
    rw [BinarySymplecticSix.map_liftConj_apply]
    obtain ⟨A, hA⟩ := hy
    rw [← hA, torusE_conj_psiG]
    exact ⟨_, rfl⟩
  have h1 : ⁅H, H⁆.map α.toMonoidHom ≤ ⁅H, H⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hαH hαH
  exact h1 ⟨x, hx, rfl⟩

end Levi

section LeviThree

variable {K F : Type} [Field K] [Field F] [Algebra K F] [CharP K 2] [Finite K]
  {T : NormTailData K F} {E : Type*} [Group E] {θ : E →* G0 T 3}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem levi_ker_eq_bot_three [Finite E] (hK : 4 ≤ Nat.card K)
    [Group.IsPerfect ↥⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆]
    (θF : ↥⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆ →*
      SpecialLinearGroup (Fin 3) K)
    (hθF : Function.Surjective θF) (hθFι : ∀ x, psiG T (θF x) = θ x)
    (hcen : θF.ker ≤ Subgroup.center _) (h2F : IsPGroup 2 θF.ker) : θF.ker = ⊥ := by
  have hker : ∀ x, θF x = 1 ↔ θ x = 1 := fun x => by
    rw [← hθFι, ← map_one (psiG T)]
    exact (psiG_injective T).eq_iff.symm
  set α : (Fin 3 → Kˣ) →* MulAut E := (BinarySymplecticSix.liftConj hθ hC).comp (torusE T 3)
  have hαY : ∀ t, ∀ x ∈ ⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆,
      α t x ∈ ⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆ :=
    fun t x hx => liftConj_torusE_mem hθ hC t hx
  let : MulDistribMulAction (Fin 3 → Kˣ)
      ↥⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆ :=
    MulDistribMulAction.compHom _ (BinarySymplecticSix.restrictAct α _ hαY)
  have hsmul : ∀ (t : Fin 3 → Kˣ)
      (x : ↥⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆),
      ((t • x : ↥⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆) : E) =
        α t x := fun _ _ => rfl
  have hfix : ∀ t : Fin 3 → Kˣ, ∀ z ∈ θF.ker, t • z = z := fun t z hz => Subtype.ext (by
    rw [hsmul]
    exact BinarySymplecticSix.liftConj_apply_of_mem_ker hθ hC _ ((hker z).mp hz))
  have hd : ∀ (t : Fin 3 → Kˣ)
      (x : ↥⁅(psiG T (r := 3)).range.comap θ, (psiG T (r := 3)).range.comap θ⁆),
      ((θF (t • x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun i => (t i : K)) * (θF x : Matrix (Fin 3) (Fin 3) K) *
          (diagonal (fun i => (t i : K)))⁻¹ := by
    intro t x
    have h1 : psiG T (θF (t • x)) = psiG T (diagConj t (θF x)) := by
      rw [hθFι, hsmul, MonoidHom.comp_apply, BinarySymplecticSix.map_liftConj_apply, ← hθFι,
        torusE_conj_psiG]
    rw [psiG_injective T h1, coe_diagConj, Matrix.coe_units_inv]
    rfl
  exact (LinearCover.even_linear_three_diagonal_action_central_two_cover_trivial hK θF hθF hcen
    h2F hfix hd).1

end LeviThree

section Core

variable {K F : Type} [Field K] [Field F] [Algebra K F] [CharP K 2] [Finite K]
  {T : NormTailData K F} {r : ℕ} {E : Type*} [Group E] {θ : E →* G0 T r}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem levi_inj [Finite E] (hK : 4 ≤ Nat.card K) (hr : 3 ≤ r) (h2 : IsPGroup 2 θ.ker) {y : E}
    (hy : y ∈ ⁅(psiG T (r := r)).range.comap θ, (psiG T (r := r)).range.comap θ⁆)
    (hθy : θ y = 1) : y = 1 := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hr
  have : Group.IsPerfect (psiG T (r := r)).range := Group.IsPerfect.range _
  obtain ⟨θF, hθF, hθFι⟩ :=
    SymplecticSixCover.exists_derivedComap_cover hθ (psiG T) (psiG_injective T)
  have hker : ∀ x, θF x = 1 ↔ θ x = 1 := fun x => by
    rw [← hθFι, ← map_one (psiG T)]
    exact (psiG_injective T).eq_iff.symm
  have : Group.IsPerfect
      ↥⁅(psiG T (r := r)).range.comap θ, (psiG T (r := r)).range.comap θ⁆ :=
    SymplecticSixCover.isPerfect_derivedComap hθ hC _
  have hcen : θF.ker ≤ Subgroup.center _ := fun x hx => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hker x).mp hx)) g)
  have h2F : IsPGroup 2 θF.ker := fun x => by
    obtain ⟨n, hn⟩ := h2 ⟨(x : E), (hker x).mp x.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  have hbot : θF.ker = ⊥ := by
    rcases Nat.lt_or_ge r 4 with hr4 | hr4
    · obtain rfl : r = 3 := by omega
      exact levi_ker_eq_bot_three hθ hC hK θF hθF hθFι hcen h2F
    · obtain ⟨P₁, hP₁⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := r) (by omega)
      exact LinearCover.ker_eq_bot_of_rootHom (by omega) hr4 (MonoidHom.id _)
        (fun u _ hu => hu) P₁ (by rw [hP₁, Subgroup.map_id]) θF hθF hcen h2F
  have hk : (⟨y, hy⟩ : ↥⁅(psiG T (r := r)).range.comap θ, (psiG T (r := r)).range.comap θ⁆) ∈
      θF.ker := (hker _).mpr hθy
  rw [hbot, Subgroup.mem_bot] at hk
  exact congrArg Subtype.val hk

include hθ hC in
theorem ker_eq_bot_of_normTail [Finite E] [Group.IsPerfect E] (hF : Module.finrank K F = 2)
    {f : ℕ} (hcard : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr : 3 ≤ r) (h2 : IsPGroup 2 θ.ker) :
    θ.ker = ⊥ := by
  have hK : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc0, hc1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le (K := K) (by omega)
  set s : Kˣ := Units.mk0 c hc0 with hsdef
  have hs : (s : K) ≠ 1 := hc1
  obtain ⟨t₀, ht₀⟩ := hθ (torusE T r (fun _ => s))
  have hg₀ : ∀ y, θ y ∈ (radTau T r).range → θ (t₀ * y * t₀⁻¹) ∈ (radTau T r).range :=
    fun y hy => by
      rw [map_mul, map_mul, map_inv, ht₀]
      exact torusE_conj_mem_range_radTau _ hy
  have hV : ∀ x y, θ x ∈ (radTau T r).range → θ y ∈ (radTau T r).range → x * y = y * x :=
    fun x y hx hy => commute_of_mem_preV hθ hC hs hF hx (range_radTau_le T hy)
  set W := conjComm θ (radTau T r).range t₀ hg₀ hV with hW
  have hWT : ∀ v ∈ W, θ v ∈ (radTau T r).range := by
    rintro _ ⟨y, hy, rfl⟩
    rw [map_mul θ (t₀ * y * t₀⁻¹) y⁻¹, map_inv]
    exact mul_mem (hg₀ y hy) (inv_mem hy)
  have hWN : ∀ v ∈ W, θ v ∈ radN T r := fun v hv => range_radTau_le T (hWT v hv)
  have hWV : ∀ g ∈ (radTau T r).range, ∃ v ∈ W, θ v = g := by
    rintro _ ⟨B, rfl⟩
    obtain ⟨x, hx, hxB⟩ := exists_mem_conjComm hθ hs ht₀ (hg₀ := hg₀) (hV := hV) B.toAdd
    exact ⟨x, hx, by rw [hxB, ofAdd_toAdd]⟩
  have hWt : ∀ v ∈ W, t₀ * v * t₀⁻¹ ∈ W := fun v hv => conj_mem_conjComm hC rfl hg₀ hv
  have hWC : ∀ v ∈ W, θ v = 1 → v = 1 := fun v hv hθv =>
    eq_one_of_mem_conjComm hC h2 ht₀ hv hθv
  have hM : ∀ m, θ m ∈ radN T r → θ (t₀ * m * t₀⁻¹) ∈ radN T r := fun m hm => by
    rw [map_mul, map_mul, map_inv, ht₀]
    exact (torusE_conj_mem_radN T _ hm).1
  have hWc : ∀ v ∈ W, ∀ m, θ m ∈ radN T r → v * m = m * v := fun v hv m hm =>
    commute_of_mem_preV hθ hC hs hF (hWT v hv) hm
  have hcomm : ∀ m m', θ m ∈ radN T r → θ m' ∈ radN T r → ⁅m, m'⁆ ∈ W := fun m m' hm hm' =>
    commutatorElement_mem_conjComm hθ hC hF hcard hf h2 hs ht₀ hm hm'
  set M₀ := radComplement θ t₀ W hM hWc hcomm with hM₀
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hr
  have : Group.IsPerfect (psiG T (r := r)).range := Group.IsPerfect.range _
  set Y := ⁅(psiG T (r := r)).range.comap θ, (psiG T (r := r)).range.comap θ⁆ with hY
  have hYinj : ∀ y ∈ Y, θ y = 1 → y = 1 := fun y hy hθy => levi_inj hθ hC hK hr h2 hy hθy
  have hYR : ∀ u ∈ Y, θ u ∈ (psiG T (r := r)).range := fun u hu =>
    Subgroup.mem_comap.1 (Subgroup.commutator_le_self _ hu)
  have hgood : ∀ g : E, θ g ∈ (psiG T (r := r)).range → ∀ x ∈ M₀, g * x * g⁻¹ ∈ M₀ := by
    rintro g ⟨A, hA⟩ x hx
    have hgt : θ g * θ t₀ = θ t₀ * θ g := by
      rw [← hA, ht₀]
      exact (torusE_const_commute_psiG T s A).symm
    have hgN : ∀ m, θ m ∈ radN T r → θ (g * m * g⁻¹) ∈ radN T r := fun m hm => by
      rw [map_mul, map_mul, map_inv, ← hA]
      exact psiG_conj_mem_radN T A hm
    have hgV : ∀ y, θ y ∈ (radTau T r).range → θ (g * y * g⁻¹) ∈ (radTau T r).range :=
      fun y hy => by
        rw [map_mul, map_mul, map_inv, ← hA]
        exact psiG_conj_mem_range_radTau T A hy
    exact conj_mem_radComplement hC hgt hgN (fun v hv => conj_mem_conjComm hC hgt hgV hv) hx
  set UR := (LinearFlag.unitriangular r K).map (psiG T) with hUR
  set Ũ := Y ⊓ UR.comap θ with hŨ
  have hŨN : Ũ ≤ Subgroup.normalizer (M₀ : Set E) := by
    intro u hu
    have hu' : θ u⁻¹ ∈ (psiG T (r := r)).range := by
      rw [map_inv]
      exact inv_mem (hYR u hu.1)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hgood u (hYR u hu.1) x hx, fun hx => ?_⟩
    have h := hgood u⁻¹ hu' _ hx
    rwa [show u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x by group] at h
  set P₀ := Ũ ⊔ M₀ with hP₀def
  have hP₀ : (P₀ : Set E) = (Ũ : Set E) * (M₀ : Set E) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Ũ M₀ hŨN
  have hinj : ∀ z ∈ P₀, θ z = 1 → z = 1 := by
    intro z hz hθz
    rw [← SetLike.mem_coe, hP₀, Set.mem_mul] at hz
    obtain ⟨u, hu, x, hx, rfl⟩ := hz
    have hθx : θ x ∈ radN T r := map_mem_radN_of_mem_radComplement hWN hx
    have h1 : θ u = (θ x)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul]; exact hθz)
    have hbot : θ u ∈ UR ⊓ radN T r :=
      Subgroup.mem_inf.2 ⟨hu.2, by rw [h1]; exact inv_mem hθx⟩
    rw [inf_radN_eq_bot T, Subgroup.mem_bot] at hbot
    have hθx1 : θ x = 1 := by
      rw [hbot, eq_comm, inv_eq_one] at h1
      exact h1
    rw [hYinj u hu.1 hbot, eq_one_of_mem_radComplement hC h2 ht₀ hWt hWC hx hθx1, one_mul]
  obtain ⟨S, hS⟩ := exists_sylow T hF hr
  have hSle : (S : Subgroup (G0 T r)) ≤ P₀.map θ := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hS g hg
    obtain ⟨x, hx, hxb⟩ := exists_mem_radComplement hθ hs ht₀ hWV hb
    have haR : a ∈ Y.map θ := by
      rw [hY, SymplecticSixCover.map_derivedComap hθ (psiG T (r := r)).range]
      exact Subgroup.map_le_range _ _ ha
    obtain ⟨u, huY, hua⟩ := haR
    have huŨ : u ∈ Ũ := ⟨huY, Subgroup.mem_comap.2 (by rw [hua]; exact ha)⟩
    exact ⟨u * x, mul_mem (Subgroup.mem_sup_left huŨ) (Subgroup.mem_sup_right hx), by
      rw [map_mul, hua, hxb]⟩
  exact LinearCover.ker_eq_bot_of_sylow_le_map θ hθ hC h2 S P₀ hSle hinj

end Core

end CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalog

namespace CFSG.LocalAnalysis.ComponentInitial

open NonsplitCatalog NormTail

theorem even_nonsplit_orthogonal_catalog_perfect_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f) (hJ : CFSG.Blueprint.LieModel J .POmegaMinus n 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, _, hcard, -, F, _, _, T, hF, ⟨e⟩⟩ := exists_normTail_of_lieModel hJ
  set η' : E →* G0 T (n - 1) := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_normTail (θ := η') (e.surjective.comp hη) (hker' ▸ hC) hF hcard hf
    (by omega) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial
