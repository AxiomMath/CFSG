module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl
open scoped commutatorElement Pointwise

variable {K : Type} [Field K] {E : Type*} [Group E] {θ : E →* StatedSp 3 K}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem liftConj_torusHom_mem (t : Fin 3 → Kˣ) {x : E}
    (hx : x ∈ ⁅(leviSL (K := K)).range.comap θ, (leviSL (K := K)).range.comap θ⁆) :
    BinarySymplecticSix.liftConj hθ hC (torusHom t) x ∈
      ⁅(leviSL (K := K)).range.comap θ, (leviSL (K := K)).range.comap θ⁆ := by
  set H := (leviSL (K := K)).range.comap θ
  set α := BinarySymplecticSix.liftConj hθ hC (torusHom t)
  have hαH : H.map α.toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    change θ (α y) ∈ (leviSL (K := K)).range
    rw [BinarySymplecticSix.map_liftConj_apply]
    obtain ⟨A, hA⟩ := hy
    rw [← hA, torusHom_mul_leviSL_mul_inv]
    exact ⟨_, rfl⟩
  have h1 : ⁅H, H⁆.map α.toMonoidHom ≤ ⁅H, H⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hαH hαH
  exact h1 ⟨x, hx, rfl⟩

variable [Finite K] [CharP K 2] [Finite E]

include hθ hC in
theorem levi_inj (hK : 4 ≤ Nat.card K) (h2 : IsPGroup 2 θ.ker) {f : E}
    (hf : f ∈ ⁅(leviSL (K := K)).range.comap θ, (leviSL (K := K)).range.comap θ⁆)
    (hθf : θ f = 1) : f = 1 := by
  set F := ⁅(leviSL (K := K)).range.comap θ, (leviSL (K := K)).range.comap θ⁆
  obtain ⟨θF, hθF, hθFι⟩ := exists_derivedComap_cover hθ leviSL leviSL_injective
  have hθFker : ∀ z : F, θF z = 1 ↔ θ z = 1 := fun z => by
    rw [← hθFι, ← map_one leviSL]
    exact leviSL_injective.eq_iff.symm
  have : Group.IsPerfect F := isPerfect_derivedComap hθ hC _
  have hcenF : θF.ker ≤ Subgroup.center F := fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker z).mp hz)) g)
  have h2F : IsPGroup 2 θF.ker := fun z => by
    obtain ⟨n, hn⟩ := h2 ⟨(z : F), (hθFker z).mp z.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  set α : (Fin 3 → Kˣ) →* MulAut E := (BinarySymplecticSix.liftConj hθ hC).comp torusHom
  have hαF : ∀ t, ∀ x ∈ F, α t x ∈ F := fun t x hx => liftConj_torusHom_mem hθ hC t hx
  let : MulDistribMulAction (Fin 3 → Kˣ) F :=
    MulDistribMulAction.compHom F (BinarySymplecticSix.restrictAct α F hαF)
  have hsmul : ∀ (t : Fin 3 → Kˣ) (x : F), ((t • x : F) : E) = α t x := fun _ _ => rfl
  have hfix : ∀ t : Fin 3 → Kˣ, ∀ z ∈ θF.ker, t • z = z := fun t z hz => Subtype.ext (by
    rw [hsmul]
    exact BinarySymplecticSix.liftConj_apply_of_mem_ker hθ hC _ ((hθFker z).mp hz))
  have hd : ∀ (t : Fin 3 → Kˣ) (x : F),
      ((θF (t • x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun i => (t i : K)) * (θF x : Matrix (Fin 3) (Fin 3) K) *
          (diagonal (fun i => (t i : K)))⁻¹ := by
    intro t x
    have h1 : leviSL (θF (t • x)) = leviSL (diagConj t (θF x)) := by
      rw [hθFι, hsmul, MonoidHom.comp_apply, BinarySymplecticSix.map_liftConj_apply, ← hθFι,
        torusHom_mul_leviSL_mul_inv]
    rw [leviSL_injective h1]
    change (TauCeti.diagGL t : Matrix (Fin 3) (Fin 3) K) * _ *
      (((TauCeti.diagGL t)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [coe_units_inv, TauCeti.diagGL_coe]
  have hbot := (LinearCover.even_linear_three_diagonal_action_central_two_cover_trivial hK θF
    hθF hcenF h2F hfix hd).1
  have hk : (⟨f, hf⟩ : F) ∈ θF.ker := (hθFker _).mpr hθf
  rw [hbot, Subgroup.mem_bot] at hk
  exact congrArg Subtype.val hk

theorem odd_card_units_of_charTwo : Odd (Nat.card Kˣ) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
  have h1 : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
  have h2 : 2 ≤ 2 ^ (n : ℕ) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) n.pos
  refine ⟨2 ^ ((n : ℕ) - 1) - 1, ?_⟩
  have h3 : 2 ^ (n : ℕ) = 2 * 2 ^ ((n : ℕ) - 1) := by
    rw [← pow_succ']
    congr 1
    have := n.pos
    omega
  omega

omit [Finite E] in
include hC in
theorem eq_one_of_conj_mul_inv (h2 : IsPGroup 2 θ.ker) {s : Kˣ} {g₀ : E}
    (hg₀ : θ g₀ = torusHom (fun _ => s)) {y : E} (hy : θ (g₀ * y * g₀⁻¹ * y⁻¹) = 1) :
    g₀ * y * g₀⁻¹ * y⁻¹ = 1 := by
  have hconj : g₀ * y * g₀⁻¹ = (g₀ * y * g₀⁻¹ * y⁻¹) * y := by group
  generalize hxdef : g₀ * y * g₀⁻¹ * y⁻¹ = x at hy hconj ⊢
  have hxc : x ∈ Subgroup.center E := hC hy
  have hcx : ∀ g : E, g * x = x * g := fun g => Subgroup.mem_center_iff.mp hxc g
  have hk : ∀ k : ℕ, g₀ ^ k * y * (g₀ ^ k)⁻¹ = x ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc g₀ ^ (k + 1) * y * (g₀ ^ (k + 1))⁻¹ = g₀ * (g₀ ^ k * y * (g₀ ^ k)⁻¹) * g₀⁻¹ := by
            group
        _ = g₀ * (x ^ k * y) * g₀⁻¹ := by rw [ih]
        _ = x ^ k * (g₀ * y * g₀⁻¹) := by
            rw [show g₀ * (x ^ k * y) * g₀⁻¹ = (g₀ * x ^ k) * y * g₀⁻¹ by group,
              (Commute.pow_right (hcx g₀) k).eq]
            group
        _ = x ^ (k + 1) * y := by rw [hconj, pow_succ, mul_assoc]
  set m := Nat.card Kˣ
  have hgm : θ (g₀ ^ m) = 1 := by
    rw [map_pow, hg₀, ← map_pow]
    have : (fun _ : Fin 3 => s) ^ m = 1 := by
      funext i
      exact pow_card_eq_one'
    rw [this, map_one]
  have hgmc : ∀ g : E, g * g₀ ^ m = g₀ ^ m * g := fun g =>
    (Subgroup.mem_center_iff.mp (hC hgm) g)
  have hxm : x ^ m = 1 := by
    have h := hk m
    rw [← hgmc y, mul_inv_cancel_right] at h
    exact (mul_eq_right.mp h.symm)
  obtain ⟨n, hn⟩ := h2 ⟨x, hy⟩
  have hn' : x ^ 2 ^ n = 1 := by
    simpa using congrArg (fun w : θ.ker => (w : E)) hn
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n
    (Nat.coprime_two_left.mpr odd_card_units_of_charTwo)
  have hord : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hn') (orderOf_dvd_of_pow_eq_one hxm)
  exact orderOf_eq_one_iff.mp hord

omit [Finite K] [CharP K 2] [Finite E] in
@[expose] def radComplement (g₀ : E)
    (hg₀M : ∀ y, θ y ∈ symGroup → θ (g₀ * y * g₀⁻¹) ∈ symGroup)
    (hM : ∀ x y, θ x ∈ symGroup → θ y ∈ symGroup → x * y = y * x) : Subgroup E where
  carrier := {x | ∃ y, θ y ∈ symGroup ∧ x = g₀ * y * g₀⁻¹ * y⁻¹}
  one_mem' := ⟨1, by rw [map_one]; exact one_mem _, by group⟩
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨y * y', by rw [map_mul]; exact mul_mem hy hy', ?_⟩
    have h1 := hM (g₀ * y' * g₀⁻¹) y⁻¹ (hg₀M y' hy') (by rw [map_inv]; exact inv_mem hy)
    have h2 := hM y y' hy hy'
    calc g₀ * y * g₀⁻¹ * y⁻¹ * (g₀ * y' * g₀⁻¹ * y'⁻¹)
        = g₀ * y * g₀⁻¹ * (y⁻¹ * (g₀ * y' * g₀⁻¹)) * y'⁻¹ := by group
      _ = g₀ * y * g₀⁻¹ * ((g₀ * y' * g₀⁻¹) * y⁻¹) * y'⁻¹ := by rw [h1]
      _ = g₀ * (y * y') * g₀⁻¹ * (y' * y)⁻¹ := by group
      _ = g₀ * (y * y') * g₀⁻¹ * (y * y')⁻¹ := by rw [h2]
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y⁻¹, by rw [map_inv]; exact inv_mem hy, ?_⟩
    have h1 := hM y (g₀ * y⁻¹ * g₀⁻¹) hy (hg₀M y⁻¹ (by rw [map_inv]; exact inv_mem hy))
    calc (g₀ * y * g₀⁻¹ * y⁻¹)⁻¹ = y * (g₀ * y⁻¹ * g₀⁻¹) := by group
      _ = g₀ * y⁻¹ * g₀⁻¹ * y := h1
      _ = g₀ * y⁻¹ * g₀⁻¹ * y⁻¹⁻¹ := by rw [inv_inv]

omit [Finite K] [CharP K 2] [Finite E] in
theorem mem_radComplement {g₀ : E}
    {hg₀M : ∀ y, θ y ∈ symGroup → θ (g₀ * y * g₀⁻¹) ∈ symGroup}
    {hM : ∀ x y, θ x ∈ symGroup → θ y ∈ symGroup → x * y = y * x} {x : E} :
    x ∈ radComplement g₀ hg₀M hM ↔ ∃ y, θ y ∈ symGroup ∧ x = g₀ * y * g₀⁻¹ * y⁻¹ :=
  Iff.rfl

omit [Finite K] [CharP K 2] [Finite E] in
theorem torusHom_const_mul_upperUnipotentSp_mul_inv (s : Kˣ) {B : Matrix (Fin 3) (Fin 3) K}
    (hB : Bᵀ = B) :
    torusHom (fun _ => s) * upperUnipotentSp 3 K hB * (torusHom (fun _ => s))⁻¹ =
      upperUnipotentSp 3 K (show (((s : K) ^ 2) • B)ᵀ = ((s : K) ^ 2) • B by
        rw [transpose_smul, hB]) := by
  change leviSp (TauCeti.diagGL fun _ => s) * upperUnipotentSp 3 K hB *
    (leviSp (TauCeti.diagGL fun _ => s))⁻¹ = _
  rw [leviSp_mul_upperUnipotentSp_mul_inv]
  refine upperUnipotentSp_congr 3 _ _ ?_
  rw [TauCeti.diagGL_coe, diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  ring

include hθ hC in
theorem ker_eq_bot_of_statedSp_three [Group.IsPerfect E] (hK : 4 ≤ Nat.card K)
    (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ := by
  set R := (leviSL (K := K)).range
  set F := ⁅R.comap θ, R.comap θ⁆
  have hFR : F.map θ = R := map_derivedComap hθ R
  have hFinj : ∀ f ∈ F, θ f = 1 → f = 1 := fun f hf hθf => levi_inj hθ hC hK h2 hf hθf
  have hM : ∀ x y, θ x ∈ symGroup → θ y ∈ symGroup → x * y = y * x := fun x y hx hy =>
    mul_comm_of_mem_symGroup hθ hC hK h2 hx hy
  obtain ⟨r, hr0, hr1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le (K := K) (by omega)
  set s : Kˣ := Units.mk0 r hr0
  have hs : (s : K) = r := rfl
  obtain ⟨g₀, hg₀⟩ := hθ (torusHom (fun _ => s))
  have hg₀M : ∀ y, θ y ∈ symGroup → θ (g₀ * y * g₀⁻¹) ∈ symGroup := by
    rintro y ⟨B, hB, hyB⟩
    rw [map_mul, map_mul, map_inv, hg₀, hyB, torusHom_const_mul_upperUnipotentSp_mul_inv]
    exact ⟨_, _, rfl⟩
  set Vt := radComplement g₀ hg₀M hM
  have hVtV : ∀ x ∈ Vt, θ x ∈ symGroup := by
    rintro _ ⟨y, hy, rfl⟩
    rw [map_mul, map_inv]
    exact mul_mem (hg₀M y hy) (inv_mem hy)
  have hVtsurj : ∀ (B : Matrix (Fin 3) (Fin 3) K) (hB : Bᵀ = B),
      ∃ x ∈ Vt, θ x = upperUnipotentSp 3 K hB := by
    intro B hB
    have hc : r ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (sq_ne_one_of_ne_one hr1)
    set B' := (r ^ 2 - 1)⁻¹ • B
    have hB' : B'ᵀ = B' := by rw [transpose_smul, hB]
    obtain ⟨y, hy⟩ := hθ (upperUnipotentSp 3 K hB')
    refine ⟨g₀ * y * g₀⁻¹ * y⁻¹, ⟨y, ⟨B', hB', hy⟩, rfl⟩, ?_⟩
    have hinv : (upperUnipotentSp 3 K hB')⁻¹ =
        upperUnipotentSp 3 K (show (-B')ᵀ = -B' by rw [transpose_neg, hB']) := by
      rw [inv_eq_iff_mul_eq_one, upperUnipotentSp_mul, ← upperUnipotentSp_zero]
      exact upperUnipotentSp_congr 3 _ _ (add_neg_cancel B')
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg₀, hy,
      torusHom_const_mul_upperUnipotentSp_mul_inv, hinv, upperUnipotentSp_mul]
    refine upperUnipotentSp_congr 3 _ _ ?_
    rw [hs, ← sub_eq_add_neg, show r ^ 2 • B' - B' = (r ^ 2 - 1) • B' by rw [sub_smul, one_smul],
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hVtinj : ∀ x ∈ Vt, θ x = 1 → x = 1 := by
    rintro _ ⟨y, -, rfl⟩ hx
    exact eq_one_of_conj_mul_inv hC h2 hg₀ hx
  have hg₀F : ∀ u ∈ F, g₀ * u * g₀⁻¹ = u := by
    intro u hu
    have hconj : g₀ * u * g₀⁻¹ ∈ F := by
      have h := liftConj_torusHom_mem hθ hC (fun _ => s) hu
      rwa [← hg₀, BinarySymplecticSix.liftConj_apply, MulAut.conj_apply] at h
    have hmem : g₀ * u * g₀⁻¹ * u⁻¹ ∈ F := mul_mem hconj (inv_mem hu)
    have hθu : θ u ∈ R := Subgroup.mem_comap.1 (Subgroup.commutator_le_self (R.comap θ) hu)
    obtain ⟨A, hA⟩ := hθu
    have h1 : θ (g₀ * u * g₀⁻¹ * u⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg₀, ← hA,
        torusHom_const_commute_leviSL, mul_inv_cancel_right, mul_inv_cancel]
    have h := hFinj _ hmem h1
    rwa [mul_inv_eq_one] at h
  have hFVt : ∀ u ∈ F, ∀ x ∈ Vt, u * x * u⁻¹ ∈ Vt := by
    rintro u hu _ ⟨y, hy, rfl⟩
    have hu' := hg₀F u hu
    have hcomm : g₀ * u = u * g₀ := by rwa [mul_inv_eq_iff_eq_mul] at hu'
    have hcomm' : u⁻¹ * g₀⁻¹ = g₀⁻¹ * u⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hcomm]
    have hθu : θ u ∈ R := Subgroup.mem_comap.1 (Subgroup.commutator_le_self (R.comap θ) hu)
    obtain ⟨A, hA⟩ := hθu
    obtain ⟨B, hB, hyB⟩ := hy
    refine ⟨u * y * u⁻¹, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, ← hA, hyB]
      change leviSp (SpecialLinearGroup.toGL A) * upperUnipotentSp 3 K hB *
        (leviSp (SpecialLinearGroup.toGL A))⁻¹ ∈ symGroup
      rw [leviSp_mul_upperUnipotentSp_mul_inv]
      exact ⟨_, _, rfl⟩
    · calc u * (g₀ * y * g₀⁻¹ * y⁻¹) * u⁻¹ = (u * g₀) * y * g₀⁻¹ * y⁻¹ * u⁻¹ := by group
        _ = (g₀ * u) * y * g₀⁻¹ * y⁻¹ * u⁻¹ := by rw [hcomm]
        _ = g₀ * u * y * (u⁻¹ * g₀⁻¹) * u * y⁻¹ * u⁻¹ := by
            rw [hcomm']
            group
        _ = g₀ * (u * y * u⁻¹) * g₀⁻¹ * (u * y * u⁻¹)⁻¹ := by group
  set UR := (BinarySymplecticSix.unitriangularGL 3 K).map leviSp
  set Ut := F ⊓ UR.comap θ
  have hUtN : Ut ≤ Subgroup.normalizer (Vt : Set E) := by
    intro u hu
    have huF : u ∈ F := hu.1
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hFVt u huF n hn, fun hn => ?_⟩
    have h := hFVt u⁻¹ (inv_mem huF) _ hn
    have e : u⁻¹ * (u * n * u⁻¹) * u⁻¹⁻¹ = n := by group
    rwa [e] at h
  set P₀ := Vt ⊔ Ut
  have hP₀ : (P₀ : Set E) = (Vt : Set E) * (Ut : Set E) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Vt Ut hUtN
  have hinj : ∀ z ∈ P₀, θ z = 1 → z = 1 := by
    intro z hz hθz
    rw [← SetLike.mem_coe, hP₀, Set.mem_mul] at hz
    obtain ⟨v, hv, u, hu, rfl⟩ := hz
    obtain ⟨B, hB, hvB⟩ := hVtV v hv
    obtain ⟨A, -, hAu⟩ := (Subgroup.mem_inf.1 hu).2
    rw [map_mul, mul_eq_one_iff_eq_inv, hvB, ← hAu, ← map_inv] at hθz
    obtain ⟨hB0, hA1⟩ := upperUnipotentSp_eq_leviSp hB hθz
    have hθv : θ v = 1 := by
      rw [hvB, ← upperUnipotentSp_zero]
      exact upperUnipotentSp_congr 3 _ _ hB0
    have hθu : θ u = 1 := by
      rw [← hAu, inv_eq_one.mp hA1, map_one]
    rw [hVtinj v hv hθv, hFinj u (Subgroup.mem_inf.1 hu).1 hθu, one_mul]
  obtain ⟨S, hS⟩ := exists_sylow_unipotent (K := K) 2 3
  have hSle : (S : Subgroup (StatedSp 3 K)) ≤ P₀.map θ := by
    intro g hg
    rw [hS] at hg
    obtain ⟨A, C', hA, hC', hgA⟩ := hg
    set Au := nonsingInvUnit A hA.isUnit_det
    have hg' : g = leviSp Au * upperUnipotentSp 3 K hC' :=
      statedSp_ext (hgA.trans (coe_blockElt hA.isUnit_det hC').symm)
    have hAR : leviSp Au ∈ R := ⟨⟨A, hA.det_eq_one⟩, congrArg leviSp (Units.ext rfl)⟩
    rw [← hFR] at hAR
    obtain ⟨u, hu, hθu⟩ := hAR
    obtain ⟨v, hv, hθv⟩ := hVtsurj C' hC'
    refine ⟨u * v, mul_mem (Subgroup.mem_sup_right ⟨hu, Au, hA, hθu.symm⟩)
      (Subgroup.mem_sup_left hv), ?_⟩
    rw [map_mul, hθu, hθv, hg']
  exact LinearCover.ker_eq_bot_of_sylow_le_map θ hθ hC h2 S P₀ hSle hinj

end CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover
