module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherField
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeFixedCommutator

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {r : ℕ} {K : Type*} [Field K] [CharP K 2] [Finite K]

section Roots

variable {E : Type*} [Group E] {θ : E →* orthElementaryGroup (quadPlus r K)}
  (hθ : Function.Surjective θ) (hker : ∀ z, θ z = 1 → z ∈ Subgroup.center E)
include hθ hker

theorem lift_radRoot_mul_comm_of_ne (hr : 3 ≤ r) {c : Kˣ} (hc : (c : K) ≠ 1)
    {i j k l m : Fin r} (hij : i ≠ j) (hm : m = i ∨ m = j) (hmk : m ≠ k) (hml : m ≠ l)
    {x y : E} {a b : K} (hx : θ x = radRoot r K i j a) (hy : θ y = radRoot r K k l b) :
    x * y = y * x := by
  refine LinearCover.lift_mul_comm_of_torus θ hker hθ (x := radRoot r K i j)
    (y := radRoot r K k l) (radRoot_add i j) (fun a b => radRoot_mul_comm i j k l a b)
    (t := torusE r K hr (Pi.mulSingle m c)) (r := (c : K)) hc (fun a => ?_) (fun b => ?_) hx hy
  · rw [torusE_mul_radRoot_mul_inv]
    congr 1
    rcases hm with h | h <;> subst h <;> simp [hij, Ne.symm hij]
  · rw [torusE_mul_radRoot_mul_inv]
    congr 1
    simp [Ne.symm hmk, Ne.symm hml]

theorem lift_radRoot_mul_comm_self (hr : 3 ≤ r) {c : Kˣ} (hc : (c : K) ≠ 1) {i j : Fin r}
    (hij : i ≠ j) {x y : E} {a b : K} (hx : θ x = radRoot r K i j a)
    (hy : θ y = radRoot r K i j b) : x * y = y * x := by
  obtain ⟨m, hmi, hmj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  obtain ⟨p, hp⟩ := hθ (leviRoot r K hr i m a)
  obtain ⟨q, hq⟩ := hθ (radRoot r K m j 1)
  have h1 : Commute y p := by
    refine LinearCover.lift_mul_comm_of_torus θ hker hθ (x := radRoot r K i j)
      (y := leviRoot r K hr i m) (radRoot_add i j)
      (fun a b => (leviRoot_mul_radRoot_comm hr hmi hmj b a).symm)
      (t := torusE r K hr (Pi.mulSingle j c)) (r := (c : K)) hc (fun a => ?_) (fun b => ?_) hy hp
    · rw [torusE_mul_radRoot_mul_inv]
      congr 1
      simp [hij]
    · rw [torusE_mul_leviRoot_mul_inv]
      congr 1
      simp [hij, hmj]
  have h2 : Commute y q := by
    refine LinearCover.lift_mul_comm_of_torus θ hker hθ (x := radRoot r K i j)
      (y := radRoot r K m j) (radRoot_add i j) (fun a b => radRoot_mul_comm i j m j a b)
      (t := torusE r K hr (Pi.mulSingle i c)) (r := (c : K)) hc (fun a => ?_) (fun b => ?_) hy hq
    · rw [torusE_mul_radRoot_mul_inv]
      congr 1
      simp [Ne.symm hij]
    · rw [torusE_mul_radRoot_mul_inv]
      congr 1
      simp [hmi, Ne.symm hij]
  have hz : ⁅p, q⁆⁻¹ * x ∈ Subgroup.center E := hker _ (by
    rw [map_mul, map_inv, map_commutatorElement, hp, hq,
      commutatorElement_leviRoot_radRoot hr hmi hmj, mul_one, hx, inv_mul_cancel])
  have hw : Commute y ⁅p, q⁆ := by
    rw [commutatorElement_def]
    exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
  calc x * y = ⁅p, q⁆ * (⁅p, q⁆⁻¹ * x) * y := by group
    _ = ⁅p, q⁆ * y * (⁅p, q⁆⁻¹ * x) := by
        rw [mul_assoc, ← Subgroup.mem_center_iff.mp hz y, ← mul_assoc]
    _ = y * ⁅p, q⁆ * (⁅p, q⁆⁻¹ * x) := by rw [hw.eq]
    _ = y * x := by group

theorem lift_radRoot_mul_comm (hr : 3 ≤ r) {c : Kˣ} (hc : (c : K) ≠ 1) {i j k l : Fin r}
    (hij : i ≠ j) {x y : E} {a b : K} (hx : θ x = radRoot r K i j a)
    (hy : θ y = radRoot r K k l b) : x * y = y * x := by
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      exact lift_radRoot_mul_comm_self hθ hker hr hc hij hx hy
    · exact lift_radRoot_mul_comm_of_ne hθ hker hr hc hij (Or.inr rfl) (Ne.symm hij) hjl hx hy
  · by_cases hil : i = l
    · subst hil
      by_cases hjk : j = k
      · subst hjk
        have hy' : θ y = radRoot r K i j (-b) := by rw [hy, radRoot_swap]
        exact lift_radRoot_mul_comm_self hθ hker hr hc hij hx hy'
      · exact lift_radRoot_mul_comm_of_ne hθ hker hr hc hij (Or.inr rfl) hjk (Ne.symm hij) hx hy
    · exact lift_radRoot_mul_comm_of_ne hθ hker hr hc hij (Or.inl rfl) hik hil hx hy

theorem preRad_mul_comm (hr : 3 ≤ r) (hK : 3 ≤ Nat.card K) {x y : E}
    (hx : x ∈ preRad θ (radicalE r K)) (hy : y ∈ preRad θ (radicalE r K)) : x * y = y * x := by
  obtain ⟨c, hc0, hc1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le hK
  set G : Set E := {g | ∃ i j a, i < j ∧ θ g = radRoot r K i j a} ∪ {g | θ g = 1} with hG
  have hGG : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g := by
    rintro g (⟨i, j, a, hij, hg⟩ | hg) h (⟨k, l, b, -, hh⟩ | hh)
    · exact lift_radRoot_mul_comm hθ hker hr (c := Units.mk0 c hc0) hc1 hij.ne hg hh
    · exact Subgroup.mem_center_iff.mp (hker h hh) g
    · exact (Subgroup.mem_center_iff.mp (hker g hg) h).symm
    · exact (Subgroup.mem_center_iff.mp (hker g hg) h).symm
  have h1 : Subgroup.closure G ≤ Subgroup.centralizer G := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    exact hGG h hh g hg
  have h2 : Subgroup.closure G ≤ Subgroup.centralizer (Subgroup.closure G : Set E) := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (h1 hh) g hg).symm
  have hM : ∀ z ∈ preRad θ (radicalE r K), z ∈ Subgroup.closure G := by
    intro z hz
    obtain ⟨B, hB⟩ := hz
    have hmap : θ z ∈ (Subgroup.closure G).map θ := by
      rw [MonoidHom.map_closure, ← hB]
      refine Subgroup.closure_mono ?_ (radicalE_mem_closure_radRoot B)
      rintro _ ⟨i, j, a, hij, rfl⟩
      obtain ⟨g, hg⟩ := hθ (radRoot r K i j a)
      exact ⟨g, Or.inl ⟨i, j, a, hij, hg⟩, hg⟩
    obtain ⟨g, hg, hgz⟩ := hmap
    have hk : g⁻¹ * z ∈ Subgroup.closure G := Subgroup.subset_closure
      (Or.inr (by rw [Set.mem_ofPred_eq, map_mul, map_inv, hgz, inv_mul_cancel]))
    have := Subgroup.mul_mem _ hg hk
    rwa [mul_inv_cancel_left] at this
  exact Subgroup.mem_centralizer_iff.mp (h2 (hM y hy)) x (hM x hx)

end Roots

variable (r K) in
@[expose] def constUnits : Kˣ →* (Fin r → Kˣ) where
  toFun s _ := s
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coprimeCommutator_map_le {U V : Type*} [Group U] [AddCommGroup V] [DistribMulAction U V]
    (A : Subgroup U) (φ : V →+ V) (hφ : ∀ a ∈ A, ∀ v, φ (a • v) = a • φ v) :
    (coprimeCommutator A V).map φ ≤ coprimeCommutator A V := by
  rw [AddSubgroup.map_le_iff_le_comap, coprimeCommutator, AddSubgroup.closure_le]
  rintro _ ⟨a, ha, v, rfl⟩
  change φ (a • v - v) ∈ AddSubgroup.closure _
  rw [map_sub, hφ a ha v]
  exact AddSubgroup.subset_closure ⟨a, ha, φ v, rfl⟩

theorem coprime_two_card_units : Nat.Coprime 2 (Nat.card Kˣ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) fun _ _ => Units.ext
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 2 h
  have hx1 : x = 1 := by
    have h2 : x ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
    apply Units.ext
    apply eq_of_mul_self_eq_mul_self
    rw [← Units.val_mul, ← sq, h2, Units.val_one, mul_one]
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

section Core

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
  {θ : E →* orthElementaryGroup (quadPlus r K)}

theorem ker_eq_bot_of_catalog (hr : 4 ≤ r) (hK : 3 ≤ Nat.card K) (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ := by
  have hr3 : 3 ≤ r := by omega
  have hker : ∀ z, θ z = 1 → z ∈ Subgroup.center E := fun z hz => hC hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (orthElementaryGroup (quadPlus r K)) := finite_orthElementaryGroup
  obtain ⟨c, hc0, hc1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le hK
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hr3
  set R := (leviSL r K hr3).range with hR
  have : Group.IsPerfect R := Group.IsPerfect.range _
  set F := leviLift θ R with hF
  have : Group.IsPerfect F := isPerfect_leviLift θ R hθ hC
  have hFinj : ∀ f ∈ F, θ f = 1 → f = 1 := by
    obtain ⟨P₁, hP₁⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := r) (by omega)
    set S : Sylow 2 R := P₁.mapSurjective (leviSL r K hr3).rangeRestrict_surjective with hSdef
    have hS : (S : Subgroup R) ≤ (LinearFlag.unitriangular r K).map
        (leviSL r K hr3).rangeRestrict := by
      rw [hSdef, Sylow.coe_mapSurjective, hP₁]
    have hinj : Function.Injective (leviSL r K hr3).rangeRestrict :=
      MonoidHom.rangeRestrict_injective_iff.mpr (leviSL_injective hr3)
    have hbot := LinearCover.ker_eq_bot_of_rootHom hK hr (leviSL r K hr3).rangeRestrict
      (fun u _ hu => hinj (hu.trans (map_one _).symm)) S hS (leviLiftHom θ R)
      (leviLiftHom_surjective θ R hθ) (leviLiftHom_ker_le_center θ R hC)
      (isPGroup_leviLiftHom_ker θ R h2)
    intro f hf hθf
    have hmem : (⟨f, hf⟩ : F) ∈ (leviLiftHom θ R).ker := (leviLiftHom_eq_one_iff θ R _).2 hθf
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  set M := preRad θ (radicalE r K) with hM
  have hcommM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy =>
    preRad_mul_comm hθ hker hr3 hK hx hy
  set ρ₀ : Kˣ →* orthElementaryGroup (quadPlus r K) := (torusE r K hr3).comp (constUnits r K)
    with hρ₀
  set f₀ : Kˣ → altSubgroup r K → altSubgroup r K := fun s B =>
    ⟨((s : K) * s) • (B : Matrix (Fin r) (Fin r) K), smul_mem_altSubgroup _ B.2⟩ with hf₀def
  have hf₀ : ∀ s B, ρ₀ s * radicalE r K (Multiplicative.ofAdd B) * (ρ₀ s)⁻¹ =
      radicalE r K (Multiplicative.ofAdd (f₀ s B)) := fun s B =>
    torusE_const_mul_radicalE_mul_inv hr3 s (Multiplicative.ofAdd B)
  set act := actRad hθ hC ρ₀ hf₀ with hact
  let _ : CommGroup M :=
    { (inferInstance : Group M) with mul_comm := fun x y => Subtype.ext (hcommM x x.2 y y.2) }
  let actA : Kˣ →* AddMonoid.End (Additive M) :=
    { toFun := fun s => MonoidHom.toAdditive (act s).toMonoidHom
      map_one' := by
        ext x
        rw [map_one]
        rfl
      map_mul' := fun s t => by
        ext x
        rw [map_mul]
        rfl }
  let _ : DistribMulAction Kˣ (Additive M) := DistribMulAction.compHom (Additive M) actA
  have hsmul : ∀ (s : Kˣ) (x : Additive M), s • x = Additive.ofMul (act s x.toMul) :=
    fun _ _ => rfl
  have hM2 : IsPGroup 2 M := by
    intro x
    obtain ⟨B, hB⟩ := x.2
    have hx2 : θ ((x : E) ^ 2) = 1 := by
      rw [map_pow, ← hB, ← map_pow]
      have hB2 : B ^ 2 = 1 := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        rw [toAdd_pow, AddSubgroup.coe_nsmul, two_nsmul, toAdd_one, ZeroMemClass.coe_zero]
        exact Matrix.ext fun k l => CharTwo.add_self_eq_zero _
      rw [hB2, map_one]
    obtain ⟨k, hk⟩ := h2 ⟨(x : E) ^ 2, hx2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk' ⊢
    rw [pow_succ', pow_mul]
    exact hk'
  have hcop : Nat.Coprime (Nat.card (⊤ : Subgroup Kˣ)) (Nat.card (Additive M)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hM2
    rw [Subgroup.card_top, show Nat.card (Additive M) = Nat.card M from rfl, hn]
    exact Nat.Coprime.pow_right n (coprime_two_card_units (K := K)).symm
  obtain ⟨hcompl, -⟩ :=
    abelian_coprime_fixed_commutator_decomposition (U := Kˣ) (V := Additive M) ⊤ hcop
  set D := coprimeCommutator (⊤ : Subgroup Kˣ) (Additive M) with hD
  set Cf := coprimeFixed (⊤ : Subgroup Kˣ) (Additive M) with hCf
  obtain ⟨s₀, hs₀⟩ : ∃ s : Kˣ, (s : K) * s ≠ 1 :=
    ⟨Units.mk0 c hc0, LinearCover.mul_self_ne_one hc1⟩
  have hfix_ker : ∀ x : Additive M, x ∈ Cf → θ (x.toMul : E) = 1 := by
    intro x hx
    have h : act s₀ x.toMul = x.toMul := by
      have := hx s₀ (Subgroup.mem_top _)
      rw [hsmul] at this
      exact Additive.ofMul.injective (this.trans (ofMul_toMul x).symm)
    have hπ := piRad_actRad hθ hC ρ₀ (radicalE_injective (r := r) (K := K)) hf₀ s₀ x.toMul
    rw [h] at hπ
    set B := (piRad θ (radicalE_injective (r := r) (K := K)) x.toMul).toAdd with hBdef
    have hB : (B : Matrix (Fin r) (Fin r) K) = 0 := by
      have hm : (B : Matrix (Fin r) (Fin r) K) = ((s₀ : K) * s₀) • (B : Matrix (Fin r) (Fin r) K) :=
        congrArg Subtype.val hπ
      have h0 : (((s₀ : K) * s₀) - 1) • (B : Matrix (Fin r) (Fin r) K) = 0 := by
        rw [sub_smul, one_smul, ← hm, sub_self]
      exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hs₀)
    have hB1 : piRad θ (radicalE_injective (r := r) (K := K)) x.toMul = 1 := by
      rw [← ofAdd_toAdd (piRad θ _ x.toMul), ← hBdef]
      exact congrArg Multiplicative.ofAdd (Subtype.ext hB)
    exact (piRad_eq_one_iff _ _).1 hB1
  have hker_fix : ∀ x : Additive M, θ (x.toMul : E) = 1 → x ∈ Cf := by
    intro x hx s _
    rw [hsmul, actRad_apply_of_mem_ker hθ hC ρ₀ (radicalE_injective (r := r) (K := K)) hf₀ s
      ((MonoidHom.mem_ker).2 ((piRad_eq_one_iff _ _).2 hx)), ofMul_toMul]
  let VM : Subgroup M :=
    { carrier := {x | Additive.ofMul x ∈ D}
      mul_mem' := fun {a b} ha hb => by
        change Additive.ofMul (a * b) ∈ D
        rw [ofMul_mul]
        exact D.add_mem ha hb
      one_mem' := by
        change Additive.ofMul (1 : M) ∈ D
        rw [ofMul_one]
        exact D.zero_mem
      inv_mem' := fun {a} ha => by
        change Additive.ofMul a⁻¹ ∈ D
        rw [ofMul_inv]
        exact D.neg_mem ha }
  have hVM : ∀ x, x ∈ VM ↔ Additive.ofMul x ∈ D := fun _ => Iff.rfl
  set V' : Subgroup E := VM.map M.subtype with hV'def
  set V := (radicalE r K).range with hVdef
  have hV' : ∀ v ∈ V', θ v ∈ V := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hV'ker : ∀ v ∈ V', θ v = 1 → v ∈ (⊥ : Subgroup E) := by
    rintro _ ⟨y, hy, rfl⟩ hθy
    have hCy : Additive.ofMul y ∈ Cf := hker_fix _ hθy
    have hbot : Additive.ofMul y ∈ D ⊓ Cf := ⟨(hVM y).1 hy, hCy⟩
    rw [hcompl.inf_eq_bot, AddSubgroup.mem_bot] at hbot
    rw [Subgroup.mem_bot]
    change ((y : M) : E) = 1
    rw [show y = 1 from Additive.ofMul.injective (hbot.trans ofMul_one.symm)]
    rfl
  have hV'surj : ∀ b ∈ V, ∃ v ∈ V', θ v = b := by
    intro b hb
    obtain ⟨x, hx⟩ := hθ b
    have hxM : x ∈ M := by rw [hM, preRad, Subgroup.mem_comap, hx]; exact hb
    have htop : Additive.ofMul (⟨x, hxM⟩ : M) ∈ D ⊔ Cf := by
      rw [hcompl.sup_eq_top]
      exact AddSubgroup.mem_top _
    obtain ⟨d, hd, z, hz, hdz⟩ := AddSubgroup.mem_sup.1 htop
    refine ⟨(d.toMul : E), ⟨d.toMul, (hVM _).2 (by rwa [ofMul_toMul]), rfl⟩, ?_⟩
    have hxdz : (x : E) = (d.toMul : E) * (z.toMul : E) := by
      have := congrArg (fun w : Additive M => ((w.toMul : M) : E)) hdz
      simpa [toMul_add] using this.symm
    rw [← hx, hxdz, map_mul, hfix_ker z hz, mul_one]
  have hFR : ∀ u ∈ F, θ u ∈ R := fun u hu => leviLift_le_comap θ R hu
  have hnormM : ∀ u ∈ F, ∀ y ∈ M, u * y * u⁻¹ ∈ M := by
    intro u hu y hy
    obtain ⟨A, hA⟩ := hFR u hu
    obtain ⟨B, hB⟩ := hy
    refine ⟨Multiplicative.ofAdd ⟨(A : Matrix (Fin r) (Fin r) K) *
      (B.toAdd : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K)ᵀ,
        congr_mem_altSubgroup _ B.toAdd.2⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hA, ← hB, leviSL_mul_radicalE_mul_inv]
  have hcommT : ∀ u ∈ F, ∀ (s : Kˣ) (t : E), θ t = ρ₀ s → t * u = u * t := by
    intro u hu s t ht
    have hDR : (R.comap θ).map (MulAut.conj t).toMonoidHom ≤ R.comap θ := by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨A, hA⟩ := hd
      change θ (t * d * t⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv, ht, ← hA, hρ₀, MonoidHom.comp_apply,
        show constUnits r K s = fun _ => s from rfl, torusE_const_mul_leviSL_comm,
        mul_inv_cancel_right]
      exact ⟨A, rfl⟩
    have hFt : t * u * t⁻¹ ∈ F := by
      have hmap : F.map (MulAut.conj t).toMonoidHom ≤ F := by
        rw [hF, leviLift, Subgroup.map_commutator]
        exact Subgroup.commutator_mono hDR hDR
      exact hmap ⟨u, hu, rfl⟩
    have hw : t * u * t⁻¹ * u⁻¹ = 1 := by
      refine hFinj _ (F.mul_mem hFt (F.inv_mem hu)) ?_
      obtain ⟨A, hA⟩ := hFR u hu
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ht, ← hA, hρ₀, MonoidHom.comp_apply,
        show constUnits r K s = fun _ => s from rfl, torusE_const_mul_leviSL_comm,
        mul_inv_cancel_right, mul_inv_cancel]
    calc t * u = t * u * t⁻¹ * u⁻¹ * u * t := by group
      _ = u * t := by rw [hw, one_mul]
  have hnormV : ∀ u ∈ F, ∀ v ∈ V', u * v * u⁻¹ ∈ V' := by
    intro u hu
    let φ : M →* M :=
      { toFun := fun y => ⟨u * y * u⁻¹, hnormM u hu y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
    have hφ : ∀ (s : Kˣ) (y : M), φ (act s y) = act s (φ y) := by
      intro s y
      obtain ⟨t, ht⟩ := hθ (ρ₀ s)
      apply Subtype.ext
      change u * ((act s y : M) : E) * u⁻¹ = ((act s (φ y) : M) : E)
      rw [coe_actRad_of_map_eq hθ hC ρ₀ hf₀ ht, coe_actRad_of_map_eq hθ hC ρ₀ hf₀ ht]
      change u * (t * y * t⁻¹) * u⁻¹ = t * (u * y * u⁻¹) * t⁻¹
      have htu := hcommT u hu s t ht
      calc u * (t * y * t⁻¹) * u⁻¹ = (u * t) * y * (u * t)⁻¹ := by group
        _ = (t * u) * y * (t * u)⁻¹ := by rw [htu]
        _ = t * (u * y * u⁻¹) * t⁻¹ := by group
    have hDφ := coprimeCommutator_map_le (⊤ : Subgroup Kˣ) (MonoidHom.toAdditive φ)
      (fun s _ x => by rw [hsmul, hsmul]; exact congrArg Additive.ofMul (hφ s x.toMul))
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨φ y, (hVM _).2 (hDφ ⟨Additive.ofMul y, (hVM y).1 hy, rfl⟩), rfl⟩
  set UR := (LinearFlag.unitriangular r K).map (leviSL r K hr3) with hURdef
  set Ũ : Subgroup E := UR.comap θ ⊓ F with hŨdef
  have hŨ : ∀ u ∈ Ũ, θ u ∈ UR := fun u hu => hu.1
  have hŨsurj : ∀ a ∈ UR, ∃ u ∈ Ũ, θ u = a := by
    intro a ha
    have haR : a ∈ F.map θ := by
      rw [map_leviLift θ R hθ]
      exact Subgroup.map_le_range _ _ ha
    obtain ⟨f, hf, hfa⟩ := haR
    exact ⟨f, Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 (by rw [hfa]; exact ha), hf⟩, hfa⟩
  have hŨker : ∀ u ∈ Ũ, θ u = 1 → u ∈ (⊥ : Subgroup E) := fun u hu h =>
    (Subgroup.mem_bot).2 (hFinj u hu.2 h)
  have hŨN : Ũ ≤ Subgroup.normalizer (V' : Set E) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hnormV u hu.2 v hv, fun hv => ?_⟩
    have := hnormV u⁻¹ (F.inv_mem hu.2) _ hv
    rwa [show u⁻¹ * (u * v * u⁻¹) * u⁻¹⁻¹ = v by group] at this
  obtain ⟨S, hSU⟩ := posUnip_isSylow (r := r) (K := K) 2 (by omega)
    fun a ha => map_flag_top_ne_Xstar hr3 ha
  have hS : ∀ g ∈ (S : Subgroup (orthElementaryGroup (quadPlus r K))),
      ∃ a ∈ UR, ∃ b ∈ V, g = a * b := by
    intro g hg
    rw [hSU, Subgroup.mem_subgroupOf] at hg
    obtain ⟨A, hA, B, rfl⟩ := exists_leviSL_radicalE_of_mem_posUnip hr3 hg
    exact ⟨_, ⟨A, hA, rfl⟩, _, ⟨B, rfl⟩, rfl⟩
  have hVUR : UR ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨A, -, rfl⟩, ⟨B, hB⟩⟩
    exact (Subgroup.mem_bot).2 (leviSL_eq_one_of_eq_radicalE hr3 hB.symm)
  exact le_bot_iff.1 (ker_le_of_lifts hθ hC h2 ⊥ V UR S hS hVUR V' Ũ hŨN hV' hŨ hV'surj
    hŨsurj hV'ker hŨker)

end Core

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

namespace CFSG.LocalAnalysis.ComponentInitial

open OrthogonalSplit CFSG.LieType.Universal.Spin

theorem even_split_orthogonal_catalog_perfect_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f) (hJ : CFSG.Blueprint.LieModel J .POmegaPlus n 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, _, hcard, -, ⟨e⟩⟩ := exists_mulEquiv_elementaryGroup_of_lieModel hJ
  have hK : 3 ≤ Nat.card K := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set η' : E →* orthElementaryGroup (quadPlus n K) := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_catalog hn hK (e.surjective.comp hη) (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial
