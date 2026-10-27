module

public import CFSG.GF2Type.Smith1979.IdxFourIdentWeightsDefs
import all CFSG.GF2Type.Smith1979.GammaU.Bridge
public import CFSG.GF2Type.Smith1979.CaseI25Weights
public import CFSG.GF2Type.Smith1979.GammaU.Bridge
public import CFSG.GF2Type.Smith1979.IdxFourIdentMonPlanes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU MonAux

namespace FrameAux

theorem eq_zero_of_theta0_eq {x : V12} (h : theta0 x = x) : x = 0 := by
  have key : ∀ a b : ZMod 2, b = a → a + b = b → a = 0 ∧ b = 0 := by decide
  have hp := fun i => key (x (lo i)) (x (hi i)) ((theta0_lo x i).symm.trans (congrFun h (lo i)))
    ((theta0_hi x i).symm.trans (congrFun h (hi i)))
  exact ext_lo_hi (fun i => (hp i).1) (fun i => (hp i).2)

theorem theta0_theta0 (x : V12) : theta0 (theta0 x) = theta0 x + x := by
  refine ext_lo_hi (fun i => ?_) (fun i => ?_) <;>
    simp only [theta0_lo, theta0_hi, Pi.add_apply] <;> ring

theorem q0_theta0 (x : V12) : q0 (theta0 x) = q0 x := (mem_gammaU.1 theta0e_mem_gammaU).1 x

theorem f0_map {g : G12} (hg : g ∈ gammaU) (x y : V12) : f0 (g x) (g y) = f0 x y := by
  rw [← polar_q0, ← polar_q0]
  simp only [QuadraticMap.polar, ← map_add, (mem_gammaU.1 hg).1]

theorem f0_add_right (x y z : V12) : f0 x (y + z) = f0 x y + f0 x z := by
  rw [← polar_q0Form, ← polar_q0Form, ← polar_q0Form, QuadraticMap.polar_add_right]

theorem f0_zero_right (x : V12) : f0 x 0 = 0 := by
  rw [← polar_q0Form, QuadraticMap.polar_zero_right]

theorem thPair_iterate (k : ℕ) (p : ZMod 2 × ZMod 2) : thPair^[k] p = omegaPow (k : ZMod 3) p := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Nat.cast_zero, omegaPow_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← omegaPow_one, ← omegaPow_add]
    congr 1
    push_cast
    ring

theorem theta0_iterate_comb (v : V12) (p : ZMod 2 × ZMod 2) (k : ℕ) :
    (⇑theta0)^[k] (p.1 • v + p.2 • theta0 v) =
      (omegaPow (k : ZMod 3) p).1 • v + (omegaPow (k : ZMod 3) p).2 • theta0 v := by
  have h : Function.Semiconj (fun p : ZMod 2 × ZMod 2 => p.1 • v + p.2 • theta0 v) thPair
      theta0 := fun p => by
    simp only [thPair, map_add, map_smul, theta0_theta0, smul_add, add_smul]
    abel
  rw [← thPair_iterate]
  exact (h.iterate_right k p).symm

section Group

variable {A : Type} [CommGroup A] [Finite A]

theorem sup_zpowers_eq_top {H : Subgroup A} (hH : H.index = 3) {θ : A} (hθ : θ ∉ H) :
    H ⊔ Subgroup.zpowers θ = ⊤ := by
  have hd : (H ⊔ Subgroup.zpowers θ).index ∣ 3 := hH ▸ Subgroup.index_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact Subgroup.index_eq_one.mp h1
  · have h := Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ Subgroup.zpowers θ)
    rw [hH, h3] at h
    have hle : H ⊔ Subgroup.zpowers θ ≤ H := Subgroup.relIndex_eq_one.mp (by omega)
    exact absurd (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers θ))) hθ

theorem exists_pow_mul {H : Subgroup A} (hH : H.index = 3) {θ : A} (hθ : θ ∉ H) (a : A) :
    ∃ n : ℕ, ∃ h ∈ H, a = θ ^ n * h := by
  have ha : a ∈ H ⊔ Subgroup.zpowers θ := by
    rw [sup_zpowers_eq_top hH hθ]
    exact Subgroup.mem_top a
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp ha
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  exact ⟨n, y, hy, mul_comm _ _⟩

theorem pow_mem_iff (hA3 : ∀ a : A, a ^ 3 = 1) {H : Subgroup A} {θ : A} (hθ : θ ∉ H) (n : ℕ) :
    θ ^ n ∈ H ↔ 3 ∣ n := by
  rw [pow_eq_pow_mod n (hA3 θ)]
  refine ⟨fun h => ?_, fun h => by rw [Nat.mod_eq_zero_of_dvd h, pow_zero]; exact one_mem H⟩
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · exact Nat.dvd_of_mod_eq_zero h0
  · rw [h1, pow_one] at h
    exact absurd h hθ
  · rw [h2] at h
    have h4 := pow_mem h 2
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hA3, one_mul, pow_one] at h4
    exact absurd h4 hθ

theorem apply_mem_weightSpace (hA3 : ∀ a : A, a ^ 3 = 1) {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (σ : Representation (ZMod 2) A V) {H : Subgroup A} (a : A) {w : V}
    (hw : w ∈ LemmaW.weightSpace σ H) : σ a w ∈ LemmaW.weightSpace σ H := by
  obtain ⟨hfix, h0⟩ := (LemmaW.mem_weightSpace_iff σ hA3 H w).mp hw
  refine (LemmaW.mem_weightSpace_iff σ hA3 H _).mpr
    ⟨(LemmaW.mem_fixedSpace σ).mpr fun h hh => ?_, ?_⟩
  · rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
      (LemmaW.mem_fixedSpace σ).mp hfix h hh]
  · have := congrArg (fun x => σ.asAlgebraHom x w)
      (show LemmaW.eSub (⊤ : Subgroup A) * MonoidAlgebra.of (ZMod 2) A a = LemmaW.eSub ⊤ by
        rw [mul_comm]
        exact LemmaW.of_mul_eSub (Subgroup.mem_top a))
    simpa [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply, h0] using this

theorem exists_iterate_of_weightSpace (hA3 : ∀ a : A, a ^ 3 = 1) {ρ : A →* G12} {θ : A}
    (hθ : ρ θ = theta0e) {H : Subgroup A} (hH : H.index = 3) (hθH : θ ∉ H) (a : A) :
    ∃ n : ℕ, (a ∈ H ↔ 3 ∣ n) ∧
      ∀ w ∈ LemmaW.weightSpace (rep ρ) H, ρ a w = (⇑theta0)^[n] w := by
  obtain ⟨n, h, hh, rfl⟩ := exists_pow_mul hH hθH a
  refine ⟨n, (Subgroup.mul_mem_cancel_right H hh).trans (pow_mem_iff hA3 hθH n), fun w hw => ?_⟩
  have hfix : ρ h w = w := (LemmaW.mem_fixedSpace (rep ρ)).mp
    ((LemmaW.mem_weightSpace_iff (rep ρ) hA3 H w).mp hw).1 h hh
  rw [map_mul, LinearEquiv.mul_apply, hfix, map_pow, hθ, LinearEquiv.pow_apply]
  rfl

end Group

end FrameAux

open FrameAux

theorem exists_frame
    {A : Type} [CommGroup A] [Finite A] (hA3 : ∀ a : A, a ^ 3 = 1)
    {ρ : A →* G12} (hρg : ∀ a, ρ a ∈ gammaU) {θ : A} (hθ : ρ θ = theta0e)
    (H : Fin 6 → Subgroup A) (hH3 : ∀ i, (H i).index = 3) (hθH : ∀ i, θ ∉ H i)
    (hHinj : Function.Injective H)
    (hdim : ∀ i, Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) (H i)) = 2)
    (htop : ⨆ i, LemmaW.weightSpace (rep ρ) (H i) = ⊤) :
    ∃ (g : G12) (c : A →* Multiplicative (Fin 6 → ZMod 3)),
      g ∈ gammaU ∧ g * theta0e = theta0e * g ∧
      (∀ i x, x ∈ plane i ↔ g x ∈ LemmaW.weightSpace (rep ρ) (H i)) ∧
      (∀ a, g⁻¹ * ρ a * g = diagE (c a).toAdd) ∧
      (∀ a i, a ∈ H i ↔ (c a).toAdd i = 0) := by
  set V : Fin 6 → Submodule (ZMod 2) V12 := fun i => LemmaW.weightSpace (rep ρ) (H i)
  have hVρ : ∀ i a {v}, v ∈ V i → ρ a v ∈ V i := fun i a v hv =>
    apply_mem_weightSpace hA3 (rep ρ) a hv
  have hVθ : ∀ i {v}, v ∈ V i → theta0 v ∈ V i := fun i v hv => by
    have h := hVρ i θ hv
    rwa [hθ, theta0e_apply] at h
  have hkey := fun i a => exists_iterate_of_weightSpace hA3 hθ (hH3 i) (hθH i) a
  have horth : ∀ i j, i ≠ j → ∀ v ∈ V i, ∀ w ∈ V j, f0 v w = 0 := by
    intro i j hij v hv w hw
    have hnle : ¬ H i ≤ H j := fun hle => by
      have h := LemmaW.sup_eq_top_of_index_eq_three (hH3 i) (hH3 j) (fun h => hij (hHinj h))
      rw [sup_eq_right.mpr hle] at h
      have h3 := hH3 j
      rw [h, Subgroup.index_top] at h3
      exact absurd h3 (by norm_num)
    obtain ⟨a, hai, haj⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    obtain ⟨n, hnH, hnV⟩ := hkey j a
    have hav : ρ a v = v := (LemmaW.mem_fixedSpace (rep ρ)).mp
      ((LemmaW.mem_weightSpace_iff (rep ρ) hA3 (H i) v).mp hv).1 a hai
    have h1 : ∀ u ∈ V j, f0 v u = f0 v ((⇑theta0)^[n % 3] u) := fun u hu => by
      rw [← f0_map (hρg a) v u, hav, hnV u hu,
        (show Function.IsPeriodicPt (⇑theta0) 3 u from theta0_theta0_theta0 u).iterate_mod_apply]
    have hn : n % 3 = 1 ∨ n % 3 = 2 := by
      have : ¬ 3 ∣ n := fun h => haj (hnH.mpr h)
      omega
    rcases hn with hn | hn
    · have h := h1 (theta0 w) (hVθ j hw)
      rw [hn, Function.iterate_one, theta0_theta0, f0_add_right] at h
      linear_combination -h
    · have h := h1 (theta0 (theta0 w)) (hVθ j (hVθ j hw))
      rw [hn, show (⇑theta0)^[2] (theta0 (theta0 w)) = theta0 (theta0 (theta0 (theta0 w))) from rfl,
        theta0_theta0 (theta0 (theta0 w)), theta0_theta0_theta0, f0_add_right] at h
      linear_combination -h
  have hex : ∀ i, ∃ v ∈ V i, q0 v = 1 := by
    intro i
    by_contra hne
    push Not at hne
    have hz : ∀ v ∈ V i, q0 v = 0 := fun v hv =>
      (zmod2_eq_zero_or_eq_one _).resolve_right (hne v hv)
    have hbot : V i = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => eq_zero_of_f0 fun y => ?_
      have hy : y ∈ ⨆ j, V j := by rw [htop]; exact Submodule.mem_top
      refine Submodule.iSup_induction V (motive := fun y => f0 v y = 0) hy (fun j w hw => ?_)
        (f0_zero_right v) (fun y z hy hz => by rw [f0_add_right, hy, hz, add_zero])
      by_cases hij : i = j
      · rw [← hij] at hw
        rw [← polar_q0]
        simp only [QuadraticMap.polar, hz _ (add_mem hv hw), hz v hv, hz w hw, sub_zero]
      · exact horth i j hij v hv w hw
    have h2 := hdim i
    rw [show LemmaW.weightSpace (rep ρ) (H i) = V i from rfl, hbot, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  choose bv hbvV hbvq using hex
  obtain ⟨b, hb⟩ : ∃ b : ℕ → V12, ∀ i : Fin 6, b i = bv i :=
    ⟨fun n => if h : n < 6 then bv ⟨n, h⟩ else 0, fun i => dite_eq_left i.isLt⟩
  have hθq : ∀ v, q0Form (theta0 v) = q0Form v := q0_theta0
  have hθ3 : ∀ v, theta0 (theta0 (theta0 v)) = v := theta0_theta0_theta0
  have hfix : ∀ v, theta0 v = v → v = 0 := fun v h => eq_zero_of_theta0_eq h
  have hfam : IsFam q0Form theta0 6 b := by
    refine ⟨fun n hn => ?_, fun n hn m hm hnm => ?_⟩
    · rw [show b n = bv ⟨n, hn⟩ from hb ⟨n, hn⟩, q0Form_apply]
      exact hbvq _
    · have hne : (⟨n, hn⟩ : Fin 6) ≠ ⟨m, hm⟩ := fun h => hnm (congrArg Fin.val h)
      rw [show b n = bv ⟨n, hn⟩ from hb ⟨n, hn⟩, show b m = bv ⟨m, hm⟩ from hb ⟨m, hm⟩,
        polar_q0Form, polar_q0Form]
      exact ⟨horth _ _ hne _ (hbvV _) _ (hbvV _), horth _ _ hne _ (hVθ _ (hbvV _)) _ (hbvV _)⟩
  have hinj := famMap_injective hθq hθ3 hfix hfam
  set g : G12 := LinearEquiv.ofBijective (famMap theta0 b)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hgx : ∀ x, g x = famMap theta0 b x := fun x => rfl
  have hgθ : ∀ x, g (theta0 x) = theta0 (g x) := fun x =>
    (theta_famMap hθq hθ3 hfix hfam x).symm
  have hgΓ : g ∈ gammaU := mem_gammaU.2 ⟨fun x => q_famMap hθq hθ3 hfix hfam x, Or.inl hgθ⟩
  have hplane : ∀ i x, x ∈ plane i ↔ g x ∈ V i := by
    intro i x
    constructor
    · intro hx
      rw [hgx, famMap_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hji : j = i
      · rw [hji, hb i]
        exact add_mem (Submodule.smul_mem _ _ (hbvV i)) (Submodule.smul_mem _ _ (hVθ i (hbvV i)))
      · obtain ⟨h1, h2⟩ := (mem_plane_iff i x).1 hx j hji
        rw [h1, h2, zero_smul, zero_smul, add_zero]
        exact zero_mem _
    · intro hx
      refine (mem_plane_iff i x).2 fun j hji => ⟨?_, ?_⟩
      · rw [← polar_famMap_theta_b hθq hθ3 hfix hfam x j, polar_q0Form, hb j]
        exact horth i j (Ne.symm hji) _ hx _ (hVθ j (hbvV j))
      · rw [← polar_famMap_b hθq hθ3 hfix hfam x j, polar_q0Form, hb j]
        exact horth i j (Ne.symm hji) _ hx _ (hbvV j)
  choose n hnH hnV using hkey
  set c₀ : A → Fin 6 → ZMod 3 := fun a i => (n i a : ZMod 3)
  have hact : ∀ a x, ρ a (g x) = g (diagE (c₀ a) x) := by
    intro a x
    rw [hgx, hgx, famMap_apply, famMap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hu : x (lo i) • bv i + x (hi i) • theta0 (bv i) ∈ V i :=
      add_mem (Submodule.smul_mem _ _ (hbvV i)) (Submodule.smul_mem _ _ (hVθ i (hbvV i)))
    rw [hb i, hnV i a _ hu, diagE_apply, diagFun_lo, diagFun_hi]
    exact theta0_iterate_comb (bv i) (x (lo i), x (hi i)) (n i a)
  have hconj : ∀ a, g⁻¹ * ρ a * g = diagE (c₀ a) := by
    intro a
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    exact LinearEquiv.ext fun x => hact a x
  have hmul : ∀ a a', c₀ (a * a') = c₀ a + c₀ a' := by
    intro a a'
    apply diagE_injective
    rw [diagE_add, ← hconj, ← hconj, ← hconj, map_mul]
    group
  refine ⟨g, MonoidHom.mk' (fun a => Multiplicative.ofAdd (c₀ a)) fun a a' => by rw [hmul]; rfl,
    hgΓ, LinearEquiv.ext fun x => hgθ x, hplane, hconj, fun a i => ?_⟩
  change a ∈ H i ↔ ((n i a : ℕ) : ZMod 3) = 0
  rw [ZMod.natCast_eq_zero_iff]
  exact hnH i a

end CFSG.GF2Type.Smith1979.IdxFour
