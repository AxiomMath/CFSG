module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.LinearAlgebra.MatrixPlanes
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.HardMathSupport.Timmesfeld.LinearRank

section Powers

theorem exists_eq_pow_of_pow_eq {G : Type*} [CommGroup G] {p d : ℕ} (hp : p.Prime)
    (hd : ¬ p ∣ d) {c lam : G} (h : c ^ d = lam ^ p) : ∃ μ : G, c = μ ^ p := by
  have hcop : Nat.gcd d p = 1 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hd))
  have hb : ((Nat.gcd d p : ℕ) : ℤ) = d * Nat.gcdA d p + p * Nat.gcdB d p := Nat.gcd_eq_gcd_ab d p
  rw [hcop, Nat.cast_one] at hb
  refine ⟨lam ^ Nat.gcdA d p * c ^ Nat.gcdB d p, ?_⟩
  have e1 : (lam ^ Nat.gcdA d p) ^ p = c ^ ((d : ℤ) * Nat.gcdA d p) := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm (Nat.gcdA d p : ℤ) (p : ℤ), _root_.zpow_mul,
      zpow_natCast, ← h, ← zpow_natCast c d, ← _root_.zpow_mul]
  have e2 : (c ^ Nat.gcdB d p) ^ p = c ^ ((p : ℤ) * Nat.gcdB d p) := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm]
  rw [mul_pow, e1, e2, ← _root_.zpow_add, ← hb, zpow_one]

theorem exists_pow_mul_eq_pow {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card Kˣ) (u v : Kˣ) (hu : ¬ ∃ μ : Kˣ, u = μ ^ p) :
    ∃ (i : ℕ) (μ : Kˣ), u ^ i * v = μ ^ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  obtain ⟨a, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg u)
  obtain ⟨b, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg v)
  have hpa : ¬ p ∣ a := by
    rintro ⟨k, rfl⟩
    exact hu ⟨g ^ k, by rw [← pow_mul, mul_comm]⟩
  have hcop : Nat.Coprime a p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)
  obtain ⟨a', -, ha'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hdvd : p ∣ a * (a' * (p - 1) * b) + b := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h1 : ((a * a' : ℕ) : ZMod p) = 1 := by
      rw [← Nat.mod_add_div (a * a') p, ha']
      push_cast
      rw [ZMod.natCast_self, zero_mul, add_zero]
    have h2 : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
    have h3 : ((a * (a' * (p - 1) * b) + b : ℕ) : ZMod p) =
        ((a * a' : ℕ) : ZMod p) * ((p - 1 : ℕ) : ZMod p) * (b : ZMod p) + (b : ZMod p) := by
      push_cast
      ring
    rw [h3, h1, h2]
    ring
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨a' * (p - 1) * b, g ^ k, ?_⟩
  rw [← pow_mul, ← pow_add, ← pow_mul, hk, mul_comm k p]

end Powers

section Preimage

variable {K : Type} [Field K] {n : ℕ}

abbrev pglMk (n : ℕ) (K : Type) [Field K] : GL (Fin n) K →* PGL n K :=
  QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))

theorem pglMk_eq_one_iff {A : GL (Fin n) K} :
    pglMk n K A = 1 ↔ ∃ c : Kˣ, A = GeneralLinearGroup.scalar (Fin n) c :=
  (QuotientGroup.eq_one_iff A).trans mem_center_iff

theorem center_le_comap_pglMk (E : Subgroup (PGL n K)) :
    Subgroup.center (GL (Fin n) K) ≤ E.comap (pglMk n K) := by
  intro A hA
  rw [Subgroup.mem_comap, show pglMk n K A = 1 from (QuotientGroup.eq_one_iff A).2 hA]
  exact E.one_mem

theorem exists_pow_eq_scalar {p : ℕ} {E : Subgroup (PGL n K)} (hE : IsElemAbelian p E)
    {x : GL (Fin n) K} (hx : x ∈ E.comap (pglMk n K)) :
    ∃ c : Kˣ, x ^ p = GeneralLinearGroup.scalar (Fin n) c :=
  pglMk_eq_one_iff.1 (by rw [map_pow]; exact hE.2 _ hx)

theorem exists_conj_eq_scalar {p : ℕ} {E : Subgroup (PGL n K)} (hE : IsElemAbelian p E)
    {x y : GL (Fin n) K} (hx : x ∈ E.comap (pglMk n K)) (hy : y ∈ E.comap (pglMk n K)) :
    ∃ z : Kˣ, y * x * y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * x := by
  have hc : pglMk n K y * pglMk n K x = pglMk n K x * pglMk n K y := by
    have := hE.1.is_comm.comm (⟨_, hy⟩ : E) ⟨_, hx⟩
    exact congrArg Subtype.val this
  obtain ⟨z, hz⟩ := pglMk_eq_one_iff.1 (show pglMk n K (y * x * y⁻¹ * x⁻¹) = 1 by
    simp only [map_mul, map_inv]
    rw [hc]
    group)
  exact ⟨z, by rw [← hz]; group⟩

end Preimage

section Heisenberg

variable {K : Type} [Field K] {n : ℕ}

open CFSG.LinearAlgebra in
theorem exists_heisenberg_pair [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card Kˣ) (hn : 0 < n) {E : Subgroup (PGL n K)} (hE : IsElemAbelian p E)
    {x y : GL (Fin n) K} (hx : x ∈ E.comap (pglMk n K)) (hy : y ∈ E.comap (pglMk n K))
    (hxy : x * y ≠ y * x) :
    ∃ X ∈ E.comap (pglMk n K), ∃ Y ∈ E.comap (pglMk n K), ∃ z : Kˣ, X ^ p = 1 ∧
      IsPrimitiveRoot (z : K) p ∧ Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := center_le_comap_pglMk (K := K) (n := n) E
  have hsc : ∀ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c ∈ E.comap (pglMk n K) := fun c =>
    hZ (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩)
  obtain ⟨z, hz⟩ := exists_conj_eq_scalar hE hx hy
  obtain ⟨b, hb⟩ := exists_pow_eq_scalar hE hx
  obtain ⟨a, ha⟩ := exists_pow_eq_scalar hE hy
  have hzp : z ^ p = 1 := scalar_pow_eq_one_of_conj_eq_scalar hz hb hn
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hxy
    rw [map_one, one_mul] at hz
    calc x * y = y * x * y⁻¹ * y := by rw [hz]
      _ = y * x := by group
  have hzprim : IsPrimitiveRoot (z : K) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hzp hz1))
  by_cases hbp : ∃ d : Kˣ, b = d ^ p
  ·
    obtain ⟨d, rfl⟩ := hbp
    refine ⟨GeneralLinearGroup.scalar (Fin n) d⁻¹ * x, mul_mem (hsc _) hx, y, hy, z, ?_, hzprim,
      ?_⟩
    · rw [((commute_iff_eq _ _).mpr (GeneralLinearGroup.scalar_commute d⁻¹ x)).mul_pow, hb,
        ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
    · rw [conj_scalar_mul_conj, hz, ← mul_assoc, ← mul_assoc,
        GeneralLinearGroup.scalar_commute d⁻¹ (GeneralLinearGroup.scalar (Fin n) z)]
  · by_cases hap : ∃ e : Kˣ, a = e ^ p
    ·
      obtain ⟨e, rfl⟩ := hap
      have hz' := conj_eq_scalar_inv hz
      refine ⟨GeneralLinearGroup.scalar (Fin n) e⁻¹ * y, mul_mem (hsc _) hy, x, hx, z⁻¹, ?_,
        ?_, ?_⟩
      · rw [((commute_iff_eq _ _).mpr (GeneralLinearGroup.scalar_commute e⁻¹ y)).mul_pow, ha,
          ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
      · rw [Units.val_inv_eq_inv_val]
        exact hzprim.inv
      · rw [conj_scalar_mul_conj, hz', ← mul_assoc, ← mul_assoc,
          GeneralLinearGroup.scalar_commute e⁻¹ (GeneralLinearGroup.scalar (Fin n) z⁻¹)]
    ·
      obtain ⟨i, μ, hμ⟩ := exists_pow_mul_eq_pow hp hpK a b⁻¹ (fun ⟨e, he⟩ => hap ⟨e, he⟩)
      have hb' : b = a ^ (i : ℤ) * μ⁻¹ ^ p := by
        rw [zpow_natCast, inv_pow, ← hμ, _root_.mul_inv_rev, inv_inv, mul_comm b,
          mul_inv_cancel_left]
      refine ⟨GeneralLinearGroup.scalar (Fin n) μ⁻¹⁻¹ * x * y ^ (-(i : ℤ)),
        mul_mem (mul_mem (hsc _) hx) (zpow_mem hy _), y, hy, z,
        scalar_inv_mul_mul_zpow_neg_pow_eq_one hp hp2 hz hzp hb ha hb', hzprim, ?_⟩
      have hyy : y * y ^ (-(i : ℤ)) * y⁻¹ = y ^ (-(i : ℤ)) := by group
      calc y * (GeneralLinearGroup.scalar (Fin n) μ⁻¹⁻¹ * x * y ^ (-(i : ℤ))) * y⁻¹
          = GeneralLinearGroup.scalar (Fin n) μ⁻¹⁻¹ * ((y * x * y⁻¹) *
              (y * y ^ (-(i : ℤ)) * y⁻¹)) := by
            rw [show GeneralLinearGroup.scalar (Fin n) μ⁻¹⁻¹ * x * y ^ (-(i : ℤ)) =
              GeneralLinearGroup.scalar (Fin n) μ⁻¹⁻¹ * (x * y ^ (-(i : ℤ))) from mul_assoc _ _ _,
              conj_scalar_mul_conj]
            group
        _ = GeneralLinearGroup.scalar (Fin n) z *
              (GeneralLinearGroup.scalar (Fin n) μ⁻¹⁻¹ * x * y ^ (-(i : ℤ))) := by
            rw [hz, hyy, ← mul_assoc, ← mul_assoc, ← mul_assoc,
              GeneralLinearGroup.scalar_commute μ⁻¹⁻¹ (GeneralLinearGroup.scalar (Fin n) z)]
            simp only [mul_assoc]

end Heisenberg

section Commutant

variable {K : Type} [Field K] {n : ℕ}

open CFSG.LinearAlgebra

theorem mulVec_eq_smul_of_eigenspace_one {p : ℕ} (hp : p.Prime) {X Y u : GL (Fin n) K}
    {z : Kˣ} (hz : IsPrimitiveRoot (z : K) p) (hX : X ^ p = 1)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) (huY : u * Y = Y * u)
    {c : K} (hc : ∀ v ∈ Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1,
      (u : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) (v : Fin n → K) :
    (u : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)
      (Matrix.GeneralLinearGroup.toLin X) with hg
  have hgL : g.toLinearMap = Matrix.toLin' (X : Matrix (Fin n) (Fin n) K) := by
    rw [hg, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply']
  have hgp : g ^ p = 1 := by
    rw [hg, ← map_pow, ← map_pow, hX]
    simp
  have hdir : DirectSum.IsInternal (fun i : Fin p =>
      Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K))
        ((z : K) ^ (i : ℤ))) := by
    have h := CFSG.proposition_2_4_a (g := g) hgp hp.two_le (ε := (z : K)) hz
    simpa only [hgL] using h
  set L : Submodule K (Fin n → K) :=
    LinearMap.ker (Matrix.toLin' (u : Matrix (Fin n) (Fin n) K) - c • LinearMap.id) with hL
  have hmemL : ∀ w, w ∈ L ↔ (u : Matrix (Fin n) (Fin n) K) *ᵥ w = c • w := fun w => by
    rw [hL, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hle : ∀ i : Fin p, Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K))
      ((z : K) ^ (i : ℤ)) ≤ L := by
    intro i
    have hk : (((z ^ (p - i.val) : Kˣ) : K))⁻¹ * 1 = (z : K) ^ (i : ℤ) := by
      rw [mul_one, zpow_natCast, Units.val_pow_eq_pow_val]
      have h1 : (z : K) ^ i.val * (z : K) ^ (p - i.val) = 1 := by
        rw [← pow_add, Nat.add_sub_cancel' i.isLt.le, hz.pow_eq_one]
      exact (eq_inv_of_mul_eq_one_left h1).symm
    rw [← hk, ← map_eigenspace_eq (pow_conj_eq_scalar hXY (p - i.val)) 1]
    rintro _ ⟨w, hw, rfl⟩
    rw [hmemL, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    have hcomm : (u : Matrix (Fin n) (Fin n) K) *
        ((Y ^ (p - i.val) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((Y ^ (p - i.val) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (u : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, ((show Commute u Y from huY).pow_right _).eq]
    rw [hcomm, ← Matrix.mulVec_mulVec, hc w hw, Matrix.mulVec_smul]
  have htop : (⊤ : Submodule K (Fin n → K)) ≤ L := hdir.submodule_iSup_eq_top ▸ iSup_le hle
  exact (hmemL v).1 (htop Submodule.mem_top)

theorem eq_scalar_of_mulVec_eq_smul {u : GL (Fin n) K} {c : Kˣ}
    (h : ∀ v, (u : Matrix (Fin n) (Fin n) K) *ᵥ v = (c : K) • v) :
    u = GeneralLinearGroup.scalar (Fin n) c := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

@[expose] noncomputable def restrictGL {U : Subgroup (GL (Fin n) K)}
    {W : Submodule K (Fin n → K)}
    (hU : ∀ u ∈ U, ∀ w ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) {m : ℕ}
    (b : Module.Basis (Fin m) K W) : ↥U →* GL (Fin m) K :=
  MonoidHom.toHomUnits
    { toFun := fun u => LinearMap.toMatrix b b
        ((Matrix.toLin' ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).restrict
          fun w hw => by rw [Matrix.toLin'_apply]; exact hU u u.2 w hw)
      map_one' := by
        rw [← LinearMap.toMatrix_id b]
        congr 1
        refine LinearMap.ext fun w => Subtype.ext ?_
        simp
      map_mul' := fun u v => by
        rw [← LinearMap.toMatrix_mul]
        congr 1
        refine LinearMap.ext fun w => Subtype.ext ?_
        simp [Matrix.mulVec_mulVec] }

theorem restrictGL_eq_scalar_iff {U : Subgroup (GL (Fin n) K)} {W : Submodule K (Fin n → K)}
    (hU : ∀ u ∈ U, ∀ w ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) {m : ℕ}
    (b : Module.Basis (Fin m) K W) (u : ↥U) (c : Kˣ) :
    restrictGL hU b u = GeneralLinearGroup.scalar (Fin m) c ↔
      ∀ w ∈ W, ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = (c : K) • w := by
  have hsc : ((GeneralLinearGroup.scalar (Fin m) c : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      LinearMap.toMatrix b b ((c : K) • LinearMap.id) := by
    rw [map_smul, LinearMap.toMatrix_id, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [← Units.val_inj, hsc]
  change LinearMap.toMatrix b b _ = _ ↔ _
  rw [(LinearMap.toMatrix b b).injective.eq_iff, LinearMap.ext_iff]
  constructor
  · intro h w hw
    have := congrArg Subtype.val (h ⟨w, hw⟩)
    simpa [Matrix.toLin'_apply] using this
  · intro h w
    apply Subtype.ext
    simpa [Matrix.toLin'_apply] using h w w.2

end Commutant

section HeisenbergBound

variable {K : Type} [Field K] {n : ℕ}

open CFSG.LinearAlgebra
open scoped commutatorElement

private theorem isElemAbelian_mono {G : Type*} [Group G] {p : ℕ} {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hFE : F ≤ E) : IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (by
      have := hE.1.is_comm.comm (⟨a, hFE a.2⟩ : E) ⟨b, hFE b.2⟩
      exact congrArg (fun x : E => (x : G)) this)⟩⟩, fun x hx => hE.2 x (hFE hx)⟩

theorem card_eq_card_map_mul_card_center [Finite K] {S : Subgroup (GL (Fin n) K)}
    (hS : Subgroup.center (GL (Fin n) K) ≤ S) :
    Nat.card S = Nat.card (S.map (pglMk n K)) * Nat.card (Subgroup.center (GL (Fin n) K)) := by
  have h := Subgroup.card_ker_mul_card_range ((pglMk n K).comp S.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hker : ((pglMk n K).comp S.subtype).ker =
      (Subgroup.center (GL (Fin n) K)).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv] at h
  rw [← h, mul_comm]

theorem commutatorElement_mul_left_of_mem_center {G : Type*} [Group G] {u v V : G}
    (hc : ⁅v, V⁆ ∈ Subgroup.center G) : ⁅u * v, V⁆ = ⁅u, V⁆ * ⁅v, V⁆ := by
  have hc' := Subgroup.mem_center_iff.1 hc
  have e1 : ⁅u * v, V⁆ = u * ⁅v, V⁆ * (V * u⁻¹ * V⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1, hc' u, hc' ⁅u, V⁆]
  simp only [commutatorElement_def]
  group

theorem card_le_of_heisenberg [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card Kˣ) (hn : 0 < n) {E : Subgroup (PGL n K)} (hE : IsElemAbelian p E)
    {X Y : GL (Fin n) K} (hXE : X ∈ E.comap (pglMk n K)) (hYE : Y ∈ E.comap (pglMk n K))
    {z : Kˣ} (hXp : X ^ p = 1) (hz : IsPrimitiveRoot (z : K) p)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X) :
    n = p * Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1) ∧
      Nat.card E ≤ p ^ (Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1) + 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set W := Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1 with hW
  set m := Module.finrank K W with hm
  have hnm : n = p * m := card_eq_mul_finrank_eigenspace_one hp hz hXp hXY
  refine ⟨hnm, ?_⟩
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hnm
      omega
    · exact h0
  set Q := E.comap (pglMk n K) with hQ
  have hZQ : Subgroup.center (GL (Fin n) K) ≤ Q := center_le_comap_pglMk E
  set U : Subgroup (GL (Fin n) K) :=
    Q ⊓ Subgroup.centralizer {X} ⊓ Subgroup.centralizer {Y} with hU
  have hmemU : ∀ u, u ∈ U ↔ u ∈ Q ∧ u * X = X * u ∧ u * Y = Y * u := by
    intro u
    simp only [hU, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    tauto
  have hZU : Subgroup.center (GL (Fin n) K) ≤ U := by
    intro c hc
    exact (hmemU c).2 ⟨hZQ hc, (Subgroup.mem_center_iff.1 hc X).symm,
      (Subgroup.mem_center_iff.1 hc Y).symm⟩
  have hUW : ∀ u ∈ U, ∀ w ∈ W, (u : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro u hu w hw
    have hXu := ((hmemU u).1 hu).2.1
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← hXu, Units.val_mul, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_smul]
  let b : Module.Basis (Fin m) K W := Module.finBasisOfFinrankEq K W hm.symm
  set r := restrictGL hUW b with hr
  have hscal : ∀ (u : ↥U) (c : Kˣ), r u = GeneralLinearGroup.scalar (Fin m) c ↔
      (u : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
    intro u c
    rw [hr, restrictGL_eq_scalar_iff]
    constructor
    · intro h
      exact eq_scalar_of_mulVec_eq_smul
        (mulVec_eq_smul_of_eigenspace_one hp hz hXp hXY ((hmemU _).1 u.2).2.2 h)
    · intro h w _
      rw [h, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      funext i
      rw [Matrix.mulVec_diagonal]
      rfl
  have hrinj : Function.Injective r := by
    intro u v huv
    have h1 : r (u⁻¹ * v) = GeneralLinearGroup.scalar (Fin m) 1 := by
      rw [map_mul, map_inv, huv, inv_mul_cancel, map_one]
    have h2 := (hscal _ 1).1 h1
    rw [map_one] at h2
    have h3 : u⁻¹ * v = 1 := Subtype.ext h2
    exact inv_mul_eq_one.1 h3
  set e := MonoidHom.ofInjective hrinj with he
  set ρ : ↥r.range →* PGL n K := ((pglMk n K).comp U.subtype).comp e.symm.toMonoidHom with hρ
  have hρapp : ∀ u : ↥U, ρ (e u) = pglMk n K u := fun u => by
    simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
  have hker : ∀ A : ↥r.range,
      ρ A = 1 ↔ (A : GL (Fin m) K) ∈ Subgroup.center (GL (Fin m) K) := by
    intro A
    obtain ⟨u, rfl⟩ := e.surjective A
    rw [hρapp, pglMk_eq_one_iff, mem_center_iff]
    have he' : ((e u : ↥r.range) : GL (Fin m) K) = r u := MonoidHom.ofInjective_apply hrinj
    rw [he']
    exact ⟨fun ⟨c, hc⟩ => ⟨c, (hscal u c).2 hc⟩, fun ⟨c, hc⟩ => ⟨c, (hscal u c).1 hc⟩⟩
  set E₂ := U.map (pglMk n K) with hE₂
  have hE₂E : E₂ ≤ E := by
    rintro _ ⟨u, hu, rfl⟩
    exact ((hmemU u).1 hu).1
  have hE₂el : IsElemAbelian p E₂ := isElemAbelian_mono hE hE₂E
  have hE₂ρ : E₂ ≤ ρ.range := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨e ⟨u, hu⟩, hρapp ⟨u, hu⟩⟩
  have hcardE₂ : Nat.card E₂ ≤ p ^ (m - 1) :=
    card_le_of_scalar_kernel hp hp2 hpK hm0 r.range ρ hker E₂ hE₂ρ hE₂el
  set T : Subgroup (GL (Fin n) K) :=
    (rootsOfUnity p K).map (GeneralLinearGroup.scalar (Fin n)) with hT
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hTcard : Nat.card T ≤ p := by
    rw [hT, Subgroup.card_map_of_injective
      (fun a b h => generalLinearGroup_scalar_injective h)]
    exact card_rootsOfUnity K p
  have hTZ : T ≤ Subgroup.center (GL (Fin n) K) := by
    rintro _ ⟨ζ, -, rfl⟩
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨ζ, rfl⟩
  have hcomT : ∀ u ∈ Q, ∀ V ∈ Q, ⁅u, V⁆ ∈ T := by
    intro u hu V hV
    obtain ⟨ζ, hζ⟩ := exists_conj_eq_scalar hE hV hu
    obtain ⟨a, ha⟩ := exists_pow_eq_scalar hE hV
    have hζp : ζ ^ p = 1 := scalar_pow_eq_one_of_conj_eq_scalar hζ ha hn
    refine ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp, ?_⟩
    rw [commutatorElement_def, hζ]
    group
  let κ : ↥Q →* ↥T × ↥T :=
    { toFun := fun u => (⟨⁅(u : GL (Fin n) K), X⁆, hcomT u u.2 X hXE⟩,
        ⟨⁅(u : GL (Fin n) K), Y⁆, hcomT u u.2 Y hYE⟩)
      map_one' := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp
      map_mul' := fun u v => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · exact commutatorElement_mul_left_of_mem_center (hTZ (hcomT v v.2 X hXE))
        · exact commutatorElement_mul_left_of_mem_center (hTZ (hcomT v v.2 Y hYE)) }
  have hκker : κ.ker = U.subgroupOf Q := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmemU]
    change ((⟨⁅(u : GL (Fin n) K), X⁆, _⟩, ⟨⁅(u : GL (Fin n) K), Y⁆, _⟩) : ↥T × ↥T) = 1 ↔ _
    rw [Prod.ext_iff, Subtype.ext_iff, Subtype.ext_iff]
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one,
      commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => ⟨u.2, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  have hUQ : U ≤ Q := fun u hu => ((hmemU u).1 hu).1
  have hQcard : Nat.card Q ≤ Nat.card U * p ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range κ
    rw [hκker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv] at h1
    have h2 : Nat.card κ.range ≤ p ^ 2 := by
      calc Nat.card κ.range ≤ Nat.card (↥T × ↥T) := Subgroup.card_le_card_group _
        _ = Nat.card T * Nat.card T := Nat.card_prod _ _
        _ ≤ p * p := Nat.mul_le_mul hTcard hTcard
        _ = p ^ 2 := (sq p).symm
    rw [← h1]
    exact Nat.mul_le_mul_left _ h2
  have hQE : Q.map (pglMk n K) = E :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) E
  have hcQ := card_eq_card_map_mul_card_center hZQ
  have hcU := card_eq_card_map_mul_card_center hZU
  rw [hQE] at hcQ
  have hZpos : 0 < Nat.card (Subgroup.center (GL (Fin n) K)) := Nat.card_pos
  have hEle : Nat.card E ≤ Nat.card E₂ * p ^ 2 := by
    have h3 : Nat.card E * Nat.card (Subgroup.center (GL (Fin n) K)) ≤
        Nat.card E₂ * p ^ 2 * Nat.card (Subgroup.center (GL (Fin n) K)) := by
      rw [← hcQ]
      calc Nat.card Q ≤ Nat.card U * p ^ 2 := hQcard
        _ = Nat.card E₂ * p ^ 2 * Nat.card (Subgroup.center (GL (Fin n) K)) := by
          rw [hcU]
          ring
    exact Nat.le_of_mul_le_mul_right h3 hZpos
  calc Nat.card E ≤ Nat.card E₂ * p ^ 2 := hEle
    _ ≤ p ^ (m - 1) * p ^ 2 := Nat.mul_le_mul_right _ hcardE₂
    _ = p ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      omega

end HeisenbergBound

section Weights

variable {K : Type} [Field K] {n : ℕ}

open scoped IsMulCommutative

@[expose] noncomputable def tautRep (A : Subgroup (GL (Fin n) K)) :
    ↥A →* Module.End K (Fin n → K) where
  toFun a := Matrix.toLin' ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  map_one' := by
    rw [OneMemClass.coe_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' a b := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

theorem tautRep_apply (A : Subgroup (GL (Fin n) K)) (a : ↥A) (v : Fin n → K) :
    tautRep A a v = ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v :=
  Matrix.toLin'_apply _ _

noncomputable abbrev wtSpace (A : Subgroup (GL (Fin n) K)) (χ : ↥A →* Kˣ) :
    Submodule K (Fin n → K) :=
  ⨅ a : ↥A, (tautRep A a).eigenspace (χ a : K)

theorem mem_wtSpace_iff {A : Subgroup (GL (Fin n) K)} {χ : ↥A →* Kˣ} {v : Fin n → K} :
    v ∈ wtSpace A χ ↔ ∀ a : ↥A, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (χ a : K) • v := by
  simp only [wtSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, tautRep_apply]

theorem natCast_ne_zero_of_dvd_card_units [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card Kˣ) : (p : K) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hprim : IsPrimitiveRoot (ζ : K) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  exact (hprim.neZero').out

open Classical in
theorem isInternal_wtSpace [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ)
    {A : Subgroup (GL (Fin n) K)} (hA : IsElemAbelian p A) :
    DirectSum.IsInternal (fun χ : ↥A →* Kˣ => wtSpace A χ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥A := hA.1
  haveI : Finite ↥A := inferInstance
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hprim : IsPrimitiveRoot (ζ : K) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  haveI : HasEnoughRootsOfUnity K p := ⟨⟨_, hprim⟩, inferInstance⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hexp : Monoid.exponent ↥A ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (hA.2 a a.2)
  haveI : HasEnoughRootsOfUnity K (Monoid.exponent ↥A) := HasEnoughRootsOfUnity.of_dvd K hexp
  have hpg : IsPGroup p ↥A := fun a => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.2 a a.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  have hunit : IsUnit (Nat.card ↥A : K) := by
    rw [hk, Nat.cast_pow]
    exact (IsUnit.mk0 _ (natCast_ne_zero_of_dvd_card_units hp hpK)).pow k
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (TauCeti.iSupIndep_iInf_eigenspace_unitHom (ρ := tautRep A))
    (TauCeti.iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup (ρ := tautRep A) hunit)

theorem card_le_pow_card_wtSpace [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ)
    {A : Subgroup (GL (Fin n) K)} (hA : IsElemAbelian p A) :
    Nat.card ↥A ≤ p ^ Nat.card {χ : ↥A →* Kˣ // wtSpace A χ ≠ ⊥} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hint := isInternal_wtSpace hp hpK hA
  set X := {χ : ↥A →* Kˣ // wtSpace A χ ≠ ⊥}
  have hroot : ∀ (χ : ↥A →* Kˣ) (a : ↥A), χ a ∈ rootsOfUnity p K := fun χ a => by
    rw [mem_rootsOfUnity, ← map_pow, show a ^ p = 1 from Subtype.ext (hA.2 a a.2), map_one]
  let F : ↥A → X → ↥(rootsOfUnity p K) := fun a χ => ⟨χ.1 a, hroot χ.1 a⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hall : ∀ χ : ↥A →* Kˣ, ∀ v ∈ wtSpace A χ,
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
          ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := by
      intro χ v hv
      by_cases hχ : wtSpace A χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hv
        rw [hv, Matrix.mulVec_zero, Matrix.mulVec_zero]
      · have h1 := congrArg (fun f => ((f ⟨χ, hχ⟩ : ↥(rootsOfUnity p K)) : Kˣ)) hab
        simp only [F] at h1
        rw [mem_wtSpace_iff.1 hv a, mem_wtSpace_iff.1 hv b, h1]
    set L : Submodule K (Fin n → K) := LinearMap.ker (tautRep A a - tautRep A b) with hL
    have hle : ∀ χ, wtSpace A χ ≤ L := fun χ v hv => by
      rw [hL, LinearMap.mem_ker, LinearMap.sub_apply, tautRep_apply, tautRep_apply, sub_eq_zero]
      exact hall χ v hv
    have htop : (⊤ : Submodule K (Fin n → K)) ≤ L := hint.submodule_iSup_eq_top ▸ iSup_le hle
    have heq : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      have hv := htop (Submodule.mem_top (x := v))
      rw [hL, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
      exact hv
    exact Subtype.ext (Units.ext heq)
  calc Nat.card ↥A ≤ Nat.card (X → ↥(rootsOfUnity p K)) := Nat.card_le_card_of_injective F hF
    _ = Nat.card ↥(rootsOfUnity p K) ^ Nat.card X := Nat.card_fun
    _ ≤ p ^ Nat.card X := Nat.pow_le_pow_left (card_rootsOfUnity K p) _

theorem dvd_finrank_of_pow_eq_scalar {p : ℕ} (hp : p.Prime) {W : Submodule K (Fin n → K)}
    {x : GL (Fin n) K} (hxW : ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) {c : Kˣ}
    (hxp : x ^ p = GeneralLinearGroup.scalar (Fin n) c) (hc : ¬ ∃ μ : Kˣ, c = μ ^ p) :
    p ∣ Module.finrank K W := by
  by_contra hd
  set f : W →ₗ[K] W := (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)).restrict
    (fun w hw => by rw [Matrix.toLin'_apply]; exact hxW w hw) with hf
  have hfp : f ^ p = (c : K) • (1 : Module.End K W) := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    have h1 : ∀ k : ℕ, (((f ^ k) w : W) : Fin n → K) =
        ((x ^ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, hf, LinearMap.coe_restrict_apply, ← hf, ih,
          Matrix.toLin'_apply, Matrix.mulVec_mulVec, pow_succ', Units.val_mul]
    rw [h1, hxp, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  have hdet : (LinearMap.det f) ^ p = (c : K) ^ Module.finrank K W := by
    rw [← map_pow, hfp, LinearMap.det_smul, map_one, mul_one]
  have hne : LinearMap.det f ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hdet
    exact (pow_ne_zero _ c.ne_zero) hdet.symm
  have hu : c ^ Module.finrank K W = (Units.mk0 _ hne) ^ p := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, hdet]
  exact hc (exists_eq_pow_of_pow_eq hp hd hu)

end Weights

section Abelian

variable {K : Type} [Field K] {n : ℕ}

open scoped IsMulCommutative

@[expose] def omegaOne (Q : Subgroup (GL (Fin n) K)) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (p : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {u | u ∈ Q ∧ u ^ p = 1}
  one_mem' := ⟨Q.one_mem, one_pow p⟩
  mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
    rw [Commute.mul_pow (hQ a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem isElemAbelian_omegaOne (Q : Subgroup (GL (Fin n) K))
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (p : ℕ) : IsElemAbelian p (omegaOne Q hQ p) :=
  ⟨⟨⟨fun a b => Subtype.ext (hQ a a.2.1 b b.2.1)⟩⟩, fun _ hu => hu.2⟩

theorem mul_card_map_le_card_omegaOne [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ)
    (hn : 0 < n) {Q : Subgroup (GL (Fin n) K)} (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hZQ : Subgroup.center (GL (Fin n) K) ≤ Q) :
    p * Nat.card ((omegaOne Q hQ p).map (pglMk n K)) ≤ Nat.card (omegaOne Q hQ p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Ω := omegaOne Q hQ p
  have h := Subgroup.card_ker_mul_card_range ((pglMk n K).comp Ω.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  rw [← h]
  refine Nat.mul_le_mul_right _ ?_
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hprim : IsPrimitiveRoot (ζ : K) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  set T : Subgroup (GL (Fin n) K) :=
    (rootsOfUnity p K).map (GeneralLinearGroup.scalar (Fin n)) with hT
  have hTcard : Nat.card T = p := by
    rw [hT, Subgroup.card_map_of_injective
      (fun a b h => CFSG.LinearAlgebra.generalLinearGroup_scalar_injective h)]
    exact hprim.card_rootsOfUnity
  have hTΩ : T ≤ Ω := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨hZQ ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    · rw [← map_pow, (mem_rootsOfUnity p c).1 hc, map_one]
  have hTker : T.subgroupOf Ω ≤ ((pglMk n K).comp Ω.subtype).ker := by
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    obtain ⟨c, -, hc⟩ := Subgroup.mem_subgroupOf.1 ht
    rw [← hc]
    exact pglMk_eq_one_iff.2 ⟨c, rfl⟩
  calc p = Nat.card T := hTcard.symm
    _ = Nat.card (T.subgroupOf Ω) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΩ).toEquiv).symm
    _ ≤ Nat.card ((pglMk n K).comp Ω.subtype).ker := Subgroup.card_le_of_le hTker

theorem card_le_of_not_pow [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ)
    (hn : 0 < n) {E : Subgroup (PGL n K)} (hE : IsElemAbelian p E)
    (hcomm : ∀ x ∈ E.comap (pglMk n K), ∀ y ∈ E.comap (pglMk n K), x * y = y * x)
    {x : GL (Fin n) K} (hx : x ∈ E.comap (pglMk n K)) {c : Kˣ}
    (hxc : x ^ p = GeneralLinearGroup.scalar (Fin n) c) (hc : ¬ ∃ μ : Kˣ, c = μ ^ p) :
    ∃ w : ℕ, p * w ≤ n ∧ Nat.card E ≤ p ^ w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Q := E.comap (pglMk n K) with hQ
  have hZQ : Subgroup.center (GL (Fin n) K) ≤ Q := center_le_comap_pglMk E
  set Ω := omegaOne Q hcomm p with hΩdef
  have hΩ : IsElemAbelian p Ω := isElemAbelian_omegaOne Q hcomm p
  have hsc : ∀ d : Kˣ, GeneralLinearGroup.scalar (Fin n) d ∈ Q := fun d => hZQ (by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨d, rfl⟩)
  haveI : Fintype (↥Ω →* Kˣ) := Fintype.ofFinite _
  refine ⟨Nat.card {χ : ↥Ω →* Kˣ // wtSpace Ω χ ≠ ⊥}, ?_, ?_⟩
  ·
    have hint := isInternal_wtSpace hp hpK hΩ
    have hsum := TauCeti.finrank_eq_sum_finrank_of_isInternal hint
    rw [Module.finrank_fin_fun] at hsum
    have hdvd : ∀ χ : ↥Ω →* Kˣ, p ∣ Module.finrank K (wtSpace Ω χ) := by
      intro χ
      refine dvd_finrank_of_pow_eq_scalar hp (fun v hv => ?_) hxc hc
      rw [mem_wtSpace_iff] at hv ⊢
      intro a
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← hcomm x hx a a.2.1, Units.val_mul,
        ← Matrix.mulVec_mulVec, hv a, Matrix.mulVec_smul]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    calc p * (Finset.univ.filter fun χ : ↥Ω →* Kˣ => wtSpace Ω χ ≠ ⊥).card
        = ∑ _χ ∈ Finset.univ.filter (fun χ : ↥Ω →* Kˣ => wtSpace Ω χ ≠ ⊥), p := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ χ ∈ Finset.univ.filter (fun χ : ↥Ω →* Kˣ => wtSpace Ω χ ≠ ⊥),
            Module.finrank K (wtSpace Ω χ) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          have hne : wtSpace Ω χ ≠ ⊥ := (Finset.mem_filter.1 hχ).2
          have hpos : 0 < Module.finrank K (wtSpace Ω χ) :=
            Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.1 h0)
          exact Nat.le_of_dvd hpos (hdvd χ)
      _ ≤ ∑ χ : ↥Ω →* Kˣ, Module.finrank K (wtSpace Ω χ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
      _ = n := hsum.symm
  · refine le_trans ?_ (card_le_pow_card_wtSpace hp hpK hΩ)
    have hdec : ∀ e ∈ E, ∃ i : ℤ, ∃ u ∈ Ω, e = pglMk n K x ^ i * pglMk n K u := by
      intro e he
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (GL (Fin n) K)) e
      have hy : y ∈ Q := he
      obtain ⟨a, ha⟩ := exists_pow_eq_scalar hE hy
      obtain ⟨i, μ, hμ⟩ := exists_pow_mul_eq_pow hp hpK c a hc
      have hxy : Commute (x ^ i) y := (show Commute x y from hcomm x hx y hy).pow_left i
      refine ⟨-(i : ℤ), GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (x ^ i * y),
        ⟨mul_mem (hsc _) (mul_mem (pow_mem hx i) hy), ?_⟩, ?_⟩
      · rw [((commute_iff_eq _ _).mpr (GeneralLinearGroup.scalar_commute μ⁻¹ (x ^ i * y))).mul_pow,
          hxy.mul_pow, ← pow_mul, mul_comm i p, pow_mul, hxc, ha, ← map_pow, ← map_pow,
          ← map_mul, ← map_mul, inv_pow, ← hμ, inv_mul_cancel, map_one]
      · rw [map_mul, map_mul, pglMk_eq_one_iff.2 ⟨μ⁻¹, rfl⟩, one_mul, map_pow, ← mul_assoc,
          ← zpow_natCast, ← _root_.zpow_add, neg_add_cancel, zpow_zero, one_mul]
    set M := (omegaOne Q hcomm p).map (pglMk n K)
    have hxE : pglMk n K x ∈ E := hx
    have hzE : Subgroup.zpowers (pglMk n K x) ≤ E := Subgroup.zpowers_le.2 hxE
    have hME : M ≤ E := by
      rintro _ ⟨u, hu, rfl⟩
      exact hu.1
    let ψ : ↥(Subgroup.zpowers (pglMk n K x)) × ↥M →* ↥E :=
      (Subgroup.inclusion hzE).noncommCoprod (Subgroup.inclusion hME)
        (fun a b => hE.1.is_comm.comm _ _)
    have hψ : Function.Surjective ψ := by
      rintro ⟨e, he⟩
      obtain ⟨i, u, hu, rfl⟩ := hdec e he
      refine ⟨(⟨_, Subgroup.zpow_mem_zpowers _ i⟩, ⟨pglMk n K u, u, hu, rfl⟩), ?_⟩
      rfl
    have hzc : Nat.card (Subgroup.zpowers (pglMk n K x)) ≤ p := by
      rw [Nat.card_zpowers]
      refine Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one ?_)
      rw [← map_pow, hxc]
      exact pglMk_eq_one_iff.2 ⟨c, rfl⟩
    calc Nat.card ↥E ≤ Nat.card (↥(Subgroup.zpowers (pglMk n K x)) × ↥M) :=
          Nat.card_le_card_of_surjective ψ hψ
      _ = Nat.card (Subgroup.zpowers (pglMk n K x)) * Nat.card M := Nat.card_prod _ _
      _ ≤ p * Nat.card M := Nat.mul_le_mul_right _ hzc
      _ ≤ Nat.card Ω := mul_card_map_le_card_omegaOne hp hpK hn hcomm hZQ

theorem exists_lift_of_split [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ)
    (hn : 0 < n) {E : Subgroup (PGL n K)}
    (hcomm : ∀ x ∈ E.comap (pglMk n K), ∀ y ∈ E.comap (pglMk n K), x * y = y * x)
    (hsplit : ∀ y ∈ E.comap (pglMk n K), ∃ μ : Kˣ,
      y ^ p = GeneralLinearGroup.scalar (Fin n) (μ ^ p))
    {Y : Subgroup (GL (Fin n) K)} (hEY : E ≤ Y.map (pglMk n K))
    (hYμ : ∀ l : Kˣ, l ^ p = 1 → GeneralLinearGroup.scalar (Fin n) l ∈ Y)
    (hYroot : ∀ μ : Kˣ, GeneralLinearGroup.scalar (Fin n) (μ ^ p) ∈ Y →
      ∃ ν : Kˣ, GeneralLinearGroup.scalar (Fin n) ν ∈ Y ∧ ν ^ p = μ ^ p) :
    ∃ A : Subgroup (GL (Fin n) K), A ≤ Y ∧ IsElemAbelian p A ∧
      A ⊓ Subgroup.center (GL (Fin n) K) = ⊥ ∧ A.map (pglMk n K) = E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Q := E.comap (pglMk n K) with hQ
  have hZQ : Subgroup.center (GL (Fin n) K) ≤ Q := center_le_comap_pglMk E
  set Ω := omegaOne Q hcomm p ⊓ Y with hΩdef
  have hΩ : IsElemAbelian p Ω := isElemAbelian_mono (isElemAbelian_omegaOne Q hcomm p) inf_le_left
  have hsc : ∀ d : Kˣ, GeneralLinearGroup.scalar (Fin n) d ∈ Q := fun d => hZQ (by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨d, rfl⟩)
  have hint := isInternal_wtSpace hp hpK hΩ
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ : ↥Ω →* Kˣ, wtSpace Ω χ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have htop := hint.submodule_iSup_eq_top
    rw [show (⨆ χ : ↥Ω →* Kˣ, wtSpace Ω χ) = ⊥ from iSup_eq_bot.2 hall] at htop
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact bot_ne_top htop
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ₀
  have hχsc : ∀ (l : Kˣ) (hl : GeneralLinearGroup.scalar (Fin n) l ∈ Ω),
      χ₀ ⟨_, hl⟩ = l := by
    intro l hl
    have h1 := mem_wtSpace_iff.1 hw₀ ⟨_, hl⟩
    have h2 : ((GeneralLinearGroup.scalar (Fin n) l : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ w₀ = (l : K) • w₀ := by
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      funext i
      rw [Matrix.mulVec_diagonal]
      rfl
    have h3 : ((χ₀ ⟨_, hl⟩ : Kˣ) : K) = (l : K) :=
      smul_left_injective K hw₀0 (h1.symm.trans h2)
    exact Units.ext h3
  set A : Subgroup (GL (Fin n) K) := (χ₀.ker).map Ω.subtype with hA
  have hAΩ : A ≤ Ω := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  refine ⟨A, hAΩ.trans inf_le_right, isElemAbelian_mono hΩ hAΩ, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, hZ⟩
    obtain ⟨l, hl⟩ := mem_center_iff.1 hZ
    have hl0 : (a : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) l := hl
    have hl' : GeneralLinearGroup.scalar (Fin n) l ∈ Ω := hl0 ▸ a.2
    have h1 : χ₀ ⟨_, hl'⟩ = 1 := by
      have : (⟨_, hl'⟩ : ↥Ω) = a := Subtype.ext hl0.symm
      rw [this]
      exact ha
    rw [hχsc l hl'] at h1
    rw [Subgroup.mem_bot]
    change (a : GL (Fin n) K) = 1
    rw [hl0, h1, map_one]
  ·
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact (hAΩ hu).1.1
    · intro e he
      obtain ⟨y, hyY, rfl⟩ := hEY he
      have hy : y ∈ Q := he
      obtain ⟨μ, hμ⟩ := hsplit y hy
      obtain ⟨ν, hνY, hν⟩ := hYroot μ (hμ ▸ pow_mem hyY p)
      have hu : GeneralLinearGroup.scalar (Fin n) ν⁻¹ * y ∈ Ω := by
        refine ⟨⟨mul_mem (hsc _) hy, ?_⟩, Y.mul_mem (by rw [map_inv]; exact Y.inv_mem hνY) hyY⟩
        rw [((commute_iff_eq _ _).mpr (GeneralLinearGroup.scalar_commute ν⁻¹ y)).mul_pow, hμ,
          ← map_pow, ← map_mul, inv_pow, hν, inv_mul_cancel, map_one]
      set l := χ₀ ⟨_, hu⟩ with hl
      have hlp : l ^ p = 1 := by
        rw [hl, ← map_pow, show (⟨_, hu⟩ : ↥Ω) ^ p = 1 from Subtype.ext hu.1.2, map_one]
      have hl' : GeneralLinearGroup.scalar (Fin n) l⁻¹ ∈ Ω :=
        ⟨⟨hsc _, by rw [← map_pow, inv_pow, hlp, inv_one, map_one]⟩,
          hYμ _ (by rw [inv_pow, hlp, inv_one])⟩
      have hmem : (⟨_, hl'⟩ : ↥Ω) * ⟨_, hu⟩ ∈ χ₀.ker := by
        rw [MonoidHom.mem_ker, map_mul, hχsc _ hl', ← hl, inv_mul_cancel]
      refine ⟨_, ⟨_, hmem, rfl⟩, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, map_mul,
        pglMk_eq_one_iff.2 ⟨l⁻¹, rfl⟩, pglMk_eq_one_iff.2 ⟨ν⁻¹, rfl⟩, one_mul]

end Abelian

section Lift

variable {K : Type} [Field K] {n : ℕ}

theorem exists_elemAbelian_lift [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card Kˣ) (hn : 5 ≤ n) {E : Subgroup (PGL n K)} (hE : IsElemAbelian p E)
    (hcard : p ^ (n - 2) ≤ Nat.card E) {Y : Subgroup (GL (Fin n) K)}
    (hEY : E ≤ Y.map (pglMk n K))
    (hYμ : ∀ l : Kˣ, l ^ p = 1 → GeneralLinearGroup.scalar (Fin n) l ∈ Y)
    (hYroot : ∀ μ : Kˣ, GeneralLinearGroup.scalar (Fin n) (μ ^ p) ∈ Y →
      ∃ ν : Kˣ, GeneralLinearGroup.scalar (Fin n) ν ∈ Y ∧ ν ^ p = μ ^ p) :
    ∃ A : Subgroup (GL (Fin n) K), A ≤ Y ∧ IsElemAbelian p A ∧
      A ⊓ Subgroup.center (GL (Fin n) K) = ⊥ ∧ A.map (pglMk n K) = E := by
  have hn0 : 0 < n := by omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hle : ∀ w : ℕ, Nat.card E ≤ p ^ w → n - 2 ≤ w := fun w hw =>
    (Nat.pow_le_pow_iff_right hp.one_lt).1 (hcard.trans hw)
  by_cases hcomm : ∀ x ∈ E.comap (pglMk n K), ∀ y ∈ E.comap (pglMk n K), x * y = y * x
  · by_cases hsplit : ∀ y ∈ E.comap (pglMk n K), ∃ μ : Kˣ,
        y ^ p = GeneralLinearGroup.scalar (Fin n) (μ ^ p)
    · exact exists_lift_of_split hp hpK hn0 hcomm hsplit hEY hYμ hYroot
    · exfalso
      push Not at hsplit
      obtain ⟨y, hy, hny⟩ := hsplit
      obtain ⟨c, hc⟩ := exists_pow_eq_scalar hE hy
      have hc' : ¬ ∃ μ : Kˣ, c = μ ^ p := fun ⟨μ, hμ⟩ => hny μ (hμ ▸ hc)
      obtain ⟨w, hpw, hEw⟩ := card_le_of_not_pow hp hpK hn0 hE hcomm hy hc hc'
      have h1 := hle w hEw
      have h2 : 3 * w ≤ n := (Nat.mul_le_mul_right w hp3).trans hpw
      omega
  · exfalso
    push Not at hcomm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcomm
    obtain ⟨X, hX, Y, hY, z, hXp, hz, hXY⟩ := exists_heisenberg_pair hp hp2 hpK hn0 hE hx hy hxy
    obtain ⟨hnm, hEm⟩ := card_le_of_heisenberg hp hp2 hpK hn0 hE hX hY hXp hz hXY
    set m := Module.finrank K
      (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1)
    have h1 := hle (m + 1) hEm
    have h2 : 3 * m ≤ n := hnm ▸ Nat.mul_le_mul_right m hp3
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · omega
      ·
        omega
    · omega

end Lift

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
