module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3L
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.LinearDescent (higher_linear_prime_semilinear_field_descent)

@[expose] def OrdPConcl (r : ℕ) (Y : Type) [Group Y] (b : MulAut Y) : Prop :=
  (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
    b ∈ (MulAut.conj : Y →* MulAut Y).range

theorem OrdPConcl.of_mulEquiv {r : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    {b : MulAut Y} (h : OrdPConcl r Y' (MulAut.congr e b)) : OrdPConcl r Y b := by
  have hb : ∀ x : Y, MulAut.congr e b (e x) = e (b x) := fun x => by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rcases h with ⟨E', hE'0, hE'p, hE'i⟩ | ⟨y', hy'⟩
  · refine Or.inl ⟨E'.comap e.toMonoidHom, ?_, hE'p.comap_of_injective _ e.injective, ?_⟩
    · intro hbot
      apply hE'0
      rw [eq_bot_iff]
      intro y hy
      have hy' : e.symm y ∈ E'.comap e.toMonoidHom := by
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        exact hy
      rw [hbot, Subgroup.mem_bot] at hy'
      rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e y, hy', map_one]
    · intro x hx
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hx ⊢
      rw [← hb]
      exact hE'i _ hx
  · refine Or.inr ⟨e.symm y', ?_⟩
    ext x
    apply e.injective
    rw [← hb, ← hy', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

namespace OrdPL

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem mem_semilinear_of_odd {r f : ℕ} (hr : r.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n) [CharP K r]
    (hK : Nat.card K = r ^ f) (α : MulAut (projectiveSL n K)) {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1) : α ∈ semilinearAutGroup n K := by
  have hdesc := higher_linear_prime_semilinear_field_descent (n := n) (K := K) (ℓ := r)
    hr hf hn hK
  obtain ⟨-, -, -, -, -, -, hab, -⟩ := hdesc
  have htrans := standard_automorphism_transport (K := K) (n := n)
  obtain ⟨A, σ0, ε, hε, hαeq⟩ := (automorphism_generation (K := K) (n := n) hn).2 α
  have hx : conjAut n K A * fieldAut n K σ0 ∈ semilinearAutGroup n K :=
    mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ0)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hαeq
    rw [hαeq]
    exact hx
  · rw [pow_one] at hαeq
    set x := conjAut n K A * fieldAut n K σ0 with hxdef
    set δ := dualAut n K with hδdef
    have hδδ : δ * δ = 1 := htrans.2.2.2.1
    have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδδ
    have hcomm : δ * x * δ⁻¹ * x⁻¹ ∈ linearAutGroup n K := hab δ x
    have hsq : α * α ∈ semilinearAutGroup n K := by
      have h1 : α * α = x * ((δ * x * δ⁻¹ * x⁻¹) * x) := by
        rw [hαeq, hδinv]
        group
      rw [h1]
      exact mul_mem hx (mul_mem (linearAutGroup_le_semilinearAutGroup hcomm) hx)
    obtain ⟨k, hk⟩ := hm
    have h2 : α = (α * α) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = m + 1 by omega, pow_succ, hαm, one_mul]
    rw [h2]
    exact pow_mem hsq _

omit [Finite K] in
theorem conj_proj_eq_conjAut (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj (proj n K g) = conjAut n K (SpecialLinearGroup.toGL g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [MulAut.conj_apply, conjAut_proj, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

omit [Finite K] in
theorem conjAut_scalar (u : Kˣ) : conjAut n K (GeneralLinearGroup.scalar (Fin n) u) = 1 := by
  have hc : GeneralLinearGroup.scalar (Fin n) u ∈ Subgroup.center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  have hcomm := Subgroup.mem_center_iff.mp hc (SpecialLinearGroup.toGL g)
  rw [coe_slConjugation, ← SpecialLinearGroup.coe_GL_coe_matrix g, ← Units.val_mul,
    ← Units.val_mul, ← hcomm, mul_inv_cancel_right]

omit [Finite K] in
theorem conjAut_mem_range_conj_of_det {C : GL (Fin n) K} {y : Kˣ}
    (hC : GeneralLinearGroup.det C = y ^ n) :
    conjAut n K C ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have hdet : ((GeneralLinearGroup.scalar (Fin n) y⁻¹ * C : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, hC, ← Units.val_one]
    congr 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, inv_mul_cancel]
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin n) K,
      SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin n) y⁻¹ * C :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  refine ⟨proj n K g, ?_⟩
  rw [conj_proj_eq_conjAut, hg, map_mul, conjAut_scalar, one_mul]

theorem conjAut_inner_of_coprime (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (A : GL (Fin n) K) (hA : conjAut n K A ^ p = 1) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have h1 : conjAut n K (A ^ p) * fieldAut n K 1 = 1 := by rw [map_one, mul_one, map_pow, hA]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1
  have hdet : GeneralLinearGroup.det A ^ p = c ^ n := by
    rw [← map_pow, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  set u : ℤ := Nat.gcdA p n
  set v : ℤ := Nat.gcdB p n
  have huv : (p : ℤ) * u + (n : ℤ) * v = 1 := by
    have := Nat.gcd_eq_gcd_ab p n
    rw [hcop.gcd_eq_one, Nat.cast_one] at this
    exact this.symm
  refine conjAut_mem_range_conj_of_det (y := c ^ u * GeneralLinearGroup.det A ^ v) ?_
  have e1 : GeneralLinearGroup.det A = GeneralLinearGroup.det A ^ ((p : ℤ) * u + (n : ℤ) * v) := by
    rw [huv, zpow_one]
  have e2 : (c ^ u * GeneralLinearGroup.det A ^ v) ^ n =
      GeneralLinearGroup.det A ^ ((p : ℤ) * u + (n : ℤ) * v) := by
    have hc' : c ^ ((n : ℤ) * u) = GeneralLinearGroup.det A ^ ((p : ℤ) * u) := by
      rw [_root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast, hdet]
    rw [mul_pow, ← zpow_natCast (c ^ u), ← zpow_natCast (GeneralLinearGroup.det A ^ v),
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm u, hc', mul_comm v, ← _root_.zpow_add]
  rw [e2, ← e1]

theorem ordP_psl {r f : ℕ} (hr : r.Prime) (hf : 1 ≤ f) [CharP K r]
    (hK : Nat.card K = r ^ f) (hn : n = 3 ∨ n = 4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (α : MulAut (projectiveSL n K)) (hα : orderOf α = p) :
    OrdPConcl r (projectiveSL n K) α := by
  have : Fact r.Prime := ⟨hr⟩
  have hn3 : 3 ≤ n := by omega
  have hαp : α ^ p = 1 := hα ▸ pow_orderOf_eq_one α
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hE := mem_semilinear_of_odd hr hf hn3 hK α hpodd hαp
  by_cases hD : α ∈ linearAutGroup n K
  · right
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hD
    refine conjAut_inner_of_coprime hn3 hp ?_ A hαp
    intro hpn
    have := Nat.le_of_dvd (by omega) hpn
    omega
  · left
    obtain ⟨-, σ, -, ⟨h, hh, hαh⟩, -⟩ :=
      linear_prime_descent_char (ℓ := r) (K := K) (n := n) hr hf hn3 hK hp hE hD hα
    obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hh
    rw [hαh]
    exact StepH3L.exists_rgroup_of_field (by omega) H σ

end OrdPL

theorem ordPInner_fl3d : OrdPInner FL3d := by
  intro r p Y _ _ hr _ hp hp5 _ hY b hb
  obtain ⟨f, hf, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLM
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  change OrdPConcl r Y b
  apply OrdPConcl.of_mulEquiv e
  exact OrdPL.ordP_psl hr hf hK (Or.inl rfl) hp hp5 _
    ((MulEquiv.orderOf_eq (MulAut.congr e) b).trans hb)

theorem ordPInner_fl4d : OrdPInner FL4d := by
  intro r p Y _ _ hr _ hp hp5 _ hY b hb
  obtain ⟨f, hf, -, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLM
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  change OrdPConcl r Y b
  apply OrdPConcl.of_mulEquiv e
  exact OrdPL.ordP_psl hr hf hK (Or.inr rfl) hp hp5 _
    ((MulEquiv.orderOf_eq (MulAut.congr e) b).trans hb)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
