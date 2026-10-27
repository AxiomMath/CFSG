module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs
public import CFSG.RankThree.SubgroupLists.CliffordPrime

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists

variable {q : ℕ} [Fact q.Prime]

private theorem mem_center_of_commute_of_eigen {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) {w : GL (Fin 3) (ZMod q)}
    (hw : ∀ x ∈ H, w * x = x * w) {v : Fin 3 → ZMod q} (hv : v ≠ 0) {c : ZMod q}
    (hwv : (w : Matrix (Fin 3) (Fin 3) (ZMod q)) *ᵥ v = c • v) :
    w ∈ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  set W : Submodule (ZMod q) (Fin 3 → ZMod q) :=
    Module.End.eigenspace (Matrix.toLin' (w : Matrix (Fin 3) (Fin 3) (ZMod q))) c
  have hmem : ∀ u, u ∈ W ↔ (w : Matrix (Fin 3) (Fin 3) (ZMod q)) *ᵥ u = c • u := fun u => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hinv : ∀ g : H, ∀ u ∈ W, ((H.subtype g : GL (Fin 3) (ZMod q)) :
      Matrix (Fin 3) (Fin 3) (ZMod q)) *ᵥ u ∈ W := by
    intro g u hu
    rw [hmem] at hu ⊢
    have hc := congrArg Units.val (hw g g.2)
    simp only [Units.val_mul] at hc
    rw [Subgroup.coe_subtype, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hu,
      Matrix.mulVec_smul]
  rcases hirr W hinv with hbot | htop
  · exact absurd (hbot ▸ (hmem v).2 hwv : v ∈ (⊥ : Submodule (ZMod q) (Fin 3 → ZMod q)))
      (by simpa using hv)
  refine Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, ?_⟩
  refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, scalar_mulVec,
    ← (hmem u).1 (htop ▸ Submodule.mem_top)]

private theorem two_ne_zero_zmod (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

private theorem diagSign_val (i : Fin 3) :
    ((diagSign i : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)) =
      diagonal fun j => if j = i then 1 else -1 := by
  ext a b
  simp only [diagSign, diagThree, diagonal_apply]
  split_ifs <;> simp

private theorem diagSign_mul_self (i : Fin 3) :
    (diagSign i : GL (Fin 3) (ZMod q)) * diagSign i = 1 := by
  ext : 1
  rw [Units.val_mul, diagSign_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

private theorem diagSign_two :
    (diagSign 2 : GL (Fin 3) (ZMod q)) = diagSign 0 * diagSign 1 := by
  ext : 1
  rw [Units.val_mul, diagSign_val, diagSign_val, diagSign_val, diagonal_mul_diagonal]
  congr 1
  funext j
  fin_cases j <;> norm_num

private theorem mulVec_single_of_commute_diagSign (hq2 : q ≠ 2) (i : Fin 3)
    {w : GL (Fin 3) (ZMod q)} (hw : diagSign i * w = w * diagSign i) :
    (w : Matrix (Fin 3) (Fin 3) (ZMod q)) *ᵥ Pi.single i 1 =
      (w : Matrix (Fin 3) (Fin 3) (ZMod q)) i i • Pi.single i 1 := by
  have hc := congrArg Units.val hw
  simp only [Units.val_mul, diagSign_val] at hc
  funext j
  rw [Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = i
  · subst hj; simp
  have hji := congrFun (congrFun hc j) i
  rw [diagonal_mul, mul_diagonal, if_neg hj, if_pos rfl] at hji
  have h2 : (2 : ZMod q) * (w : Matrix (Fin 3) (Fin 3) (ZMod q)) j i = 0 := by
    rw [neg_one_mul, mul_one] at hji
    rw [two_mul]
    nth_rw 1 [← hji]
    exact neg_add_cancel _
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (two_ne_zero_zmod hq2)
  · simp [Matrix.col_apply, h, hj]

private theorem mul_conj_mem_center (hq2 : q ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hd : ∀ i : Fin 3, ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ ∈ H) (i : Fin 3)
    {h : GL (Fin 3) (ZMod q)} (hh : h ∈ H) :
    h * (diagSign i * h * (diagSign i)⁻¹) ∈ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  set d : GL (Fin 3) (ZMod q) := diagSign i
  set a := d * h * d⁻¹
  have ha : a ∈ H := hd i h hh
  have hdd : d⁻¹ = d := inv_eq_of_mul_eq_one_right (diagSign_mul_self i)
  have hcd : d * (h * a) = (h * a) * d := by
    have e : d * (h * a) * d⁻¹ = a * ((d * d) * h * (d * d)⁻¹) := by simp only [a]; group
    rw [← mul_inv_eq_iff_eq_mul, e, show d * d = 1 from diagSign_mul_self i, inv_one, one_mul,
      mul_one]
    exact hcomm a ha h hh
  refine mem_center_of_commute_of_eigen hirr (fun x hx => hcomm _ (H.mul_mem hh ha) x hx)
    (v := Pi.single i 1) (by simp) (mulVec_single_of_commute_diagSign hq2 i hcd)

private theorem sq_mem_center_of_conj {G : Type*} [Group G] {h d₀ d₁ d₂ : G}
    (h2 : d₂ = d₀ * d₁) (hc : (d₀ * h * d₀⁻¹) * h = h * (d₀ * h * d₀⁻¹))
    (hz₀ : h * (d₀ * h * d₀⁻¹) ∈ Subgroup.center G)
    (hz₁ : h * (d₁ * h * d₁⁻¹) ∈ Subgroup.center G)
    (hz₂ : h * (d₂ * h * d₂⁻¹) ∈ Subgroup.center G) : h ^ 2 ∈ Subgroup.center G := by
  have e1 : h * (d₁ * h * d₁⁻¹) = (d₀ * h * d₀⁻¹) * (d₂ * h * d₂⁻¹) := by
    have hc₁ := Subgroup.mem_center_iff.mp hz₁ d₀
    calc h * (d₁ * h * d₁⁻¹) = d₀ * (h * (d₁ * h * d₁⁻¹)) * d₀⁻¹ := by rw [hc₁]; group
      _ = _ := by rw [h2]; group
  have e : h ^ 2 = (h * (d₀ * h * d₀⁻¹)) * (h * (d₂ * h * d₂⁻¹)) *
      (h * (d₁ * h * d₁⁻¹))⁻¹ := by
    rw [sq, e1, show h * (d₀ * h * d₀⁻¹) * (h * (d₂ * h * d₂⁻¹)) *
      (d₀ * h * d₀⁻¹ * (d₂ * h * d₂⁻¹))⁻¹ =
      h * ((d₀ * h * d₀⁻¹) * h) * (d₀ * h * d₀⁻¹)⁻¹ by group, hc]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hz₀ hz₂) (Subgroup.inv_mem _ hz₁)

private theorem sq_mem_center (hq2 : q ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hd : ∀ i : Fin 3, ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ ∈ H)
    {h : GL (Fin 3) (ZMod q)} (hh : h ∈ H) :
    h ^ 2 ∈ Subgroup.center (GL (Fin 3) (ZMod q)) :=
  have hz := fun i => mul_conj_mem_center hq2 hirr hcomm hd i hh
  sq_mem_center_of_conj diagSign_two (hcomm _ (hd 0 h hh) h hh) (hz 0) (hz 1) (hz 2)

private theorem pow_sub_one_of_mem_center {x : GL (Fin 3) (ZMod q)}
    (hx : x ∈ Subgroup.center (GL (Fin 3) (ZMod q))) : x ^ (q - 1) = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
  obtain ⟨u, rfl⟩ := hx
  rw [← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]

private theorem dvd_sub_one_of_dvd (hq : 1 ≤ q) {n : ℕ} (h1 : n ∣ 2 * (q - 1))
    (h2 : n ∣ q ^ 3 - 1) : n ∣ q - 1 := by
  have e : q ^ 3 - 1 = (q ^ 2 + q + 1) * (q - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hodd : Nat.Coprime 2 (q ^ 2 + q + 1) := by
    rw [Nat.coprime_two_left]
    have : Even (q * (q + 1)) := Nat.even_mul_succ_self q
    rw [show q ^ 2 + q = q * (q + 1) by ring]
    exact this.add_one
  have := Nat.dvd_gcd h1 (e ▸ h2)
  rwa [Nat.gcd_mul_right, hodd, one_mul] at this

theorem false_of_isCyclic {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {H : Subgroup (GL (Fin 3) (ZMod q))} (hirr : IsIrreducibleMatrixRep H.subtype)
    (hcyc : IsCyclic H) (hdvd : Nat.card H ∣ q ^ 3 - 1) (hndvd : ¬ Nat.card H ∣ q - 1)
    (hd : ∀ i : Fin 3, ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ ∈ H) : False := by
  have hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsCyclic.commutative (α := H)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card H := orderOf_eq_card_of_forall_mem_zpowers hg
  have hpow : (g : GL (Fin 3) (ZMod q)) ^ (2 * (q - 1)) = 1 := by
    rw [pow_mul]
    exact pow_sub_one_of_mem_center (sq_mem_center hq2 hirr hcomm hd g.2)
  have h1 : Nat.card H ∣ 2 * (q - 1) := by
    rw [← hord, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hpow
  exact hndvd (dvd_sub_one_of_dvd (Fact.out : q.Prime).one_le h1 hdvd)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
