module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarKappaAlg
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Star

open Subgroup Matrix

section Crd

variable {H : Type*} [CommGroup H] {b : Fin 5 → H}

@[expose] def crd (b : Fin 5 → H) (a : Fin 5 → ZMod 4) : H := ∏ i, b i ^ (a i).val

theorem pow_mod_four {x : H} (hx : x ^ 4 = 1) (k : ℕ) : x ^ (k % 4) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k 4, pow_add, pow_mul, hx, one_pow, mul_one]

theorem pow_val_add {x : H} (hx : x ^ 4 = 1) (m n : ZMod 4) :
    x ^ (m + n).val = x ^ m.val * x ^ n.val := by
  rw [ZMod.val_add, pow_mod_four hx, pow_add]

theorem crd_add (hb : ∀ i, b i ^ 4 = 1) (a a' : Fin 5 → ZMod 4) :
    crd b (a + a') = crd b a * crd b a' := by
  unfold crd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_val_add (hb i)]

theorem crd_zero : crd b 0 = 1 := by
  simp [crd]

theorem crd_neg (hb : ∀ i, b i ^ 4 = 1) (a : Fin 5 → ZMod 4) : crd b (-a) = (crd b a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← crd_add hb, neg_add_cancel, crd_zero]

theorem crd_sub (hb : ∀ i, b i ^ 4 = 1) (a a' : Fin 5 → ZMod 4) :
    crd b (a - a') = crd b a * (crd b a')⁻¹ := by
  rw [sub_eq_add_neg, crd_add hb, crd_neg hb]

theorem crd_nsmul (hb : ∀ i, b i ^ 4 = 1) (n : ℕ) (a : Fin 5 → ZMod 4) :
    crd b (n • a) = crd b a ^ n := by
  induction n with
  | zero => rw [zero_smul, crd_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, crd_add hb, ih, pow_succ]

theorem crd_single (i : Fin 5) : crd b (Pi.single i 1) = b i := by
  unfold crd
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  exact pow_one (b i)

theorem crd_sum (hb : ∀ i, b i ^ 4 = 1) (s : Finset (Fin 5)) (f : Fin 5 → Fin 5 → ZMod 4) :
    crd b (∑ i ∈ s, f i) = ∏ i ∈ s, crd b (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, crd_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, crd_add hb, ih]

theorem map_crd (hb : ∀ i, b i ^ 4 = 1) (σ : H →* H) (B : Matrix (Fin 5) (Fin 5) (ZMod 4))
    (hB : ∀ i, σ (b i) = crd b (B i)) (a : Fin 5 → ZMod 4) : σ (crd b a) = crd b (a ᵥ* B) := by
  have hsum : a ᵥ* B = ∑ i, (a i).val • B i := by
    ext j
    rw [Finset.sum_apply j Finset.univ fun i => (a i).val • B i]
    show ∑ i, a i * B i j = ∑ i, ((a i).val • B i) j
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  calc σ (crd b a) = ∏ i, σ (b i) ^ (a i).val := by simp only [crd, map_prod, map_pow]
    _ = ∏ i, crd b ((a i).val • B i) :=
        Finset.prod_congr rfl fun i _ => by rw [hB, crd_nsmul hb]
    _ = crd b (∑ i, (a i).val • B i) := (crd_sum hb _ _).symm
    _ = crd b (a ᵥ* B) := by rw [hsum]

theorem crd_surjective (hb : ∀ i, b i ^ 4 = 1) {P : H → Prop} (hsq : ∀ v, P (v ^ 2))
    (hker : ∀ w, w ^ 2 = 1 → P w) (hP : ∀ v, P v → v ∈ closure (Set.range fun i => b i ^ 2)) :
    Function.Surjective (crd b) := by
  have hcl : ∀ x ∈ closure (Set.range fun i => b i ^ 2), ∃ c, x = crd b c ^ 2 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨Pi.single i 1, by rw [crd_single]⟩
    | one => exact ⟨0, by rw [crd_zero, one_pow]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨c, rfl⟩ := ihx
      obtain ⟨c', rfl⟩ := ihy
      exact ⟨c + c', by rw [crd_add hb, mul_pow]⟩
    | inv x _ ihx =>
      obtain ⟨c, rfl⟩ := ihx
      exact ⟨-c, by rw [crd_neg hb, inv_pow]⟩
  intro v
  obtain ⟨c, hc⟩ := hcl _ (hP _ (hsq v))
  have hw : (v * (crd b c)⁻¹) ^ 2 = 1 := by rw [mul_pow, inv_pow, ← hc, mul_inv_cancel]
  obtain ⟨c', hc'⟩ := hcl _ (hP _ (hker _ hw))
  refine ⟨c + 2 • c', ?_⟩
  rw [crd_add hb, crd_nsmul hb, ← hc', mul_comm v, ← mul_assoc, mul_inv_cancel, one_mul]

theorem crd_bijective (hcard : Nat.card H = 2 ^ 10) (hs : Function.Surjective (crd b)) :
    Function.Bijective (crd b) :=
  hs.bijective_of_nat_card_le (by rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin]; norm_num)

@[expose] noncomputable def crdMat (hbij : Function.Bijective (crd b)) (σ : H →* H) :
    Matrix (Fin 5) (Fin 5) (ZMod 4) :=
  Matrix.of fun i => (Equiv.ofBijective _ hbij).symm (σ (b i))

theorem crd_crdMat (hbij : Function.Bijective (crd b)) (σ : H →* H) (i : Fin 5) :
    σ (b i) = crd b (crdMat hbij σ i) :=
  (Equiv.ofBijective_apply_symm_apply _ hbij _).symm

theorem kapA_rows :
    kapA 0 = Pi.single 0 1 ∧ kapA 1 = Pi.single 1 1 ∧ kapA 2 = Pi.single 0 1 + Pi.single 2 1 ∧
      kapA 3 = Pi.single 0 1 + Pi.single 1 1 + Pi.single 3 1 ∧
      kapA 4 = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 4 1 := by
  decide

theorem false_of_crd (hb : ∀ i, b i ^ 4 = 1) (hbij : Function.Bijective (crd b))
    (σ τ : H →* H) (hτ : ∀ x, τ x = σ (σ x)) (hττ : ∀ x, τ (τ x) = x)
    (hσ0 : σ (b 0 ^ 2) = b 0 ^ 2) (hσ1 : σ (b 1 ^ 2) = b 1 ^ 2)
    (hσ2 : σ (b 2 ^ 2) = b 0 ^ 2 * b 2 ^ 2) (hσ3 : σ (b 3 ^ 2) = b 0 ^ 2 * b 1 ^ 2 * b 3 ^ 2)
    (hσ4 : σ (b 4 ^ 2) = b 0 ^ 2 * b 1 ^ 2 * b 2 ^ 2 * b 4 ^ 2)
    (hκ1 : b 1 * (τ (b 1))⁻¹ ∈ closure ({b 0 ^ 2, b 1 ^ 2} : Set H))
    (hκ2 : b 2 * (τ (b 2))⁻¹ ∈ closure ({b 0 ^ 2, b 1 ^ 2} : Set H)) : False := by
  set B := crdMat hbij σ with hBdef
  have hσa : ∀ a, σ (crd b a) = crd b (a ᵥ* B) := map_crd hb σ B (crd_crdMat hbij σ)
  have hτa : ∀ a, τ (crd b a) = crd b (a ᵥ* (B * B)) := fun a => by
    rw [hτ, hσa, hσa, vecMul_vecMul]
  have inj := hbij.1
  have hQQ : B * B * (B * B) = 1 := by
    ext i j
    have h := hττ (b i)
    rw [← crd_single (b := b) i, hτa, hτa, vecMul_vecMul] at h
    have h' := congrFun (inj h) j
    rw [single_one_vecMul, Matrix.row_apply] at h'
    rw [h', Matrix.one_apply, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  have hrow : ∀ i, σ (b i ^ 2) = crd b (2 • kapA i) := by
    obtain ⟨r0, r1, r2, r3, r4⟩ := kapA_rows
    have s : ∀ k, crd b (Pi.single k 1) = b k := fun k => crd_single k
    intro i
    fin_cases i
    · show σ (b 0 ^ 2) = crd b (2 • kapA 0)
      rw [hσ0, r0, crd_nsmul hb, s]
    · show σ (b 1 ^ 2) = crd b (2 • kapA 1)
      rw [hσ1, r1, crd_nsmul hb, s]
    · show σ (b 2 ^ 2) = crd b (2 • kapA 2)
      rw [hσ2, r2, crd_nsmul hb, crd_add hb, s, s, mul_pow]
    · show σ (b 3 ^ 2) = crd b (2 • kapA 3)
      rw [hσ3, r3, crd_nsmul hb, crd_add hb, crd_add hb, s, s, s, mul_pow, mul_pow]
    · show σ (b 4 ^ 2) = crd b (2 • kapA 4)
      rw [hσ4, r4, crd_nsmul hb, crd_add hb, crd_add hb, crd_add hb, s, s, s, s, mul_pow, mul_pow,
        mul_pow]
  have h2 : ∀ i j, 2 * B i j = 2 * kapA i j := by
    intro i j
    have h : σ (b i ^ 2) = crd b ((2 • Pi.single i 1) ᵥ* B) := by
      rw [← hσa, crd_nsmul hb, crd_single]
    rw [hrow i] at h
    have h' := congrFun (inj h) j
    rw [smul_vecMul, single_one_vecMul, Pi.smul_apply, Pi.smul_apply, Matrix.row_apply,
      nsmul_eq_mul, nsmul_eq_mul] at h'
    exact_mod_cast h'.symm
  have hU : ∀ y ∈ closure ({b 0 ^ 2, b 1 ^ 2} : Set H), ∃ x : Fin 5 → ZMod 4, x 2 = 0 ∧
      y = crd b x := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ⟨2 • Pi.single 0 1, by decide, by rw [crd_nsmul hb, crd_single]⟩
      · exact ⟨2 • Pi.single 1 1, by decide, by rw [crd_nsmul hb, crd_single]⟩
    | one => exact ⟨0, rfl, crd_zero.symm⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨c, hc2, rfl⟩ := ihx
      obtain ⟨c', hc'2, rfl⟩ := ihy
      exact ⟨c + c', by rw [Pi.add_apply, hc2, hc'2, add_zero], (crd_add hb c c').symm⟩
    | inv x _ ihx =>
      obtain ⟨c, hc2, rfl⟩ := ihx
      exact ⟨-c, by rw [Pi.neg_apply, hc2, neg_zero], (crd_neg hb c).symm⟩
  have hκ : ∀ i, b i * (τ (b i))⁻¹ ∈ closure ({b 0 ^ 2, b 1 ^ 2} : Set H) →
      (Pi.single i 1 : Fin 5 → ZMod 4) 2 - (B * B) i 2 = 0 := by
    intro i hi
    obtain ⟨x, hx2, hx⟩ := hU _ hi
    rw [← crd_single (b := b) i, hτa, ← crd_sub hb] at hx
    have h' := congrFun (inj hx) 2
    rw [Pi.sub_apply, single_one_vecMul, Matrix.row_apply] at h'
    rw [h', hx2]
  have h12 : (B * B) 1 2 = 0 := by
    have h := hκ 1 hκ1
    rw [Pi.single_eq_of_ne (by decide), zero_sub, neg_eq_zero] at h
    exact h
  have h22 : (B * B) 2 2 = 1 := by
    have h := hκ 2 hκ2
    rw [Pi.single_eq_same, sub_eq_zero] at h
    exact h.symm
  exact false_of_kapMatrix B h2 hQQ h12 h22

end Crd

section Conj

variable {G : Type*} [Group G]

@[expose] def conjEnd (V : Subgroup G) {g : G} (hg : g ∈ normalizer (V : Set G)) : V →* V where
  toFun v := ⟨g * v * g⁻¹, (mem_normalizer_iff.1 hg v).1 v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a c := Subtype.ext (by simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left])

theorem conjEnd_apply (V : Subgroup G) {g : G} (hg : g ∈ normalizer (V : Set G)) (v : V) :
    ((conjEnd V hg v : V) : G) = g * v * g⁻¹ := rfl

theorem mem_closure_of_coe_mem {V : Subgroup G} {T : Set V} {h : V}
    (hh : (h : G) ∈ closure (((↑) : V → G) '' T)) : h ∈ closure T := by
  rw [← V.coe_subtype, ← MonoidHom.map_closure] at hh
  obtain ⟨h', hh', he⟩ := hh
  rwa [Subtype.ext he] at hh'

end Conj

end CFSG.LocalAnalysis.EvenBN.Tits.N.Star
