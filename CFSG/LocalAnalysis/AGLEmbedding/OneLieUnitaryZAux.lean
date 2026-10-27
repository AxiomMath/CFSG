module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin
open scoped IsMulCommutative

theorem mem_centralizer_of_isPGroup_of_card_eq_pow {G : Type*} [Group G] [Finite G] {p r n : ℕ}
    [Fact p.Prime] [hr : Fact r.Prime] {Z : Subgroup G} {t : G} (hZ : Nat.card Z = p ^ n)
    (htZ : t ∈ Subgroup.normalizer (Z : Set G)) (htr : IsPGroup r (Subgroup.zpowers t))
    (hprim : ∀ k : ℕ, 0 < k → k ≤ n → ¬ r ∣ p ^ k - 1) (hrp : r ≠ p) :
    ∀ z ∈ Z, t * z * t⁻¹ = z := by
  have hp : p.Prime := Fact.out
  set t' : Subgroup.normalizer (Z : Set G) := ⟨t, htZ⟩ with ht'
  set S : Subgroup (Subgroup.normalizer (Z : Set G)) := Subgroup.zpowers t' with hS
  have hSr : IsPGroup r S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp htr
    refine IsPGroup.of_card (n := k) ?_
    rw [hS, Nat.card_zpowers, ht', Subgroup.orderOf_mk, ← Nat.card_zpowers, hk]
  have hmod := hSr.card_modEq_card_fixedPoints Z
  set F : Subgroup Z := FixedPoints.subgroup S Z with hF
  have hFcard : Nat.card (MulAction.fixedPoints S Z) = Nat.card F := rfl
  rw [hFcard, hZ] at hmod
  obtain ⟨i, hi, hFi⟩ := (Nat.dvd_prime_pow hp).mp (hZ ▸ Subgroup.card_subgroup_dvd_card F)
  have hin : i = n := by
    rw [hFi] at hmod
    by_contra hne
    have hd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hp.pos hi)).mp hmod.symm
    have he : p ^ n - p ^ i = p ^ i * (p ^ (n - i) - 1) := by
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hi]
    rw [he] at hd
    rcases (Nat.Prime.dvd_mul hr.out).mp hd with h | h
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr.out hp).mp (hr.out.dvd_of_dvd_pow h))
    · exact hprim (n - i) (by omega) (by omega) h
  have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hFi, hin, hZ])
  intro z hz
  have hmem : (⟨z, hz⟩ : Z) ∈ F := hFtop ▸ Subgroup.mem_top _
  have h := congrArg Subtype.val
    ((FixedPoints.mem_subgroup S Z _).mp hmem ⟨t', Subgroup.mem_zpowers t'⟩)
  have h3 : ((t' • (⟨z, hz⟩ : Z) : Z) : G) = t * z * t⁻¹ := rfl
  simpa [Subgroup.smul_def, h3] using h

section Abstract

variable {Y : Type*} [Group Y]

theorem forall_mul_comm_of_inf_eq_centerOf {K T W : Subgroup Y}
    [(Subgroup.centralizer (K : Set Y)).Normal] (hTK : T ≤ K)
    (hWTC : W ≤ T ⊔ Subgroup.centralizer (K : Set Y)) (hWT : W ⊓ T = centerOf T) {c : Y}
    (hcK : c ∈ K) (hcT : c ∈ Subgroup.normalizer (T : Set Y))
    (hcW : c ∈ Subgroup.normalizer (W : Set Y))
    (hnt : ∃ u ∈ T, c * u * c⁻¹ * u⁻¹ ∉ centerOf T)
    (hirr : ∀ V : Subgroup Y, centerOf T ≤ V → V ≤ T → c ∈ Subgroup.normalizer (V : Set Y) →
      V = centerOf T ∨ V = T) :
    ∀ w ∈ W, ∀ x ∈ T, w * x = x * w := by
  set C := Subgroup.centralizer (K : Set Y) with hC
  have hcC : ∀ y ∈ C, c * y * c⁻¹ = y := fun y hy => by
    rw [Subgroup.mem_centralizer_iff.mp hy c hcK]
    group
  have hcCn : c ∈ Subgroup.normalizer (C : Set Y) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    have := hcC y hy
    calc y * c = c * y * c⁻¹ * c := by rw [this]
      _ = c * y := by group
  set V : Subgroup Y := T ⊓ (W ⊔ C) with hV
  have hZV : centerOf T ≤ V := fun x hx =>
    ⟨hx.1, Subgroup.mem_sup_left (hWT.ge hx).1⟩
  have hcV : c ∈ Subgroup.normalizer (V : Set Y) := by
    have hcWC : c ∈ Subgroup.normalizer ((W ⊔ C : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hcW hcCn ⊢
      rw [Subgroup.map_sup, hcW, hcCn]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcT, hcWC⟩
  rcases hirr V hZV inf_le_left hcV with hVZ | hVT
  · intro w hw x hx
    obtain ⟨s, hs, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hWTC hw)
    have hsV : s ∈ V := by
      refine ⟨hs, ?_⟩
      have e : s = s * y * y⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right (C.inv_mem hy))
    have hsZ : s ∈ centerOf T := hVZ ▸ hsV
    have hxy : x * y = y * x := Subgroup.mem_centralizer_iff.mp hy x (hTK hx)
    have hxs : x * s = s * x := Subgroup.mem_centralizer_iff.mp hsZ.2 x hx
    calc s * y * x = s * (x * y) := by rw [mul_assoc, hxy]
      _ = x * (s * y) := by rw [← mul_assoc, ← hxs, mul_assoc]
  · exfalso
    obtain ⟨u, hu, hnu⟩ := hnt
    apply hnu
    have huV : u ∈ W ⊔ C := (show u ∈ V from hVT ▸ hu).2
    obtain ⟨w, hw, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp huV
    have key : c * (w * y) * c⁻¹ * (w * y)⁻¹ = c * w * c⁻¹ * w⁻¹ := by
      calc c * (w * y) * c⁻¹ * (w * y)⁻¹ = c * w * c⁻¹ * (c * y * c⁻¹) * y⁻¹ * w⁻¹ := by group
        _ = c * w * c⁻¹ * w⁻¹ := by rw [hcC y hy]; group
    have hW' : c * (w * y) * c⁻¹ * (w * y)⁻¹ ∈ W := by
      rw [key]
      exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp hcW w).mp hw) (W.inv_mem hw)
    have hT' : c * (w * y) * c⁻¹ * (w * y)⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp hcT _).mp hu) (T.inv_mem hu)
    exact hWT ▸ ⟨hW', hT'⟩

private theorem prod_range_add_of_periodic {N : Type*} [CommGroup N] {g : ℕ → N} {o : ℕ}
    (hg : ∀ k, g (k + o) = g k) (j : ℕ) :
    ∏ k ∈ Finset.range o, g (j + k) = ∏ k ∈ Finset.range o, g k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have h1 := Finset.prod_range_succ' (fun k => g (j + k)) o
    rw [Finset.prod_range_succ, hg j, add_zero] at h1
    have h2 : ∏ k ∈ Finset.range o, g (j + (k + 1)) = ∏ k ∈ Finset.range o, g (j + k) :=
      (mul_right_cancel h1).symm
    rw [← h2]
    exact Finset.prod_congr rfl fun k _ => by rw [show j + 1 + k = j + (k + 1) by omega]

theorem exists_forall_mem_zpowers_of_conj {q : ℕ} {t c : Y}
    (hcomm : ∀ i j : ℕ, Commute (t ^ i * c * (t ^ i)⁻¹) (t ^ j * c * (t ^ j)⁻¹))
    (hcop : Nat.Coprime (orderOf t) q) :
    ∃ g : Y, ∀ w ∈ Subgroup.closure (Set.range fun k : ℕ => t ^ k * c * (t ^ k)⁻¹),
      t * w * t⁻¹ = w → w ^ q = 1 → w ∈ Subgroup.zpowers g := by
  classical
  set f : ℕ → Y := fun k => t ^ k * c * (t ^ k)⁻¹ with hf
  set C := Subgroup.closure (Set.range f) with hC
  have hpair : (Set.range f).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hcomm i j
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure hpair
  let _ : CommGroup C := inferInstance
  set o := orderOf t with ho
  have hto : t ^ o = 1 := pow_orderOf_eq_one t
  have hfk : ∀ k j : ℕ, t ^ k * f j * (t ^ k)⁻¹ = f (j + k) := by
    intro k j
    simp only [hf, pow_add, mul_inv_rev]
    group
  have hconjC : ∀ k : ℕ, ∀ x ∈ C, t ^ k * x * (t ^ k)⁻¹ ∈ C := by
    intro k x hx
    have hle : C.map (MulAut.conj (t ^ k)).toMonoidHom ≤ C := by
      rw [hC, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j + k, (hfk k j).symm⟩
    exact hle ⟨x, hx, rfl⟩
  let φ : ℕ → C →* C := fun k =>
    { toFun := fun x => ⟨t ^ k * x * (t ^ k)⁻¹, hconjC k x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let N : C →* C := ∏ k ∈ Finset.range o, φ k
  have hN : ∀ x : C, N x = ∏ k ∈ Finset.range o, φ k x := fun x => by
    simp only [N, MonoidHom.finsetProd_apply]
  set gen : ℕ → C := fun j => ⟨f j, Subgroup.subset_closure ⟨j, rfl⟩⟩ with hgen
  have hφgen : ∀ k j : ℕ, φ k (gen j) = gen (j + k) := fun k j => Subtype.ext (hfk k j)
  have hper : ∀ k : ℕ, gen (k + o) = gen k := by
    intro k
    apply Subtype.ext
    simp only [hgen, hf, pow_add, hto, mul_one]
  have hNgen : ∀ j : ℕ, N (gen j) = N (gen 0) := by
    intro j
    rw [hN, hN]
    simp only [hφgen, zero_add]
    exact prod_range_add_of_periodic hper j
  have hNC : ∀ x : C, N x ∈ Subgroup.zpowers (N (gen 0)) := by
    have htop : (Subgroup.zpowers (N (gen 0))).comap N = ⊤ := by
      rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range f),
        Subgroup.closure_le]
      rintro x ⟨j, hj⟩
      have hx : x = gen j := Subtype.ext hj.symm
      rw [SetLike.mem_coe, Subgroup.mem_comap, hx, hNgen j]
      exact Subgroup.mem_zpowers (N (gen 0))
    intro x
    have hx : x ∈ (Subgroup.zpowers (N (gen 0))).comap N := htop ▸ Subgroup.mem_top x
    exact hx
  refine ⟨(N (gen 0) : Y), fun w hw htw hwq => ?_⟩
  have htkw : ∀ k : ℕ, t ^ k * w * (t ^ k)⁻¹ = w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc t ^ (k + 1) * w * (t ^ (k + 1))⁻¹ = t ^ k * (t * w * t⁻¹) * (t ^ k)⁻¹ := by group
        _ = w := by rw [htw, ih]
  have hNw : N ⟨w, hw⟩ = ⟨w, hw⟩ ^ o := by
    rw [hN]
    have : ∀ k ∈ Finset.range o, φ k ⟨w, hw⟩ = ⟨w, hw⟩ := fun k _ => Subtype.ext (htkw k)
    rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_range]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hNC ⟨w, hw⟩)
  have hwo : w ^ o = (N (gen 0) : Y) ^ m := by
    have := congrArg Subtype.val hm
    rw [hNw] at this
    simpa using this.symm
  have hdvd : orderOf w ∣ q := orderOf_dvd_of_pow_eq_one hwq
  have hcop' : o.Coprime (orderOf w) := Nat.Coprime.coprime_dvd_right hdvd hcop
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime hcop'
  rw [← he, hwo, ← zpow_natCast, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

end Abstract

end CFSG.AGLEmbedding
