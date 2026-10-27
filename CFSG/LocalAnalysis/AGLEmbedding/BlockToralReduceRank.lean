module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCentOmega

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace ToralReduce

variable {K : Type*} [Field K]

theorem geom_sum_eq_zero_of_fixed {n p : ℕ} {U : Matrix (Fin n) (Fin n) K} (hU : U ^ p = 1)
    (hfix : ∀ v : Fin n → K, U *ᵥ v = v → v = 0) : ∑ i ∈ Finset.range p, U ^ i = 0 := by
  have hcol : ∀ y, (∑ i ∈ Finset.range p, U ^ i) *ᵥ y = 0 := fun y => by
    rw [Matrix.sum_mulVec]
    exact hfix _ (LinearThreeKit.mulVec_fixedSum hU y)
  ext i j
  simpa [Matrix.mulVec_single] using congrFun (hcol (Pi.single j 1)) i

theorem sum_geom_mul_eq {n p : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hAB : Commute A B) :
    ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p, (A ^ i * B) ^ j =
      ∑ j ∈ Finset.range p, (∑ i ∈ Finset.range p, (A ^ j) ^ i) * B ^ j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hAB.pow_left i).mul_pow, ← pow_mul, ← pow_mul, mul_comm i j]

theorem exists_fixed_of_commute {n p : ℕ} [NeZero n] (hpK : (p : K) ≠ 0)
    {a b : Matrix.SpecialLinearGroup (Fin n) K} (hab : Commute a b) (ha : a ^ p = 1)
    (hb : b ^ p = 1) :
    (∃ k : ℕ, 0 < k ∧ k < p ∧ ∃ v : Fin n → K, v ≠ 0 ∧
        ((a ^ k : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v) ∨
      ∃ i : ℕ, i < p ∧ ∃ v : Fin n → K, v ≠ 0 ∧
        ((a ^ i * b : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
          v := by
  refine or_iff_not_imp_left.mpr fun h1 => ?_
  by_contra h2
  have hA : (a : Matrix (Fin n) (Fin n) K) ^ p = 1 := LinearThreeKit.coe_pow_eq_one ha
  have hB : (b : Matrix (Fin n) (Fin n) K) ^ p = 1 := LinearThreeKit.coe_pow_eq_one hb
  have hAB : Commute (a : Matrix (Fin n) (Fin n) K) b := by
    have h : (a : Matrix (Fin n) (Fin n) K) * b = b * a := by
      have := congrArg
        (fun x : Matrix.SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hab.eq
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
    exact h
  have hp0 : p ≠ 0 := by rintro rfl; exact hpK Nat.cast_zero
  have hzA : ∀ k, 0 < k → k < p →
      ∑ i ∈ Finset.range p, ((a : Matrix (Fin n) (Fin n) K) ^ k) ^ i = 0 := by
    intro k hk hkp
    refine geom_sum_eq_zero_of_fixed (by rw [← pow_mul, mul_comm, pow_mul, hA, one_pow]) ?_
    intro v hv
    by_contra hv0
    exact h1 ⟨k, hk, hkp, v, hv0, by rw [Matrix.SpecialLinearGroup.coe_pow]; exact hv⟩
  have hzAB : ∀ i < p, ∑ j ∈ Finset.range p,
      ((a : Matrix (Fin n) (Fin n) K) ^ i * (b : Matrix (Fin n) (Fin n) K)) ^ j = 0 := by
    intro i hi
    refine geom_sum_eq_zero_of_fixed ?_ ?_
    · rw [((hAB.pow_left i)).mul_pow, ← pow_mul, mul_comm, pow_mul, hA, one_pow, one_mul, hB]
    · intro v hv
      by_contra hv0
      exact h2 ⟨i, hi, v, hv0, by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]; exact hv⟩
  have hsum := sum_geom_mul_eq (p := p) hAB
  rw [Finset.sum_eq_zero fun i hi => hzAB i (Finset.mem_range.mp hi),
    Finset.sum_eq_single 0 (fun j hj hj0 => by
      rw [hzA j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hj), zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero hp0)) h)] at hsum
  simp only [pow_zero, one_pow, Finset.sum_const, Finset.card_range, mul_one] at hsum
  have h00 := congrFun (congrFun hsum 0) 0
  simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, nsmul_eq_mul,
    mul_one] at h00
  exact hpK h00.symm

theorem eq_one_of_fixed_pair {p : ℕ} (hpK : (p : K) ≠ 0) {u : Matrix.SpecialLinearGroup (Fin 3) K}
    (hu : u ^ p = 1) {a b : Fin 3 → K} (hab : LinearIndependent K ![a, b])
    (ha : (u : Matrix (Fin 3) (Fin 3) K) *ᵥ a = a)
    (hb : (u : Matrix (Fin 3) (Fin 3) K) *ᵥ b = b) : u = 1 := by
  set U : Matrix (Fin 3) (Fin 3) K := (u : Matrix (Fin 3) (Fin 3) K) with hUdef
  have hUp : U ^ p = 1 := LinearThreeKit.coe_pow_eq_one hu
  set W : Submodule K (Fin 3 → K) := Submodule.span K (Set.range ![a, b])
  have hW : W ≠ ⊤ := by
    intro h
    have h2 : Module.finrank K W = 2 := by
      rw [finrank_span_eq_card hab, Fintype.card_fin]
    rw [h, finrank_top, Module.finrank_fin_fun] at h2
    omega
  obtain ⟨c, -, hc⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hW)
  have haW : a ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hbW : b ∈ W := Submodule.subset_span ⟨1, rfl⟩
  have hli : LinearIndependent K ![a, b, c] := by
    rw [Fintype.linearIndependent_iff]
    intro t ht
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at ht
    have ht2 : t 2 = 0 := by
      by_contra h2
      apply hc
      have : c = -(t 2)⁻¹ • (t 0 • a + t 1 • b) := by
        have h' : t 2 • c = -(t 0 • a + t 1 • b) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact ht
        rw [neg_smul, ← smul_neg, ← h', smul_smul, inv_mul_cancel₀ h2, one_smul]
      rw [this]
      exact W.smul_mem _ (W.add_mem (W.smul_mem _ haW) (W.smul_mem _ hbW))
    rw [ht2, zero_smul, add_zero] at ht
    obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hab (t 0) (t 1) ht
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact ht2
  obtain ⟨d, hd⟩ := LinearThreeKit.exists_sum_smul_eq hli (U *ᵥ c)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hd
  have hdet : U.det = !![1, 0, d 0; 0, 1, d 1; 0, 0, d 2].det := by
    refine LinearThreeKit.det_eq_of_mulVec_eq_sum hli fun j => ?_
    fin_cases j
    · simp [Fin.sum_univ_three, ha]
    · simp [Fin.sum_univ_three, hb]
    · simp [Fin.sum_univ_three, ← hd]
  rw [hUdef, u.prop, Matrix.det_fin_three] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const] at hdet
  have hd2 : d 2 = 1 := by linear_combination -hdet
  have hsub : (U - 1) *ᵥ c = d 0 • a + d 1 • b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hd, hd2, one_smul, add_sub_cancel_right]
  have hfixc : (U - 1) *ᵥ c = 0 := by
    refine LinearThreeKit.sub_one_mulVec_eq_zero hpK hUp c ?_
    rw [hsub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb]
  have hc' : U *ᵥ c = c := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hfixc
    exact hfixc
  have hU1 : U = 1 := by
    refine LinearThreeKit.eq_of_mulVec_eq hli fun j => ?_
    fin_cases j
    · simpa using ha
    · simpa using hb
    · simpa using hc'
  exact Subtype.ext hU1

theorem isFixedLine_of_fixed {p : ℕ} (hp : Odd p) (hpK : (p : K) ≠ 0)
    {u : Matrix.SpecialLinearGroup (Fin 3) K} (hu : u ^ p = 1) (hu1 : u ≠ 1) {x : Fin 3 → K}
    (hx : x ≠ 0) (hux : (u : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x) :
    LinearThreeKit.IsFixedLine p u x := by
  refine ⟨hp, hpK, hu, hx, hux, fun v hv => ?_⟩
  by_contra hvx
  exact hu1 (eq_one_of_fixed_pair hpK hu
    (LinearThreeKit.linearIndependent_pair_of_notMem (Submodule.mem_span_singleton_self x) hx
      hvx) hux hv)

theorem card_le_sq_of_commute {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hcomm : ∀ a ∈ P, ∀ b ∈ P, Commute a b)
    (hexp : ∀ g ∈ P, g ^ p = 1) : Nat.card P ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, haP, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr h
    rw [hbot, Subgroup.card_bot] at hlt
    exact absurd hlt (not_lt.mpr (Nat.one_le_pow _ _ hp.pos))
  have hoa : orderOf a = p := orderOf_eq_prime (hexp a haP) ha1
  obtain ⟨b, hbP, hba⟩ : ∃ b ∈ P, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hza : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hoa]
    have : Finite (Subgroup.zpowers a) :=
      Nat.finite_of_card_ne_zero (by rw [hza]; exact hp.ne_zero)
    have hle : Nat.card P ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le h
    have : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
    omega
  obtain ⟨g, hgP, hg1, v, hv0, hgv⟩ : ∃ g ∈ P, g ≠ 1 ∧ ∃ v : Fin 3 → K, v ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    rcases exists_fixed_of_commute hpK (hcomm a haP b hbP) (hexp a haP) (hexp b hbP) with
      ⟨k, hk, hkp, v, hv0, hv⟩ | ⟨i, hi, v, hv0, hv⟩
    · refine ⟨a ^ k, P.pow_mem haP k, ?_, v, hv0, hv⟩
      exact pow_ne_one_of_lt_orderOf hk.ne' (hoa ▸ hkp)
    · refine ⟨a ^ i * b, P.mul_mem (P.pow_mem haP i) hbP, fun h => hba ?_, v, hv0, hv⟩
      have : b = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact (Subgroup.zpowers a).inv_mem (Subgroup.npow_mem_zpowers a i)
  have hfl := isFixedLine_of_fixed (hp.odd_of_ne_two hp2) hpK (hexp g hgP) hg1 hv0 hgv
  have hPC : P ≤ Subgroup.centralizer ({g} : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    exact (hcomm g hgP h hh).eq
  have := (hfl.finite_card_le_sq hPC hexp).2
  omega

theorem pow_three_eq_one_of_mem_scalars {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ scalars 3 K) : g ^ 3 = 1 := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hgc, ← map_pow, ← Units.val_pow_eq_pow_val, hc,
    Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem exists_lift_of_commute [Finite K] {p k : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {Eb : Subgroup (projectiveSL 3 K)} (hc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x)
    (hexp : ∀ x ∈ Eb, x ^ p = 1) (hdvd : p ^ k ∣ Nat.card Eb) :
    ∃ P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K), Nat.card P = p ^ k ∧
      (∀ a ∈ P, ∀ b ∈ P, Commute a b) ∧ ∀ g ∈ P, g ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := Eb.comap (proj 3 K)
  let ψ : ↥H →* ↥Eb := ((proj 3 K).comp H.subtype).codRestrict Eb fun h => h.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := proj_surjective 3 K y
    exact ⟨⟨s, hy⟩, rfl⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime p
    (hdvd.trans (Subgroup.card_dvd_of_surjective hψ))
  refine ⟨P₀.map H.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hP₀]
  have hker : ∀ g ∈ P₀.map H.subtype, proj 3 K g = 1 → g = 1 := by
    intro g hg hg1
    obtain ⟨g', hg', rfl⟩ := hg
    have h3 : (g' : Matrix.SpecialLinearGroup (Fin 3) K) ^ 3 = 1 :=
      pow_three_eq_one_of_mem_scalars (proj_eq_one_iff.mp hg1)
    have hpk : (g' : Matrix.SpecialLinearGroup (Fin 3) K) ^ p ^ k = 1 := by
      have := pow_card_eq_one' (G := ↥P₀) (x := ⟨g', hg'⟩)
      rw [hP₀] at this
      simpa using congrArg (fun x : ↥P₀ => ((x : ↥H) : Matrix.SpecialLinearGroup (Fin 3) K))
        this
    have hcop : Nat.Coprime 3 (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
    have := pow_gcd_eq_one.mpr ⟨h3, hpk⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hmemE : ∀ g ∈ P₀.map H.subtype, proj 3 K g ∈ Eb := by
    rintro _ ⟨g', -, rfl⟩
    exact g'.2
  refine ⟨fun a ha b hb => ?_, fun g hg => ?_⟩
  · have h1 : a * b * (b * a)⁻¹ = 1 := hker _ ((P₀.map H.subtype).mul_mem
        ((P₀.map H.subtype).mul_mem ha hb) ((P₀.map H.subtype).inv_mem
          ((P₀.map H.subtype).mul_mem hb ha))) (by
      rw [map_mul, map_inv, map_mul, map_mul, hc _ (hmemE a ha) _ (hmemE b hb), mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  · refine hker _ ((P₀.map H.subtype).pow_mem hg p) ?_
    rw [map_pow, hexp _ (hmemE g hg)]

end ToralReduce

open ToralReduce in
theorem kFactL3RankTwo : KFactL3RankTwo := by
  intro Y _ _ L _ p hp hp5 hpZ ⟨e, ⟨φ⟩⟩ E hEL hE hcard
  set K := GaloisField 2 e
  have hpK : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
    omega
  let f : ↥E →* projectiveSL 3 K :=
    φ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hEL))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center ↥L) (Subgroup.inclusion hEL x) = 1 :=
      φ.injective (by rw [map_one]; exact hx)
    have hz : Subgroup.inclusion hEL x ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have hzp : (⟨_, hz⟩ : Subgroup.center ↥L) ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hE.2 x x.2
    have hdZ : orderOf (⟨_, hz⟩ : Subgroup.center ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
      orderOf_dvd_natCard _
    have hz1 : orderOf (⟨_, hz⟩ : Subgroup.center ↥L) = 1 := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hzp) with h | h
      · exact h
      · exact absurd (h ▸ hdZ) hpZ
    have := congrArg (fun z : Subgroup.center ↥L => ((z : ↥L) : Y)) (orderOf_eq_one_iff.mp hz1)
    exact Subtype.ext (by simpa using this)
  set Eb : Subgroup (projectiveSL 3 K) := f.range
  have hEb : Nat.card Eb = p ^ 3 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hEbc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, hE.1.is_comm.comm x y]
  have hEbp : ∀ x ∈ Eb, x ^ p = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (by simpa using hE.2 x x.2), map_one]
  obtain ⟨P, hPc, hPcomm, hPexp⟩ := exists_lift_of_commute hp (by omega) hEbc hEbp hEb.symm.dvd
  have hle := card_le_sq_of_commute hp (by omega) hpK hPcomm hPexp
  rw [hPc] at hle
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.AGLEmbedding
