module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding.R3

@[expose] def actMatN (p n : ℕ) (g : NAct) : Matrix (Fin n) (Fin n) (ZMod p) :=
  fun k i => ((g.mat.getD (n * k.val + i.val) 0 : ℕ) : ZMod p)

@[expose] def qMat (p n : ℕ) (q : List ℕ) : Matrix (Fin n) (Fin n) (ZMod p) :=
  fun a b => ((q.getD (n * a.val + b.val) 0 : ℕ) : ZMod p)

theorem fsum_eq (N : ℕ) (f : Fin N → ℤ) : fsum N f = ∑ i, f i := (Fin.sum_univ_def f).symm

theorem cast_fsum {p : ℕ} (N : ℕ) (f : Fin N → ℤ) :
    ((fsum N f : ℤ) : ZMod p) = ∑ i, ((f i : ℤ) : ZMod p) := by
  rw [fsum_eq, Int.cast_sum]

theorem cast_kd {p : ℕ} (a b : ℕ) : ((kd a b : ℤ) : ZMod p) = if a = b then 1 else 0 := by
  unfold kd; split_ifs <;> simp

theorem cast_kd_fin {p n : ℕ} (a b : Fin n) :
    ((kd a.val b.val : ℤ) : ZMod p) = if a = b then 1 else 0 := by
  rw [cast_kd]; simp [Fin.val_inj]

theorem cast_ent {p : ℕ} (g : NAct) (n : ℕ) (k i : Fin n) :
    ((g.ent n k.val i.val : ℤ) : ZMod p) = actMatN p n g k i := by
  simp [NAct.ent, actMatN]

theorem zmod_eq_of_emod {p : ℕ} {x y : ℤ} (h : (x - y) % (p : ℤ) == 0) : (x : ZMod p) = y := by
  have h' : (x - y) % (p : ℤ) = 0 := beq_iff_eq.1 h
  have hd : (p : ℤ) ∣ x - y := Int.dvd_of_emod_eq_zero h'
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) p).2 hd
  push_cast at this
  exact sub_eq_zero.1 this

theorem noFun_of_funOK {p : ℕ} {m : NMod} {cf : ℕ → ℕ → ℕ → ℤ} (h : m.funOK p cf = true)
    (v : Fin m.basis.length → ZMod p)
    (hv : ∀ j : Fin m.acts.length,
      Matrix.vecMul v (actMatN p m.basis.length (m.acts.get j)) = v) : v = 0 := by
  funext r₀
  unfold NMod.funOK at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have key : ∀ r : Fin m.basis.length,
      (∑ j : Fin m.acts.length, ∑ s : Fin m.basis.length, (cf r₀.val j.val s.val : ZMod p) *
        (actMatN p m.basis.length (m.acts.get j) r s - if r = s then 1 else 0)) =
        if r = r₀ then 1 else 0 := by
    intro r
    have := zmod_eq_of_emod (h r₀ r)
    simp only [cast_fsum, Int.cast_mul, Int.cast_sub, cast_ent, cast_kd_fin] at this
    exact this
  have hsum : ∀ (j : Fin m.acts.length) (s : Fin m.basis.length),
      ∑ r, (actMatN p m.basis.length (m.acts.get j) r s - if r = s then 1 else 0) * v r = 0 := by
    intro j s
    have := congrFun (hv j) s
    simp only [Matrix.vecMul, dotProduct] at this
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [sub_eq_zero]
    calc ∑ r, actMatN p m.basis.length (m.acts.get j) r s * v r
        = ∑ r, v r * actMatN p m.basis.length (m.acts.get j) r s :=
          Finset.sum_congr rfl fun r _ => mul_comm _ _
      _ = v s := this
  calc v r₀ = ∑ r, (if r = r₀ then (1 : ZMod p) else 0) * v r := by simp
    _ = ∑ r, (∑ j : Fin m.acts.length, ∑ s : Fin m.basis.length,
        (cf r₀.val j.val s.val : ZMod p) *
          (actMatN p m.basis.length (m.acts.get j) r s - if r = s then 1 else 0)) * v r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [key r]
    _ = ∑ j : Fin m.acts.length, ∑ s : Fin m.basis.length, (cf r₀.val j.val s.val : ZMod p) *
        ∑ r, (actMatN p m.basis.length (m.acts.get j) r s - if r = s then 1 else 0) * v r := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun s _ => ?_
        rw [hsum j s, mul_zero]

theorem sum5_comm {R : Type*} [AddCommMonoid R] {k n : ℕ}
    (T : Fin n → Fin n → Fin k → Fin n → Fin n → R) :
    ∑ a, ∑ b, ∑ j, ∑ r, ∑ s, T a b j r s = ∑ j, ∑ r, ∑ s, ∑ a, ∑ b, T a b j r s := by
  have h1 : ∑ a, ∑ b, ∑ j, ∑ r, ∑ s, T a b j r s =
      ∑ x : Fin n × Fin n, ∑ y : Fin k × Fin n × Fin n, T x.1 x.2 y.1 y.2.1 y.2.2 := by
    simp only [Fintype.sum_prod_type]
  have h2 : ∑ j, ∑ r, ∑ s, ∑ a, ∑ b, T a b j r s =
      ∑ y : Fin k × Fin n × Fin n, ∑ x : Fin n × Fin n, T x.1 x.2 y.1 y.2.1 y.2.2 := by
    simp only [Fintype.sum_prod_type]
  rw [h1, h2, Finset.sum_comm]

theorem sum4_comm {R : Type*} [AddCommMonoid R] {n : ℕ} (T : Fin n → Fin n → Fin n → Fin n → R) :
    ∑ a, ∑ b, ∑ r, ∑ s, T a b r s = ∑ r, ∑ s, ∑ a, ∑ b, T a b r s := by
  have h1 : ∑ a, ∑ b, ∑ r, ∑ s, T a b r s =
      ∑ x : Fin n × Fin n, ∑ y : Fin n × Fin n, T x.1 x.2 y.1 y.2 := by
    simp only [Fintype.sum_prod_type]
  have h2 : ∑ r, ∑ s, ∑ a, ∑ b, T a b r s =
      ∑ y : Fin n × Fin n, ∑ x : Fin n × Fin n, T x.1 x.2 y.1 y.2 := by
    simp only [Fintype.sum_prod_type]
  rw [h1, h2, Finset.sum_comm]

theorem inv_sum {p n : ℕ} (M B : Matrix (Fin n) (Fin n) (ZMod p)) (r s : Fin n) :
    ∑ a, ∑ b, (M a r * M b s - (if a = r then 1 else 0) * (if b = s then 1 else 0)) * B a b
      = (M.transpose * B * M) r s - B r s := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp [ite_mul, Finset.sum_ite_eq']

theorem alt_sum {p n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod p)) (r s : Fin n) :
    ∑ a, ∑ b, ((if a = r then 1 else 0) * (if b = s then 1 else 0) +
      (if a = s then 1 else 0) * (if b = r then 1 else 0)) * B a b = B r s + B s r := by
  simp [add_mul, Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq']

theorem alt_combo_of_altOK {p : ℕ} {m : NMod} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
    {ct : ℕ → ℕ → ℕ → ℕ → ℤ} {tgt : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : m.altOK p ci ct tgt = true)
    (B : Matrix (Fin m.basis.length) (Fin m.basis.length) (ZMod p)) (hB : B.transpose = -B)
    (hinv : ∀ j : Fin m.acts.length, (actMatN p m.basis.length (m.acts.get j)).transpose * B *
      actMatN p m.basis.length (m.acts.get j) = B) (a₀ b₀ : Fin m.basis.length) :
    ∑ a, ∑ b, (tgt a₀.val b₀.val a.val b.val : ZMod p) * B a b = 0 := by
  unfold NMod.altOK at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have key : ∀ a b : Fin m.basis.length, (tgt a₀.val b₀.val a.val b.val : ZMod p) =
      (∑ j : Fin m.acts.length, ∑ r : Fin m.basis.length, ∑ s : Fin m.basis.length,
        (ci a₀.val b₀.val j.val r.val s.val : ZMod p) *
          (actMatN p m.basis.length (m.acts.get j) a r *
            actMatN p m.basis.length (m.acts.get j) b s -
            (if a = r then 1 else 0) * (if b = s then 1 else 0))) +
      ∑ r : Fin m.basis.length, ∑ s : Fin m.basis.length,
        (ct a₀.val b₀.val r.val s.val : ZMod p) *
          ((if a = r then 1 else 0) * (if b = s then 1 else 0) +
            (if a = s then 1 else 0) * (if b = r then 1 else 0)) := by
    intro a b
    have := zmod_eq_of_emod (h a₀ b₀ a b)
    simp only [Int.cast_add, cast_fsum, Int.cast_mul, Int.cast_sub, cast_ent, cast_kd_fin] at this
    exact this.symm
  have hE : ∀ (j : Fin m.acts.length) (r s : Fin m.basis.length),
      ∑ a, ∑ b, (actMatN p m.basis.length (m.acts.get j) a r *
        actMatN p m.basis.length (m.acts.get j) b s -
        (if a = r then 1 else 0) * (if b = s then 1 else 0)) * B a b = 0 := by
    intro j r s
    rw [inv_sum, hinv j, sub_self]
  have hF : ∀ r s : Fin m.basis.length, ∑ a, ∑ b, ((if a = r then 1 else 0) *
      (if b = s then 1 else 0) + (if a = s then 1 else 0) * (if b = r then 1 else 0)) *
        B a b = 0 := by
    intro r s
    rw [alt_sum]
    have := congrFun (congrFun hB r) s
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    rw [this]; ring
  have part1 : ∑ a, ∑ b, (∑ j : Fin m.acts.length, ∑ r : Fin m.basis.length,
      ∑ s : Fin m.basis.length, (ci a₀.val b₀.val j.val r.val s.val : ZMod p) *
        (actMatN p m.basis.length (m.acts.get j) a r *
          actMatN p m.basis.length (m.acts.get j) b s -
          (if a = r then 1 else 0) * (if b = s then 1 else 0))) * B a b = 0 := by
    simp only [Finset.sum_mul]
    rw [sum5_comm]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun r _ =>
      Finset.sum_eq_zero fun s _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hE j r s, mul_zero]
  have part2 : ∑ a, ∑ b, (∑ r : Fin m.basis.length, ∑ s : Fin m.basis.length,
      (ct a₀.val b₀.val r.val s.val : ZMod p) *
        ((if a = r then 1 else 0) * (if b = s then 1 else 0) +
          (if a = s then 1 else 0) * (if b = r then 1 else 0))) * B a b = 0 := by
    simp only [Finset.sum_mul]
    rw [sum4_comm]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hF r s, mul_zero]
  calc ∑ a, ∑ b, (tgt a₀.val b₀.val a.val b.val : ZMod p) * B a b
      = ∑ a, ∑ b, ((∑ j : Fin m.acts.length, ∑ r : Fin m.basis.length,
        ∑ s : Fin m.basis.length, (ci a₀.val b₀.val j.val r.val s.val : ZMod p) *
          (actMatN p m.basis.length (m.acts.get j) a r *
            actMatN p m.basis.length (m.acts.get j) b s -
            (if a = r then 1 else 0) * (if b = s then 1 else 0))) +
        ∑ r : Fin m.basis.length, ∑ s : Fin m.basis.length,
          (ct a₀.val b₀.val r.val s.val : ZMod p) *
            ((if a = r then 1 else 0) * (if b = s then 1 else 0) +
              (if a = s then 1 else 0) * (if b = r then 1 else 0))) * B a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [key a b]
    _ = 0 := by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [part1, part2, add_zero]

theorem noAlt_of_altOK {p : ℕ} {m : NMod} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
    {ct : ℕ → ℕ → ℕ → ℕ → ℤ} (h : m.altOK p ci ct tgtAlt = true)
    (B : Matrix (Fin m.basis.length) (Fin m.basis.length) (ZMod p)) (hB : B.transpose = -B)
    (hinv : ∀ j : Fin m.acts.length, (actMatN p m.basis.length (m.acts.get j)).transpose * B *
      actMatN p m.basis.length (m.acts.get j) = B) : B = 0 := by
  ext a₀ b₀
  have := alt_combo_of_altOK h B hB hinv a₀ b₀
  simpa [tgtAlt, cast_kd_fin, ite_mul, Finset.sum_ite_eq'] using this

theorem cast_kd_pivot {p n : ℕ} (x : Fin n) {a₁ : ℕ} (ha : a₁ < n) :
    ((kd x.val a₁ : ℤ) : ZMod p) = if x = ⟨a₁, ha⟩ then 1 else 0 := by
  rw [cast_kd]; simp [Fin.ext_iff]

theorem tgtNondeg_sum {p n : ℕ} (q : List ℕ) {a₁ b₁ : ℕ} (ha : a₁ < n) (hb : b₁ < n)
    (a₀ b₀ : Fin n) (B : Fin n → Fin n → ZMod p) :
    ∑ x, ∑ y, ((tgtNondeg n q a₁ b₁ a₀.val b₀.val x.val y.val : ℤ) : ZMod p) * B x y =
      B a₀ b₀ - ((q.getD (n * a₀.val + b₀.val) 0 : ℕ) : ZMod p) * B ⟨a₁, ha⟩ ⟨b₁, hb⟩ := by
  have hsplit : ∀ x y : Fin n,
      ((tgtNondeg n q a₁ b₁ a₀.val b₀.val x.val y.val : ℤ) : ZMod p) * B x y =
        (if x = a₀ then 1 else 0) * (if y = b₀ then 1 else 0) * B x y -
          ((q.getD (n * a₀.val + b₀.val) 0 : ℕ) : ZMod p) *
            ((if x = (⟨a₁, ha⟩ : Fin n) then 1 else 0) *
              (if y = (⟨b₁, hb⟩ : Fin n) then 1 else 0)) * B x y := by
    intro x y
    simp only [tgtNondeg, Int.cast_sub, Int.cast_mul, cast_kd_fin, cast_kd_pivot _ ha,
      cast_kd_pivot _ hb, Int.cast_natCast]
    ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsplit x y]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · simp [ite_mul, Finset.sum_ite_eq']
  · simp [ite_mul, Finset.sum_ite_eq']

theorem nondeg_of_altOK {p : ℕ} [Fact p.Prime] {m : NMod} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
    {ct : ℕ → ℕ → ℕ → ℕ → ℤ} {q : List ℕ} {a₁ b₁ : ℕ} (ha : a₁ < m.basis.length)
    (hb : b₁ < m.basis.length)
    (h : m.altOK p ci ct (tgtNondeg m.basis.length q a₁ b₁) = true)
    (hq : IsUnit (qMat p m.basis.length q).det)
    (B : Matrix (Fin m.basis.length) (Fin m.basis.length) (ZMod p)) (hB : B.transpose = -B)
    (hinv : ∀ j : Fin m.acts.length, (actMatN p m.basis.length (m.acts.get j)).transpose * B *
      actMatN p m.basis.length (m.acts.get j) = B) (hne : B ≠ 0) : IsUnit B.det := by
  have hmul : B = (B ⟨a₁, ha⟩ ⟨b₁, hb⟩) • qMat p m.basis.length q := by
    ext a₀ b₀
    have key := alt_combo_of_altOK h B hB hinv a₀ b₀
    have key2 := (tgtNondeg_sum (p := p) q ha hb a₀ b₀ (fun x y => B x y)).symm.trans key
    rw [sub_eq_zero] at key2
    simpa [qMat, mul_comm] using key2
  have hc : B ⟨a₁, ha⟩ ⟨b₁, hb⟩ ≠ 0 := by
    intro h0
    apply hne
    rw [hmul, h0, zero_smul]
  rw [hmul, Matrix.det_smul]
  exact IsUnit.mul (IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)) hq

end CFSG.AGLEmbedding.R3
