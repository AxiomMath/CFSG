module

public import CFSG.CGT.Foote81L6.PiDihedral
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralAut

public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

section End

variable {G : Type*} [Group G]

theorem mulAut_pow_apply_succ (y : MulAut G) (n : ℕ) (g : G) :
    (y ^ (n + 1)) g = y ((y ^ n) g) := by simp [pow_succ']

theorem mulAut_pow_apply_succ' (y : MulAut G) (n : ℕ) (g : G) :
    (y ^ (n + 1)) g = (y ^ n) (y g) := by simp [pow_succ]

theorem exists_mulAut_of_iterate (f : G →* G) {N : ℕ} (hN : 0 < N) (hf : ∀ x, f^[N] x = x) :
    ∃ ψ : MulAut G, (∀ x, ψ x = f x) ∧ ψ ^ N = 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  let ψ : MulAut G :=
    { toFun := f
      invFun := f^[M]
      left_inv := fun x => by
        have := hf x
        rwa [Function.iterate_succ_apply] at this
      right_inv := fun x => by
        have := hf x
        rwa [Function.iterate_succ_apply'] at this
      map_mul' := map_mul f }
  have hψ : ∀ x, ψ x = f x := fun _ => rfl
  refine ⟨ψ, hψ, ?_⟩
  have key : ∀ m x, (ψ ^ m) x = f^[m] x := by
    intro m x
    induction m with
    | zero => simp
    | succ m ih => rw [mulAut_pow_apply_succ, ih, hψ, Function.iterate_succ_apply']
  ext x
  rw [key, hf]; simp

end End

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {a : ι → ℕ}

theorem central_apply_cases (ha : ∀ i, 2 ≤ a i) {c : PX a} (hc : ∀ x, x * c = c * x) (i : ι) :
    c i = 1 ∨ c i = zc (a i) :=
  eq_one_or_zc_of_comm (ha i) fun g =>
    ((comm_mulSingle_iff c).mp (fun i h => (hc _).symm) i g).symm

theorem central_sq (ha : ∀ i, 2 ≤ a i) {c : PX a} (hc : ∀ x, x * c = c * x) : c * c = 1 := by
  ext i
  rcases central_apply_cases ha hc i with h | h
  · simp [h]
  · simp [h, zc_mul_self (a := a i) (by have := ha i; omega)]

theorem central_pow_odd (ha : ∀ i, 2 ≤ a i) {c : PX a} (hc : ∀ x, x * c = c * x) {N : ℕ}
    (hN : Odd N) : c ^ N = c := by
  obtain ⟨k, rfl⟩ := hN
  rw [pow_succ, pow_mul, sq, central_sq ha hc, one_pow, one_mul]

theorem pi_induction {P : PX a → Prop} (h1 : P 1) (hmul : ∀ x z, P x → P z → P (x * z))
    (hs : ∀ j (g : DihedralGroup (2 ^ a j)), P (Pi.mulSingle j g)) (x : PX a) : P x := by
  have key : ∀ s : Finset ι, ∀ x : PX a, (∀ i ∉ s, x i = 1) → P x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      have : x = 1 := funext fun i => hx i (by simp)
      rwa [this]
    | insert i s hi ih =>
      intro x hx
      have hx' : x = Pi.mulSingle i (x i) * (Pi.mulSingle i (x i)⁻¹ * x) := by
        rw [Pi.mulSingle_inv, mul_inv_cancel_left]
      rw [hx']
      refine hmul _ _ (hs i _) (ih _ fun k hk => ?_)
      by_cases hki : k = i
      · subst hki; simp
      · have : k ∉ insert i s := by simp [hki, hk]
        simp [Pi.mulSingle_eq_of_ne hki, hx k this]
  exact key Finset.univ x (by simp)

theorem eq_one_of_fix_mulSingle (y : MulAut (PX a))
    (h : ∀ j (g : DihedralGroup (2 ^ a j)), y (Pi.mulSingle j g) = Pi.mulSingle j g) : y = 1 := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  refine pi_induction (P := fun x => y x = x) (by simp) ?_ h x
  intro x z hx hz
  simp [hx, hz]

theorem fix_center_gen (y : MulAut (PX a)) (hfix : ∀ j, 2 ≤ a j → y (zz a j) = zz a j)
    {c : PX a} (hc : ∀ x, x * c = c * x) (hab : ∀ i, a i ≤ 1 → c i = 1) : y c = c := by
  have key : ∀ s : Finset ι, ∀ c : PX a, (∀ x, x * c = c * x) → (∀ i, a i ≤ 1 → c i = 1) →
      (∀ i ∉ s, c i = 1) → y c = c := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro c _ _ hx
      have : c = 1 := funext fun i => hx i (by simp)
      rw [this, map_one]
    | insert i s hi ih =>
      intro c hc hab hx
      by_cases hai : 2 ≤ a i
      · rcases eq_one_or_zc_of_comm hai (fun g =>
            ((comm_mulSingle_iff c).mp (fun i h => (hc _).symm) i g).symm) with h | h
        · refine ih c hc hab fun k hk => ?_
          by_cases hki : k = i
          · subst hki; exact h
          · exact hx k (by simp [hki, hk])
        · have hi1 : 1 ≤ a i := by omega
          have hc' : ∀ x, x * (zz a i * c) = (zz a i * c) * x := by
            intro x
            calc x * (zz a i * c) = (x * zz a i) * c := (mul_assoc ..).symm
              _ = (zz a i * x) * c := by rw [zz_comm i hi1 x]
              _ = zz a i * (x * c) := mul_assoc ..
              _ = zz a i * (c * x) := by rw [hc x]
              _ = (zz a i * c) * x := (mul_assoc ..).symm
          have := ih (zz a i * c) hc' (fun k hk => by
            by_cases hki : k = i
            · subst hki; simp [zz_apply_same, h, zc_mul_self hi1]
            · simp [zz_apply_ne hki, hab k hk]) (fun k hk => by
            by_cases hki : k = i
            · subst hki; simp [zz_apply_same, h, zc_mul_self hi1]
            · simp [zz_apply_ne hki, hx k (by simp [hki, hk])])
          rw [map_mul, hfix i hai] at this
          exact mul_left_cancel this
      · exact ih c hc hab fun k hk => by
          by_cases hki : k = i
          · subst hki; exact hab k (by omega)
          · exact hx k (by simp [hki, hk])
  exact key Finset.univ c hc hab (by simp)

theorem fix_center (ha : ∀ i, 2 ≤ a i) (y : MulAut (PX a)) (hfix : ∀ j, y (zz a j) = zz a j)
    {c : PX a} (hc : ∀ x, x * c = c * x) : y c = c :=
  fix_center_gen y (fun j _ => hfix j) hc fun i hi => by have := ha i; omega

theorem central_mul {c₁ c₂ : PX a} (h₁ : ∀ x, x * c₁ = c₁ * x) (h₂ : ∀ x, x * c₂ = c₂ * x) :
    ∀ x, x * (c₁ * c₂) = (c₁ * c₂) * x := by
  intro x
  calc x * (c₁ * c₂) = (x * c₁) * c₂ := (mul_assoc ..).symm
    _ = (c₁ * x) * c₂ := by rw [h₁ x]
    _ = c₁ * (x * c₂) := mul_assoc ..
    _ = c₁ * (c₂ * x) := by rw [h₂ x]
    _ = (c₁ * c₂) * x := (mul_assoc ..).symm

theorem central_of_comp {c : PX a} (h : ∀ i (h : DihedralGroup (2 ^ a i)), c i * h = h * c i) :
    ∀ x, x * c = c * x := by
  intro x
  ext i
  simp [(h i (x i)).symm]

@[expose] def Cent (y : MulAut (PX a)) : Prop :=
  ∀ j k, k ≠ j → ∀ (d : DihedralGroup (2 ^ a j)) (h : DihedralGroup (2 ^ a k)),
    y (Pi.mulSingle j d) * Pi.mulSingle k h = Pi.mulSingle k h * y (Pi.mulSingle j d)

theorem fix_of_cent (ha : ∀ i, 2 ≤ a i) (y : MulAut (PX a)) (hc : Cent y) :
    ∀ j, y (zz a j) = zz a j := by
  intro j
  obtain ⟨i, d, h, hne⟩ := sig2 (ha j) y
  have : i = j := by
    by_contra hij
    exact hne (hc j i hij d h)
  subst this
  exact (sig1 (ha i) y d h hne).2

theorem kl (ha : ∀ i, 2 ≤ a i) (y : MulAut (PX a)) {N : ℕ} (hN : Odd N) (hy : y ^ N = 1)
    (hc : Cent y) : y = 1 := by
  have hfix := fix_of_cent ha y hc
  have hN0 : 0 < N := hN.pos
  have hcomp : ∀ j k, k ≠ j → ∀ (d : DihedralGroup (2 ^ a j)) (h : DihedralGroup (2 ^ a k)),
      (y (Pi.mulSingle j d)) k * h = h * (y (Pi.mulSingle j d)) k := fun j k hk d h => by
    have := congrFun (hc j k hk d h) k
    simpa using this
  let yj : ∀ j, DihedralGroup (2 ^ a j) →* DihedralGroup (2 ^ a j) := fun j =>
    (Pi.evalMonoidHom (fun i => DihedralGroup (2 ^ a i)) j).comp
      (y.toMonoidHom.comp (MonoidHom.mulSingle (fun i => DihedralGroup (2 ^ a i)) j))
  have hyj : ∀ j g, yj j g = y (Pi.mulSingle j g) j := fun _ _ => rfl
  have step : ∀ j (g : DihedralGroup (2 ^ a j)), ∃ c : PX a, (∀ x, x * c = c * x) ∧ c j = 1 ∧
      y (Pi.mulSingle j g) = Pi.mulSingle j (yj j g) * c := by
    intro j g
    refine ⟨(Pi.mulSingle j (yj j g))⁻¹ * y (Pi.mulSingle j g), ?_, ?_, by simp⟩
    · refine central_of_comp fun k h => ?_
      by_cases hk : k = j
      · subst hk; simp [hyj]
      · simpa [Pi.mulSingle_eq_of_ne hk] using hcomp j k hk g h
    · simp [hyj]
  have iter : ∀ m j (g : DihedralGroup (2 ^ a j)), ∃ c : PX a, (∀ x, x * c = c * x) ∧ c j = 1 ∧
      (y ^ m) (Pi.mulSingle j g) = Pi.mulSingle j ((yj j)^[m] g) * c := by
    intro m
    induction m with
    | zero => intro j g; exact ⟨1, fun x => by simp, by simp, by simp⟩
    | succ m ih =>
      intro j g
      obtain ⟨c, hc1, hc2, hc3⟩ := ih j g
      obtain ⟨c₁, hd1, hd2, hd3⟩ := step j ((yj j)^[m] g)
      refine ⟨c₁ * c, central_mul hd1 hc1, by simp [hd2, hc2], ?_⟩
      rw [mulAut_pow_apply_succ, hc3, map_mul, hd3, fix_center ha y hfix hc1, mul_assoc,
        Function.iterate_succ_apply']
  have hyjN : ∀ j (g : DihedralGroup (2 ^ a j)), (yj j)^[N] g = g := by
    intro j g
    obtain ⟨c, -, hc2, hc3⟩ := iter N j g
    rw [hy] at hc3
    have := congrFun hc3 j
    simpa [hc2] using this.symm
  have hid : ∀ j (g : DihedralGroup (2 ^ a j)), yj j g = g := by
    intro j g
    obtain ⟨ψ, hψ, hψN⟩ := exists_mulAut_of_iterate (yj j) hN0 (hyjN j)
    have := CFSG.ComponentClassification.HarrisLit.dihedral_mulAut_eq_one_of_odd (ha j) ψ hN hψN
    rw [← hψ, this]; rfl
  refine eq_one_of_fix_mulSingle y fun j g => ?_
  obtain ⟨c, hc1, hc2, hc3⟩ := step j g
  rw [hid] at hc3
  have hpow : ∀ m, (y ^ m) (Pi.mulSingle j g) = Pi.mulSingle j g * c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [mulAut_pow_apply_succ, ih, map_mul, hc3, map_pow, fix_center ha y hfix hc1, pow_succ',
        mul_assoc]
  have h1 := hpow N
  rw [hy, central_pow_odd ha hc1 hN, MulAut.one_apply] at h1
  have : c = 1 := by
    have h2 : (Pi.mulSingle j g : PX a) * c = Pi.mulSingle j g * 1 := by
      rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  rw [hc3, this, mul_one]

theorem eq_one_of_fix (ha : ∀ i, 2 ≤ a i) (y : MulAut (PX a)) {N : ℕ} (hN : Odd N)
    (hy : y ^ N = 1) (hfix : ∀ j, y (zz a j) = zz a j) : y = 1 := by
  refine kl ha y hN hy fun j k hk d h => ?_
  obtain ⟨i, -, -, hz, hcomm⟩ := sig (ha j) y
  have hzz : zz a i = zz a j := hz.symm.trans (hfix j)
  have hij : i = j := zz_injective (by have := ha i; omega) (by have := ha j; omega) hzz
  subst hij
  exact hcomm k hk d h

theorem perm (ha : ∀ i, 2 ≤ a i) (y : MulAut (PX a)) :
    ∃ σ : Equiv.Perm ι, (∀ j, y (zz a j) = zz a (σ j)) ∧ ∀ j, a j ≤ a (σ j) := by
  choose f _ hfle hfz _ using fun j => sig (ha j) y
  have hinj : Function.Injective f := by
    intro j j' h
    have : y (zz a j) = y (zz a j') := by rw [hfz, hfz, h]
    exact zz_injective (by have := ha j; omega) (by have := ha j'; omega) (y.injective this)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hfz, hfle⟩

theorem pow_zz (y : MulAut (PX a)) (σ : Equiv.Perm ι) (h : ∀ j, y (zz a j) = zz a (σ j))
    (m : ℕ) : ∀ j, (y ^ m) (zz a j) = zz a ((σ ^ m) j) := by
  induction m with
  | zero => intro j; simp
  | succ m ih =>
    intro j
    rw [mulAut_pow_apply_succ', h, ih, pow_succ, Equiv.Perm.mul_apply]

end CFSG.CGT.Foote81L6
