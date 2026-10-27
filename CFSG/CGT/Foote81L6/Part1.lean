module

public import CFSG.CGT.Foote81L6.Part1Aux

public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

@[expose] def commAut {G : Type*} [Group G] (y : MulAut G) : Subgroup G :=
  Subgroup.closure (Set.range fun g => g⁻¹ * y g)

variable {a : Fin 3 → ℕ}

structure Setup (a : Fin 3 → ℕ) (y : MulAut (PX a)) (N : ℕ) : Prop where
  h0 : a 0 = 1
  h1 : 2 ≤ a 1
  h2 : 2 ≤ a 2
  hN : Odd N
  hyN : y ^ N = 1

variable {y : MulAut (PX a)} {N : ℕ}

theorem Setup.hcase (S : Setup a y N) : ∀ i, a i = 1 ∨ 2 ≤ a i := by
  intro i; fin_cases i
  · exact Or.inl S.h0
  · exact Or.inr S.h1
  · exact Or.inr S.h2

theorem Setup.fixW (S : Setup a y N) {c : PX a} (hc : ∀ x, x * c = c * x) (h0 : c 0 = 1) :
    y c = c := by
  refine fix_center_gen y (fun j hj => ?_) hc (fun i hi => ?_)
  · have : j ≠ 0 := fun h => by rw [h, S.h0] at hj; omega
    exact (p1 S.h0 S.h1 S.h2 y S.hN S.hyN j this).1
  · have : i = 0 := by
      fin_cases i
      · rfl
      · have := S.h1; simp at hi; omega
      · have := S.h2; simp at hi; omega
    subst this; exact h0

theorem Setup.eq_one_of_comm_central (S : Setup a y N)
    (hfix : ∀ c, (∀ x, x * c = c * x) → y c = c)
    (hcomm : ∀ x, ∀ z, z * (x⁻¹ * y x) = (x⁻¹ * y x) * z) : y = 1 := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  set c := x⁻¹ * y x with hc
  have hyx : y x = x * c := by rw [hc]; group
  have hpow : ∀ m, (y ^ m) x = x * c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [mulAut_pow_apply_succ, ih, map_mul, hyx, map_pow, hfix c (hcomm x), pow_succ', mul_assoc]
  have h1 := hpow N
  rw [S.hyN, central_pow_odd' S.hcase (hcomm x) S.hN, MulAut.one_apply] at h1
  have h2 : c = 1 := by
    have h3 : x * c = x * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h3
  rw [hyx, h2, mul_one]


def projY (a : Fin 3 → ℕ) : PX a →* PY a where
  toFun x := fun i => x i.succ
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projY_ιY (g : PY a) : projY a (ιY a g) = g := by
  ext i; simp [projY, ιY_succ]

def K0 (a : Fin 3 → ℕ) : Subgroup (PX a) where
  carrier := {x | ∀ i : Fin 2, x i.succ = 1}
  mul_mem' := by intro x z hx hz i; simp [hx i, hz i]
  one_mem' := by intro i; rfl
  inv_mem' := by intro x hx i; simp [hx i]

theorem K0_le_center (S : Setup a y N) : K0 a ≤ Subgroup.center (PX a) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro z
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · show z 0 * x 0 = x 0 * z 0
    exact mul_comm_of_le_one (by rw [S.h0]) _ _
  · simp [show x i.succ = 1 from hx i]

theorem Setup.case_fixed (S : Setup a y N) (hW : ∀ c, (∀ x, x * c = c * x) → y c = c) : y = 1 := by
  have hc := K0_le_center S
  have key := twist S.h0 S.h1 S.h2 y S.hN S.hyN (K0 a) hc
    (fun k hk => by rw [hW k (Subgroup.mem_center_iff.mp (hc hk))]; exact hk)
    (projY a) projY_ιY (fun k hk => by ext i; exact hk i) (fun x hx i => congrFun hx i)
  exact S.eq_one_of_comm_central hW fun x z => (Subgroup.mem_center_iff.mp (hc (key x)) z)


theorem center_map (y : MulAut (PX a)) {w : PX a} (hw : w ∈ Subgroup.center (PX a)) :
    y w ∈ Subgroup.center (PX a) :=
  Subgroup.mem_center_iff.mpr (map_central (Subgroup.mem_center_iff.mp hw))

def delta (y : MulAut (PX a)) : Subgroup.center (PX a) →* PX a :=
  MonoidHom.mk' (fun w => (w : PX a)⁻¹ * y w) (by
    intro w1 w2
    have a1 : y w1 * (w2 : PX a)⁻¹ = (w2 : PX a)⁻¹ * y w1 :=
      (Subgroup.mem_center_iff.mp (center_map y w1.2) _).symm
    have a2 : (w1 : PX a)⁻¹ * (w2 : PX a)⁻¹ = (w2 : PX a)⁻¹ * (w1 : PX a)⁻¹ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ w1.2) _).symm
    show ((w1 * w2 : Subgroup.center (PX a)) : PX a)⁻¹ * y ((w1 * w2 : Subgroup.center (PX a)) : PX a) = _
    rw [Subgroup.coe_mul, mul_inv_rev, map_mul]
    calc (w2 : PX a)⁻¹ * (w1 : PX a)⁻¹ * (y w1 * y w2)
        = ((w1 : PX a)⁻¹ * (w2 : PX a)⁻¹) * (y w1 * y w2) := by rw [a2]
      _ = (w1 : PX a)⁻¹ * ((w2 : PX a)⁻¹ * y w1) * y w2 := by group
      _ = (w1 : PX a)⁻¹ * (y w1 * (w2 : PX a)⁻¹) * y w2 := by rw [a1]
      _ = _ := by group)

def Kc (y : MulAut (PX a)) : Subgroup (PX a) := (delta y).range

theorem mem_Kc {k : PX a} :
    k ∈ Kc y ↔ ∃ w : PX a, w ∈ Subgroup.center (PX a) ∧ w⁻¹ * y w = k := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, w.2, hw⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

theorem Kc_le_center : Kc y ≤ Subgroup.center (PX a) := by
  intro k hk
  obtain ⟨w, hw, rfl⟩ := mem_Kc.mp hk
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) (center_map y hw)

theorem Kc_map {k : PX a} (hk : k ∈ Kc y) : y k ∈ Kc y := by
  obtain ⟨w, hw, rfl⟩ := mem_Kc.mp hk
  refine mem_Kc.mpr ⟨y w, center_map y hw, ?_⟩
  simp

theorem pow_fix {k : PX a} (hk : y k = k) (m : ℕ) : (y ^ m) k = k := by
  induction m with
  | zero => simp
  | succ m ih => rw [mulAut_pow_apply_succ, ih, hk]

theorem Setup.Kc_fix (S : Setup a y N) {k : PX a} (hk : k ∈ Kc y) (hyk : y k = k) : k = 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_Kc.mp hk
  set k := w⁻¹ * y w with hkdef
  have hyw : y w = w * k := by rw [hkdef]; group
  have hkc : ∀ x, x * k = k * x := Subgroup.mem_center_iff.mp (Kc_le_center (mem_Kc.mpr ⟨w, hw, rfl⟩))
  have hpow : ∀ m, (y ^ m) w = w * k ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [mulAut_pow_apply_succ', hyw, map_mul, ih, pow_fix hyk, pow_succ, mul_assoc]
  have h1 := hpow N
  rw [S.hyN, central_pow_odd' S.hcase hkc S.hN, MulAut.one_apply] at h1
  have h3 : w * k = w * 1 := by rw [mul_one]; exact h1.symm
  exact mul_left_cancel h3

theorem Setup.Kc_inj (S : Setup a y N) {k₁ k₂ : PX a} (h₁ : k₁ ∈ Kc y) (h₂ : k₂ ∈ Kc y)
    (h : k₁ 0 = k₂ 0) : k₁ = k₂ := by
  have hk : k₁⁻¹ * k₂ ∈ Kc y := Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁) h₂
  have hc := Subgroup.mem_center_iff.mp (Kc_le_center hk)
  have := S.Kc_fix hk (S.fixW hc (by simp [h]))
  exact inv_mul_eq_one.mp this


theorem Setup.Kc_enum (S : Setup a y N) {t : PX a} (ht : t ∈ Kc y) (ht1 : t ≠ 1) (hyt : y t ≠ t) :
    (∀ k ∈ Kc y, k = 1 ∨ k = t ∨ k = y t ∨ k = t * y t) ∧
      ∀ s : DihedralGroup (2 ^ a 0), ∃ k ∈ Kc y, k 0 = s := by
  have hyt' : y t ∈ Kc y := Kc_map ht
  have hu : t 0 ≠ 1 := fun h => ht1 (S.Kc_inj ht (Kc y).one_mem (by simpa using h))
  have hv : (y t) 0 ≠ 1 := fun h => by
    have := S.Kc_inj hyt' (Kc y).one_mem (by simpa using h)
    exact ht1 (y.injective (this.trans (map_one y).symm))
  have huv : t 0 ≠ (y t) 0 := fun h => hyt (S.Kc_inj hyt' ht h.symm)
  have htt : t * y t ∈ Kc y := Subgroup.mul_mem _ ht hyt'
  constructor
  · intro k hk
    rcases e4_enum S.h0 _ _ hu hv huv (k 0) with h | h | h | h
    · exact Or.inl (S.Kc_inj hk (Kc y).one_mem (by simpa using h))
    · exact Or.inr (Or.inl (S.Kc_inj hk ht h))
    · exact Or.inr (Or.inr (Or.inl (S.Kc_inj hk hyt' h)))
    · exact Or.inr (Or.inr (Or.inr (S.Kc_inj hk htt (by simpa using h))))
  · intro s
    rcases e4_enum S.h0 _ _ hu hv huv s with h | h | h | h
    · exact ⟨1, (Kc y).one_mem, by simpa using h.symm⟩
    · exact ⟨t, ht, h.symm⟩
    · exact ⟨y t, hyt', h.symm⟩
    · exact ⟨t * y t, htt, by simpa using h.symm⟩

theorem Setup.Kc_card (S : Setup a y N) {t : PX a} (ht : t ∈ Kc y) (ht1 : t ≠ 1) (hyt : y t ≠ t) :
    Nat.card (Kc y) = 4 := by
  obtain ⟨-, hsurj⟩ := S.Kc_enum ht ht1 hyt
  have : Function.Bijective (fun k : Kc y => (k : PX a) 0) :=
    ⟨fun k₁ k₂ h => Subtype.ext (S.Kc_inj k₁.2 k₂.2 h),
      fun s => by obtain ⟨k, hk, h⟩ := hsurj s; exact ⟨⟨k, hk⟩, h⟩⟩
  rw [Nat.card_congr (Equiv.ofBijective _ this), e4_card S.h0]

theorem Setup.Kc_sq (S : Setup a y N) {k : PX a} (hk : k ∈ Kc y) : k * k = 1 :=
  central_sq' S.hcase (Subgroup.mem_center_iff.mp (Kc_le_center hk))

theorem Setup.Kc_pow_two_ne (S : Setup a y N) {t : PX a} (ht : t ∈ Kc y) (hyt : y t ≠ t) :
    y (y t) ≠ t := by
  intro h
  have key : ∀ m, (y ^ (2 * m)) t = t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, mulAut_pow_apply_succ, mulAut_pow_apply_succ,
        ih, h]
  obtain ⟨j, hj⟩ := S.hN
  have h1 : (y ^ N) t = t := by rw [S.hyN]; rfl
  rw [hj, mulAut_pow_apply_succ, key] at h1
  exact hyt h1

theorem Setup.Kc_pow3 (S : Setup a y N) {t : PX a} (ht : t ∈ Kc y) (ht1 : t ≠ 1) (hyt : y t ≠ t)
    {k : PX a} (hk : k ∈ Kc y) : y (y (y k)) = k := by
  obtain ⟨henum, -⟩ := S.Kc_enum ht ht1 hyt
  have hyt' : y t ∈ Kc y := Kc_map ht
  have hy2 : y (y t) ∈ Kc y := Kc_map hyt'
  have h2t : y (y t) = t * y t := by
    rcases henum _ hy2 with h | h | h | h
    · exfalso
      have : y t = 1 := y.injective (h.trans (map_one y).symm)
      exact ht1 (y.injective (this.trans (map_one y).symm))
    · exact absurd h (S.Kc_pow_two_ne ht hyt)
    · exact absurd (y.injective h) hyt
    · exact h
  have hcomm := Subgroup.mem_center_iff.mp (Kc_le_center hyt')
  have h3t : y (y (y t)) = t := by
    rw [h2t, map_mul, h2t, ← mul_assoc, ← hcomm t, mul_assoc, S.Kc_sq hyt', mul_one]
  rcases henum _ hk with rfl | rfl | rfl | rfl
  · simp
  · exact h3t
  · rw [h3t]
  · rw [map_mul, map_mul, map_mul, h3t]


def phiHom (hK : Kc y ≤ Subgroup.center (PX a)) : ↥(Kc y) × PY a →* PX a :=
  MonoidHom.mk' (fun p => (p.1 : PX a) * ιY a p.2) (by
    intro p q
    have h := Subgroup.mem_center_iff.mp (hK q.1.2) (ιY a p.2)
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
    calc (p.1 : PX a) * q.1 * (ιY a p.2 * ιY a q.2)
        = p.1 * ((q.1 : PX a) * ιY a p.2) * ιY a q.2 := by group
      _ = p.1 * (ιY a p.2 * (q.1 : PX a)) * ιY a q.2 := by rw [h]
      _ = _ := by group)

theorem Setup.phiHom_bijective (S : Setup a y N) {t : PX a} (ht : t ∈ Kc y) (ht1 : t ≠ 1)
    (hyt : y t ≠ t) : Function.Bijective (phiHom (Kc_le_center (y := y))) := by
  obtain ⟨-, hsurj⟩ := S.Kc_enum ht ht1 hyt
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨k, g⟩ hkg
    rw [MonoidHom.mem_ker] at hkg
    have h0 : (k : PX a) 0 = 1 := by
      have := congrFun hkg 0
      simpa [phiHom, ιY_zero] using this
    have hk1 : (k : PX a) = 1 := S.Kc_inj k.2 (Kc y).one_mem (by simpa using h0)
    have hg : ιY a g = 1 := by
      have : (k : PX a) * ιY a g = 1 := hkg
      rwa [hk1, one_mul] at this
    have hg1 : g = 1 := ιY_injective (hg.trans (map_one _).symm)
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext hk1) hg1
  · intro x
    obtain ⟨k, hk, h⟩ := hsurj (x 0)
    obtain ⟨g, hg⟩ := exists_ιY (k⁻¹ * x) (by simp [h])
    exact ⟨(⟨k, hk⟩, g), by
      show k * ιY a g = x
      rw [← hg]; group⟩

theorem Setup.main_ii (S : Setup a y N) {t : PX a} (ht : t ∈ Kc y) (ht1 : t ≠ 1)
    (hyt : y t ≠ t) :
    commAut y = Kc y ∧ y ^ 3 = 1 ∧
      ∃ φ : ↥(Kc y) × PY a ≃* PX a, ∀ k g, φ (k, g) = (k : PX a) * ιY a g := by
  have hKc : Kc y ≤ Subgroup.center (PX a) := Kc_le_center
  let φ : ↥(Kc y) × PY a ≃* PX a := MulEquiv.ofBijective (phiHom hKc) (S.phiHom_bijective ht ht1 hyt)
  have hφ : ∀ k g, φ (k, g) = (k : PX a) * ιY a g := fun _ _ => rfl
  let π : PX a →* PY a := (MonoidHom.snd _ _).comp φ.symm.toMonoidHom
  have hπι : ∀ g, π (ιY a g) = g := by
    intro g
    have : φ.symm (ιY a g) = (1, g) := by
      rw [MulEquiv.symm_apply_eq, hφ]; simp
    simp [π, this]
  have hπK : ∀ k ∈ Kc y, π k = 1 := by
    intro k hk
    have : φ.symm k = (⟨k, hk⟩, 1) := by
      rw [MulEquiv.symm_apply_eq, hφ]; simp
    simp [π, this]
  have hker : ∀ x, π x = 1 → x ∈ Kc y := by
    intro x hx
    have h1 : (φ.symm x).2 = 1 := hx
    have h2 : x = (φ.symm x).1 * ιY a (φ.symm x).2 := by
      conv_lhs => rw [← φ.apply_symm_apply x]
      rfl
    rw [h2, h1, map_one, mul_one]
    exact (φ.symm x).1.2
  have hall := twist S.h0 S.h1 S.h2 y S.hN S.hyN (Kc y) hKc (fun k hk => Kc_map hk) π hπι hπK hker
  have hcomm : commAut y = Kc y := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, rfl⟩
      exact hall g
    · intro k hk
      obtain ⟨w, hw, rfl⟩ := mem_Kc.mp hk
      exact Subgroup.subset_closure ⟨w, rfl⟩
  have hy3 : y ^ 3 = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.one_apply]
    set c := x⁻¹ * y x with hc
    have hcK : c ∈ Kc y := hall x
    have hyx : y x = x * c := by rw [hc]; group
    have hcc := Subgroup.mem_center_iff.mp (hKc hcK)
    have hs : c * y c * y (y c) ∈ Kc y :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcK (Kc_map hcK)) (Kc_map (Kc_map hcK))
    have h3 := S.Kc_pow3 ht ht1 hyt hcK
    have hfix : y (c * y c * y (y c)) = c * y c * y (y c) := by
      rw [map_mul, map_mul, h3]
      have e1 := Subgroup.mem_center_iff.mp (hKc (Kc_map hcK))
      have e2 := Subgroup.mem_center_iff.mp (hKc (Kc_map (Kc_map hcK)))
      calc y c * y (y c) * c = y c * (y (y c) * c) := mul_assoc ..
        _ = y c * (c * y (y c)) := by rw [e2 c]
        _ = (y c * c) * y (y c) := (mul_assoc ..).symm
        _ = c * y c * y (y c) := by rw [e1 c]
    have hs1 := S.Kc_fix hs hfix
    have : (y ^ 3) x = y (y (y x)) := by simp [pow_succ]
    have e1 : y (y x) = x * c * y c := by rw [hyx, map_mul, hyx]
    have e2 : y (y (y x)) = x * c * y c * y (y c) := by rw [e1, map_mul, map_mul, hyx]
    rw [this, e2]
    calc x * c * y c * y (y c) = x * (c * y c * y (y c)) := by group
      _ = x := by rw [hs1, mul_one]
  exact ⟨hcomm, hy3, φ, hφ⟩


theorem part1 (h0 : a 0 = 1) (h1 : 2 ≤ a 1) (h2 : 2 ≤ a 2) (y : MulAut (PX a)) (hy : y ≠ 1)
    {N : ℕ} (hN : Odd N) (hyN : y ^ N = 1) :
    orderOf y = 3 ∧ Nat.card (commAut y) = 4 ∧ (∀ x ∈ commAut y, x * x = 1) ∧
      ∃ φ : ↥(commAut y) × PY a ≃* PX a, ∀ x g, φ (x, g) = (x : PX a) * ιY a g := by
  have S : Setup a y N := ⟨h0, h1, h2, hN, hyN⟩
  by_cases hex : ∃ w : PX a, w ∈ Subgroup.center (PX a) ∧ y w ≠ w
  swap
  · push_neg at hex
    exact absurd (S.case_fixed fun c hc => hex c (Subgroup.mem_center_iff.mpr hc)) hy
  obtain ⟨w, hw, hyw⟩ := hex
  have ht : w⁻¹ * y w ∈ Kc y := mem_Kc.mpr ⟨w, hw, rfl⟩
  have ht1 : w⁻¹ * y w ≠ 1 := fun h => hyw (inv_mul_eq_one.mp h).symm
  have hyt : y (w⁻¹ * y w) ≠ w⁻¹ * y w := fun h => ht1 (S.Kc_fix ht h)
  obtain ⟨hcomm, hy3, φ, hφ⟩ := S.main_ii ht ht1 hyt
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy
    · exact h
  · rw [hcomm]; exact S.Kc_card ht ht1 hyt
  · intro x hx
    rw [hcomm] at hx
    exact S.Kc_sq hx
  · exact ⟨((MulEquiv.subgroupCongr hcomm).prodCongr (MulEquiv.refl _)).trans φ, fun x g => by
      show φ (MulEquiv.subgroupCongr hcomm x, g) = _
      rw [hφ]; rfl⟩

end CFSG.CGT.Foote81L6
