module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3

namespace Sigma3Core

variable {𝔄 : Type*} [Group 𝔄]

theorem conjBy_mul (g g' : 𝔄) (L : Subgroup 𝔄) :
    conjBy (g * g') L = conjBy g (conjBy g' L) := by
  ext x
  simp only [mem_conjBy, mul_inv_rev, mul_assoc]

theorem conjBy_one (L : Subgroup 𝔄) : conjBy 1 L = L := by
  ext x
  simp [mem_conjBy]

theorem conjBy_inj (g : 𝔄) {L L' : Subgroup 𝔄} (h : conjBy g L = conjBy g L') : L = L' := by
  have h1 := congrArg (conjBy g⁻¹) h
  rwa [← conjBy_mul, ← conjBy_mul, inv_mul_cancel, conjBy_one, conjBy_one] at h1

theorem conjBy_pow_stable {g : 𝔄} {L : Subgroup 𝔄} (hg : conjBy g L = L) (n : ℕ) :
    conjBy (g ^ n) L = L := by
  induction n with
  | zero => simp [conjBy_one]
  | succ n ih => rw [pow_succ', conjBy_mul, ih, hg]

theorem conjBy_pow_mem {I : Finset (Subgroup 𝔄)} {δ : 𝔄} (hδperm : ∀ L ∈ I, conjBy δ L ∈ I)
    {L : Subgroup 𝔄} (hL : L ∈ I) (n : ℕ) : conjBy (δ ^ n) L ∈ I := by
  induction n with
  | zero => simpa [conjBy_one] using hL
  | succ n ih => rw [pow_succ', conjBy_mul]; exact hδperm _ ih

theorem conj_eq_one_iff (g a : 𝔄) : g * a * g⁻¹ = 1 ↔ a = 1 := by
  constructor
  · intro h
    have h1 : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [h1, h]
    group
  · rintro rfl
    group

theorem dvd_of_conjBy_pow_eq {δ : 𝔄} {p : ℕ} (hp : p.Prime) (hδp : δ ^ p = 1)
    {L : Subgroup 𝔄} (hδL : conjBy δ L ≠ L) {d : ℕ} (hd : conjBy (δ ^ d) L = L) : p ∣ d := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    exact hδL (conjBy_one L)
  have hord : orderOf δ = p := orderOf_eq_prime hδp hδ1
  have hcop : d.Coprime (orderOf δ) := by
    rw [hord]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime hcop
  apply hδL
  rw [← he]
  exact conjBy_pow_stable hd e

def famRest (I : Finset (Subgroup 𝔄)) (L : Subgroup 𝔄) : Subgroup 𝔄 :=
  ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L'

theorem le_famRest {I : Finset (Subgroup 𝔄)} {L L' : Subgroup 𝔄} (hL' : L' ∈ I) (hne : L' ≠ L) :
    L' ≤ famRest I L :=
  le_iSup₂_of_le L' hL' (le_iSup_of_le hne le_rfl)

theorem famRest_commute {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {L : Subgroup 𝔄}
    (hL : L ∈ I) {r : 𝔄} (hr : r ∈ famRest I L) {c : 𝔄} (hc : c ∈ L) : Commute c r := by
  have hle : famRest I L ≤ Subgroup.centralizer (L : Set 𝔄) := by
    refine iSup₂_le fun L' hL' => iSup_le fun hne => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hI.comm L hL L' hL' hne.symm g hg x hx
  have h1 := hle hr
  rw [Subgroup.mem_centralizer_iff] at h1
  exact h1 c hc

theorem inf_famRest {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {L : Subgroup 𝔄}
    (hL : L ∈ I) : L ⊓ famRest I L = ⊥ := hI.indep L hL

theorem pow_eq_one_of_mul_famRest {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I)
    {L : Subgroup 𝔄} (hL : L ∈ I) {c r : 𝔄} (hc : c ∈ L) (hr : r ∈ famRest I L) {n : ℕ}
    (h : (c * r) ^ n = 1) : c ^ n = 1 := by
  have hcomm : Commute c r := famRest_commute hI hL hr hc
  rw [hcomm.mul_pow] at h
  have h1 : c ^ n ∈ L := L.pow_mem hc n
  have h2 : c ^ n ∈ famRest I L := by
    have h3 : c ^ n = (r ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h3]
    exact (famRest I L).inv_mem ((famRest I L).pow_mem hr n)
  have h4 : c ^ n ∈ L ⊓ famRest I L := ⟨h1, h2⟩
  rw [inf_famRest hI hL] at h4
  simpa using h4

theorem sl22_order_three :
    ∀ x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 → y ≠ 1 → y = x ∨ y = x⁻¹ := by
  decide

theorem order_three_cases {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {L : Subgroup 𝔄}
    (hL : L ∈ I) {x y : 𝔄} (hx : x ∈ L) (hy : y ∈ L) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  obtain ⟨φ⟩ := hI.sigma3 L hL
  have hx3' : (⟨x, hx⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hy3' : (⟨y, hy⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hx1' : (⟨x, hx⟩ : L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hy1' : (⟨y, hy⟩ : L) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  rcases sl22_order_three (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) (by rw [← map_pow, hx3', map_one])
      (by simpa using hx1') (by rw [← map_pow, hy3', map_one]) (by simpa using hy1') with h | h
  · left
    exact congrArg Subtype.val (φ.injective h)
  · right
    have h' : φ ⟨y, hy⟩ = φ (⟨x, hx⟩⁻¹) := by rw [map_inv]; exact h
    exact congrArg Subtype.val (φ.injective h')

theorem eq_one_of_pow_three_two_pow {x : 𝔄} (h3 : x ^ 3 = 1) {k : ℕ} (h2 : x ^ (2 ^ k) = 1) :
    x = 1 := by
  have h1 : x ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨h3, h2⟩
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  simpa [hg] using h1

theorem eq_of_mul_inv_two_pow {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I)
    {L : Subgroup 𝔄} (hL : L ∈ I) {a m : 𝔄} (ha : a ∈ L) (hm : m ∈ L) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hm3 : m ^ 3 = 1) (hm1 : m ≠ 1) {k : ℕ} (hk : (m * a⁻¹) ^ (2 ^ k) = 1) :
    m = a := by
  rcases order_three_cases hI hL ha hm ha3 ha1 hm3 hm1 with h | h
  · exact h
  · exfalso
    subst h
    have h2 : a⁻¹ * a⁻¹ = a := by
      calc a⁻¹ * a⁻¹ = a⁻¹ * a⁻¹ * a ^ 3 := by rw [ha3, mul_one]
        _ = a := by group
    rw [h2] at hk
    exact ha1 (eq_one_of_pow_three_two_pow ha3 hk)

theorem step_move {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {L M : Subgroup 𝔄}
    (hL : L ∈ I) (hM : M ∈ I) (hML : M ≠ L) {h a u : 𝔄} (haL : a ∈ L)
    (hha : h * a * h⁻¹ ∈ M) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hu : u ∈ famRest I M)
    (hhu : h * u * h⁻¹ ∈ famRest I M) {k : ℕ}
    (hk : (h * (a * u) * h⁻¹ * (a * u)⁻¹) ^ (2 ^ k) = 1) : False := by
  have hLM : L ≤ famRest I M := le_famRest hL (Ne.symm hML)
  have ha' : a⁻¹ ∈ famRest I M := (famRest I M).inv_mem (hLM haL)
  have hr : h * u * h⁻¹ * u⁻¹ * a⁻¹ ∈ famRest I M :=
    mul_mem (mul_mem hhu ((famRest I M).inv_mem hu)) ha'
  have heq : h * (a * u) * h⁻¹ * (a * u)⁻¹ = (h * a * h⁻¹) * (h * u * h⁻¹ * u⁻¹ * a⁻¹) := by
    group
  rw [heq] at hk
  have h1 := pow_eq_one_of_mul_famRest hI hM hha hr hk
  have h3 : (h * a * h⁻¹) ^ 3 = 1 := by rw [conj_pow, ha3]; group
  have h4 : h * a * h⁻¹ = 1 := eq_one_of_pow_three_two_pow h3 h1
  exact ha1 ((conj_eq_one_iff h a).1 h4)

theorem step_stay {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {L : Subgroup 𝔄}
    (hL : L ∈ I) {h a u : 𝔄} (haL : a ∈ L) (hha : h * a * h⁻¹ ∈ L) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hu : u ∈ famRest I L) (hhu : h * u * h⁻¹ ∈ famRest I L) {k : ℕ}
    (hk : (h * (a * u) * h⁻¹ * (a * u)⁻¹) ^ (2 ^ k) = 1) : h * a * h⁻¹ = a := by
  have hwR : h * u * h⁻¹ * u⁻¹ ∈ famRest I L := mul_mem hhu ((famRest I L).inv_mem hu)
  have hcomm : Commute a⁻¹ (h * u * h⁻¹ * u⁻¹) :=
    famRest_commute hI hL hwR (L.inv_mem haL)
  have heq : h * (a * u) * h⁻¹ * (a * u)⁻¹ =
      (h * a * h⁻¹ * a⁻¹) * (h * u * h⁻¹ * u⁻¹) := by
    calc h * (a * u) * h⁻¹ * (a * u)⁻¹
        = (h * a * h⁻¹) * ((h * u * h⁻¹ * u⁻¹) * a⁻¹) := by group
      _ = (h * a * h⁻¹) * (a⁻¹ * (h * u * h⁻¹ * u⁻¹)) := by rw [hcomm.eq]
      _ = (h * a * h⁻¹ * a⁻¹) * (h * u * h⁻¹ * u⁻¹) := by group
  rw [heq] at hk
  have hc : h * a * h⁻¹ * a⁻¹ ∈ L := mul_mem hha (L.inv_mem haL)
  have h1 := pow_eq_one_of_mul_famRest hI hL hc hwR hk
  have h3 : (h * a * h⁻¹) ^ 3 = 1 := by rw [conj_pow, ha3]; group
  have h4 : h * a * h⁻¹ ≠ 1 := fun h5 => ha1 ((conj_eq_one_iff h a).1 h5)
  exact eq_of_mul_inv_two_pow hI hL haL hha ha3 ha1 h3 h4 h1

def seqProd (x : ℕ → 𝔄) : ℕ → ℕ → 𝔄
  | _, 0 => 1
  | s, n + 1 => x s * seqProd x (s + 1) n

theorem seqProd_mem (H : Subgroup 𝔄) (x : ℕ → 𝔄) :
    ∀ (n s : ℕ), (∀ i, s ≤ i → i < s + n → x i ∈ H) → seqProd x s n ∈ H
  | 0, s, _ => by simp only [seqProd]; exact H.one_mem
  | n + 1, s, hx => by
    simp only [seqProd]
    exact H.mul_mem (hx s le_rfl (by omega))
      (seqProd_mem H x n (s + 1) (fun i hi1 hi2 => hx i (by omega) (by omega)))

theorem seqProd_conj (g : 𝔄) (x y : ℕ → 𝔄) (hxy : ∀ i, g * x i * g⁻¹ = y i) :
    ∀ (n s : ℕ), g * seqProd x s n * g⁻¹ = seqProd y s n
  | 0, s => by simp [seqProd]
  | n + 1, s => by
    simp only [seqProd]
    rw [← hxy s, ← seqProd_conj g x y hxy n (s + 1)]
    group

theorem seqProd_shift (δ : 𝔄) (x : ℕ → 𝔄) (hx : ∀ i, δ * x i * δ⁻¹ = x (i + 1)) :
    ∀ (n s : ℕ), δ * seqProd x s n * δ⁻¹ = seqProd x (s + 1) n
  | 0, s => by simp [seqProd]
  | n + 1, s => by
    simp only [seqProd]
    rw [← hx s, ← seqProd_shift δ x hx n (s + 1)]
    group

theorem seqProd_succ_right (x : ℕ → 𝔄) :
    ∀ (n s : ℕ), seqProd x s (n + 1) = seqProd x s n * x (s + n)
  | 0, s => by simp [seqProd]
  | n + 1, s => by
    rw [seqProd, seqProd_succ_right x n (s + 1), seqProd, mul_assoc,
      show s + 1 + n = s + (n + 1) by omega]

theorem core_aux {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {δ h : 𝔄}
    (hδperm : ∀ L ∈ I, conjBy δ L ∈ I) (hhperm : ∀ L ∈ I, conjBy h L ∈ I)
    {m : ℕ} (hhm : h ^ (2 ^ m) = 1) (hδh : δ * h = h * δ)
    (key : ∀ y ∈ (⨆ L ∈ I, L : Subgroup 𝔄), δ * y * δ⁻¹ = y →
      ∃ k : ℕ, (h * y * h⁻¹ * y⁻¹) ^ (2 ^ k) = 1)
    {L : Subgroup 𝔄} (hL : L ∈ I) {a : 𝔄} (ha : a ∈ L) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    {q : ℕ} (hxq : δ ^ (q + 1) * a * (δ ^ (q + 1))⁻¹ = a)
    (hdist : ∀ i, 0 < i → i ≤ q → conjBy (δ ^ i) L ≠ L)
    (hstab : ∀ j, conjBy (δ ^ (2 ^ m * j)) L = L → conjBy (δ ^ j) L = L) :
    h * a * h⁻¹ = a := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ → 𝔄, ∀ i, x i = δ ^ i * a * (δ ^ i)⁻¹ := ⟨_, fun _ => rfl⟩
  have hx0 : x 0 = a := by rw [hx]; simp
  have hxq' : x (q + 1) = a := by rw [hx]; exact hxq
  have hLi : ∀ i, conjBy (δ ^ i) L ∈ I := fun i => conjBy_pow_mem hδperm hL i
  have hxmem : ∀ i, x i ∈ conjBy (δ ^ i) L := by
    intro i
    rw [hx, mem_conjBy]
    have e : (δ ^ i)⁻¹ * (δ ^ i * a * (δ ^ i)⁻¹) * δ ^ i = a := by group
    rw [e]
    exact ha
  have hδx : ∀ i, δ * x i * δ⁻¹ = x (i + 1) := by
    intro i
    rw [hx, hx, pow_succ']
    group
  have hu_mem : ∀ H : Subgroup 𝔄, (∀ i, 1 ≤ i → i ≤ q → x i ∈ H) → seqProd x 1 q ∈ H :=
    fun H hH => seqProd_mem H x q 1 (fun i hi1 hi2 => hH i hi1 (by omega))
  have hu_fam : seqProd x 1 q ∈ famRest I L :=
    hu_mem _ (fun i hi1 hiq => le_famRest (hLi i) (hdist i hi1 hiq) (hxmem i))
  have hcomm_au : a * seqProd x 1 q = seqProd x 1 q * a :=
    (famRest_commute hI hL hu_fam ha).eq
  have hy_fixed : δ * (a * seqProd x 1 q) * δ⁻¹ = a * seqProd x 1 q := by
    have h1 : δ * seqProd x 0 (q + 1) * δ⁻¹ = seqProd x 1 (q + 1) :=
      seqProd_shift δ x hδx (q + 1) 0
    have h2 : seqProd x 0 (q + 1) = a * seqProd x 1 q := by
      simp [seqProd, hx0]
    have h3 : seqProd x 1 (q + 1) = seqProd x 1 q * a := by
      rw [seqProd_succ_right, show 1 + q = q + 1 by omega, hxq']
    calc δ * (a * seqProd x 1 q) * δ⁻¹ = seqProd x 1 (q + 1) := by rw [← h2]; exact h1
      _ = seqProd x 1 q * a := h3
      _ = a * seqProd x 1 q := hcomm_au.symm
  have hJ : ∀ L' ∈ I, L' ≤ (⨆ L ∈ I, L : Subgroup 𝔄) :=
    fun L' hL' => le_iSup₂ (f := fun (L : Subgroup 𝔄) (_ : L ∈ I) => L) L' hL'
  have hyJ : a * seqProd x 1 q ∈ (⨆ L ∈ I, L : Subgroup 𝔄) :=
    mul_mem (hJ L hL ha) (hu_mem _ (fun i _ _ => hJ _ (hLi i) (hxmem i)))
  obtain ⟨k, hk⟩ := key _ hyJ hy_fixed
  have hconj : h * seqProd x 1 q * h⁻¹ = seqProd (fun i => h * x i * h⁻¹) 1 q :=
    seqProd_conj h x _ (fun i => rfl) q 1
  have hha : ∀ {L' : Subgroup 𝔄} {b : 𝔄}, b ∈ L' → h * b * h⁻¹ ∈ conjBy h L' := by
    intro L' b hb
    rw [mem_conjBy]
    have e : h⁻¹ * (h * b * h⁻¹) * h = b := by group
    rw [e]
    exact hb
  have B1 : ∃ j, j ≤ q ∧ conjBy h L = conjBy (δ ^ j) L := by
    by_contra hcon
    push Not at hcon
    refine step_move hI hL (hhperm L hL) ?_ ha (hha ha) ha3 ha1 ?_ ?_ hk
    · have h1 := hcon 0 (Nat.zero_le _)
      simpa [conjBy_one] using h1
    · exact hu_mem _ (fun i hi1 hiq => le_famRest (hLi i)
        (fun heq => hcon i hiq heq.symm) (hxmem i))
    · rw [hconj]
      refine seqProd_mem _ _ q 1 (fun i hi1 hi2 => ?_)
      refine le_famRest (hhperm _ (hLi i)) ?_ (hha (hxmem i))
      intro heq
      exact hdist i hi1 (by omega) (conjBy_inj h heq)
  obtain ⟨j, -, hjeq⟩ := B1
  have hcomm_pow : ∀ i, h * δ ^ i = δ ^ i * h :=
    fun i => ((Commute.pow_left (show Commute δ h from hδh) i).eq).symm
  have h1 : ∀ i, conjBy h (conjBy (δ ^ i) L) = conjBy (δ ^ (i + j)) L := by
    intro i
    rw [← conjBy_mul, hcomm_pow i, conjBy_mul, hjeq, ← conjBy_mul, pow_add]
  have h2 : ∀ n : ℕ, conjBy (h ^ n) L = conjBy (δ ^ (n * j)) L := by
    intro n
    induction n with
    | zero => simp [conjBy_one]
    | succ n ih => rw [pow_succ', conjBy_mul, ih, h1, add_mul, one_mul]
  have h3 : conjBy (δ ^ (2 ^ m * j)) L = L := by
    have h4 := h2 (2 ^ m)
    rw [hhm, conjBy_one] at h4
    exact h4.symm
  have h4 : conjBy (δ ^ j) L = L := hstab j h3
  have h5 : conjBy h L = L := by rw [hjeq, h4]
  have h6 : ∀ i, conjBy h (conjBy (δ ^ i) L) = conjBy (δ ^ i) L := by
    intro i
    rw [h1, pow_add, conjBy_mul, h4]
  refine step_stay hI hL ha ?_ ha3 ha1 hu_fam ?_ hk
  · have h7 := hha ha
    rwa [h5] at h7
  · rw [hconj]
    refine seqProd_mem _ _ q 1 (fun i hi1 hi2 => ?_)
    refine le_famRest (hLi i) (hdist i hi1 (by omega)) ?_
    have h7 := hha (hxmem i)
    rwa [h6] at h7

end Sigma3Core

variable {𝔄 : Type*} [Group 𝔄] [Finite 𝔄]

theorem IsSigma3Family.core {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {δ h : 𝔄}
    (hδperm : ∀ L ∈ I, conjBy δ L ∈ I) (hhperm : ∀ L ∈ I, conjBy h L ∈ I)
    (hδp : δ ^ p = 1) {m : ℕ} (hhm : h ^ (2 ^ m) = 1) (hδh : δ * h = h * δ)
    (key : ∀ y ∈ (⨆ L ∈ I, L : Subgroup 𝔄), δ * y * δ⁻¹ = y →
      ∃ k : ℕ, (h * y * h⁻¹ * y⁻¹) ^ (2 ^ k) = 1)
    {L : Subgroup 𝔄} (hL : L ∈ I) {a : 𝔄} (ha : a ∈ L) (ha3 : a ^ 3 = 1) :
    h * a * h⁻¹ = a := by
  by_cases ha1 : a = 1
  · subst ha1
    simp
  by_cases hA : conjBy δ L = L
  ·
    refine Sigma3Core.core_aux hI hδperm hhperm hhm hδh key hL ha ha3 ha1 (q := 0) ?_ ?_ ?_
    · simp only [zero_add, pow_one]
      have hδa : δ * a * δ⁻¹ ∈ L := by
        have h0 : δ * a * δ⁻¹ ∈ conjBy δ L := by
          rw [mem_conjBy]
          have e : δ⁻¹ * (δ * a * δ⁻¹) * δ = a := by group
          rw [e]
          exact ha
        rwa [hA] at h0
      have hδa3 : (δ * a * δ⁻¹) ^ 3 = 1 := by rw [conj_pow, ha3]; group
      have hδa1 : δ * a * δ⁻¹ ≠ 1 := fun h1 => ha1 ((Sigma3Core.conj_eq_one_iff δ a).1 h1)
      rcases Sigma3Core.order_three_cases hI hL ha hδa ha3 ha1 hδa3 hδa1 with h1 | h1
      · exact h1
      · exfalso
        have h2 : δ ^ 2 * a * (δ ^ 2)⁻¹ = a := by
          have e1 : δ ^ 2 * a * (δ ^ 2)⁻¹ = δ * (δ * a * δ⁻¹) * δ⁻¹ := by
            rw [pow_two]
            simp only [mul_inv_rev, mul_assoc]
          have e2 : δ * a⁻¹ * δ⁻¹ = (δ * a * δ⁻¹)⁻¹ := by group
          rw [e1, h1, e2, h1, inv_inv]
        have hc2 : Commute (δ ^ 2) a := by
          show δ ^ 2 * a = a * δ ^ 2
          calc δ ^ 2 * a = (δ ^ 2 * a * (δ ^ 2)⁻¹) * δ ^ 2 := by group
            _ = a * δ ^ 2 := by rw [h2]
        obtain ⟨c, hc⟩ := hp.eq_two_or_odd'.resolve_left hp2
        have hδ : (δ ^ 2) ^ (c + 1) = δ := by
          rw [← pow_mul, show 2 * (c + 1) = p + 1 by omega, pow_succ, hδp, one_mul]
        have hcδ : Commute δ a := by
          have h3 := hc2.pow_left (c + 1)
          rwa [hδ] at h3
        have h3 : δ * a * δ⁻¹ = a := by rw [hcδ.eq, mul_inv_cancel_right]
        rw [h3] at h1
        have h4 : a * a = 1 := by
          calc a * a = a * a⁻¹ := congrArg (a * ·) h1
            _ = 1 := mul_inv_cancel a
        apply ha1
        calc a = a * (a * a) := by rw [h4, mul_one]
          _ = a ^ 3 := (pow_three a).symm
          _ = 1 := ha3
    · intro i hi1 hi2
      omega
    · intro j _
      exact Sigma3Core.conjBy_pow_stable hA j
  ·
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    refine Sigma3Core.core_aux hI hδperm hhperm hhm hδh key hL ha ha3 ha1 (q := q) ?_ ?_ ?_
    · rw [hδp]
      group
    · intro i hi0 hiq hcon
      have h1 := Sigma3Core.dvd_of_conjBy_pow_eq hp hδp hA hcon
      have h2 := Nat.le_of_dvd hi0 h1
      omega
    · intro j hj
      have hdvd := Sigma3Core.dvd_of_conjBy_pow_eq hp hδp hA hj
      have hpj : (q + 1) ∣ j := by
        rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
            (hp.dvd_of_dvd_pow h1)) hp2
        · exact h1
      obtain ⟨c, hc⟩ := hpj
      rw [hc, pow_mul, hδp, one_pow, Sigma3Core.conjBy_one]

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3
