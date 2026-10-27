module

public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusSylowFiveSupport
public import CFSG.CharacterTheory.BrauerLinearThree.TenCentralizer

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

namespace TrivialCoreTorus

theorem zpowers_cover_of_sigma {G : Type*} [Group G] (W P : Subgroup G)
    (σ : G → Equiv.Perm (Fin 5))
    (hσmul : ∀ x ∈ P, ∀ z ∈ P, σ (x * z) = σ x * σ z)
    (hσker : ∀ x ∈ P, σ x = 1 ↔ x ∈ W)
    {w y : G} {c : Equiv.Perm (Fin 5)}
    (hσc : ∀ x ∈ P, σ x ∈ Subgroup.zpowers c) (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1)
    (hwP : w ∈ P) (hwW : w ∈ W) (hword : orderOf w = 5)
    (hWP : ∀ x ∈ W, x ∈ P → x ∈ Subgroup.zpowers w)
    (hyP : y ∈ P) (hσy : σ y = c) (hy5 : y ^ 5 = 1) (hwy : w * y = y * w) :
    (∀ z ∈ P, z ^ 5 = 1 → z ≠ 1 → Subgroup.zpowers z = Subgroup.zpowers w ∨
      ∃ a : ZMod 5, Subgroup.zpowers z = Subgroup.zpowers (y * w ^ a.val)) ∧
    (∀ a : ZMod 5, Subgroup.zpowers (y * w ^ a.val) ≠ Subgroup.zpowers w) ∧
    (∀ a b : ZMod 5, Subgroup.zpowers (y * w ^ a.val) = Subgroup.zpowers (y * w ^ b.val) →
      a = b) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hw5 : w ^ 5 = 1 := hword ▸ pow_orderOf_eq_one w
  have hσ1 : σ 1 = 1 := by
    have h := hσmul 1 P.one_mem 1 P.one_mem
    rw [one_mul] at h
    exact (mul_eq_left.mp h.symm)
  have hσpow : ∀ x ∈ P, ∀ n : ℕ, σ (x ^ n) = σ x ^ n := by
    intro x hx n
    induction n with
    | zero => rw [pow_zero, pow_zero, hσ1]
    | succ n ih => rw [pow_succ, hσmul _ (P.pow_mem hx n) _ hx, ih, pow_succ]
  have hσinv : ∀ x ∈ P, σ x⁻¹ = (σ x)⁻¹ := by
    intro x hx
    have h := hσmul x⁻¹ (P.inv_mem hx) x hx
    rw [inv_mul_cancel, hσ1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hwaP : ∀ a : ℕ, w ^ a ∈ P := fun a => P.pow_mem hwP a
  have hwaW : ∀ a : ℕ, w ^ a ∈ W := fun a => W.pow_mem hwW a
  have hσw : ∀ a : ℕ, σ (w ^ a) = 1 := fun a => (hσker _ (hwaP a)).mpr (hwaW a)
  have hfP : ∀ a : ℕ, y * w ^ a ∈ P := fun a => P.mul_mem hyP (hwaP a)
  have hσf : ∀ a : ℕ, σ (y * w ^ a) = c := fun a => by
    rw [hσmul _ hyP _ (hwaP a), hσy, hσw, mul_one]
  have hf5 : ∀ a : ℕ, (y * w ^ a) ^ 5 = 1 := by
    intro a
    rw [((show Commute w y from hwy).symm.pow_right a).mul_pow, hy5, one_mul, ← pow_mul,
      mul_comm, pow_mul, hw5, one_pow]
  have hcord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hmod4 : ∀ n : ℕ, n % 5 ≠ 0 → n ^ 4 % 5 = 1 ∧ n ^ 3 % 5 ≠ 0 := by
    intro n hn
    rw [Nat.pow_mod, Nat.pow_mod n 3]
    rcases (show n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 by omega) with h | h | h | h <;>
      rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro z hzP hz5 hz1
    by_cases hzW : z ∈ W
    · left
      obtain ⟨a, rfl⟩ := exists_eq_pow_val_of_mem_zpowers hw5 (hWP z hzW hzP)
      have ha : a.val % 5 ≠ 0 := by
        intro h0
        have h0' : a.val = 0 := by
          have := ZMod.val_lt a
          omega
        rw [h0', pow_zero] at hz1
        exact hz1 rfl
      exact zpowers_pow_eq hw5 ha
    · right
      have hσz : σ z ≠ 1 := fun h => hzW ((hσker z hzP).mp h)
      obtain ⟨i, hi⟩ := exists_eq_pow_val_of_mem_zpowers hc5 (hσc z hzP)
      have hi0 : i.val % 5 ≠ 0 := by
        intro h0
        have h0' : i.val = 0 := by
          have := ZMod.val_lt i
          omega
        rw [h0', pow_zero] at hi
        exact hσz hi
      obtain ⟨h4, h3⟩ := hmod4 i.val hi0
      have hσx : σ (z ^ (i.val ^ 3)) = c := by
        rw [hσpow z hzP, hi, ← pow_mul, show i.val * i.val ^ 3 = i.val ^ 4 by ring,
          pow_eq_pow_mod _ hc5, h4, pow_one]
      have hxP : z ^ (i.val ^ 3) ∈ P := P.pow_mem hzP _
      have hyxP : y⁻¹ * z ^ (i.val ^ 3) ∈ P := P.mul_mem (P.inv_mem hyP) hxP
      have hyx : y⁻¹ * z ^ (i.val ^ 3) ∈ W := by
        rw [← hσker _ hyxP, hσmul _ (P.inv_mem hyP) _ hxP, hσinv y hyP, hσy, hσx, inv_mul_cancel]
      obtain ⟨a, ha⟩ := exists_eq_pow_val_of_mem_zpowers hw5 (hWP _ hyx hyxP)
      refine ⟨a, ?_⟩
      rw [← zpowers_pow_eq hz5 h3, ← ha, mul_inv_cancel_left]
  · intro a h
    have hmem : y * w ^ a.val ∈ Subgroup.zpowers w := h ▸ Subgroup.mem_zpowers _
    have hyW : y ∈ W := by
      have h1 : y = (y * w ^ a.val) * (w ^ a.val)⁻¹ := by group
      rw [h1]
      exact W.mul_mem ((Subgroup.zpowers_le.mpr hwW) hmem) (W.inv_mem (hwaW _))
    exact hc1 (hσy ▸ (hσker y hyP).mpr hyW)
  · intro a b hab
    have hmem : y * w ^ b.val ∈ Subgroup.zpowers (y * w ^ a.val) :=
      hab ▸ Subgroup.mem_zpowers _
    obtain ⟨j, hj⟩ := exists_eq_pow_val_of_mem_zpowers (hf5 a.val) hmem
    have hcj : c ^ 1 = c ^ j.val := by
      have h := congrArg σ hj
      rw [hσf, hσpow _ (hfP _), hσf] at h
      rw [pow_one]
      exact h
    have hj1 : j.val = 1 := by
      have h := (pow_eq_pow_iff_modEq (x := c)).mp hcj
      rw [hcord] at h
      have := ZMod.val_lt j
      unfold Nat.ModEq at h
      omega
    rw [hj1, pow_one] at hj
    have hwab : w ^ b.val = w ^ a.val := mul_left_cancel hj
    have h := (pow_eq_pow_iff_modEq (x := w)).mp hwab
    rw [hword] at h
    unfold Nat.ModEq at h
    have hav := ZMod.val_lt a
    have hbv := ZMod.val_lt b
    exact ZMod.val_injective 5 (by omega)

theorem exists_lift_data {G : Type} [Group G] [Finite G] (W H P : Subgroup G)
    (σ : G → Equiv.Perm (Fin 5))
    (hσmul : ∀ x ∈ H, ∀ z ∈ H, σ (x * z) = σ x * σ z)
    (hσker : ∀ x ∈ H, σ x = 1 ↔ x ∈ W)
    (hσsurj : ∀ d, ∃ x ∈ H, σ x = d)
    (hσodd : ∀ x ∈ H, Equiv.Perm.sign (σ x) = -1 → ∀ v ∈ W, x * v * x⁻¹ = v⁻¹)
    (hW15 : Nat.card W = 15) (hPH : P ≤ H) (hP : Nat.card P = 25)
    (hPW : ∀ x ∈ P, ∀ v ∈ W, x * v = v * x)
    {w : G} (hwP : w ∈ P) (hwW : w ∈ W) (hword : orderOf w = 5)
    (hW5 : ∀ x ∈ W, x ^ 5 = 1 → x ∈ Subgroup.zpowers w) :
    ∃ (y h : G) (c : Equiv.Perm (Fin 5)) (k : ℕ),
      y ∈ P ∧ σ y = c ∧ c ^ 5 = 1 ∧ c ≠ 1 ∧ (∀ x ∈ P, σ x ∈ Subgroup.zpowers c) ∧
      y ^ 5 = 1 ∧ h ∈ Subgroup.normalizer (P : Set G) ∧ h * w * h⁻¹ = w⁻¹ ∧
      h * y * h⁻¹ = y ^ 2 * w ^ k := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hw5 : w ^ 5 = 1 := hword ▸ pow_orderOf_eq_one w
  have hσ1 : σ 1 = 1 := by
    have h := hσmul 1 H.one_mem 1 H.one_mem
    rw [one_mul] at h
    exact (mul_eq_left.mp h.symm)
  have hσpow : ∀ x ∈ H, ∀ n : ℕ, σ (x ^ n) = σ x ^ n := by
    intro x hx n
    induction n with
    | zero => rw [pow_zero, pow_zero, hσ1]
    | succ n ih => rw [pow_succ, hσmul _ (H.pow_mem hx n) _ hx, ih, pow_succ]
  have hσinv : ∀ x ∈ H, σ x⁻¹ = (σ x)⁻¹ := by
    intro x hx
    have h := hσmul x⁻¹ (H.inv_mem hx) x hx
    rw [inv_mul_cancel, hσ1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hσconj : ∀ g ∈ H, ∀ x ∈ H, σ (g * x * g⁻¹) = σ g * σ x * (σ g)⁻¹ := by
    intro g hg x hx
    rw [hσmul _ (H.mul_mem hg hx) _ (H.inv_mem hg), hσmul _ hg _ hx, hσinv g hg]
  have hP25 : ∀ x ∈ P, x ^ 25 = 1 := by
    intro x hx
    have h := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
    rw [hP] at h
    exact congrArg Subtype.val h
  have hW15' : ∀ v ∈ W, v ^ 15 = 1 := by
    intro v hv
    have h := pow_card_eq_one' (G := W) (x := ⟨v, hv⟩)
    rw [hW15] at h
    exact congrArg Subtype.val h
  have hWP5 : ∀ v ∈ W, v ∈ P → v ∈ Subgroup.zpowers w := fun v hv hvP =>
    hW5 v hv (pow_five_eq_one_of_pow_eq_one (hP25 v hvP) (hW15' v hv) (by norm_num))
  have hzwP : Subgroup.zpowers w ≤ P := Subgroup.zpowers_le.mpr hwP
  obtain ⟨y, hyP, hyW⟩ : ∃ y ∈ P, y ∉ W := by
    by_contra! hall
    have hle : P ≤ Subgroup.zpowers w := fun x hx => hWP5 x (hall x hx) hx
    have h := Subgroup.card_le_of_le hle
    rw [hP, Nat.card_zpowers, hword] at h
    omega
  have hyH := hPH hyP
  have hc1 : σ y ≠ 1 := fun h => hyW ((hσker y hyH).mp h)
  have hc5 : σ y ^ 5 = 1 := by
    have h25 : σ y ^ 25 = 1 := by rw [← hσpow y hyH, hP25 y hyP, hσ1]
    have h120 : σ y ^ 120 = 1 := by
      have h := pow_card_eq_one' (G := Equiv.Perm (Fin 5)) (x := σ y)
      rwa [Nat.card_perm, Nat.card_fin, show (5 : ℕ).factorial = 120 from rfl] at h
    exact pow_five_eq_one_of_pow_eq_one h25 h120 (by norm_num)
  have hcord : orderOf (σ y) = 5 := orderOf_eq_prime hc5 hc1
  let σP : P →* Equiv.Perm (Fin 5) :=
    { toFun := fun x => σ x
      map_one' := hσ1
      map_mul' := fun x z => hσmul x (hPH x.2) z (hPH z.2) }
  have hrange : σP.range = Subgroup.zpowers (σ y) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨y, hyP⟩, rfl⟩
    · rw [Nat.card_zpowers, hcord]
      have h1 : Nat.card σP.range ∣ 25 := hP ▸ Subgroup.card_range_dvd σP
      have h2 : Nat.card σP.range ∣ 120 := by
        have h := Subgroup.card_subgroup_dvd_card σP.range
        rwa [Nat.card_perm, Nat.card_fin, show (5 : ℕ).factorial = 120 from rfl] at h
      have h3 := Nat.dvd_gcd h1 h2
      rw [(by norm_num : Nat.gcd 25 120 = 5)] at h3
      exact Nat.le_of_dvd (by norm_num) h3
  have hσc : ∀ x ∈ P, σ x ∈ Subgroup.zpowers (σ y) := fun x hx => hrange ▸ ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨d, hdc, hdsign⟩ := exists_odd_perm_conj_eq_sq (σ y) hc5 hc1
  obtain ⟨h, hhH, hσh⟩ := hσsurj d
  have hinvW : ∀ v ∈ W, h * v * h⁻¹ = v⁻¹ := hσodd h hhH (by rw [hσh]; exact hdsign)
  have hconjP : ∀ x ∈ P, h * x * h⁻¹ ∈ P := by
    intro x hx
    have hxH := hPH hx
    have hhxH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH hxH) (H.inv_mem hhH)
    have hσhx : σ (h * x * h⁻¹) ∈ σP.range := by
      rw [hrange, hσconj h hhH x hxH, hσh]
      obtain ⟨a, ha⟩ := exists_eq_pow_val_of_mem_zpowers hc5 (hσc x hx)
      rw [ha, ← conj_pow, hdc]
      exact Subgroup.pow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2) _
    obtain ⟨⟨x', hx'P⟩, hx'⟩ := hσhx
    have hx' : σ x' = σ (h * x * h⁻¹) := hx'
    have hx'H := hPH hx'P
    have hvH : x'⁻¹ * (h * x * h⁻¹) ∈ H := H.mul_mem (H.inv_mem hx'H) hhxH
    have hvW : x'⁻¹ * (h * x * h⁻¹) ∈ W := by
      rw [← hσker _ hvH, hσmul _ (H.inv_mem hx'H) _ hhxH, hσinv x' hx'H, hx', inv_mul_cancel]
    have hxv : h * x * h⁻¹ = x' * (x'⁻¹ * (h * x * h⁻¹)) := by rw [mul_inv_cancel_left]
    have hv25 : (x'⁻¹ * (h * x * h⁻¹)) ^ 25 = 1 := by
      have h1 : (h * x * h⁻¹) ^ 25 = 1 := by rw [conj_pow, hP25 x hx, mul_one, mul_inv_cancel]
      rw [hxv, (show Commute x' (x'⁻¹ * (h * x * h⁻¹)) from hPW x' hx'P _ hvW).mul_pow,
        hP25 x' hx'P, one_mul] at h1
      exact h1
    have hv5 := pow_five_eq_one_of_pow_eq_one hv25 (hW15' _ hvW) (by norm_num)
    rw [hxv]
    exact P.mul_mem hx'P (hzwP (hW5 _ hvW hv5))
  have hhN : h ∈ Subgroup.normalizer (P : Set G) := mem_normalizer_of_forall_conj_mem hconjP
  have hhyP := hconjP y hyP
  have hy2P : y ^ 2 ∈ P := P.pow_mem hyP 2
  have hv₀P : (y ^ 2)⁻¹ * (h * y * h⁻¹) ∈ P := P.mul_mem (P.inv_mem hy2P) hhyP
  have hv₀W : (y ^ 2)⁻¹ * (h * y * h⁻¹) ∈ W := by
    rw [← hσker _ (hPH hv₀P), hσmul _ (H.inv_mem (hPH hy2P)) _ (hPH hhyP),
      hσinv _ (hPH hy2P), hσpow y hyH, hσconj h hhH y hyH, hσh, hdc, inv_mul_cancel]
  obtain ⟨a, ha⟩ := exists_eq_pow_val_of_mem_zpowers hw5 (hWP5 _ hv₀W hv₀P)
  have hhy : h * y * h⁻¹ = y ^ 2 * w ^ a.val := by rw [← ha, mul_inv_cancel_left]
  have hy5W : y ^ 5 ∈ W := (hσker _ (H.pow_mem hyH 5)).mp (by rw [hσpow y hyH, hc5])
  have h1 : h * y ^ 5 * h⁻¹ = (y ^ 5)⁻¹ := hinvW _ hy5W
  have hcomm : Commute (y ^ 2) (w ^ a.val) :=
    (show Commute y (w ^ a.val) from hPW y hyP _ (W.pow_mem hwW _)).pow_left 2
  have hw' : (w ^ a.val) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw5, one_pow]
  have hy' : (y ^ 2) ^ 5 = y ^ 10 := by rw [← pow_mul]
  have h2 : h * y ^ 5 * h⁻¹ = y ^ 10 := by
    rw [← conj_pow, hhy, hcomm.mul_pow, hw', mul_one, hy']
  have hy15 : y ^ 15 = 1 := by
    have h3 : (y ^ 5)⁻¹ = y ^ 10 := h1.symm.trans h2
    calc y ^ 15 = y ^ 5 * y ^ 10 := by rw [← pow_add]
      _ = y ^ 5 * (y ^ 5)⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel _
  have hy5 : y ^ 5 = 1 := pow_five_eq_one_of_pow_eq_one (hP25 y hyP) hy15 (by norm_num)
  exact ⟨y, h, σ y, a.val, hyP, rfl, hc5, hc1, hσc, hy5, hhN, hinvW w hwW, hhy⟩


end TrivialCoreTorus

open TrivialCoreTorus

theorem false_of_cyclic_fifteen_torus_sylow_five {G : Type} [Group G] [Finite G]
    (W : Subgroup G) (hWcyc : IsCyclic W) (hW15 : Nat.card W = 15)
    (hCU : ∀ U : Subgroup G, U ≤ W → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) = Subgroup.centralizer (W : Set G))
    (hOK : (CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))).map
      (Subgroup.centralizer (W : Set G)).subtype = W)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hinv : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hA5 : Nonempty ((Subgroup.centralizer (W : Set G) ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))) ≃* alternatingGroup (Fin 5)))
    (hdih : ∃ P : Sylow 2 (Subgroup.normalizer (W : Set G)),
      Nonempty ((P : Subgroup (Subgroup.normalizer (W : Set G))) ≃* DihedralGroup 4))
    (hK : Nat.card (Subgroup.centralizer (W : Set G)) = 900)
    (hH : Nat.card (Subgroup.normalizer (W : Set G)) = 1800)
    (M : ℕ) (hG : Nat.card G = 1800 * M) (hM : M % 5 = 4) : False := by
  set K := Subgroup.centralizer (W : Set G) with hKdef
  set H := Subgroup.normalizer (W : Set G) with hHdef
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  obtain ⟨σH, hsurj, hker, hσK⟩ :=
    exists_perm_hom_of_torus W (by rw [hW15]; decide) hWab hKH hOK hA5 hdih
  let σ : G → Equiv.Perm (Fin 5) := fun x => if hx : x ∈ H then σH ⟨x, hx⟩ else 1
  have hσ : ∀ x (hx : x ∈ H), σ x = σH ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hσmul : ∀ x ∈ H, ∀ z ∈ H, σ (x * z) = σ x * σ z := by
    intro x hx z hz
    rw [hσ _ (H.mul_mem hx hz), hσ x hx, hσ z hz, ← map_mul]
    rfl
  have hσker : ∀ x ∈ H, σ x = 1 ↔ x ∈ W := fun x hx => by
    rw [hσ x hx]
    exact hker ⟨x, hx⟩
  have hσsurj : ∀ d, ∃ x ∈ H, σ x = d := by
    intro d
    obtain ⟨x, rfl⟩ := hsurj d
    exact ⟨x, x.2, hσ x x.2⟩
  have hσodd : ∀ x ∈ H, Equiv.Perm.sign (σ x) = -1 → ∀ v ∈ W, x * v * x⁻¹ = v⁻¹ := by
    intro x hx hsign v hv
    refine hinv x hx (fun hxK => ?_) v hv
    have h1 := (hσK ⟨x, hx⟩).mp hxK
    rw [Equiv.Perm.mem_alternatingGroup, ← hσ x hx, hsign] at h1
    exact absurd h1 (by decide)
  obtain ⟨P, w, hPK, hP, hwW, hwP, hword, hW5⟩ := exists_sylow_five_of_torus W hWcyc hW15 hK
  have hPH : P ≤ H := hPK.trans hKH'
  have hPW : ∀ x ∈ P, ∀ v ∈ W, x * v = v * x := fun x hx v hv =>
    (Subgroup.mem_centralizer_iff.mp (hPK hx) v hv).symm
  obtain ⟨y, h, c, k, hyP, hσy, hc5, hc1, hσc, hy5, hhN, hhw, hhy⟩ :=
    exists_lift_data W H P σ hσmul hσker hσsurj hσodd hW15 hPH hP hPW hwP hwW hword hW5
  have hw5 : w ^ 5 = 1 := hword ▸ pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hword
    exact absurd hword (by norm_num)
  have hP25 : ∀ x ∈ P, x ^ 25 = 1 := by
    intro x hx
    have h1 := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
    rw [hP] at h1
    exact congrArg Subtype.val h1
  have hW15' : ∀ v ∈ W, v ^ 15 = 1 := by
    intro v hv
    have h1 := pow_card_eq_one' (G := W) (x := ⟨v, hv⟩)
    rw [hW15] at h1
    exact congrArg Subtype.val h1
  have hWP : ∀ x ∈ W, x ∈ P → x ∈ Subgroup.zpowers w := fun x hx hxP =>
    hW5 x hx (pow_five_eq_one_of_pow_eq_one (hP25 x hxP) (hW15' x hx) (by norm_num))
  obtain ⟨hcover, hne, hinj⟩ := zpowers_cover_of_sigma W P σ
    (fun x hx z hz => hσmul x (hPH hx) z (hPH hz)) (fun x hx => hσker x (hPH hx))
    hσc hc5 hc1 hwP hwW hword hWP hyP hσy hy5 (hPW y hyP w hwW).symm
  have hcover' : ∀ n ∈ Subgroup.normalizer (P : Set G),
      Subgroup.zpowers (n * w * n⁻¹) = Subgroup.zpowers w ∨
        ∃ a : ZMod 5, Subgroup.zpowers (n * w * n⁻¹) = Subgroup.zpowers (y * w ^ a.val) := by
    intro n hn
    apply hcover
    · exact (Subgroup.mem_normalizer_iff.mp hn w).mp hwP
    · rw [conj_pow, hw5, mul_one, mul_inv_cancel]
    · intro h1
      apply hw1
      have h2 : w = n⁻¹ * (n * w * n⁻¹) * n := by group
      rw [h2, h1, mul_one, inv_mul_cancel]
  have hCK : ∀ x ∈ W, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = K := by
    intro x hx hx1
    have h1 := hCU (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hx)
      (by rwa [Ne, Subgroup.zpowers_eq_bot])
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h1
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set G), g ∈ H →
      g * w * g⁻¹ ∈ Subgroup.zpowers w := fun g hg hgH =>
    hWP _ ((Subgroup.mem_normalizer_iff.mp hgH w).mp hwW)
      ((Subgroup.mem_normalizer_iff.mp hg w).mp hwP)
  have hstab : ∀ n ∈ Subgroup.normalizer (P : Set G),
      n ∈ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) ↔ n ∈ H := by
    intro n hn
    constructor
    · intro hnw
      have h1 : n * w * n⁻¹ ∈ W := (Subgroup.zpowers_le.mpr hwW)
        ((Subgroup.mem_normalizer_iff.mp hnw w).mp (Subgroup.mem_zpowers w))
      exact BrauerLinearThree.mem_normalizer_of_conj_mem hOK hCK hwW hw1 h1
    · intro hnH
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact conj_mem_zpowers_of_conj_mem (hconj n hn hnH)
      · intro hx
        have h1 := conj_mem_zpowers_of_conj_mem
          (hconj n⁻¹ (Subgroup.inv_mem _ hn) (H.inv_mem hnH)) hx
        rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at h1
  have h1 := ncard_conjOrbit_mod_five H P (Subgroup.zpowers w) hPH hP hH M hG (by omega) hstab
  have h2 := ncard_conjOrbit_mod_five_ne_four (Subgroup.normalizer (P : Set G)) hw5 hy5
    (hPW y hyP w hwW).symm hcover' hne hinj hhN hhw hhy
  omega

end CFSG.Semidihedral.Principal
