module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchClassify

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

section BitProd

variable {T : Type*} [Group T]

@[expose] def bitProd (n : ℕ) (ρ : ℕ → T) (v : ℕ) : T :=
  ((List.range n).filter (v.testBit ·)).foldl (fun x i => x * ρ i) 1

theorem bitProd_succ (n : ℕ) (ρ : ℕ → T) (v : ℕ) :
    bitProd (n + 1) ρ v = bitProd n ρ v * (if v.testBit n then ρ n else 1) := by
  unfold bitProd
  rw [List.range_succ, List.filter_append, List.foldl_append]
  by_cases h : v.testBit n
  · simp [h]
  · simp [h]

theorem bitProd_zero_right (n : ℕ) (ρ : ℕ → T) : bitProd n ρ 0 = 1 := by
  induction n with
  | zero => simp [bitProd]
  | succ n ih => rw [bitProd_succ, ih, Nat.zero_testBit]; simp

theorem commute_bitProd {n : ℕ} {ρ : ℕ → T} {t : T} (ht : ∀ i, i < n → t * ρ i = ρ i * t)
    (v : ℕ) : t * bitProd n ρ v = bitProd n ρ v * t := by
  induction n with
  | zero => simp [bitProd]
  | succ n ih =>
    rw [bitProd_succ]
    have h1 := ih fun i hi => ht i (by omega)
    have h2 : t * (if v.testBit n then ρ n else 1) = (if v.testBit n then ρ n else 1) * t := by
      split
      · exact ht n (by omega)
      · simp
    calc t * (bitProd n ρ v * (if v.testBit n then ρ n else 1)) =
        t * bitProd n ρ v * (if v.testBit n then ρ n else 1) := (mul_assoc _ _ _).symm
      _ = bitProd n ρ v * (t * (if v.testBit n then ρ n else 1)) := by rw [h1, mul_assoc]
      _ = bitProd n ρ v * (if v.testBit n then ρ n else 1) * t := by rw [h2, mul_assoc]

theorem bitProd_xor {n : ℕ} {ρ : ℕ → T} (h2 : ∀ i, i < n → ρ i * ρ i = 1)
    (hc : ∀ i j, i < n → j < n → ρ i * ρ j = ρ j * ρ i) (v w : ℕ) :
    bitProd n ρ (v ^^^ w) = bitProd n ρ v * bitProd n ρ w := by
  induction n with
  | zero => simp [bitProd]
  | succ n ih =>
    have ih' := ih (fun i hi => h2 i (by omega)) (fun i j hi hj => hc i j (by omega) (by omega))
    have hQ : (if (v ^^^ w).testBit n then ρ n else 1) =
        (if v.testBit n then ρ n else 1) * (if w.testBit n then ρ n else 1) := by
      by_cases ha : v.testBit n <;> by_cases hb : w.testBit n <;>
        simp [Nat.testBit_xor, ha, hb, h2 n (by omega)]
    have hB : (if v.testBit n then ρ n else 1) * bitProd n ρ w =
        bitProd n ρ w * (if v.testBit n then ρ n else 1) := by
      split
      · exact commute_bitProd (fun i hi => hc n i (by omega) (by omega)) w
      · simp
    rw [bitProd_succ, bitProd_succ, bitProd_succ, ih', hQ]
    calc bitProd n ρ v * bitProd n ρ w *
          ((if v.testBit n then ρ n else 1) * (if w.testBit n then ρ n else 1)) =
        bitProd n ρ v * ((if v.testBit n then ρ n else 1) * bitProd n ρ w) *
          (if w.testBit n then ρ n else 1) := by rw [hB]; group
      _ = _ := by group

theorem conj_bitProd {n : ℕ} {ρ : ℕ → T} (h2 : ∀ i, i < n → ρ i * ρ i = 1)
    (hc : ∀ i j, i < n → j < n → ρ i * ρ j = ρ j * ρ i) {t : T} {c : ℕ → ℕ}
    (ht : ∀ i, i < n → t * ρ i * t⁻¹ = bitProd n ρ (c i)) (v : ℕ) :
    t * bitProd n ρ v * t⁻¹ = bitProd n ρ (xorBits n c v) := by
  have key : ∀ m, m ≤ n → t * bitProd m ρ v * t⁻¹ = bitProd n ρ (xorBits m c v) := by
    intro m
    induction m with
    | zero => intro _; rw [xorBits_zero, bitProd_zero_right]; simp [bitProd]
    | succ m ih =>
      intro hm
      rw [bitProd_succ, xorBits_succ, bitProd_xor h2 hc, ← ih (by omega)]
      by_cases hb : v.testBit m = true
      · rw [ite_eq_left hb, ite_eq_left hb, ← ht m (by omega)]; group
      · rw [ite_eq_right hb, ite_eq_right hb, bitProd_zero_right]; group
  exact key n le_rfl

end BitProd

theorem wprodN_zero (mul : ℕ → ℕ → ℕ) (m : ℕ) (ys : ℕ → ℕ) : wprodN mul m ys 0 = 0 := by
  induction m with
  | zero => simp [wprodN]
  | succ m ih => rw [wprodN_succ, ih]; simp

namespace AutFacts

open KFacts

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {D : AutData}
  (hF : AutFacts N mul inv D) (Φ : CodeIso H N mul)

include hF in
theorem g_nf {x : ℕ} (hx : x < N) :
    Φ.g x = Φ.g (wprodN mul D.q D.g (D.nfE x)) * el Φ D.K (D.nfA x) := by
  obtain ⟨-, hA, hnf⟩ := hF.nf x hx
  apply Φ.inj
  rw [Φ.f_g hx, Φ.map_mul, Φ.f_g (Φ.g_wprodN hF.h0 hF.g_lt _).1, hF.kf.f_el Φ hA]
  exact hnf

include hF in
theorem nf_unique (hN : N = 2 ^ D.q * 2 ^ D.K.n) {e e' a a' : ℕ} (he : e < 2 ^ D.q)
    (he' : e' < 2 ^ D.q) (ha : a < 2 ^ D.K.n) (ha' : a' < 2 ^ D.K.n)
    (h : Φ.g (wprodN mul D.q D.g e) * el Φ D.K a = Φ.g (wprodN mul D.q D.g e') * el Φ D.K a') :
    e = e' ∧ a = a' := by
  have := Φ.finite
  let p : Fin (2 ^ D.q) × Fin (2 ^ D.K.n) → H := fun z =>
    Φ.g (wprodN mul D.q D.g z.1) * el Φ D.K z.2
  have hsurj : Function.Surjective p := by
    intro x
    obtain ⟨hE, hA, -⟩ := hF.nf _ (Φ.lt x)
    refine ⟨(⟨_, hE⟩, ⟨_, hA⟩), ?_⟩
    simp only [p]
    rw [← hF.g_nf Φ (Φ.lt x), Φ.g_f]
  have hcard : Nat.card (Fin (2 ^ D.q) × Fin (2 ^ D.K.n)) = Nat.card H := by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_fin, Φ.card_univ, hN]
  have hinj := (hsurj.bijective_of_nat_card_le hcard.le).1
  have hp := @hinj (⟨e, he⟩, ⟨a, ha⟩) (⟨e', he'⟩, ⟨a', ha'⟩) h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at hp
  exact hp

include hF Φ in
theorem nf_mul_lin (hN : N = 2 ^ D.q * 2 ^ D.K.n) {x c : ℕ} (hx : x < N) (hc : c < 2 ^ D.K.n) :
    D.nfE (mul x (D.K.lin c)) = D.nfE x ∧ D.nfA (mul x (D.K.lin c)) = D.nfA x ^^^ c := by
  have hlt : mul x (D.K.lin c) < N := by
    rw [← Φ.f_g hx, ← hF.kf.f_el Φ hc, ← Φ.map_mul]
    exact Φ.lt _
  obtain ⟨hE, hA, -⟩ := hF.nf x hx
  obtain ⟨hE', hA', -⟩ := hF.nf _ hlt
  have h1 : Φ.g (mul x (D.K.lin c)) = Φ.g x * el Φ D.K c := by
    apply Φ.inj
    rw [Φ.f_g hlt, Φ.map_mul, Φ.f_g hx, hF.kf.f_el Φ hc]
  have h2 : Φ.g (mul x (D.K.lin c)) =
      Φ.g (wprodN mul D.q D.g (D.nfE x)) * el Φ D.K (D.nfA x ^^^ c) := by
    rw [h1, hF.g_nf Φ hx, hF.kf.el_xor Φ hA hc, mul_assoc]
  rw [hF.g_nf Φ hlt] at h2
  exact hF.nf_unique Φ hN hE' hE hA' (Nat.xor_lt_two_pow hA hc) h2

variable {T : Type*} [Group T]

include hF in
theorem map_mul_gen (hN : N = 2 ^ D.q * 2 ^ D.K.n)
    (hnorm : ∀ x : H, Mem Φ D.K x → ∀ y : H, Mem Φ D.K (y * x * y⁻¹)) {W ρ φ : ℕ → T}
    (hφ : ∀ x, x < N → φ x = W (D.nfE x) * bitProd D.K.n ρ (D.nfA x)) (hW0 : W 0 = 1)
    (h2 : ∀ i, i < D.K.n → ρ i * ρ i = 1)
    (hc : ∀ i j, i < D.K.n → j < D.K.n → ρ i * ρ j = ρ j * ρ i)
    (hcb : ∀ l, l < D.q → ∀ i, i < D.K.n →
      φ (D.g l) * ρ i * (φ (D.g l))⁻¹ = bitProd D.K.n ρ (D.cb l i))
    (hstep : ∀ e, e < 2 ^ D.q → ∀ l, l < D.q →
      φ (mul (wprodN mul D.q D.g e) (D.g l)) = W e * φ (D.g l))
    {x : ℕ} (hx : x < N) {g : ℕ} (hg : (∃ l, l < D.q ∧ g = D.g l) ∨ D.K.In g) :
    φ (mul x g) = φ x * φ g := by
  have hlt : ∀ y z, y < N → z < N → mul y z < N := fun y z hy hz => by
    rw [← Φ.f_g hy, ← Φ.f_g hz, ← Φ.map_mul]
    exact Φ.lt _
  have hlin : ∀ y, y < N → ∀ c, c < 2 ^ D.K.n →
      φ (mul y (D.K.lin c)) = φ y * bitProd D.K.n ρ c := by
    intro y hy c hc'
    obtain ⟨hE, hA⟩ := hF.nf_mul_lin Φ hN hy hc'
    rw [hφ _ (hlt _ _ hy (hF.kf.lin_lt c hc')), hφ y hy, hE, hA, bitProd_xor h2 hc, mul_assoc]
  have h0N : 0 < N := Φ.pos
  have hg0 : Φ.g 0 = 1 := by rw [← Φ.f_one hF.h0, Φ.g_f]
  have hnf0 : D.nfE 0 = 0 ∧ D.nfA 0 = 0 := by
    obtain ⟨hE, hA, -⟩ := hF.nf 0 h0N
    have h := hF.g_nf Φ h0N
    rw [hg0] at h
    have h' : Φ.g (wprodN mul D.q D.g 0) * el Φ D.K 0 =
        Φ.g (wprodN mul D.q D.g (D.nfE 0)) * el Φ D.K (D.nfA 0) := by
      rw [wprodN_zero, hg0, hF.el_zero Φ, one_mul]
      exact h
    have := hF.nf_unique Φ hN (Nat.two_pow_pos _) hE (Nat.two_pow_pos _) hA h'
    exact ⟨this.1.symm, this.2.symm⟩
  have hφ0 : φ 0 = 1 := by
    rw [hφ 0 h0N, hnf0.1, hnf0.2, hW0, bitProd_zero_right, one_mul]
  have hmul0 : ∀ y, y < N → mul 0 y = y := by
    intro y hy
    have := Φ.map_mul 1 (Φ.g y)
    rw [one_mul, Φ.f_one hF.h0, Φ.f_g hy] at this
    exact this.symm
  rcases hg with ⟨l, hl, rfl⟩ | hK
  ·
    have hgl : D.g l < N := hF.g_lt l hl
    obtain ⟨hE, hA, -⟩ := hF.nf x hx
    have hm : Mem Φ D.K ((Φ.g (D.g l))⁻¹ * el Φ D.K (D.nfA x) * Φ.g (D.g l)) := by
      have := hnorm _ (hF.el_mem Φ hA) (Φ.g (D.g l))⁻¹
      rwa [inv_inv] at this
    obtain ⟨v, hv, hel⟩ : ∃ v, v < 2 ^ D.K.n ∧
        el Φ D.K v = (Φ.g (D.g l))⁻¹ * el Φ D.K (D.nfA x) * Φ.g (D.g l) :=
      ⟨_, hm.1, hF.el_co Φ hm⟩
    have hmem : ∀ u, u < 2 ^ D.K.n → Mem Φ D.K (Φ.g (D.g l) * el Φ D.K u * (Φ.g (D.g l))⁻¹) :=
      fun u hu => hnorm _ (hF.el_mem Φ hu) _
    have hel_inj : ∀ u w, u < 2 ^ D.K.n → w < 2 ^ D.K.n → el Φ D.K u = el Φ D.K w → u = w := by
      intro u w hu hw h
      have := congrArg (fun z => D.K.co (Φ.f z)) h
      simp only [hF.kf.f_el Φ hu, hF.kf.f_el Φ hw, hF.kf.co_lin _ hu, hF.kf.co_lin _ hw] at this
      exact this
    have hadd : ∀ u w, u < 2 ^ D.K.n → w < 2 ^ D.K.n →
        D.K.co (Φ.f (Φ.g (D.g l) * el Φ D.K (u ^^^ w) * (Φ.g (D.g l))⁻¹)) =
          D.K.co (Φ.f (Φ.g (D.g l) * el Φ D.K u * (Φ.g (D.g l))⁻¹)) ^^^
            D.K.co (Φ.f (Φ.g (D.g l) * el Φ D.K w * (Φ.g (D.g l))⁻¹)) := by
      intro u w hu hw
      have h1 := (hmem u hu).1
      have h3 := (hmem w hw).1
      refine hel_inj _ _ (hmem _ (Nat.xor_lt_two_pow hu hw)).1 (Nat.xor_lt_two_pow h1 h3) ?_
      rw [hF.el_co Φ (hmem _ (Nat.xor_lt_two_pow hu hw)), hF.kf.el_xor Φ h1 h3,
        hF.el_co Φ (hmem u hu), hF.el_co Φ (hmem w hw), hF.kf.el_xor Φ hu hw]
      group
    have hcbF : ∀ i, i < D.K.n →
        D.K.co (Φ.f (Φ.g (D.g l) * el Φ D.K (2 ^ i) * (Φ.g (D.g l))⁻¹)) = D.cb l i := by
      intro i hi
      have h2i : 2 ^ i < 2 ^ D.K.n := Nat.pow_lt_pow_right Nat.one_lt_two hi
      obtain ⟨hcbl, hcbe⟩ := hF.cb_eq l hl i hi
      have hcbn : D.cb l i < 2 ^ D.K.n :=
        lt_of_lt_of_le hcbl (Nat.pow_le_pow_right Nat.two_pos (by omega))
      rw [hF.f_conj' Φ, Φ.f_g hgl, hF.kf.f_el Φ h2i, ← hcbe, hF.kf.co_lin _ hcbn]
    have hconj : D.K.co (Φ.f (Φ.g (D.g l) * el Φ D.K v * (Φ.g (D.g l))⁻¹)) =
        xorBits D.K.n (D.cb l) v :=
      (eq_xorBits (F := fun u => D.K.co (Φ.f (Φ.g (D.g l) * el Φ D.K u * (Φ.g (D.g l))⁻¹)))
        hadd hv).trans (xorBits_congr hcbF v)
    have hael : el Φ D.K (D.nfA x) = Φ.g (D.g l) * el Φ D.K v * (Φ.g (D.g l))⁻¹ := by
      rw [hel]; group
    have hav : D.nfA x = xorBits D.K.n (D.cb l) v := by
      rw [← hconj, ← hael, hF.kf.f_el Φ hA, hF.kf.co_lin _ hA]
    have hz : mul (wprodN mul D.q D.g (D.nfE x)) (D.g l) < N :=
      hlt _ _ (Φ.g_wprodN hF.h0 hF.g_lt _).1 hgl
    have hgx : Φ.g x * Φ.g (D.g l) =
        Φ.g (wprodN mul D.q D.g (D.nfE x)) * Φ.g (D.g l) * el Φ D.K v := by
      rw [hF.g_nf Φ hx, hael]; group
    have hxz : mul x (D.g l) = mul (mul (wprodN mul D.q D.g (D.nfE x)) (D.g l)) (D.K.lin v) := by
      have := congrArg Φ.f hgx
      rw [Φ.map_mul, Φ.map_mul, Φ.map_mul, Φ.f_g hx, Φ.f_g hgl,
        Φ.f_g (Φ.g_wprodN hF.h0 hF.g_lt _).1, hF.kf.f_el Φ hv] at this
      exact this
    rw [hxz, hlin _ hz v hv, hstep _ hE l hl, hφ x hx, hav, ← conj_bitProd h2 hc (hcb l hl) v]
    group
  ·
    have hco : D.K.co g < 2 ^ D.K.n := hK.1
    have hgl : D.K.lin (D.K.co g) = g := hK.2
    rw [← hgl, hlin x hx _ hco, ← hmul0 _ (hF.kf.lin_lt _ hco), hlin 0 h0N _ hco, hφ0, one_mul]

end AutFacts

end CFSG.EvenSmallLie.OmegaEight.SpBranch
