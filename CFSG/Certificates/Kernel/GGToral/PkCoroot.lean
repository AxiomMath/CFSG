module

public import CFSG.Certificates.Kernel.GGToral.PkRoots

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.StepTwoToralCert

theorem sumN_eq_sum (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sumN n f + f n = _
    rw [ih, Finset.sum_range_succ]

theorem cartan_eq_lit {τ : Tag} (hτ : tgOK τ = true) (j k : Fin τ.rank) :
    τ.cartan j k = (if j = k then 2 else 0) - ((lane (row (tgCneg τ) j) k : ℕ) : ℤ) := by
  by_cases hjk : j = k
  · subst hjk
    rw [cartan_self hτ, if_pos rfl, (tgCneg_lane_le hτ j j).2 rfl]
    simp
  · rw [tgCneg_lane hτ j k hjk, if_neg hjk]
    ring

theorem symmetrizedCartan_eq_lit {τ : Tag} (hτ : tgOK τ = true) (j k : Fin τ.rank) :
    τ.symmetrizedCartan j k = ((lane (tgDiag τ) j : ℕ) : ℤ) * τ.cartan j k := by
  unfold Tag.symmetrizedCartan
  rw [Matrix.mul_apply]
  simp only [symmetrizer_eq hτ, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp

variable {τ : Tag} {p mode : ℕ} {H : Hd}

theorem latGram_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (j : Fin N) (β : Fin N → ℤ) :
    latGram S (Pi.single j 1) β = ∑ k, S j k * β k := by
  unfold latGram
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [Pi.single_apply, hij]) (by simp)]
  simp

theorem latGram_expand {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram S α β = ∑ j, α j * latGram S (Pi.single j 1) β := by
  simp only [latGram_single]
  unfold latGram
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem latGram_single_rowZ (h : tagHdOK τ p mode H = true) (r : ℕ) (j : Fin τ.rank) :
    latGram τ.symmetrizedCartan (Pi.single j 1) (rowZ τ H r) =
      ((lane (tgDiag τ) j : ℕ) : ℤ) * (((2 * rtC H r j : ℕ) : ℤ) - ((negC τ H r j : ℕ) : ℤ)) := by
  obtain ⟨hτ, -, hn, -⟩ := tagHdOK_basic h
  rw [latGram_single]
  simp only [symmetrizedCartan_eq_lit hτ, cartan_eq_lit hτ, rowZ]
  unfold negC
  rw [sumN_eq_sum, hn]
  change _ = _ * (_ - ((∑ k ∈ Finset.range τ.rank, lane (row (tgCneg τ) j) k * rtC H r k : ℕ) : ℤ))
  rw [Finset.sum_range (fun k => lane (row (tgCneg τ) j) k * rtC H r k)]
  push_cast
  simp only [sub_mul, mul_sub, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.mul_sum,
    mul_ite, mul_zero, Finset.sum_ite_eq Finset.univ j, Finset.mem_univ, if_true]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun k _ => by ring

theorem latGram_rowZ (h : tagHdOK τ p mode H = true) (r : ℕ) :
    latGram τ.symmetrizedCartan (rowZ τ H r) (rowZ τ H r) =
      ((sumN H.n (fun j => rtC H r j * lane (tgDiag τ) j * (2 * rtC H r j)) : ℕ) : ℤ) -
        ((sumN H.n (fun j => rtC H r j * lane (tgDiag τ) j * negC τ H r j) : ℕ) : ℤ) := by
  obtain ⟨hτ, -, hn, -⟩ := tagHdOK_basic h
  rw [latGram_expand, sumN_eq_sum, sumN_eq_sum, hn]
  simp only [latGram_single_rowZ h]
  push_cast
  rw [Finset.sum_range (fun j => ((rtC H r j : ℤ) * (lane (tgDiag τ) j : ℤ) * (2 * (rtC H r j : ℤ)))),
    Finset.sum_range (fun j => ((rtC H r j : ℤ) * (lane (tgDiag τ) j : ℤ) * (negC τ H r j : ℤ))),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp only [rowZ]; ring

theorem tagHdOK_cor (h : tagHdOK τ p mode H = true) {r : ℕ} (hr : r < H.np) :
    row H.cor r = packN H.n (corC τ H r) ∧ corExact τ H r = true := by
  simp only [tagHdOK, andB_eq_true] at h
  have := allN_eq_true.mp h.2.2.2.2.2.2.2.2.2.2.2.1 r hr
  rw [andB_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, this.2⟩

theorem vecZ_cor (h : tagHdOK τ p mode H = true) {r : ℕ} (hr : r < H.np) :
    vecZ p τ.rank (row H.cor r) =
      fun j => ((latCorootZ τ.symmetrizedCartan (rowZ τ H r) j : ℤ) : ZMod p) := by
  obtain ⟨hτ, -, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨hrow, hex⟩ := tagHdOK_cor h hr
  unfold corExact at hex
  rw [andB_eq_true, allN_eq_true] at hex
  obtain ⟨hg0, hdiv⟩ := hex
  have hg0' : 0 < gramC τ H r := Nat.le_of_ble_eq_true hg0
  have hp65 : H.p ≤ 65536 := by rw [hpp]; omega
  have hcorlt : ∀ j, corC τ H r j < 65536 := fun j => by
    have : corC τ H r j < H.p := by
      unfold corC
      dsimp only
      cases Nat.ble (negC τ H r j) (Nat.mul 2 (rtC H r j)) <;> exact Nat.mod_lt _ hpos
    omega
  have hG : latGram τ.symmetrizedCartan (rowZ τ H r) (rowZ τ H r) = ((gramC τ H r : ℕ) : ℤ) := by
    rw [latGram_rowZ h]
    unfold gramC at hg0' ⊢
    change _ = (((sumN H.n _ - sumN H.n _ : ℕ)) : ℤ)
    change 0 < sumN H.n _ - sumN H.n _ at hg0'
    rw [Nat.cast_sub (by omega)]
    rfl
  funext j
  have hj : (j : ℕ) < H.n := by rw [hn]; exact j.2
  have hdj := hdiv j hj
  simp only [vecZ]
  rw [hrow, lane_packN (fun k _ => hcorlt k) hj]
  unfold latCorootZ
  rw [hG, latGram_single_rowZ h]
  have hdj' : (2 * lane (tgDiag τ) j * (2 * rtC H r j - negC τ H r j +
      (negC τ H r j - 2 * rtC H r j))) % gramC τ H r = 0 := Nat.eq_of_beq_eq_true hdj
  by_cases hle : negC τ H r j ≤ 2 * rtC H r j
  · have hb : Nat.ble (negC τ H r j) (Nat.mul 2 (rtC H r j)) = true := Nat.ble_eq.mpr hle
    have hc : corC τ H r j = 2 * lane (tgDiag τ) j * (2 * rtC H r j - negC τ H r j) /
        gramC τ H r % H.p := by
      simp only [corC, hb]
      rfl
    rw [hc]
    set g := gramC τ H r with hg
    set ps := 2 * rtC H r j with hps
    set ng := negC τ H r j with hng
    set d := lane (tgDiag τ) j with hd
    have hz : ng - ps = 0 := by omega
    rw [hz, add_zero] at hdj'
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hdj'
    rw [hq, Nat.mul_div_cancel_left _ hg0', hpp, ZMod.natCast_mod]
    have hI : (2 : ℤ) * ((d : ℤ) * ((ps : ℤ) - (ng : ℤ))) = (g : ℤ) * q := by
      rw [← Nat.cast_sub hle]
      exact_mod_cast (by rw [← hq]; ring)
    rw [hI, Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0'.ne')]
    push_cast
    rfl
  · have hb : Nat.ble (negC τ H r j) (Nat.mul 2 (rtC H r j)) = false := by
      rw [Bool.eq_false_iff]
      intro h1
      exact hle (Nat.le_of_ble_eq_true h1)
    have hc : corC τ H r j = (H.p - 2 * lane (tgDiag τ) j * (negC τ H r j - 2 * rtC H r j) /
        gramC τ H r % H.p) % H.p := by
      simp only [corC, hb]
      rfl
    rw [hc]
    set g := gramC τ H r with hg
    set ps := 2 * rtC H r j with hps
    set ng := negC τ H r j with hng
    set d := lane (tgDiag τ) j with hd
    have hz : ps - ng = 0 := by omega
    rw [hz, zero_add] at hdj'
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hdj'
    rw [hq, Nat.mul_div_cancel_left _ hg0', hpp, ZMod.natCast_mod,
      Nat.cast_sub (Nat.mod_lt _ (by omega)).le, ZMod.natCast_self, ZMod.natCast_mod]
    have hI : (2 : ℤ) * ((d : ℤ) * ((ps : ℤ) - (ng : ℤ))) = (g : ℤ) * (-(q : ℤ)) := by
      have h1 : ((2 * d * (ng - ps) : ℕ) : ℤ) = ((g * q : ℕ) : ℤ) := by rw [hq]
      push_cast [Nat.cast_sub (by omega : ps ≤ ng)] at h1
      linarith
    rw [hI, Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0'.ne')]
    push_cast
    ring

theorem memB_iff_div (m r : ℕ) : memB m r = true ↔ m / 2 ^ r % 2 = 1 := by
  rw [memB_iff, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

theorem maskN_lt (m : ℕ) (f : ℕ → Bool) : maskN m f < 2 ^ m := by
  induction m with
  | zero => exact Nat.zero_lt_one
  | succ m ih =>
    change maskN m f + Bool.rec (motive := fun _ => ℕ) 0 (1 <<< m) (f m) < _
    rw [pow_succ]
    cases f m
    · change maskN m f + 0 < _
      omega
    · change maskN m f + 1 <<< m < _
      rw [Nat.shiftLeft_eq, one_mul]
      omega

theorem memB_maskN {m : ℕ} (f : ℕ → Bool) {s : ℕ} (hs : s < m) : memB (maskN m f) s = f s := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hlt := maskN_lt m f
    have hstep : maskN (m + 1) f = maskN m f + 2 ^ m * (if f m then 1 else 0) := by
      change maskN m f + Bool.rec (motive := fun _ => ℕ) 0 (1 <<< m) (f m) = _
      cases f m <;> simp [Nat.shiftLeft_eq]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · rw [← ih hs, hstep]
      apply Bool.eq_iff_iff.mpr
      rw [memB_iff_div, memB_iff_div]
      obtain ⟨k, rfl⟩ : ∃ k, m = s + 1 + k := ⟨m - (s + 1), by omega⟩
      have h2 : 2 ^ (s + 1 + k) * (if f (s + 1 + k) then 1 else 0) =
          2 ^ s * (2 * (2 ^ k * (if f (s + 1 + k) then 1 else 0))) := by
        rw [pow_add, pow_add]
        ring
      rw [h2, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
    · rw [hstep]
      apply Bool.eq_iff_iff.mpr
      rw [memB_iff_div, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
      cases f s <;> simp

theorem adj_iff (h : tagHdOK τ p mode H = true) {r s : ℕ} (hr : r < H.np) (hs : s < H.np) :
    memB (row H.adj r) s = true ↔
      latGram τ.symmetrizedCartan (rowZ τ H s) (rowZ τ H r) ≠ 0 := by
  obtain ⟨hτ, -, hn, -⟩ := tagHdOK_basic h
  have hadj : row H.adj r = maskN H.np (gramNZ τ H r) := by
    simp only [tagHdOK, andB_eq_true] at h
    exact Nat.eq_of_beq_eq_true (allN_eq_true.mp h.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr)
  rw [hadj, memB_maskN _ hs, latGram_expand]
  simp only [latGram_single_rowZ h]
  unfold gramNZ
  rw [notB_eq_true, Bool.eq_false_iff, ne_eq, Nat.beq_eq, sumN_eq_sum, sumN_eq_sum, hn]
  change ¬ (∑ k ∈ Finset.range τ.rank, rtC H s k * lane (tgDiag τ) k * (2 * rtC H r k)) =
    ∑ k ∈ Finset.range τ.rank, rtC H s k * lane (tgDiag τ) k * negC τ H r k ↔ _
  rw [Finset.sum_range (fun j => rtC H s j * lane (tgDiag τ) j * (2 * rtC H r j)),
    Finset.sum_range (fun j => rtC H s j * lane (tgDiag τ) j * negC τ H r j)]
  have key : (∑ x : Fin τ.rank, rowZ τ H s x * (((lane (tgDiag τ) x : ℕ) : ℤ) *
      (((2 * rtC H r x : ℕ) : ℤ) - ((negC τ H r x : ℕ) : ℤ)))) =
      ((∑ i : Fin τ.rank, rtC H s i * lane (tgDiag τ) i * (2 * rtC H r i) : ℕ) : ℤ) -
        ((∑ i : Fin τ.rank, rtC H s i * lane (tgDiag τ) i * negC τ H r i : ℕ) : ℤ) := by
    push_cast
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [rowZ]; ring
  rw [ne_eq, key, sub_eq_zero, Nat.cast_inj]

theorem lane_cast_inj {p a b : ℕ} (ha : a < p) (hb : b < p) : ((a : ℕ) : ZMod p) = b ↔ a = b := by
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
  · rintro rfl
    rfl

theorem inV_iff_twist (h : tagHdOK .E6 p 1 H = true) {v : ℕ} (hv : red H v = true) :
    inV H v = true ↔ vecZ p Tag.E6.rank v ∈ fixedSub p e6Gamma := by
  obtain ⟨-, hm, hn, hpp, hp3, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨-, hvl⟩ := red_spec hpos hv
  have hl : ∀ j < 6, lane v j < p := fun j hj => hpp ▸ hvl j (by rw [hn]; exact hj)
  have htw : tw H = true := by
    rw [tw, hm]
    rfl
  unfold inV
  rw [htw]
  change (andB (Nat.beq (lane v 5) (lane v 0)) (Nat.beq (lane v 4) (lane v 2))) = true ↔ _
  rw [andB_eq_true, Nat.beq_eq, Nat.beq_eq]
  change _ ↔ ∀ i, vecZ p 6 v (e6Gamma i) = vecZ p 6 v i
  constructor
  · rintro ⟨h50, h42⟩ i
    simp only [vecZ]
    rw [lane_cast_inj (hl _ (e6Gamma i).2) (hl _ i.2)]
    have := e6Gamma_apply i
    fin_cases i <;> simp_all [tcGammaArr]
  · intro hfix
    have h0 := hfix ⟨0, by decide⟩
    have h2 := hfix ⟨2, by decide⟩
    simp only [vecZ] at h0 h2
    rw [lane_cast_inj (hl _ (e6Gamma _).2) (hl _ (by decide))] at h0 h2
    have g0 := e6Gamma_apply ⟨0, by decide⟩
    have g2 := e6Gamma_apply ⟨2, by decide⟩
    simp only [tcGammaArr] at g0 g2
    change ((e6Gamma ⟨0, _⟩ : Fin 6) : ℕ) = 5 at g0
    change ((e6Gamma ⟨2, _⟩ : Fin 6) : ℕ) = 4 at g2
    rw [g0] at h0
    rw [g2] at h2
    exact ⟨h0, h2⟩

end CFSG.KC.GGToral
