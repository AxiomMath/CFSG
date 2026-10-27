module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

namespace BlockData

variable {X : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

private theorem sl2_cube_div : ∀ A B : S1417.SL2, A ^ 3 = 1 → B ^ 3 = 1 → (B * A⁻¹) ^ 3 = 1 := by
  decide

private theorem sl2_cube_of_comm :
    ∀ A B : S1417.SL2, A ^ 3 = 1 → A ≠ 1 → A * B = B * A → B ^ 3 = 1 := by
  decide

private theorem coprime_cube_div {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hN : ActsAsNaturalL2 L U) {a b : MulAut W} (ha : a ∈ L) (hb : b ∈ L) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) : (b * a⁻¹) ^ 3 = 1 := by
  obtain ⟨e, -, -⟩ := hN
  have h1 : (e ⟨a, ha⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨a, ha⟩ : L) ^ 3 = 1 from Subtype.ext ha3, map_one]
  have h2 : (e ⟨b, hb⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨b, hb⟩ : L) ^ 3 = 1 from Subtype.ext hb3, map_one]
  have h4 : ((⟨b, hb⟩ : L) * ⟨a, ha⟩⁻¹) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_mul, map_inv, map_one]
    exact sl2_cube_div _ _ h1 h2
  exact congrArg Subtype.val h4

private theorem coprime_cube_of_comm {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hN : ActsAsNaturalL2 L U) {a l : MulAut W} (ha : a ∈ L) (hl : l ∈ L) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hcomm : a * l = l * a) : l ^ 3 = 1 := by
  obtain ⟨e, -, -⟩ := hN
  have h1 : (e ⟨a, ha⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨a, ha⟩ : L) ^ 3 = 1 from Subtype.ext ha3, map_one]
  have h2 : e ⟨a, ha⟩ ≠ 1 := by
    intro h
    apply ha1
    have h' : (⟨a, ha⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  have h3 : e ⟨a, ha⟩ * e ⟨l, hl⟩ = e ⟨l, hl⟩ * e ⟨a, ha⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hcomm)
  have h4 : (e ⟨l, hl⟩) ^ 3 = 1 := sl2_cube_of_comm _ _ h1 h2 h3
  have h5 : (⟨l, hl⟩ : L) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact h4
  exact congrArg Subtype.val h5

private theorem coprime_eq_one_of_cube {g : MulAut W} (h3 : g ^ 3 = 1)
    (hc : Nat.Coprime (orderOf g) 3) : g = 1 :=
  orderOf_eq_one_iff.mp (hc.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h3))

private theorem coprime_le_biSup {L : Subgroup (MulAut W)} (hL : L ∈ I) : L ≤ ⨆ L ∈ I, L :=
  le_iSup₂_of_le L hL le_rfl

private theorem coprime_comm_mem {N : Subgroup (MulAut W)}
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {n a : MulAut W} (hn : n ∈ N) (haX : a ∈ X) :
    n * a * n⁻¹ * a⁻¹ ∈ N := by
  have h2 : n * (a * n * a⁻¹)⁻¹ ∈ N := N.mul_mem hn (N.inv_mem (hN a haX n hn))
  simpa [mul_assoc] using h2

private theorem coprime_conjAut_eq (hI : BlockData X I) {N : Subgroup (MulAut W)} (hNX : N ≤ X)
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN3 : ∀ n ∈ N, Nat.Coprime (orderOf n) 3)
    {n : MulAut W} (hn : n ∈ N) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    B1.conjAut n L = L := by
  by_contra hne
  obtain ⟨hL'', -⟩ := hI.perm n (hNX hn) L hL
  obtain ⟨a, haL, ha3, ha1⟩ := S1417.exists_orderThree (hI.natural L hL)
  have haX : a ∈ X := hI.le (coprime_le_biSup hL haL)
  have hbL : n * a * n⁻¹ ∈ B1.conjAut n L :=
    B1.mem_conjAut.2 (by simpa [mul_assoc] using haL)
  have hcomm : n * a * n⁻¹ * a = a * (n * a * n⁻¹) :=
    hI.comm _ hL'' L hL hne _ hbL a haL
  have hb3 : (n * a * n⁻¹) ^ 3 = 1 := by rw [conj_pow, ha3, mul_one, mul_inv_cancel]
  have hd3 : (n * a * n⁻¹ * a⁻¹) ^ 3 = 1 := by
    rw [(Commute.inv_right hcomm).mul_pow, hb3, inv_pow, ha3]
    simp
  have hd1 := coprime_eq_one_of_cube hd3 (hN3 _ (coprime_comm_mem hN hn haX))
  have hba : n * a * n⁻¹ = a := mul_inv_eq_one.mp hd1
  have hmem : a ∈ L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' := by
    refine ⟨haL, ?_⟩
    have : B1.conjAut n L ≤ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' :=
      le_iSup₂_of_le _ hL'' (le_iSup_of_le hne le_rfl)
    exact this (hba ▸ hbL)
  rw [hI.indep L hL] at hmem
  exact ha1 (Subgroup.mem_bot.mp hmem)

private theorem coprime_mem_stabSub (hI : BlockData X I) {n : MulAut W} (hnX : n ∈ X)
    {L : Subgroup (MulAut W)} (hL : L ∈ I) (hnL : B1.conjAut n L = L) :
    n ∈ stabSub (commV L) := by
  have h := (hI.perm n hnX L hL).2
  rw [hnL] at h
  refine S1417.mem_stabSub_of_forall (fun u hu => ?_) (fun u hu => ?_)
  · rw [← h]
    exact Subgroup.mem_map_of_mem _ hu
  · rw [← h] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    simpa using hw

private theorem coprime_conj_eq_of_cube (hI : BlockData X I) {N : Subgroup (MulAut W)}
    (hNX : N ≤ X) (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hN3 : ∀ n ∈ N, Nat.Coprime (orderOf n) 3) {n : MulAut W} (hn : n ∈ N)
    {L : Subgroup (MulAut W)} (hL : L ∈ I) {a : MulAut W} (haL : a ∈ L) (ha3 : a ^ 3 = 1) :
    n * a * n⁻¹ = a := by
  have hnL := coprime_conjAut_eq hI hNX hN hN3 hn hL
  have hbL : n * a * n⁻¹ ∈ L := by
    have : n * a * n⁻¹ ∈ B1.conjAut n L := B1.mem_conjAut.2 (by simpa [mul_assoc] using haL)
    rwa [hnL] at this
  have hb3 : (n * a * n⁻¹) ^ 3 = 1 := by rw [conj_pow, ha3, mul_one, mul_inv_cancel]
  have hd3 : (n * a * n⁻¹ * a⁻¹) ^ 3 = 1 :=
    coprime_cube_div (hI.natural L hL) haL hbL ha3 hb3
  have hdN := coprime_comm_mem hN hn (hI.le (coprime_le_biSup hL haL))
  exact mul_inv_eq_one.mp (coprime_eq_one_of_cube hd3 (hN3 _ hdN))

private theorem coprime_pow_apply_eq {L : Subgroup (MulAut W)} {n l : MulAut W} (hl : l ∈ L)
    (h : ∀ u ∈ commV L, l u = n u) (k : ℕ) : ∀ u ∈ commV L, (n ^ k) u = (l ^ k) u := by
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih u hu]
    exact (h _ (commV_stable L (L.pow_mem hl k) hu)).symm

private theorem coprime_fixes_block (hI : BlockData X I) {N : Subgroup (MulAut W)} (hNX : N ≤ X)
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN3 : ∀ n ∈ N, Nat.Coprime (orderOf n) 3)
    {n : MulAut W} (hn : n ∈ N) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    ∀ v ∈ commV L, n v = v := by
  have hnL := coprime_conjAut_eq hI hNX hN hN3 hn hL
  have hnat := hI.natural L hL
  have hst : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu => commV_stable L hl hu
  obtain ⟨l, hlL, hl⟩ := S1417.exists_apply_eq_of_stab hnat hst
    (coprime_mem_stabSub hI (hNX hn) hL hnL)
  obtain ⟨a, haL, ha3, ha1⟩ := S1417.exists_orderThree hnat
  have hna : n * a = a * n :=
    mul_inv_eq_iff_eq_mul.mp (coprime_conj_eq_of_cube hI hNX hN hN3 hn hL haL ha3)
  have hal : a * l = l * a := by
    have hg : (l * a)⁻¹ * (a * l) ∈ L :=
      L.mul_mem (L.inv_mem (L.mul_mem hlL haL)) (L.mul_mem haL hlL)
    have h1 := S1417.eq_one_of_forall_apply_eq hnat hst hg (fun u hu => ?_)
    · exact (inv_mul_eq_one.mp h1).symm
    · have h2 : (a * l) u = (l * a) u := by
        rw [MulAut.mul_apply, MulAut.mul_apply, hl u hu, hl _ (hst a haL u hu)]
        have := congrArg (fun f : MulAut W => f u) hna
        simpa using this.symm
      rw [MulAut.mul_apply, h2]
      simp
  have hl3 : l ^ 3 = 1 := coprime_cube_of_comm hnat haL hlL ha3 ha1 hal
  have hn3 : n ^ 3 ∈ centSub (commV L) := fun u hu => by
    rw [coprime_pow_apply_eq hlL hl 3 u hu, hl3]
    rfl
  have hmem : n ∈ Subgroup.zpowers (n ^ 3) := A4.mem_zpowers_pow_of_coprime (hN3 n hn).symm
  exact fun v hv => (Subgroup.zpowers_le.mpr hn3) hmem v hv

theorem fixes_commV_of_coprime (hI : BlockData X I) {N : Subgroup (MulAut W)} (hNX : N ≤ X)
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN3 : ∀ n ∈ N, Nat.Coprime (orderOf n) 3) :
    ∀ n ∈ N, ∀ L ∈ I, ∀ v ∈ commV L, n v = v := fun _ hn _ hL =>
  coprime_fixes_block hI hNX hN hN3 hn hL

end BlockData

end CFSG.LocalAnalysis.RankThreeUC
