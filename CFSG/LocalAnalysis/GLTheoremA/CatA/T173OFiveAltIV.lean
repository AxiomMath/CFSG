module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveAltIV2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X

variable {Ω : Type} [Group Ω] {S B : Subgroup Ω} {Γ : Type} [Group Γ] {G₀ Ghat : Subgroup Γ}

private lemma exists_twoElement_lift [Finite Ω] (M : S172DModel S B G₀ Ghat) {u : G₀}
    (hu : u ^ 2 = 1) :
    ∃ v : ↥S, ((M.π v : ↥G₀) : Γ) = ((u : G₀) : Γ) ∧ ∃ k, orderOf v = 2 ^ k := by
  obtain ⟨g, hg⟩ := M.surj u
  obtain ⟨c, m, hm_odd, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ m, ?_, ?_⟩
  · rw [map_pow, hg]
    obtain ⟨n, hn⟩ := hm_odd
    rw [show u ^ m = u from by
      rw [hn, pow_succ, pow_mul, hu, one_pow, one_mul]]
  · rw [orderOf_pow, hm]
    have hmpos : 0 < m := by
      obtain ⟨n, hn⟩ := hm_odd
      omega
    have hgcd : (2 ^ c * m).gcd m = m := Nat.gcd_eq_right (dvd_mul_left m (2 ^ c))
    rw [hgcd, Nat.mul_div_cancel (2 ^ c) hmpos]
    exact ⟨c, rfl⟩

private lemma isTwoElement_pow {G : Type*} [Group G] {x : G} (hx : ∃ k, orderOf x = 2 ^ k)
    (n : ℕ) : ∃ k, orderOf (x ^ n) = 2 ^ k := by
  obtain ⟨a, ha⟩ := hx
  have hdvd : orderOf (x ^ n) ∣ 2 ^ a := by
    rw [← ha]
    exact orderOf_pow_dvd n
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

private lemma isTwoElement_mul_of_commute {G : Type*} [Group G] {x y : G}
    (hxy : Commute x y) (hx : ∃ k, orderOf x = 2 ^ k) (hy : ∃ k, orderOf y = 2 ^ k) :
    ∃ k, orderOf (x * y) = 2 ^ k := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hdvd : orderOf (x * y) ∣ 2 ^ a * 2 ^ b := by
    rw [← ha, ← hb]
    exact hxy.orderOf_mul_dvd_mul_orderOf
  rw [← pow_add] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

private lemma isTwoElement_conj_mul_inv {G : Type*} [Group G] {g t : G} {S : Subgroup G}
    (htS : t ∈ S) (hgtS : g * t * g⁻¹ ∈ S)
    (hc : g * t * g⁻¹ * t⁻¹ ∈ Subgroup.centralizer (S : Set G))
    (ht2 : ∃ k, orderOf t = 2 ^ k) :
    ∃ k, orderOf (g * t * g⁻¹ * t⁻¹) = 2 ^ k := by
  obtain ⟨a, ha⟩ := ht2
  have hu2 : ∃ k, orderOf (g * t * g⁻¹) = 2 ^ k := by
    refine ⟨a, ?_⟩
    rw [show g * t * g⁻¹ = (MulAut.conj g) t from (MulAut.conj_apply g t).symm,
      MulEquiv.orderOf_eq]
    exact ha
  obtain ⟨b, hb⟩ := hu2
  obtain ⟨c, hc2⟩ : ∃ k, orderOf (t⁻¹) = 2 ^ k := ⟨a, by rw [orderOf_inv, ha]⟩
  have hcomm : Commute (g * t * g⁻¹) t⁻¹ := by
    have h1 : t⁻¹ * ((g * t * g⁻¹) * t⁻¹) = ((g * t * g⁻¹) * t⁻¹) * t⁻¹ :=
      Subgroup.mem_centralizer_iff.1 hc t⁻¹ (S.inv_mem htS)
    have h2 : t⁻¹ * (g * t * g⁻¹) = (g * t * g⁻¹) * t⁻¹ := by
      calc t⁻¹ * (g * t * g⁻¹) = t⁻¹ * (g * t * g⁻¹) * t⁻¹ * t := by group
        _ = (t⁻¹ * (g * t * g⁻¹ * t⁻¹)) * t := by group
        _ = ((g * t * g⁻¹ * t⁻¹) * t⁻¹) * t := by rw [h1]
        _ = (g * t * g⁻¹) * t⁻¹ := by group
    exact h2.symm
  have hdvd : orderOf (g * t * g⁻¹ * t⁻¹) ∣ 2 ^ b * 2 ^ c := by
    rw [← hb, ← hc2]
    exact hcomm.orderOf_mul_dvd_mul_orderOf
  rw [← pow_add] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

private lemma eq_one_of_twoElement_pow_prime {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) {x : G} (hx : ∃ k, orderOf x = 2 ^ k) (hxp : x ^ p = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hx
  cases k with
  | zero =>
      rw [pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
  | succ k =>
      have h2 : 2 ∣ orderOf x := by
        rw [hk]
        exact dvd_pow_self 2 (Nat.succ_ne_zero k)
      have h2p : 2 ∣ p := h2.trans (orderOf_dvd_of_pow_eq_one hxp)
      exact absurd (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp |>.mp h2p).symm hp2

private lemma mem_centralizer_of_pi_eq_one (M : S172DModel S B G₀ Ghat) {u : Ω} (huS : u ∈ S)
    (huπ : ((M.π ⟨u, huS⟩ : ↥G₀) : Γ) = 1) :
    u ∈ Subgroup.centralizer (S : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hcen : (⟨u, huS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [← M.ker_π, MonoidHom.mem_ker]
    exact Subtype.ext huπ
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨z, hz⟩)

private lemma commutator_mem_centralizer_of_pi (M : S172DModel S B G₀ Ghat)
    {g t : Ω} (hgS : ∀ z ∈ S, g * z * g⁻¹ ∈ S) (htS : t ∈ S)
    (hπ : ((M.π ⟨g * t * g⁻¹, hgS t htS⟩ : ↥G₀) : Γ) =
      ((M.π ⟨t, htS⟩ : ↥G₀) : Γ)) :
    g * t * g⁻¹ * t⁻¹ ∈ Subgroup.centralizer (S : Set Ω) := by
  have hmem : g * t * g⁻¹ * t⁻¹ ∈ S :=
    S.mul_mem (hgS t htS) (S.inv_mem htS)
  refine mem_centralizer_of_pi_eq_one M hmem ?_
  have e : (⟨g * t * g⁻¹ * t⁻¹, hmem⟩ : ↥S) =
      (⟨g * t * g⁻¹, hgS t htS⟩ : ↥S) * (⟨t, htS⟩ : ↥S)⁻¹ := by
    apply Subtype.ext
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, map_mul, map_inv]
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hπ, mul_inv_cancel]

private lemma commutator_twoElement_of_actions (M : S172DModel S B G₀ Ghat)
    {g t s x : Ω} (hgS : ∀ z ∈ S, g * z * g⁻¹ ∈ S) (htS : t ∈ S) (hsS : s ∈ S)
    (hx : x = t * s)
    (hπt : ((M.π ⟨g * t * g⁻¹, hgS t htS⟩ : ↥G₀) : Γ) =
      ((M.π ⟨t, htS⟩ : ↥G₀) : Γ))
    (hπs : ((M.π ⟨g * s * g⁻¹, hgS s hsS⟩ : ↥G₀) : Γ) =
      ((M.π ⟨s, hsS⟩ : ↥G₀) : Γ))
    (ht2 : ∃ k, orderOf t = 2 ^ k) (hs2 : ∃ k, orderOf s = 2 ^ k) :
    g * x * g⁻¹ * x⁻¹ ∈ Subgroup.centralizer (S : Set Ω) ∧
      ∃ k, orderOf (g * x * g⁻¹ * x⁻¹) = 2 ^ k := by
  have hct := commutator_mem_centralizer_of_pi M hgS htS hπt
  have hcs := commutator_mem_centralizer_of_pi M hgS hsS hπs
  have hgtS : g * t * g⁻¹ ∈ S := hgS t htS
  have hgsS : g * s * g⁻¹ ∈ S := hgS s hsS
  have hctS : g * t * g⁻¹ * t⁻¹ ∈ S := S.mul_mem hgtS (S.inv_mem htS)
  have hct2 := isTwoElement_conj_mul_inv htS hgtS hct ht2
  have hcs2 := isTwoElement_conj_mul_inv hsS hgsS hcs hs2
  have hcomm_ct_cs : Commute (g * t * g⁻¹ * t⁻¹) (g * s * g⁻¹ * s⁻¹) :=
    Subgroup.mem_centralizer_iff.1 hcs (g * t * g⁻¹ * t⁻¹) hctS
  have hc2 := isTwoElement_mul_of_commute hcomm_ct_cs hct2 hcs2
  have hxconj : g * x * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * (g * s * g⁻¹ * s⁻¹) * x := by
    rw [hx]
    calc g * (t * s) * g⁻¹ = (g * t * g⁻¹) * (g * s * g⁻¹) := by group
      _ = ((g * t * g⁻¹ * t⁻¹) * t) * ((g * s * g⁻¹ * s⁻¹) * s) := by group
      _ = (g * t * g⁻¹ * t⁻¹) * (g * s * g⁻¹ * s⁻¹) * (t * s) := by
          have htc : t * (g * s * g⁻¹ * s⁻¹) = (g * s * g⁻¹ * s⁻¹) * t :=
            Subgroup.mem_centralizer_iff.1 hcs t htS
          calc ((g * t * g⁻¹ * t⁻¹) * t) * ((g * s * g⁻¹ * s⁻¹) * s)
              = (g * t * g⁻¹ * t⁻¹) * (t * (g * s * g⁻¹ * s⁻¹)) * s := by group
            _ = (g * t * g⁻¹ * t⁻¹) * ((g * s * g⁻¹ * s⁻¹) * t) * s := by rw [htc]
            _ = (g * t * g⁻¹ * t⁻¹) * (g * s * g⁻¹ * s⁻¹) * (t * s) := by group
  have hc_eq : g * x * g⁻¹ * x⁻¹ = (g * t * g⁻¹ * t⁻¹) * (g * s * g⁻¹ * s⁻¹) := by
    rw [hxconj]
    group
  have hcC : (g * t * g⁻¹ * t⁻¹) * (g * s * g⁻¹ * s⁻¹) ∈
      Subgroup.centralizer (S : Set Ω) :=
    (Subgroup.centralizer (S : Set Ω)).mul_mem hct hcs
  exact ⟨hc_eq ▸ hcC, hc_eq ▸ hc2⟩

private lemma conjugate_pow_eq_of_commutator {G : Type*} [Group G] {p N : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) {g x u : G} {S : Subgroup G}
    (hxS : x ∈ S)
    (hcC : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.centralizer (S : Set G))
    (hc2 : ∃ k, orderOf (g * x * g⁻¹ * x⁻¹) = 2 ^ k)
    (hu : u = x ^ N) (hup : u ^ p = 1) :
    g * u * g⁻¹ = u := by
  set c : G := g * x * g⁻¹ * x⁻¹ with hc
  have hcx : g * x * g⁻¹ = c * x := by rw [hc]; group
  have hcomm : Commute c x := (Subgroup.mem_centralizer_iff.1 hcC x hxS).symm
  have hconj : g * u * g⁻¹ = (g * x * g⁻¹) ^ N := by
    rw [hu]
    have h := map_pow (MulAut.conj g).toMonoidHom x N
    simpa [MulAut.conj_apply, MulAut.conj] using h.symm
  have hpow : g * u * g⁻¹ = c ^ N * u := by
    rw [hconj, hcx, hcomm.mul_pow N, hu]
  have hcpN : (c ^ N) ^ p = 1 := by
    have h1 : (g * u * g⁻¹) ^ p = 1 := by
      rw [hu]
      have hconjpow : g * x ^ N * g⁻¹ = (g * x * g⁻¹) ^ N := by
        have h := map_pow (MulAut.conj g).toMonoidHom x N
        simpa [MulAut.conj_apply, MulAut.conj] using h.symm
      rw [hconjpow, show g * x * g⁻¹ = (MulAut.conj g) x from (MulAut.conj_apply g x).symm,
        ← map_pow, ← map_pow, ← hu, hup, map_one]
    rw [hpow] at h1
    have hcomm2 : Commute (c ^ N) u := by
      rw [hu]
      exact (hcomm.pow_left N).pow_right N
    rw [hcomm2.mul_pow p, hup, mul_one] at h1
    exact h1
  have hcN2 : ∃ k, orderOf (c ^ N) = 2 ^ k := isTwoElement_pow hc2 N
  have hcN1 : c ^ N = 1 := eq_one_of_twoElement_pow_prime hp hp2 hcN2 hcpN
  rw [hpow, hcN1, one_mul]

private lemma mul_conj_eq_sq_mul {G : Type*} [Group G] {t s x a b : G}
    (hx : x = t * s) (ha : a = t * t) (hb : b = s * s)
    (haC : ∀ w, a * w = w * a) :
    t * x * t⁻¹ = a * b * x⁻¹ := by
  have hat : a * t⁻¹ = t := by rw [ha]; group
  have hbs : b * s⁻¹ = s := by rw [hb]; group
  have hleft : t * x * t⁻¹ = s * t := by
    rw [hx]
    calc t * (t * s) * t⁻¹ = (t * t) * s * t⁻¹ := by group
      _ = (a * s) * t⁻¹ := by rw [ha]
      _ = (s * a) * t⁻¹ := by rw [haC s]
      _ = s * (a * t⁻¹) := by group
      _ = s * t := by rw [hat]
  have hright : a * b * x⁻¹ = s * t := by
    rw [hx, mul_inv_rev]
    calc a * b * (s⁻¹ * t⁻¹) = a * (b * s⁻¹) * t⁻¹ := by group
      _ = a * s * t⁻¹ := by rw [hbs]
      _ = s * a * t⁻¹ := by rw [haC s]
      _ = s * (a * t⁻¹) := by group
      _ = s * t := by rw [hat]
  rw [hleft, hright]

private lemma sq_eq_sq_mul {G : Type*} [Group G] {p : ℕ} {t x a b z : G}
    (hz : z = x ^ p) (hform : t * x * t⁻¹ = a * b * x⁻¹)
    (hzC : ∀ w, w * z = z * w)
    (haC : ∀ w, a * w = w * a) (hbC : ∀ w, b * w = w * b) :
    z * z = (a * b) ^ p := by
  have hconj_pow : x ^ p = (a * b) ^ p * (x ^ p)⁻¹ := by
    have h1 : (t * x * t⁻¹) ^ p = (a * b * x⁻¹) ^ p := by rw [hform]
    have hleft : (t * x * t⁻¹) ^ p = x ^ p := by
      rw [show t * x * t⁻¹ = (MulAut.conj t) x from (MulAut.conj_apply t x).symm,
        ← map_pow, MulAut.conj_apply, ← hz, hzC t, mul_assoc, mul_inv_cancel, mul_one]
    have hright : (a * b * x⁻¹) ^ p = (a * b) ^ p * (x ^ p)⁻¹ := by
      have habC : Commute (a * b) x⁻¹ := by
        show (a * b) * x⁻¹ = x⁻¹ * (a * b)
        calc (a * b) * x⁻¹ = a * (b * x⁻¹) := by group
          _ = a * (x⁻¹ * b) := by rw [hbC x⁻¹]
          _ = (a * x⁻¹) * b := by group
          _ = (x⁻¹ * a) * b := by rw [haC x⁻¹]
          _ = x⁻¹ * (a * b) := by group
      rw [habC.mul_pow p, inv_pow]
    rw [hleft, hright] at h1
    exact h1
  calc z * z = x ^ p * x ^ p := by rw [hz]
    _ = ((a * b) ^ p * (x ^ p)⁻¹) * x ^ p := by
          nth_rewrite 1 [hconj_pow]
          rfl
    _ = (a * b) ^ p := by rw [mul_assoc, inv_mul_cancel, mul_one]

private lemma twoElement_of_sq_twoElement {G : Type*} [Group G] {z : G}
    (h : ∃ k, orderOf (z * z) = 2 ^ k) : ∃ k, orderOf z = 2 ^ k := by
  obtain ⟨j, hj⟩ := h
  have hpow : z ^ 2 ^ (j + 1) = 1 := by
    rw [show 2 ^ (j + 1) = 2 * 2 ^ j by rw [pow_succ, Nat.mul_comm]]
    rw [pow_mul, show z ^ 2 = z * z from pow_two z, ← hj, pow_orderOf_eq_one]
  obtain ⟨k, -, hk⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
  exact ⟨k, hk⟩

private lemma exists_fermat_exponent {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) {z : G} (hz : ∃ j, orderOf z = 2 ^ j) :
    ∃ N : ℕ, 0 < N ∧ N ≡ 1 [MOD p] ∧ z ^ N = 1 := by
  obtain ⟨j, hj⟩ := hz
  have h2p : 2 ≤ p := hp.two_le
  set N : ℕ := (2 ^ j) ^ (p - 1) with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hcop : (2 ^ j).Coprime p := by
    have hnot : ¬ p ∣ 2 ^ j := by
      intro hd
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    exact ((hp.coprime_iff_not_dvd).mpr hnot).symm
  have hFermat : N ≡ 1 [MOD p] := by
    rw [hN]
    exact Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have hzN : z ^ N = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hj, hN]
    exact dvd_pow_self _ (by omega)
  exact ⟨N, hNpos, hFermat, hzN⟩

private lemma pow_eq_self_of_fermat {G : Type*} [Group G] {p N : ℕ} (hp : Nat.Prime p)
    {u : G} (hu : orderOf u = p) (hN : N ≡ 1 [MOD p]) (hNpos : 0 < N) :
    u ^ N = u := by
  have hdvd : p ∣ N - 1 := hN.symm.dvd'
  rw [← hu] at hdvd
  have h1 : u ^ (N - 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact hdvd
  calc u ^ N = u ^ ((N - 1) + 1) := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hNpos)]
    _ = u ^ (N - 1) * u := pow_succ _ _
    _ = u := by rw [h1, one_mul]

private lemma pow_mul_pow_eq_one {G : Type*} [Group G] {p N : ℕ} {x z y : G}
    (hz : z = x ^ p) (hN : z ^ N = 1) (hy : y = x ^ N) : y ^ p = 1 := by
  rw [hy, ← pow_mul, Nat.mul_comm N p, pow_mul, ← hz, hN]

private lemma exists_twoElement_lifts [Finite Ω] (M : S172DModel S B G₀ Ghat)
    {t s : Γ} {tg sg : ↥G₀} (htg : ((tg : ↥G₀) : Γ) = t) (hsg : ((sg : ↥G₀) : Γ) = s)
    (ht2' : tg ^ 2 = 1) (hs2' : sg ^ 2 = 1) :
    ∃ tT sT : ↥S,
      ((M.π tT : ↥G₀) : Γ) = t ∧ ((M.π sT : ↥G₀) : Γ) = s ∧
      (∃ k, orderOf ((tT : ↥S) : Ω) = 2 ^ k) ∧
      (∃ k, orderOf ((sT : ↥S) : Ω) = 2 ^ k) := by
  obtain ⟨tT, htTπ, htT2⟩ := exists_twoElement_lift (M := M) (u := tg) ht2'
  obtain ⟨sT, hsTπ, hsT2⟩ := exists_twoElement_lift (M := M) (u := sg) hs2'
  have htπ : ((M.π tT : ↥G₀) : Γ) = t := htTπ.trans htg
  have hsπ : ((M.π sT : ↥G₀) : Γ) = s := hsTπ.trans hsg
  have htT2' : ∃ k, orderOf ((tT : ↥S) : Ω) = 2 ^ k := by
    obtain ⟨c, hc⟩ := htT2
    exact ⟨c, by rw [Subgroup.orderOf_coe]; exact hc⟩
  have hsT2' : ∃ k, orderOf ((sT : ↥S) : Ω) = 2 ^ k := by
    obtain ⟨c, hc⟩ := hsT2
    exact ⟨c, by rw [Subgroup.orderOf_coe]; exact hc⟩
  exact ⟨tT, sT, htπ, hsπ, htT2', hsT2'⟩

private lemma pi_conj_of_mem_B [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat)
    {u : Γ} (hu : u ∈ Subgroup.centralizer (((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ)))
    {uT : ↥S} (huπ : ((M.π uT : ↥G₀) : Γ) = u)
    {bb : Ω} (hbb : bb ∈ B) :
    ((M.π ⟨bb * uT * bb⁻¹, hcfg.normal.conj_mem uT uT.2 bb⟩ : ↥G₀) : Γ) =
      ((M.π uT : ↥G₀) : Γ) := by
  have hbarb : ((M.β ⟨bb, hbb⟩ : ↥Ghat) : Γ) ∈ M.barB :=
    Subgroup.mem_map_of_mem Ghat.subtype (MonoidHom.mem_range.mpr ⟨⟨bb, hbb⟩, rfl⟩)
  have hucent : u ∈ Subgroup.centralizer (M.barB : Set Γ) :=
    Subgroup.centralizer_le (by intro z hz; exact Subgroup.mem_sup_left hz) hu
  have hcomm : ((M.β ⟨bb, hbb⟩ : ↥Ghat) : Γ) * u =
      u * ((M.β ⟨bb, hbb⟩ : ↥Ghat) : Γ) :=
    Subgroup.mem_centralizer_iff.1 hucent _ hbarb
  have hconj := M.conj ⟨bb⁻¹, B.inv_mem hbb⟩ uT
    ⟨bb * uT * bb⁻¹, hcfg.normal.conj_mem uT uT.2 bb⟩ (by simp)
  have hβ : ((M.β ⟨bb⁻¹, B.inv_mem hbb⟩ : ↥Ghat) : Γ) =
      ((M.β ⟨bb, hbb⟩ : ↥Ghat) : Γ)⁻¹ := by
    have h1 : (⟨bb⁻¹, B.inv_mem hbb⟩ : ↥B) = (⟨bb, hbb⟩ : ↥B)⁻¹ := by
      ext
      simp
    rw [h1, map_inv]
    rfl
  calc ((M.π ⟨bb * uT * bb⁻¹, hcfg.normal.conj_mem uT uT.2 bb⟩ : ↥G₀) : Γ)
      = ((M.β ⟨bb, hbb⟩ : ↥Ghat) : Γ) * ((M.π uT : ↥G₀) : Γ) *
          ((M.β ⟨bb, hbb⟩ : ↥Ghat) : Γ)⁻¹ := by simpa [hβ] using hconj
    _ = ((M.π uT : ↥G₀) : Γ) := by rw [huπ, hcomm, mul_assoc, mul_inv_cancel, mul_one]

private lemma pi_conj_of_mem_K [Finite Ω] {K : Subgroup Ω}
    (hKS : K ≤ S) (M : S172DModel S B G₀ Ghat)
    {u : Γ} (hu : u ∈ Subgroup.centralizer (M.piImg K : Set Γ))
    {uT : ↥S} (huπ : ((M.π uT : ↥G₀) : Γ) = u)
    {kk : Ω} (hkk : kk ∈ K) (hgS : ∀ z ∈ S, kk * z * kk⁻¹ ∈ S) :
    ((M.π ⟨kk * uT * kk⁻¹, hgS uT uT.2⟩ : ↥G₀) : Γ) = ((M.π uT : ↥G₀) : Γ) := by
  have hkS : kk ∈ S := hKS hkk
  have hmem : ((M.π ⟨kk, hkS⟩ : ↥G₀) : Γ) ∈ M.piImg K :=
    Subgroup.mem_map_of_mem G₀.subtype
      (Subgroup.mem_map_of_mem M.π (Subgroup.mem_subgroupOf.2 hkk))
  have hcomm : ((M.π ⟨kk, hkS⟩ : ↥G₀) : Γ) * u =
      u * ((M.π ⟨kk, hkS⟩ : ↥G₀) : Γ) :=
    Subgroup.mem_centralizer_iff.1 hu _ hmem
  have e : (⟨kk * uT * kk⁻¹, hgS uT uT.2⟩ : ↥S) =
      (⟨kk, hkS⟩ : ↥S) * uT * (⟨kk, hkS⟩ : ↥S)⁻¹ := by
    apply Subtype.ext
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [huπ, hcomm, mul_assoc, mul_inv_cancel, mul_one]

private lemma centralizes_B_of_pow_lift [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat)
    {t s : Γ} (htcent : t ∈ Subgroup.centralizer (((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ)))
    (hscent : s ∈ Subgroup.centralizer (((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ)))
    {tT sT : ↥S} (htπt : ((M.π tT : ↥G₀) : Γ) = t)
    (hsπs : ((M.π sT : ↥G₀) : Γ) = s)
    (htT2 : ∃ k, orderOf ((tT : ↥S) : Ω) = 2 ^ k)
    (hsT2 : ∃ k, orderOf ((sT : ↥S) : Ω) = 2 ^ k)
    {x₀ : ↥S} (hx₀ : x₀ = tT * sT) {Nn : ℕ}
    (hyp : ((x₀ : Ω) ^ Nn) ^ p = 1) :
    (x₀ : Ω) ^ Nn ∈ Subgroup.centralizer (B : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff]
  intro bb hbb
  have hgS : ∀ z ∈ S, bb * z * bb⁻¹ ∈ S := fun z hz => hcfg.normal.conj_mem z hz bb
  have hπt := pi_conj_of_mem_B hcfg M htcent htπt hbb
  have hπs := pi_conj_of_mem_B hcfg M hscent hsπs hbb
  have hc := commutator_twoElement_of_actions (M := M) (g := bb) (t := (tT : Ω))
    (s := (sT : Ω)) (x := (x₀ : Ω)) hgS tT.2 sT.2 (by rw [hx₀]; rfl) hπt hπs htT2 hsT2
  have hconj := conjugate_pow_eq_of_commutator hcfg.prime hcfg.odd (x := (x₀ : Ω))
    (u := (x₀ : Ω) ^ Nn) x₀.2 hc.1 hc.2 rfl hyp
  calc bb * (x₀ : Ω) ^ Nn = (bb * (x₀ : Ω) ^ Nn * bb⁻¹) * bb := by group
    _ = (x₀ : Ω) ^ Nn * bb := by rw [hconj]

private lemma centralizes_K_of_pow_lift [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    {t s : Γ} (htcent : t ∈ Subgroup.centralizer (((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ)))
    (hscent : s ∈ Subgroup.centralizer (((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ)))
    {tT sT : ↥S} (htπt : ((M.π tT : ↥G₀) : Γ) = t)
    (hsπs : ((M.π sT : ↥G₀) : Γ) = s)
    (htT2 : ∃ k, orderOf ((tT : ↥S) : Ω) = 2 ^ k)
    (hsT2 : ∃ k, orderOf ((sT : ↥S) : Ω) = 2 ^ k)
    {x₀ : ↥S} (hx₀ : x₀ = tT * sT) {Nn : ℕ}
    (hyp : ((x₀ : Ω) ^ Nn) ^ p = 1) :
    (x₀ : Ω) ^ Nn ∈ Subgroup.centralizer (K : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff]
  intro kk hkk
  have hkS : kk ∈ S := hKS hkk
  have hgS : ∀ z ∈ S, kk * z * kk⁻¹ ∈ S :=
    fun z hz => S.mul_mem (S.mul_mem hkS hz) (S.inv_mem hkS)
  have htcentK : t ∈ Subgroup.centralizer (M.piImg K : Set Γ) :=
    Subgroup.centralizer_le (by intro z hz; exact Subgroup.mem_sup_right hz) htcent
  have hscentK : s ∈ Subgroup.centralizer (M.piImg K : Set Γ) :=
    Subgroup.centralizer_le (by intro z hz; exact Subgroup.mem_sup_right hz) hscent
  have hπt := pi_conj_of_mem_K (K := K) hKS M htcentK htπt hkk hgS
  have hπs := pi_conj_of_mem_K (K := K) hKS M hscentK hsπs hkk hgS
  have hc := commutator_twoElement_of_actions (M := M) (g := kk) (t := (tT : Ω))
    (s := (sT : Ω)) (x := (x₀ : Ω)) hgS tT.2 sT.2 (by rw [hx₀]; rfl) hπt hπs htT2 hsT2
  have hconj := conjugate_pow_eq_of_commutator hcfg.prime hcfg.odd (x := (x₀ : Ω))
    (u := (x₀ : Ω) ^ Nn) x₀.2 hc.1 hc.2 rfl hyp
  calc kk * (x₀ : Ω) ^ Nn = (kk * (x₀ : Ω) ^ Nn * kk⁻¹) * kk := by group
    _ = (x₀ : Ω) ^ Nn * kk := by rw [hconj]

private lemma not_mem_B_of_pow_lift [Finite Ω] (M : S172DModel S B G₀ Ghat)
    {ts : ↥G₀} (htsnot : ((ts : ↥G₀) : Γ) ∉ M.barB)
    {y : Ω} (hyS : y ∈ S)
    (hπy : ((M.π ⟨y, hyS⟩ : ↥G₀) : Γ) = ((ts : ↥G₀) : Γ)) : y ∉ B := by
  intro hmem
  have hβy : ((M.β ⟨y, hmem⟩ : ↥Ghat) : Γ) = ((M.π ⟨y, hyS⟩ : ↥G₀) : Γ) :=
    M.coe_β_eq_coe_π rfl
  have hbar : ((M.π ⟨y, hyS⟩ : ↥G₀) : Γ) ∈ M.barB := by
    rw [← hβy]
    exact Subgroup.mem_map_of_mem Ghat.subtype
      (MonoidHom.mem_range.mpr ⟨⟨_, hmem⟩, rfl⟩)
  rw [hπy] at hbar
  exact htsnot hbar

private lemma pow_lift_core [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat)
    {tg sg ts : ↥G₀} (htg2 : tg ^ 2 = 1) (hsg2 : sg ^ 2 = 1)
    (hts : ((ts : ↥G₀) : Γ) = ((tg : ↥G₀) : Γ) * ((sg : ↥G₀) : Γ))
    (htsp : ts ^ p = 1)
    {tT sT : ↥S} (htπt : ((M.π tT : ↥G₀) : Γ) = ((tg : ↥G₀) : Γ))
    (hsπs : ((M.π sT : ↥G₀) : Γ) = ((sg : ↥G₀) : Γ)) :
    ∃ x₀ a b : ↥S, x₀ = tT * sT ∧ a = tT ^ 2 ∧ b = sT ^ 2 ∧
      (∀ w : ↥S, w * (x₀ ^ p) = (x₀ ^ p) * w) ∧
      (∀ w : ↥S, a * w = w * a) ∧ (∀ w : ↥S, b * w = w * b) ∧
      ((M.π x₀ : ↥G₀) : Γ) = ((ts : ↥G₀) : Γ) := by
  let x₀ : ↥S := tT * sT
  let a : ↥S := tT ^ 2
  let b : ↥S := sT ^ 2
  have htπtG : M.π tT = tg := Subtype.ext htπt
  have hsπsG : M.π sT = sg := Subtype.ext hsπs
  have hπx : ((M.π x₀ : ↥G₀) : Γ) = ((ts : ↥G₀) : Γ) := by
    rw [show x₀ = tT * sT from rfl, map_mul, Subgroup.coe_mul, htπt, hsπs, ← hts]
  have hzC : ∀ w : ↥S, w * (x₀ ^ p) = (x₀ ^ p) * w := by
    intro w
    have hzπ : M.π (x₀ ^ p) = 1 := by
      rw [map_pow, Subtype.ext hπx, htsp]
    have hcen : (x₀ ^ p) ∈ Subgroup.center ↥S := by
      rw [← M.ker_π, MonoidHom.mem_ker]
      exact hzπ
    exact Subgroup.mem_center_iff.1 hcen w
  have haC : ∀ w : ↥S, a * w = w * a := by
    intro w
    have haπ : M.π a = 1 := by
      rw [show a = tT ^ 2 from rfl, map_pow, htπtG, htg2]
    have hcen : a ∈ Subgroup.center ↥S := by
      rw [← M.ker_π, MonoidHom.mem_ker]
      exact haπ
    exact (Subgroup.mem_center_iff.1 hcen w).symm
  have hbC : ∀ w : ↥S, b * w = w * b := by
    intro w
    have hbπ : M.π b = 1 := by
      rw [show b = sT ^ 2 from rfl, map_pow, hsπsG, hsg2]
    have hcen : b ∈ Subgroup.center ↥S := by
      rw [← M.ker_π, MonoidHom.mem_ker]
      exact hbπ
    exact (Subgroup.mem_center_iff.1 hcen w).symm
  exact ⟨x₀, a, b, rfl, rfl, rfl, hzC, haC, hbC, hπx⟩

private lemma pow_lift_twoElement [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat)
    {tg sg ts : ↥G₀} (htg2 : tg ^ 2 = 1) (hsg2 : sg ^ 2 = 1)
    (hts : ((ts : ↥G₀) : Γ) = ((tg : ↥G₀) : Γ) * ((sg : ↥G₀) : Γ))
    (htsp : ts ^ p = 1)
    {tT sT : ↥S} (htπt : ((M.π tT : ↥G₀) : Γ) = ((tg : ↥G₀) : Γ))
    (hsπs : ((M.π sT : ↥G₀) : Γ) = ((sg : ↥G₀) : Γ))
    (htT2 : ∃ k, orderOf tT = 2 ^ k) (hsT2 : ∃ k, orderOf sT = 2 ^ k) :
    ∃ x₀ : ↥S, x₀ = tT * sT ∧
      (∀ w : ↥S, w * (x₀ ^ p) = (x₀ ^ p) * w) ∧
      (∃ k, orderOf (x₀ ^ p) = 2 ^ k) ∧
      ((M.π x₀ : ↥G₀) : Γ) = ((ts : ↥G₀) : Γ) := by
  obtain ⟨x₀, a, b, hx₀, ha, hb, hzC, haC, hbC, hπx⟩ :=
    pow_lift_core hcfg M htg2 hsg2 hts htsp htπt hsπs
  have hform := mul_conj_eq_sq_mul (t := tT) (s := sT) (x := x₀) (a := a) (b := b)
    hx₀ (ha.trans (pow_two tT)) (hb.trans (pow_two sT)) haC
  have hz2 := sq_eq_sq_mul (z := x₀ ^ p) (x := x₀) rfl hform hzC haC hbC
  have ha2 : ∃ k, orderOf a = 2 ^ k := by
    rw [ha]
    exact isTwoElement_pow htT2 2
  have hb2 : ∃ k, orderOf b = 2 ^ k := by
    rw [hb]
    exact isTwoElement_pow hsT2 2
  have hab2 : ∃ k, orderOf (a * b) = 2 ^ k :=
    isTwoElement_mul_of_commute (show Commute a b from haC b) ha2 hb2
  have hz2elem : ∃ k, orderOf ((x₀ ^ p) * (x₀ ^ p)) = 2 ^ k := by
    rw [hz2]
    exact isTwoElement_pow hab2 p
  exact ⟨x₀, hx₀, hzC, twoElement_of_sq_twoElement hz2elem, hπx⟩

private lemma orderOf_coe_twoElement {X : Subgroup Ω} {u : ↥X}
    (h : ∃ k, orderOf ((u : Ω)) = 2 ^ k) : ∃ k, orderOf u = 2 ^ k := by
  obtain ⟨c, hc⟩ := h
  rw [Subgroup.orderOf_coe] at hc
  exact ⟨c, hc⟩

private lemma exists_pElement_of_involution_pair [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hy : ∃ t ∈ G₀, ∃ s ∈ G₀, t ^ 2 = 1 ∧ s ^ 2 = 1 ∧
      t ∈ Subgroup.centralizer ((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ) ∧
      s ∈ Subgroup.centralizer ((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ) ∧
      (t * s) ^ p = 1 ∧ t * s ∉ M.barB) :
    ∃ y : Ω, y ∈ S ∧ y ^ p = 1 ∧ y ∈ Subgroup.centralizer (B : Set Ω) ∧
      y ∈ Subgroup.centralizer (K : Set Ω) ∧ y ∉ B := by
  classical
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨t, htG, s, hsG, ht2, hs2, htcent, hscent, htsp, htsnot⟩ := hy
  let tg : ↥G₀ := ⟨t, htG⟩
  let sg : ↥G₀ := ⟨s, hsG⟩
  let ts : ↥G₀ := tg * sg
  have htg2 : tg ^ 2 = 1 := Subtype.ext ht2
  have hsg2 : sg ^ 2 = 1 := Subtype.ext hs2
  have hts : ((ts : ↥G₀) : Γ) = t * s := rfl
  have htsp' : ts ^ p = 1 := Subtype.ext htsp
  have htsne : ts ≠ 1 := by
    intro h
    exact htsnot (by rw [← hts, h]; exact M.barB.one_mem)
  obtain ⟨tT, sT, htπt, hsπs, htT2, hsT2⟩ :=
    exists_twoElement_lifts M (t := t) (s := s) rfl rfl htg2 hsg2
  have htT2S : ∃ k, orderOf tT = 2 ^ k := orderOf_coe_twoElement htT2
  have hsT2S : ∃ k, orderOf sT = 2 ^ k := orderOf_coe_twoElement hsT2
  obtain ⟨x₀, hx₀, hzC, hzpowe, hπx⟩ :=
    pow_lift_twoElement hcfg M htg2 hsg2 hts htsp' htπt hsπs htT2S hsT2S
  have hordts : orderOf ts = p := orderOf_eq_prime htsp' htsne
  obtain ⟨Nn, hNpos, hFermat, hzN⟩ :=
    exists_fermat_exponent hcfg.prime hcfg.odd hzpowe
  have htsN_G : ts ^ Nn = ts := pow_eq_self_of_fermat hcfg.prime hordts hFermat hNpos
  have htsN : ((ts : ↥G₀) : Γ) ^ Nn = ((ts : ↥G₀) : Γ) := by
    rw [← Subgroup.coe_pow, htsN_G]
  have hup : ((x₀ : ↥S) ^ Nn) ^ p = 1 := pow_mul_pow_eq_one rfl hzN rfl
  have hyp : ((x₀ : Ω) ^ Nn) ^ p = 1 := by
    have := congrArg (fun w : ↥S => ((w : Ω))) hup
    simpa using this
  have hyS : (x₀ : Ω) ^ Nn ∈ S := S.pow_mem x₀.2 Nn
  have hπy : ((M.π ⟨(x₀ : Ω) ^ Nn, hyS⟩ : ↥G₀) : Γ) = ((ts : ↥G₀) : Γ) := by
    change ((M.π ((x₀ : ↥S) ^ Nn) : ↥G₀) : Γ) = ((ts : ↥G₀) : Γ)
    rw [map_pow, Subgroup.coe_pow, hπx, htsN]
  exact ⟨(x₀ : Ω) ^ Nn, hyS, hyp,
    centralizes_B_of_pow_lift hcfg M htcent hscent htπt hsπs htT2 hsT2 hx₀ hyp,
    centralizes_K_of_pow_lift hcfg M hKS htcent hscent htπt hsπs htT2 hsT2 hx₀ hyp,
    not_mem_B_of_pow_lift M htsnot hyS hπy⟩

namespace S172DModel

theorem concl_of_inner [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1)
    (hK2 : 2 ∣ Nat.card (M.piImg K))
    (hinner : ∀ a ∈ M.barB, ∃ k ∈ M.piImg K, k ^ p = 1 ∧
      k ∈ Subgroup.centralizer (M.barB : Set Γ) ∧
      a * k⁻¹ ∈ Subgroup.centralizer (M.piImg K : Set Γ))
    (hy : ∃ t ∈ G₀, ∃ s ∈ G₀, t ^ 2 = 1 ∧ s ^ 2 = 1 ∧
      t ∈ Subgroup.centralizer ((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ) ∧
      s ∈ Subgroup.centralizer ((M.barB ⊔ M.piImg K : Subgroup Γ) : Set Γ) ∧
      (t * s) ^ p = 1 ∧ t * s ∉ M.barB) :
    T173Concl p S B K N := by
  classical
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  obtain ⟨y, hyS, hyp, hyBcent, hyKcent, hyB⟩ :=
    exists_pElement_of_involution_pair hcfg M hKS hy
  obtain ⟨U, hUK, hU1, hU2⟩ := exists_twoGroup_le_of_two_dvd_card_piImg hcfg M hKS hK2
  have hdecomp : B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set Ω)) :=
    le_antisymm (le_inf_sup_inf_centralizer_of_inner hcfg M hKS hKZ hinner)
      (by refine sup_le ?_ ?_ <;> exact inf_le_left)
  have hUcent : y ∈ Subgroup.centralizer (U : Set Ω) :=
    Subgroup.centralizer_le (fun z hz => hUK hz) hyKcent
  have hyNormU : y ∈ Subgroup.normalizer (U : Set Ω) :=
    Subgroup.centralizer_le_normalizer (U : Set Ω) hUcent
  have hsplit : B ⊔ Subgroup.zpowers y = ((B ⊔ Subgroup.zpowers y) ⊓ K) ⊔
      ((B ⊔ Subgroup.zpowers y) ⊓ Subgroup.normalizer (U : Set Ω)) := by
    refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    calc B ⊔ Subgroup.zpowers y
        = ((B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set Ω))) ⊔ Subgroup.zpowers y := by
          conv_lhs => rw [hdecomp]
      _ ≤ ((B ⊔ Subgroup.zpowers y) ⊓ K) ⊔
            ((B ⊔ Subgroup.zpowers y) ⊓ Subgroup.normalizer (U : Set Ω)) := by
          refine sup_le ?_ ?_
          · refine sup_le ?_ ?_
            · exact (inf_le_inf_right K le_sup_left).trans le_sup_left
            · exact (le_inf (inf_le_left.trans le_sup_left)
                (inf_le_right.trans ((Subgroup.centralizer_le (fun z hz => hUK hz)).trans
                  (Subgroup.centralizer_le_normalizer (U : Set Ω))))).trans le_sup_right
          · exact (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2
              ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers y), hyNormU⟩)).trans le_sup_right
  have hle : B ⊔ Subgroup.zpowers y ≤ S ⊔ B := by
    refine sup_le le_sup_right ?_
    exact Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hyS)
  refine Or.inr ⟨B ⊔ Subgroup.zpowers y, U, ?_, hle, le_sup_left, ?_, hU1, hU2, hUK, hsplit⟩
  · refine hcfg.elem.sup_of_commute (isElemAbelian_zpowers hyp) ?_
    intro a ha z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (show Commute a y from Subgroup.mem_centralizer_iff.1 hyBcent a ha).zpow_right n
  · intro hEq
    exact hyB (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))

end S172DModel


end CFSG.LocalAnalysis.GLTheoremA.T173O

end
