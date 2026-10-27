module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutGlue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HeisLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.AGLEmbeddingD2
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_of_commute {a b z₁ z₂ : G} (h₁ : Commute z₁ (b * z₂))
    (h₂ : Commute a z₂) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, h₁.commutator_eq,
    commutatorElement_mul_right_eq_mul_conj, h₂.commutator_eq]
  simp

theorem commutatorElement_pow_pow_of_commute {x y : G} (hx : Commute x ⁅x, y⁆)
    (hy : Commute y ⁅x, y⁆) (m n : ℕ) : ⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n) := by
  have h1 : ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m := (hx.commutatorElement_pow_left m).symm
  have h2 : Commute y ⁅x ^ m, y⁆ := by rw [h1]; exact hy.pow_right m
  rw [← h2.commutatorElement_pow_right n, h1, ← pow_mul]

theorem pow_zpow_comm (c : G) (n : ℕ) (j : ℤ) : (c ^ n) ^ j = (c ^ j) ^ n := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (c ^ j) n, ← zpow_mul, mul_comm]

end Commutators

theorem sporCore_of_heisLocal {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type} [Group K]
    [Finite K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (T : Sylow p K)
    (h : HeisLocal p (T : Subgroup K)) : SporCore p K T := by
  have hpf : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcard, hmax, hcent, hZ, hcomm, hexp, hsolv, t, htN, m, lam, e, hm, hlam, he, hpow, hinv,
    hline⟩ := h
  have hcen : Subgroup.center K = ⊥ := center_eq_bot_of_simple hs hnab
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, orderOf_zero] at hlam
    omega
  have hlam1 : (lam : ZMod p) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hlam
    omega
  have hlam2 : ((lam * lam : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    have h2 : (lam : ZMod p) ^ 2 = 1 := by rw [pow_two]; push_cast at h1; exact h1
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hlam] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  set P : Subgroup K := (T : Subgroup K) with hP
  set Z : Subgroup K := P ⊓ Subgroup.centralizer (P : Set K) with hZdef
  have hZP : Z ≤ P := inf_le_left
  have hZc : ∀ z ∈ Z, ∀ x ∈ P, z * x = x * z := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.1 hz.2 x hx).symm
  have hPbot : P ≠ ⊥ := by
    intro hb
    rw [hb] at hcard
    have : (1 : ℕ) = p ^ 3 := by simpa using hcard
    have := hp.one_lt
    have h3 : p ^ 3 ≥ p := Nat.le_self_pow (by norm_num) p
    omega
  have hPtop : P ≠ ⊤ := by
    intro ht
    have hZbot : Z = ⊥ := by
      rw [hZdef, ht, Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
      simp
    rw [hZbot, Subgroup.card_bot] at hZ
    have := hp.one_lt
    omega
  have hzp : ∀ w ∈ Z, w ≠ 1 → Subgroup.zpowers w = Z := by
    intro w hw hw1
    have hw5 : w ^ p = 1 := hexp w (hZP hw)
    have hord : orderOf w = p := orderOf_eq_prime hw5 hw1
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw)
      (by rw [Nat.card_zpowers, hord, hZ])
  obtain ⟨x₀, hx₀, y₀, hy₀, hc₀⟩ : ∃ x₀ ∈ P, ∃ y₀ ∈ P, ⁅x₀, y₀⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : ⁅P, P⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      rw [hcon a ha b hb]
      exact Subgroup.one_mem _
    rw [hcomm] at hbot
    rw [hbot, Subgroup.card_bot] at hZ
    have := hp.one_lt
    omega
  have hcZ : ⁅x₀, y₀⁆ ∈ Z := by
    rw [← hcomm]; exact Subgroup.commutator_mem_commutator hx₀ hy₀
  have hZc' : Subgroup.zpowers ⁅x₀, y₀⁆ = Z := hzp _ hcZ hc₀
  set u : K := t ^ m with hu
  have huN : u ∈ Subgroup.normalizer (P : Set K) := Subgroup.pow_mem _ htN m
  have huc : u * ⁅x₀, y₀⁆ * u⁻¹ = ⁅x₀, y₀⁆ ^ (lam * lam) := by
    obtain ⟨z₁, hz₁, h₁⟩ := hpow x₀ hx₀
    obtain ⟨z₂, hz₂, h₂⟩ := hpow y₀ hy₀
    have hx₀l : x₀ ^ lam ∈ P := P.pow_mem hx₀ _
    have hy₀l : y₀ ^ lam ∈ P := P.pow_mem hy₀ _
    have hxc : Commute x₀ ⁅x₀, y₀⁆ := (hZc _ hcZ x₀ hx₀).symm
    have hyc : Commute y₀ ⁅x₀, y₀⁆ := (hZc _ hcZ y₀ hy₀).symm
    rw [conjugate_commutatorElement, h₁, h₂,
      commutatorElement_mul_mul_of_commute ?_ ?_]
    · exact commutatorElement_pow_pow_of_commute hxc hyc lam lam
    · exact Commute.mul_right (hZc _ hz₁ _ hy₀l) (hZc _ hz₁ _ (hZP hz₂))
    · exact (hZc _ hz₂ _ hx₀l).symm
  have hZact : ∀ z ∈ Z, u * z * u⁻¹ = z ^ (lam * lam) := by
    intro z hz
    rw [← hZc'] at hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← conj_zpow, huc, pow_zpow_comm]
  have hiter : ∀ j : ℕ, ∀ y ∈ P, ∃ z ∈ Z, u ^ j * y * (u ^ j)⁻¹ = y ^ (lam ^ j) * z := by
    intro j
    induction j with
    | zero => intro y hy; exact ⟨1, Z.one_mem, by simp⟩
    | succ j ih =>
      intro y hy
      obtain ⟨z₀, hz₀, h₀⟩ := ih y hy
      obtain ⟨z₁, hz₁, h₁⟩ := hpow y hy
      have hyl : y ^ lam ∈ P := P.pow_mem hy _
      have hcz : Commute (y ^ lam) z₁ := (hZc z₁ hz₁ _ hyl).symm
      refine ⟨z₁ ^ (lam ^ j) * z₀ ^ (lam * lam), Z.mul_mem (Z.pow_mem hz₁ _) (Z.pow_mem hz₀ _),
        ?_⟩
      have e1 : u ^ (j + 1) * y * (u ^ (j + 1))⁻¹ = u * (u ^ j * y * (u ^ j)⁻¹) * u⁻¹ := by
        group
      have e2 : u * (y ^ (lam ^ j) * z₀) * u⁻¹ = (u * y * u⁻¹) ^ (lam ^ j) * (u * z₀ * u⁻¹) := by
        rw [conj_pow]; group
      rw [e1, h₀, e2, h₁, hZact z₀ hz₀, hcz.mul_pow, ← pow_mul, ← pow_succ', mul_assoc]
  have hfix : ∀ a : ℕ, ∀ y ∈ P, u ^ (p ^ a) * y = y * u ^ (p ^ a) → y = 1 := by
    intro a y hy hcomm'
    have hy5 : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one (hexp y hy)
    obtain ⟨z, hz, hz'⟩ := hiter (p ^ a) y hy
    have hsy : u ^ (p ^ a) * y * (u ^ (p ^ a))⁻¹ = y := by
      rw [hcomm']; group
    rw [hsy] at hz'
    have hLpos : 0 < lam ^ (p ^ a) := pow_pos (Nat.pos_of_ne_zero hlam0) _
    have hLm : ((lam ^ (p ^ a) : ℕ) : ZMod p) ≠ 1 := by
      rw [natCast_pow_prime_pow]; exact hlam1
    have hL1 : y ^ (lam ^ (p ^ a) - 1) ∈ Z := by
      have h1 : y ^ (lam ^ (p ^ a)) = y ^ (lam ^ (p ^ a) - 1) * y := by
        rw [← pow_succ, Nat.sub_add_cancel hLpos]
      have h2 : y ^ (lam ^ (p ^ a) - 1) * z * y = y := by
        calc y ^ (lam ^ (p ^ a) - 1) * z * y
            = y ^ (lam ^ (p ^ a) - 1) * (y * z) := by rw [mul_assoc, hZc z hz y hy]
          _ = y ^ (lam ^ (p ^ a) - 1) * y * z := by rw [mul_assoc]
          _ = y ^ (lam ^ (p ^ a)) * z := by rw [h1]
          _ = y := hz'.symm
      have h3 : y ^ (lam ^ (p ^ a) - 1) * z = 1 :=
        mul_right_cancel (h2.trans (one_mul y).symm)
      have h4 : y ^ (lam ^ (p ^ a) - 1) = z⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [h4]; exact Z.inv_mem hz
    have hcop : Nat.Coprime (lam ^ (p ^ a) - 1) (orderOf y) :=
      Nat.Coprime.coprime_dvd_right hy5
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_sub_one hLpos hLm)).symm
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
    have hyZ : y ∈ Z := by rw [← hk]; exact Z.pow_mem hL1 k
    have hconjZ := conj_pow_eq_pow_pow (R := Z) hZact (p ^ a) y hyZ
    have hy2 : y ^ ((lam * lam) ^ (p ^ a)) = y := by rw [← hconjZ]; exact hsy
    exact eq_one_of_pow_eq_self (p := p) (k := 1) hp (by simpa using hy5)
      (by rw [natCast_pow_prime_pow]; exact hlam2) hy2
  have hinvariant : ∀ V : Subgroup K, V ≤ P →  V ≠ ⊥ →
      Subgroup.normalizer (P : Set K) ≤ Subgroup.normalizer (V : Set K) →
      V = P ∨ (V = Z ∧ Z ≠ P) := by
    intro V hVP hV hVN
    have hVnorm : ∀ g ∈ P, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
      (Subgroup.mem_normalizer_iff.1 (hVN (Subgroup.le_normalizer hg)) v).1 hv
    have hZV : Z ≤ V := by
      obtain ⟨⟨x, hxV⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV
      have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      by_cases hxZ : x ∈ Z
      · rw [← hzp x hxZ hx1']
        exact Subgroup.zpowers_le.2 hxV
      · have hxP : x ∈ P := hVP hxV
        have hxnc : ¬ ∀ y ∈ P, y * x = x * y := fun hc =>
          hxZ ⟨hxP, Subgroup.mem_centralizer_iff.2 hc⟩
        push Not at hxnc
        obtain ⟨y, hy, hxy⟩ := hxnc
        have hwV : ⁅x, y⁆ ∈ V := by
          have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
          rw [this]
          exact V.mul_mem hxV (hVnorm y hy x⁻¹ (V.inv_mem hxV))
        have hwZ : ⁅x, y⁆ ∈ Z := by
          rw [← hcomm]; exact Subgroup.commutator_mem_commutator hxP hy
        have hw1 : ⁅x, y⁆ ≠ 1 := fun h1 =>
          hxy (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
        rw [← hzp _ hwZ hw1]
        exact Subgroup.zpowers_le.2 hwV
    have hVc : Nat.card V ∣ p ^ 3 := hcard ▸ Subgroup.card_dvd_of_le hVP
    obtain ⟨i, hi, hiV⟩ := (Nat.dvd_prime_pow hp).1 hVc
    have hZVc : p ∣ Nat.card V := hZ ▸ Subgroup.card_dvd_of_le hZV
    interval_cases i
    · exfalso
      rw [pow_zero] at hiV
      rw [hiV] at hZVc
      exact hp.one_lt.ne' (Nat.dvd_one.1 hZVc)
    · right
      refine ⟨(Subgroup.eq_of_le_of_card_ge hZV (by rw [hiV, hZ, pow_one])).symm, ?_⟩
      intro hZP'
      have h1 : Nat.card Z = Nat.card P := by rw [hZP']
      rw [hZ, hcard] at h1
      have h2 : p * 1 = p * p ^ 2 := by rw [mul_one, ← pow_succ']; exact h1
      have h3 := Nat.eq_of_mul_eq_mul_left hp.pos h2
      have h4 : p ^ 2 ≥ 5 * 5 := by rw [pow_two]; exact Nat.mul_le_mul hp5 hp5
      omega
    · exfalso
      have hrel : V.relIndex P = p := by
        have h1 := Subgroup.relIndex_mul_card (H := V) (K := P)
        rw [inf_of_le_left hVP, hiV, hcard] at h1
        apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2)
        rw [h1]; ring
      have htV : t ∈ Subgroup.normalizer (V : Set K) := hVN htN
      exact hline 1 (by norm_num) (by omega) V hZV hVP hrel (by simpa using htV)
    · left
      exact Subgroup.eq_of_le_of_card_ge hVP (by rw [hiV, hcard])
  refine ⟨?_, hcen, ?_, isCoatom_of_overgroups (normalizer_ne_top_of_simple hs hPbot hPtop) hmax,
    hsolv, torus_of_conj_data hp huN hfix, hinvariant⟩
  · rw [hcard]; exact dvd_pow_self p (by norm_num)
  · intro g hg
    exact hcent (Subgroup.mem_centralizer_iff.2 fun t ht => (hg t ht).symm)

section D2

theorem sporCore_of_d2HeisLocalAt {i : TauCeti.CFSGIndex} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (H : D2HeisLocalAt i fun q => q = p) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (hK : Nonempty (K ≃* i.Group))
    (T : Sylow p K) : SporCore p K T := by
  have hcen : Subgroup.center K = ⊥ := center_eq_bot_of_simple hs hnab
  obtain ⟨e⟩ := hK
  have hKc : Subgroup.centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  exact sporCore_of_heisLocal hp hp5 hs hnab T
    (H K ⊤ inferInstance hKc ⟨Subgroup.topEquiv.trans e⟩ p rfl T).2

theorem autFixInner_of_d2HeisLocalAt {i : TauCeti.CFSGIndex} {p : ℕ} (hp : p.Prime)
    (H : D2HeisLocalAt i fun q => q = p) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (hK : Nonempty (K ≃* i.Group))
    (T : Sylow p K) : AutFixInner p K T := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center K = ⊥ := center_eq_bot_of_simple hs hnab
  obtain ⟨e⟩ := hK
  have hnormal : ((MulAut.conj : K →* MulAut K).range).Normal := innerRange_normal
  have hKc : Subgroup.centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  refine autFixInner_of_centralizer hcen T
    (H K ⊤ inferInstance hKc ⟨Subgroup.topEquiv.trans e⟩ p rfl T).2.1 fun R => ?_
  have hR := H (MulAut K) (MulAut.conj : K →* MulAut K).range hnormal
    (centralizer_innerRange hcen) ⟨(innerEquiv hcen).symm.trans e⟩ p rfl R
  exact ⟨hR.2.1, hR.2.2.2.1⟩

end D2

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
