module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U6Lift
public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem u6_cube_mul {G : Type} [Group G] {c : G} (hc : ∀ g : G, c * g = g * c) {u v : G}
    (hdef : u * v = c * (v * u)) (hc3 : c ^ 3 = 1) : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  have he : ∀ g : G, c⁻¹ * g = g * c⁻¹ := fun g => (Commute.inv_left (hc g)).eq
  have hL : ∀ a b : G, a * (c⁻¹ * b) = c⁻¹ * (a * b) := fun a b => by
    rw [← mul_assoc, ← he a, mul_assoc]
  have hvu : v * u = c⁻¹ * (u * v) := by
    rw [hdef, ← mul_assoc, inv_mul_cancel, one_mul]
  have hvuX : ∀ X : G, v * (u * X) = c⁻¹ * (u * (v * X)) := fun X => by
    rw [← mul_assoc, hvu, mul_assoc, mul_assoc]
  have hc3' : c⁻¹ ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  have key : u * (v * u) * (v * u) * v = c⁻¹ ^ 3 * (u * u * u * (v * v * v)) := by
    rw [hvu]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc, hL, hvuX]
  have e1 : (u * v) ^ 3 = u * (v * u) * (v * u) * v := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e1, key, hc3', one_mul]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

section Witness

variable {X : Type} [Group X] [Finite X]

theorem u6_pRank_le_card (H : Subgroup X) : CFSG.Open.pRank 3 H ≤ Nat.card X := by
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hE⟩
  have h1 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
  have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  omega
theorem u6_sSup_mem {A : Set ℕ} (hb : BddAbove A) (h : 2 ≤ sSup A) : sSup A ∈ A := by
  apply Nat.sSup_mem _ hb
  rcases A.eq_empty_or_nonempty with h0 | h0
  · rw [h0, csSup_empty] at h
    simp at h
  · exact h0
theorem u6_witness_of_two_le (h : 2 ≤ CFSG.Assembly.RankThreeEven.localRank 3 X) :
    ∃ (P E : Subgroup X) (j : ℕ), P ≠ ⊥ ∧ IsPGroup 2 P ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ j ∧ 2 ≤ j ∧ E ≤ Subgroup.normalizer (P : Set X) := by
  have hbA : BddAbove {k | ∃ H : Subgroup X, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} :=
    ⟨Nat.card X, by rintro k ⟨H, -, rfl⟩; exact u6_pRank_le_card H⟩
  obtain ⟨H, hH, hHk⟩ := u6_sSup_mem hbA h
  have h2 : 2 ≤ CFSG.Open.pRank 3 H := by rw [hHk]; exact h
  obtain ⟨P, hP0, hP2, rfl⟩ := hH
  have hbB : BddAbove {k | ∃ E : Subgroup X, E ≤ Subgroup.normalizer (P : Set X) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E, -, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
    have h3 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  have h3 := u6_sSup_mem hbB h2
  obtain ⟨E, hE, hEel, hEc⟩ := h3
  refine ⟨P, E, _, hP0, hP2, hEel, hEc, ?_, hE⟩
  unfold CFSG.Open.pRank at h2
  exact h2
end Witness

section Cover2

variable {K X : Type} [Group K] [Group X] [Finite K] [Finite X]

theorem u6_two_le_of_cover (π : K →* X) (hπ : Function.Surjective π) (hk : π.ker = Subgroup.center K)
    (h3 : 3 ∣ Nat.card (Subgroup.center K)) (h12 : Nat.card (Subgroup.center K) ∣ 12)
    {Pb Eb : Subgroup X} (hPb : Pb ≠ ⊥) (hPb2 : IsPGroup 2 Pb)
    (hEb : CFSG.Open.IsElemAbelian 3 Eb) {j : ℕ} (hj : 2 ≤ j) (hEbc : Nat.card Eb = 3 ^ j)
    (hEbN : Eb ≤ Subgroup.normalizer (Pb : Set X)) :
    2 ≤ CFSG.Assembly.RankThreeEven.localRank 3 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hPb2
  have ha1 : 1 ≤ a := by
    have h1 := (Subgroup.one_lt_card_iff_ne_bot Pb).2 hPb
    rw [ha] at h1
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at h1; simp at h1
    · exact h0
  obtain ⟨b, hb⟩ : ∃ b, Nat.card (Subgroup.center K) = 3 * 2 ^ b := by
    have key : ∀ n < 13, 3 ∣ n → n ∣ 12 → ∃ b ≤ 2, n = 3 * 2 ^ b := by decide
    obtain ⟨b, -, hb⟩ := key _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) h12)) h3 h12
    exact ⟨b, hb⟩
  set Q : Subgroup K := Pb.comap π with hQ
  have hQc : Nat.card Q = 3 * 2 ^ (a + b) := by
    rw [hQ, u6_card_comap π hπ Pb, hk, ha, hb, pow_add]; ring
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 3 h3
  have hzK : orderOf (z : K) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  have hπz : π (z : K) = 1 := by rw [← MonoidHom.mem_ker, hk]; exact z.2
  have hzQ : (z : K) ∈ Q := by
    rw [hQ, Subgroup.mem_comap, hπz]; exact Pb.one_mem
  set zQ : Q := ⟨z, hzQ⟩ with hzQdef
  have hzQc : zQ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 z.2 (g : K))
  have horder : orderOf zQ = 3 := by rw [← Subgroup.orderOf_coe]; exact hzK
  obtain ⟨K₂, hK₂⟩ := Sylow.exists_subgroup_card_pow_prime 2
    (show 2 ^ (a + b) ∣ Nat.card Q by rw [hQc]; exact ⟨3, by ring⟩)
  have hZQc : Nat.card (Subgroup.zpowers zQ) = 3 := by rw [Nat.card_zpowers, horder]
  have hZQN : Subgroup.zpowers zQ ≤ Subgroup.normalizer (K₂ : Set Q) :=
    Subgroup.zpowers_le.2 (Subgroup.center_le_normalizer _ hzQc)
  have hcard1 := card_sup_mul_card_inf_of_le_normalizer (A := K₂) (B := Subgroup.zpowers zQ) hZQN
  have hinf : Nat.card (K₂ ⊓ Subgroup.zpowers zQ : Subgroup Q) = 1 := by
    have d1 : Nat.card (K₂ ⊓ Subgroup.zpowers zQ : Subgroup Q) ∣ 3 :=
      hZQc ▸ Subgroup.card_dvd_of_le inf_le_right
    have d2 : Nat.card (K₂ ⊓ Subgroup.zpowers zQ : Subgroup Q) ∣ 2 ^ (a + b) :=
      hK₂ ▸ Subgroup.card_dvd_of_le inf_le_left
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right _ (by norm_num)) d1 d2
  have hsup : K₂ ⊔ Subgroup.zpowers zQ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hinf, hK₂, hZQc] at hcard1
    rw [hQc]
    linarith
  have hK₂n : K₂.Normal := by
    have htop : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (K₂ : Set Q) := by
      rw [← hsup]; exact sup_le Subgroup.le_normalizer hZQN
    exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 htop)
  have hidx : K₂.index = 3 := by
    have h := Subgroup.card_mul_index K₂
    rw [hK₂, hQc] at h
    have hpos : 0 < 2 ^ (a + b) := by positivity
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h]; ring
  set P₀ : Subgroup K := K₂.map Q.subtype with hP₀
  have hP₀c : Nat.card P₀ = 2 ^ (a + b) := by
    rw [hP₀, Subgroup.card_map_of_injective Subtype.val_injective, hK₂]
  have hP₀mem : ∀ x : K, x ∈ P₀ ↔ ∃ y ∈ K₂, (y : K) = x := by
    intro x
    rw [hP₀, Subgroup.mem_map]
    rfl
  have hsel : ∀ g : K, ∀ hg : g ∈ Q, ∀ j : ℕ, g ^ 2 ^ j = 1 → g ∈ P₀ := by
    intro g hg j hgj
    set x : Q := ⟨g, hg⟩ with hxdef
    have h1 : (QuotientGroup.mk' K₂ x) ^ 2 ^ j = 1 := by
      rw [← map_pow]
      have : x ^ 2 ^ j = 1 := Subtype.ext (by simpa using hgj)
      rw [this, map_one]
    have h2 : (QuotientGroup.mk' K₂ x) ^ 3 = 1 := by
      have := orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_natCard (QuotientGroup.mk' K₂ x))
      rwa [show Nat.card (Q ⧸ K₂) = 3 from hidx] at this
    have hcop : Nat.gcd (2 ^ j) 3 = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left j (by norm_num))
    have h3 : (QuotientGroup.mk' K₂ x) ^ Nat.gcd (2 ^ j) 3 = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rw [hcop, pow_one] at h3
    have hx : x ∈ K₂ := (QuotientGroup.eq_one_iff x).1 h3
    exact (hP₀mem g).2 ⟨x, hx, rfl⟩
  set T : Subgroup K := Eb.comap π with hT
  have hTQ : ∀ t ∈ T, ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := by
    intro t ht x hx
    have hN := hEbN (Subgroup.mem_comap.1 ht)
    have := (Subgroup.mem_normalizer_iff.1 hN (π x)).1 (Subgroup.mem_comap.1 hx)
    rw [hQ, Subgroup.mem_comap]
    simpa [map_mul, map_inv] using this
  have hconj : ∀ t ∈ T, ∀ g ∈ P₀, t * g * t⁻¹ ∈ P₀ := by
    intro t ht g hg
    obtain ⟨y, hy, rfl⟩ := (hP₀mem g).1 hg
    have hyp : (y : K) ^ 2 ^ (a + b) = 1 := by
      have h1 : (⟨y, hy⟩ : K₂) ^ Nat.card K₂ = 1 :=
        orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_natCard _)
      rw [hK₂] at h1
      have h2 := congrArg (fun w : K₂ => ((w : Q) : K)) h1
      simpa using h2
    apply hsel _ (hTQ t ht _ y.2) (a + b)
    rw [conj_pow, hyp, mul_one, mul_inv_cancel]
  have hTn : ∀ t ∈ T, t ∈ Subgroup.normalizer (P₀ : Set K) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj t ht h
    · intro hh
      have := hconj t⁻¹ (inv_mem ht) _ hh
      simpa [mul_assoc] using this
  have hTc : Nat.card T = 3 ^ j * (3 * 2 ^ b) := by
    rw [hT, u6_card_comap π hπ Eb, hk, hEbc, hb]
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ (j + 1) ∣ Nat.card T by rw [hTc]; exact ⟨2 ^ b, by ring⟩)
  set S : Subgroup K := S₀.map T.subtype with hS
  have hSc : Nat.card S = 3 ^ (j + 1) := by
    rw [hS, Subgroup.card_map_of_injective Subtype.val_injective, hS₀]
  have hST : S ≤ T := by
    intro s hs
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hs
    exact t.2
  have hSN : S ≤ Subgroup.normalizer (P₀ : Set K) := fun s hs => hTn s (hST hs)
  set ψ : S →* X := π.comp S.subtype with hψ
  have hψr : ψ.range ≤ Eb := by
    rintro _ ⟨s, rfl⟩
    exact Subgroup.mem_comap.1 (hST s.2)
  set Y : Subgroup K := ψ.ker.map S.subtype with hY
  have hYmem : ∀ x : K, x ∈ Y ↔ x ∈ S ∧ π x = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
      exact ⟨s.2, MonoidHom.mem_ker.1 hs⟩
    · rintro ⟨hxS, hx1⟩
      exact Subgroup.mem_map.2 ⟨⟨x, hxS⟩, MonoidHom.mem_ker.2 hx1, rfl⟩
  have hYZ : Y ≤ Subgroup.center K := fun x hx => by
    rw [← hk]; exact MonoidHom.mem_ker.2 ((hYmem x).1 hx).2
  have hYS : Y ≤ S := fun x hx => ((hYmem x).1 hx).1
  have hkψ : Nat.card ψ.ker * Nat.card ψ.range = 3 ^ (j + 1) := by
    rw [Subgroup.card_ker_mul_card_range, hSc]
  have hrψ : Nat.card ψ.range ≤ 3 ^ j := hEbc ▸ Subgroup.card_le_of_le hψr
  have hkerge : 3 ≤ Nat.card ψ.ker := by
    have hpos : 0 < 3 ^ j := by positivity
    have h2 : 3 * 3 ^ j ≤ Nat.card ψ.ker * 3 ^ j := by
      calc 3 * 3 ^ j = 3 ^ (j + 1) := by ring
        _ = Nat.card ψ.ker * Nat.card ψ.range := hkψ.symm
        _ ≤ Nat.card ψ.ker * 3 ^ j := Nat.mul_le_mul_left _ hrψ
    exact Nat.le_of_mul_le_mul_right h2 hpos
  have hYc' : Nat.card Y = Nat.card ψ.ker := by
    rw [hY, Subgroup.card_map_of_injective Subtype.val_injective]
  have hYc : Nat.card Y = 3 := by
    have hdvdS : Nat.card Y ∣ 3 ^ (j + 1) := by
      rw [← hkψ, hYc']; exact Dvd.intro _ rfl
    obtain ⟨m, -, hYm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvdS
    have hdvdZ : Nat.card Y ∣ 3 * 2 ^ b := by
      rw [← hb]; exact Subgroup.card_dvd_of_le hYZ
    have hm1 : m ≤ 1 := by
      by_contra hm1
      push Not at hm1
      have h9 : 3 ^ 2 ∣ Nat.card Y := by rw [hYm]; exact pow_dvd_pow 3 hm1
      have h3d : 3 ∣ 2 ^ b := by
        have : 3 ^ 2 ∣ 3 * 2 ^ b := h9.trans hdvdZ
        norm_num at this
        omega
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
      norm_num at this
    have hge : 3 ≤ Nat.card Y := hYc' ▸ hkerge
    have hm : m = 1 := by
      rcases Nat.lt_or_ge m 1 with h0 | h0
      · have : m = 0 := by omega
        rw [this, pow_zero] at hYm; omega
      · omega
    rw [hYm, hm]; norm_num
  have hYp : ∀ y ∈ Y, y ^ 3 = 1 := by
    intro y hy
    have h1 : (⟨y, hy⟩ : Y) ^ Nat.card Y = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_natCard _)
    rw [hYc] at h1
    exact congrArg Subtype.val h1
  have hcS : ∀ s : S, (s : K) ^ 3 ∈ Y := by
    intro s
    rw [hYmem]
    refine ⟨S.pow_mem s.2 3, ?_⟩
    rw [map_pow]
    exact hEb.2 _ (Subgroup.mem_comap.1 (hST s.2))
  have hcomm : ∀ s t : S, π (s : K) * π (t : K) = π (t : K) * π (s : K) := by
    intro s t
    exact congrArg Subtype.val (hEb.1.is_comm.comm
      (⟨π (s : K), Subgroup.mem_comap.1 (hST s.2)⟩ : Eb)
      ⟨π (t : K), Subgroup.mem_comap.1 (hST t.2)⟩)
  have hcen : ∀ s t : S, (s : K) * t * ((t : K) * s)⁻¹ ∈ Y := by
    intro s t
    rw [hYmem]
    refine ⟨S.mul_mem (S.mul_mem s.2 t.2) (S.inv_mem (S.mul_mem t.2 s.2)), ?_⟩
    rw [map_mul, map_mul, map_inv, map_mul, ← hcomm s t, mul_inv_cancel]
  have hcenter : ∀ s t : S, ∀ g : K,
      ((s : K) * t * ((t : K) * s)⁻¹) * g = g * ((s : K) * t * ((t : K) * s)⁻¹) := fun s t g =>
    (Subgroup.mem_center_iff.1 (hYZ (hcen s t)) g).symm
  have hcube : ∀ s t : S, ((s : K) * (t : K)) ^ 3 = (s : K) ^ 3 * (t : K) ^ 3 := fun s t =>
    u6_cube_mul (hcenter s t) (by rw [inv_mul_cancel_right]) (hYp _ (hcen s t))
  let c : S →* Y := MonoidHom.mk' (fun s : S => (⟨(s : K) ^ 3, hcS s⟩ : Y))
    (fun s t => Subtype.ext (by simpa [Subgroup.coe_mul] using hcube s t))
  have hkc : Nat.card c.ker * Nat.card c.range = 3 ^ (j + 1) := by
    rw [Subgroup.card_ker_mul_card_range, hSc]
  have hrc : Nat.card c.range ≤ 3 := by
    have := Subgroup.card_le_card_group c.range
    rw [hYc] at this
    exact this
  have hkc9 : 9 ≤ Nat.card c.ker := by
    have hpos : 0 < 3 ^ j := by positivity
    have h2 : 3 ^ j * 3 ≤ Nat.card c.ker * 3 := by
      calc 3 ^ j * 3 = 3 ^ (j + 1) := by ring
        _ = Nat.card c.ker * Nat.card c.range := hkc.symm
        _ ≤ Nat.card c.ker * 3 := Nat.mul_le_mul_left _ hrc
    have h3 : 3 ^ j ≤ Nat.card c.ker := Nat.le_of_mul_le_mul_right h2 (by norm_num)
    have h9 : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  obtain ⟨w, hw, hwY⟩ : ∃ w ∈ c.ker, (w : K) ∉ Y := by
    by_contra hcon
    push Not at hcon
    have hle : c.ker.map S.subtype ≤ Y := by
      rintro _ ⟨w, hw, rfl⟩
      exact hcon w hw
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hYc] at h1
    omega
  have hw3 : (w : K) ^ 3 = 1 := by
    have h1 := MonoidHom.mem_ker.1 hw
    exact congrArg Subtype.val h1
  have hw1 : (w : K) ≠ 1 := by
    intro h
    exact hwY (by rw [h]; exact Y.one_mem)
  have horder : orderOf (w : K) = 3 := orderOf_eq_prime hw3 hw1
  set A : Subgroup K := Subgroup.zpowers (w : K) with hA
  have hAc : Nat.card A = 3 := by rw [hA, Nat.card_zpowers, horder]
  have hAS : A ≤ S := Subgroup.zpowers_le.2 w.2
  have hYN : Y ≤ Subgroup.normalizer (A : Set K) := fun y hy =>
    Subgroup.center_le_normalizer _ (hYZ hy)
  have hAY := card_sup_mul_card_inf_of_le_normalizer (A := A) (B := Y) hYN
  have hAYinf : Nat.card (A ⊓ Y : Subgroup K) = 1 := by
    have hd : Nat.card (A ⊓ Y : Subgroup K) ∣ 3 := hAc ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
    · exact h1
    · exfalso
      have heq : A ⊓ Y = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAc, h1])
      have hwA : (w : K) ∈ A ⊓ Y := by
        rw [heq]; exact Subgroup.mem_zpowers _
      exact hwY (Subgroup.mem_inf.1 hwA).2
  have hAYcard : Nat.card (A ⊔ Y : Subgroup K) = 9 := by
    rw [hAYinf, hAc, hYc] at hAY
    omega
  have hYnorm : Y.Normal := ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.1 (hYZ hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  have hcomm_AY : ∀ x ∈ A ⊔ Y, ∀ x' ∈ A ⊔ Y, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨a, ha, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    obtain ⟨a', ha', y', hy', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx'
    have hyc : ∀ g : K, y * g = g * y := fun g => (Subgroup.mem_center_iff.1 (hYZ hy) g).symm
    have hyc' : ∀ g : K, y' * g = g * y' := fun g => (Subgroup.mem_center_iff.1 (hYZ hy') g).symm
    have haa : a * a' = a' * a := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      exact ((Commute.refl (w : K)).zpow_zpow i i').eq
    have key1 : a * y * (a' * y') = (a * a') * (y * y') := by
      calc a * y * (a' * y') = a * (y * (a' * y')) := by rw [mul_assoc]
        _ = a * ((y * a') * y') := by rw [mul_assoc y]
        _ = a * ((a' * y) * y') := by rw [hyc a']
        _ = (a * a') * (y * y') := by simp only [mul_assoc]
    have key2 : a' * y' * (a * y) = (a' * a) * (y' * y) := by
      calc a' * y' * (a * y) = a' * (y' * (a * y)) := by rw [mul_assoc]
        _ = a' * ((y' * a) * y) := by rw [mul_assoc y']
        _ = a' * ((a * y') * y) := by rw [hyc' a]
        _ = (a' * a) * (y' * y) := by simp only [mul_assoc]
    rw [key1, key2, haa, hyc y']
  have hexp : ∀ x ∈ A ⊔ Y, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    have hcy : Commute a y := Subgroup.mem_center_iff.1 (hYZ hy) a
    have ha3 : a ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers ha).trans (dvd_of_eq horder))
    rw [hcy.mul_pow, ha3, hYp y hy, one_mul]
  have hE9el : CFSG.Open.IsElemAbelian 3 (A ⊔ Y : Subgroup K) :=
    ⟨⟨⟨fun x x' => Subtype.ext (hcomm_AY x x.2 x' x'.2)⟩⟩, fun x hx => hexp x hx⟩
  have hE9N : A ⊔ Y ≤ Subgroup.normalizer (P₀ : Set K) :=
    sup_le (hAS.trans hSN) (hYS.trans hSN)
  have hP0ne : P₀ ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot P₀).1 (by rw [hP₀c]; exact Nat.one_lt_two_pow (by omega))
  have hP02 : IsPGroup 2 P₀ := IsPGroup.of_card hP₀c
  exact CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer (k := 2) Nat.prime_three
    hP0ne hP02 hE9el (hAYcard.trans (by norm_num)) hE9N
end Cover2

end CFSG.LocalAnalysis.GLTheoremA