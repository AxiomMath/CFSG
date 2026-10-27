module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary

public section

namespace CFSG.QuasithinUnique.Tight

open CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

theorem exists_involution_pow {G : Type*} [Group G] {T : Subgroup G} (hT : IsPGroup 2 T) {y : G}
    (hy : y ∈ T) (hy1 : y ≠ 1) : ∃ n : ℕ, y ^ n ≠ 1 ∧ (y ^ n) ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT ⟨y, hy⟩
  have hk' : orderOf y = 2 ^ k := by
    rw [← hk]; exact (Subgroup.orderOf_mk y hy).symm
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    apply hy1
    simpa using hk'
  refine ⟨2 ^ (k - 1), ?_, ?_⟩
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hk'] at this
    have h2 : 2 ^ k ≤ 2 ^ (k - 1) := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_mul]
    have : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ]; congr 1; omega
    rw [this, ← hk']
    exact pow_orderOf_eq_one y

theorem exists_order_four {G : Type*} [Group G] {T : Subgroup G} (hT : IsPGroup 2 T) {y : G}
    (hy : y ∈ T) (hy2 : y ^ 2 ≠ 1) : ∃ x : G, x ∈ T ∧ x ^ 2 ≠ 1 ∧ x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT ⟨y, hy⟩
  have hk' : orderOf y = 2 ^ k := by
    rw [← hk]; exact (Subgroup.orderOf_mk y hy).symm
  have hk2 : 2 ≤ k := by
    by_contra h
    apply hy2
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · have : y = 1 := by simpa using hk'
      simp [this]
    · rw [← orderOf_dvd_iff_pow_eq_one, hk']
      norm_num
  refine ⟨y ^ (2 ^ (k - 2)), T.pow_mem hy _, ?_, ?_⟩
  · intro h
    rw [← pow_mul] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hk'] at this
    have h5 : 2 ^ (k - 2) * 2 = 2 ^ (k - 1) := by
      rw [← pow_succ]; congr 1; omega
    rw [h5] at this
    have h2 : 2 ^ k ≤ 2 ^ (k - 1) := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_mul]
    have : 2 ^ (k - 2) * 4 = 2 ^ k := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this, ← pow_add]; congr 1; omega
    rw [this, ← hk']
    exact pow_orderOf_eq_one y

theorem exists_central_involution {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) {x : G} (hx : x ∈ Subgroup.normalizer (R : Set G))
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    ∃ z ∈ R, z ≠ 1 ∧ z ^ 2 = 1 ∧ (∀ r ∈ R, z * r = r * z) ∧ z * x = x * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := R ⊔ Subgroup.zpowers x with hP
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hx
  have hP2 : IsPGroup 2 P := hR.to_sup_of_normal_left' hx2 hxN
  have hRP : R ≤ P := le_sup_left
  have hxP : x ∈ P := (le_sup_right : Subgroup.zpowers x ≤ P) (Subgroup.mem_zpowers x)
  have hnormal : (R.subgroupOf P).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hxN)
  have hnt : Nontrivial (R.subgroupOf P) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRP hr⟩ : P) ∈ R.subgroupOf P := hr
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have : Fact (IsPGroup 2 P) := ⟨hP2⟩
  obtain ⟨c, hc1, hcc⟩ := CFSG.exists_nontrivial_center_mem_normal (p := 2) (R.subgroupOf P)
  have hcR : ((c : P) : G) ∈ R := c.2
  have hc1' : ((c : P) : G) ≠ 1 := by
    intro h
    apply hc1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  have hcentral : ∀ q ∈ P, ((c : P) : G) * q = q * ((c : P) : G) := by
    intro q hq
    have := Subgroup.mem_center_iff.mp hcc ⟨q, hq⟩
    have h2 := congrArg Subtype.val this
    exact h2.symm
  obtain ⟨n, hn1, hn2⟩ := exists_involution_pow hR hcR hc1'
  refine ⟨((c : P) : G) ^ n, R.pow_mem hcR n, hn1, hn2, ?_, ?_⟩
  · intro r hr
    exact (Commute.pow_left (hcentral r (hRP hr)) n).eq
  · exact (Commute.pow_left (hcentral x hxP) n).eq

theorem mem_normalizer_zpowers_of_commute {G : Type*} [Group G] {g c : G} (hc : g * c = c * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Commute.zpow_left (show Commute c g from hc.symm) k).eq

theorem final_contradiction {G : Type*} [Group G] {W : Subgroup G} {x a0 a1 a2 a3 : G}
    (h01 : a1 = x⁻¹ * a0 * x) (h12 : a2 = x⁻¹ * a1 * x) (h23 : a3 = x⁻¹ * a2 * x)
    (h30 : a0 = x⁻¹ * a3 * x)
    (s1 : a1 * a1 = 1) (s2 : a2 * a2 = 1)
    (c01 : a0 * a1 = a1 * a0) (c02 : a0 * a2 = a2 * a0) (c12 : a1 * a2 = a2 * a1)
    (m0 : a0 ∈ W) (m1 : a1 ∈ W) (m2 : a2 ∈ W)
    (hC : ∀ w ∈ W, x⁻¹ * (x⁻¹ * w * x) * x = w → x * w = w * x)
    (hne : a2 ≠ a0) : False := by
  have e1 : x⁻¹ * (a0 * a2) * x = a1 * a3 := by
    calc x⁻¹ * (a0 * a2) * x = (x⁻¹ * a0 * x) * (x⁻¹ * a2 * x) := by group
      _ = a1 * a3 := by rw [← h01, ← h23]
  have e2 : x⁻¹ * (a1 * a3) * x = a2 * a0 := by
    calc x⁻¹ * (a1 * a3) * x = (x⁻¹ * a1 * x) * (x⁻¹ * a3 * x) := by group
      _ = a2 * a0 := by rw [← h12, ← h30]
  have hb : x * (a0 * a2) = (a0 * a2) * x := by
    apply hC _ (W.mul_mem m0 m2)
    rw [e1, e2, c02]
  have e : a1 * a3 = a0 * a2 := by
    rw [← e1]
    calc x⁻¹ * (a0 * a2) * x = x⁻¹ * ((a0 * a2) * x) := by group
      _ = x⁻¹ * (x * (a0 * a2)) := by rw [hb]
      _ = a0 * a2 := by group
  have e3 : a2 * a3 = a0 * a1 := by
    have h1 : a2 * (a1 * a3) = a2 * (a0 * a2) := by rw [e]
    have h2 : a1 * (a2 * a3) = a0 := by
      calc a1 * (a2 * a3) = (a1 * a2) * a3 := by rw [mul_assoc]
        _ = (a2 * a1) * a3 := by rw [c12]
        _ = a2 * (a1 * a3) := by rw [mul_assoc]
        _ = a2 * (a0 * a2) := h1
        _ = (a2 * a0) * a2 := by rw [mul_assoc]
        _ = (a0 * a2) * a2 := by rw [c02]
        _ = a0 := by rw [mul_assoc, s2, mul_one]
    have h3 : a2 * a3 = a1 * a0 := by
      calc a2 * a3 = a1 * (a1 * (a2 * a3)) := by rw [← mul_assoc, s1, one_mul]
        _ = a1 * a0 := by rw [h2]
    rw [h3, c01]
  have e4 : x⁻¹ * (a0 * a1) * x = a1 * a2 := by
    calc x⁻¹ * (a0 * a1) * x = (x⁻¹ * a0 * x) * (x⁻¹ * a1 * x) := by group
      _ = a1 * a2 := by rw [← h01, ← h12]
  have e5 : x⁻¹ * (a1 * a2) * x = a2 * a3 := by
    calc x⁻¹ * (a1 * a2) * x = (x⁻¹ * a1 * x) * (x⁻¹ * a2 * x) := by group
      _ = a2 * a3 := by rw [← h12, ← h23]
  have hc : x * (a0 * a1) = (a0 * a1) * x := by
    apply hC _ (W.mul_mem m0 m1)
    rw [e4, e5, e3]
  have hc' : x⁻¹ * (a0 * a1) * x = a0 * a1 := by
    calc x⁻¹ * (a0 * a1) * x = x⁻¹ * ((a0 * a1) * x) := by group
      _ = x⁻¹ * (x * (a0 * a1)) := by rw [hc]
      _ = a0 * a1 := by group
  rw [e4] at hc'
  have hh : a1 * a2 = a1 * a0 := by rw [hc', c01]
  exact hne (mul_left_cancel hh)

theorem commute_of_inf_eq_bot {G : Type*} [Group G] {W T : Subgroup G} (hTW : T ⊓ W = ⊥)
    {x w : G} (hx : x ∈ T) (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hwW : w ∈ W)
    (hwT : w ∈ Subgroup.normalizer (T : Set G)) : x * w = w * x := by
  have h1 : w⁻¹ * x⁻¹ * w * x ∈ T := by
    have hw' : w⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).inv_mem hwT
    have := (Subgroup.mem_normalizer_iff.mp hw' x⁻¹).mp (T.inv_mem hx)
    simpa [mul_assoc] using T.mul_mem this hx
  have h2 : w⁻¹ * x⁻¹ * w * x ∈ W := by
    have hx' : x⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      (Subgroup.normalizer (W : Set G)).inv_mem hxW
    have := (Subgroup.mem_normalizer_iff.mp hx' w).mp hwW
    have h3 := W.mul_mem (W.inv_mem hwW) this
    simpa [mul_assoc] using h3
  have h3 : w⁻¹ * x⁻¹ * w * x ∈ T ⊓ W := ⟨h1, h2⟩
  rw [hTW, Subgroup.mem_bot] at h3
  have h4 : x⁻¹ * w * x = w := by
    calc x⁻¹ * w * x = w * (w⁻¹ * x⁻¹ * w * x) := by group
      _ = w := by rw [h3, mul_one]
  calc x * w = x * (x⁻¹ * w * x) := by rw [h4]
    _ = w * x := by group

theorem mem_normalizer_of_two_subgroup {G : Type*} [Group G] {K : Subgroup G}
    (hK : TightlyEmbedded K) {g : G} {X : Subgroup G} (hX2 : IsPGroup 2 X) (hX1 : X ≠ ⊥)
    (hXK : X ≤ K ⊓ CFSG.conjugate K g) : g ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hg
  have hodd : Odd (Nat.card (K ⊓ CFSG.conjugate K g : Subgroup G)) := hK.2 g hg
  have hdvd : Nat.card X ∣ Nat.card (K ⊓ CFSG.conjugate K g : Subgroup G) :=
    Subgroup.card_dvd_of_le hXK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX2.card_eq_or_dvd with h1 | h2
  · exact hX1 (Subgroup.card_eq_one.mp h1)
  · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))

structure Setup {G : Type*} [Group G] (K H Q S : Subgroup G) : Prop where
  tight : TightlyEmbedded K
  sylow : IsSylowTwoOf Q (H ⊓ K)
  ne_bot : Q ≠ ⊥
  two : IsPGroup 2 S
  S_le : S ≤ H
  Q_le : Q ≤ S

section Basic

variable {G : Type*} [Group G] {K H Q S : Subgroup G}

theorem Setup.Q_le_K (h : Setup K H Q S) : Q ≤ K := h.sylow.1.trans inf_le_right

theorem Setup.eq_inf [Finite G] (h : Setup K H Q S) : S ⊓ K = Q :=
  h.sylow.eq_of_le (le_inf h.Q_le h.Q_le_K) (inf_le_inf_right K h.S_le) (h.two.to_le inf_le_left)

theorem Setup.conj_mem [Finite G] (h : Setup K H Q S) {g : G} (hg : g ∈ H) (hQS : CFSG.conjugate Q g ≤ S) :
    Setup (CFSG.conjugate K g) H (CFSG.conjugate Q g) S := by
  refine ⟨rightConjugate_tightlyEmbedded K h.tight g, ?_, ?_, h.two, h.S_le, hQS⟩
  · have h1 := h.sylow.map_equiv (MulAut.conj g⁻¹)
    have hH : CFSG.conjugate H g = H :=
      conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg)
    have h2 : IsSylowTwoOf (CFSG.conjugate Q g) (CFSG.conjugate (H ⊓ K) g) := h1
    rwa [conjugate_inf, hH] at h2
  · intro hbot
    apply h.ne_bot
    have := card_conjugate Q g
    rw [hbot] at this
    exact Subgroup.card_eq_one.mp (by simpa using this.symm)

theorem Setup.inf_conjugate_eq_bot [Finite G] (h : Setup K H Q S) {g : G} (hg : g ∈ H)
    (hQS : CFSG.conjugate Q g ≤ S) (hne : CFSG.conjugate Q g ≠ Q) :
    Q ⊓ CFSG.conjugate Q g = ⊥ := by
  by_contra hne'
  have hgK : g ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_two_subgroup h.tight (h.two.to_le (inf_le_left.trans h.Q_le)) hne'
      (inf_le_inf h.Q_le_K (conjugate_mono h.Q_le_K g))
  have hK' : CFSG.conjugate K g = K := conjugate_eq_iff_mem_normalizer.mpr hgK
  have h1 := (h.conj_mem hg hQS).eq_inf
  rw [hK', h.eq_inf] at h1
  exact hne h1.symm

theorem Setup.normalizer_le [Finite G] (h : Setup K H Q S) {X : Subgroup G} (hXQ : X ≤ Q)
    (hX1 : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      S ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  have hnK : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    have hXg : CFSG.conjugate X g = X := conjugate_eq_iff_mem_normalizer.mpr hg
    refine mem_normalizer_of_two_subgroup h.tight (h.two.to_le (hXQ.trans h.Q_le)) hX1 ?_
    refine le_inf (hXQ.trans h.Q_le_K) ?_
    rw [← hXg]
    exact conjugate_mono (hXQ.trans h.Q_le_K) g
  refine ⟨hnK, fun g hg => ?_⟩
  have hgK := hnK hg.2
  have hK' : CFSG.conjugate K g = K := conjugate_eq_iff_mem_normalizer.mpr hgK
  have hS' : CFSG.conjugate S g = S :=
    conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg.1)
  rw [← conjugate_eq_iff_mem_normalizer, ← h.eq_inf, conjugate_inf, hK', hS']

theorem card_mul_le_card_of_inf_eq_bot [Finite G] {A B N : Subgroup G} (hA : A ≤ N) (hB : B ≤ N)
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card N := by
  have hinj : Function.Injective
      (fun p : A × B => (⟨(p.1 : G) * p.2, N.mul_mem (hA p.1.2) (hB p.2.2)⟩ : N)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    have ha_eq : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [hmem, mul_one]
    subst ha_eq
    have hb_eq : b = b' := mul_left_cancel h1
    subst hb_eq
    rfl
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_prod] using this

theorem Setup.normal_of_card_le [Finite G] (h : Setup K H Q S) (hcard : Nat.card S ≤ Nat.card Q ^ 2) :
    S ≤ Subgroup.normalizer (Q : Set G) := by
  by_contra hS
  set N : Subgroup G := S ⊓ Subgroup.normalizer (Q : Set G) with hN
  have hNS : N < S := lt_of_le_of_ne inf_le_left (fun e => hS (e ▸ inf_le_right))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs, hsN⟩ := exists_mem_inf_normalizer_of_ne (p := 2) h.two hNS.le hNS.ne
  have hQN : Q ≤ N := le_inf h.Q_le Subgroup.le_normalizer
  have hQsN : CFSG.conjugate Q s ≤ N := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    exact (Subgroup.mem_normalizer_iff.mp hs.2 x).mpr (hQN hx)
  have hne : CFSG.conjugate Q s ≠ Q := fun e => hsN ⟨hs.1, conjugate_eq_iff_mem_normalizer.mp e⟩
  have hbot := h.inf_conjugate_eq_bot (h.S_le hs.1) (hQsN.trans inf_le_left) hne
  have hcard' := card_mul_le_card_of_inf_eq_bot hQN hQsN hbot
  rw [card_conjugate] at hcard'
  have hlt := Subgroup.card_lt_of_lt hNS
  have h3 : Nat.card Q * Nat.card Q < Nat.card Q ^ 2 :=
    lt_of_le_of_lt hcard' (lt_of_lt_of_le hlt hcard)
  rw [sq] at h3
  exact lt_irrefl _ h3

theorem Setup.commute_of_conj [Finite G] (h : Setup K H Q S) {g : G} (hg : g ∈ H)
    (hne : CFSG.conjugate Q g ≠ Q)
    (hQg : CFSG.conjugate Q g ≤ S ⊓ Subgroup.normalizer (Q : Set G)) :
    ∀ a ∈ Q, ∀ b ∈ CFSG.conjugate Q g, a * b = b * a := by
  have hn : CFSG.conjugate Q g ≤ Subgroup.normalizer (Q : Set G) := hQg.trans inf_le_right
  have hbot : Q ⊓ CFSG.conjugate Q g = ⊥ :=
    h.inf_conjugate_eq_bot hg (hQg.trans inf_le_left) hne
  have hS'le : Q ⊔ CFSG.conjugate Q g ≤ S := sup_le h.Q_le (hQg.trans inf_le_left)
  have hh : Setup (CFSG.conjugate K g) H (CFSG.conjugate Q g) (Q ⊔ CFSG.conjugate Q g) := by
    have h0 := h.conj_mem hg (hQg.trans inf_le_left)
    exact ⟨h0.tight, h0.sylow, h0.ne_bot, h.two.to_le hS'le, hS'le.trans h.S_le, le_sup_right⟩
  have hcardS' : Nat.card ↥(Q ⊔ CFSG.conjugate Q g) ≤ Nat.card ↥(CFSG.conjugate Q g) ^ 2 := by
    have hsurj : Function.Surjective
        (fun p : Q × CFSG.conjugate Q g => (⟨(p.1 : G) * p.2,
          (Q ⊔ CFSG.conjugate Q g).mul_mem (Subgroup.mem_sup_left p.1.2)
            (Subgroup.mem_sup_right p.2.2)⟩ : ↥(Q ⊔ CFSG.conjugate Q g))) := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_le_normalizer hn hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, card_conjugate] at this
    rw [card_conjugate] at *
    rw [sq]
    simpa [card_conjugate] using this
  have hnorm := hh.normal_of_card_le hcardS'
  have hQn : Q ≤ Subgroup.normalizer (CFSG.conjugate Q g : Set G) := le_sup_left.trans hnorm
  intro a ha b hb
  have h1 : a * b * a⁻¹ ∈ CFSG.conjugate Q g :=
    (Subgroup.mem_normalizer_iff.mp (hQn ha) b).mp hb
  have h2 : b * a⁻¹ * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hn hb) a⁻¹).mp (Q.inv_mem ha)
  have h3q : a * b * a⁻¹ * b⁻¹ ∈ Q := by
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact Q.mul_mem ha h2
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ Q ⊓ CFSG.conjugate Q g :=
    ⟨h3q, (CFSG.conjugate Q g).mul_mem h1 ((CFSG.conjugate Q g).inv_mem hb)⟩
  rw [hbot, Subgroup.mem_bot] at h3
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

end Basic

section Delta

variable {G : Type*} [Group G] {K H Q S : Subgroup G}

@[expose] def Delta (H Q S : Subgroup G) : Set (Subgroup G) :=
  {R | (∃ h ∈ H, R = CFSG.conjugate Q h) ∧ R ≤ S}

theorem Setup.mem_delta_self (h : Setup K H Q S) : Q ∈ Delta H Q S :=
  ⟨⟨1, H.one_mem, (conjugate_one Q).symm⟩, h.Q_le⟩

theorem Setup.setup_of_mem [Finite G] (h : Setup K H Q S) {R : Subgroup G} (hR : R ∈ Delta H Q S) :
    ∃ K', Setup K' H R S := by
  obtain ⟨⟨g, hg, rfl⟩, hRS⟩ := hR
  exact ⟨_, h.conj_mem hg hRS⟩

theorem Setup.conj_mem_delta (h : Setup K H Q S) {R : Subgroup G} (hR : R ∈ Delta H Q S)
    {s : G} (hs : s ∈ S) : CFSG.conjugate R s ∈ Delta H Q S := by
  obtain ⟨⟨g, hg, rfl⟩, hRS⟩ := hR
  refine ⟨⟨g * s, H.mul_mem hg (h.S_le hs), (conjugate_conjugate Q g s)⟩, ?_⟩
  intro x hx
  rw [mem_conjugate_iff] at hx
  have := S.mul_mem (S.mul_mem (S.inv_mem hs) (hRS hx)) hs
  simpa [mul_assoc] using this

theorem nonelem_of_mem_delta (hΦ : ∃ y ∈ Q, y ^ 2 ≠ 1) {R : Subgroup G}
    (hR : R ∈ Delta H Q S) : ∃ y ∈ R, y ^ 2 ≠ 1 := by
  obtain ⟨⟨g, hg, rfl⟩, hRS⟩ := hR
  obtain ⟨y, hy, hy2⟩ := hΦ
  refine ⟨g⁻¹ * y * g, ?_, ?_⟩
  · rw [mem_conjugate_iff]
    simpa [mul_assoc] using hy
  · intro h2
    apply hy2
    have e : (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g := by
      rw [sq, sq]; group
    rw [e] at h2
    have h3 : y ^ 2 = g * (g⁻¹ * y ^ 2 * g) * g⁻¹ := by group
    rw [h3, h2]; group

theorem Setup.commute_of_mem_delta [Finite G] (h : Setup K H Q S) {R R' : Subgroup G}
    (hR : R ∈ Delta H Q S) (hR' : R' ∈ Delta H Q S) (hne : R' ≠ R)
    (hn : R' ≤ S ⊓ Subgroup.normalizer (R : Set G)) :
    ∀ a ∈ R, ∀ b ∈ R', a * b = b * a := by
  obtain ⟨K', hK'⟩ := h.setup_of_mem hR
  obtain ⟨⟨g, hg, rfl⟩, hRS⟩ := hR
  obtain ⟨⟨k, hk, rfl⟩, hR'S⟩ := hR'
  have e : CFSG.conjugate (CFSG.conjugate Q g) (g⁻¹ * k) = CFSG.conjugate Q k := by
    rw [conjugate_conjugate]; simp
  rw [← e] at hne hn ⊢
  exact hK'.commute_of_conj (H.mul_mem (H.inv_mem hg) hk) hne hn

theorem Setup.normalizer_le_of_mem [Finite G] (h : Setup K H Q S) {R : Subgroup G}
    (hR : R ∈ Delta H Q S) {X : Subgroup G} (hXR : X ≤ R) (hX1 : X ≠ ⊥) :
    S ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (R : Set G) := by
  obtain ⟨K', hK'⟩ := h.setup_of_mem hR
  exact (hK'.normalizer_le hXR hX1).2

end Delta

section Families

variable {G : Type*} [Group G]

@[expose] def CommFam (Γ : Set (Subgroup G)) : Prop :=
  ∀ R₁ ∈ Γ, ∀ R₂ ∈ Γ, R₁ ≠ R₂ → ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a

@[expose] def NormAll (x : G) (Γ : Set (Subgroup G)) : Prop :=
  ∀ R ∈ Γ, CFSG.conjugate R x ∈ Γ ∧ CFSG.conjugate R x⁻¹ ∈ Γ

theorem NormAll.inv {x : G} {Γ : Set (Subgroup G)} (h : NormAll x Γ) : NormAll x⁻¹ Γ := by
  intro R hR
  refine ⟨(h R hR).2, ?_⟩
  rw [inv_inv]
  exact (h R hR).1

theorem NormAll.mul {x y : G} {Γ : Set (Subgroup G)} (hx : NormAll x Γ) (hy : NormAll y Γ) :
    NormAll (x * y) Γ := by
  intro R hR
  refine ⟨?_, ?_⟩
  · rw [← conjugate_conjugate]
    exact (hy _ (hx R hR).1).1
  · rw [mul_inv_rev, ← conjugate_conjugate]
    exact (hx _ (hy R hR).2).2

theorem NormAll.one {Γ : Set (Subgroup G)} : NormAll (1 : G) Γ := by
  intro R hR
  simpa [conjugate_one] using And.intro hR hR

@[expose] def Stab (S : Subgroup G) (Γ : Set (Subgroup G)) : Subgroup G where
  carrier := {s | s ∈ S ∧ NormAll s Γ}
  mul_mem' := fun ha hb => ⟨S.mul_mem ha.1 hb.1, ha.2.mul hb.2⟩
  one_mem' := ⟨S.one_mem, NormAll.one⟩
  inv_mem' := fun ha => ⟨S.inv_mem ha.1, ha.2.inv⟩

@[expose] def Wgen (Γ : Set (Subgroup G)) : Subgroup G := Subgroup.closure {x | ∃ R ∈ Γ, x ∈ R}

theorem le_Wgen {Γ : Set (Subgroup G)} {R : Subgroup G} (hR : R ∈ Γ) : R ≤ Wgen Γ :=
  fun _ hx => Subgroup.subset_closure ⟨R, hR, hx⟩

theorem Wgen_le_of_le {Γ : Set (Subgroup G)} {S : Subgroup G} (h : ∀ R ∈ Γ, R ≤ S) :
    Wgen Γ ≤ S := by
  unfold Wgen
  rw [Subgroup.closure_le]
  rintro x ⟨R, hR, hx⟩
  exact h R hR hx

theorem Wgen_le_normalizer {Γ : Set (Subgroup G)} (hΓ : CommFam Γ) {R : Subgroup G}
    (hR : R ∈ Γ) : Wgen Γ ≤ Subgroup.normalizer (R : Set G) := by
  unfold Wgen
  rw [Subgroup.closure_le]
  rintro x ⟨R', hR', hx⟩
  by_cases hRR : R' = R
  · subst hRR
    exact Subgroup.le_normalizer hx
  · exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (hΓ R' hR' R hR hRR x hx h hh).symm)

theorem normAll_of_mem {Γ : Set (Subgroup G)} (hΓ : CommFam Γ) {R : Subgroup G} (hR : R ∈ Γ)
    {x : G} (hx : x ∈ R) : NormAll x Γ := by
  have hN : ∀ R' ∈ Γ, CFSG.conjugate R' x = R' := by
    intro R' hR'
    rw [conjugate_eq_iff_mem_normalizer]
    exact Wgen_le_normalizer hΓ hR' (le_Wgen hR hx)
  intro R' hR'
  refine ⟨?_, ?_⟩
  · rw [hN R' hR']; exact hR'
  · have : x⁻¹ ∈ Subgroup.normalizer (R' : Set G) :=
      (Subgroup.normalizer (R' : Set G)).inv_mem (Wgen_le_normalizer hΓ hR' (le_Wgen hR hx))
    rw [conjugate_eq_iff_mem_normalizer.mpr this]; exact hR'

theorem Wgen_le_stab {Γ : Set (Subgroup G)} {S : Subgroup G} (hΓ : CommFam Γ)
    (hS : ∀ R ∈ Γ, R ≤ S) : Wgen Γ ≤ Stab S Γ := by
  unfold Wgen
  rw [Subgroup.closure_le]
  rintro x ⟨R, hR, hx⟩
  exact ⟨hS R hR hx, normAll_of_mem hΓ hR hx⟩

theorem conj_mem_Wgen {Γ : Set (Subgroup G)} {g : G} (hg : NormAll g Γ) {w : G}
    (hw : w ∈ Wgen Γ) : g * w * g⁻¹ ∈ Wgen Γ := by
  unfold Wgen at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨R, hR, hyR⟩ := hy
    have : g * y * g⁻¹ ∈ CFSG.conjugate R g⁻¹ := by
      rw [mem_conjugate_iff]
      have e : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y := by group
      rw [e]; exact hyR
    exact Subgroup.subset_closure ⟨_, (hg R hR).2, this⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

theorem mem_normalizer_Wgen {Γ : Set (Subgroup G)} {g : G} (hg : NormAll g Γ) :
    g ∈ Subgroup.normalizer (Wgen Γ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => conj_mem_Wgen hg hw, fun hw => ?_⟩
  have := conj_mem_Wgen hg.inv hw
  simpa [mul_assoc] using this

end Families

section Main

variable {G : Type*} [Group G] [Finite G] {K H Q S : Subgroup G}

theorem star (h : Setup K H Q S) {Γ : Set (Subgroup G)} (hΓΔ : Γ ⊆ Delta H Q S)
    (hΓ : CommFam Γ) {T : Subgroup G} (hTΔ : T ∈ Delta H Q S) (hT : ∀ x ∈ T, NormAll x Γ)
    (hTΓ : T ∉ Γ) {R : Subgroup G} (hR : R ∈ Γ)
    (hnb : T ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥) :
    ∀ a ∈ T, ∀ b ∈ R, a * b = b * a := by
  have hRΔ := hΓΔ hR
  have hT2 : IsPGroup 2 T := h.two.to_le hTΔ.2
  have hR2 : IsPGroup 2 R := h.two.to_le hRΔ.2
  obtain ⟨K', hK'⟩ := h.setup_of_mem hRΔ
  have hR1 : R ≠ ⊥ := hK'.ne_bot
  have hTS : T ≤ S := hTΔ.2
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnb
  have hx₀' : x₀ ≠ 1 := fun e => hx₀1 (Subtype.ext e)
  obtain ⟨n, hn1, hn2⟩ := exists_involution_pow hT2 hx₀.1 hx₀'
  have hx₁T : x₀ ^ n ∈ T := T.pow_mem hx₀.1 n
  have hx₁N : x₀ ^ n ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normalizer (R : Set G)).pow_mem hx₀.2 n
  have hzp : IsPGroup 2 (Subgroup.zpowers (x₀ ^ n)) :=
    hT2.to_le (Subgroup.zpowers_le.mpr hx₁T)
  obtain ⟨z, hzR, hz1, hz2, hzc, hzx⟩ := exists_central_involution hR2 hR1 hx₁N hzp
  have hzW : ∀ w ∈ Wgen Γ, z * w = w * z := by
    have : Wgen Γ ≤ Subgroup.centralizer ({z} : Set G) := by
      unfold Wgen
      rw [Subgroup.closure_le]
      rintro y ⟨R', hR', hy⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      by_cases hRR : R = R'
      · subst hRR; exact hzc y hy
      · exact hΓ R hR R' hR' hRR g hzR y hy
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (this hw)) z (Set.mem_singleton z)
  have hzS : z ∈ S := hRΔ.2 hzR
  have hzT : z ∈ Subgroup.normalizer (T : Set G) := by
    have hx1ne : Subgroup.zpowers (x₀ ^ n) ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]; exact hn1
    exact h.normalizer_le_of_mem hTΔ (Subgroup.zpowers_le.mpr hx₁T) hx1ne
      ⟨hzS, mem_normalizer_zpowers_of_commute hzx⟩
  by_cases hcen : ∀ τ ∈ T, z * τ = τ * z
  · have hz1' : Subgroup.zpowers z ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]; exact hz1
    have hTN : T ≤ S ⊓ Subgroup.normalizer (R : Set G) := fun τ hτ =>
      ⟨hTS hτ, h.normalizer_le_of_mem hRΔ (Subgroup.zpowers_le.mpr hzR) hz1'
        ⟨hTS hτ, mem_normalizer_zpowers_of_commute (hcen τ hτ).symm⟩⟩
    have hRT : R ≠ T := fun e => hTΓ (e ▸ hR)
    intro a ha b hb
    exact (h.commute_of_mem_delta hRΔ hTΔ (Ne.symm hRT) hTN b hb a ha).symm
  · have hcen' : ∃ τ ∈ T, z * τ ≠ τ * z := by
      by_contra hcon
      exact hcen fun τ hτ => by by_contra hh; exact hcon ⟨τ, hτ, hh⟩
    obtain ⟨τ, hτ, hzτ⟩ := hcen'
    set c : G := z⁻¹ * τ⁻¹ * z * τ with hc
    have hc1 : c ≠ 1 := by
      intro e
      apply hzτ
      have h1 : τ⁻¹ * z * τ = z := by
        calc τ⁻¹ * z * τ = z * (z⁻¹ * τ⁻¹ * z * τ) := by group
          _ = z := by rw [← hc, e, mul_one]
      calc z * τ = τ * (τ⁻¹ * z * τ) := by group
        _ = τ * z := by rw [h1]
    have hcT : c ∈ T := by
      have h1 : z⁻¹ * τ⁻¹ * z ∈ T := by
        have hzi : z⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
          (Subgroup.normalizer (T : Set G)).inv_mem hzT
        have := (Subgroup.mem_normalizer_iff.mp hzi τ⁻¹).mp (T.inv_mem hτ)
        simpa [mul_assoc] using this
      exact T.mul_mem h1 hτ
    have hcW : ∀ w ∈ Wgen Γ, c * w = w * c := by
      intro w hw
      have hwτ : τ * w * τ⁻¹ ∈ Wgen Γ := conj_mem_Wgen (hT τ hτ) hw
      have h1' : z * (τ * w * τ⁻¹) = (τ * w * τ⁻¹) * z := hzW _ hwτ
      have h2 := hzW w hw
      have h2' : z⁻¹ * w = w * z⁻¹ := by
        calc z⁻¹ * w = z⁻¹ * (w * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * w) * z⁻¹ := by rw [h2]
          _ = w * z⁻¹ := by group
      calc c * w = z⁻¹ * τ⁻¹ * (z * (τ * w * τ⁻¹)) * τ := by simp only [hc]; group
        _ = z⁻¹ * τ⁻¹ * ((τ * w * τ⁻¹) * z) * τ := by rw [h1']
        _ = z⁻¹ * w * (τ⁻¹ * z * τ) := by group
        _ = w * z⁻¹ * (τ⁻¹ * z * τ) := by rw [h2']
        _ = w * c := by simp only [hc]; group
    have hcen2 : ∀ r ∈ R, r * c = c * r := fun r hr => (hcW r (le_Wgen hR hr)).symm
    have hc1' : Subgroup.zpowers c ≠ ⊥ := by rw [Ne, Subgroup.zpowers_eq_bot]; exact hc1
    have hRN : R ≤ S ⊓ Subgroup.normalizer (T : Set G) := fun r hr =>
      ⟨hRΔ.2 hr, h.normalizer_le_of_mem hTΔ (Subgroup.zpowers_le.mpr hcT) hc1'
        ⟨hRΔ.2 hr, mem_normalizer_zpowers_of_commute (hcen2 r hr)⟩⟩
    have hRT : R ≠ T := fun e => hTΓ (e ▸ hR)
    intro a ha b hb
    exact h.commute_of_mem_delta hTΔ hRΔ hRT hRN a ha b hb

theorem delta_subset_of_normalizing (h : Setup K H Q S) {Γ : Set (Subgroup G)}
    (hΓΔ : Γ ⊆ Delta H Q S) (hΓ : CommFam Γ)
    (hA : ∀ T ∈ Delta H Q S, (∀ x ∈ T, NormAll x Γ) → T ∈ Γ) : Delta H Q S ⊆ Γ := by
  set N := Stab S Γ with hN
  have hNS : N ≤ S := fun x hx => hx.1
  have hWN : Wgen Γ ≤ N := Wgen_le_stab hΓ (fun R hR => (hΓΔ hR).2)
  have key : ∀ T ∈ Delta H Q S, T ≤ N → T ∈ Γ := fun T hT hTN =>
    hA T hT (fun x hx => (hTN hx).2)
  have hself : S ⊓ Subgroup.normalizer (N : Set G) ≤ N := by
    have hconj : ∀ s' ∈ S ⊓ Subgroup.normalizer (N : Set G), ∀ R ∈ Γ,
        CFSG.conjugate R s' ∈ Γ := by
      intro s' hs' R hR
      have hRN : R ≤ N := (le_Wgen hR).trans hWN
      apply key _ (h.conj_mem_delta (hΓΔ hR) hs'.1)
      intro y hy
      rw [mem_conjugate_iff] at hy
      have hs'inv : s'⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
        (Subgroup.normalizer (N : Set G)).inv_mem hs'.2
      have := (Subgroup.mem_normalizer_iff.mp hs'inv (s' * y * s'⁻¹)).mp (hRN hy)
      simpa [mul_assoc] using this
    intro s hs
    refine ⟨hs.1, fun R hR => ⟨hconj s hs R hR, ?_⟩⟩
    exact hconj s⁻¹ ⟨S.inv_mem hs.1, (Subgroup.normalizer (N : Set G)).inv_mem hs.2⟩ R hR
  have hNeq : N = S := by
    by_contra hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx, hxN⟩ := exists_mem_inf_normalizer_of_ne (p := 2) h.two hNS hne
    exact hxN (hself hx)
  intro T hT
  exact key T hT (hNeq ▸ hT.2)

theorem false_of_normalizing (h : Setup K H Q S) (hΦ : ∃ y ∈ Q, y ^ 2 ≠ 1)
    {Γ : Set (Subgroup G)} (hΓΔ : Γ ⊆ Delta H Q S) (hΓ : CommFam Γ)
    (hmax : ∀ Γ' : Set (Subgroup G), Γ ⊆ Γ' → Γ' ⊆ Delta H Q S → CommFam Γ' → Γ' = Γ)
    {T : Subgroup G} (hTΔ : T ∈ Delta H Q S) (hT : ∀ x ∈ T, NormAll x Γ) (hTΓ : T ∉ Γ) :
    False := by
  have hT2 : IsPGroup 2 T := h.two.to_le hTΔ.2
  have hTS : T ≤ S := hTΔ.2
  obtain ⟨R₀, hR₀, hnc⟩ : ∃ R ∈ Γ, ¬ ∀ a ∈ T, ∀ b ∈ R, a * b = b * a := by
    by_contra hcon
    have hcon' : ∀ R ∈ Γ, ∀ a ∈ T, ∀ b ∈ R, a * b = b * a := fun R hR => by
      by_contra hh; exact hcon ⟨R, hR, hh⟩
    have hins : insert T Γ = Γ := by
      refine hmax _ (Set.subset_insert _ _) (Set.insert_subset hTΔ hΓΔ) ?_
      intro R₁ h₁ R₂ h₂ hne a ha b hb
      rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
      · exact absurd rfl hne
      · exact hcon' R₂ h₂ a ha b hb
      · exact (hcon' R₁ h₁ b hb a ha).symm
      · exact hΓ R₁ h₁ R₂ h₂ hne a ha b hb
    exact hTΓ (hins ▸ Set.mem_insert _ _)
  have hR₀Δ := hΓΔ hR₀
  obtain ⟨K₀, hK₀⟩ := h.setup_of_mem hR₀Δ
  have hN : T ⊓ Subgroup.normalizer (R₀ : Set G) = ⊥ := by
    by_contra hne
    exact hnc (star h hΓΔ hΓ hTΔ hT hTΓ hR₀ hne)
  set W := Wgen Γ with hW
  have hWR₀ : W ≤ Subgroup.normalizer (R₀ : Set G) := Wgen_le_normalizer hΓ hR₀
  have hTW : T ⊓ W = ⊥ := le_bot_iff.mp (hN ▸ inf_le_inf_left T hWR₀)
  have hWS : W ≤ S := Wgen_le_of_le (fun R hR => (hΓΔ hR).2)
  obtain ⟨y, hyT, hy2⟩ := nonelem_of_mem_delta hΦ hTΔ
  obtain ⟨x, hxT, hx2, hx4⟩ := exists_order_four hT2 hyT hy2
  have hx1 : x ≠ 1 := fun e => hx2 (by rw [e]; simp)
  have hxx1 : x * x ≠ 1 := by rw [← sq]; exact hx2
  have hxxT : x * x ∈ T := T.mul_mem hxT hxT
  have hxH : x ∈ H := h.S_le (hTS hxT)
  have hR₁ : CFSG.conjugate R₀ x ∈ Γ := (hT x hxT R₀ hR₀).1
  have hR₂ : CFSG.conjugate (CFSG.conjugate R₀ x) x ∈ Γ := (hT x hxT _ hR₁).1
  have hR₂' : CFSG.conjugate (CFSG.conjugate R₀ x) x = CFSG.conjugate R₀ (x * x) :=
    conjugate_conjugate _ _ _
  have hne01 : R₀ ≠ CFSG.conjugate R₀ x := by
    intro e
    have : x ∈ T ⊓ Subgroup.normalizer (R₀ : Set G) :=
      ⟨hxT, conjugate_eq_iff_mem_normalizer.mp e.symm⟩
    rw [hN] at this
    exact hx1 (Subgroup.mem_bot.mp this)
  have hne02 : R₀ ≠ CFSG.conjugate (CFSG.conjugate R₀ x) x := by
    intro e
    rw [hR₂'] at e
    have : x * x ∈ T ⊓ Subgroup.normalizer (R₀ : Set G) :=
      ⟨hxxT, conjugate_eq_iff_mem_normalizer.mp e.symm⟩
    rw [hN] at this
    exact hxx1 (Subgroup.mem_bot.mp this)
  have hne12 : CFSG.conjugate R₀ x ≠ CFSG.conjugate (CFSG.conjugate R₀ x) x := by
    intro e
    exact hne01 (conjugate_inj.mp e.symm).symm
  obtain ⟨⟨y₀, hy₀⟩, hy₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK₀.ne_bot
  have hy₀' : y₀ ≠ 1 := fun e => hy₀1 (Subtype.ext e)
  obtain ⟨m, hm1, hm2⟩ := exists_involution_pow (h.two.to_le hR₀Δ.2) hy₀ hy₀'
  set u : G := y₀ ^ m with hu
  have huR : u ∈ R₀ := R₀.pow_mem hy₀ m
  have hu1 : u ≠ 1 := hm1
  have huu : u * u = 1 := by rw [← sq]; exact hm2
  set a1 : G := x⁻¹ * u * x with ha1
  set a2 : G := x⁻¹ * a1 * x with ha2
  set a3 : G := x⁻¹ * a2 * x with ha3
  have ha1R : a1 ∈ CFSG.conjugate R₀ x := by
    rw [mem_conjugate_iff]
    have : x * a1 * x⁻¹ = u := by rw [ha1]; group
    rw [this]; exact huR
  have ha2R : a2 ∈ CFSG.conjugate (CFSG.conjugate R₀ x) x := by
    rw [mem_conjugate_iff]
    have : x * a2 * x⁻¹ = a1 := by rw [ha2]; group
    rw [this]; exact ha1R
  have hx4' : u = x⁻¹ * a3 * x := by
    have e4 : x * x * x * x = 1 := by
      have : x * x * x * x = x ^ 4 := by simp [pow_succ, mul_assoc]
      rw [this, hx4]
    calc u = (x * x * x * x)⁻¹ * u * (x * x * x * x) := by rw [e4]; group
      _ = x⁻¹ * a3 * x := by simp only [ha3, ha2, ha1]; group
  have s1 : a1 * a1 = 1 := by
    calc a1 * a1 = x⁻¹ * (u * u) * x := by rw [ha1]; group
      _ = 1 := by rw [huu]; group
  have s2 : a2 * a2 = 1 := by
    calc a2 * a2 = x⁻¹ * (a1 * a1) * x := by rw [ha2]; group
      _ = 1 := by rw [s1]; group
  have c01 : u * a1 = a1 * u := hΓ _ hR₀ _ hR₁ hne01 u huR a1 ha1R
  have c02 : u * a2 = a2 * u := hΓ _ hR₀ _ hR₂ hne02 u huR a2 ha2R
  have c12 : a1 * a2 = a2 * a1 := hΓ _ hR₁ _ hR₂ hne12 a1 ha1R a2 ha2R
  have m0 : u ∈ W := le_Wgen hR₀ huR
  have m1 : a1 ∈ W := le_Wgen hR₁ ha1R
  have m2 : a2 ∈ W := le_Wgen hR₂ ha2R
  have hC : ∀ w ∈ W, x⁻¹ * (x⁻¹ * w * x) * x = w → x * w = w * x := by
    intro w hw hfix
    have hcomm : w * (x * x) = (x * x) * w := by
      calc w * (x * x) = (x * x) * ((x * x)⁻¹ * w * (x * x)) := by group
        _ = (x * x) * (x⁻¹ * (x⁻¹ * w * x) * x) := by congr 1; group
        _ = (x * x) * w := by rw [hfix]
    have hxx1' : Subgroup.zpowers (x * x) ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]; exact hxx1
    have hwT : w ∈ Subgroup.normalizer (T : Set G) :=
      h.normalizer_le_of_mem hTΔ (Subgroup.zpowers_le.mpr hxxT) hxx1'
        ⟨hWS hw, mem_normalizer_zpowers_of_commute hcomm⟩
    exact commute_of_inf_eq_bot hTW hxT (mem_normalizer_Wgen (hT x hxT)) hw hwT
  have hne : a2 ≠ u := by
    intro e
    have hbot := hK₀.inf_conjugate_eq_bot (g := x * x) (H.mul_mem hxH hxH)
      (hR₂' ▸ (hΓΔ hR₂).2) (hR₂' ▸ hne02.symm)
    have hu' : u ∈ R₀ ⊓ CFSG.conjugate R₀ (x * x) := ⟨huR, hR₂' ▸ (e ▸ ha2R)⟩
    rw [hbot] at hu'
    exact hu1 (Subgroup.mem_bot.mp hu')
  exact final_contradiction (W := W) (x := x) (a0 := u) (a1 := a1) (a2 := a2) (a3 := a3)
    rfl rfl rfl hx4' s1 s2 c01 c02 c12 m0 m1 m2 hC hne

theorem Setup.delta_commute (h : Setup K H Q S) (hΦ : ∃ y ∈ Q, y ^ 2 ≠ 1) :
    ∀ R₁ ∈ Delta H Q S, ∀ R₂ ∈ Delta H Q S, R₁ ≠ R₂ → ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a := by
  obtain ⟨Γ, hΓ, hmax⟩ := Set.Finite.exists_maximal
    (s := {Γ : Set (Subgroup G) | Γ ⊆ Delta H Q S ∧ CommFam Γ}) (Set.toFinite _)
    ⟨∅, Set.empty_subset _, fun R₁ h₁ => (Set.notMem_empty R₁ h₁).elim⟩
  obtain ⟨hΓΔ, hΓc⟩ := hΓ
  have hmax' : ∀ Γ' : Set (Subgroup G), Γ ⊆ Γ' → Γ' ⊆ Delta H Q S → CommFam Γ' → Γ' = Γ :=
    fun Γ' hle hΔ hc => le_antisymm (hmax ⟨hΔ, hc⟩ hle) hle
  have hall : Delta H Q S ⊆ Γ := by
    apply delta_subset_of_normalizing h hΓΔ hΓc
    intro T hTΔ hT
    by_contra hTΓ
    exact false_of_normalizing h hΦ hΓΔ hΓc hmax' hTΔ hT hTΓ
  intro R₁ hR₁ R₂ hR₂ hne a ha b hb
  exact hΓc R₁ (hall hR₁) R₂ (hall hR₂) hne a ha b hb

end Main

end CFSG.QuasithinUnique.Tight
