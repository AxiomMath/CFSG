module

public import CFSG.ClassicalInvolution.AschTight.MuZ2Closed
public import CFSG.ClassicalInvolution.AschTight.CSMD
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem odd_geom_sum {u : ℤ} (hu : Odd u) {m : ℕ} (hm : Odd m) :
    Odd (∑ i ∈ Finset.range m, u ^ i) := by
  have key : ∀ n : ℕ, (Odd (∑ i ∈ Finset.range n, u ^ i) ↔ Odd n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : ¬ Even (u ^ n) := Int.not_even_iff_odd.mpr hu.pow
      rw [Finset.sum_range_succ, Int.odd_add, ih, Nat.odd_add_one]
      simp [hne]
  exact (key m).mpr hm

theorem isCoprime_two_pow_of_odd {c : ℤ} (hc : Odd c) (e : ℕ) : IsCoprime ((2 : ℤ) ^ e) c := by
  obtain ⟨c', rfl⟩ := hc
  exact IsCoprime.pow_left ⟨-c', 1, by ring⟩

namespace SDData

variable {P : Subgroup G} {a b : G} {M : ℕ}

theorem mem_centralizer_of_odd [Finite G] (h : SDData P a b M) {n : G}
    (hnN : n ∈ Subgroup.normalizer (P : Set G)) (hn : Odd (orderOf n)) :
    n ∈ Subgroup.centralizer (P : Set G) := by
  have hM := h.M_pos
  obtain ⟨e, he⟩ := h.pow2
  have h8 : (8 * M : ℤ) = 2 ^ (e + 3) := by rw [he]; push_cast; ring
  set m := orderOf n with hm
  have hnm : n ^ m = 1 := pow_orderOf_eq_one n
  have hconjP : ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hnN x).mp hx
  obtain ⟨u, hu⟩ : ∃ u : ℤ, a ^ u = n * a * n⁻¹ := by
    rcases h.mem_or (hconjP a h.a_mem) with hu | ⟨i, hi⟩
    · exact hu
    · exfalso
      have hord : orderOf (n * a * n⁻¹) = 8 * M := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.ord]
      have hdvd : orderOf (n * a * n⁻¹) ∣ 4 := by
        rw [← hi]
        exact orderOf_dvd_of_pow_eq_one (h.pow_four i)
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  have hσ : ∀ k : ℕ, n ^ k * a * (n ^ k)⁻¹ = a ^ (u ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc n ^ (k + 1) * a * (n ^ (k + 1))⁻¹ = n * (n ^ k * a * (n ^ k)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = a ^ (u ^ (k + 1)) := by
            rw [ih, ← _root_.conj_zpow, ← hu, ← zpow_mul, pow_succ']
  have hu1 : n * a * n⁻¹ = a := by
    have h1 := hσ m
    rw [hnm, one_mul, inv_one, mul_one] at h1
    have h2 : (8 * M : ℤ) ∣ u ^ m - 1 := by
      rw [← h.zpow_eq_one_iff, zpow_sub, zpow_one, ← h1, mul_inv_cancel]
    have hu_odd : Odd u := by
      rcases Int.even_or_odd u with hev | hodd
      · exfalso
        have h3 : (2 : ℤ) ∣ u ^ m - 1 := dvd_trans ⟨4 * M, by ring⟩ h2
        have h4 : (2 : ℤ) ∣ u ^ m := dvd_pow (even_iff_two_dvd.mp hev) hn.pos.ne'
        have h5 := dvd_sub h4 h3
        simp at h5
      · exact hodd
    have hcop : IsCoprime (8 * M : ℤ) (∑ i ∈ Finset.range m, u ^ i) := by
      rw [h8]; exact isCoprime_two_pow_of_odd (odd_geom_sum hu_odd hn) _
    have h3 : (8 * M : ℤ) ∣ (∑ i ∈ Finset.range m, u ^ i) * (u - 1) := by
      rw [geom_sum_mul]; exact h2
    have h4 := hcop.dvd_of_dvd_mul_left h3
    rw [← hu]
    calc a ^ u = a ^ (u - 1) * a := by rw [← zpow_add_one, sub_add_cancel]
      _ = a := by rw [(h.zpow_eq_one_iff _).mpr h4, one_mul]
  have hinv : n⁻¹ * a * n = a := by
    calc n⁻¹ * a * n = n⁻¹ * (n * a * n⁻¹) * n := by rw [hu1]
      _ = a := by group
  have hconjinv : ∀ i : ℤ, n⁻¹ * a ^ i * n = a ^ i := by
    intro i
    have := map_zpow (MulAut.conj n⁻¹) a i
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hinv]
  obtain ⟨v, hv⟩ : ∃ v : ℤ, a ^ v * b = n * b * n⁻¹ := by
    rcases h.mem_or (hconjP b h.b_mem) with ⟨v, hv⟩ | hv
    · exfalso
      apply h.bA
      have : b = a ^ v := by
        calc b = n⁻¹ * (n * b * n⁻¹) * n := by group
          _ = a ^ v := by rw [← hv, hconjinv]
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · exact hv
  have hconjpow : ∀ i : ℤ, n * a ^ i * n⁻¹ = a ^ i := by
    intro i
    rw [← _root_.conj_zpow, hu1]
  have hσb : ∀ k : ℕ, n ^ k * b * (n ^ k)⁻¹ = a ^ ((k : ℤ) * v) * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc n ^ (k + 1) * b * (n ^ (k + 1))⁻¹ = n * (n ^ k * b * (n ^ k)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = (n * a ^ ((k : ℤ) * v) * n⁻¹) * (n * b * n⁻¹) := by rw [ih]; group
        _ = a ^ (((k + 1 : ℕ) : ℤ) * v) * b := by
            rw [hconjpow, ← hv, ← mul_assoc, ← zpow_add]
            congr 2
            push_cast
            ring
  have hb1 : n * b * n⁻¹ = b := by
    have h1 := hσb m
    rw [hnm, one_mul, inv_one, mul_one] at h1
    have h2 : a ^ ((m : ℤ) * v) = 1 := by
      have := congrArg (· * b⁻¹) h1
      simpa using this.symm
    rw [h.zpow_eq_one_iff] at h2
    have hcop : IsCoprime (8 * M : ℤ) (m : ℤ) := by
      rw [h8]
      exact isCoprime_two_pow_of_odd (by exact_mod_cast hn) _
    have h3 := hcop.dvd_of_dvd_mul_left h2
    rw [← hv, (h.zpow_eq_one_iff _).mpr h3, one_mul]
  have hle : P ≤ Subgroup.centralizer ({n} : Set G) := by
    rw [← h.eq]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * n = n * (n⁻¹ * a * n) := by group
        _ = n * a := by rw [hinv]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc b * n = n * b * n⁻¹ * n := by rw [hb1]
        _ = n * b := by group
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem card_le_four_of_isElemAbelian [Finite G] (h : SDData P a b M) {E : Subgroup G}
    (hEP : E ≤ P) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have hM := h.M_pos
  have hAP : Subgroup.zpowers a ≤ P := Subgroup.zpowers_le.mpr h.a_mem
  have hidx : (Subgroup.zpowers a).relIndex P = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers a) (K := P)
    rw [inf_of_le_left hAP, Nat.card_zpowers, h.ord, h.card] at h1
    have : (Subgroup.zpowers a).relIndex P * (8 * M) = 2 * (8 * M) := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have hidxE : (Subgroup.zpowers a).relIndex E ≤ 2 :=
    hidx ▸ Subgroup.relIndex_le_of_le_right hEP (by rw [hidx]; norm_num)
  have h4 : a ^ (4 * (M : ℤ)) * a ^ (4 * (M : ℤ)) = 1 := by
    rw [← zpow_add, h.zpow_eq_one_iff]
    exact ⟨1, by ring⟩
  have h41 : a ^ (4 * (M : ℤ)) ≠ 1 := by
    rw [Ne, h.zpow_eq_one_iff]
    rintro ⟨c, hc⟩
    have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0 <;> omega
  have hle : Subgroup.zpowers a ⊓ E ≤ Subgroup.zpowers (a ^ (4 * (M : ℤ))) := by
    rintro x ⟨hxa, hxE⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa
    by_cases hx1 : a ^ i = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · have hx2 : a ^ i * a ^ i = 1 := by rw [← _root_.sq]; exact hE.2 _ hxE
      rw [zpow_eq_zpow_of_mul_self_eq_one hx2 h4 hx1 h41]
      exact Subgroup.mem_zpowers _
  have hcard2 : Nat.card ↥(Subgroup.zpowers a ⊓ E) ≤ 2 := by
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact h4) h41]
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers a) (K := E)
  rw [← h1]
  calc (Subgroup.zpowers a).relIndex E * Nat.card ↥(Subgroup.zpowers a ⊓ E) ≤ 2 * 2 :=
        Nat.mul_le_mul hidxE hcard2
    _ = 4 := by norm_num

end SDData

@[expose] def GoldschmidtB3Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), A ≤ (S : Subgroup G) →
    fusionStronglyClosed (A : Set G) S →
    (∀ n ∈ Subgroup.normalizer (A : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (A : Set G)) →
    IsSylow2In A (Subgroup.normalClosure (A : Set G))

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem exists_conj_mem_sylow_ne [IsSimpleGroup G] (ht : S19R.TightStd p f K z) (S : Sylow 2 G)
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) ∧ g * z * g⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hI.sq) hI.ne_one
  have hiso : ∀ g : G, g * z * g⁻¹ * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hg
    have hu : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hg
    have hu2 : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]
    obtain ⟨c, hc, hcS⟩ := exists_conj_mem_of_sylow_le S hSz hu hu2
    have h1 := hcon (c * g) (by
      rw [show c * g * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ by group]; exact hcS)
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc g * z * g⁻¹ = c⁻¹ * (c * g * z * (c * g)⁻¹) * c := by group
      _ = c⁻¹ * (z * c) := by rw [h1, mul_assoc]
      _ = z := by rw [← hcz]; group
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G z hI.ne_one hI.sq hiso
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · obtain ⟨x, y, hxy⟩ := ht.branch.nonabelian
    have hzZ : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hN g
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h1]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · rw [hc, Subgroup.mem_bot] at hzZ
      exact hI.ne_one hzZ
    · have := Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top x) y
      exact hxy this.symm
  · rw [htop, Subgroup.card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    obtain ⟨c, hc⟩ := hNodd
    omega

theorem false_of_allTypeTwo (hB3 : GoldschmidtB3Tmp) [IsSimpleGroup G]
    (ht : S19R.TightStd p f K z) (hA : AllTypeTwo K z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  set R : Subgroup G := (Q₀ : Subgroup K).map K.subtype with hRdef
  have hR : R ∈ RSet (CoreAssembly.conjClass K) :=
    ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hzR : IsUniqueInvolution R z := isUniqueInvolution_of_mem_rSet_of_le htb hR hRK
  obtain ⟨S, hRS⟩ := (Q₀.isPGroup'.map K.subtype).exists_le_sylow
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    have hle : conjSubgroup s R ≤ (S : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hRS hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp
      (conjSubgroup_sylow_eq_of_tightD ht Q₀ S.isPGroup' hRS hle)
  have hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hzR.conj_eq (conjSub_eq_of_mem_normalizer (hSN hs))
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h1]
  have hSKR : (S : Subgroup G) ⊓ K ≤ R := by
    have h2 : IsPGroup 2 (((S : Subgroup G) ⊓ K).subgroupOf K) :=
      (S.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (Q₀ : Subgroup K) ≤ ((S : Subgroup G) ⊓ K).subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hRS ⟨x, hx, rfl⟩, x.2⟩
    have heq := Q₀.3 h2 hle
    intro x hx
    have hxK : x ∈ K := hx.2
    have : (⟨x, hxK⟩ : K) ∈ ((S : Subgroup G) ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact ⟨⟨x, hxK⟩, this, rfl⟩
  obtain ⟨g, htS, htz⟩ := exists_conj_mem_sylow_ne ht S hSz
  set t := g * z * g⁻¹ with htdef
  set P := R ⊔ Subgroup.zpowers t with hPdef
  have hPS : P ≤ (S : Subgroup G) := sup_le hRS (Subgroup.zpowers_le.mpr htS)
  have htzc : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hSz htS)
  have hsd := isSemidihedral_sup_of_allTypeTwo ht hA hR hRK (hSN htS) htzc htz
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (S.isPGroup'.to_le hPS) hsd
  have hcl : fusionStronglyClosed (P : Set G) S := by
    intro x hx y hy
    have := mem_sup_of_conj_mem ht hA hR hRK hRS hSKR hSN hSz htS htz hx (y := y⁻¹)
      (by rwa [inv_inv])
    rwa [inv_inv] at this
  have hNC : ∀ n ∈ Subgroup.normalizer (P : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (P : Set G) := by
    intro n hn
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    refine ⟨k, hsdd.mem_centralizer_of_odd (Subgroup.pow_mem _ hn _) ?_⟩
    rw [orderOf_pow' n (pow_ne_zero _ two_ne_zero), hkm,
      Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hB := hB3 G S P hPS hcl hNC
  have hncl : Subgroup.normalClosure (P : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (P : Set G)) with
      h0 | h0
    · exfalso
      have : z ∈ Subgroup.normalClosure (P : Set G) :=
        Subgroup.le_normalClosure (Subgroup.mem_sup_left hzR.mem)
      rw [h0, Subgroup.mem_bot] at this
      exact hI.ne_one this
    · exact h0
  have hPeq : (S : Subgroup G) = P := hB.2.2 _ (hncl ▸ le_top) S.isPGroup' hPS
  have h3 := ht.branch.rank
  unfold CFSG.Open.twoRank CFSG.Open.pRank at h3
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨Nat.card G, fun k ⟨E, _, _, hk⟩ => by
      have h1 : 2 ^ k ≤ Nat.card G := hk ▸ Subgroup.card_le_card_group E
      have h2 : k < 2 ^ k := Nat.lt_two_pow_self
      omega⟩
  have hne : {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}.Nonempty :=
    ⟨0, ⊥, le_top, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by
      rw [Subgroup.mem_bot] at hx; rw [hx, one_pow]⟩, by simp⟩
  obtain ⟨E, -, hE, hEcard⟩ := Nat.sSup_mem hne hbdd
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hEcard
  obtain ⟨T, hET⟩ := hE2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S T
  set E' : Subgroup G := E.map (MulAut.conj c⁻¹).toMonoidHom with hE'
  have hE'P : E' ≤ P := by
    rw [← hPeq]
    rintro _ ⟨x, hx, rfl⟩
    have hxT := hET hx
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxT
    simpa [MulAut.smul_def] using hxT
  have hE'el : IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y₀, hy₀, hy⟩ := Subgroup.mem_map.mp y.2
      have hc' : x₀ * y₀ = y₀ * x₀ :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, hc']
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  have hE'card : Nat.card E' = Nat.card E :=
    (Nat.card_congr (Subgroup.equivMapOfInjective E _ (MulAut.conj c⁻¹).injective).toEquiv).symm
  have h4 := hsdd.card_le_four_of_isElemAbelian hE'P hE'el
  rw [hE'card, hEcard] at h4
  have h8 : 2 ^ 3 ≤ 2 ^ sSup {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := Nat.pow_le_pow_right (by norm_num) h3
  omega

end CFSG.ClassicalInvolution.Disconnected.AschTight
