module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XSylow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped commutatorElement

theorem pow_eq_self_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) {n : ℕ}
    (hn : Odd n) : x ^ n = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

theorem commutatorElement_eq_of_commute {G : Type*} [Group G] {u₁ u₂ v₁ v₂ : G}
    (hu : Commute u₁ u₂) (h11 : Commute u₁ v₁) (h12 : Commute u₁ v₂) (h21 : Commute u₂ v₁)
    (h22 : Commute u₂ v₂) : ⁅u₁ * v₁, u₂ * v₂⁆ = ⁅v₁, v₂⁆ := by
  rw [commutatorElement_mul_left_of_commute h11 (hu.mul_right h12),
    commutatorElement_mul_right_of_commute h22 h21]

theorem map_conj_centralizer' {G : Type*} [Group G] (g a : G) :
    (centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * a * g⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact conj_mem_centralizer_of_conj rfl hy
  · intro hx
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, conj_mem_centralizer_of_conj (by group) hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem card_centralizer_conj' {G : Type*} [Group G] (g a : G) :
    Nat.card ↥(centralizer ({g * a * g⁻¹} : Set G)) = Nat.card ↥(centralizer ({a} : Set G)) := by
  rw [← map_conj_centralizer', card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} {i : spinGroup (quadOdd 3 K)}

theorem exists_decomp_pow (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {y : spinGroup (quadOdd 3 K)} (hyE : y ∈ spinE K) (hyp : y ^ p = 1) :
    ∃ a ∈ spinJ₁ K, ∃ b ∈ spinJ₂ K, ∃ c ∈ spinJ₃ K, y = a * b * c ∧ a ^ p = 1 ∧ b ^ p = 1 ∧
      c ^ p = 1 := by
  have h4 := four_le_card_spin hK h5
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hzz, -, hzc, htt, -, -, hz1J, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨hJ₁C, hJ₂C, hJ₃C⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  rw [← range_spinMul h4] at hyE
  obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := hyE
  rw [spinMul_apply] at hyp ⊢
  change ((a : spinGroup (quadOdd 3 K)) * b * c) ^ p = 1 at hyp
  have hab : Commute (a : spinGroup (quadOdd 3 K)) b := commute_spinJ₁_spinJ₂ a.2 b.2
  have hac : Commute (a : spinGroup (quadOdd 3 K)) c := commute_spinJ₁_spinJ₃ a.2 c.2
  have hbc : Commute (b : spinGroup (quadOdd 3 K)) c := commute_spinJ₂_spinJ₃ h4 b.2 c.2
  have hpow : ((a : spinGroup (quadOdd 3 K)) * b * c) ^ p =
      (a : spinGroup (quadOdd 3 K)) ^ p * (b : spinGroup (quadOdd 3 K)) ^ p *
        (c : spinGroup (quadOdd 3 K)) ^ p := by
    rw [(hac.mul_left hbc).mul_pow, hab.mul_pow]
  have hker : (((a ^ p, b ^ p), c ^ p) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) ∈
      (spinMul h4).ker := by
    rw [MonoidHom.mem_ker, spinMul_apply]
    change (a : spinGroup (quadOdd 3 K)) ^ p * (b : spinGroup (quadOdd 3 K)) ^ p *
      (c : spinGroup (quadOdd 3 K)) ^ p = 1
    rw [← hpow]
    exact hyp
  rcases (mem_ker_spinMul_iff hp hp2 hK h5 h4 _).mp hker with h | h
  · have e1 : (a : spinGroup (quadOdd 3 K)) ^ p = 1 :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K))) h
    have e2 : (b : spinGroup (quadOdd 3 K)) ^ p = 1 :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.1.2 : ↥(spinJ₂ K)) : spinGroup (quadOdd 3 K))) h
    have e3 : (c : spinGroup (quadOdd 3 K)) ^ p = 1 :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.2 : ↥(spinJ₃ K)) : spinGroup (quadOdd 3 K))) h
    exact ⟨a, a.2, b, b.2, c, c.2, rfl, e1, e2, e3⟩
  · have e1 : (a : spinGroup (quadOdd 3 K)) ^ p = spinZ K :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K))) h
    have e2 : (b : spinGroup (quadOdd 3 K)) ^ p = tSeven K :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.1.2 : ↥(spinJ₂ K)) : spinGroup (quadOdd 3 K))) h
    have e3 : (c : spinGroup (quadOdd 3 K)) ^ p = spinZ K * tSeven K :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.2 : ↥(spinJ₃ K)) : spinGroup (quadOdd 3 K))) h
    have hz : ∀ g : spinGroup (quadOdd 3 K), Commute (spinZ K) g := fun g =>
      (mem_center_iff.mp hzc g).symm
    have hat : Commute (a : spinGroup (quadOdd 3 K)) (tSeven K) :=
      mem_centralizer_singleton_iff.mp (hJ₁C a.2)
    have hbt : Commute (b : spinGroup (quadOdd 3 K)) (tSeven K) :=
      mem_centralizer_singleton_iff.mp (hJ₂C b.2)
    have hct : Commute (c : spinGroup (quadOdd 3 K)) (tSeven K) :=
      mem_centralizer_singleton_iff.mp (hJ₃C c.2)
    have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
      rw [mul_mul_self_of_commute (hz _), hzz, htt, one_mul]
    have hX : Commute ((a : spinGroup (quadOdd 3 K)) * b) (spinZ K * tSeven K) :=
      ((hz _).symm).mul_right (hat.mul_left hbt)
    refine ⟨spinZ K * a, mul_mem hz1J a.2, tSeven K * b, mul_mem ht2J b.2,
      spinZ K * tSeven K * c, mul_mem hzt3J c.2, ?_, ?_, ?_, ?_⟩
    · calc (a : spinGroup (quadOdd 3 K)) * b * c =
          1 * ((a : spinGroup (quadOdd 3 K)) * b * c) := (one_mul _).symm
        _ = spinZ K * tSeven K * (spinZ K * tSeven K) *
            ((a : spinGroup (quadOdd 3 K)) * b * c) := by rw [hztzt]
        _ = spinZ K * tSeven K * ((a : spinGroup (quadOdd 3 K)) * b) *
            (spinZ K * tSeven K * c) := (hX.mul_mul_mul_comm _ _).symm
        _ = spinZ K * a * (tSeven K * b) * (spinZ K * tSeven K * c) := by
            rw [hat.mul_mul_mul_comm]
    · rw [(hz _).mul_pow, pow_eq_self_of_mul_self hzz hpo, e1, hzz]
    · rw [hbt.symm.mul_pow, pow_eq_self_of_mul_self htt hpo, e2, htt]
    · rw [((hz _).mul_left hct.symm).mul_pow, pow_eq_self_of_mul_self hztzt hpo, e3, hztzt]

theorem exists_decomp_centralizer (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) {a b c e : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K) (hb : b ∈ spinJ₂ K)
    (hc : c ∈ spinJ₃ K) (hap : a ^ p = 1) (he : e ∈ spinE K)
    (hey : e * (a * b * c) = a * b * c * e) :
    ∃ a₁ ∈ spinJ₁ K, ∃ b₁ ∈ spinJ₂ K, ∃ c₁ ∈ spinJ₃ K, e = a₁ * b₁ * c₁ ∧
      a₁ * a = a * a₁ ∧ b₁ * b = b * b₁ ∧ c₁ * c = c * c₁ := by
  have h4 := four_le_card_spin hK h5
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hzz, hz1, hzc, -⟩ := spinZ_facts hp hp2 hK
  rw [← range_spinMul h4] at he
  obtain ⟨u, rfl⟩ := he
  have hvy : spinMul h4 (((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) =
      a * b * c := rfl
  have hker : u * (((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) * u⁻¹ *
      ((((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K))⁻¹ ∈
        (spinMul h4).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hvy, hey]
    group
  rcases (mem_ker_spinMul_iff hp hp2 hK h5 h4 _).mp hker with h | h
  · have huv : u * (((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) =
        (((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) * u := by
      have e := mul_inv_eq_one.mp h
      calc u * (((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) =
          u * (((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) * u⁻¹ * u := by
            group
        _ = (((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) * u := by rw [e]
    have e1 : ((u.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K)) * a = a * u.1.1 :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K))) huv
    have e2 : ((u.1.2 : ↥(spinJ₂ K)) : spinGroup (quadOdd 3 K)) * b = b * u.1.2 :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.1.2 : ↥(spinJ₂ K)) : spinGroup (quadOdd 3 K))) huv
    have e3 : ((u.2 : ↥(spinJ₃ K)) : spinGroup (quadOdd 3 K)) * c = c * u.2 :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.2 : ↥(spinJ₃ K)) : spinGroup (quadOdd 3 K))) huv
    exact ⟨u.1.1, u.1.1.2, u.1.2, u.1.2.2, u.2, u.2.2, spinMul_apply h4 u, e1, e2, e3⟩
  · exfalso
    have e1 : ((u.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K)) * a *
        ((u.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K))⁻¹ * a⁻¹ = spinZ K :=
      congrArg (fun w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K =>
        ((w.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K))) h
    have e2 : ((u.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K)) * a *
        ((u.1.1 : ↥(spinJ₁ K)) : spinGroup (quadOdd 3 K))⁻¹ = spinZ K * a := by
      rw [← e1]
      group
    have hpow := congrArg (· ^ p) e2
    have hza : Commute (spinZ K) a := (mem_center_iff.mp hzc a).symm
    rw [conj_pow, hap, mul_one, mul_inv_cancel, hza.mul_pow, pow_eq_self_of_mul_self hzz hpo, hap,
      mul_one] at hpow
    exact hz1 hpow.symm

theorem mem_centralizer_t_of_odd (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {k : spinGroup (quadOdd 3 K)} (hk : k ∈ normalizer (fourT K : Set (spinGroup (quadOdd 3 K))))
    (hodd : Odd (orderOf k)) : k ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
  obtain ⟨hzz, -, hzc, -⟩ := spinZ_facts hp hp2 hK
  rcases conj_t_of_mem_normalizer_fourT hp hp2 hK hk with h | h
  · exact mem_centralizer_singleton_iff.mpr (commute_of_conj_eq h)
  · have hk2 : k * k ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
      have hkz : k * spinZ K * k⁻¹ = spinZ K := by
        rw [mem_center_iff.mp hzc k, mul_inv_cancel_right]
      have e : (k * k) * tSeven K * (k * k)⁻¹ = tSeven K := by
        calc (k * k) * tSeven K * (k * k)⁻¹ = k * (k * tSeven K * k⁻¹) * k⁻¹ := by group
          _ = k * (spinZ K * tSeven K) * k⁻¹ := by rw [h]
          _ = (k * spinZ K * k⁻¹) * (k * tSeven K * k⁻¹) := by group
          _ = tSeven K := by rw [hkz, h, ← mul_assoc, hzz, one_mul]
      exact mem_centralizer_singleton_iff.mpr (commute_of_conj_eq e)
    obtain ⟨m, hm⟩ := hodd
    have hkm : k ∈ zpowers (k * k) := by
      refine mem_zpowers_iff.mpr ⟨((m + 1 : ℕ) : ℤ), ?_⟩
      rw [zpow_natCast, ← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf k + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    exact zpowers_le.mpr hk2 hkm

theorem card_centQThree_le (hF1 : F1) (hA2 : A2) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    Nat.card ↥(centQThree K) ≤
      Nat.card K ^ 5 * (Nat.card ↥(spinJ₂ K) * Nat.card ↥(spinJ₃ K) * Nat.card K * 2) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨hcK, hle⟩ := hF1 K hodd (hK ▸ h5)
  have hKn : ∀ y ∈ centQThree K, ∀ k ∈ oddQThree K, y * k * y⁻¹ ∈ oddQThree K :=
    fun _ hy _ hk => CFSG.Walter.conj_mem_map_of_characteristic (le_normalizer hy) hk
  have hMN : mX K ≤ normalizer (oddQThree K : Set (spinGroup (quadOdd 3 K))) :=
    le_normalizer_of_conj_mem hKn inf_le_left
  have hcard := card_sup_mul_card_inf_of_le_normalizer' hMN
  have hsup : oddQThree K ⊔ mX K = centQThree K :=
    le_antisymm (sup_le (map_subtype_le _) inf_le_left) hle
  have hcK' : Nat.card ↥(oddQThree K) = Nat.card K ^ 5 := hcK
  rw [hsup, hcK', hI.card_mX hp hp2 hK, card_centralizer_inf hA2 hp hp2 hK h5] at hcard
  have hpos : 0 < Nat.card ↥(oddQThree K ⊓ mX K) := Nat.card_pos
  calc Nat.card ↥(centQThree K) ≤ Nat.card ↥(centQThree K) * Nat.card ↥(oddQThree K ⊓ mX K) :=
        Nat.le_mul_of_pos_right _ hpos
    _ = _ := hcard

theorem not_conj_long (hF1 : F1) (hF2b : F2b) (hA2 : A2) (hA3 : A3) (hI : IsIBar K i)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₂ K ∨ x ∈ spinJ₃ K) (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) (l : spinGroup (quadOdd 3 K)) (hxl : l⁻¹ * qThree K * l = x) : False := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hq5 : 5 ≤ Nat.card K := hK ▸ h5
  obtain ⟨-, h32, -⟩ := hA3 K hodd
  obtain ⟨g, hg⟩ := h32 x hx hx1 (by rw [ringChar_eq hp hK]; exact hxp)
  have hF2 := hF2b K hodd hq5
  have heq : Nat.card ↥(centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K)))) =
      Nat.card ↥(centQThree K) := by
    rw [← hg, card_centralizer_conj', ← hxl, show l⁻¹ * qThree K * l = l⁻¹ * qThree K * l⁻¹⁻¹ by
      rw [inv_inv], card_centralizer_conj']
  have hC := card_centQThree_le hF1 hA2 hI hp hp2 hK h5
  rw [card_spinJ₂, card_spinJ₃] at hC
  obtain ⟨r, hr'⟩ : ∃ r, r = Nat.card K ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hr'] at hF2 hC
  have hr : 0 < r := by
    rw [hr']
    have : 25 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  have key : Nat.card K * (Nat.card K ^ 8 * r ^ 2) ≤ 2 * (Nat.card K ^ 8 * r ^ 2) := by
    calc Nat.card K * (Nat.card K ^ 8 * r ^ 2) = Nat.card K ^ 9 * r ^ 2 := by ring
      _ ≤ Nat.card ↥(centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K)))) := hF2
      _ = Nat.card ↥(centQThree K) := heq
      _ ≤ Nat.card K ^ 5 * (Nat.card K * r * (Nat.card K * r) * Nat.card K * 2) := hC
      _ = 2 * (Nat.card K ^ 8 * r ^ 2) := by ring
  have hpos : 0 < Nat.card K ^ 8 * r ^ 2 := Nat.mul_pos (pow_pos (by omega) 8) (pow_pos hr 2)
  have := Nat.le_of_mul_le_mul_right key hpos
  omega

theorem not_conj_short (hF1 : F1) (hA3 : A3) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {l : spinGroup (quadOdd 3 K)}
    (hl : l * tSeven K * l⁻¹ = i) (hy : l⁻¹ * qThree K * l ∈ spinJ₁ K)
    (hy1 : l⁻¹ * qThree K * l ≠ 1) (hyp : (l⁻¹ * qThree K * l) ^ p = 1) : False := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, -, -, -, -, -, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨h31, -⟩ := hA3 K hodd
  obtain ⟨g, hgt, hg⟩ := h31 _ hy hy1 (by rw [ringChar_eq hp hK]; exact hyp)
  have hmq : g * l⁻¹ ∈ centQThree K := by
    rw [mem_centralizer_singleton_iff]
    apply commute_of_conj_eq
    calc g * l⁻¹ * qThree K * (g * l⁻¹)⁻¹ = g * (l⁻¹ * qThree K * l) * g⁻¹ := by group
      _ = qThree K := hg
  have hmi : (g * l⁻¹) * i * (g * l⁻¹)⁻¹ = tSeven K := by
    calc (g * l⁻¹) * i * (g * l⁻¹)⁻¹ = g * (l⁻¹ * (l * tSeven K * l⁻¹) * l) * g⁻¹ := by
          rw [hl]; group
      _ = g * tSeven K * g⁻¹ := by group
      _ = tSeven K := by rw [mem_centralizer_singleton_iff.mp hgt, mul_inv_cancel_right]
  obtain ⟨-, hle⟩ := hF1 K hodd (hK ▸ h5)
  have hKn : ∀ y ∈ centQThree K, ∀ k ∈ oddQThree K, y * k * y⁻¹ ∈ oddQThree K :=
    fun _ hy _ hk => CFSG.Walter.conj_mem_map_of_characteristic (le_normalizer hy) hk
  have hMN : mX K ≤ normalizer (oddQThree K : Set (spinGroup (quadOdd 3 K))) :=
    le_normalizer_of_conj_mem hKn inf_le_left
  have hK₃ : Odd (Nat.card ↥(oddQThree K)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hm : g * l⁻¹ ∈ ((oddQThree K ⊔ mX K : Subgroup (spinGroup (quadOdd 3 K))) :
      Set (spinGroup (quadOdd 3 K))) := hle hmq
  rw [coe_mul_of_right_le_normalizer_left _ _ hMN] at hm
  obtain ⟨k, hk, m', hm', hkm'⟩ := hm
  have hkm : k * m' = g * l⁻¹ := hkm'
  have hk' : k ∈ oddQThree K := hk
  have hm'' : m' ∈ mX K := hm'
  have hi : i = (k * m')⁻¹ * tSeven K * (k * m') := by
    rw [hkm, ← hmi]
    group
  have hCt := sup_le_centralizer_inf (K := K) hp hp2 hK
  have htq : tSeven K ∈ centQThree K := (mem_inf.mp (hCt (mem_sup_left ht2J))).2
  obtain ⟨k₂, hk₂def⟩ : ∃ k₂, k₂ = m'⁻¹ * (k⁻¹ * (tSeven K * k * (tSeven K)⁻¹)) * m' := ⟨_, rfl⟩
  have hk₁ : k⁻¹ * (tSeven K * k * (tSeven K)⁻¹) ∈ oddQThree K :=
    mul_mem (inv_mem hk') (hKn _ htq _ hk')
  have hk₂ : k₂ ∈ oddQThree K := by
    have h := hKn _ (inv_mem (mem_inf.mp hm'').1) _ hk₁
    rw [inv_inv] at h
    rw [hk₂def]
    exact h
  have hs : m'⁻¹ * tSeven K * m' ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centQThree K := by
    rcases conj_t_of_mem_normalizer_fourT hp hp2 hK (inv_mem (mem_inf.mp hm'').2) with h | h <;>
      rw [inv_inv] at h <;> rw [h]
    · exact hCt (mem_sup_left ht2J)
    · exact hCt (mem_sup_right hzt3J)
  have hi' : i = k₂ * (m'⁻¹ * tSeven K * m') := by
    rw [hk₂def, hi]
    group
  have hk₂M : k₂ ∈ mX K := by
    have e : k₂ = i * (m'⁻¹ * tSeven K * m')⁻¹ := by
      rw [hi']
      group
    rw [e]
    exact mul_mem (hI.mem_mX hp hp2 hK) (inv_mem (centralizer_inf_le_mX hp hp2 hK hs))
  have hk₂t := mem_centralizer_t_of_odd hp hp2 hK (mem_inf.mp hk₂M).2
    (Odd.of_dvd_nat hK₃ (Subgroup.orderOf_dvd_natCard _ hk₂))
  apply hI.not_mem_centralizer_t hp hp2 hK
  rw [hi']
  exact mul_mem hk₂t (mem_inf.mp hs).1

theorem not_mixed (hA3 : A3) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {l : spinGroup (quadOdd 3 K)}
    (hl : l * tSeven K * l⁻¹ = i) {a b c : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K)
    (hb : b ∈ spinJ₂ K) (hc : c ∈ spinJ₃ K) (hap : a ^ p = 1) (hbp : b ^ p = 1) (hcp : c ^ p = 1)
    (hy : l⁻¹ * qThree K * l = a * b * c) (ha1 : a ≠ 1) (hbc : b ≠ 1 ∨ c ≠ 1) : False := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have h4 := four_le_card_spin hK h5
  obtain ⟨-, hz1, hzc, -, -, -, hz1J, -⟩ := spinZ_facts hp hp2 hK
  have hli : l⁻¹ * i * l⁻¹⁻¹ = tSeven K := by rw [inv_inv, ← hl]; group
  have hlq : l⁻¹ * qThree K * l⁻¹⁻¹ = a * b * c := by rw [inv_inv]; exact hy
  have hDperf := hI.isPerfect_dTwoThree hp hp2 hK h5
  have hQperf : Group.IsPerfect ↥((hI.dTwoThree hp hp2 hK h5).map
      (MulAut.conj l⁻¹).toMonoidHom) :=
    Group.IsPerfect.map (H := hI.dTwoThree hp hp2 hK h5) (MulAut.conj l⁻¹).toMonoidHom
  have hQt : (hI.dTwoThree hp hp2 hK h5).map (MulAut.conj l⁻¹).toMonoidHom ≤
      centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
    rintro _ ⟨d, hd, rfl⟩
    exact conj_mem_centralizer_of_conj hli (hI.dTwoThree_le_centralizer_i hp hp2 hK h5 hd)
  have hQE := le_spinE_of_isPerfect hp hp2 hK h5 hQt hQperf
  have hQy : ∀ x ∈ (hI.dTwoThree hp hp2 hK h5).map (MulAut.conj l⁻¹).toMonoidHom,
      x * (a * b * c) = a * b * c * x := by
    rintro _ ⟨d, hd, rfl⟩
    have hdq : d ∈ centQThree K :=
      (mem_inf.mp (sup_le_centralizer_inf hp hp2 hK (hI.dTwoThree_le_sup hp hp2 hK h5 hd))).2
    exact mem_centralizer_singleton_iff.mp (conj_mem_centralizer_of_conj hlq hdq)
  have hzQ : spinZ K ∈ (hI.dTwoThree hp hp2 hK h5).map (MulAut.conj l⁻¹).toMonoidHom := by
    refine ⟨spinZ K, hI.spinZ_mem_dTwoThree hp hp2 hK h5, ?_⟩
    show l⁻¹ * spinZ K * l⁻¹⁻¹ = spinZ K
    rw [mem_center_iff.mp hzc l⁻¹, mul_inv_cancel_right]
  have hQQ := Subgroup.isPerfect_iff.mp hQperf
  rcases hbc with hb1 | hc1
  ·
    have hcomm : ⁅(hI.dTwoThree hp hp2 hK h5).map (MulAut.conj l⁻¹).toMonoidHom,
        (hI.dTwoThree hp hp2 hK h5).map (MulAut.conj l⁻¹).toMonoidHom⁆ ≤ spinJ₃ K := by
      rw [commutator_le]
      intro x hx x' hx'
      obtain ⟨a₁, ha₁, b₁, hb₁, c₁, hc₁, rfl, haa₁, hbb₁, -⟩ :=
        exists_decomp_centralizer hp hp2 hK h5 ha hb hc hap (hQE hx) (hQy _ hx)
      obtain ⟨a₂, ha₂, b₂, hb₂, c₂, hc₂, rfl, haa₂, hbb₂, -⟩ :=
        exists_decomp_centralizer hp hp2 hK h5 ha hb hc hap (hQE hx') (hQy _ hx')
      have h12a : Commute a₁ a₂ :=
        commute_of_mem_spinJ₁ hA3 hp hp2 hK ha ha1 hap ha₁ ha₂ haa₁ haa₂
      have h12b : Commute b₁ b₂ :=
        commute_of_mem_spinJ₂ hA3 hp hp2 hK hb hb1 hbp hb₁ hb₂ hbb₁ hbb₂
      have hab₂ : Commute a₁ b₂ := commute_spinJ₁_spinJ₂ ha₁ hb₂
      have hba₂ : Commute b₁ a₂ := (commute_spinJ₁_spinJ₂ ha₂ hb₁).symm
      have h11 : Commute (a₁ * b₁) c₁ :=
        Commute.mul_left (commute_spinJ₁_spinJ₃ ha₁ hc₁) (commute_spinJ₂_spinJ₃ h4 hb₁ hc₁)
      have h12 : Commute (a₁ * b₁) c₂ :=
        Commute.mul_left (commute_spinJ₁_spinJ₃ ha₁ hc₂) (commute_spinJ₂_spinJ₃ h4 hb₁ hc₂)
      have h21 : Commute (a₂ * b₂) c₁ :=
        Commute.mul_left (commute_spinJ₁_spinJ₃ ha₂ hc₁) (commute_spinJ₂_spinJ₃ h4 hb₂ hc₁)
      have h22 : Commute (a₂ * b₂) c₂ :=
        Commute.mul_left (commute_spinJ₁_spinJ₃ ha₂ hc₂) (commute_spinJ₂_spinJ₃ h4 hb₂ hc₂)
      rw [commutatorElement_eq_of_commute ((h12a.mul_right hab₂).mul_left (hba₂.mul_right h12b))
        h11 h12 h21 h22, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂)
    rw [hQQ] at hcomm
    exact hz1 (eq_one_of_mem_spinJ₁_of_mem_spinJ₃ hp hp2 hK h5 hz1J (hcomm hzQ))
  ·
    have hcomm : ⁅(hI.dTwoThree hp hp2 hK h5).map (MulAut.conj l⁻¹).toMonoidHom,
        (hI.dTwoThree hp hp2 hK h5).map (MulAut.conj l⁻¹).toMonoidHom⁆ ≤ spinJ₂ K := by
      rw [commutator_le]
      intro x hx x' hx'
      obtain ⟨a₁, ha₁, b₁, hb₁, c₁, hc₁, rfl, haa₁, -, hcc₁⟩ :=
        exists_decomp_centralizer hp hp2 hK h5 ha hb hc hap (hQE hx) (hQy _ hx)
      obtain ⟨a₂, ha₂, b₂, hb₂, c₂, hc₂, rfl, haa₂, -, hcc₂⟩ :=
        exists_decomp_centralizer hp hp2 hK h5 ha hb hc hap (hQE hx') (hQy _ hx')
      have h12a : Commute a₁ a₂ :=
        commute_of_mem_spinJ₁ hA3 hp hp2 hK ha ha1 hap ha₁ ha₂ haa₁ haa₂
      have h12c : Commute c₁ c₂ :=
        hI.commute_of_mem_spinJ₃ hA3 hp hp2 hK h5 hc hc1 hcp hc₁ hc₂ hcc₁ hcc₂
      have e1 : a₁ * b₁ * c₁ = a₁ * c₁ * b₁ := by
        rw [mul_assoc, commute_spinJ₂_spinJ₃ h4 hb₁ hc₁, ← mul_assoc]
      have e2 : a₂ * b₂ * c₂ = a₂ * c₂ * b₂ := by
        rw [mul_assoc, commute_spinJ₂_spinJ₃ h4 hb₂ hc₂, ← mul_assoc]
      have hac₂ : Commute a₁ c₂ := commute_spinJ₁_spinJ₃ ha₁ hc₂
      have hca₂ : Commute c₁ a₂ := (commute_spinJ₁_spinJ₃ ha₂ hc₁).symm
      have h11 : Commute (a₁ * c₁) b₁ :=
        Commute.mul_left (commute_spinJ₁_spinJ₂ ha₁ hb₁) (commute_spinJ₂_spinJ₃ h4 hb₁ hc₁).symm
      have h12 : Commute (a₁ * c₁) b₂ :=
        Commute.mul_left (commute_spinJ₁_spinJ₂ ha₁ hb₂) (commute_spinJ₂_spinJ₃ h4 hb₂ hc₁).symm
      have h21 : Commute (a₂ * c₂) b₁ :=
        Commute.mul_left (commute_spinJ₁_spinJ₂ ha₂ hb₁) (commute_spinJ₂_spinJ₃ h4 hb₁ hc₂).symm
      have h22 : Commute (a₂ * c₂) b₂ :=
        Commute.mul_left (commute_spinJ₁_spinJ₂ ha₂ hb₂) (commute_spinJ₂_spinJ₃ h4 hb₂ hc₂).symm
      rw [e1, e2, commutatorElement_eq_of_commute
        ((h12a.mul_right hac₂).mul_left (hca₂.mul_right h12c)) h11 h12 h21 h22,
        commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hb₁ hb₂) (inv_mem hb₁)) (inv_mem hb₂)
    rw [hQQ] at hcomm
    exact hz1 (eq_one_of_mem_spinJ₁_of_mem_spinJ₂ hp hp2 hK h5 hz1J (hcomm hzQ))

theorem shape (hF1 : F1) (hF2b : F2b) (hA2 : A2) (hA3 : A3) (hI : IsIBar K i) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {l : spinGroup (quadOdd 3 K)}
    (hl : l * tSeven K * l⁻¹ = i) :
    ∃ a ∈ spinJ₂ K, ∃ b ∈ spinJ₃ K, a ≠ 1 ∧ b ≠ 1 ∧ a ^ p = 1 ∧ b ^ p = 1 ∧
      l⁻¹ * qThree K * l = a * b := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have : Fact p.Prime := ⟨hp⟩
  have hli : l⁻¹ * i * l⁻¹⁻¹ = tSeven K := by rw [inv_inv, ← hl]; group
  have hyl : l⁻¹ * qThree K * l = l⁻¹ * qThree K * l⁻¹⁻¹ := by rw [inv_inv]
  have hyt : l⁻¹ * qThree K * l ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
    rw [hyl]
    exact conj_mem_centralizer_of_conj hli
      (mem_centralizer_singleton_iff.mpr hI.commute_qThree.symm)
  have hyp : (l⁻¹ * qThree K * l) ^ p = 1 := by
    rw [hyl, conj_pow, qThree_pow_p hp hK, mul_one, mul_inv_cancel]
  have hy1 : l⁻¹ * qThree K * l ≠ 1 := by
    intro h
    apply qThree_ne_one' (K := K)
    calc qThree K = l * (l⁻¹ * qThree K * l) * l⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hyE : l⁻¹ * qThree K * l ∈ spinE K := by
    have hle := le_spinE_of_coprime hp hp2 hK h5 (P := zpowers (l⁻¹ * qThree K * l))
      (zpowers_le.mpr hyt) (by
        rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1]
        exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact hle (mem_zpowers _)
  obtain ⟨a, ha, b, hb, c, hc, hy, hap, hbp, hcp⟩ := exists_decomp_pow hp hp2 hK h5 hyE hyp
  by_cases ha1 : a = 1
  · subst ha1
    by_cases hb1 : b = 1
    · subst hb1
      exfalso
      by_cases hc1 : c = 1
      · subst hc1
        exact hy1 (by rw [hy]; group)
      · exact not_conj_long hF1 hF2b hA2 hA3 hI hp hp2 hK h5 (Or.inr hc) hc1 hcp l
          (by rw [hy]; group)
    · by_cases hc1 : c = 1
      · subst hc1
        exfalso
        exact not_conj_long hF1 hF2b hA2 hA3 hI hp hp2 hK h5 (Or.inl hb) hb1 hbp l
          (by rw [hy]; group)
      · exact ⟨b, hb, c, hc, hb1, hc1, hbp, hcp, by rw [hy, one_mul]⟩
  · exfalso
    by_cases hb1 : b = 1
    · by_cases hc1 : c = 1
      · subst hb1
        subst hc1
        have hya : l⁻¹ * qThree K * l = a := by rw [hy, mul_one, mul_one]
        exact not_conj_short hF1 hA3 hI hp hp2 hK h5 hl (by rw [hya]; exact ha) hy1 hyp
      · exact not_mixed hA3 hI hp hp2 hK h5 hl ha hb hc hap hbp hcp hy ha1 (Or.inr hc1)
    · exact not_mixed hA3 hI hp hp2 hK h5 hl ha hb hc hap hbp hcp hy ha1 (Or.inl hb1)

end Model

end CFSG.ComponentClassification.HarrisLit.T1.S74
