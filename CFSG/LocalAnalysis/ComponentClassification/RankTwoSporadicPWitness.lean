module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open
open scoped commutatorElement

section Perfect

variable {H W : Type*} [Group H] [Group W]

@[expose] def iterComm (Q : Subgroup H) : ℕ → Subgroup H
  | 0 => Q
  | k + 1 => ⁅iterComm Q k, iterComm Q k⁆

theorem iterComm_succ_le (Q : Subgroup H) (k : ℕ) : iterComm Q (k + 1) ≤ iterComm Q k := by
  change ⁅iterComm Q k, iterComm Q k⁆ ≤ iterComm Q k
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact (iterComm Q k).mul_mem ((iterComm Q k).mul_mem ((iterComm Q k).mul_mem ha hb)
    ((iterComm Q k).inv_mem ha)) ((iterComm Q k).inv_mem hb)

theorem iterComm_le (Q : Subgroup H) (k : ℕ) : iterComm Q k ≤ Q := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (iterComm_succ_le Q k).trans ih

theorem exists_perfect_le_map_eq [Finite H] (f : H →* W) {Q : Subgroup H} {P : Subgroup W}
    (hQ : Q.map f = P) (hP : ⁅P, P⁆ = P) :
    ∃ P' : Subgroup H, P' ≤ Q ∧ ⁅P', P'⁆ = P' ∧ P'.map f = P := by
  have hmap : ∀ k, (iterComm Q k).map f = P := by
    intro k
    induction k with
    | zero => exact hQ
    | succ k ih =>
      change (⁅iterComm Q k, iterComm Q k⁆).map f = P
      rw [map_commutator, ih, hP]
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (iterComm Q)
  have hanti : Antitone (iterComm Q) := antitone_nat_of_succ_le (iterComm_succ_le Q)
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨iterComm Q i, iterComm_le Q i, le_antisymm (iterComm_succ_le Q i) ?_, hmap i⟩
    calc iterComm Q i = iterComm Q j := heq
      _ ≤ iterComm Q (i + 1) := hanti (Nat.succ_le_of_lt h)
  · refine ⟨iterComm Q j, iterComm_le Q j, le_antisymm (iterComm_succ_le Q j) ?_, hmap j⟩
    calc iterComm Q j = iterComm Q i := heq.symm
      _ ≤ iterComm Q (j + 1) := hanti (Nat.succ_le_of_lt h)

theorem sq_mem_zpowers_pow [Finite H] {x : H} (hx : IsPGroup 2 (zpowers x)) {n : ℕ}
    (hn : Odd n) : x ^ 2 ∈ zpowers (x ^ (2 * n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hx) ⟨x ^ 2, pow_mem (mem_zpowers x) 2⟩
  have hord : orderOf (x ^ 2) = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨x ^ 2, pow_mem (mem_zpowers x) 2⟩ : zpowers x)
  have hcop : (orderOf (x ^ 2)).Coprime n := by
    rw [hord]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hn)
  have hle : zpowers ((x ^ 2) ^ n) ≤ zpowers (x ^ 2) := zpowers_le.mpr (pow_mem (mem_zpowers _) n)
  have hcard : Nat.card (zpowers ((x ^ 2) ^ n)) = Nat.card (zpowers (x ^ 2)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow]
  have heq := eq_of_le_of_card_ge hle hcard.ge
  rw [pow_mul, heq]
  exact mem_zpowers _

end Perfect

section Main

variable {G W : Type*} [Group G] [Group W] [Finite G] [Finite W]

omit [Finite G] [Finite W] in
theorem map_mem_of_mem_perfect {A' : Subgroup G} {X : Subgroup W}
    {ψ' : normalizer (A' : Set G) →* W} (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X) {P : Subgroup G}
    (hPN : P ≤ normalizer (A' : Set G)) (hP : ⁅P, P⁆ = P) {p : G} (hp : p ∈ P) :
    ψ' ⟨p, hPN hp⟩ ∈ X := by
  rw [← hP, Subgroup.commutator_def] at hp
  induction hp using closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    have : (⟨⁅a, b⁆, hPN (hP ▸ commutator_mem_commutator ha hb)⟩ : normalizer (A' : Set G)) =
        ⁅(⟨a, hPN ha⟩ : normalizer (A' : Set G)), ⟨b, hPN hb⟩⁆ := by
      ext
      simp [commutatorElement_def]
    rw [this, map_commutatorElement]
    exact hWX (commutator_mem_commutator (mem_top _) (mem_top _))
  | one =>
    have : (⟨1, hPN (P.one_mem)⟩ : normalizer (A' : Set G)) = 1 := rfl
    rw [this, map_one]
    exact X.one_mem
  | mul y z hy hz ihy ihz =>
    have hyP : y ∈ P := by rw [← hP, Subgroup.commutator_def]; exact hy
    have hzP : z ∈ P := by rw [← hP, Subgroup.commutator_def]; exact hz
    have : (⟨y * z, hPN (P.mul_mem hyP hzP)⟩ : normalizer (A' : Set G)) =
        ⟨y, hPN hyP⟩ * ⟨z, hPN hzP⟩ := rfl
    rw [this, map_mul]
    exact X.mul_mem (ihy hyP) (ihz hzP)
  | inv y hy ihy =>
    have hyP : y ∈ P := by rw [← hP, Subgroup.commutator_def]; exact hy
    have : (⟨y⁻¹, hPN (P.inv_mem hyP)⟩ : normalizer (A' : Set G)) = (⟨y, hPN hyP⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact X.inv_mem (ihy hyP)

omit [Finite G] in
theorem pow_two_mul_ordCompl_eq_one {A' : Subgroup G}
    (hK2 : ∀ k ∈ centralizer (A' : Set G), IsPGroup 2 (zpowers k) → k ^ 2 = 1) {k : G}
    (hk : k ∈ centralizer (A' : Set G)) : k ^ (2 * ordCompl[2] (Nat.card G)) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (zpowers (k ^ ordCompl[2] (Nat.card G))) := by
    have hpow : (k ^ ordCompl[2] (Nat.card G)) ^ (2 ^ (Nat.card G).factorization 2) = 1 := by
      rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_card_eq_one']
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  rw [mul_comm, pow_mul]
  exact hK2 _ (pow_mem hk _) h2

theorem not_pWitness_map {A A' T : Subgroup G} {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    {ψ' : normalizer (A' : Set G) →* W} (hψ' : IsActionHom A' X ψ')
    (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X) (hTC : T ≤ centralizer (A' : Set G))
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (A' : Set G))
    (hK2 : ∀ k ∈ centralizer (A' : Set G), IsPGroup 2 (zpowers k) → k ^ 2 = 1) :
    ¬ PWitness X ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨P, hPΓ, hPperf, hEP, x, hxP, hx2, hPgen⟩
  let Γ : Subgroup (normalizer (A : Set G)) := ⨆ t ∈ T, ⨆ (_ : t ≠ 1),
    (A ⊓ centralizer ({t} : Set G)).subgroupOf (normalizer (A : Set G))
  have hΓ : Γ ≤ (A ⊓ normalizer (A' : Set G)).subgroupOf (normalizer (A : Set G)) := by
    refine iSup₂_le fun t ht => iSup_le fun ht1 => ?_
    intro c hc
    exact ⟨hc.1, hQ t ht ht1 c hc.1 ((mem_centralizer_iff.mp hc.2 t rfl).symm)⟩
  have hPΓ' : P ≤ Γ.map ψ := by
    refine hPΓ.trans (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    obtain ⟨t, ht, rfl⟩ := he
    have ht1 : (t : G) ≠ 1 := fun h => he1 (by rw [show t = 1 from Subtype.ext h, map_one])
    exact (centDer_le_map hψ t).trans (map_mono (le_iSup₂_of_le (t : G) ht
      (le_iSup_of_le ht1 le_rfl)))
  obtain ⟨P₁, hP₁Γ, hP₁perf, hP₁map⟩ := exists_perfect_le_map_eq ψ (Q := Γ ⊓ P.comap ψ)
    (by
      apply le_antisymm
      · exact (map_mono inf_le_right).trans (map_comap_le _ _)
      · intro y hy
        obtain ⟨c, hc, rfl⟩ := hPΓ' hy
        exact ⟨c, ⟨hc, hy⟩, rfl⟩) hPperf
  have hP₁A : ∀ q ∈ P₁, (q : G) ∈ A ∧ (q : G) ∈ normalizer (A' : Set G) :=
    fun q hq => hΓ ((hP₁Γ hq).1)
  let PG : Subgroup G := P₁.map (normalizer (A : Set G)).subtype
  have hPGperf : ⁅PG, PG⁆ = PG := by rw [← map_commutator, hP₁perf]
  have hPGN : PG ≤ normalizer (A' : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hP₁A q hq).2
  have hdec : ∀ q ∈ P₁, ∃ a ∈ A', a⁻¹ * (q : G) ∈ centralizer (A' : Set G) := by
    intro q hq
    have hqG : (q : G) ∈ PG := ⟨q, hq, rfl⟩
    obtain ⟨a, ha, he⟩ := hψ'.exists_eq _ (map_mem_of_mem_perfect hWX hPGN hPGperf hqG)
    refine ⟨a, ha, (hψ'.eq_one_iff (⟨a, le_normalizer ha⟩⁻¹ * ⟨q, hPGN hqG⟩)).mp ?_⟩
    rw [map_mul, map_inv, he, inv_mul_cancel]
  let M : Subgroup G := A' ⊔ centralizer (A' : Set G)
  have hMN : M ≤ normalizer (A' : Set G) := sup_le le_normalizer (centralizer_le_normalizer _)
  have hA'M : (A'.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hMN
  have hPM : ∀ q : P₁, ((q : normalizer (A : Set G)) : G) ∈ M := by
    intro q
    obtain ⟨a, ha, hk⟩ := hdec q q.2
    rw [show ((q : normalizer (A : Set G)) : G) = a * (a⁻¹ * q) by group]
    exact mul_mem_sup ha hk
  let φ : P₁ →* M ⧸ A'.subgroupOf M := (QuotientGroup.mk' (A'.subgroupOf M)).comp
    (((normalizer (A : Set G)).subtype.comp P₁.subtype).codRestrict M hPM)
  have hφpow : ∀ q : P₁, φ q ^ (2 * ordCompl[2] (Nat.card G)) = 1 := by
    intro q
    obtain ⟨a, ha, hk⟩ := hdec q q.2
    have hsplit : (⟨((q : normalizer (A : Set G)) : G), hPM q⟩ : M) =
        ⟨a, le_sup_left (b := centralizer (A' : Set G)) ha⟩ *
          ⟨a⁻¹ * q, le_sup_right (a := A') hk⟩ := by
      ext
      simp
    change (QuotientGroup.mk' (A'.subgroupOf M) ⟨_, hPM q⟩) ^ _ = 1
    have h1 : QuotientGroup.mk' (A'.subgroupOf M)
        ⟨a, le_sup_left (b := centralizer (A' : Set G)) ha⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ha
    rw [hsplit, map_mul, h1, one_mul, ← map_pow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow]
    rw [pow_two_mul_ordCompl_eq_one hK2 hk]
    exact A'.one_mem
  let ψP : P₁ →* W := ψ.comp P₁.subtype
  have hsurj : ∀ y ∈ P, ∃ q : P₁, ψP q = y := by
    intro y hy
    rw [← hP₁map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨⟨q, hq⟩, rfl⟩
  let S : Subgroup W := φ.ker.map ψP
  have hSnorm : ∀ y ∈ P, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    obtain ⟨q, rfl⟩ := hsurj y hy
    obtain ⟨m, hm, rfl⟩ := hs
    refine ⟨q * m * q⁻¹, ?_, by simp [ψP]⟩
    exact (MonoidHom.normal_ker φ).conj_mem m hm q
  have hodd : Odd (ordCompl[2] (Nat.card G)) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two Nat.card_pos.ne')
  have hxS : x ^ 2 ∈ S := by
    obtain ⟨q, hq⟩ := hsurj x hxP
    have hmem : x ^ (2 * ordCompl[2] (Nat.card G)) ∈ S := by
      refine ⟨q ^ (2 * ordCompl[2] (Nat.card G)), ?_, by rw [map_pow, hq]⟩
      exact MonoidHom.mem_ker.mpr (by rw [map_pow]; exact hφpow q)
    exact (zpowers_le.mpr hmem) (sq_mem_zpowers_pow hx2 hodd)
  have hPS : P ≤ S := by
    refine hPgen.trans (closure_le _ |>.mpr ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact hSnorm y hy _ hxS
  have hcent : ∀ q : P₁, ∃ c : P₁, φ q = φ c ∧
      ((c : normalizer (A : Set G)) : G) ∈ centralizer (A : Set G) := by
    intro q
    have hqP : ψP q ∈ P := by
      rw [← hP₁map]
      exact ⟨q, q.2, rfl⟩
    obtain ⟨m, hm, he⟩ := hPS hqP
    refine ⟨m⁻¹ * q, by rw [map_mul, map_inv, MonoidHom.mem_ker.mp hm, inv_one, one_mul], ?_⟩
    have h1 : ψ ((m⁻¹ * q : P₁) : normalizer (A : Set G)) = 1 := by
      change ψP (m⁻¹ * q) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    exact (hψ.eq_one_iff _).mp h1
  have hcomm : ∀ q₁ q₂ : P₁, φ q₁ * φ q₂ = φ q₂ * φ q₁ := by
    intro q₁ q₂
    obtain ⟨c₁, h₁, hc₁⟩ := hcent q₁
    obtain ⟨c₂, h₂, hc₂⟩ := hcent q₂
    have hc : c₁ * c₂ = c₂ * c₁ := by
      apply Subtype.ext
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hc₁ _ (hP₁A c₂ c₂.2).1).symm
    rw [h₁, h₂, ← map_mul, ← map_mul, hc]
  have hφ1 : ∀ q : P₁, φ q = 1 := by
    have hperf : Group.IsPerfect P₁ := (Subgroup.isPerfect_iff).mpr hP₁perf
    have hrange : φ.range = ⊥ := by
      rw [MonoidHom.range_eq_map, ← (Group.isPerfect_def).mp hperf, map_commutator_eq,
        commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨a, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨b, rfl⟩
      exact hcomm b a
    intro q
    have : φ q ∈ φ.range := ⟨q, rfl⟩
    rwa [hrange, mem_bot] at this
  have hP₁A' : ∀ q : P₁, ((q : normalizer (A : Set G)) : G) ∈ A' := by
    intro q
    have := hφ1 q
    change QuotientGroup.mk' (A'.subgroupOf M) ⟨_, hPM q⟩ = 1 at this
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at this
  apply hEP
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨q, rfl⟩ := hsurj y hy
  change ψ (q : normalizer (A : Set G)) * ψ t = ψ t * ψ (q : normalizer (A : Set G))
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (hTC ht) _ (hP₁A' q))

end Main

end CFSG.ComponentClassification.RankTwoSporadic
