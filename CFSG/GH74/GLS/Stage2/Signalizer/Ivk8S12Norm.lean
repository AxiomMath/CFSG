module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Three

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Sporadic.Schreier

theorem evalCodes_mem_prefix {n : ℕ} {S : List (Equiv.Perm (Fin n))}
    {H : Subgroup (Equiv.Perm (Fin n))} {m : ℕ} (hS : ∀ i, i < m → S.getD i 1 ∈ H) :
    ∀ w : List ℤ, (∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ m) → evalCodes S w ∈ H
  | [], _ => by simp [evalCodes]
  | z :: w, h => by
    simp only [evalCodes]
    have hz := h z List.mem_cons_self
    have hw : ∀ z' ∈ w, z' ≠ 0 ∧ z'.natAbs ≤ m := fun z' hz' =>
      h z' (List.mem_cons_of_mem _ hz')
    refine H.mul_mem ?_ (evalCodes_mem_prefix hS w hw)
    split_ifs with hpos
    · exact hS _ (by omega)
    · exact H.inv_mem (hS _ (by omega))

theorem noThree_of_cent {M : Type*} [Group M] [Finite M] {G S₀ K : Subgroup M} (hS₀G : S₀ ≤ G)
    {A B r : M} (hAS : A ∈ S₀) (hBS : B ∈ S₀) (hAA : A * A = 1) (hBB : B * B = 1)
    (hAB : A * B = B * A) (hA1 : A ≠ 1) (hB1 : B ≠ 1) (hAneB : A ≠ B)
    (hK : ∀ x ∈ G, x * r = r * x → x ∈ K) (h9 : ¬ 9 ∣ Nat.card K)
    {cs : List M} (hcs : ∀ c ∈ cs, c ∈ G) (hcov : ∀ e ∈ [A, B, A * B], ∃ c ∈ cs, c * r * c⁻¹ = e)
    (hN : ∀ y ∈ K, ∀ c ∈ cs, orderOf y = 3 →
      ¬ (A ∈ normalizer (zpowers (c * y * c⁻¹) : Set M) ∧
        B ∈ normalizer (zpowers (c * y * c⁻¹) : Set M)))
    {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup M, P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k → IsPGroup 3 W →
      P ≤ normalizer (W : Set M) → W = ⊥ := by
  classical
  intro P W hPS hWG hPc hW3 hPW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hWne
  have hP : IsSylowOf 2 P S₀ := by
    rw [isSylowOf_iff]
    refine ⟨hPS, IsPGroup.of_card hPc, ?_⟩
    intro h2
    apply hS₀
    have h1 := (P.subgroupOf S₀).card_mul_index
    have hc : Nat.card (P.subgroupOf S₀) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv
    rw [hc, hPc] at h1
    rw [← h1, pow_succ]
    exact mul_dvd_mul_left _ h2
  have hABc : Commute A B := hAB
  set T : Subgroup M := GorensteinWalter.kleinFourOfCommutingInvolutions A B hAA hBB hABc with hT
  have hTK : IsKleinFour T :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions A B hAA hBB hA1 hB1 hAneB hABc
  have hmemT : ∀ z, z ∈ T ↔ z = A * B ∨ z = A ∨ z = B ∨ z = 1 := fun z => by
    change z ∈ ({A * B, A, B, 1} : Set M) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hAT : A ∈ T := (hmemT A).2 (Or.inr (Or.inl rfl))
  have hBT : B ∈ T := (hmemT B).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hABT : A * B ∈ T := (hmemT _).2 (Or.inl rfl)
  have hTS : T ≤ S₀ := by
    intro z hz
    rcases (hmemT z).1 hz with rfl | rfl | rfl | rfl
    · exact S₀.mul_mem hAS hBS
    · exact hAS
    · exact hBS
    · exact S₀.one_mem
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hTK.card_four]; norm_num)
  obtain ⟨S, hS, hTS'⟩ : ∃ S : Subgroup M, IsSylowOf 2 S S₀ ∧ T ≤ S := by
    have hH' : IsPGroup 2 ↥(T.subgroupOf S₀) := hT2.comap_subtype
    obtain ⟨Q, hQ⟩ := hH'.exists_le_sylow
    refine ⟨(Q : Subgroup S₀).map S₀.subtype, ⟨Q, rfl⟩, fun h hh => ?_⟩
    exact ⟨⟨h, hTS hh⟩, hQ (show (⟨h, hTS hh⟩ : S₀) ∈ T.subgroupOf S₀ from hh), rfl⟩
  obtain ⟨κ, hκS, hκ⟩ := hS.exists_mem_conj hP
  have hκG : κ ∈ G := hS₀G hκS
  set W' : Subgroup M := W.comap (MulAut.conj κ).toMonoidHom with hW'
  have hmemW' : ∀ x, x ∈ W' ↔ κ * x * κ⁻¹ ∈ W := fun x => by
    rw [hW', Subgroup.mem_comap]
    rfl
  have hW'G : W' ≤ G := by
    intro x hx
    have h1 : κ * x * κ⁻¹ ∈ G := hWG ((hmemW' x).1 hx)
    have : x = κ⁻¹ * (κ * x * κ⁻¹) * κ := by group
    rw [this]
    exact G.mul_mem (G.mul_mem (G.inv_mem hκG) h1) hκG
  have hW'eq : W' = W.map (MulAut.conj κ⁻¹).toMonoidHom := by
    ext x
    rw [hmemW', Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨κ * x * κ⁻¹, hx, by simp [mul_assoc]⟩
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
  have hW'3 : IsPGroup 3 W' := by
    rw [hW'eq]
    exact hW3.map _
  have hW'ne : W' ≠ ⊥ := by
    rw [hW'eq]
    intro hb
    exact hWne ((Subgroup.map_eq_bot_iff_of_injective W (MulAut.conj κ⁻¹).injective).1 hb)
  have hTW' : T ≤ normalizer (W' : Set M) := by
    intro a ha
    have haP : κ * a * κ⁻¹ ∈ P := by
      rw [hκ]
      have : κ⁻¹ * (κ * a * κ⁻¹) * κ = a := by group
      rw [this]
      exact hTS' ha
    have hn := Subgroup.mem_normalizer_iff.1 (hPW haP)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemW', hmemW', hn (κ * x * κ⁻¹)]
    constructor <;> intro h <;> convert h using 1 <;> group
  have hodd : Odd (Nat.card W') := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hW'3
    rw [hm]
    exact Odd.pow (by decide)
  have hAB1 : A * B ≠ 1 := fun h => hAneB (by
    have : A = B⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hBB])
  have hAneAB : A ≠ A * B := fun h => hB1 (by
    have := congrArg (A⁻¹ * ·) h
    simpa using this.symm)
  have hBneAB : B ≠ A * B := fun h => hA1 (by
    have := congrArg (· * B⁻¹) h
    simpa using this.symm)
  have hdec := four_group_odd_eq_mul_centralizers hodd hTW' hAT hBT hABT hA1 hB1 hAB1 hAneB
    hAneAB hBneAB
  obtain ⟨e, he, u, huW, hue, hu1⟩ : ∃ e ∈ [A, B, A * B], ∃ u ∈ W', u * e = e * u ∧ u ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : ∀ e ∈ [A, B, A * B], ∀ u ∈ (W' ⊓ centralizer {e} : Subgroup M), u = 1 := by
      intro e he u hu
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hu
      exact hno e he u hu.1 hu.2
    apply hW'ne
    rw [eq_bot_iff]
    intro w hw
    have hw' : w ∈ (W' : Set M) := hw
    rw [hdec] at hw'
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hw'
    rw [hbot A (by simp) a ha, hbot B (by simp) b hb, hbot (A * B) (by simp) c hc]
    simp
  set U : Subgroup M := W' ⊓ centralizer {e} with hU
  have huU : u ∈ U := by
    rw [hU, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨huW, hue⟩
  obtain ⟨c, hc, hcr⟩ := hcov e he
  have hcG := hcs c hc
  have hUK : ∀ x ∈ U, c⁻¹ * x * c ∈ K := by
    intro x hx
    rw [hU, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hx
    refine hK _ (G.mul_mem (G.mul_mem (G.inv_mem hcG) (hW'G hx.1)) hcG) ?_
    have h1 : x * (c * r * c⁻¹) = (c * r * c⁻¹) * x := by rw [hcr]; exact hx.2
    calc c⁻¹ * x * c * r = c⁻¹ * (x * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * x) * c := by rw [h1]
      _ = r * (c⁻¹ * x * c) := by group
  have hU3 : IsPGroup 3 U := hW'3.to_le inf_le_left
  have hUdvd : Nat.card U ∣ Nat.card K := by
    have hle : U.map (MulAut.conj c⁻¹).toMonoidHom ≤ K := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using hUK x hx
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective] at this
  have hUc : Nat.card U = 3 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hU3
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      have : U = ⊥ := Subgroup.card_eq_one.1 hm
      rw [this, Subgroup.mem_bot] at huU
      exact hu1 huU
    have hm1 : m = 1 := by
      by_contra hm1
      apply h9
      have : (9 : ℕ) ∣ 3 ^ m := by
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
        rw [pow_add]
        exact Dvd.intro_left _ rfl
      rw [← hm] at this
      exact this.trans hUdvd
    rw [hm, hm1, pow_one]
  have huo : orderOf u = 3 := by
    have h1 : orderOf u ∣ 3 := by
      rw [← hUc, ← Subgroup.orderOf_mk u huU]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hu1
    · exact h
  have hUz : zpowers u = U := by
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 huU) ?_
    rw [hUc, Nat.card_zpowers, huo]
  have hnormU : ∀ a ∈ T, a ∈ normalizer (U : Set M) := by
    intro a ha
    have hae : a * e * a⁻¹ = e := by
      have hcA : ∀ z ∈ T, Commute A z := by
        intro z hz
        rcases (hmemT z).1 hz with h | h | h | h <;> rw [h] <;>
          first
          | exact (Commute.refl A).mul_right hABc
          | exact hABc
          | exact Commute.one_right A
      have hcB : ∀ z ∈ T, Commute B z := by
        intro z hz
        rcases (hmemT z).1 hz with h | h | h | h <;> rw [h] <;>
          first
          | exact hABc.symm.mul_right (Commute.refl B)
          | exact hABc.symm
          | exact Commute.one_right B
      have hcomm : ∀ z ∈ T, a * z = z * a := by
        intro z hz
        rcases (hmemT a).1 ha with h | h | h | h <;> rw [h]
        · exact ((hcA z hz).mul_left (hcB z hz)).eq
        · exact (hcA z hz).eq
        · exact (hcB z hz).eq
        · exact (Commute.one_left z).eq
      have heT : e ∈ T := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact hAT
        · exact hBT
        · exact hABT
      rw [hcomm e heT, mul_inv_cancel_right]
    have hn := Subgroup.mem_normalizer_iff.1 (hTW' ha)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hU, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, ← hn x]
    apply and_congr_right
    intro _
    constructor
    · intro h
      calc a * x * a⁻¹ * e = a * x * a⁻¹ * (a * e * a⁻¹) := by rw [hae]
        _ = a * (x * e) * a⁻¹ := by group
        _ = a * (e * x) * a⁻¹ := by rw [h]
        _ = (a * e * a⁻¹) * (a * x * a⁻¹) := by group
        _ = e * (a * x * a⁻¹) := by rw [hae]
    · intro h
      have h' : a * (x * e) * a⁻¹ = a * (e * x) * a⁻¹ := by
        calc a * (x * e) * a⁻¹ = a * x * a⁻¹ * (a * e * a⁻¹) := by group
          _ = a * x * a⁻¹ * e := by rw [hae]
          _ = e * (a * x * a⁻¹) := h
          _ = (a * e * a⁻¹) * (a * x * a⁻¹) := by rw [hae]
          _ = a * (e * x) * a⁻¹ := by group
      simpa using h'
  have hy : c⁻¹ * u * c ∈ K := hUK u huU
  have hyo : orderOf (c⁻¹ * u * c) = 3 := by
    have : c⁻¹ * u * c = (MulAut.conj c⁻¹) u := by simp
    rw [this, MulEquiv.orderOf_eq, huo]
  have hcy : c * (c⁻¹ * u * c) * c⁻¹ = u := by group
  apply hN _ hy c hc hyo
  rw [hcy, hUz]
  exact ⟨hnormU A hAT, hnormU B hBT⟩

theorem card_eq_of_isSylowOf {M : Type*} [Group M] [Finite M] {P K : Subgroup M}
    (hP : IsSylowOf 2 P K) {k m : ℕ} (hK : Nat.card K = 2 ^ k * m) (hm : Odd m) :
    Nat.card P = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, h2, hidx⟩ := isSylowOf_iff.1 hP
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 h2
  have h1 := (P.subgroupOf K).card_mul_index
  have hc : Nat.card (P.subgroupOf K) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hc, hj, hK] at h1
  change 2 ^ j * P.relIndex K = 2 ^ k * m at h1
  have hm2 : ¬ 2 ∣ m := by
    have := Nat.odd_iff.1 hm
    omega
  rw [hj]
  rcases Nat.lt_trichotomy j k with hjk | rfl | hjk
  · exfalso
    apply hidx
    have hd : 2 ^ (j + 1) ∣ 2 ^ j * P.relIndex K := by
      rw [h1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 hjk) m
    rw [pow_succ] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) hd
  · rfl
  · exfalso
    apply hm2
    have hd : 2 ^ (k + 1) ∣ 2 ^ k * m := by
      rw [← h1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 hjk) _
    rw [pow_succ] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) hd

theorem not_threeCfg_sub_of_noThree {M : Type*} [Group M] [Finite M] (N S₀ : Subgroup M)
    (hSN : S₀ ≤ N) {k m : ℕ} (hS : Nat.card S₀ = 2 ^ k * m) (hm : Odd m)
    (h : ∀ P W : Subgroup M, P ≤ S₀ → W ≤ N → Nat.card P = 2 ^ k → IsPGroup 3 W →
      P ≤ normalizer (W : Set M) → W = ⊥) :
    ¬ ThreeCfg (S₀.subgroupOf N) := by
  rintro ⟨P, W, hP, hW3, hWne, hPW⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsSylowOf 2 (P.map N.subtype) S₀ := by
    have h1 := (isSylowOf_map_iff N.subtype N.subtype_injective).2 hP
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hSN] at h1
  refine hWne ((Subgroup.map_eq_bot_iff_of_injective W N.subtype_injective).1
    (h _ _ hP'.le (Subgroup.map_subtype_le W) (card_eq_of_isSylowOf hP' hS hm) ?_ ?_))
  · exact hW3.of_equiv (W.equivMapOfInjective N.subtype N.subtype_injective)
  · exact (Subgroup.map_mono hPW).trans (Subgroup.le_normalizer_map N.subtype)

theorem not_sylCfgOf_of_noThree {M : Type*} [Group M] [Finite M] (N : Subgroup M) {k m : ℕ}
    (hN : Nat.card N = 2 ^ k * m) (hm : Odd m)
    (h : ∀ P W : Subgroup M, P ≤ N → W ≤ N → Nat.card P = 2 ^ k → IsPGroup 3 W →
      P ≤ normalizer (W : Set M) → W = ⊥)
    {Y : Type} [Group Y] (e : Y ≃* ↥N) (hc : Subgroup.center ↥N = ⊥)
    (hcard : Nat.card (MulAut ↥N) ≤ 2 * Nat.card ↥N) : ¬ SylCfgOf Y := by
  intro hcfg
  have hYfin : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hcY : Subgroup.center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : e z ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := congrArg e (hz (e.symm g))
      simpa using this
    rw [hc, Subgroup.mem_bot] at hz'
    exact e.injective (by simpa using hz')
  have hcardY : Nat.card (MulAut Y) ≤ 2 * Nat.card Y := by
    have h1 : Nat.card (MulAut Y) = Nat.card (MulAut ↥N) := Nat.card_congr (MulAut.congr e).toEquiv
    have h2 : Nat.card Y = Nat.card ↥N := Nat.card_congr e.toEquiv
    rw [h1, h2]
    exact hcard
  have h2 := threeCfg_map e (threeCfg_of_sylCfgOf_inner hcY hcardY hcfg)
  have htop : (⊤ : Subgroup Y).map e.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    exact e.surjective
  rw [htop, ← Subgroup.subgroupOf_self] at h2
  exact not_threeCfg_sub_of_noThree N N le_rfl hN hm h h2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
