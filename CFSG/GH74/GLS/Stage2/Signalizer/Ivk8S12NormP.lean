module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Sporadic.Schreier

theorem exists_cent_part {M : Type*} [Group M] [Finite M] {G S₀ H : Subgroup M} (hS₀G : S₀ ≤ G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A B : M} (hAH : A ∈ H) (hBH : B ∈ H)
    (hAA : A * A = 1) (hBB : B * B = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1) (hB1 : B ≠ 1)
    (hAneB : A ≠ B) (hH2 : IsPGroup 2 H) (hHS : H ≤ S₀)
    (hHc : ∀ h ∈ H, h * A = A * h ∧ h * B = B * h) {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀)
    {P W : Subgroup M} (hPS : P ≤ S₀) (hWG : W ≤ G) (hPc : Nat.card P = 2 ^ k)
    (hWp : IsPGroup p W) (hPW : P ≤ normalizer (W : Set M)) (hWne : W ≠ ⊥) :
    ∃ e ∈ [A, B, A * B], ∃ U : Subgroup M, U ≤ G ∧ (∀ x ∈ U, x * e = e * x) ∧ IsPGroup p U ∧
      U ≠ ⊥ ∧ ∀ a ∈ H, a ∈ normalizer (U : Set M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
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
  have hTH : T ≤ H := by
    intro z hz
    rcases (hmemT z).1 hz with rfl | rfl | rfl | rfl
    · exact H.mul_mem hAH hBH
    · exact hAH
    · exact hBH
    · exact H.one_mem
  obtain ⟨S, hS, hHS'⟩ : ∃ S : Subgroup M, IsSylowOf 2 S S₀ ∧ H ≤ S := by
    have hH' : IsPGroup 2 ↥(H.subgroupOf S₀) := hH2.comap_subtype
    obtain ⟨Q, hQ⟩ := hH'.exists_le_sylow
    refine ⟨(Q : Subgroup S₀).map S₀.subtype, ⟨Q, rfl⟩, fun h hh => ?_⟩
    exact ⟨⟨h, hHS hh⟩, hQ (show (⟨h, hHS hh⟩ : S₀) ∈ H.subgroupOf S₀ from hh), rfl⟩
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
  have hW'p : IsPGroup p W' := by
    rw [hW'eq]
    exact hWp.map _
  have hW'ne : W' ≠ ⊥ := by
    rw [hW'eq]
    intro hb
    exact hWne ((Subgroup.map_eq_bot_iff_of_injective W (MulAut.conj κ⁻¹).injective).1 hb)
  have hHW' : H ≤ normalizer (W' : Set M) := by
    intro a ha
    have haP : κ * a * κ⁻¹ ∈ P := by
      rw [hκ]
      have : κ⁻¹ * (κ * a * κ⁻¹) * κ = a := by group
      rw [this]
      exact hHS' ha
    have hn := Subgroup.mem_normalizer_iff.1 (hPW haP)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemW', hmemW', hn (κ * x * κ⁻¹)]
    constructor <;> intro h <;> convert h using 1 <;> group
  have hTW' : T ≤ normalizer (W' : Set M) := hTH.trans hHW'
  have hodd : Odd (Nat.card W') := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hW'p
    rw [hm]
    exact Odd.pow (hp.odd_of_ne_two hp2)
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
  have hnormU : ∀ a ∈ H, a ∈ normalizer (U : Set M) := by
    intro a ha
    have hae : a * e * a⁻¹ = e := by
      obtain ⟨haA, haB⟩ := hHc a ha
      have hcomm : a * e = e * a := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact haA
        · exact haB
        · rw [← mul_assoc, haA, mul_assoc, haB, mul_assoc]
      rw [hcomm, mul_inv_cancel_right]
    have hn := Subgroup.mem_normalizer_iff.1 (hHW' ha)
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
  refine ⟨e, he, U, fun x hx => hW'G (inf_le_left (a := W') hx), fun x hx => ?_,
    hW'p.to_le inf_le_left, ?_, hnormU⟩
  · rw [hU, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hx
    exact hx.2
  · intro hb
    rw [hb, Subgroup.mem_bot] at huU
    exact hu1 huU

theorem noP_of_cents {M : Type*} [Group M] [Finite M] {G S₀ H : Subgroup M} (hS₀G : S₀ ≤ G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A B : M} (hAH : A ∈ H) (hBH : B ∈ H)
    (hAA : A * A = 1) (hBB : B * B = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1) (hB1 : B ≠ 1)
    (hAneB : A ≠ B) (hH2 : IsPGroup 2 H) (hHS : H ≤ S₀)
    (hHc : ∀ h ∈ H, h * A = A * h ∧ h * B = B * h) {ds : List (M × M × Subgroup M)}
    (hK : ∀ d ∈ ds, ∀ x ∈ G, x * d.2.1 = d.2.1 * x → x ∈ d.2.2)
    (hpK : ∀ d ∈ ds, ¬ p ^ 2 ∣ Nat.card d.2.2) (hcs : ∀ d ∈ ds, d.1 ∈ G)
    (hcov : ∀ e ∈ [A, B, A * B], ∃ d ∈ ds, d.1 * d.2.1 * d.1⁻¹ = e)
    (hN : ∀ d ∈ ds, ∀ y ∈ d.2.2, orderOf y = p →
      ∃ h ∈ H, h ∉ normalizer (zpowers (d.1 * y * d.1⁻¹) : Set M))
    {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup M, P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k → IsPGroup p W →
      P ≤ normalizer (W : Set M) → W = ⊥ := by
  classical
  intro P W hPS hWG hPc hWp hPW
  have : Fact p.Prime := ⟨hp⟩
  by_contra hWne
  obtain ⟨e, he, U, hUG, hUe, hUp, hU1, hnormU⟩ := exists_cent_part hS₀G hp hp2 hAH hBH hAA hBB
    hAB hA1 hB1 hAneB hH2 hHS hHc hS₀ hPS hWG hPc hWp hPW hWne
  obtain ⟨u, huU, hu1⟩ := U.bot_or_exists_ne_one.resolve_left hU1
  obtain ⟨⟨c, r, K⟩, hd, hcr⟩ := hcov e he
  have hcG := hcs _ hd
  have hUK : ∀ x ∈ U, c⁻¹ * x * c ∈ K := by
    intro x hx
    refine hK _ hd _ (G.mul_mem (G.mul_mem (G.inv_mem hcG) (hUG hx)) hcG) ?_
    have h1 : x * (c * r * c⁻¹) = (c * r * c⁻¹) * x := by rw [hcr]; exact hUe x hx
    calc c⁻¹ * x * c * r = c⁻¹ * (x * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * x) * c := by rw [h1]
      _ = r * (c⁻¹ * x * c) := by group
  have hUdvd : Nat.card U ∣ Nat.card K := by
    have hle : U.map (MulAut.conj c⁻¹).toMonoidHom ≤ K := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using hUK x hx
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective] at this
  have hUc : Nat.card U = p := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hUp
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact hU1 (Subgroup.card_eq_one.1 hm)
    have hm1 : m = 1 := by
      by_contra hm1
      apply hpK _ hd
      have : p ^ 2 ∣ p ^ m := pow_dvd_pow p (by omega)
      rw [← hm] at this
      exact this.trans hUdvd
    rw [hm, hm1, pow_one]
  have huo : orderOf u = p := by
    have h1 : orderOf u ∣ p := by
      rw [← hUc, ← Subgroup.orderOf_mk u huU]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hu1
    · exact h
  have hUz : zpowers u = U := by
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 huU) ?_
    rw [hUc, Nat.card_zpowers, huo]
  have hy : c⁻¹ * u * c ∈ K := hUK u huU
  have hyo : orderOf (c⁻¹ * u * c) = p := by
    have : c⁻¹ * u * c = (MulAut.conj c⁻¹) u := by simp
    rw [this, MulEquiv.orderOf_eq, huo]
  have hcy : c * (c⁻¹ * u * c) * c⁻¹ = u := by group
  obtain ⟨h, hh, hnot⟩ := hN _ hd _ hy hyo
  rw [hcy, hUz] at hnot
  exact hnot (hnormU h hh)

theorem noP_of_cent {M : Type*} [Group M] [Finite M] {G S₀ K H : Subgroup M} (hS₀G : S₀ ≤ G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A B r : M} (hAH : A ∈ H) (hBH : B ∈ H)
    (hAA : A * A = 1) (hBB : B * B = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1) (hB1 : B ≠ 1)
    (hAneB : A ≠ B) (hH2 : IsPGroup 2 H) (hHS : H ≤ S₀)
    (hHc : ∀ h ∈ H, h * A = A * h ∧ h * B = B * h)
    (hK : ∀ x ∈ G, x * r = r * x → x ∈ K) (hpK : ¬ p ^ 2 ∣ Nat.card K)
    {cs : List M} (hcs : ∀ c ∈ cs, c ∈ G) (hcov : ∀ e ∈ [A, B, A * B], ∃ c ∈ cs, c * r * c⁻¹ = e)
    (hN : ∀ y ∈ K, ∀ c ∈ cs, orderOf y = p →
      ∃ h ∈ H, h ∉ normalizer (zpowers (c * y * c⁻¹) : Set M))
    {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup M, P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k → IsPGroup p W →
      P ≤ normalizer (W : Set M) → W = ⊥ := by
  refine noP_of_cents hS₀G hp hp2 hAH hBH hAA hBB hAB hA1 hB1 hAneB hH2 hHS hHc
    (ds := cs.map fun c => (c, r, K)) ?_ ?_ ?_ ?_ ?_ hS₀
  · intro d hd
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    exact hK
  · intro d hd
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    exact hpK
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    exact hcs c hc
  · intro e he
    obtain ⟨c, hc, h⟩ := hcov e he
    exact ⟨(c, r, K), List.mem_map_of_mem hc, h⟩
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    exact fun y hy hyo => hN y hy c hc hyo

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

end
