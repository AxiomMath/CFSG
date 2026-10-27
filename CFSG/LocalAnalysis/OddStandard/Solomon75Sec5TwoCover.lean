module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoBase

public section

namespace CFSG.OddStandard.Solomon75

namespace Sec5Two

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem isSylowOf_sup {K N P : Subgroup X} (hP : IsSylowOf 2 P K)
    (hKN : K ≤ normalizer (N : Set X)) (hN : Odd (Nat.card N)) : IsSylowOf 2 P (K ⊔ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hPK, hP2, hdvd⟩ := hP
  refine ⟨hPK.trans le_sup_left, hP2, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K (K ⊔ N) hPK le_sup_left]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · exact hdvd h
  · have hNH : N ≤ K ⊔ N := le_sup_right
    have hKH : K ≤ K ⊔ N := le_sup_left
    have hHN : K ⊔ N ≤ normalizer (N : Set X) := sup_le hKN Subgroup.le_normalizer
    have hnormal : (N.subgroupOf (K ⊔ N)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
    have h1 := relIndex_sup_eq_relIndex_of_normal (N.subgroupOf (K ⊔ N)) (K.subgroupOf (K ⊔ N))
    have h2' : N.subgroupOf (K ⊔ N) ⊔ K.subgroupOf (K ⊔ N) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNH hKH, sup_comm]
      exact Subgroup.subgroupOf_self _
    rw [h2', Subgroup.relIndex_top_right] at h1
    have h3 : K.relIndex (K ⊔ N) = (K.subgroupOf (K ⊔ N)).index := rfl
    rw [h3, h1] at h
    have h4 := Subgroup.relIndex_mul_card (K.subgroupOf (K ⊔ N)) (N.subgroupOf (K ⊔ N))
    have h5 : Nat.card (N.subgroupOf (K ⊔ N)) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    rw [h5] at h4
    have h6 : 2 ∣ Nat.card N := h.trans (Dvd.intro _ h4)
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h6)

theorem exists_sylow_le_of_covers {A O Xs : Subgroup X} (hAO : A ≤ normalizer (O : Set X))
    (hodd : Odd (Nat.card O)) (hOA : O ≤ normalizer (A : Set X))
    (hcov : ∀ a ∈ A, ∃ x ∈ Xs, ∃ o ∈ O, a = x * o) :
    ∃ Q : Subgroup X, IsSylowOf 2 Q A ∧ Q ≤ Xs := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := exists_isSylowOf 2 A
  have hQ₀A : Q₀ ≤ A := hQ₀.le
  set R : Subgroup X := Q₀ ⊔ O with hR
  have hQ₀n : Q₀ ≤ normalizer (O : Set X) := fun x hx => hAO (hQ₀A hx)
  set Y : Subgroup X := Xs ⊓ R with hY
  have hRn : R ≤ normalizer (O : Set X) := sup_le hQ₀n Subgroup.le_normalizer
  have hcover : ∀ r ∈ R, ∃ y ∈ Y, ∃ o ∈ O, r = y * o := by
    intro r hr
    obtain ⟨q, hq, o₁, ho₁, rfl⟩ := exists_mul_of_mem_sup hQ₀n hr
    obtain ⟨x, hx, o₂, ho₂, hqx⟩ := hcov q (hQ₀A hq)
    have hxR : x ∈ R := by
      have : x = q * o₂⁻¹ := by rw [hqx]; group
      rw [this]
      exact R.mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (O.inv_mem ho₂))
    refine ⟨x, ⟨hx, hxR⟩, o₂ * o₁, O.mul_mem ho₂ ho₁, ?_⟩
    rw [hqx]; group
  have hYO : Y ⊔ O = R := by
    refine le_antisymm (sup_le inf_le_right le_sup_right) ?_
    intro r hr
    obtain ⟨y, hy, o, ho, rfl⟩ := hcover r hr
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ho)
  obtain ⟨P'', hP''⟩ := exists_isSylowOf 2 Y
  have hYn : Y ≤ normalizer (O : Set X) := inf_le_right.trans hRn
  have hP''R : IsSylowOf 2 P'' R := by
    have := isSylowOf_sup hP'' hYn hodd
    rwa [hYO] at this
  have hQ₀R : IsSylowOf 2 Q₀ R := by
    have hself : IsSylowOf 2 Q₀ Q₀ := by
      rw [isSylowOf_iff]
      exact ⟨le_rfl, hQ₀.isPGroup, by simp [Subgroup.relIndex_self]⟩
    exact isSylowOf_sup hself hQ₀n hodd
  obtain ⟨k, hkR, hk⟩ := hQ₀R.exists_mem_conj hP''R
  obtain ⟨q, hq, o, ho, rfl⟩ := exists_mul_of_mem_sup hQ₀n hkR
  have hP''A : P'' ≤ A := by
    intro x hx
    have h1 : (q * o)⁻¹ * x * (q * o) ∈ Q₀ := (hk x).1 hx
    have h2 : (q * o)⁻¹ * x * (q * o) ∈ A := hQ₀A h1
    have e : x = (q * o) * ((q * o)⁻¹ * x * (q * o)) * (q * o)⁻¹ := by group
    rw [e]
    have h3 : o * ((q * o)⁻¹ * x * (q * o)) * o⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 (hOA ho) _).1 h2
    have e2 : (q * o) * ((q * o)⁻¹ * x * (q * o)) * (q * o)⁻¹ =
        q * (o * ((q * o)⁻¹ * x * (q * o)) * o⁻¹) * q⁻¹ := by group
    rw [e2]
    exact A.mul_mem (A.mul_mem (hQ₀A hq) h3) (A.inv_mem (hQ₀A hq))
  have hcard : Nat.card P'' = 2 ^ (Nat.card A).factorization 2 := by
    rw [hP''R.card_eq, ← hQ₀.card_eq]
    exact (hQ₀R.card_eq).symm ▸ rfl
  exact ⟨P'', isSylowOf_of_card hP''A hcard, hP''.le.trans inf_le_left⟩

theorem comm_of_centralizes_sylow' {n : ℕ} (hn : 8 ≤ n) {N A : Subgroup X}
    (hA : Sec5Comp X n N A) {Q : Subgroup X} (hQ : IsSylowOf 2 Q A) {c : X} (hcN : c ∈ N)
    (hc2 : c * c = 1) (hc : ∀ y ∈ Q, c * y = y * c) :
    ∀ a ∈ A, ⁅a, c⁆ ∈ oddCoreOf A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp := hA.isPCompIn
  have hAN : A ≤ N := hAp.1
  obtain ⟨P, rfl⟩ := hQ
  have hPmem : ∀ y : ↥A, y ∈ (P : Subgroup ↥A) →
      (y : X) ∈ (P : Subgroup ↥A).map A.subtype := fun y hy => Subgroup.mem_map_of_mem _ hy
  have hdc := hA.2
  let M₀ : AhatModel X n A := ⟨↥A ⧸ pPrimeCore 2 ↥A, MulEquiv.refl _,
    AhatData.CoverSetup.ofCover hdc⟩
  let ξ : ↥A →* M₀.K := M₀.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥A))
  have hξ : Function.Surjective ξ := fun k => by
    obtain ⟨a, ha⟩ := M₀.surj_mk k
    exact ⟨a, ha⟩
  have hξapp : ∀ a : ↥A, ξ a = M₀.e (QuotientGroup.mk a) := fun a => rfl
  let Pb : Sylow 2 M₀.K := Sylow.mapSurjective hξ P
  have hPb : ∀ p ∈ (Pb : Subgroup M₀.K), ∃ y ∈ (P : Subgroup ↥A), ξ y = p := fun p hp => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hp
    exact ⟨y, hy, rfl⟩
  have hnormA : A.map (MulAut.conj c).toMonoidHom = A := by
    by_contra hne
    have hA' := hA.map_conj (Subgroup.le_normalizer hcN)
    have hAp' := hA'.isPCompIn
    have hcen : (Pb : Subgroup M₀.K) ≤ center M₀.K := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := hPb p hp
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨a, rfl⟩ := hξ k
      have hy1 := hPmem y hy
      have hyc := hc y hy1
      have hyA' : (y : X) ∈ A.map (MulAut.conj c).toMonoidHom :=
        ⟨y, y.2, by
          show c * (y : X) * c⁻¹ = y
          rw [hyc]; group⟩
      have hcomm := commutator_mem_oddCoreOf_of_ne hAp hAp' (fun h => hne h.symm) a.2 hyA'
      have hmem : ⁅(a : X), (y : X)⁆ ∈ oddCoreOf A := by
        refine inf_oddCoreOf_le hAN ⟨?_, hcomm⟩
        simp only [commutatorElement_def]
        exact A.mul_mem (A.mul_mem (A.mul_mem a.2 y.2) (A.inv_mem a.2)) (A.inv_mem y.2)
      obtain ⟨_, hmemP⟩ := mem_oddCoreOf_iff.1 hmem
      have : ξ (a * y) = ξ (y * a) := by
        have h1 : a * y = ⁅a, y⁆ * (y * a) := by
          simp only [commutatorElement_def]; group
        rw [h1, map_mul]
        have h2 : (⁅a, y⁆ : ↥A) ∈ pPrimeCore 2 ↥A := hmemP
        have : ξ ⁅a, y⁆ = 1 := by
          rw [hξapp, (QuotientGroup.eq_one_iff _).2 h2, map_one]
        rw [this, one_mul]
      rw [map_mul, map_mul] at this
      exact this
    exact not_sylow_le_center hn hdc Pb hcen
  have hcA : c ∈ normalizer (A : Set X) := mem_normalizer_of_map_conj_eq hnormA
  let σ : Perm (Fin n) := M₀.perm c hcA
  have hσ2 : σ * σ = 1 := by
    have h1 := M₀.perm_mul hn hcA hcA
    have h2 : (⟨c, hcA⟩ : ↥(normalizer (A : Set X))) * ⟨c, hcA⟩ = 1 := Subtype.ext hc2
    have h3 := congrArg (M₀.permHom hn) h2
    rw [map_mul, map_one] at h3
    exact h3
  by_cases hσ1 : σ = 1
  · exact (M₀.perm_eq_one_iff hn hcA).1 hσ1
  · exfalso
    have hind : M₀.C.Induces (M₀.autOf c hcA) σ := M₀.induces_perm hn c hcA
    have hpow : σ ^ 2 = 1 := by rw [pow_two]; exact hσ2
    have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
    have hsum := Equiv.Perm.sum_cycleType σ
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hk : σ.support.card = 2 * σ.cycleType.card := by omega
    have hk1 : 1 ≤ σ.cycleType.card := by
      by_contra hcon
      have h0 : σ.support.card = 0 := by omega
      exact hσ1 (Equiv.Perm.card_support_eq_zero.1 h0)
    have hfix : (Pb : Subgroup M₀.K) ≤ AhatData.fixSub (M₀.autOf c hcA) := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := hPb p hp
      have hyc := hc y (hPmem y hy)
      rw [AhatData.mem_fixSub, hξapp, M₀.autOf_mk]
      congr 2
      apply Subtype.ext
      show c * (y : X) * c⁻¹ = y
      rw [hyc]; group
    exact hind.not_sylow_le_fixSub hn hσ2 hk hk1 Pb hfix

theorem sylow_center_of (h : Sec5Data X n z (zpowers z) S) {A Q : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hQ : IsSylowOf 2 Q A) :
    z ∈ Q ∧ ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z := by
  obtain ⟨P, rfl⟩ := hQ
  exact sylow_center h hA P

theorem normalizer_le_of (h : Sec5Data X n z (zpowers z) S) {A Q : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hQ : IsSylowOf 2 Q A) :
    normalizer (Q : Set X) ≤ centralizer ({z} : Set X) := by
  obtain ⟨P, rfl⟩ := hQ
  exact normalizer_sylow_le h hA P

theorem core_le_normalizer_comp {H A : Subgroup X} (hA : Sec5Comp X n H A) :
    pPrimeCoreOf 2 (K0 X n H) ≤ normalizer (A : Set X) := by
  intro o ho
  have hAD : A ≤ K0 X n H := comp_le_K0 hA
  have hoC : o ∈ normalizer (H : Set X) :=
    Subgroup.le_normalizer (K0_le n H (oddCoreOf_le (K0 X n H) ho))
  refine (normalizes_of_comm hA hoC ?_).1
  intro a ha
  have e : ⁅a, o⁆ = (a * o * a⁻¹) * o⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact (pPrimeCoreOf 2 (K0 X n H)).mul_mem
    ((Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem (hAD ha)) o).1 ho)
    ((pPrimeCoreOf 2 (K0 X n H)).inv_mem ho)

omit [Finite X] in
theorem exists_pow_orderOf_eq_two' {s : X} {k : ℕ} (hk : s ^ 2 ^ k = 1) (hs : s ≠ 1) :
    ∃ n : ℕ, orderOf (s ^ n) = 2 := by
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hn
    exact hs hn
  refine ⟨2 ^ (n - 1), ?_⟩
  rw [orderOf_pow_of_dvd (pow_pos (by norm_num) _).ne'
    (by rw [hn]; exact pow_dvd_pow 2 (by omega)), hn, Nat.pow_div (by omega) (by norm_num),
    show n - (n - 1) = 1 by omega, pow_one]

omit [Finite X] in
theorem commutator_pow_mem' {O L : Subgroup X} {s : X} (hs : s ∈ normalizer (O : Set X))
    (h : ∀ l ∈ L, ⁅l, s⁆ ∈ O) (n : ℕ) : ∀ l ∈ L, ⁅l, s ^ n⁆ ∈ O := by
  induction n with
  | zero => intro l _; simp [one_mem]
  | succ n ih =>
    intro l hl
    have e : ⁅l, s ^ (n + 1)⁆ = ⁅l, s ^ n⁆ * (s ^ n * ⁅l, s⁆ * (s ^ n)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine O.mul_mem (ih l hl) ?_
    exact (Subgroup.mem_normalizer_iff.1 ((Subgroup.pow_mem _ hs n)) _).1 (h l hl)

end Sec5Two

end CFSG.OddStandard.Solomon75
