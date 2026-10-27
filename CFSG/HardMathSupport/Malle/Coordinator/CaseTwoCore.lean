module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSieve
public import CFSG.HardMathSupport.Malle.Coordinator.MaxCaseTwo
public import CFSG.HardMathSupport.Malle.Coordinator.OuterFiveCoprime
public import CFSG.HardMathSupport.Malle.Coordinator.FixedPointCount
public import CFSG.HardMathSupport.Malle.Coordinator.SylowTest

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

theorem card_dvd_of_pow_eq_one [Finite G] {K H : Subgroup G} (hHK : H ≤ K) {E X Q : ℕ}
    (hK : Nat.card K = X * Q) (hEQ : Nat.Coprime E Q) (hE : ∀ g ∈ H, g ^ E = 1) :
    Nat.card H ∣ X := by
  have hdvd : Nat.card H ∣ X * Q := hK ▸ Subgroup.card_dvd_of_le hHK
  refine (Nat.Coprime.dvd_of_dvd_mul_right ?_ hdvd)
  apply Nat.coprime_of_dvd
  intro q hq hqH hqQ
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) q hqH
  have hgE : (g : G) ^ E = 1 := hE g g.2
  have hqE : q ∣ E := by
    rw [← hg, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hgE
  have h1 := Nat.dvd_gcd hqE hqQ
  rw [hEQ.gcd_eq_one] at h1
  exact hq.one_lt.ne' (Nat.dvd_one.mp h1)

theorem card_subgroupOf_of_le {H L : Subgroup G} (h : H ≤ L) :
    Nat.card (H.subgroupOf L) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem card_centralizer_subtype (K : Subgroup G) (w : K) :
    Nat.card (Subgroup.centralizer ({w} : Set K)) =
      Nat.card (K ⊓ Subgroup.centralizer ({(w : G)} : Set G) : Subgroup G) := by
  have h : (Subgroup.centralizer ({w} : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(w : G)} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hxK, hx⟩
      exact ⟨⟨x, hxK⟩, Subtype.ext (by simpa using hx), rfl⟩
  rw [← h, Subgroup.card_map_of_injective K.subtype_injective]

section Core

variable [Finite G] {K M P Z : Subgroup G} {φ : G}

theorem caseTwo_core (D : OuterFiveData P Z φ)
    (hKcard : Nat.card K = reeF4Order) (hPcard : Nat.card P = 625) (hZcard : Nat.card Z = 25)
    (hPK : P ≤ K) (hP5 : IsPGroup 5 P)
    (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    (hφKn : ∀ k ∈ K, φ⁻¹ * k * φ ∈ K)
    (hφfix : ∀ F : Subgroup G, F ≤ K → F ≤ Subgroup.centralizer ({φ} : Set G) →
      Nat.card F ∣ 35942400)
    (hNcard : Nat.card (K ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) = 60000)
    (hTor : ∀ p ∈ ({13, 61, 331, 1321} : Finset ℕ), ∀ w ∈ K, orderOf w = p →
      Nat.card (K ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) ∣ cyclicCentralizerBound p)
    (hSieve : ReeF4IndexSieve)
    (hMK : M ≤ K) (hφM : φ ∈ Subgroup.normalizer (M : Set G))
    (hNM : K ⊓ Subgroup.normalizer (P : Set G) ≤ M)
    (hC : ∀ x ∈ Z, x ≠ 1 →
      M ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (P : Set G))
    (hEnd : ¬ 2 ∣ (K ⊓ Subgroup.normalizer (P : Set G)).relIndex M →
      M ≤ Subgroup.normalizer (P : Set G)) :
    M = K ⊓ Subgroup.normalizer (P : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set N := K ⊓ Subgroup.normalizer (P : Set G) with hN
  have hMN : M ⊓ Subgroup.normalizer (P : Set G) = N := by
    apply le_antisymm
    · exact inf_le_inf_right _ hMK
    · exact le_inf hNM inf_le_right
  have hPN : P ≤ N := le_inf hPK Subgroup.le_normalizer
  have hPM : P ≤ M := hPN.trans hNM
  have hNMle : N ≤ M := hNM
  have hPZ : Nat.card P = Nat.card Z * Nat.card Z := by rw [hPcard, hZcard]
  have hidxK : ¬ 5 ∣ P.relIndex K := by
    intro h
    have h1 := Subgroup.relIndex_mul_card (H := P) (K := K)
    rw [inf_eq_left.mpr hPK, hKcard, hPcard] at h1
    have h2 : P.relIndex K = reeF4Order / 625 := by
      rw [← h1, Nat.mul_div_cancel _ (by norm_num)]
    rw [h2] at h
    norm_num [reeF4Order] at h
  have hidx : ¬ 5 ∣ P.relIndex M := by
    intro h
    apply hidxK
    rw [← Subgroup.relIndex_mul_relIndex P M K hPM hMK]
    exact Dvd.dvd.mul_right h _
  set n := N.relIndex M with hn
  have hMcard : Nat.card M = 60000 * n := by
    have h1 := Subgroup.relIndex_mul_card (H := N) (K := M)
    rw [inf_eq_left.mpr hNMle, hNcard] at h1
    rw [← h1, mul_comm]
  have hn1 : n ∣ reeF4SylowIndex := by
    have h1 : Nat.card M ∣ Nat.card K := Subgroup.card_dvd_of_le hMK
    rw [hMcard, hKcard, show reeF4Order = 60000 * reeF4SylowIndex by norm_num [reeF4Order,
      reeF4SylowIndex]] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hn2 : n % 625 = 1 := by
    have hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := D.comm
    have hC' : ∀ x ∈ P, orderOf x = 5 → ∀ g ∈ M, g * x = x * g →
        g ∈ Subgroup.normalizer (P : Set G) := by
      intro x hx hxo g hg hgx
      have hx5 : x ^ 5 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
      have hx1 : x ≠ 1 := by
        intro h; rw [h, orderOf_one] at hxo; norm_num at hxo
      exact hC x (D.omega x hx hx5) hx1
        ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgx⟩
    have h := relIndex_modEq_one_of_centralizer_le hPM hP5 hidx hab hC'
    rw [hMN, hPcard] at h
    exact h
  have htwN : ∀ x ∈ N, x⁻¹ * (φ⁻¹ * x * φ) ∈ P := fun x hx =>
    D.twist_mem_of_centralizer_le (N := N) (fun y hy => hy.1)
      (fun y hy => D.normalizer_le_normalizer hy.2) hCZ hφKn hx
  have hNφ : Nat.card (N ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G) = 2400 := by
    have h := D.card_eq_mul_card_inf_centralizer hPN htwN hPZ
    rw [hNcard, hZcard] at h
    omega
  set d := Nat.card {Q : Sylow 5 M // conjAut hφM • Q = Q} with hd
  have hR : d * 2400 = Nat.card (M ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G) := by
    have h := D.card_fixed_mul_card_centralizer hPZ hPM hMK hφKn hCZ hφM hP5 hidx
    rw [hMN, hNφ] at h
    exact h
  have hd1 : d ∣ 14976 := by
    have h := hφfix (M ⊓ Subgroup.centralizer ({φ} : Set G)) (inf_le_left.trans hMK) inf_le_right
    rw [← hR, show (35942400 : ℕ) = 14976 * 2400 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h
  have hdn : d ∣ n := by
    have h : Nat.card (M ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G) ∣ Nat.card M :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [← hR, hMcard] at h
    have h2 : d ∣ 25 * n := by
      have : d * 2400 ∣ (25 * n) * 2400 := by
        rw [show 25 * n * 2400 = 60000 * n by ring]; exact h
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    have hcop : Nat.Coprime d 25 := Nat.Coprime.coprime_dvd_left hd1 (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h2
  set α := conjAut hφM with hα
  let P' : Sylow 5 M := (hP5.comap_subtype (K := M)).toSylow hidx
  have hPset : (P' : Set M) = ((P.subgroupOf M : Subgroup M) : Set M) := rfl
  have hα5 : α ^ 5 = 1 := by
    rw [hα, conjAut_pow]
    ext x
    simp [D.order]
  have hf5 : (MulAction.toPermHom (MulAut M) (Sylow 5 M) α) ^ 5 = 1 := by
    rw [← map_pow, hα5, map_one]
  have hfree : ∀ p ∈ P.subgroupOf M, ∀ x : Sylow 5 M, x ≠ P' → p • x = x → p = 1 := by
    intro p hp x hx hpx
    obtain ⟨m, rfl⟩ := MulAction.exists_smul_eq M P' x
    rw [Subgroup.mem_subgroupOf] at hp
    have hm : (m⁻¹ * p * m) • P' = P' := by
      rw [mul_smul, mul_smul, hpx, inv_smul_smul]
    rw [Sylow.smul_eq_iff_mem_normalizer, hPset, ← Subgroup.subgroupOf_normalizer_eq hPM,
      Subgroup.mem_subgroupOf] at hm
    have hmM : ((m⁻¹ * p * m : M) : G) ∈ M := (m⁻¹ * p * m).2
    have h25 : ∃ k : ℕ, ((m⁻¹ * p * m : M) : G) ^ (5 ^ k) = 1 := by
      refine ⟨2, ?_⟩
      have : ((m⁻¹ * p * m : M) : G) = (m : G)⁻¹ * p * m := by simp
      rw [this, inv_conj_pow, show (5 : ℕ) ^ 2 = 25 by norm_num, D.exp _ hp]
      group
    have hmem := mem_of_pElement_of_not_dvd hP5 hPM hidx hmM hm h25
    have hmN : (m : G) ∉ Subgroup.normalizer (P : Set G) := by
      intro hmN
      apply hx
      rw [Sylow.smul_eq_iff_mem_normalizer, hPset, ← Subgroup.subgroupOf_normalizer_eq hPM,
        Subgroup.mem_subgroupOf]
      exact hmN
    have hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := D.comm
    have hC' : ∀ y ∈ P, orderOf y = 5 → ∀ g ∈ M, g * y = y * g →
        g ∈ Subgroup.normalizer (P : Set G) := by
      intro y hy hyo g hg hgy
      have hy5 : y ^ 5 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
      have hy1 : y ≠ 1 := by
        intro h; rw [h, orderOf_one] at hyo; norm_num at hyo
      exact hC y (D.omega y hy hy5) hy1 ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgy⟩
    have hti := ti_of_centralizer_le hPM hP5 hidx hab hC' m m.2 hmN p hp
      (by simpa using hmem)
    exact Subtype.ext hti
  have hfc := card_modEq_fixedPoints_of_free (H := M) (X := Sylow 5 M) α
    (MulAction.toPermHom (MulAut M) (Sylow 5 M) α)
    (fun h x => mulAut_smul_smul α h x) hf5 (P.subgroupOf M) (Z.subgroupOf M)
    (fun a ha b hb => Subtype.ext (D.comm _ ha _ hb))
    (fun p hp => by
      rw [Subgroup.mem_subgroupOf] at hp ⊢
      rw [hα, conjAut_apply]; exact D.conj_inv_mem _ hp)
    (fun p => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hz
        refine ⟨D.le hz, Subtype.ext ?_⟩
        rw [hα, conjAut_apply, D.centralizes _ hz]
        group
      · rintro ⟨hp, hαp⟩
        have h1 := congrArg Subtype.val hαp
        rw [hα, conjAut_apply] at h1
        refine D.fixed _ hp ?_
        calc φ * (p : G) = φ * p * φ⁻¹ * φ := by group
          _ = p * φ := by rw [h1])
    (fun p hp hp5 => by
      rw [Subgroup.mem_subgroupOf] at hp ⊢
      exact D.omega _ hp (by simpa using congrArg Subtype.val hp5))
    (fun p hp => by
      rw [Subgroup.mem_subgroupOf] at hp ⊢
      have hq := D.conj_inv_mem _ hp
      have h1 := D.twist_mem hq
      have h2 : (φ * p * φ⁻¹)⁻¹ * (φ⁻¹ * (φ * p * φ⁻¹) * φ) = ((p : G)⁻¹ * (φ * p * φ⁻¹))⁻¹ := by
        group
      rw [h2] at h1
      have h3 := Z.inv_mem h1
      rw [inv_inv] at h3
      simpa [hα, conjAut_apply] using h3)
    (fun z hz => by
      rw [Subgroup.mem_subgroupOf] at hz
      exact Subtype.ext (by simpa using D.pow_five _ hz))
    (by rw [card_subgroupOf_of_le hPM, card_subgroupOf_of_le (D.le.trans hPM), hPZ])
    P'
    (fun p hp => by
      rw [Sylow.smul_eq_iff_mem_normalizer]
      exact Subgroup.le_normalizer (show p ∈ P.subgroupOf M from hp))
    (D.conjAut_smul_sylow_eq hφM P' rfl)
    hfree
  rw [card_subgroupOf_of_le (D.le.trans hPM), card_subgroupOf_of_le hPM, hZcard] at hfc
  have hfixcard : Nat.card {x : Sylow 5 M // MulAction.toPermHom (MulAut M) (Sylow 5 M) α x = x} =
      d := rfl
  rw [hfixcard] at hfc
  have hsylcard : Nat.card (Sylow 5 M) = n := by
    rw [Sylow.card_eq_index_normalizer P', hPset, ← Subgroup.subgroupOf_normalizer_eq hPM, hn,
      Subgroup.relIndex]
    congr 1
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hN, Subgroup.mem_inf]
    exact ⟨fun h => ⟨hMK x.2, h⟩, fun h => h.2⟩
  rw [hsylcard] at hfc
  obtain ⟨h3125, h25⟩ := hfc
  rw [hPcard] at h3125
  have h3125' : n % 3125 = (1 + 25 * (d - 1)) % 3125 := h3125
  have h25' : d % 25 = 1 := h25
  have hL5 : ∀ p ∈ ({3, 13} : Finset ℕ), ∀ a : ℕ, p ^ a ∣ 60000 * n →
      ¬ p ^ (a + 1) ∣ 60000 * n → ∃ s : ℕ, s ∣ p ^ a ∧ s ∣ 2400 * d ∧ p ^ a % 5 = s % 5 := by
    intro p hp a ha ha1
    have hpp : p.Prime := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> norm_num
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨S'⟩ := Sylow.nonempty (p := p) (G := M)
    set S := (S' : Subgroup M).map M.subtype with hS
    have hSM : S ≤ M := Subgroup.map_subtype_le _
    have hScard : Nat.card S = p ^ a := by
      rw [hS, Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity,
        hMcard]
      congr 1
      have hpos : 60000 * n ≠ 0 := by
        rw [← hMcard]; exact Nat.card_pos.ne'
      apply le_antisymm
      · by_contra hlt
        push Not at hlt
        exact ha1 ((Nat.Prime.pow_dvd_iff_le_factorization hpp hpos).mpr hlt)
      · exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hpos).mp ha
    have hSp : IsPGroup p S := S'.isPGroup'.map _
    have hSidx : ¬ p ∣ S.relIndex M := by
      have h1 : S.subgroupOf M = (S' : Subgroup M) := by
        rw [hS]; exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
      rw [Subgroup.relIndex, h1]
      exact S'.not_dvd_index
    obtain ⟨s, hs, hsor, hsmod⟩ := D.exists_card_modEq_of_sylow hPZ hPM hMK hφKn hCZ hφM hP5
      hidx hC hSM hSp hSidx
    rw [hScard] at hs hsmod
    refine ⟨s, hs, ?_, hsmod⟩
    rcases hsor with hsR | hsN
    · rw [← hR, mul_comm] at hsR; exact hsR
    · rw [hMN, hNcard] at hsN
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hpp).mp hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · have hj1 : j ≤ 1 := by
          by_contra hlt
          push Not at hlt
          have h9 : 3 ^ 2 ∣ 3 ^ j := Nat.pow_dvd_pow 3 hlt
          have := h9.trans hsN
          norm_num at this
        interval_cases j
        · simp
        · exact Dvd.dvd.mul_right (by norm_num) _
      · have hj0 : j = 0 := by
          by_contra hne
          have h13 : 13 ∣ 13 ^ j := dvd_pow_self 13 hne
          have := h13.trans hsN
          norm_num at this
        subst hj0
        simp
  have hSy : ∀ p ∈ ({13, 61, 331, 1321} : Finset ℕ), p ∣ n →
      ∃ c r m : ℕ, p ∣ c ∧ c ∣ cyclicCentralizerBound p ∧ r ∣ p - 1 ∧ c * r ∣ reeF4Order ∧
        reeF4Order / (c * r) % p = 1 ∧ p ∣ m ∧ m ∣ c * r ∧ m ∣ 60000 * n ∧
        60000 * n / m % p = 1 := by
    intro p hp hpn
    have hpp : p.Prime := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num
    have : Fact p.Prime := ⟨hpp⟩
    have hpK : ¬ p ^ 2 ∣ Nat.card K := by
      rw [hKcard]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num [reeF4Order]
    have hpM : p ∣ Nat.card (M.subgroupOf K) := by
      rw [card_subgroupOf_of_le hMK, hMcard]
      exact Dvd.dvd.mul_left hpn _
    have hX : ∀ w : K, orderOf w = p →
        Nat.card (Subgroup.centralizer ({w} : Set K)) ∣ cyclicCentralizerBound p := by
      intro w hw
      rw [card_centralizer_subtype]
      exact hTor p hp w w.2 (by rw [Subgroup.orderOf_coe]; exact hw)
    obtain ⟨c, r, m, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      exists_sylow_test (Γ := K) (M.subgroupOf K) hpM hpK hX
    rw [hKcard] at h4 h5
    rw [card_subgroupOf_of_le hMK, hMcard] at h8 h9
    exact ⟨c, r, m, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases hSieve n d hn1 hn2 hd1 hdn h25' h3125' hL5 hSy with h1 | hodd
  · have hle : M ≤ N := Subgroup.relIndex_eq_one.mp h1
    exact le_antisymm hle hNM
  · have hle : M ≤ Subgroup.normalizer (P : Set G) := hEnd (by rw [hodd]; norm_num)
    exact le_antisymm (le_inf hMK hle) hNM

end Core

end CFSG.HardMathSupport.Malle.Coordinator
