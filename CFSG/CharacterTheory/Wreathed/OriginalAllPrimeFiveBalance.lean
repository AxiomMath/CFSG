module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeFiveCentralizer
public import CFSG.CharacterTheory.Wreathed.FourPointConnectedGraphSupport

public section

namespace CFSG.Wreathed.OriginalAllPrime.Five

open CFSG.Wreathed.FourPointConnectedGraph CFSG.Assembly.LowTwoRank

section Balance

variable {G : Type*} [Group G]

theorem odd_orderOf_of_mem_involutionOddCore [Finite G] {t w : G}
    (hw : w ∈ involutionOddCore t) : Odd (orderOf w) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hw₀)

theorem coprime_two_card_involutionOddCore [Finite G] (t : G) :
    Nat.Coprime 2 (Nat.card (involutionOddCore t)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [involutionOddCore, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact CFSG.pPrimeCore_coprime_card

theorem conj_mem_involutionOddCore {t g w : G} (hg : g ∈ Subgroup.centralizer {t})
    (hw : w ∈ involutionOddCore t) : g * w * g⁻¹ ∈ involutionOddCore t := by
  obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
  exact ⟨⟨g, hg⟩ * w₀ * ⟨g, hg⟩⁻¹,
    (inferInstance : (CFSG.pPrimeCore 2 (Subgroup.centralizer {t})).Normal).conj_mem w₀ hw₀
      ⟨g, hg⟩, rfl⟩

theorem involutionOddCore_inf_centralizer_le [Finite G]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    {x : G} (hx : orderOf x = 2)
    (hcore : ∀ t c : G, t ∈ Subgroup.centralizer {x} → orderOf t = 2 → t ≠ x →
      c ∈ Subgroup.centralizer {x} → c ∈ Subgroup.centralizer {t} → Odd (orderOf c) →
      c ∈ involutionOddCore x)
    {t : G} (ht : orderOf t = 2) (htx : t ∈ Subgroup.centralizer {x}) :
    involutionOddCore x ⊓ Subgroup.centralizer {t} ≤ involutionOddCore t := by
  intro w hw
  obtain ⟨hwx, hwt⟩ := Subgroup.mem_inf.mp hw
  by_cases hteq : t = x
  · subst hteq
    exact hwx
  obtain ⟨c, hc⟩ := isConj_iff.mp (hinv t x ht hx)
  have hwCx : w ∈ Subgroup.centralizer {x} := Subgroup.map_subtype_le _ hwx
  have htx' := Subgroup.mem_centralizer_singleton_iff.mp htx
  have hwx' := Subgroup.mem_centralizer_singleton_iff.mp hwCx
  have hwt' := Subgroup.mem_centralizer_singleton_iff.mp hwt
  have hx₀x : c * x * c⁻¹ ∈ Subgroup.centralizer {x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * x * c⁻¹ * x = c * x * c⁻¹ * (c * t * c⁻¹) := by rw [hc]
      _ = c * (t * x) * c⁻¹ := by rw [htx']; group
      _ = c * t * c⁻¹ * (c * x * c⁻¹) := by group
      _ = x * (c * x * c⁻¹) := by rw [hc]
  have hx₀ord : orderOf (c * x * c⁻¹) = 2 := by
    rw [show c * x * c⁻¹ = MulAut.conj c x from rfl, MulEquiv.orderOf_eq, hx]
  have hx₀ne : c * x * c⁻¹ ≠ x := by
    intro h
    apply hteq
    have h' : c * t * c⁻¹ = c * x * c⁻¹ := hc.trans h.symm
    simpa using h'
  have hw'x : c * w * c⁻¹ ∈ Subgroup.centralizer {x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * w * c⁻¹ * x = c * w * c⁻¹ * (c * t * c⁻¹) := by rw [hc]
      _ = c * (w * t) * c⁻¹ := by group
      _ = c * (t * w) * c⁻¹ := by rw [hwt']
      _ = c * t * c⁻¹ * (c * w * c⁻¹) := by group
      _ = x * (c * w * c⁻¹) := by rw [hc]
  have hw'x₀ : c * w * c⁻¹ ∈ Subgroup.centralizer {c * x * c⁻¹} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * w * c⁻¹ * (c * x * c⁻¹) = c * (w * x) * c⁻¹ := by group
      _ = c * (x * w) * c⁻¹ := by rw [hwx']
      _ = c * x * c⁻¹ * (c * w * c⁻¹) := by group
  have hw'odd : Odd (orderOf (c * w * c⁻¹)) := by
    rw [show c * w * c⁻¹ = MulAut.conj c w from rfl, MulEquiv.orderOf_eq]
    exact odd_orderOf_of_mem_involutionOddCore hwx
  have hw'core := hcore _ _ hx₀x hx₀ord hx₀ne hw'x hw'x₀ hw'odd
  have hmap := involutionOddCore_conj x c⁻¹
  have htc : c⁻¹ * x * c⁻¹⁻¹ = t := by rw [← hc]; group
  rw [htc] at hmap
  rw [← hmap]
  exact ⟨c * w * c⁻¹, hw'core, by change c⁻¹ * (c * w * c⁻¹) * c⁻¹⁻¹ = w; group⟩

end Balance

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem involutionOddCore_original_x (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    involutionOddCore (wreathModelHom S e (Original.x (2 ^ n))) =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := by
  change (CFSG.pPrimeCore 2 (involutionCentralizer n S e)).map _ =
    (CFSG.oddCore (involutionCentralizer n S e)).map _
  rw [weakClosure_oddCore_eq_pPrimeCore]
  rfl

theorem odd_mem_involutionOddCore_original_x
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    (t c : G) (htx : t ∈ involutionCentralizer n S e)
    (ht : orderOf t = 2) (htne : t ≠ wreathModelHom S e (Original.x (2 ^ n)))
    (hcx : c ∈ involutionCentralizer n S e)
    (hct : c ∈ Subgroup.centralizer {t}) (hodd : Odd (orderOf c)) :
    c ∈ involutionOddCore (wreathModelHom S e (Original.x (2 ^ n))) := by
  rw [involutionOddCore_original_x]
  refine ⟨⟨c, hcx⟩, ?_, rfl⟩
  apply mem_centralizerOddCore_of_odd_of_mem_centralizer hnonab n hn S e hfour hmodel ⟨t, htx⟩
  · rwa [Subgroup.orderOf_mk]
  · intro h
    exact htne (congrArg Subtype.val h)
  · rw [Subgroup.mem_centralizer_singleton_iff] at hct ⊢
    exact Subtype.ext hct
  · rwa [Subgroup.orderOf_mk]

theorem centralizerOddCore_inf_centralizer_le
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    {t : G} (ht : orderOf t = 2) (htx : t ∈ involutionCentralizer n S e) :
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
      Subgroup.centralizer {t} ≤ involutionOddCore t := by
  rw [← involutionOddCore_original_x]
  have hx : orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
  exact involutionOddCore_inf_centralizer_le
    (all_involutions_conjugate_of_simple_wreathed hnonab n hn S e) hx
    (odd_mem_involutionOddCore_original_x hnonab n hn S e hfour hmodel) ht htx

theorem exists_balance_subgroup
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    {g : G} (hgN : g ∈ involutionCentralizer n S e) {k : ℕ} (hg2 : orderOf g ∣ 2 ^ k)
    (hg1 : g ≠ 1) :
    ∃ X : Subgroup G,
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        Subgroup.centralizer {g} ≤ X ∧
      X ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) ∧
      (∀ h ∈ Subgroup.centralizer (Subgroup.zpowers g : Set G), ∀ w ∈ X, h * w * h⁻¹ ∈ X) ∧
      Nat.Coprime 2 (Nat.card X) := by
  have h2 : 2 ∣ orderOf g := by
    obtain ⟨j, -, hgj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hg2
    rcases j with _ | j
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hgj)) hg1
    · rw [hgj, pow_succ]
      exact dvd_mul_left 2 _
  set t := g ^ (orderOf g / 2)
  have ht : orderOf t = 2 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h2
  have htN : t ∈ involutionCentralizer n S e := (involutionCentralizer n S e).pow_mem hgN _
  have hCt : Subgroup.centralizer (Subgroup.zpowers g : Set G) ≤ Subgroup.centralizer {t} := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hh t (Subgroup.npow_mem_zpowers g _)).symm
  refine ⟨involutionOddCore t ⊓ Subgroup.centralizer (Subgroup.zpowers g : Set G), ?_,
    inf_le_right, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwR, hwg⟩ := Subgroup.mem_inf.mp hw
    rw [← CFSG.BlockBasics.centralizer_zpowers_eq_centralizer_singleton] at hwg
    exact ⟨centralizerOddCore_inf_centralizer_le hnonab n hn S e hfour hmodel ht htN
      ⟨hwR, hCt hwg⟩, hwg⟩
  · intro h hh w hw
    obtain ⟨hwt, hwg⟩ := Subgroup.mem_inf.mp hw
    exact ⟨conj_mem_involutionOddCore (hCt hh) hwt,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hwg) (Subgroup.inv_mem _ hh)⟩
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_two_card_involutionOddCore t)

end CFSG.Wreathed.OriginalAllPrime.Five
