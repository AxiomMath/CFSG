module

public import CFSG.Walter.Statement
public import CFSG.Foundations.Basic
import CFSG.Walter.AStar.Components
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Walter.PSL2Facts.Even
import CFSG.Walter.PSL2Facts.Odd
import CFSG.Walter.J1Props.Elt
import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.Local
import CFSG.Dihedral.DisconnectedInvolutionGraph.SimpleGroupReductions
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup

theorem exists_card_eq_mul_self {X : Type*} [Group X] (A : Subgroup X) [Finite A]
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h4 : ∀ x ∈ A, x ^ 4 = 1)
    (hsq : ∀ z ∈ A, z ^ 2 = 1 → ∃ y ∈ A, y ^ 2 = z) : ∃ s : ℕ, Nat.card A = s * s := by
  let φ : A →* A :=
    { toFun := fun x => x ^ 2
      map_one' := one_pow 2
      map_mul' := fun x y => by
        have hxy : x * y = y * x := Subtype.ext (hab _ x.2 _ y.2)
        rw [sq, sq, sq, mul_assoc, ← mul_assoc y x y, ← hxy, mul_assoc, mul_assoc] }
  have hφ : ∀ x : A, φ x = x ^ 2 := fun _ => rfl
  have hker : φ.ker = φ.range := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_range, hφ]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hsq x x.2 (by rw [← Subgroup.coe_pow, hx, Subgroup.coe_one])
      exact ⟨⟨y, hy⟩, Subtype.ext (by rw [hφ, Subgroup.coe_pow]; exact hyx)⟩
    · rintro ⟨y, rfl⟩
      rw [hφ, ← pow_mul]
      exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h4 _ y.2)
  refine ⟨Nat.card φ.ker, ?_⟩
  have h1 := φ.ker.card_mul_index
  rw [Subgroup.index_ker, ← hker] at h1
  exact h1.symm

theorem factorization_eight_mul_odd {u : ℕ} (hu : Odd u) : (8 * u).factorization 2 = 3 := by
  rw [Nat.factorization_mul (by norm_num) (by rintro rfl; simp at hu), Finsupp.add_apply,
    show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h))]

theorem ordRee_eq_eight_mul (m : ℕ) : ∃ u, Odd u ∧ CFSG.Open.ordRee (3 ^ (2 * m + 1)) = 8 * u := by
  set q := 3 ^ (2 * m + 1) with hq
  have h1 : q % 8 = 3 := by
    rw [hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : q ^ 3 % 8 = 3 := by
    rw [Nat.pow_mod, h1]
  obtain ⟨k, hk⟩ : ∃ k, q = 8 * k + 3 := ⟨q / 8, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, q ^ 3 = 8 * j + 3 := ⟨q ^ 3 / 8, by omega⟩
  have hqodd : Odd (q ^ 3) := ⟨4 * j + 1, by omega⟩
  refine ⟨q ^ 3 * (2 * j + 1) * (4 * k + 1),
    (hqodd.mul ⟨j, by ring⟩).mul ⟨2 * k, by ring⟩, ?_⟩
  rw [CFSG.Open.ordRee, show q ^ 3 + 1 = 4 * (2 * j + 1) by omega,
    show q - 1 = 2 * (4 * k + 1) by omega]
  ring

theorem false_of_simple_of_sylow (hW : CFSG.Walter.WalterOrderForm) {X : Type} [Group X]
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (A : Sylow 2 X)
    (hab : ∀ x ∈ (A : Subgroup X), ∀ y ∈ (A : Subgroup X), x * y = y * x)
    (h4 : ∀ x ∈ (A : Subgroup X), x ^ 4 = 1)
    (hsq : ∀ z ∈ (A : Subgroup X), z ^ 2 = 1 → ∃ y ∈ (A : Subgroup X), y ^ 2 = z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2X : 2 ∣ Nat.card X := even_iff_two_dvd.mp (CFSG.Walter.even_card_of_isSimpleGroup hnab)
  have h2A : 2 ∣ Nat.card (A : Subgroup X) :=
    A.isPGroup'.card_eq_or_dvd.resolve_left fun h =>
      A.ne_bot_of_dvd_card h2X (Subgroup.card_eq_one.mp h)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (A : Subgroup X)) 2 h2A
  have hz2 : (z : X) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz] at h
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have hz1 : (z : X) ≠ 1 := fun h => by
    rw [show z = 1 from Subtype.ext h, orderOf_one] at hz
    omega
  obtain ⟨y, hyA, hyz⟩ := hsq z z.2 hz2
  have hy2 : y ^ 2 ≠ 1 := by rwa [hyz]
  have hy4 : y ^ 4 = 1 := h4 y hyA
  obtain ⟨s, hs⟩ := exists_card_eq_mul_self (A : Subgroup X) hab h4 hsq
  have hcomm : IsMulCommutative (A : Subgroup X) :=
    ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
  have hnot8 : ∀ u, Odd u → Nat.card X = 8 * u → False := by
    intro u hu hX
    have h8 : Nat.card (A : Subgroup X) = 8 := by
      rw [A.card_eq_multiplicity, hX, factorization_eight_mul_odd hu]
      norm_num
    rw [h8] at hs
    have hs3 : s ≤ 3 := by nlinarith
    interval_cases s <;> omega
  rcases hW X hnab A hcomm with ⟨m, -, ⟨e⟩⟩ | ⟨p, m, hp, hpodd, hm, -, h8, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | he
  ·
    have ht : orderOf (e y ^ 2) = 2 := by
      rw [← map_pow, MulEquiv.orderOf_eq, hyz, Subgroup.orderOf_coe, hz]
    have hc : e y ∈ centralizer ({e y ^ 2} : Set _) :=
      mem_centralizer_singleton_iff.2 (by rw [sq, mul_assoc])
    have := CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo ht hc
    rw [← map_pow, map_eq_one_iff _ e.injective] at this
    exact hy2 this
  ·
    have hP2 : IsPGroup 2 (zpowers (e y)) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_zpowers, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime_pow (by rw [show 2 ^ 1 = 2 by norm_num]; exact hy2) hy4
    obtain ⟨P', hP'⟩ := hP2.exists_le_sylow
    have hK4 := CFSG.Walter.psl2_odd_sylow_two_isKleinFour hpodd hm h8 P'
    have hyP : e y ∈ (P' : Subgroup _) := hP' (mem_zpowers _)
    have h1 : (⟨e y, hyP⟩ : (P' : Subgroup _)) ^ 2 = 1 := by
      have h0 := Monoid.pow_exponent_eq_one (⟨e y, hyP⟩ : (P' : Subgroup _))
      rwa [hK4.exponent_two] at h0
    have h2 : e y ^ 2 = 1 := by
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← map_pow, map_eq_one_iff _ e.injective] at h2
    exact hy2 h2
  ·
    obtain ⟨u, hu, hu8⟩ := ordRee_eq_eight_mul m
    exact hnot8 u hu (hcard.trans hu8)
  ·
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, CFSG.Walter.J1Props.card_walterJ1] at hnot8
    exact hnot8 21945 (by decide) (by norm_num)

theorem layer_eq_bot_of_sylow (hW : CFSG.Walter.WalterOrderForm) {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 2 X = ⊥) (P : Sylow 2 X)
    (hab : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x)
    (h4 : ∀ x ∈ (P : Subgroup X), x ^ 4 = 1)
    (hsq : ∀ z ∈ (P : Subgroup X), z ^ 2 = 1 → ∃ y ∈ (P : Subgroup X), y ^ 2 = z) :
    CFSG.layer X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.layer, sSup_eq_bot]
  intro L hLc
  have hL := (CFSG.Walter.isComponent_iff_isComponentOf_top L).mp hLc
  have hY : CFSG.Walter.HasAbelianSylowTwo X :=
    CFSG.Walter.hasAbelianSylowTwo_of_sylow P ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
  have : IsSimpleGroup L := CFSG.Walter.isSimpleGroup_of_isComponentOf hO hY hL
  have hnonab := CFSG.Walter.nonabelian_of_isComponentOf hL
  have hinner := CFSG.Walter.exists_inner_of_sylow_le_normalizer hY L hnonab P
    (CFSG.Walter.sylow_le_normalizer_of_isComponentOf hO hY P hL)
  have hLC : ∀ x ∈ L, x ∈ centralizer (L : Set X) → x = 1 := by
    intro x hxL hxC
    have hmem : (⟨x, hxL⟩ : L) ∈ center L := mem_center_iff.mpr fun y =>
      Subtype.ext ((mem_centralizer_iff.mp hxC) y y.2)
    rw [CFSG.Walter.center_eq_bot_of_isSimpleGroup hnonab, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P
    (CFSG.Walter.isSubnormal_of_isComponentOf hL)
  have hQmem : ∀ x : L, x ∈ (Q : Subgroup L) ↔ (x : X) ∈ (P : Subgroup X) := by
    intro x
    constructor
    · intro hx
      have hx' : (x : X) ∈ (Q : Subgroup L).map L.subtype := ⟨x, hx, rfl⟩
      rw [hQ] at hx'
      exact hx'.1
    · intro hx
      have hx' : (x : X) ∈ (P : Subgroup X) ⊓ L := ⟨hx, x.2⟩
      rw [← hQ] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rwa [← Subtype.ext hyx]
  have hdec : ∀ u ∈ (P : Subgroup X), ∃ k ∈ L, k ∈ (P : Subgroup X) ∧
      k⁻¹ * u ∈ centralizer (L : Set X) := by
    intro u hu
    obtain ⟨k, hkL, hk⟩ := hinner u hu
    have hcC : k⁻¹ * u ∈ centralizer (L : Set X) := by
      rw [mem_centralizer_iff]
      intro x hx
      calc x * (k⁻¹ * u) = k⁻¹ * (k * x * k⁻¹) * u := by group
        _ = k⁻¹ * (u * x * u⁻¹) * u := by rw [hk x hx]
        _ = k⁻¹ * u * x := by group
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨u, hu⟩
    have hupow : u ^ (2 ^ a) = 1 := by
      have h := pow_orderOf_eq_one (⟨u, hu⟩ : (P : Subgroup X))
      rw [ha] at h
      exact congrArg Subtype.val h
    have hkc : Commute k (k⁻¹ * u) := mem_centralizer_iff.mp hcC k hkL
    have hkpow : k ^ (2 ^ a) = 1 := by
      have h1 := hkc.mul_pow (2 ^ a)
      rw [mul_inv_cancel_left, hupow] at h1
      have hk' : k ^ (2 ^ a) = ((k⁻¹ * u) ^ (2 ^ a))⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      apply hLC _ (L.pow_mem hkL _)
      rw [hk']
      exact inv_mem (pow_mem hcC _)
    have hkN : (⟨k, hkL⟩ : L) ∈ normalizer ((Q : Subgroup L) : Set L) := by
      rw [mem_normalizer_iff]
      intro y
      rw [hQmem, hQmem]
      have hy : ((⟨k, hkL⟩ * y * (⟨k, hkL⟩ : L)⁻¹ : L) : X) = u * y * u⁻¹ := (hk y y.2).symm
      rw [hy]
      constructor
      · intro hyU
        exact mul_mem (mul_mem hu hyU) (inv_mem hu)
      · intro hyU
        have := mul_mem (mul_mem (inv_mem hu) hyU) hu
        simpa [mul_assoc] using this
    have hkP := CFSG.RankTwoShapes.mem_sylow_of_mem_normalizer_of_pow Q hkN a (Subtype.ext hkpow)
    exact ⟨k, hkL, (hQmem _).mp hkP, hcC⟩
  refine (false_of_simple_of_sylow hW (X := L) hnonab Q ?_ ?_ ?_).elim
  · intro x hx y hy
    exact Subtype.ext (hab _ ((hQmem x).1 hx) _ ((hQmem y).1 hy))
  · intro x hx
    exact Subtype.ext (by rw [Subgroup.coe_pow, h4 _ ((hQmem x).1 hx), Subgroup.coe_one])
  · intro z hz hz2
    have hzP := (hQmem z).1 hz
    have hz2' : (z : X) ^ 2 = 1 := by rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one]
    obtain ⟨y, hyP, hyz⟩ := hsq _ hzP hz2'
    obtain ⟨k, hkL, hkP, hkc⟩ := hdec y hyP
    have hky : k⁻¹ * y = y * k⁻¹ := hab _ (inv_mem hkP) _ hyP
    have hsq' : (k⁻¹ * y) ^ 2 = k⁻¹ * k⁻¹ * (z : X) := by
      rw [← hyz, sq, sq]
      calc k⁻¹ * y * (k⁻¹ * y) = k⁻¹ * (y * k⁻¹) * y := by group
        _ = k⁻¹ * (k⁻¹ * y) * y := by rw [hky]
        _ = k⁻¹ * k⁻¹ * (y * y) := by group
    have hc2 : (k⁻¹ * y) ^ 2 = 1 := by
      refine hLC _ ?_ (pow_mem hkc 2)
      rw [hsq']
      exact mul_mem (mul_mem (inv_mem hkL) (inv_mem hkL)) z.2
    refine ⟨⟨k, hkL⟩, (hQmem _).2 hkP, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow]
    change k ^ 2 = (z : X)
    rw [hsq'] at hc2
    have : (z : X) = k * k := by
      calc (z : X) = k * k * (k⁻¹ * k⁻¹ * (z : X)) := by group
        _ = k * k := by rw [hc2, mul_one]
    rw [this, sq]

theorem sylow_normal_of_pPrimeCore_eq_bot (hW : CFSG.Walter.WalterOrderForm) {X : Type}
    [Group X] [Finite X] (hO : CFSG.pPrimeCore 2 X = ⊥) (P : Sylow 2 X)
    (hab : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x)
    (h4 : ∀ x ∈ (P : Subgroup X), x ^ 4 = 1)
    (hsq : ∀ z ∈ (P : Subgroup X), z ^ 2 = 1 → ∃ y ∈ (P : Subgroup X), y ^ 2 = z) :
    (P : Subgroup X).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X 2 hO
      (layer_eq_bot_of_sylow hW hO P hab h4 hsq)
  have : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hFP : CFSG.pCore 2 X ≤ (P : Subgroup X) := CFSG.pCore_isPGroup.le_sylow_of_normal P
  have hPC : (P : Subgroup X) ≤ centralizer (CFSG.pCore 2 X : Set X) := fun u hu =>
    mem_centralizer_iff.2 fun x hx => hab _ (hFP hx) _ hu
  rw [le_antisymm (hPC.trans hchar) hFP]
  exact CFSG.pCore_normal

theorem pPrimeCore_sup_sylow_normal (hW : CFSG.Walter.WalterOrderForm) {X : Type} [Group X]
    [Finite X] (P : Sylow 2 X)
    (hab : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x)
    (h4 : ∀ x ∈ (P : Subgroup X), x ^ 4 = 1)
    (hsq : ∀ z ∈ (P : Subgroup X), z ^ 2 = 1 → ∃ y ∈ (P : Subgroup X), y ^ 2 = z) :
    (CFSG.pPrimeCore 2 X ⊔ (P : Subgroup X)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 X with hOdef
  have : O.Normal := CFSG.pPrimeCore_normal
  set π := QuotientGroup.mk' O with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hO : CFSG.pPrimeCore 2 (X ⧸ O) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two
  have hPO : ∀ x ∈ (P : Subgroup X), x ∈ O → x = 1 := by
    have hcop : Nat.Coprime (Nat.card (P : Subgroup X)) (Nat.card O) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rw [hk]
      exact (CFSG.pPrimeCore_coprime_card).pow_left k
    intro x hxP hxO
    have := (Subgroup.disjoint_of_coprime_natCard hcop).le_bot ⟨hxP, hxO⟩
    exact (mem_bot).mp this
  let Pbar : Sylow 2 (X ⧸ O) := P.mapSurjective hπ
  have hPbar : (Pbar : Subgroup (X ⧸ O)) = (P : Subgroup X).map π := Sylow.coe_mapSurjective _ _
  have hab' : ∀ x ∈ (Pbar : Subgroup (X ⧸ O)), ∀ y ∈ (Pbar : Subgroup (X ⧸ O)),
      x * y = y * x := by
    rw [hPbar]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hab x hx y hy]
  have h4' : ∀ x ∈ (Pbar : Subgroup (X ⧸ O)), x ^ 4 = 1 := by
    rw [hPbar]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h4 x hx, map_one]
  have hsq' : ∀ z ∈ (Pbar : Subgroup (X ⧸ O)), z ^ 2 = 1 →
      ∃ y ∈ (Pbar : Subgroup (X ⧸ O)), y ^ 2 = z := by
    rw [hPbar]
    rintro _ ⟨w, hw, rfl⟩ hw2
    have hw2' : w ^ 2 = 1 := by
      refine hPO _ (pow_mem hw 2) ?_
      rw [← map_pow, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw2
      exact hw2
    obtain ⟨v, hv, hvw⟩ := hsq w hw hw2'
    exact ⟨π v, ⟨v, hv, rfl⟩, by rw [← map_pow, hvw]⟩
  have hn := sylow_normal_of_pPrimeCore_eq_bot hW hO Pbar hab' h4' hsq'
  have hcomap : (Pbar : Subgroup (X ⧸ O)).comap π = O ⊔ (P : Subgroup X) := by
    rw [hPbar, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  rw [← hcomap]
  exact hn.comap π

theorem false_of_simple_inf_sylow (hW : CFSG.Walter.WalterOrderForm) {X : Type} [Group X]
    [Finite X] (P : Sylow 2 X)
    (hab : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x)
    (h4 : ∀ x ∈ (P : Subgroup X), x ^ 4 = 1)
    (hsq : ∀ z ∈ (P : Subgroup X), z ^ 2 = 1 → ∃ y ∈ (P : Subgroup X), y ^ 2 = z)
    {J : Subgroup X} [IsSimpleGroup J] (hJ : ∃ a b : J, a * b ≠ b * a) {z : X} (hzJ : z ∈ J)
    (hzP : z ∈ (P : Subgroup X)) (hz1 : z ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 X with hOdef
  have : O.Normal := CFSG.pPrimeCore_normal
  set M := O ⊔ (P : Subgroup X) with hMdef
  have hMn : M.Normal := pPrimeCore_sup_sylow_normal hW P hab h4 hsq
  have hJM : J ≤ M := by
    have := hMn.subgroupOf J
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf J) with h | h
    · exfalso
      rw [subgroupOf_eq_bot] at h
      exact hz1 (h.le_bot ⟨mem_sup_right hzP, hzJ⟩)
    · rwa [subgroupOf_eq_top] at h
  have hMM : ⁅M, M⁆ ≤ O := by
    set π := QuotientGroup.mk' O
    have hmap : M.map π = (P : Subgroup X).map π := by
      rw [hMdef, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr
        (by rw [QuotientGroup.ker_mk']), bot_sup_eq]
    have h1 : ⁅M, M⁆.map π = ⊥ := by
      rw [Subgroup.map_commutator, hmap, Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hab y hy x hx]
    have h2 := (Subgroup.map_eq_bot_iff _).mp h1
    rwa [QuotientGroup.ker_mk'] at h2
  have hJJ : ⁅J, J⁆ = J := by
    have h1 : commutator J = ⊤ :=
      (CFSG.DisconnectedInvolutionGraph.Helpers.simple_nonabelian_perfect hJ).commutator_eq_top
    have h2 := congrArg (Subgroup.map J.subtype) h1
    rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hzO : z ∈ O := hMM (commutator_mono hJM hJM (hJJ.symm ▸ hzJ))
  have hcop : Nat.Coprime (Nat.card (P : Subgroup X)) (Nat.card O) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hk]
    exact (CFSG.pPrimeCore_coprime_card).pow_left k
  exact hz1 ((mem_bot).mp ((Subgroup.disjoint_of_coprime_natCard hcop).le_bot ⟨hzP, hzO⟩))

end CFSG.LocalAnalysis.EvenBN.G2
