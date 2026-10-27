module

public import CFSG.GH74.Generic.BProg.B3.SolvKGDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911L2

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2.P911 CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.L2Aux
open CFSG.ComponentClassification.Burgoyne (oddCoreIn)
open scoped Pointwise

namespace SolvKG

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem commutator_mem_innDiag (e : K ≃* L2 F) (u v : MulAut K) :
    u * v * u⁻¹ * v⁻¹ ∈ innDiagSub e := by
  have hDn : (innDiagSub e).Normal := innDiagSub_normal e
  have : IsCyclic ↥(fieldAutSub e) := isCyclic_fieldAutSub e
  have : IsCyclic (MulAut K ⧸ innDiagSub e) := by
    refine isCyclic_of_surjective
      ((QuotientGroup.mk' (innDiagSub e)).comp (fieldAutSub e).subtype) ?_
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∈ ((innDiagSub e : Set (MulAut K)) * (fieldAutSub e : Set (MulAut K))) := by
      rw [← Subgroup.normal_mul, innDiagSub_sup_fieldAutSub e]
      exact Subgroup.mem_top a
    obtain ⟨d, hd, φ, hφ, rfl⟩ := ha
    refine ⟨⟨φ, hφ⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype,
      QuotientGroup.mk_mul]
    rw [(QuotientGroup.eq_one_iff d).mpr hd, one_mul]
  have hcomm : ∀ a b : MulAut K ⧸ innDiagSub e, a * b = b * a := fun a b =>
    (IsCyclic.commGroup (α := MulAut K ⧸ innDiagSub e)).mul_comm a b
  have hc : (QuotientGroup.mk (u * v * u⁻¹ * v⁻¹) : MulAut K ⧸ innDiagSub e) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hcomm (QuotientGroup.mk u : MulAut K ⧸ innDiagSub e)
      (QuotientGroup.mk v), mul_inv_cancel_right, mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff _).mp hc

theorem odd_orderOf_of_mem_oddCoreIn' {M : Type} [Group M] [Finite M] {B : Subgroup M} {t y : M}
    (hy : y ∈ oddCoreIn B t) : Odd (orderOf y) := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set M)))) :=
    Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have h1 : orderOf (⟨z, hz⟩ : ↥(pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set M)))) ∣
      Nat.card ↥(pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set M))) := orderOf_dvd_natCard _
  have h2 : orderOf (((B ⊓ centralizer ({t} : Set M)).subtype z : M)) = orderOf z :=
    orderOf_injective _ (Subgroup.subtype_injective _) z
  have h3 : orderOf z = orderOf (⟨z, hz⟩ : ↥(pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set M)))) :=
    (Subgroup.orderOf_mk z hz).symm
  rw [h2, h3]
  exact Odd.of_dvd_nat hodd h1

theorem kgAut_l2 (hF : L2Field F) (e : K ≃* L2 F) : KGAut K := by
  intro B hB t htB ht I _ _ hI ψ hψ a ⟨k, hk⟩ y hy
  classical
  have hinj := conj_injective_of_L2 e
  set Y : Subgroup (MulAut K) := oddCoreIn B t with hYdef
  have hψN : ∀ i, ψ i ∈ normalizer (Y : Set (MulAut K)) := fun i =>
    mem_normalizer_oddCoreIn (hψ i)
  have hYodd : ∀ w ∈ Y, Odd (orderOf w) := fun w hw => odd_orderOf_of_mem_oddCoreIn' hw
  have hYt : ∀ w ∈ Y, w * t = t * w := by
    rintro _ ⟨z, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 z.2).2
  set E : Subgroup K := Y.comap (MulAut.conj : K →* MulAut K) with hE
  have hfix : ∀ g : K, MulAut.conj g * t = t * MulAut.conj g → g ∈ fixedSubgroup K t := by
    intro g hc
    have h1 : t * MulAut.conj g * t⁻¹ = MulAut.conj g := by
      rw [← hc]; group
    show t g = g
    apply hinj
    rw [← mulAut_conj_conj' t g, h1]
  have hEz : E ≤ fixedSubgroup K t := fun g hg => hfix g (hYt _ hg)
  have hEodd : ∀ g ∈ E, Odd (orderOf g) := by
    intro g hg
    have h1 := hYodd _ hg
    rwa [orderOf_injective _ hinj g] at h1
  have htt : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hEcyc : IsCyclic ↥E := by
    rcases fixedSubgroup_dihedral_or_pgl hF e t htt ht1 with ⟨d, hdih, -⟩ | ⟨F₀, _, _, hF₀, ⟨ePGL⟩⟩
    · set M : Subgroup K := fixedSubgroup K t with hM
      have hcycW : IsCyclic ↥(E.subgroupOf M) :=
        isCyclic_of_odd_dihedral hdih (E.subgroupOf M) (fun w hw => by
          rw [← Subgroup.orderOf_coe]
          exact hEodd _ (Subgroup.mem_subgroupOf.mp hw))
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEz).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hEz).surjective
    · set M : Subgroup K := fixedSubgroup K t with hM
      have hnorm : (E.subgroupOf M).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have hgt : t (g : K) = g := g.2
        have h1 : t * MulAut.conj (g : K) * t⁻¹ = MulAut.conj (g : K) := by
          rw [mulAut_conj_conj', hgt]
        have hcomm : MulAut.conj (g : K) * t = t * MulAut.conj (g : K) := by
          calc MulAut.conj (g : K) * t = (t * MulAut.conj (g : K) * t⁻¹) * t := by rw [h1]
            _ = t * MulAut.conj (g : K) := by group
        have hgB : MulAut.conj (g : K) ∈ B ⊓ centralizer ({t} : Set (MulAut K)) :=
          mem_inf.2 ⟨hB ⟨g, rfl⟩, mem_centralizer_singleton_iff.2 hcomm⟩
        have h2 := (mem_normalizer_iff.1 (mem_normalizer_oddCoreIn hgB) _).1 hn
        show MulAut.conj ((g : K) * (n : K) * (g : K)⁻¹) ∈ Y
        rw [map_mul, map_mul, map_inv]
        exact h2
      have hodd : Odd (Nat.card ↥(E.subgroupOf M)) := by
        have h1 : Nat.card ↥(E.subgroupOf M) = Nat.card ↥E :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEz).toEquiv
        have h2 : Nat.card ↥E ∣ Nat.card ↥Y := by
          have hmap : Nat.card ↥(E.map (MulAut.conj : K →* MulAut K)) = Nat.card ↥E :=
            Subgroup.card_map_of_injective hinj
          rw [← hmap]
          exact Subgroup.card_dvd_of_le (fun x ⟨g, hg, hgx⟩ => hgx ▸ hg)
        have hY : Odd (Nat.card ↥Y) := by
          have h3 : Nat.card ↥Y =
              Nat.card ↥(pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set (MulAut K)))) :=
            Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
          rw [h3]
          exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
        rw [h1]
        exact Odd.of_dvd_nat hY h2
      have hF₀odd : Odd (Nat.card F₀) := (Nat.odd_mul.mp (hF₀ ▸ hF.1)).1
      have hpp := isOddPrimePower_of_odd_card hF₀odd
      have hbot := CFSG.DihedralBlueprint.normal_odd_eq_bot_of_pgl2_model F₀ hpp ePGL
        (E.subgroupOf M) hnorm hodd
      have hEbot : E = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        have hgM : (⟨g, hEz hg⟩ : ↥M) ∈ E.subgroupOf M := Subgroup.mem_subgroupOf.mpr hg
        rw [hbot, Subgroup.mem_bot] at hgM
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hgM)
      rw [hEbot]
      exact inferInstance
  set YK : Subgroup (MulAut K) := E.map (MulAut.conj : K →* MulAut K) with hYK
  have hYKcyc : IsCyclic ↥YK :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective E _ hinj).toMonoidHom
      (Subgroup.equivMapOfInjective E _ hinj).surjective
  have hYKY : YK ≤ Y := fun x ⟨g, hg, hgx⟩ => hgx ▸ hg
  have hYKN : ∀ i, ψ i ∈ normalizer (YK : Set (MulAut K)) := by
    intro i
    rw [mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨ψ i g, ?_, ?_⟩
      · show MulAut.conj (ψ i g) ∈ Y
        rw [← mulAut_conj_conj']
        exact (mem_normalizer_iff.1 (hψN i) _).1 hg
      · exact (mulAut_conj_conj' (ψ i) g).symm
    · rintro ⟨g, hg, hgw⟩
      have hw : w = MulAut.conj ((ψ i)⁻¹ g) := by
        rw [← mulAut_conj_conj']
        have hgw' : MulAut.conj g = ψ i * w * (ψ i)⁻¹ := hgw
        rw [hgw']
        group
      have hwY : w ∈ Y := by
        have h1 : ψ i * w * (ψ i)⁻¹ ∈ Y := by
          have hgw' : MulAut.conj g = ψ i * w * (ψ i)⁻¹ := hgw
          rw [← hgw']
          exact hg
        exact (mem_normalizer_iff.1 (hψN i) w).2 h1
      refine ⟨(ψ i)⁻¹ g, ?_, hw.symm⟩
      show MulAut.conj ((ψ i)⁻¹ g) ∈ Y
      rw [← hw]
      exact hwY
  have hcK : ∀ w ∈ YK, ψ a * w = w * ψ a := commute_of_isCyclic hI hYKcyc ψ hYKN hk
  set c : MulAut K := ψ a * y * (ψ a)⁻¹ * y⁻¹ with hc
  have hcY : c ∈ Y := by
    have h1 : ψ a * y * (ψ a)⁻¹ ∈ Y := (mem_normalizer_iff.1 (hψN a) y).1 hy
    exact Y.mul_mem h1 (Y.inv_mem hy)
  have hcD : c ∈ innDiagSub e := commutator_mem_innDiag e (ψ a) y
  obtain ⟨m, hm⟩ := hYodd c hcY
  have hcI : c ∈ innAut K := by
    refine mem_innAut_of_odd_pow hF e hcD (m := orderOf c) ⟨m, hm⟩ (pow_orderOf_eq_one c)
  have hcYK : c ∈ YK := by
    obtain ⟨g, hg⟩ := hcI
    refine ⟨g, ?_, hg⟩
    show MulAut.conj g ∈ Y
    rw [hg]
    exact hcY
  have hcomm_c : ψ a * c = c * ψ a := hcK c hcYK
  have hpow : ∀ n : ℕ, (ψ a) ^ n * y * ((ψ a) ^ n)⁻¹ = c ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : ψ a * y * (ψ a)⁻¹ = c * y := by rw [hc]; group
      have hcn : ψ a * c ^ n = c ^ n * ψ a := (Commute.pow_right hcomm_c n).eq
      calc (ψ a) ^ (n + 1) * y * ((ψ a) ^ (n + 1))⁻¹
          = ψ a * ((ψ a) ^ n * y * ((ψ a) ^ n)⁻¹) * (ψ a)⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = ψ a * (c ^ n * y) * (ψ a)⁻¹ := by rw [ih]
        _ = c ^ n * (ψ a * y * (ψ a)⁻¹) := by
            rw [← mul_assoc, hcn]; group
        _ = c ^ (n + 1) * y := by rw [h1, pow_succ]; group
  have hψk : (ψ a) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hck : c ^ (2 ^ k) = 1 := by
    have h1 := hpow (2 ^ k)
    rw [hψk, one_mul, inv_one, mul_one] at h1
    have h2 : c ^ (2 ^ k) * y = 1 * y := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel h2
  have hc1 : c = 1 := by
    have hodd := hYodd c hcY
    have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.1 hj
    · exfalso
      rw [hj] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero j⟩)
  have h1 : ψ a * y * (ψ a)⁻¹ * y⁻¹ = 1 := hc1
  calc ψ a * y = (ψ a * y * (ψ a)⁻¹ * y⁻¹) * y * ψ a := by group
    _ = y * ψ a := by rw [h1, one_mul]

end SolvKG

end CFSG.GH74.Generic.BProg.B3
