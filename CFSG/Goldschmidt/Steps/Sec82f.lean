module

public import CFSG.Goldschmidt.Steps.Sec82a
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec84a
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.G36Setup
import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open CFSG.GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G} {a : G}
  {H : Subgroup G} {p : ℕ} {M L : Subgroup G}

theorem normalizer_le (h31 : S_G31) (c : Ctx S A a H p M L) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  obtain ⟨n, hnM, hn, hnc⟩ := Sec8.exists_mem_normalizer_of_isComponentOf h31 c.hset c.h4 c.hS
    c.hLQ
  exact Sec8.normalizer_le c.hset c.h4 c.hCM hnM hn hnc

theorem odd_card_center (h31 : S_G31) (c : Ctx S A a H p M L) :
    Odd (Nat.card (Subgroup.center L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T₀, hT₀, -⟩ := exists_g36Hyp h31 c.hS c.hset.elem c.hLQ
  obtain ⟨n, hnM, hn, hnc⟩ := Sec8.exists_mem_normalizer_of_isComponentOf h31 c.hset c.h4 c.hS
    c.hLQ
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center L) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 2 h2
  have hz2 : (z : L) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at hz
    rw [← hz, pow_orderOf_eq_one]
  have hzA : ((z : L) : G) ∈ A := hT₀.center_two (z : L) z.2 1 (by rw [pow_one]; exact hz2)
  have hz1 : ((z : L) : G) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨m, hm, hma⟩ := Sec8.exists_conj_of_mem_normalizer c.hset c.h4 hnM hn hnc hzA hz1 c.ha
    c.ha1
  apply c.haL
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have hl' : m⁻¹ * l * m ∈ L := by
    simpa using (Subgroup.mem_normalizer_iff.mp (c.hML (M.inv_mem hm)) l).mp hl
  have hzc := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨_, hl'⟩)
  simp only [Subgroup.coe_mul] at hzc
  rw [← hma]
  calc l * (m * (z : L) * m⁻¹) = m * ((m⁻¹ * l * m) * (z : L)) * m⁻¹ := by group
    _ = m * ((z : L) * (m⁻¹ * l * m)) * m⁻¹ := by rw [hzc]
    _ = m * (z : L) * m⁻¹ * l := by group

theorem card_le_four (h31 : S_G31) (c : Ctx S A a H p M L) {X : Subgroup G} (hXL : X ≤ L)
    (hX : IsPGroup 2 X) : Nat.card X ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, f, hq, hqodd, hf, -, h8, ⟨e⟩⟩ := c.hL2
  have hZodd := odd_card_center h31 c
  set X' := X.subgroupOf L with hX'
  let π : L →* PSL(2, GaloisField q f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have himg : IsPGroup 2 (X'.map π) := by
    refine IsPGroup.map (fun x => ?_) π
    obtain ⟨k, hk⟩ := hX ⟨(x : L), x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨P, hP⟩ := himg.exists_le_sylow
  have hP4 : Nat.card P = 4 := (Walter.psl2_odd_sylow_two_isKleinFour hqodd hf h8 P).card_four
  let ψ : X' → P := fun x => ⟨π x, hP ⟨x, x.2, rfl⟩⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : π x = π y := congrArg Subtype.val hxy
    have h2 : π ((x : L)⁻¹ * y) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (x : L)⁻¹ * y ∈ Subgroup.center L := by
      have h4 : QuotientGroup.mk' (Subgroup.center L) ((x : L)⁻¹ * y) = 1 :=
        e.injective (by simpa [π] using h2)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
    have hxy' : (x : L)⁻¹ * y ∈ X' := X'.mul_mem (X'.inv_mem x.2) y.2
    obtain ⟨k, hk⟩ := hX ⟨(((x : L)⁻¹ * y : L) : G), hxy'⟩
    have h5 : orderOf (⟨(x : L)⁻¹ * y, h3⟩ : Subgroup.center L) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk)))
    have h6 := orderOf_dvd_natCard (⟨(x : L)⁻¹ * y, h3⟩ : Subgroup.center L)
    have h7 : orderOf (⟨(x : L)⁻¹ * y, h3⟩ : Subgroup.center L) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZodd)) h5 h6
    have h8 : (x : L)⁻¹ * y = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp h7)
    exact Subtype.ext (inv_mul_eq_one.mp h8)
  calc Nat.card X = Nat.card X' := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv).symm
    _ ≤ Nat.card P := Nat.card_le_card_of_injective ψ hψ
    _ = 4 := hP4

theorem exists_mul_eq_of_mem_centralizer (h31 : S_G31) (h35 : S_G35) (c : Ctx S A a H p M L)
    {s : G} (hs : s ∈ Subgroup.centralizer (A : Set G)) {k : ℕ} (hk : s ^ 2 ^ k = 1) :
    ∃ l ∈ L, ∃ y ∈ M ⊓ Subgroup.centralizer (L : Set G), l * y = s := by
  have hII : IsGoldTypeII L := ⟨odd_card_center h31 c, Or.inl c.hL2⟩
  set L' := L.subgroupOf M with hL'
  set A' := A.subgroupOf M with hA'
  set Y' := (Subgroup.centralizer (A : Set G)).subgroupOf M with hY'
  have hLn : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer c.hLM).mpr c.hML
  let e : L ≃* L' := (Subgroup.subgroupOfEquivOfLe c.hLM).symm
  have hLq : CFSG.Open.IsQuasisimple L' := isQuasisimple_of_mulEquiv e ⟨c.hL.2.2.2.1, c.hL.2.2.2.2⟩
  have hII' : IsGoldTypeII L' := SStarTransport.isGoldTypeII_of_mulEquiv e hII
  have hS' : IsSStarIn L' A' :=
    SStarTransport.isSStarIn_subgroupOf (Sec8.sstar_of_le c.hset c.hLtop c.hAL) c.hLM
  have hA1 : A' ≠ ⊥ := by
    obtain ⟨b, hb, hb1⟩ := Sec8.exists_mem_ne_one c.hset
    intro h
    have hb' : (⟨b, c.hAM hb⟩ : M) ∈ A' := hb
    rw [h, Subgroup.mem_bot] at hb'
    exact hb1 (congrArg Subtype.val hb')
  obtain ⟨h1, -⟩ := h35 M L' A' Y' hLn hLq hII' hS' hA1
  have hYA : ⁅Y', A'⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun y hy => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.mp hy x hx
  obtain ⟨hodd, -⟩ := h1 hYA
  have hsM : s ∈ M := c.hCM hs
  have hN : (L' ⊔ Subgroup.centralizer (L' : Set M)).Normal := inferInstance
  have hYN : Y' ≤ Subgroup.normalizer
      ((L' ⊔ Subgroup.centralizer (L' : Set M) : Subgroup M) : Set M) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
    exact le_top
  have hmem := mem_of_odd_index hYN hodd (show (⟨s, hsM⟩ : M) ∈ Y' from hs) (k := k)
    (Subtype.ext (by simpa using hk))
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨l, hl, y, hy, hly⟩ := Set.mem_mul.mp hmem
  refine ⟨l, hl, y, ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy ⟨x, c.hLM hx⟩ hx)
  · exact congrArg Subtype.val hly

end CFSG.Goldschmidt.Sec82
