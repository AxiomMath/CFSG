module

public import CFSG.LocalAnalysis.GLTheoremA.P55.OppCent
public import CFSG.LocalAnalysis.GLTheoremA.Sec5A
import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator.Generation228
  (exists_fixed_mem_coset tools_conj_comm_X tools_le_normalizer)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
  (exists_invariant_sylow_containing_of_pGroup)
open CFSG.QuasithinUnique.Setup.Layer (coprime_abelian_decomp)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section OPPrime

private theorem mem_glaPPrimeCoreOf_c2 {p : ℕ} {X : Subgroup G} {y : G} :
    y ∈ GLAPPrimeCoreOf p X ↔ ∃ h : y ∈ X, (⟨y, h⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

private theorem mem_oPPrimeP_c2 {p : ℕ} {X : Subgroup G} {y : G} :
    y ∈ oPPrimeP p X ↔ ∃ h : y ∈ X, QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, h⟩ ∈
      CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  unfold oPPrimeP
  simp [Subgroup.mem_map]

private theorem mk'_eq_one_iff_c2 {H : Type*} [Group H] {N : Subgroup H} [N.Normal] {z : H} :
    QuotientGroup.mk' N z = 1 ↔ z ∈ N :=
  QuotientGroup.eq_one_iff z

private theorem mem_map_subtype_c2 {X : Subgroup G} {N : Subgroup ↥X} {y : G} :
    y ∈ N.map X.subtype ↔ ∃ h : y ∈ X, (⟨y, h⟩ : ↥X) ∈ N := by
  simp [Subgroup.mem_map]

private theorem mem_map_comap_c2 {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]
    {Qb : Subgroup (↥X ⧸ N)} {y : G} :
    y ∈ (Qb.comap (QuotientGroup.mk' N)).map X.subtype ↔
      ∃ h : y ∈ X, QuotientGroup.mk' N ⟨y, h⟩ ∈ Qb := by
  simp [Subgroup.mem_map]

private theorem oPPrimeP_le_c2 (p : ℕ) (X : Subgroup G) : oPPrimeP p X ≤ X :=
  Subgroup.map_subtype_le _

private theorem le_normalizer_oPPrimeP_c2 (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oPPrimeP p X : Set G) := by
  have key : ∀ g ∈ X, ∀ y ∈ oPPrimeP p X, g * y * g⁻¹ ∈ oPPrimeP p X := by
    intro g hg y hy
    obtain ⟨hyX, hy'⟩ := mem_oPPrimeP_c2.1 hy
    refine mem_oPPrimeP_c2.2 ⟨X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg), ?_⟩
    have : (⟨g * y * g⁻¹, X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg)⟩ : ↥X) =
        ⟨g, hg⟩ * ⟨y, hyX⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact (CFSG.pCore_normal (G := ↥X ⧸ GLAPPrimeCore p ↥X) (p := p)).conj_mem _ hy' _
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨key g hg y, fun h => by simpa [mul_assoc] using key g⁻¹ (X.inv_mem hg) _ h⟩

private theorem eq_one_of_sq_eq_one_c2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p X))) {q : G} (hq : q ∈ oPPrimeP p X)
    (hq2 : q ^ 2 = 1) : q = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hqX, hqc⟩ := mem_oPPrimeP_c2.1 hq
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥X ⧸ GLAPPrimeCore p ↥X) (p := p))
    ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨q, hqX⟩, hqc⟩
  have hn' : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨q, hqX⟩ ^ (p ^ n) = 1 :=
    congrArg Subtype.val hn
  have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨q, hqX⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨q, hqX⟩ : ↥X) ^ 2 = 1 := Subtype.ext hq2
    rw [this, map_one]
  have hcop : Nat.Coprime 2 (p ^ n) :=
    ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)).pow_right n
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨q, hqX⟩ = 1 := by
    have := pow_gcd_eq_one.2 ⟨h2, hn'⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hmem : (⟨q, hqX⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 h1
  have hO : q ∈ GLAPPrimeCoreOf p X := mem_glaPPrimeCoreOf_c2.2 ⟨hqX, hmem⟩
  by_contra hq1
  have hord : orderOf q = 2 := orderOf_eq_prime hq2 hq1
  have hd : orderOf q ∣ Nat.card (GLAPPrimeCoreOf p X) := Subgroup.orderOf_dvd_natCard _ hO
  rw [hord] at hd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd)

private theorem not_two_dvd_card_c2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X Y : Subgroup G}
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p X))) (hY : Y ≤ oPPrimeP p X) :
    ¬ 2 ∣ Nat.card Y := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 h2
  have hy2 : (y : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hy1 : y = 1 := Subtype.ext (eq_one_of_sq_eq_one_c2 hp hp2 hodd (hY y.2) hy2)
  rw [hy1, orderOf_one] at hy
  omega

end OPPrime

section Sylow

private theorem exists_decomp_c2 {p : ℕ} (hp : p.Prime) {Y P₀ M : Subgroup G}
    (hP₀i : ¬ p ∣ P₀.relIndex Y) (hMn : P₀ ≤ Subgroup.normalizer (M : Set G))
    (hM : ∃ n, M.relIndex Y ∣ p ^ n) : ∀ y ∈ Y, ∃ a ∈ P₀, ∃ m ∈ M, y = a * m := by
  obtain ⟨n, hn⟩ := hM
  have h1 : (P₀ ⊔ M).relIndex Y ∣ P₀.relIndex Y := Subgroup.relIndex_dvd_of_le_left Y le_sup_left
  have h2 : (P₀ ⊔ M).relIndex Y ∣ M.relIndex Y := Subgroup.relIndex_dvd_of_le_left Y le_sup_right
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (h2.trans hn)
  have hi0 : i = 0 := by
    by_contra hne
    exact hP₀i ((dvd_pow_self p hne).trans (hi ▸ h1))
  rw [hi0, pow_zero] at hi
  have hY : Y ≤ P₀ ⊔ M := Subgroup.relIndex_eq_one.1 hi
  intro y hy
  have := hY hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P₀ M hMn] at this
  obtain ⟨a, ha, m, hm, rfl⟩ := Set.mem_mul.1 this
  exact ⟨a, ha, m, hm, rfl⟩

end Sylow

section AxB

private theorem centralizes_of_centralizes_fixed_c2 {p : ℕ} (hp : p.Prime) {H : Type*} [Group H]
    [Finite H] {Qb : Subgroup H} [Qb.Normal] (hQ : IsPGroup p Qb) {Eb : Subgroup H}
    (hE : IsPGroup p Eb) {a : H} (ha : ¬ p ∣ orderOf a) (hcomm : ∀ e ∈ Eb, a * e = e * a)
    (hfix : ∀ r ∈ Qb, (∀ e ∈ Eb, e * r = r * e) → a * r = r * a) :
    ∀ r ∈ Qb, a * r = r * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  let α : Subgroup.zpowers a →* MulAut Qb := MulAut.conjNormal.comp (Subgroup.zpowers a).subtype
  let β : Eb →* MulAut Qb := MulAut.conjNormal.comp Eb.subtype
  have hA : ¬ p ∣ Nat.card (Subgroup.zpowers a) := by rw [Nat.card_zpowers]; exact ha
  have hcomm' : ∀ (a' : Subgroup.zpowers a) (e : Eb), (a' : H) * e = e * a' := by
    intro a' e
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 a'.2
    rw [← hn]
    exact (Commute.zpow_left (show Commute a e from hcomm e e.2) n).eq
  have key := CFSG.GroupTheory.thompson_A_times_B hQ hA hE α β (fun a' e => by
      change (MulAut.conjNormal (a' : H) : MulAut Qb) * MulAut.conjNormal (e : H) =
        MulAut.conjNormal (e : H) * MulAut.conjNormal (a' : H)
      rw [← map_mul, ← map_mul, hcomm' a' e]) (fun a' r hr => by
      have hr' : ∀ e ∈ Eb, e * (r : H) = r * e := fun e he => by
        have h1 := congrArg Subtype.val (hr ⟨e, he⟩)
        change e * (r : H) * e⁻¹ = r at h1
        calc e * (r : H) = e * (r : H) * e⁻¹ * e := by group
          _ = r * e := by rw [h1]
      have hc : Commute a (r : H) := hfix r r.2 hr'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 a'.2
      apply Subtype.ext
      change (a' : H) * r * (a' : H)⁻¹ = r
      rw [← hn]
      have := (Commute.zpow_left hc n).eq
      calc a ^ n * (r : H) * (a ^ n)⁻¹ = (r : H) * a ^ n * (a ^ n)⁻¹ := by rw [this]
        _ = r := by group)
  intro r hr
  have h1 := congrArg (fun φ : MulAut Qb => (φ ⟨r, hr⟩ : H)) (key ⟨a, Subgroup.mem_zpowers a⟩)
  change a * r * a⁻¹ = r at h1
  calc a * r = a * r * a⁻¹ * a := by group
    _ = r * a := by rw [h1]

end AxB

private theorem commutator_mem_gen_c2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (N : Subgroup ↥X) [N.Normal] (Qb : Subgroup (↥X ⧸ N)) [Qb.Normal] (hQb : IsPGroup p Qb)
    (hXO : X ≤ Subgroup.normalizer (N.map X.subtype : Set G))
    (hOp : ¬ p ∣ Nat.card (N.map X.subtype)) {E P₀ : Subgroup G} {u : G}
    (hEp : IsPGroup p E) (hEX : E ≤ X) (huX : u ∈ X) (hu2 : u ^ 2 = 1)
    (huE : ∀ e ∈ E, e * u = u * e)
    (hP₀Y : P₀ ≤ (Qb.comap (QuotientGroup.mk' N)).map X.subtype ⊓
      Subgroup.centralizer (E : Set G))
    (hP₀i : ¬ p ∣ P₀.relIndex ((Qb.comap (QuotientGroup.mk' N)).map X.subtype ⊓
      Subgroup.centralizer (E : Set G)))
    (hP₀u : ∀ y ∈ P₀, y * u = u * y) :
    ∀ q ∈ (Qb.comap (QuotientGroup.mk' N)).map X.subtype, ⁅q, u⁆ ∈ N.map X.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Q₀ := (Qb.comap (QuotientGroup.mk' N)).map X.subtype with hQ₀
  set O := N.map X.subtype with hO
  set Y := Q₀ ⊓ Subgroup.centralizer (E : Set G) with hY
  have hQ₀X : Q₀ ≤ X := Subgroup.map_subtype_le _
  have hYX : Y ≤ X := inf_le_left.trans hQ₀X
  have hOQ₀ : O ≤ Q₀ := by
    intro y hy
    obtain ⟨h, hyN⟩ := mem_map_subtype_c2.1 hy
    refine mem_map_comap_c2.2 ⟨h, ?_⟩
    rw [mk'_eq_one_iff_c2.2 hyN]
    exact Subgroup.one_mem _
  have hdecomp : ∀ y ∈ Y, ∃ b ∈ P₀, ∃ m ∈ Y ⊓ O, y = b * m := by
    refine exists_decomp_c2 hp hP₀i (fun g hg => ?_) ?_
    · exact Prop53.mem_normalizer_inf_of_mem (Subgroup.le_normalizer (hP₀Y hg))
        (hXO (hYX (hP₀Y hg)))
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQb
      refine ⟨n, ?_⟩
      rw [Subgroup.inf_relIndex_left]
      let φ : ↥Y →* ↥X ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hYX)
      have hker : φ.ker = O.subgroupOf Y := by
        ext y
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_map_subtype_c2]
        exact ⟨fun h => ⟨hYX y.2, mk'_eq_one_iff_c2.1 h⟩, fun ⟨_, h⟩ => mk'_eq_one_iff_c2.2 h⟩
      have hidx : O.relIndex Y = Nat.card φ.range := by
        rw [Subgroup.relIndex, ← hker]
        exact Subgroup.index_ker φ
      rw [hidx, ← hn]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨y, rfl⟩
      obtain ⟨h, hq⟩ := mem_map_comap_c2.1 y.2.1
      exact hq
  let Eb : Subgroup (↥X ⧸ N) := (E.subgroupOf X).map (QuotientGroup.mk' N)
  have hEbp : IsPGroup p Eb := (hEp.comap_subtype (K := X)).map _
  let a : ↥X ⧸ N := QuotientGroup.mk' N ⟨u, huX⟩
  have ha2 : a ^ 2 = 1 := by
    change QuotientGroup.mk' N ⟨u, huX⟩ ^ 2 = 1
    rw [← map_pow]
    have : (⟨u, huX⟩ : ↥X) ^ 2 = 1 := Subtype.ext hu2
    rw [this, map_one]
  have ha : ¬ p ∣ orderOf a := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hd.trans (orderOf_dvd_of_pow_eq_one ha2)))
  have hcomm : ∀ e ∈ Eb, a * e = e * a := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
    have h1 : (⟨u, huX⟩ : ↥X) * e' = e' * ⟨u, huX⟩ := Subtype.ext (huE e' he').symm
    change QuotientGroup.mk' N ⟨u, huX⟩ * QuotientGroup.mk' N e' =
      QuotientGroup.mk' N e' * QuotientGroup.mk' N ⟨u, huX⟩
    rw [← map_mul, ← map_mul, h1]
  have hfix : ∀ r ∈ Qb, (∀ e ∈ Eb, e * r = r * e) → a * r = r * a := by
    intro r hr hrE
    obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective N r
    have hqQ : (q' : G) ∈ Q₀ := mem_map_comap_c2.2 ⟨q'.2, hr⟩
    have hy : ∀ e ∈ E, (q' : G)⁻¹ * (e * q' * e⁻¹) ∈ O := by
      intro e he
      have heX : e ∈ X := hEX he
      have h1 := hrE (QuotientGroup.mk' N ⟨e, heX⟩) (Subgroup.mem_map.2 ⟨⟨e, heX⟩, he, rfl⟩)
      refine mem_map_subtype_c2.2 ⟨X.mul_mem (X.inv_mem q'.2)
        (X.mul_mem (X.mul_mem heX q'.2) (X.inv_mem heX)), ?_⟩
      have h2 : (⟨(q' : G)⁻¹ * (e * q' * e⁻¹), X.mul_mem (X.inv_mem q'.2)
          (X.mul_mem (X.mul_mem heX q'.2) (X.inv_mem heX))⟩ : ↥X) =
          q'⁻¹ * (⟨e, heX⟩ * q' * ⟨e, heX⟩⁻¹) := rfl
      rw [h2, ← mk'_eq_one_iff_c2 (N := N), map_mul, map_inv, map_mul, map_mul, map_inv, h1]
      group
    obtain ⟨n, hnO, hn⟩ := exists_fixed_mem_coset hp hEp (fun g hg => hXO (hEX hg)) hOp hy
    have hyY : (q' : G) * n ∈ Y := ⟨Subgroup.mul_mem _ hqQ (hOQ₀ hnO), hn⟩
    obtain ⟨b, hbP, m, hmYO, hbm⟩ := hdecomp _ hyY
    have hbX : b ∈ X := hYX (hP₀Y hbP)
    obtain ⟨hnX, hnN⟩ := mem_map_subtype_c2.1 hnO
    obtain ⟨hmX, hmN⟩ := mem_map_subtype_c2.1 hmYO.2
    have e1 : q' * ⟨n, hnX⟩ = (⟨b, hbX⟩ : ↥X) * ⟨m, hmX⟩ := Subtype.ext hbm
    have hπb : QuotientGroup.mk' N q' = QuotientGroup.mk' N ⟨b, hbX⟩ := by
      have e2 : QuotientGroup.mk' N (q' * ⟨n, hnX⟩) = QuotientGroup.mk' N q' := by
        rw [map_mul, mk'_eq_one_iff_c2.2 hnN, mul_one]
      have e3 : QuotientGroup.mk' N ((⟨b, hbX⟩ : ↥X) * ⟨m, hmX⟩) =
          QuotientGroup.mk' N ⟨b, hbX⟩ := by
        rw [map_mul, mk'_eq_one_iff_c2.2 hmN, mul_one]
      rw [← e2, e1, e3]
    rw [hπb]
    have h3 : (⟨u, huX⟩ : ↥X) * ⟨b, hbX⟩ = ⟨b, hbX⟩ * ⟨u, huX⟩ := Subtype.ext (hP₀u b hbP).symm
    change QuotientGroup.mk' N ⟨u, huX⟩ * QuotientGroup.mk' N ⟨b, hbX⟩ =
      QuotientGroup.mk' N ⟨b, hbX⟩ * QuotientGroup.mk' N ⟨u, huX⟩
    rw [← map_mul, ← map_mul, h3]
  have hAB := centralizes_of_centralizes_fixed_c2 hp hQb hEbp ha hcomm hfix
  intro q hq
  obtain ⟨hqX, hqQ⟩ := mem_map_comap_c2.1 hq
  have h1 := hAB _ hqQ
  refine mem_map_subtype_c2.2 ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hqX huX) (X.inv_mem hqX)) (X.inv_mem huX)
  · refine mk'_eq_one_iff_c2.1 ?_
    have : (⟨⁅q, u⁆, by rw [commutatorElement_def]; exact X.mul_mem (X.mul_mem (X.mul_mem hqX huX)
        (X.inv_mem hqX)) (X.inv_mem huX)⟩ : ↥X) = ⁅(⟨q, hqX⟩ : ↥X), ⟨u, huX⟩⁆ := rfl
    rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1.symm

private theorem commutator_mem_of_centralizes_c2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X E P₀ : Subgroup G} {u : G} (hEp : IsPGroup p E) (hEX : E ≤ X) (huX : u ∈ X)
    (hu2 : u ^ 2 = 1) (huE : ∀ e ∈ E, e * u = u * e)
    (hP₀Y : P₀ ≤ oPPrimeP p X ⊓ Subgroup.centralizer (E : Set G))
    (hP₀i : ¬ p ∣ P₀.relIndex (oPPrimeP p X ⊓ Subgroup.centralizer (E : Set G)))
    (hP₀u : ∀ y ∈ P₀, y * u = u * y) : ∀ q ∈ oPPrimeP p X, ⁅q, u⁆ ∈ GLAPPrimeCoreOf p X :=
  commutator_mem_gen_c2 hp hp2 (GLAPPrimeCore p ↥X) (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X))
    CFSG.pCore_isPGroup (le_normalizer_glaPPrimeCoreOf p X) (not_dvd_card_glaPPrimeCoreOf hp X)
    hEp hEX huX hu2 huE hP₀Y hP₀i hP₀u

theorem false_of_faithful {p : ℕ} (hc : Sec5Ctx G p) (h51 : Prop51At G p) (hdih : DihedralUsed)
    {B L T E U : Subgroup G} {x : G} {k : ℕ} (hBxL : IsS0Max p B x L)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))))
    (hT2 : IsPGroup 2 T) (hTx : T ≤ Subgroup.centralizer ({x} : Set G))
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hEB : E ≤ B)
    (hEk : Nat.card E * p ^ k = Nat.card B) (hk : 1 ≤ k)
    (hUR : U ≤ T ⊓ Subgroup.centralizer (E : Set G)) (hU : IsElemAbelian 2 U)
    (hUk : Nat.card U = 2 ^ (k + 1))
    (hfaith : ∀ u ∈ U, (∀ q ∈ oPPrimeP p (Subgroup.centralizer ({x} : Set G)),
      ⁅q, u⁆ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) → u = 1) : False := by
  clear hT2 hBT
  have hp := hc.prime
  have hp2 := hc.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : IsSTriple p B x L := hBxL.1.1
  have hB : GLAIsBmax p B := hS.1
  have hxB : x ∈ B := hS.2.1.1
  have hBX : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hB.1 hxB
  have hLX : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  set X := Subgroup.centralizer ({x} : Set G) with hXdef
  have hEX : E ≤ X := hEB.trans hBX
  have hEelem : IsElemAbelian p E := isElemAbelian_mono hB.1 hEB
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hEelem
  have hUX : U ≤ X := (hUR.trans inf_le_left).trans hTx
  have hUE : U ≤ Subgroup.centralizer (E : Set G) := hUR.trans inf_le_right
  have hUp : IsPGroup 2 U := isPGroup_of_isElemAbelian hU
  have hUEc : ∀ u ∈ U, ∀ e ∈ E, e * u = u * e := fun u hu e he =>
    Subgroup.mem_centralizer_iff.1 (hUE hu) e he
  set Q₀ := oPPrimeP p X with hQ₀
  set Y := Q₀ ⊓ Subgroup.centralizer (E : Set G) with hY
  have hUY : U ≤ Subgroup.normalizer (Y : Set G) := fun u hu =>
    Prop53.mem_normalizer_inf_of_mem (le_normalizer_oPPrimeP_c2 p X (hUX hu))
      (Subgroup.le_normalizer (hUE hu))
  have hUbot : U ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨P₀, -, hP₀Y, hP₀p, hP₀i, hUP₀⟩ := exists_invariant_sylow_containing_of_pGroup
    Nat.prime_two hp hUp hUY (not_two_dvd_card_c2 hp hp2 hodd inf_le_left) bot_le
    IsPGroup.of_bot hUbot
  have hfaith' : ∀ u ∈ U, P₀ ≤ Subgroup.centralizer ({u} : Set G) → u = 1 := by
    intro u hu hP
    refine hfaith u hu fun q hq => ?_
    exact commutator_mem_of_centralizes_c2 hp hp2 hEp hEX (hUX hu) (hU.2 u hu) (hUEc u hu) hP₀Y
      hP₀i (fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hP hy)) q hq
  obtain ⟨u, hu, hu1, Q₁, hQ₁P, hQ₁e, hQ₁k, hQ₁u, hQ₁U⟩ :=
    hdih G p hp hp2 P₀ U k hP₀p hU hUk hUP₀ hfaith'
  have hQ₁Y : Q₁ ≤ Y := hQ₁P.trans hP₀Y
  have hQ₁Q₀ : Q₁ ≤ Q₀ := hQ₁Y.trans inf_le_left
  have hQ₁E : Q₁ ≤ Subgroup.centralizer (E : Set G) := hQ₁Y.trans inf_le_right
  have hQ₁X : Q₁ ≤ X := hQ₁Q₀.trans (oPPrimeP_le_c2 p X)
  have hcomm : ∀ q ∈ Q₁, ∀ e ∈ E, q * e = e * q := fun q hq e he =>
    (Subgroup.mem_centralizer_iff.1 (hQ₁E hq) e he).symm
  have hAelem : IsElemAbelian p (Q₁ ⊔ E) := Prop53.isElemAbelian_sup_of_commute hQ₁e hEelem hcomm
  have hU1norm : U ≤ Subgroup.normalizer (Q₁ : Set G) := by
    refine tools_le_normalizer (fun g hg y hy => ?_)
    have hy' : y ∈ (⁅U, Q₁⁆ : Subgroup G) := by
      rw [Subgroup.commutator_comm, hQ₁U]
      exact hy
    have h2 := tools_conj_comm_X hg y hy'
    rw [Subgroup.commutator_comm, hQ₁U] at h2
    exact h2
  have hcop : Nat.Coprime (Nat.card U) (Nat.card Q₁) := by
    rw [hUk, hQ₁k]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hdisj := (coprime_abelian_decomp Q₁ U hU1norm
    (fun a b => Subtype.ext (isElemAbelian_commute hQ₁e a.2 b.2)) hcop).2
  rw [hQ₁U] at hdisj
  have hQ₁EU : Q₁ ⊓ E = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have hzU : z ∈ Q₁ ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨hz.1, Subgroup.mem_centralizer_iff.2 fun h hh => (hUEc h hh z hz.2).symm⟩
    rwa [hdisj.eq_bot_of_le inf_le_left] at hzU
  have hEN : E ≤ Subgroup.normalizer (Q₁ : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun q hq =>
      hcomm q hq e he)
  have hcardA : Nat.card (Q₁ ⊔ E : Subgroup G) = Nat.card B := by
    have h := card_sup_mul_card_inf_of_le_normalizer hEN
    rw [hQ₁EU, Subgroup.card_bot, mul_one, hQ₁k] at h
    rw [h, mul_comm, hEk]
  have hAu : Q₁ ⊔ E ≤ Subgroup.centralizer ({u} : Set G) := sup_le hQ₁u fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (hUEc u hu e he)
  have hAnorm : Q₁ ⊔ E ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := fun a ha =>
    Prop53.mem_normalizer_zpowers_of_comm (Subgroup.mem_centralizer_singleton_iff.1 (hAu ha))
  have hzu : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
  have hzu2 : IsPGroup 2 (Subgroup.zpowers u) := hUp.to_le (Subgroup.zpowers_le.2 hu)
  have hAmax : GLAIsBmax p (Q₁ ⊔ E) :=
    ⟨hAelem, by rw [hcardA]; exact hB.2.1, Subgroup.zpowers u, hzu, hzu2, hAnorm⟩
  have hxp : x ^ p = 1 := hB.1.2 x hxB
  have hxu : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.1 (hUX hu)).symm
  have hxA : x ∈ Q₁ ⊔ E := by
    have hAx : Q₁ ⊔ E ≤ Subgroup.centralizer ({x} : Set G) := sup_le hQ₁X hEX
    have hE' := isElemAbelian_sup_zpowers hAelem hAx hxp
    have := GLAIsBmax.eq_of_le hp hAmax le_sup_left hE' hzu hzu2
      (sup_le hAnorm (Subgroup.zpowers_le.2 (Prop53.mem_normalizer_zpowers_of_comm hxu)))
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hdec : ∀ b ∈ Q₁ ⊔ E, ∃ w ∈ B ⊓ (Q₁ ⊔ E), ∃ v ∈ Q₁ ⊔ E, CentMod p L v ∧ b = w * v := by
    intro b hb
    have hnorm : Q₁ ≤ Subgroup.normalizer (E : Set G) := fun q hq =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun e he =>
        (hcomm q hq e he).symm)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Q₁ E hnorm] at hb
    obtain ⟨q, hq, e, he, rfl⟩ := Set.mem_mul.1 hb
    exact ⟨e, ⟨hEB he, Subgroup.mem_sup_right he⟩, q, Subgroup.mem_sup_left hq,
      centMod_iff.2 (oPPrimeP_le_centModSubgroup hp hLX (hQ₁Q₀ hq)), hcomm q hq e he⟩
  have h52 := lemma52 hc h51 hBxL hAmax hxA hdec
  have hQ₁x : Q₁ ≤ Subgroup.zpowers x := fun q hq =>
    (h52 q (Subgroup.mem_sup_left hq)).1
      (centMod_iff.2 (oPPrimeP_le_centModSubgroup hp hLX (hQ₁Q₀ hq)))
  have hxcU : x ∈ Subgroup.centralizer (U : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hUX hh)
  have hbot : (⁅Q₁, U⁆ : Subgroup G) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hQ₁x.trans (Subgroup.zpowers_le.2 hxcU))
  rw [hQ₁U] at hbot
  have h1 : Nat.card Q₁ = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [hQ₁k] at h1
  exact (Nat.one_lt_pow (by omega) hp.one_lt).ne' h1

end CFSG.LocalAnalysis.GLTheoremA.P55
