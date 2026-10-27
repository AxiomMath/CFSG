module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Comp
public import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

theorem pow_eq_one_of_fixed_div {A : Type*} [CommGroup A] (α : MulAut A) (q : ℕ)
    (hα : α ^ q = 1) (a : A) (hfix : α (α a / a) = α a / a) : (α a / a) ^ q = 1 := by
  have h1 : ∀ i : ℕ, (α ^ i) (α a / a) = α a / a := by
    intro i
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hfix]
  have h2 : (α a / a) ^ q = ∏ i ∈ Finset.range q, (α ^ i) (α a / a) := by
    simp only [h1, Finset.prod_const, Finset.card_range]
  have h3 : ∀ i : ℕ, (α ^ i) (α a / a) = (α ^ (i + 1)) a / (α ^ i) a := by
    intro i
    rw [map_div, pow_succ, MulAut.mul_apply]
  rw [h2]
  simp only [h3]
  rw [Finset.prod_range_div (fun i => (α ^ i) a) q]
  simp [hα]

theorem commute_of_fixed_order_p {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q)
    {Y : Type} [Group Y]
    {A : Subgroup Y} [A.Normal] (hAc : ∀ a b : A, a * b = b * a) (hAp : IsPGroup p A)
    {g : Y} (hg : g ^ q = 1) (hfix : ∀ a : A, a ^ p = 1 → MulAut.conjNormal g a = a)
    (a : A) : MulAut.conjNormal g a = a := by
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hAc }
  set α : MulAut A := MulAut.conjNormal g with hα
  have hαq : α ^ q = 1 := by rw [hα, ← map_pow, hg, map_one]
  by_contra hne
  set b : A := α a / a with hb
  have hb1 : b ≠ 1 := fun h => hne (div_eq_one.1 h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hAp) b
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hb1 (orderOf_eq_one_iff.1 (by simpa using hk))
  set e : ℕ := p ^ (k - 1) with he
  have he0 : e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hdvd : e ∣ orderOf b := by
    rw [hk]
    exact pow_dvd_pow p (Nat.sub_le k 1)
  have hord : orderOf (b ^ e) = p := by
    rw [orderOf_pow_of_dvd he0 hdvd, hk, he, Nat.pow_div (Nat.sub_le k 1)
      (Fact.out : p.Prime).pos]
    have : k - (k - 1) = 1 := by omega
    rw [this, pow_one]
  have hbp : (b ^ e) ^ p = 1 := by
    have := pow_orderOf_eq_one (b ^ e)
    rwa [hord] at this
  have hfixb : α (α (a ^ e) / a ^ e) = α (a ^ e) / a ^ e := by
    have : α (a ^ e) / a ^ e = b ^ e := by rw [map_pow, div_pow]
    rw [this]
    exact hfix _ hbp
  have hnorm := pow_eq_one_of_fixed_div α q hαq (a ^ e) hfixb
  have hbe : α (a ^ e) / a ^ e = b ^ e := by rw [map_pow, div_pow]
  rw [hbe] at hnorm
  have hcop : Nat.Coprime p q := (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hpq
  have h1 : b ^ e = 1 := by
    have h : (b ^ e) ^ Nat.gcd p q = 1 := pow_gcd_eq_one.2 ⟨hbp, hnorm⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
  rw [h1, orderOf_one] at hord
  exact (Fact.out : p.Prime).one_lt.ne hord

theorem layer_eq {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L) : CFSG.layer Y = L := by
  rw [CFSG.layer_eq_componentClassification, ComponentClassification.Layer.subgroup.eq_sSup]
  have hset : {K : Subgroup Y | IsComponentOf K ⊤} = {L} :=
    Set.ext fun K => ⟨hLu K, fun h => h ▸ hL⟩
  rw [hset, sSup_singleton]

theorem pCore_le_centralizer {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : CFSG.pCore p Y ≤ centralizer (L : Set Y) := by
  have hsub : IsSubnormal (CFSG.pCore p Y) ⊤ :=
    ComponentClassification.Components.chain_of_mathlib_subnormal
      (inferInstance : (CFSG.pCore p Y).Normal).isSubnormal
  haveI : Group.IsNilpotent ↥(CFSG.pCore p Y) :=
    (CFSG.pCore_isPGroup (G := Y) (p := p)).isNilpotent
  haveI : Group.IsSolvable ↥(CFSG.pCore p Y) := inferInstance
  have hcomm := ComponentClassification.Layer.commutes_with_solvable_subnormal
    (CFSG.pCore p Y) hsub
  have hLle : L ≤ ComponentClassification.Layer.subgroup Y :=
    ComponentClassification.Layer.component_le hL
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hcent (hLle hl)) x hx).symm

theorem centralizer_isPGroup {p : ℕ} [hp : Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hcore : primeComplementCore (G := Y) p = ⊥) (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L)
    (hcyc : IsCyclic ↥(CFSG.pCore p Y)) (hΩ : ∀ g ∈ CFSG.pCore p Y, g ^ p = 1 → g ∈ L) :
    IsPGroup p (centralizer (L : Set Y)) := by
  haveI : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have hLn : L.Normal := normal_of_unique hL hLu
  set C := centralizer (L : Set Y) with hC
  have hF : CFSG.generalizedFitting Y = CFSG.pCore p Y ⊔ L := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Y p hcore, layer_eq hL hLu]
  have hbound : centralizer (((CFSG.pCore p Y ⊔ L : Subgroup Y)) : Set Y) ≤ CFSG.pCore p Y := by
    have := CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup (G := Y)
    rwa [hF, CFSG.Fitting_eq_pcore Y p hcore] at this
  have hAc : ∀ a b : CFSG.pCore p Y, a * b = b * a := by
    haveI := hcyc
    intro a b
    letI : CommGroup (CFSG.pCore p Y) := IsCyclic.commGroup
    exact mul_comm a b
  have hAp : IsPGroup p (CFSG.pCore p Y) := CFSG.pCore_isPGroup
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro q hq hqdvd
  by_contra hqp
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  have hgC : (g : Y) ∈ C := g.2
  have hgq : (g : Y) ^ q = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    simpa using congrArg Subtype.val h
  have hgcL : ∀ l ∈ L, l * (g : Y) = (g : Y) * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp hgC l hl
  have hfix : ∀ a : CFSG.pCore p Y, a ^ p = 1 → MulAut.conjNormal (g : Y) a = a := by
    intro a ha
    have hap : (a : Y) ^ p = 1 := by simpa using congrArg Subtype.val ha
    have hl := hΩ a a.2 hap
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc (g : Y) * (a : Y) * (g : Y)⁻¹ = (a : Y) * (g : Y) * (g : Y)⁻¹ := by
          rw [← hgcL _ hl]
      _ = (a : Y) := by group
  have hcomm : ∀ a : CFSG.pCore p Y, (g : Y) * a * (g : Y)⁻¹ = a := by
    intro a
    have := commute_of_fixed_order_p hq (Ne.symm hqp) hAc hAp hgq hfix a
    simpa [MulAut.conjNormal_apply] using congrArg Subtype.val this
  have hle : (CFSG.pCore p Y ⊔ L : Subgroup Y) ≤ centralizer ({(g : Y)} : Set Y) := by
    refine sup_le (fun a ha => ?_) (fun l hl => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := hcomm ⟨a, ha⟩
      calc a * (g : Y) = (g : Y) * a * (g : Y)⁻¹ * (g : Y) := by rw [this]
        _ = (g : Y) * a := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hgcL l hl
  have hgcent : (g : Y) ∈ centralizer (((CFSG.pCore p Y ⊔ L : Subgroup Y)) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
  have hgR : (g : Y) ∈ CFSG.pCore p Y := hbound hgcent
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hAp) ⟨(g : Y), hgR⟩
  have hord : orderOf (⟨(g : Y), hgR⟩ : CFSG.pCore p Y) = q := by
    rw [← hg, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe g]
  rw [hord] at hk
  have hqk : q ∣ p ^ k := by rw [← hk]
  exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).1 (hq.dvd_of_dvd_pow hqk))

theorem centralizer_eq_pCore {p : ℕ} [hp : Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hcore : primeComplementCore (G := Y) p = ⊥) (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L)
    (hcyc : IsCyclic ↥(CFSG.pCore p Y)) (hΩ : ∀ g ∈ CFSG.pCore p Y, g ^ p = 1 → g ∈ L) :
    centralizer (L : Set Y) = CFSG.pCore p Y := by
  have hLn : L.Normal := normal_of_unique hL hLu
  have hCn : (centralizer (L : Set Y)).Normal := inferInstance
  refine le_antisymm (le_sSup ⟨hCn, centralizer_isPGroup hcore hL hLu hcyc hΩ⟩)
    (pCore_le_centralizer hL)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292
