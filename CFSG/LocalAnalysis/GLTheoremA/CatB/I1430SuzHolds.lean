module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts
public import CFSG.RankThree.PartTwo.Census.TripleCoverSuz

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz


theorem i1430TwoLocal_of_suzX {H : Type} [Group H] [Finite H] (φ : H →* suzX)
    (hφ : Function.Surjective φ) (hker : φ.ker = Subgroup.center H) :
    I1430TwoLocal H (3 + CFSG.Open.pRank 3 (Subgroup.center H)) := by
  have hkc : φ.ker ≤ Subgroup.center H := hker.le
  set r := CFSG.Open.pRank 3 (Subgroup.center H) with hr
  have hcomm : ∀ x ∈ suzE.comap φ, ∀ y ∈ suzE.comap φ, x * y = y * x :=
    fun x hx y hy => commute_of_mem_suzE hφ hkc hx hy
  set U := TripleCoverLift.powOneSubgroup φ suzE 3 hcomm with hU
  have hmem : ∀ {y : H}, y ∈ U ↔ φ y ∈ suzE ∧ y ^ 3 = 1 := TripleCoverLift.mem_powOneSubgroup
  have hUe : CFSG.Open.IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (hmem.1 a.2).1 _ (hmem.1 b.2).1)⟩⟩,
      fun x hx => (hmem.1 hx).2⟩
  obtain ⟨Z₀, hZ₀, hZ₀e, hZ₀c⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (Subgroup.center H)
  have hZk : ∀ z ∈ Z₀, φ z = 1 := fun z hz => by
    rw [← MonoidHom.mem_ker, hker]
    exact hZ₀ hz
  have hZU : Z₀ ≤ U := fun z hz => hmem.2 ⟨by rw [hZk z hz]; exact suzE.one_mem, hZ₀e.2 z hz⟩
  let ψ : U →* suzX := φ.comp U.subtype
  have hψr : ψ.range = suzE := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (hmem.1 x.2).1
    · intro he
      obtain ⟨y, hy, hy3⟩ := exists_lift_of_mem_suzE hφ hkc he
      exact ⟨⟨y, hmem.2 ⟨hy ▸ he, hy3⟩⟩, hy⟩
  have hψk : 3 ^ r ≤ Nat.card ψ.ker := by
    rw [← hZ₀c, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv]
    exact Subgroup.card_le_of_le fun w hw => hZk _ (Subgroup.mem_subgroupOf.1 hw)
  have hcardU : 3 ^ (3 + r) ≤ Nat.card U := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψr] at h
    calc 3 ^ (3 + r) = 3 ^ r * 3 ^ 3 := by rw [pow_add, mul_comm]
      _ ≤ Nat.card ψ.ker * Nat.card suzE := Nat.mul_le_mul hψk card_suzE
      _ = Nat.card U := h
  obtain ⟨F₀, hF₀⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hUe.isPGroup hcardU
  have hFU : F₀.map U.subtype ≤ U := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hFc : Nat.card (F₀.map U.subtype) = 3 ^ (3 + r) := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hF₀]
  obtain ⟨y, hy⟩ := hφ tX
  have hdvd : 2 ∣ orderOf y := by
    rw [← orderOf_eq_prime tX_sq tX_ne_one, ← hy]
    exact orderOf_map_dvd φ y
  set u := y ^ (orderOf y / 2) with hu
  have huo : orderOf u = 2 := orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
  have hu2 : u ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [huo] at h
  have hcent : ∀ x ∈ U, Commute u x := by
    intro x hx
    have h : Commute (φ u) (φ x) := by
      rw [hu, map_pow, hy]
      exact (commute_tX (hmem.1 hx).1).pow_left _
    exact TripleCoverLift.commute_of_sq_eq_one hkc (by decide) hu2 (hmem.1 hx).2 h
  have hT : Subgroup.zpowers u ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    rw [h, orderOf_one] at huo
    exact absurd huo (by norm_num)
  have hT2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huo, pow_one])
  have hFN : F₀.map U.subtype ≤ Subgroup.normalizer (Subgroup.zpowers u : Set H) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨n, rfl⟩
    exact ((hcent x (hFU hx)).zpow_left n).eq
  exact ⟨Subgroup.zpowers u, F₀.map U.subtype, hT, hT2, hFN, hUe.mono hFU, hFc⟩

theorem i1430M23Suz_holds : I1430M23Suz := by
  intro H _ _ hq _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  have : IsSimpleGroup (H ⧸ Subgroup.center H) := hq.2
  have : IsSimpleGroup TauCeti.SporadicName.Suz.Group := e.symm.isSimpleGroup
  obtain ⟨eX⟩ := nonempty_mulEquiv_suzX
  let φ : H →* suzX := (e.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hφ : Function.Surjective φ :=
    (e.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center H := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact i1430TwoLocal_of_suzX φ hφ hker

end CFSG.LocalAnalysis.GLTheoremA.S8.L84

end
