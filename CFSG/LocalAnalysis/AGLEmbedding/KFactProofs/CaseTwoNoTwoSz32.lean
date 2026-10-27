module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoSplit
public import CFSG.RankThree.PartOne.K159.AutSzAbs
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.LieType.Suzuki.SuzukiOuterCyclic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.AGLEmbedding

namespace SzNoTwo

open CFSG.RankThree.PartOne.K159.SzAbs
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem eq_bot_of_normalizes {G : Type} [Group G] [Finite G]
    (hSz : SzSylow G) (hZ : ∀ g : G, (∀ x, g * x = x * g) → g = 1)
    (hOut : Nat.card (Outer G) ∣ 5)
    {t : G} (ht : orderOf t = 5) {U : Subgroup (MulAut G)} (hU : IsPGroup 2 U)
    (hN : MulAut.conj t ∈ Subgroup.normalizer (U : Set (MulAut G))) : U = ⊥ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup (MulAut G) := inner G with hI
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.2 (hZ g fun x => ?_)
    have := congrArg (fun α : MulAut G => α x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [this]
  have hidx : I.index ∣ 5 := hOut
  have hUI : U ≤ I := by
    intro f hf
    obtain ⟨k, hk⟩ := hU ⟨f, hf⟩
    have hfk : f ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hf5 : f ^ 5 ∈ I := by
      obtain ⟨c, hc⟩ := hidx
      rw [hc, pow_mul]
      exact I.pow_mem (Subgroup.pow_index_mem I f) c
    have hcop : Nat.Coprime 5 (orderOf f) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hfk)
        (Nat.Coprime.pow_right k (by norm_num))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact I.pow_mem hf5 m
  set V : Subgroup G := U.comap (MulAut.conj : G →* MulAut G) with hV
  have hVp : IsPGroup 2 V := by
    intro g
    obtain ⟨k, hk⟩ := hU ⟨MulAut.conj (g : G), g.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    apply hinj
    rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    simpa using congrArg Subtype.val hk
  by_contra hne
  obtain ⟨⟨f, hfU⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨u, rfl⟩ := hUI hfU
  have hu1 : u ≠ 1 := fun h => hf1 (Subtype.ext (by simp [h]))
  have huV : u ∈ V := hfU
  have htV : ∀ g, g ∈ V ↔ t * g * t⁻¹ ∈ V := by
    intro g
    have := Subgroup.mem_normalizer_iff.1 hN (MulAut.conj g)
    simpa [hV] using this
  obtain ⟨P, hVP⟩ := hVp.exists_le_sylow
  have hVP' : (V : Subgroup G) ≤ ((t • P : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    intro v hv
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    have hv' : t⁻¹ * v * t ∈ V := (htV _).2 (by simpa [mul_assoc] using hv)
    refine ⟨t⁻¹ * v * t, hVP hv', ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  have hTI : t • P = P := by
    by_contra hne
    have hti := hSz.ti (t • P) P hne
    have hu_in : u ∈ ((t • P : Sylow 2 G) : Subgroup G) ⊓ (P : Subgroup G) :=
      ⟨hVP' huV, hVP huV⟩
    rw [hti] at hu_in
    exact hu1 (Subgroup.mem_bot.1 hu_in)
  have htN : t ∈ Subgroup.normalizer (P : Set G) := Sylow.smul_eq_iff_mem_normalizer.1 hTI
  have hcard : Nat.card (Subgroup.normalizer (P : Set G)) = 31744 := by
    have h0 := Sylow.card_eq_index_normalizer P
    have h1 := Subgroup.card_mul_index (Subgroup.normalizer (P : Set G))
    rw [← h0, hSz.card_sylow, hSz.card] at h1
    omega
  have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.normalizer (P : Set G)) htN
  rw [hcard, ht] at hdvd
  omega

end SzNoTwo

theorem kFactCaseTwoNoTwoSz32 :
    KFactCaseTwoNoTwoSz32 := by
  rintro p K _ _ ⟨rfl, d, hd, he⟩ t ht U hU hN
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, he⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ∣ 5 :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} K 2 5 hmodel).1.2.1
  have hsimple : IsSimpleGroup K := by
    obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hmodel
    have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  have hnc : ∃ a b : K, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd (q := 5) (by norm_num) (by rw [hSz.card]; norm_num)
  have hcenter := center_bot_of_simple_nonab hnc
  exact SzNoTwo.eq_bot_of_normalizes hSz
    (fun g hg => Subgroup.mem_bot.1 (hcenter ▸ Subgroup.mem_center_iff.2 fun y => (hg y).symm))
    hOut ht hU hN

end CFSG.AGLEmbedding
