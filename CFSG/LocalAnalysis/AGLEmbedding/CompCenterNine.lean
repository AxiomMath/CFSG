module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideKFacts
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineOrbit
import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineMult
import CFSG.RankThree.PartOne.KF.F128Act

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne (centerQuotientConj centerQuotientConj_mem_innerAut_iff)

theorem kFactCompCenterNine_of (hGA : GriessMultipliersAllModels)
    (hSpM : SporadicMultipliers) : KFactCompCenterNine := by
  intro X _ _ L hcomp hLn hcat E hEL hEc hEel hE9
  have hq : Open.IsQuasisimple L := hcomp.2.2
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  let ι : E →* Subgroup.center L := MonoidHom.mk'
    (fun e => ⟨⟨e.1, hEL e.2⟩, Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext (hEc e.1 e.2 l.1 l.2).symm⟩) fun _ _ => rfl
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (congrArg (fun z : Subgroup.center L => ((z : L) : X)) hab)
  have h9 : 9 ∣ Nat.card (Subgroup.center L) := by
    rw [← hE9, Nat.card_congr (MonoidHom.ofInjective hι).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hpow : ∀ e : E, ι e ^ 3 = 1 := fun e => by
    rw [← map_pow]
    have h1 : e ^ 3 = 1 := Subtype.ext (hEel.2 e.1 e.2)
    rw [h1, map_one]
  let κ : E → {z : Subgroup.center L // z ^ 3 = 1} := fun e => ⟨ι e, hpow e⟩
  have hκ : Function.Injective κ := fun a b hab => hι (congrArg Subtype.val hab)
  have hc : 9 ≤ Nat.card {z : Subgroup.center L // z ^ 3 = 1} :=
    hE9 ▸ Nat.card_le_card_of_injective κ hκ
  obtain ⟨hle9, h8, a, b, ha, hb, ha2, hb2, hab⟩ :=
    CompCenterNine.center_nine_cases hGA hSpM hq hcat h9 hc
  have hκs : Function.Surjective κ :=
    (hκ.bijective_of_nat_card_le (hle9.trans hE9.ge)).2
  have hEn : ∀ n : X, ∀ e ∈ E, n * e * n⁻¹ ∈ E := by
    intro n e he
    have hzL : n * e * n⁻¹ ∈ L := hLn.conj_mem e (hEL he) n
    have hzc : ∀ l : L, l * (⟨n * e * n⁻¹, hzL⟩ : L) = ⟨n * e * n⁻¹, hzL⟩ * l := by
      intro l
      apply Subtype.ext
      have hl : n⁻¹ * l * n⁻¹⁻¹ ∈ L := hLn.conj_mem l l.2 n⁻¹
      have h1 := hEc e he _ hl
      show (l : X) * (n * e * n⁻¹) = n * e * n⁻¹ * l
      calc (l : X) * (n * e * n⁻¹) = n * ((n⁻¹ * l * n⁻¹⁻¹) * e) * n⁻¹ := by group
        _ = n * (e * (n⁻¹ * l * n⁻¹⁻¹)) * n⁻¹ := by rw [h1]
        _ = n * e * n⁻¹ * l := by group
    have hz3 : (⟨⟨n * e * n⁻¹, hzL⟩, Subgroup.mem_center_iff.mpr hzc⟩ :
        Subgroup.center L) ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      show (n * e * n⁻¹) ^ 3 = 1
      rw [conj_pow, hEel.2 e he, mul_one, mul_inv_cancel]
    obtain ⟨e', he'⟩ := hκs ⟨_, hz3⟩
    have h1 := congrArg (fun z : {z : Subgroup.center L // z ^ 3 = 1} => ((z.1 : L) : X)) he'
    change (e' : X) = n * e * n⁻¹ at h1
    rw [← h1]
    exact e'.2
  have hN : ∀ x : X, x ∈ Subgroup.normalizer (L : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top x
  let Φ : X →* Outer (L ⧸ Subgroup.center L) :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner (L ⧸ Subgroup.center L))).comp
      ((centerQuotientConj L).comp ((MonoidHom.id X).codRestrict _ hN))
  have hker : ∀ x : X, Φ x = 1 → ∀ e ∈ E, x * e * x⁻¹ = e := by
    intro x hx e he
    have hinn : centerQuotientConj L ⟨x, hN x⟩ ∈ OuterAutomorphisms.inner (L ⧸ Subgroup.center L) :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨j, hj, z, hz, rfl⟩ := (CFSG.RankThree.PartOne.K1214.mem_sup_centralizer_iff L).mp
      ((centerQuotientConj_mem_innerAut_iff hperf (hN x)).mp hinn)
    have hze : z * e * z⁻¹ = e := by
      rw [← Subgroup.mem_centralizer_iff.mp hz e (hEL he), mul_inv_cancel_right]
    have hje : j * e * j⁻¹ = e := by rw [← hEc e he j hj, mul_inv_cancel_right]
    calc j * z * e * (j * z)⁻¹ = j * (z * e * z⁻¹) * j⁻¹ := by group
      _ = e := by rw [hze, hje]
  have : Finite (Outer (L ⧸ Subgroup.center L)) :=
    Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  exact CompCenterNine.exists_not_conj_of_two_involutions E hEn
    (fun a ha b hb => hEc a ha b (hEL hb)) hE9 Φ h8.le hker ha hb ha2 hb2 hab

end CFSG.AGLEmbedding
