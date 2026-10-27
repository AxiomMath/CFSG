module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideKFacts
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
import CFSG.Alternating.Multipliers.Main
import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineMult
import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineOrbit
import CFSG.RankThree.PartOne.KF.F128Act

public section

namespace CFSG.AGLEmbedding.SporadicMultD1

theorem exists_not_conj_of_card_dvd_two {X O : Type*} [Group X] [Group O] (E : Subgroup X)
    (hE9 : Nat.card E = 9) (Φ : X →* O) (hO : Nat.card O ∣ 2)
    (hker : ∀ x : X, Φ x = 1 → ∀ e ∈ E, x * e * x⁻¹ = e) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ f ∈ E, f ≠ 1 ∧ ∀ n : X, n * e * n⁻¹ ≠ f := by
  classical
  have : Finite O := Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hO; omega)
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hE1 : 1 < Nat.card E := by omega
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 hE1
  obtain ⟨e₀, he₀⟩ := exists_ne (1 : E)
  by_contra hcon
  push Not at hcon
  have htr := hcon (e₀ : X) e₀.2 (fun h => he₀ (Subtype.ext h))
  choose n hn using fun f : {f : E // f ≠ 1} =>
    htr (f.1 : X) f.1.2 (fun h => f.2 (Subtype.ext h))
  have hinj : Function.Injective fun f : {f : E // f ≠ 1} => Φ (n f) := by
    intro f g hfg
    have h1 : Φ ((n g)⁻¹ * n f) = 1 := by
      simp only at hfg
      rw [map_mul, map_inv, hfg, inv_mul_cancel]
    have h2 := hker _ h1 (e₀ : X) e₀.2
    have h3 : (f.1 : X) = g.1 := by
      rw [← hn f, ← hn g]
      calc n f * (e₀ : X) * (n f)⁻¹
          = n g * (((n g)⁻¹ * n f) * (e₀ : X) * ((n g)⁻¹ * n f)⁻¹) * (n g)⁻¹ := by group
        _ = n g * (e₀ : X) * (n g)⁻¹ := by rw [h2]
    exact Subtype.ext (Subtype.ext h3)
  have h8 : Nat.card {f : E // f ≠ 1} = 8 := by
    have := Fintype.ofFinite E
    have hfc : Fintype.card E = 9 := by rw [← Nat.card_eq_fintype_card]; exact hE9
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hfc, Fintype.card_subtype_eq]
  have := Nat.card_le_card_of_injective _ hinj
  have := Nat.le_of_dvd (by norm_num) hO
  omega

open TauCeti CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.Helpers (quasisimple_central_quotient_nonabelian)

theorem center_nine_cases_of_not_sporadic
    (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hcat : IsCatalogGroup (K ⧸ Subgroup.center K))
    (hspor : ∀ s : SporadicName, IsEmpty (K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic s).Group))
    (h9 : 9 ∣ Nat.card (Subgroup.center K))
    (hc : 9 ≤ Nat.card {z : Subgroup.center K // z ^ 3 = 1}) :
    Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤ 9 ∧
      Nat.card (Outer (K ⧸ Subgroup.center K)) = 8 ∧
      ∃ a b : Outer (K ⧸ Subgroup.center K), a ≠ 1 ∧ b ≠ 1 ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b := by
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2, quasisimple_central_quotient_nonabelian K hq⟩
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hq'.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod r)) _ _
  | alternating n hn =>
    exfalso
    have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
    rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd
    have h9' := h9.trans hdvd
    split_ifs at h9' <;> omega
  | sporadic s => exact ((hspor s).false e).elim
  | lie d => exact CompCenterNine.lie_center_nine hGA hq d e h9 hc

end CFSG.AGLEmbedding.SporadicMultD1

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne (centerQuotientConj centerQuotientConj_mem_innerAut_iff)

theorem kFactCompCenterNine_of_outer
    (hGA : GriessMultipliersAllModels)
    (hOut : ∀ s : TauCeti.SporadicName,
      Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) ∣ 2) : KFactCompCenterNine := by
  intro X _ _ L hcomp hLn hcat E hEL hEc hEel hE9
  have hq : Open.IsQuasisimple L := hcomp.2.2
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  have hN : ∀ x : X, x ∈ Subgroup.normalizer (L : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top x
  let Φ : X →* Outer (L ⧸ Subgroup.center L) :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner (L ⧸ Subgroup.center L))).comp
      ((centerQuotientConj L).comp ((MonoidHom.id X).codRestrict _ hN))
  have hker : ∀ x : X, Φ x = 1 → ∀ e ∈ E, x * e * x⁻¹ = e := by
    intro x hx e he
    have hinn : centerQuotientConj L ⟨x, hN x⟩ ∈
        OuterAutomorphisms.inner (L ⧸ Subgroup.center L) :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨j, hj, z, hz, rfl⟩ := (CFSG.RankThree.PartOne.K1214.mem_sup_centralizer_iff L).mp
      ((centerQuotientConj_mem_innerAut_iff hperf (hN x)).mp hinn)
    have hze : z * e * z⁻¹ = e := by
      rw [← Subgroup.mem_centralizer_iff.mp hz e (hEL he), mul_inv_cancel_right]
    have hje : j * e * j⁻¹ = e := by rw [← hEc e he j hj, mul_inv_cancel_right]
    calc j * z * e * (j * z)⁻¹ = j * (z * e * z⁻¹) * j⁻¹ := by group
      _ = e := by rw [hze, hje]
  by_cases hs : ∃ s : TauCeti.SporadicName,
      Nonempty (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
  ·
    obtain ⟨s, ⟨e⟩⟩ := hs
    have hO : Nat.card (Outer (L ⧸ Subgroup.center L)) ∣ 2 := by
      rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
      exact hOut s
    exact SporadicMultD1.exists_not_conj_of_card_dvd_two E hE9 Φ hO hker
  · have hspor : ∀ s : TauCeti.SporadicName,
        IsEmpty (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic s).Group) :=
      fun s => not_nonempty_iff.1 fun h => hs ⟨s, h⟩
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
      SporadicMultD1.center_nine_cases_of_not_sporadic hGA hq hcat hspor h9 hc
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
    have : Finite (Outer (L ⧸ Subgroup.center L)) :=
      Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
    exact CompCenterNine.exists_not_conj_of_two_involutions E hEn
      (fun a ha b hb => hEc a ha b (hEL hb)) hE9 Φ h8.le hker ha hb ha2 hb2 hab

end CFSG.AGLEmbedding
