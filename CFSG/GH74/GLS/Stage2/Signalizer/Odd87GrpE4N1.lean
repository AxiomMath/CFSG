module

public import CFSG.GH74.GLS.Stage2.Local.Concl
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpYLift
import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

section Abstract

variable {E : Type*} [Group E] [Finite E]

theorem sl2_perfect_odd_cover_kernel {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) [Group.IsPerfect E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    (p ^ f ≠ 9 → π.ker = ⊥) ∧ (p ^ f = 9 → Nat.card π.ker ≤ 3) := by
  let ρ : E →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).comp π
  have hρsurj : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hπ
  have hρker : ρ.ker = Subgroup.center E := by
    rw [← CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel π hπ hcen]
    ext x
    exact QuotientGroup.eq_one_iff _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.center E)) := inferInstance
  set T : Subgroup E := (P : Subgroup (Subgroup.center E)).map (Subgroup.center E).subtype
    with hT
  have hTc : T ≤ Subgroup.center E := Subgroup.map_subtype_le _
  have : T.Normal := Subgroup.normal_of_le_center hTc
  have hTp : IsPGroup 2 T := P.isPGroup'.map (Subgroup.center E).subtype
  have hTker : T ≤ ρ.ker := hρker ▸ hTc
  let ψ : E ⧸ T →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K := QuotientGroup.lift T ρ hTker
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨j, hj⟩ := hρsurj y
    exact ⟨(j : E ⧸ T), hj⟩
  have hψker : ψ.ker = (Subgroup.center E).map (QuotientGroup.mk' T) := by
    rw [QuotientGroup.ker_lift, hρker]
  have hψcentral : ψ.ker ≤ Subgroup.center (E ⧸ T) := by
    rw [hψker]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective T q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
  have hψodd : Odd (Nat.card ψ.ker) := by
    let ρ' : Subgroup.center E →* E ⧸ T := (QuotientGroup.mk' T).comp (Subgroup.center E).subtype
    have hker' : ρ'.ker = (P : Subgroup (Subgroup.center E)) := by
      ext x
      change QuotientGroup.mk' T x.1 = 1 ↔ x ∈ (P : Subgroup (Subgroup.center E))
      rw [show QuotientGroup.mk' T x.1 = 1 ↔ x.1 ∈ T from QuotientGroup.eq_one_iff _]
      exact Subgroup.mem_map_iff_mem (Subgroup.center E).subtype_injective
    have hrange : ρ'.range = ψ.ker := by
      rw [hψker]
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.1, z.2, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
    have hcard : Nat.card ψ.ker = (P : Subgroup (Subgroup.center E)).index := by
      rw [← hrange, ← hker', Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ').toEquiv).symm
    rw [hcard]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (fun h => P.not_dvd_index (by simpa using h)) |> fun h => by omega)
  have : Group.IsPerfect (E ⧸ T) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
  have hcov := CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel hp2 hK ψ hψsurj hψcentral
    hψodd
  have hmem : ∀ c ∈ π.ker, QuotientGroup.mk' T c ∈ ψ.ker := fun c hc => by
    change ψ (QuotientGroup.mk' T c) = 1
    change ρ c = 1
    rw [show ρ c = QuotientGroup.mk' _ (π c) from rfl, MonoidHom.mem_ker.1 hc, map_one]
  let emb : π.ker →* ψ.ker :=
    ((QuotientGroup.mk' T).comp π.ker.subtype).codRestrict ψ.ker fun c => hmem c c.2
  have hemb : Function.Injective emb := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcT : (c : E) ∈ T := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hc)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hTp) ⟨(c : E), hcT⟩
    have hk' : orderOf (c : E) = 2 ^ k := (Subgroup.orderOf_coe ⟨(c : E), hcT⟩).trans hk
    have hodd' : Odd (orderOf (c : E)) := by
      have h1 : orderOf (c : E) ∣ Nat.card π.ker := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard c
      exact Odd.of_dvd_nat hodd h1
    exact Subtype.ext (CFSG.LieType.Steinberg.eq_one_of_odd_orderOf hodd' hk')
  have hdvd : Nat.card π.ker ∣ Nat.card ψ.ker := Subgroup.card_dvd_of_injective emb hemb
  refine ⟨fun h9 => ?_, fun h9 => ?_⟩
  · have hbot : ψ.ker = ⊥ := hcov.1 h9
    have h1 : Nat.card ψ.ker = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 : Nat.card π.ker = 1 := Nat.eq_one_of_dvd_one (h1 ▸ hdvd)
    exact Subgroup.card_eq_one.1 h2
  · have hle : Nat.card ψ.ker ≤ 3 := (hcov.2 h9).2
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    exact (Nat.le_of_dvd hpos hdvd).trans hle

end Abstract

theorem pPrimeCoreOf_eq_bot_of_sl2 {A : Type} [Group A] [Finite A] {J : Subgroup A} (hJ : IsComponent J)
    (hJn : J.Normal) {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Hat J ≃* IVK.SL2 F) (h9 : Nat.card F = 9 → pCore 3 A = ⊥) : pPrimeCoreOf 2 J = ⊥ := by
  have _ := h3
  classical
  have : J.Normal := hJn
  have : Group.IsPerfect ↥J := hJ.1.1
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hK] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  let ε : Hat J ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  let π : ↥J →* Matrix.SpecialLinearGroup (Fin 2) F :=
    ε.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))
  have hπ : Function.Surjective π := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = pPrimeCore 2 ↥J := by
    ext x
    rw [MonoidHom.mem_ker]
    change ε (QuotientGroup.mk' (pPrimeCore 2 ↥J) x) = 1 ↔ _
    rw [map_eq_one_iff _ ε.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcen : π.ker ≤ center ↥J := hker ▸ pPrimeCore_le_center_comp hJ.1
  have hodd' : Odd (Nat.card π.ker) := by rw [hker]; exact hNodd
  obtain ⟨hne, heq⟩ := sl2_perfect_odd_cover_kernel hp2 hK π hπ hcen hodd'
  by_cases h9' : p ^ (n : ℕ) = 9
  ·
    have hcard3 : Nat.card π.ker ≤ 3 := heq h9'
    have hpos : 0 < Nat.card π.ker := Nat.card_pos
    have hmem : Nat.card π.ker = 1 ∨ Nat.card π.ker = 3 := by
      obtain ⟨m, hm⟩ := hodd'
      omega
    have hpg : IsPGroup 3 (pPrimeCore 2 ↥J) := by
      rcases hmem with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [← hker, h]; rfl)
      · exact IsPGroup.of_card (n := 1) (by rw [← hker, h]; rfl)
    have hn : (pPrimeCoreOf 2 J).Normal := inferInstanceAs ((pPrimeCore 2 ↥J).map J.subtype).Normal
    have hpg' : IsPGroup 3 (pPrimeCoreOf 2 J) := hpg.map J.subtype
    have hle : pPrimeCoreOf 2 J ≤ pCore 3 A := le_sSup ⟨hn, hpg'⟩
    rw [h9 (by rw [hK]; exact h9')] at hle
    exact le_bot_iff.mp hle
  ·
    have hbot : pPrimeCore 2 ↥J = ⊥ := hker ▸ hne h9'
    show (pPrimeCore 2 ↥J).map J.subtype = ⊥
    rw [hbot, Subgroup.map_bot]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
