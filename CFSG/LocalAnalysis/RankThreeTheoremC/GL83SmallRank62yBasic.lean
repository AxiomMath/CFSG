module

public import CFSG.Open.RankThreeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr628_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hR : IsPGroup p R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

theorem sr628_mem_normalizer_primeCore (q : ℕ) [Fact q.Prime] (D : Subgroup G) {g : G}
    (hg : g ∈ normalizer (D : Set G)) : g ∈ normalizer (rankThreePrimeCore q D : Set G) := by
  obtain ⟨hOD, hDO, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec q D
  have key : ∀ g ∈ normalizer (D : Set G), ∀ y ∈ rankThreePrimeCore q D,
      g * y * g⁻¹ ∈ rankThreePrimeCore q D := by
    intro g hg y hy
    have h1 : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hg
    have h2 : (normalizer (rankThreePrimeCore q D : Set G)).map (MulAut.conj g).toMonoidHom =
        normalizer (((rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G) :=
      Subgroup.map_equiv_normalizer_eq (rankThreePrimeCore q D) (MulAut.conj g)
    have hle : (rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom ≤
        rankThreePrimeCore q D := by
      have hsub : (rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom ≤ D := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp hg y).mp (hOD hy)
      refine le_sSup ⟨hsub, (normal_subgroupOf_iff_le_normalizer hsub).mpr ?_, ?_⟩
      · calc D = D.map (MulAut.conj g).toMonoidHom := h1.symm
          _ ≤ (normalizer (rankThreePrimeCore q D : Set G)).map (MulAut.conj g).toMonoidHom :=
            map_mono hDO
          _ = _ := h2
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hcop
    exact hle ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem sr628_centralizer_le_normalizer_oddCore (p : ℕ) [Fact p.Prime] (x : G) :
    centralizer ({x} : Set G) ≤
      normalizer (rankThreePrimeCore 2 (rankThreePrimeCore p (centralizer ({x} : Set G))) :
        Set G) :=
  fun _ hc => sr628_mem_normalizer_primeCore 2 _
    ((CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p _).2.1 hc)

theorem sr628_isNilpotent_fitting (H : Subgroup G) :
    Group.IsNilpotent (CFSG.fittingSubgroupOf H) := by
  have h : Group.IsNilpotent (CFSG.fittingSubgroup H) := inferInstance
  exact Group.nilpotent_of_mulEquiv
    ((CFSG.fittingSubgroup H).equivMapOfInjective H.subtype H.subtype_injective)

theorem sr628_exists_pGroup {F : Subgroup G} [Group.IsNilpotent F] {q : ℕ}
    [Fact q.Prime] {g : G} (hgF : g ∈ F) (hg : orderOf g = q) :
    ∃ Q : Subgroup G, IsPGroup q Q ∧ Q ≤ F ∧ g ∈ Q ∧
      normalizer (F : Set G) ≤ normalizer (Q : Set G) := by
  have hzp : IsPGroup q (zpowers (⟨g, hgF⟩ : F)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, pow_one]
    exact hg
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hSc : (S : Subgroup F).Characteristic := Sylow.characteristic_of_normal S inferInstance
  exact ⟨(S : Subgroup F).map F.subtype, S.isPGroup'.map F.subtype, Subgroup.map_subtype_le _,
    ⟨⟨g, hgF⟩, hS (mem_zpowers _), rfl⟩,
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _⟩

omit [Finite G] in
theorem sr628_centralizer_le_normalizer_zpowers (z : G) :
    centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
  have h1 : centralizer ({z} : Set G) = centralizer (zpowers z : Set G) := by
    rw [zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [h1]
  exact Subgroup.centralizer_le_normalizer _

end CFSG.LocalAnalysis.RankThreeTheoremC
