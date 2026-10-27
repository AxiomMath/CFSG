module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S14612DC
public import CFSG.Quasithin.EmptyFaithful.S146zMSol

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Elem

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_exists_elemAbelian_image_F4 (h12 : Stage14612PartP_F4) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) :
    ∃ E : Subgroup (OTwoQuot (mcOf T)), E ≤ imageOTwoQuot (mcOf T) (oTwoUpper H) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  obtain ⟨-, H₀, H₁, H₂, t, hdecP⟩ := h12 G T M S H PQ p hred hmax
  have : Fact p.Prime := ⟨hred.prime⟩
  obtain ⟨E, hEH, hEK, hEel, hEcard⟩ := hdecP.exists_elemAbelian_sq hred.prime hred.odd
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  obtain ⟨hE', hE'card⟩ := zm_isElemAbelian_subgroupOf (hEH.trans hHG) hEel
  have hRp : IsPGroup 2 (CFSG.Open.pCore 2 ↥(mcOf T)) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨hEb, hEbcard⟩ := isElemAbelian_map_quotient (CFSG.Open.pCore 2 ↥(mcOf T)) hRp
    hred.odd hE'
  exact ⟨(E.subgroupOf (mcOf T)).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(mcOf T))),
    Subgroup.map_mono (Subgroup.comap_mono hEK), hEb, by rw [hEbcard, hE'card, hEcard]⟩

end Elem

end CFSG.Quasithin
