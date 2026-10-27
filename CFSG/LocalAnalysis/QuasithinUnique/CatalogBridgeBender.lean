module

public import CFSG.Assembly.InCatalog
public import CFSG.Open.Catalog
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.StronglyEmbedded.Catalog.Unitary
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.QuasithinUnique

open TauCeti

private theorem not_isMulCommutative_of_mulEquiv_aux {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative H := by
  rintro ⟨hc⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (e.injective (by rw [map_mul, map_mul]; exact hc.comm _ _))

theorem inCatalog_of_mulEquiv_sz {X : Type} [Group X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* CFSG.Open.Sz a) : CFSG.Assembly.InCatalog X := by
  have hv : (LieTypeIndex.suzuki a).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simpa using ha
  have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a := CFSG.Models.benderSzModel_eq_sz a
  exact ⟨.lie ⟨_, hv⟩,
    ⟨(e.trans (MulEquiv.subgroupCongr (hmodel.symm.trans
      (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a)))).trans
      (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩

theorem inCatalog_of_mulEquiv_psu3 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) {f : ℕ} (hf : 2 ≤ f) (e : X ≃* CFSG.Open.PSU3 2 f) :
    CFSG.Assembly.InCatalog X := by
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
      CFSG.Models.benderPSU3Model_eq_psu3 f
  let e' : X ≃* CFSG.Theory.Comparator.PSU3Model f := e.trans (MulEquiv.subgroupCongr hmodel.symm)
  have := e'.symm.isSimpleGroup
  have hP := not_isMulCommutative_of_mulEquiv_aux e' hnonab
  have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hv : (LieTypeIndex.twistedA 2 ⟨2, f, Nat.prime_two, by omega⟩).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [PrimePower.card_def]
    generalize 2 ^ f = N at *
    simp
    omega
  exact ⟨.lie ⟨_, hv⟩,
    ⟨e'.trans (CFSG.BenderSuzuki.Catalog.groupEquivPSU3Model (by omega) hv hP).symm⟩⟩

end CFSG.QuasithinUnique
