module

public import CFSG.ClassicalInvolution.AschTight.S1911SecF
public import CFSG.ClassicalInvolution.AschTight.S1916F16
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.ClassicalInvolution.AschTight.S1916Data
public import CFSG.ClassicalInvolution.AschTight.Sec71Rel

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem exists_sylow_perfectCore (hd : Sec19Data p f K z S W) (h9 : p ^ f ≠ 9) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ Q : Subgroup G, Q ≤ K ⊓ Subgroup.centralizer ({a} : Set G) ∧ IsPGroup 2 Q ∧
      ¬ IsCyclic Q ∧ 8 ≤ Nat.card Q ∧ 2 * Nat.card Q = Nat.card ↥((S : Subgroup G) ⊓ K) := by
  have hp2 := hd.tight.branch.odd
  obtain ⟨e₀, hf, h5, -, -, hΩ, -, -, -, -⟩ := sectionData_fieldInvolution hd h9 haS ha2 haX
  have he₀ : e₀ ≠ 0 := by
    rintro rfl
    simp at h5
  set C := Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨Q'⟩ : Nonempty (Sylow 2 ↥(perfectCoreIn K a)) := inferInstance
  set Q₀ : Subgroup ↥C := (Q' : Subgroup ↥(perfectCoreIn K a)).map (perfectCoreIn K a).subtype
    with hQ₀
  have hQ₀syl : IsSylow2In Q₀ (perfectCoreIn K a) := isSylow2In_map_sylow _ Q'
  have hLmem : perfectCoreIn K a ∈ conjFamily (perfectCoreIn K a) := ⟨1, conjSub_one _⟩
  have hQ₀card : Nat.card Q₀ = 2 ^ (Nat.card SL(2, GaloisField p e₀)).factorization 2 :=
    hΩ.natCard_isSylow2In hLmem hQ₀syl
  have hQ₀nc : ¬ IsCyclic Q₀ :=
    Sec71.not_isCyclic_of_mem_RSet hp2 hΩ (mem_RSet_of_isSylow2In hLmem hQ₀syl)
  have hQcard : Nat.card (Q₀.map C.subtype) = Nat.card Q₀ :=
    Subgroup.card_map_of_injective C.subtype_injective
  refine ⟨Q₀.map C.subtype, ?_, hQ₀syl.2.1.map C.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact perfectResidualOf_le _ (Subgroup.mem_subgroupOf.mp (hQ₀syl.1 hy))
  · intro hc
    apply hQ₀nc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Q₀ C.subtype C.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  · rw [hQcard, hQ₀card]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (three_le_factorization_two_card_sl2 hp2 he₀)
  · rw [(hypOmegaMod_of_tightD hd.tight).natCard_isSylow2In (CoreAssembly.mem_conjClass_self K)
      (S1911.isSylow2In_inf hd), hQcard, hQ₀card, hf, factorization_two_card_sl2_two_mul hp2 he₀,
      pow_succ]
    ring

theorem exists_good_involution (hd : Sec19Data p f K z S W) (h9 : p ^ f ≠ 9) {a₀ : G}
    (haS : a₀ ∈ (S : Subgroup G)) (ha2 : a₀ * a₀ = 1)
    (haX : a₀ ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ a ∈ (S : Subgroup G), a * a = 1 ∧ a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K ∧
      ∃ Q : Subgroup G, Q ≤ (S : Subgroup G) ⊓ K ∧ Q ≤ Subgroup.centralizer ({a} : Set G) ∧
        ¬ IsCyclic Q ∧ 8 ≤ Nat.card Q ∧ 2 * Nat.card Q = Nat.card ↥((S : Subgroup G) ⊓ K) := by
  obtain ⟨Q, hQKa, hQ2, hQnc, hQ8, hQcard⟩ := exists_sylow_perfectCore hd h9 haS ha2 haX
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (S1916.mul_comm_of_isUniqueInvolution hI hx)
  have haN : a₀ ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hQKa hy).2)
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers a₀ ⊔ Q) :=
    IsPGroup.to_sup_of_normal_right' (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS)) hQ2
      (Subgroup.zpowers_le.mpr haN)
  have hPC : Subgroup.zpowers a₀ ⊔ Q ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (hd.hSz haS)) ((hQKa.trans inf_le_left).trans hKz)
  obtain ⟨c, hcC, hcP⟩ := exists_conj_le_of_sylow_le S hd.hSz hPC hP2
  have hcK : conjSub c K = K := by
    refine mem_normalizer_iff_conjSub_eq.mp ?_
    rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
    exact hcC
  have hQS : conjSub c Q ≤ (S : Subgroup G) := (conjSub_mono le_sup_right).trans hcP
  have hcQ : Nat.card ↥(conjSub c Q) = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  refine ⟨c * a₀ * c⁻¹, hcP (conj_mem_conjSub (Subgroup.mem_sup_left (Subgroup.mem_zpowers a₀))),
    ?_, ?_, conjSub c Q, le_inf hQS (hcK ▸ conjSub_mono (hQKa.trans inf_le_left)), ?_, ?_,
    hcQ ▸ hQ8, hcQ ▸ hQcard⟩
  · calc c * a₀ * c⁻¹ * (c * a₀ * c⁻¹) = c * (a₀ * a₀) * c⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  · intro h
    apply haX
    have hN := S1916.mem_normalizer_sup_cStar hd (Subgroup.inv_mem _ hcC)
    have h' := (Subgroup.mem_normalizer_iff.mp hN _).mp h
    convert h' using 1
    group
  · rw [← S1916.conjSub_centralizer]
    exact conjSub_mono (hQKa.trans inf_le_right)
  · intro hc
    have : IsCyclic ↥(Q.map (MulAut.conj c).toMonoidHom) := hc
    apply hQnc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Q (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm.toMonoidHom (MulEquiv.surjective _)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
