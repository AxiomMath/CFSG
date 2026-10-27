module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceBlocks
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaEightMinusAut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaEightMinusOrderNine
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel

public section

namespace CFSG.AGLEmbedding

namespace OmegaEightMinusElemRank

theorem exists_conj_le {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → Nat.card Q ∣ p ^ k) {E : Subgroup G}
    (hE : IsPGroup p E) (hcard : Nat.card E = p ^ k) {A : Subgroup G} (hA : IsPGroup p A) :
    ∃ c : G, ∀ a ∈ A, c⁻¹ * a * c ∈ E := by
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  have hSle : Nat.card (S : Subgroup G) ≤ Nat.card E := by
    rw [hcard]
    exact Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos k) (hmax S S.2)
  have hES' : E = S := Subgroup.eq_of_le_of_card_ge hES hSle
  obtain ⟨T, hAT⟩ := hA.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S T
  refine ⟨c, fun a ha => ?_⟩
  have haT : a ∈ (T : Subgroup G) := hAT ha
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haT
  rw [hES']
  have h1 : (MulAut.conj c)⁻¹ • a = c⁻¹ * a * c := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rwa [h1] at haT

theorem exists_pow_nine_of_omegaMinus {L : Type} [Group L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOmegaMinusTwoIndex 4 d) (he : Nonempty (L ≃* CatGroup d)) :
    ∃ g : L, g ^ 9 = 1 ∧ g ^ 3 ∉ Subgroup.center L := by
  obtain ⟨e⟩ := he
  rcases d with ⟨i, hi⟩
  obtain ⟨q, hqp, hqe, hiq⟩ := hd
  simp only at hiq
  subst hiq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hi hqp e
  rw [hqp, hqe] at hmodel
  obtain ⟨K, _, _, _, hK, -, ⟨e'⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.exists_mulEquiv_of_lieModel
      (Or.inl ⟨by decide, hmodel⟩ : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1)
  obtain ⟨g, hg9, hg3⟩ := exists_pow_nine hK
  refine ⟨e'.symm g, by rw [← map_pow, hg9, map_one], fun hc => hg3 ?_⟩
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro h
  have := congrArg e' (hc (e'.symm h))
  simpa [map_pow] using this

end OmegaEightMinusElemRank

theorem omegaEightMinusAutNoE81 : OmegaEightMinusAutNoE81 := by
  intro L _ _ d hd he E hE h81
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut L) := MulEquiv.finite_left
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨g, hg9, hg3⟩ := OmegaEightMinusElemRank.exists_pow_nine_of_omegaMinus hd he
  have ha : IsPGroup 3 (Subgroup.zpowers (MulAut.conj g)) := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hn, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, ← map_pow]
    norm_num [hg9]
  obtain ⟨c, hc⟩ := OmegaEightMinusElemRank.exists_conj_le
    (kFactOmegaEightMinusAut L d hd he) hEp (by rw [h81]) ha
  have h1 := hE.2 _ (hc (MulAut.conj g) (Subgroup.mem_zpowers _))
  have h2 : (MulAut.conj g) ^ 3 = 1 := by
    have h3 : (c⁻¹ * MulAut.conj g * c) ^ 3 = c⁻¹ * (MulAut.conj g) ^ 3 * c := by
      simpa using conj_pow (a := c⁻¹) (b := MulAut.conj g) (i := 3)
    rw [h3] at h1
    calc (MulAut.conj g) ^ 3 = c * (c⁻¹ * (MulAut.conj g) ^ 3 * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  apply hg3
  rw [Subgroup.mem_center_iff]
  intro h
  have h4 := DFunLike.congr_fun h2 h
  rw [← map_pow, MulAut.conj_apply] at h4
  exact (mul_inv_eq_iff_eq_mul.1 h4).symm

theorem kFactOmegaEightMinusAutElemRank : KFactOmegaEightMinusAutElemRank :=
  kFactOmegaEightMinusAutElemRank_of_noE81 omegaEightMinusAutNoE81

end CFSG.AGLEmbedding
