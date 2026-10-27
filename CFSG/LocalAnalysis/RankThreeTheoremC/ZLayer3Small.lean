module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Small
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Onan
import CFSG.GH74.KGroups.A6
import CFSG.GH74.KGroups.A7
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Monster.B.TwoA.Fischer.M22Aut
import CFSG.LocalAnalysis.AGLEmbedding.CoverCoreAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open

@[expose] def KFactAlphaSmallAut3Card : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group)) →
    ∀ B : Subgroup (MulAut K), IsPGroup 3 B → Nat.card B ≤ 9

@[expose] def KFactAlphaOnan3Comm : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) →
    AGLEmbedding.KOutTwoGroup K ∧ (∀ T : Sylow 3 K, ∀ t ∈ (T : Subgroup K), t ^ 3 = 1) ∧
      ∀ T : Sylow 3 K, ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K),
        x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K

private theorem smallAut_card_le {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    {n : ℕ} (hn : Nat.card (MulAut (K ⧸ Subgroup.center K)) = n) (h27 : ¬ 3 ^ 3 ∣ n)
    (B : Subgroup (MulAut K)) (hB : IsPGroup 3 B) : Nat.card B ≤ 9 := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  obtain ⟨k, hk, hdvd⟩ := card_dvd_of_isPGroup_mulAut_of_perfect Nat.prime_three hn B hB
  have hk2 : k ≤ 2 := by
    by_contra h
    exact h27 ((pow_dvd_pow 3 (by omega)).trans hdvd)
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem kFactAlphaSmallAut3Card :
    KFactAlphaSmallAut3Card := by
  intro K _ _ hK _ _ _ he B hB
  rcases he with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨e⟩
    exact smallAut_card_le hK (CFSG.GH74.KGroups.A6.card_mulAut e') (by norm_num) B hB
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A7.equiv_of_alt e
    exact smallAut_card_le hK (CFSG.GH74.KGroups.A7.card_mulAut e') (by norm_num) B hB
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    have hcard := CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.1
    refine smallAut_card_le hK (n := 887040) ?_ (by norm_num) B hB
    rw [← hcard]
    exact Nat.card_congr (MulAut.congr (e.trans b.symm)).toEquiv

private theorem mul_comm_of_mem_sylow_of_abelianSylowDatum {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hD : AGLEmbedding.AbelianSylowDatum X p) (S : Sylow p X) {a b : X}
    (ha : a ∈ (S : Subgroup X)) (hb : b ∈ (S : Subgroup X)) : a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, -, -, -, hidx⟩ := hD
  have hP : IsPGroup p D.span := fun u => ⟨1, Subtype.ext (by simpa using D.pow_eq_one_of_mem u.2)⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hP.toSylow hidx) S
  have hS : (S : Subgroup X) = D.span.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, Subgroup.pointwise_smul_def]
    rfl
  rw [hS] at ha hb
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hb
  rw [← map_mul, ← map_mul, D.mul_comm_of_mem hs ht]

private theorem commutator_mem_center_of_abelianSylowDatum {K X : Type} [Group K] [Finite K]
    [Group X] (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    {p : ℕ} (hp : p.Prime) (hD : AGLEmbedding.AbelianSylowDatum X p) (T : Sylow p K) :
    ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Finite.of_surjective π hπ
  intro x hx y hy
  have hcomm := mul_comm_of_mem_sylow_of_abelianSylowDatum hp hD (T.mapSurjective hπ)
    (a := π x) (b := π y) (by rw [Sylow.coe_mapSurjective]; exact Subgroup.mem_map_of_mem π hx)
    (by rw [Sylow.coe_mapSurjective]; exact Subgroup.mem_map_of_mem π hy)
  rw [← hker, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]

private theorem commutator_mem_center_of_equiv {K X : Type} [Group K] [Finite K] [Group X]
    {p : ℕ} (hp : p.Prime) (hD : AGLEmbedding.AbelianSylowDatum X p)
    (e : K ⧸ Subgroup.center K ≃* X) (T : Sylow p K) :
    ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K :=
  commutator_mem_center_of_abelianSylowDatum _
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (ker_coverHom e) hp hD T

theorem kFactAlphaOnan3Comm_of_datum
    (hS : ONanSylowThreeDatum) : KFactAlphaOnan3Comm := by
  intro K _ _ hK hZ hZp hZc he
  obtain ⟨e⟩ := he
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have e' : K ⧸ Subgroup.center K ≃* Blueprint.NativeSporadic.ON := e.trans b.symm
  have h1 := pow_three_eq_one_of_abelianSylowDatum (X := Blueprint.NativeSporadic.ON) hK hZ hZp
    hZc e'
  have h2 := commutator_mem_center_of_equiv (K := K) (X := Blueprint.NativeSporadic.ON)
    Nat.prime_three hS e'
  exact ⟨kOutTwoGroup_of_onan hK e, fun T => h1 hS T, fun T => h2 T⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
