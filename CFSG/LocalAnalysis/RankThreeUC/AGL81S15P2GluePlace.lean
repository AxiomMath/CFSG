module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K5192P2PB
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueKernel
import CFSG.Quasithin.Background.A4V
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
import CFSG.Quasithin.Background.Equivariance
import CFSG.Quasithin.EmptyFaithful.S1412

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.AGLEmbedding
  KFactsPair CFSG.Open

open scoped Pointwise

private theorem tStar_sylow_inf_oddHull_of_isC118Pair {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hc : IsC118Pair T T₁ T₂) {P : Subgroup (X ⧸ gnC T)}
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T))) :
    (gnImg T T ≤ gnImg T (Subgroup.normalizer (T₁ : Set X))) ∧
      (gnImg T T ≤ gnImg T (Subgroup.normalizer (T₂ : Set X))) ∧
      (gnImg T T ≤ Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T))) ∧
      CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ oddHull P) (oddHull P) := by
  have hT₁cen : T₁ ≤ Subgroup.centralizer (T : Set X) :=
    hc.2.1.trans ((CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf T).trans
      (CFSG.Quasithin.A4.centerOf_le_centralizer T))
  have hT₁N : T ≤ Subgroup.normalizer (T₁ : Set X) := by
    have hsub : T ≤ Subgroup.centralizer (T₁ : Set X) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro t₁ ht₁
      exact (Subgroup.mem_centralizer_iff.mp (hT₁cen ht₁) t ht).symm
    exact hsub.trans (Subgroup.centralizer_le_normalizer (T₁ : Set X))
  have hT₂N : T ≤ Subgroup.normalizer (T₂ : Set X) :=
    (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_baum T)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_of_characteristic_subgroupOf
        hc.2.2.2.2.1 hc.2.2.2.2.2.1)
  have hSA : gnImg T T ≤ gnImg T (Subgroup.normalizer (T₁ : Set X)) := by
    simpa [gnImg] using Subgroup.map_mono (f := QuotientGroup.mk' (gnC T)) hT₁N
  have hSB : gnImg T T ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
    simpa [gnImg] using Subgroup.map_mono (f := QuotientGroup.mk' (gnC T)) hT₂N
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T) ⊤ := by
    simpa [gnImg] using
      isSylowTwoOf_map_top_of_surjective hT (QuotientGroup.mk'_surjective (gnC T))
  have hSK : gnImg T T ≤ Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T)) :=
    hTP.trans (normalizer_le_normalizer_oddHull P)
  have hSylSup : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T) (oddHull P ⊔ gnImg T T) :=
    CFSG.Quasithin.A4.isSylowTwoOf_mono hS le_sup_right le_top
  have hKNormal : oddHull P ⊔ gnImg T T ≤
      Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T)) :=
    sup_le Subgroup.le_normalizer hSK
  have hSylK : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ oddHull P) (oddHull P) :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hSylSup le_sup_left hKNormal
  exact ⟨hSA, hSB, hSK, hSylK⟩

private theorem exists_mul_inf_of_forall_mul {X : Type} [Group X] {T T₁ T₂ : Subgroup X}
    {P : Subgroup (X ⧸ gnC T)}
    (hSA : gnImg T T ≤ gnImg T (Subgroup.normalizer (T₁ : Set X)))
    (hSB : gnImg T T ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)))
    (hSK : gnImg T T ≤ Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T)))
    (hmul : ∀ x ∈ (oddHull P ⊔ gnImg T T).comap (toStar T),
      ∃ a ∈ Subgroup.centralizer (T₁ : Set X) ⊓ (oddHull P ⊔ gnImg T T).comap (toStar T),
        ∃ b ∈ Subgroup.normalizer (T₂ : Set X) ⊓ (oddHull P ⊔ gnImg T T).comap (toStar T),
          x = a * b) :
    ∀ k ∈ oddHull P,
      ∃ a ∈ gnImg T (Subgroup.normalizer (T₁ : Set X)) ⊓ oddHull P,
        ∃ b ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) ⊓ oddHull P, k = a * b := by
  have hset : ((oddHull P ⊔ gnImg T T : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) =
      (oddHull P : Set (X ⧸ gnC T)) * (gnImg T T : Set (X ⧸ gnC T)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (oddHull P) (gnImg T T) hSK
  intro k hk
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (gnC T) k
  have hxM : x ∈ (oddHull P ⊔ gnImg T T).comap (toStar T) := by
    rw [Subgroup.mem_comap]
    rw [show toStar T x = k from hx]
    exact Subgroup.mem_sup_left hk
  obtain ⟨a, ha, b, hb, hab⟩ := hmul x hxM
  have hpaM : QuotientGroup.mk' (gnC T) a ∈ oddHull P ⊔ gnImg T T :=
    Subgroup.mem_comap.mp ha.2
  have hpaMul : QuotientGroup.mk' (gnC T) a ∈
      (oddHull P : Set (X ⧸ gnC T)) * (gnImg T T : Set (X ⧸ gnC T)) := by
    rw [← hset]
    exact hpaM
  rw [Set.mem_mul] at hpaMul
  obtain ⟨k₁, hk₁K, t₁, ht₁S, hk₁t₁⟩ := hpaMul
  have hpa_eq : QuotientGroup.mk' (gnC T) a = k₁ * t₁ := hk₁t₁.symm
  have ht₁A : t₁ ∈ gnImg T (Subgroup.normalizer (T₁ : Set X)) := hSA ht₁S
  have hpaA : QuotientGroup.mk' (gnC T) a ∈ gnImg T (Subgroup.normalizer (T₁ : Set X)) :=
    Subgroup.mem_map.mpr ⟨a, Subgroup.centralizer_le_normalizer (T₁ : Set X) ha.1, rfl⟩
  have hk₁A : k₁ ∈ gnImg T (Subgroup.normalizer (T₁ : Set X)) := by
    have hk₁eq : k₁ = QuotientGroup.mk' (gnC T) a * t₁⁻¹ := by
      rw [hpa_eq]; group
    rw [hk₁eq]
    exact (gnImg T (Subgroup.normalizer (T₁ : Set X))).mul_mem hpaA
      ((gnImg T (Subgroup.normalizer (T₁ : Set X))).inv_mem ht₁A)
  have ht₁B : t₁ ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) := hSB ht₁S
  have hpbB : QuotientGroup.mk' (gnC T) b ∈
      gnImg T (Subgroup.normalizer (T₂ : Set X)) :=
    Subgroup.mem_map.mpr ⟨b, hb.1, rfl⟩
  have hxmul : k = QuotientGroup.mk' (gnC T) a * QuotientGroup.mk' (gnC T) b := by
    rw [← hx, hab, map_mul]
  have hpbK : t₁ * QuotientGroup.mk' (gnC T) b ∈ oddHull P := by
    have hEq : t₁ * QuotientGroup.mk' (gnC T) b = k₁⁻¹ * k := by
      rw [hxmul, hpa_eq]
      group
    rw [hEq]
    exact (oddHull P).mul_mem ((oddHull P).inv_mem hk₁K) hk
  exact ⟨k₁, ⟨hk₁A, hk₁K⟩, t₁ * QuotientGroup.mk' (gnC T) b,
    ⟨(gnImg T (Subgroup.normalizer (T₂ : Set X))).mul_mem ht₁B hpbB, hpbK⟩,
    by rw [hxmul, hpa_eq, mul_assoc]⟩

theorem oddHull_le_gnA_of_forall_mul {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hc : IsC118Pair T T₁ T₂)
    {Ls P : Subgroup (X ⧸ gnC T)} (hPL : P ≤ Ls) (hP : IsTwoFourSFive P)
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)))
    (hmul : ∀ x ∈ (oddHull P ⊔ gnImg T T).comap (toStar T),
      ∃ a ∈ Subgroup.centralizer (T₁ : Set X) ⊓ (oddHull P ⊔ gnImg T T).comap (toStar T),
        ∃ b ∈ Subgroup.normalizer (T₂ : Set X) ⊓ (oddHull P ⊔ gnImg T T).comap (toStar T),
          x = a * b) :
    oddHull P ≤ gnA T T₁ Ls ∨ oddHull P ≤ gnA T T₂ Ls := by
  obtain ⟨hSA, hSB, hSK, hSylK⟩ := tStar_sylow_inf_oddHull_of_isC118Pair hT hc hTP
  have hmulK := exists_mul_inf_of_forall_mul hSA hSB hSK hmul
  have hKP : oddHull P ≤ P := (Subgroup.closure_le P).2 fun x hx => hx.1
  rcases oddHull_eq_or_eq_of_mul_of_isTwoFourSFive hP
      (H₁ := gnImg T (Subgroup.normalizer (T₁ : Set X)) ⊓ oddHull P)
      (H₂ := gnImg T (Subgroup.normalizer (T₂ : Set X)) ⊓ oddHull P)
      (S₁ := gnImg T T ⊓ oddHull P) (S₂ := gnImg T T ⊓ oddHull P)
      inf_le_right inf_le_right hSylK hSylK
      (le_inf (inf_le_left.trans hSA) inf_le_right)
      (le_inf (inf_le_left.trans hSB) inf_le_right) hmulK with hA | hB
  · refine Or.inl ?_
    have hKA : oddHull P ≤ gnImg T (Subgroup.normalizer (T₁ : Set X)) := by
      have hAK : gnImg T (Subgroup.normalizer (T₁ : Set X)) ⊓ oddHull P = oddHull P := hA
      exact hAK ▸ inf_le_left
    simpa [gnA] using le_inf hKA (hKP.trans hPL)
  · refine Or.inr ?_
    have hKB : oddHull P ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
      have hBK : gnImg T (Subgroup.normalizer (T₂ : Set X)) ⊓ oddHull P = oddHull P := hB
      exact hBK ▸ inf_le_left
    simpa [gnA] using le_inf hKB (hKP.trans hPL)

end CFSG.LocalAnalysis.RankThreeUC.S15
