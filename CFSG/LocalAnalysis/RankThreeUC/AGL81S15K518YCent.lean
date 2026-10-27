module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YLayer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X]

theorem toStar_eq_one_iff_mem_gnC {T : Subgroup X} (x : X) : toStar T x = 1 ↔ x ∈ gnC T :=
  QuotientGroup.eq_one_iff x

theorem not_dvd_card_centralizer_of_cover {T T₁ T₂ : Subgroup X} (hc : GNCentre T T₁ T₂)
    (hcov : GNCoverP T T₁ T₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m1 : mS T T₁ p Ls = 1) (m2 : mS T T₂ p Ls = 1) (n1 : mN T₁ p = 1) (n2 : mN T₂ p = 1)
    (hoth : ∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ p ∣ Nat.card ↥Is) (hn : Ls.Normal) :
    ¬ p ∣ Nat.card (Subgroup.centralizer (Ls : Set (X ⧸ gnC T))) := by
  intro hd
  haveI := hn
  haveI hEn : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T))).Normal :=
    CFSG.ComponentClassification.Layer.normal _
  set K : Subgroup (X ⧸ gnC T) := Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) with hK
  set E : Subgroup (X ⧸ gnC T) := CFSG.Open.rankThreeLayer ⊤ with hE
  have hKE : ¬ p ∣ Nat.card ↥(K ⊓ E) :=
    not_dvd_card_centralizer_inf_layer_of_k518Y hc hp hp2 hLs hinv m1 m2 n1 n2 hoth
  have hrel : p ∣ (K ⊓ E).relIndex K := by
    have h := Subgroup.relIndex_mul_card (H := K ⊓ E) (K := K)
    rw [inf_right_comm, inf_idem] at h
    rw [← h] at hd
    exact (hp.dvd_mul.1 hd).resolve_right hKE
  have hCB : gnC T ≤ (K ⊓ E).comap (toStar T) := fun x hx => by
    rw [Subgroup.mem_comap, (toStar_eq_one_iff_mem_gnC x).2 hx]
    exact Subgroup.one_mem _
  have hidx : p ∣ ((K ⊓ E).comap (toStar T)).relIndex (K.comap (toStar T)) := by
    rw [Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    exact hrel
  obtain ⟨x, hxA, hxB, ⟨k, hk⟩, hxT⟩ := hcov p hp hp2 (K.comap (toStar T))
    ((K ⊓ E).comap (toStar T)) (Subgroup.Normal.comap inferInstance _)
    (Subgroup.Normal.comap inferInstance _) hCB (Subgroup.comap_mono inf_le_left)
    (fun y hy => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩) hidx
  have hx1 : toStar T x ≠ 1 := fun h => hxB (hCB ((toStar_eq_one_iff_mem_gnC x).1 h))
  have hxK : toStar T x ∈ K := hxA
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (hk ▸ orderOf_map_dvd (toStar T) x : orderOf (toStar T x) ∣ p ^ k)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hx1 hj
  have hdvd : p ∣ Nat.card (Subgroup.zpowers (toStar T x)) := by
    rw [Nat.card_zpowers, hj]
    exact dvd_pow_self p hj0
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers (toStar T x))) p hdvd
  have hyo : orderOf (y : X ⧸ gnC T) = p := by rw [Subgroup.orderOf_coe, hy]
  have hyK : (y : X ⧸ gnC T) ∈ K := Subgroup.zpowers_le.2 hxK y.2
  have hZ := not_dvd_card_center_of_mS hc hLs hinv hp m1 m2
  rcases hxT with h | h
  · have hxN : toStar T x ∈ gnImg T (Subgroup.normalizer (T₁ : Set X)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.centralizer_le_normalizer _ h)
    have hyN : (y : X ⧸ gnC T) ∈ gnImg T (Subgroup.normalizer (T₁ : Set X)) :=
      Subgroup.zpowers_le.2 hxN y.2
    exact orderOf_ne_of_mem_centralizer hp hp2 hZ (dvd_card_gnA_of_mS hp m1) n1.le hyN hyK hyo
  · have hxN : toStar T x ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) :=
      Subgroup.mem_map_of_mem _ h
    have hyN : (y : X ⧸ gnC T) ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) :=
      Subgroup.zpowers_le.2 hxN y.2
    exact orderOf_ne_of_mem_centralizer hp hp2 hZ (dvd_card_gnA_of_mS hp m2) n2.le hyN hyK hyo

end CFSG.LocalAnalysis.RankThreeUC.S15
