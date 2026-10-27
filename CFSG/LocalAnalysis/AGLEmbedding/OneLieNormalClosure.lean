module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_of_le_normalizer_of_isSimpleGroup {Y : Type*} [Group Y] {K S : Subgroup Y}
    [IsSimpleGroup K] (hSK : S ≤ K) (hKS : K ≤ Subgroup.normalizer (S : Set Y))
    (hS : S ≠ ⊥) : S = K := by
  have hN : (S.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).mpr hKS
  rcases hN.eq_bot_or_eq_top with h | h
  · exact absurd ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hSK) hS
  · exact le_antisymm hSK (Subgroup.subgroupOf_eq_top.mp h)

theorem map_mk_ne_bot_of_isPGroup {p : ℕ} (hp : p.Prime) {H Y : Subgroup G} (hYH : Y ≤ H)
    (hYp : IsPGroup p Y) (hY : Y ≠ ⊥) :
    (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≠ ⊥ := by
  intro hbot
  have hYp' : IsPGroup p (Y.subgroupOf H) := hYp.comap_subtype
  have hc := card_map_mk_of_isPGroup hp (primeComplementCore (G := H) p)
    (primeComplementCore_coprime p) hYp'
  rw [hbot, Subgroup.card_bot] at hc
  exact hY ((Subgroup.subgroupOf_eq_bot.mp (Subgroup.eq_bot_of_card_eq _ hc.symm)).eq_bot_of_le
    hYH)

omit [Finite G] in
theorem nclIn_le_of_forall_conj_mem {H X L : Subgroup G}
    (h : ∀ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ L) : nclIn H X ≤ L := by
  rintro _ ⟨y, hy, rfl⟩
  have hcl : Subgroup.normalClosure ((X.subgroupOf H : Subgroup H) : Set H) ≤
      L.subgroupOf H := by
    show Subgroup.closure (Group.conjugatesOfSet _) ≤ _
    rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨b, hb, hbz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hbz
    exact h c c.2 b hb
  exact hcl hy

end General

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1CompCore.map_nclIn_eq (hd : D1CompCore p P M H R Rbar K) {Y : Subgroup G}
    (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) :
    ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K := by
  have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
  have : IsSimpleGroup K := hd.isSimpleGroup.1
  have hYH : Y ≤ H := hYX.trans (d1LiftX_le_H p H R K)
  have hYp : IsPGroup p Y := hd.esc.isPGroup.to_le (hYX.trans (d1LiftX_le p H R K))
  set Kh : Subgroup G :=
    (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype with hKh
  have hKhH : Kh ≤ H := Subgroup.map_subtype_le _
  have hKhsub : Kh.subgroupOf H = K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hHKh : H ≤ Subgroup.normalizer (Kh : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKhH).mp ?_
    rw [hKhsub]
    exact hKn.comap _
  have hYKh : Y ≤ Kh := fun y hy => by
    obtain ⟨x, ⟨-, hxK⟩, rfl⟩ := hYX hy
    exact ⟨x, hxK, rfl⟩
  have hJn : (((nclIn H Y).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal :=
    (nclIn_normal H Y).map _ (QuotientGroup.mk'_surjective _)
  refine eq_of_le_normalizer_of_isSimpleGroup ?_ ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, ← hKhsub]
    exact Subgroup.comap_mono (nclIn_le hYKh hKhH hHKh)
  · rw [Subgroup.normalizer_eq_top]
    exact le_top
  · exact ne_bot_of_le_ne_bot (map_mk_ne_bot_of_isPGroup hd.red.prime hYH hYp hY)
      (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hYH)))

theorem D1OneLieData.map_nclIn_eq (hd : D1OneLieData p P M H R Rbar K) {Y : Subgroup G}
    (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) :
    ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K :=
  hd.toCore.map_nclIn_eq hYX hY

theorem D1CompCore.nclIn_eq (hd : D1CompCore p P M H R Rbar K) {Y : Subgroup G}
    (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) : nclIn H Y = nclIn H (d1LiftX p H R K) := by
  have : Fact p.Prime := ⟨hd.red.prime⟩
  have hXH : d1LiftX p H R K ≤ H := d1LiftX_le_H p H R K
  have hXp : IsPGroup p (d1LiftX p H R K) := hd.esc.isPGroup.to_le (d1LiftX_le p H R K)
  refine le_antisymm (nclIn_le (hYX.trans (le_nclIn hXH)) (nclIn_le_self H _)
    (le_normalizer_nclIn H _)) (nclIn_le ?_ (nclIn_le_self H Y) (le_normalizer_nclIn H Y))
  refine le_of_le_sup_of_coprime_card_of_le hXH (nclIn_le_self H Y) (glbPrimeCore_le p H)
    (nclIn_normal H Y) hXp (glbPrimeCore_coprime p H).symm ?_
  intro x hx
  have hxK : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hXH hx⟩ ∈ K := by
    obtain ⟨x', ⟨-, hx'K⟩, rfl⟩ := hx
    exact hx'K
  rw [← hd.map_nclIn_eq hYX hY] at hxK
  obtain ⟨j, hj, hjx⟩ := hxK
  have hn : (j : G)⁻¹ * x ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (j⁻¹ * ⟨x, hXH hx⟩)).mp
      (by rw [map_mul, map_inv, hjx, inv_mul_cancel])
  have e : x = j * ((j : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hj hn

theorem D1OneLieData.nclIn_eq (hd : D1OneLieData p P M H R Rbar K) {Y : Subgroup G}
    (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) : nclIn H Y = nclIn H (d1LiftX p H R K) :=
  hd.toCore.nclIn_eq hYX hY

theorem D1CompCore.nclIn_nclIn (hd : D1CompCore p P M H R Rbar K) :
    nclIn (nclIn H (d1LiftX p H R K)) (d1LiftX p H R K) = nclIn H (d1LiftX p H R K) := by
  have hp := hd.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup K := hd.isSimpleGroup.1
  have hJK := hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot
  set X := d1LiftX p H R K with hXdef
  set J := nclIn H X with hJdef
  have hXH : X ≤ H := d1LiftX_le_H p H R K
  have hXp : IsPGroup p X := hd.esc.isPGroup.to_le (d1LiftX_le p H R K)
  have hXJ : X ≤ J := le_nclIn hXH
  have hJH : J ≤ H := nclIn_le_self H X
  have hLJ : nclIn J X ≤ J := nclIn_le_self J X
  have hLK : ((nclIn J X).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K :=
    eq_of_le_normalizer_of_isSimpleGroup
      ((Subgroup.map_mono (Subgroup.comap_mono hLJ)).trans hJK.le)
      (hJK.ge.trans (map_le_normalizer_map _ (hLJ.trans hJH) (le_normalizer_nclIn J X)))
      (ne_bot_of_le_ne_bot (map_mk_ne_bot_of_isPGroup hp hXH hXp hd.d1LiftX_ne_bot)
        (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hXJ))))
  have hJLN : J ≤ nclIn J X ⊔ (J ⊓ GLBPrimeCore p H) := by
    intro j hj
    have hjK : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, hJH hj⟩ ∈
        ((nclIn J X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
      rw [hLK, ← hJK]
      exact Subgroup.mem_map_of_mem _ (show (⟨j, hJH hj⟩ : H) ∈ J.subgroupOf H from hj)
    obtain ⟨l, hl, hlj⟩ := hjK
    have hn : (l : G)⁻¹ * j ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p (l⁻¹ * ⟨j, hJH hj⟩)).mp
        (by rw [map_mul, map_inv, hlj, inv_mul_cancel])
    have e : j = l * ((l : G)⁻¹ * j) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hl ⟨J.mul_mem (J.inv_mem (hLJ hl)) hj, hn⟩
  have hcop : (Nat.card (J ⊓ GLBPrimeCore p H : Subgroup G)).Coprime p :=
    ((glbPrimeCore_coprime p H).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)).symm
  have hconj : ∀ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ nclIn J X := by
    intro c hc x hx
    have hXc : X.map (MulAut.conj c).toMonoidHom ≤ J := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hc) y).mp (hXJ hy)
    exact le_of_le_sup_of_coprime_card_of_le hXc hLJ inf_le_left (nclIn_normal J X)
      (hXp.map _) hcop (hXc.trans hJLN) ⟨x, hx, rfl⟩
  exact le_antisymm hLJ (nclIn_le_of_forall_conj_mem hconj)

theorem D1OneLieData.nclIn_nclIn (hd : D1OneLieData p P M H R Rbar K) :
    nclIn (nclIn H (d1LiftX p H R K)) (d1LiftX p H R K) = nclIn H (d1LiftX p H R K) :=
  hd.toCore.nclIn_nclIn

end Config

end CFSG.AGLEmbedding
