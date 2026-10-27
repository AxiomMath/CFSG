module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem conj_apply_toMonoidHom (x y : G) :
    (MulAut.conj x : G →* G) y = x * y * x⁻¹ := by
  show MulAut.conj x y = x * y * x⁻¹
  rw [MulAut.conj_apply]

theorem f3_B_char {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ normalizer (s.fr.S : Set G), x ∈ normalizer (s.fr.B : Set G) := by
  intro x hx
  have hC := hH.hLF.fact14.2.2.1
  have hmax : IsMaximalIn s.fr.S s.fr.B := hC.2.2.1
  have hcyc : ¬ IsCyclic ↥(cen s.fr.B) := hC.2.2.2.1
  have huniq : ∀ M : Subgroup G, IsMaximalIn s.fr.S M → ¬ IsCyclic ↥(cen M) → M = s.fr.B :=
    hC.2.2.2.2.1
  have hxS : s.fr.S.map (MulAut.conj x : G →* G) = s.fr.S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hmax' : IsMaximalIn s.fr.S (s.fr.B.map (MulAut.conj x : G →* G)) := by
    have h := (isMaximalIn_map (f := (MulAut.conj x : G →* G)) (MulAut.conj x).injective
      s.fr.S s.fr.B).mpr hmax
    rwa [hxS] at h
  have hcyc' : ¬ IsCyclic ↥(cen (s.fr.B.map (MulAut.conj x : G →* G))) := by
    rw [cen_map (f := (MulAut.conj x : G →* G)) (MulAut.conj x).injective s.fr.B]
    exact (isCyclic_map (f := (MulAut.conj x : G →* G)) (MulAut.conj x).injective
      (cen s.fr.B)).not.mpr hcyc
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ hmax' hcyc')

theorem f3_T1_le_X {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : e.T₁ ≤ s.X := by
  intro x hx
  have hSleT : s.fr.S ≤ e.T₁ := hH.h32.2.1.1
  have hSnorm : (s.fr.S.subgroupOf e.T₁).Normal := hH.h32.2.1.2
  have hxS : x ∈ normalizer (s.fr.S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSleT).mp hSnorm hx
  have hxB : x ∈ normalizer (s.fr.B : Set G) := f3_B_char hH x hxS
  have hBmap : s.fr.B.map (MulAut.conj x : G →* G) = s.fr.B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxB
  have htx : x * s.t * x⁻¹ ∈ s.tCoset (cen s.fr.S) := by
    rw [← hH.hDef.2.2]
    exact ⟨x, hx, rfl⟩
  obtain ⟨c, hc, hceq⟩ := htx
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  have hcZ : c ∈ s.fr.Z := by
    rw [s3_cen_S s hA] at hc
    exact hc
  have hzB : s.fr.z ∈ s.fr.B := by
    have hzcen : s.fr.z ∈ cen s.fr.B := by
      rw [show cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} from
        hH.hLF.fact14.2.2.1.1]
      exact Subgroup.subset_closure (by simp)
    exact (Subgroup.mem_inf.mp hzcen).1
  have hcB : c ∈ s.fr.B := by
    rw [SFrame.Z] at hcZ
    exact Subgroup.zpowers_le.mpr hzB hcZ
  have hxtxP : x * s.t * x⁻¹ ∈ s.fr.B ⊔ zpowers s.t := by
    rw [hceq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcB)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  change x ∈ normalizer ((s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_sup, hBmap, MonoidHom.map_zpowers]
    exact sup_le le_sup_left (Subgroup.zpowers_le.mpr (by
      rw [conj_apply_toMonoidHom]
      exact hxtxP))
  · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj x : G →* G))
      (MulAut.conj x).injective).symm

theorem f3_N_le_X (s : Setting3 G L) : f3N s ≤ s.X := by
  intro n hn
  rw [f3N, normIn] at hn
  obtain ⟨hnH, hnB⟩ := Subgroup.mem_inf.mp hn
  have hBmap : s.fr.B.map (MulAut.conj n : G →* G) = s.fr.B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnB
  have hnt : n * s.t = s.t * n :=
    (Subgroup.mem_centralizer_iff.mp hnH s.t (Set.mem_singleton s.t)).symm
  change n ∈ normalizer ((s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, hBmap, MonoidHom.map_zpowers]
  have hconj : (MulAut.conj n : G →* G) s.t = s.t := by
    rw [conj_apply_toMonoidHom, hnt, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]

theorem f3_X_inf_H {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.X ⊓ s.H = f3N s := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxX, hxH⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ normalizer (s.fr.B : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hPmap : (s.fr.B ⊔ zpowers s.t).map (MulAut.conj x : G →* G) =
          s.fr.B ⊔ zpowers s.t :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hxX
      have hLmap : L.map (MulAut.conj x : G →* G) = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (s3_H_le_N s hH.hS hxH)
      have hPL : (s.fr.B ⊔ zpowers s.t) ⊓ L = s.fr.B := f3_P_inf_L hH
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · intro y hy
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
        have hbP : (MulAut.conj x : G →* G) b ∈ s.fr.B ⊔ zpowers s.t := by
          have hmem : (MulAut.conj x : G →* G) b ∈
              (s.fr.B ⊔ zpowers s.t).map (MulAut.conj x : G →* G) :=
            Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hb)
          rwa [hPmap] at hmem
        have hbL : (MulAut.conj x : G →* G) b ∈ L := by
          have hmem : (MulAut.conj x : G →* G) b ∈ L.map (MulAut.conj x : G →* G) :=
            Subgroup.mem_map_of_mem _ (f3_B_le_L s hb)
          rwa [hLmap] at hmem
        exact hPL ▸ Subgroup.mem_inf.mpr ⟨hbP, hbL⟩
      · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj x : G →* G))
          (MulAut.conj x).injective).symm
    exact Subgroup.mem_inf.mpr ⟨hxH, hxN⟩
  · exact le_inf (f3_N_le_X s) inf_le_left

theorem f3_T_le_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : s.T ≤ f3N s := by
  intro x hx
  rw [← f3_X_inf_H hH]
  exact ⟨f3_T1_le_X hH (e.T_le hx), s.sylow_T.1 hx⟩

theorem f3_tX_sub {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∃ v ∈ cen s.fr.B, x * s.t * x⁻¹ = v * s.t := by
  intro x hx
  have hPmap : (s.fr.B ⊔ zpowers s.t).map (MulAut.conj x : G →* G) = s.fr.B ⊔ zpowers s.t :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hPmap_inv : (s.fr.B ⊔ zpowers s.t).map (MulAut.conj x⁻¹ : G →* G) =
      s.fr.B ⊔ zpowers s.t :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (s.X.inv_mem hx)
  have htP : s.t ∈ s.fr.B ⊔ zpowers s.t := Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t)
  have hxtxP : x * s.t * x⁻¹ ∈ s.fr.B ⊔ zpowers s.t := by
    have hmem : (MulAut.conj x : G →* G) s.t ∈
        (s.fr.B ⊔ zpowers s.t).map (MulAut.conj x : G →* G) :=
      Subgroup.mem_map_of_mem _ htP
    rw [hPmap] at hmem
    rwa [conj_apply_toMonoidHom] at hmem
  have hxtx_notL : x * s.t * x⁻¹ ∉ L := hH.h31.2.2.1 x
  obtain ⟨b, hbB, hbeq⟩ := f3_mem_P_not_L (s := s) hH hxtxP hxtx_notL
  have ht_cent : s.t ∈ Subgroup.centralizer (s.fr.B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => s3_comm_t_of_mem_L s (f3_B_le_L s hy)
  have htt : s.t * s.t = 1 := by
    simpa [s.t_order, pow_two] using pow_orderOf_eq_one s.t
  have ht_centP : s.t ∈ Subgroup.centralizer
      ((s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rcases f3_mem_P p hp with hpB | ⟨b', hb', rfl⟩
    · exact s3_comm_t_of_mem_L s (f3_B_le_L s hpB)
    · have hbt : b' * s.t = s.t * b' := s3_comm_t_of_mem_L s (f3_B_le_L s hb')
      calc (b' * s.t) * s.t = b' * (s.t * s.t) := by rw [mul_assoc]
        _ = b' := by rw [htt, mul_one]
        _ = (s.t * s.t) * b' := by rw [htt, one_mul]
        _ = s.t * (s.t * b') := by rw [mul_assoc]
        _ = s.t * (b' * s.t) := by rw [hbt]
  have hbt_cent : b * s.t ∈ Subgroup.centralizer (s.fr.B : Set G) := by
    rw [← hbeq, Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hb'P : x⁻¹ * b' * x ∈ s.fr.B ⊔ zpowers s.t := by
      have hmem : (MulAut.conj x⁻¹ : G →* G) b' ∈
          (s.fr.B ⊔ zpowers s.t).map (MulAut.conj x⁻¹ : G →* G) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hb')
      rw [hPmap_inv] at hmem
      simpa [conj_apply_toMonoidHom] using hmem
    have htcomm : s.t * (x⁻¹ * b' * x) = (x⁻¹ * b' * x) * s.t :=
      (Subgroup.mem_centralizer_iff.mp ht_centP (x⁻¹ * b' * x) hb'P).symm
    calc b' * (x * s.t * x⁻¹) = x * ((x⁻¹ * b' * x) * s.t) * x⁻¹ := by group
      _ = x * (s.t * (x⁻¹ * b' * x)) * x⁻¹ := by rw [← htcomm]
      _ = (x * s.t * x⁻¹) * b' := by group
  have hb_cent : b ∈ Subgroup.centralizer (s.fr.B : Set G) := by
    have hmul : (b * s.t) * s.t ∈ Subgroup.centralizer (s.fr.B : Set G) :=
      Subgroup.mul_mem _ hbt_cent ht_cent
    simpa only [mul_assoc, htt, mul_one] using hmul
  exact ⟨b, Subgroup.mem_inf.mpr ⟨hbB, hb_cent⟩, hbeq⟩

end CFSG.OddStandard.HigherRank.YamadaG23
