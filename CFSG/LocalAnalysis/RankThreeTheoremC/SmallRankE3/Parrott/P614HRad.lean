module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HKbar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H S K : Subgroup G} {x z : G}

abbrev bar (K A : Subgroup G) : Subgroup (Kbar K) :=
  (A.subgroupOf K).map (kbarMk K)

theorem comap_bar (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) {A : Subgroup G}
    (hOA : pCoreOf 2 H ≤ A) : (bar K A).comap (kbarMk K) = A.subgroupOf K := by
  rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left]
  intro k hk
  rw [mem_subgroupOf]
  exact hOA ((mem_pPrimeCore_iff hyp h618 k).1 hk)

theorem mk_mem_bar_iff (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) {A : Subgroup G}
    (hOA : pCoreOf 2 H ≤ A) (k : K) : kbarMk K k ∈ bar K A ↔ (k : G) ∈ A := by
  rw [← mem_comap, comap_bar hyp h618 hOA, mem_subgroupOf]

theorem sup_le_normalizer_pCoreOf (h618 : Stage618 M H K z) :
    K ⊔ pCoreOf 2 H ≤ normalizer (pCoreOf 2 H : Set G) :=
  sup_le (h618.comp.le.trans (le_normalizer_pCoreOf 2 H)) le_normalizer

theorem exists_mul_of_mem_sup (h618 : Stage618 M H K z) {y : G} (hy : y ∈ K ⊔ pCoreOf 2 H) :
    ∃ k ∈ K, ∃ o ∈ pCoreOf 2 H, y = k * o := by
  have h : y ∈ ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hy
  rw [coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H)
    (h618.comp.le.trans (le_normalizer_pCoreOf 2 H))] at h
  obtain ⟨k, hk, o, ho, rfl⟩ := h
  exact ⟨k, hk, o, ho, rfl⟩

theorem pCoreOf_le_kRad (hyp : Hyp P M x z H S) : pCoreOf 2 H ≤ kRad H S K :=
  le_inf hyp.optimal.core_le le_sup_right

theorem kRad_le_sup : kRad H S K ≤ K ⊔ pCoreOf 2 H :=
  inf_le_right

theorem pCoreOf_le_kPar (hyp : Hyp P M x z H S) : pCoreOf 2 H ≤ kPar H S K :=
  le_inf le_sup_right ((pCoreOf_le_kRad hyp).trans le_normalizer)

theorem kPar_le_sup : kPar H S K ≤ K ⊔ pCoreOf 2 H :=
  inf_le_left

theorem conj_mem_kRad (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) {g : K}
    (hg : kbarMk K g ∈ normalizer (bar K (kRad H S K) : Set (Kbar K))) {s : G}
    (hs : s ∈ kRad H S K) : (g : G) * s * (g : G)⁻¹ ∈ kRad H S K := by
  have hO := pCoreOf_le_kRad (K := K) hyp
  obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup h618 (kRad_le_sup hs)
  have hkR : k ∈ kRad H S K := by
    have h := mul_mem hs (inv_mem (hO ho))
    rwa [mul_inv_cancel_right] at h
  have hgo : (g : G) * o * (g : G)⁻¹ ∈ pCoreOf 2 H :=
    (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (h618.comp.le g.2)) o).mp ho
  have hgk : (g : G) * k * (g : G)⁻¹ ∈ K := mul_mem (mul_mem g.2 hk) (inv_mem g.2)
  have hbar : kbarMk K ⟨(g : G) * k * (g : G)⁻¹, hgk⟩ ∈ bar K (kRad H S K) := by
    have h1 : (⟨(g : G) * k * (g : G)⁻¹, hgk⟩ : K) = g * ⟨k, hk⟩ * g⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hg _).mp ((mk_mem_bar_iff hyp h618 hO ⟨k, hk⟩).2 hkR)
  have h2 := (mk_mem_bar_iff hyp h618 hO _).1 hbar
  have h3 : (g : G) * (k * o) * (g : G)⁻¹ =
      ((g : G) * k * (g : G)⁻¹) * ((g : G) * o * (g : G)⁻¹) := by group
  rw [h3]
  exact mul_mem h2 (hO hgo)

theorem mk_mem_normalizer_bar_kRad_iff (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (k : K) : kbarMk K k ∈ normalizer (bar K (kRad H S K) : Set (Kbar K)) ↔
      (k : G) ∈ kPar H S K := by
  have hO := pCoreOf_le_kRad (K := K) hyp
  constructor
  · intro hk
    refine mem_inf.mpr ⟨mem_sup_left k.2, ?_⟩
    rw [mem_normalizer_iff]
    intro s
    refine ⟨fun hs => conj_mem_kRad hyp h618 hk hs, fun hs => ?_⟩
    have hk' : kbarMk K k⁻¹ ∈ normalizer (bar K (kRad H S K) : Set (Kbar K)) := by
      rw [map_inv]
      exact inv_mem hk
    have h := conj_mem_kRad hyp h618 hk' hs
    simpa [mul_assoc] using h
  · intro hk
    have hkN : (k : G) ∈ normalizer (kRad H S K : Set G) := hk.2
    rw [mem_normalizer_iff]
    intro a
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ a
    have h1 : kbarMk K k * QuotientGroup.mk' _ r * (kbarMk K k)⁻¹ =
        kbarMk K (k * r * k⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    change kbarMk K r ∈ _ ↔ _
    rw [mk_mem_bar_iff hyp h618 hO, mk_mem_bar_iff hyp h618 hO]
    exact mem_normalizer_iff.mp hkN r

theorem normalizer_bar_kRad (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    normalizer (bar K (kRad H S K) : Set (Kbar K)) = bar K (kPar H S K) := by
  ext a
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ a
  change kbarMk K k ∈ _ ↔ kbarMk K k ∈ _
  rw [mk_mem_bar_iff hyp h618 (pCoreOf_le_kPar hyp), mk_mem_normalizer_bar_kRad_iff hyp h618]

theorem isPGroup_bar_kRad (hyp : Hyp P M x z H S) : IsPGroup 2 (bar K (kRad H S K)) := by
  have hS : IsPGroup 2 S := hyp.optimal.maxInv.1.2.1
  exact ((hS.to_le inf_le_left).comap_subtype).map _

theorem bar_kRad_ne_bot (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (hL : LieCase M H S K x z) : bar K (kRad H S K) ≠ ⊥ := by
  obtain ⟨s, hs, hsO⟩ := SetLike.exists_of_lt hL.rad_gt
  obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup h618 (kRad_le_sup hs)
  have hO := pCoreOf_le_kRad (K := K) hyp
  have hkR : k ∈ kRad H S K := by
    have h := mul_mem hs (inv_mem (hO ho))
    rwa [mul_inv_cancel_right] at h
  intro hbot
  have h1 : kbarMk K ⟨k, hk⟩ ∈ bar K (kRad H S K) := (mk_mem_bar_iff hyp h618 hO _).2 hkR
  rw [hbot, mem_bot, kbarMk_eq_one_iff hyp h618] at h1
  exact hsO (mul_mem h1 ho)

theorem relIndex_eq_relIndex_sup (h618 : Stage618 M H K z) {A : Subgroup G}
    (hOA : pCoreOf 2 H ≤ A) : A.relIndex K = A.relIndex (K ⊔ pCoreOf 2 H) := by
  have hKH : K ≤ H := h618.comp.le
  have hOH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  haveI hN : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOH).2 (le_normalizer_pCoreOf 2 H)
  let f : H →* H ⧸ (pCoreOf 2 H).subgroupOf H := QuotientGroup.mk' _
  have hA : ((A.subgroupOf H).map f).comap f = A.subgroupOf H := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left]
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact hOA hy
  have hNf : ((pCoreOf 2 H).subgroupOf H).map f = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_bot]
    exact (QuotientGroup.eq_one_iff y).mpr hy
  have e1 : (A.subgroupOf H).relIndex (K.subgroupOf H) =
      ((A.subgroupOf H).map f).relIndex ((K.subgroupOf H).map f) := by
    have h := relIndex_comap ((A.subgroupOf H).map f) f (K.subgroupOf H)
    rwa [hA] at h
  have e2 : (A.subgroupOf H).relIndex (K.subgroupOf H ⊔ (pCoreOf 2 H).subgroupOf H) =
      ((A.subgroupOf H).map f).relIndex ((K.subgroupOf H).map f) := by
    have h := relIndex_comap ((A.subgroupOf H).map f) f
      (K.subgroupOf H ⊔ (pCoreOf 2 H).subgroupOf H)
    rwa [hA, Subgroup.map_sup, hNf, sup_bot_eq] at h
  rw [← relIndex_subgroupOf hKH, ← relIndex_subgroupOf (sup_le hKH hOH),
    subgroupOf_sup hKH hOH, e1, e2]

theorem index_bar_kRad (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    (bar K (kRad H S K)).index = (kRad H S K).relIndex (K ⊔ pCoreOf 2 H) := by
  have hO := pCoreOf_le_kRad (K := K) hyp
  rw [← index_comap_of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 K)),
    comap_bar hyp h618 hO, ← relIndex_eq_relIndex_sup h618 hO]
  rfl

theorem le_pCoreOf_normalizer {T : Type*} [Group T] {R : Subgroup T} (hR : IsPGroup 2 R) :
    R ≤ pCoreOf 2 (normalizer (R : Set T)) := by
  have hn : (R.subgroupOf (normalizer (R : Set T))).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_normalizer).2 le_rfl
  have hle : R.subgroupOf (normalizer (R : Set T)) ≤ CFSG.pCore 2 (normalizer (R : Set T)) :=
    le_sSup (s := {N : Subgroup (normalizer (R : Set T)) | N.Normal ∧ IsPGroup 2 N})
      ⟨hn, hR.comap_subtype⟩
  intro r hr
  exact ⟨⟨r, le_normalizer hr⟩, hle hr, rfl⟩

theorem mem_normalizer_map_comap {Q : Subgroup (Kbar K)} {k : K}
    (hk : kbarMk K k ∈ normalizer (Q : Set (Kbar K))) :
    (k : G) ∈ normalizer ((Q.comap (kbarMk K)).map K.subtype : Set G) := by
  have key : ∀ g : K, kbarMk K g ∈ normalizer (Q : Set (Kbar K)) →
      ∀ w ∈ (Q.comap (kbarMk K)).map K.subtype,
        (g : G) * w * (g : G)⁻¹ ∈ (Q.comap (kbarMk K)).map K.subtype := by
    intro g hg w hw
    obtain ⟨w, hwQ, rfl⟩ := hw
    refine ⟨g * w * g⁻¹, ?_, rfl⟩
    show kbarMk K (g * w * g⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hg _).mp hwQ
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key k hk w, fun hw => ?_⟩
  have hk' : kbarMk K k⁻¹ ∈ normalizer (Q : Set (Kbar K)) := by
    rw [map_inv]
    exact inv_mem hk
  have h := key k⁻¹ hk' _ hw
  simpa [mul_assoc] using h

theorem pCoreOf_normalizer_bar_kRad (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (hL : LieCase M H S K x z) :
    pCoreOf 2 (normalizer (bar K (kRad H S K) : Set (Kbar K))) = bar K (kRad H S K) := by
  refine le_antisymm ?_ (le_pCoreOf_normalizer (isPGroup_bar_kRad hyp))
  have hQN := pCoreOf_le 2 (normalizer (bar K (kRad H S K) : Set (Kbar K)))
  have hQ2 := isPGroup_pCoreOf 2 (normalizer (bar K (kRad H S K) : Set (Kbar K)))
  have hNQ := le_normalizer_pCoreOf 2 (normalizer (bar K (kRad H S K) : Set (Kbar K)))
  set Q := pCoreOf 2 (normalizer (bar K (kRad H S K) : Set (Kbar K))) with hQdef
  set W₀ : Subgroup G := (Q.comap (kbarMk K)).map K.subtype with hW₀def
  have hO := pCoreOf_le_kPar (K := K) hyp
  have hW₀ : W₀ ≤ kPar H S K := by
    rintro _ ⟨w, hw, rfl⟩
    exact (mk_mem_normalizer_bar_kRad_iff hyp h618 w).1 (hQN hw)
  have hW₀2 : IsPGroup 2 W₀ := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    obtain ⟨n, hn⟩ := hQ2 ⟨kbarMk K w, hw⟩
    have h1 : kbarMk K (w ^ 2 ^ n) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hn
    have h2 : (w : G) ^ 2 ^ n ∈ pCoreOf 2 H := by
      have h3 := (kbarMk_eq_one_iff hyp h618 _).1 h1
      simpa using h3
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow (isPGroup_pCoreOf 2 H) h2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hk]
    exact pow_orderOf_eq_one _
  have hW₀O : W₀ ≤ normalizer (pCoreOf 2 H : Set G) :=
    (map_subtype_le _).trans (h618.comp.le.trans (le_normalizer_pCoreOf 2 H))
  have hW2 : IsPGroup 2 (W₀ ⊔ pCoreOf 2 H : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hW₀2 (isPGroup_pCoreOf 2 H) hW₀O
  have hWle : W₀ ⊔ pCoreOf 2 H ≤ kPar H S K := sup_le hW₀ hO
  have hWnorm : kPar H S K ≤ normalizer ((W₀ ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro y hy
    obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_mem_sup h618 (kPar_le_sup hy)
    have hkP : k ∈ kPar H S K := by
      have h := mul_mem hy (inv_mem (hO ho))
      rwa [mul_inv_cancel_right] at h
    have hkN := (mk_mem_normalizer_bar_kRad_iff hyp h618 ⟨k, hk⟩).2 hkP
    have hk1 : k ∈ normalizer (W₀ : Set G) := mem_normalizer_map_comap (hNQ hkN)
    have hk2 : k ∈ normalizer (pCoreOf 2 H : Set G) :=
      le_normalizer_pCoreOf 2 H (h618.comp.le hk)
    have hk3 := inf_normalizer_le_normalizer_sup W₀ (pCoreOf 2 H) ⟨hk1, hk2⟩
    have ho3 : o ∈ normalizer ((W₀ ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
      le_normalizer (mem_sup_right ho)
    exact mul_mem hk3 ho3
  have hWcore : W₀ ⊔ pCoreOf 2 H ≤ kRad H S K := by
    rw [← hL.par_core]
    have hn : ((W₀ ⊔ pCoreOf 2 H).subgroupOf (kPar H S K)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hWle).2 hWnorm
    have hle : (W₀ ⊔ pCoreOf 2 H).subgroupOf (kPar H S K) ≤ CFSG.pCore 2 (kPar H S K) :=
      le_sSup (s := {N : Subgroup (kPar H S K) | N.Normal ∧ IsPGroup 2 N})
        ⟨hn, hW2.comap_subtype⟩
    intro w hw
    exact ⟨⟨w, hWle hw⟩, hle hw, rfl⟩
  intro q hq
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hw : (w : G) ∈ W₀ := ⟨w, hq, rfl⟩
  exact (mk_mem_bar_iff hyp h618 (pCoreOf_le_kRad hyp) w).2 (hWcore (mem_sup_left hw))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H
