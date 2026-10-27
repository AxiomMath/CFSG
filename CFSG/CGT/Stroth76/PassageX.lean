module

public import CFSG.CGT.Stroth76.Passage

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

section General

variable {Y : Type*} [Group Y] [Finite Y] (K : Config Y) {O : Subgroup Y} [O.Normal]

theorem config_mk_injOn_A (hO : ¬ 2 ∣ Nat.card O) : Set.InjOn (QuotientGroup.mk' O) K.A :=
  injOn_of_isPGroup hO K.isPGroup_A

theorem config_map_normal [K.A.Normal] (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    (K.map (QuotientGroup.mk' O) hinj).A.Normal :=
  (inferInstance : K.A.Normal).map _ (QuotientGroup.mk'_surjective O)

theorem config_odd_orderOf_map_ρ (hρ : Odd (orderOf K.ρ))
    (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    Odd (orderOf (K.map (QuotientGroup.mk' O) hinj).ρ) :=
  hρ.of_dvd_nat (orderOf_map_dvd _ _)

theorem config_centralizer_map [K.A.Normal] (hO : ¬ 2 ∣ Nat.card O) {Q : Subgroup Y}
    (hQC : Q ≤ Subgroup.centralizer (K.A : Set Y))
    (hZ : Subgroup.centralizer (K.A : Set Y) ≤ Q ⊔ O)
    (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    Subgroup.centralizer ((K.map (QuotientGroup.mk' O) hinj).A : Set (Y ⧸ O)) =
      Q.map (QuotientGroup.mk' O) :=
  centralizer_map_mk' K.isPGroup_A hO hQC hZ

theorem config_map_T (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    (K.A ⊔ Subgroup.closure {K.uv, K.t, K.u}).map (QuotientGroup.mk' O) =
      (K.map (QuotientGroup.mk' O) hinj).A ⊔
        Subgroup.closure {(K.map (QuotientGroup.mk' O) hinj).uv,
          (K.map (QuotientGroup.mk' O) hinj).t, (K.map (QuotientGroup.mk' O) hinj).u} := by
  rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton]
  rfl

theorem config_map_E (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    (Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}).map (QuotientGroup.mk' O) =
      Subgroup.closure {(K.map (QuotientGroup.mk' O) hinj).x ^ 2,
        (K.map (QuotientGroup.mk' O) hinj).y ^ 2, (K.map (QuotientGroup.mk' O) hinj).uv,
        (K.map (QuotientGroup.mk' O) hinj).t} := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, map_pow, map_pow]
  rfl

theorem card_map_mk'_of_isPGroup (hO : ¬ 2 ∣ Nat.card O) {R : Subgroup Y}
    (hR : IsPGroup 2 R) : Nat.card (R.map (QuotientGroup.mk' O)) = Nat.card R :=
  Nat.card_image_of_injOn (injOn_of_isPGroup hO hR)

theorem eq_of_map_eq_of_le_isPGroup (hO : ¬ 2 ∣ Nat.card O) {P R R' : Subgroup Y}
    (hP : IsPGroup 2 P) (hR : R ≤ P) (hR' : R' ≤ P)
    (h : R.map (QuotientGroup.mk' O) = R'.map (QuotientGroup.mk' O)) : R = R' := by
  have hRR' : IsPGroup 2 (R ⊔ R' : Subgroup Y) := hP.to_le (sup_le hR hR')
  have hmap : (R ⊔ R').map (QuotientGroup.mk' O) = R.map (QuotientGroup.mk' O) := by
    rw [Subgroup.map_sup, h, sup_idem]
  apply le_antisymm
  · exact le_sup_left.trans (le_of_map_le hO hRR' le_sup_right (by rw [hmap, h]))
  · exact le_sup_right.trans (le_of_map_le hO hRR' le_sup_left hmap.le)

variable [K.A.Normal]

theorem config_T_le_map_sylow (P : Sylow 2 Y)
    (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P)
    (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    (K.map (QuotientGroup.mk' O) hinj).A ⊔
        Subgroup.closure {(K.map (QuotientGroup.mk' O) hinj).uv,
          (K.map (QuotientGroup.mk' O) hinj).t, (K.map (QuotientGroup.mk' O) hinj).u} ≤
      P.mapSurjective (QuotientGroup.mk'_surjective O) := by
  rw [← config_map_T K hinj]
  exact Subgroup.map_mono hTP

theorem config_E_le_sylow (P : Sylow 2 Y) (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P) :
    Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} ≤ (P : Subgroup Y) := by
  have hAP : K.A ≤ P := le_sup_left.trans hTP
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hAP (pow_mem K.x_mem 2)
  · exact hAP (pow_mem K.y_mem 2)
  · exact hTP K.uv_mem_T
  · exact hTP K.t_mem_T

theorem config_hE_map_sylow (hO : ¬ 2 ∣ Nat.card O) (P : Sylow 2 Y)
    (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P)
    (hE : ∀ g ∈ (P : Subgroup Y),
      g ∈ Subgroup.normalizer (Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set Y) →
        g ∈ K.A ⊔ Subgroup.closure {K.uv, K.t, K.u})
    (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    ∀ g ∈ (P.mapSurjective (QuotientGroup.mk'_surjective O) : Subgroup (Y ⧸ O)),
      g ∈ Subgroup.normalizer (Subgroup.closure {(K.map (QuotientGroup.mk' O) hinj).x ^ 2,
        (K.map (QuotientGroup.mk' O) hinj).y ^ 2, (K.map (QuotientGroup.mk' O) hinj).uv,
        (K.map (QuotientGroup.mk' O) hinj).t} : Set (Y ⧸ O)) →
      g ∈ (K.map (QuotientGroup.mk' O) hinj).A ⊔
        Subgroup.closure {(K.map (QuotientGroup.mk' O) hinj).uv,
          (K.map (QuotientGroup.mk' O) hinj).t, (K.map (QuotientGroup.mk' O) hinj).u} := by
  intro g hg hgN
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
  rw [← config_map_E K hinj] at hgN
  have := hE g' hg' (mem_normalizer_of_map hO P.isPGroup' (config_E_le_sylow K P hTP) hg' hgN)
  rw [← config_map_T K hinj]
  exact Subgroup.mem_map_of_mem _ this

theorem config_hE_map_centralizer (hO : ¬ 2 ∣ Nat.card O) (P : Sylow 2 Y)
    (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P) {Q : Subgroup Y}
    (hQP : Q ≤ (P : Subgroup Y))
    (hQE : ∀ g ∈ Q,
      g ∈ Subgroup.normalizer (Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set Y) →
        g ∈ K.A)
    (hinj : Set.InjOn (QuotientGroup.mk' O) K.A) :
    ∀ g ∈ Q.map (QuotientGroup.mk' O),
      g ∈ Subgroup.normalizer (Subgroup.closure {(K.map (QuotientGroup.mk' O) hinj).x ^ 2,
        (K.map (QuotientGroup.mk' O) hinj).y ^ 2, (K.map (QuotientGroup.mk' O) hinj).uv,
        (K.map (QuotientGroup.mk' O) hinj).t} : Set (Y ⧸ O)) →
      g ∈ (K.map (QuotientGroup.mk' O) hinj).A := by
  intro g hg hgN
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
  rw [← config_map_E K hinj] at hgN
  exact Subgroup.mem_map_of_mem _
    (hQE q hq (mem_normalizer_of_map hO P.isPGroup' (config_E_le_sylow K P hTP) (hQP hq) hgN))

end General

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem frame_T_le_sylowN :
    F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} ≤
      (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) := by
  rw [← Subgroup.map_le_map_iff_of_injective
    (show Function.Injective (Subgroup.normalizer (F.A : Set G)).subtype from
      Subtype.val_injective), F.T_map, frame_map_sylowN]
  exact le_inf F.T_le_S F.T_le_normalizer

theorem frame_hE_sylowN : ∀ g ∈ (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))),
    g ∈ Subgroup.normalizer (Subgroup.closure
      {F.configN.x ^ 2, F.configN.y ^ 2, F.configN.uv, F.configN.t} :
        Set (Subgroup.normalizer (F.A : Set G))) →
      g ∈ F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} := by
  intro g hg hgE
  have hgS : (g : G) ∈ (F.S : Subgroup G) := by
    rw [coe_frameSylowN, Subgroup.mem_subgroupOf] at hg
    exact hg.1
  have hgE' := coe_mem_normalizer_map hgE
  rw [F.E_map] at hgE'
  have hT := F.mem_T_of_normalizer_E hgS hgE'
  rw [← F.T_map] at hT
  exact (Subgroup.mem_map_iff_mem Subtype.val_injective).mp hT

theorem frame_hE_centralizerN : ∀ g ∈
    Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
      (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))),
    g ∈ Subgroup.normalizer (Subgroup.closure
      {F.configN.x ^ 2, F.configN.y ^ 2, F.configN.uv, F.configN.t} :
        Set (Subgroup.normalizer (F.A : Set G))) → g ∈ F.configN.A := by
  intro g hg hgE
  have hgQ : (g : G) ∈ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) := by
    rw [← frame_map_centralizer_inf_sylowN F]
    exact Subgroup.mem_map_of_mem _ hg
  have hgE' := coe_mem_normalizer_map hgE
  rw [F.E_map] at hgE'
  exact Subgroup.mem_subgroupOf.mpr (frame_mem_A_of_mem_normalizer_E F hgQ.2 hgE' hgQ.1)

theorem frame_odd_orderOf_configN_ρ : Odd (orderOf F.configN.ρ) := by
  rw [show orderOf F.configN.ρ = orderOf F.dA.ρ from Subgroup.orderOf_mk _ _]
  exact F.dA.rho_odd

theorem frame_card_centralizerN :
    Nat.card (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) :
          Subgroup (Subgroup.normalizer (F.A : Set G))) =
      Nat.card (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) := by
  rw [← frame_map_centralizer_inf_sylowN F,
    Subgroup.card_map_of_injective Subtype.val_injective]

theorem frame_isPGroup_centralizerN :
    IsPGroup 2 (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) :
          Subgroup (Subgroup.normalizer (F.A : Set G))) :=
  (frameSylowN F).isPGroup'.to_le inf_le_right

theorem frame_card_sylowN_dvd (h11 : ¬ 2 ^ 11 ∣ Nat.card G) :
    Nat.card (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) ∣ 2 ^ 10 := by
  rw [← Subgroup.card_map_of_injective (f := (Subgroup.normalizer (F.A : Set G)).subtype)
    Subtype.val_injective, frame_map_sylowN]
  exact (Subgroup.card_dvd_of_le inf_le_left).trans (frame_card_S_dvd F h11)

variable (O : Subgroup (Subgroup.normalizer (F.A : Set G))) [O.Normal]

theorem frame_injOn_configN_A (hO : ¬ 2 ∣ Nat.card O) :
    Set.InjOn (QuotientGroup.mk' O) F.configN.A :=
  config_mk_injOn_A F.configN hO

theorem frame_injOn_sylowN (hO : ¬ 2 ∣ Nat.card O) :
    Set.InjOn (QuotientGroup.mk' O)
      (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) :=
  injOn_of_isPGroup hO (frameSylowN F).isPGroup'

theorem frame_configX_normal (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A) :
    (F.configN.map (QuotientGroup.mk' O) hinj).A.Normal :=
  config_map_normal F.configN hinj

theorem frame_odd_orderOf_configX_ρ (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A) :
    Odd (orderOf (F.configN.map (QuotientGroup.mk' O) hinj).ρ) :=
  config_odd_orderOf_map_ρ F.configN (frame_odd_orderOf_configN_ρ F) hinj

theorem frame_centralizer_configX (hO : ¬ 2 ∣ Nat.card O)
    (hZ : Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ≤
      (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))) ⊔ O)
    (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A) :
    Subgroup.centralizer ((F.configN.map (QuotientGroup.mk' O) hinj).A :
        Set (Subgroup.normalizer (F.A : Set G) ⧸ O)) =
      (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).map
          (QuotientGroup.mk' O) :=
  config_centralizer_map F.configN hO inf_le_left hZ hinj

theorem frame_card_map_centralizerN (hO : ¬ 2 ∣ Nat.card O) :
    Nat.card ((Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).map
          (QuotientGroup.mk' O)) =
      Nat.card (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) := by
  rw [card_map_mk'_of_isPGroup hO (frame_isPGroup_centralizerN F), frame_card_centralizerN F]

theorem frame_card_map_centralizerN_dvd (h11 : ¬ 2 ^ 11 ∣ Nat.card G) (hO : ¬ 2 ∣ Nat.card O) :
    Nat.card ((Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).map
          (QuotientGroup.mk' O)) ∣ 2 ^ 7 := by
  rw [frame_card_map_centralizerN F O hO]
  exact frame_card_centralizer_inf_dvd F h11

theorem frame_map_centralizerN_ne (hO : ¬ 2 ∣ Nat.card O)
    (hne : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) ≠ F.A)
    (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A) :
    (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).map
          (QuotientGroup.mk' O) ≠ (F.configN.map (QuotientGroup.mk' O) hinj).A := by
  intro h
  apply hne
  refine (Subgroup.eq_of_le_of_card_ge (frame_A_le_centralizer_inf F) ?_).symm
  have h1 := frame_card_map_centralizerN F O hO
  rw [h, (F.configN.map (QuotientGroup.mk' O) hinj).hAcard] at h1
  rw [← h1, F.dA.card_eq_32]

theorem frame_hE_centralizerX (hO : ¬ 2 ∣ Nat.card O)
    (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A) :
    ∀ g ∈ (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).map
          (QuotientGroup.mk' O),
      g ∈ Subgroup.normalizer (Subgroup.closure
        {(F.configN.map (QuotientGroup.mk' O) hinj).x ^ 2,
          (F.configN.map (QuotientGroup.mk' O) hinj).y ^ 2,
          (F.configN.map (QuotientGroup.mk' O) hinj).uv,
          (F.configN.map (QuotientGroup.mk' O) hinj).t} :
            Set (Subgroup.normalizer (F.A : Set G) ⧸ O)) →
        g ∈ (F.configN.map (QuotientGroup.mk' O) hinj).A :=
  config_hE_map_centralizer F.configN hO (frameSylowN F) (frame_T_le_sylowN F) inf_le_right
    (frame_hE_centralizerN F) hinj

theorem frame_T_le_sylowX (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A) :
    (F.configN.map (QuotientGroup.mk' O) hinj).A ⊔
        Subgroup.closure {(F.configN.map (QuotientGroup.mk' O) hinj).uv,
          (F.configN.map (QuotientGroup.mk' O) hinj).t,
          (F.configN.map (QuotientGroup.mk' O) hinj).u} ≤
      (frameSylowN F).mapSurjective (QuotientGroup.mk'_surjective O) :=
  config_T_le_map_sylow F.configN (frameSylowN F) (frame_T_le_sylowN F) hinj

theorem frame_card_sylowX_dvd (h11 : ¬ 2 ^ 11 ∣ Nat.card G) (hO : ¬ 2 ∣ Nat.card O) :
    Nat.card ((frameSylowN F).mapSurjective (QuotientGroup.mk'_surjective O) :
      Subgroup (Subgroup.normalizer (F.A : Set G) ⧸ O)) ∣ 2 ^ 10 := by
  rw [show (((frameSylowN F).mapSurjective (QuotientGroup.mk'_surjective O) :
      Subgroup (Subgroup.normalizer (F.A : Set G) ⧸ O))) =
      (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))).map (QuotientGroup.mk' O)
      from rfl, card_map_mk'_of_isPGroup hO (frameSylowN F).isPGroup']
  exact frame_card_sylowN_dvd F h11

theorem frame_hE_sylowX (hO : ¬ 2 ∣ Nat.card O)
    (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A) :
    ∀ g ∈ ((frameSylowN F).mapSurjective (QuotientGroup.mk'_surjective O) :
        Subgroup (Subgroup.normalizer (F.A : Set G) ⧸ O)),
      g ∈ Subgroup.normalizer (Subgroup.closure
        {(F.configN.map (QuotientGroup.mk' O) hinj).x ^ 2,
          (F.configN.map (QuotientGroup.mk' O) hinj).y ^ 2,
          (F.configN.map (QuotientGroup.mk' O) hinj).uv,
          (F.configN.map (QuotientGroup.mk' O) hinj).t} :
            Set (Subgroup.normalizer (F.A : Set G) ⧸ O)) →
        g ∈ (F.configN.map (QuotientGroup.mk' O) hinj).A ⊔
          Subgroup.closure {(F.configN.map (QuotientGroup.mk' O) hinj).uv,
            (F.configN.map (QuotientGroup.mk' O) hinj).t,
            (F.configN.map (QuotientGroup.mk' O) hinj).u} :=
  config_hE_map_sylow F.configN hO (frameSylowN F) (frame_T_le_sylowN F) (frame_hE_sylowN F)
    hinj

theorem frame_sylowN_eq_of_sylowX_eq (hO : ¬ 2 ∣ Nat.card O)
    (hinj : Set.InjOn (QuotientGroup.mk' O) F.configN.A)
    (h : ((frameSylowN F).mapSurjective (QuotientGroup.mk'_surjective O) :
        Subgroup (Subgroup.normalizer (F.A : Set G) ⧸ O)) =
      (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
          (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).map
            (QuotientGroup.mk' O) ⊔
        Subgroup.closure {(F.configN.map (QuotientGroup.mk' O) hinj).uv,
          (F.configN.map (QuotientGroup.mk' O) hinj).t,
          (F.configN.map (QuotientGroup.mk' O) hinj).u}) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) =
      (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)) ⊔
        Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} := by
  have hTP := frame_T_le_sylowN F
  have hD : Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} ≤
      (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) := le_sup_right.trans hTP
  have hR : (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))) ⊔
      Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} ≤
      (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) := sup_le inf_le_right hD
  have hmap : ((Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))) ⊔
      Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u}).map
      (QuotientGroup.mk' O) = (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))).map
        (QuotientGroup.mk' O) := by
    rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton]
    exact h.symm
  have hPN := eq_of_map_eq_of_le_isPGroup hO (frameSylowN F).isPGroup' le_rfl hR hmap.symm
  rw [← frame_map_sylowN F, hPN, Subgroup.map_sup, frame_map_centralizer_inf_sylowN F,
    MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

end CFSG.CGT.Stroth76
