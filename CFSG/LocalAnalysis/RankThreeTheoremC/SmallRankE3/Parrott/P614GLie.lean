module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GBender

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem core_le_normalizer_pre (c : Ctx M B H S K z) (U : Subgroup (Kbar K)) :
    pCoreOf 2 H ≤ normalizer (pre K U : Set G) := by
  intro o ho
  rw [mem_normalizer_iff]
  intro g
  have hoH : o ∈ H := c.S_le (c.core_le ho)
  have hfix : ∀ (n : G) (hn : n ∈ H), c.rho ⟨n, hn⟩ = 1 → ∀ u ∈ U, c.rho ⟨n, hn⟩ u ∈ U :=
    fun n hn h u hu => by rw [h]; exact hu
  refine ⟨fun hg => c.conj_mem_pre hoH (hfix o hoH (c.rho_eq_one_of_mem_core ho)) hg,
    fun hg => ?_⟩
  have := c.conj_mem_pre (H.inv_mem hoH)
    (hfix _ _ (by
      have h1 := c.rho_eq_one_of_mem_core (inv_mem ho)
      exact h1)) hg
  simpa [mul_assoc] using this

theorem mem_pre_sup_iff (c : Ctx M B H S K z) (U : Subgroup (Kbar K)) {k : G} (hk : k ∈ K) :
    k ∈ pre K U ⊔ pCoreOf 2 H ↔ (QuotientGroup.mk ⟨k, hk⟩ : Kbar K) ∈ U := by
  constructor
  · intro h
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (c.core_le_normalizer_pre U)]
      at h
    obtain ⟨t, ht, o, ho, rfl⟩ := Set.mem_mul.1 h
    have htK := pre_le K U ht
    have hoK : o ∈ K := by simpa using K.mul_mem (K.inv_mem htK) hk
    have he : (QuotientGroup.mk ⟨t * o, hk⟩ : Kbar K) = QuotientGroup.mk ⟨t, htK⟩ := by
      rw [c.mk_eq_mk_iff]
      simpa using inv_mem ho
    rw [he]
    exact (mem_pre htK).1 ht
  · intro h
    exact mem_sup_left ((mem_pre hk).2 h)

theorem isPGroup_pre_sup (c : Ctx M B H S K z) {U : Subgroup (Kbar K)} (hU : IsPGroup 2 U) :
    IsPGroup 2 (pre K U ⊔ pCoreOf 2 H : Subgroup G) :=
  (c.isPGroup_pre hU).to_sup_of_normal_left' c.isPGroup_core (c.core_le_normalizer_pre U)

theorem index_pre_sup (c : Ctx M B H S K z) (U : Subgroup (Kbar K)) :
    ((pre K U ⊔ pCoreOf 2 H).subgroupOf (K ⊔ pCoreOf 2 H)).index = U.index := by
  have hTK : pre K U ⊔ pCoreOf 2 H ≤ normalizer (K : Set G) :=
    sup_le ((pre_le K U).trans (c.K_le.trans c.comp.normal))
      ((c.core_le.trans c.S_le).trans c.comp.normal)
  have h := index_sup_eq_index_inf hTK
  have e1 : K ⊔ (pre K U ⊔ pCoreOf 2 H) = K ⊔ pCoreOf 2 H := by
    rw [← sup_assoc, sup_eq_left.mpr (pre_le K U)]
  rw [e1] at h
  rw [h]
  have e2 : (K ⊓ (pre K U ⊔ pCoreOf 2 H)).subgroupOf K =
      U.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
    ext k
    rw [mem_subgroupOf, mem_comap, QuotientGroup.mk'_apply, ← c.mem_pre_sup_iff U k.2]
    exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩
  rw [e2, index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem mem_pre_rbar_iff (c : Ctx M B H S K z) {k : G} (hk : k ∈ K) :
    k ∈ pre K (rbar K S) ↔ k ∈ S := by
  rw [mem_pre hk]
  constructor
  · rintro ⟨s, hs, he⟩
    have h1 := (c.mk_eq_mk_iff _ _).1 he
    have e : k = (s : G) * ((s : G)⁻¹ * k) := by group
    rw [e]
    exact S.mul_mem (mem_subgroupOf.mp hs) (c.core_le h1)
  · intro h
    exact mk_mem_rbar hk h

theorem kRad_eq (c : Ctx M B H S K z) : kRad H S K = pre K (rbar K S) ⊔ pCoreOf 2 H := by
  apply le_antisymm
  · intro r hr
    obtain ⟨hrS, hrKO⟩ := mem_inf.mp hr
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H)
      (c.K_le.trans c.H_le_normalizer_core)] at hrKO
    obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 hrKO
    have hkS : k ∈ S := by simpa using S.mul_mem hrS (S.inv_mem (c.core_le ho))
    exact mul_mem (mem_sup_left ((c.mem_pre_rbar_iff hk).2 hkS)) (mem_sup_right ho)
  · refine sup_le (fun k hk => ?_) (le_inf c.core_le le_sup_right)
    have hkK := pre_le K _ hk
    exact ⟨(c.mem_pre_rbar_iff hkK).1 hk, mem_sup_left hkK⟩

theorem kRad_le_S : kRad H S K ≤ S := inf_le_left

theorem kRad_le_KO : kRad H S K ≤ K ⊔ pCoreOf 2 H := inf_le_right

theorem le_normalizer_KO (c : Ctx M B H S K z) {g : G} (hg : g ∈ H) :
    g ∈ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  inf_normalizer_le_normalizer_sup _ _ ⟨c.comp.normal hg, c.H_le_normalizer_core hg⟩

theorem le_normalizer_kRad (c : Ctx M B H S K z) {g : G} (hg : g ∈ H)
    (hgS : g ∈ normalizer (S : Set G)) : g ∈ normalizer ((kRad H S K : Subgroup G) : Set G) :=
  inf_normalizer_le_normalizer_inf ⟨hgS, c.le_normalizer_KO hg⟩

theorem S_le_normalizer_kRad (c : Ctx M B H S K z) :
    S ≤ normalizer ((kRad H S K : Subgroup G) : Set G) :=
  fun _ hs => c.le_normalizer_kRad (c.S_le hs) (le_normalizer hs)

theorem B_le_normalizer_kRad (c : Ctx M B H S K z) :
    B ≤ normalizer ((kRad H S K : Subgroup G) : Set G) :=
  fun _ hb => c.le_normalizer_kRad (c.B_le hb) (c.B_le_normalizer_S hb)

theorem normalizer_kRad_le (c : Ctx M B H S K z) (hR : pCoreOf 2 H < kRad H S K) :
    normalizer ((kRad H S K : Subgroup G) : Set G) ≤ M :=
  c.norm_le _ hR kRad_le_S (sup_le c.S_le_normalizer_kRad c.B_le_normalizer_kRad)

theorem le_normalizer_kPar (c : Ctx M B H S K z) {g : G} (hg : g ∈ H)
    (hgS : g ∈ normalizer (S : Set G)) : g ∈ normalizer ((kPar H S K : Subgroup G) : Set G) :=
  inf_normalizer_le_normalizer_inf ⟨c.le_normalizer_KO hg,
    (normalizer ((kRad H S K : Subgroup G) : Set G)).le_normalizer (c.le_normalizer_kRad hg hgS)⟩

theorem kPar_le_KO : kPar H S K ≤ K ⊔ pCoreOf 2 H := inf_le_left

theorem kRad_le_kPar (c : Ctx M B H S K z) : kRad H S K ≤ kPar H S K :=
  le_inf kRad_le_KO le_normalizer

theorem pCoreOf_kPar (c : Ctx M B H S K z) : pCoreOf 2 (kPar H S K) = kRad H S K := by
  apply le_antisymm
  · set Q := pCoreOf 2 (kPar H S K) with hQ
    have hQK : Q ≤ kPar H S K := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
    have hnQ : ∀ g ∈ H, g ∈ normalizer (S : Set G) → g ∈ normalizer (Q : Set G) := fun g hg hgS =>
      normalizer_localGroup_le_normalizer_pCoreOf 2 _ (c.le_normalizer_kPar hg hgS)
    have hSQ : S ≤ normalizer (Q : Set G) := fun s hs => hnQ s (c.S_le hs) (le_normalizer hs)
    have hBQ : B ≤ normalizer (Q : Set G) := fun b hb => hnQ b (c.B_le hb) (c.B_le_normalizer_S hb)
    have hjoin : IsTwoInvariantIn B H (Q ⊔ S) :=
      ⟨sup_le (hQK.trans (kPar_le_KO.trans (sup_le c.K_le (c.core_le.trans c.S_le)))) c.S_le,
        (pCoreOf_isPGroup 2 _).to_sup_of_normal_left' c.isPGroup_S hSQ,
        fun b hb => inf_normalizer_le_normalizer_sup _ _ ⟨hBQ hb, c.B_le_normalizer_S hb⟩⟩
    have hQS : Q ≤ S := le_sup_left.trans (c.maxInv.2 _ hjoin le_sup_right).le
    exact le_inf hQS (hQK.trans kPar_le_KO)
  · refine normal_pGroup_le_pCoreOf 2 _ _ c.kRad_le_kPar
      ((normal_subgroupOf_iff_le_normalizer c.kRad_le_kPar).mpr inf_le_right)
      (c.isPGroup_S.to_le kRad_le_S)

theorem pCoreOf_normalizer_rbar (c : Ctx M B H S K z) :
    pCoreOf 2 (normalizer ((rbar K S : Subgroup (Kbar K)) : Set (Kbar K))) = rbar K S := by
  set N := normalizer ((rbar K S : Subgroup (Kbar K)) : Set (Kbar K)) with hN
  set Q := pCoreOf 2 N with hQ
  apply le_antisymm
  ·
    have hpres : ∀ (n : G) (hn : n ∈ H), n ∈ normalizer (S : Set G) →
        ∀ u ∈ Q, c.rho ⟨n, hn⟩ u ∈ Q := by
      intro n hn hnS
      have hφN : ∀ (m : G) (hm : m ∈ H), m ∈ normalizer (S : Set G) →
          ∀ g ∈ N, c.rho ⟨m, hm⟩ g ∈ N := by
        intro m hm hmS g hg
        have hfin : (rbar K S).map (c.rho ⟨m, hm⟩).toMonoidHom = rbar K S := by
          apply Subgroup.eq_of_le_of_card_ge
          · rintro _ ⟨u, hu, rfl⟩
            exact c.rho_mem_rbar hm hmS hu
          · rw [card_map_of_injective (c.rho ⟨m, hm⟩).injective]
        rw [mem_normalizer_iff]
        intro u
        have key : ∀ v, v ∈ rbar K S ↔ c.rho ⟨m, hm⟩ v ∈ rbar K S := fun v => by
          constructor
          · intro hv
            exact c.rho_mem_rbar hm hmS hv
          · intro hv
            rw [← hfin] at hv
            obtain ⟨w, hw, hwv⟩ := hv
            rw [← (c.rho ⟨m, hm⟩).injective hwv]
            exact hw
        obtain ⟨v, rfl⟩ := (c.rho ⟨m, hm⟩).surjective u
        rw [← key v, ← map_inv, ← map_mul, ← map_mul, ← key]
        exact mem_normalizer_iff.mp hg v
      have hmap : Q.map (c.rho ⟨n, hn⟩).toMonoidHom ≤ Q := by
        refine normal_pGroup_le_pCoreOf 2 _ N ?_ ?_ ((pCoreOf_isPGroup 2 N).map _)
        · rintro _ ⟨u, hu, rfl⟩
          exact hφN n hn hnS u (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N hu)
        · rw [normal_subgroupOf_iff_le_normalizer (by
            rintro _ ⟨u, hu, rfl⟩
            exact hφN n hn hnS u (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N hu))]
          intro g hg
          rw [mem_normalizer_iff]
          have hninv : n⁻¹ ∈ normalizer (S : Set G) := inv_mem hnS
          have hg' : c.rho ⟨n⁻¹, H.inv_mem hn⟩ g ∈ N := hφN _ _ hninv g hg
          have hQn := localGroup_le_normalizer_pCoreOf 2 N hg'
          have einv : ∀ v, c.rho ⟨n, hn⟩ (c.rho ⟨n⁻¹, H.inv_mem hn⟩ v) = v := fun v => by
            rw [← MulAut.mul_apply, ← map_mul]
            have e1 : (⟨n, hn⟩ : ↥H) * ⟨n⁻¹, H.inv_mem hn⟩ = 1 := Subtype.ext (mul_inv_cancel n)
            rw [e1, map_one, MulAut.one_apply]
          intro v
          constructor
          · rintro ⟨u, hu, rfl⟩
            refine ⟨c.rho ⟨n⁻¹, H.inv_mem hn⟩ g * u * (c.rho ⟨n⁻¹, H.inv_mem hn⟩ g)⁻¹,
              (mem_normalizer_iff.mp hQn u).1 hu, ?_⟩
            simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, einv]
          · rintro ⟨u, hu, hue⟩
            refine ⟨(c.rho ⟨n⁻¹, H.inv_mem hn⟩ g)⁻¹ * u * c.rho ⟨n⁻¹, H.inv_mem hn⟩ g, ?_, ?_⟩
            · have := (mem_normalizer_iff.mp (inv_mem hQn) u).1 hu
              simpa using this
            · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, einv] at hue ⊢
              rw [hue]
              group
      exact fun u hu => hmap (mem_map_of_mem _ hu)
    have hpre := c.pre_le_S (U := Q) (pCoreOf_isPGroup 2 N)
      (fun s hs => hpres s (c.S_le hs) (le_normalizer hs))
      (fun b hb => hpres b (c.B_le hb) (c.B_le_normalizer_S hb))
    intro u hu
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective u
    exact mk_mem_rbar k.2 (hpre ((mem_pre k.2).2 hu))
  · exact normal_pGroup_le_pCoreOf 2 _ _ le_normalizer
      ((normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl) c.isPGroup_rbar

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
