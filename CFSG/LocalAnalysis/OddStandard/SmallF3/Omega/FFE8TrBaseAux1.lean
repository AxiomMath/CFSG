module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G H : Type} [Group G] [Group H] {K : Subgroup G}

@[expose] def ffOutFFE8TrPull (ρ : ↥K →* H) (S : Subgroup H) : Subgroup G :=
  (S.comap ρ).map K.subtype

theorem ffOutFFE8TrPull_mem_iff {ρ : ↥K →* H} {S : Subgroup H} {x : G} :
    x ∈ ffOutFFE8TrPull ρ S ↔ ∃ hx : x ∈ K, ρ ⟨x, hx⟩ ∈ S := by
  unfold ffOutFFE8TrPull
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hS⟩
    exact ⟨⟨x, hx⟩, hS, rfl⟩

theorem ffOutFFE8TrPull_coe_mem_iff {ρ : ↥K →* H} {S : Subgroup H} (x : ↥K) :
    (x : G) ∈ ffOutFFE8TrPull ρ S ↔ ρ x ∈ S :=
  ⟨fun h => (ffOutFFE8TrPull_mem_iff.mp h).2, fun h => ffOutFFE8TrPull_mem_iff.mpr ⟨x.2, h⟩⟩

theorem ffOutFFE8TrPull_le (ρ : ↥K →* H) (S : Subgroup H) : ffOutFFE8TrPull ρ S ≤ K :=
  Subgroup.map_subtype_le _

theorem ffOutFFE8TrPull_mono {ρ : ↥K →* H} {S S' : Subgroup H} (h : S ≤ S') :
    ffOutFFE8TrPull ρ S ≤ ffOutFFE8TrPull ρ S' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem ffOutFFE8TrPull_subgroupOf (ρ : ↥K →* H) (S : Subgroup H) :
    (ffOutFFE8TrPull ρ S).subgroupOf K = S.comap ρ := by
  rw [← Subgroup.comap_subtype]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem ffOutFFE8TrPull_range (ρ : ↥K →* H) : ffOutFFE8TrPull ρ ρ.range = K := by
  ext x
  rw [ffOutFFE8TrPull_mem_iff]
  exact ⟨fun h => h.1, fun hx => ⟨hx, ⟨⟨x, hx⟩, rfl⟩⟩⟩

theorem ffOutFFE8TrPull_img {ρ : ↥K →* H} (hρ : Function.Injective ρ) {T : Subgroup G}
    (hT : T ≤ K) : ffOutFFE8TrPull ρ (ffImg ρ T) = T := by
  ext x
  rw [ffOutFFE8TrPull_mem_iff]
  constructor
  · rintro ⟨hx, hmem⟩
    obtain ⟨l, hlT, hl⟩ := mem_ffImg_iff.mp hmem
    have hl' : l = ⟨x, hx⟩ := hρ hl
    have h3 : (l : G) = x := congrArg Subtype.val hl'
    rw [h3] at hlT
    exact hlT
  · intro hx
    exact ⟨hT hx, mem_ffImg_iff.mpr ⟨⟨x, hT hx⟩, hx, rfl⟩⟩

theorem ffOutFFE8TrPull_isPGroup {p : ℕ} {ρ : ↥K →* H} (hρ : Function.Injective ρ)
    {S : Subgroup H} (hS : IsPGroup p S) : IsPGroup p (ffOutFFE8TrPull ρ S) := by
  rintro ⟨x, hx⟩
  obtain ⟨hxK, hxS⟩ := ffOutFFE8TrPull_mem_iff.mp hx
  obtain ⟨k, hk⟩ := hS ⟨ρ ⟨x, hxK⟩, hxS⟩
  refine ⟨k, ?_⟩
  have h1 : ρ ((⟨x, hxK⟩ : ↥K) ^ p ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  have h2 : (⟨x, hxK⟩ : ↥K) ^ p ^ k = 1 := hρ (by rw [h1, map_one])
  apply Subtype.ext
  simpa using congrArg Subtype.val h2

theorem ffOutFFE8TrPull_card {ρ : ↥K →* H} (hρ : Function.Injective ρ) {S : Subgroup H}
    (hS : S ≤ ρ.range) : Nat.card (ffOutFFE8TrPull ρ S) = Nat.card S := by
  unfold ffOutFFE8TrPull
  rw [Subgroup.card_subtype K (S.comap ρ)]
  have h1 : (S.comap ρ).map ρ = S := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hS
  conv_rhs => rw [← h1]
  exact (Subgroup.card_map_of_injective hρ).symm

theorem ffOutFFE8TrPull_elemAb2 {ρ : ↥K →* H} (hρ : Function.Injective ρ) {S : Subgroup H}
    (hS : S ≤ ρ.range) {k : ℕ} (h : IsElemAb2 S k) : IsElemAb2 (ffOutFFE8TrPull ρ S) k := by
  refine ⟨⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨haK, haS⟩ := ffOutFFE8TrPull_mem_iff.mp a.2
    obtain ⟨hbK, hbS⟩ := ffOutFFE8TrPull_mem_iff.mp b.2
    have hc := congrArg Subtype.val (h.1.1.is_comm.comm (⟨_, haS⟩ : ↥S) ⟨_, hbS⟩)
    have h2 : (⟨a, haK⟩ : ↥K) * ⟨b, hbK⟩ = ⟨b, hbK⟩ * ⟨a, haK⟩ := by
      apply hρ
      rw [map_mul, map_mul]
      exact hc
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  · obtain ⟨hxK, hxS⟩ := ffOutFFE8TrPull_mem_iff.mp hx
    have h1 : ρ ((⟨x, hxK⟩ : ↥K) ^ 2) = 1 := by
      rw [map_pow]
      simpa using h.1.2 _ hxS
    have h2 : (⟨x, hxK⟩ : ↥K) ^ 2 = 1 := hρ (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  · rw [ffOutFFE8TrPull_card hρ hS, h.2]

theorem ffOutFFE8TrPull_sylow {ρ : ↥K →* H} (hρ : Function.Injective ρ) {S : Subgroup H}
    (h : IsSylow2Of S ρ.range) : IsSylow2Of (ffOutFFE8TrPull ρ S) K := by
  refine ⟨ffOutFFE8TrPull_le ρ S, ffOutFFE8TrPull_isPGroup hρ h.2.1, ?_⟩
  rw [Subgroup.relIndex, ffOutFFE8TrPull_subgroupOf, Subgroup.index_comap]
  exact h.2.2

theorem ffOutFFE8TrPull_mem_normalizer {ρ : ↥K →* H} {S : Subgroup H} (x : ↥K)
    (hx : ρ x ∈ normalizer (S : Set H)) :
    (x : G) ∈ normalizer (ffOutFFE8TrPull ρ S : Set G) :=
  Subgroup.le_normalizer_map K.subtype
    (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap ρ (Subgroup.mem_comap.mpr hx)))

theorem ffOutFFE8TrImg_mem_normalizer {ρ : ↥K →* H} (hρ : Function.Injective ρ)
    {T : Subgroup G} (hT : T ≤ K) (x : ↥K) (hx : ρ x ∈ normalizer (ffImg ρ T : Set H)) :
    (x : G) ∈ normalizer (T : Set G) := by
  have h := ffOutFFE8TrPull_mem_normalizer (ρ := ρ) (S := ffImg ρ T) x hx
  rwa [ffOutFFE8TrPull_img hρ hT] at h

theorem ffOutFFE8TrPull_normalE16 {ρ : ↥K →* H} (hρ : Function.Injective ρ) {P B : Subgroup H}
    (hP : P ≤ ρ.range) (h : IsNormalE16In P B) :
    IsNormalE16In (ffOutFFE8TrPull ρ P) (ffOutFFE8TrPull ρ B) := by
  obtain ⟨hBP, hB, hN⟩ := h
  refine ⟨ffOutFFE8TrPull_mono hBP, ffOutFFE8TrPull_elemAb2 hρ (hBP.trans hP) hB, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (ffOutFFE8TrPull_mono hBP)]
  intro x hx
  obtain ⟨hxK, hxP⟩ := ffOutFFE8TrPull_mem_iff.mp hx
  have hxN : ρ ⟨x, hxK⟩ ∈ normalizer (B : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp hN hxP
  exact ffOutFFE8TrPull_mem_normalizer ⟨x, hxK⟩ hxN

theorem ffOutFFE8TrImg_le_range {ρ : ↥K →* H} (T : Subgroup G) : ffImg ρ T ≤ ρ.range :=
  fun _ hx => by
    obtain ⟨l, -, rfl⟩ := mem_ffImg_iff.mp hx
    exact ⟨l, rfl⟩

theorem ffOutFFE8TrImg_elemAb2 {ρ : ↥K →* H} (hρ : Function.Injective ρ) {E : Subgroup G}
    (hE : E ≤ K) {k : ℕ} (h : IsElemAb2 E k) : IsElemAb2 (ffImg ρ E) k := by
  have hE' : ffOutFFE8TrPull ρ (ffImg ρ E) = E := ffOutFFE8TrPull_img hρ hE
  refine ⟨⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨l, hlE, hl⟩ := mem_ffImg_iff.mp a.2
    obtain ⟨l', hl'E, hl'⟩ := mem_ffImg_iff.mp b.2
    have hc := congrArg Subtype.val (h.1.1.is_comm.comm (⟨l, hlE⟩ : ↥E) ⟨l', hl'E⟩)
    have h2 : l * l' = l' * l := Subtype.ext hc
    apply Subtype.ext
    show (a : H) * b = b * a
    rw [← hl, ← hl', ← map_mul, ← map_mul, h2]
  · obtain ⟨l, hlE, rfl⟩ := mem_ffImg_iff.mp hx
    rw [← map_pow]
    have h1 : l ^ 2 = 1 := Subtype.ext (by simpa using h.1.2 _ hlE)
    rw [h1, map_one]
  · have hc := ffOutFFE8TrPull_card hρ (ffOutFFE8TrImg_le_range (ρ := ρ) E)
    rw [hE'] at hc
    rw [← hc]
    exact h.2

theorem ffOutFFE8TrMap_mem_normalizer {N : Subgroup G} (θ : ↥N →* H) {T : Subgroup G} {y : G}
    (hyN : y ∈ N) (hyT : y ∈ normalizer (T : Set G)) :
    θ ⟨y, hyN⟩ ∈ normalizer (((T.subgroupOf N).map θ : Subgroup H) : Set H) :=
  Subgroup.le_normalizer_map θ (Subgroup.mem_map_of_mem θ
    (Subgroup.le_normalizer_comap N.subtype (Subgroup.mem_comap.mpr hyT)))

end CFSG.OddStandard.SmallF3.Omega
