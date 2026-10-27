module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import Certificates.Certificate24720

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier
open CFSG.Sporadic.Mathieu

variable {Y : Type} [Group Y]

theorem gens_mem : ∀ g ∈ HypOne.M24.gens, g ∈ NativeSporadic.M24 := by
  intro g hg
  simp only [HypOne.M24.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact m24a.2
  · exact m24b.2

theorem exists_mul_self_eq_of_orderOf_two
    (hY : IsSporadic Y .M24) {u : Y} (hu : orderOf u = 2) :
    ∃ v : Y, v * v = u := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.M24 := e
  set w : NativeSporadic.M24 := e' u with hw
  have hw2 : orderOf (w : Equiv.Perm (Fin 24)) = 2 := by
    rw [Subgroup.orderOf_coe, hw, MulEquiv.orderOf_eq]
    exact hu
  obtain ⟨r, hr, c, hc, hwc⟩ := HypOne.M24.involution_cover.1 (w : Equiv.Perm (Fin 24))
    (by simp) hw2
  obtain ⟨h1, h2⟩ := Certificates.certificate24720.1
  have hv1 : evalCodes HypOne.M24.gens wordV1 ∈ NativeSporadic.M24 := evalCodes_mem _ gens_mem _
  have hv2 : evalCodes HypOne.M24.gens wordV2 ∈ NativeSporadic.M24 := evalCodes_mem _ gens_mem _
  have key : ∃ v ∈ NativeSporadic.M24, v * v = r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hv1, h1⟩
    · exact ⟨_, hv2, h2⟩
  obtain ⟨v, hv, hvv⟩ := key
  have hcv : c * v * c⁻¹ ∈ NativeSporadic.M24 :=
    NativeSporadic.M24.mul_mem (NativeSporadic.M24.mul_mem hc hv) (NativeSporadic.M24.inv_mem hc)
  refine ⟨e'.symm ⟨c * v * c⁻¹, hcv⟩, ?_⟩
  rw [← map_mul]
  apply e'.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  show c * v * c⁻¹ * (c * v * c⁻¹) = (w : Equiv.Perm (Fin 24))
  rw [hwc]
  calc c * v * c⁻¹ * (c * v * c⁻¹) = c * (v * v) * c⁻¹ := by group
    _ = c * r * c⁻¹ := by rw [hvv]


theorem centralizerIn_conj_eq {M : Type*} [Group M] {H : Subgroup M} {c : M} (hc : c ∈ H) (r : M) :
    centralizerIn H (c * r * c⁻¹) = (centralizerIn H r).map (MulAut.conj c).toMonoidHom := by
  ext y
  simp only [mem_centralizerIn, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hy, hyc⟩
    refine ⟨c⁻¹ * y * c, ⟨H.mul_mem (H.mul_mem (H.inv_mem hc) hy) hc, ?_⟩, by group⟩
    have : y * (c * r * c⁻¹) = (c * r * c⁻¹) * y := hyc
    calc c⁻¹ * y * c * r = c⁻¹ * (y * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * y) * c := by rw [this]
      _ = r * (c⁻¹ * y * c) := by group
  · rintro ⟨x, ⟨hx, hxr⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hc hx) (H.inv_mem hc), ?_⟩
    calc c * x * c⁻¹ * (c * r * c⁻¹) = c * (x * r) * c⁻¹ := by group
      _ = c * (r * x) * c⁻¹ := by rw [hxr]
      _ = (c * r * c⁻¹) * (c * x * c⁻¹) := by group

theorem not_nine_dvd_card_centralizer
    (hY : IsSporadic Y .M24) {u : Y} (hu : orderOf u = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({u} : Set Y)) := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.M24 := e
  let φ : Y →* Equiv.Perm (Fin 24) := NativeSporadic.M24.subtype.comp e'.toMonoidHom
  have hφ : Function.Injective φ := fun a b h => e'.injective (Subtype.ext h)
  have h1 : (centralizer ({u} : Set Y)).map φ = centralizerIn NativeSporadic.M24 (φ u) := by
    ext y
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, mem_centralizerIn]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(e' x).2, ?_⟩
      have := congrArg φ hx
      simpa using this
    · rintro ⟨hy, hyu⟩
      refine ⟨e'.symm ⟨y, hy⟩, ?_, by simp [φ]⟩
      apply hφ
      simp only [map_mul, φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, Subgroup.coe_subtype]
      exact hyu
  have h2 : Nat.card (centralizer ({u} : Set Y)) =
      Nat.card (centralizerIn NativeSporadic.M24 (φ u)) := by
    rw [← h1, Subgroup.card_map_of_injective hφ]
  have hw2 : orderOf (φ u) = 2 := by
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hu
  obtain ⟨r, hr, c, hc, hwc⟩ := HypOne.M24.involution_cover.1 (φ u)
    (by simp [φ]) hw2
  rw [h2, hwc, centralizerIn_conj_eq hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [HypOne.M24.centralizerIn_rep1, (m24_rep_data1).2.2.2.1]
    decide
  · rw [HypOne.M24.centralizerIn_rep2, (m24_rep_data2).2.2.2.1]
    decide


open CFSG.QuasithinUnique

theorem le_pCore_two {H : Type*} [Group H] {N : Subgroup H} (hN : N.Normal) (hp : IsPGroup 2 N) :
    N ≤ CFSG.Open.pCore 2 H := by
  intro x hx
  rw [CFSG.pCore_eq_iSup]
  exact Subgroup.mem_iSup_of_mem N (Subgroup.mem_iSup_of_mem hN (Subgroup.mem_iSup_of_mem hp hx))

theorem card_sylow_two [Finite Y] (hY : IsSporadic Y .M24)
    {U : Subgroup Y} (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) : Nat.card U = 1024 := by
  obtain ⟨e⟩ := hY
  have hcard : Nat.card Y = 244823040 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  have h1 := Subgroup.card_mul_index U
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hUp
  rw [hn, hcard] at h1
  have h2 : n = 10 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h4 : (2 : ℕ) ^ n * U.index = 2 ^ n * (2 ^ (10 - n) * 239085) := by
        rw [h1, ← mul_assoc, ← pow_add]
        have : n + (10 - n) = 10 := by omega
        rw [this]
        norm_num
      have h6 := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) n) h4
      exact hUi (h6 ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _)
    · have h3 : (2 : ℕ) ^ 11 ∣ 244823040 := by
        rw [← h1]
        exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
      norm_num at h3
  rw [hn, h2]
  norm_num

theorem normalizer_eq_of_sylow [Finite Y]
    (hY : IsSporadic Y .M24) {U : Subgroup Y} (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) :
    normalizer (U : Set Y) = U := by
  have hX : Nonempty (Y ≃* Carrier .M24) := hY
  have hU : IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, hUp, ?_⟩
    have : (U.subgroupOf ⊤).index = U.index := Subgroup.relIndex_top_right U
    rw [this]
    exact hUi
  have hle : U ≤ normalizer (U : Set Y) := Subgroup.le_normalizer
  have hUc := card_sylow_two hY hUp hUi
  rcases CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_overgroups hX hU hle with
    htop | ⟨m, hm, hord, ho2, -⟩
  · exfalso
    have hnorm : U.Normal := by
      constructor
      intro x hx g
      have : g ∈ normalizer (U : Set Y) := by rw [htop]; trivial
      exact (Subgroup.mem_normalizer_iff.1 this x).1 hx
    obtain ⟨e⟩ := hY
    have e' : Y ≃* NativeSporadic.M24 := e
    have hsimple : IsSimpleGroup Y := by
      have : IsSimpleGroup NativeSporadic.M24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
      exact e'.isSimpleGroup
    rcases hsimple.eq_bot_or_eq_top_of_normal U with h | h
    · rw [h, Subgroup.card_bot] at hUc
      omega
    · rw [h, Subgroup.card_top] at hUc
      have : Nat.card Y = 244823040 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.Sporadic.Mathieu.card_M24
      omega
  · have hUle : (1024 : ℕ) ≤ m.o2 := by
      rw [← ho2, ← hUc]
      refine Subgroup.card_le_of_le ?_
      have hnorm : (U.subgroupOf (normalizer (U : Set Y))).Normal := by
        constructor
        intro x hx g
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact (Subgroup.mem_normalizer_iff.1 g.2 x).1 hx
      have h2 : IsPGroup 2 (U.subgroupOf (normalizer (U : Set Y))) :=
        hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
      have h3 := le_pCore_two hnorm h2
      intro x hx
      have hx' : (⟨x, hle hx⟩ : normalizer (U : Set Y)) ∈ U.subgroupOf (normalizer (U : Set Y)) :=
        hx
      exact ⟨⟨x, hle hx⟩, h3 hx', rfl⟩
    have hmo : m.order = 1024 := by
      have hm' : ∀ m ∈ CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems,
          1024 ≤ m.o2 → m.order = 1024 := by
        simp [CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems]
      exact hm' m hm hUle
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hord, hmo, hUc]


open CFSG.QuasithinUnique.Setup.X1 in
theorem card_le_of_elemAbelian
    (hY : IsSporadic Y .M24)
    (B : Subgroup Y) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hs : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 64 := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.M24 := e
  have h := m24_rank_le (B.map e'.toMonoidHom) ?_ ?_
  · rw [Subgroup.card_map_of_injective e'.injective] at h
    simpa using h
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [hc x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [hs x hx, map_one]

open CFSG.QuasithinUnique.Setup.X1 in
theorem nine_dvd_card_normalizer [Finite Y]
    (hY : IsSporadic Y .M24) {A : Subgroup Y}
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hs : ∀ x ∈ A, x * x = 1) (hA : Nat.card A = 64) :
    9 ∣ Nat.card (normalizer (A : Set Y)) := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* S24 := e
  set B : Subgroup S24 := A.map e'.toMonoidHom with hBdef
  have hmemB : ∀ a : Y, a ∈ A ↔ e' a ∈ B := fun a =>
    (Subgroup.mem_map_iff_mem e'.injective).symm
  have hcB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [hc x hx y hy]
  have hsB : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [hs x hx, map_one]
  have hB : Nat.card B = 64 := by
    rw [hBdef, Subgroup.card_map_of_injective e'.injective]
    exact hA
  obtain ⟨g, hg⟩ := m24_unique64 B hcB hsB hB
  have key : ∀ (l : List S24) (x y : S24), E9Data l x y → (∀ z, z ∈ B ↔ g * z * g⁻¹ ∈ l) →
      9 ∣ Nat.card (normalizer (A : Set Y)) := by
    intro l x y hxy hl
    obtain ⟨hlen, hnd, hmul, hnorm⟩ := hxy
    obtain ⟨R, hR⟩ := exists_subgroup_of_list (nineList x y) (by simp [nineList]) hmul
    have hRc : Nat.card R = 9 := by
      rw [card_eq_length_of_list_subgroup hR hnd]
      exact hlen
    have hnorm' : ∀ r ∈ R, ∀ s, s ∈ l ↔ r * s * r⁻¹ ∈ l := by
      intro r hr s
      refine ⟨fun hs => hnorm r ((hR r).1 hr) s hs, fun hs => ?_⟩
      have := hnorm r⁻¹ ((hR r⁻¹).1 (R.inv_mem hr)) _ hs
      simpa [mul_assoc] using this
    let R' : Subgroup Y := (R.map (MulAut.conj g⁻¹).toMonoidHom).map e'.symm.toMonoidHom
    have hR'c : Nat.card R' = 9 := by
      rw [Subgroup.card_map_of_injective e'.symm.injective,
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hRc
    have hle : R' ≤ normalizer (A : Set Y) := by
      rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro a
      rw [hmemB, hmemB, hl, hl]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      have := hnorm' r hr (g * e' a * g⁻¹)
      convert this using 2
      group
    rw [← hR'c]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨hN1, hN2⟩ := Certificates.certificate24720.2
  rcases hg with hg | hg
  · exact key _ _ _ hN1 hg
  · exact key _ _ _ hN2 hg

end CFSG.EvenSporadicStandard.M24Std
