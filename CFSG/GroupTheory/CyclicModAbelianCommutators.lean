module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

private def cyclicConj {G : Type*} [Group G] {S N : Subgroup G} (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N) : ↥N →* ↥N :=
  { toFun := fun u => ⟨g * (u : G) * g⁻¹, hNn g hgS u u.2⟩
    map_one' := by ext; simp
    map_mul' := fun x y => by ext; simp [mul_assoc] }

private def cyclicDelta {G : Type*} [Group G] {N : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (c : ↥N →* ↥N) : ↥N →* ↥N := by
  letI : CommGroup ↥N :=
    { (inferInstance : Group ↥N) with
      mul_comm := fun x y => Subtype.ext (hN x x.2 y y.2) }
  exact
    { toFun := fun u => u * (c u)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }

private theorem cyclicDelta_apply {G : Type*} [Group G] {N : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (c : ↥N →* ↥N) (u : ↥N) :
    cyclicDelta hN c u = u * (c u)⁻¹ := by
  simp [cyclicDelta]

private def cyclicDeltaRange {G : Type*} [Group G] {N : Subgroup G}
    (δ : ↥N →* ↥N) : Subgroup G := δ.range.map N.subtype

private theorem conj_cyclicDelta {G : Type*} [Group G] {N : Subgroup G}
    (c : ↥N →* ↥N) (δ : ↥N →* ↥N)
    (hδ : ∀ u : ↥N, δ u = u * (c u)⁻¹) :
    ∀ u : ↥N, c (δ u) = δ (c u) := by
  intro u
  rw [hδ u, hδ (c u), map_mul, map_inv]

private def cyclicD {G : Type*} [Group G] {S N : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N) : Subgroup G :=
  cyclicDeltaRange (cyclicDelta hN (cyclicConj g hgS hNn))

private theorem conj_mem_cyclicD {G : Type*} [Group G] {S N : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N) :
    ∀ d ∈ cyclicD hN g hgS hNn, (MulAut.conj g) d ∈ cyclicD hN g hgS hNn := by
  intro d hd
  rw [cyclicD, cyclicDeltaRange] at hd ⊢
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hd
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hv
  have h1 : (MulAut.conj g) ((cyclicDelta hN (cyclicConj g hgS hNn) u : ↥N) : G) =
      ((cyclicConj g hgS hNn (cyclicDelta hN (cyclicConj g hgS hNn) u) : ↥N) : G) := by
    rw [MulAut.conj_apply]
    rfl
  change (MulAut.conj g) ((cyclicDelta hN (cyclicConj g hgS hNn) u : ↥N) : G) ∈
    (cyclicDelta hN (cyclicConj g hgS hNn)).range.map N.subtype
  rw [h1, conj_cyclicDelta (cyclicConj g hgS hNn) (cyclicDelta hN (cyclicConj g hgS hNn))
    (cyclicDelta_apply hN (cyclicConj g hgS hNn)) u]
  exact Subgroup.mem_map_of_mem N.subtype
    (MonoidHom.mem_range.mpr ⟨cyclicConj g hgS hNn u, rfl⟩)

private theorem g_mem_normalizer_cyclicD {G : Type*} [Group G] {S N : Subgroup G}
    [Finite N] (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N) :
    g ∈ Subgroup.normalizer (cyclicD hN g hgS hNn) := by
  have hDN : cyclicD hN g hgS hNn ≤ N := by
    rw [cyclicD, cyclicDeltaRange]
    exact Subgroup.map_subtype_le _
  have hDfin : Finite ↥(cyclicD hN g hgS hNn) :=
    Finite.of_injective (fun d : ↥(cyclicD hN g hgS hNn) => (⟨d.1, hDN d.2⟩ : ↥N))
      (by intro a b h; ext; exact congrArg (fun x : ↥N => (x : G)) h)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (cyclicD hN g hgS hNn).map (MulAut.conj g).toMonoidHom ≤ cyclicD hN g hgS hNn := by
    intro d hd
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hd
    exact conj_mem_cyclicD hN g hgS hNn y hy
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem N_le_normalizer_cyclicD {G : Type*} [Group G] {S N : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N) :
    N ≤ Subgroup.normalizer (cyclicD hN g hgS hNn) := by
  have hDN : cyclicD hN g hgS hNn ≤ N := by
    rw [cyclicD, cyclicDeltaRange]
    exact Subgroup.map_subtype_le _
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hcomm : n * y * n⁻¹ = y := by
      rw [hN n hn y (hDN hy)]
      group
    change n * y * n⁻¹ ∈ cyclicD hN g hgS hNn
    rw [hcomm]
    exact hy
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    have hcomm : n * x * n⁻¹ = x := by
      rw [hN n hn x (hDN hx)]
      group
    change n * x * n⁻¹ = x
    exact hcomm

private theorem S_le_normalizer_cyclicD {G : Type*} [Group G] {S N : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hgcyc : ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ N)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    (hg_norm : g ∈ Subgroup.normalizer (cyclicD hN g hgS hNn))
    (hN_norm : N ≤ Subgroup.normalizer (cyclicD hN g hgS hNn)) :
    S ≤ Subgroup.normalizer (cyclicD hN g hgS hNn) := by
  intro s hs
  obtain ⟨k, hk⟩ := hgcyc s hs
  have hgk : g ^ k ∈ Subgroup.normalizer (cyclicD hN g hgS hNn) :=
    Subgroup.zpow_mem _ hg_norm k
  have hm : g ^ k * s ∈ Subgroup.normalizer (cyclicD hN g hgS hNn) := hN_norm hk
  have hEq : s = (g ^ k)⁻¹ * (g ^ k * s) := by group
  rw [hEq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hgk) hm

private theorem cyclicD_normal {G : Type*} [Group G] {S N : Subgroup G}
    [Finite N] (hNS : N ≤ S) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (g : G) (hgS : g ∈ S) (hgcyc : ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ N)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N) :
    ((cyclicD hN g hgS hNn).subgroupOf S).Normal := by
  have hDN : cyclicD hN g hgS hNn ≤ N := by
    rw [cyclicD, cyclicDeltaRange]
    exact Subgroup.map_subtype_le _
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hDN.trans hNS)).mpr
    (S_le_normalizer_cyclicD hN g hgS hgcyc hNn
      (g_mem_normalizer_cyclicD hN g hgS hNn) (N_le_normalizer_cyclicD hN g hgS hNn))

private def cyclicQuot {G : Type*} [Group G] {S N : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    [hD : ((cyclicD hN g hgS hNn).subgroupOf S).Normal] :
    ↥S →* ↥S ⧸ (cyclicD hN g hgS hNn).subgroupOf S :=
  QuotientGroup.mk' _

private theorem quotient_g_comm_N {G : Type*} [Group G] {S N : Subgroup G}
    (hNS : N ≤ S) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    [hD : ((cyclicD hN g hgS hNn).subgroupOf S).Normal] :
    ∀ n : ↥N, Commute (cyclicQuot hN g hgS hNn (⟨g, hgS⟩ : ↥S))
      (cyclicQuot hN g hgS hNn (⟨n, hNS n.2⟩ : ↥S)) := by
  intro n
  let c := cyclicConj g hgS hNn
  let δ := cyclicDelta hN c
  let D := cyclicD hN g hgS hNn
  let π := cyclicQuot hN g hgS hNn
  let nS : ↥S := ⟨n, hNS n.2⟩
  let x : ↥S := ⟨g * (n : G) * g⁻¹ * (n : G)⁻¹, by
    exact S.mul_mem (S.mul_mem (S.mul_mem hgS (hNS n.2)) (S.inv_mem hgS))
      (S.inv_mem (hNS n.2))⟩
  have hxeq : x = (⟨g, hgS⟩ : ↥S) * nS * (⟨g, hgS⟩ : ↥S)⁻¹ * nS⁻¹ := rfl
  have hDmem : ((δ n)⁻¹ : ↥N) ∈ δ.range :=
    Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨n, rfl⟩)
  have hG : N.subtype ((δ n)⁻¹) ∈ D := Subgroup.mem_map_of_mem N.subtype hDmem
  have hcoe : N.subtype ((δ n)⁻¹) = g * (n : G) * g⁻¹ * (n : G)⁻¹ := by
    rw [cyclicDelta_apply hN c n]
    change (((n * (c n)⁻¹ : ↥N) : G))⁻¹ = g * (n : G) * g⁻¹ * (n : G)⁻¹
    rw [show ((n * (c n)⁻¹ : ↥N) : G) = (n : G) * (g * (n : G) * g⁻¹)⁻¹ from rfl]
    group
  have hmem : x ∈ D.subgroupOf S := by
    rw [Subgroup.mem_subgroupOf]
    change g * (n : G) * g⁻¹ * (n : G)⁻¹ ∈ D
    rw [← hcoe]
    exact hG
  have h1 : π x = 1 := by
    change QuotientGroup.mk x = 1
    exact (QuotientGroup.eq_one_iff x).mpr hmem
  have h2 : π (⟨g, hgS⟩ : ↥S) * π nS * (π (⟨g, hgS⟩ : ↥S))⁻¹ * (π nS)⁻¹ = 1 := by
    have hx : π x = π (⟨g, hgS⟩ : ↥S) * π nS * (π (⟨g, hgS⟩ : ↥S))⁻¹ * (π nS)⁻¹ := by
      rw [hxeq]
      simp only [map_mul, map_inv]
    rwa [← hx]
  show π (⟨g, hgS⟩ : ↥S) * π nS = π nS * π (⟨g, hgS⟩ : ↥S)
  calc
    π (⟨g, hgS⟩ : ↥S) * π nS =
        (π (⟨g, hgS⟩ : ↥S) * π nS * (π (⟨g, hgS⟩ : ↥S))⁻¹ * (π nS)⁻¹) *
          (π nS * π (⟨g, hgS⟩ : ↥S)) := by group
    _ = 1 * (π nS * π (⟨g, hgS⟩ : ↥S)) := by rw [h2]
    _ = π nS * π (⟨g, hgS⟩ : ↥S) := by simp

private theorem quotient_N_comm {G : Type*} [Group G] {S N : Subgroup G}
    (hNS : N ≤ S) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    [hD : ((cyclicD hN g hgS hNn).subgroupOf S).Normal] :
    ∀ m n : ↥N, Commute (cyclicQuot hN g hgS hNn (⟨m, hNS m.2⟩ : ↥S))
      (cyclicQuot hN g hgS hNn (⟨n, hNS n.2⟩ : ↥S)) := by
  intro m n
  show cyclicQuot hN g hgS hNn (⟨m, hNS m.2⟩ : ↥S) *
      cyclicQuot hN g hgS hNn (⟨n, hNS n.2⟩ : ↥S) =
    cyclicQuot hN g hgS hNn (⟨n, hNS n.2⟩ : ↥S) *
      cyclicQuot hN g hgS hNn (⟨m, hNS m.2⟩ : ↥S)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hN m m.2 n n.2)

private theorem quotient_commutative {G : Type*} [Group G] {S N : Subgroup G}
    (hNS : N ≤ S) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hgcyc : ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ N)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    [hD : ((cyclicD hN g hgS hNn).subgroupOf S).Normal]
    (hqg : ∀ n : ↥N, Commute (cyclicQuot hN g hgS hNn (⟨g, hgS⟩ : ↥S))
      (cyclicQuot hN g hgS hNn (⟨n, hNS n.2⟩ : ↥S)))
    (hNN : ∀ m n : ↥N, Commute (cyclicQuot hN g hgS hNn (⟨m, hNS m.2⟩ : ↥S))
      (cyclicQuot hN g hgS hNn (⟨n, hNS n.2⟩ : ↥S))) :
    ∀ x y : ↥S, cyclicQuot hN g hgS hNn (x * y) =
      cyclicQuot hN g hgS hNn (y * x) := by
  intro x y
  let π := cyclicQuot hN g hgS hNn
  let gS : ↥S := ⟨g, hgS⟩
  obtain ⟨kx, hkx⟩ := hgcyc x x.2
  obtain ⟨ky, hky⟩ := hgcyc y y.2
  let mx : ↥N := ⟨g ^ kx * x, hkx⟩
  let my : ↥N := ⟨g ^ ky * y, hky⟩
  have hx : x = gS ^ (-kx) * ⟨mx, hNS mx.2⟩ := by
    apply Subtype.ext
    change (x : G) = g ^ (-kx) * (g ^ kx * (x : G))
    group
  have hy : y = gS ^ (-ky) * ⟨my, hNS my.2⟩ := by
    apply Subtype.ext
    change (y : G) = g ^ (-ky) * (g ^ ky * (y : G))
    group
  have hxπ : π x = π gS ^ (-kx) * π ⟨mx, hNS mx.2⟩ := by
    rw [hx, map_mul, map_zpow]
  have hyπ : π y = π gS ^ (-ky) * π ⟨my, hNS my.2⟩ := by
    rw [hy, map_mul, map_zpow]
  have hcomm_prod : Commute (π gS ^ (-kx) * π ⟨mx, hNS mx.2⟩)
      (π gS ^ (-ky) * π ⟨my, hNS my.2⟩) := by
    have h1 : Commute (π gS ^ (-kx)) (π gS ^ (-ky)) := Commute.zpow_zpow_self _ _ _
    have h2 : Commute (π ⟨mx, hNS mx.2⟩) (π gS ^ (-ky)) :=
      (hqg mx).symm.zpow_right (-ky)
    have h3 : Commute (π gS ^ (-kx)) (π ⟨my, hNS my.2⟩) := (hqg my).zpow_left (-kx)
    have h4 : Commute (π ⟨mx, hNS mx.2⟩) (π ⟨my, hNS my.2⟩) := hNN mx my
    exact (h1.mul_left h2).mul_right (h3.mul_left h4)
  calc
    π (x * y) = π x * π y := map_mul π x y
    _ = (π gS ^ (-kx) * π ⟨mx, hNS mx.2⟩) * (π gS ^ (-ky) * π ⟨my, hNS my.2⟩) := by
      rw [hxπ, hyπ]
    _ = (π gS ^ (-ky) * π ⟨my, hNS my.2⟩) * (π gS ^ (-kx) * π ⟨mx, hNS mx.2⟩) :=
      hcomm_prod.eq
    _ = π y * π x := by rw [hyπ, hxπ]
    _ = π (y * x) := (map_mul π y x).symm

private theorem commutators_mem_cyclicD {G : Type*} [Group G] {S N V : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    [hD : ((cyclicD hN g hgS hNn).subgroupOf S).Normal]
    (hVc : ∀ v ∈ V, ∃ x ∈ S, ∃ y ∈ S, v = x * y⁻¹ * x⁻¹ * y)
    (hcomm_Q : ∀ x y : ↥S, cyclicQuot hN g hgS hNn (x * y) =
      cyclicQuot hN g hgS hNn (y * x)) :
    V ≤ cyclicD hN g hgS hNn := by
  intro v hv
  obtain ⟨x, hxS, y, hyS, hvxy⟩ := hVc v hv
  have hvS : v ∈ S := by
    rw [hvxy]
    exact S.mul_mem (S.mul_mem (S.mul_mem hxS (S.inv_mem hyS)) (S.inv_mem hxS)) hyS
  let xS : ↥S := ⟨x, hxS⟩
  let yS : ↥S := ⟨y, hyS⟩
  let vS : ↥S := ⟨v, hvS⟩
  have hvS_eq : vS = xS * yS⁻¹ * xS⁻¹ * yS := by
    apply Subtype.ext
    change v = x * y⁻¹ * x⁻¹ * y
    exact hvxy
  have hcommxy : Commute (cyclicQuot hN g hgS hNn xS) (cyclicQuot hN g hgS hNn yS) := by
    show cyclicQuot hN g hgS hNn xS * cyclicQuot hN g hgS hNn yS =
      cyclicQuot hN g hgS hNn yS * cyclicQuot hN g hgS hNn xS
    have h := hcomm_Q xS yS
    rwa [map_mul, map_mul] at h
  have hπv : cyclicQuot hN g hgS hNn vS = 1 := by
    rw [hvS_eq, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hinv : Commute (cyclicQuot hN g hgS hNn xS)
        ((cyclicQuot hN g hgS hNn yS)⁻¹) := hcommxy.inv_right
    calc
      cyclicQuot hN g hgS hNn xS * (cyclicQuot hN g hgS hNn yS)⁻¹ *
          (cyclicQuot hN g hgS hNn xS)⁻¹ * cyclicQuot hN g hgS hNn yS =
          (cyclicQuot hN g hgS hNn xS * (cyclicQuot hN g hgS hNn yS)⁻¹) *
            (cyclicQuot hN g hgS hNn xS)⁻¹ * cyclicQuot hN g hgS hNn yS := by group
      _ = ((cyclicQuot hN g hgS hNn yS)⁻¹ * cyclicQuot hN g hgS hNn xS) *
            (cyclicQuot hN g hgS hNn xS)⁻¹ * cyclicQuot hN g hgS hNn yS := by rw [hinv.eq]
      _ = 1 := by group
  have hmem : vS ∈ (cyclicD hN g hgS hNn).subgroupOf S := by
    change QuotientGroup.mk vS = 1 at hπv
    exact (QuotientGroup.eq_one_iff vS).mp hπv
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem delta_mem_Z {G : Type*} [Group G] {S N Z : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    (hZ : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z) :
    ∀ z : ↥N, z ∈ Z.subgroupOf N → cyclicDelta hN (cyclicConj g hgS hNn) z = 1 := by
  intro z hz
  have hzZ : ((z : ↥N) : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
  apply Subtype.ext
  rw [cyclicDelta_apply hN (cyclicConj g hgS hNn) z]
  change (z : G) * (g * (z : G) * g⁻¹)⁻¹ = 1
  have hcomm : g * (z : G) * g⁻¹ = (z : G) := by
    rw [← hZ ((z : ↥N) : G) hzZ g hgS]
    group
  rw [hcomm]
  group

private theorem delta_preimage_surjective {G : Type*} [Group G] {S N V : Subgroup G}
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    (hVD : V ≤ cyclicD hN g hgS hNn) :
    ∀ v ∈ V.subgroupOf N,
      ∃ w ∈ (V.subgroupOf N).comap (cyclicDelta hN (cyclicConj g hgS hNn)),
        cyclicDelta hN (cyclicConj g hgS hNn) w = v := by
  intro v hv
  have hvV : ((v : ↥N) : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
  have hvD : ((v : ↥N) : G) ∈ cyclicD hN g hgS hNn := hVD hvV
  rw [cyclicD, cyclicDeltaRange] at hvD
  obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hvD
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hw
  have hwv' : w = v := Subtype.ext hwv
  refine ⟨u, ?_, ?_⟩
  · rw [Subgroup.mem_comap, hu, hwv']
    exact hv
  · rw [hu, hwv']

private def deltaW {N : Type*} [Group N] (δ : N →* N) (V : Subgroup N) :
    ↥(V.comap δ) →* ↥V :=
  { toFun := fun w => ⟨δ (w : N), w.2⟩
    map_one' := by ext; simp
    map_mul' := fun x y => by ext; simp [map_mul] }

private theorem deltaW_ker {N : Type*} [Group N] (δ : N →* N) {V Z : Subgroup N}
    (hZV : Z ≤ δ.ker) : Z.subgroupOf (V.comap δ) ≤ (deltaW δ V).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  exact MonoidHom.mem_ker.mp (hZV (Subgroup.mem_subgroupOf.mp hz))

private def deltaQuotient {N : Type*} [Group N] (δ : N →* N) (V Z : Subgroup N)
    (hZV : Z ≤ δ.ker) [(Z.subgroupOf (V.comap δ)).Normal] :
    (↥(V.comap δ) ⧸ (Z.subgroupOf (V.comap δ))) →* ↥V :=
  QuotientGroup.lift _ (deltaW δ V) (deltaW_ker δ hZV)

private theorem deltaQuotient_surjective {N : Type*} [Group N] (δ : N →* N) {V Z : Subgroup N}
    (hZV : Z ≤ δ.ker) [(Z.subgroupOf (V.comap δ)).Normal]
    (hVrange : V ≤ δ.range) : Function.Surjective (deltaQuotient δ V Z hZV) := by
  intro v
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (hVrange v.2)
  refine ⟨QuotientGroup.mk' (Z.subgroupOf (V.comap δ)) ⟨w, ?_⟩, ?_⟩
  · rw [Subgroup.mem_comap]
    rw [hw]
    exact v.2
  · rw [deltaQuotient, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
    apply Subtype.ext
    exact hw

private theorem deltaQuotient_power {N : Type*} [CommGroup N] {p : ℕ} (δ : N →* N)
    {V Z : Subgroup N} (hZV : Z ≤ δ.ker) [(Z.subgroupOf (V.comap δ)).Normal]
    (hV : ∀ v ∈ V, v ^ p = 1) :
    ∀ b : (↥(V.comap δ) ⧸ (Z.subgroupOf (V.comap δ))),
      deltaQuotient δ V Z hZV (powMonoidHom p b) = 1 := by
  intro b
  change deltaQuotient δ V Z hZV (b ^ p) = 1
  rw [map_pow]
  apply Subtype.ext
  exact hV ((deltaQuotient δ V Z hZV b : ↥V) : N)
    (deltaQuotient δ V Z hZV b).2

private theorem card_le_target_of_delta {N : Type*} [CommGroup N] [Finite N] {p : ℕ}
    (W : Subgroup N) (Z : Subgroup N)
    [(Z.subgroupOf W).Normal]
    (f : (↥W ⧸ (Z.subgroupOf W)) →* (↥W ⧸ (Z.subgroupOf W)))
    (hf : ∀ b, f b = b ^ p) :
    Nat.card ↥(f.ker.comap (QuotientGroup.mk' (Z.subgroupOf W))) ≤
      Nat.card {u : N // u ^ p ∈ Z} := by
  haveI : Finite {u : N // u ^ p ∈ Z} := Subtype.finite
  refine Nat.card_le_card_of_injective
    (fun k : ↥(f.ker.comap (QuotientGroup.mk' (Z.subgroupOf W))) =>
      ⟨((k : ↥W) : N), ?_⟩) ?_
  · have hk : (QuotientGroup.mk' (Z.subgroupOf W)) (k : ↥W) ∈ f.ker := k.2
    have hpow : ((QuotientGroup.mk' (Z.subgroupOf W)) (k : ↥W)) ^ p = 1 := by
      rw [← hf]
      exact hk
    have hmemZ : (k : ↥W) ^ p ∈ Z.subgroupOf W := by
      refine (QuotientGroup.eq_one_iff ((k : ↥W) ^ p)).mp ?_
      change (QuotientGroup.mk' (Z.subgroupOf W)) ((k : ↥W) ^ p) = 1
      rw [map_pow]
      exact hpow
    exact Subgroup.mem_subgroupOf.mp (by simpa [Subgroup.coe_pow] using hmemZ)
  · intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {u : N // u ^ p ∈ Z} => x.1) h

private theorem card_comap_mk'_ker {W : Type*} [Group W] (Z : Subgroup W) [Z.Normal]
    (f : W ⧸ Z →* W ⧸ Z) :
    Nat.card ↥(f.ker.comap (QuotientGroup.mk' Z)) = Nat.card ↥f.ker * Nat.card ↥Z := by
  have h := QuotientGroup.card_preimage_mk Z (f.ker : Set (W ⧸ Z))
  have hEq : Nat.card ↥(f.ker.comap (QuotientGroup.mk' Z)) =
      Nat.card ↑(QuotientGroup.mk ⁻¹' (f.ker : Set (W ⧸ Z))) := by
    congr 1
  rw [hEq, h, Nat.mul_comm]
  congr 1

private theorem card_le_ker_of_range_le {B V : Type*} [Group B] [Group V] [Finite B]
    (ψ : B →* V) (hψ : Function.Surjective ψ) (f : B →* B)
    (h : f.range ≤ ψ.ker) : Nat.card V ≤ Nat.card f.ker := by
  have hBψ := Subgroup.card_ker_mul_card_of_surjective hψ
  have hBf := Subgroup.card_ker_mul_card_range f
  have hfr : Nat.card ↥f.range ≤ Nat.card ↥ψ.ker := Subgroup.card_le_of_le h
  have h1 : Nat.card V * Nat.card ↥ψ.ker = Nat.card ↥f.ker * Nat.card ↥f.range := by
    rw [Nat.mul_comm (Nat.card V) (Nat.card ↥ψ.ker), hBψ, hBf]
  have h2 : Nat.card V * Nat.card ↥ψ.ker ≤ Nat.card ↥f.ker * Nat.card ↥ψ.ker := by
    rw [h1]
    exact Nat.mul_le_mul_left _ hfr
  exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos

private theorem card_mul_card_le_of_delta {N : Type*} [CommGroup N] [Finite N] {p : ℕ}
    (δ : N →* N) {V Z : Subgroup N}
    (hV : ∀ v ∈ V, v ^ p = 1)
    (hZV : Z ≤ δ.ker) (hVrange : V ≤ δ.range) :
    Nat.card V * Nat.card Z ≤ Nat.card {u : N // u ^ p ∈ Z} := by
  let W : Subgroup N := V.comap δ
  have hZW : Z ≤ W := by
    intro z hz
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.mp (hZV hz)]
    exact V.one_mem
  let ψ : (↥W ⧸ (Z.subgroupOf W)) →* ↥V := deltaQuotient δ V Z hZV
  let f : (↥W ⧸ (Z.subgroupOf W)) →* (↥W ⧸ (Z.subgroupOf W)) := powMonoidHom p
  have hψ_surj : Function.Surjective ψ := deltaQuotient_surjective δ hZV hVrange
  have hψf : ∀ b, ψ (f b) = 1 := deltaQuotient_power δ hZV hV
  have hfr_le : f.range ≤ ψ.ker := by
    rintro y hy
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [MonoidHom.mem_ker]
    exact hψf b
  have hV_le_fker : Nat.card ↥V ≤ Nat.card ↥f.ker :=
    card_le_ker_of_range_le ψ hψ_surj f hfr_le
  let K : Subgroup ↥W := f.ker.comap (QuotientGroup.mk' (Z.subgroupOf W))
  have hKcard : Nat.card ↥K = Nat.card ↥f.ker * Nat.card ↥Z := by
    rw [card_comap_mk'_ker (Z.subgroupOf W) f]
    have hZWcard : Nat.card ↥(Z.subgroupOf W) = Nat.card ↥Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
    rw [hZWcard]
  have hKle : Nat.card ↥K ≤ Nat.card {u : N // u ^ p ∈ Z} :=
    card_le_target_of_delta W Z f (fun b => rfl)
  calc
    Nat.card V * Nat.card Z ≤ Nat.card ↥f.ker * Nat.card ↥Z :=
      Nat.mul_le_mul_right _ hV_le_fker
    _ = Nat.card ↥K := hKcard.symm
    _ ≤ Nat.card {u : N // u ^ p ∈ Z} := hKle

private def targetEquiv {G : Type*} [Group G] {N Z : Subgroup G} (p : ℕ) :
    {u : ↥N // u ^ p ∈ Z.subgroupOf N} ≃ {u : G // u ∈ N ∧ u ^ p ∈ Z} :=
  { toFun := fun u => ⟨u.1.1, u.1.2, by
      have h := u.2
      rw [Subgroup.mem_subgroupOf] at h
      simpa [Subgroup.coe_pow] using h⟩
    invFun := fun u => ⟨⟨u.1, u.2.1⟩, by
      rw [Subgroup.mem_subgroupOf]
      simpa [Subgroup.coe_pow] using u.2.2⟩
    left_inv := fun u => by ext; rfl
    right_inv := fun u => by ext; rfl }

private theorem delta_count_conclusion {G : Type*} [Group G] {S N Z V : Subgroup G} [Finite N]
    (p : ℕ) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) (hgS : g ∈ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N)
    (hV : ∀ v ∈ V, v ^ p = 1)
    (hZ : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z)
    (hZN : Z ≤ N) (hVD : V ≤ cyclicD hN g hgS hNn) :
    Nat.card V * Nat.card Z ≤ Nat.card {u : G // u ∈ N ∧ u ^ p ∈ Z} := by
  letI : CommGroup ↥N :=
    { (inferInstance : Group ↥N) with
      mul_comm := fun x y => Subtype.ext (hN x x.2 y y.2) }
  let δ := cyclicDelta hN (cyclicConj g hgS hNn)
  have hVexp : ∀ v ∈ V.subgroupOf N, v ^ p = 1 := by
    intro v hv
    have hvV : ((v : ↥N) : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hV ((v : ↥N) : G) hvV
  have hZV : Z.subgroupOf N ≤ δ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    exact delta_mem_Z hN g hgS hNn hZ z hz
  have hVrange : V.subgroupOf N ≤ δ.range := by
    intro v hv
    obtain ⟨w, _, hw⟩ := delta_preimage_surjective hN g hgS hNn hVD v hv
    exact MonoidHom.mem_range.mpr ⟨w, hw⟩
  have hcount := card_mul_card_le_of_delta (N := ↥N) (p := p) δ hVexp hZV hVrange
  have hDN : cyclicD hN g hgS hNn ≤ N := by
    rw [cyclicD, cyclicDeltaRange]
    exact Subgroup.map_subtype_le _
  have hVN : V ≤ N := hVD.trans hDN
  have hVNcard : Nat.card ↥(V.subgroupOf N) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
  have hZNcard : Nat.card ↥(Z.subgroupOf N) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv
  rw [hVNcard, hZNcard] at hcount
  have hset : Nat.card {u : ↥N // u ^ p ∈ Z.subgroupOf N} =
      Nat.card {u : G // u ∈ N ∧ u ^ p ∈ Z} :=
    Nat.card_congr (targetEquiv (G := G) (N := N) (Z := Z) p)
  rw [hset] at hcount
  exact hcount

theorem card_mul_card_le_of_commutator_of_cyclic {G : Type*} [Group G] {p : ℕ}
    {S N Z V : Subgroup G} [Finite N] (hNS : N ≤ S)
    (hNn : ∀ s ∈ S, ∀ u ∈ N, s * u * s⁻¹ ∈ N) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ N)
    (hZN : Z ≤ N) (hZ : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z) (hV : ∀ v ∈ V, v ^ p = 1)
    (hVc : ∀ v ∈ V, ∃ x ∈ S, ∃ y ∈ S, v = x * y⁻¹ * x⁻¹ * y) :
    Nat.card V * Nat.card Z ≤ Nat.card {u : G // u ∈ N ∧ u ^ p ∈ Z} := by
  classical
  obtain ⟨g, hgS, hgcyc⟩ := hcyc
  haveI hDnormal : ((cyclicD hN g hgS hNn).subgroupOf S).Normal :=
    cyclicD_normal hNS hN g hgS hgcyc hNn
  have hqg := quotient_g_comm_N hNS hN g hgS hNn
  have hNN := quotient_N_comm hNS hN g hgS hNn
  have hcomm_Q := quotient_commutative hNS hN g hgS hgcyc hNn hqg hNN
  have hVD : V ≤ cyclicD hN g hgS hNn :=
    commutators_mem_cyclicD hN g hgS hNn hVc hcomm_Q
  exact delta_count_conclusion p hN g hgS hNn hV hZ hZN hVD

end CFSG.GroupTheory
