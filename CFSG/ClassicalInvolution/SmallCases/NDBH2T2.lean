module

public import CFSG.ClassicalInvolution.SmallCases.NDB1Main
public import CFSG.ClassicalInvolution.SmallCases.NDBG8

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ComponentClassification

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBH2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem axisSeed_of_triangle {Ω : Set (Subgroup G)} {z : G} (C : Asc77.XCtx p f Ω z)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {N N' : Subgroup G}
    (hN : N ∈ tqMembers Ω z) (hN' : N' ∈ tqMembers Ω z) {n n' : G}
    (hn : IsClassicalMember p f N n) (hn' : IsClassicalMember p f N' n') (hnz : n ≠ z)
    (hn'z : n' ≠ z) (hne : modOdd z (exactCore z N') ≠ modOdd z (exactCore z N))
    (hprod : ∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
      (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) :
    AxisSeed p f Ω C.K z N N' n n' := by
  obtain ⟨jK, eK⟩ := NDBG.exists_range_eq C hall C.K_tq
  obtain ⟨jN, eN⟩ := NDBG.exists_range_eq C hall hN
  obtain ⟨jN', eN'⟩ := NDBG.exists_range_eq C hall hN'
  have hKimg : modOdd z C.K = (C.psi jK).range := by rw [← eK, C.exactCore_K]
  have hdist : ∀ {M : Subgroup G} {m : G} (hM : M ∈ tqMembers Ω z)
      (hm : IsClassicalMember p f M m), m ≠ z → ∀ {j : Fin C.D.card},
        modOdd z (exactCore z M) = (C.psi j).range → jK ≠ j := by
    intro M m hM hm hmz j ej hj
    subst hj
    apply NDBG.nbar_ne_zbar C hM hm hmz
    have u₁ := C.isUniqueInvolution_modOdd hM hm
    have u₂ := C.isUniqueInvolution_modOdd C.K_tq C.K_cl
    rw [ej] at u₁
    rw [eK] at u₂
    exact u₁.eq u₂
  have hKN := hdist hN hn hnz eN
  have hKN' := hdist hN' hn' hn'z eN'
  have hNN' : jN ≠ jN' := fun h => hne (by rw [eN', eN, h])
  have hcomm : ∀ {j j' : Fin C.D.card}, j ≠ j' → ∀ a ∈ (C.psi j).range,
      ∀ b ∈ (C.psi j').range, a * b = b * a := by
    rintro j j' hjj' _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact C.psi_commute hjj' a b
  obtain ⟨h, h', hp⟩ := hprod
  refine ⟨hN, hN', hn, hn', ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [hKimg] at ha
    rw [eN] at hb
    exact hcomm hKN a ha b hb
  · intro a ha b hb
    rw [hKimg] at ha
    rw [eN'] at hb
    exact hcomm hKN' a ha b hb
  · intro a ha b hb
    rw [eN] at ha
    rw [eN'] at hb
    exact hcomm hNN' a ha b hb
  · intro h₁ h₂ h₃
    have hn2 : oddQuotMk z ⟨n, h₂⟩ * oddQuotMk z ⟨n, h₂⟩ = 1 := by
      rw [← map_mul]
      have e : (⟨n, h₂⟩ * ⟨n, h₂⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
        Subtype.ext hn.isCentralInvolution.sq
      rw [e, map_one]
    have hzn : oddQuotMk z ⟨z, h₁⟩ * oddQuotMk z ⟨n, h₂⟩ =
        oddQuotMk z ⟨n, h₂⟩ * oddQuotMk z ⟨z, h₁⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h₂).symm
    have hp' : oddQuotMk z ⟨n, h₂⟩ * oddQuotMk z ⟨n', h₃⟩ = oddQuotMk z ⟨z, h₁⟩ := hp
    calc oddQuotMk z ⟨z, h₁⟩ * oddQuotMk z ⟨n, h₂⟩ =
          oddQuotMk z ⟨n, h₂⟩ * oddQuotMk z ⟨z, h₁⟩ := hzn
      _ = oddQuotMk z ⟨n, h₂⟩ * (oddQuotMk z ⟨n, h₂⟩ * oddQuotMk z ⟨n', h₃⟩) := by rw [hp']
      _ = oddQuotMk z ⟨n', h₃⟩ := by rw [← mul_assoc, hn2, one_mul]

theorem not_hasTwin_unique (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hnt : ¬ HasTwin p f K z) : ¬ AscHypOmega.HasTwin K z := by
  rintro ⟨K₁, ⟨g, rfl⟩, hne, hu⟩
  apply hnt
  refine ⟨conjSub g K, ⟨g, rfl⟩, hne, ?_⟩
  have hzg : g * z * g⁻¹ = z :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hz.conj g)).eq hu
  have h := hz.conj g
  rwa [hzg] at h

theorem eq_of_isClassicalMember (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hnt : ¬ HasTwin p f K z) {M M' : Subgroup G}
    (hM : M ∈ 𝒞 K) (hM' : M' ∈ 𝒞 K) {x : G} (hx : IsClassicalMember p f M x)
    (hx' : IsClassicalMember p f M' x) : M = M' := by
  obtain ⟨g, rfl⟩ := hM'
  have hxg : x = g * z * g⁻¹ :=
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hx').eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hz.conj g))
  subst hxg
  obtain ⟨h, rfl⟩ := hM
  by_contra hne
  apply hnt
  refine ⟨conjSub (g⁻¹ * h) K, ⟨g⁻¹ * h, rfl⟩, fun he => hne ?_, ?_⟩
  · calc conjSub h K = conjSub g (conjSub (g⁻¹ * h) K) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
      _ = conjSub g K := by rw [he]
  · have h1 := hx.conj g⁻¹
    rwa [← conjSub_mul, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h1

theorem mem_tqMembers_of_mem_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : Asc77.HypOmegaMod p f Ω) {L L' : Subgroup G} (hL : L ∈ Ω)
    (hN : L' ∈ Asc77.omegaNbr Ω L) {x : G} (hx : IsClassicalMember p f L x) :
    L' ∈ tqMembers Ω x := by
  obtain ⟨a, ha, htq⟩ := Disconnected.tq_of_mem_omegaNbr hp hq hΩ.classical hL hN
  have hax : a = x := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hx)
  subst hax
  exact ⟨hN.1, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩

theorem eq_or_eq_mul_of_mem {Ω : Set (Subgroup G)} {z : G} (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {L J : Subgroup G}
    (hL : L ∈ tqMembers Ω z) (hJ : J ∈ tqMembers Ω z) {l w : G}
    (hl : IsClassicalMember p f L l) (hw : IsClassicalMember p f J w) (hlz : l ≠ z)
    (hwz : w ≠ z) {T : Subgroup G} (hT : IsPGroup 2 T) (hlT : l ∈ T) (hwT : w ∈ T)
    (hzT : z ∈ T) : l = w ∨ l = z * w := by
  have hlC : l ∈ Subgroup.centralizer ({z} : Set G) := C.involution_mem_centralizer hL hl
  have hwC : w ∈ Subgroup.centralizer ({z} : Set G) := C.involution_mem_centralizer hJ hw
  have hzC := Asc77.XCtx.hzC z
  have hTc2 : IsPGroup 2 (T.subgroupOf (Subgroup.centralizer ({z} : Set G))) :=
    hT.comap_subtype
  have hmem : ∀ {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)), y ∈ T →
      y ∈ (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype := fun {y} hy hyT =>
    ⟨⟨y, hy⟩, hyT, rfl⟩
  have hzwC : z * w ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hzC hwC
  have hw2 : oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨w, hwC⟩ = 1 := by
    rw [← map_mul]
    have e : (⟨w, hwC⟩ * ⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext hw.isCentralInvolution.sq
    rw [e, map_one]
  rcases NDBG.nbar_eq_or_mul_eq C hnoF hall hL hJ hl hw hlz hwz with h | h
  · exact Or.inl (Axis.eq_of_mem_map hTc2 (hmem hlC hlT) (hmem hwC hwT) fun _ _ => h)
  · refine Or.inr (Axis.eq_of_mem_map hTc2 (hmem hlC hlT)
      (hmem hzwC (Subgroup.mul_mem _ hzT hwT)) fun ha hb => ?_)
    calc oddQuotMk z ⟨l, ha⟩ =
          oddQuotMk z ⟨l, hlC⟩ * oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨w, hwC⟩ := by
          rw [mul_assoc, hw2, mul_one]
      _ = oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨w, hwC⟩ := by rw [h]
      _ = oddQuotMk z ⟨z * w, hb⟩ := (map_mul (oddQuotMk z) ⟨z, hzC⟩ ⟨w, hwC⟩).symm

theorem eq_or_eq_mul_of_conj {K : Subgroup G} {z : G} (C : Asc77.XCtx p f (𝒞 K) z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {g x : G} (hx : x = g * z * g⁻¹)
    {L J : Subgroup G} (hL : L ∈ tqMembers (𝒞 K) x) (hJ : J ∈ tqMembers (𝒞 K) x) {l w : G}
    (hl : IsClassicalMember p f L l) (hw : IsClassicalMember p f J w) (hlx : l ≠ x)
    (hwx : w ≠ x) {T : Subgroup G} (hT : IsPGroup 2 T) (hlT : l ∈ T) (hwT : w ∈ T)
    (hxT : x ∈ T) : l = w ∨ l = x * w := by
  subst hx
  rw [tqMembers_conj C.hΩ.conjInvariant] at hL hJ
  obtain ⟨L₀, hL₀, rfl⟩ := hL
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  have hl₀ : IsClassicalMember p f L₀ (g⁻¹ * l * g) := by
    have h1 := hl.conj g⁻¹
    rwa [conjSub_inv_conjSub, inv_inv] at h1
  have hw₀ : IsClassicalMember p f J₀ (g⁻¹ * w * g) := by
    have h1 := hw.conj g⁻¹
    rwa [conjSub_inv_conjSub, inv_inv] at h1
  have hl₀z : g⁻¹ * l * g ≠ z := fun h => hlx (by rw [← h]; group)
  have hw₀z : g⁻¹ * w * g ≠ z := fun h => hwx (by rw [← h]; group)
  have hmemT : ∀ {y : G}, y ∈ T → g⁻¹ * y * g ∈ conjSub g⁻¹ T := fun {y} hy => by
    have h1 := conj_mem_conjSub (n := g⁻¹) hy
    rwa [inv_inv] at h1
  have hzT₀ : z ∈ conjSub g⁻¹ T := by
    have h1 := hmemT hxT
    rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h1
  rcases eq_or_eq_mul_of_mem C hnoF hall hL₀ hJ₀ hl₀ hw₀ hl₀z hw₀z
      (Asc77.isPGroup_conjSub g⁻¹ hT) (hmemT hlT) (hmemT hwT) hzT₀ with h | h
  · left
    calc l = g * (g⁻¹ * l * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [h]
      _ = w := by group
  · right
    calc l = g * (g⁻¹ * l * g) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * w := by group

end NDBH2

end CFSG.ClassicalInvolution.NDB
