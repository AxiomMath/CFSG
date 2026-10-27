module

public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnGamma

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b CFSG.GH74.GLS.Stage1.Thm6.Sec14

section Quot

variable {C' : Type} [Group C']

theorem mem_zpowers_sq {z y : C'} (hz2 : z * z = 1) :
    y ∈ Subgroup.zpowers z ↔ y = 1 ∨ y = z := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
    have hk : z ^ k = z ^ (k % 2) := zpow_eq_zpow_emod k h2
    show z ^ k = 1 ∨ z ^ k = z
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [hk, h]; simp
    · right; rw [hk, h]; simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

abbrev piZ (z : C') [(Subgroup.zpowers z).Normal] : C' →* C' ⧸ Subgroup.zpowers z :=
  QuotientGroup.mk' (Subgroup.zpowers z)

variable {z : C'} [(Subgroup.zpowers z).Normal]

theorem piZ_eq_iff {a b : C'} : piZ z a = piZ z b ↔ a⁻¹ * b ∈ Subgroup.zpowers z :=
  QuotientGroup.eq

theorem piZ_eq_iff_sq (hz2 : z * z = 1) {a b : C'} : piZ z a = piZ z b ↔ b = a ∨ b = a * z := by
  rw [piZ_eq_iff, mem_zpowers_sq hz2]
  constructor
  · rintro (h | h)
    · left; exact (inv_mul_eq_one.1 h).symm
    · right; rw [← h]; group
  · rintro (h | h)
    · left; rw [h]; group
    · right; rw [h]; group

theorem comap_map_piZ {K : Subgroup C'} (hK : Subgroup.zpowers z ≤ K) :
    (K.map (piZ z)).comap (piZ z) = K := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hK]

theorem mem_map_piZ {K : Subgroup C'} (hK : Subgroup.zpowers z ≤ K) {a : C'} :
    piZ z a ∈ K.map (piZ z) ↔ a ∈ K := by
  rw [← Subgroup.mem_comap, comap_map_piZ hK]

theorem card_map_piZ [Finite C'] (hz2 : z * z = 1) (hz1 : z ≠ 1) {K : Subgroup C'}
    (hK : Subgroup.zpowers z ≤ K) : 2 * Nat.card (K.map (piZ z)) = Nat.card K := by
  let f : ↥K →* C' ⧸ Subgroup.zpowers z := (piZ z).comp K.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card f.ker = 2 := by
    have : Nat.card f.ker = Nat.card (Subgroup.zpowers z) := by
      refine Nat.card_congr
        { toFun := fun k => ⟨(k.1 : C'), by
            have := MonoidHom.mem_ker.1 k.2
            simpa [f, QuotientGroup.eq_one_iff] using this⟩
          invFun := fun y => ⟨⟨y.1, hK y.2⟩, by
            simp [f, QuotientGroup.eq_one_iff]⟩
          left_inv := fun k => rfl
          right_inv := fun y => rfl }
    rw [this, card_zpowers_of_sq hz2 hz1]
  have hrange : f.range = K.map (piZ z) := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [hker, hrange] at h1
  exact h1


theorem map_mem_normalizer {K : Subgroup C'} (hK : Subgroup.zpowers z ≤ K) {g : C'}
    (hg : g ∈ Subgroup.normalizer (K : Set C')) :
    piZ z g ∈ Subgroup.normalizer ((K.map (piZ z) : Subgroup _) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [mem_map_piZ hK, ← map_inv, ← map_mul, ← map_mul, mem_map_piZ hK]
  exact Subgroup.mem_normalizer_iff.1 hg h

theorem mem_normalizer_of_map {K : Subgroup C'} (hK : Subgroup.zpowers z ≤ K) {g : C'}
    (hg : piZ z g ∈ Subgroup.normalizer ((K.map (piZ z) : Subgroup _) : Set _)) :
    g ∈ Subgroup.normalizer (K : Set C') := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have := Subgroup.mem_normalizer_iff.1 hg (piZ z h)
  rw [mem_map_piZ hK, ← map_inv, ← map_mul, ← map_mul, mem_map_piZ hK] at this
  exact this

theorem Hconj_map_piZ {K : Subgroup C'} (hK : Subgroup.zpowers z ≤ K) {g : C'}
    (hzg : g * z * g⁻¹ = z) :
    Hconj (piZ z g) (K.map (piZ z)) = (Hconj g K).map (piZ z) := by
  ext y
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have hZ : Subgroup.zpowers z ≤ Hconj g K := by
    rw [Subgroup.zpowers_le, mem_Hconj, hzg]; exact Subgroup.zpowers_le.1 hK
  rw [mem_Hconj, ← map_inv, ← map_mul, ← map_mul, mem_map_piZ hK, mem_map_piZ hZ, mem_Hconj]

end Quot


section Cfg

variable {C' : Type} [Group C']

structure RCfg (z : C') (S R R₁ R₂ : Subgroup C') : Prop where
  z_central : ∀ g : C', g * z = z * g
  z_sq : z * z = 1
  z_ne : z ≠ 1
  sylow : IsSylow2In S ⊤
  card_S : Nat.card S = 64
  R_le : R ≤ S
  card_R : Nat.card R = 32
  R₁_le : R₁ ≤ R
  R₂_le : R₂ ≤ R
  card_R₁ : Nat.card R₁ = 8
  card_R₂ : Nat.card R₂ = 8
  z₁ : z ∈ R₁
  z₂ : z ∈ R₂
  ex₁ : ∃ u ∈ R₁, u * u = z
  ex₂ : ∃ u ∈ R₂, u * u = z
  inter : ∀ r ∈ R₁, r ∈ R₂ → r = 1 ∨ r = z
  comm₁₂ : ∀ r ∈ R₁, ∀ r' ∈ R₂, r * r' = r' * r
  prod : ∀ r ∈ R, ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, r = r₁ * r₂
  sq : ∀ r ∈ R, r * r = 1 ∨ r * r = z
  comm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r ∨ r * r' = r' * r * z
  nn : ∀ r ∈ R, r * r = z → r ∈ R₁ ∨ r ∈ R₂
  sq₁ : ∀ r ∈ R₁, r ≠ 1 → r ≠ z → r * r = z
  sq₂ : ∀ r ∈ R₂, r ≠ 1 → r ≠ z → r * r = z
  nc₁ : ∀ r ∈ R₁, ∀ r' ∈ R₁, r * r = z → r' * r' = z → r' ≠ r → r' ≠ r * z → r * r' ≠ r' * r
  nc₂ : ∀ r ∈ R₂, ∀ r' ∈ R₂, r * r = z → r' * r' = z → r' ≠ r → r' ≠ r * z → r * r' ≠ r' * r
  cent8 : ∀ s ∈ S, s ∉ R →
    Nat.card {r : C' // r ∈ R ∧ (r * s = s * r ∨ r * s = s * r * z)} = 8
  norm₁ : ∀ s ∈ S, s ∈ Subgroup.normalizer (R₁ : Set C')
  norm₂ : ∀ s ∈ S, s ∈ Subgroup.normalizer (R₂ : Set C')

theorem dich_aux {z : C'} {R Ra Rb : Subgroup C'} (hzc : ∀ g : C', g * z = z * g)
    (hRa : Ra ≤ R) (hza : z ∈ Ra) (hzb : z ∈ Rb)
    (hcomm : ∀ r ∈ Ra, ∀ r' ∈ Rb, r * r' = r' * r)
    (hnn : ∀ r ∈ R, r * r = z → r ∈ Ra ∨ r ∈ Rb)
    (hsq : ∀ r ∈ Ra, r ≠ 1 → r ≠ z → r * r = z)
    (hnc : ∀ r ∈ Ra, ∀ r' ∈ Ra, r * r = z → r' * r' = z → r' ≠ r → r' ≠ r * z → r * r' ≠ r' * r)
    {u : C'} (hu : u ∈ Ra) (hu2 : u * u = z) {g : C'} (hg : g ∈ Subgroup.normalizer (R : Set C')) :
    (∀ r ∈ Ra, g * r * g⁻¹ ∈ Ra) ∨ (∀ r ∈ Ra, g * r * g⁻¹ ∈ Rb) := by
  have hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.1 hg r).1 hr
  have hzconj : g * z * g⁻¹ = z := by rw [hzc g]; group
  have hgu2 : (g * u * g⁻¹) * (g * u * g⁻¹) = z := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = z := by rw [hu2, hzconj]
  have hguR : g * u * g⁻¹ ∈ R := hgR u (hRa hu)
  have key : ∀ (Rc Rd : Subgroup C'), z ∈ Rc → (∀ r ∈ Rd, ∀ r' ∈ Rc, r * r' = r' * r) →
      (∀ r ∈ R, r * r = z → r ∈ Rc ∨ r ∈ Rd) → g * u * g⁻¹ ∈ Rc →
      ∀ r ∈ Ra, g * r * g⁻¹ ∈ Rc := by
    intro Rc Rd hzc' hcomm' hnn' hgu r hr
    by_cases h1 : r = 1
    · subst h1; simp
    by_cases h2 : r = z
    · subst h2; rw [hzconj]; exact hzc'
    have hr2 : r * r = z := hsq r hr h1 h2
    by_cases h3 : r = u
    · subst h3; exact hgu
    by_cases h4 : r = u * z
    · subst h4
      have : g * (u * z) * g⁻¹ = (g * u * g⁻¹) * z := by
        calc g * (u * z) * g⁻¹ = (g * u * g⁻¹) * (g * z * g⁻¹) := by group
          _ = (g * u * g⁻¹) * z := by rw [hzconj]
      rw [this]; exact Rc.mul_mem hgu hzc'
    have hne := hnc u hu r hr hu2 hr2 h3 h4
    have hr'R : g * r * g⁻¹ ∈ R := hgR r (by
      have := hRa hr; exact this)
    have hr'2 : (g * r * g⁻¹) * (g * r * g⁻¹) = z := by
      calc (g * r * g⁻¹) * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
        _ = z := by rw [hr2, hzconj]
    rcases hnn' _ hr'R hr'2 with h | h
    · exact h
    · exfalso
      have hc := hcomm' _ h _ hgu
      apply hne
      have : g * (u * r) * g⁻¹ = g * (r * u) * g⁻¹ := by
        calc g * (u * r) * g⁻¹ = (g * u * g⁻¹) * (g * r * g⁻¹) := by group
          _ = (g * r * g⁻¹) * (g * u * g⁻¹) := hc.symm
          _ = g * (r * u) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel this)
  rcases hnn _ hguR hgu2 with h | h
  · exact Or.inl (key Ra Rb hza (fun r hr r' hr' => (hcomm r' hr' r hr).symm) hnn h)
  · exact Or.inr (key Rb Ra hzb (fun r hr r' hr' => hcomm r hr r' hr') (fun r hr h2 =>
      (hnn r hr h2).symm) h)

theorem hconj_eq [Finite C'] {Ra Rb : Subgroup C'} (hcard : Nat.card Ra = Nat.card Rb) {g : C'}
    (h : ∀ r ∈ Ra, g * r * g⁻¹ ∈ Rb) : Hconj g Rb = Ra := by
  have hle : Ra ≤ Hconj g Rb := fun r hr => by rw [mem_Hconj]; exact h r hr
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Hconj_card, hcard])).symm

theorem RCfg.inv_cfg [Finite C'] {z : C'} {S R R₁ R₂ : Subgroup C'} (c : RCfg z S R R₁ R₂)
    {g : C'} (hg : g ∈ Subgroup.normalizer (R : Set C')) :
    (g ∈ Subgroup.normalizer (R₁ : Set C') ∧ g ∈ Subgroup.normalizer (R₂ : Set C')) ∨
      (Hconj g R₁ = R₂ ∧ Hconj g R₂ = R₁) := by
  obtain ⟨u₁, hu₁, hu₁2⟩ := c.ex₁
  obtain ⟨u₂, hu₂, hu₂2⟩ := c.ex₂
  have d₁ := dich_aux c.z_central c.R₁_le c.z₁ c.z₂ c.comm₁₂ c.nn c.sq₁ c.nc₁ hu₁ hu₁2 hg
  have d₂ := dich_aux c.z_central c.R₂_le c.z₂ c.z₁
    (fun r hr r' hr' => (c.comm₁₂ r' hr' r hr).symm) (fun r hr h => (c.nn r hr h).symm)
    c.sq₂ c.nc₂ hu₂ hu₂2 hg
  have bad : ∀ Rc : Subgroup C', Nat.card Rc = 8 → (∀ r ∈ R₁, g * r * g⁻¹ ∈ Rc) →
      (∀ r ∈ R₂, g * r * g⁻¹ ∈ Rc) → False := by
    intro Rc hRc h1 h2
    have hRle : R ≤ Rc := by
      intro a ha
      have hgi : g⁻¹ * a * g ∈ R := by
        have := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * a * g)).2 (by
          have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
          rw [e]; exact ha)
        exact this
      obtain ⟨r₁, hr₁, r₂, hr₂, he⟩ := c.prod _ hgi
      have e : a = (g * r₁ * g⁻¹) * (g * r₂ * g⁻¹) := by
        calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
          _ = g * (r₁ * r₂) * g⁻¹ := by rw [he]
          _ = (g * r₁ * g⁻¹) * (g * r₂ * g⁻¹) := by group
      rw [e]
      exact Rc.mul_mem (h1 r₁ hr₁) (h2 r₂ hr₂)
    have := Subgroup.card_le_of_le hRle
    rw [c.card_R, hRc] at this
    omega
  rcases d₁ with d₁ | d₁ <;> rcases d₂ with d₂ | d₂
  · left
    refine ⟨?_, ?_⟩
    · rw [mem_normalizer_iff_Hconj]
      exact hconj_eq (Rb := R₁) rfl d₁
    · rw [mem_normalizer_iff_Hconj]
      exact hconj_eq (Rb := R₂) rfl d₂
  · exact absurd (bad R₁ c.card_R₁ d₁ d₂) id
  · exact absurd (bad R₂ c.card_R₂ d₁ d₂) id
  · right
    exact ⟨hconj_eq (Ra := R₂) (Rb := R₁) (by rw [c.card_R₁, c.card_R₂]) d₂,
      hconj_eq (Ra := R₁) (Rb := R₂) (by rw [c.card_R₁, c.card_R₂]) d₁⟩

theorem RCfg.ctx16 [Finite C'] {z : C'} {S R R₁ R₂ : Subgroup C'} (c : RCfg z S R R₁ R₂)
    [(Subgroup.zpowers z).Normal] :
    Ctx16 (S.map (piZ z)) (R.map (piZ z)) (R₁.map (piZ z)) (R₂.map (piZ z)) := by
  classical
  have hz2 := c.z_sq
  have hz1 := c.z_ne
  have hzR : z ∈ R := c.R₁_le c.z₁
  have hZR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.2 hzR
  have hZS : Subgroup.zpowers z ≤ S := hZR.trans c.R_le
  have hZR₁ : Subgroup.zpowers z ≤ R₁ := Subgroup.zpowers_le.2 c.z₁
  have hZR₂ : Subgroup.zpowers z ≤ R₂ := Subgroup.zpowers_le.2 c.z₂
  have hπz : piZ z z = 1 := (QuotientGroup.eq_one_iff z).2 (Subgroup.mem_zpowers z)
  have h64 := c.card_S
  have h32 := c.card_R
  have h8₁ := c.card_R₁
  have h8₂ := c.card_R₂
  have cardT : Nat.card (S.map (piZ z)) = 32 := by
    have := card_map_piZ hz2 hz1 hZS
    omega
  have cardA : Nat.card (R.map (piZ z)) = 16 := by
    have := card_map_piZ hz2 hz1 hZR
    omega
  have cardA₁ : Nat.card (R₁.map (piZ z)) = 4 := by
    have := card_map_piZ hz2 hz1 hZR₁
    omega
  have cardA₂ : Nat.card (R₂.map (piZ z)) = 4 := by
    have := card_map_piZ hz2 hz1 hZR₂
    omega
  have hAT : R.map (piZ z) ≤ S.map (piZ z) := Subgroup.map_mono c.R_le
  refine
    { sylow := ?_
      le := hAT
      idx := ?_
      elem := ?_
      card := cardA
      cent := ?_
      le₁ := Subgroup.map_mono c.R₁_le
      le₂ := Subgroup.map_mono c.R₂_le
      card₁ := cardA₁
      card₂ := cardA₂
      disj := ?_
      inv := ?_
      Tinv := ?_ }
  · refine ⟨le_top, ?_, ?_⟩
    · have hS2 : IsPGroup 2 ↥S := c.sylow.2.1
      exact hS2.of_surjective ((piZ z).subgroupMap S) (MonoidHom.subgroupMap_surjective _ _)
    · rw [Subgroup.relIndex_top_right, Subgroup.index_map_eq S (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk']; exact hZS)]
      have := c.sylow.2.2
      rwa [Subgroup.relIndex_top_right] at this
  · have h5 := Subgroup.relIndex_mul_card (H := R.map (piZ z)) (K := S.map (piZ z))
    rw [inf_eq_left.2 hAT, cardA, cardT] at h5
    omega
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 ha
    refine ⟨?_, fun b hb => ?_⟩
    · rcases c.sq r hr with h | h
      · rw [← map_mul, h, map_one]
      · rw [← map_mul, h, hπz]
    · obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.1 hb
      rw [← map_mul, ← map_mul]
      rcases c.comm r hr r' hr' with h | h
      · rw [h]
      · rw [h, map_mul, hπz, mul_one]
  · intro w hwT hwA
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.1 hwT
    have hsR : s ∉ R := fun h => hwA (Subgroup.mem_map.2 ⟨s, h, rfl⟩)
    set K : Subgroup C' := R ⊓ (Subgroup.centralizer ({piZ z s} : Set (C' ⧸ Subgroup.zpowers z))).comap
      (piZ z) with hK
    have hZK : Subgroup.zpowers z ≤ K := by
      refine le_inf hZR ?_
      intro y hy
      have : piZ z y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      rw [Subgroup.mem_comap, this]
      exact Subgroup.one_mem _
    have hKcard : Nat.card K = 8 := by
      rw [← c.cent8 s hsS hsR]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
      simp only [hK, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      rw [← map_mul, ← map_mul, piZ_eq_iff_sq hz2]
    have hmap : K.map (piZ z) =
        (R.map (piZ z)) ⊓ Subgroup.centralizer ({piZ z s} : Set (C' ⧸ Subgroup.zpowers z)) := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨k, (Subgroup.mem_inf.1 hk).1, rfl⟩,
          (Subgroup.mem_inf.1 hk).2⟩
      · intro hy
        obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.1 hy
        obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hyA
        exact Subgroup.mem_map.2 ⟨r, Subgroup.mem_inf.2 ⟨hr, hyC⟩, rfl⟩
    rw [← hmap]
    have := card_map_piZ hz2 hz1 hZK
    omega
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨r₁, hr₁, rfl⟩ := Subgroup.mem_map.1 hy1
    have hr₁₂ : r₁ ∈ R₂ := (mem_map_piZ hZR₂).1 hy2
    rcases c.inter r₁ hr₁ hr₁₂ with h | h
    · rw [h, map_one]; exact Subgroup.one_mem _
    · rw [h, hπz]; exact Subgroup.one_mem _
  · intro g hg
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hg' : g' ∈ Subgroup.normalizer (R : Set C') := mem_normalizer_of_map hZR hg
    have hzg : g' * z * g'⁻¹ = z := by rw [c.z_central g']; group
    rcases c.inv_cfg hg' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨map_mem_normalizer hZR₁ h1, map_mem_normalizer hZR₂ h2⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [Hconj_map_piZ hZR₁ hzg, h1]
      · rw [Hconj_map_piZ hZR₂ hzg, h2]
  · intro t ht
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.1 ht
    exact ⟨map_mem_normalizer hZR₁ (c.norm₁ s hsS), map_mem_normalizer hZR₂ (c.norm₂ s hsS)⟩

end Cfg

section Odd

variable {C' : Type} [Group C']

theorem pPrimeCore_quot_eq_bot [Finite C'] {z : C'} [(Subgroup.zpowers z).Normal]
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hcen : ∀ g : C', g * z = z * g)
    (h : CFSG.pPrimeCore 2 C' = ⊥) :
    CFSG.pPrimeCore 2 (C' ⧸ Subgroup.zpowers z) = ⊥ := by
  classical
  rw [CFSG.pPrimeCore_eq_bot_iff] at h ⊢
  intro K hKn hKc
  have hKodd : ¬ 2 ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hKc
  set Kh : Subgroup C' := K.comap (piZ z) with hKh
  have hKhn : Kh.Normal := hKn.comap _
  have hπz : piZ z z = 1 := (QuotientGroup.eq_one_iff z).2 (Subgroup.mem_zpowers z)
  have hzKh : z ∈ Kh := by
    rw [hKh, Subgroup.mem_comap, hπz]
    exact K.one_mem
  have hZKh : Subgroup.zpowers z ≤ Kh := Subgroup.zpowers_le.2 hzKh
  have hmapK : Kh.map (piZ z) = K :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K
  have hcard : 2 * Nat.card K = Nat.card Kh := by
    have := card_map_piZ hz2 hz1 hZKh
    rwa [hmapK] at this
  set m := Nat.card K with hm
  set N : Subgroup ↥Kh := (Subgroup.zpowers z).subgroupOf Kh with hN
  have hNn : N.Normal := (inferInstance : (Subgroup.zpowers z).Normal).subgroupOf Kh
  have hNcard : Nat.card N = 2 := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZKh).toEquiv]
    exact card_zpowers_of_sq hz2 hz1
  have hidxN : N.index = m := by
    have h1 := N.card_mul_index
    rw [hNcard] at h1
    omega
  have hcop : Nat.Coprime (Nat.card N) N.index := by rw [hNcard, hidxN]; exact hKc
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := N) hcop
  have hHcard : Nat.card H = m := by
    have := hH.card_mul_card
    rw [hNcard] at this
    omega
  set Nodd : Subgroup C' := H.map Kh.subtype with hNodd
  obtain ⟨k, hk⟩ : Odd m := Nat.odd_iff.2 (by omega)
  have hP : ∀ g : C', g ∈ Nodd ↔ g ∈ Kh ∧ g ^ m = 1 := by
    intro g
    constructor
    · rintro ⟨h', hh', rfl⟩
      refine ⟨h'.2, ?_⟩
      have h1 : (⟨h', hh'⟩ : ↥H) ^ Nat.card H = 1 := pow_card_eq_one'
      rw [hHcard] at h1
      have h2 : h' ^ m = 1 := congrArg Subtype.val h1
      have : ((h' ^ m : ↥Kh) : C') = 1 := by rw [h2]; rfl
      simpa using this
    · rintro ⟨hg, hgm⟩
      obtain ⟨⟨n, h''⟩, hnh⟩ := (Subgroup.isComplement'_def.1 hH).2 (⟨g, hg⟩ : ↥Kh)
      have hnz : ((n : ↥Kh) : C') ∈ Subgroup.zpowers z := n.2
      have hn12 : ((n : ↥Kh) : C') = 1 ∨ ((n : ↥Kh) : C') = z := (mem_zpowers_sq hz2).1 hnz
      have hcomm : Commute (n : ↥Kh) (h'' : ↥Kh) := by
        apply Subtype.ext
        rcases hn12 with h | h
        · simp [h]
        · simp only [Subgroup.coe_mul, h]
          exact (hcen _).symm
      have hh''m : (h'' : ↥Kh) ^ m = 1 := by
        have h1 : (⟨h''.1, h''.2⟩ : ↥H) ^ Nat.card H = 1 := pow_card_eq_one'
        rw [hHcard] at h1
        exact congrArg Subtype.val h1
      have hnm : (n : ↥Kh) ^ m = n := by
        have hn2 : (n : ↥Kh) * n = 1 := by
          apply Subtype.ext
          rcases hn12 with h | h
          · simp [h]
          · simp [h, hz2]
        have hn2' : (n : ↥Kh) ^ 2 = 1 := by rw [pow_two]; exact hn2
        rw [hk, pow_succ, pow_mul, hn2', one_pow, one_mul]
      have hgm' : (⟨g, hg⟩ : ↥Kh) ^ m = 1 := Subtype.ext (by simpa using hgm)
      have hnh' : (n : ↥Kh) * (h'' : ↥Kh) = ⟨g, hg⟩ := hnh
      rw [← hnh', hcomm.mul_pow, hnm, hh''m, mul_one] at hgm'
      have hn1 : (n : ↥Kh) = 1 := hgm'
      rw [hn1, one_mul] at hnh'
      exact ⟨h'', h''.2, by rw [hnh']; rfl⟩
  have hNoddn : Nodd.Normal := ⟨fun n hn g => by
    obtain ⟨hnK, hnm⟩ := (hP n).1 hn
    refine (hP _).2 ⟨hKhn.conj_mem n hnK g, ?_⟩
    rw [conj_pow, hnm]
    group⟩
  have hNoddcard : Nat.card Nodd = m := by
    rw [hNodd, Subgroup.card_map_of_injective Kh.subtype_injective, hHcard]
  have hbot := h Nodd hNoddn (by rw [hNoddcard]; exact hKc)
  have hm1 : m = 1 := by
    have : Nat.card Nodd = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  exact Subgroup.card_eq_one.1 hm1

theorem pPrimeCoreOf_normal_eq_bot {Y : Type*} [Group Y] [Finite Y] (h : CFSG.pPrimeCore 2 Y = ⊥)
    {N : Subgroup Y} [N.Normal] : pPrimeCoreOf 2 N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := pPrimeCoreOf_le_of_subnormal 2 (Subgroup.Normal.isSubnormal (H := N) inferInstance)
  rw [h] at hle
  exact le_bot_iff.1 hle

end Odd

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
