module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSigma
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPosition

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

section Realization

variable {G : Type} [Group G] {J : Subgroup G}
  {q : Jhat J →* Equiv.Perm (Fin 42)}

theorem exists_real (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hker : q.ker = center (Jhat J)) {y : G} (hy : y ∈ normalizer (J : Set G)) :
    ∃ r ∈ R, ∀ e, q (betaHat J hy e) = r * q e * r⁻¹ :=
  exists_realization q hqS hqsurj (betaHat J hy) (fun e => by
    rw [hker]
    exact mulEquiv_mem_center_iff _ e)

theorem real_unique (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {r r' : Equiv.Perm (Fin 42)}
    (hr : r ∈ R) (hr' : r' ∈ R) {β : Jhat J → Jhat J} (h : ∀ e, q (β e) = r * q e * r⁻¹)
    (h' : ∀ e, q (β e) = r' * q e * r'⁻¹) : r = r' := by
  have hc : r'⁻¹ * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem (R.inv_mem hr') hr⟩
    obtain ⟨e, rfl⟩ := hqsurj s hs
    have := (h e).symm.trans (h' e)
    calc q e * (r'⁻¹ * r) = r'⁻¹ * (r' * q e * r'⁻¹) * r := by group
      _ = r'⁻¹ * (r * q e * r⁻¹) * r := by rw [this]
      _ = r'⁻¹ * r * q e := by group
  rw [centralizer_S_inf_R, mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

end Realization

section RealHom

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  (d : Datum A) {q : Jhat A →* Equiv.Perm (Fin 42)}

noncomputable def realHom (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hker : q.ker = center (Jhat A)) : ↥d.X →* ↥R where
  toFun y := ⟨(Classical.choose (exists_real hqS hqsurj hker (d.X_sylow.le y.2)))⁻¹,
    R.inv_mem (Classical.choose_spec (exists_real hqS hqsurj hker (d.X_sylow.le y.2))).1⟩
  map_one' := by
    refine Subtype.ext ?_
    have hs := Classical.choose_spec (exists_real hqS hqsurj hker (d.X_sylow.le (d.X.one_mem)))
    have h1 := real_unique hqsurj hs.1 R.one_mem (β := betaHat A (d.X_sylow.le d.X.one_mem))
      hs.2 (fun e => by rw [betaHat_eq_self A _ rfl]; simp)
    show (Classical.choose _)⁻¹ = 1
    rw [h1, inv_one]
  map_mul' y y' := by
    refine Subtype.ext ?_
    have hs := Classical.choose_spec (exists_real hqS hqsurj hker (d.X_sylow.le y.2))
    have hs' := Classical.choose_spec (exists_real hqS hqsurj hker (d.X_sylow.le y'.2))
    have hs'' := Classical.choose_spec
      (exists_real hqS hqsurj hker (d.X_sylow.le (d.X.mul_mem y.2 y'.2)))
    set r := Classical.choose (exists_real hqS hqsurj hker (d.X_sylow.le y.2))
    set r' := Classical.choose (exists_real hqS hqsurj hker (d.X_sylow.le y'.2))
    set r'' := Classical.choose
      (exists_real hqS hqsurj hker (d.X_sylow.le (d.X.mul_mem y.2 y'.2)))
    have h1 := real_unique hqsurj hs''.1 (R.mul_mem hs'.1 hs.1)
      (β := betaHat A (d.X_sylow.le (d.X.mul_mem y.2 y'.2))) hs''.2 (fun e => by
        rw [betaHat_mul A (d.X_sylow.le y.2) (d.X_sylow.le y'.2), hs'.2, hs.2]
        group)
    show r''⁻¹ = r⁻¹ * r'⁻¹
    rw [h1, mul_inv_rev]

theorem realHom_spec (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hker : q.ker = center (Jhat A)) (y : ↥d.X) (e : Jhat A) :
    q (betaHat A (d.X_sylow.le y.2) e) =
      ((realHom d hqS hqsurj hker y : ↥R) : Equiv.Perm (Fin 42))⁻¹ * q e *
        ((realHom d hqS hqsurj hker y : ↥R) : Equiv.Perm (Fin 42)) := by
  have hs := Classical.choose_spec (exists_real hqS hqsurj hker (d.X_sylow.le y.2))
  have := hs.2 e
  simpa [realHom] using this

omit [Finite G] in
theorem betaHat_of_mem {s : G} (hs : s ∈ A) (e : Jhat A) :
    betaHat A (le_normalizer hs) e = (jq A ⟨s, hs⟩)⁻¹ * e * jq A ⟨s, hs⟩ := by
  obtain ⟨j, rfl⟩ := jq_surjective A e
  rw [betaHat_jq, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem realHom_of_mem (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hker : q.ker = center (Jhat A)) (s : ↥d.S) :
    ((realHom d hqS hqsurj hker ⟨s, d.S_le_X s.2⟩ : ↥R) : Equiv.Perm (Fin 42)) =
      q (jS d s) := by
  have hs := Classical.choose_spec
    (exists_real hqS hqsurj hker (d.X_sylow.le (d.S_le_X s.2)))
  have hmem : (q (jS d s))⁻¹ ∈ R := R.inv_mem (S_le_R (hqS _))
  have h1 := real_unique hqsurj hs.1 hmem (β := betaHat A (d.X_sylow.le (d.S_le_X s.2))) hs.2
    (fun e => by
      rw [betaHat_of_mem (d.S_le_A s.2), map_mul, map_mul, map_inv]
      rfl)
  simp only [realHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h1, inv_inv]

theorem conj_T0_iff {m : Equiv.Perm (Fin 42)}
    (hle : ∀ t ∈ T0, m * t * m⁻¹ ∈ T0) (t : Equiv.Perm (Fin 42)) : m * t * m⁻¹ ∈ T0 ↔ t ∈ T0 := by
  refine ⟨fun ht => ?_, hle t⟩
  have hmap : T0.map (MulAut.conj m).toMonoidHom = T0 := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hle x hx
    · rw [card_map_of_injective (MulAut.conj m).injective]
  rw [← hmap] at ht
  obtain ⟨x, hx, hxt⟩ := ht
  have : x = t := (MulAut.conj m).injective (by simpa using hxt)
  rwa [← this]


theorem exists_sylow_conj (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hker : q.ker = center (Jhat A))
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ d.S, ∃ hp : p ∈ A, jq A ⟨p, hp⟩ = e) :
    ∃ m ∈ R, (∀ t, m * t * m⁻¹ ∈ T0 ↔ t ∈ T0) ∧ ∀ (y : G) (hy : y ∈ d.X),
      m * ((realHom d hqS hqsurj hker ⟨y, hy⟩ : ↥R) : Equiv.Perm (Fin 42)) * m⁻¹ ∈ Sigma0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := realHom d hqS hqsurj hker with hρ
  have hΨ : IsPGroup 2 ρ.range :=
    d.X_sylow.isPGroup.of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
  let sylS0 : Sylow 2 ↥R := isPGroup_Sigma0.toSylow not_two_dvd_index_Sigma0
  obtain ⟨P', hP'⟩ := hΨ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥R sylS0 P'
  have key : ∀ x ∈ ρ.range, g⁻¹ * x * g ∈ Sigma0.subgroupOf R := by
    intro x hx
    have h1 : x ∈ ((g • sylS0 : Sylow 2 ↥R) : Subgroup ↥R) := hg ▸ hP' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, hsx⟩ := h1
    have : s = g⁻¹ * x * g := by
      rw [← hsx]
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
    rw [← this]
    have hs' : s ∈ (sylS0 : Subgroup ↥R) := hs
    simpa [sylS0] using hs'
  set m : Equiv.Perm (Fin 42) := ((g⁻¹ : ↥R) : Equiv.Perm (Fin 42)) with hm
  have hmR : m ∈ R := (g⁻¹).2
  have hkey : ∀ x ∈ ρ.range, m * (x : Equiv.Perm (Fin 42)) * m⁻¹ ∈ Sigma0 := by
    intro x hx
    have := key x hx
    rw [mem_subgroupOf] at this
    simpa [hm] using this
  have hT0le : ∀ t ∈ T0, m * t * m⁻¹ ∈ T0 := by
    intro t ht
    obtain ⟨e, he⟩ := hqsurj t (T0_le_S ht)
    obtain ⟨p, hpS, hpA, hpe⟩ := (hT e).1 (by rw [he]; exact ht)
    have hx : ρ ⟨p, d.S_le_X hpS⟩ ∈ ρ.range := ⟨_, rfl⟩
    have hval : ((ρ ⟨p, d.S_le_X hpS⟩ : ↥R) : Equiv.Perm (Fin 42)) = t := by
      have := realHom_of_mem d hqS hqsurj hker ⟨p, hpS⟩
      rw [hρ, this, jS_apply]
      simp only
      rw [hpe, he]
    have h1 := hkey _ hx
    rw [hval] at h1
    have h2 : m * t * m⁻¹ ∈ S := conj_mem_S hmR (T0_le_S ht)
    exact mem_T0_of_mem_Sigma0 h1 h2
  refine ⟨m, hmR, conj_T0_iff hT0le, fun y hy => hkey _ ⟨⟨y, hy⟩, rfl⟩⟩

end RealHom

section PosSection

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

structure Pos (d : Datum A) where
  q : Jhat A →* Equiv.Perm (Fin 42)
  l : Cover →* Jhat A
  isQ : IsQSetting q l
  hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ d.S, ∃ hp : p ∈ A, jq A ⟨p, hp⟩ = e
  act : ∀ (y : G) (hy : y ∈ d.X), ∃ r ∈ Sigma0, ∀ e,
    q (betaHat A (d.X_sylow.le hy) e) = r * q e * r⁻¹

theorem exists_pos
    (h : Hyp G A) (d : Datum A) : Nonempty (Pos d) := by
  have hA : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h.commutator_eq_top)
  obtain ⟨q₀, l₀, hqS, hqsurj, hker, h3, hl, hls, hT⟩ :=
    exists_sylow_standard hA h.isL34Type (S_isSylowTwoIn d)
  obtain ⟨m, hmR, hmT, hmS0⟩ := exists_sylow_conj d hqS hqsurj hker hT
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj hmR
  set q : Jhat A →* Equiv.Perm (Fin 42) := (MulAut.conj m).toMonoidHom.comp q₀ with hq
  have hker'' : q.ker = center (Jhat A) := hker'.trans hker
  obtain ⟨l, hl', hls'⟩ := exists_lam (commutator_jhat hA) q hS' hsurj' (hker''.le)
  refine ⟨⟨q, l, ⟨hS', hsurj', hker'', fun e he => h3 e (by rwa [← hker'] ), hl', hls'⟩,
    fun e => ?_, fun y hy => ?_⟩⟩
  · have : q e = m * q₀ e * m⁻¹ := rfl
    rw [this, hmT, hT]
  · refine ⟨(m * ((realHom d hqS hqsurj hker ⟨y, hy⟩ : ↥R) : Equiv.Perm (Fin 42)) * m⁻¹)⁻¹,
      Sigma0.inv_mem (hmS0 y hy), fun e => ?_⟩
    have h1 := realHom_spec d hqS hqsurj hker ⟨y, hy⟩ e
    have : q (betaHat A (d.X_sylow.le hy) e) = m * q₀ (betaHat A (d.X_sylow.le hy) e) * m⁻¹ := rfl
    rw [this, h1]
    have : q e = m * q₀ e * m⁻¹ := rfl
    rw [this]
    group

end PosSection

end CFSG.OddStandard.ChengHeld.M1b
