module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure SimpleSec (A M : Subgroup G) : Prop where
  le : M ≤ A
  normal : ∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M
  simple : ∀ D : Subgroup G, M ≤ D → D ≤ A → (∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D) →
    D = M ∨ D = A
  central : ∀ a ∈ A, (∀ b ∈ A, ⁅a, b⁆ ∈ M) → a ∈ M
  card : Nat.card A = 168 * Nat.card M

theorem simpleSec_of_gl3 {A M : Subgroup G} (hMA : M ≤ A)
    (h : SecProp A M (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) :
    SimpleSec A M := by
  classical
  obtain ⟨hn, ⟨e⟩⟩ := h
  haveI := hn
  let Q : Type := ↥A ⧸ M.subgroupOf A
  let π : ↥A →* Q := QuotientGroup.mk' (M.subgroupOf A)
  have hGL : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI := hGL
  haveI : IsSimpleGroup Q := e.isSimpleGroup
  have hcardQ : Nat.card Q = 168 := by
    rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]
  refine ⟨hMA, ?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact hn.conj_mem (⟨m, hMA hm⟩ : ↥A) hm (⟨a, ha⟩ : ↥A)
  · intro D hMD hDA hnD
    have hDnorm : (D.subgroupOf A).Normal :=
      ⟨fun n hn' g => by
        show ((g * n * g⁻¹ : ↥A) : G) ∈ D
        exact hnD g g.2 n hn'⟩
    have hmapnorm : ((D.subgroupOf A).map π).Normal :=
      hDnorm.map π (QuotientGroup.mk'_surjective _)
    haveI := hmapnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.subgroupOf A).map π) with hbot | htop
    · left
      have hle : D.subgroupOf A ≤ M.subgroupOf A := by
        intro x hx
        have hx' : π x ∈ (D.subgroupOf A).map π := Subgroup.mem_map_of_mem π hx
        rw [hbot] at hx'
        have hx1 : π x = 1 := Subgroup.mem_bot.mp hx'
        have hker : x ∈ π.ker := MonoidHom.mem_ker.mpr hx1
        rwa [QuotientGroup.ker_mk'] at hker
      have heq : D.subgroupOf A = M.subgroupOf A :=
        le_antisymm hle (Subgroup.subgroupOf_mono A hMD)
      have hinf : D ⊓ A = M ⊓ A := Subgroup.subgroupOf_inj.mp heq
      simpa [inf_eq_left.mpr hDA, inf_eq_left.mpr hMA] using hinf
    · right
      have htopD : D.subgroupOf A = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top]
        intro x hx
        have hx' : π ⟨x, hx⟩ ∈ (D.subgroupOf A).map π := by
          rw [htop]; exact Subgroup.mem_top _
        obtain ⟨d, hd, hdπ⟩ := Subgroup.mem_map.mp hx'
        have hker : d⁻¹ * ⟨x, hx⟩ ∈ M.subgroupOf A := by
          have h1 : π (d⁻¹ * ⟨x, hx⟩) = 1 := by
            rw [map_mul, map_inv, hdπ, inv_mul_cancel]
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
          exact h1
        have h2 : d⁻¹ * ⟨x, hx⟩ ∈ D.subgroupOf A :=
          Subgroup.subgroupOf_mono A hMD hker
        have h3 : d * (d⁻¹ * ⟨x, hx⟩) ∈ D.subgroupOf A :=
          (D.subgroupOf A).mul_mem hd h2
        exact Subgroup.mem_subgroupOf.mp (by simpa using h3)
      have hAD : A ≤ D := Subgroup.subgroupOf_eq_top.mp htopD
      exact le_antisymm hDA hAD
  · intro a ha hcomm
    have hcenter : Subgroup.center Q = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hc | hc
      · exact hc
      · exfalso
        haveI : IsMulCommutative Q := Subgroup.center_eq_top_iff.mp hc
        have hp : (Nat.card Q).Prime := Group.is_simple_iff_prime_card.mp inferInstance
        rw [hcardQ] at hp
        exact absurd hp (by norm_num)
    have hqa : π ⟨a, ha⟩ ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf A) u
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement π,
        ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      have hcoe : ((⁅w, (⟨a, ha⟩ : ↥A)⁆ : ↥A) : G) = ⁅(w : G), a⁆ := by
        simp [commutatorElement_def]
      rw [hcoe, ← commutatorElement_inv (g₁ := a) (g₂ := (w : G))]
      exact M.inv_mem (hcomm (w : G) w.2)
    have hker : (⟨a, ha⟩ : ↥A) ∈ M.subgroupOf A := by
      have h1 : π ⟨a, ha⟩ = 1 := by
        have hmem := hqa
        rw [hcenter] at hmem
        exact Subgroup.mem_bot.mp hmem
      have h2 : (⟨a, ha⟩ : ↥A) ∈ π.ker := MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    exact Subgroup.mem_subgroupOf.mp hker
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf A), hcardQ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMA).toEquiv]

theorem SimpleSec.conj {A M : Subgroup G} (h : SimpleSec A M) (x : G) :
    SimpleSec (conjSub x A) (conjSub x M) := by
  let f : G →* G := (MulAut.conj x).toMonoidHom
  have hf_inj : Function.Injective f := (MulAut.conj x).injective
  have hf_surj : Function.Surjective f := (MulAut.conj x).surjective
  change SimpleSec (A.map f) (M.map f)
  refine ⟨Subgroup.map_mono h.le, ?_, ?_, ?_, ?_⟩
  · intro a' ha' m' hm'
    rw [Subgroup.mem_map] at ha' hm' ⊢
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨m, hm, rfl⟩ := hm'
    exact ⟨a * m * a⁻¹, h.normal a ha m hm, by simp⟩
  · intro D' hMD' hD'A hnD'
    let D : Subgroup G := D'.comap f
    have hmapD : D.map f = D' := Subgroup.map_comap_eq_self_of_surjective hf_surj D'
    have hMD : M ≤ D := fun m hm => Subgroup.mem_comap.mpr (hMD' (Subgroup.mem_map_of_mem f hm))
    have hDA : D ≤ A := by
      intro d hd
      have hfd : f d ∈ A.map f := hD'A hd
      rw [Subgroup.mem_map] at hfd
      obtain ⟨a, ha, haf⟩ := hfd
      have had : a = d := hf_inj haf
      rw [← had]
      exact ha
    have hnD : ∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
      intro a ha d hd
      have hconj := hnD' (f a) (Subgroup.mem_map_of_mem f ha) (f d) hd
      have hg : f (a * d * a⁻¹) = f a * f d * (f a)⁻¹ := by simp
      change f (a * d * a⁻¹) ∈ D'
      rw [hg]
      exact hconj
    rcases h.simple D hMD hDA hnD with hDM | hDA'
    · left
      rw [← hmapD, hDM]
    · right
      rw [← hmapD, hDA']
  · intro a' ha' hcomm'
    rw [Subgroup.mem_map] at ha'
    obtain ⟨a, ha, rfl⟩ := ha'
    have hmem : ∀ b ∈ A, ⁅a, b⁆ ∈ M := by
      intro b hb
      have h1 : ⁅f a, f b⁆ ∈ M.map f := hcomm' (f b) (Subgroup.mem_map_of_mem f hb)
      have h2 : f ⁅a, b⁆ ∈ M.map f := by
        rw [map_commutatorElement f]
        exact h1
      rw [Subgroup.mem_map] at h2
      obtain ⟨m, hm, hmf⟩ := h2
      have hm_eq : m = ⁅a, b⁆ := hf_inj hmf
      rwa [hm_eq] at hm
    exact Subgroup.mem_map_of_mem f (h.central a ha hmem)
  · rw [Subgroup.card_map_of_injective hf_inj, Subgroup.card_map_of_injective hf_inj, h.card]

end CFSG.OddStandard.HigherRank.YamadaG23
