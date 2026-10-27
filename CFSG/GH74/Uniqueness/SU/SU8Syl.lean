module

public import CFSG.GH74.Uniqueness.SU.SU8Lem203
public import CFSG.GH74.Uniqueness.SU.SU8Burn

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU4
  CFSG.GH74.Uniqueness.SU.SU8.Setup CFSG.GH74.Uniqueness.SU.SU8.Burn

section Syl

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

theorem Hyp20A.exists_syl (hyp : Hyp20A z S L A) :
    ∃ T : Subgroup G, IsSylowIn ⊤ T ∧ A ≤ T ∧
      ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ T → g⁻¹ * a * g ∈ A := by
  obtain ⟨T, hAT, hcl⟩ := hyp.A_strongly_closed
  refine ⟨(T : Subgroup G), ⟨le_top, T.isPGroup', ?_⟩, hAT, hcl⟩
  rw [Subgroup.relIndex_top_right]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp T.not_dvd_index)

theorem normalizer_le_of_strongly_closed {T : Subgroup G} (hAT : A ≤ T)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ T → g⁻¹ * a * g ∈ A) {n : G}
    (hn : n ∈ normalizer (T : Set G)) : n ∈ normalizer (A : Set G) := by
  refine mem_normalizer_of_conj_le (fun a ha => ?_)
  have h1 : n * a * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn a).mp (hAT ha)
  have := hcl a ha n⁻¹ (by simpa using h1)
  simpa using this

omit [Finite G] in
theorem Out203.centralizes_of_two_power (o : Out203 z S L A) {s : G}
    (hs : s ∈ normalizer (A : Set G)) {k : ℕ} (hk : s ^ (2 ^ k) = 1) :
    ∀ a ∈ A, s * a * s⁻¹ = a := by
  obtain ⟨hN, h21, -⟩ := o.order
  have h1 : (QuotientGroup.mk (⟨s, hs⟩ : ↥(normalizer (A : Set G))) :
      ↥(normalizer (A : Set G)) ⧸ (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)))
        ^ (2 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨s, hs⟩ : ↥(normalizer (A : Set G))) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk (⟨s, hs⟩ : ↥(normalizer (A : Set G))) :
      ↥(normalizer (A : Set G)) ⧸ (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)))
        ^ 21 = 1 := by
    rw [← h21]; exact pow_card_eq_one'
  have hq := eq_one_of_pow_odd h1 h2 (by norm_num : Odd 21)
  have hmem := (QuotientGroup.eq_one_iff _).mp hq
  intro a ha
  have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hmem) a ha
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem Out203.syl_centralizes (o : Out203 z S L A) {T : Subgroup G} (hT : IsSylowIn ⊤ T)
    (hAT : A ≤ T) (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ T → g⁻¹ * a * g ∈ A) :
    ∀ s ∈ T, ∀ a ∈ A, s * a * s⁻¹ = a := by
  intro s hs
  have hsN : s ∈ normalizer (A : Set G) :=
    normalizer_le_of_strongly_closed hAT hcl (Subgroup.le_normalizer hs)
  obtain ⟨k, hk⟩ := hT.2.1 ⟨s, hs⟩
  exact o.centralizes_of_two_power hsN (k := k) (by simpa using congrArg Subtype.val hk)

theorem Out203.syl_le_H (o : Out203 z S L A) {T : Subgroup G} (hT : IsSylowIn ⊤ T)
    (hAT : A ≤ T) (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ T → g⁻¹ * a * g ∈ A)
    (hyp : Hyp20A z S L A) : T ≤ Hz z := by
  intro s hs
  refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
  rw [Set.mem_singleton_iff.mp hy]
  have hzA : z ∈ A := hyp.z_mem.1
  have := o.syl_centralizes hT hAT hcl s hs z hzA
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem Hyp20A.Q_tame' (hyp : Hyp20A z S L A) {T : Subgroup G} (hT : IsSylowIn (Hz z) T) :
    ∀ x : G, x ∉ normalizer (L : Set G) →
      (T ⊓ centralizerBar (Hz z) L) ⊓ conjSub x (T ⊓ centralizerBar (Hz z) L) = ⊥ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(Hz z)) (sylowOf hyp.S_sylow_H) (sylowOf hT)
  have hconj : ∀ w ∈ T, (g : G)⁻¹ * w * (g : G) ∈ S := by
    intro w hw
    have h1 : (⟨w, hT.1 hw⟩ : ↥(Hz z)) ∈ (sylowOf hT : Subgroup ↥(Hz z)) :=
      Subgroup.mem_subgroupOf.mpr hw
    rw [← hg, Setup.mem_sylow_smul_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hC : ∀ {y : G}, y ∈ centralizerBar (Hz z) L → (g : G)⁻¹ * y * (g : G) ∈ centralizerBar (Hz z) L := by
    intro y hy
    have := Lem203.conj_mem_centralizerBar hyp.L_normal ((Hz z).inv_mem g.2) hy
    simpa using this
  intro x hx
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨e, he, hew⟩ := mem_conjSub.mp hw2
  have hw' : (g : G)⁻¹ * w * (g : G) ∈ S ⊓ centralizerBar (Hz z) L :=
    ⟨hconj w hw1.1, hC hw1.2⟩
  have he' : (g : G)⁻¹ * e * (g : G) ∈ S ⊓ centralizerBar (Hz z) L :=
    ⟨hconj e he.1, hC he.2⟩
  have hxn : (g : G)⁻¹ * x * (g : G) ∉ normalizer (L : Set G) := by
    intro hxn
    apply hx
    have hgn : (g : G) ∈ normalizer (L : Set G) := hyp.L_normal g.2
    have : x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
    rw [this]
    exact (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem hgn hxn)
      ((normalizer (L : Set G)).inv_mem hgn)
  have hmem : (g : G)⁻¹ * w * (g : G) ∈ (S ⊓ centralizerBar (Hz z) L) ⊓
      conjSub ((g : G)⁻¹ * x * (g : G)) (S ⊓ centralizerBar (Hz z) L) := by
    refine ⟨hw', mem_conjSub.mpr ⟨_, he', ?_⟩⟩
    rw [← hew]
    group
  rw [hyp.Q_tame _ hxn] at hmem
  have h1 : (g : G)⁻¹ * w * (g : G) = 1 := (Subgroup.mem_bot).mp hmem
  rw [Subgroup.mem_bot]
  calc w = (g : G) * ((g : G)⁻¹ * w * (g : G)) * (g : G)⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem Out203.AC_eq (o : Out203 z S L A) (hyp : Hyp20A z S L A) {u : G}
    (hu : u ∈ A ⊓ centralizerBar (Hz z) L) : u = 1 ∨ u = z := by
  have hz : z ∈ A ⊓ centralizerBar (Hz z) L := hyp.z_mem
  have hle : Subgroup.zpowers z ≤ A ⊓ centralizerBar (Hz z) L := by
    rw [Subgroup.zpowers_le]; exact hz
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]; exact hyp.z_invol
  have heq : Subgroup.zpowers z = A ⊓ centralizerBar (Hz z) L :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [o.card_AC, hcard])
  rw [← heq] at hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [← zpow_mod_orderOf, hyp.z_invol]
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · left
    have : j % ((2 : ℕ) : ℤ) = 0 := by simpa using h
    rw [this]; simp
  · right
    have : j % ((2 : ℕ) : ℤ) = 1 := by simpa using h
    rw [this]; simp

theorem Out203.fixes_z (o : Out203 z S L A) (hyp : Hyp20A z S L A) {y : G}
    (hyA : y ∈ normalizer (A : Set G)) (hyL : y ∈ normalizer (L : Set G)) :
    y * z * y⁻¹ = z := by
  have hz : z ∈ A ⊓ centralizerBar (Hz z) L := hyp.z_mem
  have hzAC := o.act.mem_AC_iff.mp hz
  have hmem : y * z * y⁻¹ ∈ A ⊓ centralizerBar (Hz z) L := by
    rw [o.act.mem_AC_iff]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hyA z).mp hz.1, fun g hg => ?_⟩
    have hgL : y⁻¹ * g * y ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem hyL) g).mp hg.1
      simpa using h1
    have hgN : y⁻¹ * g * y ∈ normalizer (A : Set G) :=
      (normalizer (A : Set G)).mul_mem
        ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hyA) hg.2) hyA
    have h2 := hzAC.2 (y⁻¹ * g * y) ⟨hgL, hgN⟩
    calc g * (y * z * y⁻¹) * g⁻¹ = y * ((y⁻¹ * g * y) * z * (y⁻¹ * g * y)⁻¹) * y⁻¹ := by group
      _ = y * z * y⁻¹ := by rw [h2]
  rcases o.AC_eq hyp hmem with h | h
  · exfalso
    apply hyp.z_ne_one
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · exact h

end Syl

end CFSG.GH74.Uniqueness.SU.SU8
