module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RFusion

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.AscFusion
open scoped commutatorElement

@[expose] def A7FusionCore : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (K : Subgroup F) (z : F), IsClassical2A7 ⊤ K z →
      ∀ (J : Subgroup F) (t : F), IsClassical2A7 ⊤ J t → (∃ g : F, J = conjSub g K) → t ≠ z →
        z ∈ Subgroup.normalizer (J : Set F) →
        (∀ Q : Subgroup F, IsClassical2A7 ⊤ Q z → (∃ g : F, Q = conjSub g K) →
          t ∈ Subgroup.normalizer (Q : Set F)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → 4 ≤ orderOf v → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set F) → v ∈ Subgroup.normalizer (K : Set F)

section Reduction

variable {F : Type} [Group F] [Finite F]

theorem four_le_orderOf_of_not_mem {J K : Subgroup F} {t v : F} (hJ : IsClassical2A7 ⊤ J t)
    (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (htK : t ∈ Subgroup.normalizer (K : Set F)) (hvK : v ∉ Subgroup.normalizer (K : Set F)) :
    4 ≤ orderOf v := by
  obtain ⟨n, hn⟩ := hv2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exfalso
    apply hvK
    interval_cases n
    · rw [pow_zero, orderOf_eq_one_iff] at hn
      rw [hn]
      exact Subgroup.one_mem _
    · have hvt : v = t := hJ.eq_of_orderOf_eq_two hvJ (by rw [hn]; norm_num)
      rw [hvt]
      exact htK
  · rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge

theorem a7Omega5_of_core (h : A7FusionCore) : A7Omega5 := by
  intro F _ _ _ hnab K z hK k hkK hk2 hkz g hg
  obtain ⟨hJ, hyJ, hy2, hy4⟩ := conj_two_element hK hkK hk2 hkz g
  have hyz : g * k * g⁻¹ * z = z * (g * k * g⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hg z rfl).symm
  set J : Subgroup F := K.map (MulAut.conj g).toMonoidHom with hJdef
  set t : F := g * z * g⁻¹ with htdef
  set y : F := g * k * g⁻¹ with hydef
  by_contra hy
  by_cases htz : t = z
  ·
    have hgC : g ∈ Subgroup.centralizer ({z} : Set F) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : g * z * g⁻¹ = z := htz
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [h1]
    have hmem : J ∈ omegaAt K z z := map_conj_mem_omegaAt_self hgC
    by_cases hJK : J = K
    · exact hy (Subgroup.le_normalizer (hJK ▸ hyJ))
    · exact hy ((twins_oddCoreOf hK hmem hJK).1 hyJ)
  · obtain ⟨hzJ, a, haJ, ha4, haz⟩ := step_one hJ hyJ hy2 hy4 hyz
    have hD2 : ∀ Q : Subgroup F, IsClassical2A7 ⊤ Q z → (∃ g : F, Q = conjSub g K) →
        t ∈ Subgroup.normalizer (Q : Set F) := fun Q hQ _ =>
      mem_normalizer_of_commute_orderOf_four hJ hQ haJ ha4 haz
    have htK : t ∈ Subgroup.normalizer (K : Set F) := hD2 K hK ⟨1, (conjSub_one K).symm⟩
    obtain ⟨n, hn1, hn2⟩ := exists_pow_not_mem_sq_mem hy2 hy
    have hvJ : y ^ (2 ^ n) ∈ J := J.pow_mem hyJ _
    have hv2 : IsPGroup 2 (Subgroup.zpowers (y ^ (2 ^ n))) :=
      hy2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _))
    have hv4 : 4 ≤ orderOf (y ^ (2 ^ n)) := four_le_orderOf_of_not_mem hJ hvJ hv2 htK hn1
    have hvz : y ^ (2 ^ n) * z = z * y ^ (2 ^ n) :=
      (Commute.pow_left (show Commute y z from hyz) _).eq
    exact hn1 (h F hnab K z hK J t hJ ⟨g, rfl⟩ htz hzJ hD2 _ hvJ hv2 hv4 hvz hn2)

theorem a7FusionCore_of_prop37x (h : Prop37x) : A7FusionCore := by
  intro F _ _ _ hnab K z hK J t hJ _ _ hzJ hD2 v hvJ hv2 hv4 hvz _
  exact h F hnab J K t z hJ hK hzJ (hD2 K hK ⟨1, (conjSub_one K).symm⟩) v hvJ hv2 hv4 hvz

theorem citSimplePerfect_of_thmI_core (h1 : Generic.CITSimplePerfectSL2) (T : A7ThmI)
    (C : A7FusionCore) : CITSimplePerfect :=
  citSimplePerfect_of_thmI h1 T (a7Omega5_of_core C)

end Reduction

end CFSG.ClassicalInvolution.Hat2A7R
