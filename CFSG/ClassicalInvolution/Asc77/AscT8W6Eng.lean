module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8Four

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

variable {H : Type} [Group H] [Finite H]

theorem isConj_or_mem_omegaNbr_genE {Λ : Set (Subgroup H)} (hcl : ConjInvariant Λ)
    (hsyl : ∀ {M R : Subgroup H}, M ∈ Λ → R ∈ RSet Λ → R ≤ M → IsSylow2In R M)
    (hR8 : ∀ {R : Subgroup H}, R ∈ RSet Λ → 8 ≤ Nat.card R) {K : Subgroup H} (hK : K ∈ Λ)
    (hAE : AEmpty Λ K) (hnt : ∀ K' ∈ twinSet Λ K, K' = K) {z : H}
    (hz : IsUniqueInvolution K z)
    (h62 : ∀ J ∈ Λ, J ∉ twinSet Λ K → ∀ t : H, IsUniqueInvolution J t →
      ∀ V : Subgroup H, IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set H)) → t ∈ V →
        (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
        (V = Subgroup.zpowers t ∧ V ≤ Subgroup.normalizer (K : Set H) ∧
          ∃ R ∈ RSet Λ, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set H) ∧
            IsSemidihedral (R ⊔ V)) ∨
        (V ∈ USet Λ ∧ V ≤ Subgroup.normalizer (K : Set H) ∧
          ∃ R ∈ RSet Λ, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set H) ∧
            IsWreathed (R ⊔ V)) ∨
        (V ∈ RSet Λ ∧ ⁅V, K⁆ ≤ oddCoreOf K)) {g : H}
    (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    IsConj z (z * (g⁻¹ * z * g)) ∨ conjSub g⁻¹ K ∈ omegaNbr Λ K := by
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * z * g := ⟨_, rfl⟩
  rw [← hbdef] at hne hcomm ⊢
  obtain ⟨L, hLdef⟩ : ∃ L, L = conjSub g⁻¹ K := ⟨_, rfl⟩
  rw [← hLdef]
  have hLΩ : L ∈ Λ := hLdef ▸ hcl g⁻¹ K hK
  have hb : IsUniqueInvolution L b := by
    have := hz.conj g⁻¹
    rwa [inv_inv, ← hbdef, ← hLdef] at this
  have hbz : IsConj z b := isConj_iff.mpr ⟨g⁻¹, by rw [hbdef, inv_inv]⟩
  have hLK : L ≠ K := by
    intro h
    rcases hz.unique b (h ▸ hb.mem) hb.sq with h1 | h1
    · exact hb.ne_one h1
    · exact hne h1
  have hLtw : L ∉ twinSet Λ K := fun h => hLK (hnt L h)
  have hCz : Subgroup.centralizer ({z} : Set H) ≤ Subgroup.normalizer (K : Set H) :=
    T8.centralizer_le_normalizer_of_noTwins hcl hK hnt hz
  have hbC : b ∈ Subgroup.centralizer ({z} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hb2 : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb.sq) hb.ne_one)
  have hbLC : Subgroup.zpowers b ≤ L ⊓ Subgroup.centralizer ({z} : Set H) :=
    Subgroup.zpowers_le.mpr ⟨hb.mem, hbC⟩
  obtain ⟨V, hV, hbV⟩ := IsSylow2In.exists_ge hb2 hbLC
  have h62 := h62 L hLΩ hLtw b hb V hV
    (hbV (Subgroup.mem_zpowers b))
  rcases h62 with ⟨-, h1⟩ | ⟨hVb, -, R', hR'Ω, hR'K, hVR', hsd⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, -⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hCz hbC)) h1
  · left
    have hR'syl : IsSylow2In R' K := hsyl hK hR'Ω hR'K
    have h8 := hR8 hR'Ω
    have hzR' : z ∈ R' := T3.mem_of_isPGroup hz hR'K hR'syl.2.1 (by omega)
    have hz' : IsUniqueInvolution R' z :=
      AscP1Nine3.uniqueInvolution_restrict hz hR'K hzR'
    have hbR' : b ∉ R' := by
      intro h
      rcases hz.unique b (hR'K h) hb.sq with h1 | h1
      · exact hb.ne_one h1
      · exact hne h1
    rw [hVb] at hVR' hsd
    obtain ⟨r, -, hr⟩ := AschTight.exists_conj_eq_mul_of_isSemidihedral hR'syl.2.1 hz' hb.sq hbR'
      (hVR' (Subgroup.mem_zpowers b)) hsd
    exact hbz.trans (isConj_iff.mpr ⟨r, hr⟩)
  · have hLs : L ∈ omegaStarNbr Λ K := ⟨hLΩ, hLK, V, hVU, hV.1.trans inf_le_left, hVN⟩
    by_cases hω : L ∈ omegaNbr Λ K
    · exact Or.inr hω
    · exact Or.inl (T8.isConj_mul_of_aEmpty hAE hLs hω hz hb hcomm hne hbz)
  · right
    exact ⟨hLΩ, hLK, V, hVR, hV.1.trans inf_le_left, (hV.1.trans inf_le_right).trans hCz⟩

end T8W

end CFSG.ClassicalInvolution.Asc77
