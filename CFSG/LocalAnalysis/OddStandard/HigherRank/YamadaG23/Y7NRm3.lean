module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NRm2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma conjSub_le_of_le {H K : Subgroup G} {x : G} (hHK : H ≤ K)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) : conjSub x H ≤ K := by
  intro y hy
  rw [mem_conjSub_iff'] at hy
  obtain ⟨h, hh, rfl⟩ := hy
  exact ((Subgroup.mem_normalizer_iff (H := K)).mp hx h).mp (hHK hh)

private lemma le_normalizer_conjSub {H K : Subgroup G} {x : G}
    (hHK : K ≤ Subgroup.normalizer (H : Set G)) (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    K ≤ Subgroup.normalizer (conjSub x H : Set G) := by
  have hxK : K.map (MulAut.conj x).toMonoidHom = K :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := K) (g := x)).mp hx
  calc
    K = K.map (MulAut.conj x).toMonoidHom := hxK.symm
    _ ≤ (Subgroup.normalizer (H : Set G)).map (MulAut.conj x).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hHK
    _ ≤ Subgroup.normalizer
          ((H.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map (H := H) (f := (MulAut.conj x).toMonoidHom)
    _ = Subgroup.normalizer (conjSub x H : Set G) := rfl

theorem y7n_conj_comp_mem {K A B M : Subgroup G} (hA : SimpleSec A M) (hB : SimpleSec B M)
    (hsup : A ⊔ B = K) (hinf : A ⊓ B = M) (hcomm : ⁅A, B⁆ ≤ M) (hM2 : IsPGroup 2 M) {x : G}
    (hx : x ∈ normalizer (K : Set G)) : conjSub x A = A ∨ conjSub x A = B := by
  have hMA : M ≤ A := hA.le
  have hMB : M ≤ B := hB.le
  have hAK : A ≤ K := hsup ▸ le_sup_left
  have hBK : B ≤ K := hsup ▸ le_sup_right
  have hMK : M ≤ K := hMA.trans hAK
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_comm]
    exact hcomm.trans (hinf ▸ inf_le_left)
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact hcomm.trans (hinf ▸ inf_le_right)
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hsup]
    exact sup_le (Subgroup.le_normalizer (H := A)) hBA
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := by
    rw [← hsup]
    exact sup_le hAB (Subgroup.le_normalizer (H := B))
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := by
    have hAn : A ≤ Subgroup.normalizer (M : Set G) :=
      (Subgroup.le_normalizer_iff (H := A) (K := M)).mpr hA.normal
    have hBn : B ≤ Subgroup.normalizer (M : Set G) :=
      (Subgroup.le_normalizer_iff (H := B) (K := M)).mpr hB.normal
    rw [← hsup]
    exact sup_le hAn hBn
  have hKM' : K ≤ Subgroup.normalizer (conjSub x M : Set G) := le_normalizer_conjSub hKM hx
  have hM'_le : conjSub x M ≤ M :=
    y7n_normal_two_le hA hB hsup hinf hcomm hM2 (conjSub_le_of_le hMK hx)
      (fun k hk q hq => Subgroup.le_normalizer_iff.mp hKM' k hk q hq)
      (hM2.map (MulAut.conj x).toMonoidHom)
  have hM'card : Nat.card (conjSub x M) = Nat.card M :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hM'eq : conjSub x M = M :=
    Subgroup.eq_of_le_of_card_ge hM'_le (by rw [hM'card])
  have hMA' : M ≤ conjSub x A :=
    hM'eq ▸ Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hMA
  have hA'K : conjSub x A ≤ K := conjSub_le_of_le hAK hx
  have hA'card : Nat.card (conjSub x A) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hKA' : K ≤ Subgroup.normalizer (conjSub x A : Set G) := le_normalizer_conjSub hKA hx
  have hAnormA' : A ≤ Subgroup.normalizer (conjSub x A : Set G) := hAK.trans hKA'
  have hA'normA : conjSub x A ≤ Subgroup.normalizer (A : Set G) := hA'K.trans hKA
  have hBnormA' : B ≤ Subgroup.normalizer (conjSub x A : Set G) := hBK.trans hKA'
  have hA'normB : conjSub x A ≤ Subgroup.normalizer (B : Set G) := hA'K.trans hKB
  have hcommA'A : ⁅conjSub x A, A⁆ ≤ conjSub x A :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := A) (K := conjSub x A)).mp hAnormA'
  have hcommA'A' : ⁅conjSub x A, A⁆ ≤ A :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := conjSub x A) (K := A)).mp hA'normA
  have hcommA'B : ⁅conjSub x A, B⁆ ≤ conjSub x A :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := B) (K := conjSub x A)).mp hBnormA'
  have hcommA'B' : ⁅conjSub x A, B⁆ ≤ B :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := conjSub x A) (K := B)).mp hA'normB
  have hDnorm : ∀ a ∈ A, ∀ d ∈ conjSub x A ⊓ A, a * d * a⁻¹ ∈ conjSub x A ⊓ A := by
    intro a ha d hd
    exact ⟨Subgroup.le_normalizer_iff.mp hKA' a (hAK ha) d hd.1,
      A.mul_mem (A.mul_mem ha hd.2) (A.inv_mem ha)⟩
  rcases hA.simple (conjSub x A ⊓ A) (le_inf hMA' hMA) inf_le_right hDnorm with hD | hD
  ·
    have hEnorm : ∀ b ∈ B, ∀ d ∈ conjSub x A ⊓ B, b * d * b⁻¹ ∈ conjSub x A ⊓ B := by
      intro b hb d hd
      exact ⟨Subgroup.le_normalizer_iff.mp hKA' b (hBK hb) d hd.1,
        B.mul_mem (B.mul_mem hb hd.2) (B.inv_mem hb)⟩
    rcases hB.simple (conjSub x A ⊓ B) (le_inf hMA' hMB) inf_le_right hEnorm with hE | hE
    ·
      exfalso
      have hA'M : conjSub x A ≤ M := by
        intro a' ha'
        have ha'K : a' ∈ K := hA'K ha'
        have hdecomp : (↑K : Set G) = (A : Set G) * (B : Set G) := by
          rw [← hsup]
          exact Subgroup.coe_mul_of_right_le_normalizer_left A B hBA
        have ha'K' : a' ∈ (↑K : Set G) := ha'K
        rw [hdecomp] at ha'K'
        obtain ⟨a₀, ha₀, b₀, hb₀, hmul⟩ := ha'K'
        have hmul' : a₀ * b₀ = a' := hmul
        have hcentA : ∀ b ∈ A, ⁅a₀, b⁆ ∈ M := by
          intro b hb
          have hmem : ⁅a', b⁆ ∈ M := by
            rw [← hD]
            exact ⟨hcommA'A (Subgroup.commutator_mem_commutator ha' hb),
              hcommA'A' (Subgroup.commutator_mem_commutator ha' hb)⟩
          have hb0b : ⁅b₀, b⁆ ∈ M := by
            have h : ⁅B, A⁆ ≤ M := by rw [Subgroup.commutator_comm]; exact hcomm
            exact h (Subgroup.commutator_mem_commutator hb₀ hb)
          have hm1 : a₀ * ⁅b₀, b⁆ * a₀⁻¹ ∈ M := hA.normal a₀ ha₀ _ hb0b
          have hy : a₀ * ⁅b₀, b⁆ * a₀⁻¹ * ⁅a₀, b⁆ ∈ M := by
            rw [← commutatorElement_mul_left_eq_conj_mul, hmul']
            exact hmem
          have hxeq : (a₀ * ⁅b₀, b⁆ * a₀⁻¹)⁻¹ *
              (a₀ * ⁅b₀, b⁆ * a₀⁻¹ * ⁅a₀, b⁆) = ⁅a₀, b⁆ := by group
          have h := M.mul_mem (M.inv_mem hm1) hy
          rwa [hxeq] at h
        have ha₀M : a₀ ∈ M := hA.central a₀ ha₀ hcentA
        have hcentB : ∀ b ∈ B, ⁅b₀, b⁆ ∈ M := by
          intro b hb
          have hmem : ⁅a', b⁆ ∈ M := by
            rw [← hE]
            exact ⟨hcommA'B (Subgroup.commutator_mem_commutator ha' hb),
              hcommA'B' (Subgroup.commutator_mem_commutator ha' hb)⟩
          have ha0b : ⁅a₀, b⁆ ∈ M := hcomm (Subgroup.commutator_mem_commutator ha₀ hb)
          have hy : a₀ * ⁅b₀, b⁆ * a₀⁻¹ * ⁅a₀, b⁆ ∈ M := by
            rw [← commutatorElement_mul_left_eq_conj_mul, hmul']
            exact hmem
          have hz : a₀ * ⁅b₀, b⁆ * a₀⁻¹ ∈ M := by
            have hzeq : (a₀ * ⁅b₀, b⁆ * a₀⁻¹ * ⁅a₀, b⁆) * ⁅a₀, b⁆⁻¹ =
                a₀ * ⁅b₀, b⁆ * a₀⁻¹ := by group
            have h := M.mul_mem hy (M.inv_mem ha0b)
            rwa [hzeq] at h
          have hconj := hA.normal a₀⁻¹ (A.inv_mem ha₀) _ hz
          have heq : a₀⁻¹ * (a₀ * ⁅b₀, b⁆ * a₀⁻¹) * (a₀⁻¹)⁻¹ = ⁅b₀, b⁆ := by group
          rwa [heq] at hconj
        have hb₀M : b₀ ∈ M := hB.central b₀ hb₀ hcentB
        exact hmul' ▸ M.mul_mem ha₀M hb₀M
      have hcard : Nat.card (conjSub x A) = 168 * Nat.card M := by
        rw [hA'card, hA.card]
      have hle : Nat.card (conjSub x A) ≤ Nat.card M := Subgroup.card_le_of_le hA'M
      have hpos : 0 < Nat.card M := Nat.card_pos
      omega
    ·
      right
      have hBeA' : B ≤ conjSub x A := by
        have h : conjSub x A ⊓ B ≤ conjSub x A := inf_le_left
        rwa [hE] at h
      have hcard : Nat.card (conjSub x A) = Nat.card B := by
        rw [hA'card, hA.card, hB.card]
      exact (Subgroup.eq_of_le_of_card_ge hBeA' (le_of_eq hcard)).symm
  ·
    left
    have hAleA' : A ≤ conjSub x A := by
      have h : conjSub x A ⊓ A ≤ conjSub x A := inf_le_left
      rwa [hD] at h
    have hcard : Nat.card (conjSub x A) = Nat.card A := hA'card
    exact (Subgroup.eq_of_le_of_card_ge hAleA' (le_of_eq hcard)).symm

theorem y7n_perm_of_comp {K A B M : Subgroup G} (hA : SimpleSec A M) (hB : SimpleSec B M)
    (hsup : A ⊔ B = K) (hinf : A ⊓ B = M) (hcomm : ⁅A, B⁆ ≤ M) (hM2 : IsPGroup 2 M) {x : G}
    (hx : x ∈ normalizer (K : Set G)) :
    (conjSub x A = A ∧ conjSub x B = B) ∨ (conjSub x A = B ∧ conjSub x B = A) := by
  have hA' : conjSub x A = A ∨ conjSub x A = B :=
    y7n_conj_comp_mem hA hB hsup hinf hcomm hM2 hx
  have hB' : conjSub x B = A ∨ conjSub x B = B := by
    have h := y7n_conj_comp_mem (K := K) (A := B) (B := A) (M := M) hB hA
      (by rw [sup_comm]; exact hsup) (by rw [inf_comm]; exact hinf)
      (by rw [Subgroup.commutator_comm]; exact hcomm) hM2 hx
    exact h.elim Or.inr Or.inl
  have hneAB : A ≠ B := by
    intro h
    have hAM : A = M := by rw [← hinf, h, inf_idem]
    have hcard : Nat.card M = 168 * Nat.card M := by rw [← hA.card, hAM]
    have hpos : 0 < Nat.card M := Nat.card_pos
    omega
  have hne : conjSub x A ≠ conjSub x B := by
    intro h
    exact hneAB (Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective h)
  rcases hA' with hA' | hA' <;> rcases hB' with hB' | hB'
  · exact absurd (hA'.trans hB'.symm) hne
  · exact Or.inl ⟨hA', hB'⟩
  · exact Or.inr ⟨hA', hB'⟩
  · exact absurd (hA'.trans hB'.symm) hne

end CFSG.OddStandard.HigherRank.YamadaG23
