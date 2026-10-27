module

public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map_conj {E : Subgroup G} (hE : IsElemAbelian 2 E) (g : G) :
    IsElemAbelian 2 (E.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _


theorem exists_isMax_mem_of_conj_transvection
    {V R T A : Subgroup G} [V.Normal] [R.Normal] (hV : IsElemAbelian 2 V) (hVR : V ≤ R)
    (hVc : ∀ v ∈ V, ∀ r ∈ R, v * r = r * v)
    (hRC : Subgroup.centralizer (V : Set G) = R) (hRT : R ≤ T)
    (hA : IsMaxElemAbelian T A) (hw : Nat.card V = wtG V A)
    {t : G} (ht : t ∈ A)
    (htv : Nat.card V = 2 * Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)))
    {g : G} (hu : g * t * g⁻¹ ∈ T) :
    ∃ E : Subgroup G, IsMaxElemAbelian T E ∧ g * t * g⁻¹ ∈ E := by
  classical
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAT : A ≤ T := hA.1
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => isElemAbelian_comm' hAe ha hb
  have hVT : V ≤ T := hVR.trans hRT
  set AQ : Subgroup G := A ⊓ R with hAQ
  set CVA : Subgroup G := V ⊓ Subgroup.centralizer (A : Set G) with hCVA
  set CVt : Subgroup G := V ⊓ Subgroup.centralizer ({t} : Set G) with hCVt
  have hCVA_le_A : CVA ≤ A := by
    have hcomm : ∀ x ∈ A, ∀ y ∈ CVA, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp hy.2 x hx
    have hsup := isElemAbelian_sup' hAe (isElemAbelian_mono' hV inf_le_left) hcomm
    have hle : Nat.card ↥(A ⊔ CVA) ≤ Nat.card A :=
      hA.2.2 _ (sup_le hAT (inf_le_left.trans hVT)) hsup
    have : A = A ⊔ CVA := Subgroup.eq_of_le_of_card_ge le_sup_left hle
    rw [this]
    exact le_sup_right
  have htR : t ∉ R := by
    intro htR
    rw [← hRC] at htR
    have : CVt = V := by
      refine le_antisymm inf_le_left fun v hv => ⟨hv, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp htR v hv).symm
    rw [this] at htv
    have := Nat.card_pos (α := V)
    omega
  have ht2 : t * t = 1 := by
    have := hAe.2 t ht
    rwa [pow_two] at this
  have htne : t ≠ 1 := fun h => htR (h ▸ R.one_mem)
  have hVA : V ⊓ A = CVA := by
    ext x
    simp only [Subgroup.mem_inf, hCVA, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hxV, hxA⟩
      exact ⟨hxV, fun a ha => hcommA a ha x hxA⟩
    · rintro ⟨hxV, hx⟩
      exact ⟨hxV, hCVA_le_A ⟨hxV, Subgroup.mem_centralizer_iff.mpr hx⟩⟩
  set E0 : Subgroup G := CVt ⊔ AQ with hE0
  set E' : Subgroup G := E0 ⊔ Subgroup.zpowers t with hE'
  have hCVt_le : CVt ≤ R := inf_le_left.trans hVR
  have hAQ_le : AQ ≤ R := inf_le_right
  have hE0R : E0 ≤ R := sup_le hCVt_le hAQ_le
  have hCommE0 : ∀ x ∈ CVt, ∀ y ∈ AQ, x * y = y * x := fun x hx y hy => hVc x hx.1 y hy.2
  have hCVtAQ : CVt ⊓ AQ = CVA := by
    ext x
    simp only [Subgroup.mem_inf, hCVt, hAQ, hCVA, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨⟨hxV, _⟩, hxA, _⟩
      exact ⟨hxV, fun a ha => hcommA a ha x hxA⟩
    · rintro ⟨hxV, hx⟩
      have hxA : x ∈ A := hCVA_le_A ⟨hxV, Subgroup.mem_centralizer_iff.mpr hx⟩
      exact ⟨⟨hxV, hx t ht⟩, hxA, hVR hxV⟩
  have hcard0 := card_sup_mul_card_inf' hCommE0
  rw [hCVtAQ] at hcard0
  have hE0t : E0 ≤ Subgroup.centralizer ({t} : Set G) := by
    refine sup_le inf_le_right fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    exact hcommA t ht x hx.1
  have htcE0 : t ∈ Subgroup.centralizer (E0 : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hE0t hx) t (Set.mem_singleton t)).symm
  have hzc : ∀ x ∈ E0, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr htcE0 hy) x hx
  have hcard1 := card_sup_mul_card_inf' hzc
  have hz : ∀ x ∈ Subgroup.zpowers t, x = 1 ∨ x = t := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [← hk, hm, zpow_mul, h2, one_zpow]
    · right
      rw [← hk, hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  have hbot : E0 ⊓ Subgroup.zpowers t = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    rcases hz x hx.2 with h | h
    · exact h
    · exact absurd (hE0R (h ▸ hx.1)) htR
  rw [hbot, Subgroup.card_bot] at hcard1
  have hordt : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) htne
  have hcardz : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hordt]
  rw [hcardz] at hcard1
  have hAcard : AQ.relIndex A * Nat.card AQ = Nat.card A := by
    have := Subgroup.relIndex_mul_card AQ A
    rwa [inf_of_le_left (inf_le_left : AQ ≤ A)] at this
  have hw' : Nat.card V = AQ.relIndex A * Nat.card CVA := by
    rw [hw]
    unfold wtG
    rw [hRC]
  have hCVA_pos : 0 < Nat.card CVA := Nat.card_pos
  have hE0card : 2 * Nat.card E0 = Nat.card A := by
    have h1 : 2 * Nat.card E0 * Nat.card CVA = Nat.card A * Nat.card CVA := by
      calc 2 * Nat.card E0 * Nat.card CVA = 2 * (Nat.card E0 * Nat.card CVA) := by ring
        _ = 2 * (Nat.card CVt * Nat.card AQ) := by rw [hcard0]
        _ = (2 * Nat.card CVt) * Nat.card AQ := by ring
        _ = Nat.card V * Nat.card AQ := by rw [← htv]
        _ = (AQ.relIndex A * Nat.card CVA) * Nat.card AQ := by rw [hw']
        _ = (AQ.relIndex A * Nat.card AQ) * Nat.card CVA := by ring
        _ = Nat.card A * Nat.card CVA := by rw [hAcard]
    exact Nat.eq_of_mul_eq_mul_right hCVA_pos h1
  have hE'card : Nat.card E' = Nat.card A := by
    have : Nat.card E' * 1 = Nat.card E0 * 2 := by
      have := hcard1
      simpa using this
    omega
  have hE0e : IsElemAbelian 2 E0 :=
    isElemAbelian_sup' (isElemAbelian_mono' hV inf_le_left) (isElemAbelian_mono' hAe inf_le_left)
      hCommE0
  have hze : IsElemAbelian 2 (Subgroup.zpowers t) :=
    isElemAbelian_mono' hAe (Subgroup.zpowers_le.mpr ht)
  have hE'e : IsElemAbelian 2 E' := isElemAbelian_sup' hE0e hze hzc
  set E : Subgroup G := E'.map (MulAut.conj g).toMonoidHom with hE
  have hEe : IsElemAbelian 2 E := isElemAbelian_map_conj hE'e g
  have hEcard : Nat.card E = Nat.card A := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE'card]
  have hET : E ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hle : E' ≤ T.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        exact hVT ((inferInstance : V.Normal).conj_mem y hy.1 g)
      · intro y hy
        exact hRT ((inferInstance : R.Normal).conj_mem y (hAQ_le hy) g)
      · refine Subgroup.zpowers_le.mpr ?_
        show g * t * g⁻¹ ∈ T
        exact hu
    exact hle hx
  refine ⟨E, ⟨hET, hEe, fun B hBT hBe => ?_⟩,
    ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), rfl⟩⟩
  rw [hEcard]
  exact hA.2.2 B hBT hBe

end CFSG.CGT.PushingUpLit.CGT6
