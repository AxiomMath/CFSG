module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsD
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_barX {p q : ℕ} {N T : Subgroup G} (hT : IsPGroup q T) :
    IsPGroup q (barX p N T) :=
  (hT.comap_of_injective N.subtype Subtype.coe_injective).map _

private theorem coprime_card_barX_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) {N K : Subgroup G}
    (hKN : K ≤ N) : Nat.Coprime p (Nat.card (barX p N (GLAPPrimeCoreOf p K))) := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_
  refine not_dvd_card_glaPPrimeCoreOf hp K (hdvd.trans ?_)
  have hle : GLAPPrimeCoreOf p K ≤ N := (Subgroup.map_subtype_le _).trans hKN
  have h1 : Nat.card ((GLAPPrimeCoreOf p K).subgroupOf N) = Nat.card (GLAPPrimeCoreOf p K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← h1]
  exact Subgroup.card_map_dvd _ _

theorem glaPPrimeCoreOf_le_of_barX_component {p : ℕ} (hp : p.Prime) {N K : Subgroup G}
    (hKN : K ≤ N) (hcomp : IsComponentOf (barX p N K) ⊤) :
    GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p N := by
  set Q := barX p N (GLAPPrimeCoreOf p K) with hQ
  have hOK : GLAPPrimeCoreOf p K ≤ K := Subgroup.map_subtype_le _
  have hQK : Q ≤ barX p N K :=
    Subgroup.map_mono (fun x hx => (Subgroup.mem_subgroupOf).2 (hOK ((Subgroup.mem_subgroupOf).1 hx)))
  have hnorm : (Q.subgroupOf (barX p N K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).2
      (barX_le_normalizer (le_normalizer_glaPPrimeCoreOf p K))
  have hsn : IsSubnormal Q ⊤ := IsSubnormal.step hQK hnorm hcomp.2.1
  have hQtop : GLAPPrimeCore p ↥Q = ⊤ :=
    top_le_iff.1 (le_sSup ⟨inferInstance, by
      rw [Subgroup.card_top]; exact coprime_card_barX_glaPPrimeCoreOf hp hKN⟩)
  have hQo : Q ≤ GLAPPrimeCoreOf p Q := by
    unfold GLAPPrimeCoreOf
    rw [hQtop, Subgroup.map_top, Subgroup.range_subtype]
  have htop : GLAPPrimeCoreOf p (⊤ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) = ⊥ := by
    have h1 := glaPPrimeCore_map_iso p
      (Subgroup.topEquiv (G := ↥N ⧸ GLAPPrimeCore p ↥N))
    rw [glaPPrimeCore_quotient_eq_bot hp] at h1
    have hsub : (⊤ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)).subtype =
        (Subgroup.topEquiv (G := ↥N ⧸ GLAPPrimeCore p ↥N)).toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    unfold GLAPPrimeCoreOf
    rw [hsub, h1]
  have hQbot : Q = ⊥ := by
    have := (hQo.trans (glaPPrimeCoreOf_le_of_isSubnormal hp hsn))
    rwa [htop, le_bot_iff] at this
  have hle : GLAPPrimeCoreOf p K ≤ N := hOK.trans hKN
  exact Sec7.le_glaPPrimeCoreOf_of_barX_eq_bot hle hQbot

private theorem ker_barMap_eq_of_le {p : ℕ} (hp : p.Prime) {N K : Subgroup G} (hKN : K ≤ N)
    (hO : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p N) :
    (barMap p hKN).ker = GLAPPrimeCore p ↥K := by
  ext l
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (Subgroup.inclusion hKN l) = 1 :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    set R : Subgroup ↥K := (GLAPPrimeCoreOf p N).subgroupOf K with hR
    have hnorm : R.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_glaPPrimeCoreOf p N (hKN g.2)) (n : G)).1 ((Subgroup.mem_subgroupOf).1 hn)
      exact (Subgroup.mem_subgroupOf).2 (by simpa using h2)
    have hcop : Nat.Coprime p (Nat.card R) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_
      refine not_dvd_card_glaPPrimeCoreOf hp N (hdvd.trans ?_)
      have hc : Nat.card (R.map K.subtype) = Nat.card R :=
        Subgroup.card_map_of_injective K.subtype_injective
      rw [← hc]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hk
    have hRle : R ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hnorm, hcop⟩
    exact hRle ((Subgroup.mem_subgroupOf).2 ⟨_, h1, rfl⟩)
  · intro hl
    have h1 : (l : G) ∈ GLAPPrimeCoreOf p K := ⟨l, hl, rfl⟩
    obtain ⟨c, hc, hcl⟩ := hO h1
    have hcl' : Subgroup.inclusion hKN l = c := Subtype.ext hcl.symm
    refine Subtype.ext ?_
    change QuotientGroup.mk' (GLAPPrimeCore p ↥N) (Subgroup.inclusion hKN l) = 1
    rw [hcl', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc

theorem isLThreeFour_barX {N K : Subgroup G} (hKN : K ≤ N)
    (hO : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 N)
    (h : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)) : IsLThreeFour ↥(barX 3 N K) :=
  IsLThreeFour.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq
      (ker_barMap_eq_of_le Nat.prime_three hKN hO).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (barMap 3 hKN) (barMap_surjective hKN))) h

theorem commutator_le_inf_of_normalizes {Y : Type*} [Group Y] {A T K : Subgroup Y}
    (hAT : A ≤ Subgroup.normalizer (T : Set Y)) (hTK : T ≤ Subgroup.normalizer (K : Set Y))
    (hAK : A ≤ K) : ⁅A, T⁆ ≤ K ⊓ T := by
  rw [Subgroup.commutator_le]
  intro a ha t ht
  refine ⟨?_, ?_⟩
  · have h1 : t * a⁻¹ * t⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK ht) a⁻¹).mp (inv_mem (hAK ha))
    have : ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem (hAK ha) h1
  · have h1 : a * t * a⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hAT ha) t).mp ht
    rw [commutatorElement_def]
    exact T.mul_mem h1 (T.inv_mem ht)

theorem le_normalizer_commutator {Y : Type*} [Group Y] {A T C : Subgroup Y}
    (hCA : C ≤ Subgroup.normalizer (A : Set Y)) (hCT : C ≤ Subgroup.normalizer (T : Set Y)) :
    C ≤ Subgroup.normalizer ((⁅A, T⁆ : Subgroup Y) : Set Y) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ c ∈ C, ∀ x ∈ ⁅A, T⁆, c * x * c⁻¹ ∈ ⁅A, T⁆ := by
    intro c hc x hx
    rw [Subgroup.commutator_def] at hx ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => c * x * c⁻¹ ∈ Subgroup.closure {g | ∃ g₁ ∈ A, ∃ g₂ ∈ T, ⁅g₁, g₂⁆ = g})
      (fun y hy => ?_) (by simp [one_mem]) (fun u v _ _ hu hv => ?_) (fun u _ hu => ?_) hx
    · obtain ⟨a, ha, t, ht, rfl⟩ := hy
      have h1 : c * ⁅a, t⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * t * c⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [h1]
      exact Subgroup.subset_closure ⟨c * a * c⁻¹, (Subgroup.mem_normalizer_iff.mp (hCA hc) a).mp ha,
        c * t * c⁻¹, (Subgroup.mem_normalizer_iff.mp (hCT hc) t).mp ht, rfl⟩
    · have : c * (u * v) * c⁻¹ = (c * u * c⁻¹) * (c * v * c⁻¹) := by group
      rw [this]; exact mul_mem hu hv
    · have : c * u⁻¹ * c⁻¹ = (c * u * c⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hu
  intro x
  exact ⟨key c hc x, fun hx => by
    have := key c⁻¹ (inv_mem hc) _ hx
    simpa [mul_assoc] using this⟩

theorem eq_bot_of_two_group_normalized_by_nine_ambient {Y : Type} [Group Y] [Finite Y]
    {K E S : Subgroup Y} (hK : IsLThreeFour ↥K) (hEK : E ≤ K) (hSK : S ≤ K)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) (hS : IsPGroup 2 S)
    (hES : E ≤ Subgroup.normalizer (S : Set Y)) : S = ⊥ := by
  have hE' : IsElemAbelian 3 (E.subgroupOf K) := isElemAbelian_subgroupOf hE K
  have hEc' : Nat.card (E.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hEc]
  have hS' : IsPGroup 2 (S.subgroupOf K) := hS.comap_subtype
  have hES' : E.subgroupOf K ≤ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [normalizer_subgroupOf_eq hSK]
    intro x hx
    exact (Subgroup.mem_subgroupOf).2 (hES ((Subgroup.mem_subgroupOf).1 hx))
  have hbot := eq_bot_of_two_group_normalized_by_nine hK hE' hEc' hS' hES'
  refine (Subgroup.eq_bot_iff_forall S).2 fun s hs => ?_
  have : (⟨s, hSK hs⟩ : ↥K) ∈ S.subgroupOf K := (Subgroup.mem_subgroupOf).2 hs
  rw [hbot, Subgroup.mem_bot] at this
  simpa using congrArg Subtype.val this

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
