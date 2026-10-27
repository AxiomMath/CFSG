module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSieve
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4Structure
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleCentralizerData
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleObligations
public import CFSG.HardMathSupport.Malle.OvergroupTransport.CaseOne
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Generation

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.AGLEmbedding CFSG.Open CFSG.HardMathSupport.Malle.OvergroupTransport

variable {Y : Type} [Group Y] [Finite Y]

theorem maximal_normalizer_of_socle' {p : ℕ} [Fact p.Prime] {K T : Subgroup Y} [K.Normal]
    (hKT : K ⊔ T = ⊤)
    (hp : IsPGroup p ↥(T ⊓ K)) (hidx : ¬ p ∣ (T ⊓ K).relIndex K)
    (hN : Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) ≤ Subgroup.normalizer (T : Set Y))
    (hmax : ∀ H : Subgroup Y, H ≤ K → T ≤ Subgroup.normalizer (H : Set Y) →
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) ≤ H →
        H = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) ∨ H = K)
    (H : Subgroup Y) (hH : Subgroup.normalizer (T : Set Y) ≤ H) :
    H = Subgroup.normalizer (T : Set Y) ∨ H = ⊤ := by
  have hTM : T ⊓ K ≤ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hMK : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) ≤ K := inf_le_left
  have hMH : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) ≤ H ⊓ K :=
    le_inf (inf_le_right.trans (hN.trans hH)) hMK
  have hTH : T ≤ H := Subgroup.le_normalizer.trans hH
  have hTn : T ≤ Subgroup.normalizer ((H ⊓ K : Subgroup Y) : Set Y) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro m
    have hKm : ∀ z : Y, z ∈ K ↔ t * z * t⁻¹ ∈ K := by
      intro z
      constructor
      · intro hz
        exact Subgroup.Normal.conj_mem inferInstance z hz t
      · intro hz
        have := Subgroup.Normal.conj_mem inferInstance _ hz t⁻¹
        simpa [mul_assoc] using this
    have hHt := hTH ht
    have hHm : ∀ z : Y, z ∈ H ↔ t * z * t⁻¹ ∈ H := by
      intro z
      constructor
      · intro hz
        exact H.mul_mem (H.mul_mem hHt hz) (H.inv_mem hHt)
      · intro hz
        have := H.mul_mem (H.mul_mem (H.inv_mem hHt) hz) hHt
        simpa [mul_assoc] using this
    simp only [Subgroup.mem_inf]
    rw [hHm m, hKm m]
  rcases hmax (H ⊓ K) inf_le_right hTn hMH with h | h
  · left
    refine le_antisymm (fun g hgH => ?_) hH
    have hgM : g ∈ Subgroup.normalizer
        ((K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro m
      rw [← h]
      constructor
      · rintro ⟨hmH, hmK⟩
        exact ⟨H.mul_mem (H.mul_mem hgH hmH) (H.inv_mem hgH),
          Subgroup.Normal.conj_mem inferInstance m hmK g⟩
      · rintro ⟨hmH, hmK⟩
        refine ⟨?_, ?_⟩
        · have := H.mul_mem (H.mul_mem (H.inv_mem hgH) hmH) hgH
          simpa [mul_assoc] using this
        · have := Subgroup.Normal.conj_mem inferInstance _ hmK g⁻¹
          simpa [mul_assoc] using this
    refine hN ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_of_normalizes_overgroup hTM hMK hp hidx inf_le_right hgM hx, ?_⟩
    intro hx
    have hg' : g⁻¹ ∈ Subgroup.normalizer
        ((K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) : Subgroup Y) : Set Y) :=
      Subgroup.inv_mem _ hgM
    simpa [mul_assoc] using
      conj_mem_of_normalizes_overgroup hTM hMK hp hidx inf_le_right hg' hx
  · right
    have hK : K ≤ H := h ▸ inf_le_left
    rw [eq_top_iff, ← hKT]
    exact sup_le hK hTH

theorem reeF4NormalizerMaximal_of_caseTwoInvariant
    (hData : OvergroupTransport.ReeF4SocleLineData)
    (hInv : Coordinator.ReeF4CaseTwoInvariant)
    (hAut : OvergroupTransport.ReeF4SocleAutOrder)
    (hRank : OvergroupTransport.ReeF4SocleFiveRank)
    (hNorm : OvergroupTransport.ReeF4SocleSylowNormal) :
    OvergroupTransport.ReeF4NormalizerMaximal := by
  intro Y _ _ K d hd hKn hiso hC T h3 H hH
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrk' : ∀ P : Subgroup Y, P ≤ K → IsPGroup 5 ↥P → CFSG.Open.pRank 5 P ≤ 2 := by
    intro P hPK hP
    have := hRank ↥K d hd hiso (P.subgroupOf K) (hP.comap_subtype (K := K))
    rwa [pRank_subgroupOf 5 hPK] at this
  have hKT : K ⊔ (T : Subgroup Y) = ⊤ :=
    ambient_sup_eq_top hC (hAut ↥K d hd hiso) hrk' T h3
  have hp : IsPGroup 5 ↥((T : Subgroup Y) ⊓ K) := T.isPGroup'.to_inf_left
  have hidx : ¬ 5 ∣ ((T : Subgroup Y) ⊓ K).relIndex K := not_dvd_relIndex_inf_sylow K T
  let P : Sylow 5 ↥K := (hp.comap_subtype (K := K)).toSylow hidx
  have hP : (P : Subgroup ↥K) = ((T : Subgroup Y) ⊓ K).subgroupOf K := rfl
  have hmax : ∀ H₀ : Subgroup Y, H₀ ≤ K → (T : Subgroup Y) ≤ Subgroup.normalizer (H₀ : Set Y) →
      K ⊓ Subgroup.normalizer (((T : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ H₀ →
        H₀ = K ⊓ Subgroup.normalizer (((T : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ∨ H₀ = K := by
    intro H₀ hH₀K hTnorm hNle
    by_contra hcon
    push Not at hcon
    obtain ⟨hH₀ne, hH₀K'⟩ := hcon
    obtain ⟨Z, hZ, hab, hZc, hD, hTr⟩ := hData ↥K d hd hiso P
    have hZ5 : ∀ x ∈ Z, x ^ 5 = 1 := fun x hx => ((hZ x).1 hx).2
    have hGen := OvergroupTransport.closure_cenGen_eq_top_of_catGroup hd hiso.some Z hZ5 hZc
    have hNP : Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) ≤ H₀.subgroupOf K := by
      rw [hP, ← Subgroup.subgroupOf_normalizer_eq (inf_le_right :
        (T : Subgroup Y) ⊓ K ≤ K)]
      intro x hx
      exact hNle ⟨x.2, hx⟩
    have hM₁ : H₀.subgroupOf K ≠ ⊤ := by
      intro htop
      exact hH₀K' (le_antisymm hH₀K (Subgroup.subgroupOf_eq_top.mp htop))
    have hC' := centralizer_le_of_proper_overgroup
      (N := Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K)) (M₁ := H₀.subgroupOf K) (Z := Z)
      hNP hM₁ hD hTr hGen
    have hcent : ∀ x ∈ (T : Subgroup Y) ⊓ K, x ^ 5 = 1 → x ≠ 1 →
        H₀ ⊓ Subgroup.centralizer ({x} : Set Y) ≤
          Subgroup.normalizer (((T : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
      intro x hx h5 h1 g hg
      have hxK : x ∈ K := hx.2
      have hxZ : (⟨x, hxK⟩ : ↥K) ∈ Z := by
        rw [hZ]
        refine ⟨?_, Subtype.ext (by simpa using h5)⟩
        rw [hP]
        exact hx
      have hx1 : (⟨x, hxK⟩ : ↥K) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
      have hgK : g ∈ K := hH₀K hg.1
      have hmem : (⟨g, hgK⟩ : ↥K) ∈
          H₀.subgroupOf K ⊓ Subgroup.centralizer ({(⟨x, hxK⟩ : ↥K)} : Set ↥K) := by
        refine ⟨hg.1, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        have := (Subgroup.mem_centralizer_iff.mp hg.2) x rfl
        exact Subtype.ext this
      have h2 := hC' _ hxZ hx1 hmem
      rw [hP, ← Subgroup.subgroupOf_normalizer_eq (inf_le_right :
        (T : Subgroup Y) ⊓ K ≤ K)] at h2
      exact h2
    exact hH₀ne (hInv Y K d hd hKn hiso hC T h3 H₀ hH₀K hTnorm hNle hH₀K' hcent)
  exact maximal_normalizer_of_socle' hKT hp hidx (hNorm Y K d hd hKn hiso hC T h3) hmax H hH

theorem kFactReeF4Local_of_caseTwoInvariant
    (hInv : Coordinator.ReeF4CaseTwoInvariant) : CFSG.AGLEmbedding.KFactReeF4Local :=
  kFactReeF4Local_of_structure_of_maximal reeF4NormalizerStructure_of_certs
    (reeF4NormalizerMaximal_of_caseTwoInvariant reeF4SocleLineData_of_certs hInv
      reeF4SocleAutOrder_of_certs reeF4SocleFiveRank_of_certs reeF4SocleSylowNormal_of_certs)

end CFSG.HardMathSupport.Malle.LocalAction
