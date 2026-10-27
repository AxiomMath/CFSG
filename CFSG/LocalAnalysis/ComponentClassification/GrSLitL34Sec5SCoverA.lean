module

public import Certificates.Certificate23960
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.HSFLit.AutL34 CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four.Native

variable {G : Type} [Group G] [Finite G]

theorem card_comm_le_two
    {c : Equiv.Perm (Fin 42)} (hcW : c ∈ W) (hc2 : c * c = 1) (hcT : c ∉ T0)
    (hrcT : r₄ * c ∉ T0) :
    Nat.card {g // g ∈ T0 ∧ (g * c = c * g ∧ g * r₄ = r₄ * g)} ≤ 2 := by
  have h := Certificates.certificate23960
  simp only [unitCommOK] at h
  obtain ⟨hcr, hcTR⟩ := mem_inf.mp hcW
  have h1 := List.all_eq_true.mp h (code c) ((mem_TR_iff_code c).mp hcTR)
  have hr : commC (code c) r4c = true := by
    rw [← code_r₄, commC_iff]; exact mem_centralizer_singleton_iff.mp hcr
  have hsq : isId (psq (code c)) = true := by rw [psq_code, isId_iff]; exact hc2
  have hm1 : memB (code c) t0L = false := by
    cases hb : memB (code c) t0L
    · rfl
    · exact absurd ((mem_T0_iff c).mpr ((memB_iff _ _).mp hb)) hcT
  have hm2 : memB (pcomp r4c (code c)) t0L = false := by
    cases hb : memB (pcomp r4c (code c)) t0L
    · rfl
    · exfalso
      apply hrcT
      rw [mem_T0_iff, code_mul, code_r₄]
      exact (memB_iff _ _).mp hb
  simp only [hr, hsq, hm1, hm2, Bool.not_true, Bool.false_or, List.filter_filter] at h1
  rw [card_subtype_eq_countP certParts.nodup mem_T0_iff (fun c hc => (exists_of_mem_t0L hc).imp
    fun g hg => hg.2) (fun g => g * c = c * g ∧ g * r₄ = r₄ * g)
    (fun a => commC a (code c) && commC a r4c)
    (fun g _ => by rw [Bool.and_eq_true, ← code_r₄, commC_iff, commC_iff]),
    List.countP_eq_length_filter]
  exact Nat.le_of_ble_eq_true h1

theorem exists_inner_cover
    {K₁ : Subgroup G} (hperf : ⁅K₁, K₁⁆ = K₁)
    (htype : IsL34Type (K₁ ⧸ Open.fusionZStar K₁)) {t : G} (hunit : IsL34Unitary K₁ t)
    {X : Subgroup G} (hX2 : IsPGroup 2 X) (hXN : X ≤ normalizer (K₁ : Set G))
    (hXC : X ≤ centralizer ({t} : Set G)) {Q₁ : Subgroup G} (hQ₁X : Q₁ ≤ X) (hQ₁K : Q₁ ≤ K₁)
    (hQ₁8 : Nat.card Q₁ = 8) (hker : Nat.card ↥(Q₁ ⊓ coreActionKernel K₁) ≤ 2) {z : G}
    (hzX : z ∈ X) (hz2 : z * z = 1) (hzQ : ∀ q ∈ Q₁, q * z = z * q) :
    ∃ z₀ ∈ ({z, t * z} : Set G), ∃ j ∈ K₁, j⁻¹ * z₀ ∈ coreActionKernel K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρt⟩ := exists_real_unitary hperf htype hunit
  have hzN : z ∈ normalizer (K₁ : Set G) := hXN hzX
  have hXR : ρ.img X ≤ CR4 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hy
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, ρ.mem_R g⟩
    rw [← hρt, ← map_mul, ← map_mul]
    exact congrArg ρ.φ (Subtype.ext (mem_centralizer_singleton_iff.mp (hXC hg)))
  obtain ⟨d, hdC, hd⟩ := exists_conj_mem_of_card W_le_CR4
    (by rw [card_W, card_CR4, factorization_864]; norm_num) hXR (ρ.img_isPGroup hX2)
  have hdR : d ∈ R := (mem_inf.mp hdC).2
  have hdr : d * r₄ = r₄ * d := mem_centralizer_singleton_iff.mp (mem_inf.mp hdC).1
  have key : ∀ (g : G) (hg : g ∈ normalizer (K₁ : Set G)), ρ.φ ⟨g, hg⟩ ∈ S →
      ∃ j ∈ K₁, j⁻¹ * g ∈ coreActionKernel K₁ := by
    intro g hg hgS
    obtain ⟨j, hj, hjg⟩ := ρ.onto_S _ hgS
    refine ⟨j, hj, (ρ.ker_iff ⟨j⁻¹ * g, mul_mem (inv_mem (le_normalizer hj)) hg⟩).mp ?_⟩
    have e : (⟨j⁻¹ * g, mul_mem (inv_mem (le_normalizer hj)) hg⟩ : ↥(normalizer (K₁ : Set G))) =
        (⟨j, le_normalizer hj⟩ : ↥(normalizer (K₁ : Set G)))⁻¹ * ⟨g, hg⟩ := rfl
    rw [e, map_mul, map_inv, hjg, inv_mul_cancel]
  set zb := d * ρ.φ ⟨z, hzN⟩ * d⁻¹ with hzb
  have htz : t * z ∈ normalizer (K₁ : Set G) := mul_mem hunit.1 hzN
  have e4 : r₄ * zb = d * ρ.φ ⟨t * z, htz⟩ * d⁻¹ := by
    have h1 : ρ.φ ⟨t * z, htz⟩ = r₄ * ρ.φ ⟨z, hzN⟩ := by
      rw [← hρt, ← map_mul]
      rfl
    rw [h1, hzb]
    calc r₄ * (d * ρ.φ ⟨z, hzN⟩ * d⁻¹) = (r₄ * d) * ρ.φ ⟨z, hzN⟩ * d⁻¹ := by group
      _ = (d * r₄) * ρ.φ ⟨z, hzN⟩ * d⁻¹ := by rw [hdr]
      _ = d * (r₄ * ρ.φ ⟨z, hzN⟩) * d⁻¹ := by group
  by_cases hzT : zb ∈ T0
  · obtain ⟨j, hj, hjz⟩ := key z hzN (conj_mem_S' hdR (T0_le_S hzT))
    exact ⟨z, Or.inl rfl, j, hj, hjz⟩
  by_cases hrzT : r₄ * zb ∈ T0
  · rw [e4] at hrzT
    obtain ⟨j, hj, hjz⟩ := key (t * z) htz (conj_mem_S' hdR (T0_le_S hrzT))
    exact ⟨t * z, Or.inr rfl, j, hj, hjz⟩
  exfalso
  have hzW : zb ∈ W := hd _ (ρ.phi_mem_img (g := ⟨z, hzN⟩) hzX)
  have hzb2 : zb * zb = 1 := by
    rw [hzb, show d * ρ.φ ⟨z, hzN⟩ * d⁻¹ * (d * ρ.φ ⟨z, hzN⟩ * d⁻¹) =
      d * (ρ.φ ⟨z, hzN⟩ * ρ.φ ⟨z, hzN⟩) * d⁻¹ by group, ← map_mul]
    rw [show (⟨z, hzN⟩ : ↥(normalizer (K₁ : Set G))) * ⟨z, hzN⟩ = 1 from Subtype.ext hz2,
      map_one]
    group
  have hcard := card_comm_le_two hzW hzb2 hzT hrzT
  have hQ₁N : Q₁ ≤ normalizer (K₁ : Set G) := hQ₁X.trans hXN
  set F : ↥Q₁ →* Equiv.Perm (Fin 42) :=
    (MulAut.conj d).toMonoidHom.comp (ρ.φ.comp (Subgroup.inclusion hQ₁N)) with hF
  have hFapp : ∀ q : ↥Q₁, F q = d * ρ.φ ⟨q, hQ₁N q.2⟩ * d⁻¹ := fun q => rfl
  have hFmem : ∀ q : ↥Q₁, F q ∈ T0 ∧ (F q * zb = zb * F q ∧ F q * r₄ = r₄ * F q) := by
    intro q
    have h1 := hd _ (ρ.phi_mem_img (g := ⟨q, hQ₁N q.2⟩) (hQ₁X q.2))
    obtain ⟨h1c, h1T⟩ := mem_inf.mp h1
    refine ⟨?_, ?_, ?_⟩
    · rw [hFapp]
      exact TR_inf_S h1T (conj_mem_S hdR (ρ.map_K q (hQ₁K q.2)))
    · have hqz : (⟨q, hQ₁N q.2⟩ : ↥(normalizer (K₁ : Set G))) * ⟨z, hzN⟩ =
          ⟨z, hzN⟩ * ⟨q, hQ₁N q.2⟩ := Subtype.ext (hzQ q q.2)
      rw [hFapp, hzb]
      calc d * ρ.φ ⟨q, hQ₁N q.2⟩ * d⁻¹ * (d * ρ.φ ⟨z, hzN⟩ * d⁻¹) =
            d * ρ.φ (⟨q, hQ₁N q.2⟩ * ⟨z, hzN⟩) * d⁻¹ := by rw [map_mul]; group
        _ = d * ρ.φ (⟨z, hzN⟩ * ⟨q, hQ₁N q.2⟩) * d⁻¹ := by rw [hqz]
        _ = d * ρ.φ ⟨z, hzN⟩ * d⁻¹ * (d * ρ.φ ⟨q, hQ₁N q.2⟩ * d⁻¹) := by rw [map_mul]; group
    · rw [hFapp]
      exact mem_centralizer_singleton_iff.mp h1c
  have hrange : Nat.card F.range ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun y : F.range => (⟨(y : Equiv.Perm (Fin 42)), by
        obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp y.2
        rw [← hq]
        exact hFmem q⟩ : {g // g ∈ T0 ∧ (g * zb = zb * g ∧ g * r₄ = r₄ * g)})) ?_) hcard
    intro a b hab
    have h := congrArg (fun x : {g // g ∈ T0 ∧ (g * zb = zb * g ∧ g * r₄ = r₄ * g)} =>
      (x : Equiv.Perm (Fin 42))) hab
    exact Subtype.ext h
  have hkerF : Nat.card F.ker ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : F.ker => (⟨((k : ↥Q₁) : G), mem_inf.mpr ⟨(k : ↥Q₁).2, by
        have hk : F k = 1 := k.2
        rw [hFapp] at hk
        refine (ρ.ker_iff ⟨((k : ↥Q₁) : G), hQ₁N (k : ↥Q₁).2⟩).mp ?_
        calc ρ.φ ⟨((k : ↥Q₁) : G), hQ₁N (k : ↥Q₁).2⟩ =
              d⁻¹ * (d * ρ.φ ⟨((k : ↥Q₁) : G), hQ₁N (k : ↥Q₁).2⟩ * d⁻¹) * d := by group
          _ = 1 := by rw [hk]; group⟩⟩ : ↥(Q₁ ⊓ coreActionKernel K₁))) ?_) hker
    intro a b hab
    have h := congrArg (fun x : ↥(Q₁ ⊓ coreActionKernel K₁) => (x : G)) hab
    exact Subtype.ext (Subtype.ext h)
  have h3 := Subgroup.card_ker_mul_card_range F
  rw [hQ₁8] at h3
  have h4 := Nat.mul_le_mul hkerF hrange
  omega

end CFSG.ComponentClassification.HSFLit.L34Inv
