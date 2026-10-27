module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvL2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make
public import Certificates.Certificate22803
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Real2

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.HSFLit.AutL34 CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four.Native

variable {G : Type} [Group G] [Finite G]

theorem card_T0_cent_r₄ :
    Nat.card {g // g ∈ T0 ∧ g * r₄ = r₄ * g} = 8 := by
  have h := Certificates.certificate22803
  simp only [unitNormOK, Bool.and_eq_true, Nat.beq_eq] at h
  rw [card_subtype_eq_countP certParts.nodup mem_T0_iff (fun c hc => (exists_of_mem_t0L hc).imp
    fun g hg => hg.2) (fun g => g * r₄ = r₄ * g) (fun c => commC c r4c)
    (fun g _ => by rw [← code_r₄, commC_iff]), List.countP_eq_length_filter]
  exact h.1

theorem exists_move
    {c : Equiv.Perm (Fin 42)} (hcW : c ∈ W) (hc2 : c * c = 1) (hcT : c ∉ T0)
    (hrcT : r₄ * c ∉ T0) :
    ∃ a ∈ T0, a * r₄ = r₄ * a ∧ a * c * a⁻¹ ≠ c ∧ a * c * a⁻¹ ≠ r₄ * c := by
  have h := Certificates.certificate22803
  simp only [unitNormOK, Bool.and_eq_true] at h
  obtain ⟨hcr, hcTR⟩ := mem_inf.mp hcW
  have h1 := List.all_eq_true.mp h.2 (code c) ((mem_TR_iff_code c).mp hcTR)
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
  simp only [hr, hsq, hm1, hm2, Bool.not_true, Bool.false_or] at h1
  obtain ⟨a, ha, ha'⟩ := List.any_eq_true.mp h1
  obtain ⟨haT, har⟩ := List.mem_filter.mp ha
  obtain ⟨g, hgT, rfl⟩ := exists_of_mem_t0L haT
  rw [← code_r₄, commC_iff] at har
  have hcode : pcomp (pcomp (code g) (code c)) (pcube (code g)) = code (g * c * g⁻¹) := by
    rw [pcube_code hgT, code_mul, code_mul]
  rw [hcode] at ha'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha'
  obtain ⟨hb1, hb2⟩ := ha'
  rw [← Bool.not_eq_true, Nat.beq_eq] at hb1 hb2
  exact ⟨g, hgT, har, fun h2 => hb1 (by rw [h2]), fun h2 => hb2 (by rw [h2, code_mul, code_r₄])⟩

theorem exists_sylow_l34 (hUC : L34UnitaryCentralizerFact) {K₁ S N : Subgroup G} {t : G}
    (hperf : ⁅K₁, K₁⁆ = K₁) (htype : IsL34Type (K₁ ⧸ Open.fusionZStar K₁))
    (hunit : IsL34Unitary K₁ t) (hZodd : Odd (Nat.card ↥(zStarIn K₁)))
    (hSN : S ≤ normalizer (K₁ : Set G)) (hS : IsSylowTwoIn S N)
    (hCN : centralizer ({t} : Set G) ≤ N) (htS : t ∈ S) (hSt : ∀ s ∈ S, s * t = t * s) :
    ∃ P : Subgroup G, IsSylowTwoIn P K₁ ∧ S ≤ normalizer (P : Set G) ∧
      P ⊓ zStarIn K₁ = ⊥ ∧ S ⊓ K₁ = P ⊓ centralizer ({t} : Set G) ∧ Nat.card ↥(S ⊓ K₁) = 8 ∧
      Nonempty (↥(P ⊓ centralizer ({t} : Set G)) ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := GrS5.IsSylowTwoIn.isPGroup hS
  obtain ⟨P, hP, hSP, hSKP⟩ := exists_isSylowTwoIn_normalized hS2 hSN
  have hP2 : IsPGroup 2 P := GrS5.IsSylowTwoIn.isPGroup hP
  have hPZ : P ⊓ zStarIn K₁ = ⊥ :=
    UnbalancedLayer.eq_bot_of_le_two_group_of_le_odd hP2 hZodd inf_le_left inf_le_right
  obtain ⟨-, h8, -, hQ8, -⟩ := hUC G K₁ P t hperf htype hunit hP (hSP htS)
  have hSC : S ≤ centralizer ({t} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hSt s hs)
  have hle : S ⊓ K₁ ≤ P ⊓ centralizer ({t} : Set G) :=
    le_inf hSKP (inf_le_left.trans hSC)
  have hge : P ⊓ centralizer ({t} : Set G) ≤ S ⊓ K₁ := by
    refine le_inf (le_of_isSylowTwoIn hS (inf_le_right.trans hCN) (hP2.to_le inf_le_left)
      fun s hs => mem_normalizer_inf' (hSP hs) (le_normalizer (hSC hs))) (inf_le_left.trans hP.1)
  have heq : S ⊓ K₁ = P ⊓ centralizer ({t} : Set G) := le_antisymm hle hge
  exact ⟨P, hP, hSP, hPZ, heq, heq ▸ h8, hQ8 hPZ⟩

omit [Finite G] in
theorem eq_one_of_two_of_odd {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hxQ : x ∈ Q)
    (hx : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    have := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · simpa using hj
  · rw [hj] at hx
    exact absurd hx (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))

theorem exists_inner_l34
    {K₁ : Subgroup G} (hperf : ⁅K₁, K₁⁆ = K₁)
    (htype : IsL34Type (K₁ ⧸ Open.fusionZStar K₁)) (hZodd : Odd (Nat.card ↥(zStarIn K₁)))
    {t : G} (hunit : IsL34Unitary K₁ t) {X : Subgroup G} (hX2 : IsPGroup 2 X)
    (hXN : X ≤ normalizer (K₁ : Set G)) (hXC : X ≤ centralizer ({t} : Set G))
    {Q₁ : Subgroup G} (hQ₁X : Q₁ ≤ X) (hQ₁K : Q₁ ≤ K₁) (hQ₁8 : Nat.card Q₁ = 8) {z : G}
    (hzX : z ∈ X) (hz2 : z * z = 1)
    (hzQ : ∀ q ∈ Q₁, q * z * q⁻¹ = z ∨ q * z * q⁻¹ = t * z) :
    ∃ z₀ ∈ ({z, t * z} : Set G), ∃ j ∈ K₁, j⁻¹ * z₀ ∈ coreActionKernel K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρt⟩ := exists_real_unitary hperf htype hunit
  have hQ₁2 : IsPGroup 2 Q₁ := hX2.to_le hQ₁X
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
  let f : ↥Q₁ → {g // g ∈ T0 ∧ g * r₄ = r₄ * g} := fun q =>
    ⟨d * ρ.φ ⟨q, hXN (hQ₁X q.2)⟩ * d⁻¹, by
      have h1 := hd _ (ρ.phi_mem_img (g := ⟨q, hXN (hQ₁X q.2)⟩) (hQ₁X q.2))
      obtain ⟨h1c, h1T⟩ := mem_inf.mp h1
      exact ⟨TR_inf_S h1T (conj_mem_S hdR (ρ.map_K q (hQ₁K q.2))),
        mem_centralizer_singleton_iff.mp h1c⟩⟩
  have hf : Function.Injective f := by
    intro q q' hqq
    have h1 : ρ.φ ⟨q, hXN (hQ₁X q.2)⟩ = ρ.φ ⟨q', hXN (hQ₁X q'.2)⟩ := by
      have := congrArg Subtype.val hqq
      simpa [f] using this
    have h2 : (q : G)⁻¹ * q' ∈ coreActionKernel K₁ := by
      refine (ρ.ker_iff ⟨(q : G)⁻¹ * q', mul_mem (inv_mem (hXN (hQ₁X q.2)))
        (hXN (hQ₁X q'.2))⟩).mp ?_
      have e : (⟨(q : G)⁻¹ * q', mul_mem (inv_mem (hXN (hQ₁X q.2)))
          (hXN (hQ₁X q'.2))⟩ : ↥(normalizer (K₁ : Set G))) =
          (⟨q, hXN (hQ₁X q.2)⟩ : ↥(normalizer (K₁ : Set G)))⁻¹ *
            ⟨q', hXN (hQ₁X q'.2)⟩ := rfl
      rw [e, map_mul, map_inv, h1, inv_mul_cancel]
    have hqK : (q : G)⁻¹ * q' ∈ K₁ := mul_mem (inv_mem (hQ₁K q.2)) (hQ₁K q'.2)
    have h3 := (AutL34.mem_coreActionKernel_iff hqK).mp h2
    have h4 := eq_one_of_two_of_odd hQ₁2 (mul_mem (inv_mem q.2) q'.2)
      (Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard _ h3))
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hfs : Function.Surjective f :=
    (hf.bijective_of_nat_card_le (by rw [card_T0_cent_r₄, hQ₁8])).2
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
  obtain ⟨a, haT, har, ha1, ha2⟩ := exists_move hzW hzb2 hzT hrzT
  obtain ⟨q, hq⟩ := hfs ⟨a, haT, har⟩
  have ha : a = d * ρ.φ ⟨q, hXN (hQ₁X q.2)⟩ * d⁻¹ := by
    have := congrArg Subtype.val hq
    simp only [f] at this
    exact this.symm
  set qn : ↥(normalizer (K₁ : Set G)) := ⟨q, hXN (hQ₁X q.2)⟩ with hqn
  have hconj : a * zb * a⁻¹ = d * ρ.φ (qn * ⟨z, hzN⟩ * qn⁻¹) * d⁻¹ := by
    rw [ha, hzb, map_mul, map_mul, map_inv]
    group
  rcases hzQ q q.2 with h | h
  · apply ha1
    rw [hconj, hzb]
    congr 2
    exact congrArg ρ.φ (Subtype.ext h)
  · apply ha2
    rw [hconj, e4]
    congr 2
    exact congrArg ρ.φ (Subtype.ext h)

theorem quaternion_involution_unique :
    ∀ x y : QuaternionGroup 2, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y := by
  decide

theorem exists_conj_l34 (hUCen : L34UnitaryCenterFact) {K₁ P : Subgroup G} {t : G}
    (hperf : ⁅K₁, K₁⁆ = K₁) (htype : IsL34Type (K₁ ⧸ Open.fusionZStar K₁))
    (hunit : IsL34Unitary K₁ t) (hP : IsSylowTwoIn P K₁) (htP : t ∈ normalizer (P : Set G))
    (hPZ : P ⊓ zStarIn K₁ = ⊥)
    (hQ8 : Nonempty (↥(P ⊓ centralizer ({t} : Set G)) ≃* QuaternionGroup 2)) {z₁ : G}
    (hz₁ : z₁ ∈ P ⊓ centralizer ({t} : Set G)) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1) :
    ∃ v ∈ K₁, v * z₁ = z₁ * v ∧ v⁻¹ * t * v = t * z₁ := by
  obtain ⟨e⟩ := hQ8
  have hZ1 : ∀ z ∈ P ⊓ zStarIn K₁, z * z = 1 := fun z hz => by
    rw [hPZ, mem_bot] at hz
    rw [hz, one_mul]
  obtain ⟨h2, hcomm⟩ := hUCen G K₁ P t hperf htype hunit hP htP hZ1
  rw [hPZ, card_bot, mul_one] at h2
  set Zt := P ⊓ centralizer (P : Set G) ⊓ centralizer ({t} : Set G) with hZt
  have hZtle : Zt ≤ P ⊓ centralizer ({t} : Set G) := le_inf (inf_le_left.trans inf_le_left)
    inf_le_right
  have huniq : ∀ x ∈ P ⊓ centralizer ({t} : Set G), x * x = 1 → x ≠ 1 → x = z₁ := by
    intro x hx hx2 hx1
    have h1 := quaternion_involution_unique (e ⟨x, hx⟩) (e ⟨z₁, hz₁⟩)
      (by rw [← map_mul, show (⟨x, hx⟩ : ↥(P ⊓ centralizer ({t} : Set G))) * ⟨x, hx⟩ = 1 from
        Subtype.ext hx2, map_one])
      (by rw [← map_mul, show (⟨z₁, hz₁⟩ : ↥(P ⊓ centralizer ({t} : Set G))) * ⟨z₁, hz₁⟩ = 1 from
        Subtype.ext hz₁2, map_one])
      (fun h => hx1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h)))
      (fun h => hz₁1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h)))
    exact congrArg Subtype.val (e.injective h1)
  have hz₁Zt : z₁ ∈ Zt := by
    have : Nontrivial ↥Zt := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨w, hw1⟩ := exists_ne (1 : ↥Zt)
    have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hw2 : (w : G) * w = 1 := by
      have h3 : orderOf w ∣ 2 := h2 ▸ orderOf_dvd_natCard w
      have h4 : w ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
      have := congrArg Subtype.val h4
      simpa [pow_two] using this
    have := huniq w (hZtle w.2) hw2 hw1'
    rw [← this]
    exact w.2
  obtain ⟨v, hv, hvt⟩ := hcomm hPZ z₁ hz₁Zt
  obtain ⟨hvP, hvC⟩ := mem_inf.mp hv
  have hvz : v * z₁ = z₁ * v := ((mem_centralizer_iff.mp hvC) z₁ (mem_inf.mp hz₁).1).symm
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right hunit.2.1
  have hz₁t : z₁ * t = t * z₁ := mem_centralizer_singleton_iff.mp (mem_inf.mp hz₁).2
  refine ⟨v, hP.1 hvP, hvz, ?_⟩
  rw [ht1] at hvt
  calc v⁻¹ * t * v = v⁻¹ * t * v * t * t⁻¹ := by group
    _ = z₁ * t := by rw [hvt, ht1]
    _ = t * z₁ := hz₁t

end CFSG.ComponentClassification.HSFLit.L34Inv
