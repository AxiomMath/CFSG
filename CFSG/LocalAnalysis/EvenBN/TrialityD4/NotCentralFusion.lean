module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.NotCentralPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped commutatorElement

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem exists_J_conj_x₆ {c c' : d.Γ₀} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ j ∈ d.J, j * d.x₆ c * j⁻¹ = d.x₆ c' := by
  have := d.finite
  have hinj : Function.Injective (powMonoidHom 2 : (d.Γ₀)ˣ →* (d.Γ₀)ˣ) :=
    (injective_iff_map_eq_one _).2 fun _ hb => d.units₀_eq_one_of_sq hb
  obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.1 hinj (Units.mk0 (c' / c) (div_ne_zero hc' hc))
  refine ⟨d.torus (b, 1), d.torus_mem_J _, ?_⟩
  rw [d.torus_x₆]
  congr 1
  have hb' : (b : d.Γ₀) * (b : d.Γ₀) = c' / c := by
    have := congrArg Units.val hb
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, sq] at this
    exact this
  have hn : d.nm ((1 : d.Γˣ) : d.Γ) = 1 := by rw [Units.val_one]; exact d.nm_one
  change (b : d.Γ₀) * (b : d.Γ₀) * d.nm ((1 : d.Γˣ) : d.Γ) * c = c'
  rw [hn, mul_one, hb', div_mul_cancel₀ c' hc]

theorem J_le_normalizer_S : d.J ≤ normalizer (d.S : Set X) := by
  rw [d.normalizer_S]
  exact le_sup_right

end TrialityD4Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem conj_mem_yamadaR (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({t} : Set G))
    (hRQ : yamadaR d t ≤ Q) {c : G} (hc : ∀ r ∈ yamadaR d t, c⁻¹ * r * c ∈ Q) :
    ∀ r ∈ yamadaR d t, c⁻¹ * r * c ∈ yamadaR d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (yamadaR d t) := (h.isSylowOf_yamadaR d).isPGroup
  have hRC := h.yamadaR_le_centralizer d
  have hJR := h.rankThompson_eq d hR2 hRC le_rfl
  have hJQ := h.rankThompson_eq d hQ2 hQC hRQ
  have hrR := h.pRank_eq d hRC le_rfl
  have hrQ := h.pRank_eq d hQC hRQ
  suffices hle : yamadaR d t ≤ (yamadaR d t).comap (MulAut.conj c⁻¹).toMonoidHom by
    intro r hr
    have := hle hr
    simpa [mem_comap, MulAut.conj_apply] using this
  conv_lhs => rw [← hJR]
  unfold rankJr
  refine iSup₂_le fun A ⟨hAR, hA, hrA⟩ => ?_
  rw [← map_le_iff_le_comap, ← hJQ]
  have hAQ : A.map (MulAut.conj c⁻¹).toMonoidHom ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hc a (hAR ha)
  unfold rankJr
  refine le_iSup₂_of_le (A.map (MulAut.conj c⁻¹).toMonoidHom) ⟨hAQ, ?_, ?_⟩ le_rfl
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨a₀, ha₀, ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b₀, hb₀, hb⟩ := Subgroup.mem_map.1 b.2
    change (a : G) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨a₀, ha₀⟩ : A) ⟨b₀, hb₀⟩))
  · refine le_antisymm (SectionRank.pRank_mono one_lt_two hAQ) ?_
    rw [hrQ, ← hrR, ← hrA]
    exact SectionRank.pRank_le_map one_lt_two _ (MulAut.conj c⁻¹).injective A

theorem normalizer_le_normalizer_yamadaR (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({t} : Set G))
    (hRQ : yamadaR d t ≤ Q) :
    normalizer (Q : Set G) ≤ normalizer (yamadaR d t : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_mem_D4 fun r hr => ?_
  have h1 := h.conj_mem_yamadaR d hQ2 hQC hRQ (c := n⁻¹) (fun r' hr' => by
    rw [inv_inv]
    exact (mem_normalizer_iff.1 hn r').1 (hRQ hr')) r hr
  rwa [inv_inv] at h1

theorem exists_mul_of_mem_center_yamadaR (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q)
    {z : G} (hz : z ∈ yamadaR d t) (hzc : ∀ r ∈ yamadaR d t, z * r = r * z) :
    ∃ v ∈ d.V, ∃ c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), z = (v : G) * c := by
  have hz' : z ∈ ((yamadaR d t : Subgroup G) : Set G) := hz
  rw [h.coe_yamadaR d] at hz'
  obtain ⟨_, ⟨s, hs, rfl⟩, c, hc, rfl⟩ := hz'
  beta_reduce at hzc ⊢
  refine ⟨s, ?_, c, hc, rfl⟩
  rw [← d.S_inf_centralizer_S]
  refine Subgroup.mem_inf.2 ⟨hs, mem_centralizer_iff.2 fun r hr => Subtype.ext ?_⟩
  have hrR : (r : G) ∈ yamadaR d t := mem_sup_left ⟨r, hr, rfl⟩
  have h1 := hzc r hrR
  have h2 : (r : G) * c = c * r := S_commute_kernel d t r ⟨r, hr, rfl⟩ c hc
  have h3 : (s : G) * r * c = r * s * c := by
    calc (s : G) * r * c = s * (r * c) := by group
      _ = s * (c * r) := by rw [h2]
      _ = s * c * r := by group
      _ = r * (s * c) := h1
      _ = r * s * c := by group
  exact (mul_right_cancel h3).symm

theorem exists_conj_eq_mul_of_mem_normalizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {n : G} (hn : n ∈ normalizer (yamadaR d t : Set G)) :
    ∃ v ∈ d.V, n * t * n⁻¹ = t * (v : G) := by
  have htR : t ∈ yamadaR d t := mem_sup_right h.t_mem_kernel
  have htc : ∀ r ∈ yamadaR d t, r * t = t * r := fun r hr =>
    mem_centralizer_singleton_iff.1 (h.yamadaR_le_centralizer d hr)
  obtain ⟨hzR, hzc⟩ := conj_mem_center_of_mem_normalizer_D4 hn htR fun r hr => (htc r hr).symm
  obtain ⟨v, hv, c, hc, hzvc⟩ := h.exists_mul_of_mem_center_yamadaR d hzR hzc
  have hvc : (v : G) * c = c * v := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1 v v.2
  have hv2 : (v : G) * v = 1 := by
    have h1 := d.mul_self_eq_one_of_mem_W (d.Y_le_W (d.V_le_Y hv))
    exact congrArg Subtype.val h1
  have hz2 : n * t * n⁻¹ * (n * t * n⁻¹) = 1 := by
    calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]
  have hc2 : c * c = 1 := by
    rw [hzvc] at hz2
    calc c * c = v * v * (c * c) := by rw [hv2, one_mul]
      _ = v * (v * c) * c := by group
      _ = v * (c * v) * c := by rw [hvc]
      _ = v * c * (v * c) := by group
      _ = 1 := hz2
  by_cases hc1 : c = 1
  · exfalso
    rw [hc1, mul_one] at hzvc
    exact h.conj_not_mem_L d n (hzvc ▸ v.2)
  · have hct : c = t := h.kernel.2.2.1 c hc (orderOf_eq_prime (by rw [sq]; exact hc2) hc1)
    refine ⟨v, hv, ?_⟩
    rw [hzvc, hct]
    exact mem_centralizer_singleton_iff.1 (h.L_le_centralizer v.2)

theorem normalizer_S_le_normalizer_yamadaR (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q)
    {j : L} (hj : j ∈ normalizer (d.S : Set L)) :
    (j : G) ∈ normalizer (yamadaR d t : Set G) := by
  refine mem_normalizer_of_conj_mem_D4 fun r hr => ?_
  have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
  rw [h.coe_yamadaR d] at hr'
  obtain ⟨_, ⟨s, hs, rfl⟩, c, hc, rfl⟩ := hr'
  beta_reduce
  have hc' : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hc
  have hjc : (j : G) * c = c * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').1 j j.2
  have e : (j : G) * (s * c) * (j : G)⁻¹ = ((j * s * j⁻¹ : L) : G) * c := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (j : G) * (s * c) * (j : G)⁻¹ = j * s * ((j : G)⁻¹ * (j * c)) * (j : G)⁻¹ := by group
      _ = j * s * ((j : G)⁻¹ * (c * j)) * (j : G)⁻¹ := by rw [hjc]
      _ = j * s * (j : G)⁻¹ * c := by group
  change (j : G) * ((s : G) * c) * (j : G)⁻¹ ∈ _
  rw [e]
  exact mul_mem (mem_sup_left ⟨_, (mem_normalizer_iff.1 hj s).1 hs, rfl⟩) (mem_sup_right hc')

theorem conj_set_normalizer_yamadaR (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {n : G} (hn : n ∈ normalizer (yamadaR d t : Set G)) (hnt : n * t * n⁻¹ ≠ t) :
    {x | ∃ m ∈ normalizer (yamadaR d t : Set G), m * t * m⁻¹ = x} =
      (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨v, hv, hmv⟩ := h.exists_conj_eq_mul_of_mem_normalizer d hm
    exact ⟨v, ⟨v, hv, rfl⟩, hmv.symm⟩
  · rintro ⟨_, ⟨v', hv', rfl⟩, rfl⟩
    obtain ⟨v, hv, hnv⟩ := h.exists_conj_eq_mul_of_mem_normalizer d hn
    have hv1 : v ≠ 1 := by
      rintro rfl
      rw [OneMemClass.coe_one, mul_one] at hnv
      exact hnt hnv
    by_cases hv'1 : v' = 1
    · exact ⟨1, one_mem _, by rw [hv'1]; simp⟩
    · obtain ⟨c, rfl⟩ := hv
      obtain ⟨c', rfl⟩ := hv'
      have hc : c ≠ 0 := fun h0 => hv1 (by rw [h0, d.x₆_zero])
      have hc' : c' ≠ 0 := fun h0 => hv'1 (by rw [h0, d.x₆_zero])
      obtain ⟨j, hjJ, hjc⟩ := d.exists_J_conj_x₆ hc hc'
      refine ⟨(j : G) * n, mul_mem (h.normalizer_S_le_normalizer_yamadaR d
        (d.J_le_normalizer_S hjJ)) hn, ?_⟩
      have hjt : (j : G) * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
      have hjc' : (j : G) * (d.x₆ c : G) * (j : G)⁻¹ = (d.x₆ c' : G) := by
        rw [← hjc]
        simp
      calc (j : G) * n * t * ((j : G) * n)⁻¹ = j * (n * t * n⁻¹) * (j : G)⁻¹ := by group
        _ = j * t * (d.x₆ c : G) * (j : G)⁻¹ := by rw [hnv]; group
        _ = t * ((j : G) * (d.x₆ c : G) * (j : G)⁻¹) := by rw [hjt]; group
        _ = t * (d.x₆ c' : G) := by rw [hjc']

theorem exists_normalizer_yamadaR_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {g : G} (hy : ∀ r ∈ yamadaR d t, r * (g * t * g⁻¹) = g * t * g⁻¹ * r) :
    ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = g * t * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y := g * t * g⁻¹ with hydef
  obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
  have hC : (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({y} : Set G) := by
    ext z
    rw [mem_map_conj_iff_D4, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hz
      calc z * y = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by rw [hydef]; group
        _ = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by rw [hz]
        _ = y * z := by rw [hydef]; group
    · intro hz
      calc g⁻¹ * z * g * t = g⁻¹ * (z * y) * g := by rw [hydef]; group
        _ = g⁻¹ * (y * z) * g := by rw [hz]
        _ = t * (g⁻¹ * z * g) := by rw [hydef]; group
  have hQ' : IsSylowOf 2 (Q.map (MulAut.conj g).toMonoidHom) (centralizer ({y} : Set G)) := by
    obtain ⟨hle, hP, hdvd⟩ := isSylowOf_iff.1 hQ
    refine isSylowOf_iff.2 ⟨?_, hP.map _, ?_⟩
    · rw [← hC]
      exact Subgroup.map_mono hle
    · rw [← hC, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact hdvd
  have hRy : yamadaR d t ≤ centralizer ({y} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.2 (hy r hr)
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf_D4 hQ' hRy (h.isSylowOf_yamadaR d).isPGroup
  have hcgQ : ∀ r ∈ yamadaR d t, (c * g)⁻¹ * r * (c * g) ∈ Q := by
    intro r hr
    have h1 := hc r hr
    rw [mem_map_conj_iff_D4] at h1
    rwa [show g⁻¹ * (c⁻¹ * r * c) * g = (c * g)⁻¹ * r * (c * g) by group] at h1
  have hcgR := h.conj_mem_yamadaR d hQ.isPGroup hQ.le hRQ hcgQ
  have hN : (c * g)⁻¹ ∈ normalizer (yamadaR d t : Set G) :=
    mem_normalizer_of_conj_mem_D4 fun r hr => by
      rw [inv_inv]
      exact hcgR r hr
  refine ⟨c * g, by simpa using inv_mem hN, ?_⟩
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hcC
  calc c * g * t * (c * g)⁻¹ = c * y * c⁻¹ := by rw [hydef]; group
    _ = y := by rw [hcy]; group

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
