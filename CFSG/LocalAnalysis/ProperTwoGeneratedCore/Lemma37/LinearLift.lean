module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open scoped Pointwise

theorem exists_mem_normalizer_mk_eq {K : Type*} [Group K] [Finite K] {N : Subgroup K} [N.Normal]
    (P : Sylow 2 K) {m : K}
    (hm : QuotientGroup.mk' N m ∈
      Subgroup.normalizer (((P : Subgroup K).map (QuotientGroup.mk' N)) : Set (K ⧸ N))) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup K) : Set K),
      QuotientGroup.mk' N n = QuotientGroup.mk' N m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := (P : Subgroup K) ⊔ N with hL
  have hPL : (P : Subgroup K) ≤ L := le_sup_left
  have hconj : ∀ x ∈ (P : Subgroup K), m * x * m⁻¹ ∈ L := by
    intro x hx
    have h := (Subgroup.mem_normalizer_iff.mp hm _).mp (Subgroup.mem_map_of_mem _ hx)
    rw [← map_inv, ← map_mul, ← map_mul] at h
    have h2 : m * x * m⁻¹ ∈ ((P : Subgroup K).map (QuotientGroup.mk' N)).comap
        (QuotientGroup.mk' N) := h
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hmPL : ((m • P : Sylow 2 K) : Subgroup K) ≤ L := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hx' : m⁻¹ * x * m ∈ (P : Subgroup K) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hx
    have h := hconj _ hx'
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L ((m • P).subtype hmPL) (P.subtype hPL)
  have hmem : ∀ x ∈ (P : Subgroup K), (l : K) * m * x * ((l : K) * m)⁻¹ ∈ (P : Subgroup K) := by
    intro x hx
    have h1 : m * x * m⁻¹ ∈ ((m • P : Sylow 2 K) : Subgroup K) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj m) _ hx
    have h2 : (⟨m * x * m⁻¹, hmPL h1⟩ : L) ∈
        (((m • P).subtype hmPL : Sylow 2 L) : Subgroup L) := by
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      exact h1
    have h3 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj l) _ h2
    rw [← Sylow.coe_subgroup_smul, hl, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h3
    convert h3 using 1
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hlm : (l : K) * m ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
    Subgroup.mem_normalizer_fintype hmem
  obtain ⟨p, hp, o, ho, hpo⟩ := Subgroup.mem_sup_of_normal_right.mp l.2
  refine ⟨o * m, ?_, ?_⟩
  · have h : o * m = p⁻¹ * ((l : K) * m) := by rw [← hpo]; group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ((P : Subgroup K).inv_mem hp)) hlm
  · have h1 : QuotientGroup.mk' N o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [map_mul, h1, one_mul]

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

theorem exists_normalizer_sylowBar_lift (hz : IsCentralInvolution (S : Subgroup G) z)
    {d : EscapingQuotient z}
    (hd : d ∈ Subgroup.normalizer (((sylowBar hz).range : Subgroup (EscapingQuotient z)) :
      Set (EscapingQuotient z))) :
    ∃ n : Subgroup.centralizer ({z} : Set G),
      (n : G) ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) ∧ escapingMk z n = d ∧
      ∀ s : (S : Subgroup G), ∀ h : (n : G) * s * (n : G)⁻¹ ∈ (S : Subgroup G),
        sylowBar hz ⟨_, h⟩ = d * sylowBar hz s * d⁻¹ := by
  set M := Subgroup.centralizer ({z} : Set G)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 M) d
  set P : Sylow 2 M := S.subtype hz.le_centralizer
  have hPmap : (P : Subgroup M).map (QuotientGroup.mk' (pPrimeCore 2 M)) = (sylowBar hz).range := by
    rw [Sylow.coe_subtype, sylowBar_range]
  rw [← hPmap] at hd
  obtain ⟨n, hn, hnm⟩ := exists_mem_normalizer_mk_eq P hd
  refine ⟨n, ?_, hnm, fun s h => ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have h1 : (⟨s, hz.le_centralizer hs⟩ : M) ∈ (P : Subgroup M) := by
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      exact hs
    have h2 := (Subgroup.mem_normalizer_iff.mp hn _).mp h1
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h2
    have h3 : (n : G) * s * (n : G)⁻¹ ∈ (S : Subgroup G) := by simpa using h2
    exact h3
  · rw [← hnm, sylowBar_apply, sylowBar_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl

end CFSG.ProperTwoGeneratedCore.Lemma37
