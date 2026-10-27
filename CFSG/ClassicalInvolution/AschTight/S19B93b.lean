module

public import CFSG.ClassicalInvolution.AschTight.S19B93
public import CFSG.ClassicalInvolution.AschTight.S1916F2a

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_mem_USet_of_comm (hd : Sec19DataT p f K z S W L t V) {h u : G}
    (hne : h * z * h⁻¹ ≠ z) (huK : u ∈ K) (hu4 : orderOf u = 4)
    (hu : u * (h * z * h⁻¹) = (h * z * h⁻¹) * u) :
    ∃ U' ∈ USet (CoreAssembly.conjClass K), U' ≤ Subgroup.centralizer ({z} : Set G) ∧
      h⁻¹ * z * h ∈ U' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.tight
  have hΩ := hypOmegaMod_of_tightD ht
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hcl := conjInvariant_conjClass K
  have hKs : conjSub h K ∈ CoreAssembly.conjClass K := hcl h K hK
  have hIs : IsUniqueInvolution (conjSub h K) (h * z * h⁻¹) := hI.conj h
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)
  have huC : Subgroup.zpowers u ≤ K ⊓ Subgroup.centralizer ({h * z * h⁻¹} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨huK, Subgroup.mem_centralizer_singleton_iff.mpr hu⟩
  obtain ⟨P₀, hP₀⟩ := Sec7.exists_isSylow2In (K ⊓ Subgroup.centralizer ({h * z * h⁻¹} : Set G))
  obtain ⟨y, hy, hle⟩ := Sec7.exists_conj_le_of_isSylow2In hP₀ hu2 huC
  have hV : IsSylow2In (conjSub y P₀)
      (K ⊓ Subgroup.centralizer ({h * z * h⁻¹} : Set G)) := by
    have h1 := hP₀.conj y
    rwa [mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hy)] at h1
  have hzu : z ∈ Subgroup.zpowers u := by
    have h1 : u ^ 2 * u ^ 2 = 1 := by
      rw [← pow_add, show 2 + 2 = orderOf u by omega, pow_orderOf_eq_one]
    have h2 : u ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
    rw [← (hI.unique (u ^ 2) (K.pow_mem huK 2) h1).resolve_left h2]
    exact Subgroup.npow_mem_zpowers u 2
  have hzV : z ∈ conjSub y P₀ := hle hzu
  have hnt : K ∉ twinSet (CoreAssembly.conjClass K) (conjSub h K) := by
    rintro ⟨-, z₀, h₁, h₂⟩
    exact hne ((hIs.eq h₁).trans (hI.eq h₂).symm)
  have huV : u ∈ conjSub y P₀ := hle (Subgroup.mem_zpowers u)
  have hnz : conjSub y P₀ ≠ Subgroup.zpowers z := by
    intro e
    rw [e] at huV
    have h1 := orderOf_dvd_of_mem_zpowers huV
    rw [hu4, orderOf_eq_prime (by rw [_root_.sq]; exact hI.sq) hI.ne_one] at h1
    omega
  rcases l6_2 p f ht.branch.odd ht.branch.five G _ hΩ (conjSub h K) hKs (h * z * h⁻¹) hIs K hK
      hnt z hI (conjSub y P₀) hV hzV with ⟨hVz, -⟩ | ⟨hVz, -⟩ | ⟨hVU, -⟩ | ⟨hVR, -⟩
  · exact absurd hVz hnz
  · exact absurd hVz hnz
  · refine ⟨conjSub h⁻¹ (conjSub y P₀), conjSub_mem_USet hcl hVU h⁻¹, fun x hx => ?_, ?_⟩
    · rw [mem_conjSub_iff, inv_inv] at hx
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hV.1 hx).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * z = h⁻¹ * ((h * x * h⁻¹) * (h * z * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * z * h⁻¹) * (h * x * h⁻¹)) * h := by rw [h1]
        _ = z * x := by group
    · have h1 := conj_mem_conjSub (n := h⁻¹) hzV
      rwa [inv_inv] at h1
  · exfalso
    apply ht.edgeless (conjSub h K) hKs K hK
    refine Or.inl ⟨hK, fun hKK => hne ?_, conjSub y P₀, hVR, hV.1.trans inf_le_left, ?_⟩
    · exact hIs.eq (hKK ▸ hI)
    · exact (hV.1.trans inf_le_right).trans
        (S1911.centralizer_le_normalizer_member ht.toTightBranch hKs hIs)

theorem exists_conj_t_of_mem_USet (hd : Sec19DataT p f K z S W L t V) {U' : Subgroup G}
    (hU' : U' ∈ USet (CoreAssembly.conjClass K))
    (hU'C : U' ≤ Subgroup.centralizer ({z} : Set G)) {s' : G} (hs'U : s' ∈ U')
    (hs'2 : s' * s' = 1) (hs'1 : s' ≠ 1) (hs'z : s' ≠ z) :
    ∃ y ∈ sec19X K z, y * t * y⁻¹ = s' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  have hΩ := hypOmegaMod_of_tightD ht
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hcl := conjInvariant_conjClass K
  have hU'X : U' ≤ sec19X K z :=
    le_iSup₂_of_le (f := fun (A : Subgroup G) (_ : (A ∈ USet (CoreAssembly.conjClass K) ∨
      A ∈ RSet (CoreAssembly.conjClass K)) ∧ A ≤ Subgroup.centralizer ({z} : Set G)) => A) U'
      ⟨Or.inl hU', hU'C⟩ le_rfl
  have hU'2 : IsPGroup 2 U' := by
    obtain ⟨R, hR, hUR, -⟩ := hU'
    obtain ⟨J, -, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    exact hRJ.2.1.to_le hUR
  obtain ⟨x, hx, hle⟩ :=
    Sec7.exists_conj_le_of_isSylow2In (S1916.isSylow2In_inf_sec19X hd0) hU'2 hU'X
  have hU''S : conjSub x⁻¹ U' ≤ (S : Subgroup G) := by
    intro w hw
    rw [mem_conjSub_iff, inv_inv] at hw
    have h1 := hle hw
    rw [mem_conjSub_iff, show x⁻¹ * (x * w * x⁻¹) * x = w by group] at h1
    exact h1.1
  obtain ⟨η, hη, hWη⟩ := hd.hW
  have hηW : ∀ V' ∈ η, V' ≤ W := fun V' hV' =>
    hWη ▸ le_iSup₂_of_le (f := fun U (_ : U ∈ η) => U) V' hV' le_rfl
  have hηS : ∀ V' ∈ η, V' ≤ (S : Subgroup G) := fun V' hV' => (hηW V' hV').trans hd.hWS
  obtain ⟨V', ⟨hV'η, hV'⟩, -⟩ := l6_8 p f ht.branch.odd ht.branch.five G _ hΩ S _
    (conjSub_mem_USet hcl hU' x⁻¹) hU''S η hη hηS
  have hs''U : x⁻¹ * s' * x ∈ conjSub x⁻¹ U' := by
    have h1 := conj_mem_conjSub (n := x⁻¹) hs'U
    rwa [inv_inv] at h1
  have hxz : x * z = z * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (S1916.sec19X_le_centralizer K z hx)
  have hs''z : x⁻¹ * s' * x ≠ z := fun e => hs'z (by
    calc s' = x * (x⁻¹ * s' * x) * x⁻¹ := by group
      _ = x * z * x⁻¹ := by rw [e]
      _ = z := by rw [hxz]; group)
  have hs''2 : x⁻¹ * s' * x * (x⁻¹ * s' * x) = 1 := by
    calc x⁻¹ * s' * x * (x⁻¹ * s' * x) = x⁻¹ * (s' * s') * x := by group
      _ = 1 := by rw [hs'2]; group
  have hs''1 : x⁻¹ * s' * x ≠ 1 := fun e => hs'1 (by
    calc s' = x * (x⁻¹ * s' * x) * x⁻¹ := by group
      _ = 1 := by rw [e]; group)
  have hmem : x⁻¹ * s' * x = t ∨ x⁻¹ * s' * x = t * z := by
    rcases hV' with heq | hRS
    · have hW : x⁻¹ * s' * x ∈ W := hηW V' hV'η (heq ▸ hs''U)
      rcases S1911.invol_mem_W hd hW hs''2 hs''1 with e | e | e
      · exact absurd e hs''z
      · exact Or.inl e
      · exact Or.inr e
    · exfalso
      obtain ⟨J, hJ, hJsyl⟩ := exists_isSylow2In_of_mem_RSet hRS
      by_cases hJK : J = K
      · have hmK : x⁻¹ * s' * x ∈ K := hJK ▸ hJsyl.1 (Subgroup.mem_sup_left hs''U)
        exact hs''z ((hI.unique _ hmK hs''2).resolve_left hs''1)
      · apply ht.edgeless K hK J hJ
        refine Or.inl ⟨hJ, hJK, conjSub x⁻¹ U' ⊔ V', hRS, hJsyl.1, ?_⟩
        rw [normalizer_eq_centralizer_of_tight ht.toTightBranch]
        exact (sup_le hU''S (hηS V' hV'η)).trans hd.hSz
  rcases hmem with e | e
  · refine ⟨x, hx, ?_⟩
    calc x * t * x⁻¹ = x * (x⁻¹ * s' * x) * x⁻¹ := by rw [e]
      _ = s' := by group
  · obtain ⟨r, hr, hrt⟩ := S1911.exists_conj_eq_mul hd
    refine ⟨x * r, (sec19X K z).mul_mem hx (S1911.inf_le_sec19X hd0 hr), ?_⟩
    calc x * r * t * (x * r)⁻¹ = x * (r * t * r⁻¹) * x⁻¹ := by group
      _ = x * (x⁻¹ * s' * x) * x⁻¹ := by rw [hrt, e]
      _ = s' := by group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
