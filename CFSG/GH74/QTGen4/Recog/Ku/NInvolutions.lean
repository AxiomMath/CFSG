module

public import CFSG.GH74.QTGen4.Recog.Ku.Parabolics

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuA6Model

variable {E W V2 N : Subgroup G} {z : G}

theorem exists_lift_lamS (Ψ : KuA6Model E W V2 N z) {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ lamS) :
    ∃ x : G, x ∈ Ψ.pre lamS ∧ ∃ hx : x ∈ N, Ψ.π ⟨x, hx⟩ = σ := by
  obtain ⟨n, hn⟩ := Ψ.π_surj σ (lamS_le_alt hσ)
  exact ⟨(n : G), (Ψ.mem_pre_iff lamS).mpr ⟨n.2, by show Ψ.π n ∈ lamS; rw [hn]; exact hσ⟩,
    n.2, hn⟩

theorem mem_double_coset (Ψ : KuA6Model E W V2 N z) {t g : G} (htN : t ∈ N) (hgN : g ∈ N)
    {c b : Equiv.Perm (Fin 6)} (hc : c ∈ lamS) (hb : b ∈ lamS)
    (hgπ : Ψ.π ⟨g, hgN⟩ = c * Ψ.π ⟨t, htN⟩ * b) :
    ∃ a ∈ Ψ.pre lamS, ∃ b' ∈ Ψ.pre lamS, g = a * t * b' := by
  obtain ⟨x, hxL, hxN, hxπ⟩ := Ψ.exists_lift_lamS hc
  obtain ⟨y, hyL, hyN, hyπ⟩ := Ψ.exists_lift_lamS hb
  have hkey : Ψ.π ((⟨x, hxN⟩ * ⟨t, htN⟩ * ⟨y, hyN⟩)⁻¹ * ⟨g, hgN⟩) = 1 := by
    simp only [map_mul, map_inv, hxπ, hyπ, hgπ, inv_mul_cancel]
  obtain ⟨e, he⟩ : ∃ e : ↥N, Ψ.π e = 1 ∧ (e : G) = (x * t * y)⁻¹ * g :=
    ⟨(⟨x, hxN⟩ * ⟨t, htN⟩ * ⟨y, hyN⟩)⁻¹ * ⟨g, hgN⟩, hkey, by simp⟩
  have heL : (e : G) ∈ Ψ.pre lamS :=
    (Ψ.mem_pre_iff lamS).mpr ⟨e.2, by show Ψ.π e ∈ lamS; rw [he.1]; exact lamS.one_mem⟩
  refine ⟨x, hxL, y * e, Subgroup.mul_mem _ hyL heL, ?_⟩
  rw [he.2]
  group

end KuA6Model

theorem alt_eq_double_coset {τ σ : Equiv.Perm (Fin 6)} (h1 : τ ∈ stabS)
    (h2 : τ ∈ alternatingGroup (Fin 6)) (h3 : τ ∉ lamS) (hσ : σ ∈ alternatingGroup (Fin 6))
    (hσL : σ ∉ lamS) : ∃ c ∈ lamS, ∃ b ∈ lamS, σ = c * τ * b := by
  have hl : τ * ρS0⁻¹ ∈ lamS := (Subgroup.mem_inf.mp (mul_ρS0_inv_mem_lam0 h1 h2 h3)).1
  rcases alt_eq_union hσ with hs | ⟨b, hb, hc⟩
  · exact absurd hs hσL
  refine ⟨σ * (ρS0 * b)⁻¹ * (τ * ρS0⁻¹)⁻¹, lamS.mul_mem hc (lamS.inv_mem hl), b,
    cosetB_mem b hb, ?_⟩
  group

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuN_eq_L2_doubleCoset_of_not_mem [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {t : G}
    (ht : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htL2 : t ∉ Ψ.L2) :
    ∀ g ∈ kuN P H, g ∈ Ψ.L2 ∨ ∃ a ∈ Ψ.L2, ∃ b ∈ Ψ.L2, g = a * t * b := by
  intro g hg
  by_cases hgL : g ∈ Ψ.L2
  · exact Or.inl hgL
  right
  have htN : t ∈ kuN P H := M_inf_normalizer_V2_le_normalizer_kuA h ht
  have hstab : Ψ.π ⟨t, htN⟩ ∈ stabS := by
    intro v hv
    have hconj := (Subgroup.mem_normalizer_iff.mp ht.2 (Ψ.Φ v)).mp ((Ψ.v2 v).mpr hv)
    have hact : t * Ψ.Φ v * t⁻¹ = Ψ.Φ (actS6 (Ψ.π ⟨t, htN⟩) v) := Ψ.act ⟨t, htN⟩ v
    rw [hact] at hconj
    exact (Ψ.v2 _).mp hconj
  have hnlam : Ψ.π ⟨t, htN⟩ ∉ lamS := fun hl => htL2 ((Ψ.mem_pre_iff lamS).mpr ⟨htN, hl⟩)
  have hgnlam : Ψ.π ⟨g, hg⟩ ∉ lamS := fun hl => hgL ((Ψ.mem_pre_iff lamS).mpr ⟨hg, hl⟩)
  obtain ⟨c, hc, b, hb, hcb⟩ :=
    alt_eq_double_coset hstab (Ψ.π_alt _) hnlam (Ψ.π_alt _) hgnlam
  exact Ψ.mem_double_coset htN hg hc hb hcb

theorem kuN_eq_L2_doubleCoset_of_inf_le [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    (hM1 : Ψ.L2 ⊓ (M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) ≤ oTwoUpper M) {t : G}
    (ht : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htL : t ∉ oTwoUpper M) :
    ∀ g ∈ kuN P H, g ∈ Ψ.L2 ∨ ∃ a ∈ Ψ.L2, ∃ b ∈ Ψ.L2, g = a * t * b :=
  h.kuN_eq_L2_doubleCoset_of_not_mem Ψ ht
    (fun htL2 => htL (hM1 (Subgroup.mem_inf.mpr ⟨htL2, ht⟩)))

end KuHyp

end CFSG.GH74.QTGen4.Ku
