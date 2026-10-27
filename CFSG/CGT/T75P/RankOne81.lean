module

public import CFSG.CGT.T75P.Clos1
public import CFSG.CGT.T75P.SylowSplit
public import CFSG.CGT.T75P.Syl
public import CFSG.CGT.T75Q.Cent
public import CFSG.CGT.T75Q.SylowFin

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem Std81.hC1 (s : Std81 T T₁) {c : G}
    (hc : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) {u : G} (hu : u ∈ Uc T T₁) :
    c * u = u * c := by
  have hfin : Finite G := s.finite
  have := CFSG.CGT.T75Q.centralizer_hSub_le_centralizer_sup s.h1 s.h62 s.h63 s.hc s.hnat chain3
    (le_refl 3) hc
  exact (Subgroup.mem_centralizer_iff.1 this u hu).symm

theorem Std81.normalizer_eq_sup (s : Std81 T T₁) :
    Subgroup.normalizer (T : Set G) =
      hSub T (normIn T₁ T) ⊔ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) := by
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  apply le_antisymm
  · intro g hg
    obtain ⟨h, hh, c, hcC, rfl⟩ := normalizer_eq_mul s.h62 s.h63 s.hc s.hnat chain3 hg
    exact Subgroup.mul_mem_sup hh hcC
  · refine sup_le hHN ?_
    intro c hc
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTH hc)

theorem rank_one_81 [Finite G] [IsSimpleGroup G] (s : Std81 T T₁)
    (hna : ∃ a b : G, a * b ≠ b * a) {S₁ : Subgroup G}
    (hS₁C : S₁ ≤ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) (hS₁2 : IsPGroup 2 S₁)
    (hS₁odd : ¬ 2 ∣ (S₁.subgroupOf
      (Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))).index) (hne : S₁ ≠ ⊥)
    (hrank : ∀ α ∈ S₁, ∀ β ∈ S₁, α * α = 1 → β * β = 1 → α * β = β * α →
      α = 1 ∨ β = 1 ∨ α = β) : False := by
  classical
  have hfin : Finite G := s.finite
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  set H := hSub T (normIn T₁ T) with hH
  set C : Subgroup G := Subgroup.centralizer (H : Set G) with hC
  have hcomm : ∀ h ∈ H, ∀ c ∈ C, h * c = c * h := fun h hh c hc =>
    Subgroup.mem_centralizer_iff.1 hc h hh
  have hinf : H ⊓ C = ⊥ := inf_hSub_centralizer_eq_bot s.hc s.hnat
  have hNeq : Subgroup.normalizer (T : Set G) = H ⊔ C := s.normalizer_eq_sup
  have hodd : ¬ 2 ∣ (H ⊔ C).index := by
    rw [← hNeq]
    have h := Nat.odd_iff.1 (odd_index_normalizer s.hc.hy.pair.wc)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PH⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  let A : Subgroup G := (PH : Subgroup ↥H).map H.subtype
  have hAmem : ∀ x, x ∈ A ↔ ∃ y : ↥H, y ∈ (PH : Subgroup ↥H) ∧ (y : G) = x := by
    intro x
    simp [A, Subgroup.mem_map]
  have hAH : A ≤ H := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (hAmem x).1 hx
    exact y.2
  have hAsub : A.subgroupOf H = (PH : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hA2 : IsPGroup 2 A := by
    intro x
    obtain ⟨y, hy, hyx⟩ := (hAmem x.1).1 x.2
    obtain ⟨n, hn⟩ := PH.isPGroup' ⟨y, hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(PH : Subgroup ↥H) => ((z : ↥H) : G)) hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [← hyx]
    exact this
  have hAodd : ¬ 2 ∣ (A.subgroupOf H).index := by
    rw [hAsub]
    exact PH.not_dvd_index
  obtain ⟨P, hP⟩ := exists_sylow_of_prod hcomm hinf hodd hAH hS₁C hA2 hAodd hS₁2 hS₁odd
  have hAS : ∀ a ∈ A, ∀ c ∈ S₁, a * c = c * a := fun a ha c hc => hcomm a (hAH ha) c (hS₁C hc)
  have hiAS : A ⊓ S₁ = ⊥ := eq_bot_iff.2 (hinf ▸ inf_le_inf hAH hS₁C)
  refine CFSG.CGT.T75Q.false_of_sylow_split hna hP.symm hiAS hAS hne hrank ?_
  intro g c hcS hcc hc1 hgP
  have hcC : c ∈ C := hS₁C hcS
  obtain ⟨a, haA, c', hc'S, hm⟩ :=
    CFSG.CGT.T75H.exists_mul_of_mem_sup_of_comm hAS (hP.symm ▸ hgP)
  have haH : a ∈ H := hAH haA
  have hc'C : c' ∈ C := hS₁C hc'S
  have hmN : g⁻¹ * c * g ∈ Subgroup.normalizer (T : Set G) := by
    rw [hm]
    exact (Subgroup.normalizer (T : Set G)).mul_mem (hHN haH)
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTH hc'C))
  have hmm : (g⁻¹ * c * g) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [hcc]; group
  have hfus := fus81 s (fun u hu => s.hC1 hcC hu) (g := g⁻¹) (m := g⁻¹ * c * g)
    (by rw [inv_inv]) hmN hmm
  have haC : a ∈ C := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have h1 := hfus h (hSub_le_Uc hh)
    rw [hm] at h1
    have h2 : c' * h = h * c' := (Subgroup.mem_centralizer_iff.1 hc'C h hh).symm
    have h3 : a * h * c' = h * a * c' := by
      calc a * h * c' = a * (h * c') := by group
        _ = a * (c' * h) := by rw [h2]
        _ = a * c' * h := by group
        _ = h * (a * c') := h1
        _ = h * a * c' := by group
    exact (mul_right_cancel h3).symm
  have ha1 : a = 1 := by
    have : a ∈ H ⊓ C := ⟨haH, haC⟩
    rwa [hinf, Subgroup.mem_bot] at this
  rw [hm, ha1, one_mul]
  exact hc'S

end CFSG.CGT.T75P
