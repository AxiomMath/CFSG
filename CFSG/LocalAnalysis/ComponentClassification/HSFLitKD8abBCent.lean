module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBCoord
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abT2b

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_le_of_max {K P Q : Subgroup X} (hPK : P ≤ K) (hQK : Q ≤ K)
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → P ≤ R → R ≤ K → R = P) :
    ∃ k ∈ K, ∀ x ∈ Q, k⁻¹ * x * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 K :=
    { toSubgroup := P.subgroupOf K
      isPGroup' := hP.comap_subtype
      is_maximal' := fun {R} hR hle => by
        have hR' : IsPGroup 2 (R.map K.subtype) := hR.map _
        have hPR : P ≤ R.map K.subtype := fun x hx => ⟨⟨x, hPK hx⟩, hle hx, rfl⟩
        have h := hmax _ hR' hPR (map_subtype_le R)
        ext x
        constructor
        · intro hx
          have : (x : X) ∈ R.map K.subtype := ⟨x, hx, rfl⟩
          rw [h] at this
          exact this
        · intro hx
          exact hle hx }
  obtain ⟨Q', hQ'⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P' Q'
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h1 : (⟨x, hQK hx⟩ : K) ∈ (Q' : Subgroup K) := hQ' (show (⟨x, hQK hx⟩ : K) ∈
    Q.subgroupOf K from hx)
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨b, hb, hbx⟩ := h1
  rw [MulAut.smul_def, MulAut.conj_apply] at hbx
  have hb' : (b : X) ∈ P := hb
  have : (k : X)⁻¹ * x * k = b := by
    have := congrArg Subtype.val hbx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    group
  rw [this]
  exact hb'

variable {t : X} {L : Subgroup X} {A : L2Data t L} {C : A.CaseKD} {S : KDBase A C}
  {T₁ : Subgroup X}

namespace BData

variable (B : BData S T₁)

include B in
theorem mem_E₁_of_mem_centralizer {P : Subgroup X} (hP : IsPGroup 2 P) {e : X} (heP : e ∈ P)
    (hec : e ∈ centralizer (S.E S.y : Set X)) : e ∈ S.E S.y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsPGroup 2 (S.E S.y) :=
    Sec7.isPGroup_of_elemAbelianTwo (KD8ab.elemAbelianTwo_E S (isRefl_y S))
  have hz : IsPGroup 2 (zpowers e) := hP.to_le (zpowers_le.mpr heP)
  have hnorm : zpowers e ≤ normalizer (S.E S.y : Set X) :=
    zpowers_le.mpr (centralizer_le_normalizer _ hec)
  have hQ : IsPGroup 2 (S.E S.y ⊔ zpowers e : Subgroup X) := hE.to_sup_of_normal_left' hz hnorm
  have hQK : (S.E S.y ⊔ zpowers e : Subgroup X) ≤ normalizer (S.E S.y : Set X) :=
    sup_le le_normalizer hnorm
  obtain ⟨k, hk, hkQ⟩ := exists_conj_le_of_max B.G.D₁.S₁_le hQK B.isPGroup_S₁ hQ
    B.G.D₁.S₁_maximal
  have hke : k⁻¹ * e * k ∈ B.G.D₁.S₁ := hkQ e (mem_sup_right (mem_zpowers e))
  have hc : ∀ f ∈ S.E S.y, k⁻¹ * e * k * f = f * (k⁻¹ * e * k) := by
    intro f hf
    have hf' : k * f * k⁻¹ ∈ S.E S.y := by
      have := (mem_normalizer_iff.mp hk f).mp hf
      exact this
    have hcomm := mem_centralizer_iff.mp hec _ hf'
    calc k⁻¹ * e * k * f = k⁻¹ * (e * (k * f * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * f * k⁻¹) * e) * k := by rw [hcomm]
      _ = f * (k⁻¹ * e * k) := by group
  have h1 := B.mem_E₁_of_comm hke hc
  have h2 := (mem_normalizer_iff.mp hk (k⁻¹ * e * k)).mp h1
  rwa [show k * (k⁻¹ * e * k) * k⁻¹ = e by group] at h2

theorem E1h_le : MB.E1h.map B.ι ≤ S.E S.y := by
  rintro _ ⟨x, hx, rfl⟩
  exact B.ι_mem_E₁ hx

theorem E₁_eq : S.E S.y = MB.E1h.map B.ι :=
  (Subgroup.eq_of_le_of_card_ge B.E1h_le (by
    rw [card_map_of_injective B.ι_injective, MB.card_E1h, KD8ab.card_E S (isRefl_y S)])).symm

theorem mem_E₁_iff {g : X} : g ∈ S.E S.y ↔ ∃ x : MB, MB.inE1 x = true ∧ B.ι x = g := by
  rw [B.E₁_eq]; exact Iff.rfl

theorem ι_mem_R1 {x : MB} (hx : MB.inR1 x = true) : B.ι x ∈ B.R1 := ⟨x, hx, rfl⟩

theorem ι_mem_Q1 {x : MB} (hx : MB.inQ1 x = true) : B.ι x ∈ B.Q1 := ⟨x, hx, rfl⟩

theorem E₁_le_R1 : S.E S.y ≤ B.R1 := by
  rw [B.E₁_eq]
  rintro _ ⟨x, hx, rfl⟩
  exact B.ι_mem_R1 (MB.inR1_of_inE1 x hx)

theorem E₁_le_Q1 : S.E S.y ≤ B.Q1 := by
  rw [B.E₁_eq]
  rintro _ ⟨x, hx, rfl⟩
  exact B.ι_mem_Q1 (MB.inQ1_of_inE1 x hx)

theorem eq_of_mem_centralizer_R1 {P : Subgroup X} (hP : IsPGroup 2 P) {e : X} (heP : e ∈ P)
    (hec : e ∈ centralizer (B.R1 : Set X)) : e = 1 ∨ e = S.z ∨ e = S.k ∨ e = S.z * S.k := by
  have heE := B.mem_E₁_of_mem_centralizer hP heP (centralizer_le B.E₁_le_R1 hec)
  obtain ⟨x, -, rfl⟩ := B.mem_E₁_iff.mp heE
  have hc : ∀ g ∈ MB.gensR1, g * x = x * g := fun g hg => B.ι_injective (by
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp hec _ (B.ι_mem_R1 (MB.gensR1_mem g hg))))
  rcases MB.eq_of_comm_R1h x hc with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl B.ι_z)
  · exact Or.inr (Or.inr (Or.inl B.ι_k))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, B.ι_z, B.ι_k])))

theorem mem_E0_of_mem_centralizer_Q1 {P : Subgroup X} (hP : IsPGroup 2 P) {e : X} (heP : e ∈ P)
    (hec : e ∈ centralizer (B.Q1 : Set X)) : ∃ x : MB, MB.inE0 x = true ∧ B.ι x = e := by
  have heE := B.mem_E₁_of_mem_centralizer hP heP (centralizer_le B.E₁_le_Q1 hec)
  obtain ⟨x, hx, rfl⟩ := B.mem_E₁_iff.mp heE
  have hc : ∀ g ∈ MB.gensQ1, g * x = x * g := fun g hg => B.ι_injective (by
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp hec _ (B.ι_mem_Q1 (MB.gensQ1_mem g hg))))
  exact ⟨x, MB.mem_E0h_of_comm_Q1h x hx hc, rfl⟩

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
