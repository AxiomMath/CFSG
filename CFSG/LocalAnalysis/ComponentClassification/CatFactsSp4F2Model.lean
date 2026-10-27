module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2Abs

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

section Inner

variable {G : Type*} [Group G]

theorem inn_normal : ((MulAut.conj : G →* MulAut G).range).Normal := by
  refine ⟨fun x hx φ => ?_⟩
  obtain ⟨g, rfl⟩ := hx
  refine ⟨φ g, ?_⟩
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply,
    MulAut.inv_apply]

theorem conj_injective_of_center {g h : G} (hc : ∀ z : G, z ∈ center G → z = 1)
    (hgh : MulAut.conj g = MulAut.conj h) : g = h := by
  have hz : h⁻¹ * g ∈ center G := by
    rw [mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut G => φ y) hgh
    simp only [MulAut.conj_apply] at this
    calc y * (h⁻¹ * g) = h⁻¹ * (h * y * h⁻¹) * h * h⁻¹ * g := by group
      _ = h⁻¹ * (g * y * g⁻¹) * h * h⁻¹ * g := by rw [this]
      _ = h⁻¹ * g * y := by group
  have := hc _ hz
  calc g = h * (h⁻¹ * g) := by group
    _ = h := by rw [this, mul_one]

theorem map_conj_fixOf (hc : ∀ z : G, z ∈ center G → z = 1) (α : MulAut G) :
    (fixOf α).map (MulAut.conj : G →* MulAut G) =
      (MulAut.conj : G →* MulAut G).range ⊓ centralizer ({α} : Set (MulAut G)) := by
  have hconj : ∀ g : G, α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := fun g => by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    show MulAut.conj g ∈ centralizer ({α} : Set (MulAut G))
    rw [mem_centralizer_singleton_iff]
    have hg' : α g = g := hg
    have := hconj g
    rw [hg'] at this
    calc MulAut.conj g * α = α * MulAut.conj g * α⁻¹ * α := by rw [this]
      _ = α * MulAut.conj g := by group
  · rintro ⟨⟨g, rfl⟩, hφ0⟩
    have hφ : MulAut.conj g * α = α * MulAut.conj g := mem_centralizer_singleton_iff.mp hφ0
    refine ⟨g, ?_, rfl⟩
    show α g = g
    have h1 : α * MulAut.conj g * α⁻¹ = MulAut.conj g := by
      rw [← hφ, mul_inv_cancel_right]
    rw [hconj] at h1
    exact conj_injective_of_center hc h1

theorem relIndex_sup_zpowers {I : Subgroup G} [I.Normal] {a : G} (ha2 : a * a = 1)
    (haI : a ∉ I) : I.relIndex (I ⊔ zpowers a) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨a, mem_sup_right (mem_zpowers a)⟩, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf]
  simp only [Subgroup.coe_mul]
  rcases mem_or_mul_mem_of_mem_sup ha2 b.2 with hb | hb
  · refine Or.inr ⟨hb, fun h => haI ?_⟩
    have := mul_mem (inv_mem hb) h
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨hb, fun h => haI ?_⟩
    have := mul_mem (inv_mem h) hb
    rwa [inv_mul_cancel_left] at this

end Inner

theorem pow_two_dvd_of_dvd {q n : ℕ} (hq : Odd q) (h : 2 ^ n ∣ 2 * (q ^ 2 * (q ^ 4 - 1))) :
    2 ^ (n + 1) ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have hcop : Nat.Coprime (2 ^ n) (q ^ 2) := Nat.Coprime.pow n 2 (Nat.coprime_two_left.mpr hq)
  have h1 : 2 ^ n ∣ 2 * (q ^ 4 - 1) := by
    rw [show 2 * (q ^ 2 * (q ^ 4 - 1)) = q ^ 2 * (2 * (q ^ 4 - 1)) by ring] at h
    exact hcop.dvd_of_dvd_mul_left h
  have h4 : 4 ∣ q ^ 2 - 1 := by
    obtain ⟨k, rfl⟩ := hq
    refine ⟨k ^ 2 + k, ?_⟩
    have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    omega
  calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    _ ∣ 2 * (2 * (q ^ 4 - 1)) := Nat.mul_dvd_mul_left 2 h1
    _ = 4 * (q ^ 4 - 1) := by ring
    _ ∣ (q ^ 2 - 1) * (q ^ 4 - 1) := Nat.mul_dvd_mul_right h4 _
    _ ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := dvd_mul_left _ _

theorem f2_main {K₀ : Type} [Group K₀] [Finite K₀] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hK₀ : Blueprint.LieModel K₀ .PSp 2 p f) (α : MulAut K₀)
    (hα2 : α * α = 1) (hout : α ∉ (MulAut.conj : K₀ →* MulAut K₀).range)
    (hdvd : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ∣ Nat.card (fixOf α))
    (Q : Subgroup (MulAut K₀))
    (hQC : Q ≤ ((MulAut.conj : K₀ →* MulAut K₀).range ⊔ zpowers α) ⊓
      centralizer ({α} : Set (MulAut K₀)))
    (hQS : ∃ T : Sylow 2 ↥(((MulAut.conj : K₀ →* MulAut K₀).range ⊔ zpowers α) ⊓
        centralizer ({α} : Set (MulAut K₀))),
      (T : Subgroup _) = Q.subgroupOf (((MulAut.conj : K₀ →* MulAut K₀).range ⊔ zpowers α) ⊓
        centralizer ({α} : Set (MulAut K₀)))) :
    ∃ g : MulAut K₀, g ∈ (MulAut.conj : K₀ →* MulAut K₀).range ∧
      g ∈ normalizer (Q : Set (MulAut K₀)) ∧ g ∉ Q ∧ g * g ∈ Q ∧
        α * (g⁻¹ * α * g) ∈ (MulAut.conj : K₀ →* MulAut K₀).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hK₀
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have hqodd : Odd (p ^ f) := hK ▸ hodd
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hc : ∀ z : K₀, z ∈ center K₀ → z = 1 := by
    intro z hz
    have hz' : e z ∈ center (StatedProj (StatedSp 2 K)) := by
      rw [mem_center_iff] at hz ⊢
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hz y]
    have := eq_one_of_mem_center_P h2 h4 hs hz'
    exact e.injective (this.trans (map_one e).symm)
  set α' : MulAut (StatedProj (StatedSp 2 K)) := e.symm.trans (α.trans e) with hα'def
  have hcomm : ∀ x, e (α x) = α' (e x) := fun x => by
    simp only [hα'def, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hα'2 : α' * α' = 1 := by
    ext x
    have := congrArg (fun φ : MulAut K₀ => φ (e.symm x)) hα2
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    simp only [hα'def, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply, this, MulEquiv.apply_symm_apply]
  have hout' : α' ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
    rintro ⟨u, hu⟩
    apply hout
    refine ⟨e.symm u, ?_⟩
    ext x
    apply e.injective
    rw [hcomm, ← hu]
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hfix : Nat.card (fixOf α') = Nat.card (fixOf α) := by
    rw [← map_fixOf_of_comm hcomm]
    exact (Nat.card_congr ((fixOf α).equivMapOfInjective _ e.injective).toEquiv).symm
  obtain ⟨A, hA, d, hd0, hdsq, hAA, hμ⟩ :=
    exists_typeII_of_admissible hp hp2 hf hK α' hα'2 hout' (hfix ▸ hdvd)
  obtain ⟨-, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A hd0 hdsq hAA hμ
  have hθα : ∀ g, α' (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
    rw [hA, conjAut_proj]
  have hC0 : Nat.card (fixOf α) ∣ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
    rw [← hfix, ← hcard]
    exact card_fixOf_dvd h2 (conjSp 2 K A) hθα
  set I := (MulAut.conj : K₀ →* MulAut K₀).range with hI
  have : I.Normal := inn_normal
  set N := I ⊔ zpowers α with hN
  set C := N ⊓ centralizer ({α} : Set (MulAut K₀)) with hC
  have hrel := relIndex_sup_zpowers hα2 hout
  have hIcard : Nat.card I = Nat.card K₀ :=
    (Nat.card_congr (MonoidHom.ofInjective (f := (MulAut.conj : K₀ →* MulAut K₀))
      fun g h hgh => conj_injective_of_center hc hgh).toEquiv).symm
  have hNcard : Nat.card N = Nat.card K₀ * 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := I) (K := N)
    rw [hrel, inf_of_le_left le_sup_left, hIcard] at h1
    rw [← h1, mul_comm]
  have hCI : Nat.card (I ⊓ C : Subgroup (MulAut K₀)) = Nat.card (fixOf α) := by
    have heq : I ⊓ C = I ⊓ centralizer ({α} : Set (MulAut K₀)) := by
      rw [hC, ← inf_assoc, show I ⊓ N = I from inf_of_le_left le_sup_left]
    rw [heq, ← map_conj_fixOf hc α]
    exact (Nat.card_congr ((fixOf α).equivMapOfInjective _
      fun g h hgh => conj_injective_of_center hc hgh).toEquiv).symm
  have hCdvd : Nat.card C ∣ 2 * Nat.card (fixOf α) := by
    have h1 := Subgroup.relIndex_mul_card (H := I) (K := C)
    have hle : I.relIndex C ≤ 2 := by
      rw [← hrel]
      exact Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hrel]; norm_num)
    have hpos : 0 < I.relIndex C := by
      rcases Nat.eq_zero_or_pos (I.relIndex C) with h0 | h0
      · rw [h0, zero_mul] at h1
        exact absurd h1.symm Nat.card_pos.ne'
      · exact h0
    rw [← h1, hCI]
    interval_cases h : I.relIndex C
    · rw [one_mul]
      exact dvd_mul_left (Nat.card (fixOf α)) 2
    · exact dvd_refl _
  have hQdvd : Nat.card Q ∣ Nat.card C := Subgroup.card_dvd_of_le hQC
  obtain ⟨T, hT⟩ := hQS
  have hQ2 : IsPGroup 2 Q := by
    have h := T.isPGroup'
    rw [hT] at h
    exact h.of_equiv (subgroupOfEquivOfLe hQC)
  obtain ⟨n, hn⟩ := hQ2.exists_card_eq
  have hQN : 2 * Nat.card Q ∣ Nat.card N := by
    have h1 : 2 ^ n ∣ 2 * ((p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1)) := by
      rw [← hn]
      refine hQdvd.trans (hCdvd.trans ?_)
      rw [show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring] at hC0
      exact Nat.mul_dvd_mul_left 2 hC0
    have h2' := pow_two_dvd_of_dvd hqodd h1
    rw [hNcard, two_mul_card_of_lieModel_psp hp2 hK₀, hn, ← pow_succ']
    exact h2'
  exact exists_inner_normalizing hα2 hQC ⟨T, hT⟩ hQN

end CFSG.ComponentClassification.CatFactsSp4
