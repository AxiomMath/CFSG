module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

theorem mem_of_pPow_eq_one_of_not_dvd_relIndex {G : Type*} [Group G] {I D : Subgroup G}
    [I.Normal] {p : ℕ} (hp : p.Prime) (hID : I ≤ D) (h : ¬ p ∣ I.relIndex D) {w : G}
    (hw : w ∈ D) {k : ℕ} (hk : w ^ (p ^ k) = 1) : w ∈ I := by
  have hN : (I.subgroupOf D).Normal := Subgroup.Normal.subgroupOf inferInstance D
  have hcard : Nat.card (D ⧸ I.subgroupOf D) = I.relIndex D := by
    rw [Subgroup.relIndex, Subgroup.index]
  have hcop : Nat.Coprime (p ^ k) (Nat.card (D ⧸ I.subgroupOf D)) := by
    rw [hcard]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  have h1 : (QuotientGroup.mk (⟨w, hw⟩ : D) : D ⧸ I.subgroupOf D) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨w, hw⟩ : D) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk (⟨w, hw⟩ : D) : D ⧸ I.subgroupOf D) ∣
      Nat.card (D ⧸ I.subgroupOf D) := orderOf_dvd_natCard _
  have h4 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  have h5 := (QuotientGroup.eq_one_iff (⟨w, hw⟩ : D)).1 (orderOf_eq_one_iff.1 h4)
  exact Subgroup.mem_subgroupOf.1 h5

theorem exists_conj_pow_of_pElement {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {D I : Subgroup G} [D.Normal] [I.Normal] (hID : I ≤ D)
    (hDI : ∀ w ∈ D, (∃ k : ℕ, w ^ (p ^ k) = 1) → w ∈ I)
    {f : G} (hf : f ^ p = 1) (hG : ∀ x : G, ∃ d ∈ D, ∃ i : ℕ, x = d * f ^ i)
    {z : G} (hz : ∃ k : ℕ, z ^ (p ^ k) = 1) (hzD : z ∉ D) :
    ∃ d ∈ D, ∃ i : ℕ, ¬ p ∣ i ∧ ∃ ι ∈ I, z = ι * (d * f ^ i * d⁻¹) := by
  obtain ⟨k, hk⟩ := hz
  have hzp : IsPGroup p (Subgroup.zpowers z) := by
    rintro ⟨_, j, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (z ^ j) ^ (p ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hfp : IsPGroup p (Subgroup.zpowers f) := by
    rintro ⟨_, j, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (f ^ j) ^ (p ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf, one_zpow]
  obtain ⟨Pz, hPz⟩ := hzp.exists_le_sylow
  obtain ⟨Pf, hPf⟩ := hfp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Pf Pz
  have hgP : ((g • Pf : Sylow p G) : Subgroup G) =
      (Pf : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hzPz : z ∈ (Pz : Subgroup G) := hPz (Subgroup.mem_zpowers z)
  rw [← hg, hgP] at hzPz
  obtain ⟨u, huP, hu⟩ := Subgroup.mem_map.1 hzPz
  obtain ⟨d₁, hd₁, i, hui⟩ := hG u
  have hfi : f ^ i ∈ (Pf : Subgroup G) := hPf (Subgroup.pow_mem _ (Subgroup.mem_zpowers f) i)
  have hd₁P : d₁ ∈ (Pf : Subgroup G) := by
    have : d₁ = u * (f ^ i)⁻¹ := by rw [hui]; group
    rw [this]
    exact Subgroup.mul_mem _ huP (Subgroup.inv_mem _ hfi)
  have hd₁I : d₁ ∈ I := by
    refine hDI d₁ hd₁ ?_
    obtain ⟨m, hm⟩ := Pf.isPGroup' ⟨d₁, hd₁P⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨d₂, hd₂, j, hgj⟩ := hG g
  refine ⟨d₂, hd₂, i, ?_, g * d₁ * g⁻¹, ?_, ?_⟩
  · rintro ⟨c, rfl⟩
    apply hzD
    have hfpow : f ^ (p * c) = 1 := by rw [pow_mul, hf, one_pow]
    have : z = g * d₁ * g⁻¹ := by
      have h1 : z = g * u * g⁻¹ := by
        rw [← hu]
        simp [MulAut.conj_apply]
      rw [h1, hui, hfpow, mul_one]
    rw [this]
    exact hID (‹I.Normal›.conj_mem d₁ hd₁I g)
  · exact ‹I.Normal›.conj_mem d₁ hd₁I g
  · have h1 : z = g * u * g⁻¹ := by
      rw [← hu]
      simp [MulAut.conj_apply]
    rw [h1, hui, hgj]
    group

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
