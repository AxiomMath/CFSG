module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LargeExtraspecial

open Subgroup

variable {X : Type*} [Group X]

@[expose] def IsWeaklyClosedInNormalizer (A : Subgroup X) : Prop :=
  ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≤ normalizer (A : Set X) →
    A.map (MulAut.conj g).toMonoidHom = A

private theorem map_conj_eq_of_mem_normalizer' {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    change g⁻¹ * x * g ∈ H
    rw [mem_normalizer_iff.mp hg]
    convert hx using 1
    group

private theorem mem_normalizer_of_map_conj_eq {H : Subgroup X} {g : X}
    (hg : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hg]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hg] at hh
    obtain ⟨a, ha, hah⟩ := hh
    have : a = h := by
      have := congrArg (fun y => g⁻¹ * y * g) hah
      simpa [mul_assoc] using this
    rwa [← this]

private theorem exists_mem_normalizer_not_mem_of_lt' [Finite X] {p : ℕ} [Fact p.Prime]
    {P S₀ : Subgroup X} (hP : IsPGroup p P) (hlt : S₀ < P) :
    ∃ x ∈ P, x ∉ S₀ ∧ x ∈ normalizer (S₀ : Set X) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' : S₀.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ S₀.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt')
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S₀ : Set X)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem le_normalizer_of_isWeaklyClosed [Finite X] {p : ℕ} [Fact p.Prime] {A T : Subgroup X}
    (hw : IsWeaklyClosedInNormalizer A) (hT : IsPGroup p T) (hAT : A ≤ T) :
    T ≤ normalizer (A : Set X) := by
  set N := T ⊓ normalizer (A : Set X) with hN
  by_contra hTN
  have hlt : N < T := lt_of_le_of_ne inf_le_left fun h => hTN (h ▸ inf_le_right)
  obtain ⟨y, hyT, hyN, hyNN⟩ := exists_mem_normalizer_not_mem_of_lt' hT hlt
  have hAN : A ≤ N := le_inf hAT le_normalizer
  have hle : A.map (MulAut.conj y).toMonoidHom ≤ normalizer (A : Set X) := by
    calc A.map (MulAut.conj y).toMonoidHom ≤ N.map (MulAut.conj y).toMonoidHom := map_mono hAN
      _ = N := map_conj_eq_of_mem_normalizer' hyNN
      _ ≤ normalizer (A : Set X) := inf_le_right
  exact hyN ⟨hyT, mem_normalizer_of_map_conj_eq (hw y hle)⟩

theorem lemma_3_12 [Finite X] {p : ℕ} [Fact p.Prime] {A : Subgroup X} (hA : IsPGroup p A)
    (hw : IsWeaklyClosedInNormalizer A) {B : Set X} (hB : B ⊆ centralizer (A : Set X)) {g : X}
    (hBg : (fun b => g * b * g⁻¹) '' B ⊆ centralizer (A : Set X)) :
    ∃ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ = g * b * g⁻¹ := by
  classical
  set K := centralizer ((fun b => g * b * g⁻¹) '' B) with hK
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'
  have hAK : A ≤ K := by
    intro a ha
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_centralizer_iff.mp (hBg ⟨b, hb, rfl⟩) a ha).symm
  have hA'K : A' ≤ K := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hab : a * b = b * a := mem_centralizer_iff.mp (hB hb) a ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * b * g⁻¹ * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
      _ = g * (a * b) * g⁻¹ := by rw [hab]
      _ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
  have hpA : IsPGroup p (A.subgroupOf K) := hA.of_equiv (subgroupOfEquivOfLe hAK).symm
  have hpA' : IsPGroup p (A'.subgroupOf K) :=
    (hA.map (MulAut.conj g).toMonoidHom).of_equiv (subgroupOfEquivOfLe hA'K).symm
  obtain ⟨T, hT⟩ := hpA.exists_le_sylow
  obtain ⟨T', hT'⟩ := hpA'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K T' T
  set TG := (T : Subgroup K).map K.subtype with hTG
  have hTGp : IsPGroup p TG := T.isPGroup'.map _
  have hATG : A ≤ TG := fun a ha => ⟨⟨a, hAK ha⟩, hT (mem_subgroupOf.mpr ha), rfl⟩
  have hcA' : A'.map (MulAut.conj (c : X)).toMonoidHom ≤ TG := by
    rintro _ ⟨a', ha', rfl⟩
    have hy : (⟨a', hA'K ha'⟩ : K) ∈ (T' : Subgroup K) := hT' (mem_subgroupOf.mpr ha')
    have h1 : MulAut.conj c • (⟨a', hA'K ha'⟩ : K) ∈ ((c • T' : Sylow p K) : Subgroup K) := by
      rw [Sylow.coe_subgroup_smul]
      exact smul_mem_pointwise_smul _ _ _ hy
    rw [hc, MulAut.smul_def, MulAut.conj_apply] at h1
    exact ⟨_, h1, rfl⟩
  have hTN := le_normalizer_of_isWeaklyClosed hw hTGp hATG
  have hmap : A.map (MulAut.conj ((c : X) * g)).toMonoidHom =
      A'.map (MulAut.conj (c : X)).toMonoidHom := by
    rw [hA', map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hcg : A.map (MulAut.conj ((c : X) * g)).toMonoidHom = A :=
    hw _ (hmap ▸ hcA'.trans hTN)
  refine ⟨(c : X) * g, mem_normalizer_of_map_conj_eq hcg, fun b hb => ?_⟩
  have hcb : (c : X) * (g * b * g⁻¹) = (g * b * g⁻¹) * c :=
    (mem_centralizer_iff.mp c.2 _ ⟨b, hb, rfl⟩).symm
  calc (c : X) * g * b * ((c : X) * g)⁻¹ = (c : X) * (g * b * g⁻¹) * (c : X)⁻¹ := by group
    _ = g * b * g⁻¹ := by rw [hcb]; group

theorem lemma_3_12_isStronglyClosedIn [Finite X] {p : ℕ} [Fact p.Prime] {A : Subgroup X}
    (hA : IsPGroup p A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hw : IsWeaklyClosedInNormalizer A) :
    IsStronglyClosedIn (centralizer (A : Set X)) (A : Set X) := by
  have hAC : (A : Set X) ⊆ centralizer (A : Set X) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => hAc b hb a ha
  refine ⟨hAC, fun a ha g hg => ?_⟩
  have hBg : (fun b => g⁻¹ * b * g⁻¹⁻¹) '' {a} ⊆ centralizer (A : Set X) := by
    rintro _ ⟨b, rfl, rfl⟩
    rw [inv_inv]
    exact hg
  obtain ⟨n, hn, hna⟩ := lemma_3_12 hA hw (Set.singleton_subset_iff.mpr (hAC ha)) hBg
  have h := hna a rfl
  rw [inv_inv] at h
  rw [← h]
  exact (mem_normalizer_iff.mp hn a).mp ha

end CFSG.LargeExtraspecial
