module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.ABGLocalTools Subgroup

section General

variable {G : Type*} [Group G]

private theorem twoSided_mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simp only [conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

private theorem twoSided_exists_isSylowOf_ge {p : ℕ} {K Q : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ T : Subgroup G, IsSylowOf p T K ∧ Q ≤ T := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ⟨⟨x, hQK hx⟩, hS hx, rfl⟩⟩

private theorem twoSided_exists_mem_normalizer_of_lt {p : ℕ} [Fact p.Prime] [Finite G]
    {T P : Subgroup G} (hP : IsPGroup p P) (hTP : T < P) :
    ∃ x ∈ P, x ∉ T ∧ x ∈ normalizer (T : Set G) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  set W := T.subgroupOf P with hW
  have hWtop : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hTP.not_ge fun x hx => ?_
    have h1 : (⟨x, hx⟩ : P) ∈ W := h ▸ mem_top _
    exact h1
  obtain ⟨y, hyN, hyW⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent W hWtop)
  refine ⟨y, y.2, hyW, mem_normalizer_iff.mpr fun t => ?_⟩
  constructor
  · intro ht
    have h1 : (⟨t, hTP.le ht⟩ : P) ∈ W := ht
    exact (mem_normalizer_iff.mp hyN _).mp h1
  · intro ht
    have htP : t ∈ P := by
      have h1 : (y : G) * t * (y : G)⁻¹ ∈ P := hTP.le ht
      have h2 : t = (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G) := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem y.2) h1) y.2
    have h1 : y * (⟨t, htP⟩ : P) * y⁻¹ ∈ W := ht
    exact (mem_normalizer_iff.mp hyN _).mpr h1

private theorem twoSided_isSylowOf_of_normalizer_le {p : ℕ} [Fact p.Prime] [Finite G]
    {T X Y : Subgroup G} (hT : IsSylowOf p T X) (hXY : X ≤ Y)
    (hN : Y ⊓ normalizer (T : Set G) ≤ X) : IsSylowOf p T Y := by
  obtain ⟨T', hT', hTT'⟩ := twoSided_exists_isSylowOf_ge (hT.le.trans hXY) hT.isPGroup
  rcases eq_or_lt_of_le hTT' with h | h
  · rw [h]
    exact hT'
  exfalso
  obtain ⟨x, hxT', hxT, hxN⟩ := twoSided_exists_mem_normalizer_of_lt hT'.isPGroup h
  set R := T' ⊓ normalizer (T : Set G) with hR
  have hRX : R ≤ X := fun y hy => hN (mem_inf.mpr ⟨hT'.le (mem_inf.mp hy).1, (mem_inf.mp hy).2⟩)
  have hTR : T ≤ R := le_inf hTT' le_normalizer
  have hRp : IsPGroup p R := hT'.isPGroup.to_le inf_le_left
  have hRT : R = T := hT.eq_of_le hTR hRX hRp
  exact hxT (hRT ▸ mem_inf.mpr ⟨hxT', hxN⟩)

theorem exists_two_sided_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {M B : Subgroup G}
    (hB : IsPGroup p B) (hBM : B ≤ M) {g : G} (hg : conjugate B g ≤ M) (hgM : g ∉ M) :
    ∃ h : G, h ∉ M ∧ conjugate B h ≤ M ∧ B ≤ conjugate M h := by
  set M' : Subgroup G := conjugate M g⁻¹ with hM'
  have hmem' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M := fun x => by
    rw [hM', twoSided_mem_conjugate_iff]
    simp
  have hBM' : B ≤ M' := fun b hb => by
    rw [hmem']
    refine hg (twoSided_mem_conjugate_iff.mpr ?_)
    simpa [mul_assoc] using hb
  obtain ⟨P, hP, hBP⟩ := twoSided_exists_isSylowOf_ge (p := p) (le_inf hBM hBM') hB
  have hPM : P ≤ M := hP.le.trans inf_le_left
  have hPM' : P ≤ M' := hP.le.trans inf_le_right
  have key : ∃ h : G, h ∈ normalizer (P : Set G) ∧ h ∉ M := by
    by_contra hcon
    have hcon' : ∀ h : G, h ∈ normalizer (P : Set G) → h ∈ M := fun h hh =>
      by_contra fun hhM => hcon ⟨h, hh, hhM⟩
    have hP' : IsSylowOf p P M' :=
      twoSided_isSylowOf_of_normalizer_le hP inf_le_right fun x hx => ⟨hcon' x hx.2, hx.1⟩
    have hcardM' : Nat.card M' = Nat.card M :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective
    have hPsyl : IsSylowOf p P M := isSylowOf_of_card hPM (by rw [hP'.card_eq, hcardM'])
    have hC_le : conjugate P g ≤ M := fun x hx => by
      rw [twoSided_mem_conjugate_iff] at hx
      have h1 := (hmem' _).1 (hPM' hx)
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h1
    have hcardC : Nat.card (conjugate P g) = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hCsyl : IsSylowOf p (conjugate P g) M :=
      isSylowOf_of_card hC_le (by rw [hcardC, hPsyl.card_eq])
    obtain ⟨k, hkM, hk⟩ := hCsyl.exists_mem_conj hPsyl
    have hn : g * k⁻¹ ∈ normalizer (P : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      have e : g * k⁻¹ * x * (g * k⁻¹)⁻¹ = g * (k⁻¹ * x * k) * g⁻¹ := by group
      rw [e, hk x, twoSided_mem_conjugate_iff]
    have hgk : g * k⁻¹ ∈ M := hcon' _ hn
    apply hgM
    have e : g = g * k⁻¹ * k := by group
    rw [e]
    exact M.mul_mem hgk hkM
  obtain ⟨h, hhN, hhM⟩ := key
  rw [mem_normalizer_iff] at hhN
  refine ⟨h, hhM, ?_, ?_⟩
  · intro x hx
    rw [twoSided_mem_conjugate_iff] at hx
    exact hPM ((hhN x).2 (hBP hx))
  · intro x hx
    rw [twoSided_mem_conjugate_iff]
    exact hPM ((hhN x).1 (hBP hx))

end General

end CFSG.GH74.Generic.BProg.B2
