module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

theorem exists_mem_normalizer_not_mem {T P : Subgroup J} (hP : IsPGroup 2 P) (hTP : T ≤ P)
    (hne : ¬ P ≤ T) : ∃ n ∈ P, n ∉ T ∧ n ∈ Subgroup.normalizer (T : Set J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := T.subgroupOf P with hI
  have hIne : I ≠ ⊤ := fun htop => hne fun x hx => by
    have hmem : (⟨x, hx⟩ : P) ∈ I := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := P) I (lt_of_le_of_ne le_top hIne)
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  have hxsub : x ∈ (Subgroup.normalizer (T : Set J)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hTP]
    exact hxN
  exact ⟨x, x.2, fun hxT => hxI (Subgroup.mem_subgroupOf.mpr hxT),
    Subgroup.mem_subgroupOf.mp hxsub⟩

namespace FourGen

theorem card_le_of_sylowPlaced (hz : FourGen Q z) (h : Setting J Q B) {w : J}
    (hw : w * w = centralElt J) (hwz : w * z = z * w)
    (hmax : ∀ P ≤ Subgroup.normalizer (fourGroup z : Set J) ⊓ quasiNormalizer w,
      IsPGroup 2 P → Nat.card P ≤ Nat.card ((Q : Subgroup J) ⊓ quasiNormalizer w : Subgroup J))
    (hΩ : ∀ x ∈ (Q : Subgroup J), x * w = w * x → x * x = 1 → x ∈ fourGroup z) :
    ∀ P ≤ quasiNormalizer w, IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((Q : Subgroup J) ⊓ quasiNormalizer w : Subgroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := quasiNormalizer w with hX
  set T := (Q : Subgroup J) ⊓ X with hT
  have hT2 : IsPGroup 2 T := Q.isPGroup'.to_le inf_le_left
  obtain ⟨T₀, hT₀⟩ := (hT2.comap_of_injective X.subtype X.subtype_injective).exists_le_sylow
  set P₀ := (T₀ : Subgroup X).map X.subtype with hP₀
  have hTP₀ : T ≤ P₀ := fun t ht => ⟨⟨t, ht.2⟩, hT₀ ht, rfl⟩
  have hP₀X : P₀ ≤ X := Subgroup.map_subtype_le _
  have hP₀2 : IsPGroup 2 P₀ := T₀.isPGroup'.map _
  have hzT : z ∈ T := ⟨hz.mem, h.mem_quasiNormalizer_of_mul_eq hw hwz.symm⟩
  have hP₀T : P₀ ≤ T := by
    by_contra hne
    obtain ⟨n, hnP, hnT, hnN⟩ := exists_mem_normalizer_not_mem hP₀2 hTP₀ hne
    have hnX : n ∈ X := hP₀X hnP
    obtain ⟨a, ha⟩ : ∃ a, a = n * z * n⁻¹ := ⟨_, rfl⟩
    have haT : a ∈ T := ha ▸ (Subgroup.mem_normalizer_iff.mp hnN z).mp hzT
    have haw : a * w = w * a := by
      have hconj : a * (n * w * n⁻¹) = (n * w * n⁻¹) * a := by
        calc a * (n * w * n⁻¹) = n * (z * w) * n⁻¹ := by rw [ha]; group
          _ = n * (w * z) * n⁻¹ := by rw [hwz]
          _ = (n * w * n⁻¹) * a := by rw [ha]; group
      rcases h.conj_eq_of_mem_quasiNormalizer hw hnX with h1 | h1 <;> rw [h1] at hconj
      · exact hconj
      · have h2 : centralElt J * (a * w) = centralElt J * (w * a) := by
          rw [← h.mul_central_left, hconj, mul_assoc]
        exact mul_left_cancel h2
    have haa : a * a = 1 := by
      rw [ha]
      calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
        _ = 1 := by rw [hz.mul_self, mul_one, mul_inv_cancel]
    have haV := hΩ a haT.1 haw haa
    have hcomm : n * z * n⁻¹ * z⁻¹ ∈ Subgroup.center J := by
      rw [← ha]
      have ha1 : a ≠ 1 := by
        rw [ha, Ne, conj_eq_one_iff]
        intro h1
        have := hz.order
        rw [h1, orderOf_one] at this
        exact absurd this (by decide)
      rcases hz.eq_of_mem_fourGroup_of_ne_one h haV ha1 with h1 | h1 | h1
      · exfalso
        apply hz.ne_centralElt h
        calc z = n⁻¹ * a * n⁻¹⁻¹ := by rw [ha]; group
          _ = centralElt J := by rw [h1, Setting.conj_eq_of_mem_center h.centralElt_mem_center]
      · rw [h1, mul_inv_cancel]
        exact (Subgroup.center J).one_mem
      · rw [h1, mul_inv_cancel_right]
        exact h.centralElt_mem_center
    have hnNV := hz.mem_normalizer_fourGroup h hcomm
    set R := T ⊔ Subgroup.zpowers n with hR
    have hRP₀ : R ≤ P₀ := sup_le hTP₀ (Subgroup.zpowers_le.mpr hnP)
    have hRle : R ≤ Subgroup.normalizer (fourGroup z : Set J) ⊓ X :=
      sup_le (le_inf (inf_le_left.trans (hz.le_normalizer_fourGroup h)) inf_le_right)
        (Subgroup.zpowers_le.mpr ⟨hnNV, hnX⟩)
    have hTR : T = R := Subgroup.eq_of_le_of_card_ge le_sup_left (hmax R hRle (hP₀2.to_le hRP₀))
    exact hnT (hTR ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  intro P hPX hP2
  calc Nat.card P ≤ Nat.card (T₀ : Subgroup X) := card_le_card_sylow_of_le T₀ hPX hP2
    _ = Nat.card P₀ := (Subgroup.card_map_of_injective X.subtype_injective).symm
    _ ≤ Nat.card T := Subgroup.card_le_of_le hP₀T

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
