module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

private theorem isPGroup_zpowers_of_mul_self {B : Type*} [Group B] {b : B} (hb : b * b = 1) :
    IsPGroup 2 (Subgroup.zpowers b) := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hb)

theorem exists_sylow_central_of_surjective {B H : Type*} [Group B] [Group H] [Finite B]
    (φ : B →* H) (hφ : Function.Surjective φ) (hK : Odd (Nat.card φ.ker))
    {b : B} (hb : b * b = 1) (hC : Odd (Subgroup.centralizer {φ b}).index) :
    ∃ T : Sylow 2 B, b ∈ (T : Subgroup B) ∧ ∀ x ∈ (T : Subgroup B), b * x = x * b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite H := Finite.of_surjective φ hφ
  set C : Subgroup H := Subgroup.centralizer {φ b}
  have hC2 : ¬ 2 ∣ C.index := by
    rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hC
    omega
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  set Tb : Subgroup H := (Q : Subgroup ↥C).map C.subtype with hTb
  have hTbidx : ¬ 2 ∣ Tb.index := by
    rw [hTb, Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two Q.not_dvd_index hC2
  have hTbC : Tb ≤ C := Subgroup.map_subtype_le _
  have hφb : φ b * φ b = 1 := by rw [← map_mul, hb, map_one]
  have hφbC : φ b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set β : ↥C := ⟨φ b, hφbC⟩
  have hβc : β ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hββ : β * β = 1 := Subtype.ext hφb
  have hβQ : β ∈ (Q : Subgroup ↥C) := by
    haveI : (Subgroup.zpowers β).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hβc)
    have hp : IsPGroup 2 ((Q : Subgroup ↥C) ⊔ Subgroup.zpowers β : Subgroup ↥C) :=
      IsPGroup.to_sup_of_normal_right Q.isPGroup' (isPGroup_zpowers_of_mul_self hββ)
    have hmax : (Q : Subgroup ↥C) ⊔ Subgroup.zpowers β = (Q : Subgroup ↥C) :=
      Q.is_maximal' hp le_sup_left
    have : β ∈ (Q : Subgroup ↥C) ⊔ Subgroup.zpowers β :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers β)
    rwa [hmax] at this
  have hφbTb : φ b ∈ Tb := ⟨β, hβQ, rfl⟩
  set B₁ : Subgroup B := Tb.comap φ
  have hbB₁ : b ∈ B₁ := hφbTb
  have hB₁idx : B₁.index = Tb.index := Subgroup.index_comap_of_surjective Tb hφ
  have hzp : IsPGroup 2 ((Subgroup.zpowers b).subgroupOf B₁) :=
    (isPGroup_zpowers_of_mul_self hb).comap_subtype
  obtain ⟨T₁', hT₁'⟩ := IsPGroup.exists_le_sylow hzp
  set T₁ : Subgroup B := (T₁' : Subgroup ↥B₁).map B₁.subtype with hT₁
  have hT₁p : IsPGroup 2 T₁ := T₁'.isPGroup'.map B₁.subtype
  have hT₁idx : ¬ 2 ∣ T₁.index := by
    rw [hT₁, Subgroup.index_map_subtype, hB₁idx]
    exact Nat.Prime.not_dvd_mul Nat.prime_two T₁'.not_dvd_index hTbidx
  refine ⟨hT₁p.toSylow hT₁idx, ?_, ?_⟩
  · have : (⟨b, hbB₁⟩ : ↥B₁) ∈ (T₁' : Subgroup ↥B₁) :=
      hT₁' (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b))
    exact ⟨⟨b, hbB₁⟩, this, rfl⟩
  · intro x hx
    have hbT : b ∈ T₁ :=
      ⟨⟨b, hbB₁⟩, hT₁' (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)), rfl⟩
    have hxB₁ : x ∈ B₁ := by
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hφx : φ x ∈ C := hTbC hxB₁
    have hcomm : φ x * φ b = φ b * φ x := Subgroup.mem_centralizer_singleton_iff.mp hφx
    have hcT : b * x * b⁻¹ * x⁻¹ ∈ T₁ :=
      T₁.mul_mem (T₁.mul_mem (T₁.mul_mem hbT hx) (T₁.inv_mem hbT)) (T₁.inv_mem hx)
    have hcK : b * x * b⁻¹ * x⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      calc φ b * φ x * (φ b)⁻¹ * (φ x)⁻¹ = (φ x * φ b) * (φ b)⁻¹ * (φ x)⁻¹ := by rw [hcomm]
        _ = 1 := by group
    have hcop : Nat.Coprime (Nat.card T₁) (Nat.card φ.ker) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT₁p
      rw [hk]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hK)
    have hdis := Subgroup.disjoint_of_coprime_natCard hcop
    have h1 : b * x * b⁻¹ * x⁻¹ = 1 := Subgroup.disjoint_def.mp hdis hcT hcK
    calc b * x = (b * x * b⁻¹ * x⁻¹) * (x * b) := by group
      _ = x * b := by rw [h1, one_mul]

end CFSG.ClassicalInvolution.Sp62Rec
