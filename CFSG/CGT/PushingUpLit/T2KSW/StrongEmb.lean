module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.FusionDefs

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG.ABGLocalTools CFSG.Open

variable {X : Type*} [Group X]

private theorem mem_map_conj_inv_iff {H : Subgroup X} {g y : X} :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

private theorem mem_map_conj_iff {H : Subgroup X} {g y : X} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  simpa using (mem_map_conj_inv_iff (H := H) (g := g⁻¹) (y := y))

private theorem exists_mem_conj_mem_of_coprime_relIndex [Finite X] {p : ℕ} [Fact p.Prime]
    {R A B : Subgroup X} (hAp : IsPGroup p A) (hA : Nat.Coprime p (A.relIndex R))
    (hBR : B ≤ R) (hBp : IsPGroup p B) :
    ∃ r ∈ R, ∀ y ∈ B, r⁻¹ * y * r ∈ A := by
  let SA : Sylow p R := (hAp.comap_subtype (K := R)).toSylow
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hA)
  obtain ⟨Y, hY⟩ := (hBp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R Y SA
  refine ⟨((r⁻¹ : R) : X), (r⁻¹ : R).2, fun y hy => ?_⟩
  have hmem : MulAut.conj r • (⟨y, hBR hy⟩ : R) ∈ ((r • Y : Sylow p R) : Subgroup R) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _
      (hY (show (⟨y, hBR hy⟩ : R) ∈ B.comap R.subtype from hy))
  rw [hr] at hmem
  have hA' : ((MulAut.conj r • (⟨y, hBR hy⟩ : R) : R) : X) ∈ A := hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hA'

theorem exists_mem_conj_mem_of_isSylowOf [Finite X] {p : ℕ} [Fact p.Prime] {H A P : Subgroup X}
    (hA : IsSylowOf p A H) (hPH : P ≤ H) (hP : IsPGroup p P) :
    ∃ h ∈ H, ∀ y ∈ P, h⁻¹ * y * h ∈ A := by
  rw [isSylowOf_iff] at hA
  exact exists_mem_conj_mem_of_coprime_relIndex hA.2.1 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2
    hA.2.2) hPH hP

private theorem isSylowOf_top_of_isSylowOf_normalizer [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsSylowOf p P (Subgroup.normalizer (P : Set X))) :
    IsSylowOf p P ⊤ := by
  obtain ⟨S, hPS⟩ := hP.isPGroup.exists_le_sylow
  have hPS' : P = (S : Subgroup X) := by
    by_contra hne
    have hlt : P < (S : Subgroup X) := lt_of_le_of_ne hPS hne
    have : Group.IsNilpotent (S : Subgroup X) := S.isPGroup'.isNilpotent
    have hlt' : P.subgroupOf S < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact fun h => hne (le_antisymm hPS h)
    have hn := Group.normalizerCondition_of_isNilpotent (P.subgroupOf S) hlt'
    rw [← Subgroup.subgroupOf_normalizer_eq hPS] at hn
    obtain ⟨s, hs1, hs2⟩ := IsConcreteLE.exists_of_lt hn
    have hsN : (s : X) ∈ Subgroup.normalizer (P : Set X) := hs1
    have hsP : (s : X) ∉ P := hs2
    have heq : (S : Subgroup X) ⊓ Subgroup.normalizer (P : Set X) = P :=
      hP.eq_of_le (le_inf hPS Subgroup.le_normalizer) inf_le_right
        (S.isPGroup'.to_le inf_le_left)
    exact hsP (by rw [← heq]; exact ⟨s.2, hsN⟩)
  rw [isSylowOf_iff]
  refine ⟨le_top, hP.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right, hPS']
  exact S.not_dvd_index

private theorem mem_iff_of_conj_le [Finite X] {P B : Subgroup X} (hcard : Nat.card P = Nat.card B)
    {m : X} (hm : ∀ y ∈ P, m⁻¹ * y * m ∈ B) : ∀ y, y ∈ B ↔ m * y * m⁻¹ ∈ P := by
  have hle : P.map (MulAut.conj m⁻¹).toMonoidHom ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hm y hy
  have hcard' : Nat.card (P.map (MulAut.conj m⁻¹).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective
  have heq : P.map (MulAut.conj m⁻¹).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard', hcard])
  intro y
  rw [← heq, mem_map_conj_inv_iff]

theorem fusionStronglyEmbedded_of_normalizer_le [Finite X] {B H : Subgroup X}
    (hB : IsSylowOf 2 B ⊤) (hB1 : B ≠ ⊥) (hH : H ≠ ⊤)
    (hN : ∀ P : Subgroup X, P ≤ B → P ≠ ⊥ → Subgroup.normalizer (P : Set X) ≤ H) :
    fusionStronglyEmbedded H := by
  have hBH : B ≤ H := Subgroup.le_normalizer.trans (hN B le_rfl hB1)
  have hBH' : IsSylowOf 2 B H := hB.of_le hBH le_top
  have key : ∀ P : Subgroup X, P ≤ H → IsPGroup 2 P → P ≠ ⊥ →
      Subgroup.normalizer (P : Set X) ≤ H := by
    intro P hPH hP hP1 x hx
    obtain ⟨m, hm, hmP⟩ := exists_mem_conj_mem_of_isSylowOf hBH' hPH hP
    have hP'B : P.map (MulAut.conj m⁻¹).toMonoidHom ≤ B := by
      rintro _ ⟨y, hy, rfl⟩
      simpa using hmP y hy
    have hP'1 : P.map (MulAut.conj m⁻¹).toMonoidHom ≠ ⊥ := fun h =>
      hP1 ((Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj m⁻¹).injective).1 h)
    have hx' : m⁻¹ * x * m ∈ Subgroup.normalizer
        ((P.map (MulAut.conj m⁻¹).toMonoidHom : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [mem_map_conj_inv_iff, mem_map_conj_inv_iff]
      have h1 := Subgroup.mem_normalizer_iff.1 hx (m * y * m⁻¹)
      rw [show m⁻¹ * x * m * y * (m⁻¹ * x * m)⁻¹ = m⁻¹ * (x * (m * y * m⁻¹) * x⁻¹) * m by group]
      rw [show m * (m⁻¹ * (x * (m * y * m⁻¹) * x⁻¹) * m) * m⁻¹ = x * (m * y * m⁻¹) * x⁻¹ by group]
      exact h1
    have hxH := hN _ hP'B hP'1 hx'
    have := H.mul_mem (H.mul_mem hm hxH) (H.inv_mem hm)
    simpa [mul_assoc] using this
  refine ⟨hH, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hB.isPGroup
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hB1 ((Subgroup.eq_bot_iff_card B).2 (by simpa using hk))
    have h2 : 2 ∣ Nat.card B := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hBH))
  · intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨P, hPK⟩ := exists_isSylowOf 2 (H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom)
    have hP1 : P ≠ ⊥ := by
      intro h
      have hc := hPK.card_eq
      rw [h, Subgroup.card_bot] at hc
      have hd : 2 ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom) :=
        even_iff_two_dvd.1 hodd
      have hne : Nat.card ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom) ≠ 0 := Nat.card_pos.ne'
      have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne).1 hd
      have h2 : 2 ≤ 2 ^ (Nat.card ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom)).factorization 2 :=
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h1
      omega
    have hPH : P ≤ H := hPK.le.trans inf_le_left
    have hPHg : P ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := hPK.le.trans inf_le_right
    have hP2 : IsPGroup 2 P := hPK.isPGroup
    have hNH : Subgroup.normalizer (P : Set X) ≤ H := key P hPH hP2 hP1
    have hP₁H : P.map (MulAut.conj g).toMonoidHom ≤ H := by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_map_conj_inv_iff.1 (hPHg hy)
    have hP₁1 : P.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun h =>
      hP1 ((Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj g).injective).1 h)
    have hP₁2 : IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) := hP2.map _
    have hNH₁ := key _ hP₁H hP₁2 hP₁1
    have hNg : Subgroup.normalizer (P : Set X) ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro x hx
      rw [mem_map_conj_inv_iff]
      apply hNH₁
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [mem_map_conj_iff, mem_map_conj_iff]
      have h1 := Subgroup.mem_normalizer_iff.1 hx (g⁻¹ * y * g)
      rw [show g⁻¹ * (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ by group]
      exact h1
    have hPN : IsSylowOf 2 P (Subgroup.normalizer (P : Set X)) :=
      hPK.of_le Subgroup.le_normalizer (le_inf hNH hNg)
    have hPX : IsSylowOf 2 P ⊤ := isSylowOf_top_of_isSylowOf_normalizer hPN
    obtain ⟨m, hm, hmP⟩ := exists_mem_conj_mem_of_isSylowOf hBH' hPH hP2
    obtain ⟨m₁, hm₁, hm₁P⟩ := exists_mem_conj_mem_of_isSylowOf hBH' hP₁H hP₁2
    have hcardP : Nat.card P = Nat.card B := by rw [hPX.card_eq, hB.card_eq]
    have hcardP₁ : Nat.card (P.map (MulAut.conj g).toMonoidHom) = Nat.card B := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardP]
    have e1 := mem_iff_of_conj_le hcardP hmP
    have e2 := mem_iff_of_conj_le hcardP₁ hm₁P
    have hz : m₁⁻¹ * g * m ∈ Subgroup.normalizer (B : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [e1 y, e2 (m₁⁻¹ * g * m * y * (m₁⁻¹ * g * m)⁻¹), mem_map_conj_iff]
      rw [show g⁻¹ * (m₁ * (m₁⁻¹ * g * m * y * (m₁⁻¹ * g * m)⁻¹) * m₁⁻¹) * g = m * y * m⁻¹ by
        group]
    have hzH := hN B le_rfl hB1 hz
    apply hg
    have := H.mul_mem (H.mul_mem hm₁ hzH) (H.inv_mem hm)
    simpa [mul_assoc] using this

end CFSG.CGT.PushingUpLit.T2KSW
