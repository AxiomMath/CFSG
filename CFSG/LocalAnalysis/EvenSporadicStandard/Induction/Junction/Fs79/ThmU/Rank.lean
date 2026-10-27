module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Basic
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.LocalAnalysis.SectionRank.ThreeInvolutions

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Induction
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

private theorem cj_subgroupOf_map_subtype {C X : Subgroup G} (hXC : X ≤ C) (c : ↥C) :
    (cj c (X.subgroupOf C)).map C.subtype = cj (c : G) X := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_cj] at hy ⊢
    change ((c⁻¹ * y * c : ↥C) : G) ∈ X at hy
    change (c : G)⁻¹ * (y : G) * (c : G) ∈ X
    exact hy
  · intro hg
    rw [mem_cj] at hg
    have hgC : g ∈ C := by
      have h : g = (c : G) * ((c : G)⁻¹ * g * (c : G)) * (c : G)⁻¹ := by group
      rw [h]
      exact C.mul_mem (C.mul_mem c.2 (hXC hg)) (C.inv_mem c.2)
    refine ⟨⟨g, hgC⟩, ?_, rfl⟩
    rw [mem_cj]
    change ((c⁻¹ * (⟨g, hgC⟩ : ↥C) * c : ↥C) : G) ∈ X
    exact hg

theorem exists_sylow_forall_conj [Finite G] {C U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ C) :
    ∃ T : Subgroup G, T ≤ C ∧ IsPGroup 2 T ∧ U ≤ T ∧
      ∀ X : Subgroup G, IsPGroup 2 X → X ≤ C → ∃ c ∈ C, cj c X ≤ T := by
  have hU' : IsPGroup 2 (U.subgroupOf C) := hU.comap_subtype
  obtain ⟨S, hS⟩ := hU'.exists_le_sylow
  refine ⟨(S : Subgroup ↥C).map C.subtype, Subgroup.map_subtype_le (S : Subgroup ↥C),
    S.isPGroup'.map C.subtype, ?_, ?_⟩
  · intro u hu
    exact Subgroup.mem_map.2 ⟨⟨u, hUC hu⟩, hS ((Subgroup.mem_subgroupOf).2 hu), rfl⟩
  · intro X hX hXC
    have hX' : IsPGroup 2 (X.subgroupOf C) := hX.comap_subtype
    obtain ⟨S₂, hS₂⟩ := hX'.exists_le_sylow
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite (Sylow 2 ↥C) := S.finite_of_finiteIndex
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥C) S₂ S
    have hle : cj c (X.subgroupOf C) ≤ S := by
      intro y hy
      rw [mem_cj] at hy
      have hmem : (MulAut.conj c) • (c⁻¹ * y * c) ∈
          (MulAut.conj c) • (S₂ : Subgroup ↥C) :=
        Subgroup.smul_mem_pointwise_smul (c⁻¹ * y * c) (MulAut.conj c)
          (S₂ : Subgroup ↥C) (hS₂ hy)
      have hS₂eq : (MulAut.conj c) • (S₂ : Subgroup ↥C) = S := by
        rw [← Sylow.coe_subgroup_smul]
        exact congrArg (fun P : Sylow 2 ↥C => (P : Subgroup ↥C)) hc
      rw [hS₂eq] at hmem
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hmem
    refine ⟨(c : G), c.2, ?_⟩
    rw [← cj_subgroupOf_map_subtype hXC c]
    exact Subgroup.map_mono hle

theorem three_le_pRank_of_conj [Finite G] {C T : Subgroup G}
    (hconj : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ C → ∃ c ∈ C, cj c X ≤ T)
    (h3 : 3 ≤ CFSG.Open.pRank 2 C) : 3 ≤ CFSG.Open.pRank 2 T := by
  obtain ⟨E, hEC, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two C
  obtain ⟨c, -, hcT⟩ := hconj E (IsPGroup.of_card hcard) hEC
  have hEab : CFSG.Open.IsElemAbelian 2 (cj c E) := by
    show CFSG.Open.IsElemAbelian 2 (E.map (MulAut.conj c).toMonoidHom)
    exact CFSG.SectionRank.isElemAbelian_map hE _
  have hcardcj : Nat.card (cj c E) = 2 ^ CFSG.Open.pRank 2 C := by
    rw [card_cj, hcard]
  have hle : CFSG.Open.pRank 2 C ≤ CFSG.Open.pRank 2 T :=
    CFSG.SectionRank.le_pRank one_lt_two hcT hEab hcardcj
  omega

theorem pRank_eq_of_mulEquiv [Finite G] {A K : Subgroup G} (e : ↥A ≃* ↥K) :
    CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 K := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup A,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]

theorem exists_fourGroup_of_two_le_pRank [Finite G] {K : Subgroup G}
    (h : 2 ≤ CFSG.Open.pRank 2 K) :
    ∃ v₁ v₂ : G, v₁ ∈ K ∧ v₂ ∈ K ∧ orderOf v₁ = 2 ∧ orderOf v₂ = 2 ∧ v₁ * v₂ = v₂ * v₁ ∧
      v₁ ≠ v₂ := by
  obtain ⟨E, hEK, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two K
  have hcard4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 K := Nat.pow_le_pow_right (by norm_num) h
  have : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨v₁, hv₁⟩ := exists_ne (1 : E)
  have : IsMulCommutative E := hE.1
  have hord₁ : orderOf (v₁ : G) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hE.2 v₁ v₁.2)
      (fun h => hv₁ (Subtype.ext h))
  have hzp : Nat.card (Subgroup.zpowers v₁) = 2 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe v₁]
    exact orderOf_eq_prime (by simpa [pow_two] using hE.2 v₁ v₁.2)
      (fun h => hv₁ (Subtype.ext h))
  have hmem : ∃ v₂ : E, v₂ ∉ Subgroup.zpowers v₁ := by
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Subgroup E) ≤ Subgroup.zpowers v₁ := fun x _ => hcon x
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, hzp] at this
    omega
  obtain ⟨v₂, hv₂⟩ := hmem
  have hv₂ne : v₂ ≠ 1 := fun h => hv₂ (by rw [h]; exact Subgroup.one_mem _)
  have hord₂ : orderOf (v₂ : G) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hE.2 v₂ v₂.2)
      (fun h => hv₂ne (Subtype.ext h))
  have hcomm : (v₁ : G) * (v₂ : G) = (v₂ : G) * (v₁ : G) :=
    congrArg Subtype.val (mul_comm' v₁ v₂)
  have hne : (v₁ : G) ≠ (v₂ : G) := by
    intro h
    apply hv₂
    have hE12 : v₁ = v₂ := Subtype.ext h
    rw [← hE12]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  exact ⟨(v₁ : G), (v₂ : G), hEK v₁.2, hEK v₂.2, hord₁, hord₂, hcomm, hne⟩

theorem exists_elemAbelian_eight [Finite G] {a v₁ v₂ : G} (ha : orderOf a = 2)
    (h1 : orderOf v₁ = 2) (h2 : orderOf v₂ = 2) (h12 : v₁ * v₂ = v₂ * v₁) (hne : v₁ ≠ v₂)
    (ha1 : a * v₁ = v₁ * a) (ha2 : a * v₂ = v₂ * a) (hav₁ : a ≠ v₁) (hav₂ : a ≠ v₂)
    (hav : a ≠ v₁ * v₂) :
    ∃ P : Subgroup G, a ∈ P ∧ v₁ ∈ P ∧ v₂ ∈ P ∧ Nat.card P = 8 ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x * x = 1) ∧
      ∀ H : Subgroup G, a ∈ H → v₁ ∈ H → v₂ ∈ H → P ≤ H :=
  CFSG.SectionRank.exists_elemAbelian_eight ha h1 h2 h12 hne ha1 ha2 hav₁ hav₂ hav

theorem three_le_pRank_of_involutions [Finite G] {H : Subgroup G} {a v₁ v₂ : G}
    (ha : orderOf a = 2) (h1 : orderOf v₁ = 2) (h2 : orderOf v₂ = 2)
    (h12 : v₁ * v₂ = v₂ * v₁) (hne : v₁ ≠ v₂) (ha1 : a * v₁ = v₁ * a) (ha2 : a * v₂ = v₂ * a)
    (hav₁ : a ≠ v₁) (hav₂ : a ≠ v₂) (hav : a ≠ v₁ * v₂) (haH : a ∈ H) (h1H : v₁ ∈ H)
    (h2H : v₂ ∈ H) : 3 ≤ CFSG.Open.pRank 2 H :=
  CFSG.SectionRank.three_le_pRank_of_involutions ha h1 h2 h12 hne ha1 ha2 hav₁ hav₂ hav haH h1H h2H

theorem exists_fourGroup_of_relIndex_two [Finite G] {P R : Subgroup G} (hcard : Nat.card P = 8)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsq : ∀ x ∈ P, x * x = 1) (hRP : R ≤ P)
    (hidx : R.relIndex P = 2) :
    ∃ r₁ r₂ : G, r₁ ∈ R ∧ r₂ ∈ R ∧ orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
      orderOf (r₁ * r₂) = 2 ∧ r₁ * r₂ = r₂ * r₁ := by
  have hRcard : Nat.card R = 4 := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := P)
    have hinf : R ⊓ P = R := inf_eq_left.mpr hRP
    rw [hinf, hidx, hcard] at h
    omega
  have : Nontrivial R := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨r₁, hr₁⟩ := exists_ne (1 : R)
  have hr₁ne : (r₁ : G) ≠ 1 := fun h => hr₁ (Subtype.ext h)
  have hzp : Nat.card (Subgroup.zpowers r₁) = 2 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe r₁]
    exact orderOf_eq_prime (by simpa [pow_two] using hsq (r₁ : G) (hRP r₁.2)) hr₁ne
  have hmem : ∃ r₂ : R, r₂ ∉ Subgroup.zpowers r₁ := by
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Subgroup R) ≤ Subgroup.zpowers r₁ := fun x _ => hcon x
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, hRcard, hzp] at this
    omega
  obtain ⟨r₂, hr₂⟩ := hmem
  have hr₂ne : r₂ ≠ 1 := fun h => hr₂ (by rw [h]; exact Subgroup.one_mem _)
  have hr₂neG : (r₂ : G) ≠ 1 := fun h => hr₂ne (Subtype.ext h)
  have hcomm12 : (r₁ : G) * (r₂ : G) = (r₂ : G) * (r₁ : G) :=
    hcomm (r₁ : G) (hRP r₁.2) (r₂ : G) (hRP r₂.2)
  have hsq12 : ((r₁ : G) * (r₂ : G)) * ((r₁ : G) * (r₂ : G)) = 1 := by
    calc ((r₁ : G) * (r₂ : G)) * ((r₁ : G) * (r₂ : G))
        = (r₁ : G) * ((r₂ : G) * ((r₁ : G) * (r₂ : G))) := by group
      _ = (r₁ : G) * (((r₂ : G) * (r₁ : G)) * (r₂ : G)) := by group
      _ = (r₁ : G) * (((r₁ : G) * (r₂ : G)) * (r₂ : G)) := by rw [hcomm12]
      _ = ((r₁ : G) * (r₁ : G)) * ((r₂ : G) * (r₂ : G)) := by group
      _ = 1 := by rw [hsq (r₁ : G) (hRP r₁.2), hsq (r₂ : G) (hRP r₂.2)]; group
  have hne12 : (r₁ : G) * (r₂ : G) ≠ 1 := by
    intro h
    apply hr₂
    have hGeq : (r₂ : G) = (r₁ : G) := by
      have h1 : (r₁ : G)⁻¹ = r₁ := inv_eq_of_mul_eq_one_right (hsq (r₁ : G) (hRP r₁.2))
      calc (r₂ : G) = (r₁ : G)⁻¹ * ((r₁ : G) * (r₂ : G)) := by group
        _ = (r₁ : G)⁻¹ := by rw [h, mul_one]
        _ = (r₁ : G) := h1
    have hR : r₂ = r₁ := Subtype.ext hGeq
    rw [hR]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  refine ⟨(r₁ : G), (r₂ : G), r₁.2, r₂.2, ?_, ?_, ?_, hcomm12⟩
  · exact orderOf_eq_prime (by simpa [pow_two] using hsq (r₁ : G) (hRP r₁.2)) hr₁ne
  · exact orderOf_eq_prime (by simpa [pow_two] using hsq (r₂ : G) (hRP r₂.2)) hr₂neG
  · exact orderOf_eq_prime (by simpa [pow_two] using hsq12) hne12

end CFSG.EvenSporadicStandard.Induction.ThmU
