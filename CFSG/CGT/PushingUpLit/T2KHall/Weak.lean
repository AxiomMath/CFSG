module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Simple
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.CGT.PushingUpLit.T2K

open Subgroup CFSG.EvenSporadicStandard.Finkelstein77
open CFSG.Assembly (InCatalog KProper)
open CFSG.Open (SemidihedralGroup)
open scoped Pointwise

@[expose] def HallWeaklyClosedFourWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    ∀ (T : Subgroup G) (s : G), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → orderOf s = 4 →
      (Subgroup.zpowers s ≤ T ∧ ∀ g : G,
        (Subgroup.zpowers s).map (MulAut.conj g).toMonoidHom ≤ T →
          (Subgroup.zpowers s).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers s) →
        (∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥T ≃* DihedralGroup (2 ^ m))) ∨
          ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥T ≃* SemidihedralGroup n)

namespace Z4Hall

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_map_conj_eq (P₁ P₂ : Sylow 2 G) :
    ∃ g : G, (P₁ : Subgroup G).map (MulAut.conj g).toMonoidHom = (P₂ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₁ P₂
  refine ⟨g, ?_⟩
  have h1 : ((P₂ : Subgroup G) : Set G) = MulAut.conj g • ((P₁ : Subgroup G) : Set G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h2 : (MulAut.conj g) y ∈ MulAut.conj g • ((P₁ : Subgroup G) : Set G) :=
      ⟨y, hy, rfl⟩
    rw [← h1] at h2
    exact h2
  · intro hx
    have hx' : x ∈ MulAut.conj g • ((P₁ : Subgroup G) : Set G) := by
      rw [← h1]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    exact ⟨y, hy, hyx⟩

theorem exists_mem_conj_le {M P Q : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P M)
    (hQM : Q ≤ M) (hQ : IsPGroup 2 Q) : ∃ m ∈ M, ∀ x ∈ Q, m⁻¹ * x * m ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', rfl⟩ := hP
  have hQ' : IsPGroup 2 (Q.subgroupOf M) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) P' R
  refine ⟨m, m.2, fun x hx => ?_⟩
  have h1 : ((R : Subgroup M) : Set M) = MulAut.conj m • ((P' : Subgroup M) : Set M) := by
    rw [← hm, Sylow.coe_subgroup_smul]
    rfl
  have hxR : (⟨x, hQM hx⟩ : M) ∈ ((R : Subgroup M) : Set M) :=
    hR (Subgroup.mem_subgroupOf.2 hx)
  rw [h1] at hxR
  obtain ⟨y, hy, hyx⟩ := hxR
  have hy' : (y : G) = (m : G)⁻¹ * x * (m : G) := by
    have h2 : (m : G) * (y : G) * (m : G)⁻¹ = x := by
      have := congrArg Subtype.val hyx
      simpa [MulAut.conj_apply] using this
    rw [← h2]
    group
  rw [← hy']
  exact ⟨y, hy, rfl⟩

theorem weaklyClosedInNormalizer_of_weaklyClosed {T Z : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hZT : Z ≤ T)
    (hwc : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ T →
      Z.map (MulAut.conj g).toMonoidHom = Z) : WeaklyClosedInNormalizer Z := by
  classical
  have hZ2 : IsPGroup 2 Z := hT.isPGroup.to_le hZT
  have hmem_of_eq : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom = Z →
      g ∈ normalizer (Z : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h2 : g * y * g⁻¹ ∈ Z.map (MulAut.conj g).toMonoidHom :=
        ⟨y, hy, by simp [MulAut.conj_apply]⟩
      rw [hg] at h2
      exact h2
    · intro hy
      have h2 : g * y * g⁻¹ ∈ Z.map (MulAut.conj g).toMonoidHom := by
        rw [hg]
        exact hy
      obtain ⟨w, hw, hwy⟩ := h2
      have h3 : g * w * g⁻¹ = g * y * g⁻¹ := by simpa [MulAut.conj_apply] using hwy
      have h4 : w = y := by simpa using h3
      rwa [← h4]
  have hTN : T ≤ normalizer (Z : Set G) := by
    intro t ht
    refine hmem_of_eq t (hwc t ?_)
    rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using T.mul_mem (T.mul_mem ht (hZT hz)) (T.inv_mem ht)
  intro h hh
  have hTN' : CFSG.ABGLocalTools.IsSylowOf 2 T (normalizer (Z : Set G)) :=
    hT.of_le hTN le_top
  have hZh2 : IsPGroup 2 (Z.map (MulAut.conj h).toMonoidHom) := hZ2.map _
  obtain ⟨m, hm, hmT⟩ := exists_mem_conj_le hTN' hh hZh2
  have hle : Z.map (MulAut.conj (m⁻¹ * h)).toMonoidHom ≤ T := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : h * z * h⁻¹ ∈ Z.map (MulAut.conj h).toMonoidHom :=
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    have h2 := hmT _ h1
    have h3 : (MulAut.conj (m⁻¹ * h)).toMonoidHom z = m⁻¹ * (h * z * h⁻¹) * m := by
      show (m⁻¹ * h) * z * (m⁻¹ * h)⁻¹ = _
      group
    rw [h3]
    exact h2
  have hgN := hmem_of_eq _ (hwc (m⁻¹ * h) hle)
  have hhN : h ∈ normalizer (Z : Set G) := by
    have e : h = m * (m⁻¹ * h) := by group
    rw [e]
    exact mul_mem hm hgN
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 := (mem_normalizer_iff.1 hhN y).1 hy
    simpa [MulAut.conj_apply] using h1
  · intro hx
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    swap
    · show h * (h⁻¹ * x * h) * h⁻¹ = x
      group
    have h1 := (mem_normalizer_iff.1 hhN (h⁻¹ * x * h)).2
      (by simpa [mul_assoc] using hx)
    exact h1

theorem nonempty_mulEquiv_sylow {T N : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hTN : T ≤ N) (S : Sylow 2 ↥N) : Nonempty (↥T ≃* ↥(S : Subgroup ↥N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hT.of_le hTN le_top).exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := exists_map_conj_eq Q S
  exact ⟨(subgroupOfEquivOfLe hTN).symm.trans
    ((MulEquiv.subgroupCongr hQ.symm).trans
      (((Q : Subgroup ↥N).equivMapOfInjective _ (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hg)))⟩

end Sylow

theorem nonabelian_of_simple_of_orderOf_four {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {s : G} (hs : orderOf s = 4) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hz1 : s ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hs] at this
    omega
  have hnorm : (zpowers (s ^ 2)).Normal := ⟨fun n _ g => by
    have h1 : g * n * g⁻¹ = n := by
      rw [hcomm g n]
      group
    rwa [h1]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers (s ^ 2)) with h | h
  · exact hz1 (by simpa using h)
  · have h1 : Nat.card G = 2 := by
      have h2 : Nat.card (zpowers (s ^ 2)) = Nat.card G := by rw [h, Subgroup.card_top]
      rw [← h2, Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hs]; norm_num), hs]
    have h4 : 4 ∣ Nat.card G := hs ▸ orderOf_dvd_natCard s
    rw [h1] at h4
    omega

end Z4Hall

theorem hallWeaklyClosedFour_of_lemma25 (h : Asc76Lemma25) : HallWeaklyClosedFourWeak := by
  intro G _ _ _hK hS T s hT hs hwc'
  obtain ⟨hZT, hwc⟩ := hwc'
  have : IsSimpleGroup G := hS
  have hnonab : ∃ a b : G, a * b ≠ b * a := Z4Hall.nonabelian_of_simple_of_orderOf_four hs
  have hW : WeaklyClosedInNormalizer (zpowers s) :=
    Z4Hall.weaklyClosedInNormalizer_of_weaklyClosed hT hZT hwc
  have hz1 : s ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hs] at this
    omega
  have hX : (normalClosure {s ^ 2} : Subgroup G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (normalClosure {s ^ 2} : Subgroup G) with h1 | h1
    · exfalso
      have hmem : s ^ 2 ∈ (normalClosure {s ^ 2} : Subgroup G) :=
        subset_normalClosure (Set.mem_singleton _)
      rw [h1, mem_bot] at hmem
      exact hz1 hmem
    · exact h1
  have hTX : T ≤ (normalClosure {s ^ 2} : Subgroup G) := hX ▸ le_top
  rcases h G s hs hW with hZ | ⟨S, n, hn, ⟨ε⟩⟩ | ⟨S, n, hn, ⟨ε⟩⟩
  · exact absurd hZ (not_inZStar_of_simple hnonab hs)
  · obtain ⟨e⟩ := Z4Hall.nonempty_mulEquiv_sylow hT hTX S
    exact Or.inl ⟨n - 1, by omega, ⟨e.trans ε⟩⟩
  · obtain ⟨e⟩ := Z4Hall.nonempty_mulEquiv_sylow hT hTX S
    exact Or.inr ⟨n, hn, ⟨e.trans ε⟩⟩

end CFSG.CGT.PushingUpLit.T2K
