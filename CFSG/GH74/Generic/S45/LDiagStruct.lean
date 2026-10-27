module

public import CFSG.GH74.Generic.S45.LKCent
public import CFSG.GH74.Generic.S45.LDiagCore

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup
open scoped commutatorElement

section KDataPerfect

variable {X : Type} [Group X] [Finite X] {K : Subgroup X} {z : X}

theorem KData.commutator_sup_le (h : KData X K z) :
    ⁅K ⊔ centralizer (K : Set X), K ⊔ centralizer (K : Set X)⁆ ≤ K := by
  have hKn := h.normal
  have hDn : (centralizer (K : Set X)).Normal := inferInstance
  obtain ⟨-, hDc⟩ := h.D_isPGroup_cyclic
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨k₁, hk₁, d₁, hd₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg₁
  obtain ⟨k₂, hk₂, d₂, hd₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg₂
  have hkd : ∀ k ∈ K, ∀ d ∈ centralizer (K : Set X), k * d = d * k :=
    fun k hk d hd => mem_centralizer_iff.1 hd k hk
  have hdd : d₁ * d₂ = d₂ * d₁ := by
    have := congrArg Subtype.val (@mul_comm ↥(centralizer (K : Set X))
      (IsCyclic.commGroup (α := ↥(centralizer (K : Set X)))).toCommMagma ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩)
    simpa using this
  have e1 : k₁ * d₁ = d₁ * k₁ := hkd k₁ hk₁ d₁ hd₁
  have e2 : k₂ * d₂ = d₂ * k₂ := hkd k₂ hk₂ d₂ hd₂
  have hc : ⁅k₁ * d₁, k₂ * d₂⁆ = ⁅k₁, k₂⁆ := by
    have h1 : d₁ * (k₂ * d₂) = (k₂ * d₂) * d₁ := by
      calc d₁ * (k₂ * d₂) = (d₁ * k₂) * d₂ := by group
        _ = (k₂ * d₁) * d₂ := by rw [← hkd k₂ hk₂ d₁ hd₁]
        _ = k₂ * (d₁ * d₂) := by group
        _ = k₂ * (d₂ * d₁) := by rw [hdd]
        _ = (k₂ * d₂) * d₁ := by group
    rw [e1, comm_mul_left_of_commute e1.symm h1, e2,
      comm_mul_right_of_commute (hkd k₁ hk₁ d₂ hd₂).symm e2.symm]
  rw [hc]
  exact mul_mem (mul_mem (mul_mem hk₁ hk₂) (inv_mem hk₁)) (inv_mem hk₂)


theorem KData.perfect_le (h : KData X K z) {P : Subgroup X} (hP : ⁅P, P⁆ = P) : P ≤ K := by
  have hKn := h.normal
  have hDn : (centralizer (K : Set X)).Normal := inferInstance
  set N : Subgroup X := K ⊔ centralizer (K : Set X) with hN
  have hNn : N.Normal := inferInstance
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hTN : (T : Subgroup X) ≤ N := h.sylow_le T
  have hoddidx : Odd N.index := by
    by_contra hc
    have h2 : 2 ∣ N.index := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hc)
    exact T.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hTN))
  let ψ : X →* X ⧸ N := QuotientGroup.mk' N
  have hR : ⁅P.map ψ, P.map ψ⁆ = P.map ψ := by rw [← Subgroup.map_commutator, hP]
  have hRodd : Odd (Nat.card (P.map ψ)) := by
    have h1 : Nat.card (P.map ψ) ∣ Nat.card (X ⧸ N) := Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (X ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
    rw [h2] at h1
    exact hoddidx.of_dvd_nat h1
  have hRbot := eq_bot_of_perfect_of_odd hR hRodd
  have hPN : P ≤ N := by
    rw [← QuotientGroup.ker_mk' N]
    exact (Subgroup.map_eq_bot_iff _).1 hRbot
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hPN hPN
    _ ≤ K := h.commutator_sup_le

end KDataPerfect


section H1

variable {X U : Type} [Group X] [Finite X] [Group U] {K : Subgroup X} {z : X}

theorem map_perfect_le_map_of_KCent (hd : KData X K z) (hKC : KCent ↥K) (f : U →* X) {t : X}
    (htK : t ∈ K) (ht : orderOf t = 2) (hfc : ∀ u, f u * t = t * f u)
    (hsurj : ∀ y : X, y * t = t * y → ∃ u, f u = y)
    {W : Subgroup U} [W.Normal] (hW : ⁅W, W⁆ = W) {e : U} (heW : e ∈ W) (hfe : f e ≠ 1)
    {Q : Subgroup U} (hQ : ⁅Q, Q⁆ = Q) : Q.map f ≤ W.map f := by
  set H₀ : Subgroup X := K ⊓ centralizer ({t} : Set X) with hH₀
  set S : Subgroup X := ⁅H₀, H₀⁆ with hS
  have hmapS : ∀ R : Subgroup U, ⁅R, R⁆ = R → R.map f ≤ S := by
    intro R hR
    have hRp : ⁅R.map f, R.map f⁆ = R.map f := by rw [← Subgroup.map_commutator, hR]
    have hK1 : R.map f ≤ K := hd.perfect_le hRp
    have hC1 : R.map f ≤ centralizer ({t} : Set X) := by
      rintro _ ⟨u, -, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hfc u)
    calc R.map f = ⁅R.map f, R.map f⁆ := hRp.symm
      _ ≤ ⁅H₀, H₀⁆ := Subgroup.commutator_mono (le_inf hK1 hC1) (le_inf hK1 hC1)
  have hSsimple : IsSimpleGroup ↥S := by
    let s : ↥K := ⟨t, htK⟩
    have hs2 : orderOf s = 2 := by rw [Subgroup.orderOf_mk]; exact ht
    obtain ⟨hsimple, -, -⟩ := hKC s hs2
    have hmapC : (centralizer ({s} : Set ↥K)).map K.subtype = H₀ := by
      ext y
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hc' : c * s = s * c := mem_centralizer_singleton_iff.1 hc
        exact ⟨c.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val hc')⟩
      · intro hy
        obtain ⟨hyK, hyc⟩ := hy
        refine ⟨⟨y, hyK⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.1 hyc)
    have hSeq : (⁅centralizer ({s} : Set ↥K), centralizer ({s} : Set ↥K)⁆).map K.subtype = S := by
      rw [Subgroup.map_commutator, hmapC]
    exact (MulEquiv.isSimpleGroup_congr
      ((Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hSeq))).1 hsimple
  have hBS : W.map f ≤ S := hmapS W hW
  have hSB : S ≤ W.map f := by
    have hnorm : ((W.map f).subgroupOf S).Normal := by
      constructor
      intro n hn g
      obtain ⟨w, hw, hwn⟩ := hn
      have hgH : (g : X) ∈ H₀ := Subgroup.commutator_le_self H₀ g.2
      have hgc : (g : X) * t = t * (g : X) := mem_centralizer_singleton_iff.1 hgH.2
      obtain ⟨u, hu⟩ := hsurj (g : X) hgc
      show (g : X) * (n : X) * (g : X)⁻¹ ∈ W.map f
      refine ⟨u * w * u⁻¹, Subgroup.Normal.conj_mem inferInstance w hw u, ?_⟩
      have hwn' : f w = (n : X) := hwn
      rw [map_mul, map_mul, map_inv, hu, hwn']
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((W.map f).subgroupOf S) with h | h
    · exfalso
      have hmem : (⟨f e, hBS ⟨e, heW, rfl⟩⟩ : ↥S) ∈ (W.map f).subgroupOf S := ⟨e, heW, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hfe (congrArg Subtype.val hmem)
    · intro y hy
      have hmem : (⟨y, hy⟩ : ↥S) ∈ (W.map f).subgroupOf S := by rw [h]; trivial
      exact hmem
  exact (hmapS Q hQ).trans hSB

end H1

end CFSG.GH74.Generic.S45
