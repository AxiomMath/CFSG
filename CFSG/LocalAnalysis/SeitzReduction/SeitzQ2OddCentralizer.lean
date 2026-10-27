module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotKernel

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] {L : Subgroup G}

theorem mem_conjugate_iff_conj_mem {g x : G} : x ∈ CFSG.conjugate L g ↔ g * x * g⁻¹ ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have h : g * ((MulAut.conj g⁻¹).toMonoidHom l) * g⁻¹ = l := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h]
    exact hl
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem eq_of_odd_of_conj_eq {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (htL : t ∉ L) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c l : G} (hc : c ∈ centralizer ({t} : Set G)) (hco : Odd (orderOf c)) (hl : l ∈ L)
    (hcl : ∀ y ∈ L, c * y * c⁻¹ = l * y * l⁻¹) : c = l := by
  rcases F4Pilot.eq_or_eq_mul_of_conj_eq htC ht hK hc hl hcl with h | h
  · exact h
  · exfalso
    apply htL
    have hlt : Commute l t := mem_centralizer_iff.1 htC l hl
    obtain ⟨k, hk⟩ := hco
    have h1 : (l * t) ^ (2 * k + 1) = 1 := by rw [← h, ← hk, pow_orderOf_eq_one]
    have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    have htk : t ^ (2 * k + 1) = t := by
      rw [pow_succ, pow_mul, ht2, one_pow, one_mul]
    rw [hlt.mul_pow, htk] at h1
    have h2 : t = (l ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_mem (pow_mem hl _)

theorem exists_conj_eq_of_odd_of_isPGroup_outer (hOut : IsPGroup 2 (Outer L)) {c : G}
    (hcN : c ∈ normalizer (L : Set G)) (hco : Odd (orderOf c)) :
    ∃ l ∈ L, ∀ y ∈ L, c * y * c⁻¹ = l * y * l⁻¹ := by
  set β : MulAut L := L.normalizerMonoidHom ⟨c, hcN⟩ with hβ
  have hβc : orderOf β ∣ orderOf c := by
    have h1 := orderOf_map_dvd L.normalizerMonoidHom (⟨c, hcN⟩ : normalizer (L : Set G))
    rwa [← hβ, Subgroup.orderOf_mk] at h1
  set π : MulAut L →* Outer L := QuotientGroup.mk' (inner L) with hπ
  have hπβ : orderOf (π β) ∣ orderOf c := (orderOf_map_dvd π β).trans hβc
  obtain ⟨n, hn⟩ := hOut (π β)
  have h2n : orderOf (π β) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (2 ^ n) (orderOf c) :=
    Nat.Coprime.pow_left n ((Nat.coprime_two_left).2 hco)
  have h1 : orderOf (π β) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2n hπβ
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨l, hl⟩ := h1
  refine ⟨l, l.2, fun y hy => ?_⟩
  have h3 := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
  rw [h3, hβ]
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem mem_of_odd_of_mem_centralizer (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c : G} (hc : c ∈ centralizer ({t} : Set G)) (hco : Odd (orderOf c)) : c ∈ L := by
  obtain ⟨l, hl, hcl⟩ := exists_conj_eq_of_odd_of_isPGroup_outer hOut (hCN hc) hco
  rw [eq_of_odd_of_conj_eq htC ht htL hK hc hco hl hcl]
  exact hl

theorem mem_conjugate_of_odd_of_mem_centralizer (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (g : G)
    {c : G} (hc : c ∈ centralizer ({g⁻¹ * t * g} : Set G)) (hco : Odd (orderOf c)) :
    c ∈ CFSG.conjugate L g := by
  have hcw : c * (g⁻¹ * t * g) = (g⁻¹ * t * g) * c := mem_centralizer_singleton_iff.1 hc
  have hgc : g * c * g⁻¹ ∈ L := by
    refine mem_of_odd_of_mem_centralizer hOut htC ht htL hCN hK ?_ ?_
    · rw [mem_centralizer_singleton_iff]
      calc g * c * g⁻¹ * t = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by rw [hcw]
        _ = t * (g * c * g⁻¹) := by group
    · have h := MulEquiv.orderOf_eq (MulAut.conj g) c
      rw [MulAut.conj_apply] at h
      rw [h]
      exact hco
  exact mem_conjugate_iff_conj_mem.2 hgc

theorem false_of_conj_mem_closure_odd (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (g : G)
    (hw : g⁻¹ * t * g ∈ closure {c : G | c * (g⁻¹ * t * g) = (g⁻¹ * t * g) * c ∧
      Odd (orderOf c)}) : False := by
  apply htL
  have hle : closure {c : G | c * (g⁻¹ * t * g) = (g⁻¹ * t * g) * c ∧ Odd (orderOf c)} ≤
      CFSG.conjugate L g := by
    rw [closure_le]
    rintro c ⟨hcw, hco⟩
    exact mem_conjugate_of_odd_of_mem_centralizer hOut htC ht htL hCN hK g
      (mem_centralizer_singleton_iff.2 hcw) hco
  have h := mem_conjugate_iff_conj_mem.1 (hle hw)
  have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
  rwa [e] at h

theorem conj_ne_of_mem_closure_odd (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {w : G}
    (hw : w ∈ closure {c : G | c ∈ L ∧ c * w = w * c ∧ Odd (orderOf c)}) (g : G) :
    g⁻¹ * t * g ≠ w := by
  intro hgw
  refine false_of_conj_mem_closure_odd hOut htC ht htL hCN hK g ?_
  rw [hgw]
  exact closure_mono (show {c : G | c ∈ L ∧ c * w = w * c ∧ Odd (orderOf c)} ⊆
    {c : G | c * w = w * c ∧ Odd (orderOf c)} from fun c hc => ⟨hc.2.1, hc.2.2⟩) hw

theorem conj_not_mem_of_forall_mem_closure_odd (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hodd : ∀ w ∈ L, orderOf w = 2 →
      w ∈ closure {c : G | c ∈ L ∧ c * w = w * c ∧ Odd (orderOf c)}) (g : G) :
    g⁻¹ * t * g ∉ L := by
  intro hgL
  have h2 : orderOf (g⁻¹ * t * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [h, ht]
  exact conj_ne_of_mem_closure_odd hOut htC ht htL hCN hK (hodd _ hgL h2) g rfl

theorem not_forall_commute_sylow_of_mem_closure_odd (hOut : IsPGroup 2 (Outer L)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (htL : t ∉ L)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hodd : ∀ (U : Sylow 2 L) (z : L), z ≠ 1 → (∀ u ∈ (U : Subgroup L), u * z = z * u) →
      (z : G) ∈ closure {c : G | c ∈ L ∧ c * z = z * c ∧ Odd (orderOf c)}) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hU
  have hne : (⟨g⁻¹ * t * g, hgL⟩ : L) ≠ 1 := by
    intro h1
    have h1' : g⁻¹ * t * g = 1 := congrArg Subtype.val h1
    have ht1 : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h1']; group
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by decide)
  exact conj_ne_of_mem_closure_odd hOut htC ht htL hCN hK
    (hodd U ⟨g⁻¹ * t * g, hgL⟩ hne fun u hu => Subtype.ext (hU u hu)) g rfl

end CFSG.SeitzReduction.SeitzQ2
