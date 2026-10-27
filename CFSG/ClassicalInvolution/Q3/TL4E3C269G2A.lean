module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269GDefs
public import CFSG.ClassicalInvolution.Q3.TL4MF164Dat
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenCoatom

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3C269G2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_sup_centralizer_of_conj {N : Subgroup X} [N.Normal] {t : X} (htN : t ∈ N)
    (ht2 : orderOf t = 2) (hconj : ∀ y ∈ N, orderOf y = 2 → ∃ n ∈ N, n * t * n⁻¹ = y) :
    (⊤ : Subgroup X) ≤ N ⊔ Subgroup.centralizer ({t} : Set X) := by
  intro y _
  have hyN : y * t * y⁻¹ ∈ N := ‹N.Normal›.conj_mem t htN y
  have hord : orderOf (y * t * y⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) t
    rwa [MulAut.conj_apply, ht2] at this
  obtain ⟨n, hn, hnt⟩ := hconj _ hyN hord
  have hc : n⁻¹ * y ∈ Subgroup.centralizer ({t} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (n⁻¹ * y) * t * (n⁻¹ * y)⁻¹ = t := by
      calc (n⁻¹ * y) * t * (n⁻¹ * y)⁻¹ = n⁻¹ * (y * t * y⁻¹) * n := by group
        _ = n⁻¹ * (n * t * n⁻¹) * n := by rw [hnt]
        _ = t := by group
    calc n⁻¹ * y * t = (n⁻¹ * y) * t * (n⁻¹ * y)⁻¹ * (n⁻¹ * y) := by group
      _ = t * (n⁻¹ * y) := by rw [h1]
  have := Subgroup.mul_mem_sup hn hc
  rwa [mul_inv_cancel_left] at this

theorem sup_centralizer_psl2 {F : Type} [Field F] [Finite F]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (h4 : p ^ f % 4 = 1)
    (h13 : 13 ≤ p ^ f) {a b : GorensteinWalter.PSL2 F} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a ≠ b) :
    Subgroup.centralizer ({a} : Set (GorensteinWalter.PSL2 F)) ⊔
      Subgroup.centralizer ({b} : Set (GorensteinWalter.PSL2 F)) = ⊤ := by
  have hca := ComponentClassification.AutL2Facts.isCoatom_centralizer_involution hp hp2 hF h4
    h13 ha
  have hcb := ComponentClassification.AutL2Facts.isCoatom_centralizer_involution hp hp2 hF h4
    h13 hb
  have hne := ComponentClassification.AutL2Facts.centralizer_ne_of_involution hp hp2 hF h4 h13
    ha hb hab
  by_cases hle : Subgroup.centralizer ({b} : Set (GorensteinWalter.PSL2 F)) ≤
      Subgroup.centralizer ({a} : Set (GorensteinWalter.PSL2 F))
  · exfalso
    rcases hcb.le_iff.mp hle with h | h
    · exact hca.1 h
    · exact hne h
  · exact hca.lt_iff.mp (lt_of_le_of_ne le_sup_left fun h => hle (h ▸ le_sup_right))

omit [Finite X] in
theorem sup_centralizer_eq_top_of_normal {N : Subgroup X} [N.Normal]
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (h4 : p ^ f % 4 = 1) (h13 : 13 ≤ p ^ f)
    (e : ↥N ≃* GorensteinWalter.PSL2 F) {t s : X} (htN : t ∈ N) (ht2 : orderOf t = 2)
    (hst : s ≠ t) (hconj : ∃ g : X, s = g * t * g⁻¹) :
    Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at h13
      omega
    · exact h
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨g, rfl⟩ := hconj
  have hsN : g * t * g⁻¹ ∈ N := ‹N.Normal›.conj_mem t htN g
  have hs2 : orderOf (g * t * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) t
    rwa [MulAut.conj_apply, ht2] at this
  have he2 : ∀ y : ↥N, orderOf (y : X) = 2 → orderOf (e y) = 2 := fun y hy => by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hy]
  have hN : Subgroup.centralizer ({(⟨t, htN⟩ : ↥N)} : Set ↥N) ⊔
      Subgroup.centralizer ({(⟨g * t * g⁻¹, hsN⟩ : ↥N)} : Set ↥N) = ⊤ := by
    refine E3C269G.sup_centralizer_eq_top_of_equiv e ?_
    refine sup_centralizer_psl2 hp hp2 hF h4 h13 (he2 _ ht2) (he2 _ hs2) fun h => hst ?_
    exact congrArg Subtype.val (e.injective h).symm
  have hNle : N ≤ Subgroup.centralizer ({t} : Set X) ⊔
      Subgroup.centralizer ({g * t * g⁻¹} : Set X) := by
    intro n hn
    have hmem : (⟨n, hn⟩ : ↥N) ∈ Subgroup.centralizer ({(⟨t, htN⟩ : ↥N)} : Set ↥N) ⊔
        Subgroup.centralizer ({(⟨g * t * g⁻¹, hsN⟩ : ↥N)} : Set ↥N) := by
      rw [hN]
      exact Subgroup.mem_top _
    have hmap := Subgroup.mem_map_of_mem N.subtype hmem
    rw [Subgroup.map_sup] at hmap
    have hcent : ∀ x : ↥N, (Subgroup.centralizer ({x} : Set ↥N)).map N.subtype ≤
        Subgroup.centralizer ({(x : X)} : Set X) := by
      rintro x _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)
    exact sup_le_sup (hcent ⟨t, htN⟩) (hcent ⟨g * t * g⁻¹, hsN⟩) hmap
  have hconjN : ∀ y ∈ N, orderOf y = 2 → ∃ n ∈ N, n * t * n⁻¹ = y := by
    intro y hy hy2
    obtain ⟨c, hc⟩ := isConj_iff.mp (Walter.psl2_isConj_of_orderOf_eq_two F hF hpodd hf0
      (he2 ⟨t, htN⟩ ht2) (he2 ⟨y, hy⟩ hy2))
    refine ⟨(e.symm c : ↥N), (e.symm c).2, ?_⟩
    have h1 : e.symm c * ⟨t, htN⟩ * (e.symm c)⁻¹ = ⟨y, hy⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
    exact congrArg Subtype.val h1
  have htop := le_sup_centralizer_of_conj htN ht2 hconjN
  exact eq_top_iff.mpr (htop.trans (sup_le hNle le_sup_left))

theorem orderOf_quat_a_two : orderOf (QuaternionGroup.a 2 : QuaternionGroup 2) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

omit [Finite X] in
theorem e3C269L2_large (hs : IsSimpleGroup ↥(genFittingFStar X))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : Even f) (hL : LieModel (FStarQuot X) .PSL 2 p f)
    {ι : QuaternionGroup 2 →* X} (hι : Function.Injective ι) {t s : X}
    (hιt : ι (QuaternionGroup.a 2) = t) (htN : t ∈ genFittingFStar X) (hst : s ≠ t)
    (hconj : ∃ g : X, s = g * t * g⁻¹) (h9 : p ^ f ≠ 9) :
    Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := MF164.exists_fstar_equiv_psl2 hs hL
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  have ht2 : orderOf t = 2 := by rw [← hιt, orderOf_injective ι hι, orderOf_quat_a_two]
  obtain ⟨k, rfl⟩ := hf
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    simp at h1
  have hsq : p ^ (k + k) = (p ^ k) ^ 2 := by rw [← pow_mul, mul_two]
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have h8 := Walter.sq_mod_eight_of_odd hodd
  have h3 : 3 ≤ p ^ k :=
    le_trans (by have := hp.two_le; omega) (Nat.le_self_pow hk0 p)
  have hne3 : p ^ k ≠ 3 := fun h => h9 (by rw [hsq, h]; norm_num)
  have h5 : 5 ≤ p ^ k := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have h25 : 25 ≤ (p ^ k) ^ 2 := by nlinarith
  refine sup_centralizer_eq_top_of_normal hp hp2 hF (by rw [hsq]; omega) (by rw [hsq]; omega) e
    htN ht2 hst hconj

end CFSG.ClassicalInvolution.Q3.TL4.E3C269G2
