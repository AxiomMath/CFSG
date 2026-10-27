module

public import CFSG.GH74.GLS.IVK.Lifted.Out
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

section PGLQuot

theorem mem_center_of_conj_eq_one {Q : Type} [Group Q] {c : Q} (h : MulAut.conj c = 1) :
    c ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun ρ : MulAut Q => ρ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc g * c = (c * g * c⁻¹) * c := by rw [this]
    _ = c * g := by group

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem eq_one_or_of_mem_zpowers_two {Q : Type} [Group Q] {c y : Q} (h2 : orderOf c = 2)
    (hy : y ∈ Subgroup.zpowers c) : y = 1 ∨ y = c := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h3 : c ^ (k % (orderOf c : ℤ)) = c ^ k := zpow_mod_orderOf c k
  rw [h2] at h3
  have hk2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk2 with h4 | h4
  · left
    rw [← hk, ← h3, h4, zpow_zero]
  · right
    rw [← hk, ← h3, h4, zpow_one]

theorem mem_pPrimeCoreOf_iff_hatMk {G : Type} [Group G] [Finite G] (K : Subgroup G) (o : G) :
    o ∈ pPrimeCoreOf 2 K ↔ ∃ ho : o ∈ K, hatMk K ⟨o, ho⟩ = 1 := by
  unfold pPrimeCoreOf
  constructor
  · rintro ⟨o', ho', rfl⟩
    exact ⟨o'.2, (QuotientGroup.eq_one_iff _).2 ho'⟩
  · rintro ⟨ho, h1⟩
    exact ⟨⟨o, ho⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem hatMk_of_mem_sup_zpowers {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (hzK : z ∈ K) (hz2 : orderOf z = 2) {x : G} (hx : x ∈ pPrimeCoreOf 2 K ⊔ zpowers z) :
    ∃ hxK : x ∈ K, hatMk K ⟨x, hxK⟩ = 1 ∨ hatMk K ⟨x, hxK⟩ = hatMk K ⟨z, hzK⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzS : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  have hzKle : zpowers z ≤ K := zpowers_le.2 hzK
  have hc₀2 : orderOf (hatMk K ⟨z, hzK⟩) = 2 := by
    have := orderOf_hatMk hzKle hzS (mem_zpowers z)
    rw [hz2] at this
    exact this
  let V : Subgroup ↥K := (zpowers (hatMk K ⟨z, hzK⟩)).comap (hatMk K)
  have hOU : pPrimeCoreOf 2 K ≤ V.map K.subtype := by
    intro o ho
    obtain ⟨hoK, h0⟩ := (mem_pPrimeCoreOf_iff_hatMk K o).1 ho
    exact Subgroup.mem_map.2 ⟨⟨o, hoK⟩, by
      show hatMk K ⟨o, hoK⟩ ∈ zpowers (hatMk K ⟨z, hzK⟩)
      rw [h0]
      exact one_mem _, rfl⟩
  have hzU : zpowers z ≤ V.map K.subtype := by
    rw [zpowers_le]
    exact Subgroup.mem_map.2 ⟨⟨z, hzK⟩, mem_zpowers _, rfl⟩
  obtain ⟨x', hx', hx'x⟩ := Subgroup.mem_map.1 (sup_le hOU hzU hx)
  subst hx'x
  exact ⟨x'.2, eq_one_or_of_mem_zpowers_two hc₀2 hx'⟩

theorem eq_one_or_of_center_card_two {Q : Type} [Group Q] [Finite Q] {c₀ : Q}
    (hc₀ : c₀ ∈ Subgroup.center Q) (h2 : orderOf c₀ = 2) (hcard : Nat.card (Subgroup.center Q) = 2)
    {y : Q} (hy : y ∈ Subgroup.center Q) : y = 1 ∨ y = c₀ := by
  have hle : Subgroup.zpowers c₀ ≤ Subgroup.center Q := Subgroup.zpowers_le.2 hc₀
  have hcz : Nat.card ↥(Subgroup.zpowers c₀) = 2 := by rw [Nat.card_zpowers, h2]
  have heq : Subgroup.zpowers c₀ = Subgroup.center Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hcard])
  rw [← heq] at hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h3 : c₀ ^ (k % (orderOf c₀ : ℤ)) = c₀ ^ k := zpow_mod_orderOf c₀ k
  rw [h2] at h3
  have hk2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk2 with h4 | h4
  · left
    rw [← hk, ← h3, h4, zpow_zero]
  · right
    rw [← hk, ← h3, h4, zpow_one]

theorem exists_pgl_hom {z w : G} {K : Subgroup G} (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Hat K ≃* SpecialLinearGroup (Fin 2) F) (hzK : z ∈ K)
    (hKz : K ≤ centralizer ({z} : Set G)) (hz2 : orderOf z = 2)
    (hcen : Nat.card (Subgroup.center (Hat K)) = 2) (hwN : w ∈ normalizer (K : Set G)) (hw2 : w * w = 1)
    (hwin : ¬ phi K w hwN ∈ innOf (Hat K))
    (hσ : (gammaOf hodd h3 (MulAut.congr e (phi K w hwN))).right = 1) :
    ∃ θ : ↥(K ⊔ zpowers w) →* PGL2 F, Function.Surjective θ ∧
      θ.ker = (pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf (K ⊔ zpowers w) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := K ⊔ zpowers w with hXdef
  have hXN : X ≤ normalizer (K : Set G) := sup_le le_normalizer (zpowers_le.2 hwN)
  let Γ : ↥X →* PGammaL2 F := (gammaOf hodd h3).comp ((MulAut.congr e).toMonoidHom.comp
    ((phiHom K).comp (Subgroup.inclusion hXN)))
  have hΓ : ∀ x : ↥X, Γ x = gammaOf hodd h3 (MulAut.congr e (phi K (x : G) (hXN x.2))) :=
    fun x => rfl
  let ρ : ↥X →* (F ≃+* F) := SemidirectProduct.rightHom.comp Γ
  have hKρ : ∀ k : ↥K, ∃ hk : (k : G) ∈ X, ρ ⟨k, hk⟩ = 1 := by
    intro k
    have hkX : (k : G) ∈ X := mem_sup_left k.2
    refine ⟨hkX, ?_⟩
    show (Γ ⟨k, hkX⟩).right = 1
    rw [hΓ]
    have h1 : phi K (k : G) (hXN hkX) = MulAut.conj (hatMk K ⟨(k : G), k.2⟩) := phi_of_mem K k.2
    show (gammaOf hodd h3 (MulAut.congr e (phi K (k : G) (hXN hkX)))).right = 1
    rw [h1, congr_conj, gammaOf_conj_right]
  have hwρ : ∃ hw : w ∈ X, ρ ⟨w, hw⟩ = 1 := ⟨mem_sup_right (mem_zpowers w), hσ⟩
  have hρ : ∀ x : ↥X, ρ x = 1 := by
    let U : Subgroup G := ρ.ker.map X.subtype
    have hKU : K ≤ U := fun k hk => by
      obtain ⟨hkX, h1⟩ := hKρ ⟨k, hk⟩
      exact Subgroup.mem_map.2 ⟨⟨k, hkX⟩, h1, rfl⟩
    have hwU : zpowers w ≤ U := by
      rw [zpowers_le]
      obtain ⟨hwX, h1⟩ := hwρ
      exact Subgroup.mem_map.2 ⟨⟨w, hwX⟩, h1, rfl⟩
    intro x
    have hxU : (x : G) ∈ U := sup_le hKU hwU x.2
    obtain ⟨x', hx', hx'x⟩ := Subgroup.mem_map.1 hxU
    have : x' = x := Subtype.ext hx'x
    rw [← this]
    exact hx'
  have hright : ∀ x : ↥X, (Γ x).right = 1 := hρ
  let θ : ↥X →* PGL2 F :=
    { toFun := fun x => (Γ x).left
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, SemidirectProduct.mul_left, hright x]
        simp }
  have hθΓ : ∀ x : ↥X, θ x = 1 ↔ Γ x = 1 := by
    intro x
    constructor
    · intro h
      apply SemidirectProduct.ext
      · exact h
      · rw [hright x]
        rfl
    · intro h
      show (Γ x).left = 1
      rw [h]
      rfl
  have hθphi : ∀ x : ↥X, θ x = 1 ↔ phi K (x : G) (hXN x.2) = 1 := by
    intro x
    rw [hθΓ, hΓ]
    constructor
    · intro h
      have h1 := gammaOf_injective hodd h3 (h.trans (map_one _).symm)
      exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
    · intro h
      rw [h, map_one (MulAut.congr e), map_one]
  have hzS : IsPGroup 2 ↥(zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  have hzKle : zpowers z ≤ K := zpowers_le.2 hzK
  set c₀ : Hat K := hatMk K ⟨z, hzK⟩ with hc₀
  have hc₀2 : orderOf c₀ = 2 := by
    have := orderOf_hatMk hzKle hzS (mem_zpowers z)
    rw [hz2] at this
    exact this
  have hc₀c : c₀ ∈ Subgroup.center (Hat K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hatMk_surjective K y
    show hatMk K k * hatMk K ⟨z, hzK⟩ = hatMk K ⟨z, hzK⟩ * hatMk K k
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (k : G) * z = z * (k : G)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hKz k.2)
  have hO : ∀ o : G, o ∈ pPrimeCoreOf 2 K ↔ ∃ ho : o ∈ K, hatMk K ⟨o, ho⟩ = 1 := by
    intro o
    unfold pPrimeCoreOf
    constructor
    · rintro ⟨o', ho', rfl⟩
      exact ⟨o'.2, (QuotientGroup.eq_one_iff _).2 ho'⟩
    · rintro ⟨ho, h1⟩
      exact ⟨⟨o, ho⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hker : θ.ker = (pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hθphi]
    constructor
    · intro h1
      have hx2 : (x : G) ∈ K ∨ (x : G) * w⁻¹ ∈ K :=
        mem_or_mul_inv_mem hwN (by rw [hw2]; exact one_mem K) x.2
      rcases hx2 with hxK | hxw
      · rw [phi_congr K rfl (hXN x.2) (le_normalizer hxK), phi_of_mem K hxK] at h1
        have hcn := mem_center_of_conj_eq_one h1
        rcases eq_one_or_of_center_card_two hc₀c hc₀2 hcen hcn with h0 | h0
        · exact mem_sup_left ((hO _).2 ⟨hxK, h0⟩)
        · have h5 : hatMk K ⟨(x : G) * z⁻¹, mul_mem hxK (inv_mem hzK)⟩ = 1 := by
            have : hatMk K ⟨(x : G) * z⁻¹, mul_mem hxK (inv_mem hzK)⟩ =
                hatMk K ⟨(x : G), hxK⟩ * (hatMk K ⟨z, hzK⟩)⁻¹ := by
              rw [← map_inv, ← map_mul]
              rfl
            rw [this, h0, hc₀, mul_inv_cancel]
          have h6 : (x : G) * z⁻¹ ∈ pPrimeCoreOf 2 K ⊔ zpowers z :=
            mem_sup_left ((hO _).2 ⟨mul_mem hxK (inv_mem hzK), h5⟩)
          have h7 := mul_mem h6 (mem_sup_right (mem_zpowers z) : z ∈ pPrimeCoreOf 2 K ⊔ zpowers z)
          simpa using h7
      · exfalso
        apply hwin
        have hxwN : (x : G) * w⁻¹ ∈ normalizer (K : Set G) := le_normalizer hxw
        have h8 : phi K ((x : G) * w⁻¹) hxwN = phi K (x : G) (hXN x.2) * phi K w⁻¹ (inv_mem hwN) :=
          phi_mul K (hXN x.2) (inv_mem hwN)
        rw [h1, one_mul, phi_inv_aux K hwN (inv_mem hwN)] at h8
        have h9 : phi K ((x : G) * w⁻¹) hxwN = MulAut.conj (hatMk K ⟨(x : G) * w⁻¹, hxw⟩) :=
          phi_of_mem K hxw
        rw [h9] at h8
        have h10 : phi K w hwN = MulAut.conj (hatMk K ⟨(x : G) * w⁻¹, hxw⟩)⁻¹ := by
          rw [map_inv, h8, inv_inv]
        rw [h10, ← map_inv]
        exact ⟨_, rfl⟩
    · intro hx
      have hsub : pPrimeCoreOf 2 K ⊔ zpowers z ≤ cSec K := by
        refine sup_le (fun o ho => ?_) ?_
        · obtain ⟨hoK, h0⟩ := (hO o).1 ho
          refine (phi_eq_one_iff K (le_normalizer hoK)).1 ?_
          rw [phi_of_mem K hoK, h0, map_one]
        · rw [zpowers_le]
          refine (phi_eq_one_iff K (le_normalizer hzK)).1 ?_
          rw [phi_of_mem K hzK]
          exact conj_eq_one_of_mem_center hc₀c
      exact (phi_eq_one_iff K (hXN x.2)).2 (hsub hx)
  have hOPP := isOddPrimePower_card_of_odd hodd
  set R₀ := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hR₀
  have hidx : R₀.index = 2 := pgl2_psl2Range_index_eq_two F hOPP
  have hR₀le : ∀ r ∈ R₀, ∃ x : ↥X, θ x = r := by
    rintro r ⟨s', rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin 2) F)) s'
    obtain ⟨k, hk⟩ := hatMk_surjective K (e.symm s)
    have hkX : (k : G) ∈ X := mem_sup_left k.2
    refine ⟨⟨k, hkX⟩, ?_⟩
    show (Γ ⟨k, hkX⟩).left = _
    rw [hΓ]
    have h1 : phi K (k : G) (hXN hkX) = MulAut.conj (hatMk K k) := phi_of_mem K k.2
    show (gammaOf hodd h3 (MulAut.congr e (phi K (k : G) (hXN hkX)))).left = _
    rw [h1, congr_conj, hk, MulEquiv.apply_symm_apply, gammaOf_conj]
    rfl
  have hwX : w ∈ X := mem_sup_right (mem_zpowers w)
  have hwθ : θ ⟨w, hwX⟩ ∉ R₀ := by
    intro hmem
    apply hwin
    have hinn : MulAut.congr e (phi K w hwN) ∈
        (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
      rw [mem_inn_iff hodd h3]
      exact ⟨hσ, hmem⟩
    obtain ⟨s, hs⟩ := hinn
    refine ⟨e.symm s, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply, hs]
  have hsurj : Function.Surjective θ := by
    intro u
    by_cases hu : u ∈ R₀
    · obtain ⟨x, hx⟩ := hR₀le u hu
      exact ⟨x, hx⟩
    · have hg : (θ ⟨w, hwX⟩)⁻¹ ∉ R₀ := fun h => hwθ (R₀.inv_mem_iff.1 h)
      have hmem : u * (θ ⟨w, hwX⟩)⁻¹ ∈ R₀ := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact ⟨fun h => absurd h hu, fun h => absurd h hg⟩
      obtain ⟨x₀, hx₀⟩ := hR₀le _ hmem
      refine ⟨x₀ * ⟨w, hwX⟩, ?_⟩
      rw [map_mul, hx₀, inv_mul_cancel_right]
  exact ⟨θ, hsurj, hker⟩

theorem exists_pglQuot {z w : G} {K : Subgroup G} (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Hat K ≃* SpecialLinearGroup (Fin 2) F) (hzK : z ∈ K)
    (hKz : K ≤ centralizer ({z} : Set G)) (hz2 : orderOf z = 2)
    (hcen : Nat.card (Subgroup.center (Hat K)) = 2) (hwN : w ∈ normalizer (K : Set G)) (hw2 : w * w = 1)
    (hwin : ¬ phi K w hwN ∈ innOf (Hat K))
    (hσ : (gammaOf hodd h3 (MulAut.congr e (phi K w hwN))).right = 1) :
    PGLQuot z w K F := by
  obtain ⟨θ, hsurj, hker⟩ := exists_pgl_hom hodd h3 e hzK hKz hz2 hcen hwN hw2 hwin hσ
  have hN : ((pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf (K ⊔ zpowers w)).Normal := by
    rw [← hker]
    exact θ.normal_ker
  refine ⟨hN, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)

end PGLQuot

end CFSG.GH74.GLS.IVK.Lifted
