module

public import CFSG.GH74.GLS.SP.Local.SPLPumpTabDefs
public import CFSG.GH74.GLS.IVK.A7.Core
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS Equiv Equiv.Perm
open scoped Pointwise

private theorem tabA7_exists_involution_conj {J : Type} [Group J] (e : J ≃* alternatingGroup (Fin 7))
    (σ : MulAut J) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ∃ ρ : Perm (Fin 7), ρ ^ 2 = 1 ∧ ρ ≠ 1 ∧
      ∀ x : J, ((e (σ x) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        ρ * (e x : Perm (Fin 7)) * ρ⁻¹ := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  obtain ⟨ρ, hρ⟩ := hbij.2 (MulAut.congr e σ)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · apply hbij.1
    rw [map_pow, hρ, map_one, ← map_pow, hσ2, map_one]
  · rintro rfl
    apply hσ1
    rw [map_one] at hρ
    exact (MulAut.congr e).injective (hρ.symm.trans (map_one _).symm)
  · intro x
    have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 7)) =>
      (φ (e x) : Perm (Fin 7))) hρ
    simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h
    exact h.symm

private theorem tabA7_fixed_iff {J : Type} [Group J] (e : J ≃* alternatingGroup (Fin 7))
    (σ : MulAut J) (ρ : Perm (Fin 7))
    (hρ : ∀ x : J, ((e (σ x) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ρ * (e x : Perm (Fin 7)) * ρ⁻¹) (x : J) :
    x ∈ fixedSubgroup J σ ↔ (e x : Perm (Fin 7)) ∈ centralizer ({ρ} : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  show σ x = x ↔ _
  constructor
  · intro h
    have h1 := hρ x
    rw [h] at h1
    calc (e x : Perm (Fin 7)) * ρ = (ρ * (e x : Perm (Fin 7)) * ρ⁻¹) * ρ := by rw [← h1]
      _ = ρ * (e x : Perm (Fin 7)) := by group
  · intro h
    apply e.injective
    apply Subtype.ext
    rw [hρ x]
    calc ρ * (e x : Perm (Fin 7)) * ρ⁻¹ = ((e x : Perm (Fin 7)) * ρ) * ρ⁻¹ := by rw [h]
      _ = (e x : Perm (Fin 7)) := by group

private theorem tabA7_map_fixed {J : Type} [Group J] (e : J ≃* alternatingGroup (Fin 7))
    (σ : MulAut J) (ρ : Perm (Fin 7))
    (hρ : ∀ x : J, ((e (σ x) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ρ * (e x : Perm (Fin 7)) * ρ⁻¹) :
    (fixedSubgroup J σ).map ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom) =
      centralizer ({ρ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(tabA7_fixed_iff e σ ρ hρ x).mp hx, (e x).2⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨e.symm ⟨y, hy2⟩, (tabA7_fixed_iff e σ ρ hρ _).mpr ?_, by simp⟩
    simpa using hy1

private theorem tabA7_exists_equiv {J : Type} [Group J] (e : J ≃* alternatingGroup (Fin 7))
    (σ : MulAut J) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ∃ ρ : Perm (Fin 7), ρ ^ 2 = 1 ∧ ρ ≠ 1 ∧
      Nonempty (↥(fixedSubgroup J σ) ≃*
        ↥(centralizer ({ρ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))) := by
  obtain ⟨ρ, hρ2, hρ1, hρ⟩ := tabA7_exists_involution_conj e σ hσ2 hσ1
  refine ⟨ρ, hρ2, hρ1, ⟨?_⟩⟩
  have hinj : Function.Injective ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom) :=
    Subtype.val_injective.comp e.injective
  exact (Subgroup.equivMapOfInjective _ _ hinj).trans
    (MulEquiv.subgroupCongr (tabA7_map_fixed e σ ρ hρ))

theorem tabA7Card :
    ∀ (J : Type) [Group J] [Finite J], Nonempty (J ≃* alternatingGroup (Fin 7)) →
      ∀ σ : MulAut J, σ ^ 2 = 1 → σ ≠ 1 → 4 ≤ Nat.card ↥(fixedSubgroup J σ) := by
  intro J _ _ ⟨e⟩ σ hσ2 hσ1
  obtain ⟨ρ, hρ2, hρ1, ⟨eC⟩⟩ := tabA7_exists_equiv e σ hσ2 hσ1
  rw [Nat.card_congr eC.toEquiv]
  rcases IVK.A7.involution_cycleType ρ hρ2 hρ1 with hc | hc | hc
  · rw [IVK.A7.card_centralizer_A7_two hc hρ2 hρ1]
    norm_num
  · rw [IVK.A7.card_centralizer_A7_two_two hc hρ2 hρ1]
    norm_num
  · rw [IVK.A7.card_centralizer_A7_two_two_two hc hρ2 hρ1]
    norm_num

private theorem tabA7_card_isL2 {X : Type} [Group X] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hX : IVK.IsL2 X (fun r => r = q)) : Nat.card X = q * (q ^ 2 - 1) / 2 := by
  obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := hX
  have hF₀' : Nat.card F₀ = q := hF₀
  have hF : IVK.L2Field F₀ := ⟨by rw [hF₀']; exact hq, by omega⟩
  rw [Nat.card_congr (e.trans (IVK.L2.equivPSL F₀)).toEquiv,
    CFSG.GorensteinWalter.psl2_card_formula F₀ (IVK.isOddPrimePower_of_L2Field hF), hF₀']

private theorem tabA7_L2_bounds {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q) :
    (q = 5 ∧ q * (q ^ 2 - 1) / 2 = 60) ∨ 168 ≤ q * (q ^ 2 - 1) / 2 := by
  rcases Nat.lt_or_ge q 7 with h | h
  · left
    have h6 : q ≠ 6 := by
      rintro rfl
      exact absurd hq (by decide)
    have h5' : q = 5 := by omega
    subst h5'
    norm_num
  · right
    have h1 : 7 * (7 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    norm_num at h1
    omega

private theorem tabA7_outer_sigma5 {J : Type} [Group J] (σ : MulAut J) (C I : Subgroup J)
    (hC : ∀ x, x ∈ C ↔ σ x = x) (hfix : ∀ x ∈ I, σ x = x) (ψ : ↥C ≃* Perm (Fin 5))
    (hI : Nat.card ↥I = 60) : HasOuterTwoElement C I := by
  unfold HasOuterTwoElement
  have hIC : I ≤ C := fun x hx => (hC x).mpr (hfix x hx)
  have hCcard : Nat.card ↥C = 120 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hNcard : Nat.card ↥(I.subgroupOf C) = 60 := by
    rw [← hI]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIC).toEquiv
  have hidx : (I.subgroupOf C).index = 2 := by
    have h := Subgroup.card_mul_index (I.subgroupOf C)
    rw [hNcard, hCcard] at h
    omega
  have hsq : ∀ g : ↥C, g * g ∈ I.subgroupOf C := Subgroup.mul_self_mem_of_index_two hidx
  have hnormN : (I.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx
  have h3 : ∀ g : ↥C, g ^ 3 = 1 → g ∈ I.subgroupOf C := by
    intro g hg
    have hgg : g * g * (g * g) = g := by
      calc g * g * (g * g) = g ^ 3 * g := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = g := by rw [hg, one_mul]
    have hmem := Subgroup.mul_mem _ (hsq g) (hsq g)
    rwa [hgg] at hmem
  have hA5 : alternatingGroup (Fin 5) ≤ (I.subgroupOf C).map ψ.toMonoidHom := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro t ht
    have ht' : t.IsThreeCycle := ht
    have ht3 : t ^ 3 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht'.orderOf] at this
    refine ⟨ψ.symm t, h3 _ ?_, by simp⟩
    apply ψ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact ht3
  have hA5card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hA5eq : alternatingGroup (Fin 5) = (I.subgroupOf C).map ψ.toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hA5 ?_
    rw [Subgroup.card_map_of_injective ψ.injective, hNcard, hA5card]
  have ht2 : (swap (0 : Fin 5) 1) ^ 2 = 1 := by
    rw [pow_two]
    exact swap_mul_self _ _
  have htsign : sign (swap (0 : Fin 5) 1) = -1 := sign_swap (by decide)
  have hcnotN : ψ.symm (swap (0 : Fin 5) 1) ∉ I.subgroupOf C := by
    intro hmem
    have h1 : swap (0 : Fin 5) 1 ∈ (I.subgroupOf C).map ψ.toMonoidHom :=
      ⟨ψ.symm (swap (0 : Fin 5) 1), hmem, by simp⟩
    rw [← hA5eq, Equiv.Perm.mem_alternatingGroup, htsign] at h1
    exact absurd h1 (by decide)
  have hD : ∀ d : J, σ d = d → d ∈ centralizer (I : Set J) → d = 1 := by
    intro d hd hdc
    let dC : ↥C := ⟨d, (hC d).mpr hd⟩
    have hcomm : ∀ x ∈ alternatingGroup (Fin 5), ψ dC * x = x * ψ dC := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := hA5 hx
      have hnd : (n : J) * d = d * (n : J) := (Subgroup.mem_centralizer_iff.mp hdc) (n : J) hn
      change ψ dC * ψ n = ψ n * ψ dC
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext hnd.symm)
    have h1 : ψ dC = 1 := by
      apply (CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5 (by norm_num))
      rw [map_one]
      refine MulEquiv.ext fun a => Subtype.ext ?_
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have h := hcomm a a.2
      calc ψ dC * (a : Perm (Fin 5)) * (ψ dC)⁻¹ = (a : Perm (Fin 5)) * ψ dC * (ψ dC)⁻¹ := by
            rw [h]
        _ = a := by group
    have h2 : dC = 1 := ψ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hnorm : I ≤ normalizer ((centralizer (I : Set J) : Subgroup J) : Set J) :=
    (Subgroup.le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨(ψ.symm (swap (0 : Fin 5) 1) : J), (ψ.symm (swap (0 : Fin 5) 1)).2, ⟨1, ?_⟩, ?_, ?_⟩
  · have h : (ψ.symm (swap (0 : Fin 5) 1)) ^ (2 ^ 1) = 1 := by
      apply ψ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, map_one, pow_one]
      exact ht2
    exact congrArg Subtype.val h
  · intro x hx
    have hxC : x ∈ C := hIC hx
    have hmem : (⟨x, hxC⟩ : ↥C) ∈ I.subgroupOf C := hx
    exact hnormN.conj_mem _ hmem (ψ.symm (swap (0 : Fin 5) 1))
  · intro hcmem
    have hcmem' : (ψ.symm (swap (0 : Fin 5) 1) : J) ∈ (I : Set J) * (centralizer (I : Set J) : Set J) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right I _ hnorm]
      exact hcmem
    obtain ⟨i, hi, d, hd, hid⟩ := Set.mem_mul.mp hcmem'
    have hσc : σ (ψ.symm (swap (0 : Fin 5) 1) : J) = (ψ.symm (swap (0 : Fin 5) 1) : J) :=
      (hC _).mp (ψ.symm (swap (0 : Fin 5) 1)).2
    have hσd : σ d = d := by
      have h1 : σ (i * d) = i * d := by
        rw [hid]
        exact hσc
      rw [map_mul, hfix i hi] at h1
      exact mul_left_cancel h1
    have hd1 : d = 1 := hD d hσd hd
    rw [hd1, mul_one] at hid
    have hcI : (ψ.symm (swap (0 : Fin 5) 1) : J) ∈ I := by
      rw [← hid]
      exact hi
    exact hcnotN hcI

theorem tabA7Outer :
    ∀ (J : Type) [Group J] [Finite J], Nonempty (J ≃* alternatingGroup (Fin 7)) →
      ∀ σ : MulAut J, σ ^ 2 = 1 → σ ≠ 1 →
        ∀ q : ℕ, Odd q → 5 ≤ q → ∀ I : Subgroup J, (∀ x ∈ I, σ x = x) →
          IVK.IsL2 ↥I (fun r => r = q) → (I.subgroupOf (fixedSubgroup J σ)).IsSubnormal →
            HasOuterTwoElement (fixedSubgroup J σ) I := by
  intro J _ _ ⟨e⟩ σ hσ2 hσ1 q hq h5 I hfix hI _
  obtain ⟨ρ, hρ2, hρ1, ⟨eC⟩⟩ := tabA7_exists_equiv e σ hσ2 hσ1
  have hIC : I ≤ fixedSubgroup J σ := fun x hx => hfix x hx
  have hIcard := tabA7_card_isL2 hq h5 hI
  have hdvd := Subgroup.card_dvd_of_le hIC
  rw [Nat.card_congr eC.toEquiv, hIcard] at hdvd
  have hbounds := tabA7_L2_bounds hq h5
  rcases IVK.A7.involution_cycleType ρ hρ2 hρ1 with hc | hc | hc
  · rw [IVK.A7.card_centralizer_A7_two hc hρ2 hρ1] at hdvd
    have h60 : Nat.card ↥I = 60 := by
      rcases hbounds with ⟨-, h⟩ | h
      · rw [hIcard, h]
      · have := Nat.le_of_dvd (by norm_num) hdvd
        omega
    obtain ⟨e5⟩ := IVK.A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr hc)
    exact tabA7_outer_sigma5 σ (fixedSubgroup J σ) I (fun x => Iff.rfl) hfix (eC.trans e5) h60
  · exfalso
    rw [IVK.A7.card_centralizer_A7_two_two hc hρ2 hρ1] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · exfalso
    rw [IVK.A7.card_centralizer_A7_two_two_two hc hρ2 hρ1] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

end CFSG.GH74.GLS.SP.Local
