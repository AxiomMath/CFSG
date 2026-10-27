module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Gen
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.NoncommCoprod
import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt10
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt9
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

theorem isQuasisimple_sl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple SL(2, F) :=
  CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4

theorem even_card_sl2 {F : Type} [Field F] [Finite F] : Even (Nat.card SL(2, F)) := by
  rw [CFSG.RankThree.SubgroupLists.card_sl2_field]
  rcases Nat.even_or_odd (Nat.card F) with h | h
  · exact h.mul_right _
  · obtain ⟨k, hk⟩ := h
    refine Even.mul_left ⟨2 * k ^ 2 + 2 * k, ?_⟩ _
    rw [hk]
    have : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    omega

theorem odd_normal_bot_of_sl2 {I : Type} [Group I] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (e : I ≃* SL(2, F))
    {M : Subgroup I} (hM : M.Normal) (hMo : Odd (Nat.card M)) : M = ⊥ := by
  have hq : CFSG.IsQuasisimple I :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 h4)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hM with htop | hle
  · exfalso
    have h1 : Nat.card I = Nat.card M := by rw [htop, Subgroup.card_top]
    have h2 : Nat.card I = Nat.card SL(2, F) := Nat.card_congr e.toEquiv
    have h3 : Even (Nat.card I) := by rw [h2]; exact even_card_sl2
    rw [h1] at h3
    exact (Nat.not_even_iff_odd.2 hMo) h3
  · have hc : Nat.card (center I) = 2 := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact CFSG.ClassicalInvolution.sl2_natCard_center hodd
    have hdvd : Nat.card M ∣ Nat.card (center I) := Subgroup.card_dvd_of_le hle
    rw [hc] at hdvd
    have h1 : Nat.card M = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hMo
        exact absurd hMo (by decide)
    exact Subgroup.eq_bot_of_card_eq M h1

theorem sq_eq_one_of_mem_odd_normal {A : Type} [Group A] {I I' : Subgroup A} {F : Type}
    [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (e : ↥I ≃* SL(2, F))
    (comm : ∀ a ∈ I, ∀ b ∈ I', a * b = b * a) {N : Subgroup A}
    (hN : ∀ g ∈ I ⊔ I', ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hNo : Odd (Nat.card N))
    {a b : A} (ha : a ∈ I) (hb : b ∈ I') (hab : a * b ∈ N) : a * a = 1 := by
  have hnorm : (N.subgroupOf I).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN _ (Subgroup.mem_sup_left g.2) _ hn
  have hodd' : Odd (Nat.card (N.subgroupOf I)) := by
    have h1 : Nat.card (N.subgroupOf I) ∣ Nat.card N := by
      rw [← Subgroup.inf_subgroupOf_right, Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ I ≤ I)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat hNo h1
  have hbot := odd_normal_bot_of_sl2 hodd h4 e hnorm hodd'
  have hcen : (⟨a, ha⟩ : ↥I) ∈ center ↥I := by
    rw [Subgroup.mem_center_iff]
    intro c
    have hc : (c : A) * (a * b) * (c : A)⁻¹ * (a * b)⁻¹ ∈ N :=
      N.mul_mem (hN _ (Subgroup.mem_sup_left c.2) _ hab) (N.inv_mem hab)
    have hbc : b * (c : A) = (c : A) * b := (comm c c.2 b hb).symm
    have hcomm : (c : A) * (a * b) * (c : A)⁻¹ * (a * b)⁻¹ =
        (c : A) * a * (c : A)⁻¹ * a⁻¹ := by
      have hbc' : b * (c : A)⁻¹ = (c : A)⁻¹ * b := by
        have := comm (c⁻¹ : ↥I) (c⁻¹).2 b hb
        simpa using this.symm
      calc (c : A) * (a * b) * (c : A)⁻¹ * (a * b)⁻¹
          = (c : A) * a * (b * (c : A)⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = (c : A) * a * ((c : A)⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hbc']
        _ = (c : A) * a * (c : A)⁻¹ * a⁻¹ := by group
    rw [hcomm] at hc
    have hmem : (c * ⟨a, ha⟩ * c⁻¹ * ⟨a, ha⟩⁻¹ : ↥I) ∈ N.subgroupOf I := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hc
    rw [hbot, Subgroup.mem_bot] at hmem
    have : (c : ↥I) * ⟨a, ha⟩ = ⟨a, ha⟩ * c := by
      have h2 := congrArg (· * (⟨a, ha⟩ : ↥I) * c) hmem
      simpa [mul_assoc] using h2
    exact this
  have hc2 : Nat.card (center ↥I) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.ClassicalInvolution.sl2_natCard_center hodd
  have hsq : (⟨⟨a, ha⟩, hcen⟩ : ↥(center ↥I)) ^ 2 = 1 := by
    rw [← hc2]
    exact pow_card_eq_one'
  have := congrArg (fun x : ↥(center ↥I) => ((x : ↥I) : A)) hsq
  simpa [pow_two] using this

theorem pPrimeCore_sl2_prod {A : Type} [Group A] {I₁ I₂ : Subgroup A} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] (hodd₁ : Odd (Nat.card F₁))
    (hodd₂ : Odd (Nat.card F₂)) (h4₁ : 4 ≤ Nat.card F₁) (h4₂ : 4 ≤ Nat.card F₂)
    (e₁ : ↥I₁ ≃* SL(2, F₁)) (e₂ : ↥I₂ ≃* SL(2, F₂))
    (comm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) : pPrimeCore 2 ↥(I₁ ⊔ I₂) = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro K hK hKc
  set N : Subgroup A := K.map (I₁ ⊔ I₂).subtype with hNdef
  have hNo : Odd (Nat.card N) := by
    have : Nat.card N = Nat.card K := Nat.card_congr
      (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv.symm
    rw [this]
    exact (Nat.coprime_two_left.1 hKc)
  have hN : ∀ g ∈ I₁ ⊔ I₂, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hn
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, hK.conj_mem k hk _, by simp⟩
  have hcomm' : ∀ b ∈ I₂, ∀ a ∈ I₁, b * a = a * b := fun b hb a ha => (comm a ha b hb).symm
  have hN' : ∀ g ∈ I₂ ⊔ I₁, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    rw [sup_comm]; exact hN
  rw [eq_bot_iff]
  intro k hk
  have hkN : (k : A) ∈ N := Subgroup.mem_map.2 ⟨k, hk, rfl⟩
  obtain ⟨a, ha, b, hb, hkab⟩ := exists_mul_of_mem_sup' comm k.2
  rw [hkab] at hkN
  have h1 := sq_eq_one_of_mem_odd_normal hodd₁ h4₁ e₁ comm hN hNo ha hb hkN
  have hkN' : b * a ∈ N := by rw [← comm a ha b hb]; exact hkN
  have h2 := sq_eq_one_of_mem_odd_normal hodd₂ h4₂ e₂ hcomm' hN' hNo hb ha hkN'
  have hk2 : (k : A) * k = 1 := by
    rw [hkab]
    have hba : b * a = a * b := (comm a ha b hb).symm
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [h1, h2, mul_one]
  have hk2' : k * k = 1 := Subtype.ext (by simpa using hk2)
  have hord : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hk2')
  have hord' : orderOf k ∣ Nat.card K := by
    rw [← Subgroup.orderOf_mk k hk]
    exact orderOf_dvd_natCard _
  have h3 : orderOf k = 1 := by
    have hcop : Nat.Coprime 2 (Nat.card K) := hKc
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.coprime_dvd_left hord hcop) (dvd_refl _) hord'
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)

@[expose] def uniSL (F : Type) [Field F] (a : F) : SL(2, F) :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_uniSL {F : Type} [Field F] (a : F) :
    (uniSL F a : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl

@[expose] noncomputable def uniHom (F : Type) [Field F] : Multiplicative F →* SL(2, F) where
  toFun a := uniSL F (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uniSL]
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_uniSL,
      Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uniHom_apply {F : Type} [Field F] (a : Multiplicative F) :
    uniHom F a = uniSL F (Multiplicative.toAdd a) := rfl

theorem uniHom_injective (F : Type) [Field F] : Function.Injective (uniHom F) := by
  intro a b h
  have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [uniHom_apply, coe_uniSL] at this
  simpa using this

theorem pow_char_eq_one {F : Type} [Field F] {p : ℕ} [CharP F p] (a : Multiplicative F) :
    a ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  simp [toAdd_pow, nsmul_eq_mul, CharP.cast_eq_zero]

theorem exists_unip_prod {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (S : Shape Y F₁ F₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hc₁ : ∃ a, Nat.card F₁ = p ^ a) (hc₂ : ∃ b, Nat.card F₂ = p ^ b) :
    ∃ P : Subgroup Y, P ≤ S.I₁ ⊔ S.I₂ ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      (∀ x ∈ P, x ^ p = 1) ∧ Nat.card P = Nat.card F₁ * Nat.card F₂ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hchar : ∀ (F : Type) [Field F] [Finite F], (∃ a, Nat.card F = p ^ a) → CharP F p := by
    intro F _ _ ⟨a, ha⟩
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, ha])
  have : CharP F₁ p := hchar F₁ hc₁
  have : CharP F₂ p := hchar F₂ hc₂
  let f₁ : Multiplicative F₁ →* Y :=
    S.I₁.subtype.comp (S.e₁.symm.toMonoidHom.comp (uniHom F₁))
  let f₂ : Multiplicative F₂ →* Y :=
    S.I₂.subtype.comp (S.e₂.symm.toMonoidHom.comp (uniHom F₂))
  have hf₁ : Function.Injective f₁ :=
    (Subgroup.subtype_injective _).comp (S.e₁.symm.injective.comp (uniHom_injective F₁))
  have hf₂ : Function.Injective f₂ :=
    (Subgroup.subtype_injective _).comp (S.e₂.symm.injective.comp (uniHom_injective F₂))
  have hf₁p : ∀ a, f₁ a ^ p = 1 := by
    intro a
    simp only [f₁, MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, pow_char_eq_one, map_one, map_one]
    simp
  have hf₂p : ∀ b, f₂ b ^ p = 1 := by
    intro b
    simp only [f₂, MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, pow_char_eq_one, map_one, map_one]
    simp
  have hcomm : ∀ a b, Commute (f₁ a) (f₂ b) := by
    intro a b
    exact S.comm _ (S.e₁.symm (uniHom F₁ a)).2 _ (S.e₂.symm (uniHom F₂ b)).2
  let ψ : Multiplicative F₁ × Multiplicative F₂ →* Y := f₁.noncommCoprod f₂ hcomm
  have hψ : ∀ x, ψ x = f₁ x.1 * f₂ x.2 := fun x => MonoidHom.noncommCoprod_apply _ _ _ _
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hψ] at hx
    have h1 : f₁ x.1 = (f₂ x.2)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hmem : f₁ x.1 ∈ S.I₁ ⊓ S.I₂ :=
      ⟨(S.e₁.symm (uniHom F₁ x.1)).2, by
        rw [h1]; exact S.I₂.inv_mem (S.e₂.symm (uniHom F₂ x.2)).2⟩
    rw [S.inter] at hmem
    have hz2 : orderOf S.z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact S.z_sq)
    have hd1 : orderOf (f₁ x.1) ∣ 2 := (orderOf_dvd_of_mem_zpowers hmem).trans hz2
    have hd2 : orderOf (f₁ x.1) ∣ p := orderOf_dvd_of_pow_eq_one (hf₁p _)
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have hord : orderOf (f₁ x.1) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    have ha : f₁ x.1 = 1 := orderOf_eq_one_iff.1 hord
    have ha' : x.1 = 1 := hf₁ (by rw [ha, map_one])
    have hb : f₂ x.2 = 1 := by rw [ha, one_mul] at hx; exact hx
    have hb' : x.2 = 1 := hf₂ (by rw [hb, map_one])
    exact Prod.ext ha' hb'
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [hψ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (S.e₁.symm (uniHom F₁ x.1)).2)
      (Subgroup.mem_sup_right (S.e₂.symm (uniHom F₂ x.2)).2)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm x y]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 :=
      Prod.ext (by simpa [Prod.pow_fst] using pow_char_eq_one x.1)
        (by simpa [Prod.pow_snd] using pow_char_eq_one x.2)
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm, Nat.card_prod]
    rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
