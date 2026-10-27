module

public import CFSG.GF2Type.Smith1979.IdxFourIdentAtilde
public import CFSG.GF2Type.Smith1979.IdxFourIdentFrameData
public import CFSG.GF2Type.Smith1979.IdxFourIdentPerm
public import CFSG.GF2Type.Smith1979.IdxFourIdentTwist
public import CFSG.GF2Type.Smith1979.IdxFourIdentFLType
public import CFSG.GF2Type.Smith1979.IdxFourIdentAdj43
public import CFSG.GF2Type.Smith1979.IdxFourIdentConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.Case25.U43Weights
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six

namespace Ctx

variable (C : Ctx)

noncomputable instance instCommGroupAtilde : CommGroup C.AtildeE :=
  { (inferInstance : Group C.AtildeE) with
    mul_comm := fun a b => Subtype.ext (C.AtildeE_comm a.2 b.2) }

@[expose] noncomputable def rhoA : C.AtildeE →* G12 := C.E.subtype.comp C.AtildeE.subtype

@[expose] noncomputable def thetaA : C.AtildeE := ⟨⟨theta0e, C.theta0e_mem_E⟩, C.theta0_mem_AtildeE⟩

theorem mem_zpowers_thetaA_iff (a : C.AtildeE) :
    a ∈ Subgroup.zpowers C.thetaA ↔ ((a : C.E) : G12) ∈ Subgroup.zpowers theta0e := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : (((C.thetaA ^ n : C.AtildeE) : C.E) : G12) = theta0e ^ n := by
      simp [Ctx.thetaA]
    rw [h1]
    exact hn

theorem E_le_gammaU : C.E ≤ gammaU := C.hEX.trans C.hXg

theorem rhoA_injective : Function.Injective C.rhoA := fun a b h =>
  Subtype.ext (Subtype.ext h)

theorem rhoA_mem_gammaU (a : C.AtildeE) : C.rhoA a ∈ gammaU := C.E_le_gammaU a.1.2

theorem levLift_comm (k : Gen) :
    ((C.levLift k : C.E) : G12) * theta0e = theta0e * ((C.levLift k : C.E) : G12) :=
  C.theta0e_comm _

theorem levLift_pow_three_mem_zpowers (k : Gen) :
    ((C.levLift k : C.E) : G12) ^ 3 ∈ Subgroup.zpowers theta0e := by
  have h := (C.mem_center_iff _).1 (C.levLift_pow_three_mem_center k)
  simpa using h

theorem frame_of_ctx : ∃ (g : G12) (c : Gen → Fin 6 → ZMod 3) (p : Gen → Equiv.Perm (Fin 6))
    (ψ' : D5 →* A4), g ∈ gammaU ∧ g * theta0e = theta0e * g ∧
    (∀ a : C.AtildeE, g⁻¹ * C.rhoA a * g ∈ D5) ∧
    (∀ d ∈ D5, ∃ a : C.AtildeE, g⁻¹ * C.rhoA a * g = d) ∧
    (∀ k, g⁻¹ * ((C.levLift k : C.E) : G12) * g = diagE (c k) * permE (p k)) ∧
    (∀ k, p k ^ 3 = 1) ∧
    (∀ (a : C.AtildeE) (h : g⁻¹ * C.rhoA a * g ∈ D5), ψ' ⟨g⁻¹ * C.rhoA a * g, h⟩ = C.psiE a) ∧
    Function.Surjective ψ' ∧ (∀ d : D5, ψ' d = 1 ↔ (d : G12) ∈ Subgroup.zpowers theta0e) ∧
    (∀ (k : Gen) (d : D5) (h : permE (p k) * (d : G12) * (permE (p k))⁻¹ ∈ D5),
      ψ' ⟨permE (p k) * (d : G12) * (permE (p k))⁻¹, h⟩ = sg k (ψ' d)) := by
  haveI : Finite C.E := Nat.finite_of_card_ne_zero (by rw [C.card_E]; norm_num)
  refine frame_data (A := C.AtildeE) (fun a => Subtype.ext (C.AtildeE_pow_three a.2))
    C.card_AtildeE (ρ := C.rhoA) C.rhoA_injective C.rhoA_mem_gammaU (θ := C.thetaA) rfl C.psiE
    C.psiE_surjective (fun a => ?_) (fun k => ((C.levLift k : C.E) : G12))
    (fun k => C.E_le_gammaU (C.levLift k).2) C.levLift_comm C.levLift_pow_three_mem_zpowers
    (fun k a => ?_)
  · rw [C.psiE_eq_one_iff, C.mem_center_iff, C.mem_zpowers_thetaA_iff]
  · refine ⟨⟨C.levLift k * a * (C.levLift k)⁻¹, C.levLift_normalizes a.2⟩, rfl, ?_⟩
    exact C.psiE_levLift_conj a

theorem exists_adjacent : ∃ (y : C.E) (a₀ a₀' a₁ : C.AtildeE),
    y * (a₀ : C.E) * y⁻¹ = (a₀' : C.E) ∧
    C.psiE a₀ = Multiplicative.ofAdd ((1, 2, 1, 1) : T4) ∧
    C.psiE a₀' = Multiplicative.ofAdd ((1, 0, 0, 0) : T4) ∧
    ∀ a : C.E, a ∈ C.AtildeE → y * (a₁ : C.E) * y⁻¹ ≠ a := by
  obtain ⟨y, hy⟩ := C.hπs yBar
  obtain ⟨a₀, ha₀⟩ := C.psiE_surjective (Multiplicative.ofAdd ((1, 2, 1, 1) : T4))
  obtain ⟨a₁, ha₁⟩ := C.psiE_surjective (Multiplicative.ofAdd ((0, 1, 0, 0) : T4))
  have h1 : C.π (y * (a₀ : C.E) * y⁻¹) = thetaBar (Multiplicative.ofAdd ((1, 0, 0, 0) : T4)) := by
    rw [map_mul, map_mul, map_inv, hy, ← C.thetaBar_psiE, ha₀, mul_inv_eq_iff_eq_mul]
    exact yBar_mul_thetaBar
  have hmem : y * (a₀ : C.E) * y⁻¹ ∈ C.AtildeE := by
    rw [mem_AtildeE, h1]; exact ⟨_, rfl⟩
  refine ⟨y, a₀, ⟨_, hmem⟩, a₁, rfl, ha₀, ?_, ?_⟩
  · apply thetaBar_injective
    rw [C.thetaBar_psiE]
    exact h1
  · intro a ha hEq
    obtain ⟨x', hx'⟩ : ∃ x', thetaBar x' = C.π a := ha
    apply yBar_mul_thetaBar_ne x'
    rw [hx', ← hEq, map_mul, map_mul, map_inv, hy, ← C.thetaBar_psiE a₁, ha₁]
    group

end Ctx

@[expose] def conjSub (H : Subgroup G12) (t : G12) : Subgroup G12 :=
  H.map (MulAut.conj t).toMonoidHom

theorem mem_conjSub {H : Subgroup G12} {t x : G12} : x ∈ conjSub H t ↔ t⁻¹ * x * t ∈ H := by
  unfold conjSub
  rw [Subgroup.mem_map_equiv]
  rfl

theorem card_conjSub (H : Subgroup G12) (t : G12) : Nat.card (conjSub H t) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj t).injective

theorem conjSub_conjSub (H : Subgroup G12) (t u : G12) :
    conjSub (conjSub H t) u = conjSub H (u * t) := by
  ext x
  rw [mem_conjSub, mem_conjSub, mem_conjSub]
  simp [mul_assoc]

theorem conjSub_mono {H K : Subgroup G12} (h : H ≤ K) (t : G12) : conjSub H t ≤ conjSub K t := by
  intro x hx
  rw [mem_conjSub] at hx ⊢
  exact h hx

theorem mem_conjSub_inv {H : Subgroup G12} {t x : G12} : x ∈ conjSub H t⁻¹ ↔ t * x * t⁻¹ ∈ H := by
  rw [mem_conjSub, inv_inv]

theorem exists_conj_eq_M0 (C : Ctx) (hM0card : Nat.card M0 = 39191040) :
    ∃ t ∈ gammaU, conjSub C.X t = M0 := by
  obtain ⟨g, c, p, ψ', hgg, hgu, hD5, hD5s, hbconj, hp3, hψ'a, hψ's, hψ'k, hψ'eq⟩ :=
    C.frame_of_ctx
  have hgcomm : Commute g theta0e := hgu
  have hX₁g : conjSub C.X g⁻¹ ≤ gammaU := by
    intro x hx
    rw [mem_conjSub_inv] at hx
    have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ gammaU :=
      mul_mem (mul_mem (inv_mem hgg) (C.hXg hx)) hgg
    simpa [mul_assoc] using h1
  have hE₁X₁ : conjSub C.E g⁻¹ ≤ conjSub C.X g⁻¹ := conjSub_mono C.hEX g⁻¹
  have hEn₁ : ∀ x ∈ conjSub C.X g⁻¹, ∀ e ∈ conjSub C.E g⁻¹, x * e * x⁻¹ ∈ conjSub C.E g⁻¹ := by
    intro x hx e he
    rw [mem_conjSub_inv] at hx he ⊢
    have := C.hEnorm _ hx _ he
    simpa [mul_assoc] using this
  have hX₁4 : Nat.card (conjSub C.X g⁻¹) = 4 * Nat.card (conjSub C.E g⁻¹) := by
    rw [card_conjSub, card_conjSub]; exact C.hX4
  have hX₁card : Nat.card (conjSub C.X g⁻¹) = 39191040 := by
    rw [card_conjSub]; exact C.hXcard
  have hEu₁ : ∀ e ∈ conjSub C.E g⁻¹, e * theta0e = theta0e * e := by
    intro e he
    rw [mem_conjSub_inv] at he
    have h1 : (g * e * g⁻¹) * theta0e = theta0e * (g * e * g⁻¹) := C.theta0e_comm ⟨_, he⟩
    have h2 := commute_conj_of_commute (inv_mem hgg) h1
    simpa [mul_assoc] using h2
  have hD5E₁ : D5 ≤ conjSub C.E g⁻¹ := by
    intro d hd
    obtain ⟨a, ha⟩ := hD5s d hd
    rw [mem_conjSub_inv, ← ha]
    have h1 : g * (g⁻¹ * C.rhoA a * g) * g⁻¹ = C.rhoA a := by group
    rw [h1]
    exact a.1.2
  have hfr₁ : ∀ x ∈ conjSub C.X g⁻¹, ∃ e ∈ conjSub C.E g⁻¹, ∃ n ∈ conjSub C.X g⁻¹,
      (∀ d ∈ D5, n * d * n⁻¹ ∈ D5) ∧ x = e * n := by
    intro x hx
    rw [mem_conjSub_inv] at hx
    obtain ⟨e, he, n, hn, hnorm, hxen⟩ := C.frattini (g * x * g⁻¹) hx
    refine ⟨g⁻¹ * e * g, ?_, g⁻¹ * n * g, ?_, ?_, ?_⟩
    · rw [mem_conjSub_inv]
      have : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
      rw [this]; exact he
    · rw [mem_conjSub_inv]
      have : g * (g⁻¹ * n * g) * g⁻¹ = n := by group
      rw [this]; exact hn
    · intro d hd
      obtain ⟨a, ha⟩ := hD5s d hd
      have h1 : C.rhoA a ∈ C.AtildeG := ⟨a.1, a.2, rfl⟩
      obtain ⟨a'', ha''E, ha''⟩ := hnorm _ h1
      have hD := hD5 ⟨a'', ha''E⟩
      have h2 : C.rhoA ⟨a'', ha''E⟩ = n * C.rhoA a * n⁻¹ := ha''
      have h3 : (g⁻¹ * n * g) * d * (g⁻¹ * n * g)⁻¹ = g⁻¹ * C.rhoA ⟨a'', ha''E⟩ * g := by
        rw [h2, ← ha]; group
      rw [h3]; exact hD
    · calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (e * n) * g := by rw [hxen]
        _ = (g⁻¹ * e * g) * (g⁻¹ * n * g) := by group
  have hA6 : ∀ π ∈ alternatingGroup (Fin 6), permE π ∈ conjSub C.E g⁻¹ := by
    have hp := perm_closure_eq_alternating p hp3 ψ' hψ's hψ'k hψ'eq
    intro π hπ
    refine permE_mem_of_closure hD5E₁ c p (fun k => ?_) hp hπ
    rw [← hbconj k, mem_conjSub_inv]
    have : g * (g⁻¹ * ((C.levLift k : C.E) : G12) * g) * g⁻¹ = ((C.levLift k : C.E) : G12) := by
      group
    rw [this]
    exact (C.levLift k).2
  obtain ⟨m, hm, hNm⟩ := exists_twist (conjSub C.X g⁻¹) (conjSub C.E g⁻¹) hX₁g hE₁X₁ hEn₁ hX₁4
    hX₁card hEu₁ hD5E₁ hfr₁ hA6
  have hmg : m ∈ gammaU := monGamma_le_gammaU hm
  obtain ⟨t, ht⟩ : ∃ t : G12, t = m * g⁻¹ := ⟨_, rfl⟩
  have htg : t ∈ gammaU := ht ▸ mul_mem hmg (inv_mem hgg)
  have hX₂card : Nat.card (conjSub C.X t) = 39191040 := by
    rw [card_conjSub]; exact C.hXcard
  have hNX₂ : Nsub ≤ conjSub C.X t := by
    rw [ht, ← conjSub_conjSub]; exact hNm
  have hDt : ∀ a : C.AtildeE, t * C.rhoA a * t⁻¹ ∈ D5 := by
    intro a
    have h1 := mul_mem_D5_of_mem_monGamma hm (hD5 a)
    have h2 : t * C.rhoA a * t⁻¹ = m * (g⁻¹ * C.rhoA a * g) * m⁻¹ := by rw [ht]; group
    rw [h2]; exact h1
  have hDts : ∀ d ∈ D5, ∃ a : C.AtildeE, t * C.rhoA a * t⁻¹ = d := by
    intro d hd
    have h1 := mul_mem_D5_of_mem_monGamma (inv_mem hm) hd
    obtain ⟨a, ha⟩ := hD5s _ h1
    refine ⟨a, ?_⟩
    have h2 : t * C.rhoA a * t⁻¹ = m * (g⁻¹ * C.rhoA a * g) * m⁻¹ := by rw [ht]; group
    rw [h2, ha]; group
  obtain ⟨y, a₀, a₀', a₁, hya, hψa₀, hψa₀', hnot⟩ := C.exists_adjacent
  have hyaG : (y : G12) * C.rhoA a₀ * (y : G12)⁻¹ = C.rhoA a₀' := by
    have := congrArg Subtype.val hya
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  have hd₀ : ψ' ⟨g⁻¹ * C.rhoA a₀' * g, hD5 a₀'⟩ = Multiplicative.ofAdd ((1, 0, 0, 0) : T4) := by
    rw [hψ'a a₀' (hD5 a₀'), hψa₀']
  obtain ⟨S, j, e, c₂, hS, he, hdc, hc₂⟩ := root_type p ψ' hψ's hψ'k hψ'eq _ hd₀
  have hdc' : g⁻¹ * C.rhoA a₀' * g = diagE c₂ := hdc
  obtain ⟨c', S', j', e', hconj, hS', he', hc'⟩ := conj_diagE_type hm hS he hc₂
  have hd₂ : t * C.rhoA a₀' * t⁻¹ = diagE c' := by
    rw [← hconj, ← hdc', ht]; group
  have hyX₂ : t * (y : G12) * t⁻¹ ∈ conjSub C.X t := by
    rw [mem_conjSub]
    have : t⁻¹ * (t * (y : G12) * t⁻¹) * t = y := by group
    rw [this]
    exact C.hEX y.2
  have hyg : t * (y : G12) * t⁻¹ ∈ gammaU :=
    mul_mem (mul_mem htg (C.E_le_gammaU y.2)) (inv_mem htg)
  have hyu : (t * (y : G12) * t⁻¹) * theta0e = theta0e * (t * (y : G12) * t⁻¹) :=
    commute_conj_of_commute htg (C.theta0e_comm y)
  have hnot₂ : t * (y : G12) * t⁻¹ ∉ monLin := by
    intro hmon
    have hnorm := mul_mem_D5_of_mem_monGamma (monLin_le_monGamma hmon) (hDt a₁)
    obtain ⟨a, ha⟩ := hDts _ (by
      have h1 : t * (y : G12) * t⁻¹ * (t * C.rhoA a₁ * t⁻¹) * (t * (y : G12) * t⁻¹)⁻¹ =
          t * ((y : G12) * C.rhoA a₁ * (y : G12)⁻¹) * t⁻¹ := by group
      rwa [h1] at hnorm)
    have h2 : (y : G12) * C.rhoA a₁ * (y : G12)⁻¹ = C.rhoA a := by
      exact mul_left_cancel (mul_right_cancel ha.symm)
    apply hnot a.1 a.2
    exact Subtype.ext h2
  have hd : (t * (y : G12) * t⁻¹)⁻¹ * diagE c' * (t * (y : G12) * t⁻¹) ∈ D5 := by
    have h1 : (t * (y : G12) * t⁻¹)⁻¹ * diagE c' * (t * (y : G12) * t⁻¹) =
        t * C.rhoA a₀ * t⁻¹ := by
      rw [← hd₂]
      have h2 : C.rhoA a₀ = (y : G12)⁻¹ * C.rhoA a₀' * y := by
        rw [← hyaG]; group
      rw [h2]; group
    rw [h1]
    exact hDt a₀
  have hM0le : M0 ≤ conjSub C.X t :=
    fl_of_type hX₂card hNX₂ hyX₂ hyg hyu hnot₂ hS' he' hc' hd
  haveI : Finite (conjSub C.X t) := Nat.finite_of_card_ne_zero (by rw [hX₂card]; norm_num)
  exact ⟨t, htg, (Subgroup.eq_of_le_of_card_ge hM0le (by rw [hX₂card, hM0card])).symm⟩

end CFSG.GF2Type.Smith1979.IdxFour
