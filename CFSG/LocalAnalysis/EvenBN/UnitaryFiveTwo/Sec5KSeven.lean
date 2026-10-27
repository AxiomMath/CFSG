module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KTwo
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KFive
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KSix
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4C0
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL44Main

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG.Open CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaInputs SL44
open scoped MatrixGroups

section Types

theorem exists_eq_stdSL (θ : MulAut SL(4, F4)) :
    ∃ (A : GL (Fin 4) F4) (σ : F4 ≃+* F4) (ε : ℕ), ε ≤ 1 ∧ θ = stdSL 4 F4 A σ ε := by
  obtain ⟨A, σ, ε, hε, h⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation (K := F4)
      (n := 4) (by norm_num)).2 (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.descendAut 4 F4 θ)
  exact ⟨A, σ, ε, hε, eq_of_descendAut_eq (by norm_num) (by rw [h, descendAut_stdSL])⟩

theorem HasTrType.inv {β : MulAut SL(4, F4)} {σ : F4 ≃+* F4} {ε : ℕ} (h : HasTrType β σ ε)
    (hε : ε ≤ 1) : HasTrType β⁻¹ σ⁻¹ ε := by
  intro x
  have h1 := h (β⁻¹ (twist ε x))
  rw [MulAut.apply_inv_self, twist_map, twist_twist hε hε] at h1
  have h2 : (ε + ε) % 2 = 0 := by omega
  rw [h2, twist_zero] at h1
  rw [h1]
  exact (σ.symm_apply_apply _).symm

theorem ringEquiv_comm (σ τ : F4 ≃+* F4) : σ * τ = τ * σ := by
  rcases ringEquiv_eq_one_or_eq_barEquiv σ with rfl | rfl <;>
    rcases ringEquiv_eq_one_or_eq_barEquiv τ with rfl | rfl <;> simp

variable {G : Type} [Group G] {K : Subgroup G}

theorem ActsOn.type_eq {φ φ' : SL(4, F4) ≃* K} {x : G} {β β' : MulAut SL(4, F4)}
    (h : ActsOn φ x β) (h' : ActsOn φ' x β') {σ σ' : F4 ≃+* F4} {ε ε' : ℕ}
    (hτ : HasTrType β σ ε) (hτ' : HasTrType β' σ' ε') (hε : ε ≤ 1) (hε' : ε' ≤ 1) :
    σ = σ' ∧ ε = ε' := by
  set θ : MulAut SL(4, F4) := φ.trans φ'.symm with hθ
  have hφθ : ∀ y, φ' (θ y) = φ y := fun y => by simp [hθ]
  have hβ' : β' = θ * β * θ⁻¹ := by
    refine MulEquiv.ext fun z => φ'.injective (Subtype.ext ?_)
    have hz : φ' z = φ (θ⁻¹ z) := by rw [← hφθ, MulAut.apply_inv_self]
    rw [← h' z, hz, h, MulAut.mul_apply, MulAut.mul_apply, hφθ]
  obtain ⟨A₀, σ₀, ε₀, hε₀, hA₀⟩ := exists_eq_stdSL θ
  have hτθ : HasTrType θ σ₀ ε₀ := hA₀ ▸ hasTrType_stdSL A₀ σ₀ hε₀
  have h1 := HasTrType.mul (HasTrType.mul hτθ hτ hε₀ hε) (HasTrType.inv hτθ hε₀)
    (mod_two_le_one _) hε₀
  rw [← hβ'] at h1
  obtain ⟨hs, he⟩ := h1.unique hτ' (mod_two_le_one _) hε'
  refine ⟨?_, ?_⟩
  · rw [← hs, ringEquiv_comm σ₀ σ, mul_assoc, mul_inv_cancel, mul_one]
  · rw [← he]
    omega

theorem hasTrType_conj (g : SL(4, F4)) : HasTrType (MulAut.conj g) 1 0 := by
  intro z
  rw [twist_zero, RingAut.one_apply, MulAut.conj_apply]
  change ((g : Matrix (Fin 4) (Fin 4) F4) * z *
    ((g⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4)).trace = _
  rw [Matrix.trace_mul_cycle, show ((g⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) * g = 1 from
    congrArg Subtype.val (inv_mul_cancel g), Matrix.one_mul]

theorem actsOn_conj_of_mem (φ : SL(4, F4) ≃* K) {k : G} (hk : k ∈ K) :
    ActsOn φ k (MulAut.conj (φ.symm ⟨k, hk⟩)) := fun y => by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem inf_centralizer_eq_map (φ : SL(4, F4) ≃* K) {x : G} {β : MulAut SL(4, F4)}
    (hβ : ActsOn φ x β) :
    K ⊓ centralizer ({x} : Set G) = (fixSub β).map (K.subtype.comp φ.toMonoidHom) := by
  refine centralizer_eq_map_fixSub φ.toMonoidHom φ.surjective hβ fun y z hz hyz => ?_
  have hz1 : z = 1 := by
    rw [(MonoidHom.ker_eq_bot_iff φ.toMonoidHom).mpr φ.injective] at hz
    exact hz
  refine ⟨1, one_mem _, ?_⟩
  rw [mul_one]
  rw [hz1, mul_one] at hyz
  exact hyz

theorem card_inf_centralizer (φ : SL(4, F4) ≃* K) {x : G} {β : MulAut SL(4, F4)}
    (hβ : ActsOn φ x β) : Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) =
      Nat.card (fixSub β) := by
  rw [inf_centralizer_eq_map φ hβ, Subgroup.card_map_of_injective
    (fun a b hab => φ.injective (K.subtype_injective hab))]

end Types

theorem card_centralizer_conj {G : Type} [Group G] (g x : G) :
    Nat.card (centralizer ({g⁻¹ * x * g} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have e : centralizer ({g⁻¹ * x * g} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    ext y
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hy
      refine ⟨g * y * g⁻¹, mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [hy]
          _ = x * (g * y * g⁻¹) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
    · rintro ⟨z, hz, rfl⟩
      have hz' : z * x = x * z := mem_centralizer_singleton_iff.1 hz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * z * g * (g⁻¹ * x * g) = g⁻¹ * (z * x) * g := by group
        _ = g⁻¹ * (x * z) * g := by rw [hz']
        _ = g⁻¹ * x * g * (g⁻¹ * z * g) := by group
  rw [e, card_map_of_injective (MulAut.conj g⁻¹).injective]

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem exists_actsOn_graph (φ : SL(4, F4) ≃* d.K) {x : G} (hxN : x ∈ normalizer (d.K : Set G))
    (hg : IsGraphOn d.K x) : ∃ A : GL (Fin 4) F4, ActsOn φ x (stdSL 4 F4 A 1 1) := by
  obtain ⟨φ', C, hC⟩ := hg
  obtain ⟨A, σ, ε, hε, hA, hτ⟩ := exists_type φ hxN
  obtain ⟨rfl, rfl⟩ := hA.type_eq hC hτ (hasTrType_stdSL C 1 le_rfl) hε le_rfl
  exact ⟨A, hA⟩

omit [Finite G] in
theorem exists_actsOn_field (φ : SL(4, F4) ≃* d.K) {x : G} (hxN : x ∈ normalizer (d.K : Set G))
    (hf : IsFieldOn d.K x) : ∃ A : GL (Fin 4) F4, ActsOn φ x (stdSL 4 F4 A barEquiv 0) := by
  obtain ⟨φ', C, hC⟩ := hf
  obtain ⟨A, σ, ε, hε, hA, hτ⟩ := exists_type φ hxN
  obtain ⟨rfl, rfl⟩ := hA.type_eq hC hτ (hasTrType_stdSL C barEquiv zero_le_one) hε
    zero_le_one
  exact ⟨A, hA⟩

theorem card_F4 : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]

omit [Finite G] in
theorem ker_le_center (φ : SL(4, F4) ≃* d.K) : φ.toMonoidHom.ker ≤ center SL(4, F4) := by
  rw [(MonoidHom.ker_eq_bot_iff φ.toMonoidHom).mpr φ.injective]
  exact bot_le

omit [Finite G] in
theorem t_comm_of_mem_H {a : G} (haH : a ∈ d.H) : a * d.t = d.t * a :=
  mem_centralizer_singleton_iff.1 haH

theorem t_mul_mul_self (h : d.Hyp) {a : G} (haH : a ∈ d.H) (ha1 : a * a = 1) :
    d.t * a * (d.t * a) = 1 := by
  calc d.t * a * (d.t * a) = d.t * (a * d.t) * a := by group
    _ = d.t * (d.t * a) * a := by rw [t_comm_of_mem_H haH]
    _ = d.t * d.t * (a * a) := by group
    _ = 1 := by rw [h.t_mul_t, ha1, mul_one]


theorem not_conj_t_eq_mul (h : d.Hyp) (hK : d.KLinear) {a : G} (haH : a ∈ d.H)
    (ha1 : a * a = 1) (haf : h.act ⟨a, haH⟩ = fld) (hta : IsFieldOn d.K (d.t * a)) (g : G) :
    g⁻¹ * d.t * g ≠ d.t * a := by
  obtain ⟨φ, -⟩ := hK.graphField
  have hN : d.t * a ∈ normalizer (d.K : Set G) :=
    mul_mem h.t_mem_normalizer_K (h.mem_normalizer_K_of_act_fld haH haf)
  obtain ⟨A, hA⟩ := exists_actsOn_field φ hN hta
  rcases cases_of_lift (n := 4) (by norm_num) card_F4 φ.toMonoidHom (ker_le_center φ)
      (h.t_mul_mul_self haH ha1) zero_le_one hA with ⟨hσ, -⟩ | ⟨-, hσx, H, hH⟩
  · exact absurd hσ barEquiv_ne_one
  · obtain ⟨θ, hθ, hrange⟩ := exists_field_centralizer (n := 4) (by norm_num) φ.toMonoidHom
      φ.surjective (ker_le_center φ) hσx hH
    have hcard : Nat.card (d.K ⊓ centralizer ({d.t * a} : Set G) : Subgroup G) = 20160 := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, card_SL_four_two]
    have h7 : 7 ∣ Nat.card (centralizer ({d.t * a} : Set G)) :=
      (show 7 ∣ 20160 by norm_num).trans (hcard ▸ card_dvd_of_le inf_le_right)
    intro hg
    have hc := card_centralizer_conj g d.t
    rw [hg] at hc
    exact h.not_seven_dvd_card_H (hc ▸ h7)

omit [Finite G]
  in
theorem card_K₃ (hK : d.KLinear) : Nat.card d.K₃ = 25920 := by
  obtain ⟨φ, hφ⟩ := hK.graphField
  rw [← hK.centralizer_eq]
  change Nat.card (d.K ⊓ centralizer ({d.t} : Set G) : Subgroup G) = _
  rw [card_inf_centralizer φ hφ]
  have e : fixSub (CFSG.EvenSmallLie.UnitarySix.YamadaEnd.sigmaSL F4) =
      CFSG.EvenSmallLie.UnitarySix.YamadaEnd.msigma F4 := Subgroup.ext fun _ => Iff.rfl
  rw [e, card_msigma card_F4]

omit [Finite G]
  in
theorem K₃sub_eq_StabSub (hK : d.KLinear) : K₃sub = StabSub := by
  have h1 : Nat.card K₃sub = 25920 := by rw [← d.card_pull]; exact card_K₃ hK
  exact Subgroup.eq_of_le_of_card_ge K₃sub_le_StabSub (h1 ▸ card_StabSub_le)

omit [Finite G]
  in
theorem pull_CfldSub_le_K₃ (hK : d.KLinear) : d.pull CfldSub ≤ d.K₃ := by
  rw [Data.K₃, K₃sub_eq_StabSub hK]
  exact d.pull_mono CfldSub_le_StabSub

theorem pull_CfldSub_le_centralizer (h : d.Hyp) {a : G} (haH : a ∈ d.H)
    (haf : h.act ⟨a, haH⟩ = fld) : d.pull CfldSub ≤ centralizer ({a} : Set G) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have e := h.ι_act_apply ⟨a, haH⟩ s
  rw [haf, mem_CfldSub.1 hs] at e
  calc d.ι s * a = a * d.ι s * a⁻¹ * a := by rw [← e]
    _ = a * d.ι s := by group

theorem nine_dvd_card_CK (h : d.Hyp) (hK : d.KLinear) {a : G} (haH : a ∈ d.H)
    (haf : h.act ⟨a, haH⟩ = fld) :
    9 ∣ Nat.card (d.K ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  obtain ⟨E, hE, hE9⟩ := exists_E₉
  have hle : d.pull E ≤ d.K ⊓ centralizer ({a} : Set G) := by
    intro x hx
    have hx3 : x ∈ d.K₃ := d.pull_mono (hE.trans inf_le_left) hx
    rw [← hK.centralizer_eq] at hx3
    exact ⟨hx3.1, h.pull_CfldSub_le_centralizer haH haf (d.pull_mono (hE.trans inf_le_right) hx)⟩
  rw [← hE9, ← d.card_pull E]
  exact card_dvd_of_le hle

theorem exists_symplectic (h : d.Hyp) (hK : d.KLinear) (φ : SL(4, F4) ≃* d.K) {a : G}
    (haH : a ∈ d.H) (ha1 : a * a = 1) (haf : h.act ⟨a, haH⟩ = fld) (hag : IsGraphOn d.K a) :
    ∃ H C : GL (Fin 4) F4, (C : Matrix (Fin 4) (Fin 4) F4) = J₂ ∧
      ActsOn φ a (stdSL 4 F4 H 1 0 * stdSL 4 F4 C 1 1 * (stdSL 4 F4 H 1 0)⁻¹) := by
  have hN := h.mem_normalizer_K_of_act_fld haH haf
  obtain ⟨A, hA⟩ := exists_actsOn_graph φ hN hag
  rcases cases_of_lift (n := 4) (by norm_num) card_F4 φ.toMonoidHom (ker_le_center φ) ha1 le_rfl
      hA with ⟨-, ⟨g, -, hg⟩ | ⟨H, C, hC, hHC⟩⟩ | ⟨hσ, -⟩
  · exfalso
    have e := (hA : ActsOn φ a _).eq (hg : ActsOn φ a _)
    have hu := (hasTrType_stdSL A 1 le_rfl).unique (e ▸ hasTrType_conj g) le_rfl zero_le_one
    exact absurd hu.2 one_ne_zero
  · rcases hC with hC1 | ⟨r, hr, hrC⟩
    · exfalso
      have hC1' : C = 1 := Units.ext hC1
      subst hC1'
      have hcard := card_inf_centralizer φ hHC
      rw [fixSub_conj, card_map_of_injective (MulEquiv.injective _)] at hcard
      exact not_nine_dvd_card_OI (hcard ▸ h.nine_dvd_card_CK hK haH haf)
    · obtain rfl : r = 2 := by omega
      exact ⟨H, C, hrC, hHC⟩
  · exact absurd rfl hσ

omit [Finite G]
  in
theorem CK_eq (φ : SL(4, F4) ≃* d.K) {a : G} {H C : GL (Fin 4) F4}
    (hHC : ActsOn φ a (stdSL 4 F4 H 1 0 * stdSL 4 F4 C 1 1 * (stdSL 4 F4 H 1 0)⁻¹)) :
    d.K ⊓ centralizer ({a} : Set G) =
      ((fixSub (stdSL 4 F4 C 1 1)).map (stdSL 4 F4 H 1 0).toMonoidHom).map
        (d.K.subtype.comp φ.toMonoidHom) := by
  rw [inf_centralizer_eq_map φ hHC, fixSub_conj]

omit [Finite G]
  in
theorem lieModel_CK (φ : SL(4, F4) ≃* d.K) {a : G} {H C : GL (Fin 4) F4}
    (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂)
    (hHC : ActsOn φ a (stdSL 4 F4 H 1 0 * stdSL 4 F4 C 1 1 * (stdSL 4 F4 H 1 0)⁻¹)) :
    CFSG.Blueprint.LieModel (d.K ⊓ centralizer ({a} : Set G) : Subgroup G) .PSp 2 2 2 := by
  have e1 : fixSub (stdSL 4 F4 C 1 1) ≃*
      ((fixSub (stdSL 4 F4 C 1 1)).map (stdSL 4 F4 H 1 0).toMonoidHom) :=
    (fixSub (stdSL 4 F4 C 1 1)).equivMapOfInjective _ (MulEquiv.injective _)
  have e2 : ((fixSub (stdSL 4 F4 C 1 1)).map (stdSL 4 F4 H 1 0).toMonoidHom) ≃*
      (((fixSub (stdSL 4 F4 C 1 1)).map (stdSL 4 F4 H 1 0).toMonoidHom).map
        (d.K.subtype.comp φ.toMonoidHom)) :=
    Subgroup.equivMapOfInjective _ _ fun x y hxy => φ.injective (d.K.subtype_injective hxy)
  have e3 := (e1.trans e2).trans (MulEquiv.subgroupCongr (CK_eq φ hHC).symm)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e3 (lieModel_fixSub_symplectic hC)

omit [Finite G]
  in
theorem not_inner_on_CK {φ : SL(4, F4) ≃* d.K}
    (hφ : ActsOn φ d.t (CFSG.EvenSmallLie.UnitarySix.YamadaEnd.sigmaSL F4)) {a : G}
    {H C : GL (Fin 4) F4} (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂)
    (hHC : ActsOn φ a (stdSL 4 F4 H 1 0 * stdSL 4 F4 C 1 1 * (stdSL 4 F4 H 1 0)⁻¹)) :
    ¬ ∃ y ∈ d.K ⊓ centralizer ({a} : Set G), ∀ z ∈ d.K ⊓ centralizer ({a} : Set G),
      d.t * z * d.t⁻¹ = y * z * y⁻¹ := by
  rintro ⟨y, hy, hyz⟩
  set g : SL(4, F4) := φ.symm ⟨y, hy.1⟩ with hg
  refine not_forall_sigmaSL_eq_conj hC H g fun w hw => φ.injective (Subtype.ext ?_)
  have hwz : (φ w : G) ∈ d.K ⊓ centralizer ({a} : Set G) := by
    rw [CK_eq φ hHC]
    exact ⟨w, hw, rfl⟩
  have h1 := hyz _ hwz
  rw [hφ w] at h1
  have hyg : (φ g : G) = y := by rw [hg, MulEquiv.apply_symm_apply]
  rw [h1, ← hyg, map_mul, map_mul, map_inv]
  rfl

omit [Finite G]
  in
theorem a_not_mem_K (φ : SL(4, F4) ≃* d.K) {a : G} {A : GL (Fin 4) F4}
    (hA : ActsOn φ a (stdSL 4 F4 A 1 1)) : a ∉ d.K := by
  intro haK
  have e := hA.eq (actsOn_conj_of_mem φ haK)
  have hu := (hasTrType_stdSL A 1 le_rfl).unique (e ▸ hasTrType_conj _) le_rfl zero_le_one
  exact absurd hu.2 one_ne_zero

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
