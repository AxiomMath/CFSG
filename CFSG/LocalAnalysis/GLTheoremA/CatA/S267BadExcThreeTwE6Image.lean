module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Act
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Input
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActPSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem fixSubgroup_conj_eq_centralizer_zpowers {X : Type*} [Group X] (r : X) :
    fixSubgroup (MulAut.conj r) =
      Subgroup.centralizer ((Subgroup.zpowers r : Subgroup X) : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : Commute r g := by
      change r * g = g * r
      calc r * g = r * g * r⁻¹ * r := by group
        _ = g * r := by rw [h]
    exact (hc.zpow_left k).eq
  · intro h
    rw [h r (Subgroup.mem_zpowers r)]
    group


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_orderOf_three_twE6 (hK : Nat.card K = (ℓ ^ f) ^ 2) (h3 : 3 ∣ ℓ ^ f + 1) :
    ∃ c : Kˣ, orderOf c = 3 ∧ unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) =
      (c : K) + ((c⁻¹ : Kˣ) : K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h : (ℓ ^ f) ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, show ℓ ^ f % 3 = 2 by omega]
    have h1 : 1 ≤ (ℓ ^ f) ^ 2 := by
      have : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
      nlinarith
    omega
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hK3
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hcQ : c ^ (ℓ ^ f) = c⁻¹ := by
    rw [pow_eq_pow_mod (ℓ ^ f) hc3, show ℓ ^ f % 3 = 2 by omega]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hc3]
  refine ⟨c, hc, ?_⟩
  rw [map_add, unitaryInvolution_apply, unitaryInvolution_apply, ← Units.val_pow_eq_pow_val,
    ← Units.val_pow_eq_pow_val, hcQ, inv_pow, hcQ, inv_inv, add_comm]

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_twE6_vtw_image (hVtw : TwE6VtwInput) (hJc : TwE6JCompInput)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hB : IsElemAbelian 3 B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3)
    (hB4 : 3 ^ 4 ≤ Nat.card B)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
    {Γ : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hΓe : ∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
      e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩))
    (hΓker : Γ.ker = centModSubgroup 3 S)
    (hI : B.map Γ ≤ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ f))
    (h6 : 3 ^ 6 ≤ Nat.card ↥(B.map Γ)) : S267ConcA 3 S B := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hσ : ∀ c, unitaryInvolution K ℓ f c = c ^ (ℓ ^ f) := unitaryInvolution_apply K ℓ f
  have h3' : ¬ 3 ∣ ℓ ^ f := fun h => by omega
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  obtain ⟨ζ, hζ, hσζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 6
  obtain ⟨c, hc, hct⟩ := exists_orderOf_three_twE6 hK h3
  obtain ⟨V, hVI, hVe, hVc, hr₀V, hVt, hVJ, hVk, ⟨v₁, hv₁V, hv₁r, hv₁L⟩, -, -⟩ :=
    hVtw hK hf hℓ2 h3 hζ hσζ P hP hc hct
  set r₀ := TwE6Conc.twE6R0 c hct with hr₀
  set t := TwE6Conc.twE6T K ℓ f with ht
  set J := (TwE6Conc.leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))
    with hJ
  have hΓBe : IsElemAbelian 3 (B.map Γ) := CFSG.StandardType.TableB.isElemAbelian_map hB Γ
  have hΓBc : Nat.card ↥(B.map Γ) = 3 ^ 6 :=
    le_antisymm (card_le_of_le_twInndiag hℓ hf hK _ hσ h3' hΓBe hI) h6
  obtain ⟨γ, -, hγ⟩ :=
    exists_conj_eq_of_le_twInndiag hℓ hf hK _ hσ h3' hVI hI hVe hΓBe hVc hΓBc
  set Γ' := (MulAut.conj γ).toMonoidHom.comp Γ with hΓ'def
  set e' := e.trans γ with he'
  have hBΓ' : B.map Γ' = V := by rw [hΓ'def, ← Subgroup.map_map, hγ]
  have hker' : Γ'.ker = Γ.ker := by
    ext b
    simp only [MonoidHom.mem_ker, hΓ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro h
      have h' : Γ b = γ⁻¹ * 1 * γ := by rw [← h]; group
      rw [h']
      group
    · intro h
      rw [h]
      group
  have hΓ'e : ∀ (x : ↥B) (g : ↥S), e' (chevQuotHom 3 S ⟨(x : Ω) * g * (x : Ω)⁻¹,
      hS.conj_mem _ g.2 _⟩) = Γ' x (e' (chevQuotHom 3 S g)) := by
    intro x g
    change γ (e _) = γ (Γ x (γ⁻¹ (γ (e (chevQuotHom 3 S g)))))
    rw [MulAut.inv_apply_self, hΓe]
  have hr₀o : orderOf r₀ = 3 :=
    TwE6Conc.orderOf_twE6R0 Nat.prime_three (by norm_num) hc hct
  have hZ0 : Subgroup.center ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) = ⊥ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZ0, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK _ hσ
    exact hZ0
  have hd₁1 : MulAut.conj r₀ ≠ 1 := by
    intro h1
    have hrc : r₀ ∈ Subgroup.center ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have h := congrArg
        (fun φ : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * r₀ = r₀ * g * r₀⁻¹ * r₀ := by rw [h]
        _ = r₀ * g := by group
    rw [hZ0, Subgroup.mem_bot] at hrc
    rw [hrc, orderOf_one] at hr₀o
    exact absurd hr₀o (by norm_num)
  have hJcomp : GLAPComponent 3 (fixSubgroup (MulAut.conj r₀)) J := by
    rw [fixSubgroup_conj_eq_centralizer_zpowers]
    exact hJc hK hf hℓ2 h3 hc hct
  have hW := actData_of_distinguished Nat.prime_three hB Γ'
    (by rw [hker', hΓker]; exact hBC) hB4 (hBΓ' ▸ hr₀V) hd₁1 (hBΓ' ▸ hv₁V) hv₁r hJcomp
    (fun x hx => hVJ _ (hBΓ' ▸ Subgroup.mem_map_of_mem Γ' hx))
    (fun x hx hcm => hVk _ (hBΓ' ▸ Subgroup.mem_map_of_mem Γ' hx) hcm) hv₁L
    (TwE6Conc.twE6T_ne_one hℓ2) (TwE6Conc.twE6T_sq K ℓ f)
    (fun j hj => Subgroup.mem_centralizer_singleton_iff.2
      (TwE6Conc.twE6T_commute (Subgroup.mem_subgroupOf.1 hj)).symm)
    (by
      rw [MulAut.conj_apply, hr₀, TwE6Conc.twE6R0_mul_twE6T, mul_inv_cancel_right])
  exact ModelGen.concA_of_actData_pSimple Nat.prime_three (by norm_num) hS hperf hcore hB hBC e'
    (fun x => Γ' x) hΓ'e hW

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
