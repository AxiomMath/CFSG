module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageTorus
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

@[expose] def semilinearPerm (F : Type*) [Field F] :
    Fˣ ⋊[ringAutUnits F] RingAut F →* Equiv.Perm F where
  toFun g :=
    { toFun := fun x => (g.left : F) * g.right x
      invFun := fun x => g.right.symm (((g.left⁻¹ : Fˣ) : F) * x)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  map_one' := Equiv.ext fun x => by simp
  map_mul' g h := Equiv.ext fun x => by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Units.val_mul,
      coe_ringAutUnits_apply, Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [show (g.right * h.right) x = g.right (h.right x) from rfl, map_mul, mul_assoc]

theorem semilinearPerm_apply {F : Type*} [Field F] (g : Fˣ ⋊[ringAutUnits F] RingAut F) (x : F) :
    semilinearPerm F g x = (g.left : F) * g.right x := rfl

theorem card_range_semilinearPerm_dvd {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card (semilinearPerm F).range ∣ (2 ^ n - 1) * n := by
  have h1 := Subgroup.card_range_dvd (semilinearPerm F)
  rwa [SemidirectProduct.card, Nat.card_units, hF,
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hF).1] at h1

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem centralizer_t_le_normalizer_L :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    H.stage.start.setting.standardSetting.standard H.stage.start.mem H.stage.start.inv).1

theorem card_range_inf_stabilizer_dvd :
    Nat.card ↥(H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K)) ∣
      (2 ^ f - 1) * f := by
  classical
  obtain ⟨E, _, _, _, σ, u, w, hS⟩ :=
    H.stage.start.exists_semilinearCoords_of_card_sylow H.stage.card_sylow
  have hc := hS.coords
  have hA := hS.mem_szA₁_iff
  have hA₁T : szA₁ (szT₁ L T) ≤ szT₁ L T := szA₁_le _
  have : Fintype E := Fintype.ofFinite E
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    rw [hS.sigma, hS.sigma, ← pow_mul, ← sq]
    have h1 : x ^ Fintype.card E = x := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hS.card] at h1
  obtain ⟨F, hF⟩ : ∃ F : Subfield E, ∀ x, x ∈ F ↔ σ x = x :=
    ⟨RingHom.eqLocusField σ (RingHom.id E), fun x => by
      rw [RingHom.mem_eqLocusField, RingHom.id_apply]⟩
  have hFcard : Nat.card F = 2 ^ f := by
    rw [← hS.card_fixed]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF)
  obtain ⟨wF, hwF⟩ : ∃ wF : G → F, ∀ b ∈ szA₁ (szT₁ L T), (wF b : E) = w b := by
    refine ⟨fun g => if hg : σ (w g) = w g then ⟨w g, (hF _).mpr hg⟩ else 0, fun b hb => ?_⟩
    have hσb : σ (w b) = w b := hc.sigma_v_of_u_eq_zero (hA₁T hb) ((hA b (hA₁T hb)).mp hb)
    show ((if hg : σ (w b) = w b then (⟨w b, (hF _).mpr hg⟩ : F) else 0 : F) : E) = w b
    rw [dite_eq_left hσb]
  have hwc : U3A₁Coords (szA₁ (szT₁ L T)) 1 wF 1 :=
    U3C1Torus.u3A₁Coords hc hA₁T hA hF hwF (fun b hb => by simpa using hb)
      (fun b hb => by simp)
  let eK : szA₁ (szT₁ L T) ≃ K := Equiv.ofBijective (fun b => v b)
    ⟨fun b b' h => Subtype.ext (H.coords.inj _ b.2 _ b'.2 h), fun s => by
      obtain ⟨b, hb, rfl⟩ := H.coords.surj s
      exact ⟨⟨b, hb⟩, rfl⟩⟩
  let eF : szA₁ (szT₁ L T) ≃ F := Equiv.ofBijective (fun b => wF b)
    ⟨fun b b' h => Subtype.ext (hwc.inj _ b.2 _ b'.2 h), fun x => by
      obtain ⟨b, hb, rfl⟩ := hwc.surj x
      exact ⟨⟨b, hb⟩, rfl⟩⟩
  set e : K ≃ F := eK.symm.trans eF with he
  have he_v : ∀ b ∈ szA₁ (szT₁ L T), e (v b) = wF b := by
    intro b hb
    have h1 : eK.symm (v b) = ⟨b, hb⟩ := eK.symm_apply_eq.mpr rfl
    rw [he, Equiv.trans_apply, h1]
    rfl
  set ψ := e.permCongrHom.toMonoidHom with hψ
  have hle : (H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K)).map ψ ≤
      (semilinearPerm F).range := by
    rintro _ ⟨_, ⟨⟨n, rfl⟩, hn0⟩, rfl⟩
    have h0 : H.perm n 0 = 0 := hn0
    obtain ⟨x₀, hx₀, hx₀n⟩ := H.mem_U₁_mul_centralizer n h0
    have hx₀N : x₀ ∈ normalizer (U : Set G) := le_normalizer (H.stage.U₁_le hx₀)
    set m : normalizer (U : Set G) := ⟨x₀⁻¹ * (n : G), mul_mem (inv_mem hx₀N) n.2⟩ with hmdef
    have hpm : H.perm n = H.perm m := by
      have hx1 : H.perm ⟨x₀, hx₀N⟩ = 1 := H.perm_eq_one_of_mem_U ⟨x₀, hx₀N⟩ (H.stage.U₁_le hx₀)
      have e : m = (⟨x₀, hx₀N⟩ : normalizer (U : Set G))⁻¹ * n := Subtype.ext rfl
      rw [e, map_mul, map_inv, hx1, inv_one, one_mul]
    rw [hpm]
    have hmN : (m : G) ∈ normalizer (U : Set G) := m.2
    have hmC : (m : G) ∈ centralizer ({t} : Set G) := hx₀n
    have hmL : (m : G) ∈ normalizer (L : Set G) := H.centralizer_t_le_normalizer_L hmC
    have hmT : (m : G) ∈ normalizer (szT₁ L T : Set G) :=
      H.stage.normalizer_U_le_normalizer_T₁ H.mu H.lam H.nu hmN
    obtain ⟨c, hc0, τ, e', hτ⟩ := hS.semilinear _ hmL hmT
    have hτF : ∀ x ∈ F, τ x ∈ F := by
      intro x hx
      rw [hF] at hx ⊢
      rw [hS.sigma, ← map_pow, ← hS.sigma, hx]
    set τF : F →+* F := τ.restrict F F hτF with hτFdef
    have hτFbij : Function.Bijective τF :=
      ⟨τF.injective, Finite.injective_iff_surjective.mp τF.injective⟩
    have hNF : c * σ c ∈ F := by rw [hF, map_mul, hσσ, mul_comm]
    have hN0 : (⟨c * σ c, hNF⟩ : F) ≠ 0 := fun h0 =>
      mul_ne_zero hc0 ((map_ne_zero σ).mpr hc0) (congrArg Subtype.val h0)
    refine ⟨⟨Units.mk0 _ hN0, RingEquiv.ofBijective τF hτFbij⟩, Equiv.ext fun x => ?_⟩
    obtain ⟨b, hb, rfl⟩ := hwc.surj x
    have hmb : (m : G) * b * (m : G)⁻¹ ∈ szA₁ (szT₁ L T) := H.conj_mem_szA₁ hmN hb
    have key : w ((m : G) * b * (m : G)⁻¹) = c * σ c * τ (w b) := by
      have h1 := (hτ b (hA₁T hb)).2
      rw [(hA b (hA₁T hb)).mp hb, map_zero, mul_zero] at h1
      rw [h1]
      simp [TraceForm.form]
    have hperm : H.perm m (v b) = v ((m : G) * b * (m : G)⁻¹) :=
      H.perm_v_szA₁_of_mem_centralizer m hmC hb
    have hesymm : e.symm (wF b) = v b := (Equiv.symm_apply_eq e).mpr (he_v b hb).symm
    have hR : (ψ (H.perm m)) (wF b) = wF ((m : G) * b * (m : G)⁻¹) := by
      show e (H.perm m (e.symm (wF b))) = _
      rw [hesymm, hperm, he_v _ hmb]
    rw [hR]
    apply Subtype.ext
    rw [hwF _ hmb, key, semilinearPerm_apply]
    show c * σ c * τ ((wF b : F) : E) = c * σ c * τ (w b)
    rw [hwF b hb]
  have h1 : Nat.card ((H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K)).map ψ) =
      Nat.card ↥(H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K)) :=
    Subgroup.card_map_of_injective e.permCongrHom.injective
  rw [← h1]
  exact (Subgroup.card_dvd_of_le hle).trans (card_range_semilinearPerm_dvd hFcard)

end U3C1Next

end CFSG.SeitzReduction.RankOne
