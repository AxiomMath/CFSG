module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdNormalizer
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdAct

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

open scoped commutatorElement

namespace WreathCase

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X}

@[expose] noncomputable def conjT (H : WreathCase t Sg V K) :
    normalizer (K : Set X) →* normalizer (K : Set X) where
  toFun y := ⟨t * y * t⁻¹, H.conj_t_mem_normalizer y.2⟩
  map_one' := by
    ext
    simp
  map_mul' y z := by
    ext
    simp [mul_assoc]

@[simp] theorem coe_conjT (H : WreathCase t Sg V K) (y : normalizer (K : Set X)) :
    ((conjT H y : normalizer (K : Set X)) : X) = t * y * t⁻¹ := rfl

private theorem wt_map_conj_le_centralizer (H : WreathCase t Sg V K) :
    K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set X) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact H.comm

private theorem wt_abar_le_layer (H : WreathCase t Sg V K) :
    (⁅Sg, Sg⁆ : Subgroup X) ≤ CFSG.layer X := by
  intro g hg
  change g ∈ ((⁅Sg, Sg⁆ : Subgroup X) : Set X) at hg
  rw [H.diag] at hg
  simp only [Set.mem_setOf_eq] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  rw [H.layer_eq]
  have hk' : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := by
    rw [← MulAut.conj_apply]
    exact Subgroup.mem_map_of_mem _ hk
  exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hk')

theorem conjT_conjT (H : WreathCase t Sg V K) (y : normalizer (K : Set X)) :
    conjT H (conjT H y) = y := by
  ext
  simp only [coe_conjT]
  exact H.conj_conj (y : X)

@[expose] noncomputable def theta (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) :
    normalizer (K : Set X) →* Perm (Fin 8) × Perm (Fin 8) :=
  (actPerm K e).prod ((actPerm K e).comp (conjT H))

theorem theta_apply (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    (y : normalizer (K : Set X)) :
    theta H e y = (actPerm K e y, actPerm K e (conjT H y)) := rfl

theorem theta_conjT (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    (y : normalizer (K : Set X)) : theta H e (conjT H y) = (theta H e y).swap := by
  simp [theta_apply, conjT_conjT]

theorem mem_ker_theta_iff (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) (y : normalizer (K : Set X)) :
    y ∈ (theta H e).ker ↔ (y : X) ∈ centralizer (CFSG.layer X : Set X) := by
  rw [MonoidHom.mem_ker, theta_apply, Prod.mk_eq_one]
  constructor
  · rintro ⟨h1, h2⟩
    rw [H.mem_centralizer_layer_iff]
    exact ⟨mem_centralizer_of_actPerm_eq_one e H.commutator_eq y h1,
      by simpa using mem_centralizer_of_actPerm_eq_one e H.commutator_eq (conjT H y) h2⟩
  · intro h
    rw [H.mem_centralizer_layer_iff] at h
    exact ⟨actPerm_of_mem_centralizer e y h.1,
      actPerm_of_mem_centralizer e _ (by rw [coe_conjT]; exact h.2)⟩

theorem card_ker_theta (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) :
    Nat.card (theta H e).ker = Nat.card (centralizer (CFSG.layer X : Set X)) := by
  let f : (theta H e).ker → centralizer (CFSG.layer X : Set X) :=
    fun y => ⟨(y : X), (mem_ker_theta_iff H e y).1 y.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro y z h
      have h1 : ((f y : centralizer (CFSG.layer X : Set X)) : X) =
          ((f z : centralizer (CFSG.layer X : Set X)) : X) :=
        congrArg (fun w : centralizer (CFSG.layer X : Set X) => (w : X)) h
      exact Subtype.ext (Subtype.ext h1)
    · intro z
      refine ⟨⟨⟨(z : X), H.centralizer_layer_le_normalizer z.2⟩,
        (mem_ker_theta_iff H e _).2 z.2⟩, ?_⟩
      exact Subtype.ext rfl
  exact Nat.card_congr (Equiv.ofBijective f hbij)

theorem theta_mk_K (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    (k : K) :
    theta H e ⟨(k : X), Subgroup.le_normalizer k.2⟩ =
      (((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)), 1) := by
  apply Prod.ext
  · rw [theta_apply]
    exact actPerm_of_mem e k (Subgroup.le_normalizer k.2)
  · rw [theta_apply]
    refine actPerm_of_mem_centralizer e _ ?_
    rw [coe_conjT, ← MulAut.conj_apply]
    exact wt_map_conj_le_centralizer H (Subgroup.mem_map_of_mem _ k.2)

theorem theta_mk_map (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    (k : K) :
    theta H e ⟨t * (k : X) * t⁻¹, H.conj_t_mem_normalizer (Subgroup.le_normalizer k.2)⟩ =
      (1, ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8))) := by
  rw [theta_apply]
  refine Prod.ext ?_ ?_
  · refine actPerm_of_mem_centralizer e _ ?_
    show t * (k : X) * t⁻¹ ∈ centralizer (K : Set X)
    rw [← MulAut.conj_apply]
    exact wt_map_conj_le_centralizer H (Subgroup.mem_map_of_mem _ k.2)
  · have hconj : conjT H ⟨t * (k : X) * t⁻¹,
        H.conj_t_mem_normalizer (Subgroup.le_normalizer k.2)⟩ =
        ⟨(k : X), Subgroup.le_normalizer k.2⟩ := by
      ext
      rw [coe_conjT]
      exact H.conj_conj (k : X)
    rw [hconj]
    exact actPerm_of_mem e k (Subgroup.le_normalizer k.2)

theorem alt_prod_alt_le_range (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) :
    ∀ a ∈ alternatingGroup (Fin 8), ∀ b ∈ alternatingGroup (Fin 8), (a, b) ∈ (theta H e).range := by
  intro a ha b hb
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective (e.symm ⟨a, ha⟩)
  obtain ⟨x₂, hx₂⟩ := QuotientGroup.mk_surjective (e.symm ⟨b, hb⟩)
  have hmk₁ : ((e (QuotientGroup.mk x₁) : alternatingGroup (Fin 8)) : Perm (Fin 8)) = a := by
    rw [hx₁, MulEquiv.apply_symm_apply]
  have hmk₂ : ((e (QuotientGroup.mk x₂) : alternatingGroup (Fin 8)) : Perm (Fin 8)) = b := by
    rw [hx₂, MulEquiv.apply_symm_apply]
  have h1 : (a, 1) ∈ (theta H e).range := by
    refine MonoidHom.mem_range.mpr ⟨⟨(x₁ : X), Subgroup.le_normalizer x₁.2⟩, ?_⟩
    rw [theta_mk_K H e x₁, hmk₁]
  have h2 : (1, b) ∈ (theta H e).range := by
    refine MonoidHom.mem_range.mpr
      ⟨⟨t * (x₂ : X) * t⁻¹, H.conj_t_mem_normalizer (Subgroup.le_normalizer x₂.2)⟩, ?_⟩
    rw [theta_mk_map H e x₂, hmk₂]
  have hmul := (theta H e).range.mul_mem h1 h2
  simpa using hmul

theorem exists_odd_odd (H : WreathCase t Sg V K) (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) :
    ∃ g ∈ (theta H e).range, sign g.1 = -1 ∧ sign g.2 = -1 := by
  classical
  obtain ⟨σ, hσSg, hσnotA⟩ := H.shape.exists_mem_sg_not_mem_abar
  have hσt : σ * t = t * σ :=
    Subgroup.mem_centralizer_singleton_iff.mp (H.shape.sg_le_centralizer hσSg)
  let y₀ : X := if σ ∈ normalizer (K : Set X) then σ else σ * t
  have hy₀N : y₀ ∈ normalizer (K : Set X) := by
    by_cases hσN : σ ∈ normalizer (K : Set X)
    · have hy0 : y₀ = σ := by simp [y₀, hσN]
      rw [hy0]; exact hσN
    · have hx : Xor (σ * t ∈ normalizer (K : Set X)) (σ ∈ normalizer (K : Set X)) :=
        H.mem_normalizer_xor σ
      rw [xor_def] at hx
      rcases hx with ⟨h, _⟩ | ⟨h, _⟩
      · have hy0 : y₀ = σ * t := by simp [y₀, hσN]
        rw [hy0]; exact h
      · exact absurd h hσN
  have hy₀t : y₀ * t = t * y₀ := by
    by_cases hσN : σ ∈ normalizer (K : Set X)
    · have hy0 : y₀ = σ := by simp [y₀, hσN]
      rw [hy0]; exact hσt
    · have hy0 : y₀ = σ * t := by simp [y₀, hσN]
      rw [hy0]
      calc (σ * t) * t = σ * (t * t) := by rw [mul_assoc]
        _ = σ := by rw [H.t_mul_t, mul_one]
        _ = t * (σ * t) := by rw [← mul_assoc, hσt.symm, mul_assoc, H.t_mul_t, mul_one]
  let y : normalizer (K : Set X) := ⟨y₀, hy₀N⟩
  have hyconj : conjT H y = y := by
    ext
    rw [coe_conjT]
    calc t * y₀ * t⁻¹ = y₀ * t * t⁻¹ := by rw [hy₀t.symm]
      _ = y₀ := by simp
  let π : Perm (Fin 8) := actPerm K e y
  have hThetay : theta H e y = (π, π) := by
    rw [theta_apply, hyconj]
  have hsign : sign π = -1 := by
    by_contra hne
    have hπ1 : sign π = 1 := (Int.units_eq_one_or (sign π)).resolve_right hne
    have hπA : π ∈ alternatingGroup (Fin 8) := mem_alternatingGroup.mpr hπ1
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨π, hπA⟩)
    have hkπ : ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) = π := by
      rw [hk, MulEquiv.apply_symm_apply]
    let d : X := (k : X) * (t * (k : X) * t⁻¹)
    have hdA : d ∈ (⁅Sg, Sg⁆ : Subgroup X) := by
      change d ∈ ((⁅Sg, Sg⁆ : Subgroup X) : Set X)
      rw [H.diag]
      exact ⟨(k : X), k.2, rfl⟩
    have hdN : d ∈ normalizer (K : Set X) :=
      mul_mem (Subgroup.le_normalizer k.2)
        (H.conj_t_mem_normalizer (Subgroup.le_normalizer k.2))
    let dk : normalizer (K : Set X) := ⟨d, hdN⟩
    have hkk' : (t * (k : X) * t⁻¹) * (k : X) = (k : X) * (t * (k : X) * t⁻¹) := by
      have hk' : t * (k : X) * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := by
        rw [← MulAut.conj_apply]
        exact Subgroup.mem_map_of_mem _ k.2
      exact Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp H.comm) k.2) _ hk'
    have hconj : t * d * t⁻¹ = d := by
      calc t * d * t⁻¹
          = (t * (k : X) * t⁻¹) * (t * (t * (k : X) * t⁻¹) * t⁻¹) := by
            simp only [d]; group
        _ = (t * (k : X) * t⁻¹) * (k : X) := by rw [H.conj_conj]
        _ = (k : X) * (t * (k : X) * t⁻¹) := hkk'
        _ = d := by simp only [d]
    have hdt : t * d = d * t := by
      calc t * d = t * d * t⁻¹ * t := by group
        _ = d * t := by rw [hconj]
    have hprod : dk = (⟨(k : X), Subgroup.le_normalizer k.2⟩ : normalizer (K : Set X)) *
        ⟨t * (k : X) * t⁻¹, H.conj_t_mem_normalizer (Subgroup.le_normalizer k.2)⟩ := by
      ext; rfl
    have hTheta_d : theta H e dk = (π, π) := by
      rw [hprod, map_mul, theta_mk_K H e k, theta_mk_map H e k]
      simp [hkπ]
    have hker : y * dk⁻¹ ∈ (theta H e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hThetay, hTheta_d]
      simp
    have hcent : y₀ * d⁻¹ ∈ centralizer (CFSG.layer X : Set X) := by
      have h := (mem_ker_theta_iff H e (y * dk⁻¹)).mp hker
      simpa [y, dk, d] using h
    have hAle : (⁅Sg, Sg⁆ : Subgroup X) ≤ CFSG.layer X := wt_abar_le_layer H
    have hcommA : y₀ * d⁻¹ ∈ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) :=
      Subgroup.centralizer_le (fun x hx => hAle hx) hcent
    have hdtinv : t * d⁻¹ = d⁻¹ * t :=
      ((commute_iff_eq t d).mpr hdt).inv_right.eq
    have hcommt : y₀ * d⁻¹ ∈ centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y₀ * d⁻¹) * t = y₀ * (d⁻¹ * t) := by rw [mul_assoc]
        _ = y₀ * (t * d⁻¹) := by rw [hdtinv]
        _ = (y₀ * t) * d⁻¹ := by rw [mul_assoc]
        _ = (t * y₀) * d⁻¹ := by rw [hy₀t]
        _ = t * (y₀ * d⁻¹) := by rw [mul_assoc]
    have hV : y₀ * d⁻¹ ∈ V := by
      rw [← H.shape.centralizer_abar_inf_centralizer]
      exact ⟨hcommA, hcommt⟩
    have hdSg : d ∈ Sg := Subgroup.commutator_le_self Sg hdA
    have hSgσ : σ * d⁻¹ ∈ Sg := Sg.mul_mem hσSg (Sg.inv_mem hdSg)
    have hσd : σ = d := by
      by_cases hσN : σ ∈ normalizer (K : Set X)
      · have hy0 : y₀ = σ := by simp [y₀, hσN]
        have hVσ : σ * d⁻¹ ∈ V := by rwa [hy0] at hV
        have hbot : σ * d⁻¹ ∈ (V ⊓ Sg : Subgroup X) := ⟨hVσ, hSgσ⟩
        rw [H.shape.inf_eq] at hbot
        have hone : σ * d⁻¹ = 1 := Subgroup.mem_bot.mp hbot
        have h := congrArg (fun z : X => z * d) hone
        simpa [mul_assoc] using h
      · have hy0 : y₀ = σ * t := by simp [y₀, hσN]
        have hV' : (σ * t) * d⁻¹ ∈ V := by rwa [hy0] at hV
        have hVσ : σ * d⁻¹ ∈ V := by
          have heq : σ * d⁻¹ = ((σ * t) * d⁻¹) * t⁻¹ := by
            calc σ * d⁻¹ = σ * (t * d⁻¹) * t⁻¹ := by rw [hdtinv]; group
              _ = ((σ * t) * d⁻¹) * t⁻¹ := by group
          rw [heq]
          exact V.mul_mem hV' (V.inv_mem H.shape.mem_v)
        have hbot : σ * d⁻¹ ∈ (V ⊓ Sg : Subgroup X) := ⟨hVσ, hSgσ⟩
        rw [H.shape.inf_eq] at hbot
        have hone : σ * d⁻¹ = 1 := Subgroup.mem_bot.mp hbot
        have h := congrArg (fun z : X => z * d) hone
        simpa [mul_assoc] using h
    rw [← hσd] at hdA
    exact hσnotA hdA
  exact ⟨theta H e y, MonoidHom.mem_range.mpr ⟨y, rfl⟩,
    by rw [hThetay]; exact hsign, by rw [hThetay]; exact hsign⟩

theorem card_eq_two_mul_card_mul_card_range [Finite X] (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) :
    Nat.card X = 2 * Nat.card (centralizer (CFSG.layer X : Set X)) *
      Nat.card (theta H e).range := by
  have hN : Nat.card (normalizer (K : Set X)) =
      Nat.card (theta H e).ker * Nat.card (theta H e).range :=
    (card_ker_mul_card_range (theta H e)).symm
  have hX : (normalizer (K : Set X)).index * Nat.card (normalizer (K : Set X)) = Nat.card X :=
    index_mul_card _
  rw [← hX, H.normalizer_index_eq_two, hN, card_ker_theta H e]
  ring

end WreathCase

end CFSG.OddStandard.AltStdSec.SwapPartner