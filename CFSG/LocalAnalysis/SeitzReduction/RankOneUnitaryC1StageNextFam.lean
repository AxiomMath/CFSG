module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageNextBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchAffine

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

structure U3C1Next (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T : Subgroup G) (d : G) (V U U₁ : Subgroup G) (k : ℕ) (K : Type) [Field K] [Fintype K]
    [CharP K 2] (v : G → K) (μ : K) : Prop where
  stage : U3C1Stage G L f t T d V U U₁ k
  card_K : Fintype.card K = 2 ^ f
  coords : U3A₁Coords (szA₁ (szT₁ L T)) d v μ
  gen : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w
  mu : U₁ ≤ centralizer (V : Set G)
  lam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))
  nu : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}
  (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem V_le_V₁ : V ≤ U₁ ⊓ centralizer (szT₁ L T : Set G) := H.stage.V_le_V₁

theorem V₁_le_U : U₁ ⊓ centralizer (szT₁ L T : Set G) ≤ U := inf_le_left.trans H.stage.U₁_le

theorem V₁_comm {w w' : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) : w * w' = w' * w :=
  H.stage.V₁_comm H.mu H.lam w hw w' hw'

theorem X_mul {w w' : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w * w') ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) + v (w' ^ 2 ^ (k + 1)) :=
  H.stage.X_mul H.card_K H.coords H.mu H.lam hw hw'

theorem X_eq_iff {w w' : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v (w ^ 2 ^ (k + 1)) = v (w' ^ 2 ^ (k + 1)) ↔ w⁻¹ * w' ∈ V :=
  H.stage.X_eq_iff H.card_K H.coords H.mu H.lam H.nu hw hw'

noncomputable def sec (s : K) : G :=
  (H.stage.X_surj H.card_K H.coords H.gen H.lam H.nu s).choose

theorem sec_mem (s : K) : H.sec s ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
  (H.stage.X_surj H.card_K H.coords H.gen H.lam H.nu s).choose_spec.1

theorem sec_X (s : K) : v (H.sec s ^ 2 ^ (k + 1)) = s :=
  (H.stage.X_surj H.card_K H.coords H.gen H.lam H.nu s).choose_spec.2

noncomputable def fam (s : K) : Subgroup G := V ⊔ zpowers (H.sec s * t)

theorem mul_t_mem_normalizer_V {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    w * t ∈ normalizer (V : Set G) :=
  H.stage.U_le_normalizer_V (mul_mem (H.V₁_le_U hw) H.stage.t_mem_U)

theorem sup_zpowers_eq {w w' : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (hV : w⁻¹ * w' ∈ V) :
    V ⊔ zpowers (w * t) = V ⊔ zpowers (w' * t) := by
  have hc := H.V₁_comm hw hw'
  refine le_antisymm (sup_le le_sup_left (zpowers_le.mpr ?_))
    (sup_le le_sup_left (zpowers_le.mpr ?_))
  · have e : w * t = (w⁻¹ * w')⁻¹ * (w' * t) := by
      calc w * t = w'⁻¹ * (w' * w) * t := by group
        _ = w'⁻¹ * (w * w') * t := by rw [hc]
        _ = (w⁻¹ * w')⁻¹ * (w' * t) := by group
    rw [e]
    exact mul_mem (mem_sup_left (inv_mem hV)) (mem_sup_right (mem_zpowers _))
  · have e : w' * t = (w⁻¹ * w') * (w * t) := by
      calc w' * t = w⁻¹ * (w * w') * t := by group
        _ = w⁻¹ * (w' * w) * t := by rw [hc]
        _ = (w⁻¹ * w') * (w * t) := by group
    rw [e]
    exact mul_mem (mem_sup_left hV) (mem_sup_right (mem_zpowers _))

theorem fam_eq {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    V ⊔ zpowers (w * t) = H.fam (v (w ^ 2 ^ (k + 1))) :=
  H.sup_zpowers_eq hw (H.sec_mem _) ((H.X_eq_iff hw (H.sec_mem _)).mp (H.sec_X _).symm)

theorem fam_injective : Function.Injective H.fam := by
  intro s s' heq
  set w := H.sec s with hwdef
  set w' := H.sec s' with hw'def
  have hw := H.sec_mem s
  have hw' := H.sec_mem s'
  have hmem : w * t ∈ V ⊔ zpowers (w' * t) := by
    have : w * t ∈ H.fam s := mem_sup_right (mem_zpowers _)
    rwa [heq] at this
  have hsq : w' * t * (w' * t) = 1 := by rw [← sq]; exact H.nu w' hw'
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers hsq (H.mul_t_mem_normalizer_V hw')
    hmem with h1 | h1
  · exfalso
    refine H.stage.t_not_mem ?_
    have e : t = w⁻¹ * (w * t) := by group
    rw [e]
    exact mul_mem (inv_mem (mem_inf.mp hw).1) (H.stage.V_le_U₁ h1)
  · have e : w * t * (w' * t) = w * w'⁻¹ := by
      calc w * t * (w' * t) = w * (t * w' * t⁻¹) := by rw [H.stage.t_inv]; group
        _ = w * w'⁻¹ := by rw [H.stage.inv_V₁ H.nu hw']
    rw [e] at h1
    have h2 : w⁻¹ * w' ∈ V := by
      have := inv_mem h1
      rwa [mul_inv_rev, inv_inv, H.V₁_comm hw' (inv_mem hw)] at this
    have h3 := (H.X_eq_iff hw hw').mpr h2
    rwa [H.sec_X, H.sec_X] at h3

theorem conj_mem_V₁ {n : G} (hn : n ∈ normalizer (U : Set G)) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    n * w * n⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
  (mem_normalizer_iff.mp (H.stage.normalizer_U_le_normalizer_V₁ H.mu H.lam H.nu hn) w).mp hw

theorem comm_t_mem_V₁ {n : G} (hn : n ∈ normalizer (U : Set G)) :
    n * t * n⁻¹ * t⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
  H.stage.comm_t_mem_V₁_of_normalizer H.lam H.nu hn

theorem map_conj_sup_zpowers {n : G} (hn : n ∈ normalizer (U : Set G)) (w : G) :
    (V ⊔ zpowers (w * t)).map (MulAut.conj n).toMonoidHom =
      V ⊔ zpowers ((n * w * n⁻¹) * (n * t * n⁻¹ * t⁻¹) * t) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers,
    SzC1.map_conj_eq_of_mem_normalizer (H.stage.normalizer_U_le_normalizer_V hn)]
  congr 2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem fam_invariant : ∀ n ∈ normalizer (U : Set G), ∀ s : K, ∃ s' : K,
    (H.fam s).map (MulAut.conj n).toMonoidHom = H.fam s' := by
  intro n hn s
  refine ⟨v (((n * H.sec s * n⁻¹) * (n * t * n⁻¹ * t⁻¹)) ^ 2 ^ (k + 1)), ?_⟩
  rw [fam, H.map_conj_sup_zpowers hn]
  exact H.fam_eq (mul_mem (H.conj_mem_V₁ hn (H.sec_mem s)) (H.comm_t_mem_V₁ hn))

noncomputable def perm : normalizer (U : Set G) →* Equiv.Perm K :=
  SzC1.familyPerm H.fam H.fam_invariant H.fam_injective

theorem perm_spec (n : normalizer (U : Set G)) (s : K) :
    (H.fam s).map (MulAut.conj (n : G)).toMonoidHom = H.fam (H.perm n s) :=
  SzC1.familyPerm_spec _ _ _ n s

theorem perm_apply (n : normalizer (U : Set G)) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    H.perm n (v (w ^ 2 ^ (k + 1))) = v (((n : G) * w * (n : G)⁻¹) ^ 2 ^ (k + 1)) +
      v (((n : G) * t * (n : G)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) := by
  have hn := n.2
  have hw₁ := H.conj_mem_V₁ hn hw
  have hc₁ := H.comm_t_mem_V₁ hn
  rw [← H.X_mul hw₁ hc₁]
  apply H.fam_injective
  rw [← H.perm_spec, ← H.fam_eq hw, H.map_conj_sup_zpowers hn, H.fam_eq (mul_mem hw₁ hc₁)]

theorem perm_zero (n : normalizer (U : Set G)) :
    H.perm n 0 = v (((n : G) * t * (n : G)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) := by
  have e := H.perm_apply n (one_mem (U₁ ⊓ centralizer (szT₁ L T : Set G)))
  simp only [one_pow, mul_one, mul_inv_cancel, H.coords.v_one, zero_add] at e
  exact e

theorem d_mem_normalizer_U : d ∈ normalizer (U : Set G) := by
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.mp H.stage.d_norm.2
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  rcases H.stage.mem_or_mul_t_mem hx with h1 | h1
  · exact H.stage.U₁_le (H.stage.conj_d_mem_U₁ h1)
  · have e : d⁻¹ * x * d = (d⁻¹ * (x * t) * d) * t := by
      rw [show d⁻¹ * (x * t) * d * t = d⁻¹ * x * (t * d) * t by group, ← hdt]
      rw [show d⁻¹ * x * (d * t) * t = d⁻¹ * x * d * (t * t) by group, H.stage.t_mul_self,
        mul_one]
    rw [e]
    exact mul_mem (H.stage.U₁_le (H.stage.conj_d_mem_U₁ h1)) H.stage.t_mem_U

theorem perm_d_inv (s : K) :
    H.perm ⟨d⁻¹, inv_mem H.d_mem_normalizer_U⟩ s = μ * s := by
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.mp H.stage.d_norm.2
  have e1 : d⁻¹ * t * d⁻¹⁻¹ * t⁻¹ = 1 := by
    rw [inv_inv, show d⁻¹ * t * d = t by rw [mul_assoc, ← hdt, inv_mul_cancel_left],
      mul_inv_cancel]
  conv_lhs => rw [← H.sec_X s]
  rw [H.perm_apply _ (H.sec_mem s)]
  show v ((d⁻¹ * H.sec s * d⁻¹⁻¹) ^ 2 ^ (k + 1)) + v ((d⁻¹ * t * d⁻¹⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = _
  rw [e1, one_pow, H.coords.v_one, add_zero, conj_pow, inv_inv,
    H.coords.conj _ (H.stage.pow_mem_szA₁_V₁ (H.sec_mem s)), H.sec_X]

theorem X_conj_eq_of_mem_U {x : G} (hx : x ∈ U) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((x * w * x⁻¹) ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) := by
  have hcV := H.stage.comm_mem_V x hx w (H.V₁_le_U hw)
  have hcV₁ := H.V_le_V₁ hcV
  have e : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
  have hxw : x * w * x⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
    rw [e]
    exact mul_mem hcV₁ hw
  refine ((H.X_eq_iff hw hxw).mpr ?_).symm
  have e2 : w⁻¹ * (x * w * x⁻¹) = x * w * x⁻¹ * w⁻¹ := by
    calc w⁻¹ * (x * w * x⁻¹) = w⁻¹ * ((x * w * x⁻¹ * w⁻¹) * w) := by group
      _ = w⁻¹ * (w * (x * w * x⁻¹ * w⁻¹)) := by rw [H.V₁_comm hcV₁ hw]
      _ = x * w * x⁻¹ * w⁻¹ := by group
  rw [e2]
  exact hcV

theorem perm_eq_one_of_mem_U (n : normalizer (U : Set G)) (hn : (n : G) ∈ U) : H.perm n = 1 := by
  refine Equiv.ext fun s => ?_
  rw [Equiv.Perm.one_apply]
  conv_lhs => rw [← H.sec_X s]
  rw [H.perm_apply n (H.sec_mem s), H.X_conj_eq_of_mem_U hn (H.sec_mem s),
    H.stage.X_eq_zero_of_mem_V H.card_K H.coords (H.stage.comm_t_mem hn), add_zero, H.sec_X]

theorem perm_affine (n : normalizer (U : Set G)) :
    ∃ ℓ : K →+ K, ∀ s, H.perm n s = H.perm n 0 + ℓ s := by
  have hn := n.2
  refine ⟨AddMonoidHom.mk' (fun s => v (((n : G) * H.sec s * (n : G)⁻¹) ^ 2 ^ (k + 1)))
    fun s s' => ?_, fun s => ?_⟩
  · have hw := H.sec_mem s
    have hw' := H.sec_mem s'
    have hww := mul_mem hw hw'
    have h1 : v (H.sec (s + s') ^ 2 ^ (k + 1)) = v ((H.sec s * H.sec s') ^ 2 ^ (k + 1)) := by
      rw [H.sec_X, H.X_mul hw hw', H.sec_X, H.sec_X]
    have h2 := (H.X_eq_iff (H.sec_mem (s + s')) hww).mp h1
    have h3 : ((n : G) * H.sec (s + s') * (n : G)⁻¹)⁻¹ *
        ((n : G) * (H.sec s * H.sec s') * (n : G)⁻¹) ∈ V := by
      have := (mem_normalizer_iff.mp (H.stage.normalizer_U_le_normalizer_V hn) _).mp h2
      rw [show (n : G) * ((H.sec (s + s'))⁻¹ * (H.sec s * H.sec s')) * (n : G)⁻¹ =
        ((n : G) * H.sec (s + s') * (n : G)⁻¹)⁻¹ *
          ((n : G) * (H.sec s * H.sec s') * (n : G)⁻¹) by group] at this
      exact this
    have h4 := (H.X_eq_iff (H.conj_mem_V₁ hn (H.sec_mem (s + s'))) (H.conj_mem_V₁ hn hww)).mpr h3
    show v (((n : G) * H.sec (s + s') * (n : G)⁻¹) ^ 2 ^ (k + 1)) =
      v (((n : G) * H.sec s * (n : G)⁻¹) ^ 2 ^ (k + 1)) +
        v (((n : G) * H.sec s' * (n : G)⁻¹) ^ 2 ^ (k + 1))
    rw [h4, show (n : G) * (H.sec s * H.sec s') * (n : G)⁻¹ =
      ((n : G) * H.sec s * (n : G)⁻¹) * ((n : G) * H.sec s' * (n : G)⁻¹) by group,
      H.X_mul (H.conj_mem_V₁ hn hw) (H.conj_mem_V₁ hn hw')]
  · conv_lhs => rw [← H.sec_X s]
    rw [H.perm_apply n (H.sec_mem s), H.perm_zero n, AddMonoidHom.mk'_apply, add_comm]

theorem exists_pow_eq_of_mem_szA₁ {b : G} (hb : b ∈ szA₁ (szT₁ L T)) :
    ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), w ^ 2 ^ (k + 1) = b := by
  obtain ⟨w, hw, hwb⟩ := H.stage.X_surj H.card_K H.coords H.gen H.lam H.nu (v b)
  exact ⟨w, hw, H.coords.inj _ (H.stage.pow_mem_szA₁_V₁ hw) _ hb hwb⟩

theorem conj_mem_szA₁ {n : G} (hn : n ∈ normalizer (U : Set G)) {b : G}
    (hb : b ∈ szA₁ (szT₁ L T)) : n * b * n⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hT := H.stage.normalizer_U_le_normalizer_T₁ H.mu H.lam H.nu hn
  obtain ⟨hbT, hbC⟩ := mem_szA₁.mp hb
  refine mem_szA₁.mpr ⟨(mem_normalizer_iff.mp hT b).mp hbT, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n ∈ szT₁ L T := by
    simpa using (mem_normalizer_iff.mp (inv_mem hT) y).mp hy
  have e := mem_centralizer_iff.mp hbC _ hy'
  calc y * (n * b * n⁻¹) = n * ((n⁻¹ * y * n) * b) * n⁻¹ := by group
    _ = n * (b * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
    _ = n * b * n⁻¹ * y := by group

theorem conj_szA₁_of_X_conj {n : G} (hn : n ∈ normalizer (U : Set G))
    (hX : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      v ((n * w * n⁻¹) ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1))) :
    ∀ b ∈ szA₁ (szT₁ L T), n * b * n⁻¹ = b := by
  intro b hb
  obtain ⟨w, hw, rfl⟩ := H.exists_pow_eq_of_mem_szA₁ hb
  refine H.coords.inj _ (H.conj_mem_szA₁ hn hb) _ hb ?_
  rw [← conj_pow, hX w hw]

end U3C1Next

end CFSG.SeitzReduction.RankOne
