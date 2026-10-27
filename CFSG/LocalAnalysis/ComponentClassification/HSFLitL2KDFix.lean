module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDBase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KE

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2KD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open L2K

variable {F : Type} [Field F] [Finite F]

theorem sqLeft_conj_iff (x y : PGammaL2 F) : SqLeft (y * x * y⁻¹) ↔ SqLeft x := by
  rw [sqLeft_mul, sqLeft_mul, sqLeft_inv]
  tauto

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}

theorem act_frame (e e' : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (g : X) :
    act A e' g = (semilinearEquivAut F).symm (e.symm.trans e') * act A e g *
      ((semilinearEquivAut F).symm (e.symm.trans e'))⁻¹ := by
  by_cases hg : g ∈ centralizer ({t} : Set X)
  · rw [act_of_mem _ hg, act_of_mem _ hg]
    exact autEquiv_eq_conj e' e _
  · simp [act, hg]

theorem sqLeft_act_iff (e e' : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (g : X) :
    SqLeft (act A e' g) ↔ SqLeft (act A e g) := by
  rw [act_frame e e', sqLeft_conj_iff]

omit [Finite X] in
theorem L2E_comm {z w k : X} (hzw : z * w = w * z) (hzt : z * t = t * z) (hzk : z * k = k * z)
    (hwt : w * t = t * w) (hwk : w * k = k * w) (htk : t * k = k * t) {a b : X}
    (ha : a ∈ L2E z w t k) (hb : b ∈ L2E z w t k) : a * b = b * a := by
  have hcomm : ({z, w, t, k} : Set X).Pairwise Commute := by
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact hzw | exact hzw.symm | exact hzt | exact hzt.symm | exact hzk | exact hzk.symm
      | exact hwt | exact hwt.symm | exact hwk | exact hwk.symm | exact htk | exact htk.symm
  have h : (⟨a, ha⟩ : closure ({z, w, t, k} : Set X)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    (isMulCommutative_closure hcomm).is_comm.comm _ _
  exact congrArg Subtype.val h

theorem mem_L2E_one {G : Type} [Group G] (z w s k : G) : z ∈ L2E z w s k :=
  subset_closure (by simp)

theorem mem_L2E_two {G : Type} [Group G] (z w s k : G) : w ∈ L2E z w s k :=
  subset_closure (by simp)

theorem mem_L2E_three {G : Type} [Group G] (z w s k : G) : s ∈ L2E z w s k :=
  subset_closure (by simp)

theorem mem_L2E_four {G : Type} [Group G] (z w s k : G) : k ∈ L2E z w s k :=
  subset_closure (by simp)

namespace Gens

variable (S : Gens A) (C : A.CaseKD)

theorem mem_L2E_kd {w : X} (hw : w ∈ A.R) (hw2 : w ^ 2 = 1) {g : X}
    (hg : g ∈ L2E S.z w t C.k) :
    ∃ a b c d : ℕ, a < 2 ∧ b < 2 ∧ c < 2 ∧ d < 2 ∧ g = S.z ^ a * w ^ b * t ^ c * C.k ^ d := by
  have hzC := A.T_le_centralizer S.z_mem.1
  have hwC := A.T_le_centralizer hw.1
  exact mem_closure_four S.z_sq hw2 (t_sq (A := A)) C.k_sq (S.z_comm_R hw)
    (commute_t_of_mem_C hzC) (commute_k C S.z_mem).symm (commute_t_of_mem_C hwC)
    (commute_k C hw).symm (commute_t_of_mem_C (k_mem_C C)).symm hg

theorem comm_L2E_kd {w : X} (hw : w ∈ A.R) {a b : X} (ha : a ∈ L2E S.z w t C.k)
    (hb : b ∈ L2E S.z w t C.k) : a * b = b * a :=
  L2E_comm (S.z_comm_R hw) (commute_t_of_mem_C (A.T_le_centralizer S.z_mem.1))
    (commute_k C S.z_mem).symm (commute_t_of_mem_C (A.T_le_centralizer hw.1))
    (commute_k C hw).symm (commute_t_of_mem_C (k_mem_C C)).symm ha hb

omit [Finite X] in
theorem L2E_le_T_kd {w : X} (hw : w ∈ A.R) : L2E S.z w t C.k ≤ A.T := by
  rw [L2E, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact S.z_mem.1
  · exact hw.1
  · exact A.t_mem_T
  · exact C.k_mem

end Gens

namespace Frame

variable {κ : X} (Fr : Frame A F κ)

theorem eq_one_of_conj_sq {n v : X} (hn : n ∈ centralizer ({t} : Set X))
    (hS : SqLeft (act A Fr.e n)) (hv : v ∈ Fr.V) (c : ℕ) (h : n * κ * n⁻¹ = v * t ^ c * κ) :
    v = 1 := by
  have hvR := Fr.V_le_R hv
  have hvC := L_le_C (A := A) hvR.2
  have h1 := congrArg (act A Fr.e) h
  rw [act_conj Fr.e hn Fr.κ_C, act_mul Fr.e (mul_mem hvC (pow_mem t_mem_C c)) Fr.κ_C,
    act_mul Fr.e hvC (pow_mem t_mem_C c), act_pow Fr.e t_mem_C, act_t, one_pow, mul_one,
    Fr.act_κ, act_of_mem_L Fr.e hvR.2] at h1
  obtain ⟨y, hy⟩ := hS
  rw [conj_inr_eq hy.symm, mul_left_inj] at h1
  have h2 := incl_injective F h1
  have h3 := eq_one_of_lang Fr.σσ Fr.two_ne_zero Fr.mem_K₀ (Fr.mem_V.mp hv).2 h2
  exact rho_eq_one Fr.e hvR h3

theorem right_act_k_kd (S : Gens A) (C : A.CaseKD) (hκ : κ = C.k ∨ κ = S.z * C.k) :
    (act A Fr.e C.k).right = Fr.σ := by
  rcases hκ with rfl | rfl
  · rw [Fr.act_κ]
    rfl
  · have hzC := A.T_le_centralizer S.z_mem.1
    have h : act A Fr.e C.k = (act A Fr.e S.z)⁻¹ * act A Fr.e (S.z * C.k) := by
      rw [act_mul Fr.e hzC (k_mem_C C), inv_mul_cancel_left]
    rw [h, Fr.act_κ, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      Fr.right_act_of_mem_R S.z_mem, inv_one, one_mul]
    rfl

theorem sqLeft_act_k (S : Gens A) (C : A.CaseKD) (hκ : κ = C.k ∨ κ = S.z * C.k) :
    SqLeft (act A Fr.e C.k) := by
  have hσ : SqLeft (SemidirectProduct.inr Fr.σ : PGammaL2 F) := ⟨1, by simp⟩
  rcases hκ with rfl | rfl
  · rw [Fr.act_κ]
    exact hσ
  · have hzC := A.T_le_centralizer S.z_mem.1
    have h : act A Fr.e C.k = (act A Fr.e S.z)⁻¹ * act A Fr.e (S.z * C.k) := by
      rw [act_mul Fr.e hzC (k_mem_C C), inv_mul_cancel_left]
    rw [h, Fr.act_κ, sqLeft_mul, sqLeft_inv, act_of_mem_L Fr.e S.z_mem.2]
    exact iff_of_true (sqLeft_incl _) hσ

theorem conj_eq_or_of_mem_L2E_kd (S : Gens A) (C : A.CaseKD) (hκ : κ = C.k ∨ κ = S.z * C.k)
    {w : X} (hwV : w ∈ Fr.V) (hw2 : w ^ 2 = 1) {n : X} (hn : n ∈ centralizer ({t} : Set X))
    (hS : SqLeft (act A Fr.e n)) (hnE : n * κ * n⁻¹ ∈ L2E S.z w t C.k) :
    n * κ * n⁻¹ = κ ∨ n * κ * n⁻¹ = t * κ := by
  have hwR := Fr.V_le_R hwV
  obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ := Gens.mem_L2E_kd S C hwR hw2 hnE
  have hzC := A.T_le_centralizer S.z_mem.1
  have hwC := A.T_le_centralizer hwR.1
  have hkC := k_mem_C C
  have hσ1 : Fr.σ ≠ 1 := by
    intro h
    have := Fr.orderOf_σ
    rw [h, orderOf_one] at this
    norm_num at this
  have hd1 : d = 1 := by
    have h1 := congrArg (fun g => (act A Fr.e g).right) habcd
    rw [act_conj Fr.e hn Fr.κ_C, right_conj, Fr.act_κ,
      act_mul Fr.e (mul_mem (mul_mem (pow_mem hzC a) (pow_mem hwC b)) (pow_mem t_mem_C c))
        (pow_mem hkC d),
      act_mul Fr.e (mul_mem (pow_mem hzC a) (pow_mem hwC b)) (pow_mem t_mem_C c),
      act_mul Fr.e (pow_mem hzC a) (pow_mem hwC b), act_pow Fr.e hzC, act_pow Fr.e hwC,
      act_pow Fr.e t_mem_C, act_pow Fr.e hkC, act_t, one_pow, mul_one] at h1
    change Fr.σ = (fieldProj F) (act A Fr.e S.z ^ a * act A Fr.e w ^ b * act A Fr.e C.k ^ d)
      at h1
    rw [map_mul, map_mul, map_pow, map_pow, map_pow] at h1
    change Fr.σ = (act A Fr.e S.z).right ^ a * (act A Fr.e w).right ^ b *
      (act A Fr.e C.k).right ^ d at h1
    rw [Fr.right_act_of_mem_R S.z_mem, Fr.right_act_of_mem_R hwR, Frame.right_act_k_kd Fr S C hκ,
      one_pow, one_pow, one_mul, one_mul] at h1
    by_contra hd1
    have hd0 : d = 0 := by omega
    rw [hd0, pow_zero] at h1
    exact hσ1 h1
  subst hd1
  have hzV := Fr.z_mem_V S
  have hzt : S.z * t = t * S.z := commute_t_of_mem_C hzC
  obtain ⟨v, hvV, hv⟩ : ∃ v ∈ Fr.V, n * κ * n⁻¹ = v * t ^ c * κ := by
    rw [habcd, pow_one]
    rcases hκ with h | h
    · exact ⟨S.z ^ a * w ^ b, mul_mem (pow_mem hzV a) (pow_mem hwV b), by rw [h]⟩
    · refine ⟨S.z ^ a * w ^ b * S.z, mul_mem (mul_mem (pow_mem hzV a) (pow_mem hwV b)) hzV, ?_⟩
      rw [h]
      have htc : S.z * t ^ c = t ^ c * S.z := (Commute.pow_right hzt c)
      calc S.z ^ a * w ^ b * t ^ c * C.k = S.z ^ a * w ^ b * (S.z * S.z) * t ^ c * C.k := by
            rw [← pow_two, S.z_sq, mul_one]
        _ = S.z ^ a * w ^ b * S.z * (S.z * t ^ c) * C.k := by group
        _ = S.z ^ a * w ^ b * S.z * t ^ c * (S.z * C.k) := by rw [htc]; group
  have hv1 := Frame.eq_one_of_conj_sq Fr hn hS hvV c hv
  rw [hv1, one_mul] at hv
  interval_cases c
  · left
    rw [hv, pow_zero, one_mul]
  · right
    rw [hv, pow_one]

theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {g : G} {m : ℕ} (hg : g ^ 2 ^ m = 1) :
    IsPGroup 2 (zpowers g) := by
  intro h
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h.2
  refine ⟨m, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hg, one_zpow]

theorem two_elem (S : Gens A) (C : A.CaseKD) (hκ : κ = C.k ∨ κ = S.z * C.k) {w : X}
    (hwV : w ∈ Fr.V) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) (hwz : w ≠ S.z) {g : X}
    (hgC : g ∈ centralizer ({t} : Set X)) (hgN : g ∈ normalizer (L2E S.z w t C.k : Set X))
    {m : ℕ} (hgm : g ^ 2 ^ m = 1) : SqLeft (act A Fr.e g) ∧ g * κ * g⁻¹ = κ := by
  have hwR := Fr.V_le_R hwV
  have hET := Gens.L2E_le_T_kd S C hwR
  have hE2 : IsPGroup 2 (L2E S.z w t C.k) := A.isPGroup_T.to_le hET
  have hQ : IsPGroup 2 (zpowers g ⊔ L2E S.z w t C.k : Subgroup X) :=
    (isPGroup_zpowers_of_pow hgm).to_sup_of_normal_right' hE2 (zpowers_le.mpr hgN)
  have hQC : zpowers g ⊔ L2E S.z w t C.k ≤ centralizer ({t} : Set X) :=
    sup_le (zpowers_le.mpr hgC) (hET.trans A.T_le_centralizer)
  obtain ⟨c, hcC, hcT⟩ := exists_conj_le_T (A := A) hQ hQC
  have hconjT : ∀ q ∈ (zpowers g ⊔ L2E S.z w t C.k : Subgroup X), c * q * c⁻¹ ∈ A.T :=
    fun q hq => hcT ⟨q, hq, rfl⟩
  have hhT : c * g * c⁻¹ ∈ A.T := hconjT g (mem_sup_left (mem_zpowers g))
  have hET' : ∀ e ∈ L2E S.z w t C.k, c * e * c⁻¹ ∈ A.T := fun e he => hconjT e (mem_sup_right he)
  set h := c * g * c⁻¹ with hhdef
  have hzE := mem_L2E_one S.z w t C.k
  have hwE := mem_L2E_two S.z w t C.k
  have hz2 := S.z_sq
  obtain ⟨e₀, he₀E, he₀R, hr1, hrz, hr2⟩ : ∃ e₀ ∈ L2E S.z w t C.k, e₀ ∈ A.R ∧
      c * e₀ * c⁻¹ ≠ 1 ∧ c * e₀ * c⁻¹ ≠ S.z ∧ e₀ ^ 2 = 1 := by
    have hc1 : ∀ e : X, e ≠ 1 → c * e * c⁻¹ ≠ 1 := fun e he h' => he (by
      calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
        _ = 1 := by rw [h']; group)
    by_cases hcw : c * w * c⁻¹ = S.z
    · refine ⟨S.z * w, mul_mem hzE hwE, mul_mem S.z_mem hwR, hc1 _ ?_, ?_, ?_⟩
      · intro h'
        apply hwz
        calc w = S.z⁻¹ * (S.z * w) := by group
          _ = S.z := by rw [h', mul_one, inv_eq_iff_mul_eq_one, ← pow_two, hz2]
      · intro h'
        apply S.z_ne_one
        have : c * S.z * c⁻¹ * (c * w * c⁻¹) = c * (S.z * w) * c⁻¹ := by group
        rw [h', hcw] at this
        have h1 : c * S.z * c⁻¹ = 1 := by
          calc c * S.z * c⁻¹ = c * S.z * c⁻¹ * S.z * S.z⁻¹ := by group
            _ = 1 := by rw [this, mul_inv_cancel]
        calc S.z = c⁻¹ * (c * S.z * c⁻¹) * c := by group
          _ = 1 := by rw [h1]; group
      · rw [(show Commute S.z w from S.z_comm_R hwR).mul_pow, hz2, hw2, one_mul]
    · exact ⟨w, hwE, hwR, hc1 w hw1, hcw, hw2⟩
  set r := c * e₀ * c⁻¹ with hrdef
  have hrT := hET' e₀ he₀E
  have hrL : r ∈ L := conj_mem_L (A := A) hcC he₀R.2
  have hrR : r ∈ A.R := ⟨hrT, hrL⟩
  have hr2' : r ^ 2 = 1 := by rw [hrdef, conj_pow, hr2]; group
  have hψr : ψX A r ∈ R8 := ψX_mem_R8 hrR
  have hψr2 : ψX A r ^ 2 = 1 := by rw [← ψX_pow hrT, hr2', ψX_one]
  have hψr1 : ψX A r ≠ 1 := fun h' => hr1 (eq_one_of_ψX hrR h')
  have hψrz : ψX A r ≠ z8 := fun h' => hrz (eq_of_ψX_eq hrR S.z_mem (by rw [h', S.ψ_z]))
  obtain ⟨e', he', hψre⟩ := refl_of_mem_R8 hψr hψr2 hψr1 hψrz
  have hgeE : g * e₀ * g⁻¹ ∈ L2E S.z w t C.k := (mem_normalizer_iff.mp hgN e₀).mp he₀E
  have hcomm : (h * r * h⁻¹) * r = r * (h * r * h⁻¹) := by
    have h1 := Gens.comm_L2E_kd S C hwR hgeE he₀E
    calc (h * r * h⁻¹) * r = c * ((g * e₀ * g⁻¹) * e₀) * c⁻¹ := by rw [hhdef, hrdef]; group
      _ = c * (e₀ * (g * e₀ * g⁻¹)) * c⁻¹ := by rw [h1]
      _ = r * (h * r * h⁻¹) := by rw [hhdef, hrdef]; group
  obtain ⟨u, b, hub⟩ := ψX_mem_H8 hhT
  have hb0 : dbit8 b = 0 := by
    rcases dbit8_eq b with hb | hb
    · exact hb
    · exfalso
      apply conj_refl_not_comm u b e' hb he'
      have hcT : h * r * h⁻¹ ∈ A.T := mul_mem (mul_mem hhT hrT) (inv_mem hhT)
      have := congrArg (ψX A) hcomm
      rw [ψX_mul hcT hrT, ψX_mul hrT hcT, ψX_conj hhT hrT, ← hub, hψre] at this
      exact this
  obtain ⟨r₁, hr₁, a₁, e₁, ha₁, he₁, hh₁, -⟩ := exists_eq_of_mem_T C hhT hub.symm hb0
  have hkS := Frame.sqLeft_act_k Fr S C hκ
  have hhS : SqLeft (act A Fr.e h) := by
    have hr₁C := L_le_C (A := A) hr₁.2
    rw [hh₁, act_mul Fr.e (mul_mem hr₁C (pow_mem t_mem_C a₁)) (pow_mem (k_mem_C C) e₁),
      act_mul Fr.e hr₁C (pow_mem t_mem_C a₁), act_pow Fr.e t_mem_C, act_t, one_pow, mul_one,
      act_of_mem_L Fr.e hr₁.2, act_pow Fr.e (k_mem_C C), sqLeft_mul]
    interval_cases e₁
    · simp only [pow_zero]
      exact iff_of_true (sqLeft_incl _) sqLeft_one
    · simp only [pow_one]
      exact iff_of_true (sqLeft_incl _) hkS
  have hgS : SqLeft (act A Fr.e g) := by
    have hg' : g = c⁻¹ * h * c⁻¹⁻¹ := by rw [hhdef]; group
    rw [hg', act_conj Fr.e (inv_mem hcC) (A.T_le_centralizer hhT), sqLeft_conj_iff]
    exact hhS
  refine ⟨hgS, ?_⟩
  have hκE : κ ∈ L2E S.z w t C.k := by
    rcases hκ with rfl | rfl
    · exact mem_L2E_four S.z w t C.k
    · exact mul_mem hzE (mem_L2E_four S.z w t C.k)
  have hgκE : g * κ * g⁻¹ ∈ L2E S.z w t C.k := (mem_normalizer_iff.mp hgN κ).mp hκE
  rcases Frame.conj_eq_or_of_mem_L2E_kd Fr S C hκ hwV hw2 hgC hgS hgκE with h1 | h1
  · exact h1
  · exfalso
    have hcκT := hET' κ hκE
    have hκT := hET hκE
    have hψκ : ψX A κ = aff8 u5 0 ∨ ψX A κ = aff8 u5 4 := by
      rcases hκ with rfl | rfl
      · left
        rw [ψX_k C]
      · right
        rw [ψX_mul S.z_mem.1 C.k_mem, S.ψ_z, ψX_k C, aff8_mul]
        rfl
    obtain ⟨u', b', hub'⟩ := ψX_mem_H8 hcκT
    have hbits : dbit8 b' = 0 ∧ fbit8 u' = 1 := by
      rcases hψκ with hψκ | hψκ
      · obtain ⟨h1, h2⟩ := bits_conj hcC hκT hcκT hψκ hub'.symm
        exact ⟨by rw [h1]; decide, by rw [h2]; decide⟩
      · obtain ⟨h1, h2⟩ := bits_conj hcC hκT hcκT hψκ hub'.symm
        exact ⟨by rw [h1]; decide, by rw [h2]; decide⟩
    obtain ⟨r₂, hr₂, a₂, e₂, ha₂, he₂, hκ₂, he₂1⟩ :=
      exists_eq_of_mem_T C hcκT hub'.symm hbits.1
    have he₂' : e₂ = 1 := he₂1 hbits.2
    subst he₂'
    rw [pow_one] at hκ₂
    have hhk : h * C.k * h⁻¹ = C.k := by
      have hkr : C.k * r₁ = r₁ * C.k := commute_k C hr₁
      have hkt : C.k * t ^ a₁ = t ^ a₁ * C.k :=
        (Commute.pow_right (commute_t_of_mem_C (k_mem_C C)) a₁)
      have hkk : C.k * C.k ^ e₁ = C.k ^ e₁ * C.k := (Commute.self_pow C.k e₁).eq
      rw [hh₁]
      calc r₁ * t ^ a₁ * C.k ^ e₁ * C.k * (r₁ * t ^ a₁ * C.k ^ e₁)⁻¹
          = r₁ * t ^ a₁ * (C.k ^ e₁ * C.k) * (C.k ^ e₁)⁻¹ * (t ^ a₁)⁻¹ * r₁⁻¹ := by group
        _ = r₁ * (t ^ a₁ * C.k) * (t ^ a₁)⁻¹ * r₁⁻¹ := by rw [← hkk]; group
        _ = r₁ * C.k * r₁⁻¹ := by rw [← hkt]; group
        _ = C.k := by rw [← hkr]; group
    have hht : h * t = t * h := commute_t_of_mem_C (A.T_le_centralizer hhT)
    have hct : c * t * c⁻¹ = t := by
      rw [commute_t_of_mem_C hcC, mul_inv_cancel_right]
    have h2 : h * (c * κ * c⁻¹) * h⁻¹ = t * (c * κ * c⁻¹) := by
      calc h * (c * κ * c⁻¹) * h⁻¹ = c * (g * κ * g⁻¹) * c⁻¹ := by rw [hhdef]; group
        _ = (c * t * c⁻¹) * (c * κ * c⁻¹) := by rw [h1]; group
        _ = t * (c * κ * c⁻¹) := by rw [hct]
    rw [hκ₂] at h2
    have h3 : h * (r₂ * t ^ a₂ * C.k) * h⁻¹ = h * r₂ * h⁻¹ * t ^ a₂ * C.k := by
      have hht' : h * t ^ a₂ = t ^ a₂ * h := (Commute.pow_right hht a₂)
      calc h * (r₂ * t ^ a₂ * C.k) * h⁻¹ = h * r₂ * (t ^ a₂ * h⁻¹) * (h * C.k * h⁻¹) := by
            group
        _ = h * r₂ * h⁻¹ * t ^ a₂ * C.k := by
          rw [hhk, show t ^ a₂ * h⁻¹ = h⁻¹ * t ^ a₂ by
            calc t ^ a₂ * h⁻¹ = h⁻¹ * (h * t ^ a₂) * h⁻¹ := by group
              _ = h⁻¹ * (t ^ a₂ * h) * h⁻¹ := by rw [hht']
              _ = h⁻¹ * t ^ a₂ := by group]
          group
    rw [h3] at h2
    have h4 : h * r₂ * h⁻¹ = t * r₂ := by
      have := congrArg (fun y => y * C.k⁻¹ * (t ^ a₂)⁻¹) h2
      simpa [mul_assoc] using this
    have htL : t ∈ L := by
      have hhrL : h * r₂ * h⁻¹ ∈ L := conj_mem_L (A := A) (A.T_le_centralizer hhT) hr₂.2
      have : t = h * r₂ * h⁻¹ * r₂⁻¹ := by rw [h4]; group
      rw [this]
      exact mul_mem hhrL (inv_mem hr₂.2)
    exact A.config.not_mem htL

theorem sqLeft_of_mem_normalizer (S : Gens A) (C : A.CaseKD) (hκ : κ = C.k ∨ κ = S.z * C.k)
    {w : X} (hwV : w ∈ Fr.V) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) (hwz : w ≠ S.z) {n : X}
    (hn : n ∈ normalizer (L2E S.z w t C.k : Set X) ⊓ centralizer ({t} : Set X)) :
    SqLeft (act A Fr.e n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G' : Subgroup X := normalizer (L2E S.z w t C.k : Set X) ⊓ centralizer ({t} : Set X)
    with hG'
  let χ : G' →* Multiplicative (ZMod 2) :=
    { toFun := fun g => if SqLeft (act A Fr.e (g : X)) then 1 else Multiplicative.ofAdd 1
      map_one' := by
        rw [OneMemClass.coe_one, act_one]
        split_ifs with h
        · rfl
        · exact absurd sqLeft_one h
      map_mul' := fun a b => by
        rw [Subgroup.coe_mul, act_mul Fr.e a.2.2 b.2.2, sqLeft_mul]
        by_cases ha : SqLeft (act A Fr.e (a : X)) <;> by_cases hb : SqLeft (act A Fr.e (b : X)) <;>
          simp only [ha, hb, iff_true, iff_false, not_true, ite_true, ite_false, one_mul,
            mul_one, ofAdd_one_mul_self] }
  have hχ : ∀ g : G', χ g = 1 ↔ SqLeft (act A Fr.e (g : X)) := by
    intro g
    change (if SqLeft (act A Fr.e (g : X)) then 1 else Multiplicative.ofAdd 1) = 1 ↔ _
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false ofAdd_one_ne_one h
  obtain ⟨P⟩ : Nonempty (Sylow 2 G') := inferInstance
  have hP : (P : Subgroup G') ≤ χ.ker := by
    intro p hp
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    have hk' : ((p : G') : X) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : (P : Subgroup G') => ((x : G') : X)) hk
      simpa using this
    rw [MonoidHom.mem_ker, hχ]
    exact (Frame.two_elem Fr S C hκ hwV hw2 hw1 hwz p.2.2 p.2.1 hk').1
  have hdvd : χ.ker.index ∣ (P : Subgroup G').index := Subgroup.index_dvd_of_le hP
  have hnd := Sylow.not_dvd_index P
  have hle : χ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card χ.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  have hpos : χ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : χ.ker.index = 1 := by
    by_contra hne
    have h2 : χ.ker.index = 2 := by omega
    rw [h2] at hdvd
    exact hnd hdvd
  have hker : χ.ker = ⊤ := Subgroup.index_eq_one.mp h1
  have hm : (⟨n, hn⟩ : G') ∈ χ.ker := by rw [hker]; exact mem_top _
  rw [MonoidHom.mem_ker, hχ] at hm
  exact hm

theorem conj_eq_of_mem_normalizer_kd (S : Gens A) (C : A.CaseKD)
    (hκ : κ = C.k ∨ κ = S.z * C.k) {w : X} (hwV : w ∈ Fr.V) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hwz : w ≠ S.z) {n : X}
    (hn : n ∈ normalizer (L2E S.z w t C.k : Set X) ⊓ centralizer ({t} : Set X)) :
    n * κ * n⁻¹ = κ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G' : Subgroup X := normalizer (L2E S.z w t C.k : Set X) ⊓ centralizer ({t} : Set X)
    with hG'
  have hκE : κ ∈ L2E S.z w t C.k := by
    rcases hκ with rfl | rfl
    · exact mem_L2E_four S.z w t C.k
    · exact mul_mem (mem_L2E_one S.z w t C.k) (mem_L2E_four S.z w t C.k)
  have hpair : ∀ m ∈ G', m * κ * m⁻¹ = κ ∨ m * κ * m⁻¹ = t * κ := fun m hm =>
    Frame.conj_eq_or_of_mem_L2E_kd Fr S C hκ hwV hw2 hm.2
      (Frame.sqLeft_of_mem_normalizer Fr S C hκ hwV hw2 hw1 hwz hm)
      ((mem_normalizer_iff.mp hm.1 κ).mp hκE)
  have hsub : {y | ∃ g ∈ G', g * κ * g⁻¹ = y} ⊆ ({κ, t * κ} : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    rcases hpair g hg with h | h <;> simp [h]
  have hle2 : (G' ⊓ centralizer ({κ} : Set X)).relIndex G' ≤ 2 := by
    rw [relIndex_inf_centralizer_eq_ncard]
    calc _ ≤ ({κ, t * κ} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({t * κ} : Set X).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  obtain ⟨P⟩ : Nonempty (Sylow 2 G') := inferInstance
  have hP : (P : Subgroup G') ≤ (G' ⊓ centralizer ({κ} : Set X)).subgroupOf G' := by
    intro p hp
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    have hk' : ((p : G') : X) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : (P : Subgroup G') => ((x : G') : X)) hk
      simpa using this
    have hfix := (Frame.two_elem Fr S C hκ hwV hw2 hw1 hwz p.2.2 p.2.1 hk').2
    rw [mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨p.2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc ((p : G') : X) * κ = (p : G') * κ * ((p : G') : X)⁻¹ * (p : G') := by group
      _ = κ * (p : G') := by rw [hfix]
  have hdvd : ((G' ⊓ centralizer ({κ} : Set X)).subgroupOf G').index ∣
      (P : Subgroup G').index := Subgroup.index_dvd_of_le hP
  have hnd := Sylow.not_dvd_index P
  have hpos : ((G' ⊓ centralizer ({κ} : Set X)).subgroupOf G').index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hidx : (G' ⊓ centralizer ({κ} : Set X)).relIndex G' = 1 := by
    change ((G' ⊓ centralizer ({κ} : Set X)).subgroupOf G').index = 1
    change ((G' ⊓ centralizer ({κ} : Set X)).subgroupOf G').index ≤ 2 at hle2
    by_contra hne
    have h2 : ((G' ⊓ centralizer ({κ} : Set X)).subgroupOf G').index = 2 := by omega
    rw [h2] at hdvd
    exact hnd hdvd
  have := (relIndex_eq_one.mp hidx) hn
  rw [mem_inf, mem_centralizer_singleton_iff] at this
  calc n * κ * n⁻¹ = κ * n * n⁻¹ := by rw [this.2]
    _ = κ := by group

end Frame

end CFSG.ComponentClassification.HSFLit.L2KD
