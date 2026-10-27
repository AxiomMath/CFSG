module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub8
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub7

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open scoped commutatorElement

namespace EndB

namespace IdxModel

variable {G : Type*} [Group G] {e' : ℕ → G}
  (h' : IdxModel 128 e' vT vI 0)
include h'

theorem conj_eq_of_comm_iv {l : G} (hn : ∀ x ∈ h'.sub, l * x * l⁻¹ ∈ h'.sub)
    (hc : ∀ a ∈ cModZ h'.sub, l * a = a * l) (hz2 : e' 1 * e' 1 = 1) {v : G}
    (hv : v ∈ h'.sub) : l * v * l⁻¹ = v ∨ l * v * l⁻¹ = v * e' 1 := by
  have hv' := hn v hv
  have hVn : ∀ y ∈ h'.sub, ∀ x ∈ h'.sub, y * x * y⁻¹ ∈ h'.sub :=
    fun y hy x hx => mul_mem (mul_mem hy hx) (inv_mem hy)
  have hcomm : ∀ k ∈ ivList,
      ((l * v * l⁻¹)⁻¹ * v) * e' k = e' k * ((l * v * l⁻¹)⁻¹ * v) := by
    intro k hk
    have hu : e' k ∈ cModZ h'.sub := h'.mem_iv_iff.mpr ⟨k, hk, rfl⟩
    have hvu : v * e' k * v⁻¹ ∈ cModZ h'.sub := conj_mem_cModZ hVn v hv _ hu
    have h1 := hc _ hvu
    have h2 := hc _ hu
    have h2' : l⁻¹ * e' k * l = e' k := by rw [mul_assoc, ← h2]; group
    have h3 : (l * v * l⁻¹) * e' k * (l * v * l⁻¹)⁻¹ = v * e' k * v⁻¹ := by
      calc (l * v * l⁻¹) * e' k * (l * v * l⁻¹)⁻¹ =
          l * v * (l⁻¹ * e' k * l) * v⁻¹ * l⁻¹ := by group
        _ = l * (v * e' k * v⁻¹) * l⁻¹ := by rw [h2']; group
        _ = v * e' k * v⁻¹ := by rw [h1]; group
    calc ((l * v * l⁻¹)⁻¹ * v) * e' k = (l * v * l⁻¹)⁻¹ * (v * e' k * v⁻¹) * v := by group
      _ = (l * v * l⁻¹)⁻¹ * ((l * v * l⁻¹) * e' k * (l * v * l⁻¹)⁻¹) * v := by rw [h3]
      _ = e' k * ((l * v * l⁻¹)⁻¹ * v) := by group
  rcases h'.eq_of_comm_iv (mul_mem (inv_mem hv') hv) hcomm with h | h
  · exact Or.inl (inv_mul_eq_one.mp h)
  · right
    have h4 : l * v * l⁻¹ * e' 1 = v := by rw [← h]; group
    rw [← inv_eq_of_mul_eq_one_right hz2]
    exact eq_mul_inv_iff_mul_eq.mpr h4

end IdxModel

theorem false_of_x0 {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}
    {S : Subgroup X} {w z : X} {V : Subgroup X} {i j : ℕ}
    (hs : Setting46e t L p f S w z V i j) {W W₁ V₀ : Subgroup X}
    (hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W) (hWW₁ : W ≤ W₁) (hW₁ : IsPGroup 2 W₁)
    (hV₀W : V₀ ≤ W) {β : X} (hβW : β ∈ W) (hβc : ∀ g ∈ W, g * β = β * g)
    (hzc : ∀ g ∈ W, g * z = z * g) (hβ2 : β * β = 1) (hz2 : z * z = 1) (hβt : β * t = t * β)
    (hdec : ∀ g ∈ W, ∃ v ∈ V₀, g = v ∨ g = v * t ∨ g = v * β ∨ g = v * (β * t))
    {x₀ : X} (hx₀W₁ : x₀ ∈ W₁) (hx₀W : x₀ ∉ W) (hx₀t : x₀ * t = t * x₀)
    (hx₀z : x₀ * z = z * x₀) (hx₀b : x₀ * β * x₀⁻¹ = β * z) (hx₀2 : x₀ * x₀ = 1 ∨ x₀ * x₀ = z)
    (hx₀V : ∀ v ∈ V₀, v * t = t * v → MZ z x₀ v) : False := by
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hTt : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    hs.lemma45.isSylowOf_T.le.trans inf_le_left
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_right.trans le_sup_left
  have hβz : β * z = z * β := hzc β hβW
  have key : ∀ x : X, x ∈ W₁ → x ∉ W → x * t = t * x → x * z = z * x → x * x = 1 →
      x * β * x⁻¹ = β * z → (∀ v ∈ V₀, v * t = t * v → MZ z x v) → False := by
    intro x hxW₁ hxW hxt hxz hx2 hxb hxV
    have hMt : MZ z x t := MZ.of_comm hxt
    have hMb : MZ z x β := Or.inr hxb
    have hMbt : MZ z x (β * t) := MZ.mul_right hz2 (hzc t htW) hMb hMt
    have hM : ∀ g ∈ W, g * t = t * g → MZ z x g := by
      intro g hg hgt
      obtain ⟨v, hv, hgv⟩ := hdec g hg
      have hvt : ∀ e : X, e * t = t * e → g = v * e → v * t = t * v := by
        intro e het hge
        have : v = g * e⁻¹ := by rw [hge]; group
        rw [this]
        calc g * e⁻¹ * t = g * (e⁻¹ * t) := by group
          _ = g * (t * e⁻¹) := by
            rw [show e⁻¹ * t = t * e⁻¹ by
              rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← het]; group]
          _ = (g * t) * e⁻¹ := by group
          _ = t * (g * e⁻¹) := by rw [hgt]; group
      rcases hgv with h | h | h | h
      · rw [h]
        rw [h] at hgt
        exact hxV v hv hgt
      · have := hvt t rfl h
        rw [h]
        exact MZ.mul_right hz2 (hzc t htW) (hxV v hv this) hMt
      · have := hvt β hβt h
        rw [h]
        exact MZ.mul_right hz2 hβz (hxV v hv this) hMb
      · have hbt : β * t * t = t * (β * t) :=
          ((show Commute β t from hβt).mul_left (Commute.refl t)).eq
        have := hvt (β * t) hbt h
        rw [h]
        exact MZ.mul_right hz2
          ((show Commute β z from hβz).mul_left (show Commute t z from hzc t htW)).eq
          (hxV v hv this) hMbt
    refine false_of_inv hs hTW hWW₁ hW₁ hxW₁ hxW hxt hx2 hxz
      (fun d hd => hzc d (hTW (hDT hd))) fun d hd => ?_
    have hd' : d⁻¹ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := inv_mem (hDT hd)
    exact MZ.swap hxz (hM _ (hTW hd') (mem_centralizer_singleton_iff.mp (hTt hd')))
  rcases hx₀2 with h | h
  · exact key x₀ hx₀W₁ hx₀W hx₀t hx₀z h hx₀b hx₀V
  · refine key (x₀ * β) (mul_mem hx₀W₁ (hWW₁ hβW)) (fun h' => hx₀W ?_) ?_ ?_ ?_ ?_ ?_
    · rw [show x₀ = x₀ * β * β⁻¹ by group]
      exact mul_mem h' (inv_mem hβW)
    · rw [mul_assoc, hβt, ← mul_assoc, hx₀t, mul_assoc]
    · rw [mul_assoc, hβz, ← mul_assoc, hx₀z, mul_assoc]
    · calc x₀ * β * (x₀ * β) = (x₀ * β * x₀⁻¹) * (x₀ * x₀) * β := by group
        _ = β * (z * z) * β := by rw [hx₀b, h]; group
        _ = 1 := by rw [hz2, mul_one, hβ2]
    · calc x₀ * β * β * (x₀ * β)⁻¹ = x₀ * β * x₀⁻¹ := by group
        _ = β * z := hx₀b
    · intro v hv hvt
      exact MZ.mul_left hz2 hx₀z (hx₀V v hv hvt) (MZ.of_comm (hβc v (hV₀W hv)).symm)

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem conj_t_lambda
    (hJ : JLayer hs π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W) (htW : t ∈ W) {c : Equiv.Perm (Fin 315)}
    (hcR : c ∈ R) {e' : ℕ → X} (h' : IdxModel 128 e' vT vI 0) (hsub : h'.sub = W ⊓ oP W)
    (hφ : ∀ k < 128, ∃ hk : e' k ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
      ∃ hkE : (QuotientGroup.mk ⟨e' k, hk⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      c⁻¹ * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * c = vE k)
    (hze : z = e' 1) (hz1 : z ≠ 1) (hzZ : z ∈ zW W) {l : X}
    (hlN : l ∈ normalizer (W : Set X)) (hl2 : l * l = 1)
    (hlc : ∀ a ∈ cModZ (W ⊓ oP W), l * a = a * l)
    (hlb : l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) (hlz : l * z * l⁻¹ = z) :
    t * l * t⁻¹ = l ∨ t * l * t⁻¹ = z * l := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have hgW : t * l * t⁻¹ * l⁻¹ ∈ W := by
    rw [show t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) by group]
    exact mul_mem htW (conj_mem_W l hlN _ (inv_mem htW))
  have hgc : ∀ k ∈ vBasis, (t * l * t⁻¹ * l⁻¹) * e' k = e' k * (t * l * t⁻¹ * l⁻¹) := by
    intro k hk
    have hu : e' k ∈ cModZ (W ⊓ oP W) := by
      rw [← hsub]
      refine h'.mem_iv_iff.mpr ⟨k, ?_, rfl⟩
      simp only [vBasis, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [ivList]
    have hu' : t⁻¹ * e' k * t ∈ cModZ (W ⊓ oP W) := by
      have := conj_mem_cModZ (N := normalizer (W : Set X))
        (conj_mem_inf' conj_mem_W conj_mem_oP) t⁻¹ (le_normalizer_self (inv_mem htW)) _ hu
      rwa [inv_inv] at this
    have h1 := hlc _ hu
    have h2 := hlc _ hu'
    have h1' : l⁻¹ * e' k * l = e' k := by rw [mul_assoc, ← h1]; group
    calc t * l * t⁻¹ * l⁻¹ * e' k = t * l * t⁻¹ * (l⁻¹ * e' k * l) * l⁻¹ := by group
      _ = t * (l * (t⁻¹ * e' k * t)) * t⁻¹ * l⁻¹ := by rw [h1']; group
      _ = t * ((t⁻¹ * e' k * t) * l) * t⁻¹ * l⁻¹ := by rw [h2]
      _ = e' k * (t * l * t⁻¹ * l⁻¹) := by group
  have hsq : (t * l * t⁻¹) * (t * l * t⁻¹) = 1 := by
    rw [show (t * l * t⁻¹) * (t * l * t⁻¹) = t * (l * l) * t⁻¹ by group, hl2]
    group
  have hgl : t * l * t⁻¹ = (t * l * t⁻¹ * l⁻¹) * l := by group
  have hβl : β * l * (β * l) = z := by
    calc β * l * (β * l) = β * (l * β * l⁻¹) * (l * l) := by group
      _ = β * β * z := by rw [hlb, hl2]; group
      _ = z := by
        rw [← sq, hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j), one_mul]
  have hβz : β * z = z * β := mem_centralizer_iff.mp (mem_inf.mp hzZ).2 β hβW
  rcases hJ.eq_of_comm_basis hQ hW hβW hcR h' hsub hφ hgW hgc with h | h | h | h
  · left
    rw [hgl, h, one_mul]
  · exfalso
    apply hz1
    rw [← hβl, ← hsq, hgl, h]
  · right
    rw [hgl, h, hze]
  · exfalso
    apply hz1
    have hβ2 : β * β = 1 := by
      rw [← sq]; exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
    have hz2 : z * z = 1 := by
      rw [← sq, ← hs.setup.z_order]; exact pow_orderOf_eq_one z
    rw [← hze] at h
    have : (β * z * l) * (β * z * l) = z := by
      calc (β * z * l) * (β * z * l) = β * z * (l * β * l⁻¹) * (l * z * l⁻¹) * (l * l) := by
            group
        _ = β * z * (β * z) * z := by rw [hlb, hlz, hl2]; group
        _ = (β * β) * (z * z) * z := by
            rw [show β * z * (β * z) = β * (z * β) * z by group, ← hβz]; group
        _ = z := by rw [hβ2, hz2]; group
    rw [← this, ← hsq, hgl, h]

omit [Finite X] in
theorem exists_u {W : Subgroup X} {e' : ℕ → X}
    (h' : IdxModel 128 e' vT vI 0) (hsub : h'.sub = W ⊓ oP W) {v₀ : ℕ} (hv₀ : v₀ < 128)
    (hsq : vT v₀ (vT (vCu v₀) vUsq) = 0) (hte : ∀ k < 128, t * e' k * t⁻¹ = e' (vAc v₀ k))
    (hcnt : 16 ≤ (List.range 128).countP (fun d => vAc v₀ d == d)) (hze : z = e' 1) :
    ∃ u ∈ W ⊓ oP W, t * u * t⁻¹ = u * z ∧ (u * u = 1 ∨ u * u = z) ∧
      ∀ v ∈ W ⊓ oP W, t * v * t⁻¹ = v → ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = z := by
  obtain ⟨u, hu, h1, h2, h3⟩ := vIndex_facts.2.2.2.2.2.2.2.2.2.2 v₀ hv₀ hsq hcnt
  have hcu₀ := vCu_facts
  have hAc : ∀ d < 128, vAc v₀ d < 128 := fun d hd =>
    h'.T_lt _ (h'.T_lt _ hv₀ _ (hcu₀ d hd).1) _ (h'.I_lt _ hv₀)
  refine ⟨e' u, hsub ▸ h'.e_mem hu, ?_, ?_, fun v hv hvt => ?_⟩
  · rw [hte u hu, h1, h'.e_T _ hu _ (by norm_num), hze]
  · rcases h2 with h2 | h2
    · left
      rw [← h'.e_T _ hu _ hu, h2, h'.e_o]
    · right
      rw [← h'.e_T _ hu _ hu, h2, hze]
  · rw [← hsub] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hfix : vAc v₀ d = d := h'.inj _ (hAc d hd) _ hd (by rw [← hte d hd, hvt])
    rw [← h'.e_ci hu hd]
    rcases h3 d hd hfix with h | h <;> rw [h]
    · exact Or.inl h'.e_o
    · exact Or.inr hze.symm

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
