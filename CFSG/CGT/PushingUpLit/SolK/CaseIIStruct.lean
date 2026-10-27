module

public import CFSG.CGT.PushingUpLit.SolK.CaseIIBasic
public import CFSG.CGT.PushingUpLit.SolK.AltStab
public import CFSG.CGT.PushingUpLit.SolK.RankOne

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped Pointwise

section VSupp

variable {d : ℕ}

theorem vsupp_one : vsupp (1 : ↥(coreMod d)) = ∅ := by
  ext i
  simp [mem_vsupp, vcoord_one]

theorem vsupp_eq_empty_iff {v : ↥(coreMod d)} : vsupp v = ∅ ↔ v = 1 := by
  constructor
  · intro h
    refine vcoord_ext fun i => ?_
    rw [vcoord_one]
    by_contra hne
    have h1 : vcoord v i = 1 := by
      generalize vcoord v i = a at hne ⊢
      revert a
      decide
    have : i ∈ vsupp v := mem_vsupp.2 h1
    rw [h] at this
    simp at this
  · rintro rfl
    exact vsupp_one

end VSupp

section TQ

variable {G : Type} [Group G]

def TQUnique (M X : Subgroup G) : Prop :=
  ∀ g : G, g ∉ M → conjSubgroup g (rOf M X) ≤ M → 3 ≤ Nat.card ↥(rOf M X) →
    conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥ →
      ∀ t ∈ conjSubgroup g (rOf M X), ∀ _ht : t ∈ pCoreOf 2 M, ∀ t' ∈ conjSubgroup g (rOf M X),
        ∀ _ht' : t' ∈ pCoreOf 2 M, t ≠ 1 → t' ≠ 1 → t = t'

end TQ

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

omit [Finite G] S in
theorem exists_nonid_TQ {g : G} (hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥) :
    ∃ t ∈ conjSubgroup g (rOf M X), t ∈ pCoreOf 2 M ∧ t ≠ 1 := by
  by_contra h
  push Not at h
  apply hTQ
  refine (Subgroup.eq_bot_iff_forall _).2 fun t ht => ?_
  exact h t ht.1 ht.2

theorem Q_le_conj (hP : TightDataPlus S) {g : G}
    (hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥) :
    ∀ q ∈ pCoreOf 2 M, g⁻¹ * q * g ∈ M := by
  obtain ⟨t, ht, htQ, ht1⟩ := exists_nonid_TQ hTQ
  intro q hq
  have hr : g⁻¹ * t * g ∈ rOf M X := mem_conjSubgroup.1 ht
  have hr1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply ht1
    have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [this, h]
    group
  refine S.mem_M_of_comm_R hr hr1 ?_
  have hqt : q * t * q⁻¹ = t := by
    have := hP.abelian q hq t htQ
    rw [this]
    group
  calc (g⁻¹ * q * g) * (g⁻¹ * t * g) * (g⁻¹ * q * g)⁻¹ = g⁻¹ * (q * t * q⁻¹) * g := by group
    _ = g⁻¹ * t * g := by rw [hqt]

theorem Q_normalizes_T (hP : TightDataPlus S) {g : G}
    (hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥) :
    ∀ q ∈ pCoreOf 2 M, ∀ τ ∈ conjSubgroup g (rOf M X), q * τ * q⁻¹ ∈ conjSubgroup g (rOf M X) := by
  obtain ⟨t, ht, htQ, ht1⟩ := exists_nonid_TQ hTQ
  intro q hq τ hτ
  have hqt : q * t * q⁻¹ = t := by
    have := hP.abelian q hq t htQ
    rw [this]
    group
  exact S.conjR_normal_of_comm g ht ht1 hqt hτ

noncomputable def pv (t : G) (ht : t ∈ pCoreOf 2 M) : ↥(coreMod (2 * n + 1)) :=
  S.D.β (S.projW ⟨t, ht⟩)

theorem pv_mul {t t' : G} (ht : t ∈ pCoreOf 2 M) (ht' : t' ∈ pCoreOf 2 M) :
    S.pv (t * t') ((pCoreOf 2 M).mul_mem ht ht') = S.pv t ht * S.pv t' ht' := by
  unfold pv
  have : (⟨t * t', (pCoreOf 2 M).mul_mem ht ht'⟩ : ↥(pCoreOf 2 M)) = ⟨t, ht⟩ * ⟨t', ht'⟩ := rfl
  rw [this, map_mul, map_mul]

theorem pv_inv {t : G} (ht : t ∈ pCoreOf 2 M) :
    S.pv t⁻¹ ((pCoreOf 2 M).inv_mem ht) = (S.pv t ht)⁻¹ := by
  unfold pv
  have : (⟨t⁻¹, (pCoreOf 2 M).inv_mem ht⟩ : ↥(pCoreOf 2 M)) = (⟨t, ht⟩ : ↥(pCoreOf 2 M))⁻¹ := rfl
  rw [this, map_inv, map_inv]
  rfl

theorem pv_eq_one_iff {t : G} (ht : t ∈ pCoreOf 2 M) : S.pv t ht = 1 ↔ t ∈ rOf M X := by
  unfold pv
  rw [map_eq_one_iff _ S.D.β.injective]
  exact (S.mem_ker_projW (q := ⟨t, ht⟩)).trans Iff.rfl

theorem X_comm_of_fix (x : ↥X) {t : G} (ht : t ∈ pCoreOf 2 M)
    (hfix : coreAct (2 * n + 1) (S.D.ρ x) (S.pv t ht) = S.pv t ht) :
    (x : G) * t * (x : G)⁻¹ = t := by
  obtain ⟨r, hr, e⟩ := S.projWFun_spec ⟨t, ht⟩
  have hw : ((S.projW ⟨t, ht⟩ : ↥S.D.W) : G) = (S.projWFun ⟨t, ht⟩ : G) :=
    S.projW_apply (S.projWFun ⟨t, ht⟩).2 hr e
  set w : ↥S.D.W := S.projW ⟨t, ht⟩ with hwdef
  have hte : t = (w : G) * r := by
    have : t = (S.projWFun ⟨t, ht⟩ : G) * r := e
    rw [this, ← hw]
  have hxw : (x : G) * (w : G) * (x : G)⁻¹ = (w : G) := by
    have h1 := S.D.equivar x w (S.W_normalized (S.hyp.le x.2) w.2)
    have h2 : S.D.β w = S.pv t ht := rfl
    rw [h2, hfix] at h1
    have h3 : (⟨(x : G) * (w : G) * (x : G)⁻¹, S.W_normalized (S.hyp.le x.2) w.2⟩ : ↥S.D.W) = w :=
      S.D.β.injective (h1.trans h2.symm)
    exact congrArg Subtype.val h3
  calc (x : G) * t * (x : G)⁻¹ = ((x : G) * (w : G) * (x : G)⁻¹) * ((x : G) * r * (x : G)⁻¹) := by
        rw [hte]; group
    _ = t := by rw [hxw, X_comm_R x.2 hr, ← hte]

theorem TQ_unique (hP : TightDataPlus S) {g : G} (hgM : g ∉ M) :
    ∀ t ∈ conjSubgroup g (rOf M X), ∀ _ht : t ∈ pCoreOf 2 M, ∀ t' ∈ conjSubgroup g (rOf M X),
      ∀ _ht' : t' ∈ pCoreOf 2 M, t ≠ 1 → t' ≠ 1 → t = t' := by
  classical
  intro t htT ht t' ht'T ht' ht1 ht'1
  by_contra hne
  set T := conjSubgroup g (rOf M X) with hT
  have hd : 5 ≤ 2 * n + 1 := by have := S.hyp.two_le; omega
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hTR : ∀ s ∈ T, s ∈ rOf M X → s = 1 := fun s hs hr =>
    Subgroup.mem_bot.1 (by rw [← hP.ti g hgM]; exact ⟨hr, hs⟩)
  have hCG : ∀ s ∈ T, s ≠ 1 → ∀ y : G, y * s * y⁻¹ = s → g⁻¹ * y * g ∈ M := by
    intro s hsT hs1 y hy
    have hr : g⁻¹ * s * g ∈ rOf M X := mem_conjSubgroup.1 hsT
    have hr1 : g⁻¹ * s * g ≠ 1 := by
      intro h
      apply hs1
      have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      rw [this, h]
      group
    refine S.mem_M_of_comm_R hr hr1 ?_
    calc (g⁻¹ * y * g) * (g⁻¹ * s * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * s * y⁻¹) * g := by group
      _ = g⁻¹ * s * g := by rw [hy]
  have hne' : ∀ s (hs : s ∈ pCoreOf 2 M), s ∈ T → s ≠ 1 → (vsupp (S.pv s hs)).Nonempty := by
    intro s hs hsT hs1
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [vsupp_eq_empty_iff, S.pv_eq_one_iff] at h
    exact hs1 (hTR s hsT h)
  have hIJ : vsupp (S.pv t ht) ≠ vsupp (S.pv t' ht') := by
    intro h
    have hpv : S.pv t ht = S.pv t' ht' := eq_of_vsupp_eq h
    have hmem : t⁻¹ * t' ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem ((pCoreOf 2 M).inv_mem ht) ht'
    have h1 : S.pv (t⁻¹ * t') hmem = 1 := by
      rw [S.pv_mul ((pCoreOf 2 M).inv_mem ht) ht', S.pv_inv ht, hpv]
      exact inv_mul_cancel _
    have h2 : t⁻¹ * t' ∈ rOf M X := (S.pv_eq_one_iff hmem).1 h1
    have h3 : t⁻¹ * t' ∈ T := T.mul_mem (T.inv_mem htT) ht'T
    have h4 := hTR _ h3 h2
    apply hne
    calc t = t * (t⁻¹ * t') := by rw [h4, mul_one]
      _ = t' := by group
  let K : Subgroup ↥X := Subgroup.comap ((MulAut.conj g⁻¹).toMonoidHom.comp X.subtype) M
  have hK : ∀ x : ↥X, x ∈ K ↔ g⁻¹ * (x : G) * g ∈ M := fun x => by
    show g⁻¹ * (x : G) * g⁻¹⁻¹ ∈ M ↔ _
    rw [inv_inv]
  let ρ' : ↥X →* ↥(alternatingGroup (Fin (2 * n + 1))) := S.D.ρ.codRestrict _ S.D.ρ_alt
  have hstab : ∀ (s : G) (hs : s ∈ pCoreOf 2 M), s ∈ T → s ≠ 1 →
      MulAction.stabilizer (alternatingGroup (Fin (2 * n + 1)))
        (↑(vsupp (S.pv s hs)) : Set (Fin (2 * n + 1))) ≤ K.map ρ' := by
    intro s hs hsT hs1 σ hσ
    obtain ⟨x, hx⟩ := S.D.ρ_surj σ.1 σ.2
    have hfix : coreAct (2 * n + 1) (S.D.ρ x) (S.pv s hs) = S.pv s hs := by
      refine (coreAct_eq_iff _ _).2 (mem_setStab.2 fun y => ?_)
      rw [hx]
      exact (mem_stabilizer_alt_iff _ σ).1 hσ y
    have hxs : (x : G) * s * (x : G)⁻¹ = s := S.X_comm_of_fix x hs hfix
    have hxK : x ∈ K := (hK x).2 (hCG s hsT hs1 x hxs)
    exact ⟨x, hxK, Subtype.ext hx⟩
  have htop : K.map ρ' = ⊤ :=
    eq_top_of_stab_le hd hodd (even_card_vsupp _) (even_card_vsupp _) (hne' t ht htT ht1)
      (hne' t' ht' ht'T ht'1) hIJ (hstab t ht htT ht1) (hstab t' ht' ht'T ht'1)
  have hXg : ∀ x ∈ X, g⁻¹ * x * g ∈ M := by
    intro x hx
    have hmem : ρ' ⟨x, hx⟩ ∈ K.map ρ' := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hkK, hk⟩ := hmem
    have hρ : S.D.ρ k = S.D.ρ ⟨x, hx⟩ := congrArg Subtype.val hk
    have hy : coreAct (2 * n + 1) (S.D.ρ (k⁻¹ * ⟨x, hx⟩)) (S.pv t ht) = S.pv t ht := by
      rw [map_mul, map_inv, hρ, inv_mul_cancel]
      exact map_one (coreAct (2 * n + 1)) ▸ rfl
    have hyt : ((k⁻¹ * ⟨x, hx⟩ : ↥X) : G) * t * ((k⁻¹ * ⟨x, hx⟩ : ↥X) : G)⁻¹ = t :=
      S.X_comm_of_fix _ ht hy
    have hyM : g⁻¹ * ((k⁻¹ * ⟨x, hx⟩ : ↥X) : G) * g ∈ M := hCG t htT ht1 _ hyt
    have hkM : g⁻¹ * (k : G) * g ∈ M := (hK k).1 hkK
    have : g⁻¹ * x * g = (g⁻¹ * (k : G) * g) * (g⁻¹ * ((k⁻¹ * ⟨x, hx⟩ : ↥X) : G) * g) := by
      have e : ((k⁻¹ * ⟨x, hx⟩ : ↥X) : G) = (k : G)⁻¹ * x := rfl
      rw [e]
      group
    rw [this]
    exact M.mul_mem hkM hyM
  have hg1 : g⁻¹ ∈ M := S.mem_of_conj_le g⁻¹ (fun x hx => by
    rw [inv_inv]
    exact hXg x hx)
  exact hgM (by simpa using M.inv_mem hg1)

theorem tqUnique_of_two_le (hP : TightDataPlus S) : TQUnique M X :=
  fun _g hgM _ _ _ => S.TQ_unique hP hgM

theorem beta_comm {w τ : G} (hw : w ∈ S.D.W) (hτ : τ ∈ M)
    (hc : w * (τ * w⁻¹ * τ⁻¹) ∈ S.D.W) :
    S.D.β ⟨w * (τ * w⁻¹ * τ⁻¹), hc⟩ =
      S.D.β ⟨w, hw⟩ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) (S.D.β ⟨w, hw⟩) := by
  have hwi : w⁻¹ ∈ S.D.W := S.D.W.inv_mem hw
  have hw' : τ * w⁻¹ * τ⁻¹ ∈ S.D.W := S.W_normalized hτ hwi
  have h1 : S.D.β ⟨τ * w⁻¹ * τ⁻¹, hw'⟩ =
      coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) (S.D.β ⟨w⁻¹, hwi⟩) :=
    S.θ_spec ⟨τ, hτ⟩ ⟨w⁻¹, hwi⟩ hw'
  have hβinv : S.D.β ⟨w⁻¹, hwi⟩ = (S.D.β ⟨w, hw⟩)⁻¹ := by
    have : (⟨w⁻¹, hwi⟩ : ↥S.D.W) = (⟨w, hw⟩ : ↥S.D.W)⁻¹ := rfl
    rw [this, map_inv]
    rfl
  have h2 : (⟨w * (τ * w⁻¹ * τ⁻¹), hc⟩ : ↥S.D.W) = ⟨w, hw⟩ * ⟨τ * w⁻¹ * τ⁻¹, hw'⟩ := rfl
  rw [h2, map_mul, h1, hβinv, map_inv]
  congr 1
  exact coreMod_inv_eq _

theorem TQ_structure (hP : TightDataPlus S) (hU : TQUnique M X) {g : G} (hgM : g ∉ M)
    (hTM : conjSubgroup g (rOf M X) ≤ M) (hcard : 3 ≤ Nat.card ↥(rOf M X))
    (hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥) :
    ∃ a b : Fin (2 * n + 1), a ≠ b ∧
      (∃ s : G, ∃ hs : s ∈ M, s ∈ conjSubgroup g (rOf M X) ∧ S.θ ⟨s, hs⟩ = swap a b) ∧
      (∀ τ : G, ∀ hτ : τ ∈ M, τ ∈ conjSubgroup g (rOf M X) →
        S.θ ⟨τ, hτ⟩ = 1 ∨ S.θ ⟨τ, hτ⟩ = swap a b) ∧
      ∃ t₁ : G, t₁ ∈ conjSubgroup g (rOf M X) ∧ t₁ ∈ S.D.W ∧ t₁ ≠ 1 ∧
        ∀ t ∈ conjSubgroup g (rOf M X), t ∈ pCoreOf 2 M → t = 1 ∨ t = t₁ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set T := conjSubgroup g (rOf M X) with hT
  have hQT := S.Q_normalizes_T hP hTQ
  have huniq := hU g hgM hTM hcard hTQ
  have hd5 : 3 ≤ 2 * n + 1 := by have := S.hyp.two_le; omega
  obtain ⟨s, hsT, hsQ⟩ : ∃ s ∈ T, s ∉ pCoreOf 2 M := by
    by_contra hall
    push Not at hall
    have hcardT : Nat.card ↥T = Nat.card ↥(rOf M X) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have h3 : 2 < Fintype.card ↥T := by
      rw [← Nat.card_eq_fintype_card, hcardT]
      omega
    obtain ⟨u, v, w, huv, huw, hvw⟩ := Fintype.two_lt_card_iff.1 h3
    have key : ∀ x y : ↥T, x ≠ y → (x : G) ≠ 1 → (y : G) ≠ 1 → False := fun x y hxy hx hy =>
      hxy (Subtype.ext (huniq x x.2 (hall x x.2) y y.2 (hall y y.2) hx hy))
    by_cases hu : (u : G) = 1
    · exact key v w hvw (fun h => huv (Subtype.ext (hu.trans h.symm)))
        (fun h => huw (Subtype.ext (hu.trans h.symm)))
    · by_cases hv : (v : G) = 1
      · exact key u w huw hu (fun h => hvw (Subtype.ext (hv.trans h.symm)))
      · exact key u v huv hu hv
  have hsM : s ∈ M := hTM hsT
  have hsθ : S.θ ⟨s, hsM⟩ ≠ 1 := fun h => hsQ (hP.ker_two ⟨s, hsM⟩ h (conjR_two g hsT))
  obtain ⟨w₀, hw₀, hw₀s⟩ : ∃ w₀ ∈ S.D.W, s * w₀ * s⁻¹ ≠ w₀ := by
    by_contra h
    push Not at h
    exact hsθ ((theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨s, hsM⟩).2 h)
  have hw₀Q : w₀ ∈ pCoreOf 2 M := S.W_le_Q hw₀
  set t₁ : G := w₀ * (s * w₀⁻¹ * s⁻¹) with ht₁def
  have ht₁W : t₁ ∈ S.D.W := S.D.W.mul_mem hw₀ (S.W_normalized hsM (S.D.W.inv_mem hw₀))
  have ht₁T : t₁ ∈ T := by
    have h1 : w₀ * s * w₀⁻¹ ∈ T := hQT w₀ hw₀Q s hsT
    have : t₁ = (w₀ * s * w₀⁻¹) * s⁻¹ := by rw [ht₁def]; group
    rw [this]
    exact T.mul_mem h1 (T.inv_mem hsT)
  have ht₁1 : t₁ ≠ 1 := by
    intro h
    apply hw₀s
    have h' : w₀ * (s * w₀⁻¹ * s⁻¹) = 1 := h
    have h1 : w₀ = (s * w₀⁻¹ * s⁻¹)⁻¹ := mul_eq_one_iff_eq_inv.1 h'
    calc s * w₀ * s⁻¹ = (s * w₀⁻¹ * s⁻¹)⁻¹ := by group
      _ = w₀ := h1.symm
  have ht₁Q : t₁ ∈ pCoreOf 2 M := S.W_le_Q ht₁W
  have hTQ' : ∀ t ∈ T, t ∈ pCoreOf 2 M → t = 1 ∨ t = t₁ := by
    intro t htT htQ
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    · exact Or.inr (huniq t htT htQ t₁ ht₁T ht₁Q ht1 ht₁1)
  set b₁ : ↥(coreMod (2 * n + 1)) := S.D.β ⟨t₁, ht₁W⟩ with hb₁
  have hdich : ∀ τ : G, ∀ hτ : τ ∈ M, τ ∈ T → ∀ v : ↥(coreMod (2 * n + 1)),
      v⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) v = 1 ∨
        v⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) v = b₁ := by
    intro τ hτ hτT v
    obtain ⟨wv, hwv⟩ := S.D.β.surjective v
    set c : G := (wv : G) * (τ * (wv : G)⁻¹ * τ⁻¹) with hc
    have hcW : c ∈ S.D.W := S.D.W.mul_mem wv.2 (S.W_normalized hτ (S.D.W.inv_mem wv.2))
    have hcT : c ∈ T := by
      have h1 : (wv : G) * τ * (wv : G)⁻¹ ∈ T := hQT wv (S.W_le_Q wv.2) τ hτT
      have : c = ((wv : G) * τ * (wv : G)⁻¹) * τ⁻¹ := by rw [hc]; group
      rw [this]
      exact T.mul_mem h1 (T.inv_mem hτT)
    have hβc : S.D.β ⟨c, hcW⟩ =
        S.D.β wv * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) (S.D.β wv) := S.beta_comm wv.2 hτ hcW
    have hv : v⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) v = S.D.β ⟨c, hcW⟩ := by
      rw [hβc, hwv, coreMod_inv_eq]
    rw [hv]
    rcases hTQ' c hcT (S.W_le_Q hcW) with h | h
    · left
      have : (⟨c, hcW⟩ : ↥S.D.W) = 1 := Subtype.ext h
      rw [this, map_one]
    · right
      have : (⟨c, hcW⟩ : ↥S.D.W) = ⟨t₁, ht₁W⟩ := Subtype.ext h
      rw [this]
  have hz : ∀ τ : G, ∀ hτ : τ ∈ M, τ ∈ T → ∀ v w : ↥(coreMod (2 * n + 1)),
      v⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) v ≠ 1 →
      w⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) w ≠ 1 →
      v⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) v = w⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) w := by
    intro τ hτ hτT v w hv hw
    rcases hdich τ hτ hτT v with h | h
    · exact absurd h hv
    · rcases hdich τ hτ hτT w with h' | h'
      · exact absurd h' hw
      · rw [h, h']
  have hswap : ∀ τ : G, ∀ hτ : τ ∈ M, τ ∈ T → S.θ ⟨τ, hτ⟩ ≠ 1 →
      ∃ a b : Fin (2 * n + 1), a ≠ b ∧ S.θ ⟨τ, hτ⟩ = swap a b ∧ b₁ = pairVec a b := by
    intro τ hτ hτT hθ
    obtain ⟨j, hj⟩ := conjR_two g hτT
    have hσj : (S.θ ⟨τ, hτ⟩) ^ (2 ^ j) = 1 := by
      have : (⟨τ, hτ⟩ : ↥M) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
      rw [← map_pow, this, map_one]
    obtain ⟨a, b, hab, hσ⟩ :=
      exists_swap_of_small_image (odd_two_mul_add_one n) hσj hθ (hz τ hτ hτT)
    obtain ⟨p, hpa, hpb⟩ := exists_ne_ne hd5 a b
    have hval : (pairVec a p)⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) (pairVec a p) =
        pairVec a b := by
      rw [hσ]
      exact swap_pairVec_value hpa hpb
    have hne1 : (pairVec a p)⁻¹ * coreAct (2 * n + 1) (S.θ ⟨τ, hτ⟩) (pairVec a p) ≠ 1 := by
      rw [hval]
      exact pairVec_ne_one hab
    refine ⟨a, b, hab, hσ, ?_⟩
    rcases hdich τ hτ hτT (pairVec a p) with h | h
    · exact absurd h hne1
    · exact h.symm.trans hval
  obtain ⟨a, b, hab, hsswap, hb₁ab⟩ := hswap s hsM hsT hsθ
  refine ⟨a, b, hab, ⟨s, hsM, hsT, hsswap⟩, ?_, t₁, ht₁T, ht₁W, ht₁1, hTQ'⟩
  intro τ hτ hτT
  by_cases hθτ : S.θ ⟨τ, hτ⟩ = 1
  · exact Or.inl hθτ
  · obtain ⟨a', b', hab', hτswap, hb₁ab'⟩ := hswap τ hτ hτT hθτ
    right
    rw [hτswap]
    exact swap_eq_of_pairVec_eq hab' hab (hb₁ab'.symm.trans hb₁ab)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
