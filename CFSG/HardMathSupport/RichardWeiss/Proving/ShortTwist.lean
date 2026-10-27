module

public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortCocycle
public import CFSG.HardMathSupport.RichardWeiss.Proving.HeartCocycleL

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] {N : ℕ}

theorem altHeart_add_self (a : altHeart N) : a + a = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 := by
    apply Subtype.ext
    funext p
    have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
    exact h2 _
  rw [this]; rfl

theorem pairEW_twist_id (σ : Perm (Fin N)) (a b : Fin N) :
    (pairEW (σ b) (σ a) : altHeart N) + (pairEW b a : altHeart N) + (pairEW (σ a) a : altHeart N) =
      (pairEW (σ b) b : altHeart N) := by
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
  congr 1
  apply Subtype.ext
  funext p
  simp only [AddSubgroup.coe_add, Pi.add_apply, pairEW_apply]
  have key : ∀ A B C D : ZMod 2, (A + B) + (C + D) + (B + D) = A + C := by decide
  exact key _ _ _ _

namespace ShortData

variable {Q L V S : Subgroup G} (D : ShortData Q L V S)
  {π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)} {θ : ↥(L ⊔ S) →* Perm (Fin N)}
  (H : ShortSection Q L V S π θ)
include D H

theorem short_twist_cob (hN : 6 ≤ N) (hev : Even N) {y : G} (hy : y ∈ Q) {m : G}
    (hm : m ∈ L ⊔ S) :
    ∃ w₃ : altHeart N, ∀ l : G, l ∈ L →
      Fy π (m * y * m⁻¹ * y⁻¹) l = altAct (thetaA θ l) w₃ - w₃ := by
  classical
  let a : Fin N := ⟨0, by omega⟩
  let θL : ↥L →* Perm (Fin N) := θ.comp (Subgroup.inclusion le_sup_left)
  have hθt : ∀ l : ↥L, thetaA θ (l : G) = θL l := fun l =>
    thetaA_of_mem (Subgroup.mem_sup_left l.2)
  have hAlt : ∀ l : ↥L, θL l ∈ alternatingGroup (Fin N) := fun l => by
    rw [mem_alternatingGroup]
    exact perfect_hom_trivial D.hperf (Perm.sign.comp θL) l
  have hsurj : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θL l = σ := H.hAθ
  let F : ↥L → altHeart N := fun l => Fy π y (l : G)
  have hF : ∀ l₁ l₂ : ↥L, F (l₁ * l₂) = F l₁ + altAct (θL l₁) (F l₂) := by
    intro l₁ l₂
    show Fy π y ((l₁ : G) * (l₂ : G)) = _
    rw [D.Fy_mul H hy l₁.2 l₂.2, hθt]
  have hker : ∀ r : ↥L, θL r = 1 → F r = 0 := fun r hr => D.Fy_ker H hy r.2 hr
  obtain ⟨w, β, hwβ⟩ := cocycle_heart_decomp_of_hom hN hev a θL hAlt hsurj F hF hker
  let π₁ : Perm (Fin N) := θ ⟨m, hm⟩
  have hπ₁ : thetaA θ m = π₁ := thetaA_of_mem hm
  let P : altHeart N := if β then (pairEW (π₁ a) a : altHeart N) else 0
  refine ⟨P + (altAct π₁ w - w), fun l hl => ?_⟩
  have hl2 : m⁻¹ * l * m ∈ L := by
    have := D.hML m⁻¹ (Subgroup.inv_mem _ hm) l hl
    simpa using this
  let l' : ↥L := ⟨m⁻¹ * l * m, hl2⟩
  have hθl' : θL l' = π₁⁻¹ * thetaA θ l * π₁ := by
    have h1 : (⟨m⁻¹ * l * m, Subgroup.mem_sup_left hl2⟩ : ↥(L ⊔ S)) =
        (⟨m, hm⟩ : ↥(L ⊔ S))⁻¹ * ⟨l, Subgroup.mem_sup_left hl⟩ * ⟨m, hm⟩ := Subtype.ext rfl
    show θ ⟨m⁻¹ * l * m, Subgroup.mem_sup_left hl2⟩ = _
    rw [h1, map_mul, map_mul, map_inv, thetaA_of_mem (Subgroup.mem_sup_left hl)]
  set σ : Perm (Fin N) := thetaA θ l with hσ
  have hσL : θL ⟨l, hl⟩ = σ := (hθt ⟨l, hl⟩).symm
  have hfy : Fy π y l = (if β then (pairEW (σ a) a : altHeart N) else 0) +
      (altAct σ w - w) := by
    have := hwβ ⟨l, hl⟩
    rw [hσL] at this
    exact this
  have hfy' : Fy π y (m⁻¹ * l * m) = (if β then (pairEW ((π₁⁻¹ * σ * π₁) a) a : altHeart N) else 0) +
      (altAct (π₁⁻¹ * σ * π₁) w - w) := by
    have := hwβ l'
    rw [hθl'] at this
    exact this
  have hA : Fy π (m * y * m⁻¹) l = (if β then (pairEW (σ (π₁ a)) (π₁ a) : altHeart N) else 0) +
      (altAct σ (altAct π₁ w) - altAct π₁ w) := by
    rw [D.Fy_twist H hy hm hl, hπ₁, hfy', map_add, map_sub]
    have e1 : altAct π₁ (altAct (π₁⁻¹ * σ * π₁) w) = altAct σ (altAct π₁ w) := by
      rw [← altAct_mul, ← altAct_mul]; congr 1; group
    rw [e1]
    cases β
    · simp
    · simp only [if_true, ite_true]
      rw [altAct_pairEW]
      have : π₁ ((π₁⁻¹ * σ * π₁) a) = σ (π₁ a) := by
        simp [Perm.mul_apply]
      rw [this]
  have hxQ : m * y * m⁻¹ * y⁻¹ ∈ Q :=
    Q.mul_mem (D.hMQ m hm y hy) (Q.inv_mem hy)
  have hy'x : Fy π (m * y * m⁻¹) l = Fy π (m * y * m⁻¹ * y⁻¹) l + Fy π y l := by
    have e : m * y * m⁻¹ = (m * y * m⁻¹ * y⁻¹) * y := by group
    conv_lhs => rw [e]
    exact D.Fy_yMul H hxQ hy hl
  have hneg : ∀ z : altHeart N, -z = z := fun z =>
    (eq_neg_of_add_eq_zero_left (altHeart_add_self z)).symm
  have hPb : (if β then (pairEW (σ (π₁ a)) (π₁ a) : altHeart N) else 0) =
      (altAct σ P - P) + (if β then (pairEW (σ a) a : altHeart N) else 0) := by
    cases β
    · simp [P]
    · simp only [P, ite_true, altAct_pairEW]
      have := pairEW_twist_id σ a (π₁ a)
      rw [sub_eq_add_neg, hneg]
      rw [← this]
  have hx : Fy π (m * y * m⁻¹ * y⁻¹) l =
      (if β then (pairEW (σ (π₁ a)) (π₁ a) : altHeart N) else 0) +
        (altAct σ (altAct π₁ w) - altAct π₁ w) -
      ((if β then (pairEW (σ a) a : altHeart N) else 0) + (altAct σ w - w)) := by
    rw [← hA, ← hfy]
    exact eq_sub_of_add_eq hy'x.symm
  rw [hx, hPb]
  simp only [map_add, map_sub]
  abel

attribute [local instance] IsMulCommutative.instCommGroup in
theorem short_twist (hN : 6 ≤ N) (hev : Even N) {y : G} (hy : y ∈ Q) {m : G}
    (hm : m ∈ L ⊔ S) :
    ∃ u ∈ ⁅V, L⁆, ∃ c ∈ Q ⊓ Subgroup.centralizer (L : Set G), ⁅m, y⁆ = u * c := by
  classical
  obtain ⟨w₃, hw₃⟩ := D.short_twist_cob H hN hev hy hm
  have hUV := D.commutator_le
  have hUQ : ⁅V, L⁆ ≤ Q := hUV.trans D.hVQ
  obtain ⟨u, hu⟩ := H.hπ (Multiplicative.ofAdd w₃)
  have hu₁U : (u : G) ∈ ⁅V, L⁆ := u.2
  have hu₁Q : (u : G) ∈ Q := hUQ hu₁U
  have hpiu : piA π (u : G) = w₃ := by
    rw [piA_of_mem hu₁U]
    have : (⟨(u : G), hu₁U⟩ : ↥⁅V, L⁆) = u := rfl
    rw [this, hu]; rfl
  have hFu : ∀ l ∈ L, Fy π (u : G) l = altAct (thetaA θ l) w₃ - w₃ := by
    intro l hl
    have hlM : l ∈ L ⊔ S := Subgroup.mem_sup_left hl
    have hc := D.conj_mem_U H hlM hu₁U
    have e : ⁅l, (u : G)⁆ = (l * (u : G) * l⁻¹) * (u : G)⁻¹ := by
      simp only [commutatorElement_def]
    show piA π ⁅l, (u : G)⁆ = _
    rw [e, piA_mul hc (⁅V, L⁆.inv_mem hu₁U), piA_conj H.hequiv hlM hu₁U hc,
      piA_inv hu₁U, hpiu, sub_eq_add_neg]
  have hxQ : ⁅m, y⁆ ∈ Q := by
    have : ⁅m, y⁆ = m * y * m⁻¹ * y⁻¹ := rfl
    rw [this]; exact Q.mul_mem (D.hMQ m hm y hy) (Q.inv_mem hy)
  have hcQ : ⁅m, y⁆ * (u : G)⁻¹ ∈ Q := Q.mul_mem hxQ (Q.inv_mem hu₁Q)
  have hFc : ∀ l ∈ L, Fy π (⁅m, y⁆ * (u : G)⁻¹) l = 0 := by
    intro l hl
    rw [D.Fy_yMul H hxQ (Q.inv_mem hu₁Q) hl, D.Fy_yInv H hu₁Q hl, hFu l hl]
    have : ⁅m, y⁆ = m * y * m⁻¹ * y⁻¹ := rfl
    rw [this, hw₃ l hl]
    exact add_neg_cancel _
  set c : G := ⁅m, y⁆ * (u : G)⁻¹ with hcdef
  have hker : ∀ l ∈ L, ⁅l, c⁆ ∈ ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
    intro l hl
    have hU := D.comm_mem_U hcQ hl
    refine ⟨hU, ?_⟩
    have h0 : piA π ⁅l, c⁆ = 0 := hFc l hl
    rw [piA_of_mem hU] at h0
    have h1 : π ⟨⁅l, c⁆, hU⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      exact h0
    have : (⟨⁅l, c⁆, hU⟩ : ↥⁅V, L⁆) ∈ π.ker := h1
    rw [H.hπker, Subgroup.mem_subgroupOf] at this
    exact this.2
  set K₀ : Subgroup G := ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) with hK₀
  have : IsMulCommutative ↥K₀ :=
    ⟨⟨fun a b => Subtype.ext (D.hQV a (hUQ a.2.1) b (hUV b.2.1))⟩⟩
  let ψ : ↥L →* ↥K₀ :=
    { toFun := fun l => ⟨⁅(l : G), c⁆, hker l l.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro l₁ l₂
        apply Subtype.ext
        have e : ⁅(l₁ : G) * (l₂ : G), c⁆ =
            ((l₁ : G) * ⁅(l₂ : G), c⁆ * (l₁ : G)⁻¹) * ⁅(l₁ : G), c⁆ := by
          simp only [commutatorElement_def]; group
        have hc₂ : (l₁ : G) * ⁅(l₂ : G), c⁆ * (l₁ : G)⁻¹ = ⁅(l₂ : G), c⁆ := by
          have := Subgroup.mem_centralizer_iff.1 (hker l₂ l₂.2).2 (l₁ : G) l₁.2
          rw [this]; group
        show ⁅(l₁ : G) * (l₂ : G), c⁆ = ⁅(l₁ : G), c⁆ * ⁅(l₂ : G), c⁆
        rw [e, hc₂]
        exact D.hQV _ (hUQ (D.comm_mem_U hcQ l₂.2)) _ (hUV (D.comm_mem_U hcQ l₁.2)) }
  have hψ := perfect_hom_trivial D.hperf ψ
  have hcc : c ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg Subtype.val (hψ ⟨l, hl⟩)
    have h1 : ⁅l, c⁆ = 1 := this
    have h2 : l * c * l⁻¹ * c⁻¹ = 1 := h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm ▸ rfl
  refine ⟨(u : G), hu₁U, c, ⟨hcQ, hcc⟩, ?_⟩
  have hcu : c * (u : G) = (u : G) * c := D.hQV c hcQ _ (hUV hu₁U)
  have : ⁅m, y⁆ = c * (u : G) := by simp [hcdef]
  rw [this, hcu]

end ShortData

end CFSG.HardMathSupport.RichardWeiss.Proving
