module

public import CFSG.GH74.E2.Cl2CaseDefs
public import CFSG.GH74.E2.Cl2BPair

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

section Calc

variable {Q : Type*} [Group Q] {a b : MulAut Q} {N : Subgroup Q}

private theorem caseB_cube {g : MulAut Q} (hg : g ^ 3 = 1) (x : Q) : g (g (g x)) = x := by
  have := congrArg (fun f : MulAut Q => f x) hg
  simpa [pow_succ, MulAut.mul_apply] using this

private theorem caseB_comm (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (q : Q) : q * n = n * q :=
  Subgroup.mem_center_iff.mp (h.N_central hn) q

private theorem caseB_conj (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (q : Q) : q * n * q⁻¹ = n := by
  rw [caseB_comm h hn q]
  group

private theorem caseB_conj' (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (q : Q) : n * q * n⁻¹ = q := by
  rw [← caseB_comm h hn q]
  group

private theorem caseB_N_inv (h : Cl3 Q a b N) (x : Q) : a x ∈ N ↔ x ∈ N := by
  refine ⟨fun hx => ?_, h.N_inva x⟩
  rw [← caseB_cube h.bpair.a_cube x]
  exact h.N_inva _ (h.N_inva _ hx)

private theorem caseB_dsub (g g' : Q) : ⁅g, g'⁆ ∈ dsub Q :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top g')

private theorem caseB_commN (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (z : Q) : ⁅u, z⁆ ∈ N := by
  rw [h.N_eq]
  exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_top z)

private theorem caseB_commN' (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (z : Q) :
    ⁅z, u⁆ ∈ N := by
  rw [← commutatorElement_inv]
  exact N.inv_mem (caseB_commN h hu z)

private theorem caseB_N_le (h : Cl3 Q a b N) : N ≤ dsub Q := by
  rw [h.N_eq]
  exact Subgroup.commutator_le_left _ _

private theorem caseB_comm_one (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (k : Q) : ⁅n, k⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (caseB_comm h hn k).symm

private theorem caseB_mul_central_left (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (w k : Q) :
    ⁅n * w, k⁆ = ⁅w, k⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, caseB_comm_one h hn k, mul_one,
    caseB_conj' h hn]

private theorem caseB_mul_left (h : Cl3 Q a b N) {g g' k : Q} (hg' : ⁅g', k⁆ ∈ N) :
    ⁅g * g', k⁆ = ⁅g', k⁆ * ⁅g, k⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, caseB_conj h hg' g]

private theorem caseB_mul_right (h : Cl3 Q a b N) {g k k' : Q} (hk' : ⁅g, k'⁆ ∈ N) :
    ⁅g, k * k'⁆ = ⁅g, k⁆ * ⁅g, k'⁆ := by
  have h1 := caseB_conj h hk' k
  calc ⁅g, k * k'⁆ = ⁅g, k⁆ * (k * ⁅g, k'⁆ * k⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj]
        simp only [mul_assoc]
    _ = ⁅g, k⁆ * ⁅g, k'⁆ := by rw [h1]

private theorem caseB_inv_left (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (k : Q) :
    ⁅u⁻¹, k⁆ = ⁅u, k⁆⁻¹ := by
  have h1 : ⁅u⁻¹ * u, k⁆ = ⁅u, k⁆ * ⁅u⁻¹, k⁆ := caseB_mul_left h (caseB_commN h hu k)
  rw [inv_mul_cancel, commutatorElement_one_left] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

private theorem caseB_triple_swap (h : Cl3 Q a b N) (g g' k : Q) :
    ⁅⁅g, g'⁆, k⁆ = ⁅⁅g', g⁆, k⁆⁻¹ := by
  rw [← commutatorElement_inv g' g]
  exact caseB_inv_left h (caseB_dsub g' g) k

private theorem caseB_conj_right (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (x y : Q) :
    ⁅u, x * y * x⁻¹⁆ = ⁅u, y⁆ := by
  have hy : ⁅u, y⁆ ∈ N := caseB_commN h hu y
  have hxi : ⁅u, x⁻¹⁆ = ⁅u, x⁆⁻¹ := by
    have h1 := caseB_mul_right h (g := u) (k := x) (k' := x⁻¹) (caseB_commN h hu x⁻¹)
    rw [mul_inv_cancel, commutatorElement_one_right] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  rw [mul_assoc, caseB_mul_right h (caseB_commN h hu _), caseB_mul_right h (caseB_commN h hu _),
    hxi, ← mul_assoc, caseB_comm h hy, mul_assoc, mul_inv_cancel, mul_one]

private theorem caseB_triple_mul_left (h : Cl3 Q a b N) (g g' g'' k : Q) :
    ⁅⁅g * g', g''⁆, k⁆ = ⁅⁅g, g''⁆, k⁆ * ⁅⁅g', g''⁆, k⁆ := by
  have e : ⁅g * g', g''⁆ = ⁅g, ⁅g', g''⁆⁆ * (⁅g', g''⁆ * ⁅g, g''⁆) := by
    simp only [commutatorElement_def]
    group
  have hc : ⁅g, ⁅g', g''⁆⁆ ∈ N := caseB_commN' h (caseB_dsub g' g'') g
  rw [e, caseB_mul_central_left h hc]
  exact caseB_mul_left h (g := ⁅g', g''⁆) (g' := ⁅g, g''⁆) (caseB_commN h (caseB_dsub g g'') k)

private theorem caseB_triple_mul_mid (h : Cl3 Q a b N) (g g' g'' k : Q) :
    ⁅⁅g, g' * g''⁆, k⁆ = ⁅⁅g, g'⁆, k⁆ * ⁅⁅g, g''⁆, k⁆ := by
  have e : ⁅g, g' * g''⁆ = ⁅g, g'⁆ * (⁅g', ⁅g, g''⁆⁆ * ⁅g, g''⁆) := by
    simp only [commutatorElement_def]
    group
  have hc : ⁅g', ⁅g, g''⁆⁆ ∈ N := caseB_commN' h (caseB_dsub g g'') g'
  have e2 : ⁅g, g'⁆ * (⁅g', ⁅g, g''⁆⁆ * ⁅g, g''⁆) = ⁅g', ⁅g, g''⁆⁆ * (⁅g, g'⁆ * ⁅g, g''⁆) := by
    rw [← mul_assoc, caseB_comm h hc, mul_assoc]
  rw [e, e2, caseB_mul_central_left h hc,
    caseB_mul_left h (g := ⁅g, g'⁆) (g' := ⁅g, g''⁆) (caseB_commN h (caseB_dsub g g'') k)]
  exact (caseB_comm h (caseB_commN h (caseB_dsub g g'') k) _).symm

private theorem caseB_triple_mul_right (h : Cl3 Q a b N) (g g' k k' : Q) :
    ⁅⁅g, g'⁆, k * k'⁆ = ⁅⁅g, g'⁆, k⁆ * ⁅⁅g, g'⁆, k'⁆ :=
  caseB_mul_right h (caseB_commN h (caseB_dsub g g') k')

private theorem caseB_triple_mem (h : Cl3 Q a b N) (g g' k : Q) : ⁅⁅g, g'⁆, k⁆ ∈ N :=
  caseB_commN h (caseB_dsub g g') k

private theorem caseB_symm (h : Cl3 Q a b N) {y z : Q} (hyz : ⁅y, z⁆ = 1) (x : Q) :
    ⁅⁅x, y⁆, z⁆ = ⁅⁅x, z⁆, y⁆ := by
  have hw := commutatorElement_commutatorElement_conj_mul x y z
  have h1 : y * z * y⁻¹ = z := by
    rw [(commutatorElement_eq_one_iff_mul_comm.mp hyz)]
    group
  rw [h1, hyz, commutatorElement_one_left, mul_one, caseB_conj_right h (caseB_dsub z x),
    caseB_triple_swap h z x y] at hw
  exact mul_inv_eq_one.mp hw

private theorem caseB_E1 (h : Cl3 Q a b N) (hG2 : ∀ u ∈ dsub Q, b u * (a u)⁻¹ ∈ N) {x z : Q}
    (hx : b x = x) (hz : a z = z) (y : Q) : ⁅⁅x, b y⁆, z⁆ = a ⁅⁅x, y⁆, z⁆ := by
  have h1 : ⁅x, b y⁆ = b ⁅x, y⁆ := by rw [map_commutatorElement, hx]
  have hn := hG2 _ (caseB_dsub x y)
  have h2 : b ⁅x, y⁆ = (b ⁅x, y⁆ * (a ⁅x, y⁆)⁻¹) * a ⁅x, y⁆ := by group
  rw [h1, h2, caseB_mul_central_left h hn, map_commutatorElement a ⁅x, y⁆ z, hz]

private theorem caseB_d (h : Cl3 Q a b N) (hc : CaseBHyp Q a b N) {x y z : Q} (hx : b x = x)
    (hy : a y = y) (hz : a z = z) : ⁅⁅x, y⁆, z⁆ = 1 := by
  obtain ⟨⟨hNb, hNa⟩, hG2, hfa⟩ := hc
  have hQ2 : ∀ {p q : Q}, a p = p → a q = q → ⁅p, q⁆ = 1 := fun {p q} hp hq =>
    hfa _ (caseB_dsub p q) (by rw [map_commutatorElement, hp, hq])
  have hba : ∀ w : Q, a w = w → a (b w) = b w := fun w hw => by
    have := congrArg (fun f : MulAut Q => f w) h.bpair.comm
    simp only [MulAut.mul_apply] at this
    rw [this, hw]
  set w := ⁅⁅x, y⁆, z⁆ with hwdef
  have hwN : w ∈ N := caseB_triple_mem h x y z
  have h1 : ⁅⁅x, b y⁆, b z⁆ = a (a w) := by
    rw [caseB_E1 h hG2 hx (hba z hz) y, caseB_symm h (hQ2 hy (hba z hz)) x,
      caseB_E1 h hG2 hx hy z, caseB_symm h (hQ2 hz hy) x]
  have h2 : ⁅⁅x, b y⁆, b z⁆ = w := by
    have : ⁅⁅x, b y⁆, b z⁆ = b w := by
      rw [hwdef, map_commutatorElement, map_commutatorElement, hx]
    rw [this]
    exact hNb _ hwN
  have h3 : a (a w) = w := h1.symm.trans h2
  have h4 : a w = w := by
    have := congrArg a h3
    rw [caseB_cube h.bpair.a_cube] at this
    exact this.symm
  exact hNa w hwN h4

private theorem caseB_gen (hQ' : fixSub a ⊔ fixSub b = ⊤) {f : Q → Q}
    (hmul : ∀ x y, f (x * y) = f x * f y) (h1 : ∀ x, b x = x → f x = 1)
    (h2 : ∀ x, a x = x → f x = 1) (x : Q) : f x = 1 := by
  let φ : Q →* Q := MonoidHom.mk' f hmul
  have hle : fixSub a ⊔ fixSub b ≤ φ.ker :=
    sup_le (fun y hy => MonoidHom.mem_ker.mpr (h2 y hy))
      (fun y hy => MonoidHom.mem_ker.mpr (h1 y hy))
  rw [hQ'] at hle
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top x))

end Calc

section Main

variable {Q : Type*} [Group Q] [Finite Q] {a b : MulAut Q} {N : Subgroup Q}

private theorem caseB_Q1 (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseBHyp Q a b N) {g g' : Q}
    (hg : b g = g) (hg' : b g' = g') : ⁅g, g'⁆ ∈ N := by
  obtain ⟨⟨hNb, hNa⟩, hG2, hfa⟩ := hc
  have hud : ⁅g, g'⁆ ∈ dsub Q := caseB_dsub g g'
  have hbu : b ⁅g, g'⁆ = ⁅g, g'⁆ := by rw [map_commutatorElement, hg, hg']
  generalize ⁅g, g'⁆ = u at hud hbu ⊢
  have hn : b u * (a u)⁻¹ ∈ N := hG2 u hud
  rw [hbu] at hn
  have hn' : a u * u⁻¹ ∈ N := by
    have := N.inv_mem hn
    simpa [mul_inv_rev] using this
  have hx : u⁻¹ * a u ∈ N := by
    have h3 : u⁻¹ * a u = u⁻¹ * (a u * u⁻¹) * u⁻¹⁻¹ := by group
    rw [h3, caseB_conj h hn' u⁻¹]
    exact hn'
  have : N.Normal := ⟨fun n hn q => by rw [caseB_conj h hn q]; exact hn⟩
  obtain ⟨d, hd, hfix⟩ := exists_fixed_mul_mem hQ h.bpair.a_cube (caseB_N_inv h) hx
  have h1 : u * d = 1 := hfa _ ((dsub Q).mul_mem hud (caseB_N_le h hd)) hfix
  rw [eq_inv_of_mul_eq_one_left h1]
  exact N.inv_mem hd

private theorem caseB_c (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseBHyp Q a b N) {x z : Q}
    (hx : b x = x) (hz : b z = z) (y : Q) : ⁅⁅x, y⁆, z⁆ = 1 := by
  have hNb : ∀ n ∈ N, b n = n := hc.1.1
  let ψ : Q →* Q :=
    MonoidHom.mk' (fun y => ⁅⁅x, y⁆, z⁆) (fun y y' => caseB_triple_mul_mid h x y y' z)
  have hψb : ∀ y, ψ (b y) = ψ y := by
    intro y
    show ⁅⁅x, b y⁆, z⁆ = ⁅⁅x, y⁆, z⁆
    have h1 : ⁅⁅x, b y⁆, z⁆ = b ⁅⁅x, y⁆, z⁆ := by
      rw [map_commutatorElement, map_commutatorElement, hx, hz]
    rw [h1]
    exact hNb _ (caseB_triple_mem h x y z)
  have hker : ∀ y, b y ∈ ψ.ker ↔ y ∈ ψ.ker := fun y => by
    simp only [MonoidHom.mem_ker, hψb]
  have hy : y⁻¹ * b y ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψb, inv_mul_cancel]
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_mem hQ h.bpair.b_cube hker hy
  have h1 : ψ (y * n) = ψ y := by
    rw [map_mul, MonoidHom.mem_ker.mp hn, mul_one]
  have h2 : ψ (y * n) = 1 :=
    caseB_comm_one h (caseB_Q1 hQ h hc hx hfix) z
  exact h1.symm.trans h2

private theorem caseB_gens (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseBHyp Q a b N)
    {g g' k : Q} (hg : b g = g ∨ a g = g) (hg' : b g' = g' ∨ a g' = g')
    (hk : b k = k ∨ a k = k) : ⁅⁅g, g'⁆, k⁆ = 1 := by
  rcases hg with hg | hg <;> rcases hg' with hg' | hg'
  · exact caseB_comm_one h (caseB_Q1 hQ h hc hg hg') k
  · rcases hk with hk | hk
    · exact caseB_c hQ h hc hg hk g'
    · exact caseB_d h hc hg hg' hk
  · rw [caseB_triple_swap h g g' k]
    rcases hk with hk | hk
    · rw [caseB_c hQ h hc hg' hk g, inv_one]
    · rw [caseB_d h hc hg' hg hk, inv_one]
  · have hQ2 : ⁅g, g'⁆ = 1 :=
      hc.2.2 _ (caseB_dsub g g') (by rw [map_commutatorElement, hg, hg'])
    rw [hQ2, commutatorElement_one_left]

theorem caseB (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseBHyp Q a b N) : False := by
  have htop : fixSub a ⊔ fixSub b = ⊤ := h.bpair.sup_fix hQ h.four
  have R : ∀ g g' : Q, (b g = g ∨ a g = g) → (b g' = g' ∨ a g' = g') → ∀ k : Q, ⁅⁅g, g'⁆, k⁆ = 1 :=
    fun g g' hg hg' =>
      caseB_gen htop (f := fun k => ⁅⁅g, g'⁆, k⁆) (caseB_triple_mul_right h g g')
        (fun k hk => caseB_gens hQ h hc hg hg' (Or.inl hk))
        (fun k hk => caseB_gens hQ h hc hg hg' (Or.inr hk))
  have M : ∀ g : Q, (b g = g ∨ a g = g) → ∀ k g' : Q, ⁅⁅g, g'⁆, k⁆ = 1 :=
    fun g hg k =>
      caseB_gen htop (f := fun g' => ⁅⁅g, g'⁆, k⁆) (fun g' g'' => caseB_triple_mul_mid h g g' g'' k)
        (fun g' hg' => R g g' hg (Or.inl hg') k) (fun g' hg' => R g g' hg (Or.inr hg') k)
  have L : ∀ g g' k : Q, ⁅⁅g, g'⁆, k⁆ = 1 := fun g g' k =>
    caseB_gen htop (f := fun g₁ => ⁅⁅g₁, g'⁆, k⁆) (fun g₁ g₂ => caseB_triple_mul_left h g₁ g₂ g' k)
      (fun g₁ hg₁ => M g₁ (Or.inl hg₁) k g') (fun g₁ hg₁ => M g₁ (Or.inr hg₁) k g') g
  have hDc : dsub Q ≤ center Q := by
    refine Subgroup.commutator_le.2 (fun g _ g' _ => ?_)
    rw [Subgroup.mem_center_iff]
    intro k
    exact (commutatorElement_eq_one_iff_mul_comm.mp (L g g' k)).symm
  have hN : N ≤ ⊥ := by
    rw [h.N_eq]
    refine Subgroup.commutator_le.2 (fun u hu k _ => ?_)
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hDc hu) k).symm
  exact h.N_ne (le_bot_iff.mp hN)

end Main

end CFSG.GH74.E2
