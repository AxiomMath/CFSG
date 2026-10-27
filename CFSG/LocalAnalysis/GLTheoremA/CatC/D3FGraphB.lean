module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Lang.D4Three.UnitLayers
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FPair

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E27Lie
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]


theorem permLattice_add' {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (v w : Fin τ.rank → ℤ) :
    permLattice π (v + w) = permLattice π v + permLattice π w := by
  ext j
  simp [permLattice]

theorem coord_rel {α : MulAut ↥(adjointGroup Tag.D4 K)} (la : LayerAct Tag.D4 α (1 : K ≃+* K))
    {p : Equiv.Perm (D4Idx)}
    (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (τ := Tag.D4) p δ.1)
    {k : ℕ} {γ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ height γ = ((k + 1 : ℕ) : ℤ)) :
    ∃ f : K, ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K k →
      pc γ ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        f * pc (permLattice (τ := Tag.D4) p γ) (x : ModGL Tag.D4 K) := by
  let δ : UnitRoots Tag.D4 k := ⟨γ, hγ⟩
  refine ⟨la.f k δ, fun x hx => ?_⟩
  have hpos : IsRoot Tag.D4 γ ∧ 0 < height γ := UnitRoots.pos Tag.D4 δ
  have e : permLattice (τ := Tag.D4) p γ = (la.r k δ).1 := (hr k δ).symm
  have hc : pc (permLattice (τ := Tag.D4) p γ) (x : ModGL Tag.D4 K) =
      rootCoord (UnitRoots.pos Tag.D4 (la.r k δ)) (x : ModGL Tag.D4 K) := by
    rw [e]
    exact pc_of_pos _ _
  rw [pc_of_pos hpos, hc]
  exact la.coord k δ x hx

theorem rel_rA {α : MulAut ↥(adjointGroup Tag.D4 K)} (la : LayerAct Tag.D4 α (1 : K ≃+* K))
    {p : Equiv.Perm (D4Idx)}
    (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (τ := Tag.D4) p δ.1) (o : D4Idx) :
    ∃ f : K, ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 0 →
      pc (rA o) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        f * pc (rA (p o)) (x : ModGL Tag.D4 K) := by
  have h := coord_rel la hr (k := 0) (γ := rA o) ⟨(isPos_rA o).1, by rw [height_rA]; rfl⟩
  have e : permLattice (τ := Tag.D4) p (rA o) = rA (p o) := permLattice_single (τ := Tag.D4) p o
  rw [e] at h
  exact h

theorem rel_rB {α : MulAut ↥(adjointGroup Tag.D4 K)} (la : LayerAct Tag.D4 α (1 : K ≃+* K))
    {p : Equiv.Perm (D4Idx)}
    (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (τ := Tag.D4) p δ.1)
    (hp2 : p 2 = 2) {o : D4Idx} (ho : o ∈ ({0, 1, 3} : Finset (D4Idx))) :
    ∃ g : K, ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 1 →
      pc (rB o) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        g * pc (rB (p o)) (x : ModGL Tag.D4 K) := by
  have h := coord_rel la hr (k := 1) (γ := rB o)
    ⟨(isPos_rB o ho).1, by rw [(isPos_rB o ho).2]; rfl⟩
  have e : permLattice (τ := Tag.D4) p (rB o) = rB (p o) := by
    refine funext fun (j : D4Idx) => ?_
    have h1 : (p.symm j = o) ↔ (j = p o) := p.symm_apply_eq
    have h2 : (p.symm j = 2) ↔ (j = 2) := by rw [p.symm_apply_eq, hp2]
    simp only [rB, rA, permLattice, Function.comp_apply, Pi.add_apply, Pi.single_apply]
    simp only [h1, h2]
  rw [e] at h
  exact h

@[expose] def rootElt (γ : D4Vec) (c : K) : ↥(adjointGroup Tag.D4 K) :=
  ⟨pinnedX Tag.D4 K γ c, pinnedX_mem_adjointGroup (τ := Tag.D4) γ c⟩

theorem coe_rootElt (γ : D4Vec) (c : K) :
    ((rootElt γ c : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = pinnedX Tag.D4 K γ c := rfl

theorem rootElt_mem_unitN {γ : D4Vec} {k : ℕ} (hγ : IsRoot Tag.D4 γ ∧ height γ = ((k + 1 : ℕ) : ℤ))
    (c : K) : rootElt γ c ∈ unitN Tag.D4 K k := by
  refine mem_hs_pinnedX ⟨hγ.1, by rw [hγ.2]; positivity, by rw [hγ.2]⟩ c

theorem rootElt_rA_mem (o : D4Idx) (c : K) : rootElt (rA o) c ∈ unitN Tag.D4 K 0 :=
  rootElt_mem_unitN ⟨(isPos_rA o).1, by rw [height_rA]; rfl⟩ c

theorem pc_rootElt_rA [Finite K] (a o : D4Idx) (c : K) :
    pc (rA a) ((rootElt (rA o) c : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      if o = a then c else 0 :=
  pc_rA_pinnedX a o c

theorem f_two_eq_one [CharP K 3] {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (la : LayerAct Tag.D4 α (1 : K ≃+* K)) {p : Equiv.Perm D4Idx} (hp2 : p 2 = 2)
    (h3 : α ^ 3 = 1) {f : K}
    (hf : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 0 →
      pc (rA 2) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        f * pc (rA 2) (x : ModGL Tag.D4 K)) : f = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x : ↥(adjointGroup Tag.D4 K) := rootElt (rA 2) 1 with hx
  have hx0 : x ∈ unitN Tag.D4 K 0 := rootElt_rA_mem 2 1
  have hx1 : α x ∈ unitN Tag.D4 K 0 := la.stable 0 x hx0
  have hx2 : α (α x) ∈ unitN Tag.D4 K 0 := la.stable 0 _ hx1
  have e : α (α (α x)) = x := by
    have := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ x) h3
    simpa [pow_succ] using this
  have hpc : pc (rA 2) (x : ModGL Tag.D4 K) = 1 := by
    rw [hx, pc_rootElt_rA, if_pos rfl]
  have h : pc (rA 2) (x : ModGL Tag.D4 K) = f * (f * (f * pc (rA 2) (x : ModGL Tag.D4 K))) := by
    conv_lhs => rw [← e]
    rw [hf _ hx2, hf _ hx1, hf _ hx0]
  rw [hpc] at h
  have h' : (f - 1) ^ 3 = 0 := by
    rw [sub_pow_char]
    linear_combination (-1 : K) * h
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h')

theorem mem_hs_one {u : ↥(adjointGroup Tag.D4 K)} (hu : u ∈ unitN Tag.D4 K 0) :
    (u : ModGL Tag.D4 K) ∈ heightSeries Tag.D4 K 1 := hu

theorem mem_hs_two {w : ↥(adjointGroup Tag.D4 K)} (hw : w ∈ unitN Tag.D4 K 1) :
    (w : ModGL Tag.D4 K) ∈ heightSeries Tag.D4 K 2 := hw

theorem comm_mem_hs_two {u w : ↥(adjointGroup Tag.D4 K)} (hu : u ∈ unitN Tag.D4 K 0)
    (hw : w ∈ unitN Tag.D4 K 0) : ((⁅u, w⁆ : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      heightSeries Tag.D4 K 2 :=
  commutator_heightSeries_le K 1 1
    (Subgroup.commutator_mem_commutator (mem_hs_one hu) (mem_hs_one hw))

theorem coe_comm {u w : ↥(adjointGroup Tag.D4 K)} :
    ((⁅u, w⁆ : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      ⁅(u : ModGL Tag.D4 K), (w : ModGL Tag.D4 K)⁆ := rfl

theorem rB_pos {o : D4Idx} (ho : o ∈ ({0, 1, 3} : Finset D4Idx)) :
    IsRoot Tag.D4 (rB o) ∧ 0 < height (rB o) :=
  ⟨(isPos_rB o ho).1, by rw [(isPos_rB o ho).2]; norm_num⟩

theorem rel_R2 {α : MulAut ↥(adjointGroup Tag.D4 K)} (la : LayerAct Tag.D4 α (1 : K ≃+* K))
    {o' : D4Idx} (ho' : o' = 1 ∨ o' = 3) {f₀ g₀ f₂ : K}
    (h0 : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 0 →
      pc (rA 0) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        f₀ * pc (rA o') (x : ModGL Tag.D4 K))
    (h2 : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 0 →
      pc (rA 2) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        f₂ * pc (rA 2) (x : ModGL Tag.D4 K))
    (hg : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 1 →
      pc (rB 0) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        g₀ * pc (rB o') (x : ModGL Tag.D4 K)) :
    g₀ * cc (K := K) (rA o') (rA 2) = cc (rA 0) (rA 2) * f₀ * f₂ := by
  have ho'2 : o' ≠ 2 := by rcases ho' with rfl | rfl <;> decide
  have ho'0 : o' ≠ 0 := by rcases ho' with rfl | rfl <;> decide
  have ho'mem : o' ∈ ({0, 1, 3} : Finset D4Idx) := by rcases ho' with rfl | rfl <;> simp
  set x : ↥(adjointGroup Tag.D4 K) := rootElt (rA o') 1 with hx
  set y : ↥(adjointGroup Tag.D4 K) := rootElt (rA 2) 1 with hy
  have hx0 : x ∈ unitN Tag.D4 K 0 := rootElt_rA_mem o' 1
  have hy0 : y ∈ unitN Tag.D4 K 0 := rootElt_rA_mem 2 1
  have hαx : α x ∈ unitN Tag.D4 K 0 := la.stable 0 x hx0
  have hαy : α y ∈ unitN Tag.D4 K 0 := la.stable 0 y hy0
  set z : ↥(adjointGroup Tag.D4 K) := ⁅x, y⁆ with hz
  have hz1 : z ∈ unitN Tag.D4 K 1 := comm_mem_hs_two hx0 hy0
  have hne1 : ((rA o', rA 2) : D4Vec × D4Vec) ≠ (rA 2, rA o') := fun h =>
    ho'2 ((rA_inj _ _).1 (congrArg Prod.fst h))
  have hne0 : ((rA 0, rA 2) : D4Vec × D4Vec) ≠ (rA 2, rA 0) := fun h =>
    (by decide : (0 : D4Idx) ≠ 2) ((rA_inj _ _).1 (congrArg Prod.fst h))
  have hL : pc (rB o') (z : ModGL Tag.D4 K) = cc (K := K) (rA o') (rA 2) := by
    rw [pc_of_pos (rB_pos ho'mem), hz, coe_comm,
      rootCoord_pairs_two (by norm_num) (by norm_num) (mem_hs_one hx0) (mem_hs_one hy0)
        (rB_pos ho'mem) (by rw [(isPos_rB o' ho'mem).2]; norm_num) (d4Pairs_11_gen o' (by
          rcases ho' with rfl | rfl <;> simp)) hne1]
    simp [hx, hy, coe_rootElt, pc_rA_pinnedX, ho'2, Ne.symm ho'2]
  have hR : pc (rB 0) ((α z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      cc (K := K) (rA 0) (rA 2) * f₀ * f₂ := by
    have hαz : α z = ⁅α x, α y⁆ := map_commutatorElement α x y
    have e := rootCoord_pairs_two (by norm_num) (by norm_num) (mem_hs_one hαx) (mem_hs_one hαy)
      (rB_pos (by simp : (0 : D4Idx) ∈ ({0, 1, 3} : Finset D4Idx)))
      (by rw [(isPos_rB 0 (by simp)).2]; norm_num) (d4Pairs_11_gen 0 (Or.inl rfl)) hne0
    have a1 : pc (rA 0) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = f₀ := by
      rw [h0 x hx0, hx, coe_rootElt, pc_rA_pinnedX, if_pos rfl, mul_one]
    have a2 : pc (rA 2) ((α y : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = f₂ := by
      rw [h2 y hy0, hy, coe_rootElt, pc_rA_pinnedX, if_pos rfl, mul_one]
    have a3 : pc (rA 2) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = 0 := by
      rw [h2 x hx0, hx, coe_rootElt, pc_rA_pinnedX, if_neg ho'2, mul_zero]
    rw [pc_of_pos (rB_pos (by simp : (0 : D4Idx) ∈ ({0, 1, 3} : Finset D4Idx))), hαz, coe_comm,
      e]
    simp only [a1, a2, a3]
    ring
  have := hg z hz1
  rw [hL] at this
  rw [hR] at this
  exact this.symm

theorem rA_ne_rA {a b : D4Idx} (h : a ≠ b) : rA a ≠ rA b := fun h' => h ((rA_inj _ _).1 h')

theorem coe_comm_eq_one {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) {u w : ↥(adjointGroup Tag.D4 K)} (hu : u ∈ A)
    (hw : w ∈ A) : ⁅(u : ModGL Tag.D4 K), (w : ModGL Tag.D4 K)⁆ = 1 := by
  have h : ⁅u, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hcomm u hu w hw)
  have := congrArg (fun g : ↥(adjointGroup Tag.D4 K) => (g : ModGL Tag.D4 K)) h
  exact this

theorem claim_one {A : Subgroup ↥(adjointGroup Tag.D4 K)} (hA0 : A ≤ unitN Tag.D4 K 0)
    (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) {u w : ↥(adjointGroup Tag.D4 K)} (hu : u ∈ A)
    (hw : w ∈ A) :
    pc (rA 0) (u : ModGL Tag.D4 K) * pc (rA 2) (w : ModGL Tag.D4 K) =
      pc (rA 2) (u : ModGL Tag.D4 K) * pc (rA 0) (w : ModGL Tag.D4 K) := by
  have h0mem : (0 : D4Idx) ∈ ({0, 1, 3} : Finset D4Idx) := by simp
  have hne0 : ((rA 0, rA 2) : D4Vec × D4Vec) ≠ (rA 2, rA 0) := fun h =>
    (by decide : (0 : D4Idx) ≠ 2) ((rA_inj _ _).1 (congrArg Prod.fst h))
  have e := rootCoord_pairs_two (by norm_num) (by norm_num) (mem_hs_one (hA0 hu))
    (mem_hs_one (hA0 hw)) (rB_pos h0mem) (by rw [(isPos_rB 0 h0mem).2]; norm_num)
    (d4Pairs_11_gen 0 (Or.inl rfl)) hne0
  rw [coe_comm_eq_one hcomm hu hw, rootCoord_one] at e
  have h02 : rA 0 ≠ rA 2 := rA_ne_rA (by decide)
  have hanti : cc (K := K) (rA 2) (rA 0) = - cc (rA 0) (rA 2) :=
    cc_antisymm (isPos_rA 0) (isPos_rA 2) h02 (isPos_rB 0 h0mem).1
  have hne : cc (K := K) (rA 0) (rA 2) ≠ 0 :=
    cc_ne_zero (isPos_rA 0) (isPos_rA 2) h02 (isPos_rB 0 h0mem).1
  have h : cc (K := K) (rA 0) (rA 2) * (pc (rA 0) (u : ModGL Tag.D4 K) * pc (rA 2) (w : ModGL Tag.D4 K) -
      pc (rA 2) (u : ModGL Tag.D4 K) * pc (rA 0) (w : ModGL Tag.D4 K)) = 0 := by
    rw [hanti] at e
    linear_combination -e
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hne)

theorem claim_three {A : Subgroup ↥(adjointGroup Tag.D4 K)} (hA0 : A ≤ unitN Tag.D4 K 0)
    (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) {u : ↥(adjointGroup Tag.D4 K)} (hu : u ∈ A)
    (hu2 : pc (rA 2) (u : ModGL Tag.D4 K) ≠ 0) {w : ↥(adjointGroup Tag.D4 K)} (hw : w ∈ A)
    (hw3 : w ∈ unitN Tag.D4 K 3) : w ∈ unitN Tag.D4 K 4 := by
  have hT4 : IsRoot Tag.D4 rT4 ∧ 0 < height rT4 := ⟨isPos_rT4.1, by rw [isPos_rT4.2]; norm_num⟩
  have hT5 : IsRoot Tag.D4 rT5 ∧ 0 < height rT5 := ⟨isPos_rT5.1, by rw [isPos_rT5.2]; norm_num⟩
  have hw4 : (w : ModGL Tag.D4 K) ∈ heightSeries Tag.D4 K 4 := hw3
  have e := rootCoord_pairs_one (by norm_num) (by norm_num) (mem_hs_one (hA0 hu)) hw4 hT5
    (by rw [isPos_rT5.2]; norm_num) (d4Pairs_14_T5)
  rw [coe_comm_eq_one hcomm hu hw, rootCoord_one] at e
  have hne : rA 2 ≠ rT4 := by decide +kernel
  have hr5 : IsRoot Tag.D4 (rA 2 + rT4) := by
    have : rA 2 + rT4 = rT5 := by decide +kernel
    rw [this]; exact isPos_rT5.1
  have hcc : cc (K := K) (rA 2) rT4 ≠ 0 := cc_ne_zero (isPos_rA 2) hT4 hne hr5
  have hpc : pc rT4 (w : ModGL Tag.D4 K) = 0 := by
    have h : cc (K := K) (rA 2) rT4 * pc (rA 2) (u : ModGL Tag.D4 K) * pc rT4 (w : ModGL Tag.D4 K) = 0 :=
      e.symm
    exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero hcc hu2)
  refine unitPhi_ker Tag.D4 ⟨w, hw3⟩ ?_
  refine congrArg Multiplicative.ofAdd (funext fun δ => ?_)
  have hδ : δ.1 = rT4 := by
    have h1 : δ.1 ∈ d4RootsAt 4 := mem_d4RootsAt.2 ⟨δ.2.1, by have := δ.2.2; simpa using this⟩
    have h2 : ∀ γ ∈ d4RootsAt 4, γ = rT4 := by decide +kernel
    exact h2 _ h1
  have hpos := UnitRoots.pos Tag.D4 δ
  show rootCoord hpos (w : ModGL Tag.D4 K) = 0
  rw [← pc_of_pos hpos, hδ]
  exact hpc

theorem two_ne_zero_of_char3 [CharP K 3] : (2 : K) ≠ 0 := by
  intro h
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have : (1 : K) = 0 := by linear_combination h3 - h
  exact one_ne_zero this

theorem claim_two [CharP K 3] {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (la : LayerAct Tag.D4 α (1 : K ≃+* K)) {p : Equiv.Perm D4Idx}
    (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (τ := Tag.D4) p δ.1)
    (hp : (p 0 = 1 ∧ p 1 = 3 ∧ p 3 = 0 ∧ p 2 = 2) ∨ (p 0 = 3 ∧ p 1 = 0 ∧ p 3 = 1 ∧ p 2 = 2))
    (h3 : α ^ 3 = 1) {A : Subgroup ↥(adjointGroup Tag.D4 K)} (hA0 : A ≤ unitN Tag.D4 K 0)
    (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) (hfix : ∀ a ∈ A, α a = a)
    {u : ↥(adjointGroup Tag.D4 K)} (hu : u ∈ A) (hu0 : pc (rA 0) (u : ModGL Tag.D4 K) ≠ 0)
    {w : ↥(adjointGroup Tag.D4 K)} (hw : w ∈ A) (hw1 : w ∈ unitN Tag.D4 K 1) :
    w ∈ unitN Tag.D4 K 2 := by
  have hp2 : p 2 = 2 := by rcases hp with h | h <;> exact h.2.2.2
  have ho' : p 0 = 1 ∨ p 0 = 3 := by
    rcases hp with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨f₀, hf₀⟩ := rel_rA la hr 0
  obtain ⟨f₂, hf₂⟩ := rel_rA la hr 2
  obtain ⟨g₀, hg₀⟩ := rel_rB la hr hp2 (o := 0) (by simp)
  obtain ⟨g₁, hg₁⟩ := rel_rB la hr hp2 (o := 1) (by simp)
  obtain ⟨g₃, hg₃⟩ := rel_rB la hr hp2 (o := 3) (by simp)
  have hf₂' : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 0 →
      pc (rA 2) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        f₂ * pc (rA 2) (x : ModGL Tag.D4 K) := by
    intro x hx
    have := hf₂ x hx
    rwa [hp2] at this
  have hf2one : f₂ = 1 := f_two_eq_one la hp2 h3 hf₂'
  have hR2 := rel_R2 la ho' hf₀ hf₂' hg₀
  rw [hf2one, mul_one] at hR2
  have hJ := cc_jacobi_gen (K := K) ho'
  have hz' : pc (rB (p 0)) (w : ModGL Tag.D4 K) = 0 := by
    set o' := p 0 with ho'def
    have ho'2 : o' ≠ 2 := by rcases ho' with h | h <;> rw [h] <;> decide
    have ho'0 : o' ≠ 0 := by rcases ho' with h | h <;> rw [h] <;> decide
    have ho'mem : o' ∈ ({0, 1, 3} : Finset D4Idx) := by rcases ho' with h | h <;> rw [h] <;> simp
    have hC : IsRoot Tag.D4 (rC 0 o') ∧ height (rC 0 o') = 3 :=
      isPos_rC 0 (by simp) o' ho'mem (Ne.symm ho'0)
    have hC' : IsRoot Tag.D4 (rC 0 o') ∧ 0 < height (rC 0 o') := ⟨hC.1, by rw [hC.2]; norm_num⟩
    have hne : ((rA 0, rB o') : D4Vec × D4Vec) ≠ (rA o', rB 0) := fun h =>
      ho'0 ((rA_inj _ _).1 (congrArg Prod.fst h)).symm
    have e := rootCoord_pairs_two (by norm_num) (by norm_num) (mem_hs_one (hA0 hu)) (mem_hs_two hw1) hC'
      (by rw [hC.2]; norm_num) (d4Pairs_12_gen o' ho') hne
    rw [coe_comm_eq_one hcomm hu hw, rootCoord_one] at e
    have hu_rel : pc (rA 0) (u : ModGL Tag.D4 K) = f₀ * pc (rA o') (u : ModGL Tag.D4 K) := by
      have := hf₀ u (hA0 hu)
      rwa [hfix u hu] at this
    have hw_rel : pc (rB 0) (w : ModGL Tag.D4 K) = g₀ * pc (rB o') (w : ModGL Tag.D4 K) := by
      have := hg₀ w hw1
      rwa [hfix w hw] at this
    have hB0 : IsRoot Tag.D4 (rB 0) ∧ 0 < height (rB 0) := rB_pos (by simp)
    have hBo : IsRoot Tag.D4 (rB o') ∧ 0 < height (rB o') := rB_pos ho'mem
    have hv1 : rB o' + rA 0 = rC 0 o' := by rcases ho' with h | h <;> rw [h] <;> decide +kernel
    have hv2 : rB 0 + rA o' = rC 0 o' := by rcases ho' with h | h <;> rw [h] <;> decide +kernel
    have hne1 : rB o' ≠ rA 0 := fun h => by
      have := congrArg height h
      rw [(isPos_rB o' ho'mem).2, height_rA] at this
      omega
    have hne2 : rB 0 ≠ rA o' := fun h => by
      have := congrArg height h
      rw [(isPos_rB 0 (by simp)).2, height_rA] at this
      omega
    have hs : cc (K := K) (rB o') (rA 0) ≠ 0 :=
      cc_ne_zero hBo (isPos_rA 0) hne1 (by rw [hv1]; exact hC.1)
    have hanti1 : cc (K := K) (rA 0) (rB o') = - cc (rB o') (rA 0) :=
      cc_antisymm hBo (isPos_rA 0) hne1 (by rw [hv1]; exact hC.1)
    have hanti2 : cc (K := K) (rA o') (rB 0) = - cc (rB 0) (rA o') :=
      cc_antisymm hB0 (isPos_rA o') hne2 (by rw [hv2]; exact hC.1)
    have hε' : cc (K := K) (rA o') (rA 2) ≠ 0 :=
      cc_ne_zero (isPos_rA o') (isPos_rA 2) (rA_ne_rA ho'2) (isPos_rB o' ho'mem).1
    have hε₀ : cc (K := K) (rA 0) (rA 2) ≠ 0 :=
      cc_ne_zero (isPos_rA 0) (isPos_rA 2) (rA_ne_rA (by decide)) (isPos_rB 0 (by simp)).1
    have hkey : cc (K := K) (rB 0) (rA o') * g₀ = cc (rB o') (rA 0) * f₀ := by
      apply mul_right_cancel₀ (mul_ne_zero hε' hε₀)
      linear_combination (-(g₀ * cc (K := K) (rA o') (rA 2))) * hJ +
        (cc (K := K) (rB o') (rA 0) * cc (rA o') (rA 2)) * hR2
    rw [hanti1, hanti2, hu_rel, hw_rel] at e
    have hf₀ne : f₀ ≠ 0 := fun h => hu0 (by rw [hu_rel, h, zero_mul])
    have ha'ne : pc (rA o') (u : ModGL Tag.D4 K) ≠ 0 := fun h => hu0 (by rw [hu_rel, h, mul_zero])
    have h2 : (2 : K) * (cc (K := K) (rB o') (rA 0) * f₀ * pc (rA o') (u : ModGL Tag.D4 K)) *
        pc (rB o') (w : ModGL Tag.D4 K) = 0 := by
      linear_combination (1 : K) * e + (-(pc (rA o') (u : ModGL Tag.D4 K) * pc (rB o') (w : ModGL Tag.D4 K))) * hkey
    rcases mul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h two_ne_zero_of_char3
      · exact absurd h (mul_ne_zero (mul_ne_zero hs hf₀ne) ha'ne)
    · exact h
  refine unitPhi_ker Tag.D4 ⟨w, hw1⟩ ?_
  refine congrArg Multiplicative.ofAdd (funext fun δ => ?_)
  have hδ : δ.1 = rB 0 ∨ δ.1 = rB 1 ∨ δ.1 = rB 3 := by
    have h1 : δ.1 ∈ d4RootsAt 2 := mem_d4RootsAt.2 ⟨δ.2.1, by have := δ.2.2; simpa using this⟩
    have h2 : ∀ γ ∈ d4RootsAt 2, γ = rB 0 ∨ γ = rB 1 ∨ γ = rB 3 := by decide +kernel
    exact h2 _ h1
  have hpos := UnitRoots.pos Tag.D4 δ
  show rootCoord hpos (w : ModGL Tag.D4 K) = 0
  rw [← pc_of_pos hpos]
  have hw_fix : ∀ o : D4Idx, ∀ g : K, (∀ x : ↥(adjointGroup Tag.D4 K), x ∈ unitN Tag.D4 K 1 →
      pc (rB o) ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        g * pc (rB (p o)) (x : ModGL Tag.D4 K)) →
      pc (rB o) (w : ModGL Tag.D4 K) = g * pc (rB (p o)) (w : ModGL Tag.D4 K) := by
    intro o g hg
    have := hg w hw1
    rwa [hfix w hw] at this
  have r0 := hw_fix 0 g₀ hg₀
  have r1 := hw_fix 1 g₁ hg₁
  have r3 := hw_fix 3 g₃ hg₃
  rcases hp with ⟨h0, h1, h3', -⟩ | ⟨h0, h1, h3', -⟩
  · rw [h0] at hz' r0
    rw [h1] at r1
    rw [h3'] at r3
    have z1 : pc (rB 1) (w : ModGL Tag.D4 K) = 0 := hz'
    have z0 : pc (rB 0) (w : ModGL Tag.D4 K) = 0 := by rw [r0, z1, mul_zero]
    have z3 : pc (rB 3) (w : ModGL Tag.D4 K) = 0 := by rw [r3, z0, mul_zero]
    rcases hδ with h | h | h <;> rw [h]
    · exact z0
    · exact z1
    · exact z3
  · rw [h0] at hz' r0
    rw [h1] at r1
    rw [h3'] at r3
    have z3 : pc (rB 3) (w : ModGL Tag.D4 K) = 0 := hz'
    have z0 : pc (rB 0) (w : ModGL Tag.D4 K) = 0 := by rw [r0, z3, mul_zero]
    have z1 : pc (rB 1) (w : ModGL Tag.D4 K) = 0 := by rw [r1, z0, mul_zero]
    rcases hδ with h | h | h <;> rw [h]
    · exact z0
    · exact z1
    · exact z3

end CFSG.LocalAnalysis.GLTheoremA
