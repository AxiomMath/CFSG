module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LieType.CentralExt.SL2Lift

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E]

section Defs

variable (π : E →* StatedSp r k)

@[expose] noncomputable def lamLift (i : Fin r) : SpecialLinearGroup (Fin 2) k →* E :=
  sl2Lift π (lam i)

@[expose] noncomputable def rhoLift (i j : Fin r) (hij : i ≠ j) :
    SpecialLinearGroup (Fin 2) k →* E :=
  sl2Lift π (rho i j hij)

@[expose] noncomputable def hLift (i : Fin r) (a : kˣ) : E := lamLift π i (sl2Diag a)

@[expose] noncomputable def hLiftRho (i j : Fin r) (hij : i ≠ j) (a : kˣ) : E :=
  rhoLift π i j hij (sl2Diag a)

@[expose] noncomputable def liftTorus : Subgroup E :=
  Subgroup.closure (Set.range fun p : Fin r × kˣ => hLift π p.1 p.2)

@[expose] noncomputable def vLift (i : Fin r) : E := lamLift π i sl2W

@[expose] noncomputable def vLiftRho (i j : Fin r) (hij : i ≠ j) : E := rhoLift π i j hij sl2W

omit [Field k] [Group E] π in
theorem succ_ne {i : Fin r} (h : i.val + 1 < r) : i ≠ ⟨i.val + 1, h⟩ :=
  Fin.ne_of_val_ne (by simp)

@[expose] noncomputable def sLift (i : Fin r) : E :=
  if h : i.val + 1 < r then vLiftRho π i ⟨i.val + 1, h⟩ (succ_ne h) else vLift π i

@[expose] noncomputable def liftWeyl : Subgroup E :=
  Subgroup.closure ((liftTorus π : Set E) ∪ Set.range (sLift π))

end Defs

structure Hyp (π : E →* StatedSp r k) : Prop where
  char : ringChar k ≠ 2
  surj : Function.Surjective π
  cen : π.ker ≤ Subgroup.center E
  two : IsPGroup 2 π.ker

variable [Finite k] [Finite E] {π : E →* StatedSp r k}

namespace Hyp

variable (hS : Hyp π)
include hS

theorem map_lift (α : SpecialLinearGroup (Fin 2) k →* StatedSp r k)
    (g : SpecialLinearGroup (Fin 2) k) : π (sl2Lift π α g) = α g :=
  map_sl2Lift hS.char hS.surj hS.cen hS.two α g

theorem lift_comp (α : SpecialLinearGroup (Fin 2) k →* StatedSp r k)
    (β : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k) :
    (sl2Lift π α).comp β = sl2Lift π (α.comp β) :=
  sl2Lift_comp hS.char hS.char hS.surj hS.cen hS.two α β

theorem commute_lift (α α' : SpecialLinearGroup (Fin 2) k →* StatedSp r k)
    (h : ∀ g g', Commute (α g) (α' g')) (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (sl2Lift π α g) (sl2Lift π α' g') :=
  commute_sl2Lift hS.char hS.char hS.surj hS.cen hS.two α α' h g g'

theorem conj_lift_apply {e : E} {α β : SpecialLinearGroup (Fin 2) k →* StatedSp r k}
    {γ : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k}
    (h : (MulAut.conj (π e)).toMonoidHom.comp α = β.comp γ) (g : SpecialLinearGroup (Fin 2) k) :
    e * sl2Lift π α g * e⁻¹ = sl2Lift π β (γ g) := by
  rw [conj_sl2Lift_apply hS.char hS.surj hS.cen hS.two α e g, h, ← hS.lift_comp]
  rfl

theorem conj_lift_apply' {e : E} {α β : SpecialLinearGroup (Fin 2) k →* StatedSp r k}
    (h : (MulAut.conj (π e)).toMonoidHom.comp α = β) (g : SpecialLinearGroup (Fin 2) k) :
    e * sl2Lift π α g * e⁻¹ = sl2Lift π β g := by
  rw [conj_sl2Lift_apply hS.char hS.surj hS.cen hS.two α e g, h]

end Hyp

section Identities

variable (hS : Hyp π)
include hS

theorem pi_hLift (i : Fin r) (a : kˣ) : π (hLift π i a) = torusHom (Pi.mulSingle i a) := by
  rw [hLift, lamLift, hS.map_lift, lam_sl2Diag]

theorem pi_vLift (i : Fin r) : π (vLift π i) = lam i sl2W := hS.map_lift _ _

theorem pi_vLiftRho {i j : Fin r} (hij : i ≠ j) : π (vLiftRho π i j hij) = rho i j hij sl2W :=
  hS.map_lift _ _

theorem commute_lamLift {i j : Fin r} (hij : i ≠ j) (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (lamLift π i g) (lamLift π j g') :=
  hS.commute_lift _ _ (commute_lam_lam hij) g g'

theorem vLiftRho_conj_lamLift_snd {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    vLiftRho π i j hij * lamLift π j g * (vLiftRho π i j hij)⁻¹ = lamLift π i g :=
  hS.conj_lift_apply' (by rw [pi_vLiftRho hS]; exact conj_rho_sl2W_comp_lam_snd hij) g

theorem vLiftRho_conj_lamLift_fst {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    vLiftRho π i j hij * lamLift π i g * (vLiftRho π i j hij)⁻¹ = lamLift π j g :=
  hS.conj_lift_apply' (by rw [pi_vLiftRho hS]; exact conj_rho_sl2W_comp_lam_fst hij) g

theorem commute_vLiftRho_lamLift {i j l : Fin r} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (g : SpecialLinearGroup (Fin 2) k) : Commute (vLiftRho π i j hij) (lamLift π l g) :=
  hS.commute_lift _ _ (commute_rho_lam hij hli hlj) sl2W g

theorem hLift_inv_conj_vLiftRho {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    (hLift π j a)⁻¹ * vLiftRho π i j hij * hLift π j a =
      hLiftRho π i j hij a * vLiftRho π i j hij := by
  have h := hS.conj_lift_apply (e := (hLift π j a)⁻¹) (β := rho i j hij)
    (by rw [map_inv, pi_hLift hS, ← lam_sl2Diag]; exact conj_lam_sl2Diag_inv_comp_rho hij a) sl2W
  rw [sl2ConjDiag_inv_sl2W, map_mul, inv_inv] at h
  exact h

theorem hLiftRho_eq {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    hLiftRho π i j hij a = hLift π i a * (hLift π j a)⁻¹ := by
  have h1 : vLiftRho π i j hij * hLift π j a * (vLiftRho π i j hij)⁻¹ = hLift π i a :=
    vLiftRho_conj_lamLift_snd hS hij (sl2Diag a)
  have h2 := hLift_inv_conj_vLiftRho hS hij a
  have h3 : hLift π i a * vLiftRho π i j hij =
      hLift π j a * (hLiftRho π i j hij a * vLiftRho π i j hij) := by
    rw [← h1, ← h2]
    group
  rw [← mul_assoc] at h3
  have h4 := mul_right_cancel h3
  rw [eq_inv_mul_of_mul_eq h4.symm]
  exact ((commute_lamLift hS hij _ _).inv_right).eq.symm

omit [Finite k] [Finite E] hS in
theorem vLiftRho_mul_self {i j : Fin r} (hij : i ≠ j) :
    vLiftRho π i j hij * vLiftRho π i j hij = hLiftRho π i j hij (-1) := by
  rw [vLiftRho, hLiftRho, ← map_mul, sl2W_mul_sl2W]

omit [Finite k] [Finite E] hS in
theorem vLift_mul_self (i : Fin r) : vLift π i * vLift π i = hLift π i (-1) := by
  rw [vLift, hLift, ← map_mul, sl2W_mul_sl2W]

omit [Finite k] [Finite E] hS in
theorem vLift_conj_hLift (i : Fin r) (a : kˣ) :
    vLift π i * hLift π i a * (vLift π i)⁻¹ = hLift π i a⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, vLift, hLift, hLift, ← map_mul, ← map_mul, sl2W_mul_sl2Diag]

theorem vLiftRho_conj_vLiftRho {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    vLiftRho π i j hij * vLiftRho π j l hjl * (vLiftRho π i j hij)⁻¹ =
      rhoLift π i l hil sl2W⁻¹ := by
  have h := hS.conj_lift_apply (e := vLiftRho π i j hij) (α := rho j l hjl) (β := rho i l hil)
    (by rw [pi_vLiftRho hS]; exact conj_rho_sl2W_comp_rho hij hjl hil) sl2W
  rwa [sl2ConjDiag_neg_one_sl2W] at h

theorem vLiftRho_inv_conj_vLiftRho {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (vLiftRho π j l hjl)⁻¹ * vLiftRho π i j hij * vLiftRho π j l hjl =
      rhoLift π i l hil sl2W⁻¹ := by
  have h := hS.conj_lift_apply (e := (vLiftRho π j l hjl)⁻¹) (α := rho i j hij)
    (β := rho i l hil)
    (by rw [map_inv, pi_vLiftRho hS]; exact conj_rho_sl2W_inv_comp_rho hij hjl hil) sl2W
  rwa [sl2ConjDiag_neg_one_sl2W, inv_inv] at h

theorem vLiftRho_braid {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    vLiftRho π j l hjl * vLiftRho π i j hij * vLiftRho π j l hjl =
      vLiftRho π i j hij * vLiftRho π j l hjl * vLiftRho π i j hij := by
  have h := (vLiftRho_conj_vLiftRho hS hij hjl hil).trans
    (vLiftRho_inv_conj_vLiftRho hS hij hjl hil).symm
  have h' := congrArg (fun x => vLiftRho π j l hjl * x * vLiftRho π i j hij) h
  simp only [mul_assoc, inv_mul_cancel, mul_inv_cancel_left, mul_one] at h'
  simpa only [mul_assoc] using h'

theorem commute_vLiftRho_vLiftRho {i j l m : Fin r} (hij : i ≠ j) (hlm : l ≠ m) (hil : i ≠ l)
    (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) :
    Commute (vLiftRho π i j hij) (vLiftRho π l m hlm) :=
  hS.commute_lift _ _ (commute_rho_rho hij hlm hil him hjl hjm) _ _

theorem commute_vLiftRho_vLift {i j l : Fin r} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    Commute (vLiftRho π i j hij) (vLift π l) :=
  commute_vLiftRho_lamLift hS hij hli hlj sl2W

theorem commute_vLift_vLift {i j : Fin r} (hij : i ≠ j) : Commute (vLift π i) (vLift π j) :=
  commute_lamLift hS hij _ _

end Identities

section Torus

omit [Finite k] [Finite E] in
theorem hLift_mem (i : Fin r) (a : kˣ) : hLift π i a ∈ liftTorus π :=
  Subgroup.subset_closure ⟨(i, a), rfl⟩

variable (hS : Hyp π)
include hS

theorem hLiftRho_mem {i j : Fin r} (hij : i ≠ j) (a : kˣ) : hLiftRho π i j hij a ∈ liftTorus π := by
  rw [hLiftRho_eq hS]
  exact mul_mem (hLift_mem _ _) (inv_mem (hLift_mem _ _))

theorem commute_hLift (i j : Fin r) (a b : kˣ) : Commute (hLift π i a) (hLift π j b) := by
  by_cases hij : i = j
  · subst hij
    rw [Commute, SemiconjBy, hLift, hLift, ← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm a b]
  · exact commute_lamLift hS hij _ _

theorem liftTorus_commute {x y : E} (hx : x ∈ liftTorus π) (hy : y ∈ liftTorus π) :
    Commute x y := by
  have hcomm := Subgroup.isMulCommutative_closure (k := Set.range fun p : Fin r × kˣ =>
    hLift π p.1 p.2) (by
      rintro _ ⟨⟨i, a⟩, rfl⟩ _ ⟨⟨j, b⟩, rfl⟩ _
      exact commute_hLift hS i j a b)
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : liftTorus π) ⟨y, hy⟩)

omit [Finite k] [Finite E] hS in
theorem noncommProd_univ_fin {M : Type*} [Monoid M] {n : ℕ} (f : Fin n → M)
    (comm : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise (Function.onFun Commute f)) :
    Finset.univ.noncommProd f comm = (List.ofFn f).prod := by
  have key : ∀ (m : Multiset M) (_ : m = ↑(List.ofFn f)) (c : Set.Pairwise {x | x ∈ m} Commute),
      m.noncommProd c = (List.ofFn f).prod := by
    rintro _ rfl c
    exact Multiset.noncommProd_coe _ _
  exact key _ (Fin.univ_val_map f) _

theorem pairwise_commute_lamLift :
    Pairwise fun i j => ∀ x y : kˣ,
      Commute (((lamLift π i).comp sl2Diag) x) (((lamLift π j).comp sl2Diag) y) :=
  fun _ _ hij _ _ => commute_lamLift hS hij _ _

noncomputable def thetaHom : (Fin r → kˣ) →* E :=
  MonoidHom.noncommPiCoprod (fun i => (lamLift π i).comp sl2Diag) (pairwise_commute_lamLift hS)

theorem thetaHom_mulSingle (i : Fin r) (a : kˣ) : thetaHom hS (Pi.mulSingle i a) = hLift π i a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem thetaHom_apply (t : Fin r → kˣ) :
    thetaHom hS t = (List.ofFn fun i => hLift π i (t i)).prod := by
  rw [thetaHom, MonoidHom.noncommPiCoprod_apply]
  exact noncommProd_univ_fin _ _

theorem comp_thetaHom : π.comp (thetaHom hS) = torusHom :=
  MonoidHom.pi_ext fun i a => by
    rw [MonoidHom.comp_apply, thetaHom_mulSingle, pi_hLift hS]

theorem thetaHom_injective : Function.Injective (thetaHom hS) := fun s t h =>
  torusHom_injective (by rw [← comp_thetaHom hS, MonoidHom.comp_apply, MonoidHom.comp_apply, h])

theorem range_thetaHom : (thetaHom hS).range = liftTorus π := by
  apply le_antisymm
  · rw [thetaHom, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    exact hLift_mem _ _
  · rw [liftTorus, Subgroup.closure_le]
    rintro _ ⟨⟨i, a⟩, rfl⟩
    exact ⟨Pi.mulSingle i a, thetaHom_mulSingle hS i a⟩

end Torus

section Weyl

omit [Finite k] [Finite E] in
theorem liftTorus_le_liftWeyl : liftTorus π ≤ liftWeyl π :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

omit [Finite k] [Finite E] in
theorem sLift_mem (i : Fin r) : sLift π i ∈ liftWeyl π :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

omit [Finite k] [Finite E] in
theorem sLift_of_lt {i : Fin r} (h : i.val + 1 < r) :
    sLift π i = vLiftRho π i ⟨i.val + 1, h⟩ (succ_ne h) := by
  rw [sLift, dite_eq_left h]

omit [Finite k] [Finite E] in
theorem sLift_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) : sLift π i = vLift π i := by
  rw [sLift, dite_eq_right h]

omit [Finite k] [Finite E] in
theorem mem_normalizer_liftTorus {x : E} (h1 : ∀ i a, x * hLift π i a * x⁻¹ ∈ liftTorus π)
    (h2 : ∀ i a, x⁻¹ * hLift π i a * x ∈ liftTorus π) :
    x ∈ Subgroup.normalizer (liftTorus π : Set E) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, liftTorus, Subgroup.closure_le]
    rintro _ ⟨⟨i, a⟩, rfl⟩
    exact h1 i a
  · rw [liftTorus, Subgroup.closure_le]
    rintro _ ⟨⟨i, a⟩, rfl⟩
    exact ⟨x⁻¹ * hLift π i a * x, h2 i a, by simp [mul_assoc]⟩

variable (hS : Hyp π)
include hS

theorem vLiftRho_mem_normalizer {i j : Fin r} (hij : i ≠ j) :
    vLiftRho π i j hij ∈ Subgroup.normalizer (liftTorus π : Set E) := by
  have hj : ∀ a, vLiftRho π i j hij * hLift π j a * (vLiftRho π i j hij)⁻¹ = hLift π i a :=
    fun a => vLiftRho_conj_lamLift_snd hS hij (sl2Diag a)
  have hi : ∀ a, vLiftRho π i j hij * hLift π i a * (vLiftRho π i j hij)⁻¹ = hLift π j a :=
    fun a => vLiftRho_conj_lamLift_fst hS hij (sl2Diag a)
  have hc : ∀ l, l ≠ i → l ≠ j → ∀ a, Commute (vLiftRho π i j hij) (hLift π l a) :=
    fun l hli hlj a => commute_vLiftRho_lamLift hS hij hli hlj (sl2Diag a)
  refine mem_normalizer_liftTorus (fun l a => ?_) (fun l a => ?_)
  · by_cases hli : l = i
    · subst hli
      exact (hi a).symm ▸ hLift_mem _ _
    by_cases hlj : l = j
    · subst hlj
      exact (hj a).symm ▸ hLift_mem _ _
    rw [(hc l hli hlj a).eq, mul_inv_cancel_right]
    exact hLift_mem _ _
  · by_cases hli : l = i
    · subst hli
      rw [← hj a]
      simpa [mul_assoc] using hLift_mem (π := π) j a
    by_cases hlj : l = j
    · subst hlj
      rw [← hi a]
      simpa [mul_assoc] using hLift_mem (π := π) i a
    rw [(hc l hli hlj a).inv_left.eq, inv_mul_cancel_right]
    exact hLift_mem _ _

theorem vLift_mem_normalizer (i : Fin r) :
    vLift π i ∈ Subgroup.normalizer (liftTorus π : Set E) := by
  have hc : ∀ l, l ≠ i → ∀ a, Commute (vLift π i) (hLift π l a) :=
    fun l hli a => commute_lamLift hS (Ne.symm hli) sl2W (sl2Diag a)
  refine mem_normalizer_liftTorus (fun l a => ?_) (fun l a => ?_)
  · by_cases hli : l = i
    · subst hli
      rw [vLift_conj_hLift]
      exact hLift_mem _ _
    rw [(hc l hli a).eq, mul_inv_cancel_right]
    exact hLift_mem _ _
  · by_cases hli : l = i
    · subst hli
      have h := vLift_conj_hLift (π := π) l a⁻¹
      rw [inv_inv] at h
      rw [← h]
      simpa [mul_assoc] using hLift_mem (π := π) l a⁻¹
    rw [(hc l hli a).inv_left.eq, inv_mul_cancel_right]
    exact hLift_mem _ _

theorem sLift_mem_normalizer (i : Fin r) :
    sLift π i ∈ Subgroup.normalizer (liftTorus π : Set E) := by
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h]
    exact vLiftRho_mem_normalizer hS _
  · rw [sLift_of_not_lt h]
    exact vLift_mem_normalizer hS i

theorem liftWeyl_le_normalizer : liftWeyl π ≤ Subgroup.normalizer (liftTorus π : Set E) := by
  rw [liftWeyl, Subgroup.closure_le]
  rintro x (hx | ⟨i, rfl⟩)
  · exact Subgroup.le_normalizer hx
  · exact sLift_mem_normalizer hS i

theorem vLiftRho_conj_vLift {i j : Fin r} (hij : i ≠ j) :
    vLiftRho π i j hij * vLift π j * (vLiftRho π i j hij)⁻¹ = vLift π i :=
  vLiftRho_conj_lamLift_snd hS hij sl2W

theorem vLift_mem (i : Fin r) : vLift π i ∈ liftWeyl π := by
  suffices h : ∀ m : ℕ, ∀ i : Fin r, i.val + m + 1 = r → vLift π i ∈ liftWeyl π from
    h (r - 1 - i.val) i (by omega)
  intro m
  induction m with
  | zero =>
    intro i hi
    rw [← sLift_of_not_lt (by omega)]
    exact sLift_mem i
  | succ m ih =>
    intro i hi
    have hlt : i.val + 1 < r := by omega
    rw [← vLiftRho_conj_vLift hS (succ_ne hlt)]
    have hs := sLift_mem (π := π) i
    rw [sLift_of_lt hlt] at hs
    exact mul_mem (mul_mem hs (ih ⟨i.val + 1, hlt⟩ (by simp only; omega))) (inv_mem hs)

theorem pi_mem_monomialGL {n : E} (hn : n ∈ liftWeyl π) :
    ((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) ∈ monomialGL (Fin r ⊕ Fin r) k := by
  have hle : liftWeyl π ≤ (monomialGL (Fin r ⊕ Fin r) k).comap ((StatedSp r k).subtype.comp π) := by
    rw [liftWeyl, Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · obtain ⟨t, rfl⟩ := (range_thetaHom hS).ge hx
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change ((π (thetaHom hS t) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) ∈
        monomialGL (Fin r ⊕ Fin r) k
      rw [← MonoidHom.comp_apply π, comp_thetaHom hS]
      exact mem_monomialGL (isLinePerm_torusHom t)
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      change ((π (sLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) ∈
        monomialGL (Fin r ⊕ Fin r) k
      by_cases h : i.val + 1 < r
      · rw [sLift_of_lt h, pi_vLiftRho hS]
        exact mem_monomialGL (isLinePerm_rho_sl2W _)
      · rw [sLift_of_not_lt h, pi_vLift hS]
        exact mem_monomialGL (isLinePerm_lam_sl2W _)
  exact hle hn

noncomputable def weylHom : liftWeyl π →* signedPermGroup r :=
  (linePerm.comp (((StatedSp r k).subtype.comp (π.comp (liftWeyl π).subtype)).codRestrict
    (monomialGL (Fin r ⊕ Fin r) k) fun n => pi_mem_monomialGL hS n.2)).codRestrict
    (signedPermGroup r) fun n => IsLinePerm.mem_signedPermGroup (π n).2 (isLinePerm_linePerm _)

theorem isLinePerm_weylHom (n : liftWeyl π) :
    IsLinePerm (weylHom hS n : Equiv.Perm (Fin r ⊕ Fin r))
      (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) :=
  isLinePerm_linePerm _

theorem weylHom_eq {n : liftWeyl π} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) :
    (weylHom hS n : Equiv.Perm (Fin r ⊕ Fin r)) = σ :=
  linePerm_eq h

end Weyl

end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
