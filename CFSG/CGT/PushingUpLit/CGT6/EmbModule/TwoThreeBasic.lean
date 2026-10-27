module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NatSL2Mat
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.MinimalMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoThree

open CFSG.Quasithin CFSG.SL2MinimalFaithful Matrix

section Generators

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}

theorem commV_le_of_generators [Group.IsPerfect ↥G] {S : Subgroup V}
    (hSU : S ≤ commV G) {X : Set (MulAut V)} (hXG : ∀ g ∈ X, g ∈ G)
    (hXS : ∀ g ∈ X, ∀ u ∈ commV G, g u * u⁻¹ ∈ S) (hgen : Subgroup.closure X = G) :
    commV G ≤ S := by
  have hinvS : ∀ g ∈ G, (∀ u ∈ commV G, g u * u⁻¹ ∈ S) → ∀ u ∈ commV G, g⁻¹ u * u⁻¹ ∈ S := by
    intro g hg h u hu
    have hu' : g⁻¹ u ∈ commV G := commV_invariant (G.inv_mem hg) hu
    have h1 := h _ hu'
    rw [show g (g⁻¹ u) = u from MulAut.apply_inv_self (M := V) g u] at h1
    have : g⁻¹ u * u⁻¹ = (u * (g⁻¹ u)⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
    rw [this]
    exact inv_mem h1
  let K : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ G ∧ (∀ u ∈ commV G, g u * u⁻¹ ∈ S) ∧ (∀ x ∈ S, g x ∈ S) ∧
        ∀ x ∈ S, g⁻¹ x ∈ S}
      one_mem' := ⟨one_mem _, fun u _ => by simp, fun x hx => hx, fun x hx => hx⟩
      mul_mem' := by
        rintro g k ⟨hgG, hg1, hg2, hg3⟩ ⟨hkG, hk1, hk2, hk3⟩
        refine ⟨G.mul_mem hgG hkG, fun u hu => ?_, fun x hx => hg2 _ (hk2 x hx), fun x hx => ?_⟩
        · have hku : k u ∈ commV G := commV_invariant hkG hu
          have : (g * k) u * u⁻¹ = (g (k u) * (k u)⁻¹) * (k u * u⁻¹) := by
            rw [mul_assoc, inv_mul_cancel_left]; rfl
          rw [this]
          exact mul_mem (hg1 _ hku) (hk1 u hu)
        · rw [_root_.mul_inv_rev]
          exact hk3 _ (hg3 x hx)
      inv_mem' := by
        rintro g ⟨hgG, hg1, hg2, hg3⟩
        exact ⟨G.inv_mem hgG, hinvS g hgG hg1, hg3, fun x hx => by rw [inv_inv]; exact hg2 x hx⟩ }
  have hXK : ∀ g ∈ X, g ∈ K := by
    intro g hg
    have hgG := hXG g hg
    have h1 := hXS g hg
    refine ⟨hgG, h1, fun x hx => ?_, fun x hx => ?_⟩
    · have := mul_mem (h1 x (hSU hx)) hx
      rwa [inv_mul_cancel_right] at this
    · have h2 := hinvS g hgG h1 x (hSU hx)
      have := mul_mem h2 hx
      rwa [inv_mul_cancel_right] at this
  have hGK : G ≤ K := hgen.symm.le.trans ((Subgroup.closure_le K).mpr hXK)
  have h1 : commOn G (commV G) ≤ S := by
    unfold commOn
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, u, hu, rfl⟩
    exact (hGK hg).2.1 u hu
  exact (commV_le_commOn_commV G).trans h1

end Generators

structure NatData (K : Type*) [Field K] {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) where
  ρ : SpecialLinearGroup (Fin 2) K →* MulAut V
  range_eq : ρ.range = G
  inj : Function.Injective ρ
  β : ↥(commV G) →* Multiplicative (Fin 2 → K)
  surj : Function.Surjective β
  ker : β.ker = (commV G ⊓ fixV G).subgroupOf (commV G)
  equiv : ∀ (m : SpecialLinearGroup (Fin 2) K) (u : ↥(commV G)) (hu : ρ m u ∈ commV G),
    β ⟨ρ m u, hu⟩ = Multiplicative.ofAdd
      ((m : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)))

namespace NatData

variable {K : Type*} [Field K] {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}
  (D : NatData K G)

theorem ρ_mem (m : SpecialLinearGroup (Fin 2) K) : (D.ρ m : MulAut V) ∈ G :=
  by
    have h : D.ρ m ∈ D.ρ.range := ⟨m, rfl⟩
    rw [D.range_eq] at h
    exact h

theorem ρ_mem_commV (m : SpecialLinearGroup (Fin 2) K) {v : V} (hv : v ∈ commV G) :
    D.ρ m v ∈ commV G :=
  commV_invariant (D.ρ_mem m) hv

open Classical in
@[expose] noncomputable def coord (v : V) : Fin 2 → K :=
  if h : v ∈ commV G then Multiplicative.toAdd (D.β ⟨v, h⟩) else 0

theorem coord_of_mem {v : V} (hv : v ∈ commV G) :
    D.coord v = Multiplicative.toAdd (D.β ⟨v, hv⟩) := by
  simp [coord, hv]

theorem coord_mul {v w : V} (hv : v ∈ commV G) (hw : w ∈ commV G) :
    D.coord (v * w) = D.coord v + D.coord w := by
  rw [D.coord_of_mem (mul_mem hv hw), D.coord_of_mem hv, D.coord_of_mem hw]
  rw [show (⟨v * w, mul_mem hv hw⟩ : ↥(commV G)) = ⟨v, hv⟩ * ⟨w, hw⟩ from rfl, map_mul, toAdd_mul]

theorem coord_one : D.coord (1 : V) = 0 := by
  rw [D.coord_of_mem (one_mem _)]
  rw [show (⟨1, one_mem _⟩ : ↥(commV G)) = 1 from rfl, map_one, toAdd_one]

theorem coord_inv {v : V} (hv : v ∈ commV G) : D.coord v⁻¹ = - D.coord v := by
  have h := D.coord_mul hv (inv_mem hv)
  rw [mul_inv_cancel, D.coord_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem coord_ρ (m : SpecialLinearGroup (Fin 2) K) {v : V} (hv : v ∈ commV G) :
    D.coord (D.ρ m v) = (m : Matrix (Fin 2) (Fin 2) K).mulVec (D.coord v) := by
  rw [D.coord_of_mem (D.ρ_mem_commV m hv), D.coord_of_mem hv,
    D.equiv m ⟨v, hv⟩ (D.ρ_mem_commV m hv), toAdd_ofAdd]

theorem coord_eq_zero_iff {v : V} (hv : v ∈ commV G) :
    D.coord v = 0 ↔ v ∈ fixV G := by
  rw [D.coord_of_mem hv]
  constructor
  · intro h
    have h1 : (⟨v, hv⟩ : ↥(commV G)) ∈ D.β.ker := by
      rw [MonoidHom.mem_ker]
      exact toAdd_eq_zero.mp h
    rw [D.ker, Subgroup.mem_subgroupOf] at h1
    exact h1.2
  · intro h
    have h1 : (⟨v, hv⟩ : ↥(commV G)) ∈ D.β.ker := by
      rw [D.ker, Subgroup.mem_subgroupOf]
      exact ⟨hv, h⟩
    exact toAdd_eq_zero.mpr (MonoidHom.mem_ker.mp h1)

theorem exists_coord (w : Fin 2 → K) : ∃ v ∈ commV G, D.coord v = w := by
  obtain ⟨u, hu⟩ := D.surj (Multiplicative.ofAdd w)
  refine ⟨(u : V), u.2, ?_⟩
  rw [D.coord_of_mem u.2, hu, toAdd_ofAdd]

@[expose] def up (s : K) : MulAut V := D.ρ (unipotent s)

@[expose] def lo (s : K) : MulAut V := D.ρ (lowerUni s)

@[expose] def dg (l : Kˣ) : MulAut V := D.ρ (diagSL l)

theorem up_mem (s : K) : D.up s ∈ G := D.ρ_mem _
theorem lo_mem (s : K) : D.lo s ∈ G := D.ρ_mem _
theorem dg_mem (l : Kˣ) : D.dg l ∈ G := D.ρ_mem _

theorem up_add (s t : K) : D.up (s + t) = D.up s * D.up t := by
  unfold up; rw [unipotent_add, map_mul]

theorem up_zero : D.up (0 : K) = 1 := by
  unfold up; rw [unipotent_zero, map_one]

theorem dg_conj_up (l : Kˣ) (s : K) : D.dg l * D.up s * (D.dg l)⁻¹ = D.up ((l : K) ^ 2 * s) := by
  unfold dg up
  rw [← map_inv, ← map_mul, ← map_mul, diagSL_mul_unipotent]

theorem coord_up {v : V} (hv : v ∈ commV G) (s : K) :
    D.coord (D.up s v) = ![D.coord v 0 + s * D.coord v 1, D.coord v 1] := by
  unfold up
  rw [D.coord_ρ _ hv, unipotent_mulVec]

theorem coord_lo {v : V} (hv : v ∈ commV G) (s : K) :
    D.coord (D.lo s v) = ![D.coord v 0, s * D.coord v 0 + D.coord v 1] := by
  unfold lo
  rw [D.coord_ρ _ hv, lowerUni_mulVec]

theorem coord_dg {v : V} (hv : v ∈ commV G) (l : Kˣ) :
    D.coord (D.dg l v) = ![(l : K) * D.coord v 0, ((l⁻¹ : Kˣ) : K) * D.coord v 1] := by
  unfold dg
  rw [D.coord_ρ _ hv, diagSL_mulVec]

theorem up_mem_commV {v : V} (hv : v ∈ commV G) (s : K) : D.up s v ∈ commV G :=
  D.ρ_mem_commV _ hv

theorem lo_mem_commV {v : V} (hv : v ∈ commV G) (s : K) : D.lo s v ∈ commV G :=
  D.ρ_mem_commV _ hv

theorem dg_mem_commV {v : V} (hv : v ∈ commV G) (l : Kˣ) : D.dg l v ∈ commV G :=
  D.ρ_mem_commV _ hv

theorem coord_up_comm {v : V} (hv : v ∈ commV G) (s : K) :
    D.coord (D.up s v * v⁻¹) = ![s * D.coord v 1, 0] := by
  rw [D.coord_mul (D.up_mem_commV hv s) (inv_mem hv), D.coord_inv hv, D.coord_up hv]
  ext i
  fin_cases i <;> simp

theorem coord_lo_comm {v : V} (hv : v ∈ commV G) (s : K) :
    D.coord (D.lo s v * v⁻¹) = ![0, s * D.coord v 0] := by
  rw [D.coord_mul (D.lo_mem_commV hv s) (inv_mem hv), D.coord_inv hv, D.coord_lo hv]
  ext i
  fin_cases i <;> simp

@[expose] def P : Subgroup V where
  carrier := {v | v ∈ commV G ∧ D.coord v 1 = 0}
  one_mem' := ⟨one_mem _, by simp [D.coord_one]⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by rw [D.coord_mul ha.1 hb.1]; simp [ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [D.coord_inv ha.1]; simp [ha.2]⟩

@[expose] def P' : Subgroup V where
  carrier := {v | v ∈ commV G ∧ D.coord v 0 = 0}
  one_mem' := ⟨one_mem _, by simp [D.coord_one]⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by rw [D.coord_mul ha.1 hb.1]; simp [ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [D.coord_inv ha.1]; simp [ha.2]⟩

theorem mem_P {v : V} : v ∈ D.P ↔ v ∈ commV G ∧ D.coord v 1 = 0 := Iff.rfl
theorem A0_le_P : commV G ⊓ fixV G ≤ D.P := by
  rintro v ⟨hv, hf⟩
  refine ⟨hv, ?_⟩
  have := (D.coord_eq_zero_iff hv).mpr hf
  rw [this]; rfl

theorem P_le_U : D.P ≤ commV G := fun _ h => h.1

theorem up_comm_mem_P {v : V} (hv : v ∈ commV G) (s : K) : D.up s v * v⁻¹ ∈ D.P := by
  refine ⟨mul_mem (D.up_mem_commV hv s) (inv_mem hv), ?_⟩
  rw [D.coord_up_comm hv]; rfl

theorem lo_comm_mem_P' {v : V} (hv : v ∈ commV G) (s : K) : D.lo s v * v⁻¹ ∈ D.P' := by
  refine ⟨mul_mem (D.lo_mem_commV hv s) (inv_mem hv), ?_⟩
  rw [D.coord_lo_comm hv]; rfl

theorem hV_inv (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)

theorem fix_comm_of_sq (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} (hg : ∀ v, g (g v) = v) (v : V) :
    g (g v * v⁻¹) = g v * v⁻¹ := by
  rw [map_mul, hg, map_inv]
  calc v * (g v)⁻¹ = (g v * v⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
    _ = g v * v⁻¹ := hV_inv hV _

@[expose] def T : Subgroup (MulAut V) := (D.ρ.comp unipotentHom).range

theorem mem_T {g : MulAut V} : g ∈ D.T ↔ ∃ s : K, D.up s = g := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toAdd, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨Multiplicative.ofAdd s, rfl⟩

theorem T_le_G : D.T ≤ G := by
  intro g hg
  obtain ⟨s, rfl⟩ := D.mem_T.mp hg
  exact D.up_mem s

section CharTwo

variable [CharP K 2]

theorem up_up (s : K) (v : V) : D.up s (D.up s v) = v := by
  have h : D.up s * D.up s = 1 := by rw [← D.up_add, CharTwo.add_self_eq_zero, D.up_zero]
  have := congrArg (fun g : MulAut V => g v) h
  simpa using this

omit [CharP K 2] in
theorem exists_comm_mul_A0 {s : K} (hs : s ≠ 0) {p : V} (hp : p ∈ D.P) :
    ∃ u ∈ commV G, p * (D.up s u * u⁻¹)⁻¹ ∈ fixV G := by
  have hpU := hp.1
  have hc1 := hp.2
  obtain ⟨u, hu, hcu⟩ := D.exists_coord ![0, s⁻¹ * D.coord p 0]
  have hx : D.up s u * u⁻¹ ∈ commV G := mul_mem (D.up_mem_commV hu s) (inv_mem hu)
  have hcx : D.coord (D.up s u * u⁻¹) = D.coord p := by
    rw [D.coord_up_comm hu, hcu]
    ext i
    fin_cases i
    · simp [mul_inv_cancel_left₀ hs]
    · simp [hc1]
  refine ⟨u, hu, ?_⟩
  rw [← D.coord_eq_zero_iff (mul_mem hpU (inv_mem hx)), D.coord_mul hpU (inv_mem hx),
    D.coord_inv hx, hcx]
  simp

theorem up_fix_P (hV : ∀ v : V, v ^ 2 = 1) (s : K) {p : V} (hp : p ∈ D.P) : D.up s p = p := by
  by_cases hs : s = 0
  · subst hs
    rw [D.up_zero]
    rfl
  · obtain ⟨u, hu, ha⟩ := D.exists_comm_mul_A0 hs hp
    have hx2 : D.up s (D.up s u * u⁻¹) = D.up s u * u⁻¹ :=
      fix_comm_of_sq hV (D.up_up s) u
    have h1 : D.up s (p * (D.up s u * u⁻¹)⁻¹) = p * (D.up s u * u⁻¹)⁻¹ :=
      mem_fixV.mp ha _ (D.up_mem s)
    calc D.up s p = D.up s ((p * (D.up s u * u⁻¹)⁻¹) * (D.up s u * u⁻¹)) := by
          rw [inv_mul_cancel_right]
      _ = (p * (D.up s u * u⁻¹)⁻¹) * (D.up s u * u⁻¹) := by rw [map_mul, h1, hx2]
      _ = p := inv_mul_cancel_right _ _

theorem up_comm_mem_P_all (hV : ∀ v : V, v ^ 2 = 1) (s : K) (v : V) :
    D.up s v * v⁻¹ ∈ D.P := by
  by_cases hs : s = 0
  · subst hs
    rw [D.up_zero]
    simp
  · have hx : D.up s v * v⁻¹ ∈ commV G := Subgroup.subset_closure ⟨D.up s, D.up_mem s, v, rfl⟩
    refine ⟨hx, ?_⟩
    have h1 : D.up s (D.up s v * v⁻¹) = D.up s v * v⁻¹ :=
      fix_comm_of_sq hV (D.up_up s) v
    have h2 : D.coord (D.up s (D.up s v * v⁻¹)) 0 = D.coord (D.up s v * v⁻¹) 0 := by rw [h1]
    rw [D.coord_up hx] at h2
    simp at h2
    exact h2.resolve_left hs

theorem isElemAbelian2_T : IsElemAbelian2 D.T := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨s, rfl⟩ := D.mem_T.mp ha
    obtain ⟨t, rfl⟩ := D.mem_T.mp hb
    rw [← D.up_add, ← D.up_add, add_comm]
  · intro a ha
    obtain ⟨s, rfl⟩ := D.mem_T.mp ha
    rw [pow_two, ← D.up_add, CharTwo.add_self_eq_zero, D.up_zero]

theorem commV_T_le_P (hV : ∀ v : V, v ^ 2 = 1) : commV D.T ≤ D.P := by
  unfold commV
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨s, rfl⟩ := D.mem_T.mp hg
  exact D.up_comm_mem_P_all hV s v

theorem P_le_fixV_T (hV : ∀ v : V, v ^ 2 = 1) : D.P ≤ fixV D.T := by
  intro p hp g hg
  obtain ⟨s, rfl⟩ := D.mem_T.mp hg
  exact D.up_fix_P hV s hp

theorem commV_T_le_fixV_T (hV : ∀ v : V, v ^ 2 = 1) : commV D.T ≤ fixV D.T :=
  (D.commV_T_le_P hV).trans (D.P_le_fixV_T hV)

theorem P_eq_inf_fixV_T (hV : ∀ v : V, v ^ 2 = 1) : D.P = commV G ⊓ fixV D.T := by
  apply le_antisymm
  · exact le_inf D.P_le_U (D.P_le_fixV_T hV)
  · rintro v ⟨hv, hf⟩
    refine ⟨hv, ?_⟩
    have h1 : D.up 1 v = v := mem_fixV.mp hf _ (D.mem_T.mpr ⟨1, rfl⟩)
    have h2 := congrArg (fun w => D.coord w 0) h1
    simp only [D.coord_up hv] at h2
    simpa using h2

end CharTwo

end NatData

end CFSG.CGT.PushingUpLit.CGT6.TwoThree
