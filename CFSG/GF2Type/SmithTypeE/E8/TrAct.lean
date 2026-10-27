module

public import CFSG.GF2Type.SmithTypeE.E8.FactsCoord
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.SmithE8M
open CFSG.SeitzReduction.EPilot (pinnedElt)

section Act


theorem exists_of_xr_sub_ne_zero {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (w : Fin e7Data.d →₀ ZMod 2) {c : Fin e7Data.d}
    (h : (e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) w - w) c ≠ 0) :
    ∃ a : Fin e7Data.d, w a ≠ 0 ∧ e7Data.wt a ⬝ᵥ β = -1 ∧
      e7Data.wt c = e7Data.wt a + MinData.toWeight β := by
  rw [F.coord_rho_sub hβ] at h
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hc : (e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt c = e7Data.wt a + MinData.toWeight β)
  · rw [if_pos hc] at ha
    exact ⟨a, ha, hc.1, hc.2⟩
  · rw [if_neg hc] at ha
    exact absurd rfl ha

theorem xr_apply_eq_of_support {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (w : Fin e7Data.d →₀ ZMod 2) (hw : ∀ a : Fin e7Data.d, w a ≠ 0 → e7Data.wt a ⬝ᵥ β ≠ -1) :
    e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) w = w := by
  refine sub_eq_zero.mp ?_
  ext c
  by_contra h
  obtain ⟨a, ha, ha1, -⟩ := exists_of_xr_sub_ne_zero hβ w h
  exact hw a ha ha1

@[expose] noncomputable def actL (L : List (Fin (Tag.rank .E7) → ℤ))
    (w : Fin e7Data.d →₀ ZMod 2) : Fin e7Data.d →₀ ZMod 2 :=
  L.foldr (fun β u => e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) u) w

@[simp] theorem actL_nil (w : Fin e7Data.d →₀ ZMod 2) : actL [] w = w := rfl

theorem actL_cons (β : Fin (Tag.rank .E7) → ℤ) (L : List (Fin (Tag.rank .E7) → ℤ))
    (w : Fin e7Data.d →₀ ZMod 2) :
    actL (β :: L) w = e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) (actL L w) := rfl

theorem e7Rep56_listProd_apply (L : List (Fin (Tag.rank .E7) → ℤ)) (w : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) ((L.map fun β => pinnedElt .E7 β (1 : ZMod 2)).prod) w = actL L w := by
  induction L with
  | nil => simp
  | cons β L ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, actL_cons, ih]

theorem toWeight_neg (γ : Fin (Tag.rank .E7) → ℤ) :
    MinData.toWeight (-γ) = -MinData.toWeight γ := by
  funext j
  simp [MinData.toWeight, Finset.sum_neg_distrib]

theorem sum_toWeight_dot (l : List (Fin (Tag.rank .E7) → ℤ)) (γ : Fin (Tag.rank .E7) → ℤ)
    (h : ∀ γ' ∈ l, MinData.toWeight γ' ⬝ᵥ γ = 0) : (l.map MinData.toWeight).sum ⬝ᵥ γ = 0 := by
  induction l with
  | nil => simp
  | cons γ' l ih =>
    simp only [List.map_cons, List.sum_cons, add_dotProduct]
    rw [h γ' (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), add_zero]

theorem actL_eq_of_support (L : List (Fin (Tag.rank .E7) → ℤ)) (hL : ∀ γ ∈ L, IsRoot .E7 γ)
    (w : Fin e7Data.d →₀ ZMod 2)
    (hw : ∀ γ ∈ L, ∀ a : Fin e7Data.d, w a ≠ 0 → e7Data.wt a ⬝ᵥ γ ≠ -1) : actL L w = w := by
  induction L with
  | nil => rfl
  | cons γ L ih =>
    rw [actL_cons, ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      (fun x hx => hw x (List.mem_cons_of_mem _ hx))]
    exact xr_apply_eq_of_support (hL γ List.mem_cons_self) w (hw γ List.mem_cons_self)

theorem actL_sub_support (L : List (Fin (Tag.rank .E7) → ℤ)) (hL : ∀ γ ∈ L, IsRoot .E7 γ)
    (w : Fin e7Data.d →₀ ZMod 2) {c : Fin e7Data.d} (hc : (actL L w - w) c ≠ 0) :
    ∃ γ ∈ L, e7Data.wt c ⬝ᵥ γ = 1 := by
  induction L with
  | nil => simp at hc
  | cons γ L ih =>
    have e : actL (γ :: L) w - w =
        (e7Rep56 (ZMod 2) (pinnedElt .E7 γ 1) (actL L w) - actL L w) + (actL L w - w) := by
      rw [actL_cons]
      abel
    rw [e, Finsupp.add_apply] at hc
    by_cases h1 : (e7Rep56 (ZMod 2) (pinnedElt .E7 γ 1) (actL L w) - actL L w) c = 0
    · rw [h1, zero_add] at hc
      obtain ⟨γ', hγ', h⟩ := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hc
      exact ⟨γ', List.mem_cons_of_mem _ hγ', h⟩
    · exact ⟨γ, List.mem_cons_self, F.coord_rho_sub_ne_zero (hL γ List.mem_cons_self) _ h1⟩

theorem exists_of_xr_apply_ne_zero {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (w : Fin e7Data.d →₀ ZMod 2) {c : Fin e7Data.d}
    (h : (e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) w) c ≠ 0) :
    w c ≠ 0 ∨ ∃ a : Fin e7Data.d, w a ≠ 0 ∧ e7Data.wt a ⬝ᵥ β = -1 ∧
      e7Data.wt c = e7Data.wt a + MinData.toWeight β := by
  by_cases hwc : w c = 0
  · right
    rw [F.coord_rho hβ, hwc, zero_add] at h
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    by_cases hc : (e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt c = e7Data.wt a + MinData.toWeight β)
    · rw [if_pos hc] at ha
      exact ⟨a, ha, hc.1, hc.2⟩
    · rw [if_neg hc] at ha
      exact absurd rfl ha
  · exact Or.inl hwc

theorem actL_support_pair {β : Fin (Tag.rank .E7) → ℤ} (L : List (Fin (Tag.rank .E7) → ℤ))
    (hL : ∀ γ ∈ L, IsRoot .E7 γ ∧ MinData.toWeight γ ⬝ᵥ β = 0) (r : ℤ)
    (w : Fin e7Data.d →₀ ZMod 2) (hw : ∀ c : Fin e7Data.d, w c ≠ 0 → e7Data.wt c ⬝ᵥ β = r) :
    ∀ c : Fin e7Data.d, actL L w c ≠ 0 → e7Data.wt c ⬝ᵥ β = r := by
  induction L with
  | nil => exact hw
  | cons γ L ih =>
    have ih' := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    intro c hc
    rw [actL_cons] at hc
    rcases exists_of_xr_apply_ne_zero (hL γ List.mem_cons_self).1 _ hc with hu | ⟨a, ha, -, hca⟩
    · exact ih' c hu
    · rw [hca, add_dotProduct, (hL γ List.mem_cons_self).2, add_zero]
      exact ih' a ha

theorem single_add_single_ne_zero {a c d : Fin e7Data.d}
    (h : (Finsupp.single a 1 + Finsupp.single c 1 : Fin e7Data.d →₀ ZMod 2) d ≠ 0) :
    d = a ∨ d = c := by
  by_contra hne
  push Not at hne
  apply h
  simp [Finsupp.single_apply, Ne.symm hne.1, Ne.symm hne.2]

theorem actL_pivot (L : List (Fin (Tag.rank .E7) → ℤ)) (hL : ∀ γ ∈ L, IsRoot .E7 γ)
    (hnd : L.Nodup) (γ₀ : Fin (Tag.rank .E7) → ℤ) (h0 : γ₀ ∈ L) (a c : Fin e7Data.d)
    (ha : e7Data.wt a ⬝ᵥ γ₀ = -1) (hc : e7Data.wt c = e7Data.wt a + MinData.toWeight γ₀)
    (hothers : ∀ γ ∈ L, γ ≠ γ₀ → e7Data.wt a ⬝ᵥ γ ≠ -1 ∧ MinData.toWeight γ₀ ⬝ᵥ γ = 0) :
    actL L (Finsupp.single a 1) = Finsupp.single a 1 + Finsupp.single c 1 := by
  induction L with
  | nil => exact absurd h0 List.not_mem_nil
  | cons γ L ih =>
    rw [List.nodup_cons] at hnd
    by_cases hγ : γ = γ₀
    · have hfix : actL L (Finsupp.single a 1) = Finsupp.single a 1 := by
        refine actL_eq_of_support L (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _ ?_
        intro γ' hγ' d hd
        have hda : d = a := by
          by_contra hne
          exact hd (by simp [Finsupp.single_apply, Ne.symm hne])
        subst hda
        exact (hothers γ' (List.mem_cons_of_mem _ hγ')
          (fun h => hnd.1 (hγ.trans h.symm ▸ hγ'))).1
      rw [actL_cons, hfix, e7Rep56_pinnedElt_single (hL γ List.mem_cons_self) a, hγ, if_pos ha,
        wt_e7Shift hc]
    · have h0' : γ₀ ∈ L := (List.mem_cons.1 h0).resolve_left (fun h => hγ h.symm)
      have ih' := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hnd.2 h0'
        (fun x hx hne => hothers x (List.mem_cons_of_mem _ hx) hne)
      rw [actL_cons, ih']
      refine xr_apply_eq_of_support (hL γ List.mem_cons_self) _ ?_
      have hγo := hothers γ List.mem_cons_self hγ
      intro d hd
      rcases single_add_single_ne_zero hd with rfl | rfl
      · exact hγo.1
      · rw [hc, add_dotProduct, hγo.2, add_zero]
        exact hγo.1

theorem actL_coord_prod (L : List (Fin (Tag.rank .E7) → ℤ)) (hL : ∀ γ ∈ L, IsRoot .E7 γ)
    (hnd : L.Nodup)
    (horth : ∀ γ ∈ L, ∀ γ' ∈ L, γ ≠ γ' → MinData.toWeight γ ⬝ᵥ γ' = 0)
    (P : (Fin (Tag.rank .E7) → ℤ) → Bool) (a c : Fin e7Data.d)
    (hP : ∀ γ ∈ L, P γ = true → e7Data.wt a ⬝ᵥ γ = -1)
    (hc : e7Data.wt c = e7Data.wt a + ((L.filter P).map MinData.toWeight).sum) :
    (actL L (Finsupp.single a 1)) c = 1 := by
  induction L generalizing c with
  | nil =>
    simp only [List.filter_nil, List.map_nil, List.sum_nil, add_zero] at hc
    have hca : c = a := e7Data_valid.wt_injective hc
    subst hca
    simp
  | cons γ L ih =>
    rw [List.nodup_cons] at hnd
    have hLr : ∀ x ∈ L, IsRoot .E7 x := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hγr : IsRoot .E7 γ := hL γ List.mem_cons_self
    have hne : ∀ x ∈ L, x ≠ γ := fun x hx h => hnd.1 (h ▸ hx)
    have horthγ : ∀ x ∈ L, MinData.toWeight x ⬝ᵥ γ = 0 := fun x hx =>
      horth x (List.mem_cons_of_mem _ hx) γ List.mem_cons_self (hne x hx)
    have horthL : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → MinData.toWeight x ⬝ᵥ y = 0 :=
      fun x hx y hy hxy => horth x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy
    have hPL : ∀ x ∈ L, P x = true → e7Data.wt a ⬝ᵥ x = -1 :=
      fun x hx hpx => hP x (List.mem_cons_of_mem _ hx) hpx
    have horthS : (((L.filter P).map MinData.toWeight).sum) ⬝ᵥ γ = 0 :=
      sum_toWeight_dot _ _ (fun x hx => horthγ x (List.mem_filter.1 hx).1)
    have hsupp := actL_support_pair (β := γ) L
      (fun x hx => ⟨hLr x hx, horthγ x hx⟩) (e7Data.wt a ⬝ᵥ γ) (Finsupp.single a 1)
      (fun d hd => by
        have : d = a := by
          by_contra hne'
          exact hd (by simp [Finsupp.single_apply, Ne.symm hne'])
        rw [this])
    rw [actL_cons]
    by_cases hPγ : P γ = true
    ·
      have hfil : (γ :: L).filter P = γ :: L.filter P := by
        rw [List.filter_cons_of_pos hPγ]
      rw [hfil] at hc
      simp only [List.map_cons, List.sum_cons] at hc
      have haγ : e7Data.wt a ⬝ᵥ γ = -1 := hP γ List.mem_cons_self hPγ
      have hcγ : e7Data.wt c ⬝ᵥ γ = 1 := by
        rw [hc, add_dotProduct, add_dotProduct, haγ, F.tw_dot_self hγr, horthS]
        norm_num
      obtain ⟨c', hc'⟩ := exists_wt_eq_of_dotProduct (F.isRoot_neg hγr)
        (a := c) (by rw [dotProduct_neg, hcγ])
      rw [toWeight_neg] at hc'
      have hc'' : e7Data.wt c' = e7Data.wt a + ((L.filter P).map MinData.toWeight).sum := by
        rw [hc', hc]
        abel
      have hu1 : actL L (Finsupp.single a 1) c' = 1 := ih hLr hnd.2 horthL c' hPL hc''
      have hu0 : actL L (Finsupp.single a 1) c = 0 := by
        by_contra h
        have := hsupp c h
        rw [hcγ, haγ] at this
        norm_num at this
      rw [F.coord_rho hγr, hu0, zero_add]
      have hc'γ : e7Data.wt c' ⬝ᵥ γ = -1 := by
        rw [hc', add_dotProduct, hcγ, neg_dotProduct, F.tw_dot_self hγr]
        norm_num
      rw [Finset.sum_eq_single c']
      · rw [if_pos ⟨hc'γ, by rw [hc']; abel⟩, hu1]
      · intro a' _ ha'
        rw [if_neg]
        rintro ⟨-, h2⟩
        apply ha'
        refine e7Data_valid.wt_injective ?_
        show e7Data.wt a' = e7Data.wt c'
        rw [hc', h2]
        abel
      · intro h
        exact absurd (Finset.mem_univ c') h
    ·
      have hfil : (γ :: L).filter P = L.filter P := by
        rw [List.filter_cons_of_neg hPγ]
      rw [hfil] at hc
      have hu1 : actL L (Finsupp.single a 1) c = 1 := ih hLr hnd.2 horthL c hPL hc
      have hcγ : e7Data.wt c ⬝ᵥ γ = e7Data.wt a ⬝ᵥ γ := by
        rw [hc, add_dotProduct, horthS, add_zero]
      rw [F.coord_rho hγr, hu1]
      have hsum : ∑ a' : Fin e7Data.d, (if (e7Data.wt a' ⬝ᵥ γ = -1 ∧
          e7Data.wt c = e7Data.wt a' + MinData.toWeight γ) then
            (actL L (Finsupp.single a 1)) a' else 0) = 0 := by
        refine Finset.sum_eq_zero fun a' _ => ?_
        by_cases hcond : (e7Data.wt a' ⬝ᵥ γ = -1 ∧
            e7Data.wt c = e7Data.wt a' + MinData.toWeight γ)
        · rw [if_pos hcond]
          by_contra hne'
          have h1 := hsupp a' hne'
          have h2 : e7Data.wt c ⬝ᵥ γ = e7Data.wt a' ⬝ᵥ γ + 2 := by
            rw [hcond.2, add_dotProduct, F.tw_dot_self hγr]
          omega
        · rw [if_neg hcond]
      rw [hsum, add_zero]

@[expose] noncomputable def commSp (a : ↥(adjointGroup .E7 (ZMod 2))) :
    Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
  LinearMap.range (e7Rep56 (ZMod 2) a - 1)

theorem mem_commSp {a : ↥(adjointGroup .E7 (ZMod 2))} {v : Fin e7Data.d →₀ ZMod 2} :
    v ∈ commSp a ↔ ∃ y, e7Rep56 (ZMod 2) a y - y = v := by
  simp [commSp]

theorem commSp_conj (g a : ↥(adjointGroup .E7 (ZMod 2))) :
    commSp (g * a * g⁻¹) = (commSp a).map (e7Rep56 (ZMod 2) g) := by
  ext v
  rw [Submodule.mem_map, mem_commSp]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) g⁻¹ y) - e7Rep56 (ZMod 2) g⁻¹ y,
      mem_commSp.2 ⟨_, rfl⟩, ?_⟩
    exact (F.rep_conj_sub g a y).symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, rfl⟩ := mem_commSp.1 hw
    refine ⟨e7Rep56 (ZMod 2) g z, ?_⟩
    rw [F.rep_conj_sub, F.rep_inv_apply']

theorem finrank_commSp_conj (g a : ↥(adjointGroup .E7 (ZMod 2))) :
    Module.finrank (ZMod 2) (commSp (g * a * g⁻¹)) = Module.finrank (ZMod 2) (commSp a) := by
  refine le_antisymm ?_ ?_
  · rw [commSp_conj]
    exact Submodule.finrank_map_le _ _
  · have h : commSp a = (commSp (g * a * g⁻¹)).map (e7Rep56 (ZMod 2) g⁻¹) := by
      rw [← commSp_conj]
      congr 1
      group
    rw [h]
    exact Submodule.finrank_map_le _ _

theorem card_le_finrank_of_single_mem (S : Finset (Fin e7Data.d))
    (N : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2))
    (h : ∀ c ∈ S, (Finsupp.single c 1 : Fin e7Data.d →₀ ZMod 2) ∈ N) :
    S.card ≤ Module.finrank (ZMod 2) N := by
  have hle : Finsupp.supported (ZMod 2) (ZMod 2) (S : Set (Fin e7Data.d)) ≤ N := by
    intro v hv
    rw [Finsupp.mem_supported] at hv
    rw [F.finsupp_eq_sum_single v]
    exact Submodule.sum_mem _ fun c hc => h c (Finset.mem_coe.1 (hv hc))
  have h1 := Submodule.finrank_mono hle
  rw [(Finsupp.supportedEquivFinsupp (M := ZMod 2) (R := ZMod 2) (S : Set (Fin e7Data.d))).finrank_eq,
    Module.finrank_finsupp_self] at h1
  simpa using h1

theorem exists_fixed_vec8 {H : Type*} [Group H] {S : Subgroup H} (hS : IsPGroup 2 S)
    (ρ : H →* Module.End (ZMod 2) (Fin e7Data.d →₀ ZMod 2))
    (N : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2)) (hN : N ≠ ⊥)
    (hinv : ∀ s ∈ S, ∀ n ∈ N, ρ s n ∈ N) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ s ∈ S, ρ s n = n := by
  classical
  let act : MulAction S N :=
    { smul := fun s n => ⟨ρ s n, hinv s s.2 n n.2⟩
      one_smul := fun n => Subtype.ext (by
        show ρ ((1 : S) : H) (n : Fin e7Data.d →₀ ZMod 2) = n
        rw [Subgroup.coe_one, map_one, Module.End.one_apply])
      mul_smul := fun s t n => Subtype.ext (by
        show ρ ((s * t : S) : H) (n : Fin e7Data.d →₀ ZMod 2) =
          ρ (s : H) (ρ (t : H) (n : Fin e7Data.d →₀ ZMod 2))
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card N := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := N), Nat.card_zmod]
    have : Module.finrank (ZMod 2) N ≠ 0 := fun h => hN (Submodule.finrank_eq_zero.mp h)
    exact dvd_pow_self 2 this
  have h0 : (0 : N) ∈ MulAction.fixedPoints S N := fun s => Subtype.ext (map_zero _)
  obtain ⟨w, hw, hw0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd h0
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h.symm), fun s hs => ?_⟩
  have := hw ⟨s, hs⟩
  exact congrArg Subtype.val this

open CFSG.SeitzReduction (E7Pilot.e7Rep) in
theorem e7Rep_eq_prod (k : Fin 5) :
    CFSG.SeitzReduction.E7Pilot.e7Rep (ZMod 2) k =
      ((CFSG.SeitzReduction.E7Pilot.e7RepFrames k).map
        fun β => pinnedElt .E7 β (1 : ZMod 2)).prod := by
  apply Subtype.ext
  rw [CFSG.SeitzReduction.E7Pilot.coe_e7Rep, Subgroup.val_list_prod, List.map_map]
  rfl

theorem e7Rep_apply (k : Fin 5) (w : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) (CFSG.SeitzReduction.E7Pilot.e7Rep (ZMod 2) k) w =
      actL (CFSG.SeitzReduction.E7Pilot.e7RepFrames k) w := by
  rw [e7Rep_eq_prod, e7Rep56_listProd_apply]

end Act

end CFSG.GF2Type.SmithTypeE.E8
