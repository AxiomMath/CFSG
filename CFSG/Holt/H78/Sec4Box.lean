module

public import CFSG.Holt.H78.Sec4Toolkit
public import CFSG.Holt.H78.Lemma27Real

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt Equiv
open scoped Pointwise

section Perm

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_mul_self_eq_one_forall_apply_ne (h : Even (Fintype.card Ψ)) :
    ∃ σ : Perm Ψ, σ * σ = 1 ∧ ∀ x, σ x ≠ x := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨σ, hσ⟩ := (Perm.exists_with_cycleType_iff Ψ (m := Multiset.replicate k 2)).2
    ⟨by rw [Multiset.sum_replicate, smul_eq_mul]; omega,
      fun a ha => (Multiset.eq_of_mem_replicate ha).ge⟩
  have h2 : σ ^ 2 = 1 := Perm.pow_prime_eq_one_iff.2 fun c hc => by
    rw [hσ] at hc
    exact Multiset.eq_of_mem_replicate hc
  have hsupp : σ.support = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [← Perm.sum_cycleType, hσ, Multiset.sum_replicate, smul_eq_mul]
    omega)
  refine ⟨σ, by rw [← sq, h2], fun x hx => ?_⟩
  have hx' : x ∈ σ.support := hsupp ▸ Finset.mem_univ x
  exact Perm.mem_support.mp hx' hx

theorem odd_card_of_mul_self_eq_one_of_existsUnique {w : Perm Ψ} (hw : w * w = 1)
    (hw1 : ∃! x, w x = x) : Odd (Fintype.card Ψ) := by
  obtain ⟨x₀, hx₀, hu⟩ := hw1
  have hsupp : w.support = Finset.univ.erase x₀ := by
    ext x
    rw [Perm.mem_support, Finset.mem_erase, Ne]
    exact ⟨fun h => ⟨fun hx => h (hx ▸ hx₀), Finset.mem_univ x⟩,
      fun h hx => h.1 (hu x hx)⟩
  have h2 := Perm.two_dvd_card_support (σ := w) (by rw [sq, hw])
  rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ] at h2
  have : 0 < Fintype.card Ψ := Fintype.card_pos_iff.mpr ⟨x₀⟩
  rw [Nat.odd_iff]
  omega

theorem exists_mem_longInv_perm_apply_eq {Λ : Set Ψ} (hΨ : Odd (Fintype.card Ψ))
    (h3 : 3 ≤ Fintype.card Ψ) {w : Perm Λ} (hw : w * w = 1) (hw1 : ∃! x, w x = x) :
    ∃ y ∈ longInv (Perm Ψ) Ψ, (∀ x (hx : x ∈ Λ), y x = w ⟨x, hx⟩) ∧ ∀ x, y x ∈ Λ ↔ x ∈ Λ := by
  classical
  have hΛ := odd_card_of_mul_self_eq_one_of_existsUnique hw hw1
  have hc : Even (Fintype.card {x // ¬ x ∈ Λ}) := by
    rw [Fintype.card_subtype_compl, Nat.even_sub (Fintype.card_subtype_le _)]
    exact iff_of_false (Nat.not_even_iff_odd.mpr hΨ) (Nat.not_even_iff_odd.mpr hΛ)
  obtain ⟨f, hf, hf1⟩ := exists_mul_self_eq_one_forall_apply_ne hc
  obtain ⟨x₀, hx₀, hu⟩ := hw1
  set y : Perm Ψ := Perm.subtypeCongr (p := (· ∈ Λ)) w f
  have hyΛ : ∀ x (hx : x ∈ Λ), y x = w ⟨x, hx⟩ := fun x hx => Perm.subtypeCongr.left_apply _ _ hx
  have hyc : ∀ x (hx : ¬ x ∈ Λ), y x = f ⟨x, hx⟩ :=
    fun x hx => Perm.subtypeCongr.right_apply _ _ hx
  have hmem : ∀ x, y x ∈ Λ ↔ x ∈ Λ := fun x => by
    by_cases hx : x ∈ Λ
    · exact iff_of_true (hyΛ x hx ▸ (w ⟨x, hx⟩).2) hx
    · exact iff_of_false (hyc x hx ▸ (f ⟨x, hx⟩).2) hx
  have hyy : y * y = 1 := by
    ext x
    rw [Perm.mul_apply, Perm.one_apply]
    by_cases hx : x ∈ Λ
    · rw [hyΛ x hx, hyΛ _ (w ⟨x, hx⟩).2, Subtype.coe_eta, ← Perm.mul_apply, hw, Perm.one_apply]
    · rw [hyc x hx, hyc _ (f ⟨x, hx⟩).2, Subtype.coe_eta, ← Perm.mul_apply, hf, Perm.one_apply]
  have hfix : ∀ x : Ψ, y • x = x ↔ x = x₀ := fun x => by
    rw [Perm.smul_def]
    by_cases hx : x ∈ Λ
    · rw [hyΛ x hx]
      refine ⟨fun h => congrArg Subtype.val (hu ⟨x, hx⟩ (Subtype.ext h)), fun h => ?_⟩
      have h' : (⟨x, hx⟩ : Λ) = x₀ := Subtype.ext h
      rw [h', hx₀, ← h]
    · rw [hyc x hx]
      exact iff_of_false (fun h => hf1 ⟨x, hx⟩ (Subtype.ext h)) (fun h => hx (h ▸ x₀.2))
  obtain ⟨ε, hε⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (x₀ : Ψ)
  exact ⟨y, (mem_longInvAt_of_mul_self hyy hfix ⟨ε, hε⟩).1, hyΛ, hmem⟩

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem subtypePerm_mem_longInv_perm {Λ : Set Ψ} {y : Perm Ψ} (hy : y ∈ longInv (Perm Ψ) Ψ)
    (hyΛ : ∀ x, y x ∈ Λ ↔ x ∈ Λ) {x₀ : Ψ} (hx₀ : x₀ ∈ Λ) (hyx₀ : y x₀ = x₀)
    (hΛ : Λ.Nontrivial) : y.subtypePerm hyΛ ∈ longInv (Perm Λ) Λ := by
  have hyy : y * y = 1 := mul_self_eq_one_of_mem_longInv hy
  obtain ⟨z, hz⟩ := hy.2
  have hz₀ : x₀ = z := hz.2 x₀ hyx₀
  have hfix : ∀ x : Λ, y.subtypePerm hyΛ • x = x ↔ x = ⟨x₀, hx₀⟩ := fun x => by
    rw [Perm.smul_def, Subtype.ext_iff, Subtype.ext_iff, Perm.subtypePerm_apply]
    exact ⟨fun h => (hz.2 x h).trans hz₀.symm,
      fun h => (congrArg y h).trans (hyx₀.trans h.symm)⟩
  obtain ⟨ε, hε, hεx⟩ := hΛ.exists_ne x₀
  refine (mem_longInvAt_of_mul_self ?_ hfix ⟨⟨ε, hε⟩, fun h => hεx (congrArg Subtype.val h)⟩).1
  refine Equiv.ext fun x => Subtype.ext ?_
  show y (y x) = x
  rw [← Perm.mul_apply, hyy, Perm.one_apply]

end Perm

section TwoPoint

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
private theorem smul_mem_of_mem_stabilizer {g : G} {s : Set Ω} (hg : g ∈ stabilizer G s)
    {ω : Ω} (hω : ω ∈ s) : g • ω ∈ s := by
  rw [← mem_stabilizer_iff.mp hg]
  exact Set.smul_mem_smul_set hω

namespace Sec4Setting

theorem exists_coord_smul_of_mem_longInvSwap (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {u : G}
    (hu : u ∈ longInvSwap G Ω α β) :
    ∃ y : ∀ i, Perm (D.Ψc i), (∀ i, y i ∈ longInv (Perm (D.Ψc i)) (D.Ψc i)) ∧
      ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = u • (δ : Ω) →
        D.coord δ' = fun i => y i (D.coord δ i) := by
  have h3 := three_le_card_holtDelta_of_holtData hS.star D
  have hg : u ∈ stabilizer G ({α, β} : Set Ω) :=
    closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hu)
  have hπ : twoPointElt hg ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    (hS.mem_longInv_twoPointSection_iff hαβ h3 _).mpr ⟨u, hu, fun _ => rfl⟩
  refine ⟨fun i => D.ρ i ⟨twoPointElt hg, mem_jHull_of_mem_longInv hπ⟩,
    fun i => D.rho_mem_longInv hπ i, fun δ δ' hδ' => funext fun i => ?_⟩
  obtain rfl : δ' = (twoPointElt hg : twoPointSection G Ω α β) • δ := Subtype.ext hδ'
  exact D.coord_smul ⟨twoPointElt hg, mem_jHull_of_mem_longInv hπ⟩ δ i

theorem exists_mem_longInvSwap_coord_smul (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hA : ∀ i, D.M i = alternatingGroup (D.Ψc i)) (y : ∀ i, Perm (D.Ψc i))
    (hy : ∀ i, y i ∈ longInv (Perm (D.Ψc i)) (D.Ψc i)) :
    ∃ u ∈ longInvSwap G Ω α β, ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = u • (δ : Ω) →
      D.coord δ' = fun i => y i (D.coord δ i) := by
  have h3 := three_le_card_holtDelta_of_holtData hS.star D
  have hR : ∀ i, y i ∈ (D.ρ i).range := fun i =>
    longInv_perm_subset_of_alternatingGroup_le ((hA i).symm.le.trans (Subgroup.map_le_range _ _))
      ⟨D.tHull, rfl⟩ (D.rho_mem_longInv D.t_mem i) (hy i)
  obtain ⟨u', hu', hρ⟩ := D.exists_mem_longInv_rho_eq y hR hy
  obtain ⟨c, hc, hcπ⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3 _).mp hu'
  refine ⟨c, hc, fun δ δ' hδ' => funext fun i => ?_⟩
  obtain rfl : δ' = (u' : twoPointSection G Ω α β) • δ := Subtype.ext (hδ'.trans (hcπ δ).symm)
  rw [D.coord_smul, hρ]

theorem exists_coord_smul_stabilize_of_mem_centralizer (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    {V : Subgroup G} (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    {c : G} (hc : c ∈ longInvSwap G Ω α β) (hcV : c ∈ Subgroup.centralizer (V : Set G)) :
    ∃ y : ∀ i, Perm (D.Ψc i), (∀ i, y i ∈ longInv (Perm (D.Ψc i)) (D.Ψc i)) ∧
      (∀ i x, y i x ∈ Λc i ↔ x ∈ Λc i) ∧ (∀ i, ∃ x ∈ Λc i, y i x = x) ∧
      ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = c • (δ : Ω) →
        D.coord δ' = fun i => y i (D.coord δ i) := by
  obtain ⟨y, hy, hcoord⟩ := hS.exists_coord_smul_of_mem_longInvSwap hαβ D hc
  obtain ⟨ω₀, hω₀, -⟩ := hc.1.2
  have hω₀V : ω₀ ∈ fixSet Ω V := fun v hv => by
    have hvc : v * c = c * v := Subgroup.mem_centralizer_iff.mp hcV v hv
    exact hc.1.2.unique (by rw [← mul_smul, ← hvc, mul_smul, hω₀]) hω₀
  set d : holtDelta G Ω α β := ⟨ω₀, c, hc, hω₀⟩
  have hd : ∀ i, D.coord d i ∈ Λc i := (hbox d).mp hω₀V
  have hmaps : ∀ i x, x ∈ Λc i → y i x ∈ Λc i := fun i x hx => by
    obtain ⟨ω, hω⟩ := D.exists_coord_eq_update d i x
    have hωV : (ω : Ω) ∈ fixSet Ω V := (hbox ω).mpr fun j => by
      rcases eq_or_ne j i with rfl | hj
      · rw [hω, Function.update_self]
        exact hx
      · rw [hω, Function.update_of_ne hj]
        exact hd j
    have hcω : c • (ω : Ω) ∈ holtDelta G Ω α β :=
      smul_mem_of_mem_stabilizer (mem_stabilizer_holtDelta_of_mem_longInvSwap hc) ω.2
    have hcωV : c • (ω : Ω) ∈ fixSet Ω V :=
      smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hcV) hωV
    have h := (hbox ⟨c • (ω : Ω), hcω⟩).mp hcωV i
    have h2 : D.coord ⟨c • (ω : Ω), hcω⟩ i = y i (D.coord ω i) :=
      congrFun (hcoord ω ⟨c • (ω : Ω), hcω⟩ rfl) i
    rwa [h2, hω, Function.update_self] at h
  refine ⟨y, hy, fun i x => ⟨fun h => ?_, hmaps i x⟩,
    fun i => ⟨D.coord d i, hd i, (congrFun (hcoord d d hω₀.symm) i).symm⟩, hcoord⟩
  have h' := hmaps i _ h
  rwa [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv (hy i), Perm.one_apply] at h'

theorem exists_mem_centralizer_coord_smul_stabilize (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hA : ∀ i, D.M i = alternatingGroup (D.Ψc i)) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    (y : ∀ i, Perm (D.Ψc i)) (hy : ∀ i, y i ∈ longInv (Perm (D.Ψc i)) (D.Ψc i))
    (hyΛ : ∀ i x, y i x ∈ Λc i ↔ x ∈ Λc i) :
    ∃ c ∈ longInvSwap G Ω α β, c ∈ Subgroup.centralizer (V : Set G) ∧
      ∀ δ δ' : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V → (δ' : Ω) = c • (δ : Ω) →
        D.coord δ' = fun i => y i (D.coord δ i) := by
  obtain ⟨u, hu, hucoord⟩ := hS.exists_mem_longInvSwap_coord_smul hαβ D hA y hy
  have huΔ := mem_stabilizer_holtDelta_of_mem_longInvSwap hu
  have hmaps : ∀ ω ∈ holtDelta G Ω α β ∩ fixSet Ω V,
      u • ω ∈ holtDelta G Ω α β ∩ fixSet Ω V := by
    rintro ω ⟨hωΔ, hωV⟩
    have huω := smul_mem_of_mem_stabilizer huΔ hωΔ
    refine ⟨huω, (hbox ⟨u • ω, huω⟩).mpr fun i => ?_⟩
    rw [show D.coord ⟨u • ω, huω⟩ i = y i (D.coord ⟨ω, hωΔ⟩ i) from
      congrFun (hucoord ⟨ω, hωΔ⟩ ⟨u • ω, huω⟩ rfl) i, hyΛ]
    exact (hbox ⟨ω, hωΔ⟩).mp hωV i
  have huu : u * u = 1 := mul_self_eq_one_of_mem_longInv hu.1
  have hustab : u ∈ stabilizer G (holtDelta G Ω α β ∩ fixSet Ω V) := by
    rw [mem_stabilizer_iff]
    refine Set.Subset.antisymm (Set.smul_set_subset_iff.mpr hmaps) fun ω hω => ?_
    refine ⟨u • ω, hmaps ω hω, ?_⟩
    show u • u • ω = ω
    rw [smul_smul, huu, one_smul]
  obtain ⟨δ₀, hδ₀Δ, hδ₀V⟩ := hS.exists_mem_holtDelta_mem_fixSet hV hVαβ
  obtain ⟨c, hc, hcV, hcu⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hV hVαβ
    (Λ := holtDelta G Ω α β ∩ fixSet Ω V) ⟨δ₀, hδ₀Δ, hδ₀V⟩ Set.inter_subset_right hu hustab
  exact ⟨c, hc, hcV, fun δ δ' hδV hδ' => hucoord δ δ' (hδ'.trans (hcu δ ⟨δ.2, hδV⟩))⟩

theorem exists_coord_smul_box_of_mem_centralizer (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    {V : Subgroup G} (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    {c : G} (hc : c ∈ longInvSwap G Ω α β) (hcV : c ∈ Subgroup.centralizer (V : Set G)) :
    ∃ w : ∀ i, Perm (Λc i), (∀ i, w i * w i = 1 ∧ ∃! x, w i x = x) ∧
      (∀ i, (Λc i).Nontrivial → w i ∈ longInv (Perm (Λc i)) (Λc i)) ∧
      ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = c • (δ : Ω) →
        ∀ (h : ∀ i, D.coord δ i ∈ Λc i) i, D.coord δ' i = w i ⟨D.coord δ i, h i⟩ := by
  obtain ⟨y, hy, hyΛ, hyfix, hcoord⟩ :=
    hS.exists_coord_smul_stabilize_of_mem_centralizer hαβ D Λc hbox hc hcV
  refine ⟨fun i => (y i).subtypePerm (hyΛ i), fun i => ⟨?_, ?_⟩, fun i hi => ?_,
    fun δ δ' hδ' _ i => congrFun (hcoord δ δ' hδ') i⟩
  · refine Equiv.ext fun x => Subtype.ext ?_
    show y i (y i x) = x
    rw [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv (hy i), Perm.one_apply]
  · obtain ⟨x, hx, hfx⟩ := hyfix i
    obtain ⟨z, -, hz⟩ := (hy i).2
    refine ⟨⟨x, hx⟩, Subtype.ext hfx, fun x' hx' => Subtype.ext ?_⟩
    exact (hz x' (congrArg Subtype.val hx')).trans (hz x hfx).symm
  · obtain ⟨x, hx, hfx⟩ := hyfix i
    exact subtypePerm_mem_longInv_perm (hy i) (hyΛ i) hx hfx hi

theorem exists_mem_centralizer_coord_smul_box (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hA : ∀ i, D.M i = alternatingGroup (D.Ψc i)) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    (w : ∀ i, Perm (Λc i)) (hw : ∀ i, w i * w i = 1 ∧ ∃! x, w i x = x) :
    ∃ c ∈ longInvSwap G Ω α β, c ∈ Subgroup.centralizer (V : Set G) ∧
      ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = c • (δ : Ω) →
        ∀ (h : ∀ i, D.coord δ i ∈ Λc i) i, D.coord δ' i = w i ⟨D.coord δ i, h i⟩ := by
  choose y hy hyw hyΛ using fun i => exists_mem_longInv_perm_apply_eq (Λ := Λc i)
    (D.odd_card_Ψc i) (by have := D.five_le_card i; omega) (hw i).1 (hw i).2
  obtain ⟨c, hc, hcV, hcoord⟩ :=
    hS.exists_mem_centralizer_coord_smul_stabilize hαβ D hA hV hVαβ Λc hbox y hy hyΛ
  refine ⟨c, hc, hcV, fun δ δ' hδ' h i => ?_⟩
  rw [show D.coord δ' i = y i (D.coord δ i) from
    congrFun (hcoord δ δ' ((hbox δ).mpr h) hδ') i, hyw i _ (h i)]

end Sec4Setting

end TwoPoint

section Centralizer

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
private theorem three_le_card_of_mem {Γ : Set Ω} [Finite Γ] {a b c : Ω} (ha : a ∈ Γ)
    (hb : b ∈ Γ) (hc : c ∈ Γ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card Γ := by
  rw [Nat.card_coe_set_eq]
  have h3 : ({a, b, c} : Set Ω).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard (Set.insert_subset ha (Set.insert_subset hb
    (Set.singleton_subset_iff.mpr hc))) (Set.toFinite Γ)

namespace Sec4Setting

theorem three_le_card_fixSet_of_ne (hS : Sec4Setting G Ω) {V : Subgroup G} (hV : IsPGroup 2 V)
    {a b : fixSet Ω V} (hab : a ≠ b) : 3 ≤ Nat.card (fixSet Ω V) := by
  have hab' : (a : Ω) ≠ b := fun h => hab (Subtype.ext h)
  obtain ⟨δ, hδ, hδV⟩ := hS.exists_mem_holtDelta_mem_fixSet hV
    (le_inf (mem_fixSet_iff_le_stabilizer.mp a.2) (mem_fixSet_iff_le_stabilizer.mp b.2))
  have hδa : (a : Ω) ≠ δ := by
    rintro rfl
    exact left_notMem_holtDelta (G := G) hab' hδ
  have hδb : (b : Ω) ≠ δ := by
    rintro rfl
    exact right_notMem_holtDelta (G := G) hab' hδ
  exact three_le_card_of_mem a.2 b.2 hδV hab' hδa hδb

variable [FaithfulSMul G Ω]

theorem box_hcoord (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {V : Subgroup G}
    (hV : IsPGroup 2 V) {a b : fixSet Ω V} (ha : (a : Ω) = α) (hb : (b : Ω) = β)
    (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    {p : D.ι → Prop} (hp : ∀ i, p i → (Λc i).Nontrivial)
    (e : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b ≃ ∀ j : {i // p i}, Λc j)
    (he : ∀ (δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) (δ₀ : holtDelta G Ω α β),
      (δ₀ : Ω) = ((δ : fixSet Ω V) : Ω) → ∀ j : {i // p i}, (e δ j : D.Ψc j) = D.coord δ₀ j) :
    ∀ c ∈ longInvSwap (centralizerImage Ω V) (fixSet Ω V) a b,
      ∃ y : ∀ j : {i // p i}, Perm (Λc j),
        (∀ j : {i // p i}, y j ∈ longInv (Perm (Λc j)) (Λc j)) ∧
        ∀ δ δ' : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b,
          (δ' : fixSet Ω V) = c • (δ : fixSet Ω V) → e δ' = fun j => y j (e δ j) := by
  subst ha hb
  intro c hc
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hV hab
  obtain ⟨c₀, hc₀, hc₀V, hc₀π⟩ := (hS.mem_longInvSwap_centralizerImage_iff hV h3 c).mp hc
  obtain ⟨w, -, hwJ, hcoord⟩ :=
    hS.exists_coord_smul_box_of_mem_centralizer hαβ D Λc hbox hc₀ hc₀V
  refine ⟨fun j => w j, fun j => hwJ j (hp j j.2),
    fun δ δ' hδ' => funext fun j => Subtype.ext ?_⟩
  have hδΔ := (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mp δ.2
  have hδ'Δ := (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mp δ'.2
  set δ₀ : holtDelta G Ω a b := ⟨((δ : fixSet Ω V) : Ω), hδΔ⟩
  set δ₀' : holtDelta G Ω a b := ⟨((δ' : fixSet Ω V) : Ω), hδ'Δ⟩
  have hsmul : (δ₀' : Ω) = c₀ • (δ₀ : Ω) := (congrArg Subtype.val hδ').trans (hc₀π δ)
  have hin : ∀ i, D.coord δ₀ i ∈ Λc i := (hbox δ₀).mp (δ : fixSet Ω V).2
  have hej : e δ j = ⟨D.coord δ₀ j, hin j⟩ := Subtype.ext (he δ δ₀ rfl j)
  rw [he δ' δ₀' rfl j, hcoord δ₀ δ₀' hsmul hin j, hej]

theorem box_hreal (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hA : ∀ i, D.M i = alternatingGroup (D.Ψc i)) {V : Subgroup G} (hV : IsPGroup 2 V)
    {a b : fixSet Ω V} (ha : (a : Ω) = α) (hb : (b : Ω) = β) (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    {p : D.ι → Prop} (hnp : ∀ i, ¬ p i → (Λc i).Subsingleton)
    (e : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b ≃ ∀ j : {i // p i}, Λc j)
    (he : ∀ (δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) (δ₀ : holtDelta G Ω α β),
      (δ₀ : Ω) = ((δ : fixSet Ω V) : Ω) → ∀ j : {i // p i}, (e δ j : D.Ψc j) = D.coord δ₀ j) :
    ∀ y : ∀ j : {i // p i}, Perm (Λc j), (∀ j : {i // p i}, y j ∈ longInv (Perm (Λc j)) (Λc j)) →
      ∃ c ∈ longInvSwap (centralizerImage Ω V) (fixSet Ω V) a b,
        ∀ δ δ' : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b,
          (δ' : fixSet Ω V) = c • (δ : fixSet Ω V) → e δ' = fun j => y j (e δ j) := by
  classical
  subst ha hb
  intro y hy
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hV hab
  have hVab : V ≤ stabilizer G (a : Ω) ⊓ stabilizer G (b : Ω) :=
    le_inf (mem_fixSet_iff_le_stabilizer.mp a.2) (mem_fixSet_iff_le_stabilizer.mp b.2)
  obtain ⟨d₀, hd₀Δ, hd₀V⟩ := hS.exists_mem_holtDelta_mem_fixSet hV hVab
  have hd : ∀ i, D.coord ⟨d₀, hd₀Δ⟩ i ∈ Λc i := (hbox ⟨d₀, hd₀Δ⟩).mp hd₀V
  let w : ∀ i, Perm (Λc i) := fun i => if h : p i then y ⟨i, h⟩ else 1
  have hw : ∀ i, w i * w i = 1 ∧ ∃! x, w i x = x := fun i => by
    by_cases h : p i
    · simp only [w, dite_eq_left h]
      exact ⟨mul_self_eq_one_of_mem_longInv (hy _), (hy ⟨i, h⟩).2⟩
    · simp only [w, dite_eq_right h]
      exact ⟨mul_one 1, ⟨_, hd i⟩, rfl, fun x _ => Subtype.ext (hnp i h x.2 (hd i))⟩
  obtain ⟨c₀, hc₀, hc₀V, hcoord⟩ :=
    hS.exists_mem_centralizer_coord_smul_box hαβ D hA hV hVab Λc hbox w hw
  refine ⟨centralizerImageElt hc₀V, (hS.mem_longInvSwap_centralizerImage_iff hV h3 _).mpr
    ⟨c₀, hc₀, hc₀V, fun _ => rfl⟩, fun δ δ' hδ' => funext fun j => Subtype.ext ?_⟩
  have hδΔ := (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mp δ.2
  have hδ'Δ := (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mp δ'.2
  set δ₀ : holtDelta G Ω a b := ⟨((δ : fixSet Ω V) : Ω), hδΔ⟩
  set δ₀' : holtDelta G Ω a b := ⟨((δ' : fixSet Ω V) : Ω), hδ'Δ⟩
  have hsmul : (δ₀' : Ω) = c₀ • (δ₀ : Ω) := congrArg Subtype.val hδ'
  have hin : ∀ i, D.coord δ₀ i ∈ Λc i := (hbox δ₀).mp (δ : fixSet Ω V).2
  have hej : e δ j = ⟨D.coord δ₀ j, hin j⟩ := Subtype.ext (he δ δ₀ rfl j)
  rw [he δ' δ₀' rfl j, hcoord δ₀ δ₀' hsmul hin j, hej]
  simp only [w, dite_eq_left j.2]

theorem exists_boxEquiv (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hO : jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥) {V : Subgroup G}
    (hV : IsPGroup 2 V) {a b : fixSet Ω V} (ha : (a : Ω) = α) (hb : (b : Ω) = β)
    (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    {p : D.ι → Prop} (hnp : ∀ i, ¬ p i → (Λc i).Subsingleton) :
    ∃ e : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b ≃ ∀ j : {i // p i}, Λc j,
      ∀ (δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) (δ₀ : holtDelta G Ω α β),
        (δ₀ : Ω) = ((δ : fixSet Ω V) : Ω) → ∀ j : {i // p i}, (e δ j : D.Ψc j) = D.coord δ₀ j := by
  classical
  subst ha hb
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hV hab
  have hmem := fun δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b =>
    (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mp δ.2
  let pt : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b → holtDelta G Ω a b :=
    fun δ => ⟨((δ : fixSet Ω V) : Ω), hmem δ⟩
  have hin : ∀ δ i, D.coord (pt δ) i ∈ Λc i := fun δ => (hbox (pt δ)).mp (δ : fixSet Ω V).2
  let f : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b → ∀ j : {i // p i}, Λc j :=
    fun δ j => ⟨D.coord (pt δ) j, hin δ j⟩
  have hinj : Function.Injective f := fun δ δ' h => by
    have hc : D.coord (pt δ) = D.coord (pt δ') := funext fun i => by
      by_cases hi : p i
      · exact congrArg Subtype.val (congrFun h ⟨i, hi⟩)
      · exact hnp i hi (hin δ i) (hin δ' i)
    have h' : ((pt δ : holtDelta G Ω a b) : Ω) = pt δ' :=
      congrArg Subtype.val (HoltData.coord_injective (D := D) hO hc)
    exact Subtype.ext (Subtype.ext h')
  have hsurj : Function.Surjective f := fun l => by
    obtain ⟨d₀, hd₀Δ, hd₀V⟩ := hS.exists_mem_holtDelta_mem_fixSet hV
      (le_inf (mem_fixSet_iff_le_stabilizer.mp a.2) (mem_fixSet_iff_le_stabilizer.mp b.2))
    have hd := (hbox ⟨d₀, hd₀Δ⟩).mp hd₀V
    let x : ∀ i, D.Ψc i := fun i =>
      if h : p i then (l ⟨i, h⟩ : D.Ψc i) else D.coord ⟨d₀, hd₀Δ⟩ i
    obtain ⟨δ₀, hδ₀⟩ := D.coord_surjective x
    have hx : ∀ i, D.coord δ₀ i ∈ Λc i := fun i => by
      rw [hδ₀]
      by_cases h : p i
      · simp only [x, dite_eq_left h]
        exact (l ⟨i, h⟩).2
      · simp only [x, dite_eq_right h]
        exact hd i
    have hδ₀V : (δ₀ : Ω) ∈ fixSet Ω V := (hbox δ₀).mpr hx
    refine ⟨⟨⟨δ₀, hδ₀V⟩, (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mpr δ₀.2⟩,
      funext fun j => Subtype.ext ?_⟩
    show D.coord δ₀ j = (l j : D.Ψc j)
    rw [hδ₀]
    simp only [x, dite_eq_left j.2]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun δ δ₀ hδ₀ j => ?_⟩
  show D.coord (pt δ) j = D.coord δ₀ j
  rw [show pt δ = δ₀ from Subtype.ext hδ₀.symm]

theorem exists_boxEquiv_ccl (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hO : jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥)
    (hA : ∀ i, D.M i = alternatingGroup (D.Ψc i)) {V : Subgroup G} (hV : IsPGroup 2 V)
    {a b : fixSet Ω V} (ha : (a : Ω) = α) (hb : (b : Ω) = β) (Λc : ∀ i, Set (D.Ψc i))
    (hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, D.coord δ i ∈ Λc i)
    {p : D.ι → Prop} (hp : ∀ i, p i → (Λc i).Nontrivial)
    (hnp : ∀ i, ¬ p i → (Λc i).Subsingleton) :
    ∃ e : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b ≃ ∀ j : {i // p i}, Λc j,
      (∀ (δ : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b) (δ₀ : holtDelta G Ω α β),
        (δ₀ : Ω) = ((δ : fixSet Ω V) : Ω) → ∀ j : {i // p i}, (e δ j : D.Ψc j) = D.coord δ₀ j) ∧
      (∀ c ∈ longInvSwap (centralizerImage Ω V) (fixSet Ω V) a b,
        ∃ y : ∀ j : {i // p i}, Perm (Λc j),
          (∀ j : {i // p i}, y j ∈ longInv (Perm (Λc j)) (Λc j)) ∧
          ∀ δ δ' : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b,
            (δ' : fixSet Ω V) = c • (δ : fixSet Ω V) → e δ' = fun j => y j (e δ j)) ∧
      (∀ y : ∀ j : {i // p i}, Perm (Λc j),
        (∀ j : {i // p i}, y j ∈ longInv (Perm (Λc j)) (Λc j)) →
        ∃ c ∈ longInvSwap (centralizerImage Ω V) (fixSet Ω V) a b,
          ∀ δ δ' : holtDelta (centralizerImage Ω V) (fixSet Ω V) a b,
            (δ' : fixSet Ω V) = c • (δ : fixSet Ω V) → e δ' = fun j => y j (e δ j)) := by
  obtain ⟨e, he⟩ := hS.exists_boxEquiv hαβ D hO hV ha hb Λc hbox hnp
  exact ⟨e, he, hS.box_hcoord hαβ D hV ha hb Λc hbox hp e he,
    hS.box_hreal hαβ D hA hV ha hb Λc hbox hnp e he⟩

end Sec4Setting

end Centralizer

end CFSG.Holt.H78
