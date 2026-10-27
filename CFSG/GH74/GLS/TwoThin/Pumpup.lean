module

public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

@[expose] noncomputable def pumpupY (Λ : Subgroup Y) : Subgroup Y :=
  ⨆ g ∈ TwoLayer.subgroup Y, Λ.map (MulAut.conj g).toMonoidHom

theorem map_barMk_twoLayer : (TwoLayer.subgroup Y).map (barMk Y) = CFSG.layer (barQ Y) := by
  rw [TwoLayerTransport.image_of_odd_kernel (barMk Y) barMk_surjective odd_card_ker_barMk,
    TwoLayerTransport.eq_layer_of_corefree oddCore_barQ, layer_subgroup_eq_layer]

theorem le_twoLayer_of_perfect {Λ : Subgroup Y} (hperf : ⁅Λ, Λ⁆ = Λ)
    (h : Λ.map (barMk Y) ≤ CFSG.layer (barQ Y)) : Λ ≤ TwoLayer.subgroup Y := by
  have : Group.IsSolvable (barMk Y).ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ odd_card_ker_barMk
  have : Group.IsPerfect Λ := Subgroup.isPerfect_iff.mpr hperf
  have : (TwoLayer.subgroup Y).Characteristic := TwoLayerTransport.characteristic Y
  exact SolvableKernelContainment.perfect_containment (barMk Y) Λ (TwoLayer.subgroup Y)
    (by rwa [map_barMk_twoLayer])

omit [Finite Y] in
theorem pumpupY_le {Λ : Subgroup Y} (hΛ : Λ ≤ TwoLayer.subgroup Y) :
    pumpupY Λ ≤ TwoLayer.subgroup Y := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨a, ha, rfl⟩
  exact mul_mem (mul_mem hg (hΛ ha)) (inv_mem hg)

omit [Finite Y] in
theorem le_pumpupY (Λ : Subgroup Y) {g : Y} (hg : g ∈ TwoLayer.subgroup Y) :
    Λ.map (MulAut.conj g).toMonoidHom ≤ pumpupY Λ :=
  le_iSup₂ (f := fun g _ => Λ.map (MulAut.conj g).toMonoidHom) g hg

omit [Finite Y] in
theorem pumpupY_le_of_forall {Λ J : Subgroup Y}
    (h : ∀ g ∈ TwoLayer.subgroup Y, Λ.map (MulAut.conj g).toMonoidHom ≤ J) : pumpupY Λ ≤ J :=
  iSup₂_le h

omit [Finite Y] in
theorem map_conj_pumpupY_le (Λ : Subgroup Y) {e : Y} (he : e ∈ TwoLayer.subgroup Y) :
    (pumpupY Λ).map (MulAut.conj e).toMonoidHom ≤ pumpupY Λ := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun g hg => ?_
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
  have : (MulAut.conj e).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (e * g)).toMonoidHom := by
    ext a
    simp [mul_assoc]
  rw [this]
  exact le_pumpupY Λ (mul_mem he hg)

theorem isSubnormal_pumpupY {Λ : Subgroup Y} (hΛ : Λ ≤ TwoLayer.subgroup Y) :
    (pumpupY Λ).IsSubnormal := by
  have : (TwoLayer.subgroup Y).Characteristic := TwoLayerTransport.characteristic Y
  refine Subgroup.IsSubnormal.step (pumpupY Λ) (TwoLayer.subgroup Y) (pumpupY_le hΛ)
    (Subgroup.IsSubnormal.step _ ⊤ le_top Subgroup.IsSubnormal.top inferInstance) ?_
  refine ⟨fun n hn g => ?_⟩
  have h := map_conj_pumpupY_le Λ g.2 ⟨(n : Y), hn, rfl⟩
  exact h

theorem map_barMk_pumpupY_le (Λ : Subgroup Y) :
    (pumpupY Λ).map (barMk Y) ≤
      ⨆ g ∈ CFSG.layer (barQ Y), (Λ.map (barMk Y)).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun g hg => ?_
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
  have hcomp : (barMk Y).comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (barMk Y g)).toMonoidHom.comp (barMk Y) := by
    ext a
    simp
  rw [hcomp, ← Subgroup.map_map]
  have hg' : barMk Y g ∈ CFSG.layer (barQ Y) := by
    rw [← map_barMk_twoLayer]
    exact Subgroup.mem_map_of_mem _ hg
  exact le_iSup₂ (f := fun h _ => (Λ.map (barMk Y)).map (MulAut.conj h).toMonoidHom)
    (barMk Y g) hg'


omit [Finite Y] in
theorem subset_pumpupY (Λ : Subgroup Y) : Λ ≤ pumpupY Λ := fun a ha =>
  le_pumpupY Λ (one_mem _) ⟨a, ha, by simp⟩

theorem map_conj_pumpupY_le_of_le_centralizer (Λ : Subgroup Y) {s : Y}
    (hΛ : Λ ≤ centralizer ({s} : Set Y)) :
    (pumpupY Λ).map (MulAut.conj s).toMonoidHom ≤ pumpupY Λ := by
  have : (TwoLayer.subgroup Y).Characteristic := TwoLayerTransport.characteristic Y
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨a, ha, rfl⟩
  have hsa : s * a = a * s := (Subgroup.mem_centralizer_iff.mp (hΛ ha)) s (Set.mem_singleton s)
  have hsg : s * g * s⁻¹ ∈ TwoLayer.subgroup Y :=
    (inferInstance : (TwoLayer.subgroup Y).Normal).conj_mem g hg s
  have hmem : (MulAut.conj (s * g * s⁻¹)).toMonoidHom a ∈ pumpupY Λ :=
    le_pumpupY Λ hsg ⟨a, ha, rfl⟩
  have heq : (MulAut.conj s) ((MulAut.conj g) a) = (MulAut.conj (s * g * s⁻¹)) a := by
    simp only [MulAut.conj_apply]
    have : s * a * s⁻¹ = a := by rw [hsa]; group
    calc s * (g * a * g⁻¹) * s⁻¹ = (s * g * s⁻¹) * (s * a * s⁻¹) * (s * g * s⁻¹)⁻¹ := by group
      _ = (s * g * s⁻¹) * a * (s * g * s⁻¹)⁻¹ := by rw [this]
  have hfinal : (MulAut.conj s) ((MulAut.conj g) a) ∈ pumpupY Λ := by
    rw [heq]
    exact hmem
  exact hfinal

theorem map_conj_pumpupY_le_of_map_le (Λ : Subgroup Y) {s : Y}
    (hΛ : ∀ a ∈ Λ, s * a * s⁻¹ ∈ Λ) :
    (pumpupY Λ).map (MulAut.conj s).toMonoidHom ≤ pumpupY Λ := by
  have : (TwoLayer.subgroup Y).Characteristic := TwoLayerTransport.characteristic Y
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨a, ha, rfl⟩
  have hsg : s * g * s⁻¹ ∈ TwoLayer.subgroup Y :=
    (inferInstance : (TwoLayer.subgroup Y).Normal).conj_mem g hg s
  have hmem : (MulAut.conj (s * g * s⁻¹)).toMonoidHom (s * a * s⁻¹) ∈ pumpupY Λ :=
    le_pumpupY Λ hsg ⟨s * a * s⁻¹, hΛ a ha, rfl⟩
  have heq : (MulAut.conj s) ((MulAut.conj g) a) =
      (MulAut.conj (s * g * s⁻¹)) (s * a * s⁻¹) := by
    simp only [MulAut.conj_apply]
    group
  have hfinal : (MulAut.conj s) ((MulAut.conj g) a) ∈ pumpupY Λ := by
    rw [heq]
    exact hmem
  exact hfinal

omit [Finite Y] in
theorem map_barMk_ne_bot_of_perfect [Finite Y] {Λ : Subgroup Y} (hperf : ⁅Λ, Λ⁆ = Λ)
    (hne : Λ ≠ ⊥) : Λ.map (barMk Y) ≠ ⊥ := by
  intro h
  have hle : Λ ≤ (barMk Y).ker := (Subgroup.map_eq_bot_iff _).mp h
  have hodd : Odd (Nat.card Λ) := odd_card_ker_barMk.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hsolv : Group.IsSolvable Λ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial Λ
  have : Group.IsPerfect Λ := Subgroup.isPerfect_iff.mpr hperf
  have h2 : commutator Λ = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1


omit [Finite Y] in
theorem mem_conjSub_iff' {Z : Type*} [Group Z] {g x : Z} {K : Subgroup Z} :
    x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem pumpupY_structure {s : Y} (hs : orderOf s = 2) {Λ : Subgroup Y}
    (hΛC : Λ ≤ centralizer ({s} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set Y)))) :
    Λ ≤ TwoLayer.subgroup Y ∧ (pumpupY Λ).IsSubnormal ∧
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧
      ((conjSub (barMk Y s)⁻¹ L = L ∧ Λ.map (barMk Y) ≤ L) ∨
        (conjSub (barMk Y s)⁻¹ L ≠ L ∧ ∃ hAB : ⁅L, conjSub (barMk Y s)⁻¹ L⁆ = ⊥,
          Λ.map (barMk Y) ≤ (swapDiag hAB).range)) ∧
      L ≤ (pumpupY Λ).map (barMk Y) ∧ conjSub (barMk Y s)⁻¹ L ≤ (pumpupY Λ).map (barMk Y) ∧
      ∀ K' : Subgroup Y, TwoComponents.IsTwoComponent K' →
        (K' ≤ pumpupY Λ ↔
          (K'.map (barMk Y) = L ∨ K'.map (barMk Y) = conjSub (barMk Y s)⁻¹ L)) := by
  have hperf : ⁅Λ, Λ⁆ = Λ := commutator_self_of_isTwoComponent hΛC hΛ
  have hΛE : Λ ≤ TwoLayer.subgroup Y :=
    le_twoLayer_of_perfect hperf (map_barMk_le_layer hs hΛC hΛ)
  have hJsub : (pumpupY Λ).IsSubnormal := isSubnormal_pumpupY hΛE
  obtain ⟨L, hL, hcases, hK'⟩ := pumpup_structure hs hΛC hΛ (map_barMk_pumpupY_le Λ)
  refine ⟨hΛE, hJsub, L, hL, hcases, ?_⟩
  have hs'ord : orderOf (barMk Y s) = 2 := orderOf_barMk hs
  have hs'inv : (barMk Y s)⁻¹ = barMk Y s := inv_eq_self_of_orderOf_eq_two hs'ord
  have hJbar : ((pumpupY Λ).map (barMk Y)).IsSubnormal := hJsub.map barMk_surjective
  have hJchain : Open.IsSubnormal (pumpupY Λ) ⊤ := Components.chain_of_mathlib_subnormal hJsub
  have hLs : CFSG.IsComponent (conjSub (barMk Y s)⁻¹ L) := isComponent_conjSub hL _
  have hΛne : Λ ≠ ⊥ := ne_bot_of_isTwoComponent hΛ
  have hA : Λ.map (barMk Y) ≠ ⊥ := map_barMk_ne_bot_of_perfect hperf hΛne
  have hAJ : Λ.map (barMk Y) ≤ (pumpupY Λ).map (barMk Y) :=
    Subgroup.map_mono (subset_pumpupY Λ)
  have hinv : ∀ j ∈ (pumpupY Λ).map (barMk Y),
      barMk Y s * j * (barMk Y s)⁻¹ ∈ (pumpupY Λ).map (barMk Y) := by
    intro j hj
    obtain ⟨j0, hj0, rfl⟩ := hj
    have h1 : s * j0 * s⁻¹ ∈ pumpupY Λ :=
      map_conj_pumpupY_le_of_le_centralizer Λ hΛC (Subgroup.mem_map_of_mem _ hj0)
    exact ⟨_, h1, by simp⟩
  have hinv' : ∀ j ∈ (pumpupY Λ).map (barMk Y),
      (barMk Y s)⁻¹ * j * barMk Y s ∈ (pumpupY Λ).map (barMk Y) := by
    intro j hj
    have := hinv j hj
    rw [hs'inv] at this ⊢
    exact this
  have hLJ : L ≤ (pumpupY Λ).map (barMk Y) := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hL hJbar with h | h
    · exact h
    · exfalso
      have hLc : L ≤ centralizer (((pumpupY Λ).map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hLsc : conjSub (barMk Y s)⁻¹ L ≤
          centralizer (((pumpupY Λ).map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)) := by
        intro x hx
        rw [mem_conjSub_iff', inv_inv] at hx
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hx0 := (Subgroup.mem_centralizer_iff.mp (hLc hx)) _ (hinv j hj)
        have e1 : j * x = (barMk Y s)⁻¹ * ((barMk Y s * j * (barMk Y s)⁻¹) *
            (barMk Y s * x * (barMk Y s)⁻¹)) * barMk Y s := by group
        have e2 : x * j = (barMk Y s)⁻¹ * ((barMk Y s * x * (barMk Y s)⁻¹) *
            (barMk Y s * j * (barMk Y s)⁻¹)) * barMk Y s := by group
        rw [e1, e2, hx0]
      have hT : L ⊔ conjSub (barMk Y s)⁻¹ L ≤
          centralizer (((pumpupY Λ).map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)) :=
        sup_le hLc hLsc
      have hAT : Λ.map (barMk Y) ≤ L ⊔ conjSub (barMk Y s)⁻¹ L := by
        rcases hcases with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
        · exact hAL.trans le_sup_left
        · refine hAD.trans ?_
          rintro _ ⟨x, rfl⟩
          exact swapDiag_mem_sup hAB x
      have hcomm : ⁅Λ.map (barMk Y), Λ.map (barMk Y)⁆ = ⊥ := by
        refine eq_bot_iff.mpr ?_
        calc ⁅Λ.map (barMk Y), Λ.map (barMk Y)⁆
            ≤ ⁅L ⊔ conjSub (barMk Y s)⁻¹ L, (pumpupY Λ).map (barMk Y)⁆ :=
              Subgroup.commutator_mono hAT hAJ
          _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hT
      have hperfA : ⁅Λ.map (barMk Y), Λ.map (barMk Y)⁆ = Λ.map (barMk Y) := by
        rw [← Subgroup.map_commutator, hperf]
      exact hA (hperfA.symm.trans hcomm)
  have hLsJ : conjSub (barMk Y s)⁻¹ L ≤ (pumpupY Λ).map (barMk Y) := by
    intro x hx
    rw [mem_conjSub_iff', inv_inv] at hx
    have h1 := hinv' _ (hLJ hx)
    have e : (barMk Y s)⁻¹ * (barMk Y s * x * (barMk Y s)⁻¹) * barMk Y s = x := by group
    rwa [e] at h1
  refine ⟨hLJ, hLsJ, fun K' hK'2 => ⟨fun hKJ => hK' K' hK'2 hKJ, ?_⟩⟩
  rintro (h | h)
  · exact TwoComponentSubnormal.le_of_odd_kernel_map_le (barMk Y) barMk_surjective
      odd_card_ker_barMk K' (pumpupY Λ) hK'2 hJchain (by rw [h]; exact hLJ)
  · exact TwoComponentSubnormal.le_of_odd_kernel_map_le (barMk Y) barMk_surjective
      odd_card_ker_barMk K' (pumpupY Λ) hK'2 hJchain (by rw [h]; exact hLsJ)

end CFSG.GH74.GLS.TwoThin
