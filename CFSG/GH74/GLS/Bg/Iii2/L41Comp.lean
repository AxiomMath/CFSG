module

public import CFSG.GH74.GLS.C3.Layer1.St1RigDiag3

public section

namespace CFSG.GH74.GLS.Bg.Iii2.L41

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

section Commutator

theorem commutator_sup_right_eq_bot {H : Type*} [Group H] {A B₁ B₂ : Subgroup H}
    (h1 : ⁅A, B₁⁆ = ⊥) (h2 : ⁅A, B₂⁆ = ⊥) : ⁅A, B₁ ⊔ B₂⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2 ⊢
  intro a ha
  have hB1 : B₁ ≤ Subgroup.centralizer ({a} : Set H) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (h1 ha) b hb)
  have hB2 : B₂ ≤ Subgroup.centralizer ({a} : Set H) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (h2 ha) b hb)
  have hsup := sup_le hB1 hB2
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hb)

theorem commutator_sup_sup_eq_bot {H : Type*} [Group H] {A₁ A₂ B₁ B₂ : Subgroup H}
    (h11 : ⁅A₁, B₁⁆ = ⊥) (h12 : ⁅A₁, B₂⁆ = ⊥) (h21 : ⁅A₂, B₁⁆ = ⊥) (h22 : ⁅A₂, B₂⁆ = ⊥) :
    ⁅A₁ ⊔ A₂, B₁ ⊔ B₂⁆ = ⊥ := by
  have e1 := commutator_sup_right_eq_bot h11 h12
  have e2 := commutator_sup_right_eq_bot h21 h22
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at e1 e2 ⊢
  exact sup_le e1 e2

end Commutator

section Layer1

variable {Y : Type} [Group Y] [Finite Y]

theorem pumpupY_le_of_common {a b : Y} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) {ΛA ΛB Θ : Subgroup Y}
    (hΛA : ΛA ≤ centralizer ({a} : Set Y))
    (hΛA2 : TwoComponents.IsTwoComponent (ΛA.subgroupOf (centralizer ({a} : Set Y))))
    (hΛB : ΛB ≤ centralizer ({b} : Set Y))
    (hΛB2 : TwoComponents.IsTwoComponent (ΛB.subgroupOf (centralizer ({b} : Set Y))))
    (hbΛA : ∀ x ∈ ΛA, b * x * b⁻¹ ∈ ΛA)
    (hΘA : Θ ≤ ΛA) (hΘB : Θ ≤ ΛB) (hΘp : ⁅Θ, Θ⁆ = Θ) (hΘne : Θ ≠ ⊥)
    {I : Subgroup Y} (hI2 : TwoComponents.IsTwoComponent I) (hIB : I ≤ pumpupY ΛB) :
    I ≤ pumpupY ΛA := by
  obtain ⟨-, -, LA, hLA, hcA, -, -, hiffA⟩ := pumpupY_structure ha hΛA hΛA2
  obtain ⟨-, -, LB, hLB, hcB, -, -, hiffB⟩ := pumpupY_structure hb hΛB hΛB2
  have haa2 : orderOf (barMk Y a) = 2 := orderOf_barMk ha
  have hbb2 : orderOf (barMk Y b) = 2 := orderOf_barMk hb
  have haainv : (barMk Y a)⁻¹ = barMk Y a := inv_eq_self_of_orderOf_eq_two haa2
  have hbbinv : (barMk Y b)⁻¹ = barMk Y b := inv_eq_self_of_orderOf_eq_two hbb2
  have hab_bar : barMk Y a * barMk Y b = barMk Y b * barMk Y a := by
    rw [← map_mul, ← map_mul, hab]
  have hPA : Θ.map (barMk Y) ≤ LA ⊔ conjSub (barMk Y a)⁻¹ LA := by
    refine (Subgroup.map_mono hΘA).trans ?_
    rcases hcA with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
    · exact hAL.trans le_sup_left
    · refine hAD.trans ?_
      rintro _ ⟨x, rfl⟩
      exact swapDiag_mem_sup hAB x
  have hPB : Θ.map (barMk Y) ≤ LB ⊔ conjSub (barMk Y b)⁻¹ LB := by
    refine (Subgroup.map_mono hΘB).trans ?_
    rcases hcB with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
    · exact hAL.trans le_sup_left
    · refine hAD.trans ?_
      rintro _ ⟨x, rfl⟩
      exact swapDiag_mem_sup hAB x
  have hPne : Θ.map (barMk Y) ≠ ⊥ := map_barMk_ne_bot_of_perfect hΘp hΘne
  have hPperf : ⁅Θ.map (barMk Y), Θ.map (barMk Y)⁆ = Θ.map (barMk Y) := by
    rw [← Subgroup.map_commutator, hΘp]
  have hLA' : CFSG.IsComponent (conjSub (barMk Y a)⁻¹ LA) := isComponent_conjSub hLA _
  have hLB' : CFSG.IsComponent (conjSub (barMk Y b)⁻¹ LB) := isComponent_conjSub hLB _
  have hF1 : ∃ C : Subgroup (barQ Y), (C = LA ∨ C = conjSub (barMk Y a)⁻¹ LA) ∧
      (C = LB ∨ C = conjSub (barMk Y b)⁻¹ LB) := by
    by_contra hne
    have hcomm : ∀ {CA CB : Subgroup (barQ Y)}, CFSG.IsComponent CA → CFSG.IsComponent CB →
        (CA = LA ∨ CA = conjSub (barMk Y a)⁻¹ LA) → (CB = LB ∨ CB = conjSub (barMk Y b)⁻¹ LB) →
        ⁅CA, CB⁆ = ⊥ := by
      intro CA CB hCA hCB hA hB
      refine (CFSG.LocalCores.distinct_components_commute hCA hCB).resolve_left ?_
      intro h
      exact hne ⟨CA, hA, h ▸ hB⟩
    have h11 := hcomm hLA hLB (Or.inl rfl) (Or.inl rfl)
    have h12 := hcomm hLA hLB' (Or.inl rfl) (Or.inr rfl)
    have h21 := hcomm hLA' hLB (Or.inr rfl) (Or.inl rfl)
    have h22 := hcomm hLA' hLB' (Or.inr rfl) (Or.inr rfl)
    have hbot := commutator_sup_sup_eq_bot h11 h12 h21 h22
    apply hPne
    rw [← hPperf]
    exact le_bot_iff.mp ((Subgroup.commutator_mono hPA hPB).trans hbot.le)
  have hF2 : conjSub (barMk Y b)⁻¹ LA = LA ∨
      conjSub (barMk Y b)⁻¹ LA = conjSub (barMk Y a)⁻¹ LA := by
    have hL2A : TwoComponents.IsTwoComponent LA :=
      TwoLayerTransport.ordinary_isTwoComponent_of_corefree oddCore_barQ LA
        ((CFSG.isComponent_iff_open LA).mp hLA)
    obtain ⟨M, hM2, hML⟩ := OddKernelTwoComponents.exists_lift (barMk Y) barMk_surjective
      odd_card_ker_barMk LA hL2A
    have hMA : M ≤ pumpupY ΛA := (hiffA M hM2).mpr (Or.inl hML)
    have hMb2 : TwoComponents.IsTwoComponent (M.map (MulAut.conj b).toMonoidHom) :=
      (TwoComponentTransport.equiv_iff (MulAut.conj b) M).mpr hM2
    have hMbA : M.map (MulAut.conj b).toMonoidHom ≤ pumpupY ΛA :=
      (Subgroup.map_mono hMA).trans (map_conj_pumpupY_le_of_map_le ΛA hbΛA)
    have himg : (M.map (MulAut.conj b).toMonoidHom).map (barMk Y) = conjSub (barMk Y b)⁻¹ LA := by
      rw [hbbinv, Subgroup.map_map]
      have hcomp : (barMk Y).comp (MulAut.conj b).toMonoidHom =
          (MulAut.conj (barMk Y b)).toMonoidHom.comp (barMk Y) := by
        ext x
        simp
      rw [hcomp, ← Subgroup.map_map, hML]
    rw [← himg]
    exact (hiffA _ hMb2).mp hMbA
  have hconj_comm : ∀ K : Subgroup (barQ Y), conjSub (barMk Y b)⁻¹ (conjSub (barMk Y a)⁻¹ K) =
      conjSub (barMk Y a)⁻¹ (conjSub (barMk Y b)⁻¹ K) := by
    intro K
    rw [← conjSub_mul, ← conjSub_mul, hbbinv, haainv, hab_bar]
  have haa_twice : ∀ K : Subgroup (barQ Y), conjSub (barMk Y a)⁻¹ (conjSub (barMk Y a)⁻¹ K) = K :=
    fun K => conjSub_conjSub_of_inv_eq haainv K
  have hbb_twice : ∀ K : Subgroup (barQ Y), conjSub (barMk Y b)⁻¹ (conjSub (barMk Y b)⁻¹ K) = K :=
    fun K => conjSub_conjSub_of_inv_eq hbbinv K
  obtain ⟨C₀, hC₀A, hC₀B⟩ := hF1
  have hC₀b : conjSub (barMk Y b)⁻¹ C₀ = LA ∨ conjSub (barMk Y b)⁻¹ C₀ = conjSub (barMk Y a)⁻¹ LA := by
    rcases hC₀A with rfl | rfl
    · exact hF2
    · rw [hconj_comm]
      rcases hF2 with h | h
      · rw [h]; exact Or.inr rfl
      · rw [h, haa_twice]; exact Or.inl rfl
  have hIimg := (hiffB I hI2).mp hIB
  have hIA : I.map (barMk Y) = C₀ ∨ I.map (barMk Y) = conjSub (barMk Y b)⁻¹ C₀ := by
    rcases hC₀B with rfl | rfl
    · exact hIimg
    · rcases hIimg with h | h
      · right; rw [hbb_twice]; exact h
      · left; exact h
  refine (hiffA I hI2).mpr ?_
  rcases hIA with h | h
  · rw [h]; exact hC₀A
  · rw [h]; exact hC₀b

end Layer1

section Layer2

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_pumpUp_of_common {s a b : G} {A B Θ : Subgroup G}
    (hs : orderOf s = 2) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (has : a ∈ centralizer ({s} : Set G)) (hbs : b ∈ centralizer ({s} : Set G))
    (hab : a * b = b * a)
    (hA : IsPCompIn 2 (centralizer ({a} : Set G)) A) (hB : IsPCompIn 2 (centralizer ({b} : Set G)) B)
    (hsA : s ∈ centralizerSection A (pPrimeCoreOf 2 A))
    (hsB : s ∈ centralizerSection B (pPrimeCoreOf 2 B))
    (hbA : b ∈ normalizer (A : Set G))
    (hΘp : ⁅Θ, Θ⁆ = Θ) (hΘne : Θ ≠ ⊥)
    (hΘA : Θ ≤ pLayerOf 2 (A ⊓ centralizer ({s} : Set G)))
    (hΘB : Θ ≤ pLayerOf 2 (B ⊓ centralizer ({s} : Set G)))
    {I : Subgroup G} (hI : IsPCompIn 2 (centralizer ({s} : Set G)) I)
    (hIB : IsPCompIn 2 (pumpUp 2 B s) I) :
    IsPCompIn 2 (pumpUp 2 A s) I := by
  obtain ⟨ΛA, hΛA⟩ := exists_isLam (z := a) hs hA hsA
  obtain ⟨ΛB, hΛB⟩ := exists_isLam (z := b) hs hB hsB
  set Y' := centralizer ({s} : Set G) with hY'
  have haA : orderOf (⟨a, has⟩ : ↥Y') = 2 := orderOf_mk_centralizer has ha
  have hbB : orderOf (⟨b, hbs⟩ : ↥Y') = 2 := orderOf_mk_centralizer hbs hb
  have hΛAC := le_centralizer_mk (isPCompIn_two_iff.mp hΛA.pcW).1 has
  have hΛA2 := isTwoComponent_centralizer_mk hΛA.pcW has
  have hΛBC := le_centralizer_mk (isPCompIn_two_iff.mp hΛB.pcW).1 hbs
  have hΛB2 := isTwoComponent_centralizer_mk hΛB.pcW hbs
  obtain ⟨hΛAE, -⟩ := pumpupY_structure haA hΛAC hΛA2 |> fun h => (⟨h.1, h.2⟩ : _ ∧ _)
  obtain ⟨hΛBE, -⟩ := pumpupY_structure hbB hΛBC hΛB2 |> fun h => (⟨h.1, h.2⟩ : _ ∧ _)
  have hΘY : Θ ≤ Y' := (hΘA.trans (pLayerOf_le 2 _)).trans inf_le_right
  have hbN : b ∈ normalizer (ΛA : Set G) := mem_normalizer_lam hΛA hbs hbA
  have hbΛA : ∀ x ∈ ΛA.subgroupOf Y', (⟨b, hbs⟩ : ↥Y') * x * (⟨b, hbs⟩ : ↥Y')⁻¹ ∈ ΛA.subgroupOf Y' := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp hbN (x : G)).mp (Subgroup.mem_subgroupOf.mp hx)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  have hΘp' : ⁅Θ.subgroupOf Y', Θ.subgroupOf Y'⁆ = Θ.subgroupOf Y' := by
    apply Subgroup.map_injective Y'.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hΘY, hΘp]
  have hΘne' : Θ.subgroupOf Y' ≠ ⊥ := by
    intro h
    apply hΘne
    have := congrArg (Subgroup.map Y'.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hΘY, Subgroup.map_bot] at this
  have hΘA' : Θ.subgroupOf Y' ≤ ΛA.subgroupOf Y' := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (by
      rw [← hΛA.layer]; exact hΘA (Subgroup.mem_subgroupOf.mp hx))
  have hΘB' : Θ.subgroupOf Y' ≤ ΛB.subgroupOf Y' := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (by
      rw [← hΛB.layer]; exact hΘB (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨hI2, hIle⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛB.layer hΛBE hIB
  have hmain := pumpupY_le_of_common haA hbB (by
      apply Subtype.ext
      exact hab) hΛAC hΛA2 hΛBC hΛB2 hbΛA hΘA' hΘB' hΘp' hΘne' hI2 hIle
  have hJ : pumpUp 2 A s = (pumpupY (ΛA.subgroupOf Y')).map Y'.subtype := by
    rw [pumpUp_eq_map_pumpupY, hΛA.layer]
  have hIA : I ≤ pumpUp 2 A s := by
    rw [hJ]
    intro x hx
    exact ⟨⟨x, hI.1 hx⟩, hmain (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hAY : pumpUp 2 A s ≤ Y' := pumpUp_le_centralizer A s
  exact ⟨hIA, (CatalogueBAlternating.pComponent_two_iff _).mpr
    (TwoComponentTransport.restrict_nested I (pumpUp 2 A s) Y' hIA hAY
      (isPCompIn_two_iff.mp hI).2)⟩

end Layer2

section Main

variable {G : Type} [Group G]

theorem mem_normalizer_cmap_iff' {c y : G} {K : Subgroup G} :
    c * y * c⁻¹ ∈ normalizer (cmap c K : Set G) ↔ y ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h k
    have := h (c * k * c⁻¹)
    rw [mem_cmap, mem_cmap] at this
    rwa [show c⁻¹ * (c * k * c⁻¹) * c = k by group,
      show c⁻¹ * (c * y * c⁻¹ * (c * k * c⁻¹) * (c * y * c⁻¹)⁻¹) * c = y * k * y⁻¹ by group] at this
  · intro h g
    rw [mem_cmap, mem_cmap]
    have := h (c⁻¹ * g * c)
    rwa [show c⁻¹ * (c * y * c⁻¹ * g * (c * y * c⁻¹)⁻¹) * c = y * (c⁻¹ * g * c) * y⁻¹ by group]

theorem cmap_one' (K : Subgroup G) : cmap (1 : G) K = K := by
  ext x
  simp

@[expose] def T1 (z : G) (L : Subgroup G) : Prop :=
  ∀ (t : G) (J : Subgroup G), PumpUpLT 2 z L t J →
    z ∈ normalizer (J : Set G) ∧ Nonempty (kBar J ≃* kBar L)

@[expose] def GoodPair (z : G) (L : Subgroup G) : Prop :=
  IsILo 2 z L ∧ z ∈ L ∧ T1 z L

variable [Finite G]

theorem T1_cmap {z : G} {L : Subgroup G} (h : T1 z L) (c : G) : T1 (c * z * c⁻¹) (cmap c L) := by
  intro t J hlt
  have hlt' := pumpUpLT_cmap hlt c⁻¹
  rw [show c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z by group, cmap_inv_cancel] at hlt'
  obtain ⟨hN, ⟨e⟩⟩ := h _ _ hlt'
  refine ⟨?_, ?_⟩
  · have := (mem_normalizer_cmap_iff' (c := c) (y := z) (K := cmap c⁻¹ J)).mpr hN
    rwa [cmap_cancel] at this
  · obtain ⟨e1⟩ := nonempty_quot_cmap c⁻¹ J
    obtain ⟨e2⟩ := nonempty_quot_cmap c L
    exact ⟨e1.symm.trans (e.trans e2.symm)⟩

theorem GoodPair_cmap {z : G} {L : Subgroup G} (h : GoodPair z L) (c : G) :
    GoodPair (c * z * c⁻¹) (cmap c L) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isILo_cmap h1 c, ?_, T1_cmap h3 c⟩
  rw [mem_cmap]
  simpa [mul_assoc] using h2

theorem mem_normalizer_of_intrinsic {z t : G} {L J : Subgroup G} (hlt : PumpUpLT 2 z L t J)
    (hzL : z ∈ L) : z ∈ normalizer (J : Set G) := by
  have hzY : z ∈ centralizer ({t} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ, hJc, ⟨LB, hLB, himg, hcases⟩, -⟩ := step_core hlt hzY
  have hz2 : orderOf z = 2 := hlt.1.1
  have hzz : z ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, ← pow_one 2] at this
  have hzΛ : z ∈ Λ := hΛ.twoElt z (Subgroup.mem_inf.mpr ⟨hzL, hzY⟩) ⟨1, hzz⟩
  have hsmem : sbar z hzY ∈ bar t Λ := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hzΛ, rfl⟩
  have hs2 : orderOf (sbar z hzY) = 2 := orderOf_sbar hz2 hzY
  have hsinv : (sbar z hzY)⁻¹ = sbar z hzY := inv_eq_self_of_orderOf_eq_two hs2
  rcases hcases with ⟨hst, hAL⟩ | ⟨hne, hAB, hAD⟩
  · have hbarJ : bar t J = LB := by
      rcases himg with h | h
      · exact h
      · exact h.trans hst
    refine mem_normalizer_of_map_normalizes hJc.1 (isPCompIn_two_iff.mp hJc).2 hzY ?_
    show (bar t J).map (MulAut.conj (sbar z hzY)).toMonoidHom = bar t J
    rw [hbarJ]
    rw [hsinv] at hst
    exact hst
  · exfalso
    have hmem : sbar z hzY ∈ LB ⊔ conjSub (sbar z hzY)⁻¹ LB := by
      obtain ⟨l, hl⟩ := hAD hsmem
      have := swapDiag_mem_sup hAB l
      rw [hl] at this
      exact this
    exact hne (conjSub_eq_of_mem_sup hAB (inv_mem hmem))

omit [Finite G] in
theorem bar_cmap {u s : G} (hs : s ∈ centralizer ({u} : Set G)) (X : Subgroup G) :
    bar u (Stage1.Thm3.Sec4.cmap s X) = (bar u X).map (MulAut.conj (sbar s hs)).toMonoidHom := by
  ext w
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm' : (m : G) ∈ Stage1.Thm3.Sec4.cmap s X := Subgroup.mem_subgroupOf.mp hm
    rw [Stage1.Thm3.Sec4.mem_cmap] at hm'
    have hxC : s⁻¹ * (m : G) * s ∈ centralizer ({u} : Set G) :=
      mul_mem (mul_mem (inv_mem hs) m.2) hs
    refine ⟨barMk ↥(centralizer ({u} : Set G)) ⟨s⁻¹ * (m : G) * s, hxC⟩, ⟨⟨s⁻¹ * (m : G) * s, hxC⟩,
      Subgroup.mem_subgroupOf.mpr hm', rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sbar]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    refine ⟨⟨s, hs⟩ * x * ⟨s, hs⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [Stage1.Thm3.Sec4.mem_cmap]
      simpa [mul_assoc] using hx'
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sbar, map_mul, map_inv]

theorem eq_of_bar_eq {t : G} {X A B : Subgroup G} (hXt : X ≤ centralizer ({t} : Set G))
    (hA : IsPCompIn 2 X A) (hB : IsPCompIn 2 X B) (h : bar t A = bar t B) : A = B := by
  have key : ∀ {A B : Subgroup G}, IsPCompIn 2 X A → IsPCompIn 2 X B → bar t A ≤ bar t B → A ≤ B := by
    intro A B hA hB hle
    have hA2 := (isPCompIn_two_iff.mp hA).2
    have hB2 := (isPCompIn_two_iff.mp hB).2
    have hperf : Group.IsPerfect ↥(A.subgroupOf X) :=
      Group.isPerfect_def.mpr (TwoComponents.perfect hA2)
    have hmap : (A.subgroupOf X).map (barMk ↥X) ≤ (B.subgroupOf X).map (barMk ↥X) := by
      rintro _ ⟨p, hp, rfl⟩
      have hpA : (p : G) ∈ A := Subgroup.mem_subgroupOf.mp hp
      have hpC : (p : G) ∈ centralizer ({t} : Set G) := hXt p.2
      have hmem : barMk ↥(centralizer ({t} : Set G)) ⟨p, hpC⟩ ∈ bar t B :=
        hle ⟨⟨p, hpC⟩, Subgroup.mem_subgroupOf.mpr hpA, rfl⟩
      obtain ⟨b', hb', hbp⟩ := hmem
      have hbB : (b' : G) ∈ B := Subgroup.mem_subgroupOf.mp hb'
      have hbX : (b' : G) ∈ X := hB.1 hbB
      have hkC : (b' : G)⁻¹ * (p : G) ∈ centralizer ({t} : Set G) :=
        mul_mem (inv_mem b'.2) hpC
      have hk1 : barMk ↥(centralizer ({t} : Set G)) ⟨(b' : G)⁻¹ * (p : G), hkC⟩ = 1 := by
        have : (⟨(b' : G)⁻¹ * (p : G), hkC⟩ : ↥(centralizer ({t} : Set G))) =
            b'⁻¹ * ⟨p, hpC⟩ := rfl
        rw [this, map_mul, map_inv, hbp, inv_mul_cancel]
      have hkO := mem_pPrimeCoreOf_of_barMk_eq_one' (Λ := X) hXt (mul_mem (inv_mem hbX) p.2) hkC hk1
      obtain ⟨o, ho, hok⟩ := hkO
      refine ⟨⟨b', hbX⟩, Subgroup.mem_subgroupOf.mpr hbB, ?_⟩
      show barMk ↥X ⟨b', hbX⟩ = barMk ↥X p
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : o = (⟨b', hbX⟩ : ↥X)⁻¹ * p := Subtype.ext (by simpa using hok)
      rw [← this]
      exact ho
    have := le_of_perfect_map_le hperf hB2 hmap
    intro a ha
    exact Subgroup.mem_subgroupOf.mp (this (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hA.1 ha⟩ : ↥X) ∈ A.subgroupOf X))
  exact le_antisymm (key hA hB h.le) (key hB hA h.ge)

theorem pPrimeCoreOf_le_of_cover {Λ K : Subgroup G} (hΛK : Λ ≤ K)
    (hcov : ∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o) :
    pPrimeCoreOf 2 Λ ≤ pPrimeCoreOf 2 K := by
  rintro _ ⟨o, ho, rfl⟩
  have hker := ker_hatMap_eq_pPrimeCore hΛK hcov
  have h1 : hatMap hΛK o = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact ho
  exact (hatMap_eq_one_iff hΛK o).mp h1

theorem mem_cSec_of_cover {Λ K : Subgroup G} (hΛK : Λ ≤ K)
    (hcov : ∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o) {q : G}
    (hqΛ : q ∈ normalizer (Λ : Set G)) (hq : q ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    q ∈ centralizerSection Λ (pPrimeCoreOf 2 Λ) := by
  refine ⟨hqΛ, mem_normalizer_pPrimeCoreOf hqΛ, fun a ha => ?_⟩
  have hcΛ : ⁅a, q⁆ ∈ Λ := by
    have : ⁅a, q⁆ = a * (q * a⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp hqΛ a⁻¹).mp (inv_mem ha))
  have hcK : ⁅a, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2 a (hΛK ha)
  have hker := ker_hatMap_eq_pPrimeCore hΛK hcov
  have h1 : hatMap hΛK ⟨⁅a, q⁆, hcΛ⟩ = 1 := (hatMap_eq_one_iff hΛK _).mpr hcK
  have h2 : (⟨⁅a, q⁆, hcΛ⟩ : ↥Λ) ∈ pPrimeCore 2 ↥Λ := by
    rw [← hker]
    exact h1
  exact ⟨⟨⁅a, q⁆, hcΛ⟩, h2, rfl⟩

theorem mem_cSec_of_cover' {Λ K : Subgroup G} (hΛK : Λ ≤ K)
    (hcov : ∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o) {q : G}
    (hqK : q ∈ normalizer (K : Set G)) (hq : q ∈ centralizerSection Λ (pPrimeCoreOf 2 Λ)) :
    q ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
  have hqO : q ∈ normalizer (pPrimeCoreOf 2 K : Set G) := mem_normalizer_pPrimeCoreOf hqK
  refine ⟨hqK, hqO, fun k hk => ?_⟩
  obtain ⟨l, hl, o, ho, rfl⟩ := hcov k hk
  have hlK : l ∈ K := hΛK hl
  have hlq : ⁅l, q⁆ ∈ pPrimeCoreOf 2 K := pPrimeCoreOf_le_of_cover hΛK hcov (hq.2.2 l hl)
  have hoq : ⁅o, q⁆ ∈ pPrimeCoreOf 2 K := by
    have : ⁅o, q⁆ = o * (q * o⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem ho ((Subgroup.mem_normalizer_iff.mp hqO _).mp (inv_mem ho))
  have e2 : ⁅l * o, q⁆ = l * ⁅o, q⁆ * l⁻¹ * ⁅l, q⁆ := by
    simp only [commutatorElement_def]; group
  rw [e2]
  exact mul_mem (pPrimeCoreOf_normalized K hlK hoq) hlq

theorem mem_cSec_of_bar {t s : G} {Λ : Subgroup G} (hΛt : Λ ≤ centralizer ({t} : Set G))
    (hst : s ∈ centralizer ({t} : Set G)) (hsΛ : s ∈ normalizer (Λ : Set G))
    (hcen : ∀ w ∈ bar t Λ, sbar s hst * w * (sbar s hst)⁻¹ = w) :
    s ∈ centralizerSection Λ (pPrimeCoreOf 2 Λ) := by
  refine ⟨hsΛ, mem_normalizer_pPrimeCoreOf hsΛ, fun a ha => ?_⟩
  have haY : a ∈ centralizer ({t} : Set G) := hΛt ha
  have hcΛ : ⁅a, s⁆ ∈ Λ := by
    have : ⁅a, s⁆ = a * (s * a⁻¹ * s⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp hsΛ a⁻¹).mp (inv_mem ha))
  have hcY : ⁅a, s⁆ ∈ centralizer ({t} : Set G) := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem haY hst) (inv_mem haY)) (inv_mem hst)
  refine mem_pPrimeCoreOf_of_barMk_eq_one' (Y' := centralizer ({t} : Set G)) hΛt hcΛ hcY ?_
  have h1 := hcen (barMk _ ⟨a, haY⟩) ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have h2 : (⟨⁅a, s⁆, hcY⟩ : ↥(centralizer ({t} : Set G))) =
      ⟨a, haY⟩ * ⟨s, hst⟩ * ⟨a, haY⟩⁻¹ * ⟨s, hst⟩⁻¹ := rfl
  rw [h2]
  simp only [map_mul, map_inv]
  change barMk _ ⟨a, haY⟩ * sbar s hst * (barMk _ ⟨a, haY⟩)⁻¹ * (sbar s hst)⁻¹ = 1
  generalize barMk ↥(centralizer ({t} : Set G)) ⟨a, haY⟩ = α at h1 ⊢
  generalize sbar s hst = β at h1 ⊢
  have h3 : β * α = α * β := by
    calc β * α = (β * α * β⁻¹) * β := by group
      _ = α * β := by rw [h1]
  calc α * β * α⁻¹ * β⁻¹ = (β * α) * α⁻¹ * β⁻¹ := by rw [h3]
    _ = 1 := by group

end Main

end CFSG.GH74.GLS.Bg.Iii2.L41
