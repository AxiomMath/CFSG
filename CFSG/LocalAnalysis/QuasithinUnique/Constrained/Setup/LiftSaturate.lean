module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect4

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer Module
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem natCard_eq_ker_mul_range {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] (f : M →ₗ[k] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at h1
  rw [h1, mul_comm]

theorem irreducible_section_weight_equality_saturates [Finite V] {L A : Subgroup (V ≃ₗ[k] V)}
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V))) (hLA : ⁅L, A⁆ = L)
    (hmax : ∀ B : Subgroup (V ≃ₗ[k] V), B ≤ A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    {I : Submodule k V} (hinvL : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) L I)
    (hinvA : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I) (hIL : commGL L I = I)
    (hinj : ∀ a : ↥A,
      actOn L A I hAn (isInvariant_sup_subgroup hinvL hinvA) A le_sup_right a = 1 →
        resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a = 1)
    (hAW : (actOn L A I hAn (isInvariant_sup_subgroup hinvL hinvA) A le_sup_right).range ≠ ⊥)
    (hw : weight (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] (↥I ⧸ fixIn L I)))
        (actOn L A I hAn (isInvariant_sup_subgroup hinvL hinvA) A le_sup_right).range =
      Nat.card (↥I ⧸ fixIn L I)) :
    (∀ a : ↥A, resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a = 1 → a = 1) ∧
    (∀ a : ↥A, actOn L A I hAn (isInvariant_sup_subgroup hinvL hinvA) A le_sup_right a = 1 →
      a = 1) ∧
    I ⊔ fixGL A = ⊤ ∧ commGL L ⊤ = I ∧ commGL (L ⊔ A) ⊤ = I ∧ I ⊓ fixGL L ≤ fixGL (L ⊔ A) ∧
    weight (MonoidHom.id (V ≃ₗ[k] V)) A = Nat.card V := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I :=
    isInvariant_sup_subgroup hinvL hinvA
  set ρ : ↥A →* (V ≃ₗ[k] V) := (MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype with hρ
  have hW : ∀ a : ↥A, ∀ w ∈ I, ρ a w ∈ I := fun a w hw => hinvA a a.2 w hw
  set R := actOn L A I hAn hI A le_sup_right with hR
  have hfix : fixSub ρ ⊤ = fixGL A := by
    ext v
    simp only [mem_fixSub, Subgroup.mem_top, forall_true_left]
    constructor
    · intro h a ha
      exact h ⟨a, ha⟩
    · intro h a
      exact h a a.2
  have hRmk : ∀ (a : ↥A) (u : ↥I), R a (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a u) :=
    fun a u => actOn_A_mk hAn hinvL hinvA a u
  have hRtriv : ∀ a : ↥A, (∀ u ∈ I, ρ a u = u) → R a = 1 := by
    intro a ha
    apply LinearEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hRmk]
    have : resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a u = u := by
      apply Subtype.ext
      rw [resSub_apply]
      exact ha u u.2
    rw [this]
    rfl
  have hker : R.ker = centSub ρ I := by
    ext a
    rw [MonoidHom.mem_ker, mem_centSub]
    constructor
    · intro h u hu
      have h1 := hinj a h
      have h2 := congrArg (fun φ : ↥I ≃ₗ[k] ↥I => (φ ⟨u, hu⟩ : V)) h1
      have h3 : (a : V ≃ₗ[k] V) u = u := by simpa [resSub_apply] using h2
      exact h3
    · exact hRtriv a
  have hwt : ∀ B : Subgroup ↥A, weight ρ B = weight (MonoidHom.id (V ≃ₗ[k] V)) (B.map A.subtype) :=
    fun B => weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) A B
  have hmaxρ : ∀ B : Subgroup ↥A, weight ρ B ≤ weight ρ ⊤ := by
    intro B
    rw [hwt, hwt, map_subtype_top]
    exact hmax _ (by rintro _ ⟨b, -, rfl⟩; exact b.2)
  have hstrictρ : ∀ B : Subgroup ↥A, ⊥ < B → B < ⊤ → weight ρ B < weight ρ ⊤ := by
    intro B hB1 hB2
    rw [hwt, hwt, map_subtype_top]
    apply hstrict
    · refine bot_lt_iff_ne_bot.2 fun h => ?_
      rw [Subgroup.map_eq_bot_iff_of_injective B A.subtype_injective] at h
      exact (bot_lt_iff_ne_bot.1 hB1) h
    · refine lt_of_le_of_ne (by rintro _ ⟨b, -, rfl⟩; exact b.2) fun h => ?_
      have h' : B.map A.subtype = (⊤ : Subgroup ↥A).map A.subtype := by
        rw [map_subtype_top]; exact h
      exact (lt_top_iff_ne_top.1 hB2) (Subgroup.map_injective A.subtype_injective h')
  have hWA : commSub ρ ⊤ I ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply hAW
    rw [MonoidHom.range_eq_bot_iff]
    ext a : 1
    exact congrArg (fun f => f a) (show R = 1 from by
      ext a' : 1
      exact hRtriv a' (fun u hu => h a' (Subgroup.mem_top a') u hu))
  obtain ⟨h1, -, hlast⟩ :=
    minimal_fixedWeight_restriction_faithful_splitting ρ I hW hmaxρ hstrictρ hWA
  set m := (centSub ρ I).index with hm
  set c := Nat.card ↥(I ⊓ fixSub ρ ⊤) with hc
  have hIle : Nat.card ↥I ≤ m * c := by
    have := h1 ⊥ bot_le
    rw [weight_bot, weightId_range] at this
    exact this
  have hRcard : Nat.card ↥R.range = m := by
    rw [← Subgroup.index_ker, hker]
  set a := Nat.card (↥I ⧸ fixIn L I) with ha
  set cW := Nat.card ↥(fixSub (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] (↥I ⧸ fixIn L I))) R.range)
    with hcW
  have hmcW : m * cW = a := by
    have := hw
    unfold weight at this
    rw [hRcard] at this
    exact this
  set z := Nat.card ↥(fixIn L I) with hz
  have hIaz : Nat.card ↥I = a * z := by
    rw [mul_comm]
    exact Submodule.card_eq_card_quotient_mul_card (fixIn L I)
  let f : ↥(I ⊓ fixSub ρ ⊤) →ₗ[k] (↥I ⧸ fixIn L I) :=
    (fixIn L I).mkQ ∘ₗ Submodule.inclusion (inf_le_left : I ⊓ fixSub ρ ⊤ ≤ I)
  have hf : ∀ v : ↥(I ⊓ fixSub ρ ⊤), f v = Submodule.Quotient.mk ⟨(v : V), v.2.1⟩ := fun v => rfl
  have hfcard := natCard_eq_ker_mul_range f
  have hrange : Nat.card ↥(LinearMap.range f) ≤ cW := by
    have hle : LinearMap.range f ≤
        fixSub (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] (↥I ⧸ fixIn L I))) R.range := by
      rintro _ ⟨v, rfl⟩ y hy
      obtain ⟨a', rfl⟩ := hy
      change R a' (f v) = f v
      rw [hf, hRmk]
      have : resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a' ⟨(v : V), v.2.1⟩ =
          ⟨(v : V), v.2.1⟩ := by
        apply Subtype.ext
        rw [resSub_apply]
        exact v.2.2 a' (Subgroup.mem_top a')
      rw [this]
    exact Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le hle)
  let g : ↥(LinearMap.ker f) → ↥(fixIn L I) := fun v =>
    ⟨⟨(v.1 : V), v.1.2.1⟩, by
      have h0 : f v.1 = 0 := v.2
      rw [hf] at h0
      exact (Submodule.Quotient.mk_eq_zero _).1 h0⟩
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun x : ↥(fixIn L I) => ((x : ↥I) : V)) hvw
    exact this
  have hkerz : Nat.card ↥(LinearMap.ker f) ≤ z := Nat.card_le_card_of_injective g hginj
  have hcy : c ≤ Nat.card ↥(LinearMap.ker f) * cW :=
    calc c = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f) := hfcard
      _ ≤ Nat.card ↥(LinearMap.ker f) * cW := Nat.mul_le_mul_left _ hrange
  have h5 : m * c ≤ a * Nat.card ↥(LinearMap.ker f) :=
    calc m * c ≤ m * (Nat.card ↥(LinearMap.ker f) * cW) := Nat.mul_le_mul_left _ hcy
      _ = (m * cW) * Nat.card ↥(LinearMap.ker f) := by ring
      _ = a * Nat.card ↥(LinearMap.ker f) := by rw [hmcW]
  have h6 : a * Nat.card ↥(LinearMap.ker f) ≤ a * z := Nat.mul_le_mul_left _ hkerz
  have h7 : a * z ≤ m * c := by rw [← hIaz]; exact hIle
  have hmc : m * c = Nat.card ↥I := by
    rw [hIaz]
    exact le_antisymm (h5.trans h6) h7
  have hy : Nat.card ↥(LinearMap.ker f) = z := by
    have : a * Nat.card ↥(LinearMap.ker f) = a * z := le_antisymm h6 (h7.trans h5)
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
  obtain ⟨hcent, hsup⟩ := hlast hmc
  have hg : Function.Bijective g := hginj.bijective_of_nat_card_le (by rw [hy])
  have hfaith : ∀ a' : ↥A, resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a' = 1 → a' = 1 := by
    intro a' h
    have : a' ∈ centSub ρ I := by
      intro u hu
      have h2 := congrArg (fun φ : ↥I ≃ₗ[k] ↥I => (φ ⟨u, hu⟩ : V)) h
      have h3 : (a' : V ≃ₗ[k] V) u = u := by simpa [resSub_apply] using h2
      exact h3
    rw [hcent] at this
    exact Subgroup.mem_bot.1 this
  have hVI : I ⊔ fixGL A = ⊤ := by rw [← hfix]; exact hsup
  have hAtriv : A ≤ trivMod I := by
    intro x hx w
    have hw' : w ∈ I ⊔ fixGL A := by rw [hVI]; trivial
    obtain ⟨i, hi, c', hc', rfl⟩ := Submodule.mem_sup.1 hw'
    have h8 : x c' = c' := hc' x hx
    rw [map_add, h8]
    have : x i + c' - (i + c') = x i - i := by abel
    rw [this]
    exact I.sub_mem (hinvA x hx i hi) hi
  have hLtriv : L ≤ trivMod I := by
    calc L = ⁅L, A⁆ := hLA.symm
      _ ≤ trivMod I := by
        refine Subgroup.commutator_le.2 fun l hl a' ha' => ?_
        rw [commutatorElement_def]
        exact (trivMod I).mul_mem (conj_mem_trivMod (fun z hz => hinvL l hl z hz) (hAtriv ha'))
          ((trivMod I).inv_mem (hAtriv ha'))
  have hLAtriv : L ⊔ A ≤ trivMod I := sup_le hLtriv hAtriv
  have hcomm_le : commGL (L ⊔ A) ⊤ ≤ I :=
    commSub_le_iff.2 fun b hb u _ => mem_trivMod.1 (hLAtriv hb) u
  have hIL' : I ≤ commGL L ⊤ :=
    calc I = commGL L I := hIL.symm
      _ ≤ commGL L ⊤ := commSub_mono_right _ le_top
  have hweight : weight (MonoidHom.id (V ≃ₗ[k] V)) A = Nat.card V := by
    have hm' : m = Nat.card ↥A := by rw [hm, hcent, Subgroup.index_bot]
    have hc' : c = Nat.card ↥(I ⊓ fixGL A) := by rw [hc, hfix]
    have e1 := natCard_sup_mul_natCard_inf I (fixGL A)
    rw [hVI] at e1
    have hVc : Nat.card ↥(⊤ : Submodule k V) = Nat.card V :=
      Nat.card_congr (Submodule.topEquiv (R := k) (M := V)).toEquiv
    rw [hVc, ← hc'] at e1
    rw [hm'] at hmc
    have hcpos : 0 < c := Nat.card_pos
    unfold weight
    apply Nat.eq_of_mul_eq_mul_right hcpos
    calc Nat.card ↥A * Nat.card ↥(fixSub (MonoidHom.id (V ≃ₗ[k] V)) A) * c
        = (Nat.card ↥A * c) * Nat.card ↥(fixGL A) := by ring
      _ = Nat.card ↥I * Nat.card ↥(fixGL A) := by rw [hmc]
      _ = Nat.card V * c := e1.symm
  refine ⟨hfaith, fun a' h => hfaith a' (hinj a' h), hVI, ?_, ?_, ?_, hweight⟩
  · exact le_antisymm ((commSub_mono_left _ le_sup_left).trans hcomm_le) hIL'
  · exact le_antisymm hcomm_le (hIL'.trans (commSub_mono_left _ le_sup_left))
  · intro w hw
    have hwA : w ∈ fixGL A := by
      obtain ⟨v, hv⟩ := hg.2 ⟨⟨w, hw.1⟩, hw.2⟩
      have h9 : (v.1 : V) = w := congrArg (fun x : ↥(fixIn L I) => ((x : ↥I) : V)) hv
      have h10 : (v.1 : V) ∈ fixSub ρ ⊤ := v.1.2.2
      rw [h9, hfix] at h10
      exact h10
    have : fixGL (L ⊔ A) = fixGL L ⊓ fixGL A := fixSub_sup _ L A
    rw [this]
    exact ⟨hw.2, hwA⟩

end CFSG.QuasithinUnique.Setup.Lift
