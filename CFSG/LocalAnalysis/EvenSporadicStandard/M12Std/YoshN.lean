module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshW

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.Fin76b.AutETable

section Setting

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

@[expose] noncomputable def Vg : Subgroup G := (Subgroup.prod ⊤ Wsub).map (jH e₀)

theorem mem_Vg_iff {y : G} :
    y ∈ Vg e₀ ↔ ∃ (a : Multiplicative (ZMod 2)) (w : G12), w ∈ Wsub ∧ y = jH e₀ (a, w) := by
  constructor
  · rintro ⟨⟨a, w⟩, hx, rfl⟩
    exact ⟨a, w, (Subgroup.mem_prod.1 hx).2, rfl⟩
  · rintro ⟨a, w, hw, rfl⟩
    exact ⟨(a, w), Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, hw⟩, rfl⟩

@[expose] noncomputable def Nn : Subgroup G := normalizer (Vg e₀)

theorem jH_mul_comm_fst (a a' : Multiplicative (ZMod 2)) (σ w : G12) :
    jH e₀ (a, σ) * jH e₀ (a', w) * (jH e₀ (a, σ))⁻¹ = jH e₀ (a', σ * w * σ⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext ?_ (by simp)
  show a * a' * a⁻¹ = a'
  rw [mul_comm a a']
  exact mul_inv_cancel_right a' a

theorem HcG_le_Nn : HcG e₀ ≤ Nn e₀ := by
  have key : ∀ y ∈ HcG e₀, ∀ v ∈ Vg e₀, y * v * y⁻¹ ∈ Vg e₀ := by
    intro y hy v hv
    obtain ⟨⟨a, σ⟩, rfl⟩ := (mem_range_jH e₀).2 hy.1
    obtain ⟨a', w, hw, rfl⟩ := (mem_Vg_iff e₀).1 hv
    have hcomm : σ * Jelt = Jelt * σ := by
      have h := mem_centralizer_iff.1 hy.2 (cG e₀) (Set.mem_singleton _)
      rw [cG_def] at h
      have h2 : jH e₀ ((1, Jelt) * (a, σ)) = jH e₀ ((a, σ) * (1, Jelt)) := by
        rw [map_mul, map_mul]
        exact h
      have h3 := congrArg Prod.snd (jH_injective e₀ h2)
      exact h3.symm
    rw [jH_mul_comm_fst]
    exact (mem_Vg_iff e₀).2 ⟨a', _, normalizes_Wsub hcomm hw, rfl⟩
  intro y hy
  rw [Nn, mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact key y hy v hv
  · intro hv
    have hyi : y⁻¹ ∈ HcG e₀ := inv_mem hy
    have := key y⁻¹ hyi _ hv
    simpa [mul_assoc] using this

theorem Nn_inf_centralizer : Nn e₀ ⊓ centralizer ({e} : Set G) = HcG e₀ := by
  apply le_antisymm
  · rintro n ⟨hnN, hnC⟩
    obtain ⟨⟨a, σ⟩, rfl⟩ := (mem_range_jH e₀).2 hnC
    have hiff := (mem_normalizer_iff.1 hnN)
    have h1 : ∀ w ∈ Wsub, σ * w * σ⁻¹ ∈ Wsub := by
      intro w hw
      have hv : jH e₀ (1, w) ∈ Vg e₀ := (mem_Vg_iff e₀).2 ⟨1, w, hw, rfl⟩
      have := (hiff _).1 hv
      rw [jH_mul_comm_fst] at this
      obtain ⟨a'', w'', hw'', hEq⟩ := (mem_Vg_iff e₀).1 this
      have h' : σ * w * σ⁻¹ = w'' := congrArg Prod.snd (jH_injective e₀ hEq)
      rw [h']
      exact hw''
    have h2 : ∀ w ∈ Wsub, σ⁻¹ * w * σ ∈ Wsub := by
      intro w hw
      have hv : jH e₀ (1, σ⁻¹ * w * σ) ∈ Vg e₀ := by
        have hmem : jH e₀ (1, w) ∈ Vg e₀ := (mem_Vg_iff e₀).2 ⟨1, w, hw, rfl⟩
        have := (hiff (jH e₀ (1, σ⁻¹ * w * σ))).2
        apply this
        rw [jH_mul_comm_fst]
        have e : σ * (σ⁻¹ * w * σ) * σ⁻¹ = w := by group
        rw [e]
        exact hmem
      obtain ⟨a'', w'', hw'', hEq⟩ := (mem_Vg_iff e₀).1 hv
      have h' : σ⁻¹ * w * σ = w'' := congrArg Prod.snd (jH_injective e₀ hEq)
      rw [h']
      exact hw''
    have hNW := mem_NW_of_normalizes h1 h2
    have hcomm := NW_le_centralizer hNW
    have hcomm' : σ * Jelt = Jelt * σ := Subtype.ext hcomm
    refine ⟨(mem_range_jH e₀).1 ⟨_, rfl⟩, mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rw [hh, cG_def, ιH, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (by simp [mul_comm]) ?_
    simpa using hcomm'.symm
  · intro y hy
    exact ⟨HcG_le_Nn e₀ hy, hy.1⟩

theorem Multiplicative_zmod_two_sq (a : Multiplicative (ZMod 2)) : a * a = 1 := by
  revert a; decide

include e₀ in
theorem not_isSq_e (he2 : orderOf e = 2) : ¬ ∃ g : G, g * g = e := by
  rintro ⟨g, hg⟩
  have hgc : g ∈ centralizer ({e} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← hg]
    group
  obtain ⟨⟨a, σ⟩, hgj⟩ := (mem_range_jH e₀).2 hgc
  have he := e_eq_jH e₀ he2
  rw [← hgj, ← map_mul] at hg
  have h1 := congrArg Prod.fst (jH_injective e₀ (hg.trans he))
  have h2 : a * a = Multiplicative.ofAdd (1 : ZMod 2) := h1
  rw [Multiplicative_zmod_two_sq] at h2
  exact ofAdd_one_ne_one h2.symm

theorem isSq_ιH {w : G12} (hw : w ∈ Wsub) : ∃ g : G, g * g = ιH e₀ w := by
  obtain ⟨g, hg⟩ := Wsub_isSq hw
  exact ⟨ιH e₀ g, by rw [← map_mul, hg]⟩

section DW

variable {d : G} {α : ℕ}

@[expose] noncomputable def dW (d : G) (m : G12) : G := ιH e₀ m * d * (ιH e₀ m)⁻¹

theorem dW_inv (hd : CentralSwap e₀ α d) (m : G12) : (dW e₀ d m)⁻¹ = dW e₀ d m := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd.sq
  unfold dW
  rw [mul_inv_rev, mul_inv_rev, inv_inv, hdi, mul_assoc]

theorem dW_e (hd : CentralSwap e₀ α d) (m : G12) :
    dW e₀ d m * e * (dW e₀ d m)⁻¹ = e * ιH e₀ (m * Jelt * m⁻¹) := by
  have hn : ιH e₀ m * e = e * ιH e₀ m := ιH_comm_e e₀ m
  have h1 : (ιH e₀ m)⁻¹ * e * ιH e₀ m = e := by
    rw [mul_assoc, ← hn]; group
  have h2 : ιH e₀ m * e * (ιH e₀ m)⁻¹ = e := by rw [hn]; group
  have h3 : ιH e₀ m * cG e₀ * (ιH e₀ m)⁻¹ = ιH e₀ (m * Jelt * m⁻¹) := by
    rw [cG_def, map_mul, map_mul, map_inv]
  unfold dW
  calc ιH e₀ m * d * (ιH e₀ m)⁻¹ * e * (ιH e₀ m * d * (ιH e₀ m)⁻¹)⁻¹
      = ιH e₀ m * d * ((ιH e₀ m)⁻¹ * e * ιH e₀ m) * d⁻¹ * (ιH e₀ m)⁻¹ := by group
    _ = ιH e₀ m * (d * e * d⁻¹) * (ιH e₀ m)⁻¹ := by rw [h1]; group
    _ = ιH e₀ m * (e * cG e₀) * (ιH e₀ m)⁻¹ := by rw [hd.conj_e]
    _ = (ιH e₀ m * e * (ιH e₀ m)⁻¹) * (ιH e₀ m * cG e₀ * (ιH e₀ m)⁻¹) := by group
    _ = e * ιH e₀ (m * Jelt * m⁻¹) := by rw [h2, h3]

theorem dW_conj_ιH (hd : CentralSwap e₀ α d) {m : G12} (hm : m * Jelt * m⁻¹ ∈ Wsub) {w' : G12}
    (hw' : w' ∈ Wsub) :
    ∃ k : ℕ, dW e₀ d m * ιH e₀ w' * (dW e₀ d m)⁻¹ = ιH e₀ (w' * (m * Jelt * m⁻¹) ^ k) := by
  set σ : G12 := m⁻¹ * w' * m with hσ
  have hcomm : σ * Jelt = Jelt * σ := by
    have hc := Wsub_comm hw' hm
    have e1 : σ * Jelt = m⁻¹ * (w' * (m * Jelt * m⁻¹)) * m := by rw [hσ]; group
    have e2 : Jelt * σ = m⁻¹ * ((m * Jelt * m⁻¹) * w') * m := by rw [hσ]; group
    rw [e1, e2, hc]
  have hconj := hd.conj_jH 1 σ hcomm
  refine ⟨(Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val +
    α * lamP (σ : Equiv.Perm (Fin 12)), ?_⟩
  have hw : ιH e₀ w' = ιH e₀ m * jH e₀ (1, σ) * (ιH e₀ m)⁻¹ := by
    have : jH e₀ (1, σ) = ιH e₀ σ := rfl
    rw [this, ← map_inv, ← map_mul, ← map_mul, hσ]
    congr 1
    group
  unfold dW
  have hinv : (ιH e₀ m * d * (ιH e₀ m)⁻¹)⁻¹ = ιH e₀ m * d⁻¹ * (ιH e₀ m)⁻¹ := by group
  calc ιH e₀ m * d * (ιH e₀ m)⁻¹ * ιH e₀ w' * (ιH e₀ m * d * (ιH e₀ m)⁻¹)⁻¹
      = ιH e₀ m * (d * jH e₀ (1, σ) * d⁻¹) * (ιH e₀ m)⁻¹ := by rw [hinv, hw]; group
    _ = ιH e₀ m * (jH e₀ (1, σ) *
        cG e₀ ^ ((Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val +
          α * lamP (σ : Equiv.Perm (Fin 12)))) * (ιH e₀ m)⁻¹ := by rw [hconj]
    _ = (ιH e₀ m * jH e₀ (1, σ) * (ιH e₀ m)⁻¹) * (ιH e₀ m * cG e₀ * (ιH e₀ m)⁻¹) ^
        ((Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val +
          α * lamP (σ : Equiv.Perm (Fin 12))) := by
        rw [conj_pow]; group
    _ = ιH e₀ (w' * (m * Jelt * m⁻¹) ^
        ((Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val +
          α * lamP (σ : Equiv.Perm (Fin 12)))) := by
        rw [← hw, show ιH e₀ m * cG e₀ * (ιH e₀ m)⁻¹ = ιH e₀ (m * Jelt * m⁻¹) by
          rw [cG_def, map_mul, map_mul, map_inv]]
        rw [map_mul (ιH e₀) w' ((m * Jelt * m⁻¹) ^ _), map_pow]

theorem mult_zmod_two_cases (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  revert a; decide

include e₀ in
theorem dW_mem_Nn (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) {m : G12}
    (hm : m * Jelt * m⁻¹ ∈ Wsub) : dW e₀ d m ∈ Nn e₀ := by
  have hinv := dW_inv e₀ hd m
  have hdd : dW e₀ d m * dW e₀ d m = 1 := by
    calc dW e₀ d m * dW e₀ d m = dW e₀ d m * (dW e₀ d m)⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel _
  have key : ∀ v ∈ Vg e₀, dW e₀ d m * v * (dW e₀ d m)⁻¹ ∈ Vg e₀ := by
    intro v hv
    obtain ⟨a', w', hw', rfl⟩ := (mem_Vg_iff e₀).1 hv
    have hsplit : jH e₀ (a', w') = jH e₀ (a', 1) * jH e₀ (1, w') := by
      rw [← map_mul]; simp
    have hfac : ∀ x y : G, dW e₀ d m * (x * y) * (dW e₀ d m)⁻¹ =
        (dW e₀ d m * x * (dW e₀ d m)⁻¹) * (dW e₀ d m * y * (dW e₀ d m)⁻¹) := by
      intro x y; group
    rw [hsplit, hfac]
    refine mul_mem ?_ ?_
    · rcases mult_zmod_two_cases a' with rfl | rfl
      · have h1 : jH e₀ (1, 1) = 1 := map_one (jH e₀)
        rw [h1]
        simp
      · have he := e_eq_jH e₀ he2
        rw [← he, dW_e e₀ hd]
        refine (mem_Vg_iff e₀).2 ⟨Multiplicative.ofAdd 1, m * Jelt * m⁻¹, hm, ?_⟩
        calc e * ιH e₀ (m * Jelt * m⁻¹) =
            jH e₀ (Multiplicative.ofAdd 1, 1) * jH e₀ (1, m * Jelt * m⁻¹) :=
              congrArg (fun x => x * ιH e₀ (m * Jelt * m⁻¹)) he
          _ = jH e₀ (Multiplicative.ofAdd 1, m * Jelt * m⁻¹) := by rw [← map_mul]; simp
    · obtain ⟨k, hk⟩ := dW_conj_ιH e₀ hd hm hw'
      have hj : jH e₀ (1, w') = ιH e₀ w' := rfl
      rw [hj, hk]
      exact (mem_Vg_iff e₀).2 ⟨1, w' * (m * Jelt * m⁻¹) ^ k, mul_mem hw' (pow_mem hm k), rfl⟩
  rw [Nn, mem_normalizer_iff]
  intro v
  constructor
  · exact key v
  · intro hv
    have := key _ hv
    rw [hinv] at this
    have e1 : dW e₀ d m * (dW e₀ d m * v * dW e₀ d m) * dW e₀ d m = v := by
      calc dW e₀ d m * (dW e₀ d m * v * dW e₀ d m) * dW e₀ d m =
          (dW e₀ d m * dW e₀ d m) * v * (dW e₀ d m * dW e₀ d m) := by group
        _ = v := by rw [hdd]; group
    rwa [e1] at this

end DW

section Count

@[expose, reducible] def NnAction : MulAction ↥(Nn e₀) G where
  smul n g := (n : G) * g * (n : G)⁻¹
  one_smul g := by
    show ((1 : ↥(Nn e₀)) : G) * g * ((1 : ↥(Nn e₀)) : G)⁻¹ = g
    simp
  mul_smul a b g := by
    show ((a * b : ↥(Nn e₀)) : G) * g * ((a * b : ↥(Nn e₀)) : G)⁻¹ =
      (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc]

theorem card_HcG : Nat.card (HcG e₀) = 384 := by
  rw [Nat.card_congr (ΘE e₀).toEquiv]
  exact yFacts.card_yK

variable {d : G} {α : ℕ}

include e₀ in
theorem orbit_e_eq (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) :
    letI := NnAction e₀
    MulAction.orbit ↥(Nn e₀) e = (fun w : G12 => e * ιH e₀ w) '' (Wsub : Set G12) := by
  let _ := NnAction e₀
  have he : e = jH e₀ (Multiplicative.ofAdd 1, 1) := e_eq_jH e₀ he2
  have heV : e ∈ Vg e₀ := (mem_Vg_iff e₀).2 ⟨Multiplicative.ofAdd 1, 1, one_mem _, he⟩
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    have hnV : (n : G) * e * (n : G)⁻¹ ∈ Vg e₀ := (mem_normalizer_iff.1 n.2 e).1 heV
    obtain ⟨a, w, hw, hEq⟩ := (mem_Vg_iff e₀).1 hnV
    rcases mult_zmod_two_cases a with rfl | rfl
    · exfalso
      have h1 : jH e₀ (1, w) = ιH e₀ w := rfl
      rw [h1] at hEq
      obtain ⟨g, hg⟩ := isSq_ιH e₀ hw
      apply not_isSq_e e₀ he2
      refine ⟨(n : G)⁻¹ * g * (n : G), ?_⟩
      calc (n : G)⁻¹ * g * (n : G) * ((n : G)⁻¹ * g * (n : G)) = (n : G)⁻¹ * (g * g) * (n : G) := by
            group
        _ = e := by rw [hg, ← hEq]; group
    · refine ⟨w, hw, ?_⟩
      show e * ιH e₀ w = (n : G) * e * (n : G)⁻¹
      rw [hEq]
      calc e * ιH e₀ w = jH e₀ (Multiplicative.ofAdd 1, 1) * jH e₀ (1, w) :=
            congrArg (fun x => x * ιH e₀ w) he
        _ = jH e₀ (Multiplicative.ofAdd 1, w) := by rw [← map_mul]; simp
  · rintro ⟨w, hw, rfl⟩
    by_cases h1 : w = 1
    · refine ⟨1, ?_⟩
      show ((1 : ↥(Nn e₀)) : G) * e * ((1 : ↥(Nn e₀)) : G)⁻¹ = e * ιH e₀ w
      simp [h1]
    · obtain ⟨m, hm⟩ := exists_conj_J hw h1
      have hmW : m * Jelt * m⁻¹ ∈ Wsub := hm ▸ hw
      refine ⟨⟨dW e₀ d m, dW_mem_Nn e₀ he2 hd hmW⟩, ?_⟩
      show dW e₀ d m * e * (dW e₀ d m)⁻¹ = e * ιH e₀ w
      rw [dW_e e₀ hd, hm]

include e₀ in
theorem card_Nn (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) : Nat.card (Nn e₀) = 3072 := by
  let _ := NnAction e₀
  have horb := orbit_e_eq e₀ he2 hd
  have hidx := MulAction.index_stabilizer ↥(Nn e₀) e
  have hinj : Function.Injective (fun w : G12 => e * ιH e₀ w) := by
    intro w w' h
    exact ιH_injective e₀ (mul_left_cancel h)
  have h8 : (MulAction.orbit ↥(Nn e₀) e).ncard = 8 := by
    rw [horb, Set.ncard_image_of_injective _ hinj]
    exact (Nat.card_coe_set_eq (Wsub : Set G12)).symm.trans card_Wsub
  have hmap : (MulAction.stabilizer ↥(Nn e₀) e).map (Nn e₀).subtype = HcG e₀ := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' : (n : G) * e * (n : G)⁻¹ = e := MulAction.mem_stabilizer_iff.1 hn
      have hcomm : e * (n : G) = (n : G) * e := by
        calc e * (n : G) = ((n : G) * e * (n : G)⁻¹) * (n : G) := by rw [hn']
          _ = (n : G) * e := by group
      rw [← Nn_inf_centralizer e₀]
      refine ⟨n.2, mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm
    · intro hy
      rw [← Nn_inf_centralizer e₀] at hy
      obtain ⟨hyN, hyC⟩ := hy
      refine ⟨⟨y, hyN⟩, MulAction.mem_stabilizer_iff.2 ?_, rfl⟩
      show y * e * y⁻¹ = e
      have hc : e * y = y * e := mem_centralizer_iff.1 hyC e (Set.mem_singleton e)
      calc y * e * y⁻¹ = e * y * y⁻¹ := by rw [hc]
        _ = e := by group
  have hstab : Nat.card (MulAction.stabilizer ↥(Nn e₀) e) = 384 := by
    rw [← Subgroup.card_map_of_injective (f := (Nn e₀).subtype) Subtype.val_injective, hmap,
      card_HcG]
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(Nn e₀) e)
  rw [hstab, hidx, h8] at hmul
  omega

end Count

end Setting

end CFSG.EvenSporadicStandard.M12Std.Yosh
