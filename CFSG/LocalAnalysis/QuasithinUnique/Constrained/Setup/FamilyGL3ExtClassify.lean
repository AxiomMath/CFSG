module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Ext
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Classify
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Sub

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

section Setup

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (ρ : H32 →* (E ≃ₗ[ZMod 2] E))

theorem rep_tGen_sq (x : E) : ρ tGen (ρ tGen x) = x := by
  have h : ρ (tGen * tGen) = 1 := by rw [tGen_mul_self, map_one]
  rw [map_mul] at h
  exact LinearEquiv.congr_fun h x

theorem rep_tGen_conj (g : GL32) (x : E) :
    ρ tGen (ρ (sIncl g) x) = ρ (sIncl (tauHom g)) (ρ tGen x) := by
  have h : ρ (tGen * sIncl g) = ρ (sIncl (tauHom g) * tGen) := by rw [tGen_mul_sIncl]
  rw [map_mul, map_mul] at h
  exact LinearEquiv.congr_fun h x

theorem rep_conj_tGen (g : GL32) (x : E) :
    ρ (sIncl g) (ρ tGen x) = ρ tGen (ρ (sIncl (tauHom g)) x) := by
  rw [rep_tGen_conj, tauHom_tauHom]

theorem transQ_transQ (X : traceZero) : transQ (transQ X) = X :=
  LinearEquiv.congr_fun transQ_mul_self X

theorem repA_tau_apply (g : GL32) (Y : traceZero) :
    repA (tauHom g) (transQ Y) = transQ (repA g Y) := by
  have hinv : transQ⁻¹ = transQ := inv_eq_of_mul_eq_one_right transQ_mul_self
  rw [repA_tau, hinv]
  show transQ (repA g (transQ (transQ Y))) = _
  rw [transQ_transQ]

end Setup

theorem fixed_traceZero_eq (X : traceZero) (hX : ∀ t ∈ sylowT, repA t X = X) :
    X = 0 ∨ (X : Mat3) = E13 := by
  have h1 : unitri 1 0 0 * (X : Mat3) * unitri 1 (1 * 0 + 0) 0 = X :=
    congrArg Subtype.val (hX (unitriGL 1 0 0) ⟨1, 0, 0, rfl⟩)
  have h2 : unitri 0 0 1 * (X : Mat3) * unitri 0 (0 * 1 + 0) 1 = X :=
    congrArg Subtype.val (hX (unitriGL 0 0 1) ⟨0, 0, 1, rfl⟩)
  have hXe := eq_traceZeroMat X.2
  rcases fixed_traceZeroMat ((X : Mat3) 0 0) ((X : Mat3) 0 1) ((X : Mat3) 0 2) ((X : Mat3) 1 0)
    ((X : Mat3) 1 1) ((X : Mat3) 1 2) ((X : Mat3) 2 0) ((X : Mat3) 2 1)
    (by rw [← hXe]; exact h1) (by rw [← hXe]; exact h2) with h | h
  · left
    exact Subtype.ext (hXe.trans h)
  · right
    exact hXe.trans h

theorem E13_mem : E13 ∈ traceZero := by
  rw [mem_traceZero_iff_trace]
  decide

theorem E13_fixed : ∀ a b c : ZMod 2, unitri a b c * E13 * unitri a (a * c + b) c = E13 := by
  decide

theorem endS_traceZero (N : traceZero ≃ₗ[ZMod 2] traceZero)
    (hN : ∀ g X, N (repA g X) = repA g (N X)) : N = 1 := by
  have hE : ∀ t ∈ sylowT, repA t ⟨E13, E13_mem⟩ = ⟨E13, E13_mem⟩ := by
    rintro _ ⟨a, b, c, rfl⟩
    exact Subtype.ext (E13_fixed a b c)
  have hfix : ∀ t ∈ sylowT, repA t (N ⟨E13, E13_mem⟩) = N ⟨E13, E13_mem⟩ := fun t ht => by
    rw [← hN, hE t ht]
  have hne : N ⟨E13, E13_mem⟩ ≠ 0 := by
    intro h
    have := N.injective (h.trans (map_zero N).symm)
    have h2 : E13 = (0 : Mat3) := congrArg Subtype.val this
    have : (E13 : Mat3) 0 2 = 1 := by simp [E13]
    rw [h2] at this
    simp at this
  have hN13 : N ⟨E13, E13_mem⟩ = ⟨E13, E13_mem⟩ := by
    rcases fixed_traceZero_eq _ hfix with h | h
    · exact absurd h hne
    · exact Subtype.ext h
  let K : Submodule (ZMod 2) traceZero :=
    LinearMap.ker ((N : traceZero →ₗ[ZMod 2] traceZero) - LinearMap.id)
  have hK : ∀ g, ∀ X ∈ K, repA g X ∈ K := by
    intro g X hX
    have h1 : N X = X := by
      have := hX
      simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at this
      exact sub_eq_zero.1 this
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    show N (repA g X) - repA g X = 0
    rw [hN, h1, sub_self]
  rcases isIrr_repA.2.2 K hK with h | h
  · exfalso
    have : (⟨E13, E13_mem⟩ : traceZero) ∈ K := by
      show N ⟨E13, E13_mem⟩ - ⟨E13, E13_mem⟩ = 0
      rw [hN13, sub_self]
    rw [h] at this
    have h3 : (⟨E13, E13_mem⟩ : traceZero) = 0 := by simpa using this
    have h4 : E13 = (0 : Mat3) := congrArg Subtype.val h3
    have : (E13 : Mat3) 0 2 = 1 := by simp [E13]
    rw [h4] at this
    simp at this
  · refine LinearEquiv.ext fun X => ?_
    have : X ∈ K := by rw [h]; trivial
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at this
    exact sub_eq_zero.1 this

section CaseI

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
  {ρ : H32 →* (E ≃ₗ[ZMod 2] E)}

theorem caseI (hS : IsIrrRep (ρ.comp sIncl)) :
    ModIso repHTriv ρ ∨ ModIso repQ ρ := by
  rcases irreducible_binary_GL3_classification (ρ.comp sIncl) hS with h | h | h | h
  ·
    left
    obtain ⟨φ, hφ⟩ := h
    have hS1 : ∀ g y, ρ (sIncl g) y = y := fun g y => by
      obtain ⟨c, rfl⟩ := φ.surjective y
      have := hφ g c
      exact this.symm
    have hone : ∀ y : E, y ≠ 0 → y = φ 1 := fun y hy => by
      obtain ⟨c, rfl⟩ := φ.surjective y
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · exact absurd (map_zero φ) hy
      · rfl
    have hT1 : ∀ y, ρ tGen y = y := fun y => by
      obtain ⟨c, rfl⟩ := φ.surjective y
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [map_zero, map_zero]
      · have hne : ρ tGen (φ 1) ≠ 0 := fun h0 => by
          have h1 := (ρ tGen).injective (h0.trans (map_zero (ρ tGen)).symm)
          have h2 : φ 1 = φ 0 := h1.trans (map_zero φ).symm
          exact absurd (φ.injective h2) (by decide)
        exact hone _ hne
    exact modIso_of_gens φ (fun g x => (hS1 g _).symm) (fun x => (hT1 _).symm)
  ·
    exfalso
    obtain ⟨φ, hφ⟩ := h
    have hφ' : ∀ g v, φ (repV g v) = ρ (sIncl g) (φ v) := hφ
    have key : ∀ (h : GL32) (y : E), φ.symm (ρ (sIncl h) y) = repV h (φ.symm y) := fun h y => by
      have h1 := hφ' h (φ.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [← h1, LinearEquiv.symm_apply_apply]
    refine not_modIso_repV_repDual ⟨φ.trans ((ρ tGen).trans φ.symm), fun g v => ?_⟩
    show φ.symm (ρ tGen (φ (repV g v))) = repDual g (φ.symm (ρ tGen (φ v)))
    rw [hφ' g v, rep_tGen_conj ρ g, key]
    rfl
  ·
    exfalso
    obtain ⟨φ, hφ⟩ := h
    have hφ' : ∀ g v, φ (repDual g v) = ρ (sIncl g) (φ v) := hφ
    have key : ∀ (h : GL32) (y : E), φ.symm (ρ (sIncl h) y) = repDual h (φ.symm y) :=
      fun h y => by
        have h1 := hφ' h (φ.symm y)
        rw [LinearEquiv.apply_symm_apply] at h1
        rw [← h1, LinearEquiv.symm_apply_apply]
    refine not_modIso_repV_repDual (ActIso.symm
      (⟨φ.trans ((ρ tGen).trans φ.symm), fun g v => ?_⟩ : ModIso repDual repV))
    show φ.symm (ρ tGen (φ (repDual g v))) = repV g (φ.symm (ρ tGen (φ v)))
    rw [hφ' g v, rep_tGen_conj ρ g, key]
    change repV (tauHom (tauHom g)) _ = _
    rw [tauHom_tauHom]
  ·
    right
    obtain ⟨φ, hφ⟩ := h
    have hφ' : ∀ g X, φ (repA g X) = ρ (sIncl g) (φ X) := hφ
    have key : ∀ (h : GL32) (y : E), φ.symm (ρ (sIncl h) y) = repA h (φ.symm y) := fun h y => by
      have h1 := hφ' h (φ.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [← h1, LinearEquiv.symm_apply_apply]
    let ψ : traceZero ≃ₗ[ZMod 2] traceZero := φ.trans ((ρ tGen).trans φ.symm)
    have hψ : ∀ g X, ψ (repA g X) = repA (tauHom g) (ψ X) := fun g X => by
      show φ.symm (ρ tGen (φ (repA g X))) = repA (tauHom g) (φ.symm (ρ tGen (φ X)))
      rw [hφ' g X, rep_tGen_conj ρ g, key]
    have htr : ∀ g Y, transQ (repA (tauHom g) Y) = repA g (transQ Y) := fun g Y => by
      have h1 := repA_tau (tauHom g)
      rw [tauHom_tauHom] at h1
      have hinv : transQ⁻¹ = transQ := inv_eq_of_mul_eq_one_right transQ_mul_self
      rw [h1, hinv]
      show transQ (repA (tauHom g) Y) = transQ (repA (tauHom g) (transQ (transQ Y)))
      rw [transQ_transQ]
    let N : traceZero ≃ₗ[ZMod 2] traceZero := ψ.trans transQ
    have hN : ∀ g X, N (repA g X) = repA g (N X) := fun g X => by
      show transQ (ψ (repA g X)) = repA g (transQ (ψ X))
      rw [hψ g X, htr]
    have hN1 := endS_traceZero N hN
    have hψT : ∀ X, ψ X = transQ X := fun X => by
      have h2 : transQ (ψ X) = X := LinearEquiv.congr_fun hN1 X
      calc ψ X = transQ (transQ (ψ X)) := (transQ_transQ _).symm
        _ = transQ X := by rw [h2]
    refine modIso_of_gens φ (fun g x => ?_) (fun X => ?_)
    · rw [repQ_sIncl]
      exact hφ' g x
    · rw [repQ_tGen]
      have h4 : ρ tGen (φ X) = φ (ψ X) := by
        show _ = φ (φ.symm (ρ tGen (φ X)))
        rw [LinearEquiv.apply_symm_apply]
      rw [h4, hψT X]

end CaseI

section CaseII

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {ρ : H32 →* (E ≃ₗ[ZMod 2] E)}

theorem modIso_repP_of_embedding (φ : Vec3 →ₗ[ZMod 2] E) (hφinj : Function.Injective φ)
    (hφ : ∀ g v, φ (repV g v) = ρ (sIncl g) (φ v))
    (hinf : ∀ a b, φ a = ρ tGen (φ b) → φ a = 0)
    (hsup : ∀ x : E, ∃ a b, x = φ a + ρ tGen (φ b)) : ModIso repP ρ := by
  let Ψ : P6 →ₗ[ZMod 2] E :=
    φ.comp (LinearMap.fst (ZMod 2) Vec3 Vec3) +
      ((ρ tGen : E →ₗ[ZMod 2] E).comp φ).comp (LinearMap.snd (ZMod 2) Vec3 Vec3)
  have hΨ : ∀ a b, Ψ (a, b) = φ a + ρ tGen (φ b) := fun a b => rfl
  have hinj : Function.Injective Ψ := by
    refine injective_of_ker_eq_bot Ψ (eq_bot_iff.2 fun x hx => ?_)
    obtain ⟨a, b⟩ := x
    have h0 : φ a + ρ tGen (φ b) = 0 := hx
    have h1 : φ a = ρ tGen (φ b) := by
      calc φ a = φ a + (ρ tGen (φ b) + ρ tGen (φ b)) := by
            rw [add_self_eq_zero_of_zmod_two, add_zero]
        _ = (φ a + ρ tGen (φ b)) + ρ tGen (φ b) := by rw [add_assoc]
        _ = ρ tGen (φ b) := by rw [h0, zero_add]
    have ha : φ a = 0 := hinf a b h1
    have ha0 : a = 0 := hφinj (ha.trans (map_zero φ).symm)
    have hb : ρ tGen (φ b) = 0 := by rw [← h1, ha]
    have hb' : φ b = 0 := (ρ tGen).injective (hb.trans (map_zero _).symm)
    have hb0 : b = 0 := hφinj (hb'.trans (map_zero φ).symm)
    rw [Submodule.mem_bot]
    exact Prod.ext ha0 hb0
  have hsurj : Function.Surjective Ψ := fun x => by
    obtain ⟨a, b, hab⟩ := hsup x
    exact ⟨(a, b), hab.symm⟩
  let f : P6 ≃ₗ[ZMod 2] E := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  have hf : ∀ p, f p = Ψ p := fun p => rfl
  refine modIso_of_gens f (fun g p => ?_) (fun p => ?_)
  · obtain ⟨a, b⟩ := p
    rw [repP_sIncl]
    show f (repV g a, repDual g b) = ρ (sIncl g) (f (a, b))
    rw [hf, hf, hΨ, hΨ, map_add, hφ g a, rep_conj_tGen ρ g]
    change ρ (sIncl g) (φ a) + ρ tGen (φ (repV (tauHom g) b)) = _
    rw [hφ (tauHom g) b]
  · obtain ⟨a, b⟩ := p
    rw [repP_tGen]
    show f (b, a) = ρ tGen (f (a, b))
    rw [hf, hf, hΨ, hΨ, map_add, rep_tGen_sq, add_comm]

theorem caseII_trivial_false (hρ : IsIrrRep ρ) (D : Submodule (ZMod 2) E) (hD0 : D ≠ ⊥)
    (hDS : ∀ g, ∀ d ∈ D, ρ (sIncl g) d = d)
    (hinf : D ⊓ D.map (ρ tGen : E →ₗ[ZMod 2] E) = ⊥) : False := by
  obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff D).1 hD0
  have hTd : ρ tGen d ∈ D.map (ρ tGen : E →ₗ[ZMod 2] E) := ⟨d, hd, rfl⟩
  have hx0 : d + ρ tGen d ≠ 0 := by
    intro h0
    have h1 : ρ tGen d = d := by
      calc ρ tGen d = d + (d + ρ tGen d) := by
            rw [← add_assoc, add_self_eq_zero_of_zmod_two, zero_add]
        _ = d := by rw [h0, add_zero]
    have hmem : d ∈ D ⊓ D.map (ρ tGen : E →ₗ[ZMod 2] E) := ⟨hd, h1 ▸ hTd⟩
    rw [hinf] at hmem
    exact hd0 (Submodule.mem_bot _ |>.1 hmem)
  have hSx : ∀ g, ρ (sIncl g) (d + ρ tGen d) = d + ρ tGen d := fun g => by
    rw [map_add, hDS g d hd, rep_conj_tGen ρ g, hDS (tauHom g) d hd]
  have hTx : ρ tGen (d + ρ tGen d) = d + ρ tGen d := by
    rw [map_add, rep_tGen_sq, add_comm]
  have hNinv : ∀ h, ∀ y ∈ Submodule.span (ZMod 2) {d + ρ tGen d}, ρ h y ∈
      Submodule.span (ZMod 2) {d + ρ tGen d} := by
    refine isInvRep_of_gens (fun g y hy => ?_) (fun y hy => ?_)
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_smul, hSx]
      exact hy
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_smul, hTx]
      exact hy
  rcases hρ.2.2 _ hNinv with h | h
  · have : d + ρ tGen d ∈ Submodule.span (ZMod 2) {d + ρ tGen d} :=
      Submodule.mem_span_singleton_self _
    rw [h] at this
    exact hx0 (Submodule.mem_bot _ |>.1 this)
  · have hdN : d ∈ Submodule.span (ZMod 2) {d + ρ tGen d} := by rw [h]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hdN
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul] at hc
      exact hd0 hc.symm
    · rw [one_smul] at hc
      have h2 : ρ tGen d = 0 := by
        have : d + ρ tGen d = d + 0 := by rw [hc, add_zero]
        exact add_left_cancel this
      exact hd0 ((ρ tGen).injective (h2.trans (map_zero _).symm))

theorem caseII_traceZero_false (hρ : IsIrrRep ρ) (φ : traceZero →ₗ[ZMod 2] E)
    (hφinj : Function.Injective φ) (hφ : ∀ g X, φ (repA g X) = ρ (sIncl g) (φ X))
    (hinf : ∀ X Y, φ X = ρ tGen (φ Y) → φ X = 0) : False := by
  let r : traceZero →ₗ[ZMod 2] E :=
    φ + ((ρ tGen : E →ₗ[ZMod 2] E).comp φ).comp (transQ : traceZero →ₗ[ZMod 2] traceZero)
  have hr : ∀ X, r X = φ X + ρ tGen (φ (transQ X)) := fun X => rfl
  have hRinv : ∀ h, ∀ y ∈ LinearMap.range r, ρ h y ∈ LinearMap.range r := by
    refine isInvRep_of_gens (fun g y hy => ?_) (fun y hy => ?_)
    · obtain ⟨X, rfl⟩ := hy
      refine ⟨repA g X, ?_⟩
      rw [hr (repA g X), hr X, map_add, ← hφ g X, rep_conj_tGen ρ g, ← hφ (tauHom g),
        repA_tau_apply]
    · obtain ⟨X, rfl⟩ := hy
      refine ⟨transQ X, ?_⟩
      rw [hr (transQ X), hr X, map_add, rep_tGen_sq, transQ_transQ, add_comm]
  have hnt : Nontrivial traceZero := isIrr_repA.1
  obtain ⟨X₀, hX₀⟩ := exists_ne (0 : traceZero)
  have hrz : ∀ X, r X = 0 → X = 0 := fun X hX => by
    rw [hr] at hX
    have h1 : φ X = ρ tGen (φ (transQ X)) := by
      calc φ X = φ X + (ρ tGen (φ (transQ X)) + ρ tGen (φ (transQ X))) := by
            rw [add_self_eq_zero_of_zmod_two, add_zero]
        _ = (φ X + ρ tGen (φ (transQ X))) + ρ tGen (φ (transQ X)) := by rw [add_assoc]
        _ = ρ tGen (φ (transQ X)) := by rw [hX, zero_add]
    exact hφinj ((hinf _ _ h1).trans (map_zero φ).symm)
  rcases hρ.2.2 _ hRinv with h | h
  · have : r X₀ ∈ LinearMap.range r := ⟨X₀, rfl⟩
    rw [h] at this
    exact hX₀ (hrz X₀ (Submodule.mem_bot _ |>.1 this))
  · have : φ X₀ ∈ LinearMap.range r := by rw [h]; trivial
    obtain ⟨Y, hY⟩ := this
    rw [hr] at hY
    have h2 : φ (X₀ + Y) = ρ tGen (φ (transQ Y)) := by
      rw [map_add, ← hY]
      calc φ Y + ρ tGen (φ (transQ Y)) + φ Y = ρ tGen (φ (transQ Y)) + (φ Y + φ Y) := by abel
        _ = ρ tGen (φ (transQ Y)) := by rw [add_self_eq_zero_of_zmod_two, add_zero]
    have h3 : φ (X₀ + Y) = 0 := hinf _ _ h2
    have h4 : X₀ + Y = 0 := hφinj (h3.trans (map_zero φ).symm)
    have h5 : ρ tGen (φ (transQ Y)) = 0 := by rw [← h2, h3]
    have h6 : transQ Y = 0 :=
      hφinj (((ρ tGen).injective (h5.trans (map_zero _).symm)).trans (map_zero φ).symm)
    have h7 : Y = 0 := by
      have := congrArg transQ h6
      rwa [transQ_transQ, map_zero] at this
    rw [h7, add_zero] at h4
    exact hX₀ h4

end CaseII

theorem irreducible_GL3_ext_classification {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] (ρ : H32 →* (E ≃ₗ[ZMod 2] E)) (hρ : IsIrrRep ρ) :
    ModIso repHTriv ρ ∨ ModIso repP ρ ∨ ModIso repQ ρ := by
  have hnt : Nontrivial E := hρ.1
  obtain ⟨D, hD0, hDinv, hDmin⟩ := exists_minimal_invRep (ρ.comp sIncl)
  let TD : Submodule (ZMod 2) E := D.map (ρ tGen : E →ₗ[ZMod 2] E)
  have hDS : ∀ g, ∀ x ∈ D, ρ (sIncl g) x ∈ D := hDinv
  have hTDS : ∀ g, ∀ x ∈ TD, ρ (sIncl g) x ∈ TD := by
    rintro g _ ⟨d, hd, rfl⟩
    refine ⟨ρ (sIncl (tauHom g)) d, hDS _ d hd, ?_⟩
    change ρ tGen (ρ (sIncl (tauHom g)) d) = ρ (sIncl g) (ρ tGen d)
    rw [rep_conj_tGen ρ g]
  have hTDT : ∀ x ∈ TD, ρ tGen x ∈ D := by
    rintro _ ⟨d, hd, rfl⟩
    change ρ tGen (ρ tGen d) ∈ D
    rw [rep_tGen_sq]
    exact hd
  have hDT : ∀ x ∈ D, ρ tGen x ∈ TD := fun x hx => ⟨x, hx, rfl⟩
  have hinfInv : ∀ h, ∀ x ∈ D ⊓ TD, ρ h x ∈ D ⊓ TD := by
    refine isInvRep_of_gens (fun g x hx => ⟨hDS g x hx.1, hTDS g x hx.2⟩) (fun x hx => ?_)
    exact ⟨hTDT x hx.2, hDT x hx.1⟩
  have hsupInv : ∀ h, ∀ x ∈ D ⊔ TD, ρ h x ∈ D ⊔ TD := by
    refine isInvRep_of_gens (fun g x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (hDS g y hy) (hTDS g z hz)
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add, add_comm]
      exact Submodule.add_mem_sup (hTDT z hz) (hDT y hy)
  have hsup : D ⊔ TD = ⊤ := by
    rcases hρ.2.2 _ hsupInv with h | h
    · exact absurd (eq_bot_iff.2 (h ▸ le_sup_left)) hD0
    · exact h
  rcases hρ.2.2 _ hinfInv with hinf | hinf
  swap
  ·
    have hDtop : D = ⊤ := eq_top_iff.2 (hinf ▸ inf_le_left)
    have hS : IsIrrRep (ρ.comp sIncl) := by
      refine isIrrRep_of hnt fun N hN => ?_
      by_cases hN0 : N = ⊥
      · exact Or.inl hN0
      · right
        rw [← hDtop]
        exact hDmin N (by rw [hDtop]; exact le_top) hN0 hN
    rcases caseI hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  ·
    refine Or.inr (Or.inl ?_)
    have hDirr : IsIrrRep (subRep (ρ.comp sIncl) D hDinv) :=
      isIrrRep_subRep_of_minimal _ D hD0 hDinv hDmin
    have hsubapply : ∀ g (x : D), ((subRep (ρ.comp sIncl) D hDinv g x : D) : E) =
        ρ (sIncl g) x := fun g x => rfl
    have hmemD : ∀ y ∈ D, ∃ x : D, (x : E) = y := fun y hy => ⟨⟨y, hy⟩, rfl⟩
    have hinf' : ∀ a b : E, a ∈ D → b ∈ D → a = ρ tGen b → a = 0 := fun a b ha hb hab => by
      have hmem : a ∈ D ⊓ TD := ⟨ha, hab ▸ hDT b hb⟩
      rw [hinf] at hmem
      exact (Submodule.mem_bot _).1 hmem
    rcases irreducible_binary_GL3_classification (subRep (ρ.comp sIncl) D hDinv) hDirr with
      h | h | h | h
    ·
      exfalso
      obtain ⟨φ, hφ⟩ := h
      refine caseII_trivial_false hρ D hD0 (fun g d hd => ?_) hinf
      obtain ⟨c, hc⟩ := φ.surjective ⟨d, hd⟩
      have h1 : φ c = ⟨d, hd⟩ := hc
      have h2 : φ c = subRep (ρ.comp sIncl) D hDinv g (φ c) := hφ g c
      rw [h1] at h2
      exact (congrArg Subtype.val h2).symm
    ·
      obtain ⟨φ, hφ⟩ := h
      refine modIso_repP_of_embedding ((D.subtype).comp φ.toLinearMap)
        (Subtype.val_injective.comp φ.injective) (fun g v => ?_) (fun a b hab => ?_)
        (fun x => ?_)
      · exact congrArg Subtype.val (hφ g v)
      · exact hinf' _ _ (φ a).2 (φ b).2 hab
      · have hx : x ∈ D ⊔ TD := by rw [hsup]; trivial
        obtain ⟨y, hy, z, ⟨d', hd', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
        obtain ⟨a, ha⟩ := φ.surjective ⟨y, hy⟩
        obtain ⟨b, hb⟩ := φ.surjective ⟨d', hd'⟩
        refine ⟨a, b, ?_⟩
        show y + ρ tGen d' = ((φ a : D) : E) + ρ tGen ((φ b : D) : E)
        rw [ha, hb]
    ·
      obtain ⟨φ, hφ⟩ := h
      refine modIso_repP_of_embedding ((ρ tGen : E →ₗ[ZMod 2] E).comp
        ((D.subtype).comp φ.toLinearMap))
        ((ρ tGen).injective.comp (Subtype.val_injective.comp φ.injective)) (fun g v => ?_)
        (fun a b hab => ?_) (fun x => ?_)
      · show ρ tGen ((φ (repV g v) : D) : E) = ρ (sIncl g) (ρ tGen ((φ v : D) : E))
        have h1 : repV g v = repDual (tauHom g) v := by
          change repV g v = repV (tauHom (tauHom g)) v
          rw [tauHom_tauHom]
        rw [h1, congrArg Subtype.val (hφ (tauHom g) v), rep_conj_tGen ρ g]
        rfl
      · have h1 : ρ tGen ((φ a : D) : E) = ((φ b : D) : E) := by
          have : ρ tGen ((φ a : D) : E) = ρ tGen (ρ tGen ((φ b : D) : E)) := hab
          rw [this, rep_tGen_sq]
        have h2 : ρ tGen ((φ a : D) : E) ∈ D := by rw [h1]; exact (φ b).2
        have h3 : ρ tGen ((φ a : D) : E) ∈ TD := ⟨_, (φ a).2, rfl⟩
        have hmem : ρ tGen ((φ a : D) : E) ∈ D ⊓ TD := ⟨h2, h3⟩
        rw [hinf] at hmem
        exact (Submodule.mem_bot _).1 hmem
      · have hx : x ∈ D ⊔ TD := by rw [hsup]; trivial
        obtain ⟨y, hy, z, ⟨d', hd', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
        obtain ⟨a, ha⟩ := φ.surjective ⟨d', hd'⟩
        obtain ⟨b, hb⟩ := φ.surjective ⟨y, hy⟩
        refine ⟨a, b, ?_⟩
        show y + ρ tGen d' = ρ tGen ((φ a : D) : E) + ρ tGen (ρ tGen ((φ b : D) : E))
        rw [ha, hb, rep_tGen_sq, add_comm]
    ·
      exfalso
      obtain ⟨φ, hφ⟩ := h
      exact caseII_traceZero_false hρ ((D.subtype).comp φ.toLinearMap)
        (Subtype.val_injective.comp φ.injective) (fun g X => congrArg Subtype.val (hφ g X))
        (fun a b hab => hinf' _ _ (φ a).2 (φ b).2 hab)

theorem card_eq_of_modIso_H {E E' : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    [AddCommMonoid E'] [Module (ZMod 2) E'] {ρ : H32 →* (E ≃ₗ[ZMod 2] E)}
    {ρ' : H32 →* (E' ≃ₗ[ZMod 2] E')} (h : ModIso ρ ρ') : Nat.card E = Nat.card E' := by
  obtain ⟨f, -⟩ := h
  exact Nat.card_congr f.toEquiv

theorem natCard_P6 : Nat.card P6 = 64 := by
  rw [Nat.card_prod, natCard_Vec3]

end CFSG.QuasithinUnique.Setup.Family