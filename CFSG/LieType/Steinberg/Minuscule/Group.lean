module

public import CFSG.LieType.Steinberg.Minuscule.RootOps
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

section SquareZero

variable {A : Type*} [Ring A] {X Y : A}

theorem one_add_mul_one_sub (h : X * X = 0) : (1 + X) * (1 - X) = 1 :=
  calc (1 + X) * (1 - X) = 1 - X * X := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

theorem one_sub_mul_one_add (h : X * X = 0) : (1 - X) * (1 + X) = 1 :=
  calc (1 - X) * (1 + X) = 1 - X * X := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

theorem commutator_one_add (hX : X * X = 0) (hY : Y * Y = 0) (h1 : X * Y * X = 0)
    (h2 : Y * X * Y = 0) : (1 + X) * (1 + Y) * (1 - X) * (1 - Y) = 1 + (X * Y - Y * X) := by
  have e : (1 + X) * (1 + Y) * (1 - X) * (1 - Y) = 1 + (X * Y - Y * X) +
      (X * X * Y - X * X - Y * Y + Y * X * Y - X * Y * X - X * Y * Y + X * Y * X * Y) := by
    noncomm_ring
  rw [e, hX, hY, h1, h2, mul_assoc X Y Y, hY]
  simp only [zero_mul, mul_zero, add_zero, sub_self]

end SquareZero

section Diagonal

variable {k : Type*} [Field k] {d : ℕ}

@[expose] def diagOp (f : Fin d → k) : Module.End k (Fin d →₀ k) :=
  Finsupp.linearCombination k fun a => f a • Finsupp.single a 1

theorem diagOp_single (f : Fin d → k) (a : Fin d) :
    diagOp f (Finsupp.single a 1) = f a • Finsupp.single a 1 := by
  simp [diagOp]

theorem diagOp_mul (f g : Fin d → k) : diagOp f * diagOp g = diagOp (f * g) :=
  ext_single fun a => by
    rw [Module.End.mul_apply, diagOp_single, map_smul, diagOp_single, smul_smul, diagOp_single,
      Pi.mul_apply, mul_comm]

theorem diagOp_one : diagOp (1 : Fin d → k) = 1 :=
  ext_single fun a => by rw [diagOp_single, Pi.one_apply, one_smul, Module.End.one_apply]

theorem diagOp_comm (f g : Fin d → k) : diagOp f * diagOp g = diagOp g * diagOp f := by
  rw [diagOp_mul, diagOp_mul, mul_comm]

theorem diagOp_injective : Function.Injective (diagOp : (Fin d → k) → Module.End k (Fin d →₀ k)) :=
  fun f g h => funext fun a => by
    have := congrArg (fun φ => φ (Finsupp.single a 1) a) h
    simpa [diagOp_single] using this

theorem diagOp_mul_of_isSignedMap {f : Module.End k (Fin d →₀ k)} {P : Fin d → Fin d → Prop}
    (hf : IsSignedMap f P) {μ μ' : Fin d → k} {c : k} (h : ∀ a b, P a b → μ' b = c * μ a) :
    diagOp μ' * f = c • (f * diagOp μ) :=
  ext_single fun a => by
    rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, diagOp_single, map_smul,
      smul_smul]
    rcases hf a with h0 | ⟨b, hb, hs | hs⟩ <;> rw [‹f _ = _›]
    · rw [map_zero, smul_zero]
    · rw [diagOp_single, h a b hb]
    · rw [map_neg, diagOp_single, h a b hb, smul_neg]

end Diagonal

namespace MinData

section HDiag

variable {τ : Tag} (D : MinData τ) (k : Type*) [Field k]

@[expose] def hDiag (i : Fin τ.rank) (t : kˣ) : Module.End k (Fin D.d →₀ k) :=
  diagOp fun a => ((t ^ D.wt a i : kˣ) : k)

theorem hDiag_single (i : Fin τ.rank) (t : kˣ) (a : Fin D.d) :
    D.hDiag k i t (Finsupp.single a 1) = ((t ^ D.wt a i : kˣ) : k) • Finsupp.single a 1 :=
  diagOp_single _ a

theorem hDiag_mul (i : Fin τ.rank) (s t : kˣ) :
    D.hDiag k i (s * t) = D.hDiag k i s * D.hDiag k i t := by
  rw [hDiag, hDiag, hDiag, diagOp_mul]
  congr 1
  ext a
  simp [mul_zpow]

end HDiag

namespace Valid

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]
include hV

@[expose] def xu (γ : Fin τ.rank → ℤ) (c : k) : (Module.End k (Fin D.d →₀ k))ˣ where
  val := 1 + c • D.rootOp k γ
  inv := 1 - c • D.rootOp k γ
  val_inv := one_add_mul_one_sub (by rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero])
  inv_val := one_sub_mul_one_add (by rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero])

theorem xu_val (γ : Fin τ.rank → ℤ) (c : k) :
    (hV.xu k γ c : Module.End k (Fin D.d →₀ k)) = 1 + c • D.rootOp k γ := rfl

theorem xu_apply (γ : Fin τ.rank → ℤ) (c : k) (v : Fin D.d →₀ k) :
    (hV.xu k γ c : Module.End k (Fin D.d →₀ k)) v = v + c • D.rootOp k γ v := rfl

theorem xu_add (γ : Fin τ.rank → ℤ) (c c' : k) :
    hV.xu k γ (c + c') = hV.xu k γ c * hV.xu k γ c' := by
  ext1
  simp only [Units.val_mul, xu_val]
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero,
    add_zero, add_smul]
  abel

theorem xu_zero (γ : Fin τ.rank → ℤ) : hV.xu k γ 0 = 1 := by
  ext1
  rw [xu_val, zero_smul, add_zero, Units.val_one]

theorem xu_of_not_isRoot {γ : Fin τ.rank → ℤ} (hγ : ¬ IsRoot τ γ) (c : k) : hV.xu k γ c = 1 := by
  ext1
  rw [xu_val, rootOp_eq_zero hγ, smul_zero, add_zero, Units.val_one]

@[expose] def minGroup : Subgroup (Module.End k (Fin D.d →₀ k))ˣ :=
  Subgroup.closure {g | ∃ γ, IsRoot τ γ ∧ ∃ c, g = hV.xu k γ c}

abbrev endo (g : hV.minGroup k) : Module.End k (Fin D.d →₀ k) :=
  ((g : (Module.End k (Fin D.d →₀ k))ˣ) : Module.End k (Fin D.d →₀ k))

theorem endo_mul (g h : hV.minGroup k) : hV.endo k (g * h) = hV.endo k g * hV.endo k h := rfl

theorem endo_one : hV.endo k 1 = 1 := rfl

theorem endo_inv_mul (g : hV.minGroup k) : hV.endo k g⁻¹ * hV.endo k g = 1 :=
  Units.inv_mul (g : (Module.End k (Fin D.d →₀ k))ˣ)

theorem endo_mul_inv (g : hV.minGroup k) : hV.endo k g * hV.endo k g⁻¹ = 1 :=
  Units.mul_inv (g : (Module.End k (Fin D.d →₀ k))ˣ)

theorem endo_injective : Function.Injective (hV.endo k) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem endo_inv_eq {g : hV.minGroup k} {f : Module.End k (Fin D.d →₀ k)}
    (h : hV.endo k g * f = 1) : hV.endo k g⁻¹ = f := by
  calc hV.endo k g⁻¹ = hV.endo k g⁻¹ * (hV.endo k g * f) := by rw [h, mul_one]
    _ = f := by rw [← mul_assoc, endo_inv_mul, one_mul]

theorem xu_mem (γ : Fin τ.rank → ℤ) (c : k) : hV.xu k γ c ∈ hV.minGroup k := by
  by_cases hγ : IsRoot τ γ
  · exact Subgroup.subset_closure ⟨γ, hγ, c, rfl⟩
  · rw [hV.xu_of_not_isRoot k hγ]
    exact one_mem _

@[expose] def xm (γ : Fin τ.rank → ℤ) (c : k) : hV.minGroup k := ⟨hV.xu k γ c, hV.xu_mem k γ c⟩

theorem endo_xm (γ : Fin τ.rank → ℤ) (c : k) : hV.endo k (hV.xm k γ c) = 1 + c • D.rootOp k γ :=
  rfl

theorem xm_add (γ : Fin τ.rank → ℤ) (c c' : k) :
    hV.xm k γ (c + c') = hV.xm k γ c * hV.xm k γ c' :=
  Subtype.ext (hV.xu_add k γ c c')

theorem xm_zero (γ : Fin τ.rank → ℤ) : hV.xm k γ 0 = 1 := Subtype.ext (hV.xu_zero k γ)

theorem xm_neg (γ : Fin τ.rank → ℤ) (c : k) : (hV.xm k γ c)⁻¹ = hV.xm k γ (-c) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← xm_add, neg_add_cancel, xm_zero]

theorem xm_of_not_isRoot {γ : Fin τ.rank → ℤ} (hγ : ¬ IsRoot τ γ) (c : k) : hV.xm k γ c = 1 :=
  Subtype.ext (hV.xu_of_not_isRoot k hγ c)

theorem xm_injective {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : Function.Injective (hV.xm k γ) := by
  intro c c' h
  have h' := congrArg (hV.endo k) h
  rw [endo_xm, endo_xm, add_right_inj] at h'
  by_contra hne
  apply hV.rootOp_ne_zero (R := k) hγ
  have : (c - c') • D.rootOp k γ = 0 := by rw [sub_smul, h', sub_self]
  exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

@[expose] def xHom (γ : Fin τ.rank → ℤ) : Multiplicative k →* hV.minGroup k where
  toFun c := hV.xm k γ c.toAdd
  map_one' := hV.xm_zero k γ
  map_mul' _ _ := hV.xm_add k γ _ _

@[expose] def rootGroup (γ : Fin τ.rank → ℤ) : Subgroup (hV.minGroup k) := (hV.xHom k γ).range

theorem mem_rootGroup {γ : Fin τ.rank → ℤ} {g : hV.minGroup k} :
    g ∈ hV.rootGroup k γ ↔ ∃ c, hV.xm k γ c = g :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem xm_mem_rootGroup (γ : Fin τ.rank → ℤ) (c : k) : hV.xm k γ c ∈ hV.rootGroup k γ :=
  (hV.mem_rootGroup k).2 ⟨c, rfl⟩

theorem rootGroup_eq_bot {γ : Fin τ.rank → ℤ} (hγ : ¬ IsRoot τ γ) : hV.rootGroup k γ = ⊥ := by
  rw [eq_bot_iff]
  rintro g hg
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hg
  rw [hV.xm_of_not_isRoot k hγ, Subgroup.mem_bot]

theorem iSup_rootGroup : ⨆ γ ∈ {γ | IsRoot τ γ}, hV.rootGroup k γ = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  let T : Subgroup (Module.End k (Fin D.d →₀ k))ˣ :=
    (⨆ γ ∈ {γ | IsRoot τ γ}, hV.rootGroup k γ).map (hV.minGroup k).subtype
  have hle : hV.minGroup k ≤ T := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    exact ⟨hV.xm k γ c, Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ
      (hV.xm_mem_rootGroup k γ c)), rfl⟩
  obtain ⟨g', hg', rfl⟩ := hle hg
  exact hg'

theorem endo_xm_inv (γ : Fin τ.rank → ℤ) (c : k) :
    hV.endo k (hV.xm k γ c)⁻¹ = 1 - c • D.rootOp k γ := by
  rw [xm_neg, endo_xm, neg_smul, ← sub_eq_add_neg]

theorem endo_commutator (γ δ : Fin τ.rank → ℤ) (c d : k) :
    hV.endo k ⁅hV.xm k γ c, hV.xm k δ d⁆ = (1 + c • D.rootOp k γ) * (1 + d • D.rootOp k δ) *
      (1 - c • D.rootOp k γ) * (1 - d • D.rootOp k δ) := by
  rw [commutatorElement_def, endo_mul, endo_mul, endo_mul, endo_xm, endo_xm, endo_xm_inv,
    endo_xm_inv]

theorem commutator_xm {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hne : γ + δ ≠ 0) :
    (IsRoot τ (γ + δ) → ∃ σ : k, IsSign σ ∧
      ∀ c d : k, ⁅hV.xm k γ c, hV.xm k δ d⁆ = hV.xm k (γ + δ) (σ * c * d)) ∧
    (¬ IsRoot τ (γ + δ) → ∀ c d : k, ⁅hV.xm k γ c, hV.xm k δ d⁆ = 1) := by
  obtain ⟨hroot, hcomm⟩ := hV.pairRel (R := k) hγ hδ hne
  have hX : ∀ c : k, (c • D.rootOp k γ) * (c • D.rootOp k γ) = 0 := fun c => by
    rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero]
  have hY : ∀ d : k, (d • D.rootOp k δ) * (d • D.rootOp k δ) = 0 := fun d => by
    rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero]
  refine ⟨fun hr => ?_, fun hnr c d => ?_⟩
  · obtain ⟨⟨σ, hσ, hc⟩, h1, h2⟩ := hroot hr
    refine ⟨σ, hσ, fun c d => hV.endo_injective k ?_⟩
    rw [endo_commutator, commutator_one_add (hX c) (hY d), endo_xm, smul_mul_smul_comm,
      smul_mul_smul_comm, mul_comm d c, ← smul_sub, hc, smul_smul, mul_comm (c * d), mul_assoc]
    · rw [smul_mul_smul_comm, smul_mul_smul_comm, h1, smul_zero]
    · rw [smul_mul_smul_comm, smul_mul_smul_comm, h2, smul_zero]
  · have h := hcomm hnr
    refine hV.endo_injective k ?_
    have h1 : (c • D.rootOp k γ) * (d • D.rootOp k δ) * (c • D.rootOp k γ) = 0 := by
      rw [smul_mul_smul_comm, smul_mul_smul_comm, h, mul_assoc (D.rootOp k δ),
        hV.rootOp_mul_self, mul_zero, smul_zero]
    have h2 : (d • D.rootOp k δ) * (c • D.rootOp k γ) * (d • D.rootOp k δ) = 0 := by
      rw [smul_mul_smul_comm, smul_mul_smul_comm, ← h, mul_assoc (D.rootOp k γ),
        hV.rootOp_mul_self, mul_zero, smul_zero]
    rw [endo_commutator, commutator_one_add (hX c) (hY d) h1 h2, smul_mul_smul_comm,
      smul_mul_smul_comm, h, mul_comm c d, sub_self, add_zero, endo_one]

@[expose] def nt (i : Fin τ.rank) (t : kˣ) : hV.minGroup k :=
  hV.xm k (Pi.single i 1) t * hV.xm k (-Pi.single i 1) (-((t⁻¹ : kˣ) : k)) *
    hV.xm k (Pi.single i 1) t

@[expose] def nm (i : Fin τ.rank) : hV.minGroup k := hV.nt k i 1

theorem endo_nt_single (i : Fin τ.rank) (t : kˣ) (a : Fin D.d) :
    hV.endo k (hV.nt k i t) (Finsupp.single a 1) =
      if D.wt a i = -1 then (t : k) • Finsupp.single (hV.sRefl i a) 1
      else if D.wt a i = 1 then -((t⁻¹ : kˣ) : k) • Finsupp.single (hV.sRefl i a) 1
      else Finsupp.single a 1 := by
  have hs := hV.wt_sRefl_self i a
  have hss := hV.sRefl_sRefl i a
  have hti : ((t⁻¹ : kˣ) : k) * t = 1 := Units.inv_mul t
  have hti' : (t : k) * ((t⁻¹ : kˣ) : k) = 1 := Units.mul_inv t
  rcases hV.wt_mem a i with h | h | h <;>
    simp only [nt, endo_mul, endo_xm, Module.End.mul_apply, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.smul_apply, map_add, map_smul, hV.rootOp_single_apply,
      hV.rootOp_neg_single_apply, hs, hss, h, smul_add, smul_smul, ite_true, neg_neg, neg_mul,
      mul_neg, hti, hti'] <;>
    norm_num

theorem endo_nm (i : Fin τ.rank) : hV.endo k (hV.nm k i) = D.nOp k i :=
  ext_single fun a => by
    rw [nm, endo_nt_single]
    rcases hV.wt_mem a i with h | h | h
    · rw [ite_eq_left h, hV.nOp_single_of_eq_neg_one h, Units.val_one, one_smul]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hV.nOp_single_of_eq_zero h]
    · rw [ite_eq_right (by omega), ite_eq_left h, hV.nOp_single_of_eq_one h, inv_one,
        Units.val_one, neg_one_smul]

theorem endo_nm_inv (i : Fin τ.rank) : hV.endo k (hV.nm k i)⁻¹ = D.nInv k i :=
  hV.endo_inv_eq k (by rw [endo_nm, hV.nOp_mul_nInv])

theorem nm_conj_xm {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (i : Fin τ.rank) :
    ∃ σ : k, IsSign σ ∧ ∀ c : k,
      hV.nm k i * hV.xm k γ c * (hV.nm k i)⁻¹ = hV.xm k (reflect τ i γ) (σ * c) := by
  obtain ⟨σ, hσ, h⟩ := hV.conj_rootOp (R := k) hγ i
  refine ⟨σ, hσ, fun c => hV.endo_injective k ?_⟩
  rw [endo_mul, endo_mul, endo_nm, endo_nm_inv, endo_xm, endo_xm, mul_add, add_mul, mul_one,
    hV.nOp_mul_nInv, mul_smul_comm, smul_mul_assoc, h, smul_smul, mul_comm c]

theorem nm_comm {i j : Fin τ.rank} (hij : i ≠ j) (h : τ.cartan i j = 0) :
    hV.nm k i * hV.nm k j = hV.nm k j * hV.nm k i :=
  hV.endo_injective k (by rw [endo_mul, endo_mul, endo_nm, endo_nm, hV.nOp_comm hij h])

theorem nm_braid {i j : Fin τ.rank} (hij : i ≠ j) (h : τ.cartan i j ≠ 0) :
    hV.nm k i * hV.nm k j * hV.nm k i = hV.nm k j * hV.nm k i * hV.nm k j :=
  hV.endo_injective k (by
    rw [endo_mul, endo_mul, endo_mul, endo_mul, endo_nm, endo_nm, hV.nOp_braid hij h])

@[expose] def hm (i : Fin τ.rank) (t : kˣ) : hV.minGroup k := hV.nt k i t * (hV.nt k i 1)⁻¹

theorem endo_nt_eq (i : Fin τ.rank) (t : kˣ) :
    hV.endo k (hV.nt k i t) = D.hDiag k i t * hV.endo k (hV.nt k i 1) :=
  ext_single fun a => by
    rw [Module.End.mul_apply, endo_nt_single, endo_nt_single, hDiag]
    have hs := hV.wt_sRefl_self i a
    rcases hV.wt_mem a i with h | h | h
    · rw [ite_eq_left h, ite_eq_left h, Units.val_one, one_smul, diagOp_single, hs, h]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), diagOp_single, h, zpow_zero, Units.val_one, one_smul]
    · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right (by omega), ite_eq_left h,
        inv_one, Units.val_one, map_smul, diagOp_single, hs, h, smul_smul]
      simp

theorem endo_hm (i : Fin τ.rank) (t : kˣ) : hV.endo k (hV.hm k i t) = D.hDiag k i t := by
  rw [hm, endo_mul, endo_nt_eq, mul_assoc, endo_mul_inv, mul_one]

theorem hm_mul (i : Fin τ.rank) (s t : kˣ) : hV.hm k i (s * t) = hV.hm k i s * hV.hm k i t :=
  hV.endo_injective k (by rw [endo_mul, endo_hm, endo_hm, endo_hm, D.hDiag_mul])

theorem hm_one (i : Fin τ.rank) : hV.hm k i 1 = 1 := by rw [hm, mul_inv_cancel]

@[expose] def hHom (i : Fin τ.rank) : kˣ →* hV.minGroup k where
  toFun := hV.hm k i
  map_one' := hV.hm_one k i
  map_mul' := hV.hm_mul k i

@[expose] def torus (i : Fin τ.rank) : Subgroup (hV.minGroup k) := (hV.hHom k i).range

theorem mem_torus {i : Fin τ.rank} {g : hV.minGroup k} : g ∈ hV.torus k i ↔ ∃ t, hV.hm k i t = g :=
  Iff.rfl

theorem hm_mem_torus (i : Fin τ.rank) (t : kˣ) : hV.hm k i t ∈ hV.torus k i := ⟨t, rfl⟩

theorem nt_eq_hm_mul (i : Fin τ.rank) (t : kˣ) : hV.nt k i t = hV.hm k i t * hV.nm k i := by
  rw [hm, nm, inv_mul_cancel_right]

theorem hDiag_mul_rootOp {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : Fin τ.rank) (t : kˣ) :
    D.hDiag k j t * D.rootOp k γ =
      ((t ^ toWeight γ j : kˣ) : k) • (D.rootOp k γ * D.hDiag k j t) := by
  unfold hDiag
  refine diagOp_mul_of_isSignedMap (hV.isSignedMap_rootOp hγ) fun a b h => ?_
  rw [h, Pi.add_apply, zpow_add, Units.val_mul, mul_comm]

theorem hm_conj_xm {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : Fin τ.rank) (t : kˣ) (c : k) :
    hV.hm k j t * hV.xm k γ c * (hV.hm k j t)⁻¹ =
      hV.xm k γ (((t ^ toWeight γ j : kˣ) : k) * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine hV.endo_injective k ?_
  rw [endo_mul, endo_mul, endo_hm, endo_xm, endo_xm, mul_add, add_mul, mul_one, one_mul,
    mul_smul_comm, hV.hDiag_mul_rootOp k hγ, smul_smul, smul_mul_assoc, mul_comm c]

theorem nm_conj_hm (j l : Fin τ.rank) (t : kˣ) :
    hV.nm k j * hV.hm k l t * (hV.nm k j)⁻¹ = hV.hm k l t * hV.hm k j (t ^ (-τ.cartan l j)) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine hV.endo_injective k ?_
  rw [endo_mul, endo_mul, endo_mul, endo_nm, endo_hm, endo_hm]
  unfold hDiag
  rw [diagOp_mul]
  refine ((diagOp_mul_of_isSignedMap (hV.isSignedMap_nOp (R := k) j) (c := 1)
    (μ := fun a => ((t ^ D.wt a l : kˣ) : k)) fun a b h => ?_).trans (one_smul _ _)).symm
  rw [h, Pi.mul_apply, hV.wt_sRefl, one_mul, ← Units.val_mul, reflectWeight]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toWeight_single, Tag.cartan_self]
  rw [← zpow_mul, ← zpow_add]
  congr 2
  ring

theorem nm_sq (i : Fin τ.rank) : hV.nm k i ^ 2 = hV.hm k i (-1) := by
  refine hV.endo_injective k (ext_single fun a => ?_)
  rw [pow_two, endo_mul, endo_hm, endo_nm, Module.End.mul_apply, hDiag, diagOp_single]
  have hs := hV.wt_sRefl_self i a
  have hss := hV.sRefl_sRefl i a
  rcases hV.wt_mem a i with h | h | h
  · rw [hV.nOp_single_of_eq_neg_one h, hV.nOp_single_of_eq_one (by omega), hss, h]
    simp
  · rw [hV.nOp_single_of_eq_zero h, hV.nOp_single_of_eq_zero h, h]
    simp
  · rw [hV.nOp_single_of_eq_one h, map_neg, hV.nOp_single_of_eq_neg_one (by omega), hss, h]
    simp

end Valid

end MinData

end CFSG.LieType.Steinberg.Minuscule
