module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364C3
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364Mat
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34L364

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Dickson.Sec6
open scoped commutatorElement

theorem commutator_self_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem exists_perfect_lift {Y Q : Type*} [Group Y] [Group Q] (π : Y →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y) (α : MulAut Y)
    (β : MulAut Q) (hαβ : ∀ y, π (α y) = β (π y)) {A : Subgroup Q} (hA : A ≤ fixSubgroup β)
    (hperf : ⁅A, A⁆ = A) :
    ∃ D : Subgroup Y, D ≤ fixSubgroup α ∧ ⁅D, D⁆ = D ∧ D.map π = A := by
  have hAle : A ≤ (fixSubgroup α).map π :=
    le_map_fixSubgroup_of_perfect π hker α β hαβ hπ hA hperf
  set C : Subgroup Y := fixSubgroup α ⊓ A.comap π with hC
  have hCA : C.map π = A := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := hAle ha
      exact ⟨x, ⟨hx, ha⟩, rfl⟩
  set D : Subgroup Y := ⁅C, C⁆ with hD
  have hDC : D ≤ C := commutator_self_le C
  have hDA : D.map π = A := by rw [hD, Subgroup.map_commutator, hCA, hperf]
  refine ⟨D, hDC.trans inf_le_left, le_antisymm (commutator_self_le D) ?_, hDA⟩
  have key : ∀ x ∈ C, ∃ d ∈ D, ∃ z ∈ Subgroup.center Y, x = d * z := by
    intro x hx
    have hx' : π x ∈ D.map π := by
      rw [hDA, ← hCA]
      exact ⟨x, hx, rfl⟩
    obtain ⟨d, hd, hdx⟩ := hx'
    refine ⟨d, hd, d⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
  show ⁅C, C⁆ ≤ ⁅D, D⁆
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := key x hx
  obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := key y hy
  rw [commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 hz₁ d₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₂ d₁))]
  exact Subgroup.commutator_mem_commutator hd₁ hd₂

theorem isCyclic_of_image {D B : Type*} [Group D] [Finite D] [Group B] (f : D →* B)
    (hf : Function.Surjective f) (hcyc : ∀ R : Subgroup D, IsPGroup 3 R → IsCyclic R)
    {E : Subgroup B} (hE : IsPGroup 3 E) : IsCyclic E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite B := Finite.of_surjective f hf
  obtain ⟨R, hER⟩ := hE.exists_le_sylow
  obtain ⟨R₀, hR₀⟩ := Sylow.mapSurjective_surjective hf 3 R
  have hcyc₀ : IsCyclic (R₀ : Subgroup D) := hcyc _ R₀.isPGroup'
  have hmap : (R₀ : Subgroup D).map f = (R : Subgroup B) := by
    have := congrArg (fun P : Sylow 3 B => (P : Subgroup B)) hR₀
    simpa using this
  have hRcyc : IsCyclic (R : Subgroup B) := by
    rw [← hmap]
    exact isCyclic_of_surjective (f.subgroupMap (R₀ : Subgroup D))
      (f.subgroupMap_surjective (R₀ : Subgroup D))
  exact Subgroup.isCyclic_of_le hER

theorem pow_apply_intertwine {Y Q : Type*} [Group Y] [Group Q] (π : Y →* Q) (α : MulAut Y)
    (β : MulAut Q) (h : ∀ y, π (α y) = β (π y)) (n : ℕ) (y : Y) :
    π ((α ^ n) y) = (β ^ n) (π y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, h]

theorem l364_core {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (φ : MulAut (StatedProj (StatedSL 3 K))) (hφ : IsConjByGL (StatedSL 3 K) φ)
    (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1) {A : Subgroup (StatedProj (StatedSL 3 K))}
    (hA : GLAPComponent 3 (fixSubgroup φ) A)
    (h34 : IsLThreeFour (↥A ⧸ GLAPPrimeCore 3 ↥A)) : False := by
  classical
  obtain ⟨g, -, hgφ⟩ := hφ
  haveI hSLn : (StatedSL 3 K).Normal := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
    infer_instance
  let π₀ : ↥(StatedSL 3 K) →* StatedProj (StatedSL 3 K) := QuotientGroup.mk' _
  let Φ : MulAut ↥(StatedSL 3 K) := MulAut.conjNormal g
  have hΦ : ∀ x : ↥(StatedSL 3 K), π₀ (Φ x) = φ (π₀ x) := by
    intro x
    exact (hgφ x (Φ x) (MulAut.conjNormal_apply g x)).symm
  have hker : π₀.ker ≤ Subgroup.center ↥(StatedSL 3 K) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hπ : Function.Surjective π₀ := QuotientGroup.mk'_surjective _
  have hAfix : A ≤ fixSubgroup φ := hA.1
  have hperf : ⁅A, A⁆ = A := glaPComponent_perfect hA
  obtain ⟨D, hDfix, hDperf, hDA⟩ := exists_perfect_lift π₀ hπ hker Φ φ hΦ hAfix hperf
  obtain ⟨h3, -⟩ := Up34Lin.exists_omega hK
  have hg3 : ∃ c : Kˣ, g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    apply Up34Mat.exists_scalar_of_conj_scalar h3 (g ^ 3)
    intro x hx
    let xs : ↥(StatedSL 3 K) := ⟨x, CFSG.Open.StatedAPI.mem_statedSL_of_det hx⟩
    have e3 := pow_apply_intertwine π₀ Φ φ hΦ 3 xs
    rw [hφ3, MulAut.one_apply] at e3
    have hΦ3 : (((Φ ^ 3) xs : ↥(StatedSL 3 K)) : GL (Fin 3) K) = g ^ 3 * x * (g ^ 3)⁻¹ := by
      have : Φ ^ 3 = MulAut.conjNormal (g ^ 3) := (map_pow MulAut.conjNormal g 3).symm
      rw [this, MulAut.conjNormal_apply]
    obtain ⟨u, hu⟩ := Up34C3.scalar_of_mk_eq (a := xs) (b := (Φ ^ 3) xs) e3.symm
    exact ⟨u, by rw [← hΦ3]; exact hu⟩
  have hgns : ∀ a : Kˣ, g ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) a := by
    intro a ha
    apply hφ1
    refine MulEquiv.ext fun p => ?_
    obtain ⟨x, rfl⟩ := hπ p
    have hx : Φ x = x := by
      apply Subtype.ext
      show (MulAut.conjNormal g x : GL (Fin 3) K) = x
      rw [MulAut.conjNormal_apply, ha, Up34C3.scalar_comm, mul_assoc, mul_inv_cancel, mul_one]
    rw [MulAut.one_apply, ← hΦ x, hx]
  obtain ⟨c, hc⟩ := hg3
  have hD' : ⁅D.map (StatedSL 3 K).subtype, D.map (StatedSL 3 K).subtype⁆ =
      D.map (StatedSL 3 K).subtype := by
    rw [← Subgroup.map_commutator, hDperf]
  have hDg : ∀ d ∈ D.map (StatedSL 3 K).subtype, d * g = g * d := by
    rintro _ ⟨d, hd, rfl⟩
    have h1 : Φ d = d := hDfix hd
    have h2 := congrArg (fun z : ↥(StatedSL 3 K) => (z : GL (Fin 3) K)) h1
    have h3' : g * (d : GL (Fin 3) K) * g⁻¹ = d := by
      have := h2
      simpa [Φ, MulAut.conjNormal_apply] using this
    exact (mul_inv_eq_iff_eq_mul.1 h3').symm
  have hcyc : ∀ R : Subgroup ↥D, IsPGroup 3 R → IsCyclic R := by
    intro R hR
    let ι : ↥R →* GL (Fin 3) K := (StatedSL 3 K).subtype.comp (D.subtype.comp R.subtype)
    refine Up34Mat.isCyclic_of_three_subgroup_gl hK g c hc hgns hD' hDg ι ?_ ?_ hR
    · intro a b hab
      exact Subtype.ext (Subtype.ext (Subtype.ext hab))
    · intro r
      exact ⟨D.subtype (R.subtype r), (R.subtype r).2, rfl⟩
  have hDA' : ∀ d : ↥D, π₀ (d : ↥(StatedSL 3 K)) ∈ A := by
    intro d
    rw [← hDA]
    exact ⟨d, d.2, rfl⟩
  let f₁ : ↥D →* ↥A := (π₀.comp D.subtype).codRestrict A hDA'
  let f : ↥D →* (↥A ⧸ GLAPPrimeCore 3 ↥A) := (QuotientGroup.mk' _).comp f₁
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥A) y
    have ha : (a : StatedProj (StatedSL 3 K)) ∈ D.map π₀ := by
      rw [hDA]
      exact a.2
    obtain ⟨d, hd, hda⟩ := ha
    refine ⟨⟨d, hd⟩, ?_⟩
    show QuotientGroup.mk' _ (f₁ ⟨d, hd⟩) = QuotientGroup.mk' _ a
    congr 1
    exact Subtype.ext hda
  obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := h34
  have hF3 : Nat.card F % 3 = 1 := by rw [hF4]
  obtain ⟨-, ω, hω3, hω1, -⟩ := Up34Lin.exists_omega hF3
  obtain ⟨E₀, hE₀p, hE₀nc⟩ := Up34C3.exists_noncyclic_three_subgroup hω3 hω1
  have hEp : IsPGroup 3 (E₀.map e.symm.toMonoidHom) := hE₀p.map _
  have hEc := isCyclic_of_image f hf hcyc hEp
  exact hE₀nc ((MulEquiv.isCyclic
    (Subgroup.equivMapOfInjective E₀ e.symm.toMonoidHom e.symm.injective)).2 hEc)

end CFSG.HardMathSupport.Dickson.Sec6.Up34L364
