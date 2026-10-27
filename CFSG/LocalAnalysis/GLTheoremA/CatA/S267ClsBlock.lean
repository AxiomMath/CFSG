module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAssemble
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFam
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}

section Normalize

variable {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} {U W : Submodule K (ι → K)}

theorem conj_mem_blkSub {g : GL ι K} (hg : g ∈ isomGL β) (hgU : ∀ u ∈ U, glEquiv g u ∈ U)
    (hgW : ∀ w ∈ W, glEquiv g w ∈ W) {h : GL ι K} (hh : h ∈ blkSub β U W) :
    g * h * g⁻¹ ∈ blkSub β U W := by
  obtain ⟨hhβ, hhU, hhW⟩ := hh
  refine ⟨(isomGL β).mul_mem ((isomGL β).mul_mem hg hhβ) ((isomGL β).inv_mem hg), fun u hu => ?_,
    fun w hw => ?_⟩
  · rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hgU _ (hhU _ (symm_mem_of_forall_mem (glEquiv g) hgU hu))
  · rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hw' : (glEquiv g)⁻¹ w ∈ W := symm_mem_of_forall_mem (glEquiv g) hgW hw
    rw [hhW _ hw']
    show glEquiv g ((glEquiv g).symm w) = w
    exact (glEquiv g).apply_symm_apply w

theorem conj_mem_blkI {g : GL ι K} (hg : g ∈ isomGL β) (hgU : ∀ u ∈ U, glEquiv g u ∈ U)
    (hgW : ∀ w ∈ W, glEquiv g w ∈ W) {h : GL ι K} (hh : h ∈ blkI β U W) :
    g * h * g⁻¹ ∈ blkI β U W := by
  have hle : (blkSub β U W).map (MulAut.conj g).toMonoidHom ≤ blkSub β U W := by
    rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_blkSub hg hgU hgW hk
  have h1 : (blkI β U W).map (MulAut.conj g).toMonoidHom ≤ blkI β U W := by
    rw [blkI, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 ⟨h, hh, rfl⟩


theorem semiConj_mem_blkSub [Finite K] {A : GL ι K} {σ : K ≃+* K}
    (hform : ModelGen.FormRel β A σ) (haU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    (haW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W) {h : GL ι K} (hh : h ∈ blkSub β U W) :
    ModelGen.semiConj A σ h ∈ blkSub β U W := by
  obtain ⟨hhβ, hhU, hhW⟩ := hh
  set a := ModelGen.semiMap A σ with ha
  have hsymm : ∀ X : Submodule K (ι → K), (∀ x ∈ X, a x ∈ X) → ∀ x ∈ X, a.symm x ∈ X := by
    intro X hX x hx
    let f : ↥X → ↥X := fun y => ⟨a y, hX y y.2⟩
    have hf : Function.Injective f := fun y y' hyy =>
      Subtype.ext (a.injective (congrArg Subtype.val hyy))
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x, hx⟩
    have hyx : a y = x := congrArg Subtype.val hy
    rw [← hyx, a.symm_apply_apply]
    exact y.2
  have hconj : ∀ v, glEquiv (ModelGen.semiConj A σ h) v = a (glEquiv h (a.symm v)) := by
    intro v
    have := ModelGen.glEquiv_semiConj_apply A σ h (a.symm v)
    rwa [a.apply_symm_apply] at this
  obtain ⟨c, hc⟩ := hform
  have key : ∀ u v, β (a u) (a v) = (c : K)⁻¹ * σ ((c : K) * β u v) := by
    intro u v
    rw [← hc u v, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero c), one_mul]
  refine ⟨?_, fun u hu => ?_, fun w hw => ?_⟩
  · rw [mem_isomGL]
    intro x y
    rw [← glEquiv_apply, ← glEquiv_apply, hconj, hconj, key,
      show β (glEquiv h (a.symm x)) (glEquiv h (a.symm y)) = β (a.symm x) (a.symm y) by
        rw [glEquiv_apply, glEquiv_apply]
        exact mem_isomGL.mp hhβ _ _,
      ← key, a.apply_symm_apply, a.apply_symm_apply]
  · rw [hconj]
    exact haU _ (hhU _ (hsymm U haU u hu))
  · rw [hconj, hhW _ (hsymm W haW w hw), a.apply_symm_apply]

theorem semiConj_mem_blkI [Finite K] {A : GL ι K} {σ : K ≃+* K}
    (hform : ModelGen.FormRel β A σ) (haU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    (haW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W) {h : GL ι K} (hh : h ∈ blkI β U W) :
    ModelGen.semiConj A σ h ∈ blkI β U W := by
  have hle : (blkSub β U W).map (ModelGen.semiConj A σ).toMonoidHom ≤ blkSub β U W := by
    rintro _ ⟨k, hk, rfl⟩
    exact semiConj_mem_blkSub hform haU haW hk
  have h1 : (blkI β U W).map (ModelGen.semiConj A σ).toMonoidHom ≤ blkI β U W := by
    rw [blkI, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 ⟨h, hh, rfl⟩

theorem semiConj_pow_mem_blkI [Finite K] {A : GL ι K} {σ : K ≃+* K}
    (hform : ModelGen.FormRel β A σ) (haU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    (haW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W) (n : ℕ) {h : GL ι K} (hh : h ∈ blkI β U W) :
    (ModelGen.semiConj A σ ^ n) h ∈ blkI β U W := by
  induction n with
  | zero => exact hh
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact semiConj_mem_blkI hform haU haW ih

theorem comm_of_scalar_of_block (hUW : IsCompl U W) {y j : GL ι K} {c : K}
    (hy : ∀ u ∈ U, glEquiv y u = c • u) (hyW : ∀ w ∈ W, glEquiv y w ∈ W)
    (hjU : ∀ u ∈ U, glEquiv j u ∈ U) (hjW : ∀ w ∈ W, glEquiv j w = w) : y * j = j * y := by
  apply glEquiv.injective
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ U ⊔ W := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 : glEquiv (y * j) (u + w) = c • glEquiv j u + glEquiv y w := by
    rw [map_mul, LinearEquiv.mul_apply, map_add, hjW w hw, map_add, hy _ (hjU u hu)]
  have e2 : glEquiv (j * y) (u + w) = c • glEquiv j u + glEquiv y w := by
    rw [map_mul, LinearEquiv.mul_apply, map_add, hy u hu, map_add, map_smul,
      hjW _ (hyW w hw)]
  rw [e1, e2]

theorem comm_of_two_scalars (hUW : IsCompl U W) {z g : GL ι K} {ε₁ ε₂ : K}
    (hzU : ∀ u ∈ U, glEquiv z u = ε₁ • u) (hzW : ∀ w ∈ W, glEquiv z w = ε₂ • w)
    (hgU : ∀ u ∈ U, glEquiv g u ∈ U) (hgW : ∀ w ∈ W, glEquiv g w ∈ W) : g * z = z * g := by
  apply glEquiv.injective
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ U ⊔ W := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 : glEquiv (g * z) (u + w) = ε₁ • glEquiv g u + ε₂ • glEquiv g w := by
    rw [map_mul, LinearEquiv.mul_apply, map_add, hzU u hu, hzW w hw, map_add, map_smul,
      map_smul]
  have e2 : glEquiv (z * g) (u + w) = ε₁ • glEquiv g u + ε₂ • glEquiv g w := by
    rw [map_mul, LinearEquiv.mul_apply, map_add, map_add, hzU _ (hgU u hu), hzW _ (hgW w hw)]
  rw [e1, e2]

end Normalize

section Main

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem card_sup_zpowers_of_not_mem (hp : p.Prime) (hB : IsElemAbelian p B) {D : Subgroup Ω}
    (hDB : D ≤ B) {e : Ω} (heB : e ∈ B) (heD : e ∉ D) :
    Nat.card ↥(D ⊔ Subgroup.zpowers e) = Nat.card D * p := by
  have hcomm : ∀ x ∈ D, ∀ y ∈ Subgroup.zpowers e, x * y = y * x := fun x hx y hy =>
    hB.comm (hDB hx) (Subgroup.zpowers_le.mpr heB hy)
  have he1 : e ≠ 1 := fun h => heD (h ▸ D.one_mem)
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (Subgroup.zpowers e) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 e heB) he1]
  have hinf : D ⊓ Subgroup.zpowers e = ⊥ := by
    have hdvd : Nat.card ↥(D ⊓ Subgroup.zpowers e) ∣ p :=
      hcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : D ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcard])
      have hmem : e ∈ D ⊓ Subgroup.zpowers e := by rw [heq]; exact Subgroup.mem_zpowers e
      exact heD hmem.1
  rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, hcard]

theorem concA_of_block (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) [Finite K]
    {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} (Dat : ClsInner p S B H β)
    (hHβ : H ≤ isomGL β) {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (hIH : blkI β U W ≤ H) (hIq : CFSG.Open.IsQuasisimple ↥(blkI β U W))
    (hpI : p ∣ Nat.card ↥(blkI β U W)) {D : Subgroup Ω} (hDB : D ≤ innerPart S B)
    (hD : ∀ x : ↥(innerPart S B),
      (x : Ω) ∈ D ↔ ∃ c : K, ∀ u ∈ U, glEquiv (Dat.θ x : GL ι K) u = c • u)
    (hθU : ∀ x : ↥(innerPart S B), ∀ u ∈ U, glEquiv (Dat.θ x : GL ι K) u ∈ U)
    (hθW : ∀ x : ↥(innerPart S B), ∀ w ∈ W, glEquiv (Dat.θ x : GL ι K) w ∈ W)
    (hCpres : ∀ g ∈ H, (∀ x : ↥(innerPart S B), (x : Ω) ∈ D →
        g * (Dat.θ x : GL ι K) = Dat.θ x * g) →
      (∀ u ∈ U, glEquiv g u ∈ U) ∧ ∀ w ∈ W, glEquiv g w ∈ W)
    (hSchur : ∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
      ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u)
    (hfield : FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ →
      (∀ u ∈ U, ModelGen.semiMap Dat.A Dat.σ u ∈ U) ∧
      (∀ w ∈ W, ModelGen.semiMap Dat.A Dat.σ w ∈ W) ∧
      ∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ w ∈ W, glEquiv y w ∈ W) →
        ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj Dat.A Dat.σ ^ k) j * y⁻¹ = j)
    (hDc : p ^ 2 ≤ Nat.card D) (hDBc : p ^ 2 * Nat.card D ≤ Nat.card B)
    (hE : Nat.card D = p ^ 2 →
      (∃ x : ↥(innerPart S B), (x : Ω) ∉ D ∧
        GLAPLayer p (blkI β U W ⊓ Subgroup.centralizer {(Dat.θ x : GL ι K)}) ≠ ⊥) ∨
      (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ ∧
        GLAPLayer p (blkI β U W ⊓ centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}) ≠ ⊥))
    {z : GL ι K} (hzH : z ∈ H) (hz2 : z ^ 2 = 1) {ε₁ ε₂ : K} (hε : ε₁ ≠ ε₂)
    (hzU : ∀ u ∈ U, glEquiv z u = ε₁ • u) (hzW : ∀ w ∈ W, glEquiv z w = ε₂ • w)
    (hU0 : U ≠ ⊥) (hW0 : W ≠ ⊥) : S267ConcA p S B := by
  classical
  set I : Subgroup ↥H := (blkI β U W).subgroupOf H with hIdef
  have hmemI : ∀ j : ↥H, j ∈ I ↔ (j : GL ι K) ∈ blkI β U W := fun j => Subgroup.mem_subgroupOf
  let eI : ↥I ≃* ↥(blkI β U W) := Subgroup.subgroupOfEquivOfLe hIH
  have hIq' : CFSG.Open.IsQuasisimple ↥I := CFSG.Open.IsQuasisimple.of_mulEquiv eI hIq
  have hpI' : p ∣ Nat.card ↥I := by rw [Nat.card_congr eI.toEquiv]; exact hpI
  have hker : Dat.φ.ker ≤ Subgroup.center ↥H := by
    rw [Dat.ker_eq]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center H
  have hkerp : Nat.Coprime (Nat.card Dat.φ.ker) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr Dat.not_dvd).symm
  have hjU : ∀ j ∈ blkI β U W, ∀ u ∈ U, glEquiv j u ∈ U := fun j hj =>
    (blkI_le_blkSub β U W hj).2.1
  have hjW : ∀ j ∈ blkI β U W, ∀ w ∈ W, glEquiv j w = w := fun j hj =>
    (blkI_le_blkSub β U W hj).2.2
  have hθI : ∀ (x : ↥(innerPart S B)) (j : GL ι K), j ∈ blkI β U W →
      (Dat.θ x : GL ι K) * j * (Dat.θ x : GL ι K)⁻¹ ∈ blkI β U W := fun x j hj =>
    conj_mem_blkI (hHβ (Dat.θ x).2) (hθU x) (hθW x) hj
  obtain ⟨lift, hlift, hlift₁, hshape⟩ : ∃ lift : ↥B → MulAut ↥H,
      (∀ (x : ↥B) (h : ↥H), Dat.φ (lift x h) = (x : Ω) * Dat.φ h * (x : Ω)⁻¹) ∧
      (∀ (x : ↥B) (hx : (x : Ω) ∈ innerPart S B), lift x = MulAut.conj (Dat.θ ⟨x, hx⟩)) ∧
      (∀ x : ↥B, (x : Ω) ∉ innerPart S B → FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ ∧
        ∃ y : ↥(innerPart S B), ∃ k : ℕ, 0 < k ∧ k < p ∧ (x : Ω) = y * Dat.b ^ k ∧
          ∀ h : ↥H, ((lift x h : ↥H) : GL ι K) =
            (Dat.θ y : GL ι K) * (ModelGen.semiConj Dat.A Dat.σ ^ k) h *
              (Dat.θ y : GL ι K)⁻¹) := by
    rcases Dat.split with hBB | hF
    · refine ⟨fun x => MulAut.conj (Dat.θ ⟨x, by rw [hBB]; exact x.2⟩), fun x h => ?_,
        fun x hx => rfl, fun x hx => absurd (by rw [hBB]; exact x.2) hx⟩
      rw [MulAut.conj_apply]
      exact Dat.map_conj _ h
    · have hF' := hF
      obtain ⟨hbB, hbN, hBb, hbout, hact, hform, hfix⟩ := hF
      choose y hy k hk hxk using fun x : ↥B =>
        exists_inner_mul_pow hp hB hbB hBb (x : Ω) x.2
      refine ⟨fun x => if hx : (x : Ω) ∈ innerPart S B then MulAut.conj (Dat.θ ⟨x, hx⟩)
          else MulAut.conj (Dat.θ ⟨y x, hy x⟩) *
            semiAut Dat.A Dat.σ (semiConj_mem_of_fieldAct hact) ^ k x,
        fun x h => ?_, fun x hx => ?_, fun x hx => ⟨hF', ⟨y x, hy x⟩, k x, ?_, hk x, hxk x,
          fun h => ?_⟩⟩
      · dsimp only
        by_cases hx : (x : Ω) ∈ innerPart S B
        · rw [dif_pos hx, MulAut.conj_apply]
          exact Dat.map_conj _ h
        · rw [dif_neg hx, MulAut.mul_apply, MulAut.conj_apply, Dat.map_conj,
            map_semiAut_pow hact, hxk x]
          simp only [Subgroup.coe_mk]
          group
      · simp only [dif_pos hx]
      · rcases Nat.eq_zero_or_pos (k x) with h0 | h0
        · exact absurd (by rw [hxk x, h0, pow_zero, mul_one]; exact hy x) hx
        · exact h0
      · dsimp only
        rw [dif_neg hx, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, coe_semiAut_pow_apply]
  set X : Subgroup ↥H := ModelGen.fixFam (fun x : {x : ↥B // (x : Ω) ∈ D} => lift x.1)
    with hXdef
  have hmemX : ∀ g : ↥H, g ∈ X ↔
      ∀ x : ↥(innerPart S B), (x : Ω) ∈ D → (g : GL ι K) * Dat.θ x = Dat.θ x * g := by
    intro g
    rw [hXdef, ModelGen.mem_fixFam]
    constructor
    · intro h x hx
      have h1 := h ⟨⟨x, x.2.1⟩, hx⟩
      rw [hlift₁ _ x.2, MulAut.conj_apply] at h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro h x
      rw [hlift₁ _ (hDB x.2), MulAut.conj_apply]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h ⟨x.1, hDB x.2⟩ x.2, mul_inv_cancel_right]
  have hIX : I ≤ X := by
    intro j hj
    rw [hmemX]
    intro x hx
    obtain ⟨c, hc⟩ := (hD x).mp hx
    exact (comm_of_scalar_of_block hUW hc (hθW x) (hjU _ ((hmemI j).mp hj))
      (hjW _ ((hmemI j).mp hj))).symm
  have hXN : X ≤ Subgroup.normalizer (I : Set ↥H) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro j
    obtain ⟨hgU, hgW⟩ := hCpres g g.2 ((hmemX g).mp hg)
    obtain ⟨hgU', hgW'⟩ := hCpres (g⁻¹ : ↥H) (g⁻¹).2 ((hmemX g⁻¹).mp (X.inv_mem hg))
    constructor
    · intro hj
      rw [hmemI] at hj ⊢
      simpa using conj_mem_blkI (hHβ g.2) hgU hgW hj
    · intro hj
      rw [hmemI] at hj ⊢
      have h1 := conj_mem_blkI (hHβ (g⁻¹).2) hgU' hgW' hj
      have e : ((g⁻¹ : ↥H) : GL ι K) * ((g * j * g⁻¹ : ↥H) : GL ι K) *
          ((g⁻¹ : ↥H) : GL ι K)⁻¹ = (j : GL ι K) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e] at h1
      exact h1
  have hInorm : (I.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIX).mpr hXN
  have hI : GLAPComponent p X I :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hIq' hpI' hIX hInorm
  have hlI : ∀ (x : ↥B) (j : ↥H), j ∈ I → lift x j ∈ I := by
    intro x j hj
    rw [hmemI] at hj ⊢
    by_cases hx : (x : Ω) ∈ innerPart S B
    · rw [hlift₁ x hx, MulAut.conj_apply]
      simpa using hθI ⟨x, hx⟩ j hj
    · obtain ⟨hF, y, k, -, -, -, hlx⟩ := hshape x hx
      obtain ⟨haU, haW, -⟩ := hfield hF
      rw [hlx]
      exact hθI y _ (semiConj_pow_mem_blkI hF.2.2.2.2.2.1 haU haW k hj)
  have hIB : ∀ x : ↥B, I.map (lift x).toMonoidHom = I := by
    intro x
    have hle : I.map (lift x).toMonoidHom ≤ I := by
      rintro _ ⟨j, hj, rfl⟩
      exact hlI x j hj
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (lift x).injective])
  have hID : ∀ x : ↥B, (∀ j ∈ I, lift x j = j) → (x : Ω) ∈ D := by
    intro x hfixI
    by_cases hx : (x : Ω) ∈ innerPart S B
    · have hcomm : ∀ j ∈ blkI β U W,
          (Dat.θ ⟨x, hx⟩ : GL ι K) * j = j * Dat.θ ⟨x, hx⟩ := by
        intro j hj
        have h1 := hfixI ⟨j, hIH hj⟩ ((hmemI _).mpr hj)
        rw [hlift₁ x hx, MulAut.conj_apply] at h1
        have h2 := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
        exact mul_inv_eq_iff_eq_mul.mp h2
      obtain ⟨c, hc⟩ := hSchur _ (hθU ⟨x, hx⟩) hcomm
      exact (hD ⟨x, hx⟩).mpr ⟨c, hc⟩
    · exfalso
      obtain ⟨hF, y, k, hk0, hkp, -, hlx⟩ := hshape x hx
      obtain ⟨-, -, hno⟩ := hfield hF
      refine hno _ (hθU y) (hθW y) k hk0 hkp fun j hj => ?_
      have h1 := hfixI ⟨j, hIH hj⟩ ((hmemI _).mpr hj)
      have h2 := congrArg Subtype.val h1
      rw [hlx] at h2
      exact h2
  set zH : ↥H := ⟨z, hzH⟩ with hzHdef
  have hzθ : ∀ x : ↥(innerPart S B), (Dat.θ x : GL ι K) * z = z * Dat.θ x := fun x =>
    comm_of_two_scalars hUW hzU hzW (hθU x) (hθW x)
  have hzD : ∀ x : ↥B, (x : Ω) ∈ D → lift x zH = zH := by
    intro x hx
    rw [hlift₁ x (hDB hx), MulAut.conj_apply]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzHdef]
    rw [hzθ, mul_inv_cancel_right]
  have hzI : ∀ j ∈ I, j * zH = zH * j := by
    intro j hj
    rw [hmemI] at hj
    apply Subtype.ext
    exact comm_of_two_scalars hUW hzU hzW (hjU _ hj) (fun w hw => by rw [hjW _ hj w hw]; exact hw)
  have hz1 : Dat.φ zH ≠ 1 := by
    intro h
    have hk : zH ∈ Dat.φ.ker := h
    rw [Dat.ker_eq, Subgroup.mem_subgroupOf] at hk
    obtain ⟨c, hc⟩ := hk
    have hc' : Matrix.GeneralLinearGroup.scalar ι c = z := hc
    have hz : ∀ v, glEquiv z v = (c : K) • v := by
      intro v
      rw [glEquiv_apply, ← hc']
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_mulVec, Matrix.one_mulVec]
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have e1 : ε₁ = c := smul_left_injective K hu0 ((hzU u hu).symm.trans (hz u))
    have e2 : ε₂ = c := smul_left_injective K hw0 ((hzW w hw).symm.trans (hz w))
    exact hε (e1.trans e2.symm)
  have hz2' : zH ^ 2 = 1 := Subtype.ext (by simpa [hzHdef] using hz2)
  have hDB' : D ≤ B := hDB.trans inf_le_left
  have key : ∀ E : Subgroup Ω, E ≤ B → D ≤ E → (Nat.card D = p ^ 2 → Nat.card E = p ^ 3) →
      (Nat.card D = p ^ 2 → GLAPLayer p
        (I ⊓ ModelGen.fixFam fun x : {x : ↥B // (x : Ω) ∈ E} => lift x.1) ≠ ⊥) →
      S267ConcA p S B := fun E hEB hDE hEc hIE =>
    concA_of_lift hp hB hBC Dat.φ Dat.range_eq hker hkerp lift hlift hDB' hEB hDE hDc hDBc hEc
      hI hIq' hpI' hIB hID hIE hz1 hz2' hzI hzD
  have hlayer : ∀ Y : Subgroup (GL ι K), Y ≤ H → GLAPLayer p Y ≠ ⊥ →
      GLAPLayer p (Y.subgroupOf H) ≠ ⊥ := by
    intro Y hYH hY hbot
    apply hY
    have h1 := CFSG.glaPLayer_map_eq_of_injective hp H.subtype H.subtype_injective (Y.subgroupOf H)
    rw [hbot, Subgroup.map_bot, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYH] at h1
    exact h1.symm
  by_cases hD2 : Nat.card D = p ^ 2
  · rcases hE hD2 with ⟨x₀, hx₀D, hlay⟩ | ⟨hF, hlay⟩
    ·
      have hEB₁ : D ⊔ Subgroup.zpowers (x₀ : Ω) ≤ innerPart S B :=
        sup_le hDB (Subgroup.zpowers_le.mpr x₀.2)
      refine key (D ⊔ Subgroup.zpowers (x₀ : Ω)) (hEB₁.trans inf_le_left) le_sup_left
        (fun _ => ?_) (fun _ => ?_)
      · rw [card_sup_zpowers_of_not_mem hp hB hDB' x₀.2.1 hx₀D, hD2]
        ring
      · have hEq : I ⊓ ModelGen.fixFam (fun x : {x : ↥B // (x : Ω) ∈ D ⊔
            Subgroup.zpowers (x₀ : Ω)} => lift x.1) =
            (blkI β U W ⊓ Subgroup.centralizer {(Dat.θ x₀ : GL ι K)}).subgroupOf H := by
          ext h
          rw [Subgroup.mem_inf, ModelGen.mem_fixFam, Subgroup.mem_subgroupOf,
            Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
          constructor
          · rintro ⟨hj, hfix⟩
            refine ⟨hj, ?_⟩
            have h1 := hfix ⟨⟨x₀, x₀.2.1⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
            rw [hlift₁ _ x₀.2, MulAut.conj_apply] at h1
            have h2 := congrArg Subtype.val h1
            simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
            exact (mul_inv_eq_iff_eq_mul.mp h2).symm
          · rintro ⟨hj, hc⟩
            refine ⟨hj, fun x => ?_⟩
            let T : Subgroup Ω := ((Subgroup.centralizer {h}).comap Dat.θ).map
              (innerPart S B).subtype
            have hDT : D ≤ T := by
              intro d hd
              refine ⟨⟨d, hDB hd⟩, ?_, rfl⟩
              rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
              apply Subtype.ext
              exact ((hmemX h).mp (hIX hj) ⟨d, hDB hd⟩ hd).symm
            have hx₀T : (x₀ : Ω) ∈ T := by
              refine ⟨x₀, ?_, rfl⟩
              rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
              exact Subtype.ext hc.symm
            obtain ⟨y, hy, hyx⟩ := sup_le hDT (Subgroup.zpowers_le.mpr hx₀T) x.2
            have hxB₁ : (x.1 : Ω) ∈ innerPart S B := hyx ▸ y.2
            rw [hlift₁ _ hxB₁, MulAut.conj_apply]
            have hy' : (⟨x.1, hxB₁⟩ : ↥(innerPart S B)) = y := Subtype.ext hyx.symm
            rw [hy']
            rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hy
            rw [hy, mul_inv_cancel_right]
        rw [hEq]
        exact hlayer _ (inf_le_left.trans hIH) hlay
    ·
      obtain ⟨hbB, hbN, hBb, hbout, hact, hform, hfix⟩ := hF
      have hbD : Dat.b ∉ D := fun h => hbN (hDB h).2
      have hDN : D ≤ S ⊔ Subgroup.centralizer (S : Set Ω) := hDB.trans inf_le_right
      refine key (D ⊔ Subgroup.zpowers Dat.b) (sup_le hDB' (Subgroup.zpowers_le.mpr hbB))
        le_sup_left (fun _ => ?_) (fun _ => ?_)
      · rw [card_sup_zpowers_of_not_mem hp hB hDB' hbB hbD, hD2]
        ring
      · have hp1 : 1 < p := hp.one_lt
        have hEq : I ⊓ ModelGen.fixFam (fun x : {x : ↥B // (x : Ω) ∈ D ⊔
            Subgroup.zpowers Dat.b} => lift x.1) =
            (blkI β U W ⊓ centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}).subgroupOf H := by
          ext h
          rw [Subgroup.mem_inf, ModelGen.mem_fixFam, Subgroup.mem_subgroupOf,
            Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          have hcen : (h : GL ι K) ∈ centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom} ↔
              ModelGen.semiConj Dat.A Dat.σ h = h := by
            rw [mem_centGL]
            constructor
            · intro hc
              apply glEquiv.injective
              refine LinearEquiv.ext fun v => ?_
              obtain ⟨v', rfl⟩ := (ModelGen.semiMap Dat.A Dat.σ).surjective v
              rw [ModelGen.glEquiv_semiConj_apply]
              exact (hc _ rfl v').symm
            · intro hc s hs v
              rw [Set.mem_singleton_iff] at hs
              subst hs
              have := ModelGen.glEquiv_semiConj_apply Dat.A Dat.σ (h : GL ι K) v
              rw [hc] at this
              exact this
          have hbB₁ : Dat.b ∉ innerPart S B := fun h => hbN h.2
          have hθ1 : ∀ y : ↥(innerPart S B), (y : Ω) = 1 → Dat.θ y = 1 := fun y hy => by
            rw [show y = 1 from Subtype.ext hy, map_one]
          constructor
          · rintro ⟨hj, hfixall⟩
            refine ⟨hj, hcen.mpr ?_⟩
            have h1 := hfixall ⟨⟨Dat.b, hbB⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
            obtain ⟨-, y, k, hk0, hkp, hbk, hlx⟩ := hshape ⟨Dat.b, hbB⟩ hbB₁
            have hNB : innerPart S B ≤ S ⊔ Subgroup.centralizer (S : Set Ω) := inf_le_right
            obtain ⟨hy1, hk1⟩ := eq_of_mul_pow_eq hp hB hNB hbB hbN hbout y.2
              (innerPart S B).one_mem hkp hp1
              (show (y : Ω) * Dat.b ^ k = 1 * Dat.b ^ 1 by rw [one_mul, pow_one]; exact hbk.symm)
            have h2 := congrArg Subtype.val h1
            rw [hlx, hθ1 y hy1, hk1, pow_one] at h2
            simpa using h2
          · rintro ⟨hj, hc⟩
            have hsc : ModelGen.semiConj Dat.A Dat.σ h = h := hcen.mp hc
            have hsck : ∀ n : ℕ, (ModelGen.semiConj Dat.A Dat.σ ^ n) h = h := by
              intro n
              induction n with
              | zero => rfl
              | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hsc]
            refine ⟨hj, fun x => ?_⟩
            obtain ⟨d, hd, j, hjp, hxd⟩ := exists_mul_pow_of_mem_sup hp hB hDB' hbB x.2
            have hcommD : ∀ y : ↥(innerPart S B), (y : Ω) ∈ D →
                (Dat.θ y : GL ι K) * h = h * Dat.θ y := fun y hy =>
              (((hmemX h).mp (hIX hj)) y hy).symm
            have hNB : innerPart S B ≤ S ⊔ Subgroup.centralizer (S : Set Ω) := inf_le_right
            by_cases hx : ((x.1 : ↥B) : Ω) ∈ innerPart S B
            · obtain ⟨hxd', -⟩ := eq_of_mul_pow_eq hp hB hNB hbB hbN hbout hx
                (hDB hd) hp.pos hjp (by simpa using hxd)
              rw [hlift₁ _ hx, MulAut.conj_apply]
              apply Subtype.ext
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
              rw [hcommD ⟨_, hx⟩ (hxd' ▸ hd), mul_inv_cancel_right]
            · obtain ⟨-, y, k, -, hkp, hyk, hlx⟩ := hshape x.1 hx
              obtain ⟨hyd, -⟩ := eq_of_mul_pow_eq hp hB hNB hbB hbN hbout y.2 (hDB hd)
                hkp hjp (hyk.symm.trans hxd)
              apply Subtype.ext
              rw [hlx, hsck, hcommD y (hyd ▸ hd), mul_inv_cancel_right]
        rw [hEq]
        exact hlayer _ (inf_le_left.trans hIH) hlay
  · exact key D hDB' le_rfl (fun h => absurd h hD2) (fun h => absurd h hD2)

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
