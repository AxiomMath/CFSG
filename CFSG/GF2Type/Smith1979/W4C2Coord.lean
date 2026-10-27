module

public import CFSG.GF2Type.Smith1979.W4C2Model
public import CFSG.LargeExtraspecial.GLRLinGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.GLR

@[expose] def conjEquiv {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
    [Module (ZMod 2) V'] (T : V ≃ₗ[ZMod 2] V') (f : V ≃ₗ[ZMod 2] V) : V' ≃ₗ[ZMod 2] V' :=
  T.symm.trans (f.trans T)

section Generic

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']

theorem conjEquiv_apply (T : V ≃ₗ[ZMod 2] V') (f : V ≃ₗ[ZMod 2] V) (v : V') :
    conjEquiv T f v = T (f (T.symm v)) := rfl

theorem conjEquiv_conjEquiv_symm (T : V ≃ₗ[ZMod 2] V') (f : V' ≃ₗ[ZMod 2] V') :
    conjEquiv T (conjEquiv T.symm f) = f :=
  LinearEquiv.ext fun v => by simp [conjEquiv_apply]

theorem map_mul_equiv (f g : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    W.map ((f * g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
      (W.map (g : V →ₗ[ZMod 2] V)).map (f : V →ₗ[ZMod 2] V) := by
  rw [← Submodule.map_comp]
  rfl

theorem map_conjEquiv (T : V ≃ₗ[ZMod 2] V') (f : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    (W.map (T : V →ₗ[ZMod 2] V')).map ((conjEquiv T f : V' ≃ₗ[ZMod 2] V') : V' →ₗ[ZMod 2] V') =
      (W.map (f : V →ₗ[ZMod 2] V)).map (T : V →ₗ[ZMod 2] V') := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun v => by simp [conjEquiv_apply]

end Generic

theorem mul_mem_of_relIndex_two {Y : Type*} [Group Y] {H K : Subgroup Y}
    (h : H.relIndex K = 2) {a b : Y} (ha : a ∈ K) (hb : b ∈ K) (haH : a ∉ H) (hbH : b ∉ H) :
    a * b ∈ H := by
  have h2 : (H.subgroupOf K).index = 2 := h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
    ⟨fun h' => absurd (Subgroup.mem_subgroupOf.mp h') haH,
      fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hbH⟩
  exact Subgroup.mem_subgroupOf.mp this

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_coord_pair {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}
    (hP : Pair S X A B) (hw : S.width = 4) :
    ∃ (φ : A ≃ₗ[ZMod 2] V4) (ψ : B ≃ₗ[ZMod 2] V4), ∀ (a : A) (b : B),
      polar S.q (a : S.Qt) (b : S.Qt) = φ a ⬝ᵥ ψ b := by
  have hA : finrank (ZMod 2) A = 4 := hP.finrank_A.trans hw
  let e : Basis (Fin 4) (ZMod 2) A := Module.finBasisOfFinrankEq (ZMod 2) A hA
  let Φ : B →ₗ[ZMod 2] Dual (ZMod 2) A :=
    A.subtype.dualMap ∘ₗ (S.q.polarBilin.flip ∘ₗ B.subtype)
  have hΦ : ∀ (b : B) (a : A), Φ b a = polar S.q (a : S.Qt) (b : S.Qt) := fun _ _ => rfl
  have hbij : Function.Bijective Φ := by
    refine ⟨?_, fun f => ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro b hb
      exact Subtype.ext (hP.eq_zero_of_polar b.2 fun a ha => by
        rw [← hΦ b ⟨a, ha⟩, hb]
        rfl)
    · obtain ⟨b, hb, hfb⟩ := hP.exists_polar_eq f
      exact ⟨⟨b, hb⟩, LinearMap.ext fun a => (hΦ _ a).trans (hfb a)⟩
  refine ⟨e.equivFun, (LinearEquiv.ofBijective Φ hbij).trans e.dualBasis.equivFun,
    fun a b => ?_⟩
  rw [← hΦ]
  have hsum : Φ b a = ∑ i, e.repr a i • Φ b (e i) := by
    conv_lhs => rw [← e.sum_repr a]
    simp only [map_sum, map_smul]
  rw [hsum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Module.Basis.dualBasis_equivFun]

theorem exists_iso_of_coord {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}
    (hP : Pair S X A B) (φ : A ≃ₗ[ZMod 2] V4) (ψ : B ≃ₗ[ZMod 2] V4)
    (hφψ : ∀ (a : A) (b : B), polar S.q (a : S.Qt) (b : S.Qt) = φ a ⬝ᵥ ψ b) :
    ∃ T : S.Qt ≃ₗ[ZMod 2] Vm, (∀ v, q0 (T v) = S.q v) ∧
      A.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nsub ∧ B.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nssub := by
  let Tinv : Vm ≃ₗ[ZMod 2] S.Qt :=
    (φ.symm.prodCongr ψ.symm).trans
      (Submodule.prodEquivOfIsCompl A B (IsCompl.of_eq hP.inf_eq hP.sup_eq))
  have hTinv : ∀ x y, Tinv (x, y) = ((φ.symm x : A) : S.Qt) + ((ψ.symm y : B) : S.Qt) :=
    fun _ _ => rfl
  have hq : ∀ x y, S.q (Tinv (x, y)) = x ⬝ᵥ y := by
    intro x y
    have hpol := hφψ (φ.symm x) (ψ.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hpol
    have h1 : polar S.q ((φ.symm x : A) : S.Qt) ((ψ.symm y : B) : S.Qt) =
        S.q (((φ.symm x : A) : S.Qt) + ((ψ.symm y : B) : S.Qt)) -
          S.q ((φ.symm x : A) : S.Qt) - S.q ((ψ.symm y : B) : S.Qt) := rfl
    rw [hP.q_A _ (φ.symm x).2, hP.q_B _ (ψ.symm y).2, sub_zero, sub_zero, hpol] at h1
    rw [hTinv]
    exact h1.symm
  refine ⟨Tinv.symm, fun v => ?_, ?_, ?_⟩
  · rw [q0_apply]
    have := hq (Tinv.symm v).1 (Tinv.symm v).2
    rw [Prod.mk.eta, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · ext w
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
    obtain ⟨x, y⟩ := w
    rw [hTinv, Nsub, Submodule.mem_prod, Submodule.add_mem_iff_right A (φ.symm x).2]
    constructor
    · intro hy
      have h0 : ((ψ.symm y : B) : S.Qt) ∈ A ⊓ B := ⟨hy, (ψ.symm y).2⟩
      rw [hP.inf_eq, Submodule.mem_bot] at h0
      refine ⟨Submodule.mem_top, ?_⟩
      have : ψ.symm y = 0 := Subtype.ext h0
      simpa using this
    · rintro ⟨-, hy⟩
      have hy' : y = 0 := hy
      simp [hy']
  · ext w
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
    obtain ⟨x, y⟩ := w
    rw [hTinv, Nssub, Submodule.mem_prod, Submodule.add_mem_iff_left B (ψ.symm y).2]
    constructor
    · intro hx
      have h0 : ((φ.symm x : A) : S.Qt) ∈ A ⊓ B := ⟨(φ.symm x).2, hx⟩
      rw [hP.inf_eq, Submodule.mem_bot] at h0
      refine ⟨?_, Submodule.mem_top⟩
      have : φ.symm x = 0 := Subtype.ext h0
      simpa using this
    · rintro ⟨hx, -⟩
      have hx' : x = 0 := hx
      simp [hx']

theorem mem_of_preserves_pair {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} (hP : Pair S X A B)
    {y : S.O} (hA : A.map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = A)
    (hB : B.map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B) : y ∈ X := by
  obtain ⟨x, hx, hxa⟩ := hP.exists_eqOn
    (LinearEquiv.ofSubmodules (y : S.Qt ≃ₗ[ZMod 2] S.Qt) A A hA)
  have hxy : ∀ a ∈ A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) a := fun a ha =>
    hxa ⟨a, ha⟩
  have hyB : ∀ b ∈ B, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) b ∈ B := fun b hb =>
    hB ▸ Submodule.mem_map_of_mem hb
  have hxyB : ∀ b ∈ B, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) b := by
    intro b hb
    refine (hP.apply_eq_iff hx hb (hyB b hb)).mpr fun a ha => ?_
    rw [hxy a ha]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup y.2 a b
  have hxy' : x = y := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have hv : v ∈ A ⊔ B := by rw [hP.sup_eq]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, map_add, hxy a ha, hxyB b hb]
  exact hxy' ▸ hx

theorem exists_mem_Mbar_notMem {X : Subgroup S.O} (hidx : X.relIndex S.Mbar = 2) :
    ∃ σ ∈ S.Mbar, σ ∉ X := by
  by_contra hcon
  push Not at hcon
  have h1 : X.relIndex S.Mbar = 1 := Subgroup.relIndex_eq_one.mpr hcon
  omega

theorem map_B_eq_A {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} (hP : Pair S X A B)
    (hidx : X.relIndex S.Mbar = 2)
    (hmap : ∀ σ ∈ S.Mbar, σ ∉ X →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B)
    {σ : S.O} (hσ : σ ∈ S.Mbar) (hσX : σ ∉ X) :
    B.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = A := by
  have h1 := hP.map_A_eq (mul_mem_of_relIndex_two hidx hσ hσ hσX hσX)
  rwa [Subgroup.coe_mul, map_mul_equiv, hmap σ hσ hσX] at h1

theorem conjEquiv_mem_Hm {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}
    (hP : Pair S X A B) (hidx : X.relIndex S.Mbar = 2)
    (hmap : ∀ σ ∈ S.Mbar, σ ∉ X →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B)
    {T : S.Qt ≃ₗ[ZMod 2] Vm} (hq : ∀ v, q0 (T v) = S.q v)
    (hA : A.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nsub) (hB : B.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nssub)
    {m : S.O} (hm : m ∈ S.Mbar) : conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Hm := by
  rw [mem_Hm_iff]
  refine ⟨fun v => ?_, ?_⟩
  · rw [conjEquiv_apply, hq, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup m.2, ← hq,
      LinearEquiv.apply_symm_apply]
  · by_cases hmX : m ∈ X
    · left
      have h1 := map_conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) A
      have h2 := map_conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) B
      rw [hP.map_A_eq hmX, hA] at h1
      rw [hP.symm.map_A_eq hmX, hB] at h2
      exact ⟨h1, h2⟩
    · right
      have h1 := map_conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) A
      have h2 := map_conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) B
      rw [hmap m hm hmX, hA, hB] at h1
      rw [map_B_eq_A hP hidx hmap hm hmX, hB, hA] at h2
      exact ⟨h1, h2⟩

theorem exists_conjEquiv_eq {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}
    (hP : Pair S X A B) (hXM : X ≤ S.Mbar) (hidx : X.relIndex S.Mbar = 2)
    (hmap : ∀ σ ∈ S.Mbar, σ ∉ X →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B)
    {T : S.Qt ≃ₗ[ZMod 2] Vm} (hq : ∀ v, q0 (T v) = S.q v)
    (hA : A.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nsub) (hB : B.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nssub)
    {f : Vm ≃ₗ[ZMod 2] Vm} (hf : f ∈ Hm) :
    ∃ m ∈ S.Mbar, conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) = f := by
  obtain ⟨hfq, hf'⟩ := mem_Hm_iff.mp hf
  have hgO : conjEquiv T.symm f ∈ S.O :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [conjEquiv_apply, LinearEquiv.symm_symm, ← hq, LinearEquiv.apply_symm_apply, hfq, hq]
  set g : S.O := ⟨conjEquiv T.symm f, hgO⟩
  have hNA : Nsub.map (T.symm : Vm →ₗ[ZMod 2] S.Qt) = A := (Submodule.map_symm_eq_iff T).mpr hA
  have hNB : Nssub.map (T.symm : Vm →ₗ[ZMod 2] S.Qt) = B := (Submodule.map_symm_eq_iff T).mpr hB
  have hgA : A.map ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      (Nsub.map (f : Vm →ₗ[ZMod 2] Vm)).map (T.symm : Vm →ₗ[ZMod 2] S.Qt) := by
    have := map_conjEquiv T.symm f Nsub
    rwa [hNA] at this
  have hgB : B.map ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      (Nssub.map (f : Vm →ₗ[ZMod 2] Vm)).map (T.symm : Vm →ₗ[ZMod 2] S.Qt) := by
    have := map_conjEquiv T.symm f Nssub
    rwa [hNB] at this
  have hconj : conjEquiv T (g : S.Qt ≃ₗ[ZMod 2] S.Qt) = f := conjEquiv_conjEquiv_symm T f
  rcases hf' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨g, hXM (mem_of_preserves_pair hP ?_ ?_), hconj⟩
    · rw [hgA, h1, hNA]
    · rw [hgB, h2, hNB]
  · obtain ⟨σ, hσ, hσX⟩ := exists_mem_Mbar_notMem (S := S) hidx
    have hσA := hmap σ hσ hσX
    have hσB := map_B_eq_A hP hidx hmap hσ hσX
    have hy : g * σ ∈ X := by
      refine mem_of_preserves_pair hP ?_ ?_
      · rw [Subgroup.coe_mul, map_mul_equiv, hσA, hgB, h2, hNA]
      · rw [Subgroup.coe_mul, map_mul_equiv, hσB, hgA, h1, hNB]
    refine ⟨g, ?_, hconj⟩
    have := S.Mbar.mul_mem (hXM hy) (S.Mbar.inv_mem hσ)
    rwa [mul_inv_cancel_right] at this

theorem exists_model_iso {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}
    (hP : Pair S X A B) (hw : S.width = 4) (hXM : X ≤ S.Mbar) (hidx : X.relIndex S.Mbar = 2)
    (hmap : ∀ σ ∈ S.Mbar, σ ∉ X →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B) :
    ∃ T : S.Qt ≃ₗ[ZMod 2] Vm, (∀ v, q0 (T v) = S.q v) ∧
      A.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nsub ∧ B.map (T : S.Qt →ₗ[ZMod 2] Vm) = Nssub ∧
      (∀ m ∈ S.Mbar, conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Hm) ∧
      (∀ f ∈ Hm, ∃ m ∈ S.Mbar, conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) = f) := by
  obtain ⟨φ, ψ, hφψ⟩ := exists_coord_pair hP hw
  obtain ⟨T, hq, hA, hB⟩ := exists_iso_of_coord hP φ ψ hφψ
  exact ⟨T, hq, hA, hB, fun _ hm => conjEquiv_mem_Hm hP hidx hmap hq hA hB hm,
    fun _ hf => exists_conjEquiv_eq hP hXM hidx hmap hq hA hB hf⟩

end CFSG.GF2Type.Smith1979.W4C2
