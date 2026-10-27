module

public import CFSG.LargeExtraspecial.S4Res

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4

section Descend

variable {K E F : Type*} [Group K] [Group E] [Group F]

@[expose] noncomputable def descend (φ : K →* E) (σ : K →* F) (h : φ.ker ≤ σ.ker) :
    φ.range →* F :=
  (QuotientGroup.lift φ.ker σ h).comp (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom

theorem descend_apply (φ : K →* E) (σ : K →* F) (h : φ.ker ≤ σ.ker) (k : K) :
    descend φ σ h ⟨φ k, k, rfl⟩ = σ k := by
  have e : (QuotientGroup.quotientKerEquivRange φ).symm ⟨φ k, k, rfl⟩ =
      (QuotientGroup.mk k : K ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [descend, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e]
  rfl

theorem descend_apply' (φ : K →* E) (σ : K →* F) (h : φ.ker ≤ σ.ker) {e : φ.range} {k : K}
    (hk : (e : E) = φ k) : descend φ σ h e = σ k := by
  have : e = ⟨φ k, k, rfl⟩ := Subtype.ext hk
  rw [this, descend_apply]

end Descend

section Section

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem isCompl_comap_map {X Y A B : Submodule (ZMod 2) U} (hXB : X ≤ B)
    (hsup : A ⊔ B = Y) (hinf : A ⊓ B = X) :
    IsCompl ((A.map X.mkQ).comap (Y.map X.mkQ).subtype)
      ((B.map X.mkQ).comap (Y.map X.mkQ).subtype) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro ⟨m, hm⟩ ⟨a, ha, hma⟩ ⟨b, hb, hmb⟩
    change X.mkQ a = m at hma
    change X.mkQ b = m at hmb
    apply Subtype.ext
    change m = 0
    have hab : a - b ∈ X := by
      rw [← Submodule.Quotient.eq]
      exact hma.trans hmb.symm
    have haB : a ∈ B := by
      have := add_mem (hXB hab) hb
      rwa [sub_add_cancel] at this
    have haX : a ∈ X := hinf ▸ ⟨ha, haB⟩
    rw [← hma]
    exact (Submodule.Quotient.mk_eq_zero X).mpr haX
  · rw [codisjoint_iff, eq_top_iff]
    rintro ⟨m, hm⟩ -
    obtain ⟨y, hy, rfl⟩ := hm
    have hy2 : y ∈ A ⊔ B := hsup ▸ hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy2
    have hay : a ∈ Y := hsup ▸ Submodule.mem_sup_left ha
    have hby : b ∈ Y := hsup ▸ Submodule.mem_sup_right hb
    have e : (⟨X.mkQ (a + b), ⟨a + b, hy, rfl⟩⟩ : ↥(Y.map X.mkQ)) =
        ⟨X.mkQ a, ⟨a, hay, rfl⟩⟩ + ⟨X.mkQ b, ⟨b, hby, rfl⟩⟩ := Subtype.ext (map_add _ a b)
    rw [e]
    exact Submodule.add_mem_sup ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩

end Section

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem map_eq_of_le {X : Submodule (ZMod 2) S.Qt} {x : S.O}
    (hx : ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X) :
    X.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = X :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact hx v hv)
    (LinearEquiv.finrank_map_eq _ X)

variable (S g) in
@[expose] noncomputable def quotHom (t : S.O) (X : Submodule (ZMod 2) S.Qt)
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X) :
    Rbar S g t →* ((S.Qt ⧸ X) ≃ₗ[ZMod 2] (S.Qt ⧸ X)) where
  toFun x := Submodule.Quotient.equiv X X ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (map_eq_of_le (hX x x.2))
  map_one' := by
    ext v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective X v
    rfl
  map_mul' x y := by
    ext v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective X v
    rfl

theorem quotHom_mk {t : S.O} {X : Submodule (ZMod 2) S.Qt}
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X) (x : Rbar S g t)
    (w : S.Qt) :
    quotHom S g t X hX x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :=
  rfl

variable (S g) in
@[expose] noncomputable def secHom (t : S.O) (X Y : Submodule (ZMod 2) S.Qt)
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y) :
    Rbar S g t →* (↥(Y.map X.mkQ) ≃ₗ[ZMod 2] ↥(Y.map X.mkQ)) :=
  restrictHom (quotHom S g t X hX) (Y.map X.mkQ) (by
    rintro x _ ⟨w, hw, rfl⟩
    exact ⟨_, hY x x.2 w hw, rfl⟩)

@[expose] noncomputable def secMk (X : Submodule (ZMod 2) S.Qt) {Y : Submodule (ZMod 2) S.Qt}
    {w : S.Qt} (hw : w ∈ Y) : ↥(Y.map X.mkQ) :=
  ⟨X.mkQ w, Submodule.mem_map_of_mem hw⟩

omit [Finite G] in
theorem coe_secMk (X : Submodule (ZMod 2) S.Qt) {Y : Submodule (ZMod 2) S.Qt} {w : S.Qt}
    (hw : w ∈ Y) : ((secMk X hw : ↥(Y.map X.mkQ)) : S.Qt ⧸ X) = X.mkQ w :=
  rfl

omit [Finite G] in
theorem exists_secMk (X : Submodule (ZMod 2) S.Qt) {Y : Submodule (ZMod 2) S.Qt}
    (m : ↥(Y.map X.mkQ)) : ∃ w, ∃ hw : w ∈ Y, m = secMk X hw := by
  obtain ⟨_, w, hw, rfl⟩ := m
  exact ⟨w, hw, rfl⟩

theorem coe_secHom_mk {t : S.O} {X Y : Submodule (ZMod 2) S.Qt}
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y) (x : Rbar S g t)
    {w : S.Qt} (hw : w ∈ Y) :
    ((secHom S g t X Y hX hY x (secMk X hw) : ↥(Y.map X.mkQ)) : S.Qt ⧸ X) =
      X.mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :=
  rfl

theorem secHom_fix_iff {t : S.O} {X Y : Submodule (ZMod 2) S.Qt}
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y) (x : Rbar S g t)
    {w : S.Qt} (hw : w ∈ Y) :
    secHom S g t X Y hX hY x (secMk X hw) = secMk X hw ↔
      ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X := by
  rw [← Submodule.Quotient.eq, Subtype.ext_iff, coe_secHom_mk hX hY x hw]
  rfl

variable (S g) in
@[expose] noncomputable def secRep (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O)
    (X Y : Submodule (ZMod 2) S.Qt)
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y)
    (hN : ∀ x ∈ Nbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ X) :
    RmodN S g t →* (↥(Y.map X.mkQ) ≃ₗ[ZMod 2] ↥(Y.map X.mkQ)) :=
  (descend (resV haQ t) (secHom S g t X Y hX hY) (by
    intro x hx
    rw [MonoidHom.mem_ker, resV_eq_one_iff] at hx
    rw [MonoidHom.mem_ker]
    ext ⟨m, hm⟩
    obtain ⟨w, hw, rfl⟩ := hm
    change X.mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = X.mkQ w
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hN _ hx w hw)).comp (MulEquiv.subgroupCongr (range_resV haQ t).symm).toMonoidHom

theorem secRep_resV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {X Y : Submodule (ZMod 2) S.Qt}
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y)
    (hN : ∀ x ∈ Nbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ X)
    {e : RmodN S g t} {x : Rbar S g t} (hex : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t x) :
    secRep S g haQ t X Y hX hY hN e = secHom S g t X Y hX hY x := by
  unfold secRep
  rw [MonoidHom.comp_apply]
  exact descend_apply' _ _ _ hex

end CFSG.LargeExtraspecial.S6
