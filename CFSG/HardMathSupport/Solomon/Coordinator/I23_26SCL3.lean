module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

section Act

variable {X : Type*} [Group X]

@[expose] def i2326sAct (K : Subgroup X) : ↥(Subgroup.normalizer (K : Set X)) →* MulAut ↥K where
  toFun g :=
    { toFun := fun k => ⟨(g : X) * k * (g : X)⁻¹, ((Subgroup.mem_normalizer_iff.1 g.2) k).1 k.2⟩
      invFun := fun k => ⟨(g : X)⁻¹ * k * (g : X), by
        have := ((Subgroup.mem_normalizer_iff.1 (inv_mem g.2)) k).1 k.2
        simpa using this⟩
      left_inv := fun k => by
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := fun k => by
        apply Subtype.ext
        simp [mul_assoc]
      map_mul' := fun a b => by
        apply Subtype.ext
        simp [mul_assoc] }
  map_one' := by
    ext k
    simp
  map_mul' := fun a b => by
    ext k
    simp [mul_assoc]

theorem i2326sAct_fixedSub (K : Subgroup X) (g : ↥(Subgroup.normalizer (K : Set X))) :
    (Lemma512Ns.fixedSub (i2326sAct K g)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(g : X)} : Set X) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h : (i2326sAct K g k : ↥K) = k := hk
    have h' : (g : X) * k * (g : X)⁻¹ = k := congrArg Subtype.val h
    exact ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h').symm⟩
  · rintro ⟨hxK, hx⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.1 hx
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    show (i2326sAct K g ⟨x, hxK⟩ : ↥K) = ⟨x, hxK⟩
    apply Subtype.ext
    show (g : X) * x * (g : X)⁻¹ = x
    rw [← hx']
    group

end Act

section Layer

variable {X : Type*} [Group X] [Finite X]

theorem i2326s_layer_map (K : Subgroup X) (A : Subgroup ↥K) :
    GLAPLayer 3 (A.map K.subtype) = (GLAPLayer 3 A).map K.subtype := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hker : ∀ S : Subgroup ↥K, Nat.Coprime 3 (Nat.card ↥(S ⊓ K.subtype.ker)) := by
    intro S
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  refine le_antisymm (sSup_le fun L hL => ?_) ?_
  · obtain ⟨L0, hL0, rfl⟩ := exists_glaPComponent_map_eq hp K.subtype (hker A) hL
    exact Subgroup.map_mono (le_sSup hL0)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_map hp K.subtype (hker A) hL)

end Layer

section Inv

theorem i2326s_isInnDiagThree_inv {Y : Type*} [Group Y] {α : MulAut Y} (h : IsInnDiagThree α) :
    IsInnDiagThree α⁻¹ := by
  rcases h with ⟨F, hF, hFin, θ, φ, ⟨g, hg, hgφ⟩, hα⟩ | ⟨F, hF, hFin, q, θ, φ, hcard, ⟨g, hg, hgφ⟩, hα⟩
  · refine Or.inl ⟨F, hF, hFin, θ, φ⁻¹, ⟨g⁻¹, inv_mem hg, fun A A' hA => ?_⟩, fun y => ?_⟩
    · rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
      refine (hgφ A' A ?_).symm
      rw [hA]
      group
    · have := hα (α⁻¹ y)
      rw [MulAut.apply_inv_self] at this
      rw [this]
      simp
  · refine Or.inr ⟨F, hF, hFin, q, θ, φ⁻¹, hcard, ⟨g⁻¹, inv_mem hg, fun A A' hA => ?_⟩, fun y => ?_⟩
    · rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
      refine (hgφ A' A ?_).symm
      rw [hA]
      group
    · have := hα (α⁻¹ y)
      rw [MulAut.apply_inv_self] at this
      rw [this]
      simp

end Inv

section Main

variable {X : Type} [Group X] [Finite X]

@[expose] def i2326sRho (K E : Subgroup X) (hN : E ≤ Subgroup.normalizer (K : Set X)) :
    ↥E →* MulAut ↥K :=
  (i2326sAct K).comp (Subgroup.inclusion hN)

theorem i2326sRho_injective {K E : Subgroup X} (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k = k * e) → e = 1) :
    Function.Injective (i2326sRho K E hN) := by
  rw [injective_iff_map_eq_one]
  intro e he
  apply Subtype.ext
  refine hfaith e e.2 (fun k hk => ?_)
  have h1 := congrArg Subtype.val (DFunLike.congr_fun he ⟨k, hk⟩)
  have h2 : (e : X) * k * (e : X)⁻¹ = k := h1
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem i2326sRho_isElemAbelian {K E : Subgroup X} (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (i2326sRho K E hN).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    show (a : MulAut ↥K) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (elemAbelian_comm hE a'.2 b'.2)
  · obtain ⟨x', rfl⟩ := hx
    rw [← map_pow]
    have : x' ^ 3 = 1 := Subtype.ext (hE.2 x' x'.2)
    rw [this, map_one]

theorem i2326s_sc_L3 (hA : BGLFieldPairGeneration) (hP : AutL3ElemStructure)
    (hV : AutL3NoE27OffType) {K E : Subgroup X}
    (hK : IsComponentOf K ⊤) (hT : IsLThreeEpsBar (↥K ⧸ Subgroup.center ↥K))
    (hE : IsElemAbelian 3 E) (h27 : Nat.card E = 27) (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k = k * e) → e = 1) :
    K ≤ ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1), GLAPLayer 3 (K ⊓ Subgroup.centralizer ({e} : Set X)) := by
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  set ρ := i2326sRho K E hN with hρdef
  have hinj : Function.Injective ρ := i2326sRho_injective hN hfaith
  have hEbar := i2326sRho_isElemAbelian hN hE
  have hcard : Nat.card ρ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact h27
  have hprod : (∃ b ∈ ρ.range, IsFieldAutThree b ∧ b ≠ 1) ∧
      ∃ x ∈ ρ.range, IsInnDiagThree x ∧ x ≠ 1 := by
    by_cases hExt : IsExtremalType (↥K ⧸ Subgroup.center ↥K)
    · exact hP ↥K hq hExt ρ.range hEbar hcard
    · exact absurd hcard (hV ↥K hq hT hExt ρ.range hEbar)
  obtain ⟨⟨bb, ⟨b, rfl⟩, hbF, hb1⟩, ⟨xx, ⟨x, rfl⟩, hxD, hx1⟩⟩ := hprod
  have hb3 : (ρ b) ^ 3 = 1 := by
    rw [← map_pow]
    have : b ^ 3 = 1 := Subtype.ext (hE.2 b b.2)
    rw [this, map_one]
  have hx3 : (ρ x) ^ 3 = 1 := by
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
    rw [this, map_one]
  have hcomm : ρ b * ρ x = ρ x * ρ b := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (elemAbelian_comm hE b.2 x.2)
  have hBGL := hA ↥K hq hT (ρ b) (ρ x) hbF hb1 hb3 hxD hx1 hx3 hcomm
  have hbx1 : ρ b * ρ x ≠ 1 := by
    intro h
    have hinv : ρ b = (ρ x)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hD : IsInnDiagThree (ρ b) := by
      rw [hinv]
      exact i2326s_isInnDiagThree_inv hxD
    exact hb1 (LocalBalance.AutL3.input7_fieldInnDiag_holds ↥K hq (ρ b) hbF hD)
  have hbne : (b : X) ≠ 1 := by
    intro h
    apply hb1
    have : b = 1 := Subtype.ext h
    rw [this, map_one]
  have hbxne : ((b * x : ↥E) : X) ≠ 1 := by
    intro h
    apply hbx1
    have : b * x = 1 := Subtype.ext h
    rw [← map_mul, this, map_one]
  have hmap : ∀ g : ↥E, (Lemma512Ns.fixedSub (ρ g)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(g : X)} : Set X) := fun g =>
    i2326sAct_fixedSub K (Subgroup.inclusion hN g)
  have hK' : K = (⊤ : Subgroup ↥K).map K.subtype := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have h1 := Subgroup.map_mono (f := K.subtype) hBGL
  rw [← hK', Subgroup.map_sup, ← i2326s_layer_map, ← i2326s_layer_map, hmap b,
    show ρ b * ρ x = ρ (b * x) by rw [map_mul], hmap (b * x)] at h1
  refine h1.trans (sup_le ?_ ?_)
  · exact le_iSup_of_le (b : X) (le_iSup_of_le b.2 (le_iSup_of_le hbne le_rfl))
  · exact le_iSup_of_le ((b * x : ↥E) : X) (le_iSup_of_le (b * x).2 (le_iSup_of_le hbxne le_rfl))

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
