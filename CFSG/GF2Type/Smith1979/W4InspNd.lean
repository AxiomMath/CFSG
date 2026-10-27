module

public import CFSG.GF2Type.Smith1979.W4InspDefs
public import CFSG.LargeExtraspecial.AS35YRU33
public import CFSG.LargeExtraspecial.DWRtMain
public import CFSG.LargeExtraspecial.S12InspFamESpOut
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G} {t : S.O}

namespace Nd

omit [IsSimpleGroup G] in
theorem exists_elemAbelian_mulAut_Xbar12 (hS : S.S12Standing g t) {E : Subgroup S.O}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hEM : E ≤ S.Mbar) :
    ∃ A : Subgroup (MulAut (S.Xbar12 g)), CFSG.Open.IsElemAbelian 2 A ∧
      Nat.card A = Nat.card E := by
  set N : Subgroup S.Mbar := (S.Xbar12 g).subgroupOf S.Mbar with hNdef
  have hN : N.Normal := ⟨fun n hn m => by
    rw [hNdef, mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (Setting.Mbar_le_normalizer_Xbar12 m.2) (n : S.O)).mp hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this⟩
  have hC : centralizer (N : Set S.Mbar) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have hmC : (m : S.O) ∈ S.CXbar12 g := by
      refine ⟨m.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h := mem_centralizer_iff.mp hm ⟨y, Setting.Xbar12_le_Mbar hy⟩
        (show (⟨y, Setting.Xbar12_le_Mbar hy⟩ : S.Mbar) ∈ N from hy)
      exact congrArg Subtype.val h
    rw [hS.cent, mem_bot] at hmC
    exact (mem_bot).mpr (Subtype.ext hmC)
  have hinj : Function.Injective (MulAut.conjNormal : S.Mbar →* MulAut N) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
    intro h hh
    rw [mem_centralizer_iff]
    intro n hn
    have e := congrArg (fun σ : MulAut N => ((σ ⟨n, hn⟩ : N) : S.Mbar))
      (MonoidHom.mem_ker.mp hh)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at e
    calc n * h = h * n * h⁻¹ * h := by rw [e]
      _ = h * n := by group
  let ε : N ≃* S.Xbar12 g := subgroupOfEquivOfLe Setting.Xbar12_le_Mbar
  have hE₀ : CFSG.Open.IsElemAbelian 2 (E.subgroupOf S.Mbar) := hE.subgroupOf _
  refine ⟨((E.subgroupOf S.Mbar).map (MulAut.conjNormal : S.Mbar →* MulAut N)).map
    (MulAut.congr ε).toMonoidHom, (hE₀.map _).map _, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.congr ε).injective,
    Subgroup.card_map_of_injective hinj,
    Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv]

theorem exists_alt_nondegenerate_six :
    ∃ b : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2), (∀ x, b x x = 0) ∧
      (∀ x, (∀ y, b x y = 0) → x = 0) := by
  let M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    Matrix.of fun i j => if i.val / 2 = j.val / 2 ∧ i ≠ j then 1 else 0
  refine ⟨Matrix.toBilin' M, ?_, ?_⟩
  · intro x
    rw [Matrix.toBilin'_apply']
    revert x
    decide +kernel
  · simp only [Matrix.toBilin'_apply']
    decide +kernel

theorem nonempty_mulEquiv_statedProj_psp3 {X : Type} [Group X] (h : LieModel X .PSp 3 2 1) :
    Nonempty (X ≃* StatedProj (StatedSp 3 (ZMod 2))) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    let σ : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hK'
    exact ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3 ⊕ Fin 3) σ.symm)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp σ.symm 3)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars σ.symm))⟩
  all_goals exact absurd ht (by decide)

end Nd

omit [IsSimpleGroup G] in
theorem false_of_psl32 (hc : Ctx S g t) (h : LieModel (S.Xbar12 g) .PSL 3 2 1) : False := by
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 h
  set Φ := MulAut.congr e
  have : Finite (MulAut (S.Xbar12 g)) := Finite.of_equiv _ Φ.symm.toEquiv
  have hcard : Nat.card (MulAut (S.Xbar12 g)) = 336 := by
    rw [Nat.card_congr Φ.toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  have hbound : ∀ A : Subgroup (MulAut (S.Xbar12 g)), CFSG.IsElementaryAbelian 2 A →
      Nat.card A ≤ 2 ^ 2 := fun A hA =>
    CFSG.LieType.SteinbergBR.card_le_sq_of_orderOf
      (g := Φ.symm CFSG.LieType.SteinbergBR.AutGL32.alphaAut) (k := 3)
      (by rw [MulEquiv.orderOf_eq, CFSG.LieType.SteinbergBR.AutGL32.orderOf_alphaAut])
      (by rw [hcard]; norm_num) A
  have hEA : CFSG.IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar hc.haQ
  obtain ⟨A, hA, hAcard⟩ := Nd.exists_elemAbelian_mulAut_Xbar12 (g := g) hc.hS
    (CFSG.Open.isElemAbelian_of_isElementaryAbelian) (S.Lbar_le_Mbar g)
  have h1 := hbound A hA.isElementaryAbelian
  have h2 := S.card_Lbar_ge hc.haQ hc.hne
  rw [hc.hw, ← hAcard] at h2
  norm_num at h1 h2
  omega

omit [IsSimpleGroup G] in
theorem false_of_psl32_f2
    (hc : Ctx S g t) (h : LieModel (S.Xbar12 g) .PSL 3 2 2) : False :=
  DW.dw2FieldInput (S.Xbar12 g) .PSL 3 2 le_rfl (Or.inl ⟨rfl, le_rfl⟩) h _
    (Setting.isTransClass34_Ebar12 hc.ht hc.htA hc.hS)

omit [IsSimpleGroup G] in
theorem spSixSpin_of_psp3 (hc : Ctx S g t) (h : LieModel (S.Xbar12 g) .PSp 3 2 1) :
    S.S12SpSixSpin g := by
  obtain ⟨b, hb₁, hb₂⟩ := Nd.exists_alt_nondegenerate_six
  obtain ⟨e₁⟩ := Nd.nonempty_mulEquiv_statedProj_psp3 h
  obtain ⟨e₂⟩ := S12InspSp.nonempty_SpG_mulEquiv (m := 3) hb₁ hb₂
  obtain ⟨e₃⟩ := S12InspSp.nonempty_SpG_mulEquiv_isometryGroup b
  have hX : S.Xbar12 g = S.Mbar :=
    Setting.xbar12_eq_mbar_of_sp hc.hS (le_refl 3) hb₁ hb₂ (e₁.trans e₂.symm)
  have hiso : s12SpIsometries b = TauCeti.BilinForm.isometryGroup b := by
    ext f
    exact TauCeti.BilinForm.mem_isometryGroup_iff.symm
  exact ⟨hc.hw, hX, b, hb₁, hb₂,
    ⟨(e₁.trans e₂.symm).trans (e₃.trans (MulEquiv.subgroupCongr hiso.symm))⟩⟩

omit [IsSimpleGroup G] in
theorem false_of_psu33
    (hc : Ctx S g t) (hirr : XIrred S g)
    (h : LieModel (S.Xbar12 g) .PSU 3 3 1) : False := by
  have htX : t ∈ S.Xbar12 g := Setting.subset_Xbar12 (Setting.mem_Ebar12_of_mem_Lbar hc.ht hc.htA)
  have h1 : (⟨t, htX⟩ : S.Xbar12 g) ≠ 1 := fun h' => hc.htA.2.1 (by
    have := congrArg (fun x : S.Xbar12 g => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h'
    simpa using this)
  have h2 : (⟨t, htX⟩ : S.Xbar12 g) * ⟨t, htX⟩ = 1 := Subtype.ext (Subtype.ext hc.htA.2.2.1)
  exact S14.asc512U33ModuleInput (S.Xbar12 g) h S.Qt S.q S.q_nondegenerate (S.actX12 g)
    ((S.O.subtype_injective).comp (S.Xbar12 g).subtype_injective)
    (fun x v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (x : S.O).2 v)
    (fun W hW => hirr W hW) _ h1 h2 hc.htA.2.2.2.1.le

end CFSG.GF2Type.Smith1979.W4Insp
