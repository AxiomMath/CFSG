module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAut
public import CFSG.RankThree.PartOne.F106.OddRadUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KU6Cent

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

abbrev Gu : Subgroup (GL (Fin 6) F4) := primeFormUnitary hF4 (idGram F4 6)

abbrev PGU6 : Type := StatedProj Gu

abbrev ZG : Subgroup Gu := (StatedScalars (Fin 6) F4).subgroupOf Gu

abbrev Z6 : Subgroup M6 := (StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4)

instance Z6_normal : Z6.Normal := Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 6) F4) _

theorem mem_ZG {g : Gu} :
    g ∈ ZG ↔ ∃ c : F4ˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) c = (g : GL (Fin 6) F4) := by
  rw [ZG, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]

theorem mem_Z6 {u : M6} :
    u ∈ Z6 ↔ ∃ c : F4ˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) c = (u : GL (Fin 6) F4) := by
  rw [Z6, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]

theorem pow_three_of_units (c : F4ˣ) : (c : F4) ^ 3 = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one (c : F4) c.ne_zero
  rw [CFSG.Fischer.F4.card] at h
  exact h

theorem units_cube (c : F4ˣ) : c ^ 3 = 1 :=
  Units.ext (by simpa using pow_three_of_units c)

theorem norm_units (c : F4ˣ) : hF4.norm (c : F4) = 1 := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
  calc (c : F4) * (c : F4) ^ 2 ^ 1 = (c : F4) ^ 3 := by ring
    _ = 1 := pow_three_of_units c

theorem map_Z6_eq :
    Subgroup.map (eGram6 : M6 ≃* ↥(gramSU hF4 (idGram F4 6))).toMonoidHom Z6 =
      normOneScalars hF4 (gramSU hF4 (idGram F4 6)) 6 := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_Z6]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, norm_units c, by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, units_cube, one_pow], hc.symm⟩
  · rintro ⟨c, -, -, hg⟩
    exact ⟨c, hg.symm⟩

noncomputable def e6 : S6 ≃* primeFormP hF4 (idGram F4 6) :=
  QuotientGroup.congr Z6 (normOneScalars hF4 (gramSU hF4 (idGram F4 6)) 6) eGram6 map_Z6_eq

@[expose] def autTr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) : MulAut X →* MulAut Y where
  toFun φ := e.symm.trans (φ.trans e)
  map_one' := MulEquiv.ext fun y => by simp
  map_mul' φ ψ := MulEquiv.ext fun y => by simp

theorem autTr_apply {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (φ : MulAut X) (y : Y) :
    autTr e φ y = e (φ (e.symm y)) := rfl

theorem autTr_injective {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Function.Injective (autTr e) := by
  intro φ ψ h
  apply MulEquiv.ext
  intro x
  have h' := congrArg (fun θ : MulAut Y => θ (e x)) h
  simpa [autTr_apply] using h'

@[expose] noncomputable def Psi0 : Gu →* MulAut S6 :=
  (autTr e6.symm).comp (primeFormConjHom hF4 (idGram F4 6))

theorem Psi0_apply (g : Gu) (x : S6) :
    Psi0 g x = e6.symm (primeFormConjHom hF4 (idGram F4 6) g (e6 x)) := rfl

theorem e6_mk (u : M6) : e6 (QuotientGroup.mk u) = QuotientGroup.mk (eGram6 u) :=
  QuotientGroup.congr_mk _ _ _ _ u

theorem Psi0_mk (g : Gu) (u v : M6) (h : (v : GL (Fin 6) F4) = g * u * g⁻¹) :
    Psi0 g (QuotientGroup.mk u) = QuotientGroup.mk v := by
  apply e6.injective
  rw [Psi0_apply, MulEquiv.apply_symm_apply, e6_mk, e6_mk]
  show primeFormConjAut hF4 (idGram F4 6) g (QuotientGroup.mk (eGram6 u)) = QuotientGroup.mk (eGram6 v)
  rw [primeFormConjAut_mk]
  congr 1
  exact Subtype.ext h.symm

theorem Psi0_eq_of (β : MulAut S6) (g : Gu)
    (h : ∀ u v : M6, (v : GL (Fin 6) F4) = g * u * g⁻¹ → β (QuotientGroup.mk u) = QuotientGroup.mk v) :
    Psi0 g = β := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [Psi0_mk g u (conjM6 g u) (conjM6_apply g u)]
    exact (h u (conjM6 g u) (conjM6_apply g u)).symm

theorem Psi0_eq_one_iff (g : Gu) :
    Psi0 g = 1 ↔ ∃ c : F4ˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) c = (g : GL (Fin 6) F4) := by
  have h1 : Psi0 g = 1 ↔ primeFormConjHom hF4 (idGram F4 6) g = 1 := by
    rw [show Psi0 g = autTr e6.symm (primeFormConjHom hF4 (idGram F4 6) g) from rfl,
      ← map_one (autTr e6.symm)]
    exact (autTr_injective _).eq_iff
  rw [h1, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.primeFormConjHom_eq_one_iff hF4
    (by norm_num) (by norm_num) g]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨c, by rw [hc]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, norm_units c, by rw [hc]⟩

theorem ZG_le_ker_Psi0 : ZG ≤ (Psi0).ker := by
  intro g hg
  rw [MonoidHom.mem_ker, Psi0_eq_one_iff]
  exact mem_ZG.1 hg

@[expose] noncomputable def Psi : PGU6 →* MulAut S6 :=
  QuotientGroup.lift ZG Psi0 ZG_le_ker_Psi0

theorem Psi_mk (g : Gu) : Psi (QuotientGroup.mk g) = Psi0 g := rfl

theorem Psi_injective : Function.Injective Psi := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [Psi_mk, Psi0_eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff]
    exact mem_ZG.2 hx

theorem exists_Psi_of_pow_three (β : MulAut S6) (hβ : β ^ 3 = 1) : ∃ g : PGU6, Psi g = β := by
  obtain ⟨B, hB, -, hβB⟩ := exists_unitary_of_pow_three β hβ
  exact ⟨QuotientGroup.mk ⟨B, hB⟩, by rw [Psi_mk]; exact Psi0_eq_of β ⟨B, hB⟩ hβB⟩

theorem Gu_of_SU : StatedSU 6 (2 ^ 1) F4 ≤ Gu := by
  rw [← gramSU_idGram_six]
  exact CFSG.RankThree.PartOne.F106.OddRadUnitary.gramSU_le_primeFormUnitary hF4

@[expose] noncomputable def iota : S6 →* PGU6 :=
  QuotientGroup.map Z6 ZG (Subgroup.inclusion Gu_of_SU) (by
    intro u hu
    rw [Subgroup.mem_comap]
    obtain ⟨c, hc⟩ := mem_Z6.1 hu
    exact mem_ZG.2 ⟨c, hc⟩)

theorem iota_mk (u : M6) :
    iota (QuotientGroup.mk u) = QuotientGroup.mk (Subgroup.inclusion Gu_of_SU u) := rfl

theorem iota_injective : Function.Injective iota := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [iota_mk, QuotientGroup.eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨c, hc⟩ := mem_ZG.1 hx
    exact mem_Z6.2 ⟨c, hc⟩

theorem iota_Psi0 (g : Gu) (x : S6) :
    iota (Psi0 g x) = QuotientGroup.mk g * iota x * (QuotientGroup.mk g)⁻¹ := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [Psi0_mk g u (conjM6 g u) (conjM6_apply g u), iota_mk, iota_mk,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1

theorem iota_mem_centralizer (g : Gu) (x : S6) (hx : Psi0 g x = x) :
    iota x ∈ Subgroup.centralizer ({QuotientGroup.mk g} : Set PGU6) := by
  have h := congrArg iota hx
  rw [iota_Psi0] at h
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : QuotientGroup.mk g * iota x = iota x * QuotientGroup.mk g := by
    calc QuotientGroup.mk g * iota x
        = QuotientGroup.mk g * iota x * (QuotientGroup.mk g)⁻¹ * QuotientGroup.mk g := by group
      _ = iota x * QuotientGroup.mk g := by rw [h]
  exact h2.symm

end CFSG.LocalAnalysis.GLTheoremA.KU6Cent

end
