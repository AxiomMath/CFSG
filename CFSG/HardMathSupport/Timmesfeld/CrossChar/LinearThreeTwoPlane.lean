module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearThreeTwoGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LieType.SeitzGeneration.LinearPlaneFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix Polynomial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.CTP

section Fixed

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_plane_fixing_vector (hn : 1 ≤ n) (h3 : (3 : F) ≠ 0)
    {D : Subgroup (SpecialLinearGroup (Fin n) F)} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 27) :
    ∃ E : Subgroup (SpecialLinearGroup (Fin n) F), E ≤ D ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ ∃ v : Fin n → F, v ≠ 0 ∧
        ∀ a ∈ E, (a : Matrix (Fin n) (Fin n) F).mulVec v = v := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ρ : SpecialLinearGroup (Fin n) F → Module.End F (Fin n → F) := fun x =>
    Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)
  have hmul : ∀ g h, ρ (g * h) = ρ g * ρ h := fun g h => by
    simp only [ρ, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl
  have hone : ρ 1 = 1 := by
    simp only [ρ, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  have hρ : ∀ x v, ρ x v = (x : Matrix (Fin n) (Fin n) F).mulVec v := fun x v => by
    simp [ρ, Matrix.toLin'_apply]
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ D, x ^ 3 = 1 := hD.2
  have hord : ∀ x ∈ D, x ≠ 1 → Nat.card (Subgroup.zpowers x) = 3 := fun x hx hx1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hexp x hx) hx1
  have hsubD : ∀ P : Subgroup D, P.map D.subtype ≤ D := by
    rintro P _ ⟨x, -, rfl⟩
    exact x.2
  have hcardmap : ∀ P : Subgroup D, Nat.card (P.map D.subtype) = Nat.card P := fun P =>
    Subgroup.card_map_of_injective D.subtype_injective
  have : Nontrivial (Fin n → F) := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  obtain ⟨P₁, hP₁⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 3 (n := 2)
    (by rw [hcard]; norm_num)
  obtain ⟨z₁, hz₁, hz₁1, v, -, hv0, hz₁v⟩ := CFSG.LieType.SeitzGeneration.exists_fixed_of_plane_rep
    ρ hmul hone (E := P₁.map D.subtype)
    (fun x hx y hy => hcomm x (hsubD P₁ hx) y (hsubD P₁ hy)) (fun x hx => hexp x (hsubD P₁ hx))
    (by rw [hcardmap, hP₁]; norm_num) h3 (U := ⊤) (fun _ _ _ _ => trivial) top_ne_bot
  have hz₁D : z₁ ∈ D := hsubD P₁ hz₁
  set U₁ : Submodule F (Fin n → F) := LinearMap.ker (ρ z₁ - 1) with hU₁
  have hmemU₁ : ∀ w, w ∈ U₁ ↔ ρ z₁ w = w := fun w => by
    simp [hU₁, LinearMap.mem_ker, sub_eq_zero]
  have hU₁D : ∀ e ∈ D, ∀ w ∈ U₁, ρ e w ∈ U₁ := fun e he w hw => by
    rw [hmemU₁] at hw ⊢
    rw [← Module.End.mul_apply, ← hmul, hcomm z₁ hz₁D e he, hmul, Module.End.mul_apply, hw]
  have hU₁0 : U₁ ≠ ⊥ := fun h => hv0 (by
    have : v ∈ U₁ := (hmemU₁ v).2 hz₁v
    rw [h] at this
    exact (Submodule.mem_bot F).1 this)
  have : CFSG.IsElementaryAbelian 3 D :=
    { toIsMulCommutative := hD.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hD.2 x x.2) }
  set z₁' : D := ⟨z₁, hz₁D⟩ with hz₁'
  have hz₁'1 : z₁' ≠ 1 := fun h => hz₁1 (congrArg Subtype.val h)
  obtain ⟨C, hBC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 3 D (Subgroup.zpowers z₁')
  have hCnorm : C.Normal := ⟨fun x hx g => by
    rw [hD.1.is_comm.comm g x, mul_inv_cancel_right]
    exact hx⟩
  have hcompl : Subgroup.IsComplement' (Subgroup.zpowers z₁') C := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hBC.disjoint ?_
    rw [← Subgroup.mul_normal, hBC.sup_eq_top, Subgroup.coe_top]
  have hCc : Nat.card C = 9 := by
    have h := hcompl.card_mul_card
    rw [Nat.card_zpowers, orderOf_eq_prime (Subtype.ext (hexp z₁ hz₁D)) hz₁'1, hcard] at h
    omega
  have hz₁C : z₁ ∉ C.map D.subtype := by
    rintro ⟨x, hx, hxz⟩
    have hx' : x = z₁' := Subtype.ext hxz
    rw [hx'] at hx
    exact hz₁'1 (Subgroup.disjoint_def.1 hBC.disjoint (Subgroup.mem_zpowers z₁') hx)
  obtain ⟨z₂, hz₂, hz₂1, u, hu, hu0, hz₂u⟩ := CFSG.LieType.SeitzGeneration.exists_fixed_of_plane_rep
    ρ hmul hone (E := C.map D.subtype)
    (fun x hx y hy => hcomm x (hsubD C hx) y (hsubD C hy)) (fun x hx => hexp x (hsubD C hx))
    (by rw [hcardmap, hCc]) h3 (U := U₁) (fun e he w hw => hU₁D e (hsubD C he) w hw) hU₁0
  have hz₂D : z₂ ∈ D := hsubD C hz₂
  have hz₁u : ρ z₁ u = u := (hmemU₁ u).1 hu
  have hz₂z₁ : z₂ ∉ Subgroup.zpowers z₁ := by
    intro h
    have heq : Subgroup.zpowers z₂ = Subgroup.zpowers z₁ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h)
        (by rw [hord z₁ hz₁D hz₁1, hord z₂ hz₂D hz₂1])
    apply hz₁C
    have : z₁ ∈ Subgroup.zpowers z₂ := heq ▸ Subgroup.mem_zpowers z₁
    exact (Subgroup.zpowers_le.2 hz₂) this
  let S : Subgroup (SpecialLinearGroup (Fin n) F) :=
    { carrier := {x | x ∈ D ∧ ρ x u = u}
      mul_mem' := fun {a b} ha hb => ⟨D.mul_mem ha.1 hb.1, by
        rw [hmul, Module.End.mul_apply, hb.2, ha.2]⟩
      one_mem' := ⟨D.one_mem, by rw [hone]; rfl⟩
      inv_mem' := fun {a} ha => ⟨D.inv_mem ha.1, by
        conv_lhs => rw [← ha.2]
        rw [← Module.End.mul_apply, ← hmul, inv_mul_cancel, hone]
        rfl⟩ }
  have hSD : S ≤ D := fun x hx => hx.1
  have hz₁S : z₁ ∈ S := ⟨hz₁D, hz₁u⟩
  have hz₂S : z₂ ∈ S := ⟨hz₂D, hz₂u⟩
  have hS9 : 3 ^ 2 ∣ Nat.card S := by
    have hdvd : Nat.card S ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hcard]
      exact Subgroup.card_dvd_of_le hSD
    obtain ⟨k, -, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hle : Nat.card S ≤ 3 := by
        rw [hSk]
        calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 3 := by norm_num
      have heq : Subgroup.zpowers z₁ = S :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz₁S) (by rw [hord z₁ hz₁D hz₁1]; omega)
      exact hz₂z₁ (heq ▸ hz₂S)
    rw [hSk]
    exact pow_dvd_pow 3 hk2
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) 3 hS9
  have hPS : P.map S.subtype ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hPD : P.map S.subtype ≤ D := hPS.trans hSD
  refine ⟨P.map S.subtype, hPD, ⟨⟨⟨fun a b => Subtype.ext (hcomm a (hPD a.2) b (hPD b.2))⟩⟩,
    fun x hx => hexp x (hPD hx)⟩, ?_, u, hu0, fun a ha => ?_⟩
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hP]
    norm_num
  · rw [← hρ]
    exact (hPS ha).2

end Fixed

section Lift

variable {n : ℕ} {F : Type} [Field F] [Finite F]

local notation "PSLn" => ProjectiveSpecialLinearGroup (Fin n) F

theorem localDeltaIn_eq_bot_psl_nonsplit_fix {p : ℕ} (hp : p.Prime) (hpF : ¬ p ∣ Nat.card F)
    (hpq : ¬ p ∣ Nat.card F - 1) (hn : 1 ≤ n)
    (hinj : Function.Injective (MulAut.conj : PSLn →* MulAut PSLn))
    (E₀ : Subgroup (SpecialLinearGroup (Fin n) F)) (hE₀ : IsElemAbelian p E₀)
    (hc₀ : Nat.card E₀ = p ^ 2)
    (hp4 : 3 < p ∨ 4 ≤ Nat.card F ∨ ∃ v : Fin n → F, v ≠ 0 ∧
      ∀ a ∈ E₀, (a : Matrix (Fin n) (Fin n) F).mulVec v = v)
    {H : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) :
    localDeltaIn p H ((E₀.map (toPSL n F)).map (MulAut.conj : PSLn →* MulAut PSLn)) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) := fun hd =>
    hpq (hd.trans ((CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd hn F).trans
      (Nat.gcd_dvd_right _ _)))
  have : CFSG.IsElementaryAbelian p E₀ :=
    { toIsMulCommutative := hE₀.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE₀.2 x x.2) }
  have hπ1 : ∀ a ∈ E₀, a ≠ 1 → toPSL n F a ≠ 1 := by
    intro a ha ha1 h1
    apply hZ
    rw [← orderOf_eq_prime (hE₀.2 a ha) ha1]
    exact Subgroup.orderOf_dvd_natCard _ (toPSL_eq_one_iff.1 h1)
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  refine eq_one_of_fixSub_toPSL (eq_top_of_good_blocks_le_fix hp
    (natCast_ne_zero_of_not_dvd_card hp hpF) hpF hpq E₀ hc₀ hp4 _ ?_)
  intro a ha ha1 hsq h hgood hpd x hx
  obtain ⟨s, hs⟩ := blockImage_le_range_toGL_of_good hsq h hgood hx
  rw [← hs] at hx ⊢
  refine ⟨s, ?_, rfl⟩
  exact blockPSL_le_fixSub hp hinj hZ hH hg ⟨_, ⟨a, ha, rfl⟩, rfl⟩ (hπ1 a ha ha1) hgood hpd
    ⟨s, hx, rfl⟩

end Lift

end CFSG.HardMathSupport.Timmesfeld.CrossChar
