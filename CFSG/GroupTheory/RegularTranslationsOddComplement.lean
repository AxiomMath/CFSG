module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CharacterTheory.Semidihedral.CentralHall
public import CFSG.GroupTheory.FixedPointFreeCommutator

public noncomputable section

open Subgroup
open scoped Pointwise

namespace CFSG

universe u

theorem exists_characteristic_two_factor_of_regular_translation
    {G : Type u} [Group G] [Finite G] (E : Subgroup G) (t : G)
    (hJpow : ∀ j ∈ E ⊔ Subgroup.zpowers t, j ^ 2 = 1)
    (hNE : Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤
      Subgroup.normalizer (E : Set G))
    (O : Subgroup G)
    (hOC : O ≤ Subgroup.centralizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G))
    (hOodd : Odd (Nat.card O))
    (hNO : Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤
      Subgroup.normalizer (O : Set G))
    (hJO : (E ⊔ Subgroup.zpowers t) ⊔ O =
      Subgroup.centralizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G))
    (hJOdisj : (E ⊔ Subgroup.zpowers t) ⊓ O = ⊥)
    (κ : (Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (E : Set G) : Subgroup G) →* E)
    (hκformula : ∀ x : (Subgroup.normalizer
        ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ⊓
        Subgroup.centralizer (E : Set G) : Subgroup G),
      ((κ x : E) : G) = t * ((x : G) * t * (x : G)⁻¹))
    (hκker : κ.ker =
      (Subgroup.centralizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (E : Set G)))
    (hκsurj : Function.Surjective κ)
    (l : G)
    (hlN : l ∈ Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G))
    (hlO : l ∈ Subgroup.centralizer (O : Set G))
    (hlt : Commute l t)
    (hlfree : ∀ x ∈ E, l * x * l⁻¹ = x → x = 1) :
    let J : Subgroup G := E ⊔ Subgroup.zpowers t
    let N : Subgroup G := Subgroup.normalizer (J : Set G)
    let _C : Subgroup G := Subgroup.centralizer (J : Set G)
    let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
    ∃ Q : Subgroup G,
      Q ≤ X ∧ IsPGroup 2 Q ∧ J ≤ Q ∧
      CFSG.ABGLocalTools.IsSylowOf 2 Q X ∧
      (∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R X → R = Q) ∧
      (Q.subgroupOf X).Characteristic ∧
      N ≤ Subgroup.normalizer (Q : Set G) ∧
      Q ⊔ O = X ∧ Q ⊓ O = ⊥ ∧
      Q ≤ Subgroup.centralizer (O : Set G) ∧
      Q ⊓ Subgroup.centralizer ({t} : Set G) = J ∧
      Nat.card Q = Nat.card J * Nat.card E ∧
      ∃ κQ : Q →* E,
        (∀ x : Q, ((κQ x : E) : G) =
          t * ((x : G) * t * (x : G)⁻¹)) ∧
        κQ.ker = J.subgroupOf Q ∧ Function.Surjective κQ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let C : Subgroup G := Subgroup.centralizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  have hJpowJ : ∀ j ∈ J, j ^ 2 = 1 := hJpow
  have hNE_N : N ≤ Subgroup.normalizer (E : Set G) := hNE
  have hOC_C : O ≤ C := hOC
  have hNO_N : N ≤ Subgroup.normalizer (O : Set G) := hNO
  have hJO_C : J ⊔ O = C := hJO
  have hJOdisj_J : J ⊓ O = ⊥ := hJOdisj
  have hκker_X : κ.ker = C.subgroupOf X := hκker
  have hlN_N : l ∈ N := hlN
  have hJC : J ≤ C := by
    rw [← hJO_C]
    exact le_sup_left
  have hJab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hJC ha) b hb).symm
  have hEJ : E ≤ J := le_sup_left
  have hJCE : J ≤ Subgroup.centralizer (E : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_iff.mp (hJC hj) e (hEJ he)
  have hJN : J ≤ N := Subgroup.le_normalizer
  have hJX : J ≤ X := by
    intro j hj
    exact ⟨hJN hj, hJCE hj⟩
  have hOCJ : O ≤ Subgroup.centralizer (J : Set G) := hOC_C
  have hJCO : J ≤ Subgroup.centralizer (O : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact (Subgroup.mem_centralizer_iff.mp (hOCJ ho) j hj).symm
  have hCX : C ≤ X := by
    intro c hc
    change c ∈ N ⊓ Subgroup.centralizer (E : Set G)
    refine ⟨?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer (J : Set G) hc
    · change c ∈ Subgroup.centralizer (E : Set G)
      change c ∈ Subgroup.centralizer (J : Set G) at hc
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_iff.mp hc e (hEJ he)
  have hOX : O ≤ X := hOC_C.trans hCX
  have hNCentE : N ≤ Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) := by
    refine hNE_N.trans ?_
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (E : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G))
  have hNCGO : N ≤ Subgroup.normalizer (Subgroup.centralizer (O : Set G) : Set G) := by
    refine hNO_N.trans ?_
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (O : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (O : Set G))
  have hNX : N ≤ Subgroup.normalizer (X : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change x ∈ N ⊓ Subgroup.centralizer (E : Set G) ↔
      n * x * n⁻¹ ∈ N ⊓ Subgroup.centralizer (E : Set G)
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxN, hxE⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hn) x).mp hxN,
        (Subgroup.mem_normalizer_iff.mp (hNCentE hn) x).mp hxE⟩
    · rintro ⟨hxN, hxE⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hn) x).mpr hxN,
        (Subgroup.mem_normalizer_iff.mp (hNCentE hn) x).mpr hxE⟩
  have hXCentO : X ≤ Subgroup.normalizer (Subgroup.centralizer (O : Set G) : Set G) :=
    (by exact inf_le_left : X ≤ N).trans hNCGO
  let Y : Subgroup G := X ⊓ Subgroup.centralizer (O : Set G)
  have hNY : N ≤ Subgroup.normalizer (Y : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [show Y = X ⊓ Subgroup.centralizer (O : Set G) from rfl, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxX, hxO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hNX hn) x).mp hxX,
        (Subgroup.mem_normalizer_iff.mp (hNCGO hn) x).mp hxO⟩
    · rintro ⟨hxX, hxO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hNX hn) x).mpr hxX,
        (Subgroup.mem_normalizer_iff.mp (hNCGO hn) x).mpr hxO⟩
  have hYX : Y ≤ X := by
    rw [show Y = X ⊓ Subgroup.centralizer (O : Set G) from rfl]
    exact inf_le_left
  have hYCO : Y ≤ Subgroup.centralizer (O : Set G) := by
    rw [show Y = X ⊓ Subgroup.centralizer (O : Set G) from rfl]
    exact inf_le_right
  have hJY : J ≤ Y := by
    intro j hj
    exact ⟨hJX hj, hJCO hj⟩
  have hYnormal : (Y.subgroupOf X).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [show Y = X ⊓ Subgroup.centralizer (O : Set G) from rfl, Subgroup.mem_inf]
    constructor
    · rintro ⟨hyX, hyO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hNX hx.1) y).mp hyX,
        (Subgroup.mem_normalizer_iff.mp (hXCentO hx) y).mp hyO⟩
    · rintro ⟨hyX, hyO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hNX hx.1) y).mpr hyX,
        (Subgroup.mem_normalizer_iff.mp (hXCentO hx) y).mpr hyO⟩
  let ιYX : Y →* X := Subgroup.inclusion hYX
  have hlNX : l ∈ Subgroup.normalizer (X : Set G) := hNX hlN_N
  let φl : MulAut E := Subgroup.normalizerMonoidHom E ⟨l, hNE_N hlN_N⟩
  have hφl_apply : ∀ e : E, ((φl e : E) : G) = l * (e : G) * l⁻¹ := fun e =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨l, hNE_N hlN_N⟩ e
  have hκconjE : ∀ x : X,
      κ (⟨l * (x : G) * l⁻¹,
        (Subgroup.mem_normalizer_iff.mp hlNX x).mp x.2⟩ : X) = φl (κ x) := by
    intro x
    apply Subtype.ext
    rw [hφl_apply]
    calc ((κ ⟨l * (x : G) * l⁻¹,
          (Subgroup.mem_normalizer_iff.mp hlNX x).mp x.2⟩ : E) : G)
        = t * ((l * (x : G) * l⁻¹) * t * (l * (x : G) * l⁻¹)⁻¹) :=
          hκformula ⟨l * (x : G) * l⁻¹,
            (Subgroup.mem_normalizer_iff.mp hlNX x).mp x.2⟩
      _ = l * (t * ((x : G) * t * (x : G)⁻¹)) * l⁻¹ := by
          have h2 : l⁻¹ * t = t * l⁻¹ := by
            calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
              _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt.eq]
              _ = t * l⁻¹ := by group
          calc t * (l * (x : G) * l⁻¹ * t * (l * (x : G) * l⁻¹)⁻¹)
              = t * l * (x : G) * (l⁻¹ * t) * l * (x : G)⁻¹ * l⁻¹ := by group
            _ = t * l * (x : G) * (t * l⁻¹) * l * (x : G)⁻¹ * l⁻¹ := by rw [h2]
            _ = l * t * (x : G) * t * (x : G)⁻¹ * l⁻¹ := by
                rw [← hlt.eq]
                group
            _ = l * (t * ((x : G) * t * (x : G)⁻¹)) * l⁻¹ := by group
      _ = l * ((κ x : E) : G) * l⁻¹ := by rw [hκformula x]
  have hlift : ∀ x : X, ∃ y : Y, κ (ιYX y) = κ x := by
    intro x
    obtain ⟨s, hsE, hs⟩ :=
      exists_eq_conj_mul_inv_of_fixedPointFree (G := G) (T := E) (b := l)
        (hNE_N hlN_N) hlfree (κ x : G) (κ x).2
    obtain ⟨x₀, hx₀⟩ := hκsurj ⟨s, hsE⟩
    have hx₀X : (x₀ : G) ∈ X := x₀.2
    have hx₀N : (x₀ : G) ∈ N := hx₀X.1
    have hconjX : l * (x₀ : G) * l⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hlNX x₀).mp x₀.2
    have hx₀CGO : (x₀ : G) ∈ Subgroup.normalizer
        (Subgroup.centralizer (O : Set G) : Set G) := hNCGO hx₀N
    have hlOinv : l⁻¹ ∈ Subgroup.centralizer (O : Set G) :=
      (Subgroup.centralizer (O : Set G)).inv_mem hlO
    have hconjO : x₀ * l⁻¹ * x₀⁻¹ ∈ Subgroup.centralizer (O : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hx₀CGO l⁻¹).mp hlOinv
    have hyO : l * (x₀ * l⁻¹ * x₀⁻¹) ∈ Subgroup.centralizer (O : Set G) :=
      (Subgroup.centralizer (O : Set G)).mul_mem hlO hconjO
    have hyX : l * (x₀ : G) * l⁻¹ * (x₀ : G)⁻¹ ∈ X :=
      X.mul_mem hconjX (X.inv_mem x₀.2)
    let y : Y := ⟨l * (x₀ : G) * l⁻¹ * (x₀ : G)⁻¹, by
      rw [show Y = X ⊓ Subgroup.centralizer (O : Set G) from rfl]
      exact ⟨hyX, by simpa [mul_assoc] using hyO⟩⟩
    refine ⟨y, ?_⟩
    have hyformula : κ (ιYX y) =
        φl (κ x₀) * (κ x₀)⁻¹ := by
      have hyXeq : (ιYX y : X) =
          (⟨l * (x₀ : G) * l⁻¹, hconjX⟩ : X) * x₀⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hyXeq, map_mul, map_inv, hκconjE]
    apply Subtype.ext
    calc ((κ (ιYX y) : E) : G)
        = ((φl (κ x₀) * (κ x₀)⁻¹ : E) : G) := by rw [hyformula]
      _ = l * (κ x₀ : E) * l⁻¹ * (κ x₀ : E)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hφl_apply]
      _ = l * s * l⁻¹ * s⁻¹ := by
          rw [hx₀]
          rfl
      _ = ((κ x : E) : G) := hs.symm
  have hJsubC_normal : (J.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.centralizer_le_normalizer (J : Set G))
  have hdecompC : ∀ z : C, ∃ j o : C,
      j ∈ J.subgroupOf C ∧ o ∈ O.subgroupOf C ∧ z = j * o := by
    intro z
    let : (J.subgroupOf C).Normal := hJsubC_normal
    have hJOsub : J.subgroupOf C ⊔ O.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (le_trans le_sup_left (le_of_eq hJO_C))
        (le_trans le_sup_right (le_of_eq hJO_C))]
      rw [hJO_C, Subgroup.subgroupOf_self]
    have hzmem : z ∈ J.subgroupOf C ⊔ O.subgroupOf C := by
      rw [hJOsub]
      exact Subgroup.mem_top z
    obtain ⟨j, hj, o, ho, hjo⟩ :=
      (Subgroup.mem_sup_of_normal_left
        (s := J.subgroupOf C) (t := O.subgroupOf C)).mp hzmem
    exact ⟨j, o, hj, ho, hjo.symm⟩
  have hXYO : X ≤ Y ⊔ O := by
    intro x hx
    have hxX : x ∈ X := hx
    obtain ⟨y, hyκ⟩ := hlift ⟨x, hxX⟩
    let xX : X := ⟨x, hxX⟩
    let zX : X := (ιYX y)⁻¹ * xX
    have hzker : zX ∈ κ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyκ, inv_mul_cancel]
    have hzC : (zX : G) ∈ C := by
      rw [hκker_X] at hzker
      exact Subgroup.mem_subgroupOf.mp hzker
    let zC : C := ⟨(zX : G), hzC⟩
    obtain ⟨j, o, hj, ho, hzjo⟩ := hdecompC zC
    have hzval : (zX : G) = (j : G) * (o : G) := by
      simpa [zC] using congrArg (fun t : C => (t : G)) hzjo
    have hx_eq : x = ((y : G) * (j : G)) * (o : G) := by
      have h1 : x = (y : G) * (zX : G) := by
        simp [zX, xX, ιYX]
      rw [h1, hzval]
      group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup
      (Y.mul_mem y.2 (hJY (Subgroup.mem_subgroupOf.mp hj)))
      (Subgroup.mem_subgroupOf.mp ho)
  let Z : Subgroup Y := O.subgroupOf Y
  have hZcenter : Z ≤ Subgroup.center Y := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hYCO y.2) (z : G)
      (Subgroup.mem_subgroupOf.mp hz)).symm
  have hZodd : Odd (Nat.card Z) := by
    have hZcard : Nat.card Z = Nat.card (O ⊓ Y : Subgroup G) := by
      dsimp [Z]
      rw [← Subgroup.inf_subgroupOf_right O Y]
      rw [← Subgroup.card_map_of_injective (K := (O ⊓ Y).subgroupOf Y) Y.subtype_injective]
      rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    rw [hZcard]
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hYZexp : ∀ y : Y, y ^ 4 ∈ Z := by
    intro y
    have hyX : (y : G) ∈ X := hYX y.2
    let xX : X := ιYX y
    have hxX : (xX : G) = (y : G) := rfl
    have hκx2 : κ (⟨(xX : G) ^ 2, X.pow_mem xX.2 2⟩ : X) = 1 := by
      have hpowG : ((κ xX : E) : G) * ((κ xX : E) : G) = 1 := by
        have hmem : ((κ xX : E) : G) ∈ J := hEJ (κ xX).2
        simpa [pow_two] using hJpowJ ((κ xX : E) : G) hmem
      have hpow : (κ xX) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hpowG
      change κ ⟨(xX : G) ^ 2, X.pow_mem xX.2 2⟩ = 1
      rw [show (⟨(xX : G) ^ 2, X.pow_mem xX.2 2⟩ : X) = xX ^ 2 from rfl,
        map_pow]
      exact hpow
    have hy2C : ((y : G) ^ 2) ∈ C := by
      have hx2C : ((xX : G) ^ 2) ∈ C := by
        have hx2ker : (⟨(xX : G) ^ 2, X.pow_mem xX.2 2⟩ : X) ∈ κ.ker := by
          simpa [MonoidHom.mem_ker] using hκx2
        rw [hκker_X] at hx2ker
        exact Subgroup.mem_subgroupOf.mp hx2ker
      simpa [hxX] using hx2C
    let zC : C := ⟨((y : G) ^ 2), hy2C⟩
    obtain ⟨j, o, hj, ho, hzjo⟩ := hdecompC zC
    have hzval : ((y : G) ^ 2) = (j : G) * (o : G) := by
      simpa [zC] using congrArg (fun t : C => (t : G)) hzjo
    have hy4 : ((y : G) ^ 4) = ((o : C) : G) ^ 2 := by
      calc ((y : G) ^ 4) = (((y : G) ^ 2) ^ 2) := by group
        _ = (((j : C) : G) * ((o : C) : G)) ^ 2 := by rw [hzval]
        _ = ((j : C) : G) ^ 2 * ((o : C) : G) ^ 2 := by
          have hcomm : ((j : C) : G) * ((o : C) : G) =
              ((o : C) : G) * ((j : C) : G) := by
            exact Subgroup.mem_centralizer_iff.mp
              (hOCJ (Subgroup.mem_subgroupOf.mp ho))
              ((j : C) : G) (Subgroup.mem_subgroupOf.mp hj)
          calc (((j : C) : G) * ((o : C) : G)) ^ 2
              = ((j : C) : G) * (((o : C) : G) * ((j : C) : G)) *
                  ((o : C) : G) := by
                rw [pow_two]
                group
            _ = ((j : C) : G) * (((j : C) : G) * ((o : C) : G)) *
                  ((o : C) : G) := by rw [← hcomm]
            _ = ((j : C) : G) ^ 2 * ((o : C) : G) ^ 2 := by
                rw [pow_two, pow_two]
                group
        _ = ((o : C) : G) ^ 2 := by
          have hj2 : ((j : C) : G) ^ 2 = 1 :=
            hJpowJ _ (Subgroup.mem_subgroupOf.mp hj)
          rw [hj2, one_mul]
    have hoO : ((o : C) : G) ∈ O := Subgroup.mem_subgroupOf.mp ho
    rw [show Z = O.subgroupOf Y from rfl]
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa [Subgroup.coe_pow, hy4] using O.pow_mem hoO 2)
  have hZnormal : Z.Normal := Subgroup.normal_of_le_center hZcenter
  let : Z.Normal := hZnormal
  have hYquot2 : IsPGroup 2 (Y ⧸ Z) := by
    apply IsPGroup.of_exponent_dvd_pow (n := 2)
    have hexp : Monoid.exponent (Y ⧸ Z) ∣ 4 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun q => by
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff (N := Z) (y ^ 4)).mpr (hYZexp y))
    simpa using hexp
  obtain ⟨n, hn⟩ := hYquot2.exists_card_eq
  have hZindex : Z.index = 2 ^ n := by
    rw [Subgroup.index_eq_card]
    exact hn
  have hcopZ : Nat.Coprime (Nat.card Z) Z.index := by
    rw [hZindex]
    exact hZodd.coprime_two_right.pow_right n
  let QY : Subgroup Y := CFSG.Semidihedral.centralHallComplement Z hZcenter hcopZ
  let Q : Subgroup G := QY.map Y.subtype
  have hQYcard : Nat.card QY = Z.index :=
    CFSG.Semidihedral.centralHallComplement_card Z hZcenter hcopZ
  have hQcard : Nat.card Q = 2 ^ n := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hQYcard, hZindex]
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card hQcard
  have hQleY : Q ≤ Y := Subgroup.map_subtype_le QY
  have hQleX : Q ≤ X := hQleY.trans hYX
  have hQYchar : QY.Characteristic :=
    CFSG.Semidihedral.centralHallComplement_characteristic Z hZcenter hcopZ
  have hQYsup : Z ⊔ QY = ⊤ :=
    CFSG.Semidihedral.centralHallComplement_sup Z hZcenter hcopZ
  have hQYinf : Z ⊓ QY = ⊥ :=
    CFSG.Semidihedral.centralHallComplement_inf Z hZcenter hcopZ
  have hYQO' : Y ≤ Q ⊔ O := by
    intro y hy
    let yY : Y := ⟨y, hy⟩
    obtain ⟨⟨z, q⟩, hzq⟩ :=
      (CFSG.Semidihedral.centralHallComplementMulEquiv Z hZcenter hcopZ).surjective yY
    have hzqG : (z : G) * (q : G) = y := by
      have h := congrArg (fun t : Y => (t : G)) hzq
      rw [CFSG.Semidihedral.centralHallComplementMulEquiv_apply] at h
      simpa using h
    have hzq_comm : (z : G) * (q : G) = (q : G) * (z : G) := by
      exact congrArg (fun t : Y => (t : G))
        (CFSG.Semidihedral.centralHall_commute hZcenter z.2).eq
    rw [← hzqG, hzq_comm]
    exact Subgroup.mul_mem_sup
      (Subgroup.mem_map_of_mem Y.subtype q.2)
      (Subgroup.mem_subgroupOf.mp z.2)
  have hQOsup : Q ⊔ O = X := by
    apply le_antisymm
    · exact sup_le hQleX hOX
    · intro x hx
      have hx1 : x ∈ Y ⊔ O := hXYO hx
      have hle : Y ⊔ O ≤ Q ⊔ O := sup_le hYQO' le_sup_right
      exact hle hx1
  have hQOdisj : Q ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx with ⟨hxQ, hxO⟩
    obtain ⟨q, hqQY, hq⟩ := Subgroup.mem_map.mp hxQ
    have hqZ : q ∈ Z := by
      rw [show Z = O.subgroupOf Y from rfl]
      exact Subgroup.mem_subgroupOf.mpr (by rw [← hq] at hxO; exact hxO)
    have hqbot : q ∈ Z ⊓ QY := ⟨hqZ, hqQY⟩
    rw [hQYinf] at hqbot
    have hq1 : q = 1 := Subgroup.mem_bot.mp hqbot
    rw [show x = (q : G) from hq.symm, hq1]
    rfl
  have hQCO : Q ≤ Subgroup.centralizer (O : Set G) := hQleY.trans hYCO
  have hforwardNQ : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := by
    intro n hn q hq
    obtain ⟨qy, hqy, hqeq⟩ := Subgroup.mem_map.mp hq
    let φ : MulAut Y := Subgroup.normalizerMonoidHom Y ⟨n, hNY hn⟩
    have hφ : QY.map φ.toMonoidHom = QY :=
      (Subgroup.characteristic_iff_map_eq.mp hQYchar) φ
    have hmem : φ qy ∈ QY := by
      rw [← hφ]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hqy
    refine Subgroup.mem_map.mpr ⟨φ qy, hmem, ?_⟩
    rw [← hqeq]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨n, hNY hn⟩ qy
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hforwardNQ n hn q hq
    · intro hq
      have := hforwardNQ n⁻¹ (N.inv_mem hn) (n * q * n⁻¹) hq
      simpa [mul_assoc] using this
  have hQnormalX : (Q.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((by exact inf_le_left : X ≤ N).trans hNQ)
  have hQOsub : (Q.subgroupOf X) ⊔ (O.subgroupOf X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQleX hOX, hQOsup, Subgroup.subgroupOf_self]
  have hdisjQXOX : Disjoint (Q.subgroupOf X) (O.subgroupOf X) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have hqG : (a : G) ∈ Q := Subgroup.mem_subgroupOf.mp ha.1
    have hoG : (a : G) ∈ O := Subgroup.mem_subgroupOf.mp ha.2
    have hbot : (a : G) ∈ (⊥ : Subgroup G) := by
      rw [← hQOdisj]
      exact ⟨hqG, hoG⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hbot))
  have hmulQXOX : ((Q.subgroupOf X : Subgroup X) : Set X) *
      ((O.subgroupOf X : Subgroup X) : Set X) = Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hxmem : x ∈ Q.subgroupOf X ⊔ O.subgroupOf X := by
        rw [hQOsub]
        exact Subgroup.mem_top x
      obtain ⟨q, hq, o, ho, hqo⟩ :=
        (Subgroup.mem_sup_of_normal_left
          (s := Q.subgroupOf X) (t := O.subgroupOf X)).mp hxmem
      exact Set.mem_mul.mpr ⟨q, hq, o, ho, hqo⟩
  have hcomplX : (Q.subgroupOf X).IsComplement' (O.subgroupOf X) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjQXOX hmulQXOX
  have hcardQX : Nat.card (Q.subgroupOf X) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleX).toEquiv
  have hcardOX : Nat.card (O.subgroupOf X) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOX).toEquiv
  have hcardX : Nat.card X = Nat.card Q * Nat.card O := by
    have h := hcomplX.card_mul_card
    rw [hcardQX, hcardOX] at h
    exact h.symm
  have hrelmul : Q.relIndex X * Nat.card Q = Nat.card X := by
    simpa [inf_eq_left.mpr hQleX] using Subgroup.relIndex_mul_card Q X
  have hQrel : Q.relIndex X = Nat.card O := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card Q from Nat.card_pos)
    rw [hrelmul, hcardX]
    exact mul_comm _ _
  have hQsylow : CFSG.ABGLocalTools.IsSylowOf 2 Q X := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hQleX, hQ2, by rw [hQrel]; exact hOodd.not_two_dvd_nat⟩
  have hJnormalX : (J.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      show X ≤ Subgroup.normalizer (J : Set G)
      exact fun x hx => hx.1)
  have hJpg : IsPGroup 2 (J.subgroupOf X) := by
    apply isPGroup_iff_exists_pow_pow_eq_one.mpr
    refine ⟨1, fun j => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (j : G) ^ 2 = 1
    exact hJpowJ (j : G) (Subgroup.mem_subgroupOf.mp j.2)
  obtain ⟨Qx, hQx⟩ := hQsylow.exists_sylow_eq_subgroupOf
  have hJQx : J.subgroupOf X ≤ (Qx : Subgroup X) :=
    IsPGroup.le_sylow_of_normal (p := 2) (N := J.subgroupOf X) hJpg Qx
  have hJQ : J ≤ Q := by
    intro j hj
    have hmem : (⟨j, hJX hj⟩ : X) ∈ J.subgroupOf X := hj
    have hmemQx : (⟨j, hJX hj⟩ : X) ∈ (Qx : Subgroup X) := hJQx hmem
    rw [hQx] at hmemQx
    exact Subgroup.mem_subgroupOf.mp hmemQx
  have hQxnorm : (Qx : Subgroup X).Normal := by
    rw [hQx]
    exact hQnormalX
  have hQchar : (Q.subgroupOf X).Characteristic := by
    have h := Sylow.characteristic_of_normal Qx hQxnorm
    rwa [hQx] at h
  have huniqR : ∀ R : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 R X → R = Q := by
    intro R hR
    let : Unique (Sylow 2 X) := Sylow.unique_of_normal Qx hQxnorm
    obtain ⟨Rx, hRx⟩ := hR.exists_sylow_eq_subgroupOf
    have hRxQx : Rx = Qx := Subsingleton.elim Rx Qx
    have hsub : R.subgroupOf X = Q.subgroupOf X := by
      rw [← hRx, ← hQx, hRxQx]
    have hmap := congrArg (Subgroup.map X.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hR.le,
      Subgroup.map_subgroupOf_eq_of_le hQleX] at hmap
  let κQ : Q →* E := κ.comp (Subgroup.inclusion hQleX)
  have hκQformula : ∀ x : Q, ((κQ x : E) : G) =
      t * ((x : G) * t * (x : G)⁻¹) := by
    intro x
    exact hκformula (Subgroup.inclusion hQleX x)
  have hQinfC : Q ⊓ C = J := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxQ, hxC⟩
      let xC : C := ⟨x, hxC⟩
      obtain ⟨j, o, hj, ho, hxjo⟩ := hdecompC xC
      have hxval : x = (j : G) * (o : G) := by
        simpa [xC] using congrArg (fun t : C => (t : G)) hxjo
      have hjQ : (j : G) ∈ Q := hJQ (Subgroup.mem_subgroupOf.mp hj)
      have hoQ : (o : G) ∈ Q := by
        have : (o : G) = (j : G)⁻¹ * x := by rw [hxval]; group
        rw [this]
        exact Q.mul_mem (Q.inv_mem hjQ) hxQ
      have hoO : (o : G) ∈ O := Subgroup.mem_subgroupOf.mp ho
      have hobot : (o : G) ∈ (⊥ : Subgroup G) := by
        rw [← hQOdisj]
        exact ⟨hoQ, hoO⟩
      have ho1 : (o : G) = 1 := Subgroup.mem_bot.mp hobot
      rw [hxval, ho1, mul_one]
      exact Subgroup.mem_subgroupOf.mp hj
    · intro x hx
      exact ⟨hJQ hx, hJC hx⟩
  have hκQker : κQ.ker = J.subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker]
    constructor
    · intro hq
      have hqker : (Subgroup.inclusion hQleX q) ∈ κ.ker := hq
      rw [hκker_X] at hqker
      have hqC : (q : G) ∈ C := Subgroup.mem_subgroupOf.mp hqker
      have hqQC : (q : G) ∈ Q ⊓ C := ⟨q.2, hqC⟩
      rw [hQinfC] at hqQC
      exact Subgroup.mem_subgroupOf.mpr hqQC
    · intro hq
      have hqJ : (q : G) ∈ J := Subgroup.mem_subgroupOf.mp hq
      have hqC : (q : G) ∈ C := hJC hqJ
      have hqker : (Subgroup.inclusion hQleX q) ∈ κ.ker := by
        rw [hκker_X]
        exact Subgroup.mem_subgroupOf.mpr hqC
      exact hqker
  have hκQsurj : Function.Surjective κQ := by
    intro e
    obtain ⟨x, hx⟩ := hκsurj e
    let xX : X := x
    have hxX : κ xX = e := hx
    have hxmem : xX ∈ Q.subgroupOf X ⊔ O.subgroupOf X := by
      rw [hQOsub]
      exact Subgroup.mem_top xX
    obtain ⟨q, hq, o, ho, hqo⟩ :=
      (Subgroup.mem_sup_of_normal_left
        (s := Q.subgroupOf X) (t := O.subgroupOf X)).mp hxmem
    let qQ : Q := ⟨q, Subgroup.mem_subgroupOf.mp hq⟩
    have hoO : (o : G) ∈ O := Subgroup.mem_subgroupOf.mp ho
    have hoC : (o : G) ∈ C := hOC_C hoO
    have hoker : (o : X) ∈ κ.ker := by
      rw [hκker_X]
      exact Subgroup.mem_subgroupOf.mpr hoC
    have hoker1 : κ (o : X) = 1 := MonoidHom.mem_ker.mp hoker
    refine ⟨qQ, ?_⟩
    apply Subtype.ext
    have hqX : (Subgroup.inclusion hQleX qQ : X) = q := rfl
    have hxeq : κ (Subgroup.inclusion hQleX qQ : X) = κ xX := by
      have h := congrArg (fun z : X => κ z) hqo
      rw [map_mul, hoker1, mul_one] at h
      rw [hqX]
      exact h
    calc ((κQ qQ : E) : G) = ((κ (Subgroup.inclusion hQleX qQ) : E) : G) := rfl
      _ = ((κ xX : E) : G) := by rw [hxeq]
      _ = (e : G) := congrArg (fun t : E => (t : G)) hxX
  have htJ : t ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have ht2 : t * t = 1 := by
    have := hJpowJ t htJ
    simpa [pow_two] using this
  have hQt : Q ⊓ Subgroup.centralizer ({t} : Set G) = J := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxQ, hxt⟩
      let q : Q := ⟨x, hxQ⟩
      have hcomm : (x : G) * t = t * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hxt
      have hcomm' : (q : G) * t = t * (q : G) := hcomm
      have hqker : q ∈ κQ.ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        rw [hκQformula]
        calc t * ((q : G) * t * (q : G)⁻¹)
            = t * (q : G) * t * (q : G)⁻¹ := by group
          _ = (q : G) * t * t * (q : G)⁻¹ := by
              rw [hcomm'.symm]
          _ = (q : G) * (t * t) * (q : G)⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      rw [hκQker] at hqker
      exact Subgroup.mem_subgroupOf.mp hqker
    · intro x hx
      refine ⟨hJQ hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact hJab x hx t htJ
  have hQcardJE : Nat.card Q = Nat.card J * Nat.card E := by
    have hcard1 : Nat.card Q =
        Nat.card (Q ⧸ κQ.ker) * Nat.card κQ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup κQ.ker
    have hquotE : Nat.card (Q ⧸ κQ.ker) = Nat.card E := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange κQ).toEquiv]
      rw [MonoidHom.range_eq_top.mpr hκQsurj, Subgroup.card_top]
    have hkerJ : Nat.card κQ.ker = Nat.card J := by
      rw [hκQker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJQ).toEquiv
    rw [hquotE, hkerJ] at hcard1
    rw [hcard1, mul_comm]
  exact ⟨Q, hQleX, hQ2, hJQ, hQsylow, huniqR, hQchar, hNQ, hQOsup,
    hQOdisj, hQCO, hQt, hQcardJE, κQ, hκQformula, hκQker, hκQsurj⟩

end CFSG
