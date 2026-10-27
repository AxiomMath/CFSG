module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseAGeneric
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGen
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelFacts
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (unipAll)
open scoped Pointwise

structure CaseAData {G : Type} [Group G] {A : Subgroup G} (d : Datum A) (W : Subgroup G)
    (F : Type) [Field F] where
  S₁ : Subgroup G
  S₀ : Subgroup G
  w₁ : G
  e : ↥S₀ ≃* ↥(unipAll F)
  sylow : IsSylowOf 2 S₁ (normalizer (W : Set G))
  S₀_le : S₀ ≤ S₁
  S₁_le : S₁ ≤ normalizer (S₀ : Set G)
  W_le : W ≤ S₀
  sup_eq : S₁ = S₀ ⊔ zpowers w₁
  inf_eq : S₀ ⊓ zpowers w₁ = ⊥
  t_mem : d.t ∈ zpowers w₁
  V_le : d.V ≤ S₀
  mem_W_iff : ∀ s : S₀, (s : G) ∈ W ↔ e s ∈ radOne F

@[expose] noncomputable def unipFieldHom {F : Type} [Field F] [CharP F 2] :
    MulAut ↥(unipAll F) →* RingAut F :=
  MonoidHom.mk' autField autField_mul

@[expose] noncomputable def unipSwapHom {F : Type} [Field F] [CharP F 2] :
    MulAut ↥(unipAll F) →* Multiplicative (ZMod 2) where
  toFun α := if autSwap α then Multiplicative.ofAdd 1 else 1
  map_one' := by simp [autSwap_eq autData_one]
  map_mul' α β := by
    rw [autSwap_mul]
    cases autSwap α <;> cases autSwap β <;> decide

theorem unipSwapHom_eq_one_iff {F : Type} [Field F] [CharP F 2] (α : MulAut ↥(unipAll F)) :
    unipSwapHom α = 1 ↔ autSwap α = false := by
  show (if autSwap α then Multiplicative.ofAdd (1 : ZMod 2) else 1) = 1 ↔ _
  cases autSwap α <;> decide

namespace CaseAData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {W : Subgroup G}
  {F : Type} [Field F] (C : CaseAData d W F)

theorem w₁_mem : C.w₁ ∈ C.S₁ := C.sup_eq ▸ mem_sup_right (mem_zpowers _)

theorem t_mem_S₁ : d.t ∈ C.S₁ := C.sup_eq ▸ mem_sup_right C.t_mem

theorem t_not_mem_S₀ : d.t ∉ C.S₀ := fun h => by
  have h1 : d.t ∈ C.S₀ ⊓ zpowers C.w₁ := ⟨h, C.t_mem⟩
  rw [C.inf_eq, mem_bot] at h1
  have := d.sector.t_order
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem S₁_le_normalizer : C.S₁ ≤ normalizer (W : Set G) := C.sylow.le

theorem isPGroup_S₁ : IsPGroup 2 C.S₁ := C.sylow.isPGroup

theorem mem_S₁_of_mem_normalizer [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (hST : C.S₁ ≤ T) {x : G} (hxT : x ∈ T) (hxN : x ∈ normalizer (W : Set G)) : x ∈ C.S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := C.sylow.eq_of_le (Q := T ⊓ normalizer (W : Set G))
    (le_inf hST C.sylow.le) inf_le_right hT.to_inf_left
  rw [← h]
  exact ⟨hxT, hxN⟩

@[expose] def Zc : Subgroup G := ((radCenter F).comap C.e.toMonoidHom).map C.S₀.subtype

theorem mem_Zc_iff {x : G} : x ∈ C.Zc ↔ ∃ hx : x ∈ C.S₀, C.e ⟨x, hx⟩ ∈ radCenter F := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hx, hz⟩
    exact ⟨⟨x, hx⟩, hz, rfl⟩

theorem Zc_le_W : C.Zc ≤ W := by
  rintro x hx
  obtain ⟨hxS, hz⟩ := C.mem_Zc_iff.1 hx
  rw [mem_radCenter] at hz
  exact (C.mem_W_iff ⟨x, hxS⟩).2 ((mem_radOne _).2 hz.2)

theorem card_Zc : Nat.card C.Zc = Nat.card F := by
  rw [Zc, Subgroup.card_map_of_injective C.S₀.subtype_injective, ← card_radCenter (F := F)]
  exact Nat.card_congr ((radCenter F).equivMapOfInjective C.e.symm.toMonoidHom
    C.e.symm.injective |>.toEquiv.trans (Equiv.subtypeEquivRight fun s => by
      constructor
      · rintro ⟨u, hu, rfl⟩
        show C.e (C.e.symm u) ∈ radCenter F
        rw [MulEquiv.apply_symm_apply]
        exact hu
      · intro hs
        exact ⟨C.e s, hs, C.e.symm_apply_apply s⟩)).symm

theorem comm_of_mem_Zc {z s : G} (hz : z ∈ C.Zc) (hs : s ∈ C.S₀) : z * s = s * z := by
  obtain ⟨hzS, hzc⟩ := C.mem_Zc_iff.1 hz
  rw [← center_unipAll, mem_center_iff] at hzc
  have h := hzc (C.e ⟨s, hs⟩)
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (C.e.injective h).symm

@[expose] noncomputable def ρ : ↥(normalizer (C.S₀ : Set G)) →* MulAut ↥(unipAll F) :=
  (MulAut.congr C.e).toMonoidHom.comp (normalizerMonoidHom C.S₀)

theorem ρ_apply (x : ↥(normalizer (C.S₀ : Set G))) (s : C.S₀) :
    C.ρ x (C.e s) = C.e ⟨x * s * x⁻¹, (mem_normalizer_iff.1 x.2 s).1 s.2⟩ := by
  show C.e ((normalizerMonoidHom C.S₀ x) (C.e.symm (C.e s))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem ρ_eq_conj (x : ↥(normalizer (C.S₀ : Set G))) (hx : (x : G) ∈ C.S₀) :
    C.ρ x = MulAut.conj (C.e ⟨x, hx⟩) := by
  refine MulEquiv.ext fun u => ?_
  obtain ⟨s, rfl⟩ := C.e.surjective u
  rw [C.ρ_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg C.e (Subtype.ext (by simp))

theorem ρ_mem_radOne_iff (x : ↥(normalizer (C.S₀ : Set G))) (s : C.S₀) :
    C.ρ x (C.e s) ∈ radOne F ↔ (x : G) * s * (x : G)⁻¹ ∈ W := by
  rw [C.ρ_apply, ← C.mem_W_iff]
  exact Iff.rfl

variable [CharP F 2]

theorem autField_ρ_of_mem (x : ↥(normalizer (C.S₀ : Set G))) (hx : (x : G) ∈ C.S₀) :
    autField (C.ρ x) = 1 := by
  rw [C.ρ_eq_conj x hx, autField_conj]

omit [CharP F 2] in
theorem autSwap_ρ_of_mem (x : ↥(normalizer (C.S₀ : Set G))) (hx : (x : G) ∈ C.S₀) :
    autSwap (C.ρ x) = false := by
  rw [C.ρ_eq_conj x hx, autSwap_conj]

theorem autSwap_ρ_eq_false_iff [Finite G] [Finite F] (x : ↥(normalizer (C.S₀ : Set G))) :
    autSwap (C.ρ x) = false ↔ (x : G) ∈ normalizer (W : Set G) := by
  constructor
  · intro hsw
    have hmap := map_radOne_aut (C.ρ x)
    rw [hsw] at hmap
    simp only [Bool.false_eq_true, ↓reduceIte] at hmap
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    have hwS : w ∈ C.S₀ := C.W_le hw
    have h1 : C.ρ x (C.e ⟨w, hwS⟩) ∈ (radOne F).map (C.ρ x).toMonoidHom :=
      ⟨C.e ⟨w, hwS⟩, (C.mem_W_iff _).1 hw, rfl⟩
    rw [hmap] at h1
    exact (C.ρ_mem_radOne_iff x ⟨w, hwS⟩).1 h1
  · intro hxN
    by_contra hne
    have htrue : autSwap (C.ρ x) = true := by simpa using hne
    have hmap := map_radOne_aut (C.ρ x)
    rw [htrue] at hmap
    simp only [↓reduceIte] at hmap
    have hle : (radOne F).map (C.ρ x).toMonoidHom ≤ radOne F := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨s, rfl⟩ := C.e.surjective u
      have hu' : (s : G) ∈ W := (C.mem_W_iff s).2 hu
      show C.ρ x (C.e s) ∈ radOne F
      exact (C.ρ_mem_radOne_iff x s).2 ((mem_normalizer_iff.1 hxN s).1 hu')
    rw [hmap] at hle
    have heq : radTwo F = radOne F := Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_radOne, card_radTwo])
    exact radOne_ne_radTwo heq.symm

@[expose] def tN : ↥(normalizer (C.S₀ : Set G)) := ⟨d.t, C.S₁_le C.t_mem_S₁⟩

theorem autField_ρ_t_ne_one [Finite G] [Finite F] {Vi V₁ V₂ : Subgroup G} {q : ℕ} (hq : 2 ≤ q)
    (hR : Radicals d.V V₁ V₂ q) (hW : Vi = V₁ ∨ Vi = V₂)
    (hcomm : ∀ v ∈ Vi, ∃ x ∈ W, d.t * x * d.t * x⁻¹ = v) :
    autField (C.ρ C.tN) ≠ 1 := by
  intro hf
  set α := C.ρ C.tN with hα
  have htN : d.t ∈ normalizer (W : Set G) := C.S₁_le_normalizer C.t_mem_S₁
  have hsw : autSwap α = false := (C.autSwap_ρ_eq_false_iff C.tN).2 htN
  have hα2 : ∀ g, α (α g) = g := by
    intro g
    have ht2 : C.tN * C.tN = 1 := Subtype.ext d.t_mul_self
    have : α * α = 1 := by rw [hα, ← map_mul, ht2, map_one]
    exact DFunLike.congr_fun this g
  have hcoord := coords_eq_of_involution α hα2 hf hsw
  have hZ : ∀ x ∈ W, d.t * x * d.t * x⁻¹ ∈ C.Zc := by
    intro x hx
    have hxS : x ∈ C.S₀ := C.W_le hx
    have htx : d.t * x * d.t⁻¹ ∈ C.S₀ := (mem_normalizer_iff.1 C.tN.2 x).1 hxS
    have hmem : d.t * x * d.t * x⁻¹ ∈ C.S₀ := by
      have := C.S₀.mul_mem htx (C.S₀.inv_mem hxS)
      rwa [inv_eq_of_mul_eq_one_right d.t_mul_self] at this
    refine C.mem_Zc_iff.2 ⟨hmem, ?_⟩
    have e1 : (⟨d.t * x * d.t * x⁻¹, hmem⟩ : C.S₀) =
        ⟨d.t * x * d.t⁻¹, htx⟩ * (⟨x, hxS⟩ : C.S₀)⁻¹ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [inv_eq_of_mul_eq_one_right d.t_mul_self]
    have e2 : C.e ⟨d.t * x * d.t⁻¹, htx⟩ = α (C.e ⟨x, hxS⟩) := (C.ρ_apply C.tN ⟨x, hxS⟩).symm
    rw [e1, map_mul, map_inv, e2, mem_radCenter, coordA_mul, coordB_mul, coordA_inv, coordB_inv,
      (hcoord _).1, (hcoord _).2]
    exact ⟨add_neg_cancel _, add_neg_cancel _⟩
  have hVZ : Vi ≤ C.Zc := fun v hv => by
    obtain ⟨x, hx, rfl⟩ := hcomm v hv
    exact hZ x hx
  obtain ⟨hViV, -, hVic⟩ := hR.property hW
  have hcen : Vi ≤ d.V ⊓ centralizer (d.V : Set G) := fun v hv =>
    ⟨hViV hv, mem_centralizer_iff.2 fun y hy => (C.comm_of_mem_Zc (hVZ hv) (C.V_le hy)).symm⟩
  have h1 := Subgroup.card_le_of_le hcen
  rw [hVic, hR.card_center] at h1
  have h2 : q * 2 ≤ q * q := Nat.mul_le_mul_left q hq
  have h3 : q ^ 2 = q * q := sq q
  omega

theorem mem_S₀_of_autField_eq_one [Finite G] (hψt : autField (C.ρ C.tN) ≠ 1) {x : G}
    (hx : x ∈ C.S₁) (hf : autField (C.ρ ⟨x, C.S₁_le hx⟩) = 1) : x ∈ C.S₀ := by
  have hw₁N : C.w₁ ∈ normalizer (C.S₀ : Set G) := C.S₁_le C.w₁_mem
  have hZN : zpowers C.w₁ ≤ normalizer (C.S₀ : Set G) := (zpowers_le).2 hw₁N
  have hxmul : x ∈ (C.S₀ : Set G) * (zpowers C.w₁ : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left C.S₀ (zpowers C.w₁) hZN, ← C.sup_eq]
    exact hx
  rw [Set.mem_mul] at hxmul
  obtain ⟨s, hs, y, hy, rfl⟩ := hxmul
  have hsN : s ∈ normalizer (C.S₀ : Set G) := C.S₁_le (C.S₀_le hs)
  have hyN : y ∈ normalizer (C.S₀ : Set G) := hZN hy
  have hfy : autField (C.ρ ⟨y, hyN⟩) = 1 := by
    have e : (⟨s * y, C.S₁_le hx⟩ : ↥(normalizer (C.S₀ : Set G))) = ⟨s, hsN⟩ * ⟨y, hyN⟩ := rfl
    rw [e, map_mul, autField_mul, C.autField_ρ_of_mem ⟨s, hsN⟩ hs, one_mul] at hf
    exact hf
  by_contra hcon
  have hy1 : y ≠ 1 := fun h => hcon (by rw [h, mul_one]; exact hs)
  have hZp : IsPGroup 2 (zpowers C.w₁) :=
    C.isPGroup_S₁.to_le ((zpowers_le).2 C.w₁_mem)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hZp ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hk
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := by
    rcases k with _ | a
    · exact absurd (orderOf_eq_one_iff.1 (by rw [hk, pow_zero])) hy1
    · exact ⟨a, rfl⟩
  set z := y ^ (2 ^ a) with hz
  have hz2 : z * z = 1 := by
    rw [hz, ← pow_add, ← two_mul, ← pow_succ', ← hk, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rw [hz]
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hk, pow_succ]
    have : 0 < 2 ^ a := by positivity
    omega
  have hzZ : z ∈ zpowers C.w₁ := pow_mem hy _
  have hzt : z = d.t := by
    have ht1 : d.t ≠ 1 := fun h => C.t_not_mem_S₀ (h ▸ C.S₀.one_mem)
    have h := eq_one_or_eq_of_mul_self (M := ↥(zpowers C.w₁)) (a := ⟨z, hzZ⟩) (b := ⟨d.t, C.t_mem⟩)
      (Subtype.ext hz2) (Subtype.ext d.t_mul_self) (fun h => ht1 (congrArg Subtype.val h))
    rcases h with h | h
    · exact absurd (congrArg Subtype.val h) hz1
    · exact congrArg Subtype.val h
  apply hψt
  have e : C.tN = ⟨y, hyN⟩ ^ (2 ^ a) := Subtype.ext (by
    show d.t = y ^ (2 ^ a)
    rw [← hzt])
  rw [e, map_pow]
  have hpow : ∀ n : ℕ, autField (C.ρ ⟨y, hyN⟩ ^ n) = 1 := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact autField_eq autData_one
    | succ n ih => rw [pow_succ, autField_mul, ih, hfy, one_mul]
  exact hpow _

theorem mem_S₀_iff [Finite G] [Finite F] (hψt : autField (C.ρ C.tN) ≠ 1) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hST : C.S₁ ≤ T) (x : ↥(normalizer (C.S₀ : Set G))) (hxT : (x : G) ∈ T) :
    (x : G) ∈ C.S₀ ↔ autField (C.ρ x) = 1 ∧ autSwap (C.ρ x) = false := by
  constructor
  · intro hx
    exact ⟨C.autField_ρ_of_mem x hx, C.autSwap_ρ_of_mem x hx⟩
  · rintro ⟨hf, hsw⟩
    have hxS₁ : (x : G) ∈ C.S₁ :=
      C.mem_S₁_of_mem_normalizer hT hST hxT ((C.autSwap_ρ_eq_false_iff x).1 hsw)
    exact C.mem_S₀_of_autField_eq_one hψt hxS₁ hf

end CaseAData

theorem exists_conj_le_P_of_conj {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)
    {x g : G} (hg : g * d.t * g⁻¹ = x) {E : Subgroup G} (hE : IsPGroup 2 E)
    (hEc : ∀ y ∈ E, y * x = x * y) :
    ∃ k : G, k * x * k⁻¹ = d.t ∧ ∀ y ∈ E, k * y * k⁻¹ ∈ d.P := by
  have hP := d.P_isSylow_centralizer
  have hE'p : IsPGroup 2 (E.map (MulAut.conj g⁻¹).toMonoidHom) := hE.map _
  have hE'c : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({d.t} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    rw [mem_map_conj_iff, inv_inv] at hz
    have h1 := hEc _ hz
    rw [← hg] at h1
    calc z * d.t = g⁻¹ * (g * z * g⁻¹ * (g * d.t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d.t * g⁻¹ * (g * z * g⁻¹)) * g := by rw [h1]
      _ = d.t * z := by group
  obtain ⟨c, hc, hcP⟩ := exists_conj_le_of_isSylowOf hP hE'p hE'c
  have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.mp hc
  refine ⟨c * g⁻¹, ?_, fun y hy => ?_⟩
  · calc c * g⁻¹ * x * (c * g⁻¹)⁻¹ = c * (g⁻¹ * x * g) * c⁻¹ := by group
      _ = c * d.t * c⁻¹ := by rw [← hg]; group
      _ = d.t := by rw [hct]; group
  · have hy' : g⁻¹ * y * g ∈ E.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_conj_iff]
      simpa [mul_assoc] using hy
    have := hcP _ hy'
    have e : c * g⁻¹ * y * (c * g⁻¹)⁻¹ = c * (g⁻¹ * y * g) * c⁻¹ := by group
    rw [e]
    exact this

theorem isPGroup_of_isElemAbelian {G : Type} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsPGroup 2 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem isElemAbelian_map_conj' {G : Type} [Group G] {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (k : G) : IsElemAbelian 2 (E.map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨hab, hsq⟩ := isElemAbelian_map_conj (fun a ha b hb => comm_of_isElemAbelian hE ha hb)
    (fun a ha => by rw [← sq]; exact hE.2 a ha) k
  exact isElemAbelian_of_forall hab fun a ha => by rw [sq]; exact hsq a ha

namespace CaseAData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ} {d : Datum A}
  {W : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] (C : CaseAData d W F)

omit [Finite F] in
theorem not_conj_mem_S₀ (hf : 3 ≤ f) (hF' : FusionFacts A (2 ^ f)) {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hsyl : ∀ Vj : Subgroup G, (Vj = V₁ ∨ Vj = V₂) →
      IsSylowOf 2 (Vj ⊔ zpowers d.t) (centralizer ((Vj ⊔ zpowers d.t : Subgroup G) : Set G)))
    (hWc : Nat.card W = (2 ^ f) ^ 4) (hWe : IsElemAbelian 2 W) (hF : Nat.card F = (2 ^ f) ^ 2)
    {x : G} (hx : x ∈ C.S₀) (hx2 : x * x = 1) : ¬ IsConj d.t x := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hd := SylowSetting.of_datum d
  set q := 2 ^ f with hq
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_cases hxW : x ∈ W
  · obtain ⟨k, -, hkW⟩ := exists_conj_le_P_of_conj d hg (isPGroup_of_isElemAbelian hWe)
      fun y hy => comm_of_isElemAbelian hWe hy hxW
    have hW'P : W.map (MulAut.conj k).toMonoidHom ≤ d.P := by
      rintro _ ⟨y, hy, rfl⟩
      exact hkW y hy
    have := hd.card_elem_le hF' (by omega) hR hW'P (isElemAbelian_map_conj' hWe k)
    rw [card_map_conj, hWc] at this
    have h1 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
    have h64 : 2 < q ^ 2 := by nlinarith
    have h2 : 2 * q ^ 2 < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_right h64 (by positivity)
    omega
  · set ex := C.e ⟨x, hx⟩ with hex
    have hex1 : ex ∉ radOne F := fun h' => hxW ((C.mem_W_iff _).2 h')
    have hex2 : ex * ex = 1 := by
      rw [hex, ← map_mul]
      have : (⟨x, hx⟩ : C.S₀) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
      rw [this, map_one]
    have hexR2 : ex ∈ radTwo F := ((sq_eq_one_iff ex).1 hex2).resolve_left hex1
    have hA : coordA ex = 0 := (mem_radTwo _).1 hexR2
    have hB : coordB ex ≠ 0 := fun h' => hex1 ((mem_radOne _).2 h')
    have hZcomm : ∀ z ∈ C.Zc, z * x = x * z := fun z hz => C.comm_of_mem_Zc hz hx
    have hZe : IsElemAbelian 2 C.Zc := IsElemAbelian.mono hWe C.Zc_le_W
    have hxZ : x ∉ C.Zc := fun h' => hxW (C.Zc_le_W h')
    have hEe : IsElemAbelian 2 (C.Zc ⊔ zpowers x) := isElemAbelian_sup_zpowers hZe hZcomm hx2
    have hEcard : Nat.card ↥(C.Zc ⊔ zpowers x) = 2 * q ^ 2 := by
      have := card_eq_two_mul_card_inf (F := C.Zc ⊔ zpowers x) (V := C.Zc) (t := x)
        (mem_sup_right (mem_zpowers x)) hxZ (fun y hy => (mem_sup_zpowers_iff hZcomm hx2).1 hy)
      rw [this, inf_eq_right.mpr le_sup_left, C.card_Zc, hF]
    obtain ⟨k, -, hkE⟩ := exists_conj_le_P_of_conj d hg (isPGroup_of_isElemAbelian hEe)
      fun y hy => comm_of_isElemAbelian hEe hy (mem_sup_right (mem_zpowers x))
    set E' := (C.Zc ⊔ zpowers x).map (MulAut.conj k).toMonoidHom with hE'
    have hE'P : E' ≤ d.P := by
      rintro _ ⟨y, hy, rfl⟩
      exact hkE y hy
    have hE'card : Nat.card E' = 2 * q ^ 2 := by rw [hE', card_map_conj, hEcard]
    have hadj := hd.elem_eq_adj hF' (by omega) hR hE'P (isElemAbelian_map_conj' hEe k)
      hE'card.ge
    set Q : Subgroup G := C.S₀ ⊓ centralizer ({x} : Set G) with hQ
    have hQc : ∀ y ∈ Q, ∀ z ∈ C.Zc ⊔ zpowers x, z * y = y * z := by
      intro y hy z hz
      have hle : C.Zc ⊔ zpowers x ≤ centralizer ({y} : Set G) := by
        refine sup_le (fun z' hz' => ?_) ?_
        · rw [mem_centralizer_singleton_iff]
          exact C.comm_of_mem_Zc hz' hy.1
        · rw [zpowers_le, mem_centralizer_singleton_iff]
          exact (mem_centralizer_singleton_iff.1 hy.2).symm
      exact mem_centralizer_singleton_iff.1 (hle hz)
    have hQ'c : Q.map (MulAut.conj k).toMonoidHom ≤ centralizer (E' : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      have := hQc y hy z hz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc k * z * k⁻¹ * (k * y * k⁻¹) = k * (z * y) * k⁻¹ := by group
        _ = k * (y * z) * k⁻¹ := by rw [this]
        _ = k * y * k⁻¹ * (k * z * k⁻¹) := by group
    have hQp : IsPGroup 2 (Q.map (MulAut.conj k).toMonoidHom) :=
      ((C.isPGroup_S₁.to_le C.S₀_le).to_inf_left).map _
    have hbound : Nat.card (Q.map (MulAut.conj k).toMonoidHom) ≤ 2 * q ^ 2 := by
      rcases hadj with h1 | h1
      · rw [h1] at hQ'c
        calc _ ≤ Nat.card ↥(V₁ ⊔ zpowers d.t) :=
              CFSG.ComponentClassification.AschbacherTheorem3.card_le_of_isSylowOf
                (hsyl V₁ (Or.inl rfl)) hQp hQ'c
          _ = 2 * q ^ 2 := (hd.adj_properties hF' hR (Or.inl rfl)).2.2
      · rw [h1] at hQ'c
        calc _ ≤ Nat.card ↥(V₂ ⊔ zpowers d.t) :=
              CFSG.ComponentClassification.AschbacherTheorem3.card_le_of_isSylowOf
                (hsyl V₂ (Or.inr rfl)) hQp hQ'c
          _ = 2 * q ^ 2 := (hd.adj_properties hF' hR (Or.inr rfl)).2.2
    rw [card_map_conj] at hbound
    have hQcard : Nat.card (radTwo F) ≤ Nat.card Q := by
      refine Nat.card_le_card_of_injective
        (fun u => (⟨(C.e.symm u : G), (C.e.symm u).2, ?_⟩ : Q)) ?_
      · have hu : (u : unipAll F) ∈ centralizer ({ex} : Set (unipAll F)) := by
          rw [centralizer_radTwo hA hB]
          exact u.2
        rw [mem_centralizer_singleton_iff] at hu
        have h1 : C.e.symm (u * ex) = C.e.symm (ex * u) := by rw [hu]
        rw [map_mul, map_mul, hex, MulEquiv.symm_apply_apply] at h1
        exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
      · intro u v huv
        have h1 := congrArg Subtype.val huv
        exact Subtype.ext (C.e.symm.injective (Subtype.ext h1))
    rw [card_radTwo, hF] at hQcard
    have h1 : (q ^ 2) ^ 2 = q ^ 2 * q ^ 2 := by ring
    have h64 : 2 < q ^ 2 := by nlinarith
    have h2 : 2 * q ^ 2 < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_right h64 (by positivity)
    omega

end CaseAData

end CFSG.LocalAnalysis.EvenBN.LinearThree
