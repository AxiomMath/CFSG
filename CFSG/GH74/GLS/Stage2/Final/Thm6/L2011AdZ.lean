module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdPair
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Lift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

section Abs

variable {X : Type} [Group X] [Finite X]

theorem odd_central_trivial (hX : pPrimeCore 2 X = ⊥) {Q : Subgroup X} (hQ : Q.Normal) {v : X}
    (hvQ : v ∈ Q) (hvc : ∀ q ∈ Q, v * q = q * v) (hodd : Odd (orderOf v)) : v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r := orderOf v with hr
  let T : Subgroup X :=
    { carrier := {w | w ∈ Q ∧ (∀ q ∈ Q, w * q = q * w) ∧ w ^ r = 1}
      mul_mem' := by
        rintro a b ⟨haQ, hac, har⟩ ⟨hbQ, hbc, hbr⟩
        refine ⟨Q.mul_mem haQ hbQ, fun q hq => ?_, ?_⟩
        · calc a * b * q = a * (b * q) := by group
            _ = a * (q * b) := by rw [hbc q hq]
            _ = (a * q) * b := by group
            _ = (q * a) * b := by rw [hac q hq]
            _ = q * (a * b) := by group
        · have hcomm : Commute a b := hac b hbQ
          rw [hcomm.mul_pow, har, hbr, one_mul]
      one_mem' := ⟨Q.one_mem, fun q _ => by simp, one_pow _⟩
      inv_mem' := by
        rintro a ⟨haQ, hac, har⟩
        refine ⟨Q.inv_mem haQ, fun q hq => ?_, ?_⟩
        · have := hac q hq
          calc a⁻¹ * q = a⁻¹ * (q * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * q) * a⁻¹ := by rw [this]
            _ = q * a⁻¹ := by group
        · rw [inv_pow, har, inv_one] }
  have hvT : v ∈ T := ⟨hvQ, hvc, pow_orderOf_eq_one v⟩
  have hTn : T.Normal := ⟨fun n hn g => by
    obtain ⟨hnQ, hnc, hnr⟩ := hn
    refine ⟨hQ.conj_mem n hnQ g, fun q hq => ?_, ?_⟩
    · have h1 : g⁻¹ * q * g ∈ Q := by simpa using hQ.conj_mem q hq g⁻¹
      have h2 := hnc _ h1
      calc g * n * g⁻¹ * q = g * (n * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * q * g) * n) * g⁻¹ := by rw [h2]
        _ = q * (g * n * g⁻¹) := by group
    · rw [conj_pow, hnr]
      simp⟩
  have hodd' : ∀ y ∈ T, Odd (orderOf y) := by
    intro y hy
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hy.2.2)
  have hle : T ≤ pPrimeCore 2 X :=
    GroupTheory.le_pPrimeCore_of_normal hTn
      (Nat.coprime_two_left.2 (IVK.Proofs2.Ivk93Adapt.odd_card_of_forall_odd T hodd'))
  have := hle hvT
  rw [hX, Subgroup.mem_bot] at this
  exact this

omit [Finite X] in
theorem isSimpleGroup_of_isComponent_center_trivial {Q : Subgroup X} (hQ : IsComponent Q)
    (hZ : ∀ u ∈ Q, (∀ q ∈ Q, u * q = q * u) → u = 1) : IsSimpleGroup ↥Q := by
  have hbot : Subgroup.center ↥Q = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.mem_center_iff] at hu
    exact hZ u u.2 (fun q hq => by
      have := hu ⟨q, hq⟩
      exact (congrArg Subtype.val this).symm)
  have e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have := hQ.1.2.1
  exact MulEquiv.isSimpleGroup e.symm

omit [Finite X] in
theorem layer_eq_of_unique {Q : Subgroup X} (hQ : IsComponent Q)
    (hone : ∀ Q' : Subgroup X, IsComponent Q' → Q' = Q) : layer X = Q :=
  le_antisymm (sSup_le fun K hK => (hone K hK).le) (le_sSup hQ)

theorem center_layer_trivial (hX : pPrimeCore 2 X = ⊥) {x : X} {K₁ K₂ Q : Subgroup X}
    (hx : PairX x K₁ K₂) (hQ : IsComponent Q) (hone : ∀ Q' : Subgroup X, IsComponent Q' → Q' = Q)
    (hQ₁ : K₁ ≤ Q) (hQ₂ : K₂ ≤ Q)
    (hZc : ∀ u : X, u * x = x * u → (∀ k ∈ K₁ ⊔ K₂, u * k = k * u) →
      ∃ v : X, Odd (orderOf v) ∧ v * x = x * v ∧ (u = v ∨ u = x * v)) :
    ∀ u ∈ Q, (∀ q ∈ Q, u * q = q * u) → u = 1 := by
  intro u huQ huc
  have hlayer : layer X = Q := layer_eq_of_unique hQ hone
  have hQn : Q.Normal := by
    have hc : (layer X).Characteristic := layer_characteristic
    have : (layer X).Normal := inferInstance
    rwa [hlayer] at this
  have hux : u * x = x * u := huc x (hQ₁ hx.mem₁)
  have huK : ∀ k ∈ K₁ ⊔ K₂, u * k = k * u := fun k hk => huc k (sup_le hQ₁ hQ₂ hk)
  obtain ⟨v, hvodd, hvx, hu | hu⟩ := hZc u hux huK
  · subst hu
    exact odd_central_trivial hX hQn huQ huc hvodd
  · have hu2 : u * u = v * v := by
      rw [hu]
      calc x * v * (x * v) = x * (v * x) * v := by group
        _ = x * (x * v) * v := by rw [hvx]
        _ = (x * x) * (v * v) := by group
        _ = v * v := by rw [hx.sq, one_mul]
    have hv2Q : v * v ∈ Q := hu2 ▸ Q.mul_mem huQ huQ
    have hv2c : ∀ q ∈ Q, (v * v) * q = q * (v * v) := by
      intro q hq
      rw [← hu2]
      calc u * u * q = u * (u * q) := by group
        _ = u * (q * u) := by rw [huc q hq]
        _ = (u * q) * u := by group
        _ = (q * u) * u := by rw [huc q hq]
        _ = q * (u * u) := by group
    have hv2odd : Odd (orderOf (v * v)) := by
      rw [← pow_two]
      exact Odd.of_dvd_nat hvodd (orderOf_pow_dvd 2)
    have hv2 : v * v = 1 := odd_central_trivial hX hQn hv2Q hv2c hv2odd
    have hv1 : v = 1 := L2012.eq_one_of_sq_odd hv2 hvodd
    rw [hv1, mul_one] at hu
    subst hu
    have hQC : Q ≤ centralizer ({u} : Set X) := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (huc q hq).symm
    exfalso
    rcases hx.component_eq hQ hQC with h | h
    · apply hx.not_comm₂
      intro a ha b hb
      exact hx.comm a (h ▸ hQ₂ ha) b hb
    · apply hx.not_comm₁
      intro a ha b hb
      exact hx.comm a ha b (h ▸ hQ₁ hb)

end Abs

section Bar

variable {G : Type} [Group G] [Finite G]

theorem mkH_ne_of_comm {H : Subgroup G} {x y : G} (hxH : x ∈ H) (hyH : y ∈ H) (hx2 : orderOf x = 2)
    (hy2 : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    mkH H ⟨x, hxH⟩ ≠ mkH H ⟨y, hyH⟩ := by
  intro h
  have hmem : (⟨x, hxH⟩ : ↥H)⁻¹ * ⟨y, hyH⟩ ∈ pPrimeCore 2 ↥H := by
    rw [← mkH_eq_one_iff, map_mul, map_inv, h, inv_mul_cancel]
  have hodd := odd_orderOf_of_mem_core H hmem
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  have hsq : ((⟨x, hxH⟩ : ↥H)⁻¹ * ⟨y, hyH⟩) * ((⟨x, hxH⟩ : ↥H)⁻¹ * ⟨y, hyH⟩) = 1 := by
    apply Subtype.ext
    show x⁻¹ * y * (x⁻¹ * y) = 1
    have hc : Commute x⁻¹ y := (show Commute x y from hxy).inv_left
    calc x⁻¹ * y * (x⁻¹ * y) = x⁻¹ * (y * x⁻¹) * y := by group
      _ = x⁻¹ * (x⁻¹ * y) * y := by rw [hc.eq]
      _ = (x * x)⁻¹ * (y * y) := by group
      _ = 1 := by rw [hxx, hyy]; simp
  have h1 := L2012.eq_one_of_sq_odd hsq hodd
  apply hne
  have := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at this
  exact inv_mul_eq_one.mp this

end Bar

section PLayer

variable {Y : Type} [Group Y] [Finite Y]

theorem isPComponent_pLayer_of_layer_single {Q : Subgroup (Y ⧸ pPrimeCore 2 Y)} (hQ : IsComponent Q)
    (hone : ∀ Q' : Subgroup (Y ⧸ pPrimeCore 2 Y), IsComponent Q' → Q' = Q) :
    IsPComponent 2 (pLayer Y 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J₁, hJ₁, hmap⟩ := C3.Layer1.Thm1.exists_pComponent_of_quotient_component hQ
  have hall : ∀ L : Subgroup Y, IsPComponent 2 L → L = J₁ := by
    intro L hL
    have hL' := hL
    obtain ⟨K, hK, -, hLK, -⟩ := hL
    exact CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq hL' hJ₁
      (hLK.trans ((hone K hK).trans hmap.symm))
  have hpl : pLayer Y 2 = J₁ :=
    le_antisymm (sSup_le fun L hL => (hall L hL).le) (le_sSup hJ₁)
  rw [hpl]
  exact hJ₁

end PLayer

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
