module

public import CFSG.GH74.Generic.BProg.B3.S1FinalDefs
public import CFSG.GH74.Generic.BProg.B3.S1FinalIdent
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalJ1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B3.S1FinalDefs
open scoped MatrixGroups commutatorElement

structure JSetup {G : Type} [Group G] [Finite G] (x : G) (K A : Subgroup G) (a : G)
    (D J J₁ J₂ : Subgroup G) : Prop where
  hc : Ctx21 G x K A a D J
  hax : a ≠ x
  hxA : x ∈ A
  hxS : x ∉ centralizerSection J (pPrimeCoreOf 2 J)
  hAJ : A ≤ normalizer (J : Set G)
  hS : S1SplitMod K A x a J₁ J₂
  hJ₂ : J₂ ≤ J
  hJ₁c : J₁ ≤ centralizerSection J (pPrimeCoreOf 2 J)

namespace JSetup

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J J₁ J₂ : Subgroup G}
  (H : JSetup x K A a D J J₁ J₂)

include H

theorem hJa : J ≤ centralizer ({a} : Set G) := H.hc.obs.comp.1

theorem hAsq : ∀ c ∈ A, c * c = 1 := fun c hc' => by
  have := H.hc.src.2.1
  rw [← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) c hc'

theorem hAcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := fun c hc' d hd => by
  have := H.hc.src.2.1
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨c, hc'⟩ ⟨d, hd⟩)

theorem ha2 : orderOf a = 2 := H.hc.obs.y_ord

theorem hx2 : orderOf x = 2 := H.hc.circ.1.1.1.1

theorem haA : a ∈ A := H.hc.a_mem

theorem haS : a ∈ centralizerSection J (pPrimeCoreOf 2 J) := H.hc.obs.y_mem_centralizerSection

theorem hKC : K ≤ centralizer ({x} : Set G) := H.hc.circ.1.1.1.2.2.1

theorem hJ₂Hg : J₂ ≤ K ⊓ centralizer ({a} : Set G) := H.hS.comp₂.1

theorem hJ₂comm_x : ∀ k ∈ J₂, k * x = x * k := fun _ hk =>
  Subgroup.mem_centralizer_singleton_iff.1 (H.hKC (H.hJ₂Hg hk).1)

theorem hJ₂comm_a : ∀ k ∈ J₂, k * a = a * k := fun _ hk =>
  Subgroup.mem_centralizer_singleton_iff.1 (H.hJ₂Hg hk).2

theorem hb : x * a ∈ J₂ := H.hS.xu_mem

theorem hb2 : (x * a) * (x * a) = 1 := by
  have h1 := H.hAsq x H.hxA
  have h2 := H.hAsq a H.haA
  have h3 := H.hAcomm a H.haA x H.hxA
  calc (x * a) * (x * a) = x * (a * x) * a := by group
    _ = x * (x * a) * a := by rw [h3]
    _ = (x * x) * (a * a) := by group
    _ = 1 := by rw [h1, h2, one_mul]

theorem bar_quasisimple : IsQuasisimple ↥(PumpCalc.bar a J) :=
  (PumpCalc.isComponent_bar H.hc.obs.comp).1

theorem center_J0 : ∀ z : J0 a J, (∀ g : J0 a J, g * z = z * g) → z = 1 := fun z hz =>
  S1FinalSl2.eq_one_of_central_of_simple H.bar_quasisimple.2.1 (by
    have := H.bar_quasisimple.2.2
    exact this) hz

end JSetup

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J J₁ J₂ : Subgroup G}

theorem q8_data (H : JSetup x K A a D J J₁ J₂) :
    ∃ φ : QuaternionGroup 2 →* CentralizerBar a, Function.Injective φ ∧
      ∀ g : QuaternionGroup 2, ∀ m ∈ PumpCalc.bar a J, φ g * m = m * φ g := by
  classical
  obtain ⟨F, _, _, hodd, hF, ⟨e₁⟩, -⟩ := H.hS.sl2
  have hk : ringChar F ≠ 2 := S1IdentSl2.ringChar_ne_two hodd
  have hJ₁Y : J₁ ≤ centralizer ({a} : Set G) := H.hS.comp₁.1.trans inf_le_right
  let ψ₁ : ↥J₁ →* SL(2, F) := e₁.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J₁))
  have hψ₁s : Function.Surjective ψ₁ := e₁.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψ₁k : ψ₁.ker = pPrimeCore 2 ↥J₁ := by
    ext y
    rw [MonoidHom.mem_ker]
    show e₁ (QuotientGroup.mk y) = 1 ↔ _
    rw [← map_one e₁, e₁.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hker : Odd (Nat.card ψ₁.ker) := by
    rw [hψ₁k]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  obtain ⟨τ₀, hτ₀⟩ := S1IdentSl2.exists_quaternion_hom hk (MonoidHom.id SL(2, F))
    Function.injective_id
  obtain ⟨τ, hτ, -⟩ := S1FinalIdent.exists_lift_q8 ψ₁ hψ₁s hker τ₀ hτ₀
  refine ⟨((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion hJ₁Y)).comp τ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : (Subgroup.inclusion hJ₁Y (τ g) : ↥(centralizer ({a} : Set G))) ∈
        pPrimeCore 2 ↥(centralizer ({a} : Set G)) := (QuotientGroup.eq_one_iff _).1 hg
    have hg8 : g ^ (2 ^ 3) = 1 := by
      have h1 : orderOf g ∣ Nat.card (QuaternionGroup 2) := orderOf_dvd_natCard g
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
      exact orderOf_dvd_iff_pow_eq_one.1 (by simpa using h1)
    have h2 : (Subgroup.inclusion hJ₁Y (τ g)) ^ (2 ^ 3) = 1 := by
      rw [← map_pow, ← map_pow, hg8, map_one, map_one]
    have h3 := S1FinalSl2.eq_one_of_pow_two_pow_of_mem_odd _
      (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) hmem 3 h2
    have h4 : τ g = 1 := Subgroup.inclusion_injective hJ₁Y (by rw [h3, map_one])
    exact hτ (by rw [h4, map_one])
  · intro g m hm
    obtain ⟨j, hj, rfl⟩ := hm
    have hz : ((τ g : ↥J₁) : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) := H.hJ₁c (τ g).2
    exact Obs.piBar_commute_of_mem_centralizerSection H.hc.obs.comp
      (z := ⟨((τ g : ↥J₁) : G), hJ₁Y (τ g).2⟩) hz _ ⟨j, hj, rfl⟩

@[expose] noncomputable def sigma2 (hJa : J ≤ centralizer ({a} : Set G)) (hJ₂ : J₂ ≤ J) :
    ↥J₂ →* J0 a J :=
  (Pi0 hJa).comp (Subgroup.inclusion hJ₂)

theorem sl2Data_J0 (H : JSetup x K A a D J J₁ J₂) : ∃ q : ℕ, 5 ≤ q ∧ S1FinalIdent.SL2Data (J0 a J) q := by
  classical
  obtain ⟨F, _, _, hodd, hF, -, ⟨e₂⟩⟩ := H.hS.sl2
  let ψ₂ : ↥J₂ →* SL(2, F) := e₂.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J₂))
  have hψ₂s : Function.Surjective ψ₂ := e₂.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψ₂k : ψ₂.ker = pPrimeCore 2 ↥J₂ := by
    ext y
    rw [MonoidHom.mem_ker]
    show e₂ (QuotientGroup.mk y) = 1 ↔ _
    rw [← map_one e₂, e₂.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hker : Odd (Nat.card ψ₂.ker) := by
    rw [hψ₂k]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hb2 : (⟨x * a, H.hb⟩ : ↥J₂) * ⟨x * a, H.hb⟩ = 1 := Subtype.ext H.hb2
  have hbc : ∀ h : ↥J₂, h * (⟨x * a, H.hb⟩ : ↥J₂) = ⟨x * a, H.hb⟩ * h := fun h => by
    apply Subtype.ext
    show (h : G) * (x * a) = (x * a) * h
    rw [← mul_assoc, H.hJ₂comm_x h h.2, mul_assoc, H.hJ₂comm_a h h.2, ← mul_assoc]
  have hσb : sigma2 H.hJa H.hJ₂ ⟨x * a, H.hb⟩ ≠ 1 := by
    intro h1
    have hz : barJ H.hJa ⟨x * a, H.hJ₂ H.hb⟩ ∈ center ↥(PumpCalc.bar a J) :=
      (QuotientGroup.eq_one_iff _).1 h1
    have hxaC : x * a ∈ centralizer ({a} : Set G) := H.hJa (H.hJ₂ H.hb)
    have hcs : x * a ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
      ObsPump.mem_cSec_of_bar_comm H.hc.obs.comp hxaC (fun l hl => by
        have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
        exact (congrArg Subtype.val this).symm)
    have hxs : x ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
      have : x = (x * a) * a⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hcs (Subgroup.inv_mem _ H.haS)
    exact H.hxS hxs
  exact ⟨Fintype.card F, hF, S1FinalIdent.sl2Data_of_quotient hodd hF (sigma2 H.hJa H.hJ₂) ψ₂ hψ₂s
    hker hb2 hbc hσb⟩

theorem qShape3SD_J0
    (H : JSetup x K A a D J J₁ J₂) : B1.QShape3SD (J0 a J) := by
  obtain ⟨φ, hφ, hcent⟩ := q8_data H
  obtain ⟨q, hq, hd⟩ := sl2Data_J0 H
  exact S1FinalIdent.J_L3_of_sl2_data (gen4_centralizerBar H.hc.hyp.gen4 a) H.bar_quasisimple φ hφ
    hcent hq hd

end S1FinalJ1

end CFSG.GH74.Generic.BProg.B3
