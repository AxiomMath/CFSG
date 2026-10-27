module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cT
public import CFSG.GH74.GLS.C3.Layer1.St1P41Lift

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1A7
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Basic

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem Env31.not_central (hG : C3Hyp G) (hS34 : P34.S_prop34) (E : Env31 x y K T f z) :
    ¬ CFSG.GH74.IsCentralInvolution x := by
  intro hcen
  have hyp : P34.Prop34Hyp G x K :=
    { simple := hG.kproper.1
      nonab := hG.kproper.2.1
      central := hcen
      comp := E.hu2.1.1.2
      unique := E.huniq
      shape := Or.inl E.hshape
      sylowQ := Thm1.exists_Q_of_card_le_two (Thm1A7.card_le_two_of_rank_le_one E.hrk) }
  exact hS34 G x K hyp f E.hfC E.hf2 E.hind

theorem Env31.core (hG : C3Hyp G) (E : Env31 x y K T f z) :
    CoreConcl (Back.actHom E.hKN) (T.subgroupOf (centralizer ({x} : Set G)))
      ((T ⊓ K).subgroupOf (centralizer ({x} : Set G))) := by
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ E.hsetup.sylowT (by rw [E.hu2.2.2.1.2, hG.pRank_eq_four])
  exact core_lift_G E.hKC E.hKN E.hsetup.sylowT E.hcen E.hAut hE₁T hE₁ hE₁16
    (Thm1A7.card_le_two_of_rank_le_one E.hrk)

theorem Env31.exists_conj_z (hG : C3Hyp G) (E : Env31 x y K T f z) {p : G} (hpP : p ∈ T ⊓ K)
    (hp2 : orderOf p = 2) : ∃ t₁ ∈ K, t₁ * z * t₁⁻¹ = p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  have hPC : T ⊓ K ≤ C := inf_le_right.trans E.hKC
  have hzC : z ∈ C := E.hTC E.hzP.1
  have hpC : p ∈ C := hPC hpP
  have hfC : f ∈ C := E.hfC
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁P, hz₁2, hz₁c, hz₁u, hfus, -⟩ := E.core hG
  have hz₁eq : z₁ = ⟨z, hzC⟩ := by
    have hz₁' : (z₁ : G) ∈ T ⊓ K := hz₁P
    have hz₁c' : ∀ w ∈ T ⊓ K, (z₁ : G) * w = w * (z₁ : G) := by
      intro w hw
      have := hz₁c ⟨w, hPC hw⟩ hw
      exact congrArg Subtype.val this
    have hz₁1 : (z₁ : G) ≠ 1 := fun h => by
      have : z₁ = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz₁2
      omega
    rcases E.hzu _ hz₁' hz₁c' with h | h
    · exact absurd h hz₁1
    · exact Subtype.ext h
  have hfCT : (⟨f, hfC⟩ : ↥C) ∈ T.subgroupOf C := E.hfT
  have hfC2 : orderOf (⟨f, hfC⟩ : ↥C) = 2 := by rw [Subgroup.orderOf_mk]; exact E.hf2
  have hfcP : ∀ q ∈ (T ⊓ K).subgroupOf C, (⟨f, hfC⟩ : ↥C) * q = q * ⟨f, hfC⟩ := by
    intro q hq
    exact Subtype.ext (E.hfc (q : G) hq)
  have hpu : (⟨p, hpC⟩ : ↥C) ∈ (T ⊓ K).subgroupOf C ⊔ zpowers (⟨f, hfC⟩ : ↥C) :=
    Subgroup.mem_sup_left (by exact hpP)
  have hpu2 : orderOf (⟨p, hpC⟩ : ↥C) = 2 := by rw [Subgroup.orderOf_mk]; exact hp2
  obtain ⟨g, hg, hgu⟩ := hfus ⟨f, hfC⟩ hfCT hfC2 hfcP (E.hfout hfC) ⟨p, hpC⟩ hpu hpu2
  have hφp : Back.actHom E.hKN ⟨p, hpC⟩ = MulAut.conj (QuotientGroup.mk (⟨p, hpP.2⟩ : ↥K) : kBar K) :=
    Back.actHom_of_mem E.hKN hpP.2 hpC
  have hφz : Back.actHom E.hKN ⟨z, hzC⟩ = MulAut.conj (QuotientGroup.mk (⟨z, E.hzP.2⟩ : ↥K) : kBar K) :=
    Back.actHom_of_mem E.hKN E.hzP.2 hzC
  have hinnp : Back.actHom E.hKN ⟨p, hpC⟩ ∈ innAut (kBar K) := by
    rw [hφp]; exact ⟨_, rfl⟩
  have hinnz : Back.actHom E.hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
    rw [hφz]; exact ⟨_, rfl⟩
  have hinn_conj : g * Back.actHom E.hKN ⟨p, hpC⟩ * g⁻¹ ∈ innAut (kBar K) :=
    (innAut (kBar K)).mul_mem ((innAut (kBar K)).mul_mem hg hinnp) ((innAut (kBar K)).inv_mem hg)
  have hcase : g * Back.actHom E.hKN ⟨p, hpC⟩ * g⁻¹ = Back.actHom E.hKN ⟨z, hzC⟩ := by
    rw [hz₁eq] at hgu
    rcases hgu with h | h | h
    · exact h
    · exfalso
      apply E.hfout hfC
      rw [← h]; exact hinn_conj
    · exfalso
      apply E.hfout hfC
      have h1 : Back.actHom E.hKN ⟨f, hfC⟩ * Back.actHom E.hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
        rw [← h]; exact hinn_conj
      have := (innAut (kBar K)).mul_mem h1 ((innAut (kBar K)).inv_mem hinnz)
      simpa using this
  obtain ⟨kb, rfl⟩ := hg
  rw [hφp, hφz] at hcase
  have hcase' : (kb * QuotientGroup.mk (⟨p, hpP.2⟩ : ↥K) * kb⁻¹ : kBar K) =
      QuotientGroup.mk (⟨z, E.hzP.2⟩ : ↥K) := by
    apply E.hcen
    simpa [map_mul, map_inv] using hcase
  obtain ⟨⟨k₀, hk₀⟩, hk₀eq⟩ := QuotientGroup.mk_surjective kb⁻¹
  have hk₀' : (QuotientGroup.mk (⟨k₀, hk₀⟩ : ↥K) : kBar K) = kb⁻¹ := hk₀eq
  have himg : (QuotientGroup.mk (⟨k₀ * z * k₀⁻¹, K.mul_mem (K.mul_mem hk₀ E.hzP.2) (K.inv_mem hk₀)⟩ :
      ↥K) : kBar K) = QuotientGroup.mk (⟨p, hpP.2⟩ : ↥K) := by
    have e1 : (⟨k₀ * z * k₀⁻¹, K.mul_mem (K.mul_mem hk₀ E.hzP.2) (K.inv_mem hk₀)⟩ : ↥K) =
        ⟨k₀, hk₀⟩ * ⟨z, E.hzP.2⟩ * ⟨k₀, hk₀⟩⁻¹ := rfl
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk₀']
    rw [inv_inv]
    calc kb⁻¹ * QuotientGroup.mk (⟨z, E.hzP.2⟩ : ↥K) * kb
        = kb⁻¹ * (kb * QuotientGroup.mk (⟨p, hpP.2⟩ : ↥K) * kb⁻¹) * kb := by rw [hcase']
      _ = QuotientGroup.mk (⟨p, hpP.2⟩ : ↥K) := by group
  have hmod : (k₀ * z * k₀⁻¹)⁻¹ * p ∈ pPrimeCoreOf 2 K := by
    refine Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.mul_mem (K.inv_mem (K.mul_mem (K.mul_mem hk₀
      E.hzP.2) (K.inv_mem hk₀))) hpP.2, ?_⟩
    exact QuotientGroup.eq.1 himg
  have hkz2 : orderOf (k₀ * z * k₀⁻¹) = 2 := by
    rw [← E.hz2]
    have := MulEquiv.orderOf_eq (MulAut.conj k₀) z
    simpa [MulAut.conj_apply] using this
  obtain ⟨o, ho, hoz⟩ := PumpLift.exists_conj_of_involutions_mod_odd (M := K)
    (K.mul_mem (K.mul_mem hk₀ E.hzP.2) (K.inv_mem hk₀)) hpP.2 hkz2 hp2 hmod
  have hoK : o ∈ K := TwoThin.pPrimeCoreOf_le K ho
  refine ⟨o * k₀, K.mul_mem hoK hk₀, ?_⟩
  calc o * k₀ * z * (o * k₀)⁻¹ = o * (k₀ * z * k₀⁻¹) * o⁻¹ := by group
    _ = p := hoz

end Basic

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
