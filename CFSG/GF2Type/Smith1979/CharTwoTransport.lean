module

public import CFSG.GF2Type.Smith1979.CharTwoSpec
public import CFSG.GF2Type.Smith1979.CharTwoModelSpec
public import CFSG.GF2Type.Smith1979.IdxFourTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
  CFSG.GF2Type.Smith1979.GammaU.Dict

local notation "GL12" => V12 ≃ₗ[ZMod 2] V12

theorem mem_stabilizer_GL12 {g : GL12} {v : V12} :
    g ∈ MulAction.stabilizer GL12 v ↔ g v = v :=
  MulAction.mem_stabilizer_iff

section Model

variable {E' : Subgroup GL12} {OB OA : V12 → Prop} {a0 w0 : V12}

theorem E0Facts.stab_triv (hF : E0Facts E' OB OA a0 w0) {w : V12} (hw : OB w) {P : Subgroup GL12}
    (hP : P ≤ E' ⊓ MulAction.stabilizer GL12 w)
    (hPn : ∀ s ∈ E' ⊓ MulAction.stabilizer GL12 w, ∀ p ∈ P, s * p * s⁻¹ ∈ P)
    (hP2 : IsPGroup 2 P) : P = ⊥ := by
  obtain ⟨e, he, hew⟩ := hF.B_trans w hw
  have hei : e⁻¹ w0 = w := by rw [← hew]; exact e.symm_apply_apply w
  have hbot := hF.stab_w0 (P.map (MulAut.conj e).toMonoidHom) ?_ ?_ (hP2.map _)
  · exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj e).injective).mp hbot
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hpE, hpw⟩ := Subgroup.mem_inf.mp (hP hp)
    refine Subgroup.mem_inf.mpr ⟨E'.mul_mem (E'.mul_mem he hpE) (E'.inv_mem he),
      mem_stabilizer_GL12.mpr ?_⟩
    show e (p (e⁻¹ w0)) = w0
    rw [hei, mem_stabilizer_GL12.mp hpw, hew]
  · rintro s hs _ ⟨p, hp, rfl⟩
    obtain ⟨hsE, hsw⟩ := Subgroup.mem_inf.mp hs
    have hs' : e⁻¹ * s * e ∈ E' ⊓ MulAction.stabilizer GL12 w := by
      refine Subgroup.mem_inf.mpr ⟨E'.mul_mem (E'.mul_mem (E'.inv_mem he) hsE) he,
        mem_stabilizer_GL12.mpr ?_⟩
      show e⁻¹ (s (e w)) = w
      rw [hew, mem_stabilizer_GL12.mp hsw, hei]
    refine ⟨(e⁻¹ * s * e) * p * (e⁻¹ * s * e)⁻¹, hPn _ hs' p hp, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end Model

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Transport

variable {E : Subgroup S.O} {E' : Subgroup GL12} {ψ : S.Qt ≃ₗ[ZMod 2] V12}

theorem mem_E'_iff (hE : E.map (tau S ψ) = E') {y : GL12} :
    y ∈ E' ↔ ∃ s ∈ E, tau S ψ s = y := by
  rw [← hE, Subgroup.mem_map]

end Transport

theorem charTwoFacts_of_model (hw : S.width = 6) {g : G} (H : Hyp4 S g) (C : Cons311 S g)
    {E : Subgroup S.O} (hEM : E ≤ S.Mbar) (hidx : E.relIndex S.Mbar ≤ 4)
    {E' : Subgroup GL12} {OB OA : V12 → Prop} {a0 w0 : V12} (hF : E0Facts E' OB OA a0 w0)
    {ψ : S.Qt ≃ₗ[ZMod 2] V12} (hq : ∀ v, q0 (ψ v) = S.q v) (hE : E.map (tau S ψ) = E') :
    CharTwoFacts S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ := tau_injective (S := S) ψ
  have hτa := tau_apply_apply (S := S) ψ
  have hψ0 : ∀ v : S.Qt, ψ v = 0 → v = 0 := fun v h => ψ.injective (h.trans (map_zero ψ).symm)
  have hiso : ∀ e ∈ E', ∀ v, q0 (e v) = q0 v := by
    intro e he v
    obtain ⟨s, -, rfl⟩ := (mem_E'_iff hE).mp he
    obtain ⟨u, rfl⟩ := ψ.surjective v
    rw [hτa, hq, hq, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 s.2]
  have hisoF : ∀ e ∈ E', ∀ v w, f0 (e v) (e w) = f0 v w := by
    intro e he v w
    rw [← polar_q0, ← polar_q0, QuadraticMap.polar, QuadraticMap.polar, ← map_add, hiso e he,
      hiso e he, hiso e he]
  have hB : ∀ v : S.Qt, OB (ψ v) → ¬ HasLbar S v := by
    rintro v hv ⟨P, hP, hPn, hP2, hcard⟩
    have hbot : (P ⊓ E).map (tau S ψ) = ⊥ := by
      refine hF.stab_triv hv ?_ ?_ (IsPGroup.map (hP2.to_le inf_le_left) _)
      · rintro _ ⟨p, ⟨hpP, hpE⟩, rfl⟩
        refine Subgroup.mem_inf.mpr ⟨(mem_E'_iff hE).mpr ⟨p, hpE, rfl⟩,
          mem_stabilizer_GL12.mpr ?_⟩
        rw [hτa, (hP hpP).2]
      · rintro s hs _ ⟨p, ⟨hpP, hpE⟩, rfl⟩
        obtain ⟨hsE, hsv⟩ := Subgroup.mem_inf.mp hs
        obtain ⟨r, hrE, rfl⟩ := (mem_E'_iff hE).mp hsE
        have hrv : r ∈ stab S v := by
          refine ⟨hEM hrE, ψ.injective ?_⟩
          rw [← hτa]
          exact mem_stabilizer_GL12.mp hsv
        exact ⟨r * p * r⁻¹, ⟨hPn r hrv p hpP, E.mul_mem (E.mul_mem hrE hpE) (E.inv_mem hrE)⟩,
          by rw [map_mul, map_mul, map_inv]⟩
    have hPE : P ⊓ E = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ hτ).mp hbot
    have h1 := Subgroup.relIndex_mul_card (H := E) (K := P)
    rw [inf_comm, hPE, Subgroup.card_bot, mul_one] at h1
    have hPM : P ≤ S.Mbar := fun p hp => (hP hp).1
    have hne : E.relIndex S.Mbar ≠ 0 := by
      intro h0
      have h := Subgroup.relIndex_mul_card (H := E) (K := S.Mbar)
      rw [h0, zero_mul] at h
      exact Nat.card_pos.ne' h.symm
    have h2 : E.relIndex P ≤ E.relIndex S.Mbar :=
      Subgroup.relIndex_le_of_le_right hPM hne
    omega
  have hLstab : S.Lbar g ≤ stab S (aT S g) := fun l hl =>
    (Case25.mem_NLbar_iff H).mp (Case25.Lbar_le_NLbar hl)
  have hLnorm : ∀ s ∈ stab S (aT S g), ∀ l ∈ S.Lbar g, s * l * s⁻¹ ∈ S.Lbar g := fun s hs l hl =>
    (mem_normalizer_iff.mp ((Case25.mem_NLbar_iff H).mpr hs).2 l).mp hl
  have hLcard : Nat.card (S.Lbar g) = 2 ^ 5 := by rw [card_Lbar C hw]; norm_num
  have hbase : HasLbar S (aT S g) :=
    ⟨S.Lbar g, hLstab, hLnorm, IsPGroup.of_card hLcard, hLcard⟩
  have hbaseA : OA (ψ (aT S g)) := by
    rcases hF.cases (ψ (aT S g)) (fun h => aT_ne_zero H (hψ0 _ h)) (by rw [hq, q_aT H]) with
      h | h
    · exact absurd hbase (hB _ h)
    · exact h
  have hA : ∀ v : S.Qt, OA (ψ v) → HasLbar S v := by
    intro v hv
    obtain ⟨e1, he1, h1⟩ := hF.A_trans _ hv
    obtain ⟨e2, he2, h2⟩ := hF.A_trans _ hbaseA
    obtain ⟨s, hsE, hs⟩ := (mem_E'_iff hE).mp (E'.mul_mem (E'.inv_mem he1) he2)
    have hsa : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) = v := by
      apply ψ.injective
      rw [← hτa, hs]
      show e1⁻¹ (e2 (ψ (aT S g))) = ψ v
      rw [h2, ← h1]
      exact e1.symm_apply_apply _
    have hsM : s ∈ S.Mbar := hEM hsE
    refine ⟨(S.Lbar g).map (MulAut.conj s).toMonoidHom, ?_, ?_, IsPGroup.map
      (IsPGroup.of_card hLcard) _, by rw [Subgroup.card_map_of_injective (MulAut.conj s).injective,
        hLcard]⟩
    · rintro _ ⟨l, hl, rfl⟩
      obtain ⟨hlM, hla⟩ := hLstab hl
      refine ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hsM hlM) (S.Mbar.inv_mem hsM), ?_⟩
      show (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((s⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v
      have hsi : ((s⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = aT S g := by
        rw [← hsa]
        show ((s⁻¹ * s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) = aT S g
        rw [inv_mul_cancel]
        rfl
      rw [hsi, hla, hsa]
    · rintro t ht _ ⟨l, hl, rfl⟩
      have ht' : s⁻¹ * t * s ∈ stab S (aT S g) := by
        refine ⟨S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.inv_mem hsM) ht.1) hsM, ?_⟩
        show ((s⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g))) = aT S g
        rw [hsa, ht.2, ← hsa]
        show ((s⁻¹ * s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) = aT S g
        rw [inv_mul_cancel]
        rfl
      refine ⟨(s⁻¹ * t * s) * l * (s⁻¹ * t * s)⁻¹, hLnorm _ ht' l hl, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hcases : ∀ v : S.Qt, v ≠ 0 → S.q v = 0 → (OB (ψ v) ∧ ¬ HasLbar S v) ∨
      (OA (ψ v) ∧ HasLbar S v) := by
    intro v hv0 hv
    rcases hF.cases (ψ v) (fun h => hv0 (hψ0 v h)) (by rw [hq, hv]) with h | h
    · exact Or.inl ⟨h, hB v h⟩
    · exact Or.inr ⟨h, hA v h⟩
  refine ⟨fun v hv0 hv hvL U hU hvU hUinv => ?_, fun w hw0 hw hwL v hv0 hv hvL hvw => ?_⟩
  ·
    have hvA : OA (ψ v) := by
      rcases hcases v hv0 hv with h | h
      · exact absurd hvL h.2
      · exact h.1
    obtain ⟨e, he, hev⟩ := hF.A_trans _ hvA
    obtain ⟨s, hsE, rfl⟩ := (mem_E'_iff hE).mp he
    let φ : S.Qt ≃ₗ[ZMod 2] V12 := ψ.trans (tau S ψ s)
    have hφ : ∀ u, φ u = ψ ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := fun u => hτa s u
    obtain ⟨w', hw'U, hw'B⟩ := hF.sub6 (U.map (φ : S.Qt →ₗ[ZMod 2] V12))
      (by rw [LinearEquiv.finrank_map_eq, hU]) ⟨v, hvU, hev⟩ (by
        rintro s' hs' _ ⟨u, huU, rfl⟩
        obtain ⟨hs'E, hs'a⟩ := Subgroup.mem_inf.mp hs'
        obtain ⟨r, hrE, rfl⟩ := (mem_E'_iff hE).mp hs'E
        have hrs : s⁻¹ * r * s ∈ stab S v := by
          refine ⟨hEM (E.mul_mem (E.mul_mem (E.inv_mem hsE) hrE) hsE), ψ.injective ?_⟩
          rw [← hτa, map_mul, map_mul, map_inv]
          show (tau S ψ s)⁻¹ (tau S ψ r (tau S ψ s (ψ v))) = ψ v
          rw [hev, mem_stabilizer_GL12.mp hs'a, ← hev]
          exact (tau S ψ s).symm_apply_apply _
        refine ⟨(((s⁻¹ * r * s : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) u, hUinv _ hrs u huU, ?_⟩
        show φ (((s⁻¹ * r * s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = tau S ψ r (φ u)
        rw [hφ, hφ, ← hτa, ← hτa, ← hτa, map_mul, map_mul, map_inv]
        exact (tau S ψ s).apply_symm_apply _)
    obtain ⟨w, hwU, rfl⟩ := hw'U
    have hwB : OB (ψ w) := by
      have h := hF.B_inv _ (E'.inv_mem he) _ hw'B
      rwa [LinearEquiv.coe_coe, hφ, ← hτa, show (tau S ψ s)⁻¹ (tau S ψ s (ψ w)) = ψ w from
        (tau S ψ s).symm_apply_apply _] at h
    obtain ⟨hw0, hwq⟩ := hF.B_sing _ hwB
    exact ⟨w, hwU, fun h => hw0 (by rw [h, map_zero]), by rw [← hq, hwq], hB w hwB⟩
  ·
    have hwB : OB (ψ w) := by
      rcases hcases w hw0 hw with h | h
      · exact h.1
      · exact absurd h.2 hwL
    have hvA : OA (ψ v) := by
      rcases hcases v hv0 hv with h | h
      · exact absurd hvL h.2
      · exact h.1
    obtain ⟨e, he, hew⟩ := hF.B_trans _ hwB
    obtain ⟨s, hsE, rfl⟩ := (mem_E'_iff hE).mp he
    have hv'A : OA (tau S ψ s (ψ v)) := hF.A_inv _ he _ hvA
    have hv'w : f0 (tau S ψ s (ψ v)) w0 = 0 := by
      rw [← hew, hisoF _ he, f0_tr hq]
      exact hvw
    have h64 := hF.orbit _ hv'A hv'w
    refine h64.trans (Set.ncard_le_ncard_of_injOn (fun u => ψ.symm ((tau S ψ s)⁻¹ u)) ?_ ?_)
    · rintro _ ⟨s', hs', rfl⟩
      obtain ⟨hs'E, hs'w⟩ := Subgroup.mem_inf.mp hs'
      obtain ⟨r, hrE, rfl⟩ := (mem_E'_iff hE).mp hs'E
      have hrs : s⁻¹ * r * s ∈ stab S w := by
        refine ⟨hEM (E.mul_mem (E.mul_mem (E.inv_mem hsE) hrE) hsE), ψ.injective ?_⟩
        rw [← hτa, map_mul, map_mul, map_inv]
        show (tau S ψ s)⁻¹ (tau S ψ r (tau S ψ s (ψ w))) = ψ w
        rw [hew, mem_stabilizer_GL12.mp hs'w, ← hew]
        exact (tau S ψ s).symm_apply_apply _
      refine ⟨s⁻¹ * r * s, hrs, ?_⟩
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply, ← hτa, map_mul, map_mul, map_inv]
      rfl
    · intro u₁ _ u₂ _ h
      have h' := congrArg (fun u => tau S ψ s (ψ u)) h
      simpa using h'

end CFSG.GF2Type.Smith1979.IdxFour
