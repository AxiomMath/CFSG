module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZKey

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.UnbalancedGS HeFM HeZF

namespace HeZF

variable {X : Type} [Group X]

@[expose] def conjL (L : Subgroup X) {n : X} (hn : n ∈ normalizer (L : Set X)) : ↥L ≃* ↥L where
  toFun l := ⟨n * l * n⁻¹, (mem_normalizer_iff.mp hn l).mp l.2⟩
  invFun l := ⟨n⁻¹ * l * n, by
    have h := (mem_normalizer_iff.mp (inv_mem hn) l).mp l.2
    rwa [inv_inv] at h⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjL (L : Subgroup X) {n : X} (hn : n ∈ normalizer (L : Set X)) (l : ↥L) :
    ((conjL L hn l : ↥L) : X) = n * l * n⁻¹ := rfl

end HeZF

theorem heldInvolAutFact :
    HeldInvolAutFact := by
  intro X _ _ L ⟨e⟩ n hnN hnn hnC
  by_cases hin : ∃ y ∈ L, y⁻¹ * n ∈ centralizer (L : Set X)
  ·
    left
    obtain ⟨y, hyL, hyc⟩ := hin
    refine ⟨y, hyL, ?_, hyc⟩
    have hy1 : y ≠ 1 := fun h => hnC (by rw [h, inv_one, one_mul] at hyc; exact hyc)
    have hcy : y * (y⁻¹ * n) = (y⁻¹ * n) * y := mem_centralizer_iff.mp hyc y hyL
    have hyy : y * y ∈ L ⊓ centralizer (L : Set X) := by
      refine mem_inf.mpr ⟨mul_mem hyL hyL, ?_⟩
      have h1 : n * n * ((y⁻¹ * n) * (y⁻¹ * n))⁻¹ = y * y :=
        calc n * n * ((y⁻¹ * n) * (y⁻¹ * n))⁻¹
            = y * (y⁻¹ * n) * (y * (y⁻¹ * n)) * ((y⁻¹ * n) * (y⁻¹ * n))⁻¹ := by group
          _ = y * ((y⁻¹ * n) * y) * (y⁻¹ * n) * ((y⁻¹ * n) * (y⁻¹ * n))⁻¹ := by group
          _ = y * (y * (y⁻¹ * n)) * (y⁻¹ * n) * ((y⁻¹ * n) * (y⁻¹ * n))⁻¹ := by rw [← hcy]
          _ = y * y := by group
      rw [← h1]
      exact mul_mem hnn (inv_mem (mul_mem hyc hyc))
    rw [HeZ.inf_centralizer_eq_bot (HeZ.center_eq_bot_of_held e), mem_bot] at hyy
    exact orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  ·
    right
    simp only [not_exists, not_and] at hin
    refine ⟨hin, ?_⟩
    let φ : ↥L ≃* ↥heP := toP e
    let β : MulAut ↥heP := (φ.symm.trans (conjL L hnN)).trans φ
    have hβa : ∀ l : ↥L, β (φ l) = φ (conjL L hnN l) := fun l => by
      show φ (conjL L hnN (φ.symm (φ l))) = _
      rw [MulEquiv.symm_apply_apply]
    have hcc : ∀ l : ↥L, conjL L hnN (conjL L hnN l) = l := fun l => by
      apply Subtype.ext
      rw [coe_conjL, coe_conjL]
      have h1 : (l : X) * (n * n) = (n * n) * l := mem_centralizer_iff.mp hnn l l.2
      calc n * (n * l * n⁻¹) * n⁻¹ = (n * n) * l * (n * n)⁻¹ := by group
        _ = l := by rw [← h1]; group
    have hβ2 : β * β = 1 := by
      refine MulEquiv.ext fun p => ?_
      rw [MulAut.mul_apply, MulAut.one_apply]
      obtain ⟨l, rfl⟩ := φ.surjective p
      rw [hβa, hβa, hcc]
    have hβ1 : β ≠ 1 := by
      intro h
      apply hnC
      rw [mem_centralizer_iff]
      intro l hl
      have h1 := hβa ⟨l, hl⟩
      rw [h, MulAut.one_apply] at h1
      have h2 : n * l * n⁻¹ = l := congrArg Subtype.val (φ.injective h1.symm)
      calc l * n = n * l * n⁻¹ * n := by rw [h2]
        _ = n * l := by group
    have hord : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
    have hinn : β ∉ (MulAut.conj : ↥heP →* MulAut ↥heP).range := by
      rintro ⟨q, hq⟩
      apply hin (φ.symm q : X) (φ.symm q).2
      rw [mem_centralizer_iff]
      intro l hl
      have h1 := hβa ⟨l, hl⟩
      rw [← hq, MulAut.conj_apply] at h1
      have h2 : φ (φ.symm q * ⟨l, hl⟩ * (φ.symm q)⁻¹) = φ (conjL L hnN ⟨l, hl⟩) := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        exact h1
      have h3 : (φ.symm q : X) * l * (φ.symm q : X)⁻¹ = n * l * n⁻¹ :=
        congrArg Subtype.val (φ.injective h2)
      calc l * ((φ.symm q : X)⁻¹ * n)
          = (φ.symm q : X)⁻¹ * ((φ.symm q : X) * l * (φ.symm q : X)⁻¹) * n := by group
        _ = (φ.symm q : X)⁻¹ * (n * l * n⁻¹) * n := by rw [h3]
        _ = (φ.symm q : X)⁻¹ * n * l := by group
    obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
    obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq hbij β hord hinn
    obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
    let ψ : ↥L ≃* ↥heP := φ.trans (conjP ⟨g, hg⟩⁻¹)
    have hψa : ∀ l : ↥L, (ψ l : Equiv.Perm (Fin 8330)) = g⁻¹ * φ l * g := fun l => by
      change (⟨g, hg⟩⁻¹ * φ l * (⟨g, hg⟩⁻¹)⁻¹ : ↥heP).1 = _
      simp only [coe_mul, coe_inv, inv_inv]
    have K1 : ∀ l : ↥L, n * l = l * n ↔
        (x : Equiv.Perm (Fin 8330)) * φ l = φ l * x := by
      intro l
      have hb : ((β (φ l) : ↥heP) : Equiv.Perm (Fin 8330)) =
          x * φ l * (x : Equiv.Perm (Fin 8330))⁻¹ := by
        rw [← hx]
        rfl
      rw [hβa] at hb
      constructor
      · intro h
        have h1 : conjL L hnN l = l := Subtype.ext (by rw [coe_conjL, h]; group)
        rw [h1] at hb
        calc (x : Equiv.Perm (Fin 8330)) * φ l = x * φ l * (x : Equiv.Perm (Fin 8330))⁻¹ * x := by
              group
          _ = φ l * x := by rw [← hb]
      · intro h
        have h1 : ((φ (conjL L hnN l) : ↥heP) : Equiv.Perm (Fin 8330)) = φ l := by
          rw [hb, h]
          group
        have h2 : n * l * n⁻¹ = l := congrArg Subtype.val (φ.injective (Subtype.ext h1))
        calc n * l = n * l * n⁻¹ * n := by group
          _ = l * n := by rw [h2]
    have K2 : ∀ p : Equiv.Perm (Fin 8330), (x : Equiv.Perm (Fin 8330)) * p = p * x ↔
        g⁻¹ * p * g * heAutU = heAutU * (g⁻¹ * p * g) := by
      intro p
      rw [hxg]
      constructor
      · intro h
        calc g⁻¹ * p * g * heAutU = g⁻¹ * (p * (g * heAutU * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * heAutU * g⁻¹ * p) * g := by rw [← h]
          _ = heAutU * (g⁻¹ * p * g) := by group
      · intro h
        calc g * heAutU * g⁻¹ * p = g * (heAutU * (g⁻¹ * p * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * p * g * heAutU) * g⁻¹ := by rw [← h]
          _ = p * (g * heAutU * g⁻¹) := by group
    have hkey : ∀ l : ↥L, n * l = l * n ↔
        (ψ l : Equiv.Perm (Fin 8330)) * heAutU = heAutU * ψ l := fun l => by
      rw [K1 l, hψa]
      exact K2 _
    have hDC : ∀ d ∈ heOuterD, d ∈ heP ∧ d * heAutU = heAutU * d := fun d hd => by
      have h : d ∈ heP ⊓ centralizer ({heAutU} : Set (Equiv.Perm (Fin 8330))) := by
        rw [← heOuterC_eq]
        exact heOuterD_le_C hd
      exact ⟨(mem_inf.mp h).1, mem_centralizer_singleton_iff.mp (mem_inf.mp h).2⟩
    have hDP : heOuterD ≤ heP := fun d hd => (hDC d hd).1
    refine ⟨?_, ?_, ?_⟩
    ·
      obtain ⟨v, hvP, hvu, hvc⟩ := HeGS.exists_twoA_comm_heAutU
      refine ⟨(ψ.symm ⟨v, hvP⟩ : X), ?_, ?_⟩
      · apply (HeT.heldTwoA_iff ψ (ψ.symm ⟨v, hvP⟩).2).mp
        show HeldTwoA heP (ψ (ψ.symm ⟨v, hvP⟩) : Equiv.Perm (Fin 8330))
        rw [MulEquiv.apply_symm_apply]
        exact (HeLay.heldTwoA_heP_iff hvP (orderOf_of_mem_conjClass hvc)).mpr hvc
      · apply (hkey _).mpr
        rw [MulEquiv.apply_symm_apply]
        exact hvu
    ·
      intro S hSL hSn
      have hle : HeT.trS ψ S ≤ heP ⊓ centralizer ({heAutU} : Set (Equiv.Perm (Fin 8330))) := by
        intro p hp
        obtain ⟨s, hs, rfl⟩ := (HeT.mem_trS ψ).mp hp
        refine mem_inf.mpr ⟨(ψ s).2, mem_centralizer_singleton_iff.mpr ?_⟩
        exact (hkey s).mp (mem_centralizer_singleton_iff.mp (hSn hs)).symm
      rw [← HeT.card_trS ψ hSL, ← card_heP_centralizer_heAutU]
      exact card_le_of_le hle
    ·
      refine ⟨HeT.trS ψ.symm heOuterD, HeT.trS_le _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        obtain ⟨d, hd, rfl⟩ := (HeT.mem_trS ψ.symm).mp hq
        rw [mem_centralizer_singleton_iff]
        refine ((hkey (ψ.symm d)).mpr ?_).symm
        rw [MulEquiv.apply_symm_apply]
        exact (hDC _ hd).2
      · have : Group.IsPerfect ↥heOuterD := isPerfect_iff.mpr heOuterD_perfect
        exact isPerfect_iff.mp (Group.IsPerfect.ofSurjective
          (f := (HeT.trEquiv ψ.symm hDP).toMonoidHom) (HeT.trEquiv ψ.symm hDP).surjective)
      · rw [HeT.card_trS ψ.symm hDP, card_heOuterD]
      · rw [← Nat.card_congr (centerCongr (HeT.trEquiv ψ.symm hDP)).toEquiv,
          card_center_heOuterD]
      · have e' : ↥heOuterD ⧸ center ↥heOuterD ≃*
            ↥(HeT.trS ψ.symm heOuterD) ⧸ center ↥(HeT.trS ψ.symm heOuterD) :=
          QuotientGroup.congr _ _ (HeT.trEquiv ψ.symm hDP)
            (map_center_eq (HeT.trEquiv ψ.symm hDP))
        have := heOuterQuot_simple
        exact e'.symm.isSimpleGroup
      · exact four_of_mulEquiv (HeT.trEquiv ψ.symm hDP) HeGS.exists_four_heOuterD

end CFSG.ComponentClassification.GrSLit
