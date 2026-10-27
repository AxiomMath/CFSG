module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Lemmas

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC

theorem signalizer_eq_bot_of_sc {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2)
    (hSC : ∀ y ∈ centralizer (D : Set X), y ^ p = 1 → y ∈ D)
    (hC : ∀ d ∈ D, d ≠ 1 →
      GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥) :
    ∀ T : Subgroup X, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set X) → T = ⊥ := by
  intro T hT hDT
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative D := hD.1
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hcent : ∀ d ∈ D, d ≠ 1 → T ⊓ centralizer ({d} : Set X) = ⊥ := by
    intro d hd hd1
    obtain ⟨hlay, hcore⟩ := hC d hd hd1
    have hDH : D ≤ centralizer ({d} : Set X) := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.2 (hDc w hw d hd)
    have hB : IsElemAbelian p (D.subgroupOf (centralizer ({d} : Set X))) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        simpa using hDc _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
      · apply Subtype.ext
        simpa using hD.2 _ (Subgroup.mem_subgroupOf.1 hy)
    have hmax : ∀ E' : Subgroup (centralizer ({d} : Set X)), IsElemAbelian p E' →
        D.subgroupOf (centralizer ({d} : Set X)) ≤ E' →
        E' = D.subgroupOf (centralizer ({d} : Set X)) := by
      intro E' hE' hBE'
      haveI : IsMulCommutative E' := hE'.1
      refine le_antisymm (fun y hy => ?_) hBE'
      have hyC : (y : X) ∈ centralizer (D : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwE' : (⟨w, hDH hw⟩ : centralizer ({d} : Set X)) ∈ E' :=
          hBE' (Subgroup.mem_subgroupOf.2 hw)
        have hc := congrArg Subtype.val (setLike_mul_comm hy hwE')
        simp only [Subgroup.coe_mul] at hc
        exact hc.symm
      have hyp : (y : X) ^ p = 1 := by
        simpa using congrArg (centralizer ({d} : Set X)).subtype (hE'.2 y hy)
      exact Subgroup.mem_subgroupOf.2 (hSC _ hyC hyp)
    have key := GL83.I_20_1_proved (centralizer ({d} : Set X)) p hp hp2
      (glaPLayer_top_eq_bot_of_subgroup hp (centralizer ({d} : Set X)) hlay)
      (D.subgroupOf (centralizer ({d} : Set X))) hB hmax
    have hcoreH := glaPPrimeCoreOf_top_eq_bot_of_subgroup (centralizer ({d} : Set X)) hcore
    have hYcop : Nat.Coprime p (Nat.card ↥((T ⊓ centralizer ({d} : Set X)).subgroupOf
        (centralizer ({d} : Set X)))) := by
      have h1 : Nat.card ↥((T ⊓ centralizer ({d} : Set X)).subgroupOf
          (centralizer ({d} : Set X))) = Nat.card ↥(T ⊓ centralizer ({d} : Set X)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : T ⊓ centralizer ({d} : Set X) ≤ centralizer ({d} : Set X))).toEquiv
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left : T ⊓ centralizer ({d} : Set X) ≤ T)) hT
    have hYnorm : D.subgroupOf (centralizer ({d} : Set X)) ≤
        normalizer ((((T ⊓ centralizer ({d} : Set X)).subgroupOf
          (centralizer ({d} : Set X)) : Subgroup (centralizer ({d} : Set X))) :
          Set (centralizer ({d} : Set X)))) := by
      intro b hb
      have hβ : (b : X) ∈ D := Subgroup.mem_subgroupOf.1 hb
      have hβd : (b : X) * d = d * (b : X) := hDc _ hβ d hd
      have hH' : ∀ z : X, z ∈ centralizer ({d} : Set X) ↔
          (b : X) * z * (b : X)⁻¹ ∈ centralizer ({d} : Set X) := by
        intro z
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
        have hinv : (b : X)⁻¹ * d = d * (b : X)⁻¹ := by
          calc (b : X)⁻¹ * d = (b : X)⁻¹ * (d * (b : X)) * (b : X)⁻¹ := by group
            _ = (b : X)⁻¹ * ((b : X) * d) * (b : X)⁻¹ := by rw [← hβd]
            _ = d * (b : X)⁻¹ := by group
        have e1 : (b : X) * z * (b : X)⁻¹ * d = (b : X) * (z * d) * (b : X)⁻¹ := by
          calc (b : X) * z * (b : X)⁻¹ * d = (b : X) * z * ((b : X)⁻¹ * d) := by group
            _ = (b : X) * z * (d * (b : X)⁻¹) := by rw [hinv]
            _ = (b : X) * (z * d) * (b : X)⁻¹ := by group
        have e2 : d * ((b : X) * z * (b : X)⁻¹) = (b : X) * (d * z) * (b : X)⁻¹ := by
          calc d * ((b : X) * z * (b : X)⁻¹) = (d * (b : X)) * z * (b : X)⁻¹ := by group
            _ = ((b : X) * d) * z * (b : X)⁻¹ := by rw [← hβd]
            _ = (b : X) * (d * z) * (b : X)⁻¹ := by group
        rw [e1, e2]
        constructor
        · intro h
          rw [h]
        · intro h
          simp only [mul_left_inj, mul_right_inj] at h
          exact h
      intro y
      have hT' : (y : X) ∈ T ↔ (b : X) * (y : X) * (b : X)⁻¹ ∈ T :=
        Subgroup.mem_normalizer_iff.1 (hDT hβ) (y : X)
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.mem_inf]
      exact and_congr hT' (hH' (y : X))
    have hY : (T ⊓ centralizer ({d} : Set X)).subgroupOf (centralizer ({d} : Set X)) ≤
        GLAPPrimeCoreOf p (⊤ : Subgroup (centralizer ({d} : Set X))) := by
      rw [← key]
      exact le_iSup_of_le _ (le_iSup_of_le hYcop (le_iSup_of_le hYnorm le_rfl))
    rw [hcoreH] at hY
    refine eq_bot_iff.2 fun t ht => Subgroup.mem_bot.2 ?_
    have ht' : (⟨t, ht.2⟩ : centralizer ({d} : Set X)) ∈
        (T ⊓ centralizer ({d} : Set X)).subgroupOf (centralizer ({d} : Set X)) :=
      Subgroup.mem_subgroupOf.2 ht
    have h1 := hY ht'
    rw [Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hp hD
    hcard.ge hDT hT
  exact hgen.symm.trans (iSup_eq_bot.2 fun a => iSup_eq_bot.2 fun ha =>
    iSup_eq_bot.2 fun ha1 => hcent a ha ha1)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291
