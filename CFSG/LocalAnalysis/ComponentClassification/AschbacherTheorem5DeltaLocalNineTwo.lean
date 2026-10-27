module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineTools

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem inf_orbitProduct_eq_bot (hC : Counterexample G D r Abar) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {a m : Fin r} {Y : Subgroup G}
    (hY2 : IsPGroup 2 Y)
    (hYm : Y ≤ orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ m}) :
    Y ⊓ aschbacherThm5Preimage D (Abar a) = ⊥ := by
  obtain ⟨b, hba⟩ := Strong.exists_ne_index (two_le hC) a
  have hC' := hC.conj g
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  by_contra ht1
  obtain ⟨n, hn⟩ := hY2 ⟨t, ht.1⟩
  apply hg
  exact SixTools.mem_normalizer_of_fusion_conj hC (g := g) (y := t)
    ⟨n, by simpa using congrArg Subtype.val hn⟩ ht1
    (centralizes_of_mem_centralizing (factor_le_centralizing hC.hyp.hcomm hba ht.2))
    (centralizes_of_mem_centralizing ((orbitProduct_le_centralizing hC'.hyp.hcomm
      (j := m) (by simp)) (hYm ht.1)))

theorem normalizer_le_of_le_orbitProduct (hC : Counterexample G D r Abar) (g : G) {m : Fin r}
    {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥)
    (hYm : Y ≤ orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ m}) :
    Subgroup.normalizer (Y : Set G) ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  have hC' := hC.conj g
  obtain ⟨⟨t, htY⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨n, hn⟩ := hY2 ⟨t, htY⟩
  have hcm := orbitProduct_le_centralizing hC'.hyp.hcomm (j := m) (I := {j | j ≠ m}) (by simp)
  intro y hy
  have hyt : y⁻¹ * t * y ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) t).mp htY
    simpa using this
  have h := mem_normalizer_of_fusion hC' m m (t := t) (g := y)
    ⟨n, by simpa using congrArg Subtype.val hn⟩ ht1'
    (centralizes_of_mem_centralizing (hcm (hYm htY)))
    (centralizes_of_mem_centralizing (hcm (hYm hyt)))
  rwa [normalizer_rightConjugate] at h

theorem part_two (hC : Counterexample G D r Abar) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {a m : Fin r} {X R T : Subgroup G}
    (hX2 : IsPGroup 2 X) (hTX : T ≤ X) (hTXne : T ≠ X)
    (hXm : X ≤ orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ m})
    (hXA : X ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hR : IsSylowOf 2 R (aschbacherThm5Preimage D (Abar a) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g))
    (hRT : Nat.card R ≤ Nat.card T) :
    ∃ S : Subgroup G, IsSylowOf 2 S (aschbacherThm5Preimage D (Abar a)) ∧
      S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g ∧ Nat.card S ≤ Nat.card T ∧
      ∀ x ∈ X, ∀ s ∈ S, x * s = s * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) g with hHgdef
  have hR2 := hR.isPGroup
  have hRA : R ≤ A := hR.le.trans inf_le_left
  have hXAbot : X ⊓ A = ⊥ := inf_orbitProduct_eq_bot hC hg hX2 hXm
  have hXR2 : IsPGroup 2 (X ⊔ R : Subgroup G) := IsPGroup.to_sup_of_normal_left' hX2 hR2 hRX
  obtain ⟨W, hW, hXRW⟩ := AschbacherTheorem3.exists_isSylowOf_le hXR2
    (sup_le_sup_right (le_sup_right : X ≤ A ⊔ X) R |>.trans (sup_le le_rfl
      (hRA.trans le_sup_left)) : X ⊔ R ≤ A ⊔ X)
  have hS := hW.inf_of_le_normalizer (le_sup_left : A ≤ A ⊔ X)
    (sup_le Subgroup.le_normalizer hXA)
  set S := W ⊓ A with hSdef
  have hRS : R ≤ S := le_inf (le_sup_right.trans hXRW) hRA
  have hXS : X ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hXRW (Subgroup.mem_sup_left hx)), hXA hx⟩
  have hSR : S ⊓ Hg = R := by
    exact hR.eq_of_le (le_inf hRS (hR.le.trans inf_le_right)) (inf_le_inf_right Hg hS.le)
      (hS.isPGroup.to_le inf_le_left)
  have hXSbot : X ⊓ S = ⊥ := le_bot_iff.mp ((inf_le_inf_left X inf_le_right).trans hXAbot.le)
  have hSHg : S ≤ Hg := by
    by_contra hSHg
    have hRlt : R < S := lt_of_le_of_ne hRS fun h => hSHg (h ▸ hR.le.trans inf_le_right)
    have hRXS : (R ⊔ X) ⊓ S = R := by
      refine le_antisymm (fun y hy => ?_) (le_inf le_sup_left hRS)
      have hy' : y ∈ ((X ⊔ R : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hy.1
      rw [Subgroup.coe_mul_of_right_le_normalizer_left X R hRX] at hy'
      obtain ⟨x, hx, ρ, hρ, rfl⟩ := Set.mem_mul.mp hy'
      have hxS : x ∈ S := by
        have := S.mul_mem hy.2 (S.inv_mem (hRS hρ))
        simpa using this
      have hx1 : x = 1 := by
        have h1 : x ∈ X ⊓ S := ⟨hx, hxS⟩
        rw [hXSbot] at h1
        exact Subgroup.mem_bot.mp h1
      rw [hx1, one_mul]
      exact hρ
    have hSX2 : IsPGroup 2 (S ⊔ X : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hS.isPGroup hX2 hXS
    have hRXlt : R ⊔ X < S ⊔ X := by
      refine lt_of_le_of_ne (sup_le_sup_right hRS X) fun h => ?_
      apply (lt_irrefl R)
      calc R < S := hRlt
        _ = (S ⊔ X) ⊓ S := (inf_eq_right.mpr le_sup_left).symm
        _ = R := by rw [← h, hRXS]
    obtain ⟨y, hyW, hyN, hyRX, -⟩ := exists_sq_mem_of_lt hSX2 hRXlt
    have hy' : y ∈ ((S ⊔ X : Subgroup G) : Set G) := hyW
    rw [Subgroup.coe_mul_of_right_le_normalizer_left S X hXS] at hy'
    obtain ⟨s, hs, x₀, hx₀, rfl⟩ := Set.mem_mul.mp hy'
    have hx₀N : x₀ ∈ Subgroup.normalizer ((R ⊔ X : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_sup_right hx₀)
    have hsN : s ∈ Subgroup.normalizer ((R ⊔ X : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ hx₀N)
      simpa using this
    have hsR : s ∉ R := fun h => hyRX (Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
      (Subgroup.mem_sup_right hx₀))
    have hN₀2 : IsPGroup 2 (S ⊓ Subgroup.normalizer ((R ⊔ X : Subgroup G) : Set G) :
        Subgroup G) := hS.isPGroup.to_le inf_le_left
    have hRN₀ : R < S ⊓ Subgroup.normalizer ((R ⊔ X : Subgroup G) : Set G) :=
      lt_of_le_of_ne (le_inf hRS (le_sup_left.trans Subgroup.le_normalizer)) fun h =>
        hsR (h ▸ ⟨hs, hsN⟩)
    obtain ⟨x, hxN₀, -, hxR, hxx⟩ := exists_sq_mem_of_lt hN₀2 hRN₀
    have hxS : x ∈ S := hxN₀.1
    have hXx : rightConjugate X x ≤ R ⊔ X := by
      rw [← (rightConjugate_eq_self_iff _ x).mpr hxN₀.2]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right x
    have hXXx : X ⊓ rightConjugate X x = ⊥ := by
      by_contra hne
      apply hxR
      have hY2 : IsPGroup 2 (X ⊓ rightConjugate X x : Subgroup G) := hX2.to_le inf_le_left
      have hxY : x ∈ Subgroup.normalizer ((X ⊓ rightConjugate X x : Subgroup G) : Set G) := by
        rw [← rightConjugate_eq_self_iff, AschbacherTheorem3.rightConjugate_inf,
          rightConjugate_mul, (rightConjugate_eq_self_iff X (x * x)).mpr (hRX hxx), inf_comm]
      rw [← hSR]
      exact ⟨hxS, normalizer_le_of_le_orbitProduct hC g hY2 hne (inf_le_left.trans hXm) hxY⟩
    have hXxN : rightConjugate X x ≤ Subgroup.normalizer (X : Set G) :=
      hXx.trans (sup_le hRX Subgroup.le_normalizer)
    have hc1 := AschbacherTheorem3.card_sup_of_le_normalizer hXxN hXXx
    have hc2 := AschbacherTheorem3.card_sup_of_le_normalizer hRX
      (le_bot_iff.mp ((inf_le_inf_left X hRA).trans hXAbot.le))
    have hc3 := Subgroup.card_le_of_le (sup_le le_sup_right hXx :
      X ⊔ rightConjugate X x ≤ R ⊔ X)
    rw [sup_comm R X, hc1, hc2, rightConjugate_card] at hc3
    have hXR : Nat.card X ≤ Nat.card R := Nat.le_of_mul_le_mul_left hc3 Nat.card_pos
    have hTlt : Nat.card T < Nat.card X := by
      have hle := Subgroup.card_le_of_le hTX
      refine lt_of_le_of_ne hle fun h => hTXne ?_
      exact Subgroup.eq_of_le_of_card_ge hTX (le_of_eq h.symm)
    omega
  have hSeqR : S = R := by
    rw [← hSR]
    exact (inf_eq_left.mpr hSHg).symm
  refine ⟨S, hS, hSHg, by rw [hSeqR]; exact hRT, fun x hx s hs => ?_⟩
  have hsX : s ∈ Subgroup.normalizer (X : Set G) := hRX (hSeqR ▸ hs)
  have h1 : x⁻¹ * s⁻¹ * x * s ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsX) x).mp hx
    have h := X.mul_mem (X.inv_mem hx) this
    simpa [mul_assoc] using h
  have h2 : x⁻¹ * s⁻¹ * x * s ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXS hx)) s⁻¹).mp (S.inv_mem hs)
    have h := S.mul_mem this hs
    simpa [mul_assoc] using h
  have h3 : x⁻¹ * s⁻¹ * x * s ∈ X ⊓ S := ⟨h1, h2⟩
  rw [hXSbot, Subgroup.mem_bot] at h3
  calc x * s = s * x * (x⁻¹ * s⁻¹ * x * s) := by group
    _ = s * x := by rw [h3, mul_one]

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5
