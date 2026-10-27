module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndAbstract
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTwelve

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_sylow_L (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a) :
    ∃ P : Subgroup G, IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g) ∧
      d.T ≤ P ∧
      d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
        Subgroup.normalizer (P : Set G) ∧
      IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓
          Subgroup.normalizer (D : Set G)) ∧
      P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) ≤ d.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  have hW2 : IsPGroup 2 W := d.sylowS.isPGroup.to_le inf_le_left
  have hTL : d.T ≤ L := d.sylowT.le.trans inf_le_left
  have hTA : d.T ≤ Subgroup.normalizer (A : Set G) := d.sylowT.le.trans inf_le_right
  have hNA : Subgroup.normalizer (A : Set G) ≤ H := factor_normalizer_le D r Abar hC.hyp.hii a
  have hWH : W ≤ H :=
    (inf_le_left.trans d.sylowS.le).trans ((preimage_le D _).trans Subgroup.le_normalizer)
  have hWT : W ≤ Subgroup.normalizer (d.T : Set G) := by
    intro w hw
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
    exact T_comm_W hC d t ht w hw
  have hWLH : W ≤ Subgroup.normalizer ((L ⊓ H : Subgroup G) : Set G) := fun w hw =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hw.2, Subgroup.le_normalizer (hWH hw)⟩
  obtain ⟨P₁, hP₁, hTP₁, hWP₁⟩ := exists_invariant_sylow hW2 hWLH d.sylowT.isPGroup
    (le_inf hTL (hTA.trans hNA)) hWT
  obtain ⟨P, hP, hP₁P, hWP⟩ := exists_invariant_sylow hW2 (fun w hw => hw.2) hP₁.isPGroup
    (hP₁.le.trans inf_le_left) hWP₁
  refine ⟨P, hP, hTP₁.trans hP₁P, hWP, ?_, ?_⟩
  · have heq := hP₁.eq_of_le (le_inf hP₁P (hP₁.le.trans inf_le_right))
      (inf_le_inf_right H hP.le) (hP.isPGroup.to_le inf_le_left)
    rw [heq]
    exact hP₁
  · have heq := d.sylowT.eq_of_le (le_inf (hTP₁.trans hP₁P) hTA)
      (inf_le_inf_right _ hP.le) (hP.isPGroup.to_le inf_le_left)
    rw [heq]

omit [Finite G] in
theorem rightConjugate_sup (X Y : Subgroup G) (g : G) :
    rightConjugate (X ⊔ Y) g = rightConjugate X g ⊔ rightConjugate Y g :=
  Subgroup.map_sup _ _ _

omit [Finite G] in
theorem rightConjugate_conj_conj (K : Subgroup G) (g z : G) :
    rightConjugate (rightConjugate (rightConjugate K g⁻¹) z) g =
      rightConjugate K (g⁻¹ * z * g) := by
  rw [rightConjugate_mul, rightConjugate_mul, mul_assoc]

theorem swap_lemma_6_10 (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hLH : ¬ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hWZ : ¬ d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      factorZStar D Abar a) :
    ∃ P : Subgroup G, ∃ y : G,
      IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g) ∧
      P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) ≤ d.T ∧
      y ∈ P ∧ y ∈ Subgroup.normalizer (D : Set G) ∧
      y ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) ∧
      IsMulCommutative (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ⊔
          rightConjugate (d.S ⊓ Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) y : Subgroup G) ∧
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ⊔
          rightConjugate (d.S ⊓ Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) y) ⊓ P ⊔
        (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) =
      d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ⊔
          rightConjugate (d.S ⊓ Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, -, hWP, hPH, hPT⟩ := exists_sylow_L hC d
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set W := d.S ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) with hWdef
  obtain ⟨-, -, hne', U'', hU''⟩ := inv_mem_deltaConjugates hloc hC (datum_mem_delta d)
  have hT'' : IsSylowOf 2 (rightConjugate W d.g⁻¹) (rightConjugate A d.g⁻¹ ⊓
      Subgroup.normalizer (A : Set G)) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hW d.g⁻¹
    rwa [rightConjugate_inf_normalizer'] at h1
  have hS'' : IsSylowOf 2 (rightConjugate P d.g⁻¹) A := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hP d.g⁻¹
    rwa [rightConjugate_rightConjugate_inv] at h1
  have hinv'' : rightConjugate W d.g⁻¹ ≤
      Subgroup.normalizer (rightConjugate P d.g⁻¹ : Set G) :=
    AschbacherTheorem3.rightConjugate_le_normalizer hWP d.g⁻¹
  have hI'' : IsSylowOf 2 (rightConjugate P d.g⁻¹ ⊓ rightConjugate H d.g⁻¹)
      (A ⊓ rightConjugate H d.g⁻¹) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hPH d.g⁻¹
    rwa [AschbacherTheorem3.rightConjugate_inf, AschbacherTheorem3.rightConjugate_inf,
      rightConjugate_rightConjugate_inv] at h1
  let d'' : DeltaDatum D Abar a := ⟨d.g⁻¹, hne', U'', hU'', rightConjugate W d.g⁻¹, hT'',
    rightConjugate P d.g⁻¹, hS'', hinv'', hI''⟩
  have hA'' : ¬ A ⊓ rightConjugate H d.g⁻¹ ≤
      Subgroup.normalizer (rightConjugate A d.g⁻¹ : Set G) := by
    intro hle
    apply hLH
    intro y hy
    have h1 : d.g * y * d.g⁻¹ ∈ A ⊓ rightConjugate H d.g⁻¹ := by
      refine Subgroup.mem_inf.mpr ⟨(mem_rightConjugate_iff A d.g y).mp hy.1, ?_⟩
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hy.2
    have h2 := hle h1
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff] at h2
    simpa [mul_assoc] using h2
  have hTZ'' : ¬ rightConjugate W d.g⁻¹ ≤ rightConjugate (factorZStar D Abar a) d.g⁻¹ := by
    intro hle
    apply hWZ
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hle d.g
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one, rightConjugate_mul,
      inv_mul_cancel, rightConjugate_one] at h1
  obtain ⟨y'', hy'', ⟨b, hba, hb⟩, -, -, hR, hab⟩ := hloc.lemma_6_10 hC d'' hA'' hTZ''
  set y := d.g⁻¹ * y'' * d.g with hydef
  have hyP : y ∈ P := by
    have h1 := (mem_rightConjugate_iff P d.g⁻¹ y'').mp hy''.1
    rwa [inv_inv] at h1
  have hyH : y ∈ H := by
    have h1 := (mem_rightConjugate_iff H d.g⁻¹ y'').mp hy''.2
    rwa [inv_inv] at h1
  have hback : ∀ K : Subgroup G, rightConjugate (rightConjugate K d.g⁻¹) d.g = K := fun K => by
    rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  have hyN : y ∉ Subgroup.normalizer (A : Set G) := by
    intro hyA
    have h1 : rightConjugate (rightConjugate (rightConjugate A d.g⁻¹) y'') d.g =
        rightConjugate (rightConjugate (aschbacherThm5Preimage D (Abar b)) d.g⁻¹) d.g := by
      rw [← hb]
    rw [rightConjugate_conj_conj, hback, ← hydef, (rightConjugate_eq_self_iff A y).mpr hyA] at h1
    exact hba (factor_injective hC h1).symm
  refine ⟨P, y, hP, hPT, hyP, hyH, hyN, ?_, ?_⟩
  · have h1 := AschbacherTheorem3.isMulCommutative_rightConjugate hab d.g
    rwa [rightConjugate_sup, rightConjugate_conj_conj, hback, ← hydef] at h1
  · have h1 : rightConjugate ((rightConjugate W d.g⁻¹ ⊔ rightConjugate (rightConjugate W d.g⁻¹)
        y'') ⊓ rightConjugate P d.g⁻¹ ⊔ rightConjugate W d.g⁻¹) d.g =
        rightConjugate (rightConjugate W d.g⁻¹ ⊔ rightConjugate (rightConjugate W d.g⁻¹) y'')
          d.g := by
      rw [hR]
    simp only [rightConjugate_sup, AschbacherTheorem3.rightConjugate_inf,
      rightConjugate_conj_conj, hback, ← hydef] at h1
    exact h1

theorem mem_factorZStar_of_comm (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    (hr : r = 2) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hLH : ¬ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    {e : G} (heS : e ∈ d.S)
    (he : ∀ u ∈ AschbacherTheorem3.omegaOne d.T, e⁻¹ * u * e = u → u = 1) {w : G}
    (hwW : w ∈ d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
    (hwe : e * w = w * e) : w ∈ factorZStar D Abar a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set W := d.S ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) with hWdef
  by_cases hWZ : W ≤ factorZStar D Abar a
  · exact hWZ hwW
  obtain ⟨P, y, -, hPT, hyP, hyH, hyN, hab, hR⟩ := swap_lemma_6_10 hloc hC d hW hLH hWZ
  obtain ⟨b, hba⟩ := exists_other hC a
  have hyN' : y⁻¹ ∉ Subgroup.normalizer (A : Set G) := fun h =>
    hyN (by simpa using (Subgroup.normalizer (A : Set G)).inv_mem h)
  have hAy : rightConjugate A y⁻¹ = aschbacherThm5Preimage D (Abar b) :=
    rightConjugate_eq_other hC hr (H.inv_mem hyH) hba hyN'
  have hWA : W ≤ A := inf_le_left.trans d.sylowS.le
  have heA : e ∈ A := d.sylowS.le heS
  set R := (W ⊔ rightConjugate W y) ⊓ P with hRdef
  have hback : rightConjugate (rightConjugate W y) y⁻¹ = W := by
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hR' : rightConjugate R y⁻¹ ⊔ rightConjugate W y⁻¹ = rightConjugate W y⁻¹ ⊔ W := by
    have h1 : rightConjugate (R ⊔ W) y⁻¹ = rightConjugate (W ⊔ rightConjugate W y) y⁻¹ := by
      rw [hR]
    rwa [rightConjugate_sup, rightConjugate_sup, hback] at h1
  have hab' : IsMulCommutative (rightConjugate W y⁻¹ ⊔ W : Subgroup G) := by
    have h1 := AschbacherTheorem3.isMulCommutative_rightConjugate hab y⁻¹
    rwa [rightConjugate_sup, hback] at h1
  have hcomm : ∀ x ∈ rightConjugate W y⁻¹ ⊔ W, ∀ x' ∈ rightConjugate W y⁻¹ ⊔ W,
      x * x' = x' * x :=
    fun x hx x' hx' => congrArg Subtype.val (hab'.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hRle : rightConjugate R y⁻¹ ≤ rightConjugate W y⁻¹ ⊔ W := hR' ▸ le_sup_left
  have hN : rightConjugate R y⁻¹ ≤ Subgroup.normalizer (rightConjugate W y⁻¹ : Set G) := by
    intro q hq
    refine Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w' hw' => ?_)
    exact hcomm _ (Subgroup.mem_sup_left hw') _ (hRle hq)
  have hw' : w ∈ ((rightConjugate R y⁻¹ ⊔ rightConjugate W y⁻¹ : Subgroup G) : Set G) := by
    rw [hR']
    exact Subgroup.mem_sup_right hwW
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hw'
  obtain ⟨q, hq, w₁, hw₁, hqw⟩ := Set.mem_mul.mp hw'
  have hRP : rightConjugate R y⁻¹ ≤ P := by
    rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (P.inv_mem hyP)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate inf_le_right y⁻¹
  have hNA : rightConjugate W y⁻¹ ⊔ W ≤ Subgroup.normalizer (A : Set G) := by
    refine sup_le ?_ (hWA.trans Subgroup.le_normalizer)
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hWA y⁻¹
    rw [hAy] at h1
    exact (h1.trans (preimage_le D _)).trans (le_normalizer_factor hC a)
  have hqT : q ∈ d.T := hPT ⟨hRP hq, hNA (hRle hq)⟩
  have hw₁b : w₁ ∈ aschbacherThm5Preimage D (Abar b) := by
    rw [← hAy]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hWA y⁻¹ hw₁
  have hcS : q⁻¹ * e⁻¹ * q * e ∈ d.S := by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (d.S : Set G)).inv_mem (d.invariant hqT)) e⁻¹).mp (d.S.inv_mem heS)
    rw [inv_inv] at h1
    exact d.S.mul_mem h1 heS
  have hcO : q⁻¹ * e⁻¹ * q * e ∈ aschbacherThm5Core D := by
    have h := hwe
    rw [← hqw] at h
    have heq : q⁻¹ * e⁻¹ * q * e = w₁⁻¹⁻¹ * e⁻¹ * w₁⁻¹ * e :=
      calc q⁻¹ * e⁻¹ * q * e = q⁻¹ * e⁻¹ * (q * w₁ * e) * (e⁻¹ * w₁⁻¹ * e) := by group
        _ = q⁻¹ * e⁻¹ * (e * (q * w₁)) * (e⁻¹ * w₁⁻¹ * e) := by rw [h]
        _ = w₁⁻¹⁻¹ * e⁻¹ * w₁⁻¹ * e := by group
    rw [heq]
    exact cross_factor_centralizes D Abar hC.hyp.hcomm a b (Ne.symm hba) w₁⁻¹
      ((aschbacherThm5Preimage D (Abar b)).inv_mem hw₁b) e heA
  have hc1 : q⁻¹ * e⁻¹ * q * e = 1 :=
    eq_one_of_mem_core hcO (twoElt_of_mem d.sylowS.isPGroup hcS)
  have hqe : Commute q e := by
    show q * e = e * q
    calc q * e = e * q * (q⁻¹ * e⁻¹ * q * e) := by group
      _ = e * q := by rw [hc1, mul_one]
  have hq1 : q = 1 := by
    by_contra hq1
    have hZ2 : IsPGroup 2 (Subgroup.zpowers q) :=
      d.sylowT.isPGroup.to_le (Subgroup.zpowers_le.mpr hqT)
    have hZ1 : Subgroup.zpowers q ≠ ⊥ := by
      rwa [Ne, Subgroup.zpowers_eq_bot]
    obtain ⟨r₀, hr₀, hr₀2⟩ := EndSetting.exists_involution hZ2 hZ1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr₀
    have hsq : (q ^ k) ^ 2 = 1 := by
      rw [← hr₀2]
      exact pow_orderOf_eq_one _
    have hU : q ^ k ∈ AschbacherTheorem3.omegaOne d.T := mem_omegaOne (d.T.zpow_mem hqT k) hsq
    have hc : e⁻¹ * q ^ k * e = q ^ k := by
      have h1 : q ^ k * e = e * q ^ k := (hqe.zpow_left k).eq
      calc e⁻¹ * q ^ k * e = e⁻¹ * (q ^ k * e) := by group
        _ = q ^ k := by rw [h1]; group
    have h1 := he _ hU hc
    rw [h1, orderOf_one] at hr₀2
    exact absurd hr₀2 (by norm_num)
  rw [hq1, one_mul] at hqw
  rw [← hqw]
  exact mem_factorZStar_of_mem_other hC hba (hqw ▸ hWA hwW) hw₁b

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
