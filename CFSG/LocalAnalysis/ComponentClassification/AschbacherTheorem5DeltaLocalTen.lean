module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNine

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix SectionSix.BarTools DeltaLocal

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace DeltaLocal.Ten

theorem exists_moving_of_sylow (hyp : Hyp61 G D r Abar) (hr : r = 2) {a : Fin r}
    {K Q : Subgroup G} (hK : K ≤ Subgroup.normalizer (D : Set G)) (hQ : IsSylowOf 2 Q K)
    (hKA : ¬ K ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G)) :
    ∃ y ∈ Q, ∃ b, b ≠ a ∧
      rightConjugate (aschbacherThm5Preimage D (Abar a)) y = aschbacherThm5Preimage D (Abar b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : ∀ z ∈ Subgroup.normalizer (D : Set G), ∀ j : Fin r, ∃ j',
      rightConjugate (aschbacherThm5Preimage D (Abar j)) z = aschbacherThm5Preimage D (Abar j') :=
    fun z hz j => hyp.hperm z⁻¹ (Subgroup.inv_mem _ hz) j
  have hinj : ∀ (z : G) {j₁ j₂ : Fin r},
      rightConjugate (aschbacherThm5Preimage D (Abar j₁)) z =
        rightConjugate (aschbacherThm5Preimage D (Abar j₂)) z → j₁ = j₂ := fun z _ _ h =>
    SixTools.index_eq_of_preimage_eq hyp (Subgroup.map_injective
      (f := (MulAut.conj z⁻¹).toMonoidHom) (MulAut.conj z⁻¹).injective h)
  have htwo : ∀ {j k : Fin r}, j ≠ k → ∀ l : Fin r, l = j ∨ l = k := by
    intro j k hjk l
    have h1 := l.isLt
    have h2 := j.isLt
    have h3 := k.isLt
    have h4 : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    rw [Fin.ext_iff, Fin.ext_iff]
    omega
  have hfix : ∀ z ∈ Subgroup.normalizer (D : Set G), ∀ {j k : Fin r}, j ≠ k →
      rightConjugate (aschbacherThm5Preimage D (Abar k)) z = aschbacherThm5Preimage D (Abar k) →
      rightConjugate (aschbacherThm5Preimage D (Abar j)) z =
        aschbacherThm5Preimage D (Abar j) := by
    intro z hz j k hjk hk
    obtain ⟨l, hl⟩ := hπ z hz j
    rcases htwo hjk l with h | h
    · rw [hl, h]
    · exact absurd (hinj z (hl.trans (by rw [h]; exact hk.symm))) hjk
  have hsq : ∀ z ∈ Subgroup.normalizer (D : Set G), ∀ j : Fin r,
      rightConjugate (aschbacherThm5Preimage D (Abar j)) (z * z) =
        aschbacherThm5Preimage D (Abar j) := by
    intro z hz j
    obtain ⟨l, hl⟩ := hπ z hz j
    by_cases hlj : l = j
    · subst hlj
      rw [← rightConjugate_mul, hl, hl]
    · obtain ⟨l', hl'⟩ := hπ z hz l
      rcases htwo hlj l' with h | h
      · exact absurd (hinj z (hl.trans (by rw [hl', h]))).symm hlj
      · rw [← rightConjugate_mul, hl, hl', h]
  obtain ⟨x, hxK, hxN⟩ := IsConcreteLE.not_le_iff_exists.mp hKA
  have hxA : rightConjugate (aschbacherThm5Preimage D (Abar a)) x ≠
      aschbacherThm5Preimage D (Abar a) := fun h => hxN ((rightConjugate_eq_self_iff _ x).mp h)
  obtain ⟨e, o, ho, hno⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  obtain ⟨t, rfl⟩ := ho
  have hpow : ∀ n : ℕ, rightConjugate (aschbacherThm5Preimage D (Abar a)) ((x * x) ^ n) =
      aschbacherThm5Preimage D (Abar a) := by
    intro n
    induction n with
    | zero => rw [pow_zero, rightConjugate_one]
    | succ n ih => rw [pow_succ, ← rightConjugate_mul, ih, hsq x (hK hxK) a]
  have hx₀ : rightConjugate (aschbacherThm5Preimage D (Abar a)) (x ^ (2 * t + 1)) =
      rightConjugate (aschbacherThm5Preimage D (Abar a)) x := by
    rw [pow_succ, pow_mul, ← rightConjugate_mul, sq, hpow]
  have hx₀2 : (x ^ (2 * t + 1)) ^ (2 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hno, pow_orderOf_eq_one]
  have hx₀K : x ^ (2 * t + 1) ∈ K := K.pow_mem hxK _
  obtain ⟨c, hcK, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hQ
    (Five.isPGroup_zpowers_of_pow hx₀2) (Subgroup.zpowers_le.mpr hx₀K)
  have hyQ : c⁻¹ * x ^ (2 * t + 1) * c ∈ Q :=
    hc (AschbacherTheorem3.conj_mem_rightConjugate (Subgroup.mem_zpowers _) c)
  have hyN : c⁻¹ * x ^ (2 * t + 1) * c ∈ Subgroup.normalizer (D : Set G) :=
    hK (K.mul_mem (K.mul_mem (K.inv_mem hcK) hx₀K) hcK)
  obtain ⟨b, hb⟩ := hπ _ hyN a
  refine ⟨_, hyQ, b, fun hba => ?_, hb⟩
  rw [hba] at hb
  obtain ⟨j, hj⟩ := hπ c⁻¹ (Subgroup.inv_mem _ (hK hcK)) a
  have hjx : rightConjugate (aschbacherThm5Preimage D (Abar j)) (x ^ (2 * t + 1)) =
      aschbacherThm5Preimage D (Abar j) := by
    have h1 := congrArg (fun L => rightConjugate L c⁻¹) hb
    simp only [rightConjugate_mul, mul_inv_cancel_right] at h1
    rw [← hj, rightConjugate_mul, h1]
  apply hxA
  rw [← hx₀]
  by_cases hja : j = a
  · rw [hja] at hjx
    exact hjx
  · exact hfix _ (hK hx₀K) (Ne.symm hja) hjx

theorem of_moving (hC : Counterexample G D r Abar) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {a b : Fin r} (hba : b ≠ a)
    {T S : Subgroup G} {y : G} (hT2 : IsPGroup 2 T)
    (hTL : T ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) g)
    (hS2 : IsPGroup 2 S) (hSA : S ≤ aschbacherThm5Preimage D (Abar a))
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hyS : y ∈ S)
    (hLy : rightConjugate (rightConjugate (aschbacherThm5Preimage D (Abar a)) g) y =
      rightConjugate (aschbacherThm5Preimage D (Abar b)) g)
    (hTZ : ¬ T ≤ rightConjugate (factorZStar D Abar a) g) :
    (T ⊔ rightConjugate T y) ⊓ S ≠ ⊥ ∧
      (T ⊔ rightConjugate T y) ⊓ S ≤ AschbacherTheorem3.centerOf (T ⊔ rightConjugate T y) ∧
      (T ⊔ rightConjugate T y) ⊓ S ⊔ T = T ⊔ rightConjugate T y ∧
      IsMulCommutative (T ⊔ rightConjugate T y : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D' := rightConjugate D g with hD'def
  set Abar' := conjFactors D Abar g with hAbar'def
  have hC' : Counterexample G D' r Abar' := hC.conj g
  set K := T ⊔ rightConjugate T y with hKdef
  set R := K ⊓ S with hRdef
  have hab : a ≠ b := Ne.symm hba
  have hLa : rightConjugate (aschbacherThm5Preimage D (Abar a)) g =
      aschbacherThm5Preimage D' (Abar' a) := (preimage_conjFactors D Abar g a).symm
  have hLb : rightConjugate (aschbacherThm5Preimage D (Abar b)) g =
      aschbacherThm5Preimage D' (Abar' b) := (preimage_conjFactors D Abar g b).symm
  have hTyL : rightConjugate T y ≤ rightConjugate (aschbacherThm5Preimage D (Abar b)) g := by
    rw [← hLy]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hTL y
  have hKD : K ≤ D' := sup_le ((hTL.trans (le_of_eq hLa)).trans (preimage_le D' _))
    ((hTyL.trans (le_of_eq hLb)).trans (preimage_le D' _))
  have hST2 : IsPGroup 2 (S ⊔ T : Subgroup G) := IsPGroup.to_sup_of_normal_left' hS2 hT2 hTS
  have hconj : ∀ u ∈ rightConjugate T y, y * u * y⁻¹ ∈ T := fun u hu =>
    (mem_rightConjugate_iff T y u).mp hu
  have hKST : K ≤ S ⊔ T := by
    refine sup_le le_sup_right fun u hu => ?_
    have h1 : y⁻¹ * (y * u * y⁻¹) * y ∈ S ⊔ T :=
      (S ⊔ T).mul_mem ((S ⊔ T).mul_mem ((S ⊔ T).inv_mem (Subgroup.mem_sup_left hyS))
        (Subgroup.mem_sup_right (hconj u hu))) (Subgroup.mem_sup_left hyS)
    rwa [show y⁻¹ * (y * u * y⁻¹) * y = u by group] at h1
  have hc1 : ∀ t ∈ T, (y⁻¹ * t * y)⁻¹ * t ∈ R := by
    intro t ht
    refine ⟨K.mul_mem (K.inv_mem (Subgroup.mem_sup_right
      (AschbacherTheorem3.conj_mem_rightConjugate ht y))) (Subgroup.mem_sup_left ht), ?_⟩
    have h1 : t⁻¹ * y * t⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTS ht)) y).mp hyS
    rw [inv_inv] at h1
    rw [show (y⁻¹ * t * y)⁻¹ * t = y⁻¹ * (t⁻¹ * y * t) by group]
    exact S.mul_mem (S.inv_mem hyS) h1
  have hc2 : ∀ t ∈ T, t⁻¹ * (y⁻¹ * t * y) ∈ R := by
    intro t ht
    refine ⟨K.mul_mem (K.inv_mem (Subgroup.mem_sup_left ht)) (Subgroup.mem_sup_right
      (AschbacherTheorem3.conj_mem_rightConjugate ht y)), ?_⟩
    have h1 : t⁻¹ * y⁻¹ * t⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTS ht)) y⁻¹).mp (S.inv_mem hyS)
    rw [inv_inv] at h1
    rw [show t⁻¹ * (y⁻¹ * t * y) = t⁻¹ * y⁻¹ * t * y by group]
    exact S.mul_mem h1 hyS
  have hTR : ∀ t ∈ T, ∀ ρ ∈ R, t * ρ = ρ * t := by
    intro t ht ρ hρ
    have hρK : ρ ∈ K := hρ.1
    have hρS : ρ ∈ S := hρ.2
    have hw1 : t⁻¹ * ρ⁻¹ * t * ρ ∈ S := by
      have h1 : t⁻¹ * ρ⁻¹ * t⁻¹⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTS ht)) ρ⁻¹).mp (S.inv_mem hρS)
      rw [inv_inv] at h1
      exact S.mul_mem h1 hρS
    have hw2 : t⁻¹ * ρ⁻¹ * t * ρ ∈ aschbacherThm5Preimage D' (Abar' a) := by
      have hρN : ρ⁻¹ ∈ Subgroup.normalizer (aschbacherThm5Preimage D' (Abar' a) : Set G) :=
        Subgroup.inv_mem _ (Eight.le_normalizer_factor hC' a (hKD hρK))
      have htL : t ∈ aschbacherThm5Preimage D' (Abar' a) := by rw [← hLa]; exact hTL ht
      have h1 : ρ⁻¹ * t * ρ⁻¹⁻¹ ∈ aschbacherThm5Preimage D' (Abar' a) :=
        (Subgroup.mem_normalizer_iff.mp hρN t).mp htL
      rw [inv_inv] at h1
      have h2 := (aschbacherThm5Preimage D' (Abar' a)).mul_mem
        ((aschbacherThm5Preimage D' (Abar' a)).inv_mem htL) h1
      simpa [mul_assoc] using h2
    have hbot := Nine.inf_orbitProduct_eq_bot hC hg (a := a) (m := b)
      (Y := S ⊓ aschbacherThm5Preimage D' (Abar' a)) (hS2.to_le inf_le_left)
      (inf_le_right.trans (factor_le_orbitProduct (I := {j | j ≠ b}) hab))
    have hw : t⁻¹ * ρ⁻¹ * t * ρ ∈
        (S ⊓ aschbacherThm5Preimage D' (Abar' a)) ⊓ aschbacherThm5Preimage D (Abar a) :=
      ⟨⟨hw1, hw2⟩, hSA hw1⟩
    rw [hbot, Subgroup.mem_bot] at hw
    calc t * ρ = ρ * t * (t⁻¹ * ρ⁻¹ * t * ρ) := by group
      _ = ρ * t := by rw [hw, mul_one]
  have hTyT : ∀ u ∈ rightConjugate T y, ∀ t ∈ T, u * t = t * u := by
    intro u hu t ht
    have h1 := cross_factor_centralizes D' Abar' hC'.hyp.hcomm a b hab u
      (by rw [← hLb]; exact hTyL hu) t (by rw [← hLa]; exact hTL ht)
    have h2 : u⁻¹ * t⁻¹ * u * t ∈ S ⊔ T := by
      have huS : u ∈ S ⊔ T := hKST (Subgroup.mem_sup_right hu)
      have htS : t ∈ S ⊔ T := Subgroup.mem_sup_right ht
      exact (S ⊔ T).mul_mem ((S ⊔ T).mul_mem ((S ⊔ T).mul_mem ((S ⊔ T).inv_mem huS)
        ((S ⊔ T).inv_mem htS)) huS) htS
    have h3 := Exclusion.eq_one_of_mem_core_of_isPGroup hST2 h2 h1
    calc u * t = t * u * (u⁻¹ * t⁻¹ * u * t) := by group
      _ = t * u := by rw [h3, mul_one]
  have hTab : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t := by
    intro t ht t' ht'
    have hu : y⁻¹ * t * y ∈ rightConjugate T y := AschbacherTheorem3.conj_mem_rightConjugate ht y
    have e1 := hTR t' ht' _ (hc1 t ht)
    have e2 := hTyT _ hu t' ht'
    have htu : (y⁻¹ * t * y) * ((y⁻¹ * t * y)⁻¹ * t) = t := mul_inv_cancel_left _ t
    calc t * t' = (y⁻¹ * t * y) * ((y⁻¹ * t * y)⁻¹ * t) * t' := by rw [htu]
      _ = (y⁻¹ * t * y) * (((y⁻¹ * t * y)⁻¹ * t) * t') := mul_assoc _ _ _
      _ = (y⁻¹ * t * y) * (t' * ((y⁻¹ * t * y)⁻¹ * t)) := by rw [← e1]
      _ = (y⁻¹ * t * y) * t' * ((y⁻¹ * t * y)⁻¹ * t) := (mul_assoc _ _ _).symm
      _ = t' * (y⁻¹ * t * y) * ((y⁻¹ * t * y)⁻¹ * t) := by rw [e2]
      _ = t' * t := by rw [mul_assoc, htu]
  have hTyab : ∀ u ∈ rightConjugate T y, ∀ u' ∈ rightConjugate T y, u * u' = u' * u := by
    intro u hu u' hu'
    have h1 := hTab _ (hconj u hu) _ (hconj u' hu')
    calc u * u' = y⁻¹ * ((y * u * y⁻¹) * (y * u' * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * u' * y⁻¹) * (y * u * y⁻¹)) * y := by rw [h1]
      _ = u' * u := by group
  have hKc : K ≤ Subgroup.centralizer (K : Set G) := by
    have hT : T ≤ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le (fun t ht => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        exact fun t' ht' => hTab t' ht' t ht
      · rw [Subgroup.mem_centralizer_iff]
        exact fun t' ht' => (hTyT u hu t' ht').symm
    have hTy : rightConjugate T y ≤ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le (fun t ht => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        exact fun u' hu' => hTyT u' hu' t ht
      · rw [Subgroup.mem_centralizer_iff]
        exact fun u' hu' => hTyab u' hu' u hu
    exact sup_le hT hTy
  have hTyRT : rightConjugate T y ≤ R ⊔ T := by
    intro u hu
    have h1 := hc2 _ (hconj u hu)
    have h2 : (y * u * y⁻¹) * ((y * u * y⁻¹)⁻¹ * (y⁻¹ * (y * u * y⁻¹) * y)) ∈ R ⊔ T :=
      (R ⊔ T).mul_mem (Subgroup.mem_sup_right (hconj u hu)) (Subgroup.mem_sup_left h1)
    rwa [show (y * u * y⁻¹) * ((y * u * y⁻¹)⁻¹ * (y⁻¹ * (y * u * y⁻¹) * y)) = u by group] at h2
  refine ⟨fun hR => hTZ ?_, fun ρ hρ => ?_, le_antisymm (sup_le inf_le_left le_sup_left)
    (sup_le le_sup_right hTyRT), Subgroup.le_centralizer_iff_isMulCommutative.mp hKc⟩
  ·
    have hTyT' : rightConjugate T y ≤ T := by
      intro u hu
      have h1 := hc2 _ (hconj u hu)
      rw [hR, Subgroup.mem_bot, inv_mul_eq_one,
        show y⁻¹ * (y * u * y⁻¹) * y = u by group] at h1
      rw [← h1]
      exact hconj u hu
    have heq : rightConjugate T y = T :=
      Subgroup.eq_of_le_of_card_ge hTyT' (le_of_eq (rightConjugate_card T y).symm)
    intro w hw
    rw [← Nine.factorZStar_conj]
    have hwb : w ∈ aschbacherThm5Preimage D' (Abar' b) := by
      rw [← hLb]
      exact hTyL (heq.ge hw)
    exact ⟨by rw [← hLa]; exact hTL hw, factor_le_centralizing hC'.hyp.hcomm hab hwb⟩
  · exact (show ρ ∈ K ⊓ Subgroup.centralizer (K : Set G) from ⟨hρ.1, hKc hρ.1⟩)

end DeltaLocal.Ten

open DeltaLocal.Ten in
theorem lemma_6_10 (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hA : ¬ aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g ≤
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
    (hT : ¬ d.T ≤ rightConjugate (factorZStar D Abar a) d.g) :
    ∃ y ∈ d.S ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g,
      (∃ b, b ≠ a ∧ rightConjugate (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g) y =
        rightConjugate (aschbacherThm5Preimage D (Abar b)) d.g) ∧
      (d.T ⊔ rightConjugate d.T y) ⊓ d.S ≠ ⊥ ∧
      (d.T ⊔ rightConjugate d.T y) ⊓ d.S ≤
        AschbacherTheorem3.centerOf (d.T ⊔ rightConjugate d.T y) ∧
      (d.T ⊔ rightConjugate d.T y) ⊓ d.S ⊔ d.T = d.T ⊔ rightConjugate d.T y ∧
      IsMulCommutative (d.T ⊔ rightConjugate d.T y : Subgroup G) := by
  have hr : r = 2 := lemma_6_9 h3 hin hC ⟨_, d.g, rfl, d.ne, d.U, d.four⟩
  have hg : d.g ∉ Subgroup.normalizer (D : Set G) := fun h =>
    d.ne ((rightConjugate_eq_self_iff _ d.g).mpr (Subgroup.le_normalizer h))
  obtain ⟨y, hyQ, b, hba, hb⟩ := exists_moving_of_sylow (hC.conj d.g).hyp hr (a := a)
    (K := aschbacherThm5Preimage D (Abar a) ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (by rw [normalizer_rightConjugate]; exact inf_le_right) d.sylowInter
    (by rw [preimage_conjFactors]; exact hA)
  rw [preimage_conjFactors, preimage_conjFactors] at hb
  exact ⟨y, hyQ, ⟨b, hba, hb⟩, of_moving hC hg hba d.sylowT.isPGroup
    (d.sylowT.le.trans inf_le_left) d.sylowS.isPGroup d.sylowS.le d.invariant hyQ.1 hb hT⟩

end CFSG.ComponentClassification.AschbacherTheorem5
