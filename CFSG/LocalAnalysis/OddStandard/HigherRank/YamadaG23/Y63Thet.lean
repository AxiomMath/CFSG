module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Reg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Model

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk

theorem y63_theta {D : Data} [Group Y63TG] (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) {G : Type} [Group G] [Finite G] {P Q : Subgroup G} {t : G}
    (φ : ↥P ≃* Y63TG) (hPQ : P ≤ Q) (hcard : Nat.card ↥Q = 2 * Nat.card ↥P) (ht : t ∈ Q)
    (htP : t ∉ P) (ht2 : t ^ 2 = 1) {k : ℕ} (hτlt : ∀ x < 512, D.tau k x < 512)
    (hτ : ∀ x : ↥P, ∃ hx : t * (x : G) * t⁻¹ ∈ P,
      (φ ⟨t * (x : G) * t⁻¹, hx⟩).val = D.tau k (φ x).val) :
    ∃ Θ : ℕ → G, Y63Model D k P Q Θ := by
  classical
  have hcardP : Nat.card ↥P = 512 := by
    rw [Nat.card_congr φ.toEquiv, Y63TG.card]
  have hcardQ : Nat.card ↥Q = 1024 := by
    rw [hcard, hcardP]
  have hmod : ∀ i : ℕ, i % 512 < 512 := fun i => Nat.mod_lt i (by norm_num)
  let Θ : ℕ → G := fun i => ((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G) * t ^ (i / 512)
  have hmulφ : ∀ (x y : Y63TG) (h : D.mt x.val y.val < 512),
      ((φ.symm ⟨D.mt x.val y.val, h⟩ : ↥P) : G)
        = ((φ.symm x : ↥P) : G) * ((φ.symm y : ↥P) : G) := by
    intro x y h
    have hxy : (⟨D.mt x.val y.val, h⟩ : Y63TG) = x * y := by
      apply Y63TG.ext
      exact (hmul x y).symm
    have h2 : (φ.symm ⟨D.mt x.val y.val, h⟩ : ↥P) = φ.symm x * φ.symm y := by
      rw [hxy, map_mul]
    rw [h2]; rfl
  have hτ' : ∀ y : Y63TG,
      t * ((φ.symm y : ↥P) : G) * t⁻¹
        = ((φ.symm ⟨D.tau k y.val, hτlt y.val y.lt⟩ : ↥P) : G) := by
    intro y
    obtain ⟨hx, hval⟩ := hτ (φ.symm y)
    have hφ : (φ ⟨t * ((φ.symm y : ↥P) : G) * t⁻¹, hx⟩ : Y63TG)
        = ⟨D.tau k y.val, hτlt y.val y.lt⟩ := by
      apply Y63TG.ext
      rw [hval, MulEquiv.apply_symm_apply]
    have hsub : (⟨t * ((φ.symm y : ↥P) : G) * t⁻¹, hx⟩ : ↥P)
        = φ.symm ⟨D.tau k y.val, hτlt y.val y.lt⟩ := by
      rw [← hφ, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val hsub
  have hmem : ∀ i < 1024, Θ i ∈ Q := by
    intro i _
    have hP : ((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G) ∈ P := (φ.symm ⟨i % 512, hmod i⟩).2
    exact Q.mul_mem (hPQ hP) (Q.pow_mem ht _)
  have hinj : ∀ i < 1024, ∀ j < 1024, Θ i = Θ j → i = j := by
    intro i hi j hj hij
    have ha : i / 512 = 0 ∨ i / 512 = 1 := by omega
    have hb : j / 512 = 0 ∨ j / 512 = 1 := by omega
    have hxa : ((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G) * t ^ (i / 512)
        = ((φ.symm ⟨j % 512, hmod j⟩ : ↥P) : G) * t ^ (j / 512) := hij
    have hval : ((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G)
        = ((φ.symm ⟨j % 512, hmod j⟩ : ↥P) : G) → i % 512 = j % 512 := by
      intro hxy
      have h1' : (φ.symm ⟨i % 512, hmod i⟩ : ↥P) = φ.symm ⟨j % 512, hmod j⟩ :=
        Subtype.val_injective hxy
      have h2' : (⟨i % 512, hmod i⟩ : Y63TG) = ⟨j % 512, hmod j⟩ := by
        have := congrArg φ h1'
        simpa only [MulEquiv.apply_symm_apply] using this
      simpa using congrArg Y63TG.val h2'
    have hdiv : i / 512 = j / 512 → i % 512 = j % 512 → i = j := by
      intro hd hm
      rw [← Nat.div_add_mod i 512, ← Nat.div_add_mod j 512, hd, hm]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb] at hxa
      simp only [pow_zero, mul_one] at hxa
      exact hdiv (by rw [ha, hb]) (hval hxa)
    · rw [ha, hb] at hxa
      simp only [pow_zero, pow_one, mul_one] at hxa
      have ht_mem : t ∈ P := by
        have hteq : t = ((φ.symm ⟨j % 512, hmod j⟩ : ↥P) : G)⁻¹
            * ((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G) := by
          rw [hxa]; group
        rw [hteq]
        exact P.mul_mem (P.inv_mem (φ.symm ⟨j % 512, hmod j⟩).2)
          (φ.symm ⟨i % 512, hmod i⟩).2
      exact absurd ht_mem htP
    · rw [ha, hb] at hxa
      simp only [pow_zero, pow_one, mul_one] at hxa
      have ht_mem : t ∈ P := by
        have hteq : t = ((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G)⁻¹
            * ((φ.symm ⟨j % 512, hmod j⟩ : ↥P) : G) := by
          rw [← hxa]; group
        rw [hteq]
        exact P.mul_mem (P.inv_mem (φ.symm ⟨i % 512, hmod i⟩).2)
          (φ.symm ⟨j % 512, hmod j⟩).2
      exact absurd ht_mem htP
    · rw [ha, hb] at hxa
      simp only [pow_one] at hxa
      exact hdiv (by rw [ha, hb]) (hval (mul_right_cancel hxa))
  have hsurj : ∀ g ∈ Q, ∃ i < 1024, Θ i = g := by
    intro g hg
    let f : Fin 1024 → ↥Q := fun i => ⟨Θ i.val, hmem i.val i.isLt⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      apply hinj a.val a.isLt b.val b.isLt
      simpa [f] using congrArg Subtype.val hab
    have hbij : Function.Bijective f :=
      hfinj.bijective_of_nat_card_le (by simp [hcardQ])
    obtain ⟨i, hi⟩ := hbij.2 ⟨g, hg⟩
    exact ⟨i.val, i.isLt, by simpa [f] using congrArg Subtype.val hi⟩
  have hone : Θ 0 = 1 := by
    show ((φ.symm ⟨0 % 512, hmod 0⟩ : ↥P) : G) * t ^ (0 / 512) = 1
    have h0 : (⟨0 % 512, hmod 0⟩ : Y63TG) = 1 := by
      apply Y63TG.ext
      simp [h1]
    rw [h0]
    simp
  have hmemP : ∀ i < 512, Θ i ∈ P := by
    intro i hi
    show ((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G) * t ^ (i / 512) ∈ P
    rw [Nat.div_eq_of_lt hi, pow_zero, mul_one]
    exact (φ.symm ⟨i % 512, hmod i⟩).2
  have hsurjP : ∀ g ∈ P, ∃ i < 512, Θ i = g := by
    intro g hg
    refine ⟨(φ ⟨g, hg⟩).val, (φ ⟨g, hg⟩).lt, ?_⟩
    have hlt : (φ ⟨g, hg⟩).val < 512 := (φ ⟨g, hg⟩).lt
    have hm : (φ ⟨g, hg⟩).val % 512 = (φ ⟨g, hg⟩).val := Nat.mod_eq_of_lt hlt
    have hd : (φ ⟨g, hg⟩).val / 512 = 0 := Nat.div_eq_of_lt hlt
    show ((φ.symm ⟨(φ ⟨g, hg⟩).val % 512, hmod _⟩ : ↥P) : G)
        * t ^ ((φ ⟨g, hg⟩).val / 512) = g
    have heq : (⟨(φ ⟨g, hg⟩).val % 512, hmod _⟩ : Y63TG)
        = ⟨(φ ⟨g, hg⟩).val, hlt⟩ := by
      apply Y63TG.ext; exact hm
    have hsub : (⟨(φ ⟨g, hg⟩).val, hlt⟩ : Y63TG) = φ ⟨g, hg⟩ := by
      apply Y63TG.ext; rfl
    rw [heq, hd, pow_zero, mul_one, hsub]
    exact congrArg Subtype.val (MulEquiv.symm_apply_apply φ ⟨g, hg⟩)
  have hmq_lt : ∀ i < 1024, ∀ j < 1024, D.mq k i j < 1024 := by
    intro i _ j _
    have hz : (if i / 512 = 1 then D.tau k (j % 512) else j % 512) < 512 := by
      split_ifs with ha
      · exact hτlt _ (Nat.mod_lt _ (by norm_num))
      · exact Nat.mod_lt _ (by norm_num)
    have hmlt : D.mt (i % 512)
        (if i / 512 = 1 then D.tau k (j % 512) else j % 512) < 512 := by
      have := (⟨i % 512, Nat.mod_lt _ (by norm_num)⟩ * ⟨_, hz⟩ : Y63TG).lt
      rwa [hmul] at this
    have he : (if i / 512 = j / 512 then 0 else 1) = 0
        ∨ (if i / 512 = j / 512 then 0 else 1) = 1 := by
      split_ifs <;> simp
    unfold Data.mq
    rcases he with he | he <;> rw [he] <;> omega
  have hmul' : ∀ i < 1024, ∀ j < 1024, Θ (D.mq k i j) = Θ i * Θ j := by
    intro i _ j _
    have hz : (if i / 512 = 1 then D.tau k (j % 512) else j % 512) < 512 := by
      split_ifs with ha
      · exact hτlt _ (Nat.mod_lt _ (by norm_num))
      · exact Nat.mod_lt _ (by norm_num)
    have hmlt : D.mt (i % 512)
        (if i / 512 = 1 then D.tau k (j % 512) else j % 512) < 512 := by
      have := (⟨i % 512, Nat.mod_lt _ (by norm_num)⟩ * ⟨_, hz⟩ : Y63TG).lt
      rwa [hmul] at this
    have hmq_mod : (D.mq k i j) % 512
        = D.mt (i % 512) (if i / 512 = 1 then D.tau k (j % 512) else j % 512) := by
      unfold Data.mq
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmlt]
    have hmq_div : (D.mq k i j) / 512 = (if i / 512 = j / 512 then 0 else 1) := by
      unfold Data.mq
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hmlt, Nat.zero_add]
    have hR : Θ i * Θ j
        = (((φ.symm ⟨i % 512, hmod i⟩ : ↥P) : G) * t ^ (i / 512))
          * (((φ.symm ⟨j % 512, hmod j⟩ : ↥P) : G) * t ^ (j / 512)) := rfl
    rw [hR]
    have hL : Θ (D.mq k i j)
        = ((φ.symm ⟨D.mt (i % 512) (if i / 512 = 1 then D.tau k (j % 512) else j % 512),
              hmlt⟩ : ↥P) : G) * t ^ (if i / 512 = j / 512 then 0 else 1) := by
      show ((φ.symm ⟨(D.mq k i j) % 512, hmod _⟩ : ↥P) : G) * t ^ ((D.mq k i j) / 512) = _
      have hsub : (⟨(D.mq k i j) % 512, hmod _⟩ : Y63TG)
          = ⟨D.mt (i % 512) (if i / 512 = 1 then D.tau k (j % 512) else j % 512),
              hmlt⟩ := by
        apply Y63TG.ext; exact hmq_mod
      rw [hsub, hmq_div]
    rw [hL]
    rw [hmulφ ⟨i % 512, hmod i⟩ ⟨_, hz⟩ hmlt]
    have hzval : ((φ.symm ⟨if i / 512 = 1 then D.tau k (j % 512) else j % 512,
          hz⟩ : ↥P) : G)
        = (if i / 512 = 1 then t * ((φ.symm ⟨j % 512, hmod j⟩ : ↥P) : G) * t⁻¹
            else ((φ.symm ⟨j % 512, hmod j⟩ : ↥P) : G)) := by
      by_cases ha : i / 512 = 1
      · have hzA : (⟨if i / 512 = 1 then D.tau k (j % 512) else j % 512, hz⟩ : Y63TG)
            = ⟨D.tau k (j % 512), hτlt (j % 512) (Nat.mod_lt _ (by norm_num))⟩ := by
          apply Y63TG.ext; exact if_pos ha
        rw [congrArg (fun u : Y63TG => ((φ.symm u : ↥P) : G)) hzA, if_pos ha,
          hτ' ⟨j % 512, hmod j⟩]
      · have hzB : (⟨if i / 512 = 1 then D.tau k (j % 512) else j % 512, hz⟩ : Y63TG)
            = ⟨j % 512, Nat.mod_lt _ (by norm_num)⟩ := by
          apply Y63TG.ext; exact if_neg ha
        rw [congrArg (fun u : Y63TG => ((φ.symm u : ↥P) : G)) hzB, if_neg ha]
    rw [hzval]
    have ha01 : i / 512 = 0 ∨ i / 512 = 1 := by omega
    have hb01 : j / 512 = 0 ∨ j / 512 = 1 := by omega
    have htinv : t⁻¹ = t := by
      have h2 : t * t = 1 := by rw [← pow_two]; exact ht2
      exact inv_eq_of_mul_eq_one_left h2
    rcases ha01 with ha | ha <;> rcases hb01 with hb | hb
    · rw [ha, hb]
      rw [if_neg (by decide : ¬ ((0 : ℕ) = 1)), if_pos (rfl : (0 : ℕ) = 0)]
      simp only [pow_zero, mul_one]
    · rw [ha, hb]
      rw [if_neg (by decide : ¬ ((0 : ℕ) = 1)), if_neg (by decide : ¬ ((0 : ℕ) = 1))]
      simp only [pow_zero, pow_one, mul_one, one_mul, mul_assoc]
    · rw [ha, hb]
      rw [if_pos rfl, if_neg (by decide : ¬ ((1 : ℕ) = 0))]
      simp only [pow_zero, pow_one, mul_one, one_mul, mul_assoc, inv_mul_cancel]
    · rw [ha, hb]
      rw [if_pos rfl, if_pos rfl, htinv]
      simp only [pow_zero, pow_one, mul_one, one_mul, mul_assoc]
  exact ⟨Θ, hmem, hinj, hsurj, hone, hmemP, hsurjP, hmq_lt, hmul'⟩

end CFSG.OddStandard.HigherRank.YamadaG23
