module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverWreath
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverRigid

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Wreathed

variable {J : Type*} [Group J] [Finite J]

theorem false_of_wreathed (hperf : commutator J = ⊤) (hZ : IsPGroup 2 (Subgroup.center J))
    (hZne : Subgroup.center J ≠ ⊥) (Q : Sylow 2 J) {n : ℕ} (hn : 2 ≤ n)
    (e : (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) ≃* CFSG.Open.WreathedTwoGroup n) :
    False := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : (Q : Subgroup J) →* Wreath (2 ^ (k + 1)), ψ = coverHom Q e :=
    ⟨_, rfl⟩
  have hψ : Function.Surjective ψ := by rw [hψ_def]; exact coverHom_surjective
  have hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g := by rw [hψ_def]; exact coverHom_central
  have hker1 : ∀ c, ψ c = 1 ↔ (c : J) ∈ Subgroup.center J := by
    rw [hψ_def]; exact coverHom_eq_one_iff
  have hker : ∀ c, ψ c = 1 → (c : J) ∈ Subgroup.center J := fun c hc => (hker1 c).mp hc
  have hcomm : ∀ c, ψ c = 1 → c ∈ commutator (Q : Subgroup J) := by
    rw [hψ_def]; exact coverHom_mem_commutator hperf
  have hh : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  have hM0 : 0 < 2 ^ (k + 1) := by positivity
  obtain ⟨⟨z₀, hz₀Z⟩, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZne
  have hz₀Q : z₀ ∈ (Q : Subgroup J) := hZ.le_sylow_of_normal Q hz₀Z
  have hψz₀ : ψ ⟨z₀, hz₀Q⟩ = 1 := (hker1 _).mpr hz₀Z
  have hz₀1' : (⟨z₀, hz₀Q⟩ : (Q : Subgroup J)) ≠ 1 := fun h1 => by
    have h2 : z₀ = 1 := congrArg Subtype.val h1
    exact hz₀1 (Subtype.ext h2)
  obtain ⟨a, ha⟩ := hψ (element (2 ^ (k + 1)) 1 0 0)
  obtain ⟨t, ht⟩ := hψ (element (2 ^ (k + 1)) 0 0 1)
  obtain ⟨b, hb_def⟩ : ∃ b, b = t * a * t⁻¹ := ⟨_, rfl⟩
  have hb : ψ b = element (2 ^ (k + 1)) 0 1 0 := by
    rw [hb_def, map_mul, map_mul, map_inv, ha, ht, conjugate_base_by_swap]
  set c := a * b * a⁻¹ * b⁻¹ with hc_def
  have hc : ψ c = 1 := wreath_commutator_ker ψ ha hb
  have hc1 : c ≠ 1 := by
    intro h1
    apply wreath_not_commute hM0 ψ hψ hcen hcomm hψz₀ hz₀1' ha ht
    rw [← hb_def]
    rw [hc_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have htnr : ¬ IsRigid (t : J) := by
    intro hrig
    have hsw := wreath_swap_conj ψ hcen ht hb_def
    rw [← hc_def] at hsw
    have hcinv : ψ c⁻¹ = 1 := by rw [map_inv, hc, inv_one]
    have key : (a * b)⁻¹ * t * (a * b) = c⁻¹ * t := by
      calc (a * b)⁻¹ * t * (a * b) = (a * b)⁻¹ * (t * (a * b) * t⁻¹) * t := by group
        _ = (a * b)⁻¹ * (c⁻¹ * (a * b)) * t := by rw [hsw]
        _ = c⁻¹ * t := by rw [← hcen _ hcinv (a * b)]; group
    have key' : ((a * b : (Q : Subgroup J)) : J)⁻¹ * t * ((a * b : (Q : Subgroup J)) : J)⁻¹⁻¹ =
        (c : J)⁻¹ * t := by
      rw [inv_inv]
      exact_mod_cast congrArg Subtype.val key
    have hcomm : ((a * b : (Q : Subgroup J)) : J)⁻¹ * t * ((a * b : (Q : Subgroup J)) : J)⁻¹⁻¹ *
        (t : J)⁻¹ ∈ Subgroup.center J := by
      rw [key', mul_inv_cancel_right]
      exact Subgroup.inv_mem _ (hker c hc)
    have := hrig _ hcomm
    rw [key', mul_eq_right, inv_eq_one] at this
    exact hc1 (Subtype.ext this)
  have hecen : ∀ g : (Q : Subgroup J), g * (a * b) ^ 2 ^ k = (a * b) ^ 2 ^ k * g :=
    wreath_central_lift ψ hcen ha ht hb_def hh
  have herig : IsRigid (((a * b) ^ 2 ^ k : (Q : Subgroup J)) : J) :=
    isRigid_of_commute_sylow hZ Q fun q hq => congrArg Subtype.val (hecen ⟨q, hq⟩)
  have hψe : ψ ((a * b) ^ 2 ^ k) =
      element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ((2 ^ k : ℕ)) 0 := by
    rw [map_pow, map_mul, ha, hb, element_base_mul, element_base_pow]
    simp [nsmul_eq_mul]
  have hrigid_of : ∀ y : (Q : Subgroup J), ψ y =
      element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ((2 ^ k : ℕ)) 0 →
      IsRigid (y : J) := by
    intro y hy
    have hz : ψ (((a * b) ^ 2 ^ k)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hy, hψe, inv_mul_cancel]
    have := herig.mul_central (hker _ hz)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using this
  have hord_iff : ∀ y : (Q : Subgroup J), orderOf (ψ y) = 2 →
      (y : J) * y ∈ Subgroup.center J ∧ (y : J) ∉ Subgroup.center J := by
    rw [hψ_def]; exact fun y hy => sq_mem_center_of_orderOf_coverHom hy
  have hord_of : ∀ y : (Q : Subgroup J), (y : J) * y ∈ Subgroup.center J →
      (y : J) ∉ Subgroup.center J → orderOf (ψ y) = 2 := by
    rw [hψ_def]; exact fun y hy2 hyZ => orderOf_coverHom_eq_two hy2 hyZ
  have hW6 : ∀ y : (Q : Subgroup J),
      ψ y = element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 →
      ¬ IsRigid (y : J) → False := by
    intro y hy hynr
    have hyB : ψ y ∈ baseSubgroup (2 ^ (k + 1)) := by rw [hy, element_mem_base]
    have hyc : ∀ g : (Q : Subgroup J), ψ g ∈ baseSubgroup (2 ^ (k + 1)) → g * y = y * g := by
      intro g hg
      have h1 := wreath_half_commute_base ψ hcen ha ht hb_def hh hg
      have hz : ψ ((a ^ 2 ^ k)⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, map_pow, ha, element_base_pow, hy, inv_mul_eq_one]
        simp [nsmul_eq_mul]
      have hy' : y = a ^ 2 ^ k * ((a ^ 2 ^ k)⁻¹ * y) := (mul_inv_cancel_left _ y).symm
      rw [hy']
      exact ((Commute.mul_right h1 (hcen _ hz g)).eq)
    obtain ⟨Bh, hBh⟩ : ∃ Bh : Subgroup (Q : Subgroup J),
        Bh = (baseSubgroup (2 ^ (k + 1))).comap ψ := ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : Subgroup J, P = Bh.map (Q : Subgroup J).subtype := ⟨_, rfl⟩
    have hP2 : IsPGroup 2 P := hPdef ▸ (Q.isPGroup'.to_subgroup Bh).map _
    have hPy : ∀ p ∈ P, p * y = y * p := by
      rw [hPdef]
      rintro _ ⟨g, hg, rfl⟩
      rw [hBh] at hg
      exact congrArg Subtype.val (hyc g hg)
    obtain ⟨P', hP', hle, hne, hP'y⟩ := exists_ne_of_not_isRigid hZ hynr hP2 hPy
    have hcardP : Nat.card P * 2 = Nat.card (Q : Subgroup J) := by
      have hidx := Subgroup.index_mul_card Bh
      rw [hBh, Subgroup.index_comap_of_surjective _ hψ, base_index_two _ hM0, ← hBh] at hidx
      rw [hPdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      omega
    have hcard : Nat.card (Q : Subgroup J) ≤ Nat.card P' := by
      obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hle
      have hPpos : 0 < Nat.card P := Nat.card_pos
      have hd1 : d ≠ 1 := by
        rintro rfl
        rw [mul_one] at hd
        exact hne (Subgroup.eq_of_le_of_card_ge hle hd.le).symm
      have hd0 : d ≠ 0 := by
        rintro rfl
        have : 0 < Nat.card P' := Nat.card_pos
        omega
      rw [← hcardP, hd]
      exact Nat.mul_le_mul_left _ (by omega)
    obtain ⟨x, hxQ, hxP'⟩ := exists_conj_of_card_le Q hP' hcard
    have hyP : (y : J) ∈ P := by
      rw [hPdef]
      exact ⟨y, by rw [hBh]; exact hyB, rfl⟩
    set y₂ : (Q : Subgroup J) := ⟨x⁻¹ * y * x, hxP' _ (hle hyP)⟩ with hy₂_def
    have hy₂c : ∀ q : (Q : Subgroup J), (q : J) * y₂ * (q : J)⁻¹ * (y₂ : J)⁻¹ ∈
        Subgroup.center J := by
      intro q
      have h1 := mem_centralizerModCenter.mp (hP'y (hxQ q q.2))
      have heq : (q : J) * (x⁻¹ * y * x) * (q : J)⁻¹ * (x⁻¹ * y * x)⁻¹ =
          x⁻¹ * ((x * q * x⁻¹) * y * (x * q * x⁻¹)⁻¹ * (y : J)⁻¹) * x⁻¹⁻¹ := by group
      change (q : J) * (x⁻¹ * y * x) * (q : J)⁻¹ * (x⁻¹ * y * x)⁻¹ ∈ Subgroup.center J
      rw [heq, conj_eq_of_mem_center h1]
      exact h1
    have hψy₂ : ψ y₂ ∈ Subgroup.center (Wreath (2 ^ (k + 1))) := by
      rw [hψ_def]; exact coverHom_mem_center y₂ hy₂c
    have hyord : orderOf (ψ y) = 2 := by
      rw [hy]
      exact (element_base_involution_iff k _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    obtain ⟨hy2, hyZ⟩ := hord_iff y hyord
    have hy₂2 : (y₂ : J) * y₂ ∈ Subgroup.center J := by
      change (x⁻¹ * y * x) * (x⁻¹ * y * x) ∈ Subgroup.center J
      rw [show (x⁻¹ * y * x) * (x⁻¹ * y * x) = x⁻¹ * ((y : J) * y) * x⁻¹⁻¹ by group,
        conj_eq_of_mem_center hy2]
      exact hy2
    have hy₂Z : (y₂ : J) ∉ Subgroup.center J := by
      intro h1
      apply hyZ
      change x⁻¹ * y * x ∈ Subgroup.center J at h1
      rw [show (y : J) = x * (x⁻¹ * y * x) * x⁻¹ by group, conj_eq_of_mem_center h1]
      exact h1
    have hcentral := unique_central_involution k (ψ y₂) (hord_of y₂ hy₂2 hy₂Z) hψy₂
    apply hynr
    have := (hrigid_of y₂ hcentral).conj x
    rwa [hy₂_def, show x * (x⁻¹ * y * x) * x⁻¹ = (y : J) by group] at this
  have ht2 : (t : J) * t ∈ Subgroup.center J := hker (t * t) (by
    rw [map_mul, ht, ← pow_two, element_swap_sq, add_zero, element_zero])
  have htZ : (t : J) ∉ Subgroup.center J := by
    intro h1
    have h2 := (hker1 t).mpr h1
    rw [ht, ← element_zero, element_eq_iff] at h2
    exact one_ne_zero h2.2.2
  obtain ⟨g, hyQ, hyB⟩ := exists_conj_coverHom_mem hperf hZ (e := e)
    (base_index_two (2 ^ (k + 1)) hM0) ht2 htZ
  rw [← hψ_def] at hyB
  set y : (Q : Subgroup J) := ⟨g⁻¹ * t * g, hyQ⟩ with hy_def
  have hynr : ¬ IsRigid (y : J) := by
    intro hr
    apply htnr
    have := hr.conj g
    rwa [hy_def, show g * (g⁻¹ * t * g) * g⁻¹ = (t : J) by group] at this
  have hy2 : (y : J) * y ∈ Subgroup.center J := by
    change (g⁻¹ * t * g) * (g⁻¹ * t * g) ∈ Subgroup.center J
    rw [show (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * ((t : J) * t) * g⁻¹⁻¹ by group,
      conj_eq_of_mem_center ht2]
    exact ht2
  have hyZ : (y : J) ∉ Subgroup.center J := by
    intro h1
    apply htZ
    change g⁻¹ * t * g ∈ Subgroup.center J at h1
    rw [show (t : J) = g * (g⁻¹ * t * g) * g⁻¹ by group, conj_eq_of_mem_center h1]
    exact h1
  have hyord := hord_of y hy2 hyZ
  obtain ⟨⟨i, j, e'⟩, he'⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective (ψ y)
  change element _ i j e' = ψ y at he'
  have he'0 : e' = 0 := (element_mem_base _ i j e').mp (he' ▸ hyB)
  subst he'0
  rw [← he', element_base_involution_iff] at hyord
  rcases hyord with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hynr (hrigid_of y he'.symm)
  · exact hW6 y he'.symm hynr
  ·
    set y' : (Q : Subgroup J) := t⁻¹ * y * t with hy'_def
    have hinv : (element (2 ^ (k + 1)) 0 0 1)⁻¹ = element (2 ^ (k + 1)) 0 0 1 := by
      rw [element_swap_inv, neg_zero]
    have hψy' : ψ y' = element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 := by
      calc ψ y' = element (2 ^ (k + 1)) 0 0 1 *
            element (2 ^ (k + 1)) 0 ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 *
            (element (2 ^ (k + 1)) 0 0 1)⁻¹ := by
              rw [hy'_def, map_mul, map_mul, map_inv, ht, ← he', hinv]
        _ = _ := conjugate_base_by_swap _ _ _ _ _
    apply hW6 y' hψy'
    intro hr
    apply hynr
    have := hr.conj (t : J)
    rwa [hy'_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      show (t : J) * ((t : J)⁻¹ * y * t) * (t : J)⁻¹ = (y : J) by group] at this

end CFSG.ProperTwoGeneratedCore.Lemma37
