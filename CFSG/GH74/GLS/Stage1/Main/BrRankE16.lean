module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionComponentTwoCore

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

section E16

variable {Gs : Type} [Group Gs]

theorem eq_one_or_eq_of_mem_zpowers_sq {y g : Gs} (hy : y * y = 1) (hg : g ∈ zpowers y) :
    g = 1 ∨ g = y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have hy' : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy
  have hk : y ^ k = y ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2]
    rw [zpow_add, zpow_mul, hy', one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem zpowers_le_centralizer_zpowers {x y : Gs} (hxy : x * y = y * x) :
    zpowers x ≤ centralizer (zpowers y : Set Gs) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact ((Commute.zpow_left (Commute.symm hxy) k)).eq

theorem decomp_unique {z' : Gs} {E₁ E₂ : Subgroup Gs} (hinter : E₁ ⊓ E₂ = zpowers z')
    (hz'sq : z' * z' = 1) {u u₀ v v₀ : Gs} (hu : u ∈ E₁) (hu₀ : u₀ ∈ E₁) (hv : v ∈ E₂)
    (hv₀ : v₀ ∈ E₂) (h : u * v = u₀ * v₀) : u₀ = u ∨ u₀ = u * z' := by
  have h1 : u⁻¹ * u₀ = v * v₀⁻¹ := by
    calc u⁻¹ * u₀ = u⁻¹ * (u₀ * v₀) * v₀⁻¹ := by group
      _ = u⁻¹ * (u * v) * v₀⁻¹ := by rw [h]
      _ = v * v₀⁻¹ := by group
  have hmem : u⁻¹ * u₀ ∈ E₁ ⊓ E₂ :=
    ⟨E₁.mul_mem (E₁.inv_mem hu) hu₀, by rw [h1]; exact E₂.mul_mem hv (E₂.inv_mem hv₀)⟩
  rw [hinter] at hmem
  rcases eq_one_or_eq_of_mem_zpowers_sq hz'sq hmem with h2 | h2
  · left
    calc u₀ = u * (u⁻¹ * u₀) := by group
      _ = u := by rw [h2, mul_one]
  · right
    calc u₀ = u * (u⁻¹ * u₀) := by group
      _ = u * z' := by rw [h2]

end E16

section E16b

variable {Gs : Type} [Group Gs] [Finite Gs]

theorem exists_E16 {z' t' a b : Gs} {E₁ E₂ : Subgroup Gs}
    (hz'sq : z' * z' = 1) (hz'1 : z' ≠ 1) (ht'sq : t' * t' = 1) (htz : t' * z' = z' * t')
    (hE₂ : E₂ = E₁.map (MulAut.conj t').toMonoidHom) (hinter : E₁ ⊓ E₂ = zpowers z')
    (hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x) (htE : t' ∉ E₁ ⊔ E₂)
    (ha : a ∈ E₁) (hb : b ∈ E₁) (haa : a * a = z') (hbb : b * b = z')
    (hba : b * a = z' * (a * b)) :
    ∃ E : Subgroup Gs, IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 4 := by
  classical
  obtain ⟨hz'E₁, hz'E₂⟩ : z' ∈ E₁ ∧ z' ∈ E₂ := by
    have : z' ∈ E₁ ⊓ E₂ := by rw [hinter]; exact mem_zpowers z'
    exact this
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'sq
  have hconj : ∀ g h : Gs, t' * (g * h) * t' = (t' * g * t') * (t' * h * t') := by
    intro g h
    have : (t' * g * t') * (t' * h * t') = t' * g * (t' * t') * h * t' := by group
    rw [this, ht'sq]
    group
  obtain ⟨a', ha'def⟩ : ∃ a', a' = t' * a * t' := ⟨_, rfl⟩
  obtain ⟨b', hb'def⟩ : ∃ b', b' = t' * b * t' := ⟨_, rfl⟩
  have ha'E : a' ∈ E₂ := by
    rw [hE₂]
    exact ⟨a, ha, by simp [MulAut.conj_apply, ht'inv, ha'def]⟩
  have hb'E : b' ∈ E₂ := by
    rw [hE₂]
    exact ⟨b, hb, by simp [MulAut.conj_apply, ht'inv, hb'def]⟩
  have hz'conj : t' * z' * t' = z' := by rw [htz, mul_assoc, ht'sq, mul_one]
  have hbackA : t' * a' * t' = a := by
    rw [ha'def]
    calc t' * (t' * a * t') * t' = (t' * t') * a * (t' * t') := by group
      _ = a := by rw [ht'sq]; group
  have hbackB : t' * b' * t' = b := by
    rw [hb'def]
    calc t' * (t' * b * t') * t' = (t' * t') * b * (t' * t') := by group
      _ = b := by rw [ht'sq]; group
  have ha'a' : a' * a' = z' := by
    calc a' * a' = t' * (a * a) * t' := by rw [ha'def]; exact (hconj a a).symm
      _ = z' := by rw [haa, hz'conj]
  have hb'b' : b' * b' = z' := by
    calc b' * b' = t' * (b * b) * t' := by rw [hb'def]; exact (hconj b b).symm
      _ = z' := by rw [hbb, hz'conj]
  have hb'a' : b' * a' = z' * (a' * b') := by
    calc b' * a' = t' * (b * a) * t' := by rw [hb'def, ha'def]; exact (hconj b a).symm
      _ = t' * (z' * (a * b)) * t' := by rw [hba]
      _ = z' * (t' * (a * b) * t') := by
          calc t' * (z' * (a * b)) * t' = (t' * z') * (a * b) * t' := by group
            _ = (z' * t') * (a * b) * t' := by rw [htz]
            _ = z' * (t' * (a * b) * t') := by group
      _ = z' * (a' * b') := by rw [ha'def, hb'def, hconj a b]
  have hcaa' : a * a' = a' * a := hcomm a ha a' ha'E
  have hcab' : a * b' = b' * a := hcomm a ha b' hb'E
  have hcba' : b * a' = a' * b := hcomm b hb a' ha'E
  have hcbb' : b * b' = b' * b := hcomm b hb b' hb'E
  have hcaz : a * z' = z' * a := hcomm a ha z' hz'E₂
  have hcbz : b * z' = z' * b := hcomm b hb z' hz'E₂
  have hcza' : z' * a' = a' * z' := hcomm z' hz'E₁ a' ha'E
  have hczb' : z' * b' = b' * z' := hcomm z' hz'E₁ b' hb'E
  have hCz : E₁ ⊔ E₂ ≤ centralizer ({z'} : Set Gs) := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact hcomm g hg z' hz'E₂
    · rw [mem_centralizer_singleton_iff]
      exact (hcomm z' hz'E₁ g hg).symm
  have hzc : ∀ g ∈ E₁ ⊔ E₂, g * z' = z' * g := fun g hg => mem_centralizer_singleton_iff.1 (hCz hg)
  have haS : a ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_left ha
  have hbS : b ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_left hb
  have ha'S : a' ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_right ha'E
  have hb'S : b' ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_right hb'E
  have hz'S : z' ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_left hz'E₁
  have hx3S : a * a' ∈ E₁ ⊔ E₂ := mul_mem haS ha'S
  have hx4S : b * b' ∈ E₁ ⊔ E₂ := mul_mem hbS hb'S
  have hx3sq : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [← hcaa']
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [haa, ha'a', hz'sq]
  have hx4sq : (b * b') * (b * b') = 1 := by
    calc (b * b') * (b * b') = b * (b' * b) * b' := by group
      _ = b * (b * b') * b' := by rw [← hcbb']
      _ = (b * b) * (b' * b') := by group
      _ = 1 := by rw [hbb, hb'b', hz'sq]
  have hx34 : (a * a') * (b * b') = (b * b') * (a * a') := by
    have e1 : (a * a') * (b * b') = (a * b) * (a' * b') := by
      calc (a * a') * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [← hcba']
        _ = (a * b) * (a' * b') := by group
    have e2 : (b * b') * (a * a') = (b * a) * (b' * a') := by
      calc (b * b') * (a * a') = b * (b' * a) * a' := by group
        _ = b * (a * b') * a' := by rw [← hcab']
        _ = (b * a) * (b' * a') := by group
    rw [e1, e2, hba, hb'a']
    have hab : z' * (a * b) = (a * b) * z' := (hzc _ (mul_mem haS hbS)).symm
    calc (a * b) * (a' * b') = (a * b) * (z' * z') * (a' * b') := by rw [hz'sq, mul_one]
      _ = (a * b) * z' * (z' * (a' * b')) := by group
      _ = z' * (a * b) * (z' * (a' * b')) := by rw [hab]
  have hz3 : z' * (a * a') = (a * a') * z' := (hzc _ hx3S).symm
  have hz4 : z' * (b * b') = (b * b') * z' := (hzc _ hx4S).symm
  have ht3 : t' * (a * a') = (a * a') * t' := by
    have h1 : t' * (a * a') * t' = a * a' := by
      rw [hconj a a', ← ha'def, hbackA]
      exact hcaa'.symm
    calc t' * (a * a') = t' * (a * a') * (t' * t') := by rw [ht'sq, mul_one]
      _ = (t' * (a * a') * t') * t' := by group
      _ = (a * a') * t' := by rw [h1]
  have ht4 : t' * (b * b') = (b * b') * t' := by
    have h1 : t' * (b * b') * t' = b * b' := by
      rw [hconj b b', ← hb'def, hbackB]
      exact hcbb'.symm
    calc t' * (b * b') = t' * (b * b') * (t' * t') := by rw [ht'sq, mul_one]
      _ = (t' * (b * b') * t') * t' := by group
      _ = (b * b') * t' := by rw [h1]
  have hnotz : ∀ g : Gs, g * g = z' → g ∉ zpowers z' := by
    intro g hg hmem
    rcases eq_one_or_eq_of_mem_zpowers_sq hz'sq hmem with h | h
    · rw [h, mul_one] at hg
      exact hz'1 hg.symm
    · rw [h, hz'sq] at hg
      exact hz'1 hg.symm
  have hzp_E₁ : ∀ p ∈ zpowers z', p ∈ E₁ := fun p hp => (Subgroup.zpowers_le.2 hz'E₁) hp
  have hx3z : (a * a') ∉ zpowers z' := by
    intro hmem
    have key : ∀ g ∈ zpowers z', a * a' = g → False := by
      intro g hg hag
      have hgE₁ : g ∈ E₁ := hzp_E₁ g hg
      rcases decomp_unique hinter hz'sq ha hgE₁ ha'E E₂.one_mem
          (by rw [mul_one]; exact hag) with h | h
      · exact hnotz a haa (by rw [← h]; exact hg)
      · apply hnotz a haa
        have : a = g * z' := by rw [h, mul_assoc, hz'sq, mul_one]
        rw [this]
        exact mul_mem hg (mem_zpowers z')
    exact key _ hmem rfl
  have hcommA : ∀ p ∈ zpowers z', ∀ r ∈ zpowers (a * a'), p * r = r * p := by
    intro p hp r hr
    exact (Subgroup.mem_centralizer_iff.1 (zpowers_le_centralizer_zpowers hz3 hp) r hr).symm
  have hcb_a : ∀ c ∈ zpowers z', b ≠ c * a := by
    intro c hc hbca
    have hca : c * a = a * c := by
      rcases eq_one_or_eq_of_mem_zpowers_sq hz'sq hc with h | h
      · rw [h, one_mul, mul_one]
      · rw [h]
        exact hcaz.symm
    have hba2 : b * a = a * b := by
      have e : a * (c * a) = (c * a) * a := by
        calc a * (c * a) = (a * c) * a := by rw [mul_assoc]
          _ = (c * a) * a := by rw [hca]
      rw [hbca]
      exact e.symm
    have h1 := hba
    rw [hba2] at h1
    exact hz'1 (mul_right_cancel (show z' * (a * b) = 1 * (a * b) by rw [one_mul]; exact h1.symm))
  have hx4n : (b * b') ∉ zpowers z' ⊔ zpowers (a * a') := by
    intro hmem
    obtain ⟨p, hp, r, hr, hpr⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcommA hmem
    have hpE₁ : p ∈ E₁ := hzp_E₁ p hp
    rcases eq_one_or_eq_of_mem_zpowers_sq hx3sq hr with hr1 | hr3
    · rw [hr1, mul_one] at hpr
      rcases decomp_unique hinter hz'sq hb hpE₁ hb'E E₂.one_mem
          (by rw [mul_one]; exact hpr) with h | h
      · exact hnotz b hbb (by rw [← h]; exact hp)
      · have : b = p * z' := by rw [h, mul_assoc, hz'sq, mul_one]
        exact hnotz b hbb (by rw [this]; exact mul_mem hp (mem_zpowers z'))
    · rw [hr3] at hpr
      rcases decomp_unique hinter hz'sq hb (mul_mem hpE₁ ha) hb'E ha'E
          (by rw [mul_assoc]; exact hpr) with h | h
      · exact hcb_a p hp h.symm
      · have : b = (p * z') * a := by
          calc b = b * z' * z' := by rw [mul_assoc, hz'sq, mul_one]
            _ = p * a * z' := by rw [← h]
            _ = p * (a * z') := by rw [mul_assoc]
            _ = p * (z' * a) := by rw [hcaz]
            _ = p * z' * a := by rw [mul_assoc]
        exact hcb_a (p * z') (mul_mem hp (mem_zpowers z')) this
  have hz'o : orderOf z' = 2 := orderOf_eq_prime (by rw [sq]; exact hz'sq) hz'1
  have hx3ne : a * a' ≠ 1 := fun h => hx3z (by rw [h]; exact one_mem _)
  have hx3o : orderOf (a * a') = 2 := orderOf_eq_prime (by rw [sq]; exact hx3sq) hx3ne
  have hx4ne : b * b' ≠ 1 := fun h => hx4n (by rw [h]; exact one_mem _)
  have hx4o : orderOf (b * b') = 2 := orderOf_eq_prime (by rw [sq]; exact hx4sq) hx4ne
  have ht'ne : t' ≠ 1 := fun h => htE (by rw [h]; exact one_mem _)
  have ht'o : orderOf t' = 2 := orderOf_eq_prime (by rw [sq]; exact ht'sq) ht'ne
  obtain ⟨C₁, -, -, hC₁e, hC₁card, hC₁le⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (firstRank := 1) (secondRank := 1) (zpowers z') (zpowers (a * a'))
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary z' hz'o)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary (a * a') hx3o)
      (by rw [Nat.card_zpowers, hz'o, pow_one]) (by rw [Nat.card_zpowers, hx3o, pow_one])
      (zpowers_le_centralizer_zpowers hz3)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint (zpowers z') (a * a') hx3o hx3z)
  obtain ⟨C₂, -, -, hC₂e, hC₂card, hC₂le⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (firstRank := 1 + 1) (secondRank := 1) C₁ (zpowers (b * b')) hC₁e
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary (b * b') hx4o) hC₁card
      (by rw [Nat.card_zpowers, hx4o, pow_one])
      (hC₁le.trans (sup_le (zpowers_le_centralizer_zpowers hz4)
        (zpowers_le_centralizer_zpowers hx34)))
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint C₁ (b * b') hx4o
        (fun h => hx4n (hC₁le h)))
  have hC₂S : C₂ ≤ E₁ ⊔ E₂ := by
    refine hC₂le.trans (sup_le (hC₁le.trans (sup_le ?_ ?_)) ?_)
    · exact Subgroup.zpowers_le.2 hz'S
    · exact Subgroup.zpowers_le.2 hx3S
    · exact Subgroup.zpowers_le.2 hx4S
  have hC₂t : C₂ ≤ centralizer (zpowers t' : Set Gs) := by
    refine hC₂le.trans (sup_le (hC₁le.trans (sup_le ?_ ?_)) ?_)
    · exact zpowers_le_centralizer_zpowers htz.symm
    · exact zpowers_le_centralizer_zpowers ht3.symm
    · exact zpowers_le_centralizer_zpowers ht4.symm
  obtain ⟨C₃, -, -, hC₃e, hC₃card, -⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (firstRank := 1 + 1 + 1) (secondRank := 1) C₂ (zpowers t') hC₂e
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary t' ht'o) hC₂card
      (by rw [Nat.card_zpowers, ht'o, pow_one]) hC₂t
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint C₂ t' ht'o
        (fun h => htE (hC₂S h)))
  refine ⟨C₃, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 C₃).2 hC₃e, ?_⟩
  rw [hC₃card]

end E16b

section Quat

variable {Gs : Type} [Group Gs]

theorem exists_quat_pair {q : ℕ} (hodd : Odd q) {z' : Gs} {E₁ : Subgroup Gs}
    (hsl2 : HasSL2Model ↥E₁ (fun r => r = q)) (hz'E : z' ∈ E₁) (hz'sq : z' * z' = 1)
    (hz'1 : z' ≠ 1) (hz'c : ∀ a ∈ E₁, a * z' = z' * a) :
    ∃ a ∈ E₁, ∃ b ∈ E₁, a * a = z' ∧ b * b = z' ∧ b * a = z' * (a * b) := by
  obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := hsl2
  have hF : Odd (Nat.card F) := by rw [hq]; exact hodd
  obtain ⟨x, y, hxy⟩ := CFSG.Semidihedral.OddFieldSL2.sum_two_squares F hF (-1)
  let e' : ↥E₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  set A := CFSG.Semidihedral.OddLinearNormals.quarterTurn F with hA
  set B := CFSG.Semidihedral.OddFieldSL2.secondGenerator F x y hxy with hB
  have hA2 : A * A = -1 := by
    have := CFSG.Semidihedral.OddFieldSL2.quarterTurn_square F
    rw [pow_two] at this
    exact this
  have hB2 : B * B = -1 := by
    have := CFSG.Semidihedral.OddFieldSL2.secondGenerator_square F x y hxy
    rw [pow_two] at this
    exact this
  have hAB := CFSG.Semidihedral.OddFieldSL2.generators_inversion F x y hxy
  have hzc : e' ⟨z', hz'E⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz'c _ g'.2)
  have hζ : e' ⟨z', hz'E⟩ = -1 := by
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hzc
    rw [Fintype.card_fin] at hr
    rcases sq_eq_one_iff.1 hr with h | h
    · exfalso
      have h1 : e' ⟨z', hz'E⟩ = 1 := by
        apply Subtype.ext
        rw [← hrA, h, map_one]
        rfl
      have h2 : (⟨z', hz'E⟩ : ↥E₁) = 1 := e'.injective (by rw [h1, map_one])
      exact hz'1 (congrArg Subtype.val h2)
    · apply Subtype.ext
      rw [← hrA, h, map_neg, map_one]
      rfl
  have hζ' : e'.symm (-1) = ⟨z', hz'E⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact hζ.symm
  refine ⟨(e'.symm A : Gs), (e'.symm A).2, (e'.symm B : Gs), (e'.symm B).2, ?_, ?_, ?_⟩
  · have : e'.symm A * e'.symm A = ⟨z', hz'E⟩ := by
      rw [← map_mul, hA2, hζ']
    exact congrArg Subtype.val this
  · have : e'.symm B * e'.symm B = ⟨z', hz'E⟩ := by
      rw [← map_mul, hB2, hζ']
    exact congrArg Subtype.val this
  · set a : ↥E₁ := e'.symm A with ha
    set b : ↥E₁ := e'.symm B with hb
    have haa : (a : Gs) * a = z' := by
      have : a * a = ⟨z', hz'E⟩ := by rw [ha, ← map_mul, hA2, hζ']
      exact congrArg Subtype.val this
    have hab : (a : Gs) * b = b * (a : Gs)⁻¹ := by
      have : a * b = b * a⁻¹ := by
        rw [ha, hb, ← map_mul, ← map_inv, ← map_mul]
        exact congrArg e'.symm hAB
      exact congrArg Subtype.val this
    have hainv : (a : Gs)⁻¹ = a * z' := by
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, haa, hz'sq]
    have hbz : (b : Gs) * z' = z' * b := hz'c b b.2
    have haz : (a : Gs) * z' = z' * a := hz'c a a.2
    rw [hainv] at hab
    have h1 : (a : Gs) * b * z' = b * a := by
      rw [hab]
      calc (b : Gs) * (a * z') * z' = b * a * (z' * z') := by group
        _ = b * a := by rw [hz'sq, mul_one]
    rw [← h1]
    calc (a : Gs) * b * z' = a * (b * z') := by rw [mul_assoc]
      _ = a * (z' * b) := by rw [hbz]
      _ = (a * z') * b := by rw [← mul_assoc]
      _ = (z' * a) * b := by rw [haz]
      _ = z' * (a * b) := by rw [mul_assoc]

end Quat

end CFSG.GH74.GLS.Stage1.Main
