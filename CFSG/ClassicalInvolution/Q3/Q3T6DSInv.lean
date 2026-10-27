module

public import CFSG.ClassicalInvolution.Asc77.AscT3SInv
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Asc77.T3CII.T3S
open scoped MatrixGroups commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem odd_natCard_galoisField3 : Odd (Nat.card (GaloisField 3 1)) :=
  Uniform.odd_natCard_galoisField_of_pos (by norm_num) (by norm_num)

theorem exists_chart3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ φ : ↥K →* SL(2, GaloisField 3 1), Function.Surjective φ ∧
      ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  obtain ⟨hp, ⟨e⟩⟩ := hz.witness
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, fun x => ?_⟩
  · intro y
    obtain ⟨q, hq⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨x, hq⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e, e.injective.eq_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem exists_sq_dataGen (hΩ : HypOmegaGen Ω)
    {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) {z : G}
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    {φ : ↥K →* SL(2, GaloisField 3 1)} (hφs : Function.Surjective φ)
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K)
    {φ' : ↥K' →* SL(2, GaloisField 3 1)}
    (hφ'k : ∀ x : ↥K', φ' x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K')
    {s : G} (hs : s ∈ K ⊔ K') (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) :
    ∃ (k : G) (hk : k ∈ K) (k' : G) (hk' : k' ∈ K'), s = k * k' ∧
      φ ⟨k, hk⟩ * φ ⟨k, hk⟩ = -1 ∧ φ' ⟨k', hk'⟩ * φ' ⟨k', hk'⟩ = -1 := by
  have hodd := odd_natCard_galoisField3
  have hcomm := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hK' hne.symm hz hz'
  have hc : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ oddCoreOf K ∧ ⁅x, y⁆ ∈ oddCoreOf K' := fun x hx y hy =>
    hcomm (Subgroup.commutator_mem_commutator hx hy)
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz
  have hNodd := oddCoreOf_odd_natCard (K ⊔ K')
  have hKN : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := oddCoreOf_le_oddCoreOf_sup hK'N
  have hKN' : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') := by
    have h' : K ≤ Subgroup.normalizer (K' : Set G) :=
      Sec6Gen.le_normalizer_of_twin hΩ hK hK' hne.symm hz hz'
    have := oddCoreOf_le_oddCoreOf_sup h'
    rwa [sup_comm] at this
  have hzc : ∀ x ∈ K ⊔ K', z * x = x * z := by
    intro x hx
    have : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
      sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hw).symm)
        (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hz'.commute_of_mem hw).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hx)).symm
  have hφz := chart_apply_z hodd hz hφk
  have hφ'z := chart_apply_z hodd hz' hφ'k
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K K' hK'N] at hs
  obtain ⟨k, hk, k', hk', rfl⟩ := hs
  have hak : ⁅k', k⁆ ∈ oddCoreOf K := by
    rw [← commutatorElement_inv]
    exact (oddCoreOf K).inv_mem (hc k hk k' hk').1
  have hoK : k * ⁅k', k⁆ * k⁻¹ ∈ oddCoreOf K :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hk)) _).mp hak
  set o : G := k * ⁅k', k⁆ * k⁻¹ with ho
  have hkey : (k * k') * (k * k') = o * (k * k) * (k' * k') := by
    rw [ho, commutatorElement_def]
    group
  have h1 : o * (k * k) * (k' * k') = 1 := by rw [← hkey]; exact hs2
  have hc1 : (k' * k')⁻¹ = o * (k * k) := (eq_inv_of_mul_eq_one_left h1).symm
  set c : G := (k' * k')⁻¹ with hc0
  have hoKK : o ∈ K := oddCoreOf_le_self K hoK
  have hcK' : c ∈ K' := K'.inv_mem (K'.mul_mem hk' hk')
  have hcK : c ∈ K := by rw [hc1]; exact K.mul_mem hoKK (K.mul_mem hk hk)
  have hφc : φ ⟨c, hcK⟩ = φ ⟨k, hk⟩ * φ ⟨k, hk⟩ := by
    have hoφ : φ ⟨o, hoKK⟩ = 1 := (hφk _).mpr (mem_oddCoreOf_iff.mp hoK).2
    have : (⟨c, hcK⟩ : ↥K) = ⟨o, hoKK⟩ * (⟨k, hk⟩ * ⟨k, hk⟩) := Subtype.ext hc1
    rw [this, map_mul, map_mul, hoφ, one_mul]
  have hφ'c : φ' ⟨c, hcK'⟩ = (φ' ⟨k', hk'⟩ * φ' ⟨k', hk'⟩)⁻¹ := by
    have : (⟨c, hcK'⟩ : ↥K') = (⟨k', hk'⟩ * ⟨k', hk'⟩)⁻¹ := rfl
    rw [this, map_inv, map_mul]
  have hcen : φ ⟨c, hcK⟩ ∈ Subgroup.center SL(2, GaloisField 3 1) :=
    chart_central hφs hφk hcK (fun y hy => by
      rw [← commutatorElement_inv]
      exact (oddCoreOf K).inv_mem (hc y hy c hcK').1)
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hcen with hA | hB
  · exfalso
    have hcO : c ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨hcK, (hφk _).mp hA⟩
    have hcO' : c ∈ oddCoreOf K' := oddCoreOf_sup_inf_le (hKN hcO) hcK'
    have hφ'c1 : φ' ⟨c, hcK'⟩ = 1 := (hφ'k _).mpr (mem_oddCoreOf_iff.mp hcO').2
    have hk1 : φ ⟨k, hk⟩ * φ ⟨k, hk⟩ = 1 := by rw [← hφc]; exact hA
    have hk'1 : φ' ⟨k', hk'⟩ * φ' ⟨k', hk'⟩ = 1 := by
      rw [hφ'c] at hφ'c1
      exact inv_eq_one.mp hφ'c1
    obtain ⟨e, he, hkO⟩ := exists_mul_mem_oddCore hodd hz hφk hk (sl2_sq_cases hodd hk1)
    obtain ⟨e', he', hk'O⟩ := exists_mul_mem_oddCore hodd hz' hφ'k hk' (sl2_sq_cases hodd hk'1)
    have hKK' : k * k' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right hk')
    have hzk' : z * k' = k' * z := hzc k' (Subgroup.mem_sup_right hk')
    have hec : ∀ x ∈ K ⊔ K', e * x = x * e := by
      intro x hx
      rcases he with rfl | rfl
      · simp
      · exact hzc x hx
    have hec' : ∀ x ∈ K ⊔ K', e' * x = x * e' := by
      intro x hx
      rcases he' with rfl | rfl
      · simp
      · exact hzc x hx
    obtain ⟨w, hw, hwe⟩ : ∃ w : G, (w = 1 ∨ w = z) ∧ w = e * e' := by
      refine ⟨e * e', ?_, rfl⟩
      rcases he with rfl | rfl <;> rcases he' with rfl | rfl
      · left; simp
      · right; simp
      · right; simp
      · left; exact hz.sq
    have hwc : ∀ x ∈ K ⊔ K', w * x = x * w := by
      intro x hx
      rcases hw with rfl | rfl
      · simp
      · exact hzc x hx
    have hw2 : w * w = 1 := by
      rcases hw with rfl | rfl
      · simp
      · exact hz.sq
    have hu : (k * k') * w ∈ oddCoreOf (K ⊔ K') := by
      have : (k * k') * w = (k * e) * (k' * e') := by
        rw [hwe]
        calc k * k' * (e * e') = k * (k' * e) * e' := by group
          _ = k * (e * k') * e' := by rw [← hec k' (Subgroup.mem_sup_right hk')]
          _ = (k * e) * (k' * e') := by group
      rw [this]
      exact (oddCoreOf (K ⊔ K')).mul_mem (hKN hkO) (hKN' hk'O)
    have huu : ((k * k') * w) * ((k * k') * w) = 1 := by
      calc ((k * k') * w) * ((k * k') * w) = (k * k') * (w * (k * k')) * w := by group
        _ = (k * k') * ((k * k') * w) * w := by rw [hwc _ hKK']
        _ = ((k * k') * (k * k')) * (w * w) := by group
        _ = 1 := by rw [hs2, hw2, one_mul]
    have hu1 : (k * k') * w = 1 := by
      by_contra hne1
      exact hne1 (eq_one_of_isPGroup_of_mem_odd hNodd hu
        (isPGroup_zpowers_of_mul_self_eq_one huu hne1))
    rcases hw with h | h
    · rw [h] at hu1
      exact hs1 (by simpa using hu1)
    · rw [h] at hu1
      apply hsz
      show k * k' = z
      have := eq_inv_of_mul_eq_one_left hu1
      rw [this]
      exact inv_eq_of_mul_eq_one_right hz.sq
  · have hk2 : φ ⟨k, hk⟩ * φ ⟨k, hk⟩ = -1 := by rw [← hφc]; exact hB
    have hczK : c * z ∈ oddCoreOf K := by
      refine mem_oddCoreOf_iff.mpr ⟨K.mul_mem hcK hz.mem, (hφk _).mp ?_⟩
      have : (⟨c * z, K.mul_mem hcK hz.mem⟩ : ↥K) = ⟨c, hcK⟩ * ⟨z, hz.mem⟩ := rfl
      rw [this, map_mul, hB, hφz]
      simp
    have hczK' : c * z ∈ oddCoreOf K' :=
      oddCoreOf_sup_inf_le (hKN hczK) (K'.mul_mem hcK' hz'.mem)
    have hφ'cz : φ' ⟨c, hcK'⟩ * φ' ⟨z, hz'.mem⟩ = 1 := by
      have h1 : φ' ⟨c * z, K'.mul_mem hcK' hz'.mem⟩ = 1 :=
        (hφ'k _).mpr (mem_oddCoreOf_iff.mp hczK').2
      have : (⟨c * z, K'.mul_mem hcK' hz'.mem⟩ : ↥K') = ⟨c, hcK'⟩ * ⟨z, hz'.mem⟩ := rfl
      rw [this, map_mul] at h1
      exact h1
    have hφ'c' : φ' ⟨c, hcK'⟩ = -1 := by
      rw [hφ'z] at hφ'cz
      have h2 : φ' ⟨c, hcK'⟩ = ((-1 : SL(2, GaloisField 3 1)))⁻¹ := eq_inv_of_mul_eq_one_left hφ'cz
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (by simp)
    refine ⟨k, hk, k', hk', rfl, hk2, ?_⟩
    rw [hφ'c] at hφ'c'
    have h3 := inv_eq_iff_eq_inv.mp hφ'c'
    rw [h3]
    exact inv_eq_of_mul_eq_one_right (by simp)

theorem exists_conj_of_involutions_sup_modGen (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K)
    {z : G} (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) {s s' : G}
    (hs : s ∈ K ⊔ K') (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) (hs' : s' ∈ K ⊔ K')
    (hs'2 : s' * s' = 1) (hs'1 : s' ≠ 1) (hs'z : s' ≠ z) :
    ∃ m ∈ K ⊔ K', m * s * m⁻¹ = s' := by
  have hΩg := hypGen_of_modU hΩ
  have hodd := odd_natCard_galoisField3
  obtain ⟨φ, hφs, hφk⟩ := exists_chart3 hΩ hK
  obtain ⟨φ', hφ's, hφ'k⟩ := exists_chart3 hΩ hK'
  have hcomm := Sec6Gen.comm_le_oddCore_of_twin hΩg hK hK' hne.symm hz hz'
  have hc : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ oddCoreOf K ∧ ⁅x, y⁆ ∈ oddCoreOf K' := fun x hx y hy =>
    hcomm (Subgroup.commutator_mem_commutator hx hy)
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩg hK' hK hne hz' hz
  have hKN'' : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩg hK hK' hne.symm hz hz'
  have hNodd := oddCoreOf_odd_natCard (K ⊔ K')
  have hKN : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := oddCoreOf_le_oddCoreOf_sup hK'N
  have hKN' : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') := by
    have := oddCoreOf_le_oddCoreOf_sup hKN''
    rwa [sup_comm] at this
  have hNnorm : ∀ x ∈ K ⊔ K', ∀ n ∈ oddCoreOf (K ⊔ K'), x * n * x⁻¹ ∈ oddCoreOf (K ⊔ K') :=
    fun x hx n hn => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hx)) n).mp hn
  obtain ⟨k, hk, k', hk', rfl, hk2, hk'2⟩ :=
    exists_sq_dataGen hΩg hK hK' hne hz hz' hφs hφk hφ'k hs hs2 hs1 hsz
  obtain ⟨h, hh, h', hh', rfl, hh2, hh'2⟩ :=
    exists_sq_dataGen hΩg hK hK' hne hz hz' hφs hφk hφ'k hs' hs'2 hs'1 hs'z
  obtain ⟨g₀, hg₀⟩ := exists_sl2_conj_of_sq_eq_neg_one hodd hk2 hh2
  obtain ⟨g, rfl⟩ := hφs g₀
  obtain ⟨g₁, hg₁⟩ := exists_sl2_conj_of_sq_eq_neg_one hodd hk'2 hh'2
  obtain ⟨g', rfl⟩ := hφ's g₁
  have hgK : (g : G) ∈ K := g.2
  have hg'K' : (g' : G) ∈ K' := g'.2
  have ho₂ : h⁻¹ * ((g : G) * k * (g : G)⁻¹) ∈ oddCoreOf K := by
    have hmem : h⁻¹ * ((g : G) * k * (g : G)⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hh) (K.mul_mem (K.mul_mem hgK hk) (K.inv_mem hgK))
    refine mem_oddCoreOf_iff.mpr ⟨hmem, (hφk _).mp ?_⟩
    have : (⟨h⁻¹ * ((g : G) * k * (g : G)⁻¹), hmem⟩ : ↥K) =
        (⟨h, hh⟩ : ↥K)⁻¹ * (g * ⟨k, hk⟩ * g⁻¹) := rfl
    rw [this, map_mul, map_inv, map_mul, map_mul, map_inv]
    have h1 : φ g * φ ⟨k, hk⟩ * (φ g)⁻¹ = φ ⟨h, hh⟩ := by
      rw [hg₀, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1, inv_mul_cancel]
  have ho₂' : h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹) ∈ oddCoreOf K' := by
    have hmem : h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹) ∈ K' :=
      K'.mul_mem (K'.inv_mem hh') (K'.mul_mem (K'.mul_mem hg'K' hk') (K'.inv_mem hg'K'))
    refine mem_oddCoreOf_iff.mpr ⟨hmem, (hφ'k _).mp ?_⟩
    have : (⟨h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹), hmem⟩ : ↥K') =
        (⟨h', hh'⟩ : ↥K')⁻¹ * (g' * ⟨k', hk'⟩ * g'⁻¹) := rfl
    rw [this, map_mul, map_inv, map_mul, map_mul, map_inv]
    have h1 : φ' g' * φ' ⟨k', hk'⟩ * (φ' g')⁻¹ = φ' ⟨h', hh'⟩ := by
      rw [hg₁, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1, inv_mul_cancel]
  have ha : ⁅(g' : G), k⁆ ∈ oddCoreOf K := by
    rw [← commutatorElement_inv]
    exact (oddCoreOf K).inv_mem (hc k hk g' hg'K').1
  have hb : ⁅(g : G), h'⁆ ∈ oddCoreOf K' := (hc g hgK h' hh').2
  have ha₁ : (g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹ ∈ oddCoreOf K :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hgK)) _).mp ha
  have hKK : k * k' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mem_sup_right hk')
  have hmM : (g : G) * g' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hgK)
    (Subgroup.mem_sup_right hg'K')
  have hhh : h * h' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hh)
    (Subgroup.mem_sup_right hh')
  have hhM : h ∈ K ⊔ K' := Subgroup.mem_sup_left hh
  have hh'M : h' ∈ K ⊔ K' := Subgroup.mem_sup_right hh'
  have hgM : (g : G) ∈ K ⊔ K' := Subgroup.mem_sup_left hgK
  have hn₃ : (g : G) * (h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹)) * (g : G)⁻¹ ∈ oddCoreOf (K ⊔ K') :=
    hNnorm g hgM _ (hKN' ho₂')
  have hX : (h⁻¹ * ((g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹) * h) *
      (h⁻¹ * ((g : G) * k * (g : G)⁻¹)) * ⁅(g : G), h'⁆ ∈ oddCoreOf (K ⊔ K') := by
    refine (oddCoreOf (K ⊔ K')).mul_mem ((oddCoreOf (K ⊔ K')).mul_mem ?_ (hKN ho₂)) (hKN' hb)
    have := hNnorm h⁻¹ ((K ⊔ K').inv_mem hhM) _ (hKN ha₁)
    simpa using this
  have hY : h'⁻¹ * ((h⁻¹ * ((g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹) * h) *
      (h⁻¹ * ((g : G) * k * (g : G)⁻¹)) * ⁅(g : G), h'⁆) * h' *
      ((g : G) * (h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹)) * (g : G)⁻¹) ∈ oddCoreOf (K ⊔ K') := by
    refine (oddCoreOf (K ⊔ K')).mul_mem ?_ hn₃
    have := hNnorm h'⁻¹ ((K ⊔ K').inv_mem hh'M) _ hX
    simpa using this
  have hcoset : (h * h')⁻¹ * (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) ∈
      oddCoreOf (K ⊔ K') := by
    have e : (h * h')⁻¹ * (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) =
        h'⁻¹ * ((h⁻¹ * ((g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹) * h) *
          (h⁻¹ * ((g : G) * k * (g : G)⁻¹)) * ⁅(g : G), h'⁆) * h' *
          ((g : G) * (h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹)) * (g : G)⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact hY
  have hs₂ : (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) *
      (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) = 1 := by
    calc _ = ((g : G) * g') * ((k * k') * (k * k')) * ((g : G) * g')⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  obtain ⟨n, hnN, hn⟩ := exists_conj_of_involutions_coset hNodd hs'2 hs₂
    (by simpa using (oddCoreOf (K ⊔ K')).inv_mem hcoset)
  refine ⟨n * ((g : G) * g'), (K ⊔ K').mul_mem (oddCoreOf_le_self _ hnN) hmM, ?_⟩
  rw [← hn]
  group

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
