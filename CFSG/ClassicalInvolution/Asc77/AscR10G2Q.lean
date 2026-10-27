module

public import CFSG.ClassicalInvolution.Asc77.AscR10G2R

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped commutatorElement



section Quot

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem omega4_quot_odd_gen (hΩ : HypOmegaGen Ω)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hne : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N)) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
        J.map (QuotientGroup.mk' N))) = 1 →
        ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' N)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' N))) := by
  set mk := QuotientGroup.mk' N with hmk
  by_cases h2 : 2 ∣ Nat.card ↥(K.map mk ⊓ J.map mk)
  swap
  · have : padicValNat 2 (Nat.card ↥(K.map mk ⊓ J.map mk)) = 0 :=
      padicValNat.eq_zero_of_not_dvd h2
    exact ⟨by omega, fun h => by omega⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hzb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
  have htb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN J) ht
  have hzmem : mk z ∈ K.map mk ⊓ J.map mk := mem_of_two_dvd_card hzb inf_le_left h2
  have hzt : mk z = mk t := by
    rcases htb.unique (mk z) hzmem.2 hzb.sq with h | h
    · exact absurd h hzb.ne_one
    · exact h
  obtain ⟨n, hn, hnt⟩ := exists_conj_eq_of_map_eq hN hz.sq ht.sq hzt
  have hnN : mk n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hJ' : conjSub n J ∈ Ω := hΩ.conjInvariant n J hJ
  have hJ'z : IsUniqueInvolution (conjSub n J) z := by
    have := ht.conj n
    rwa [hnt] at this
  have himg : (conjSub n J).map mk = J.map mk := by
    rw [AscQuot.map_conjSub, hnN, conjSub_one]
  have hne' : K ≠ conjSub n J := fun h => hne (by rw [h, himg])
  have hcomm := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ' hne' hz hJ'z
  have hsub : ∀ b ∈ K.map mk ⊓ J.map mk, IsPGroup 2 (Subgroup.zpowers b) →
      b = 1 ∨ b = mk z := by
    rintro b ⟨hbK, hbJ⟩ hb2
    obtain ⟨k, hk, hkb, hk2⟩ := exists_isPGroup_lift_of_mem_map hbK hb2
    obtain ⟨x, hx, hxb⟩ : b ∈ (conjSub n J).map mk := by
      rw [himg]
      exact hbJ
    rcases eq_one_or_eq_of_map_eq_of_twin_gen hΩ hN hK hJ' hne' hz hJ'z hx hk hk2
      (hxb.trans hkb.symm) with h1 | h1
    · left
      rw [← hkb, h1, map_one]
    · right
      rw [← hkb, h1]
  refine ⟨padicValNat_natCard_le_one_of_forall_isPGroup hsub, fun _ => ?_⟩
  have h1 : ⁅K.map mk, J.map mk⁆ = (⁅K, conjSub n J⁆).map mk := by
    rw [Subgroup.map_commutator, himg]
  have hK' : oddCoreOf (K.map mk) = (oddCoreOf K).map mk :=
    oddCoreOf_map_mk_of_odd (odd_natCard_inf hN K)
  have hJ'' : oddCoreOf (J.map mk) = (oddCoreOf (conjSub n J)).map mk := by
    rw [← himg]
    exact oddCoreOf_map_mk_of_odd (odd_natCard_inf hN (conjSub n J))
  rw [h1, hK', hJ'']
  exact le_inf (Subgroup.map_mono (hcomm.trans inf_le_left))
    (Subgroup.map_mono (hcomm.trans inf_le_right))


theorem omega5_quot_odd_gen (hΩ : HypOmegaGen Ω)
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∀ L' ∈ quotFamily Ω N, L ≠ L' → ∀ z : G ⧸ N, IsUniqueInvolution L z →
      ∀ v ∈ L', (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (L : Set (G ⧸ N)) := by
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne z' hz' _ ⟨v₀, hv₀J, rfl⟩ hvnc hv2 hcomm
  have hne0 : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N) := hne
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hz'eq : z' = QuotientGroup.mk' N z :=
    hz'.eq (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz)
  obtain ⟨v, hvJ, hvmk, hv2'⟩ :=
    exists_isPGroup_lift_of_mem_map (Subgroup.mem_map_of_mem _ hv₀J) hv2
  have hvnc' : ¬ ∀ w ∈ J, v * w = w * v := fun h => hvnc (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hvmk, ← map_mul, ← map_mul, h w hw])
  have hvz : QuotientGroup.mk' N v * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N v := by
    rw [hvmk]
    exact hz'eq ▸ hcomm
  obtain ⟨n, hn, hfix⟩ := exists_fixed_conj_involution hN hz.sq hv2' (V := Subgroup.zpowers v)
    (fun u hu => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [map_zpow]
      exact ((Commute.zpow_left (show Commute (QuotientGroup.mk' N v)
        (QuotientGroup.mk' N z) from hvz) k)).eq)
  have hnN : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hK₁ : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK
  have hz₁ : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) := hz.conj n
  have himg : (conjSub n K).map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) := by
    rw [AscQuot.map_conjSub, hnN, conjSub_one]
  have hK₁J : conjSub n K ≠ J := fun h => hne0 (by rw [← himg, h])
  have hvK₁ : v ∈ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) :=
    hΩ.omega5 (conjSub n K) hK₁ J hJ hK₁J (n * z * n⁻¹) hz₁ v hvJ hvnc' hv2'
      (hfix v (Subgroup.mem_zpowers v))
  have := mk_mem_normalizer_map (N := N) hvK₁
  rw [himg, hvmk] at this
  exact this


end Quot

section OddQuot

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem hypOmegaModU_oddQuotientFamily (hΩ : HypOmegaModU (.sl2 3 1) Λ) :
    HypOmegaModU (.sl2 3 1) (oddQuotientFamily Λ) := by
  have hΩg : HypOmegaGen Λ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AscQuot.conjInvariant_quot hΩ.conjInvariant (classicalInvolutionOddCore Y)
  · rintro _ ⟨K, hK, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical K hK
    exact ⟨_, hz.map_oddQuotient⟩
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    exact omega4_quot_odd_gen hΩg hodd hK hJ hne
  · exact omega5_quot_odd_gen hΩg hodd

end OddQuot

section Twin

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem eq_of_map_eq_of_twin_three (hΩ : HypOmegaModU (.sl2 3 1) Λ) {K K' : Subgroup Y}
    (hK : K ∈ Λ) (hK' : K' ∈ Λ) {z : Y} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (h : K.map (oddQuot Y) = K'.map (oddQuot Y)) : K = K' := by
  by_contra hne
  have hΩg : HypOmegaGen Λ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hc := Sec6Gen.comm_le_oddCore_of_twin hΩg hK hK' hne hz hz'
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have hcomm : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ oddCoreOf K := by
    intro x hx y hy
    have hyK' : oddQuot Y y ∈ K'.map (oddQuot Y) := h ▸ ⟨y, hy, rfl⟩
    obtain ⟨y', hy'K', hy'e⟩ := hyK'
    have hm : y⁻¹ * y' ∈ classicalInvolutionOddCore Y :=
      (QuotientGroup.eq.mp hy'e.symm)
    set m : Y := y⁻¹ * y' with hmdef
    have hy_eq : y = y' * m⁻¹ := by rw [hmdef]; group
    have h1 : ⁅x, y'⁆ ∈ oddCoreOf K := (hc (Subgroup.commutator_mem_commutator hx hy'K')).1
    have hxm : ⁅x, m⁻¹⁆ ∈ classicalInvolutionOddCore Y := by
      have hm' : m⁻¹ ∈ classicalInvolutionOddCore Y := (classicalInvolutionOddCore Y).inv_mem hm
      have := (classicalInvolutionOddCore Y).mul_mem
        (Subgroup.Normal.conj_mem inferInstance _ hm' x) hm
      simpa [commutatorElement_def, mul_assoc] using this
    have hw : y' * ⁅x, m⁻¹⁆ * y'⁻¹ ∈ classicalInvolutionOddCore Y :=
      Subgroup.Normal.conj_mem inferInstance _ hxm y'
    have hid : ⁅x, y⁆ = ⁅x, y'⁆ * (y' * ⁅x, m⁻¹⁆ * y'⁻¹) := by
      rw [hy_eq]
      simp only [commutatorElement_def]
      group
    have hwK : y' * ⁅x, m⁻¹⁆ * y'⁻¹ ∈ K := by
      have hxyK : ⁅x, y⁆ ∈ K := by
        simp only [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
      have h1K : ⁅x, y'⁆ ∈ K := oddCoreOf_le_self K h1
      have : y' * ⁅x, m⁻¹⁆ * y'⁻¹ = (⁅x, y'⁆)⁻¹ * ⁅x, y⁆ := by
        rw [hid]; group
      rw [this]
      exact K.mul_mem (K.inv_mem h1K) hxyK
    have hwO := inf_le_oddCoreOf_of_odd (classicalInvolutionOddCore Y)
      (odd_natCard_inf hodd K) ⟨hwK, hw⟩
    rw [hid]
    exact (oddCoreOf K).mul_mem h1 hwO
  obtain ⟨zK, hzK⟩ := hΩ.classical K hK
  obtain ⟨e⟩ := hzK.nonempty_equiv_sl2Three (show (3 : ℕ) ^ 1 = 3 by norm_num)
  have hab : ∀ a b : ↥K ⧸ classicalInvolutionOddCore ↥K, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply QuotientGroup.eq.mpr
    have h2 : ⁅((y⁻¹ : ↥K) : Y), ((x⁻¹ : ↥K) : Y)⁆ ∈ oddCoreOf K :=
      hcomm _ (y⁻¹).2 _ (x⁻¹).2
    obtain ⟨w, hw, hwe⟩ := h2
    have hw' : w = ⁅y⁻¹, x⁻¹⁆ := by
      apply Subtype.ext
      have h3 : (w : Y) = ⁅((y⁻¹ : ↥K) : Y), ((x⁻¹ : ↥K) : Y)⁆ := hwe
      rw [h3]
      simp [commutatorElement_def]
    have h4 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h4, ← hw']
    exact hw
  apply Q3.sl2Three_not_comm
  intro a b
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact hab _ _

end Twin


section AViolGen

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem mem_normalizer_of_mem_omegaStarNbr_gen (hΩ : HypOmegaGen Λ) {K J : Subgroup Y}
    (hJ : J ∈ omegaStarNbr Λ K) {j : Y} (hj : IsUniqueInvolution J j) :
    j ∈ Subgroup.normalizer (K : Set Y) := by
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hU2 := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  exact hUN (mem_of_isPGroup hj hUJ hU2 (by omega))

theorem commute_of_mem_omegaStarNbr_gen (hΩ : HypOmegaGen Λ) {K J : Subgroup Y}
    (hJ : J ∈ omegaStarNbr Λ K) {z j : Y} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) : z * j = j * z := by
  have h1 := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp
    (mem_normalizer_of_mem_omegaStarNbr_gen hΩ hJ hj))
  have := h1
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem AViol.comm_gen (hΩ : HypOmegaGen Λ) {K J : Subgroup Y} {zK zJ : Y}
    (h : AViol Λ K J zK zJ) : zK * zJ = zJ * zK :=
  commute_of_mem_omegaStarNbr_gen hΩ h.star h.hzK h.hzJ

theorem AViol.ne_involution_gen (hΩ : HypOmegaGen Λ) {K J : Subgroup Y} {zK zJ : Y}
    (hK : K ∈ Λ) (h : AViol Λ K J zK zJ) : zJ ≠ zK := by
  intro he
  subst he
  refine h.not_nbr ?_
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge h.mem (isPGroup_two_bot' (G := Y)) bot_le
  exact ⟨h.mem, h.ne, R, hR, hRJ.1,
    hRJ.1.trans (Sec6Gen.le_normalizer_of_twin hΩ h.mem hK h.ne h.hzJ h.hzK)⟩

end AViolGen

end CFSG.ClassicalInvolution.Asc77.T3CII
