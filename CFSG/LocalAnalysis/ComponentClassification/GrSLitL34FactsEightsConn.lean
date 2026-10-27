module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsConnModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsConj

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem comm_of_le_elem {X Y W : Subgroup G} (hW : IsElemTwo W) (hX : X ≤ W) (hY : Y ≤ W) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := fun x hx y hy => hW.1 x (hX hx) y (hY hy)

variable [Finite G]

theorem connected_step {J X Y W : Subgroup G} (h : AbelianConnectedIn J 3 X Y) (hW : W ≤ J)
    (hWe : IsElemTwo W) (hW8 : 8 ≤ Nat.card W) (hc : ∀ x ∈ Y, ∀ y ∈ W, x * y = y * x) :
    AbelianConnectedIn J 3 X W :=
  ⟨h.1, h.2.1, h.2.2.tail ⟨hW, hWe.isAbelianTwoOfRank hW8, hc⟩⟩

theorem l34EightsConnectedFact :
    L34EightsConnectedFact := by
  intro G _ _ J P hJ hL hP hcyc _ E F hEP hFP hE hF
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨K, hK⟩ := exists_omegaZ hP
  have hK4 := card_omegaZ hQ hP hcyc hK
  have hKZ : ∀ k ∈ K, k ∈ P ⊓ zStarIn J := fun k hk => ((hK k).1 hk).1
  have hKP : K ≤ P := fun k hk => (mem_inf.mp (hKZ k hk)).1
  have hKc : ∀ k ∈ K, ∀ p ∈ P, k * p = p * k := fun k hk p hp => comm_of_mem_Z hP (hKZ k hk) hp
  have hKe : IsElemTwo K := ⟨fun x hx y hy => hKc x hx y (hKP hy), fun k hk => ((hK k).1 hk).2⟩
  have hmulP : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      jq J ⟨u * v, hP.1 (P.mul_mem hu hv)⟩ = jq J ⟨u, hP.1 hu⟩ * jq J ⟨v, hP.1 hv⟩ :=
    fun hu hv => by rw [← map_mul]; rfl
  obtain ⟨c₄, hc₄P, hc₄J, hc₄e⟩ := (hT (ilift l (4, 1, 1, 1))).1 (by
    rw [hQ.q_ilift (by norm_num)]
    exact tg_mem_T0 4 (by norm_num))
  have hqc₄ : q (jq J ⟨c₄, hc₄J⟩) = wordPerm (tg 4) := by
    rw [hc₄e, hQ.q_ilift (by norm_num)]
  have hA : ∀ {x : G}, x ∈ P → x * x = 1 → x ∉ K →
      IsElemTwo (zpowers x ⊔ K) ∧ Nat.card ↥(zpowers x ⊔ K) = 8 ∧ zpowers x ⊔ K ≤ P := by
    intro x hxP hx2 hxK
    have hxc : ∀ y ∈ K, x * y = y * x := fun y hy => (hKc y hy x hxP).symm
    refine ⟨(isElemTwo_zpowers hx2).sup hKe (commute_zpowers_left hxc), ?_,
      sup_le (zpowers_le.2 hxP) hKP⟩
    rw [card_zpowers_sup_eq hx2 (mem_normalizer_of_commute hxc) hxK, hK4]
  have hcomm4 : ∀ {x : G} (hxP : x ∈ P), q (jq J ⟨x, hP.1 hxP⟩) = wordPerm (tg 4) →
      ∀ a ∈ zpowers x ⊔ K, ∀ b ∈ zpowers c₄ ⊔ K, a * b = b * a := by
    intro x hxP hqx
    have hz : c₄⁻¹ * x ∈ P ⊓ zStarIn J := by
      refine mem_inf.mpr ⟨P.mul_mem (P.inv_mem hc₄P) hxP, ?_⟩
      rw [mem_zStarIn_iff (hP.1 (P.mul_mem (P.inv_mem hc₄P) hxP)), ← hqker, MonoidHom.mem_ker]
      have e : (⟨c₄⁻¹ * x, hP.1 (P.mul_mem (P.inv_mem hc₄P) hxP)⟩ : J) =
          (⟨c₄, hc₄J⟩ : J)⁻¹ * ⟨x, hP.1 hxP⟩ := rfl
      rw [e, map_mul, map_mul, map_inv, map_inv, hqc₄, hqx, inv_mul_cancel]
    have hxc₄ : x * c₄ = c₄ * x := by
      have h1 := comm_of_mem_Z hP hz hc₄P
      calc x * c₄ = c₄ * ((c₄⁻¹ * x) * c₄) := by group
        _ = c₄ * (c₄ * (c₄⁻¹ * x)) := by rw [h1]
        _ = c₄ * x := by group
    refine commute_sup_left (commute_sup_right (commute_zpowers_zpowers hxc₄) ?_)
      (commute_sup_right ?_ hKe.1)
    · exact commute_zpowers_left fun y hy => (hKc y hy x hxP).symm
    · exact commute_symm (commute_zpowers_left fun y hy => (hKc y hy c₄ hc₄P).symm)
  have key : ∀ {E : Subgroup G}, E ≤ P → IsEightGroup E → ∃ e ∈ E, e ∉ K ∧ ∃ n ∈ J,
      (∀ k ∈ K, n * k * n⁻¹ = k) ∧ ∃ he' : n * e * n⁻¹ ∈ P,
        q (jq J ⟨n * e * n⁻¹, hP.1 he'⟩) = wordPerm (tg 4) := by
    intro E hEP hE
    have hEK : ¬ E ≤ K := fun h => by
      have := Subgroup.card_le_of_le h
      rw [hE.2, hK4] at this
      omega
    obtain ⟨e, heE, heK⟩ := Set.not_subset.mp hEK
    have heP := hEP heE
    have he2 := hE.1.2 e heE
    have hq1 : q (jq J ⟨e, hP.1 heP⟩) ≠ 1 := fun h => heK ((hK e).2 ⟨mem_inf.mpr ⟨heP,
      (mem_zStarIn_iff _).2 (by rw [← hqker]; exact h)⟩, he2⟩)
    have hqT : q (jq J ⟨e, hP.1 heP⟩) ∈ T0 := (hT _).2 ⟨e, heP, _, rfl⟩
    have hq2 : q (jq J ⟨e, hP.1 heP⟩) * q (jq J ⟨e, hP.1 heP⟩) = 1 := by
      rw [← map_mul, ← hmulP heP heP]
      have : (⟨e * e, hP.1 (P.mul_mem heP heP)⟩ : J) = 1 := Subtype.ext he2
      rw [this, map_one, map_one]
    refine ⟨e, heE, heK, ?_⟩
    rcases involution_mem_U hqT hq2 with hU | hU
    · obtain ⟨n, hnJ, hnZ, he'P, he'q⟩ := exists_tg4_conj hP hqsurj hqker hT U1_le_T0
        (fun v hv hv1 => by
          obtain ⟨s, hs, hsv⟩ := exists_conj_tg4_U1 hv hv1
          exact ⟨s, closure_wordSet_le _ hs, P1_le_normalizer_U1 hs, hsv⟩) heP hU hq1
      exact ⟨n, hnJ, fun k hk => hnZ k (hKZ k hk), he'P, he'q⟩
    · obtain ⟨n, hnJ, hnZ, he'P, he'q⟩ := exists_tg4_conj hP hqsurj hqker hT U2_le_T0
        (fun v hv hv1 => by
          obtain ⟨s, hs, hsv⟩ := exists_conj_tg4_U2 hv hv1
          exact ⟨s, closure_wordSet_le _ hs, P2_le_normalizer_U2 hs, hsv⟩) heP hU hq1
      exact ⟨n, hnJ, fun k hk => hnZ k (hKZ k hk), he'P, he'q⟩
  have hconjA : ∀ {x n : G}, (∀ k ∈ K, n * k * n⁻¹ = k) →
      ∀ a ∈ zpowers x ⊔ K, n * a * n⁻¹ ∈ zpowers (n * x * n⁻¹) ⊔ K := by
    intro x n hnK a ha
    have hle : zpowers x ⊔ K ≤ (zpowers (n * x * n⁻¹) ⊔ K).comap (MulAut.conj n).toMonoidHom :=
      sup_le (zpowers_le.2 (by
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left (mem_zpowers _))) fun k hk => by
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hnK k hk]
        exact mem_sup_right hk
    exact hle ha
  obtain ⟨e, heE, heK, nE, hnEJ, hnEK, he'P, he'q⟩ := key hEP hE
  obtain ⟨f, hfF, hfK, nF, hnFJ, hnFK, hf'P, hf'q⟩ := key hFP hF
  have hc₄K : c₄ ∉ K := fun h => by
    have := ((hK c₄).1 h).1
    have h1 := (mem_zStarIn_iff hc₄J).1 (mem_inf.mp this).2
    rw [← hqker, MonoidHom.mem_ker, hqc₄, ← wordPerm_tg_zero] at h1
    exact absurd (tg_injective (by norm_num) (by norm_num) h1) (by norm_num)
  have hc₄2 : c₄ * c₄ = 1 := by
    apply eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hc₄P hc₄P)
    rw [hmulP hc₄P hc₄P]
    have : (⟨c₄, hP.1 hc₄P⟩ : J) = ⟨c₄, hc₄J⟩ := rfl
    rw [this, hc₄e]
    exact hQ.ilift_mul_self (by decide)
  obtain ⟨hA4e, hA48, hA4P⟩ := hA hc₄P hc₄2 hc₄K
  obtain ⟨hAee, hAe8, hAeP⟩ := hA (hEP heE) (hE.1.2 e heE) heK
  obtain ⟨hAfe, hAf8, hAfP⟩ := hA (hFP hfF) (hF.1.2 f hfF) hfK
  set g := nF⁻¹ * nE with hg
  have hgJ : g ∈ J := J.mul_mem (J.inv_mem hnFJ) hnEJ
  have hEKe : IsElemTwo (E ⊔ K) :=
    hE.1.sup hKe fun x hx y hy => (hKc y hy x (hEP hx)).symm
  have hFKe : IsElemTwo (F ⊔ K) :=
    hF.1.sup hKe fun x hx y hy => (hKc y hy x (hFP hx)).symm
  have hEK8 : 8 ≤ Nat.card ↥(E ⊔ K) := hE.2 ▸ Subgroup.card_le_of_le le_sup_left
  have hFK8 : 8 ≤ Nat.card ↥(F ⊔ K) := hF.2 ▸ Subgroup.card_le_of_le le_sup_left
  have hAeEK : zpowers e ⊔ K ≤ E ⊔ K := sup_le (zpowers_le.2 (mem_sup_left heE)) le_sup_right
  have hAfFK : zpowers f ⊔ K ≤ F ⊔ K := sup_le (zpowers_le.2 (mem_sup_left hfF)) le_sup_right
  refine ⟨g, hgJ, ?_⟩
  have c0 : AbelianConnectedIn J 3 E E :=
    ⟨hEP.trans hP.1, hE.1.isAbelianTwoOfRank (by rw [hE.2]), Relation.ReflTransGen.refl⟩
  have c1 := connected_step c0 ((sup_le hEP hKP).trans hP.1) hEKe hEK8
    (comm_of_le_elem hEKe le_sup_left le_rfl)
  have c2 := connected_step c1 (hAeP.trans hP.1) hAee (by rw [hAe8])
    (comm_of_le_elem hEKe le_rfl hAeEK)
  have c3 := connected_step c2 (conjugate_le (hA4P.trans hP.1) hnEJ)
    (isElemTwo_conjugate hA4e nE) (by rw [card_conjugate, hA48]) fun a ha b hb => by
      have h1 := hcomm4 he'P he'q _ (hconjA hnEK a ha) _ (mem_conjugate_iff.1 hb)
      calc a * b = nE⁻¹ * ((nE * a * nE⁻¹) * (nE * b * nE⁻¹)) * nE := by group
        _ = nE⁻¹ * ((nE * b * nE⁻¹) * (nE * a * nE⁻¹)) * nE := by rw [h1]
        _ = b * a := by group
  have c4 := connected_step c3 (conjugate_le (hAfP.trans hP.1) hgJ)
    (isElemTwo_conjugate hAfe g) (by rw [card_conjugate, hAf8]) fun a ha b hb => by
      have hb' := hconjA hnFK _ (mem_conjugate_iff.1 hb)
      rw [show nF * (g * b * g⁻¹) * nF⁻¹ = nE * b * nE⁻¹ by rw [hg]; group] at hb'
      have h1 := hcomm4 hf'P hf'q _ hb' _ (mem_conjugate_iff.1 ha)
      calc a * b = nE⁻¹ * ((nE * a * nE⁻¹) * (nE * b * nE⁻¹)) * nE := by group
        _ = nE⁻¹ * ((nE * b * nE⁻¹) * (nE * a * nE⁻¹)) * nE := by rw [h1]
        _ = b * a := by group
  have c5 := connected_step c4 (conjugate_le ((sup_le hFP hKP).trans hP.1) hgJ)
    (isElemTwo_conjugate hFKe g) (by rw [card_conjugate]; exact hFK8)
    (comm_conjugate (comm_of_le_elem hFKe hAfFK le_rfl) g)
  exact connected_step c5 (conjugate_le (hFP.trans hP.1) hgJ) (isElemTwo_conjugate hF.1 g)
    (by rw [card_conjugate, hF.2]) (comm_conjugate (comm_of_le_elem hFKe le_rfl le_sup_left) g)

end CFSG.ComponentClassification.GrSLit.L34Facts
