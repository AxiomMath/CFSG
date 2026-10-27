module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadUn
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSInputs
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOutSquare
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43W
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46Z
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWFusEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWSyl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Walter.J1

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

theorem mem_coreActionKernel_of_conj_of_le_normalizer (hMax : MaximalTwoComponentInput)
    {X : Type} [Group X] [Finite X] {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K)
    (hKN : normalizer (W : Set X) ≤ normalizer (K : Set X)) {m : X}
    (hm : m ∈ normalizer (W : Set X)) (hmN : m⁻¹ * a * m ∈ normalizer (J : Set X)) :
    m⁻¹ * a * m ∈ coreActionKernel J := by
  have haK : a ∈ coreActionKernel K := GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs
  have hcK : m⁻¹ * a * m ∈ coreActionKernel K := by
    have h := UnbalancedLayer.conj_mem_coreActionKernel (inv_mem (hKN hm)) haK
    rwa [inv_inv] at h
  have hJK : J ≤ K := GrS4.le_of_singleComponentSetting hs
  have hOK : oddIn K ≤ oddIn (normalizer (W : Set X)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hs.le_normalizer hs.isPComponent_K
  have key : ∀ c : X, c ∈ coreActionKernel K → c ∈ normalizer (J : Set X) →
      c ∈ coreActionKernel J := by
    intro c hcK' hcN
    refine mem_coreActionKernel.mpr ⟨hcN, fun j hj => ?_⟩
    have h1 : j⁻¹ * c⁻¹ * j * c ∈ oddIn K := (mem_coreActionKernel.mp hcK').2 j (hJK hj)
    have h3 : c⁻¹ * j * c ∈ J := by
      have := (mem_normalizer_iff.mp (inv_mem hcN) j).mp hj
      rwa [inv_inv] at this
    have h2 : j⁻¹ * c⁻¹ * j * c ∈ J := by
      have := mul_mem (inv_mem hj) h3
      rwa [← mul_assoc, ← mul_assoc] at this
    have h4 : j⁻¹ * c⁻¹ * j * c ∈ oddIn J := by
      rw [GrS4.oddIn_eq_inf_of_singleComponentSetting hs]
      exact mem_inf.mpr ⟨h2, hOK h1⟩
    exact h4
  exact key _ hcK hmN



theorem exists_conj_of_unitaryKS (hMax : MaximalTwoComponentInput) {G : Type} [Group G] [Finite G]
    {a x : G} {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hcent : ∀ s ∈ S, s * a = a * s) (h3 : IsThreeConnected (S ⊓ withKernel J))
    (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G))
    {K : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hsup : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)))
    (hKN : normalizer (W : Set G) ≤ normalizer (K : Set G))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) {g : G} (hgS : g⁻¹ * a * g ∈ S)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J)) (hU : IsL34Unitary J (g⁻¹ * a * g)) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, haS, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haK : a ∈ coreActionKernel J := GrS4.mem_coreActionKernel_of_le_centralizer hJa
  obtain ⟨⟨hsimple, hnab, hKP, -, hUo, -, -, -⟩, -, -, hmax, -, -, -⟩ := id hset
  have : IsSimpleGroup G := hsimple
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hKP, hUo, ha2, hJa,
    hU3.2.2.2.2.1, hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34,
    Or.inl ⟨hL34, hset.1⟩⟩
  have hsc : SingleComponentSetting G a J W K :=
    { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
      normalizer_ne_top := GrS4.normalizer_ne_top_of_odd hW hWodd ha2,
      le_normalizer := hKM, isPComponent_K := hKc, sup_eq := hsup }
  have hCM : centralizer ({a} : Set G) ≤ normalizer (W : Set G) :=
    (centralizer_le_normalizer_of_sec4 hMax hset).trans hNJ
  set b : G := g⁻¹ * a * g with hbdef
  have hbK : b ∉ withKernel J := hU.2.2.1
  obtain ⟨y, hyP, hyb, hy2, hy4⟩ := exists_sq_ne_one_of_unitary hJper hL34 hP hgS hU hZc
  have hbN : b ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    UnbalancedLayer.normalizer_inf_mem (le_normalizer hgS) hU.1
  obtain ⟨-, -, -, -, -, -, -, hconjinv⟩ :=
    L34Facts.l34UnitaryCentralizerFact G J (S ⊓ J) b hJper hL34 hU hP hbN
  have hzb : y * y * b = b * (y * y) := by
    rw [mul_assoc, hyb, ← mul_assoc, hyb, mul_assoc]
  obtain ⟨q, -, hzq⟩ := hconjinv (y * y) (mul_mem hyP hyP) (by
    rw [show y * y * b * (y * y * b) = y * y * (b * (y * y)) * b by group, ← hzb,
      show y * y * (y * y * b) * b = y * y * (y * y) * (b * b) by group, hy4, hU.2.1, one_mul])
  obtain ⟨h, hbh, hSh⟩ := exists_conj_of_le_centralizer hS2 hcent hSyl
    (P := S ⊓ centralizer ({b} : Set G)) (hS2.to_le inf_le_left) inf_le_right
  have hyS' : h⁻¹ * y * h ∈ S :=
    hSh y (mem_inf.mpr ⟨(mem_inf.mp hyP).1, mem_centralizer_singleton_iff.mpr hyb⟩)
  have haS' : h⁻¹ * a * h ∈ S :=
    hSh a (mem_inf.mpr ⟨haS, mem_centralizer_singleton_iff.mpr (hcent b hgS).symm⟩)
  have hz' : h⁻¹ * (y * y) * h = h⁻¹ * y * h * (h⁻¹ * y * h) := by group
  have hz'S : h⁻¹ * (y * y) * h ∈ S := by rw [hz']; exact mul_mem hyS' hyS'
  have hz'K : h⁻¹ * (y * y) * h ∈ withKernel J := by
    rw [hz']
    exact L34Facts.outSquare G J hJper hL34 _ (hS.1 hyS') (hS2.to_le (zpowers_le.mpr hyS'))
  by_cases ha'K : h⁻¹ * a * h ∈ withKernel J
  · exact exists_conj_of_conj hCM hbh
      (exists_conj_of_mem_withKernel hset hcent h3 hWB hNJ hSyl haS' ha'K)
  set z' : G := h⁻¹ * (y * y) * h with hz'def
  set a' : G := h⁻¹ * a * h with ha'def
  have hz'a : (g * q * h)⁻¹ * a * (g * q * h) = z' * a := by
    calc (g * q * h)⁻¹ * a * (g * q * h) = h⁻¹ * (q⁻¹ * b * q) * h := by rw [hbdef]; group
      _ = h⁻¹ * (y * y * b) * h := by rw [← hzq]
      _ = z' * (h⁻¹ * b * h) := by rw [hz'def]; group
      _ = z' * a := by rw [hbh]
  have hz'aS : z' * a ∈ S := mul_mem hz'S haS
  have hz'aK : z' * a ∈ withKernel J := mul_mem hz'K (mem_sup_right haK)
  obtain ⟨m, hm, hmz⟩ := exists_conj_of_mem_withKernel hset hcent h3 hWB hNJ hSyl
    (g := g * q * h) (hz'a ▸ hz'aS) (hz'a ▸ hz'aK)
  have hmN : m⁻¹ * a * m ∈ normalizer (J : Set G) := by
    rw [← hmz, hz'a]
    exact hS.1 hz'aS
  have hz'aC : z' * a ∈ coreActionKernel J := by
    rw [← hz'a, hmz]
    exact mem_coreActionKernel_of_conj_of_le_normalizer hMax hsc hKN hm hmN
  have hz'C : z' ∈ coreActionKernel J := by
    have := mul_mem hz'aC (inv_mem haK)
    rwa [mul_inv_cancel_right] at this
  have ha'a : a' * a = a * a' := hcent a' haS'
  have ha'2 : a' * a' = 1 := by
    rw [ha'def, show h⁻¹ * a * h * (h⁻¹ * a * h) = h⁻¹ * (a * a) * h by group, haa]
    group
  have hz'2 : z' * z' = 1 := by
    rw [hz'def, show h⁻¹ * (y * y) * h * (h⁻¹ * (y * y) * h) = h⁻¹ * (y * y * (y * y)) * h by
      group, hy4]
    group
  have hz'a' : z' * a' = a' * z' := by
    rw [hz'def, ha'def, show h⁻¹ * (y * y) * h * (h⁻¹ * a * h) = h⁻¹ * (y * y * a) * h by group,
      hcent _ (mem_inf.mp (mul_mem hyP hyP)).1]
    group
  have hz'1 : z' ≠ 1 := fun h1 => hy2 (by
    calc y * y = h * z' * h⁻¹ := by rw [hz'def]; group
      _ = 1 := by rw [h1]; group)
  have hz'a1 : z' ≠ a := fun h1 => hbK (by
    have e : b = y * y := by
      calc b = h * (h⁻¹ * b * h) * h⁻¹ := by group
        _ = h * a * h⁻¹ := by rw [hbh]
        _ = h * z' * h⁻¹ := by rw [h1]
        _ = y * y := by rw [hz'def]; group
    rw [e]
    exact mem_sup_left (mem_inf.mp (mul_mem hyP hyP)).2)
  have hE₁ : IsElemTwo (zpowers a) := isElemTwo_zpowers haa
  have hca : ∀ e ∈ zpowers a, ∀ t : G, t * a = a * t → e * t = t * e := fun e he t ht => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
    exact Commute.zpow_left ht.symm n
  have ha'E₁ : a' ∉ zpowers a := fun h1 =>
    (GrS4.eq_one_or_eq_of_mem_zpowers haa h1).elim
      (fun h2 => ha1 (by
        calc a = h * a' * h⁻¹ := by rw [ha'def]; group
          _ = 1 := by rw [h2]; group))
      (fun h2 => ha'K (by rw [h2]; exact mem_sup_right haK))
  obtain ⟨hE₂, hE₂c⟩ := GrS4.isElemTwo_sup_zpowers hE₁ ha'2 ha'E₁ fun e he => hca e he a' ha'a
  have hz'E₂ : z' ∉ zpowers a ⊔ zpowers a' := by
    intro h1
    rcases GrS4.mem_or_mul_of_mem_sup_zpowers ha'2 (fun e he => hca e he a' ha'a) h1 with
      h2 | ⟨e, he, h2⟩
    · exact (GrS4.eq_one_or_eq_of_mem_zpowers haa h2).elim hz'1 hz'a1
    · rcases GrS4.eq_one_or_eq_of_mem_zpowers haa he with h3 | h3
      · rw [h3, one_mul] at h2
        exact ha'K (by rw [← h2]; exact hz'K)
      · rw [h3] at h2
        apply ha'K
        have := mul_mem (mem_sup_right (inv_mem haK) : a⁻¹ ∈ withKernel J) hz'K
        rwa [h2, ← mul_assoc, inv_mul_cancel, one_mul] at this
  have hcz : ∀ e ∈ zpowers a ⊔ zpowers a', e * z' = z' * e := by
    have hle : zpowers a ⊔ zpowers a' ≤ centralizer ({z'} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcent z' hz'S).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hz'a'.symm))
    exact fun e he => mem_centralizer_singleton_iff.mp (hle he)
  obtain ⟨hE₃, hE₃c⟩ := GrS4.isElemTwo_sup_zpowers hE₂ hz'2 hz'E₂ hcz
  set E' : Subgroup G := zpowers a ⊔ zpowers a' ⊔ zpowers z' with hE'def
  have hcardE' : Nat.card E' = 8 := by rw [hE₃c, hE₂c, Nat.card_zpowers, ha2]
  have hE' : IsEightGroup E' := ⟨hE₃, hcardE'⟩
  have hE'S : E' ≤ S := sup_le (sup_le (zpowers_le.mpr haS) (zpowers_le.mpr haS'))
    (zpowers_le.mpr hz'S)
  have ha'E' : a' ∈ E' := mem_sup_left (mem_sup_right (mem_zpowers a'))
  have hz'a2 : z' ∉ zpowers a := fun h1 => hz'E₂ (mem_sup_left h1)
  obtain ⟨-, hF₀c⟩ := GrS4.isElemTwo_sup_zpowers hE₁ hz'2 hz'a2 fun e he =>
    hca e he z' (hcent z' hz'S)
  have hF₀E : zpowers a ⊔ zpowers z' ≤ E' :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hF₀4 : Nat.card ↥(zpowers a ⊔ zpowers z') = 4 := by rw [hF₀c, Nat.card_zpowers, ha2]
  have hEC : 4 ≤ Nat.card ↥(E' ⊓ coreActionKernel J) := by
    have := Subgroup.card_le_of_le (le_inf hF₀E
      (sup_le (zpowers_le.mpr haK) (zpowers_le.mpr hz'C)))
    rwa [hF₀4] at this
  have h4 : Nat.card ↥(E' ⊓ withKernel J) = 4 := by
    have hge : 4 ≤ Nat.card ↥(E' ⊓ withKernel J) := by
      have := Subgroup.card_le_of_le (le_inf hF₀E
        (sup_le (zpowers_le.mpr (mem_sup_right haK)) (zpowers_le.mpr hz'K)))
      rwa [hF₀4] at this
    have hdvd : Nat.card ↥(E' ⊓ withKernel J) ∣ 8 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : E' ⊓ withKernel J ≤ E')
      rwa [hcardE'] at this
    have hne : Nat.card ↥(E' ⊓ withKernel J) ≠ 8 := fun h8 => ha'K (by
      have hEK : E' ⊓ withKernel J = E' :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hcardE'])
      have := ha'E'
      rw [← hEK] at this
      exact (mem_inf.mp this).2)
    obtain ⟨n, hn, hn'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card ↥(E' ⊓ withKernel J) ∣ 2 ^ 3 by norm_num; exact hdvd)
    interval_cases n <;> simp only [Nat.reducePow] at hn' <;> omega
  by_cases hiso : ∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ E', s * e = e * s) → s ∈ E'
  · exfalso
    obtain ⟨⟨h2, -⟩, -⟩ := l34WCriterionDFact_of_certs G J S hJper hL34 hP hS2 hS.1 E' hE'S hE'
      h4 (by omega) hiso
    omega
  push Not at hiso
  obtain ⟨s, hsS, hss, hsE, hsn⟩ := hiso
  exact exists_conj_of_conj hCM hbh (exists_conj_of_not_isolated hset hcent hWB hSyl (g := h)
    hE'S hE' (fun e he => hE₃.1 e he a' ha'E') (mem_inf.mp hsS).1 hss hsE hsn (hsE a' ha'E'))

end CFSG.ComponentClassification.GrSLit.GrS5S
