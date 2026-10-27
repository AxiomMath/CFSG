module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndG
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndG

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem exists_surj_GL {B T : Subgroup G} (hB8 : IsEightGroup B)
    (hTsyl : IsSylowTwoIn T (centralizer (B : Set G)))
    (hNB : normalizer (T : Set G) ≤ normalizer (B : Set G))
    (hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
      n⁻¹ * (b : G) * n = (σ b : G)) :
    ∃ φ : ↥(normalizer (T : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
      φ.ker = (centralizer (B : Set G)).subgroupOf (normalizer (T : Set G)) := by
  obtain ⟨eB⟩ := nonempty_mulAut_equiv_GL (E := ↥B) (fun u v => Subtype.ext (hB8.1.1 _ u.2 _ v.2))
    (fun u => Subtype.ext (hB8.1.2 _ u.2)) hB8.2
  let ι : ↥(normalizer (T : Set G)) →* ↥(normalizer (B : Set G)) := inclusion hNB
  let φ : ↥(normalizer (T : Set G)) →* GL (Fin 3) (ZMod 2) :=
    eB.toMonoidHom.comp ((normalizerConjAct B).comp ι)
  have hφ1 : ∀ n : ↥(normalizer (T : Set G)),
      normalizerConjAct B (ι n) = 1 ↔ (n : G) ∈ centralizer (B : Set G) := by
    intro n
    constructor
    · intro h
      refine mem_centralizer_iff.mpr fun b hb => ?_
      have h1 := congrArg (fun σ : MulAut ↥B => ((σ ⟨b, hb⟩ : ↥B) : G)) h
      simp only [normalizerConjAct_apply, MulAut.one_apply] at h1
      have h1' : (n : G) * b * (n : G)⁻¹ = b := h1
      calc b * n = (n * b * (n : G)⁻¹) * n := by rw [h1']
        _ = n * b := by group
    · intro h
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [normalizerConjAct_apply, MulAut.one_apply]
      have h1 : (b : G) * n = n * b := mem_centralizer_iff.mp h b b.2
      calc (ι n : G) * b * (ι n : G)⁻¹ = n * b * (n : G)⁻¹ := rfl
        _ = b := by rw [← h1]; group
  refine ⟨φ, ?_, ?_⟩
  · intro M
    obtain ⟨n, hnN, hn⟩ := hAut (eB.symm M)
    obtain ⟨c, hcC, hnc⟩ := exists_mul_mem_normalizer hTsyl (inv_mem hnN)
    refine ⟨⟨n⁻¹ * c, hnc⟩, ?_⟩
    have h1 : normalizerConjAct B (ι ⟨n⁻¹ * c, hnc⟩) = eB.symm M := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [normalizerConjAct_apply, ← hn b]
      have hcb : c * b = b * c := (mem_centralizer_iff.mp hcC b b.2).symm
      calc (ι ⟨n⁻¹ * c, hnc⟩ : G) * b * (ι ⟨n⁻¹ * c, hnc⟩ : G)⁻¹
          = n⁻¹ * (c * b) * c⁻¹ * n := by
            show n⁻¹ * c * b * (n⁻¹ * c)⁻¹ = _
            group
        _ = n⁻¹ * b * n := by rw [hcb]; group
    show eB (normalizerConjAct B (ι ⟨n⁻¹ * c, hnc⟩)) = M
    rw [h1, MulEquiv.apply_symm_apply]
  · ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hφ1 n]
    show eB (normalizerConjAct B (ι n)) = 1 ↔ _
    exact MulEquiv.map_eq_one_iff eB

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34EndGraphStep_of_inputs (hInv : L34GraphInvertStep)
    (hFin : L34GraphFinalStep) (hTr : L34EightTransvectionFact) : L34EndGraphStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut c hcS hcc hcW hTc
  obtain ⟨hab, hinvc⟩ := hInv G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP
    hB8 hBZ hSN hBiff hAut c hcS hcc hcW hTc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hZ4
    norm_num at hZ4
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  have ha2 : orderOf a = 2 := hU3.1
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hZJle : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_eq_right.mpr hZJle]
  have haB : a ∈ B := (le_of_eq hBZ.symm).trans inf_le_left (mem_zpowers a)
  have hSO : ∀ y ∈ S, y ∈ oddIn J → y = 1 := by
    intro y hyS hyO
    have hbot := eq_bot_of_le_two_group_of_le_odd hS2 (GrSLit.odd_card_map_pPrimeCore J)
      (inf_le_left : S ⊓ oddIn J ≤ S) inf_le_right
    have hy : y ∈ S ⊓ oddIn J := mem_inf.mpr ⟨hyS, hyO⟩
    rw [hbot] at hy
    exact hy
  have hZB : ∀ z ∈ S ⊓ zStarIn J, z ∈ centralizer (B : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro b hb
    have hzK : z ∈ coreActionKernel J := by
      have h := (mem_inf.mp hz).2
      rw [hZJ] at h
      exact (mem_inf.mp h).2
    have hbS := (mem_inf.mp (hBP hb)).1
    have h1 := (mem_coreActionKernel.mp hzK).2 b (mem_inf.mp (hBP hb)).2
    have h2 : b⁻¹ * z⁻¹ * b * z = 1 := hSO _ (mul_mem (mul_mem (mul_mem (inv_mem hbS)
      (inv_mem (mem_inf.mp hz).1)) hbS) (mem_inf.mp hz).1) h1
    calc b * z = z * (b * (b⁻¹ * z⁻¹ * b * z)) := by group
      _ = z * b := by rw [h2, mul_one]
  set S₀ : Subgroup G := S ⊓ J ⊓ centralizer (B : Set G) with hS₀
  have hZS₀ : S ⊓ zStarIn J ≤ S₀ := fun z hz =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hz).1, hZJle (mem_inf.mp hz).2⟩, hZB z hz⟩
  obtain ⟨z, hzZ, hzz⟩ : ∃ z ∈ S ⊓ zStarIn J, z * z ≠ 1 := by
    have : IsCyclic ↥(S ⊓ zStarIn J) := hZc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(S ⊓ zStarIn J))
    have hog : orderOf g = 4 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hZ4
    refine ⟨g, g.2, fun h => ?_⟩
    have h1 : g ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact h)
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hog]; norm_num) h1
  have hsz : ∀ s ∈ S₀, s * s = 1 → (s * z) * (s * z) ≠ 1 := by
    intro s hs hss h
    apply hzz
    have hcomm := hab s hs z (hZS₀ hzZ)
    calc z * z = s * s * (z * z) := by rw [hss, one_mul]
      _ = s * (s * z) * z := by group
      _ = s * (z * s) * z := by rw [hcomm]
      _ = (s * z) * (s * z) := by group
      _ = 1 := h
  have hNS₀ := GrS4.normalizer_le_of_inverts hTc hcc hinvc (hZS₀ hzZ) hzz hsz
  have hTsyl : IsSylowTwoIn (S ⊓ centralizer (B : Set G)) (centralizer (B : Set G)) :=
    GrS4.isSylowTwoIn_inf_centralizer hSyl hSN
  obtain ⟨b₂, hb₂B, hb₂1, hb₂a, -, -⟩ := GrS4.exists_mem_not_mem_four hB8.2 1 a 1 1
  obtain ⟨b₃, hb₃B, hb₃1, hb₃a, hb₃b, hb₃ab⟩ :=
    GrS4.exists_mem_not_mem_four hB8.2 1 a b₂ (a * b₂)
  obtain ⟨g₂, hg₂N, hg₂⟩ := GrS4.exists_mem_normalizer_conj_eq hB8.1 hTsyl hAut haB hb₂B ha1 hb₂1
  obtain ⟨g₃, hg₃N, hg₃⟩ := GrS4.exists_mem_normalizer_conj_eq hB8.1 hTsyl hAut haB hb₃B ha1 hb₃1
  have hS₀64 : Nat.card S₀ ≤ 64 := GrS4.card_inf_centralizer_le hTr hJper hL34 hP
    (by rwa [hZP]) (by rwa [hZP]) hBP hB8 hBZ ha1
  obtain ⟨hiso, hΩ⟩ := GrS4.fourCube_of_conj hab hS₀64 hB8.1 haB hb₂B hb₃B ha1 hb₂1 hb₂a hb₃1
    hb₃a hb₃b hb₃ab hZc hZ4 hZS₀ haZ (hNS₀ hg₂N) (hNS₀ hg₃N) hg₂ hg₃
  have hBS₀ : B ≤ S₀ := fun b hb => mem_inf.mpr ⟨hBP hb,
    mem_centralizer_iff.mpr fun d hd => hB8.1.1 d hd b hb⟩
  have hNB : normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G) ≤
      normalizer (B : Set G) := fun n hn =>
    GrS4.mem_normalizer_of_map_le_self (by
      rintro _ ⟨b, hb, rfl⟩
      have h1 : n * b * n⁻¹ ∈ S₀ := (mem_normalizer_iff.mp (hNS₀ hn) b).mp (hBS₀ hb)
      refine hΩ _ h1 ?_
      change n * b * n⁻¹ * (n * b * n⁻¹) = 1
      rw [show n * b * n⁻¹ * (n * b * n⁻¹) = n * (b * b) * n⁻¹ by group, hB8.1.2 b hb]
      group)
  exact hFin G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut c hcS hcc hcW hTc hiso hΩ hinvc hNS₀ hNB (GrS4.exists_surj_GL hB8 hTsyl hNB hAut)

end CFSG.ComponentClassification.GrSLit
