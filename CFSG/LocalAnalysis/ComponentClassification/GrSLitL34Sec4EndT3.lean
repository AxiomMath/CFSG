module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndT2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndT

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_sup_oddIn {T : Subgroup G}
    (hTsyl : IsSylowTwoIn T (centralizer (T : Set G))) :
    centralizer (T : Set G) ≤ T ⊔ oddIn (normalizer (T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := centralizer (T : Set G) with hX
  obtain ⟨-, P', hP'⟩ := hTsyl
  have hnc : normalizer (P' : Set ↥X) ≤ centralizer (P' : Set ↥X) := by
    intro x _
    rw [mem_centralizer_iff]
    intro p hp
    have hp' : (p : G) ∈ T := by
      have h : p ∈ (P' : Subgroup ↥X) := hp
      rw [hP', mem_subgroupOf] at h
      exact h
    exact Subtype.ext (mem_centralizer_iff.mp x.2 p hp')
  set τ := MonoidHom.transferSylow P' hnc with hτ
  have hKodd : ¬ 2 ∣ Nat.card τ.ker := MonoidHom.not_dvd_card_ker_transferSylow P' hnc
  have hsup : τ.ker ⊔ (P' : Subgroup ↥X) = ⊤ :=
    (MonoidHom.ker_transferSylow_isComplement' P' hnc).sup_eq_top
  have hodd : ∀ x : ↥X, ¬ 2 ∣ orderOf x → x ∈ τ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P'.isPGroup') (τ x)
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exfalso
      apply hx
      have h1 : orderOf (τ x) ∣ orderOf x := orderOf_map_dvd τ x
      rw [hk] at h1
      exact (dvd_pow_self 2 k.succ_ne_zero).trans h1
  set L : Subgroup G := normalizer (T : Set G) with hL
  have hXL : X ≤ L := fun x hx =>
    mem_normalizer_of_forall_commute fun t ht => (mem_centralizer_iff.mp hx t ht).symm
  set N : Subgroup G := τ.ker.map X.subtype with hN
  have hNL : N ≤ L := (map_subtype_le _).trans hXL
  have hNnorm : (N.subgroupOf L).Normal := ⟨fun n hn l => by
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := hn
    have hlX : (l : G) * k * (l : G)⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (mem_normalizer_centralizer l.2) k).mp k.2
    have hord : orderOf (⟨(l : G) * k * (l : G)⁻¹, hlX⟩ : ↥X) = orderOf k := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe k]
      exact orderOf_injective (MulAut.conj (l : G)).toMonoidHom (MulAut.conj (l : G)).injective _
    have hkodd : ¬ 2 ∣ orderOf k := by
      intro h
      apply hKodd
      have h1 : orderOf (⟨k, hk⟩ : ↥τ.ker) ∣ Nat.card τ.ker := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact h.trans h1
    refine ⟨⟨(l : G) * k * (l : G)⁻¹, hlX⟩, hodd _ (by rw [hord]; exact hkodd), ?_⟩
    have hkn' : (k : G) = n := hkn
    simp only [subtype_apply, coe_mul, coe_inv]
    rw [hkn']⟩
  have hNodd : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf L)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNL).toEquiv, hN,
      card_map_of_injective X.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hKodd
  have hle := CFSG.LocalAnalysis.ComponentInitial.le_pPrimeCore hNnorm hNodd
  intro x hx
  have hxtop : (⟨x, hx⟩ : ↥X) ∈ τ.ker ⊔ (P' : Subgroup ↥X) := by
    rw [hsup]
    exact mem_top _
  obtain ⟨k, hk, p, hp, hkp⟩ := mem_sup_of_normal_left.mp hxtop
  have hkO : (k : G) ∈ oddIn L := by
    refine ⟨⟨k, hNL ⟨k, hk, rfl⟩⟩, hle ?_, rfl⟩
    rw [mem_subgroupOf]
    exact ⟨k, hk, rfl⟩
  have hpT : (p : G) ∈ T := by
    rw [hP', mem_subgroupOf] at hp
    exact hp
  have hx' : x = (k : G) * p := by
    have h := congrArg Subtype.val hkp
    simpa using h.symm
  rw [hx']
  exact mul_mem (mem_sup_right hkO) (mem_sup_left hpT)

theorem fourCube_of_le_withKernel
    (hTr : L34EightTransvectionFact) {a : G} {J S B T : Subgroup G} (hJper : ⁅J, J⁆ = J)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (haZ : a ∈ S ⊓ zStarIn J) (ha1 : a ≠ 1)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J)) (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4)
    (hQc : IsCyclic ↥(S ⊓ coreActionKernel J)) (hBP : B ≤ S ⊓ J) (hB8 : IsEightGroup B)
    (hBZ : B ⊓ zStarIn J = zpowers a) (hSN : S ≤ normalizer (B : Set G))
    (hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
      n⁻¹ * (b : G) * n = (σ b : G))
    (hT : T = S ⊓ centralizer (B : Set G)) (hTW : T ≤ withKernel J) :
    Nonempty (↥T ≃* Multiplicative (Fin 3 → ZMod 4)) ∧
      centralizer (T : Set G) ≤ T ⊔ oddIn (normalizer (T : Set G)) ∧
      ∃ φ : ↥(normalizer (T : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (T ⊔ oddIn (normalizer (T : Set G))).subgroupOf (normalizer (T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hiso, hΩ, hTab, hexp⟩ := structure_of_le_withKernel hTr hJper hL34 hS hSyl haZ ha1
    hZc hZ4 hQc hBP hB8 hBZ hSN hAut hT hTW
  have hTsyl : IsSylowTwoIn T (centralizer (B : Set G)) := by
    rw [hT]
    exact isSylowTwoIn_inf_centralizer hSyl hSN
  have hT2 : IsPGroup 2 T := isPGroup_of_isSylowTwoIn hTsyl
  have hBT : B ≤ T := fun b hb => by
    rw [hT]
    exact mem_inf.mpr ⟨(mem_inf.mp (hBP hb)).1,
      mem_centralizer_iff.mpr fun c hc => hB8.1.1 c hc b hb⟩
  have hTC : T ≤ centralizer (T : Set G) := fun t ht =>
    mem_centralizer_iff.mpr fun u hu => hTab u hu t ht
  have hCTB : centralizer (T : Set G) ≤ centralizer (B : Set G) := centralizer_le hBT
  have hTsyl' : IsSylowTwoIn T (centralizer (T : Set G)) := isSylowTwoIn_of_le hTsyl hTC hCTB
  have hC := centralizer_le_sup_oddIn hTsyl'
  have hNTB : normalizer (T : Set G) ≤ normalizer (B : Set G) := fun n hn =>
    mem_normalizer_of_map_le_self (by
      rintro _ ⟨b, hb, rfl⟩
      have h1 : n * b * n⁻¹ ∈ T := (mem_normalizer_iff.mp hn b).mp (hBT hb)
      refine hΩ _ h1 ?_
      change n * b * n⁻¹ * (n * b * n⁻¹) = 1
      rw [show n * b * n⁻¹ * (n * b * n⁻¹) = n * (b * b) * n⁻¹ by group, hB8.1.2 b hb]
      group)
  have hcenB : ∀ n ∈ normalizer (T : Set G),
      n ∈ centralizer (B : Set G) ↔ n ∈ T ⊔ oddIn (normalizer (T : Set G)) := by
    intro n hn
    constructor
    · intro hnB
      have hsq : n * n ∈ centralizer (T : Set G) := by
        rw [mem_centralizer_iff]
        intro t ht
        have hnt : n⁻¹ * t * n ∈ T := by
          have h := (mem_normalizer_iff.mp (inv_mem hn) t).mp ht
          rwa [inv_inv] at h
        have ht2 : t * t ∈ B := hΩ _ (mul_mem ht ht) (hexp t ht)
        obtain ⟨u, hu_def⟩ : ∃ u, u = n⁻¹ * t * n := ⟨_, rfl⟩
        rw [← hu_def] at hnt
        have h1 : n⁻¹ * (t * t) * n = t * t := by
          rw [mul_assoc, mem_centralizer_iff.mp hnB _ ht2, ← mul_assoc, inv_mul_cancel, one_mul]
        have huu : u * u = t * t := by
          rw [hu_def, show n⁻¹ * t * n * (n⁻¹ * t * n) = n⁻¹ * (t * t) * n by group, h1]
        have hcomm : u * t⁻¹ = t⁻¹ * u := (hTab _ (inv_mem ht) _ hnt).symm
        have hc : t⁻¹ * u ∈ B := by
          refine hΩ _ (mul_mem (inv_mem ht) hnt) ?_
          calc t⁻¹ * u * (t⁻¹ * u) = t⁻¹ * (u * t⁻¹) * u := by group
            _ = t⁻¹ * (t⁻¹ * u) * u := by rw [hcomm]
            _ = t⁻¹ * t⁻¹ * (u * u) := by group
            _ = 1 := by rw [huu]; group
        have hnc : n⁻¹ * (t⁻¹ * u) * n = t⁻¹ * u := by
          rw [mul_assoc, mem_centralizer_iff.mp hnB _ hc, ← mul_assoc, inv_mul_cancel, one_mul]
        have h2 : (n * n)⁻¹ * t * (n * n) = t := by
          have e1 : n⁻¹ * t * n = t * (t⁻¹ * u) := by rw [← hu_def]; group
          calc (n * n)⁻¹ * t * (n * n) = n⁻¹ * (n⁻¹ * t * n) * n := by group
            _ = n⁻¹ * (t * (t⁻¹ * u)) * n := by rw [e1]
            _ = (n⁻¹ * t * n) * (n⁻¹ * (t⁻¹ * u) * n) := by group
            _ = t * (t⁻¹ * u) * (t⁻¹ * u) := by rw [hnc, e1]
            _ = t * ((t⁻¹ * u) * (t⁻¹ * u)) := by group
            _ = t := by rw [hB8.1.2 _ hc, mul_one]
        calc t * (n * n) = (n * n) * ((n * n)⁻¹ * t * (n * n)) := by group
          _ = (n * n) * t := by rw [h2]
      obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
      obtain ⟨j, rfl⟩ := hr
      have hy : n ^ (2 * j + 1) ∈ T := by
        set y := n ^ (2 * j + 1) with hydef
        have hyN : y ∈ normalizer (T : Set G) := pow_mem hn _
        have hyB : y ∈ centralizer (B : Set G) := pow_mem hnB _
        have h1 : y ^ (2 ^ k) = 1 := by
          rw [hydef, ← pow_mul, mul_comm, ← hkr, pow_orderOf_eq_one]
        obtain ⟨i, -, hik⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
          (orderOf_dvd_of_pow_eq_one h1)
        have hy2 : IsPGroup 2 (zpowers y) := IsPGroup.of_card (n := i) (by
          rw [Nat.card_zpowers, hik])
        have hsup2 := IsPGroup.to_sup_of_normal_right' hy2 hT2 (zpowers_le.mpr hyN)
        have heq := hTsyl.eq_of_le le_sup_right
          (sup_le (zpowers_le.mpr hyB) hTsyl.1) hsup2
        have hyT : y ∈ zpowers y ⊔ T := mem_sup_left (mem_zpowers y)
        rwa [heq] at hyT
      have e : n ^ (2 * j + 1) * ((n * n) ^ j)⁻¹ = n := by
        rw [← sq, ← pow_mul, pow_succ', mul_inv_cancel_right]
      rw [← e]
      exact mul_mem (mem_sup_left hy) (inv_mem (hC (pow_mem hsq j)))
    · intro hn'
      have hle : T ⊔ oddIn (normalizer (T : Set G)) ≤ centralizer (B : Set G) := by
        refine sup_le hTsyl.1 ?_
        intro o ho
        refine mem_centralizer_iff.mpr fun b hb => ?_
        have hoN : o ∈ normalizer (T : Set G) := map_subtype_le _ ho
        have hbN : b ∈ normalizer (T : Set G) := le_normalizer (hBT hb)
        have h1 : o * b * o⁻¹ * b⁻¹ ∈ T :=
          mul_mem ((mem_normalizer_iff.mp hoN b).mp (hBT hb)) (inv_mem (hBT hb))
        have h2 : o * b * o⁻¹ * b⁻¹ ∈ oddIn (normalizer (T : Set G)) := by
          have h3 := conj_mem_oddIn hbN (inv_mem ho)
          rw [show o * b * o⁻¹ * b⁻¹ = o * (b * o⁻¹ * b⁻¹) by group]
          exact mul_mem ho h3
        have hbot := eq_bot_of_le_two_group_of_le_odd hT2
          (GrSLit.odd_card_map_pPrimeCore (normalizer (T : Set G)))
          (inf_le_left : T ⊓ oddIn (normalizer (T : Set G)) ≤ T) inf_le_right
        have h4 : o * b * o⁻¹ * b⁻¹ ∈ T ⊓ oddIn (normalizer (T : Set G)) := mem_inf.mpr ⟨h1, h2⟩
        rw [hbot, mem_bot] at h4
        calc b * o = (o * b * o⁻¹ * b⁻¹)⁻¹ * (o * b) := by group
          _ = o * b := by rw [h4, inv_one, one_mul]
      exact hle hn'
  obtain ⟨eB⟩ := nonempty_mulAut_equiv_GL (E := ↥B) (fun u v => Subtype.ext (hB8.1.1 _ u.2 _ v.2))
    (fun u => Subtype.ext (hB8.1.2 _ u.2)) hB8.2
  let ι : ↥(normalizer (T : Set G)) →* ↥(normalizer (B : Set G)) := inclusion hNTB
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
  refine ⟨hiso, hC, φ, ?_, ?_⟩
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
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hcenB n n.2, ← hφ1 n]
    show eB (normalizerConjAct B (ι n)) = 1 ↔ _
    exact MulEquiv.map_eq_one_iff eB

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34EndTStep_of_inputs (hShape : L34EndTShapeStep)
    (hTr : L34EightTransvectionFact) : L34EndTStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut T hT
  rcases hShape G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN
    hBiff hAut T hT with hTW | hgraph
  · left
    obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
    have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
    have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
    have hZne : S ⊓ zStarIn J ≠ ⊥ := by
      intro hbot
      rw [hbot, card_bot] at hZ4
      norm_num at hZ4
    have ha2 : orderOf a = 2 := hU3.1
    have ha1 : a ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ha2
      exact absurd ha2 (by norm_num)
    exact GrS4.fourCube_of_le_withKernel hTr hJper hL34 hS hSyl (hZ hZne) ha1 hZc hZ4 hQc hBP
      hB8 hBZ hSN hAut hT hTW
  · exact Or.inr hgraph

end CFSG.ComponentClassification.GrSLit
