module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Struct

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

section Main33

variable {n : ℕ} {z : X} {Z : Subgroup X} {s : X}

theorem IsSec5Pair.mem_centralizer_of_comm (hp : IsSec5Pair X n z Z)
    (hsN : s ∈ normalizer (Z : Set X))
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) :
    s ∈ centralizer (Z : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro ζ hζ
  have h1 : ⁅ζ, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X))) :=
    hs ζ (hp.le_K0_normalizer hζ)
  have h2 : ⁅ζ, s⁆ ∈ Z := by
    have : ⁅ζ, s⁆ = ζ * (s * ζ⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact Z.mul_mem hζ ((Subgroup.mem_normalizer_iff.1 hsN ζ⁻¹).1 (Z.inv_mem hζ))
  have h3 := eq_one_of_mem_pPrimeCoreOf_of_isPGroup h1 hp.isPGroup h2
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

theorem IsSec5Pair.comm_mem_K0_centralizer (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) (hsN : s ∈ normalizer (Z : Set X))
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) :
    ∀ k ∈ K0 X n (centralizer ({z} : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) := by
  have hsC : s ∈ centralizer ({z} : Set X) := by
    have := (Subgroup.mem_centralizer_iff.1 (hp.mem_centralizer_of_comm hsN hs)) z hp.mem
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  set Kz := K0 X n (centralizer ({z} : Set X)) with hKz
  set F := K0 X n (normalizer (Z : Set X)) with hF
  have hFK : F ≤ Kz := hp.K0_normalizer_le hA hn
  have hFO : F ≤ normalizer (pPrimeCoreOf 2 Kz : Set X) := fun x hx =>
    mem_normalizer_pPrimeCoreOf_of_mem (hFK hx)
  have hKsup : Kz ≤ pPrimeCoreOf 2 Kz ⊔ F := hp.K0_centralizer_le_sup
  have hcov : F ⊔ pPrimeCoreOf 2 Kz = Kz :=
    le_antisymm (sup_le hFK (oddCoreOf_le Kz)) (by rw [sup_comm]; exact hKsup)
  have hOF : pPrimeCoreOf 2 F ≤ pPrimeCoreOf 2 Kz :=
    (pPrimeCoreOf_eq_inf_of_covers hFK hcov).le.trans inf_le_right
  have hsKz : s ∈ normalizer (Kz : Set X) :=
    mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hsC))
  have hsO : s ∈ normalizer (pPrimeCoreOf 2 Kz : Set X) :=
    normalizer_le_normalizer_pPrimeCoreOf Kz hsKz
  intro k hk
  have hk' : k ∈ ((pPrimeCoreOf 2 Kz ⊔ F : Subgroup X) : Set X) := hKsup hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ F hFO] at hk'
  obtain ⟨o, ho, f, hf, rfl⟩ := hk'
  have h1 : ⁅o * f, s⁆ = o * ⁅f, s⁆ * o⁻¹ * ⁅o, s⁆ := by simp only [commutatorElement_def]; group
  have h2 : ⁅f, s⁆ ∈ pPrimeCoreOf 2 Kz := hOF (hs f hf)
  have h3 : ⁅o, s⁆ ∈ pPrimeCoreOf 2 Kz := by
    have : ⁅o, s⁆ = o * (s * o⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (pPrimeCoreOf 2 Kz).mul_mem ho
      ((Subgroup.mem_normalizer_iff.1 hsO o⁻¹).1 ((pPrimeCoreOf 2 Kz).inv_mem ho))
  rw [h1]
  exact (pPrimeCoreOf 2 Kz).mul_mem
    ((Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ho) _).1 h2) h3

theorem IsSec5Pair.descent_centralizer (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) {L : Subgroup X} {u : X}
    (hu : IsIntrinsicIn X (centralizer ({z} : Set X)) L u) (huZ : u ∈ Z)
    (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    IsIntrinsicIn X (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X))
        (oTwoPrimeOf (L ⊓ centralizer ({s} : Set X))) u ∧
      IsDoubleCoverOfAlt
        (↥(oTwoPrimeOf (L ⊓ centralizer ({s} : Set X))) ⧸
          pPrimeCore 2 ↥(oTwoPrimeOf (L ⊓ centralizer ({s} : Set X)))) n ∧
      L ≤ pPrimeCoreOf 2 L ⊔ oTwoPrimeOf (L ⊓ centralizer ({s} : Set X)) := by
  have hs0 : s ∈ centralizer (Z : Set X) := hp.mem_centralizer_of_comm hsN hs
  have hsC : s ∈ centralizer ({z} : Set X) := by
    have := (Subgroup.mem_centralizer_iff.1 hs0) z hp.mem
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  have hs1 := hp.comm_mem_K0_centralizer hA hn hsN hs
  have hs_sq : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hLK : L ≤ K0 X n (centralizer ({z} : Set X)) := le_sSup ⟨⟨u, hu⟩, hLn⟩
  have hsc : s ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
    normalizes_isPCompIn_of_comm_mem hu.2.2.1 (Subgroup.le_normalizer hsC)
      (fun l hl => pPrimeCoreOf_K0_le n _ (hs1 l (hLK hl)))
  have hus : u ∈ centralizer ({s} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hs0) u huZ)
  exact hu.descend_singleton hLn hs_sq hsc hus

theorem IsSec5Pair.K0_centralizer_le_sup_inf (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) :
    K0 X n (centralizer ({z} : Set X)) ≤
      pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) ⊔
        K0 X n (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)) := by
  refine sSup_le fun L hL => ?_
  obtain ⟨⟨u₀, hu₀⟩, hLn⟩ := hL
  obtain ⟨u, huZ, hu⟩ := hp.exists_witness_mem hu₀ hLn
  obtain ⟨h1, h2, h3⟩ := hp.descent_centralizer hA hn hsN hs2 hs hu huZ hLn
  have hLK : L ≤ K0 X n (centralizer ({z} : Set X)) := le_sSup ⟨⟨u₀, hu₀⟩, hLn⟩
  have hLO : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) :=
    pPrimeCoreOf_le_oddCoreOf hLK (isPComponent_two_iff.1 (hu₀.isPCompIn_K0 hLn).2).1
  exact h3.trans (sup_le_sup hLO (le_sSup ⟨⟨u, h1⟩, h2⟩))

theorem IsSec5Pair.witnessSet_subset_zStar (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) :
    witnessSet X n z Z ⊆ zStar (K0 X n (centralizer ({s} : Set X))) := by
  rintro u ⟨huZ, L, hu, hLn⟩
  obtain ⟨h1, h2, -⟩ := hp.descent_centralizer hA hn hsN hs2 hs hu huZ hLn
  obtain ⟨M, hM, hMn, -⟩ := exists_isIntrinsicIn_centralizer hA hn hs2
    (inf_le_right : centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X) ≤ _) h1 h2
  exact hM.mem_zStar_K0 hMn

theorem IsSec5Pair.le_zStar_K0_centralizer (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) :
    Z ≤ zStar (K0 X n (centralizer ({s} : Set X))) :=
  hp.le_closure_witnessSet.trans
    ((Subgroup.closure_le _).2 (hp.witnessSet_subset_zStar hA hn hsN hs2 hs))

theorem IsSec5Pair.K0_centralizer_s_le_sup_inf (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) :
    K0 X n (centralizer ({s} : Set X)) ≤
      pPrimeCoreOf 2 (K0 X n (centralizer ({s} : Set X))) ⊔
        K0 X n (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)) := by
  have hs0 : s ∈ centralizer (Z : Set X) := hp.mem_centralizer_of_comm hsN hs
  have hzK : z ∈ zStar (K0 X n (centralizer ({s} : Set X))) :=
    hp.le_zStar_K0_centralizer hA hn hsN hs2 hs hp.mem
  have hzC : z ∈ centralizer ({s} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hs0) z hp.mem)
  have hz_sq : z ^ 2 = 1 := by rw [← hp.orderOf_z]; exact pow_orderOf_eq_one z
  refine sSup_le fun M hM => ?_
  obtain ⟨⟨u₀, hu₀⟩, hMn⟩ := hM
  have hMK : M ≤ K0 X n (centralizer ({s} : Set X)) := le_sSup ⟨⟨u₀, hu₀⟩, hMn⟩
  have hzc : z ∈ centralizerSection M (pPrimeCoreOf 2 M) :=
    normalizes_isPCompIn_of_comm_mem hu₀.2.2.1 (Subgroup.le_normalizer hzC)
      (fun m hm => pPrimeCoreOf_K0_le n _ (hzK.2.2.2 m (hMK hm)))
  obtain ⟨u, hu, huz⟩ := hu₀.exists_witness_centralizer_singleton hz_sq hzc
  obtain ⟨h1, h2, h3⟩ := hu.descend_singleton hMn hz_sq hzc huz
  have hMO : pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 (K0 X n (centralizer ({s} : Set X))) :=
    pPrimeCoreOf_le_oddCoreOf hMK (isPComponent_two_iff.1 (hu₀.isPCompIn_K0 hMn).2).1
  have hE : oTwoPrimeOf (M ⊓ centralizer ({z} : Set X)) ≤
      K0 X n (centralizer ({s} : Set X) ⊓ centralizer ({z} : Set X)) :=
    le_sSup ⟨⟨u, h1⟩, h2⟩
  rw [inf_comm (centralizer ({z} : Set X))]
  exact h3.trans (sup_le_sup hMO hE)

theorem IsSec5Pair.isSylowTwoIn_zStar_K0_centralizer (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hs : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X)))) :
    IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Z := by
  by_cases hsz : s = z
  · subst hsz
    exact hp.sylow
  have hs0 : s ∈ centralizer (Z : Set X) := hp.mem_centralizer_of_comm hsN hs
  have hzs : z * s = s * z := (Subgroup.mem_centralizer_iff.1 hs0) z hp.mem
  have h51c := lemma51c_of_hypA hA hn z s hp.orderOf_z hs2 hzs (Ne.symm hsz)
  have hF1z : K0 X n (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)) ≤
      K0 X n (centralizer ({z} : Set X)) := h51c.trans inf_le_left
  have hF1s : K0 X n (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)) ≤
      K0 X n (centralizer ({s} : Set X)) := h51c.trans inf_le_right
  have hcovz : K0 X n (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)) ⊔
      pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) = K0 X n (centralizer ({z} : Set X)) :=
    le_antisymm (sup_le hF1z (oddCoreOf_le _))
      (by rw [sup_comm]; exact hp.K0_centralizer_le_sup_inf hA hn hsN hs2 hs)
  have hcovs : K0 X n (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)) ⊔
      pPrimeCoreOf 2 (K0 X n (centralizer ({s} : Set X))) = K0 X n (centralizer ({s} : Set X)) :=
    le_antisymm (sup_le hF1s (oddCoreOf_le _))
      (by rw [sup_comm]; exact hp.K0_centralizer_s_le_sup_inf hA hn hsN hs2 hs)
  have hcardZ := card_eq_relIndex_of_isSylowTwoIn hp.sylow
  have e1 := relIndex_zStar_eq_of_covers hF1z hcovz
  have e2 := relIndex_zStar_eq_of_covers hF1s hcovs
  exact isSylowTwoIn_zStar_of_card_eq (hp.le_zStar_K0_centralizer hA hn hsN hs2 hs) hp.isPGroup
    (by rw [hcardZ, e1, ← e2])

theorem lemma33a_of_isSec5Pair (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) : Lemma33a X n Z :=
  lemma33a_of_isSylowTwoIn fun _ hsN hs2 hs =>
    hp.isSylowTwoIn_zStar_K0_centralizer hA hn hsN hs2 hs

theorem IsSec5Pair.isPCompIn_K0_E (hp : IsSec5Pair X n z Z) {L : Subgroup X} {u₀ : X}
    (hu₀ : IsIntrinsicIn X (centralizer ({z} : Set X)) L u₀)
    (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    IsPCompIn 2 (K0 X n (normalizer (Z : Set X)))
      (oTwoPrimeOf (L ⊓ centralizer (Z : Set X))) := by
  obtain ⟨u, huZ, hu⟩ := hp.exists_witness_mem hu₀ hLn
  obtain ⟨h1, h2, -⟩ := hp.isIntrinsicIn_normalizer huZ hu hLn
  have hle : oTwoPrimeOf (L ⊓ centralizer (Z : Set X)) ≤ K0 X n (normalizer (Z : Set X)) :=
    le_sSup ⟨⟨u, h1⟩, h2⟩
  exact ⟨hle, isPComponent_subgroupOf_mono hle (K0_le n _) h1.2.2.1.2⟩

theorem IsSec5Pair.pTwoCoreOf_K0_le (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) : pTwoCoreOf (K0 X n (normalizer (Z : Set X))) ≤ Z := by
  have hFK : K0 X n (normalizer (Z : Set X)) ≤ K0 X n (centralizer ({z} : Set X)) :=
    hp.K0_normalizer_le hA hn
  have hPF : pTwoCoreOf (K0 X n (normalizer (Z : Set X))) ≤ K0 X n (normalizer (Z : Set X)) :=
    pTwoCoreOf_le _
  have hP2 : IsPGroup 2 ↥(pTwoCoreOf (K0 X n (normalizer (Z : Set X)))) := isPGroup_pTwoCoreOf _
  have hPn : K0 X n (normalizer (Z : Set X)) ≤
      normalizer (pTwoCoreOf (K0 X n (normalizer (Z : Set X))) : Set X) :=
    le_normalizer_pTwoCoreOf _
  have hEC : ∀ E ∈ EinfSet X n z Z,
      E ≤ centralizer (pTwoCoreOf (K0 X n (normalizer (Z : Set X))) : Set X) := by
    rintro E ⟨L, ⟨⟨u₀, hu₀⟩, hLn⟩, rfl⟩
    exact le_centralizer_of_isPCompIn_of_normal_pgroup (hp.isPCompIn_K0_E hu₀ hLn) hPF hPn hP2
  have hEinfC : sSup (EinfSet X n z Z) ≤
      centralizer (pTwoCoreOf (K0 X n (normalizer (Z : Set X))) : Set X) := sSup_le hEC
  have hEinfKz : sSup (EinfSet X n z Z) ≤ K0 X n (centralizer ({z} : Set X)) :=
    hp.sSup_E_le_K0.trans hFK
  have hPz : pTwoCoreOf (K0 X n (normalizer (Z : Set X))) ≤
      zStar (K0 X n (centralizer ({z} : Set X))) := fun p hpP =>
    mem_zStar_of_comm_cover (hFK (hPF hpP)) hEinfKz hp.K0_centralizer_le_sup_E (fun e he => by
      have hc : e * p = p * e := ((Subgroup.mem_centralizer_iff.1 (hEinfC he)) p hpP).symm
      rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
      exact (pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X)))).one_mem)
  have hPOZ : pTwoCoreOf (K0 X n (normalizer (Z : Set X))) ≤
      pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) ⊔ Z :=
    hPz.trans (zStar_le_pPrimeCoreOf_sup hp.sylow)
  have hZF : Z ≤ K0 X n (normalizer (Z : Set X)) := hp.le_K0_normalizer
  have hZP : Z ≤ pTwoCoreOf (K0 X n (normalizer (Z : Set X))) :=
    le_pTwoCoreOf hZF hp.isPGroup (K0_le n _)
  have hZK : Z ≤ K0 X n (centralizer ({z} : Set X)) := hZF.trans hFK
  exact le_of_le_sup_of_isPGroup hZP hP2 (odd_card_oddCoreOf _)
    (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hZK hx)) hPOZ

theorem IsSec5Pair.oddTwoCoreOf_le_sup (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) :
    oddTwoCoreOf (K0 X n (normalizer (Z : Set X))) ≤
      pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) ⊔ Z := by
  set Kz := K0 X n (centralizer ({z} : Set X)) with hKz
  set F := K0 X n (normalizer (Z : Set X)) with hF
  have hFK : F ≤ Kz := hp.K0_normalizer_le hA hn
  have hcov : F ⊔ pPrimeCoreOf 2 Kz = Kz :=
    le_antisymm (sup_le hFK (oddCoreOf_le Kz))
      (by rw [sup_comm]; exact hp.K0_centralizer_le_sup)
  have hOF : pPrimeCoreOf 2 F ≤ pPrimeCoreOf 2 Kz :=
    (pPrimeCoreOf_eq_inf_of_covers hFK hcov).le.trans inf_le_right
  have hEinfKz : sSup (EinfSet X n z Z) ≤ Kz := hp.sSup_E_le_K0.trans hFK
  have hWz : oddTwoCoreOf F ≤ zStar Kz := by
    intro w hw
    have hwF : w ∈ F := oddTwoCoreOf_le F hw
    have hwK : w ∈ Kz := hFK hwF
    have hwO : w ∈ normalizer (pPrimeCoreOf 2 Kz : Set X) :=
      mem_normalizer_pPrimeCoreOf_of_mem hwK
    have hS : ∀ A ∈ EinfSet X n z Z, A ≤ normalizer (pPrimeCoreOf 2 Kz : Set X) := by
      intro A hA x hx
      exact mem_normalizer_pPrimeCoreOf_of_mem (hEinfKz (le_sSup hA hx))
    have hcomm : ∀ A ∈ EinfSet X n z Z, ∀ a ∈ A, ⁅a, w⁆ ∈ pPrimeCoreOf 2 Kz := by
      rintro A ⟨L, ⟨⟨u₀, hu₀⟩, hLn⟩, rfl⟩ a ha
      have hEF := hp.isPCompIn_K0_E hu₀ hLn
      have h1 := comm_mem_of_isPCompIn_oddTwoCoreOf hEF a ha w hw
      exact hOF (pPrimeCoreOf_le_oddCoreOf hEF.1 (isPComponent_two_iff.1 hEF.2).1 h1)
    exact mem_zStar_of_comm_cover hwK hEinfKz hp.K0_centralizer_le_sup_E
      (forall_comm_mem_of_sSup hwO hS hcomm)
  exact hWz.trans (zStar_le_pPrimeCoreOf_sup hp.sylow)

theorem lemma33b_of_isSec5Pair (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) : Lemma33b X n Z := by
  have hZF : Z ≤ K0 X n (normalizer (Z : Set X)) := hp.le_K0_normalizer
  have hZP : Z ≤ pTwoCoreOf (K0 X n (normalizer (Z : Set X))) :=
    le_pTwoCoreOf hZF hp.isPGroup (K0_le n _)
  have hZK : Z ≤ K0 X n (centralizer ({z} : Set X)) := hp.sylow.1.trans inf_le_left
  refine ⟨le_antisymm hZP (hp.pTwoCoreOf_K0_le hA hn), ?_⟩
  exact isSylowTwoIn_of_le_sup_odd (hZP.trans (pTwoCoreOf_le_oddTwoCoreOf _)) hp.isPGroup
    (odd_card_oddCoreOf _) (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hZK hx))
    (hp.oddTwoCoreOf_le_sup hA hn)

end Main33

end CFSG.OddStandard.Solomon75
