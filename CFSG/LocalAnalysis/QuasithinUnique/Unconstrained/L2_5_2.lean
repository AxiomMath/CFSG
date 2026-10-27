module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def IsNonAltListedType {G : Type} [Group G] (L : Subgroup G) : Prop :=
  fusionIsBenderGroup ↥L ∨ (∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel ↥L .PSL 3 2 n) ∨
    (∃ n : ℕ, 2 ≤ n ∧ StatedClassicalModel ↥L .PSp 2 2 n) ∨
    StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 2 ∨
    StatedClassicalModel ↥L .PSL 3 3 1 ∨
    Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
    (∃ p : ℕ, IsFermatOrMersenne p ∧ StatedClassicalModel ↥L .PSL 2 p 1)

@[expose] def BenderBorelFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), CFSG.IsQuasisimple ↥L →
    fusionIsBenderGroup ↥L → IsSylowTwoOf P L →
    CharTwo (L ⊓ Subgroup.normalizer (P : Set G)) ∧
      ∀ X : Subgroup G, L ⊓ Subgroup.normalizer (P : Set G) ≤ X → X ≤ L →
        X = L ⊓ Subgroup.normalizer (P : Set G) ∨ X = L

@[expose] def RankTwoBorelFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), CFSG.IsQuasisimple ↥L →
    IsRankTwoEvenType L → IsSylowTwoOf P L →
    CharTwo (L ⊓ Subgroup.normalizer (P : Set G)) ∧
      ∃ P₁ P₂ : Subgroup G,
        L ⊓ Subgroup.normalizer (P : Set G) < P₁ ∧ P₁ < L ∧
        L ⊓ Subgroup.normalizer (P : Set G) < P₂ ∧ P₂ < L ∧ P₁ ≠ P₂ ∧ P₁ ⊔ P₂ = L ∧
        (∀ X : Subgroup G, L ⊓ Subgroup.normalizer (P : Set G) < X → X < L → X = P₁ ∨ X = P₂) ∧
        CharTwo P₁ ∧ CharTwo P₂

@[expose] def A6InnerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ ML : Subgroup G) (z : G),
    (Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨ IsThreeFoldCoverAlt L 6) →
    IsPGroup 2 S₀ → S₀ ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S₀ ⊓ L) L →
    z ∈ Subgroup.normalizer (L : Set G) → S₀ ≤ Subgroup.centralizer ({z} : Set G) →
    ML ≤ L → ML ≠ L →
    (∀ K : Subgroup G, K ≤ L → S₀ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ ML) →
    Ch1.InducesInner z L

@[expose] def A7Excluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ ML : Subgroup G),
    (Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ IsThreeFoldCoverAlt L 7) →
    IsPartitionStabilizerImage L ML → ML ≤ L →
    IsPGroup 2 S₀ → S₀ ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S₀ ⊓ L) L →
    S₀ ≤ Subgroup.normalizer (ML : Set G) →
    (∀ K : Subgroup G, K ≤ L → S₀ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ ML) → False

@[expose] def M22M23Excluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ ML : Subgroup G),
    ((Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧ IsAltOverElemAbelian ML 4 6) ∨
      (Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) ∧
        IsAltOverElemAbelian ML 4 7)) →
    ML ≤ L → IsPGroup 2 S₀ → S₀ ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S₀ ⊓ L) L →
    S₀ ≤ Subgroup.normalizer (ML : Set G) →
    (∀ K : Subgroup G, K ≤ L → S₀ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ ML) → False

@[expose] def L42Excluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ ML : Subgroup G) (z zL : G),
    StatedClassicalModel ↥L .PSL 4 2 1 → (∃ s ∈ S₀, InducesOuter s L) →
    IsProjectionOn z zL L → ML = L ⊓ Subgroup.centralizer ({zL} : Set G) → ML ≠ L →
    IsPGroup 2 S₀ → S₀ ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S₀ ⊓ L) L →
    S₀ ≤ Subgroup.normalizer (ML : Set G) → S₀ ≤ Subgroup.centralizer ({z} : Set G) →
    (∀ K : Subgroup G, K ≤ L → S₀ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ ML) → False

@[expose] def SmallL2Facts : Prop :=
  (∀ (X : Type) [Group X], StatedClassicalModel X .PSL 2 5 1 → fusionIsBenderGroup X) ∧
    (∀ (X : Type) [Group X], StatedClassicalModel X .PSL 2 7 1 → StatedClassicalModel X .PSL 3 2 1)

@[expose] def NotAltQuotientFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.IsQuasisimple ↥L →
    IsNonAltListedType L → ¬ CentralQuotientAlt L 6 ∧ ¬ CentralQuotientAlt L 7

namespace Unc25G2

section Lattice

variable {G : Type*} [Group G]

theorem mem_normalizer_of_lattice {B L X Y Z : Subgroup G} {g : G}
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (hZX : Z = X)
    (hlat : ∀ W : Subgroup G, B < W → W < L → W = X ∨ W = Y) (hXY : X ≠ Y)
    (hBY : B < Y) (hYL : Y < L) : g ∈ Subgroup.normalizer (Y : Set G) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hB' := map_conj_eq_of_mem_normalizer' hgB
  have hL' := map_conj_eq_of_mem_normalizer' hgL
  have hZ' := map_conj_eq_of_mem_normalizer' hgZ
  have h1 : B < Y.map (MulAut.conj g).toMonoidHom := by
    have := (Subgroup.map_lt_map_iff_of_injective hinj).mpr hBY
    rwa [hB'] at this
  have h2 : Y.map (MulAut.conj g).toMonoidHom < L := by
    have := (Subgroup.map_lt_map_iff_of_injective hinj).mpr hYL
    rwa [hL'] at this
  apply mem_normalizer_of_map_conj_eq
  rcases hlat _ h1 h2 with h | h
  · exfalso
    apply hXY
    have hZ'' : X.map (MulAut.conj g).toMonoidHom = X := by
      rw [← hZX]
      exact hZ'
    exact (Subgroup.map_injective hinj (h.trans hZ''.symm)).symm
  · exact h

end Lattice

end Unc25G2

section Proof

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem Tuple25.sylow_inf_component (ht : Tuple25 T M H S z) {L : Subgroup G}
    (hL : IsComponentIn L H) : IsSylowTwoOf (S ⊓ L) L :=
  RankOneRecog.isSylowTwoOf_inf_of_subnormal ht.sylow hL.1 hL.2.2

theorem Tuple25.le_M (ht : Tuple25 T M H S z) : S ≤ M :=
  ht.sylow_inf.le.trans inf_le_right

theorem Tuple25.le_centralizer (ht : Tuple25 T M H S z) :
    S ≤ Subgroup.centralizer ({z} : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzc : z ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr ht.le_T) ht.z_mem.2
  exact Subgroup.mem_centralizer_iff.mp hzc s hs

theorem Tuple25.inf_eq_borel_of_bender (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hB : BenderBorelFacts) {L : Subgroup G} (hL : IsComponentIn L H) (hLM : ¬ L ≤ M)
    (hbend : fusionIsBenderGroup ↥L) :
    M ⊓ L = L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨hchar, hmax⟩ := hB G L (S ⊓ L) (BenderBranch.isQuasisimple_of_isComponentIn hL) hbend
    (ht.sylow_inf_component hL)
  have hBM : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ M :=
    ht.le_M_of_component_charTwo hs hL inf_le_left
      (Unc25G2.inf_normalizer_le_normalizer_borel S L) hchar
  rcases hmax (M ⊓ L) (le_inf hBM inf_le_left) inf_le_right with h | h
  · exact h
  · exact absurd (inf_eq_right.mp h) hLM

theorem Tuple25.rankTwo_data (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hR : RankTwoBorelFacts) {L : Subgroup G} (hL : IsComponentIn L H) (hLM : ¬ L ≤ M)
    (hrk : IsRankTwoEvenType L) :
    M ⊓ L = L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧ NontrivialOnDynkin M S L := by
  obtain ⟨hchar, P₁, P₂, hBP₁, hP₁L, hBP₂, hP₂L, hne, hjoin, hlat, hc₁, hc₂⟩ :=
    hR G L (S ⊓ L) (BenderBranch.isQuasisimple_of_isComponentIn hL) hrk
      (ht.sylow_inf_component hL)
  set B := L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) with hBdef
  have hS₁B : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (B : Set G) :=
    Unc25G2.inf_normalizer_le_normalizer_borel S L
  have hS₁ML : S ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((M ⊓ L : Subgroup G) : Set G) :=
    Unc25G2.inf_normalizer_le_normalizer_inf_of_le ht.le_M
  have hover : ∀ K : Subgroup G, K ≤ L →
      S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G) → CharTwo K →
        K ≤ M ⊓ L :=
    fun K hKL hK hKc => le_inf (ht.le_M_of_component_charTwo hs hL hKL hK hKc) hKL
  have hBML : B ≤ M ⊓ L := hover B inf_le_left hS₁B hchar
  have hinv : ∀ X : Subgroup G, B < X → X < L →
      S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (X : Set G) → X ≤ M ⊓ L := by
    intro X hBX hXL hSX
    rcases hlat X hBX hXL with rfl | rfl
    · exact hover _ hP₁L.le hSX hc₁
    · exact hover _ hP₂L.le hSX hc₂
  have hMLB : M ⊓ L = B := by
    by_contra hne'
    have hBlt : B < M ⊓ L := lt_of_le_of_ne hBML (Ne.symm hne')
    have hMLlt : M ⊓ L < L := lt_of_le_of_ne inf_le_right (fun h => hLM (inf_eq_right.mp h))
    rcases hlat (M ⊓ L) hBlt hMLlt with h1 | h2
    · have hN₂ : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (P₂ : Set G) :=
        fun g hg => Unc25G2.mem_normalizer_of_lattice (hS₁B hg) hg.2 (hS₁ML hg) h1 hlat hne
          hBP₂ hP₂L
      have h3 := hinv P₂ hBP₂ hP₂L hN₂
      rw [h1] at h3
      have hLP₁ : L ≤ P₁ := by
        rw [← hjoin]
        exact sup_le le_rfl h3
      exact lt_irrefl _ (lt_of_lt_of_le hP₁L hLP₁)
    · have hlat' : ∀ W : Subgroup G, B < W → W < L → W = P₂ ∨ W = P₁ :=
        fun W h1 h2 => (hlat W h1 h2).symm
      have hN₁ : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (P₁ : Set G) :=
        fun g hg => Unc25G2.mem_normalizer_of_lattice (hS₁B hg) hg.2 (hS₁ML hg) h2 hlat' hne.symm
          hBP₁ hP₁L
      have h3 := hinv P₁ hBP₁ hP₁L hN₁
      rw [h2] at h3
      have hLP₂ : L ≤ P₂ := by
        rw [← hjoin]
        exact sup_le h3 le_rfl
      exact lt_irrefl _ (lt_of_lt_of_le hP₂L hLP₂)
  refine ⟨hMLB, ?_⟩
  intro X hMLX hXL hSX
  by_contra hcon
  have hcon' : X ≠ M ⊓ L ∧ X ≠ L := not_or.mp hcon
  have hBX : B < X := by
    rw [← hMLB]
    exact lt_of_le_of_ne hMLX (Ne.symm hcon'.1)
  exact hcon'.1 (le_antisymm (hinv X hBX (lt_of_le_of_ne hXL hcon'.2) hSX) hMLX)

theorem three_le_of_isFermatOrMersenne {p : ℕ} (hp : IsFermatOrMersenne p) : 3 ≤ p := by
  obtain ⟨hpp, hp'⟩ := hp
  have h2 := hpp.two_le
  by_contra hlt
  have hp2 : p = 2 := by omega
  rcases hp' with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · have h1 : 1 < 2 ^ 2 ^ k := Nat.one_lt_two_pow (by positivity)
    omega
  · have h1 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

theorem lemma252_of_inputs (h237 : Lemma2_3_9_7) (hB : BenderBorelFacts) (hR : RankTwoBorelFacts)
    (hA6 : A6InnerFact) (hA7 : A7Excluded) (hM2 : M22M23Excluded) (hL42 : L42Excluded)
    (hsmall : SmallL2Facts) (hnalt : NotAltQuotientFacts) : Lemma252 := by
  intro G _ _ T M H S z hs ht L hL
  have hUS : UniqueSetting G T M := hs.setting
  have hT' : IsSylowTwoOf T M := hUS.isSylowTwoOf_M
  obtain ⟨hzN, hcomm, hLM, -⟩ := IsGamma0.component_normalized_commutator_not_le hUS ht.gamma0
    ht.sylow_inf hT' ht.le_T ht.z_mem ht.z_ne_one ht.z_sq hL
  obtain ⟨hinn, hlist⟩ := h237 G T M hUS H S T z ht.gamma0 ht.sylow_inf hT' ht.le_T ht.z_mem
    ht.z_ne_one ht.z_sq L hL
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hP : IsSylowTwoOf (S ⊓ L) L := ht.sylow_inf_component hL
  set S₁ := S ⊓ Subgroup.normalizer (L : Set G) with hS₁
  have hS₁2 : IsPGroup 2 ↥S₁ := ht.sylow.2.1.to_le inf_le_left
  have hS₁N : S₁ ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hS₁P : IsSylowTwoOf (S₁ ⊓ L) L := by
    have h : S₁ ⊓ L = S ⊓ L := by
      rw [hS₁, inf_assoc, inf_eq_right.mpr Subgroup.le_normalizer]
    rw [h]
    exact hP
  have hS₁C : S₁ ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left.trans ht.le_centralizer
  have hS₁M : S₁ ≤ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) := by
    have h := Unc25G2.inf_normalizer_le_normalizer_inf_of_le (L := L) ht.le_M
    rwa [inf_comm M L] at h
  have hover : ∀ K : Subgroup G, K ≤ L → S₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K →
      K ≤ L ⊓ M :=
    fun K hKL hK hKc => le_inf hKL (ht.le_M_of_component_charTwo hs hL hKL hK hKc)
  have hLMne : L ⊓ M ≠ L := fun h => hLM (inf_eq_left.mp h)
  have hnorm_of : IsNonAltListedType L → Ch1.InducesInner z L := fun hn =>
    hinn (hnalt G L hq hn)
  have caseBender : fusionIsBenderGroup ↥L → ComponentList M S z L := fun hbend =>
    ⟨hzN, hnorm_of (Or.inl hbend), hcomm, hLM,
      Or.inl ⟨hbend, S ⊓ L, hP, ht.inf_eq_borel_of_bender hs hB hL hLM hbend⟩⟩
  have caseRank : IsRankTwoEvenType L → ComponentList M S z L := fun hrk => by
    obtain ⟨hMLB, hdyn⟩ := ht.rankTwo_data hs hR hL hLM hrk
    have hin : Ch1.InducesInner z L := by
      by_cases hA : Nonempty (↥L ≃* alternatingGroup (Fin 6))
      · refine hA6 G L S₁ (M ⊓ L) z (Or.inl hA) hS₁2 hS₁N hS₁P hzN hS₁C inf_le_right ?_ ?_
        · rw [inf_comm]
          exact hLMne
        · intro K hKL hK hKc
          rw [inf_comm]
          exact hover K hKL hK hKc
      · refine hnorm_of ?_
        rcases hrk with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact absurd h hA
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    exact ⟨hzN, hin, hcomm, hLM, Or.inr (Or.inl ⟨hrk, hdyn, S ⊓ L, hP, hMLB⟩)⟩
  have caseCover : IsThreeFoldCoverAlt L 6 → False := fun hcov => by
    have hin : Ch1.InducesInner z L :=
      hA6 G L S₁ (L ⊓ M) z (Or.inr hcov) hS₁2 hS₁N hS₁P hzN hS₁C inf_le_left hLMne hover
    have hcen := ht.centreTwo hs hL hin
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3
      (show 3 ∣ Nat.card ↥(Subgroup.center ↥L) by rw [hcov.2.1])
    have hxc : ∀ y ∈ L, y * ((x : ↥L) : G) = ((x : ↥L) : G) * y := fun y hy => by
      have := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hcen _ (x : ↥L).2 hxc
    have hx3 : ((x : ↥L) : G) ^ 3 = 1 := by
      have h3 : x ^ 3 = 1 := by
        rw [← hx]
        exact pow_orderOf_eq_one x
      have := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : G)) h3
      simpa using this
    have h1 := Unc25G2.eq_one_of_pow_eq_one_of_two_pow Nat.prime_three (by norm_num) hx3 hk
    have hx1 : x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    rw [hx1, orderOf_one] at hx
    omega
  rcases hlist with hBend | hRank | ⟨hAlt7, hPart⟩ | ⟨hD, zL, hproj, hML⟩ |
    ⟨⟨p, hp, hpL⟩, hML⟩ | hF | ⟨hG, hout, zL, hproj, hML⟩
  · exact caseBender hBend
  · rcases hRank with h | h | h | h | h
    · exact caseRank (Or.inl h)
    · exact caseRank (Or.inr (Or.inl h))
    · exact caseRank (Or.inr (Or.inr (Or.inl h)))
    · exact caseRank (Or.inr (Or.inr (Or.inr h)))
    · exact (caseCover h).elim
  · exact (hA7 G L S₁ (L ⊓ M) hAlt7 hPart inf_le_left hS₁2 hS₁N hS₁P hS₁M hover).elim
  · have hn : IsNonAltListedType L := by
      rcases hD with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    refine ⟨hzN, hnorm_of hn, hcomm, hLM, Or.inr (Or.inr (Or.inl ⟨hD, zL, hproj, ?_⟩))⟩
    rw [inf_comm]
    exact hML
  · by_cases h7 : 7 < p
    · have hn : IsNonAltListedType L :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hpL⟩)))))
      refine ⟨hzN, hnorm_of hn, hcomm, hLM, Or.inr (Or.inr (Or.inr ⟨⟨p, hp, h7, hpL⟩, ?_⟩))⟩
      rw [inf_comm]
      exact hML
    · push Not at h7
      have hp3 : 3 ≤ p := three_le_of_isFermatOrMersenne hp
      have hpp : p.Prime := hp.1
      interval_cases p
      · obtain ⟨-, -, -, -, h3⟩ := hpL.1
        exact absurd (by norm_num) h3
      · exact absurd hpp (by norm_num)
      · exact caseBender (hsmall.1 ↥L hpL)
      · exact absurd hpp (by norm_num)
      · exact caseRank (Or.inl ⟨1, le_rfl, hsmall.2 ↥L hpL⟩)
  · exact (hM2 G L S₁ (L ⊓ M) hF inf_le_left hS₁2 hS₁N hS₁P hS₁M hover).elim
  · refine (hL42 G L S₁ (L ⊓ M) z zL hG ?_ hproj hML hLMne hS₁2 hS₁N hS₁P hS₁M hS₁C
      hover).elim
    obtain ⟨s, hsS, hso⟩ := hout
    exact ⟨s, ⟨hsS, hso.1⟩, hso⟩

end Proof

end CFSG.QuasithinUnique
