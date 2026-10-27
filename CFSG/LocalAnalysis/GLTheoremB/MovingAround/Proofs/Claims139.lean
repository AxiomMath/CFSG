module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input183
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313i
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs71
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma114
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1115
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1312b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims138

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims139

open scoped Pointwise

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section NoA7

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCore_eq_pCore_two_of_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    (hbot : GLAPPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) :
    GLAPPrimeCore p ↥L = CFSG.pCore 2 ↥L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop2 : Nat.Coprime p (Nat.card ↥(CFSG.pCore 2 ↥L)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hle1 : CFSG.pCore 2 ↥L ≤ GLAPPrimeCore p ↥L :=
    CFSG.le_pPrimeCore_of_normal_coprime (CFSG.pCore_normal (p := 2) (G := ↥L)) hcop2
  refine le_antisymm (fun x hx => ?_) hle1
  set f : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hf
  haveI : ((GLAPPrimeCore p ↥L).map f).Normal :=
    Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
  have hdvd : Nat.card ↥((GLAPPrimeCore p ↥L).map f) ∣ Nat.card ↥(GLAPPrimeCore p ↥L) :=
    Subgroup.card_map_dvd (GLAPPrimeCore p ↥L) f
  have hcopY : Nat.Coprime p (Nat.card ↥((GLAPPrimeCore p ↥L).map f)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => not_dvd_card_pPrimeCore hp L (h.trans hdvd)
  have hsub := CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcopY
  have h1 : f x ∈ (⊥ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    (hsub.trans hbot.le) (Subgroup.mem_map_of_mem f hx)
  rw [Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem card_alt_seven : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  have h := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin 7 (by norm_num)
  have h7 : Nat.factorial 7 = 5040 := by decide
  omega

theorem card_alt_ne_2520 (k : ℕ) (hk : 0 < k) :
    Nat.card ↥(alternatingGroup (Fin (k * 3 + 2))) ≠ 2520 := by
  have h := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin (k * 3 + 2)
    (by omega)
  intro hc
  rw [hc] at h
  rcases Nat.lt_or_ge (k * 3 + 2) 7 with hlt | hge
  · have h6 : (k * 3 + 2).factorial ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
    have : Nat.factorial 6 = 720 := by decide
    omega
  · have h8 : Nat.factorial 8 ≤ (k * 3 + 2).factorial := Nat.factorial_le (by omega)
    have : Nat.factorial 8 = 40320 := by decide
    omega

theorem not_isOmegaTwo_of_alt_seven {X : Type} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 7)) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hX : IsOmegaTwo ε (n + 1) X) : False := by
  have hcard : Nat.card X = 2520 := (Nat.card_congr e.toEquiv).trans card_alt_seven
  have hns : ¬ Group.IsSolvable X := by
    intro hs
    haveI : Nontrivial ↥(alternatingGroup (Fin 7)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, card_alt_seven]
      norm_num
    have hperf : commutator ↥(alternatingGroup (Fin 7)) = ⊤ :=
      commutator_alternatingGroup_eq_top (by simp)
    haveI := hs
    exact OmegaFacts.not_isSolvable_of_perfect hperf
      (Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective)
  rcases OmegaFacts.omega_data hX with ⟨h1, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨-, -, h3, -⟩ |
      ⟨-, -, h3, -⟩ | ⟨-, -, h5, -⟩
  · omega
  · omega
  · exact hns h3
  · omega
  · rw [hcard] at h5
    norm_num at h5

theorem lemma137_noA7_of_prop134 (h134 : Prop134_of_cexStatement) : Lemma137_noA7Statement := by
  intro G _ _ m p B M E A D T h L hL hp3 hA7
  have hp : p.Prime := GLStanding.prime h.standing
  have hp2 : p ≠ 2 := GLStanding.ne_two h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, -, L0, hL0, rfl⟩ := Lemma137b.istar_component' hp hL
  obtain ⟨eA⟩ := hA7
  have hbot : GLAPPrimeCore p (↥(GLBConj g L0) ⧸ CFSG.pCore 2 ↥(GLBConj g L0)) = ⊥ := by
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup (↥(GLBConj g L0) ⧸ CFSG.pCore 2 ↥(GLBConj g L0)) := eA.isSimpleGroup
    refine OmegaFacts.pPrimeCore_eq_bot_of_simple hp ?_
    rw [Nat.card_congr eA.toEquiv, card_alt_seven, hp3]
    norm_num
  have hcore := glaPPrimeCore_eq_pCore_two_of_bot hp hp2 hbot
  have e1 : barOf p (GLBConj g L0) ≃* ↥(alternatingGroup (Fin 7)) :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans eA
  have hL0M : L0 ≤ M := hL0.1.1
  have e2 : ↥(barX p M L0) ≃* ↥(alternatingGroup (Fin 7)) :=
    ((quotEquivBarX hp hL0M hL0.1.2.1).symm.trans (conjQuotEquiv p g L0)).trans e1
  have hL0I : L0 ≤ Iof p M D := by
    unfold Iof
    exact le_iSup₂_of_le (f := fun L (_ : GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤
      Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))) => L) L0 hL0 le_rfl
  have hL0c : GLAPComponent p (Iof p M D) L0 := glaPComponent_of_le hp hL0.1 hL0I (Iof_le_M p M D)
  refine h134 (⟨h, hL0c, ?_⟩ : Cex134 G m p B M E A D T L0)
  rintro (⟨k, hk, -, e, -⟩ | ⟨n, hn, ⟨-, -, e, -⟩ | ⟨-, -, e, -⟩⟩)
  · subst hp3
    exact card_alt_ne_2520 k hk ((Nat.card_congr e.toEquiv).symm.trans
      ((Nat.card_congr e2.toEquiv).trans card_alt_seven))
  · exact not_isOmegaTwo_of_alt_seven e2 hn (ε := true) ⟨e⟩
  · exact not_isOmegaTwo_of_alt_seven e2 hn (ε := false) ⟨e⟩

end NoA7

section Diag

variable {G : Type} [Group G] [Finite G]

noncomputable def centerQuotCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem gLBConj_pow_cycled {p : ℕ} {L : ZMod p → Subgroup G} {x : G}
    (hcyc : ∀ i, GLBConj x (L i) = L (i + 1)) (j : ZMod p) :
    ∀ k : ℕ, GLBConj (x ^ k) (L j) = L (j + k)
  | 0 => by simp [gLBConj_one]
  | k + 1 => by
    rw [pow_succ, ← gLBConj_gLBConj, gLBConj_pow_cycled hcyc j k, hcyc]
    congr 1
    push_cast
    ring

theorem input18_3DiagZ_holds : Lemma1313Z.Input18_3DiagZ := by
  intro p hp hp2 G _ _ hsimple hnab hKpr x y hx hy hxy J hJ L hL hinj hcyc hKeq i
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set C := Subgroup.centralizer ({y} : Set G) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hxy
  set K := ⨆ i, L i with hKdef
  have hLC : ∀ i, L i ≤ C := fun i => (hL i).1
  have hKC : K ≤ C := iSup_le hLC
  have hJ' : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J := by
    have := input18_3Two_holds p hp hp2 G hsimple hnab hKpr x y hx hy hxy J hJ
    rwa [hKeq] at this
  have hJC : J ≤ C := hJ'.1.trans (inf_le_left.trans hKC)
  have hxK : GLBConj x K = K := by
    rw [hKdef, gLBConj_iSup_eq]
    simp_rw [hcyc]
    exact (Equiv.addRight (1 : ZMod p)).iSup_comp (g := L)
  have hxKn : x ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_gLBConj_eq.2 hxK
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hx]
    exact ⟨1, (pow_one p).symm⟩
  set xb : ↥C ⧸ GLAPPrimeCore p ↥C := QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩ with hxb
  have hxbp : xb ^ p = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨x, hxC⟩ : ↥C) ^ p = 1 := Subtype.ext (by simp [← hx, pow_orderOf_eq_one])
    rw [this, map_one]
  have hxb1 : xb ≠ 1 := by
    intro h1
    have hmem : (⟨x, hxC⟩ : ↥C) ∈ GLAPPrimeCore p ↥C := (QuotientGroup.eq_one_iff _).1 h1
    have hord : orderOf (⟨⟨x, hxC⟩, hmem⟩ : ↥(GLAPPrimeCore p ↥C)) = p := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact hx
    have hdiv := orderOf_dvd_natCard (⟨⟨x, hxC⟩, hmem⟩ : ↥(GLAPPrimeCore p ↥C))
    rw [hord] at hdiv
    exact not_dvd_card_pPrimeCore hp C hdiv
  have hxbord : orderOf xb = p := orderOf_eq_prime hxbp hxb1
  have hLc : ∀ i, IsComponentOf (barX p C (L i)) ⊤ := fun i => (hL i).2.2.1
  have hKbar : barX p C K = sSup (Set.range fun i => barX p C (L i)) := by
    rw [sSup_range]
    refine le_antisymm (barX_iSup_le_iSup (fun i => L i) hLC) (iSup_le fun i => ?_)
    exact Lemma1311.barX_mono' p (le_iSup L i)
  have hxbK : xb ∈ Subgroup.normalizer ((barX p C K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
      Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    rw [hxb, ← barX_gLBConj_eq p hxC K, hxK]
  have hcomp : ∀ X ∈ Set.range fun i => barX p C (L i), IsComponentOf X (barX p C K) := by
    rintro X ⟨a, rfl⟩
    have hle : barX p C (L a) ≤ barX p C K := Lemma1311.barX_mono' p (le_iSup L a)
    exact ⟨hle, isSubnormal_of_le_of_le (hLc a).2.1 hle le_top, (hLc a).2.2⟩
  have hcomm : ∀ X ∈ Set.range (fun i => barX p C (L i)), ∀ X' ∈ Set.range (fun i => barX p C (L i)),
      X ≠ X' → ∀ u ∈ X, ∀ v ∈ X', u * v = v * u := by
    rintro X ⟨a, rfl⟩ X' ⟨b, rfl⟩ hne u hu v hv
    have hc := Sec13e.commute_of_isComponentOf (hLc a) (hLc b) hne
    have hmem := Subgroup.commutator_mem_commutator hu hv
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hnorm : ∀ X ∈ Set.range (fun i => barX p C (L i)),
      xb ∉ Subgroup.normalizer (X : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rintro X ⟨a, rfl⟩ hn
    have h1 : GLBConj xb (barX p C (L a)) = barX p C (L a) := gLBConj_eq_of_mem_normalizer hn
    rw [hxb, ← barX_gLBConj_eq p hxC (L a), hcyc a] at h1
    have h2 : L (a + 1) = L a := glaPComponent_unique (hL (a + 1)) (hL a) h1
    have h3 : a + 1 = a := hinj h2
    have h4 : (1 : ZMod p) = 0 := by
      have := congrArg (fun t => t - a) h3
      simpa using this
    exact one_ne_zero h4
  have hQ : GLAPComponent p (barX p C K ⊓ Subgroup.centralizer ({xb} : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (barX p C J) :=
    Prop126b.glaPComponent_barX_inf_centralizer hp hxC hKC hxKn hxp hJ'
  obtain ⟨X, ⟨j, rfl⟩, ⟨e⟩⟩ := input18_3_diag_holds (↥C ⧸ GLAPPrimeCore p ↥C) p hp (barX p C K)
    (Set.range fun i => barX p C (L i)) xb hxbord hxbK hKbar hcomp hcomm (Or.inr hnorm)
    (barX p C J) hQ
  have e1 : barOf p J ≃* barOf p (barX p C J) := Prop126b.barOfBarX hp hJC
  have e2 : barOf p (L j) ≃* ↥(barX p C (L j)) := quotEquivBarX hp (hLC j) (hL j).2.1
  have hLi : L i = GLBConj (x ^ (i - j).val) (L j) := by
    rw [gLBConj_pow_cycled hcyc j, ZMod.natCast_zmod_val]
    congr 1
    ring
  have e3 : barOf p (L j) ≃* barOf p (L i) := by
    rw [hLi]
    exact conjQuotEquiv p (x ^ (i - j).val) (L j)
  exact ⟨((centerQuotCongr e1).trans e).trans ((centerQuotCongr e2.symm).trans (centerQuotCongr e3))⟩

end Diag

section Proj

variable {Q : Type} [Group Q] [Finite Q]

theorem quasisimple_normal {H : Type*} [Group H] (hQ : CFSG.Open.IsQuasisimple H) {N : Subgroup H}
    (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center H := by
  obtain ⟨hp, hs⟩ := hQ
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hs
  have := hN.map (QuotientGroup.mk' (Subgroup.center H)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center H)))
    with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center H = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center H)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center H, Subgroup.center H⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup H).map (QuotientGroup.mk' N) =
        (Subgroup.center H).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator H ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem card_alt_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem a5_perfect_eq_top (H : Subgroup (alternatingGroup (Fin 5))) (hH : ⁅H, H⁆ = H)
    (hne : H ≠ ⊥) : H = ⊤ := by
  by_contra htop
  have hdvd : Nat.card H ∣ 60 := by
    rw [← card_alt_five]
    exact Subgroup.card_subgroup_dvd_card H
  have hperf : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  have hnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have hne60 : Nat.card H ≠ 60 := by
    intro h
    exact htop (Subgroup.eq_top_of_card_eq H (by rw [h, card_alt_five]))
  have h30 : Nat.card H = 30 := by
    by_contra h30
    have hle : (Nat.card H).primeFactors.card ≤ 2 := by
      have hmem : Nat.card H ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have key : ∀ d ∈ Nat.divisors 60, d ≠ 30 → d ≠ 60 → d.primeFactors.card ≤ 2 := by
        decide +kernel
      exact key _ hmem h30 hne60
    exact Group.IsPerfect.not_isSolvable H
      (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two hle)
  have hidx : H.index = 2 := by
    have := Subgroup.card_mul_index H
    rw [h30, card_alt_five] at this
    omega
  have hn : H.Normal := Subgroup.normal_of_index_eq_two hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact hne h
  · exact htop h

theorem mul_comm_of_ne_comp {X X' : Subgroup Q} (hX : IsComponentOf X ⊤) (hX' : IsComponentOf X' ⊤)
    (hne : X ≠ X') {a b : Q} (ha : a ∈ X) (hb : b ∈ X') : a * b = b * a := by
  have hc := Sec13e.commute_of_isComponentOf hX hX' hne
  have hmem := Subgroup.commutator_mem_commutator ha hb
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem le_centralizer_of_ne_comp {X X' : Subgroup Q} (hX : IsComponentOf X ⊤)
    (hX' : IsComponentOf X' ⊤) (hne : X ≠ X') : X' ≤ Subgroup.centralizer (X : Set Q) := fun b hb =>
  Subgroup.mem_centralizer_iff.2 fun a ha => mul_comm_of_ne_comp hX hX' hne ha hb

variable {𝒦 : Set (Subgroup Q)}

theorem sSup_le_normalizer_comp (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤) {X : Subgroup Q} (hX : X ∈ 𝒦) :
    sSup 𝒦 ≤ Subgroup.normalizer (X : Set Q) := by
  refine sSup_le fun X' hX' => ?_
  by_cases h : X' = X
  · subst h
    exact Subgroup.le_normalizer
  · exact (le_centralizer_of_ne_comp (h𝒦 X hX) (h𝒦 X' hX') (Ne.symm h)).trans
      (Subgroup.centralizer_le_normalizer _)

theorem conj_injective_of_center {X : Subgroup Q} (hZ : Subgroup.center ↥X = ⊥) :
    Function.Injective (MulAut.conj : ↥X →* MulAut ↥X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker] at hs
  have hsZ : s ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun τ : MulAut ↥X => τ g) hs
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ] at hsZ
  exact hsZ

theorem normalizerMonoidHom_mem_range (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤) {X : Subgroup Q}
    (hX : X ∈ 𝒦) (s : ↥(sSup 𝒦)) :
    X.normalizerMonoidHom (Subgroup.inclusion (sSup_le_normalizer_comp h𝒦 hX) s) ∈
      (MulAut.conj : ↥X →* MulAut ↥X).range := by
  set T : Subgroup Q := (((MulAut.conj : ↥X →* MulAut ↥X).range.comap X.normalizerMonoidHom).map
    (Subgroup.normalizer (X : Set Q)).subtype) with hT
  have hle : sSup 𝒦 ≤ T := by
    refine sSup_le fun X' hX' => ?_
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (X : Set Q) := sSup_le_normalizer_comp h𝒦 hX (le_sSup hX' hb)
    refine ⟨⟨b, hbN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    by_cases h : X' = X
    · subst h
      refine ⟨⟨b, hb⟩, ?_⟩
      ext y
      simp [MulAut.conj_apply]
    · have hbC : b ∈ Subgroup.centralizer (X : Set Q) :=
        le_centralizer_of_ne_comp (h𝒦 X hX) (h𝒦 X' hX') (Ne.symm h) hb
      refine ⟨1, ?_⟩
      ext y
      show ((MulAut.conj (1 : ↥X)) y : Q) = b * y * b⁻¹
      rw [map_one, MulAut.one_apply, ← Subgroup.mem_centralizer_iff.1 hbC y y.2]
      group
  obtain ⟨n, hn, hns⟩ := hle s.2
  have : n = Subgroup.inclusion (sSup_le_normalizer_comp h𝒦 hX) s := Subtype.ext hns
  rw [← this]
  exact hn

noncomputable def projA5 (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤) {X : Subgroup Q} (hX : X ∈ 𝒦)
    (hZ : Subgroup.center ↥X = ⊥) (eA : ↥X ≃* ↥(alternatingGroup (Fin 5))) :
    ↥(sSup 𝒦) →* ↥(alternatingGroup (Fin 5)) :=
  ((MonoidHom.ofInjective (conj_injective_of_center hZ)).symm.trans eA).toMonoidHom.comp
    ((X.normalizerMonoidHom.comp (Subgroup.inclusion (sSup_le_normalizer_comp h𝒦 hX))).codRestrict
      _ (normalizerMonoidHom_mem_range h𝒦 hX))

theorem mem_centralizer_of_projA5 (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤) {X : Subgroup Q} (hX : X ∈ 𝒦)
    (hZ : Subgroup.center ↥X = ⊥) (eA : ↥X ≃* ↥(alternatingGroup (Fin 5))) {s : ↥(sSup 𝒦)}
    (hs : projA5 h𝒦 hX hZ eA s = 1) : (s : Q) ∈ Subgroup.centralizer (X : Set Q) := by
  unfold projA5 at hs
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hs
  have h2 : X.normalizerMonoidHom (Subgroup.inclusion (sSup_le_normalizer_comp h𝒦 hX) s) = 1 :=
    congrArg Subtype.val hs
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h3 := congrArg (fun f : MulAut ↥X => ((f ⟨x, hx⟩ : ↥X) : Q)) h2
  change (s : Q) * x * (s : Q)⁻¹ = x at h3
  calc x * (s : Q) = ((s : Q) * x * (s : Q)⁻¹) * (s : Q) := by rw [h3]
    _ = (s : Q) * x := by group

theorem le_centralizer_of_proj_ne_top (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤) {X : Subgroup Q}
    (hX : X ∈ 𝒦) (hZ : Subgroup.center ↥X = ⊥) (eA : ↥X ≃* ↥(alternatingGroup (Fin 5)))
    {H Y : Subgroup Q} (hHS : H ≤ sSup 𝒦) (hHp : ⁅H, H⁆ = H) (hYH : Y ≤ H)
    (hYn : H ≤ Subgroup.normalizer (Y : Set Q))
    (hne : (Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) ≠ ⊤) :
    Y ≤ Subgroup.centralizer (X : Set Q) := by
  have hP : ⁅(H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA),
      (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA)⁆ =
      (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) := by
    rw [← Subgroup.map_commutator, ← subgroupOf_commutator hHS hHS, hHp]
  have hYle : Y.subgroupOf (sSup 𝒦) ≤ H.subgroupOf (sSup 𝒦) := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hYH (Subgroup.mem_subgroupOf.1 hx))
  have hYbot : (Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) = ⊥ := by
    by_cases hb : (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) = ⊥
    · exact le_bot_iff.1 (hb ▸ Subgroup.map_mono hYle)
    · have htop := a5_perfect_eq_top _ hP hb
      haveI hn : ((Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA)).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hg : g ∈ (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) := htop ▸ Subgroup.mem_top g
        obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hn
        refine Subgroup.mem_map.2 ⟨h * y * h⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        rw [Subgroup.mem_subgroupOf] at hh hy ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.1 (hYn hh) (y : Q)).1 hy
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          ((Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA)) with h1 | h1
      · exact h1
      · exact absurd h1 hne
  intro y hy
  have hyS : y ∈ sSup 𝒦 := hHS (hYH hy)
  have h1 : projA5 h𝒦 hX hZ eA ⟨y, hyS⟩ = 1 := by
    have : projA5 h𝒦 hX hZ eA ⟨y, hyS⟩ ∈ (Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy)
    rw [hYbot, Subgroup.mem_bot] at this
    exact this
  exact mem_centralizer_of_projA5 h𝒦 hX hZ eA h1

theorem le_centralizer_of_coprime (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤) {X : Subgroup Q}
    (hX : X ∈ 𝒦) (hZ : Subgroup.center ↥X = ⊥) (eA : ↥X ≃* ↥(alternatingGroup (Fin 5)))
    {H Y : Subgroup Q} (hHS : H ≤ sSup 𝒦) (hHp : ⁅H, H⁆ = H) (hYH : Y ≤ H)
    (hYn : H ≤ Subgroup.normalizer (Y : Set Q)) (hY3 : ¬ 3 ∣ Nat.card Y) :
    Y ≤ Subgroup.centralizer (X : Set Q) := by
  refine le_centralizer_of_proj_ne_top h𝒦 hX hZ eA hHS hHp hYH hYn fun htop => hY3 ?_
  have h1 : Nat.card ↥((Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA)) ∣
      Nat.card ↥(Y.subgroupOf (sSup 𝒦)) := Subgroup.card_map_dvd _ _
  rw [htop, Subgroup.card_top, card_alt_five,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hYH.trans hHS)).toEquiv] at h1
  exact (show (3 : ℕ) ∣ 60 by norm_num).trans h1

theorem le_centralizer_of_central (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤) {X : Subgroup Q}
    (hX : X ∈ 𝒦) (hZ : Subgroup.center ↥X = ⊥) (eA : ↥X ≃* ↥(alternatingGroup (Fin 5)))
    {H Y : Subgroup Q} (hHS : H ≤ sSup 𝒦) (hHp : ⁅H, H⁆ = H) (hYH : Y ≤ H)
    (hYc : H ≤ Subgroup.centralizer (Y : Set Q)) :
    Y ≤ Subgroup.centralizer (X : Set Q) := by
  have hYn : H ≤ Subgroup.normalizer (Y : Set Q) := hYc.trans (Subgroup.centralizer_le_normalizer _)
  refine le_centralizer_of_proj_ne_top h𝒦 hX hZ eA hHS hHp hYH hYn fun htop => ?_
  have hab : ∀ a b : ↥(alternatingGroup (Fin 5)), a * b = b * a := by
    intro a b
    have ha : a ∈ (Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (Y.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX hZ eA) := htop ▸ Subgroup.mem_top b
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [Subgroup.mem_subgroupOf] at hu hv
    exact (Subgroup.mem_centralizer_iff.1 (hYc (hYH hv)) (u : Q) hu)
  have h3 : (⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ :
      ↥(alternatingGroup (Fin 5))) * ⟨Equiv.swap 1 2 * Equiv.swap 2 3,
        by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ ≠
      ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ *
      ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ := by
    intro h
    have := congrArg Subtype.val h
    revert this
    decide
  exact h3 (hab _ _)

theorem eq_one_of_centralizes_all (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤)
    (hZ : ∀ X ∈ 𝒦, Subgroup.center ↥X = ⊥) {y : Q} (hy : y ∈ sSup 𝒦)
    (hc : ∀ X ∈ 𝒦, y ∈ Subgroup.centralizer (X : Set Q)) : y = 1 := by
  classical
  have key : ∀ F : Finset (Subgroup Q), (↑F : Set (Subgroup Q)) ⊆ 𝒦 →
      ∀ y ∈ sSup (↑F : Set (Subgroup Q)), (∀ X ∈ F, y ∈ Subgroup.centralizer (X : Set Q)) → y = 1 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _ y hy _
      simpa using hy
    | insert X F hXF ih =>
      intro hsub y hy hc
      have hXK : X ∈ 𝒦 := hsub (by simp)
      have hsubF : (↑F : Set (Subgroup Q)) ⊆ 𝒦 := fun Z hZ => hsub (by simp [hZ])
      rw [Finset.coe_insert, sSup_insert] at hy
      have hFC : sSup (↑F : Set (Subgroup Q)) ≤ Subgroup.centralizer (X : Set Q) := by
        refine sSup_le fun X' hX' => le_centralizer_of_ne_comp (h𝒦 X hXK) (h𝒦 X' (hsubF hX')) ?_
        rintro rfl
        exact hXF hX'
      obtain ⟨a, ha, b, hb, rfl⟩ := Lemma137.mem_sup_of_comm
        (fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hFC hb) a ha) y hy
      have hbC : b ∈ Subgroup.centralizer (X : Set Q) := hFC hb
      have hyC : a * b ∈ Subgroup.centralizer (X : Set Q) := hc X (by simp)
      have haC : a ∈ Subgroup.centralizer (X : Set Q) := by
        have := Subgroup.mul_mem _ hyC (Subgroup.inv_mem _ hbC)
        simpa using this
      have ha1 : a = 1 := by
        have hcen : (⟨a, ha⟩ : ↥X) ∈ Subgroup.center ↥X := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          exact Subgroup.mem_centralizer_iff.1 haC g g.2
        rw [hZ X hXK, Subgroup.mem_bot] at hcen
        exact congrArg Subtype.val hcen
      subst ha1
      rw [one_mul] at hc ⊢
      exact ih hsubF b hb fun X' hX' => by simpa using hc X' (by simp [hX'])
  have hfin : 𝒦.Finite := Set.toFinite 𝒦
  refine key hfin.toFinset (by simp) y (by simpa using hy) fun X hX => hc X (by simpa using hX)

theorem exists_surj_of_perfect (h𝒦 : ∀ X ∈ 𝒦, IsComponentOf X ⊤)
    (hZ : ∀ X ∈ 𝒦, Subgroup.center ↥X = ⊥)
    (hA : ∀ X ∈ 𝒦, Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    {H : Subgroup Q} (hHS : H ≤ sSup 𝒦) (hHp : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    ∃ φ : ↥H →* ↥(alternatingGroup (Fin 5)), Function.Surjective φ := by
  by_contra hno
  apply hne
  rw [eq_bot_iff]
  intro h hh
  rw [Subgroup.mem_bot]
  refine eq_one_of_centralizes_all h𝒦 hZ (hHS hh) fun X hX => ?_
  obtain ⟨eA⟩ := hA X hX
  have hP : ⁅(H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX (hZ X hX) eA),
      (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX (hZ X hX) eA)⁆ =
      (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX (hZ X hX) eA) := by
    rw [← Subgroup.map_commutator, ← subgroupOf_commutator hHS hHS, hHp]
  have hbot : (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX (hZ X hX) eA) = ⊥ := by
    by_contra hb
    have htop := a5_perfect_eq_top _ hP hb
    apply hno
    refine ⟨((projA5 h𝒦 hX (hZ X hX) eA).comp (H.subgroupOf (sSup 𝒦)).subtype).comp
      (Subgroup.subgroupOfEquivOfLe hHS).symm.toMonoidHom, fun a => ?_⟩
    have ha : a ∈ (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX (hZ X hX) eA) :=
      htop ▸ Subgroup.mem_top a
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ha
    refine ⟨Subgroup.subgroupOfEquivOfLe hHS ⟨u, hu⟩, ?_⟩
    simp
  have h1 : projA5 h𝒦 hX (hZ X hX) eA ⟨h, hHS hh⟩ = 1 := by
    have : projA5 h𝒦 hX (hZ X hX) eA ⟨h, hHS hh⟩ ∈
        (H.subgroupOf (sSup 𝒦)).map (projA5 h𝒦 hX (hZ X hX) eA) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hh)
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact mem_centralizer_of_projA5 h𝒦 hX (hZ X hX) eA h1

end Proj

section CaseB

variable {G : Type} [Group G] [Finite G]

@[expose] def compSet (p : ℕ) (M D : Subgroup G) : Set (Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :=
  Set.range (fun y : {L : Subgroup G // GLAPComponent p (Istar p M D) L} => barX p M y.1)

theorem caseB_data {p : ℕ} (hp : p.Prime) {M D : Subgroup G} (h139b : Prop139b p M D) :
    (∀ X ∈ compSet p M D, IsComponentOf X ⊤) ∧ (∀ X ∈ compSet p M D, Subgroup.center ↥X = ⊥) ∧
      (∀ X ∈ compSet p M D, Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) ∧
        barX p M (Istar p M D) ≤ sSup (compSet p M D) := by
  have hA : ∀ X ∈ compSet p M D, Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) := by
    rintro X ⟨y, rfl⟩
    have hLM : y.1 ≤ M := y.2.1.trans (istar_le_M p M D)
    obtain ⟨f⟩ := h139b.2 y.1 y.2
    exact ⟨(Lemma1311.barXIso hp hLM (Lemma1311.isSubnormal_pComp_of_istar hp y.2)).trans f⟩
  refine ⟨?_, fun X hX => ?_, hA, ?_⟩
  · rintro X ⟨y, rfl⟩
    exact Lemma1311.isComponent_barX_of_pComp hp y.2
  · obtain ⟨e⟩ := hA X hX
    exact center_eq_bot_of_mulEquiv_alt (by norm_num) e
  · unfold compSet
    rw [sSup_range]
    exact Lemma1311.barX_istar_le_iSup_pComp hp M D

theorem barX_le_normalizer_barX (p : ℕ) {M A B : Subgroup G} (hAM : A ≤ M) (hBM : B ≤ M)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    barX p M A ≤ Subgroup.normalizer ((barX p M B : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have key : ∀ a : ↥M, (a : G) ∈ Subgroup.normalizer (B : Set G) → ∀ z ∈ barX p M B,
      QuotientGroup.mk' (GLAPPrimeCore p ↥M) a * z * (QuotientGroup.mk' (GLAPPrimeCore p ↥M) a)⁻¹ ∈
        barX p M B := by
    intro a ha z hz
    obtain ⟨b, hb, rfl⟩ := (Lemma1311.mem_barX' p).1 hz
    refine (Lemma1311.mem_barX' p).2 ⟨a * b * a⁻¹, ?_, by simp⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 ha (b : G)).1 hb
  rintro _ ⟨a, ha, rfl⟩
  have haN : (a : G) ∈ Subgroup.normalizer (B : Set G) := hAB (Subgroup.mem_subgroupOf.1 ha)
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key a haN z, fun hz => ?_⟩
  have h1 := key a⁻¹ (by simpa using (Subgroup.normalizer (B : Set G)).inv_mem haN) _ hz
  simpa [mul_assoc] using h1

theorem not_dvd_card_barX {p : ℕ} {M Y : Subgroup G} (hYM : Y ≤ M) (hY : ¬ p ∣ Nat.card Y) :
    ¬ p ∣ Nat.card (barX p M Y) := by
  intro h
  apply hY
  refine h.trans ?_
  have h1 : Nat.card (barX p M Y) ∣ Nat.card (Y.subgroupOf M) := Subgroup.card_map_dvd _ _
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv] at h1

theorem core_le_of_perfect_caseB {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (h139b : Prop139b p M D) (hLI : L ≤ Istar p M D) (hperf : ⁅L, L⁆ = L) :
    GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h𝒦, hZ, hA, hIS⟩ := caseB_data hp h139b
  have hp3 : p = 3 := h139b.1
  have hLM : L ≤ M := hLI.trans (istar_le_M p M D)
  have hOL : GLAPPrimeCoreOf p L ≤ L := Lemma1313.glaPPrimeCoreOf_le_self L
  have hHS : barX p M L ≤ sSup (compSet p M D) := (Lemma1311.barX_mono' p hLI).trans hIS
  have hHp : ⁅barX p M L, barX p M L⁆ = barX p M L := by
    rw [← barX_commutator p hLM hLM, hperf]
  have hYH : barX p M (GLAPPrimeCoreOf p L) ≤ barX p M L := Lemma1311.barX_mono' p hOL
  have hYn : barX p M L ≤ Subgroup.normalizer
      ((barX p M (GLAPPrimeCoreOf p L) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    barX_le_normalizer_barX p hLM (hOL.trans hLM) (le_normalizer_glaPPrimeCoreOf p L)
  have hY3 : ¬ 3 ∣ Nat.card (barX p M (GLAPPrimeCoreOf p L)) := by
    rw [← hp3]
    exact not_dvd_card_barX (hOL.trans hLM) (not_dvd_card_glaPPrimeCoreOf hp L)
  intro x hx
  have hxM : x ∈ M := hLM (hOL hx)
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ ∈ barX p M (GLAPPrimeCoreOf p L) :=
    (Lemma1311.mem_barX' p).2 ⟨⟨x, hxM⟩, hx, rfl⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨x, hxM⟩ : ↥M) = 1 := by
    refine eq_one_of_centralizes_all h𝒦 hZ (hHS (hYH hmem)) fun X hX => ?_
    obtain ⟨eA⟩ := hA X hX
    exact le_centralizer_of_coprime h𝒦 hX (hZ X hX) eA hHS hHp hYH hYn hY3 hmem
  exact ⟨⟨x, hxM⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem inputL0CoreB_holds : Lemma1313i.InputL0CoreB := by
  intro G _ _ m p B M E A D T R L0 d h h139b
  exact core_le_of_perfect_caseB (GLStanding.prime h.standing) h139b (Lemma1313i.L0_le_istar h)
    (glaPComponent_perfect h.hL0)

theorem nontrivial_of_isQuasisimple {H : Type*} [Group H] (hQ : CFSG.Open.IsQuasisimple H) :
    Nontrivial H := by
  obtain ⟨-, hs⟩ := hQ
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hs
  obtain ⟨a, b, hab⟩ := exists_pair_ne (H ⧸ Subgroup.center H)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [h])⟩

theorem le_normalizer_map_subtype {Q : Type} [Group Q] (H : Subgroup Q) (N : Subgroup ↥H)
    (hN : N.Normal) : H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup Q) : Set Q) := by
  have h1 : (N.map H.subtype).subgroupOf H = N :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  haveI : ((N.map H.subtype).subgroupOf H).Normal := by rw [h1]; exact hN
  exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le N)

theorem exists_pComp_istar {p : ℕ} (hp : p.Prime) {M D S : Subgroup G} (hSI : S ≤ Istar p M D)
    (hS : S ≠ ⊥) : ∃ K : Subgroup G, GLAPComponent p (Istar p M D) K := by
  by_contra hno
  apply hS
  refine le_bot_iff.1 (hSI.trans ((Lemma1311.istar_le_iSup_pComp hp M D).trans
    (iSup_le fun y => absurd ⟨y.1, y.2⟩ hno)))

theorem gap1311Iso_caseB {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    (h139b : Prop139b p M D) {d : G} {J : Subgroup G}
    (hJ : GLAPComponent p (piLayer p (Istar p M D ⊓ Cg d)) J) :
    ∃ K : Subgroup G, GLAPComponent p (Istar p M D) K ∧ Nonempty (barOf p J ≃* barOf p K) := by
  have hp : p.Prime := GLStanding.prime h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hPiS, hJS⟩ := Lemma1311.pComp_piLayer_summand hp hJ
  rw [hJS]
  obtain ⟨h𝒦, hZ, hA, hIS⟩ := caseB_data hp h139b
  have hp3 : p = 3 := h139b.1
  have hSI : S ≤ Istar p M D := hS.1.trans inf_le_left
  have hSM : S ≤ M := hSI.trans (istar_le_M p M D)
  have hperf : ⁅S, S⁆ = S := glaPComponent_perfect hS
  have hHS : barX p M S ≤ sSup (compSet p M D) := (Lemma1311.barX_mono' p hSI).trans hIS
  have hHp : ⁅barX p M S, barX p M S⁆ = barX p M S := by
    rw [← barX_commutator p hSM hSM, hperf]
  have hcore : GLAPPrimeCore p ↥(barX p M S) = ⊥ := by
    have hYH : (GLAPPrimeCore p ↥(barX p M S)).map (barX p M S).subtype ≤ barX p M S :=
      Subgroup.map_subtype_le _
    have hYn := le_normalizer_map_subtype (barX p M S) (GLAPPrimeCore p ↥(barX p M S))
      (GLAPPrimeCore.normal p _)
    have hY3 : ¬ 3 ∣ Nat.card ((GLAPPrimeCore p ↥(barX p M S)).map (barX p M S).subtype) := by
      rw [← hp3, Subgroup.card_map_of_injective (barX p M S).subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have hwY : (w : ↥M ⧸ GLAPPrimeCore p ↥M) ∈
        (GLAPPrimeCore p ↥(barX p M S)).map (barX p M S).subtype := ⟨w, hw, rfl⟩
    exact Subtype.ext (eq_one_of_centralizes_all h𝒦 hZ (hHS (hYH hwY)) fun X hX => by
      obtain ⟨eA⟩ := hA X hX
      exact le_centralizer_of_coprime h𝒦 hX (hZ X hX) eA hHS hHp hYH hYn hY3 hwY)
  have e1 : barOf p S ≃* ↥(barX p M S) :=
    (Prop126b.barOfBarX hp hSM).trans
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)
  have hHq : CFSG.Open.IsQuasisimple ↥(barX p M S) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1 hPiS.1
  have hHZ : Subgroup.center ↥(barX p M S) = ⊥ := by
    have hYH : (Subgroup.center ↥(barX p M S)).map (barX p M S).subtype ≤ barX p M S :=
      Subgroup.map_subtype_le _
    have hYc : barX p M S ≤ Subgroup.centralizer
        (((Subgroup.center ↥(barX p M S)).map (barX p M S).subtype : Subgroup _) : Set _) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hw ⟨x, hx⟩).symm)
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have hwY : (w : ↥M ⧸ GLAPPrimeCore p ↥M) ∈
        (Subgroup.center ↥(barX p M S)).map (barX p M S).subtype := ⟨w, hw, rfl⟩
    exact Subtype.ext (eq_one_of_centralizes_all h𝒦 hZ (hHS (hYH hwY)) fun X hX => by
      obtain ⟨eA⟩ := hA X hX
      exact le_centralizer_of_central h𝒦 hX (hZ X hX) eA hHS hHp hYH hYc hwY)
  have hHne : barX p M S ≠ ⊥ := by
    haveI := nontrivial_of_isQuasisimple hHq
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  obtain ⟨φ, hφ⟩ := exists_surj_of_perfect h𝒦 hZ hA hHS hHp hHne
  have hker : φ.ker ≤ Subgroup.center ↥(barX p M S) := by
    rcases quasisimple_normal hHq φ.normal_ker with h1 | h1
    · exfalso
      have hφ1 : ∀ x, φ x = 1 := fun x => (MonoidHom.mem_ker).1 (h1 ▸ Subgroup.mem_top x)
      have hsurj1 : ∀ a : ↥(alternatingGroup (Fin 5)), a = 1 := fun a => by
        obtain ⟨x, rfl⟩ := hφ a
        exact hφ1 x
      have h60 := card_alt_five
      have : Nat.card ↥(alternatingGroup (Fin 5)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hsurj1 a).trans (hsurj1 b).symm⟩, ⟨1⟩⟩
      omega
    · exact h1
  obtain ⟨eH⟩ := Lemma1311.iso_of_hom hHZ φ hφ hker
  obtain ⟨K, hKc⟩ := exists_pComp_istar hp hSI (Input183.glaPComponent_ne_bot' hS)
  obtain ⟨fK⟩ := h139b.2 K hKc
  exact ⟨K, hKc, ⟨(e1.trans eH).trans fK.symm⟩⟩

end CaseB

section CaseA

variable {G : Type} [Group G] [Finite G]

theorem elemAbelian_zpowers {X : Type*} [Group X] {p : ℕ} {x : X} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem gap1311Iso_caseA (hPi : InputPiCenter) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) (h139a : Prop139a p M D) {d : G} (hd : d ∈ D) {J : Subgroup G}
    (hJ : GLAPComponent p (piLayer p (Istar p M D ⊓ Cg d)) J) :
    ∃ K : Subgroup G, GLAPComponent p (Istar p M D) K ∧ Nonempty (barOf p J ≃* barOf p K) := by
  have hp : p.Prime := GLStanding.prime h.standing
  have hp2 : p ≠ 2 := GLStanding.ne_two h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := h139a.1
  obtain ⟨S, hS, hPiS, hJS⟩ := Lemma1311.pComp_piLayer_summand hp hJ
  rw [hJS]
  have hIc : GLAPComponent p (Istar p M D) (Istar p M D) := Lemma1313i.istar_component_self_of_a h139a
  obtain ⟨hK1, hcen, hT, -, hpiX⟩ := Lemma1311.comp_data hp (by omega)
    OmegaFacts.inputOmegaDvd1311_holds (Or.inl h139a) hIc
  have hIM : Istar p M D ≤ M := istar_le_M p M D
  have hIsn : IsSubnormal (Istar p M D) M := istar_isSubnormal p M D
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hdM : d ∈ M := hAM (h.hD.1 hd)
  have hdpow : d ^ p = 1 := h.hD.2.1.2 d hd
  have hdI : d ∈ Subgroup.normalizer (Istar p M D : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 (istar_conj_eq p hdM)
  have hdp : IsPGroup p (Subgroup.zpowers d) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hdpow) with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  have hSM : S ≤ M := hS.1.trans (inf_le_left.trans hIM)
  have hcent := barX_inf_centralizer hp hdM hIM hdI hdp
  have hHc : GLAPComponent p (barX p M (Istar p M D) ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
      (barX p M S) := by
    have := Prop115b.barX_glaPComponent_of_le hp (inf_le_left.trans hIM) hS
    rwa [hcent] at this
  haveI hsX : IsSimpleGroup ↥(barX p M (Istar p M D)) := by
    haveI : IsSimpleGroup
        (↥(barX p M (Istar p M D)) ⧸ Subgroup.center ↥(barX p M (Istar p M D))) := hK1.2.2.2
    exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have e1 := Prop126b.barOfBarX hp hSM
  by_cases hdc : barX p M (Istar p M D) ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M))
  · rw [inf_eq_left.2 hdc] at hHc
    rcases eq_bot_or_eq_of_isSubnormal_of_simple hsX hHc.2.1 with hb | heq
    · exact absurd hb (Input183.glaPComponent_ne_bot' hHc)
    · refine ⟨Istar p M D, hIc, ⟨?_⟩⟩
      rw [heq] at e1
      exact e1.trans ((QuotientGroup.quotientMulEquivOfEq hpiX.2.1).trans
        (QuotientGroup.quotientBot.trans (Lemma1311.barXIso hp hIM hIsn)))
  · exfalso
    set X := barX p M (Istar p M D) with hXdef
    set db : ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ with hdb
    have hHX : barX p M S ≤ X := hHc.1.trans inf_le_left
    have hHd : barX p M S ≤ Subgroup.centralizer ({db} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
      hHc.1.trans inf_le_right
    have hnh : ¬ IsHatSeven (barOf p S) := by
      rintro ⟨-, h3, -⟩
      have hcop : Nat.Coprime p (Nat.card (Subgroup.center (barOf p S))) := by
        rw [h3]
        exact (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
      have hle : Subgroup.center (barOf p S) ≤ GLAPPrimeCore p (barOf p S) :=
        CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcop
      rw [hPiS.2.1, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at h3
      omega
    have hZS : Subgroup.center (barOf p S) = ⊥ := hPi _ p hp hp2 hPiS hnh
    haveI : Nontrivial (barOf p S) := nontrivial_of_isQuasisimple hPiS.1
    have hpS : p ∣ Nat.card (barOf p S) := Lemma137.dvd_card_of_pPrimeCore_eq_bot hp hPiS.2.1
    have hpH : p ∣ Nat.card ↥(barX p M S) := by
      rw [Nat.card_congr e1.toEquiv] at hpS
      exact hpS.trans (Subgroup.card_quotient_dvd_card _)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barX p M S)) p hpH
    have hyX : (y : ↥M ⧸ GLAPPrimeCore p ↥M) ∈ X := hHX y.2
    have hyd : (y : ↥M ⧸ GLAPPrimeCore p ↥M) * db = db * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (hHd y.2)
    have hyp' : y ^ p = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    have hdbN : db ∈ Subgroup.normalizer (X : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      rw [mem_normalizer_iff_gLBConj_eq, hdb, hXdef, ← barX_gLBConj_eq p hdM, istar_conj_eq p hdM]
    have hyN : (y : ↥M ⧸ GLAPPrimeCore p ↥M) ∈ Subgroup.normalizer (X : Set _) :=
      Subgroup.le_normalizer hyX
    have hker : ∀ g : ↥(Subgroup.normalizer (X : Set (↥M ⧸ GLAPPrimeCore p ↥M))),
        X.normalizerMonoidHom g = 1 → (g : ↥M ⧸ GLAPPrimeCore p ↥M) ∈ Subgroup.centralizer (X : Set _) := by
      intro g hg
      have : g ∈ X.normalizerMonoidHom.ker := hg
      rw [Subgroup.normalizerMonoidHom_ker] at this
      exact Subgroup.mem_subgroupOf.1 this
    obtain ⟨a, ha⟩ : ∃ a, a = X.normalizerMonoidHom ⟨y, hyN⟩ := ⟨_, rfl⟩
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = X.normalizerMonoidHom ⟨db, hdbN⟩ := ⟨_, rfl⟩
    have hcomm : a * δ = δ * a := by
      rw [ha, hδ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hyd
    have hap : a ^ p = 1 := by
      rw [ha, ← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (X : Set (↥M ⧸ GLAPPrimeCore p ↥M)))) ^ p = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hyp')
      rw [this, map_one]
    have hdbp : db ^ p = 1 := by
      rw [hdb, ← map_pow]
      have : (⟨d, hdM⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hdpow)
      rw [this, map_one]
    have hδp : δ ^ p = 1 := by
      rw [hδ, ← map_pow]
      have : (⟨db, hdbN⟩ : ↥(Subgroup.normalizer (X : Set (↥M ⧸ GLAPPrimeCore p ↥M)))) ^ p = 1 :=
        Subtype.ext (by simpa using hdbp)
      rw [this, map_one]
    have ha1 : a ≠ 1 := by
      intro h1
      rw [ha] at h1
      have hyC := hker _ h1
      have : (⟨y, hyX⟩ : ↥X) ∈ Subgroup.center ↥X := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 hyC g g.2
      rw [hcen, Subgroup.mem_bot] at this
      have h2 : (y : ↥M ⧸ GLAPPrimeCore p ↥M) = 1 := congrArg Subtype.val this
      have hy1 : y = 1 := Subtype.ext h2
      rw [hy1, orderOf_one] at hy
      exact hp.one_lt.ne hy
    have hE := CFSG.Open.IsElemAbelian.sup_of_commute (elemAbelian_zpowers hap)
      (elemAbelian_zpowers hδp) (fun u hu v hv => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
        exact ((Commute.zpow_zpow (show Commute a δ from hcomm) i j).eq))
    have hcardE := Inputs71.input7_1Aut_holds p hp (by omega) ↥X hK1.2.2 hcen hT _ hE
    have hordA : orderOf a = p := orderOf_eq_prime hap ha1
    have heqE : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers δ :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hordA]; exact hcardE)
    have hδa : δ ∈ Subgroup.zpowers a := heqE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers δ)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hδa
    have hzN : ((y ^ k : ↥(barX p M S)) : ↥M ⧸ GLAPPrimeCore p ↥M) ∈
        Subgroup.normalizer (X : Set _) := Subgroup.le_normalizer (hHX (y ^ k).2)
    have hak : a ^ k = X.normalizerMonoidHom ⟨(y ^ k : ↥(barX p M S)), hzN⟩ := by
      rw [ha, ← map_zpow]
      congr 1
    have hc : db * ((y ^ k : ↥(barX p M S)) : ↥M ⧸ GLAPPrimeCore p ↥M)⁻¹ ∈
        Subgroup.centralizer (X : Set _) := by
      have h1 : X.normalizerMonoidHom (⟨db, hdbN⟩ * ⟨(y ^ k : ↥(barX p M S)), hzN⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hδ, ← hk, hak, mul_inv_cancel]
      exact hker _ h1
    have hz1 : y ^ k ≠ 1 := by
      intro h1
      rw [h1] at hc
      simp only [OneMemClass.coe_one, inv_one, mul_one] at hc
      apply hdc
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hc x hx
    have hzp : (y ^ k) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp', one_zpow]
    have hzc : ∀ g : ↥(barX p M S), g * y ^ k = y ^ k * g := by
      intro g
      apply Subtype.ext
      have c1 : Commute (g : ↥M ⧸ GLAPPrimeCore p ↥M)
          (db * ((y ^ k : ↥(barX p M S)) : ↥M ⧸ GLAPPrimeCore p ↥M)⁻¹) :=
        Subgroup.mem_centralizer_iff.1 hc g (hHX g.2)
      have c2 : Commute (g : ↥M ⧸ GLAPPrimeCore p ↥M) db :=
        Subgroup.mem_centralizer_singleton_iff.1 (hHd g.2)
      have c3 := c1.inv_right.mul_right c2
      have hz' : (db * ((y ^ k : ↥(barX p M S)) : ↥M ⧸ GLAPPrimeCore p ↥M)⁻¹)⁻¹ * db =
          ((y ^ k : ↥(barX p M S)) : ↥M ⧸ GLAPPrimeCore p ↥M) := by group
      rw [hz'] at c3
      simpa only [Subgroup.coe_mul] using c3.eq
    have hwc : QuotientGroup.mk' (GLAPPrimeCore p ↥(barX p M S)) (y ^ k) ∈
        Subgroup.center (↥(barX p M S) ⧸ GLAPPrimeCore p ↥(barX p M S)) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
      rw [← map_mul, ← map_mul, hzc g]
    have hw1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(barX p M S)) (y ^ k) ≠ 1 := by
      intro h1
      have hzO : y ^ k ∈ GLAPPrimeCore p ↥(barX p M S) := (QuotientGroup.eq_one_iff _).1 h1
      have hord : orderOf (⟨y ^ k, hzO⟩ : ↥(GLAPPrimeCore p ↥(barX p M S))) = p := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_eq_prime hzp hz1
      have hdiv := orderOf_dvd_natCard (⟨y ^ k, hzO⟩ : ↥(GLAPPrimeCore p ↥(barX p M S)))
      rw [hord] at hdiv
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card hdiv
    have hwc' : e1.symm (QuotientGroup.mk' (GLAPPrimeCore p ↥(barX p M S)) (y ^ k)) ∈
        Subgroup.center (barOf p S) := by
      rw [Subgroup.mem_center_iff]
      intro q
      apply e1.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hwc (e1 q)
    rw [hZS, Subgroup.mem_bot] at hwc'
    exact hw1 (by simpa using congrArg e1 hwc')

theorem gap1311Iso_of_inputs (hPi : InputPiCenter) : Lemma1311.Gap1311Iso := by
  intro G _ _ m p B M E A D T h h139 d hd _ _ J hJ
  rcases h139 with h139a | h139b
  · exact gap1311Iso_caseA hPi h h139a hd hJ
  · exact gap1311Iso_caseB h h139b hJ

end CaseA

section I2710

variable {X : Type} [Group X] [Finite X]

@[expose] def Type2710Classical (p : ℕ) (J : Subgroup X) : Prop :=
  (∃ n : ℕ, Nonempty (↥J ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
      (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
    (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J ∧ HasFixedPointFreeOrder ε n p)

@[expose] def Type2710 (p : ℕ) (J : Subgroup X) : Prop :=
  (∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J) ∨
    Type2710Classical p J

@[expose] def InputI2710Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (J F : Subgroup X),
    p ∣ Nat.card ↥J → Type2710Classical p J → F ≤ J → IsElemAbelian p F →
    CFSG.Open.pRank p F = CFSG.Open.pRank p J → 3 ≤ CFSG.Open.pRank p J →
    ∃ F₀ : Subgroup X, F₀ ≤ F ∧ Nat.card F = p ^ 2 * Nat.card ↥F₀ ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (F₀ : Set X)) ≠ ⊥

theorem glaPLayer_ne_bot_of_simple {p : ℕ} (hp : p.Prime) {J : Subgroup X} (hs : IsSimpleGroup ↥J)
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) (hpJ : p ∣ Nat.card ↥J) : GLAPLayer p J ≠ ⊥ := by
  have hZ : Subgroup.center ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  have hq : CFSG.Open.IsQuasisimple ↥J := by
    refine ⟨OmegaFacts.commutator_eq_top_of_simple_of_center_bot hZ, ?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup
  have hc := CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hq
    (OmegaFacts.pPrimeCore_eq_bot_of_simple hp hpJ)
  intro hb
  have hJ : J ≤ GLAPLayer p J := le_sSup hc
  rw [hb, le_bot_iff] at hJ
  subst hJ
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2,
    Subgroup.mem_bot.1 b.2]))

theorem isSimpleGroup_of_type2710 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup X}
    (hpJ : p ∣ Nat.card ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a) (htype : Type2710 p J) :
    IsSimpleGroup ↥J := by
  rcases htype with ⟨k, hk, ⟨e⟩⟩ | ⟨k, ⟨e⟩⟩ | ⟨n, ⟨e⟩⟩ | ⟨ε, n, hn, hΩ, hfp⟩
  · haveI : IsSimpleGroup (alternatingGroup (Fin (k * p))) :=
      alternatingGroup.isSimpleGroup (by simpa using hk)
    exact e.isSimpleGroup
  · have hk : 5 ≤ k * p + 2 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        subst h0
        haveI : Nontrivial (Fin (0 * p + 2)) := Fin.nontrivial_iff_two_le.2 (by omega)
        have h2 := two_mul_nat_card_alternatingGroup (α := Fin (0 * p + 2))
        rw [Nat.card_eq_fintype_card (α := Equiv.Perm _), Fintype.card_perm, Fintype.card_fin] at h2
        simp only [zero_mul, zero_add, Nat.factorial_two] at h2
        rw [Nat.card_congr e.toEquiv] at hpJ
        have h1 : Nat.card ↥(alternatingGroup (Fin (0 * p + 2))) = 1 := by omega
        rw [h1] at hpJ
        exact hp.one_lt.ne' (Nat.dvd_one.1 hpJ)
      · have := Nat.mul_le_mul h0 (show 3 ≤ p by have := hp.two_le; omega)
        omega
    haveI : IsSimpleGroup (alternatingGroup (Fin (k * p + 2))) :=
      alternatingGroup.isSimpleGroup (by simpa using hk)
    exact e.isSimpleGroup
  ·
    set S := StatedSp n (ZMod 2) with hS
    have e1 : ↥J ≃* ↥(commutator ↥S) :=
      (e.trans (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator S).symm)).trans
        (Subgroup.equivMapOfInjective (commutator ↥S) S.subtype S.subtype_injective).symm
    obtain ⟨a, b, hab⟩ := hnab
    have hCnab : ∃ u v : ↥(commutator ↥S), u * v ≠ v * u :=
      ⟨e1 a, e1 b, fun h => hab (e1.injective (by rw [map_mul, map_mul, h]))⟩
    have hpC : p ∣ Nat.card ↥(commutator ↥S) := by rwa [← Nat.card_congr e1.toEquiv]
    suffices hs : IsSimpleGroup ↥(commutator ↥S) from e1.isSimpleGroup
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h0 | h1 | h2 | h3
    · exfalso
      subst h0
      haveI := OmegaFacts.subsingleton_statedSp_zero
      obtain ⟨u, v, huv⟩ := hCnab
      exact huv (Subtype.ext (Subsingleton.elim _ _))
    · exfalso
      subst h1
      have h6 : Nat.card ↥S = 6 := by
        rw [hS, OmegaFacts.card_statedSp_zmod_two]
        decide
      have hne : commutator ↥S ≠ ⊤ := by
        intro htop
        haveI : Nontrivial ↥S := by
          rw [← Finite.one_lt_card_iff_nontrivial, h6]
          norm_num
        have hsolv : Group.IsSolvable ↥S :=
          CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
            (by rw [h6]; decide +kernel)
        exact OmegaFacts.not_isSolvable_of_perfect htop hsolv
      have hlt : Nat.card ↥(commutator ↥S) < 6 := by
        have := card_lt_of_lt' (lt_top_iff_ne_top.2 hne)
        rwa [Subgroup.card_top, h6] at this
      have hdvd : Nat.card ↥(commutator ↥S) ∣ 6 := by
        rw [← h6]
        exact Subgroup.card_subgroup_dvd_card _
      have h3 : Nat.card ↥(commutator ↥S) = 3 := by
        have hpos : 0 < Nat.card ↥(commutator ↥S) := Nat.card_pos
        interval_cases h : Nat.card ↥(commutator ↥S)
        · exact absurd (Nat.dvd_one.1 hpC) hp.one_lt.ne'
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpC) hp2
        · rfl
        · norm_num at hdvd
        · norm_num at hdvd
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      haveI : IsCyclic ↥(commutator ↥S) := isCyclic_of_prime_card h3
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(commutator ↥S))
      obtain ⟨u, v, huv⟩ := hCnab
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg u)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg v)
      exact huv ((Commute.refl g).zpow_zpow i j).eq
    · subst h2
      obtain ⟨e0⟩ := OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
      have hmap : (commutator ↥S).map e0.toMonoidHom = alternatingGroup (Fin 6) := by
        rw [_root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ e0.surjective, ← _root_.commutator_def,
          alternatingGroup.commutator_perm_eq (by simp)]
      haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((Subgroup.equivMapOfInjective (commutator ↥S) e0.toMonoidHom e0.injective).trans
        (MulEquiv.subgroupCongr hmap)).isSimpleGroup
    · haveI : IsSimpleGroup ↥S := OmegaFacts.isSimpleGroup_statedSp_zmod_two h3
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥S) with hb | htop
      · exfalso
        obtain ⟨u, v, huv⟩ := hCnab
        have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.1 (hb ▸ u.2))
        have hv : v = 1 := Subtype.ext (Subgroup.mem_bot.1 (hb ▸ v.2))
        rw [hu, hv] at huv
        exact huv rfl
      · exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup
  · cases ε with
    | false =>
      obtain ⟨f⟩ := hΩ
      haveI := CFSG.ComponentClassification.RankTwoClassical.ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le
        (K := ZMod 2) (b := 1) (c := 1) (m := n + 1) (by omega) (by decide)
      exact f.isSimpleGroup
    | true =>
      have hn2 : 2 ≤ n := by
        rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
        · exact absurd hfp (CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2)
        · exact h2
      obtain ⟨f⟩ := hΩ
      haveI := CFSG.ComponentClassification.RankTwoClassical.ORigid.isSimpleGroup_statedOmega_quadPlus_of_three_le
        (K := ZMod 2) (k := n + 1) (by omega)
      exact f.isSimpleGroup

theorem card_eq_pow_pRank {p : ℕ} (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E) :
    Nat.card E = p ^ CFSG.Open.pRank p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hk
  have h2 : CFSG.Open.pRank p E ≤ k := CFSG.SectionRank.pRank_le hp.one_lt fun F hFE _ =>
    hk ▸ Subgroup.card_le_of_le hFE
  rw [hk, le_antisymm h1 h2]

theorem apply_eq_of_mem_orbit {Ω : Type} {R : Subgroup (Equiv.Perm Ω)}
    (hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) {v : Equiv.Perm Ω} (hv : v ∈ R) {ω : Ω}
    (hvω : v ω = ω) {x : Ω} (hx : x ∈ MulAction.orbit R ω) : v x = x := by
  obtain ⟨g, rfl⟩ := hx
  show v ((g : Equiv.Perm Ω) ω) = (g : Equiv.Perm Ω) ω
  rw [← Equiv.Perm.mul_apply, hRcomm v hv g g.2, Equiv.Perm.mul_apply, hvω]

theorem card_orbit_eq_of_moved {Ω : Type} [Finite Ω] {p : ℕ} [hp : Fact p.Prime]
    {R : Subgroup (Equiv.Perm Ω)} (hR : IsPGroup p R) {g : Equiv.Perm Ω} (hg : g ∈ R) {ω : Ω}
    (hgω : g ω ≠ ω) (hle : Nat.card (MulAction.orbit R ω) ≤ p) :
    Nat.card (MulAction.orbit R ω) = p := by
  obtain ⟨t, ht⟩ := hR.card_orbit ω
  have h2 : 2 ≤ Nat.card (MulAction.orbit R ω) := by
    have hsub : ({ω, g ω} : Set Ω) ⊆ MulAction.orbit R ω := by
      intro x hx
      rcases hx with rfl | hx
      · exact MulAction.mem_orbit_self x
      · rw [Set.mem_singleton_iff.1 hx]
        exact MulAction.mem_orbit ω (⟨g, hg⟩ : R)
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair (Ne.symm hgω), ← Nat.card_coe_set_eq] at h3
  rw [ht] at h2 hle ⊢
  rcases t with _ | _ | t
  · simp at h2
  · simp
  · exfalso
    have h5 : p ^ 2 ≤ p ^ (t + 1 + 1) := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h6 : p < p ^ 2 := by have := hp.out.two_le; nlinarith
    omega

theorem exists_moved {Ω : Type} {R : Subgroup (Equiv.Perm Ω)} (hR : R ≠ ⊥) :
    ∃ g ∈ R, ∃ ω : Ω, g ω ≠ ω := by
  by_contra h
  push Not at h
  exact hR ((Subgroup.eq_bot_iff_forall R).2 fun g hg => Equiv.ext fun a => by
    rw [Equiv.Perm.one_apply]
    exact h g hg a)

theorem core_alt {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J F : Subgroup X}
    (e : ↥J ≃* alternatingGroup (Fin n)) (hFJ : F ≤ J) (hF : IsElemAbelian p F)
    (hrk : CFSG.Open.pRank p F = CFSG.Open.pRank p J) (h3 : 3 ≤ CFSG.Open.pRank p J) :
    ∃ F₀ : Subgroup X, F₀ ≤ F ∧ Nat.card F = p ^ 2 * Nat.card ↥F₀ ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (F₀ : Set X)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  let φ : ↥J →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := (Subgroup.subtype_injective _).comp e.injective
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup (Equiv.Perm (Fin n)), R = (F.subgroupOf J).map φ := ⟨_, rfl⟩
  have hRel : IsElemAbelian p R := by
    rw [hRdef]
    exact CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hF J) φ
  have hRF : Nat.card R = Nat.card F := by
    rw [hRdef, Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFJ).toEquiv]
  have hRcard : Nat.card R = p ^ CFSG.Open.pRank p J := by
    rw [hRF, card_eq_pow_pRank hp hF, hrk]
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hRel hx hy
  have hRp : IsPGroup p R := CFSG.Open.IsElemAbelian.isPGroup hRel
  have horb := Claims138.card_orbit_le_of_rank hp hp3 hRel hRcard
    (Claims138.le_pRank_of_mulEquiv_alt hp hp2 e)
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p J ≠ 0) hp.one_lt
    omega
  obtain ⟨g₀, hg₀, ω₀, hω₀⟩ := exists_moved hRne
  have hO₀ : Nat.card (MulAction.orbit R ω₀) = p := card_orbit_eq_of_moved hRp hg₀ hω₀ (horb ω₀)
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀, R₀ = GL83.PiGen.stabIn R ω₀ := ⟨_, rfl⟩
  have hR₀R : R₀ ≤ R := by
    rw [hR₀def]
    exact GL83.PiGen.stabIn_le R ω₀
  have hR₀fix : ∀ v ∈ R₀, v ω₀ = ω₀ := fun v hv => by
    rw [hR₀def] at hv
    exact GL83.PiGen.mem_fixSet_stabIn R ω₀ v hv
  have hRR₀ : Nat.card R = p * Nat.card R₀ := by
    rw [GL83.PiGen.card_mul_card_stabIn R ω₀, hO₀, hR₀def]
  have hR₀ne : R₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, mul_one, hRcard] at hRR₀
    have h5 : p ^ 2 ≤ p ^ CFSG.Open.pRank p J := Nat.pow_le_pow_right hp.pos (by omega)
    have h6 : p < p ^ 2 := by nlinarith
    omega
  obtain ⟨g₁, hg₁, ω₁, hω₁⟩ := exists_moved hR₀ne
  have hO₁ : Nat.card (MulAction.orbit R ω₁) = p :=
    card_orbit_eq_of_moved hRp (hR₀R hg₁) hω₁ (horb ω₁)
  have hsub₁ : MulAction.orbit R₀ ω₁ ⊆ MulAction.orbit R ω₁ := by
    rintro x ⟨g, rfl⟩
    exact ⟨⟨g, hR₀R g.2⟩, rfl⟩
  have hO₀₁ : Nat.card (MulAction.orbit R₀ ω₁) = p :=
    card_orbit_eq_of_moved (hRp.to_le hR₀R) hg₁ hω₁
      ((Nat.card_mono (Set.toFinite _) hsub₁).trans hO₁.le)
  obtain ⟨V, hVdef⟩ : ∃ V, V = GL83.PiGen.stabIn R₀ ω₁ := ⟨_, rfl⟩
  have hVR₀ : V ≤ R₀ := by
    rw [hVdef]
    exact GL83.PiGen.stabIn_le R₀ ω₁
  have hVfix₁ : ∀ v ∈ V, v ω₁ = ω₁ := fun v hv => by
    rw [hVdef] at hv
    exact GL83.PiGen.mem_fixSet_stabIn R₀ ω₁ v hv
  have hR₀V : Nat.card R₀ = p * Nat.card V := by
    rw [GL83.PiGen.card_mul_card_stabIn R₀ ω₁, hO₀₁, hVdef]
  set s : Finset (Fin n) := Finset.univ.filter fun ω => ∀ v ∈ V, v ω = ω with hs
  have hs_mem : ∀ ω, ω ∈ s ↔ ∀ v ∈ V, v ω = ω := fun ω => by simp [hs]
  have horb₀s : MulAction.orbit R ω₀ ⊆ (s : Set (Fin n)) := fun x hx =>
    (hs_mem x).2 fun v hv => apply_eq_of_mem_orbit hRcomm (hR₀R (hVR₀ hv)) (hR₀fix v (hVR₀ hv)) hx
  have horb₁s : MulAction.orbit R ω₁ ⊆ (s : Set (Fin n)) := fun x hx =>
    (hs_mem x).2 fun v hv => apply_eq_of_mem_orbit hRcomm (hR₀R (hVR₀ hv)) (hVfix₁ v hv) hx
  have hω₁ₙ : ω₁ ∉ MulAction.orbit R ω₀ := fun h =>
    hω₁ (apply_eq_of_mem_orbit hRcomm (hR₀R hg₁) (hR₀fix g₁ hg₁) h)
  have hdisj : Disjoint (MulAction.orbit R ω₀) (MulAction.orbit R ω₁) := by
    rcases MulAction.orbit.eq_or_disjoint (G := ↥R) ω₀ ω₁ with h | h
    · exfalso
      apply hω₁ₙ
      rw [h]
      exact MulAction.mem_orbit_self ω₁
    · exact h
  have hscard : 2 * p ≤ s.card := by
    have h1 : (MulAction.orbit R ω₀ ∪ MulAction.orbit R ω₁).ncard = p + p := by
      rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ← Nat.card_coe_set_eq,
        ← Nat.card_coe_set_eq, hO₀, hO₁]
    have h2 := Set.ncard_le_ncard (Set.union_subset horb₀s horb₁s) (Set.toFinite _)
    rw [Set.ncard_coe_finset, h1] at h2
    omega
  set W : Subgroup ↥J := V.comap φ ⊓ F.subgroupOf J with hW
  have hWmap : W.map φ = V := by
    refine le_antisymm (fun x hx => ?_) (fun v hv => ?_)
    · obtain ⟨w, hw, rfl⟩ := hx
      exact (Subgroup.mem_inf.1 hw).1
    · have hvR : v ∈ R := hR₀R (hVR₀ hv)
      rw [hRdef] at hvR
      obtain ⟨t, ht, htv⟩ := hvR
      refine ⟨t, Subgroup.mem_inf.2 ⟨?_, ht⟩, htv⟩
      rw [Subgroup.mem_comap, htv]
      exact hv
  refine ⟨W.map J.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hw).2
  · rw [Subgroup.card_map_of_injective J.subtype_injective, ← hRF, hRR₀, hR₀V, ← hWmap,
      Subgroup.card_map_of_injective hφ]
    ring
  set L : Subgroup X := GL83.PiGen.subAlt e (s : Set (Fin n)) with hL
  have hLC : L ≤ Subgroup.centralizer ((W.map J.subtype : Subgroup X) : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hφw : φ w ∈ V := (Subgroup.mem_inf.1 hw).1
    exact (GL83.PiGen.implements_of_mem e w.2).comm_of_mem_subAlt
      (fun ω hω => (hs_mem ω).1 hω (φ w) hφw) hx
  have hLle : L ≤ J ⊓ Subgroup.centralizer ((W.map J.subtype : Subgroup X) : Set X) :=
    le_inf (GL83.PiGen.subAlt_le e _) hLC
  have hLn : (L.subgroupOf (J ⊓ Subgroup.centralizer ((W.map J.subtype : Subgroup X) : Set X))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLle]
    intro x g hx hg
    obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.1 hg
    have hcommV : ∀ v ∈ V, v * φ ⟨g, hgJ⟩ = φ ⟨g, hgJ⟩ * v := by
      intro v hv
      rw [← hWmap] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hc : (w : X) * g = g * (w : X) :=
        Subgroup.mem_centralizer_iff.1 hgC _ (Subgroup.mem_map_of_mem J.subtype hw)
      have hc' : w * ⟨g, hgJ⟩ = ⟨g, hgJ⟩ * w := Subtype.ext hc
      rw [← map_mul φ, ← map_mul φ, hc']
    refine (GL83.PiGen.implements_of_mem e hgJ).mem_subAlt_conj (fun ω => ?_) hx
    show φ ⟨g, hgJ⟩ ω ∈ s ↔ ω ∈ s
    rw [hs_mem, hs_mem]
    constructor
    · intro h v hv
      apply (φ ⟨g, hgJ⟩).injective
      rw [← Equiv.Perm.mul_apply, ← hcommV v hv, Equiv.Perm.mul_apply, h v hv]
    · intro h v hv
      rw [← Equiv.Perm.mul_apply, hcommV v hv, Equiv.Perm.mul_apply, h v hv]
  have hsn : Nat.card ↥s = s.card := Nat.card_eq_finsetCard s
  let eL : ↥L ≃* alternatingGroup ↥s :=
    (GL83.PiGen.subAltEquiv e (s : Set (Fin n))).trans (GL83.PiGen.altOnEquiv s)
  haveI : IsSimpleGroup (alternatingGroup ↥s) := alternatingGroup.isSimpleGroup (by omega)
  haveI : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hZ : Subgroup.center (alternatingGroup ↥s) = ⊤ :=
      eq_top_iff.2 fun a _ => Subgroup.mem_center_iff.2 fun b => by
        apply eL.symm.injective
        rw [map_mul, map_mul]
        exact hc _ _
    rw [alternatingGroup.center_eq_bot (by omega)] at hZ
    haveI : Nontrivial (alternatingGroup ↥s) :=
      alternatingGroup.nontrivial_of_three_le_card (by omega)
    exact bot_ne_top hZ
  have hpL : p ∣ Nat.card ↥L := by
    rw [Nat.card_congr eL.toEquiv]
    haveI : Nontrivial ↥s := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have h2 := two_mul_nat_card_alternatingGroup (α := ↥s)
    rw [Nat.card_perm, hsn] at h2
    have hdvd : p ∣ Nat.factorial s.card := Nat.dvd_factorial hp.pos (by omega)
    rw [← h2] at hdvd
    exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hdvd
  have hcomp := GL83.PiGen.glaPComponent_of_normal_simple hp hLle hLn hnab hpL
  intro hb
  have hLb : L ≤ GLAPLayer p (J ⊓ Subgroup.centralizer ((W.map J.subtype : Subgroup X) : Set X)) :=
    le_sSup hcomp
  rw [hb] at hLb
  obtain ⟨a, b, hab⟩ := hnab
  have ha : (a : X) = 1 := Subgroup.mem_bot.1 (hLb a.2)
  have hb' : (b : X) = 1 := Subgroup.mem_bot.1 (hLb b.2)
  exact hab (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb']))

theorem core_of_input (hC : InputI2710Core) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J F : Subgroup X}
    (hpJ : p ∣ Nat.card ↥J) (htype : Type2710 p J) (hFJ : F ≤ J) (hF : IsElemAbelian p F)
    (hrk : CFSG.Open.pRank p F = CFSG.Open.pRank p J) (h3 : 3 ≤ CFSG.Open.pRank p J) :
    ∃ F₀ : Subgroup X, F₀ ≤ F ∧ Nat.card F = p ^ 2 * Nat.card ↥F₀ ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (F₀ : Set X)) ≠ ⊥ := by
  rcases htype with ⟨k, -, ⟨e⟩⟩ | ⟨k, ⟨e⟩⟩ | hcl
  · exact core_alt hp hp2 e hFJ hF hrk h3
  · exact core_alt hp hp2 e hFJ hF hrk h3
  · exact hC X p hp hp2 J F hpJ hcl hFJ hF hrk h3

theorem inputI2710_of_core (hC : InputI2710Core) : InputI2710 := by
  intro X _ _ p hp hp2 J B hpJ htype hB hBN hsup hinf hrank h2
  haveI : Fact p.Prime := ⟨hp⟩
  have hFel : IsElemAbelian p (B ⊓ J) := isElemAbelian_mono hB inf_le_left
  have hCel : IsElemAbelian p (B ⊓ Subgroup.centralizer (J : Set X)) := isElemAbelian_mono hB inf_le_left
  have hcomm : ∀ x ∈ B ⊓ J, ∀ y ∈ B ⊓ Subgroup.centralizer (J : Set X), x * y = y * x :=
    fun x hx y hy => CFSG.Open.IsElemAbelian.comm hB hx.1 hy.1
  have hcard : Nat.card B = Nat.card ↥(B ⊓ J) * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    rw [hsup, hinf, Subgroup.card_bot, mul_one] at this
    exact this
  have hFcard : Nat.card ↥(B ⊓ J) = p ^ CFSG.Open.pRank p J := by
    rw [← hrank]
    exact card_eq_pow_pRank hp hFel
  have hBcard : Nat.card B = p ^ CFSG.Open.pRank p B := card_eq_pow_pRank hp hB
  have hr1 : 1 ≤ CFSG.Open.pRank p J := by
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) p hpJ
    have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hE : IsElemAbelian p (Subgroup.zpowers (g : X)) :=
      elemAbelian_zpowers (by simpa using congrArg Subtype.val hgp)
    have hcardg : Nat.card (Subgroup.zpowers (g : X)) = p ^ 1 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg, pow_one]
    exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.2 g.2) hE hcardg
  have hnab : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcon
    have hFC : B ⊓ J ≤ B ⊓ Subgroup.centralizer (J : Set X) := fun x hx => by
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
      by_contra hne
      exact hcon ⟨⟨j, hj⟩, ⟨x, hx.2⟩, fun h => hne (congrArg Subtype.val h)⟩
    have hbot : B ⊓ J = ⊥ := by
      rw [← inf_eq_left.2 hFC]
      exact hinf
    rw [hbot, Subgroup.card_bot] at hFcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p J ≠ 0) hp.one_lt
    omega
  have hJs : IsSimpleGroup ↥J := isSimpleGroup_of_type2710 hp hp2 hpJ hnab htype
  have hlayerJ : GLAPLayer p J ≠ ⊥ := glaPLayer_ne_bot_of_simple hp hJs hnab hpJ
  have hJE : ∀ E : Subgroup X, E ≤ B ⊓ Subgroup.centralizer (J : Set X) →
      J ⊓ Subgroup.centralizer (E : Set X) = J := fun E hE => by
    refine inf_eq_left.2 fun j hj => Subgroup.mem_centralizer_iff.2 fun e he => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hE he).2 j hj).symm
  rcases (show CFSG.Open.pRank p J = 1 ∨ CFSG.Open.pRank p J = 2 ∨ 3 ≤ CFSG.Open.pRank p J by
    omega) with h1 | h2' | h3
  ·
    have hCcard : Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) = p ^ (CFSG.Open.pRank p B - 1) := by
      have hpos : 0 < p := hp.pos
      have e1 : p ^ CFSG.Open.pRank p B = p * p ^ (CFSG.Open.pRank p B - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hBcard, hFcard, h1, pow_one, e1] at hcard
      exact (Nat.eq_of_mul_eq_mul_left hpos hcard).symm
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(B ⊓ Subgroup.centralizer (J : Set X)))
      p (n := CFSG.Open.pRank p B - 2) (by rw [hCcard]; exact pow_dvd_pow p (by omega))
    refine ⟨H.map (B ⊓ Subgroup.centralizer (J : Set X)).subtype,
      (Subgroup.map_subtype_le H).trans inf_le_left, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hH, hBcard]
      rw [← pow_add]
      congr 1
      omega
    · rw [hJE _ (Subgroup.map_subtype_le H)]
      exact hlayerJ
  ·
    refine ⟨B ⊓ Subgroup.centralizer (J : Set X), inf_le_left, ?_, ?_⟩
    · rw [hcard, hFcard, h2']
    · rw [hJE _ le_rfl]
      exact hlayerJ
  ·
    obtain ⟨F₀, hF₀F, hF₀card, hF₀L⟩ := core_of_input hC hp hp2 hpJ htype inf_le_right hFel hrank h3
    refine ⟨F₀ ⊔ (B ⊓ Subgroup.centralizer (J : Set X)),
      sup_le (hF₀F.trans inf_le_left) inf_le_left, ?_, ?_⟩
    · have h0 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F₀
        (B ⊓ Subgroup.centralizer (J : Set X)) (fun x hx y hy => hcomm x (hF₀F hx) y hy)).1
      have hinf0 : F₀ ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥ :=
        le_bot_iff.1 (hinf ▸ inf_le_inf_right _ hF₀F)
      rw [hinf0, Subgroup.card_bot, mul_one] at h0
      rw [hcard, hF₀card, h0]
      ring
    · have hc : J ⊓ Subgroup.centralizer ((F₀ ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) : Subgroup X) :
          Set X) = J ⊓ Subgroup.centralizer (F₀ : Set X) := by
        refine le_antisymm (inf_le_inf_left J
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))) ?_
        intro j hj
        refine ⟨hj.1, ?_⟩
        show j ∈ Subgroup.centralizer _
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        obtain ⟨a, ha, c, hc', rfl⟩ := Lemma137.mem_sup_of_comm
          (fun a ha c hc => hcomm a (hF₀F ha) c hc) x hx
        have h1 : a * j = j * a := Subgroup.mem_centralizer_iff.1 hj.2 a ha
        have h2 : c * j = j * c := (Subgroup.mem_centralizer_iff.1 hc'.2 j hj.1).symm
        exact (Commute.mul_left h1 h2).eq
      rw [hc]
      exact hF₀L

end I2710

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem pPrime_le_glbCore {p : ℕ} [hp : Fact p.Prime] {A₁ Y : Subgroup G} {s : ℕ}
    (hA₁ : IsElemAbelian p A₁) (hAN : A₁ ≤ Subgroup.normalizer (Y : Set G))
    (hcop : ¬ p ∣ Nat.card ↥Y) (hcard : Nat.card A₁ = p ^ s) (hs : 3 ≤ s) :
    Y ≤ GLBCore p 2 A₁ := by
  classical
  have hnt : Nontrivial ↥A₁ := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.out.one_lt
  letI : MulDistribMulAction ↥A₁ ↥Y := Subgroup.conjMulDistribMulActionOfLeNormalizer A₁ Y hAN
  haveI : CFSG.IsElementaryAbelian p ↥A₁ := CFSG.Open.IsElemAbelian.isElementaryAbelian hA₁
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥A₁) (H := ↥Y) hcop
  have key : ∀ B : Subgroup ↥A₁, B.index = p → ∀ y ∈ CFSG.fixedPointSubgroup B ↥Y,
      (y : G) ∈ GLBCore p 2 A₁ := by
    intro B hB y hy
    set B' : Subgroup G := B.map A₁.subtype with hB'
    have hB'le : B' ≤ A₁ := Subgroup.map_subtype_le B
    have hcomm : ∀ b ∈ B', (y : G) * b = b * (y : G) := by
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      have hfix := (FixedPoints.mem_subgroup _ _ _).mp hy ⟨b', hb'⟩
      have hval : (b' : G) * (y : G) * (b' : G)⁻¹ = (y : G) :=
        congrArg (fun z : ↥Y => (z : G)) hfix
      have h2 : (b' : G) * (y : G) = (y : G) * (b' : G) := by
        calc (b' : G) * (y : G) = ((b' : G) * (y : G) * (b' : G)⁻¹) * (b' : G) := by group
          _ = (y : G) * (b' : G) := by rw [hval]
      exact h2.symm
    have hyN : (y : G) ∈ Subgroup.normalizer (B' : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm b hb).symm
    have hB'ea : IsElemAbelian p B' := isElemAbelian_mono hA₁ hB'le
    have hcardB' : Nat.card B' = p ^ (s - 1) := by
      rw [hB', Subgroup.card_map_of_injective A₁.subtype_injective]
      exact l114_card_hyperplane hcard (by omega) hB
    have hrank : 2 ≤ CFSG.Open.pRank p B' := by
      have h := CFSG.SectionRank.le_pRank hp.out.one_lt (le_refl B') hB'ea hcardB'
      omega
    exact l114_normalizer_le_glbCore hB'le hrank hyN
  have htop : (⊤ : Subgroup ↥Y) ≤ (GLBCore p 2 A₁).comap Y.subtype := by
    rw [← hgen]
    refine iSup₂_le fun B hB => ?_
    intro y hy
    exact key B hB y hy
  intro x hx
  exact htop (Subgroup.mem_top (⟨x, hx⟩ : ↥Y))

@[expose] def KstarOf (p : ℕ) (M D T : Subgroup G) : Subgroup G :=
  ⨆ n ∈ Nof T, GLBConj n (Prop139.KBig p M D T)

@[expose] def InputFrattini139 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G}
    (_ : Sec13 G m p B M E A D T), B ≤ Nof T →
    Nof T ≤ ((GLAPPrimeCoreOf p (KstarOf p M D T) ⊔ Prop139.KBig p M D T) ⊔
        (KstarOf p M D T ⊓ Subgroup.centralizer ((B ⊓ Prop139.KBig p M D T : Subgroup G) : Set G))) ⊔
      (Nof T ⊓ Subgroup.normalizer ((B ⊓ KstarOf p M D T : Subgroup G) : Set G))

theorem frattiniBound_of_inputs (hL137i : Lemma137_iStatement) (hF : InputFrattini139) :
    Prop139.FrattiniBoundStatement := by
  intro G _ _ m p B M E A D T h
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hBc : Nat.card B = p ^ m := by rw [h.bOne.1.2.1, hS.rank_eq]
  have hcore : GLBCore p 2 B ≤ M := h.uniq.clause_d
  have hnorm : ∀ Q : Subgroup G, Q ≤ B → 2 ≤ CFSG.Open.pRank p Q →
      Subgroup.normalizer (Q : Set G) ≤ M := fun Q hQ h2 =>
    (l114_normalizer_le_glbCore hQ h2).trans hcore
  have hKK : Prop139.KBig p M D T ≤ KstarOf p M D T := by
    have h1 := le_iSup₂_of_le (f := fun n (_ : n ∈ Nof T) => GLBConj n (Prop139.KBig p M D T))
      (1 : G) (Nof T).one_mem le_rfl
    rw [gLBConj_one] at h1
    exact h1
  have h2K : 2 ≤ CFSG.Open.pRank p (B ⊓ Prop139.KBig p M D T) := by omega
  have h2Ks : 2 ≤ CFSG.Open.pRank p (B ⊓ KstarOf p M D T) :=
    h2K.trans (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_inf_left B hKK))
  apply h.hN
  have hBN : B ≤ Nof T := hL137i h
  refine (hF h hBN).trans (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_)
  ·
    have hle : ∀ n ∈ Nof T, GLBConj n (KstarOf p M D T) ≤ KstarOf p M D T := by
      intro n hn
      unfold KstarOf
      rw [gLBConj_iSup_eq]
      refine iSup_le fun g => ?_
      rw [gLBConj_iSup_eq]
      refine iSup_le fun hg => ?_
      rw [gLBConj_gLBConj]
      exact le_iSup₂_of_le (f := fun n (_ : n ∈ Nof T) => GLBConj n (Prop139.KBig p M D T))
        (g * n) ((Nof T).mul_mem hg hn) le_rfl
    have hKn : ∀ n ∈ Nof T, GLBConj n (KstarOf p M D T) = KstarOf p M D T := by
      intro n hn
      refine le_antisymm (hle n hn) ?_
      have := gLBConj_mono n (hle n⁻¹ ((Nof T).inv_mem hn))
      rwa [gLBConj_gLBConj_inv] at this
    have hBO : B ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p (KstarOf p M D T) : Subgroup G) : Set G) := by
      intro b hb
      rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, hKn b (hBN hb)]
    exact (pPrime_le_glbCore hBel hBO (not_dvd_card_glaPPrimeCoreOf hp _) hBc
      (by have := hS.four_le; omega)).trans hcore
  ·
    refine iSup₂_le fun L hL => ?_
    exact (Sec13d.derivedInf_le _).trans (inf_le_right.trans (hL.1.1.trans (istar_le_M p M D)))
  · exact (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans (hnorm _ inf_le_left h2K)
  · exact inf_le_right.trans (hnorm _ inf_le_left h2Ks)

end Frattini

section T1

variable {G : Type} [Group G] [Finite G]

theorem B_le_normalizer_L1 (h133 : Lemma133Statement) {m p : ℕ} {B M E A D T R L0 : Subgroup G}
    {d : G} (h : Cex1310 G m p B M E A D T R L0 d) :
    B ≤ Subgroup.normalizer ((L1of p M D L0 : Subgroup G) : Set G) := by
  have hp : p.Prime := GLStanding.prime h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hBM : B ≤ M := Lemma1312b.B_le_M h
  have hdM : d ∈ M := Lemma1312b.d_mem_M h
  have hL1I : L1of p M D L0 ≤ Istar p M D := Lemma1312b.L1_le_istar h
  have hIM := istar_le_M p M D
  obtain ⟨L, hL, hV⟩ := Lemma1312b.orbit_of_cex h133 h
  have hBV : ∀ b (hb : b ∈ B), GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hBM hb⟩)
      (barX p M (L1of p M D L0)) = barX p M (L1of p M D L0) := by
    intro b hb
    rw [hV, gLBConj_iSup_eq]
    refine iSup_congr fun i => ?_
    have hLi : GLAPComponent p (Istar p M D) (GLBConj (d ^ (i : ℕ)) L) :=
      Lemma1312b.istar_comp_conj hp hL (M.pow_mem hdM i)
    have hBN := ((h133 h.toSec13).2 _ hLi).2.1
    rw [← barX_gLBConj_eq p (hBM hb), gLBConj_eq_of_mem_normalizer (hBN hb)]
  have hle : ∀ b ∈ B, GLBConj b (L1of p M D L0) ≤ L1of p M D L0 := by
    intro b hb
    have hbM := hBM hb
    have hbI : GLBConj b (Istar p M D) = Istar p M D := istar_conj_eq p hbM
    have hbar : barX p M (GLBConj b (L1of p M D L0)) = barX p M (L1of p M D L0) := by
      rw [barX_gLBConj_eq p hbM, hBV b hb]
    have key : ∀ y ∈ GLBConj b (L1of p M D L0), (∃ k : ℕ, y ^ p ^ k = 1) → y ∈ L1of p M D L0 := by
      rintro y hy ⟨k, hk⟩
      have hyI : y ∈ Istar p M D := by
        rw [← hbI]
        exact gLBConj_mono b hL1I hy
      have hyM : y ∈ M := hIM hyI
      have hyb : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨y, hyM⟩ ∈ barX p M (L1of p M D L0) := by
        rw [← hbar]
        exact (Lemma1311.mem_barX' p).2 ⟨⟨y, hyM⟩, hy, rfl⟩
      exact Lemma1312b.mem_L1_of_bar h hyI hyM hyb hk
    have hL1eq : GLBConj b (L1of p M D L0) = ⨆ g ∈ Istar p M D, GLBConj (g * b) L0 := by
      unfold L1of
      rw [gLBConj_iSup_eq]
      refine iSup_congr fun g => ?_
      rw [gLBConj_iSup_eq]
      refine iSup_congr fun _ => ?_
      rw [gLBConj_gLBConj]
    have hsub : ∀ g ∈ Istar p M D, GLBConj (g * b) L0 ≤ GLBConj b (L1of p M D L0) := by
      intro g hg
      rw [hL1eq]
      exact le_iSup₂_of_le (f := fun g (_ : g ∈ Istar p M D) => GLBConj (g * b) L0) g hg le_rfl
    rw [hL1eq]
    refine iSup₂_le fun g hg => ?_
    exact Inputs1115.le_of_pElements hp (glaPComponent_gLBConj h.hL0 (g * b))
      fun y hy hyp => key y (hsub g hg hy) hyp
  intro b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (hle b hb) ?_
  have := gLBConj_mono b (hle b⁻¹ (B.inv_mem hb))
  rwa [gLBConj_gLBConj_inv] at this

def a5a : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

def a5b : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

def a5c : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem a5_facts : a5a ^ 2 = 1 ∧ a5b ^ 2 = 1 ∧ a5a * a5b = a5b * a5a ∧ a5a ≠ 1 ∧ a5b ≠ 1 ∧
    a5a ≠ a5b ∧ a5c ^ 3 = 1 ∧ a5c ≠ 1 ∧ a5c * a5a * a5c⁻¹ = a5a * a5b ∧ a5c * a5b * a5c⁻¹ = a5a := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    Subtype.ext ?_, fun h => ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  all_goals first
    | decide
    | (have := congrArg Subtype.val h; revert this; decide)

theorem not_three_dvd_card_sylow_two {X : Type*} [Group X] [Finite X]
    (e : X ≃* ↥(alternatingGroup (Fin 5))) : ¬ 3 ∣ Nat.card (Sylow 2 X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha2, hb2, hab, ha1, hb1, hba, hc3, hc1, hca, hcb⟩ := a5_facts
  have hoa : orderOf a5a = 2 := orderOf_eq_prime ha2 ha1
  have hob : orderOf a5b = 2 := orderOf_eq_prime hb2 hb1
  have hoc : orderOf a5c = 3 := orderOf_eq_prime hc3 hc1
  set V : Subgroup ↥(alternatingGroup (Fin 5)) := Subgroup.zpowers a5a ⊔ Subgroup.zpowers a5b with hV
  have hcomm : ∀ x ∈ Subgroup.zpowers a5a, ∀ y ∈ Subgroup.zpowers a5b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_zpow (show Commute a5a a5b from hab) i j).eq)
  have hinf : Subgroup.zpowers a5a ⊓ Subgroup.zpowers a5b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_bot]
    rw [mem_zpowers_iff_mem_range_orderOf, hoa] at hxa
    rw [mem_zpowers_iff_mem_range_orderOf, hob] at hxb
    simp only [Finset.mem_image, Finset.mem_range] at hxa hxb
    obtain ⟨i, hi, rfl⟩ := hxa
    obtain ⟨j, hj, hji⟩ := hxb
    interval_cases i
    · rfl
    · interval_cases j
      · exact absurd hji.symm (by simpa using ha1)
      · exact absurd hji.symm (by simpa using hba)
  have hV4 : Nat.card V = 4 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hob] at h
    exact h
  have hcN : a5c ∈ Subgroup.normalizer (V : Set ↥(alternatingGroup (Fin 5))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : V.map (MulAut.conj a5c) ≤ V := by
      rw [hV, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [MonoidHom.map_zpowers]
        show Subgroup.zpowers (a5c * a5a * a5c⁻¹) ≤ _
        rw [hca]
        exact (Subgroup.zpowers_le).2 (V.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      · rw [MonoidHom.map_zpowers]
        show Subgroup.zpowers (a5c * a5b * a5c⁻¹) ≤ _
        rw [hcb]
        exact (Subgroup.zpowers_le).2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj a5c).injective]
  set W : Subgroup X := V.comap e.toMonoidHom with hW
  have hW4 : Nat.card W = 4 := by rw [hW, OmegaFacts.card_comap_mulEquiv e V, hV4]
  have hX60 : Nat.card X = 60 := by rw [Nat.card_congr e.toEquiv, card_alt_five]
  have hWp : IsPGroup 2 ↥W := IsPGroup.of_card (n := 2) (by rw [hW4]; norm_num)
  have hWidx : W.index = 15 := by
    have := W.card_mul_index
    rw [hW4, hX60] at this
    omega
  set P := hWp.toSylow (by rw [hWidx]; norm_num) with hP
  have hcW : e.symm a5c ∈ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hW, Subgroup.mem_comap, Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_normalizer_iff.1 hcN (e y))
  have h3N : 3 ∣ Nat.card (Subgroup.normalizer (W : Set X)) := by
    have hord : orderOf (⟨e.symm a5c, hcW⟩ : ↥(Subgroup.normalizer (W : Set X))) = 3 := by
      rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hoc]
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hcard : Nat.card (Sylow 2 X) = (Subgroup.normalizer (W : Set X)).index := by
    rw [Sylow.card_eq_index_normalizer P]
    have hPW : ((P : Subgroup X) : Set X) = (W : Set X) := by rw [hP, IsPGroup.toSylow_coe]
    congr 2
  rw [hcard]
  intro h3
  have hmul := (Subgroup.normalizer (W : Set X)).card_mul_index
  rw [hX60] at hmul
  have h9 : 9 ∣ 60 := by
    rw [← hmul, show (9 : ℕ) = 3 * 3 by norm_num]
    exact Nat.mul_dvd_mul h3N h3
  norm_num at h9

theorem exists_invariant_sylow_of_not_dvd {actor acted : Type} [Group actor] [Group acted] [Finite acted]
    [MulDistribMulAction actor acted] {r : ℕ} (hr : r.Prime) (hpgroup : IsPGroup r actor) {q : ℕ}
    (hq : q.Prime) (hcard : ¬ r ∣ Nat.card (Sylow q acted)) :
    ∃ sylow : Sylow q acted, ∀ member : actor, ∀ x ∈ (sylow : Subgroup acted),
      member • x ∈ (sylow : Subgroup acted) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨fixedSylow, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow q acted) hcard
  refine ⟨fixedSylow, fun member x hx => ?_⟩
  have heq : member • fixedSylow = fixedSylow := MulAction.mem_fixedPoints.mp hfixed member
  have h1 : member • x ∈ member • (fixedSylow : Subgroup acted) :=
    Subgroup.smul_mem_pointwise_smul x member _ hx
  rw [← Sylow.pointwise_smul_def, heq] at h1
  exact h1

theorem exists_normalized_sylow_of_not_dvd {Q : Type} [Group Q] [Finite Q] {r : ℕ} (hr : r.Prime)
    {Bq Y : Subgroup Q} (hB : IsPGroup r ↥Bq) (hBY : Bq ≤ Subgroup.normalizer (Y : Set Q)) {q : ℕ}
    (hq : q.Prime) (hcard : ¬ r ∣ Nat.card (Sylow q ↥Y)) :
    ∃ S : Sylow q ↥Y, Bq ≤ Subgroup.normalizer
      (((S : Subgroup ↥Y).map Y.subtype : Subgroup Q) : Set Q) := by
  let action : MulDistribMulAction ↥Bq ↥Y :=
    { smul := fun member element => ⟨member * element * (member : Q)⁻¹,
        Subgroup.le_normalizer_iff.mp hBY member member.property element element.property⟩
      one_smul := fun element => Subtype.ext (by
        change (1 : Q) * (element : Q) * (1 : Q)⁻¹ = element
        simp)
      mul_smul := fun first second element => Subtype.ext (by
        change ((first : Q) * second) * (element : Q) * ((first : Q) * second)⁻¹ =
          first * ((second : Q) * element * (second : Q)⁻¹) * (first : Q)⁻¹
        simp [mul_assoc])
      smul_one := fun member => Subtype.ext (by
        change (member : Q) * 1 * (member : Q)⁻¹ = 1
        simp)
      smul_mul := fun member first second => Subtype.ext (by
        change (member : Q) * ((first : Q) * second) * (member : Q)⁻¹ =
          (member * first * (member : Q)⁻¹) * (member * second * (member : Q)⁻¹)
        simp [mul_assoc]) }
  let : MulDistribMulAction ↥Bq ↥Y := action
  obtain ⟨S, hS⟩ := exists_invariant_sylow_of_not_dvd (acted := ↥Y) hr hB hq hcard
  refine ⟨S, Subgroup.le_normalizer_iff.mpr ?_⟩
  intro member hmember element helement
  obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp helement
  exact ⟨(⟨member, hmember⟩ : ↥Bq) • preimage, hS _ preimage hpreimage, rfl⟩

theorem card_iSup_eq_prod {Q : Type} [Group Q] [Finite Q] (𝒮 : Finset (Subgroup Q))
    (hcomm : ∀ X ∈ 𝒮, ∀ X' ∈ 𝒮, X ≠ X' → X' ≤ Subgroup.centralizer (X : Set Q))
    (hZ : ∀ X ∈ 𝒮, Subgroup.center ↥X = ⊥) (W : Subgroup Q → Subgroup Q)
    (hW : ∀ X ∈ 𝒮, W X ≤ X) :
    Nat.card ↥(⨆ X ∈ 𝒮, W X) = ∏ X ∈ 𝒮, Nat.card ↥(W X) := by
  classical
  induction 𝒮 using Finset.induction_on with
  | empty => simp
  | insert X 𝒮 hX ih =>
    rw [Finset.iSup_insert, Finset.prod_insert hX]
    have ih' := ih (fun Y hY Y' hY' hne => hcomm Y (by simp [hY]) Y' (by simp [hY']) hne)
      (fun Y hY => hZ Y (by simp [hY])) (fun Y hY => hW Y (by simp [hY]))
    have hC : (⨆ X' ∈ 𝒮, W X') ≤ Subgroup.centralizer (X : Set Q) := by
      refine iSup₂_le fun X' hX' => (hW X' (by simp [hX'])).trans ?_
      refine hcomm X (by simp) X' (by simp [hX']) ?_
      rintro rfl
      exact hX hX'
    have hc : ∀ x ∈ W X, ∀ y ∈ ⨆ X' ∈ 𝒮, W X', x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 (hC hy) x (hW X (by simp) hx)
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
    have hinf : W X ⊓ ⨆ X' ∈ 𝒮, W X' = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
      have hzX : z ∈ X := hW X (by simp) hz1
      have hcen : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 (hC hz2) g g.2
      rw [hZ X (by simp), Subgroup.mem_bot] at hcen
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hcen)
    rw [hinf, Subgroup.card_bot, mul_one, ih'] at h
    exact h

theorem card_sylow_two_of_card_sixty {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 60)
    (S : Sylow 2 X) : Nat.card (S : Subgroup X) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hidx := S.not_dvd_index
  have hmul := (S : Subgroup X).card_mul_index
  rw [hk, hX] at hmul
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have h8 : 2 ^ 3 ∣ 60 := ⟨_, (hmul.symm.trans (by
      rw [show k = 3 + (k - 3) by omega, pow_add, mul_assoc]))⟩
    norm_num at h8
  interval_cases k
  · exfalso; apply hidx; rw [show (S : Subgroup X).index = 60 by omega]; norm_num
  · exfalso; apply hidx; rw [show (S : Subgroup X).index = 30 by omega]; norm_num
  · rw [hk]; norm_num

theorem mem_normalizer_preimage {M : Subgroup G} {N : Subgroup ↥M} [N.Normal] {V : Subgroup (↥M ⧸ N)}
    {b : G} (hbM : b ∈ M)
    (hbV : QuotientGroup.mk' N ⟨b, hbM⟩ ∈ Subgroup.normalizer (V : Set (↥M ⧸ N))) :
    b ∈ Subgroup.normalizer (((V.comap (QuotientGroup.mk' N)).map M.subtype : Subgroup G) : Set G) := by
  have key : ∀ (c : G) (hc : c ∈ M), QuotientGroup.mk' N ⟨c, hc⟩ ∈ Subgroup.normalizer (V : Set (↥M ⧸ N)) →
      ∀ y ∈ (V.comap (QuotientGroup.mk' N)).map M.subtype,
        c * y * c⁻¹ ∈ (V.comap (QuotientGroup.mk' N)).map M.subtype := by
    intro c hc hcV y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨⟨c, hc⟩ * z * ⟨c, hc⟩⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_comap] at hz ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hcV _).1 hz
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key b hbM hbV y, fun hy => ?_⟩
  have hbV' : QuotientGroup.mk' N ⟨b⁻¹, M.inv_mem hbM⟩ ∈ Subgroup.normalizer (V : Set (↥M ⧸ N)) := by
    have : QuotientGroup.mk' N ⟨b⁻¹, M.inv_mem hbM⟩ = (QuotientGroup.mk' N ⟨b, hbM⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact (Subgroup.normalizer (V : Set (↥M ⧸ N))).inv_mem hbV
  have := key b⁻¹ (M.inv_mem hbM) hbV' _ hy
  simpa [mul_assoc] using this

theorem t1CaseB_of_inputs (h133 : Lemma133Statement) : Lemma1313i.T1CaseB := by
  intro G _ _ m p B M E A D T R L0 d h h139b
  classical
  have hp : p.Prime := GLStanding.prime h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : p = 3 := h139b.1
  obtain ⟨h𝒦, hZ, hA, -⟩ := caseB_data hp h139b
  obtain ⟨L, hL, hV⟩ := Lemma1312b.orbit_of_cex h133 h
  have hBM : B ≤ M := Lemma1312b.B_le_M h
  have hdM : d ∈ M := Lemma1312b.d_mem_M h
  have hL1I : L1of p M D L0 ≤ Istar p M D := Lemma1312b.L1_le_istar h
  have hL1M : L1of p M D L0 ≤ M := hL1I.trans (istar_le_M p M D)
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hXc : ∀ i : Fin p, GLAPComponent p (Istar p M D) (GLBConj (d ^ (i : ℕ)) L) := fun i =>
    Lemma1312b.istar_comp_conj hp hL (M.pow_mem hdM i)
  have hXK : ∀ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L) ∈ compSet p M D := fun i =>
    ⟨⟨_, hXc i⟩, rfl⟩
  have hBb3 : IsPGroup 3 ↥(barX p M B) := by
    rw [← hp3]
    exact CFSG.Open.IsElemAbelian.isPGroup (isElemAbelian_barX hBel)
  have hBbX : ∀ X ∈ compSet p M D, barX p M B ≤ Subgroup.normalizer (X : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    rintro X ⟨y, rfl⟩
    exact barX_le_normalizer_barX p hBM (y.2.1.trans (istar_le_M p M D)) ((h133 h.toSec13).2 _ y.2).2.1
  have hsyl : ∀ X ∈ compSet p M D, ∃ S : Sylow 2 ↥X, barX p M B ≤ Subgroup.normalizer
      (((S : Subgroup ↥X).map X.subtype : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    intro X hX
    obtain ⟨eA⟩ := hA X hX
    exact exists_normalized_sylow_of_not_dvd Nat.prime_three hBb3 (hBbX X hX) Nat.prime_two
      (not_three_dvd_card_sylow_two eA)
  choose Sf hSf using hsyl
  obtain ⟨Wf, hWfdef⟩ : ∃ Wf : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) → Subgroup (↥M ⧸ GLAPPrimeCore p ↥M),
      ∀ X (hX : X ∈ compSet p M D), Wf X = (Sf X hX : Subgroup ↥X).map X.subtype :=
    ⟨fun X => if hX : X ∈ compSet p M D then ((Sf X hX : Subgroup ↥X).map X.subtype) else ⊥,
      fun X hX => dif_pos hX⟩
  have hWfX : ∀ X ∈ compSet p M D, Wf X ≤ X := fun X hX => by
    rw [hWfdef X hX]
    exact Subgroup.map_subtype_le _
  have hWfB : ∀ X ∈ compSet p M D, barX p M B ≤ Subgroup.normalizer
      ((Wf X : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := fun X hX => by
    rw [hWfdef X hX]
    exact hSf X hX
  have hX60 : ∀ X ∈ compSet p M D, Nat.card ↥X = 60 := fun X hX => by
    obtain ⟨eA⟩ := hA X hX
    rw [Nat.card_congr eA.toEquiv, card_alt_five]
  have hWf4 : ∀ X ∈ compSet p M D, Nat.card ↥(Wf X) = 4 := fun X hX => by
    rw [hWfdef X hX, Subgroup.card_map_of_injective X.subtype_injective]
    exact card_sylow_two_of_card_sixty (hX60 X hX) _
  set 𝒮 : Finset (Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    Finset.univ.image (fun i : Fin p => barX p M (GLBConj (d ^ (i : ℕ)) L)) with h𝒮
  have h𝒮K : ∀ X ∈ 𝒮, X ∈ compSet p M D := by
    intro X hX
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hX
    exact hXK i
  have hcomm𝒮 : ∀ X ∈ 𝒮, ∀ X' ∈ 𝒮, X ≠ X' → X' ≤ Subgroup.centralizer (X : Set _) :=
    fun X hX X' hX' hne => le_centralizer_of_ne_comp (h𝒦 X (h𝒮K X hX)) (h𝒦 X' (h𝒮K X' hX')) hne
  have hZ𝒮 : ∀ X ∈ 𝒮, Subgroup.center ↥X = ⊥ := fun X hX => hZ X (h𝒮K X hX)
  have hL1bar : barX p M (L1of p M D L0) = ⨆ X ∈ 𝒮, X := by
    rw [hV, h𝒮, Finset.iSup_finset_image]
    simp
  set Vh := ⨆ X ∈ 𝒮, Wf X with hVh
  have hVhL1 : Vh ≤ barX p M (L1of p M D L0) := by
    rw [hL1bar]
    exact iSup₂_le fun X hX => (hWfX X (h𝒮K X hX)).trans (le_iSup₂_of_le (f := fun X (_ : X ∈ 𝒮) => X) X hX le_rfl)
  have hcardVh : Nat.card ↥Vh = 4 ^ 𝒮.card := by
    rw [hVh, card_iSup_eq_prod 𝒮 hcomm𝒮 hZ𝒮 Wf (fun X hX => hWfX X (h𝒮K X hX)),
      Finset.prod_congr rfl (fun X hX => hWf4 X (h𝒮K X hX)), Finset.prod_const]
  have hcardL1h : Nat.card ↥(barX p M (L1of p M D L0)) = 15 ^ 𝒮.card * Nat.card ↥Vh := by
    have h1 := card_iSup_eq_prod 𝒮 hcomm𝒮 hZ𝒮 (fun X => X) (fun X _ => le_rfl)
    rw [hL1bar, h1, Finset.prod_congr rfl (fun X hX => hX60 X (h𝒮K X hX)), Finset.prod_const,
      hcardVh, ← mul_pow]
    norm_num
  have hBbV : ∀ b (hb : b ∈ B), GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hBM hb⟩) Vh = Vh := by
    intro b hb
    have hbB : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hBM hb⟩ ∈ barX p M B :=
      (Lemma1311.mem_barX' p).2 ⟨⟨b, hBM hb⟩, hb, rfl⟩
    rw [hVh, gLBConj_iSup_eq]
    refine iSup_congr fun X => ?_
    rw [gLBConj_iSup_eq]
    refine iSup_congr fun hX => ?_
    exact gLBConj_eq_of_mem_normalizer (hWfB X (h𝒮K X hX) hbB)
  set Y : Subgroup G := (Vh.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).map M.subtype ⊓
    L1of p M D L0 with hY
  have hYL1 : Y ≤ L1of p M D L0 := inf_le_right
  have hYM : Y ≤ M := hYL1.trans hL1M
  have hYbar : barX p M Y = Vh := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨⟨z, hz, hzy⟩, -⟩ := Subgroup.mem_subgroupOf.1 hy
      have : z = y := Subtype.ext hzy
      rw [← this]
      exact hz
    · intro v hv
      obtain ⟨l, hl, hlv⟩ := (Lemma1311.mem_barX' p).1 (hVhL1 hv)
      have hlV : l ∈ Vh.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) := by
        rw [Subgroup.mem_comap, hlv]
        exact hv
      exact (Lemma1311.mem_barX' p).2 ⟨l, ⟨Subgroup.mem_map.2 ⟨l, hlV, rfl⟩, hl⟩, hlv⟩
  have hOY : GLAPPrimeCoreOf p M ⊓ Y = GLAPPrimeCoreOf p M ⊓ L1of p M D L0 := by
    refine le_antisymm (inf_le_inf_left _ hYL1) ?_
    rintro x ⟨hxO, hxL⟩
    obtain ⟨o, ho, hox⟩ := hxO
    have : (⟨x, hL1M hxL⟩ : ↥M) = o := Subtype.ext hox.symm
    have hxV : (⟨x, hL1M hxL⟩ : ↥M) ∈ Vh.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) := by
      rw [Subgroup.mem_comap, this, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff o).2 ho]
      exact Vh.one_mem
    exact ⟨⟨o, ho, hox⟩, Subgroup.mem_map.2 ⟨_, hxV, rfl⟩, hxL⟩
  have hcY := card_eq_card_inter_mul_card_barX hp hYM
  rw [hOY, hYbar, hcardVh] at hcY
  have hcL1 := card_eq_card_inter_mul_card_barX hp hL1M
  rw [hcardL1h, hcardVh] at hcL1
  have hYp : ¬ p ∣ Nat.card Y := by
    rw [hcY]
    intro h3
    rcases (Nat.Prime.dvd_mul hp).1 h3 with h3 | h3
    · exact not_dvd_card_glaPPrimeCoreOf hp M (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    · have := Nat.Prime.dvd_of_dvd_pow hp h3
      rw [hp3] at this
      norm_num at this
  have hY3 : ¬ 3 ∣ Nat.card Y := hp3 ▸ hYp
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := by
    intro b hb
    refine mem_normalizer_inf ?_ (B_le_normalizer_L1 h133 h hb)
    exact mem_normalizer_preimage (hBM hb) (mem_normalizer_iff_gLBConj_eq.2 (hBbV b hb))
  have hB3 : IsPGroup 3 ↥B := by
    rw [← hp3]
    exact CFSG.Open.IsElemAbelian.isPGroup hBel
  obtain ⟨S, hSB⟩ := CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
    3 Nat.prime_three B Y hB3 hY3 hBY 2 Nat.prime_two
  set P : Subgroup G := (S : Subgroup ↥Y).map Y.subtype with hP
  have hPL1 : P ≤ L1of p M D L0 := (Subgroup.map_subtype_le _).trans hYL1
  have hPcard : Nat.card P = Nat.card (S : Subgroup ↥Y) :=
    Subgroup.card_map_of_injective Y.subtype_injective
  have hP2 : IsPGroup 2 ↥(P.subgroupOf (L1of p M D L0)) := by
    refine IsPGroup.of_equiv S.isPGroup' ?_
    exact ((S : Subgroup ↥Y).equivMapOfInjective Y.subtype Y.subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hPL1).symm
  have hidx : ¬ 2 ∣ (P.subgroupOf (L1of p M D L0)).index := by
    have h1 := (P.subgroupOf (L1of p M D L0)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL1).toEquiv, hPcard] at h1
    have h2 := (S : Subgroup ↥Y).card_mul_index
    have hSodd := S.not_dvd_index
    have hpos : 0 < Nat.card (S : Subgroup ↥Y) := Nat.card_pos
    have h3 : (P.subgroupOf (L1of p M D L0)).index = 15 ^ 𝒮.card * (S : Subgroup ↥Y).index := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [h1, hcL1]
      have : Nat.card ↥(GLAPPrimeCoreOf p M ⊓ L1of p M D L0) * (15 ^ 𝒮.card * 4 ^ 𝒮.card) =
          15 ^ 𝒮.card * (Nat.card ↥(GLAPPrimeCoreOf p M ⊓ L1of p M D L0) * 4 ^ 𝒮.card) := by ring
      rw [this, ← hcY, ← h2]
      ring
    rw [h3]
    intro h2d
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2d with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
      norm_num at this
    · exact hSodd h
  refine ⟨hP2.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.map_subgroupOf_eq_of_le hPL1]
  exact hSB

end T1

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims139
