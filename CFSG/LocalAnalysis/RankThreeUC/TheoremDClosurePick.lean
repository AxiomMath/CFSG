module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCBlocks
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClosureBlocks
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClosureRank
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClosureSylow
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem convI_apply_eq_self_iff {U : Subgroup G} (hU : IsElemAbelian 2 U) {g : G}
    (hg : g ∈ normalizer (U : Set G)) (a : IntMod U hU) :
    convI hU ⟨g, hg⟩ a = a ↔ g * a.val = a.val * g := by
  rw [← IntMod.val_injective.eq_iff, convI_apply_val, mul_inv_eq_iff_eq_mul]

structure PickFacts {U : Subgroup G} (hU : IsElemAbelian 2 U) (JM JT : Subgroup G)
    (I : Finset (Subgroup (MulAut (IntMod U hU)))) (L : Subgroup (MulAut (IntMod U hU))) (x : G)
    (ε : IntMod U hU) : Prop where
  xJ : x ∈ JM
  xN : x ∈ normalizer (U : Set G)
  xL : convI hU ⟨x, xN⟩ ∈ L
  x3 : convI hU ⟨x, xN⟩ ^ 3 = 1
  x1 : convI hU ⟨x, xN⟩ ≠ 1
  x3dvd : 3 ∣ orderOf x
  εV : ε ∈ commV L
  ε1 : ε ≠ 1
  εA : ε.val ∈ centralizer (JT : Set G)
  εx : convI hU ⟨x, xN⟩ ε ≠ ε
  ε_other : ∀ L' ∈ I, L' ≠ L → ∀ (z : G) (hz : z ∈ normalizer (U : Set G)),
    convI hU ⟨z, hz⟩ ∈ L' → convI hU ⟨z, hz⟩ ε = ε
  gen : ∀ a ∈ U ⊓ centralizer (JT : Set G), x * a = a * x →
    ∀ (m : G) (hm : m ∈ normalizer (U : Set G)), convI hU ⟨m, hm⟩ ∈ L → m * a = a * m
  idx : ∀ a ∈ U ⊓ centralizer (JT : Set G), x * a ≠ a * x →
    ∀ b ∈ U ⊓ centralizer (JT : Set G), x * b ≠ b * x → x * (a * b) = a * b * x


theorem exists_pickFacts {M U JM JT : Subgroup G} (hU : IsElemAbelian 2 U)
    (hMN : M ≤ normalizer (U : Set G)) (hJT : JT ≤ M)
    {I : Finset (Subgroup (MulAut (IntMod U hU)))} (hBD : BlockData (autI hU M) I)
    (hΛ : autI hU JM = ⨆ L ∈ I, L)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (autI hU JT) (autI hU JM))
    {L : Subgroup (MulAut (IntMod U hU))} (hL : L ∈ I) :
    ∃ (x : G) (ε : IntMod U hU), PickFacts hU JM JT I L x ε := by
  classical
  have hW2 : ∀ w : IntMod U hU, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hLΛ : L ≤ ⨆ L ∈ I, L := le_iSup₂_of_le L hL le_rfl
  have hSylΛ : CFSG.QuasithinUnique.IsSylowTwoOf (autI hU JT) (⨆ L ∈ I, L) := hΛ ▸ hSyl
  obtain ⟨hJdec, hts⟩ := hBD.exists_sylow_two_decomp hSylΛ
  obtain ⟨g, hgL, hg3, hg1⟩ := S1417.exists_orderThree (hBD.natural L hL)
  obtain ⟨y, hyJ, hyg⟩ := (mem_autI hU).1 (hΛ ▸ hLΛ hgL)
  obtain ⟨t, htJL, ht2, ht1, htuniq⟩ := hts L hL
  obtain ⟨ε, hεV, hε1, htε, hgε⟩ := hBD.exists_fixed_vector hL htJL.2 hgL ht2 ht1 hg3 hg1
  obtain ⟨c, hc⟩ := hBD.exists_delta hW2 hL htJL.2 hgL ht2 ht1 hg3 hg1
  have hy : convI hU ⟨(y : G), y.2⟩ = g := hyg
  have htA : ∀ (a : G) (ha : a ∈ U ⊓ centralizer (JT : Set G)),
      t (IntMod.mk hU ⟨a, ha.1⟩) = IntMod.mk hU ⟨a, ha.1⟩ := by
    intro a ha
    obtain ⟨τ, hτJ, hτ⟩ := (mem_autI hU).1 htJL.1
    rw [← hτ, convI_apply_eq_self_iff hU τ.2]
    exact mem_centralizer_iff.mp ha.2 τ hτJ
  have hΛX : (⨆ L ∈ I, L) ≤ autI hU M := hBD.le
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLeΛ : ∀ L' ∈ I, L' ≤ ⨆ L ∈ I, L := fun L' hL' =>
    le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod U hU))) (_ : K ∈ I) => K) L' hL' le_rfl
  have hJfix : ∀ φ ∈ autI hU JT, φ ε = ε := by
    intro φ hφ
    have hφ' : φ ∈ ⨆ L' ∈ I, (autI hU JT ⊓ L') := hJdec ▸ hφ
    have hle : (⨆ L' ∈ I, (autI hU JT ⊓ L')) ≤
        MulAction.stabilizer (MulAut (IntMod U hU)) ε := by
      refine iSup₂_le fun L' hL' φ' hφ'' => ?_
      by_cases hLL : L' = L
      · subst hLL
        rcases htuniq φ' hφ'' with h | h
        · rw [h]
          exact one_mem _
        · rw [h]
          exact htε
      · exact hBD.apply_eq_of_commute hL (hΛX (hLeΛ L' hL' hφ''.2))
          (fun l hl => hBD.comm L' hL' L hL hLL φ' hφ''.2 l hl) ε hεV
    exact hle hφ'
  refine ⟨y, ε, hyJ, y.2, ?_, ?_, ?_, ?_, hεV, hε1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hy]
    exact hgL
  · rw [hy]
    exact hg3
  · rw [hy]
    exact hg1
  · have h1 : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    have h2 : orderOf (convI hU y) ∣ orderOf y := orderOf_map_dvd _ _
    rw [show convI hU y = g from hyg, h1, ← Subgroup.orderOf_coe y] at h2
    exact h2
  · rw [mem_centralizer_iff]
    intro τ hτ
    have hτN : τ ∈ normalizer (U : Set G) := hMN (hJT hτ)
    exact (convI_apply_eq_self_iff hU hτN ε).1 (hJfix _ (convI_mem_autI hU hτ hτN))
  · rw [hy]
    exact hgε
  · intro L' hL' hLL' z hz hzL'
    exact hBD.apply_eq_of_commute hL (hΛX (hLeΛ L' hL' hzL'))
      (fun l hl => hBD.comm L' hL' L hL hLL' _ hzL' l hl) ε hεV
  · intro a ha hxa m hm hmL
    have hga : g (IntMod.mk hU ⟨a, ha.1⟩) = IntMod.mk hU ⟨a, ha.1⟩ := by
      rw [← hy]
      exact (convI_apply_eq_self_iff hU y.2 _).2 hxa
    have := hBD.apply_eq_of_apply_eq_gen hL htJL.2 hgL ht2 ht1 hg3 hg1 (htA a ha) hga
      (convI hU ⟨m, hm⟩) hmL
    exact (convI_apply_eq_self_iff hU hm _).1 this
  · intro a ha hxa b hb hxb
    have hgα : g (IntMod.mk hU ⟨a, ha.1⟩) ≠ IntMod.mk hU ⟨a, ha.1⟩ := fun h =>
      hxa ((convI_apply_eq_self_iff hU y.2 (IntMod.mk hU ⟨a, ha.1⟩)).1 (hy ▸ h))
    have hgβ : g (IntMod.mk hU ⟨b, hb.1⟩) ≠ IntMod.mk hU ⟨b, hb.1⟩ := fun h =>
      hxb ((convI_apply_eq_self_iff hU y.2 (IntMod.mk hU ⟨b, hb.1⟩)).1 (hy ▸ h))
    have hα := mul_inv_eq_iff_eq_mul.1 ((hc _ (htA a ha)).resolve_left hgα)
    have hβ := mul_inv_eq_iff_eq_mul.1 ((hc _ (htA b hb)).resolve_left hgβ)
    have hcc : c * c = 1 := by rw [← pow_two]; exact hW2 c
    have hfix : g (IntMod.mk hU ⟨a, ha.1⟩ * IntMod.mk hU ⟨b, hb.1⟩) =
        IntMod.mk hU ⟨a, ha.1⟩ * IntMod.mk hU ⟨b, hb.1⟩ := by
      rw [map_mul, hα, hβ, mul_mul_mul_comm, hcc, one_mul]
    exact (convI_apply_eq_self_iff hU y.2
      (IntMod.mk hU ⟨a, ha.1⟩ * IntMod.mk hU ⟨b, hb.1⟩)).1 (hy ▸ hfix)

omit [Finite G] in
theorem eq_one_of_mem_two_blocks {U : Subgroup G} {hU : IsElemAbelian 2 U}
    {X : Subgroup (MulAut (IntMod U hU))} {I : Finset (Subgroup (MulAut (IntMod U hU)))}
    (hBD : BlockData X I) {L L' : Subgroup (MulAut (IntMod U hU))} (hL : L ∈ I) (hL' : L' ∈ I)
    (hLL' : L ≠ L') {y : MulAut (IntMod U hU)} (hyL : y ∈ L) (hyL' : y ∈ L') : y = 1 := by
  have hle : L' ≤ ⨆ K ∈ I, ⨆ (_ : K ≠ L), K :=
    le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod U hU))) (_ : K ∈ I) =>
      ⨆ (_ : K ≠ L), K) L' hL' (le_iSup_of_le (Ne.symm hLL') le_rfl)
  have : y ∈ L ⊓ ⨆ K ∈ I, ⨆ (_ : K ≠ L), K := ⟨hyL, hle hyL'⟩
  rw [hBD.indep L hL] at this
  exact Subgroup.mem_bot.1 this

theorem two_le_pRank_inf_centralizer_of_pair {M U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hMN : M ≤ normalizer (U : Set G)) {I : Finset (Subgroup (MulAut (IntMod U hU)))}
    (hBD : BlockData (autI hU M) I) {L L' : Subgroup (MulAut (IntMod U hU))} (hL : L ∈ I)
    (hL' : L' ∈ I) (hLL' : L ≠ L') {x x' : G} (hxM : x ∈ M) (hx'M : x' ∈ M)
    (hxL : convI hU ⟨x, hMN hxM⟩ ∈ L) (hx3 : convI hU ⟨x, hMN hxM⟩ ^ 3 = 1)
    (hx1 : convI hU ⟨x, hMN hxM⟩ ≠ 1) (hx'L : convI hU ⟨x', hMN hx'M⟩ ∈ L')
    (hx'3 : convI hU ⟨x', hMN hx'M⟩ ^ 3 = 1) (hx'1 : convI hU ⟨x', hMN hx'M⟩ ≠ 1)
    {a : G} (haU : a ∈ U) (hxa : x * a = a * x) (hx'a : x' * a = a * x') :
    2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({a} : Set G)) := by
  classical
  set g := convI hU ⟨x, hMN hxM⟩ with hgdef
  set g' := convI hU ⟨x', hMN hx'M⟩ with hg'def
  set Q : Subgroup (MulAut (IntMod U hU)) := Subgroup.closure {g, g'} with hQ
  set H : Subgroup G := preI hU M hMN Q with hH
  have hHM : H ≤ M := preI_le hU
  have hHN : H ≤ normalizer (U : Set G) := hHM.trans hMN
  have hxH : x ∈ H := (mem_preI hU).2 ⟨hxM, Subgroup.subset_closure (Or.inl rfl)⟩
  have hx'H : x' ∈ H := (mem_preI hU).2 ⟨hx'M, Subgroup.subset_closure (Or.inr rfl)⟩
  have hrange : (convHom hU H hHN).range = Q := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨h, rfl⟩
      obtain ⟨hhM, hhQ⟩ := (mem_preI hU).1 h.2
      exact hhQ
    · refine (Subgroup.closure_le _).2 ?_
      rintro q (rfl | rfl)
      · exact ⟨⟨x, hxH⟩, rfl⟩
      · exact ⟨⟨x', hx'H⟩, rfl⟩
  have hcomm : g * g' = g' * g := hBD.comm L hL L' hL' hLL' g hxL g' hx'L
  have hne : g' ≠ g := fun h => hx1 (eq_one_of_mem_two_blocks hBD hL hL' hLL' hxL (h ▸ hx'L))
  have hne' : g' ≠ g⁻¹ := fun h => hx1 (inv_eq_one.1 (eq_one_of_mem_two_blocks hBD hL hL' hLL'
    (L.inv_mem hxL) (h ▸ hx'L)))
  have hrk := two_le_pRank_of_range_eq_closure (convHom hU H hHN) hrange hcomm hx3 hx'3 hx1 hx'1
    hne hne'
  refine hrk.trans (CFSG.SectionRank.pRank_mono (by norm_num) (le_inf hHM ?_))
  intro h hh
  rw [mem_centralizer_singleton_iff]
  have hstab : Q ≤ MulAction.stabilizer (MulAut (IntMod U hU)) (IntMod.mk hU ⟨a, haU⟩) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro q (rfl | rfl)
    · exact (convI_apply_eq_self_iff hU _ (IntMod.mk hU ⟨a, haU⟩)).2 hxa
    · exact (convI_apply_eq_self_iff hU _ (IntMod.mk hU ⟨a, haU⟩)).2 hx'a
  have hhN : h ∈ normalizer (U : Set G) := hHN hh
  have := (convI_apply_eq_self_iff hU hhN (IntMod.mk hU ⟨a, haU⟩)).1
    (hstab ((mem_preI hU).1 hh).2)
  exact this

theorem two_le_pRank_inf_centralizer_of_centralized {M JM : Subgroup G} (hJM : JM ≤ M)
    (h2 : 2 ≤ CFSG.Open.pRank 3 JM) {a : G} (ha : ∀ m ∈ JM, m * a = a * m) :
    2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({a} : Set G)) :=
  h2.trans (CFSG.SectionRank.pRank_mono (by norm_num)
    (le_inf hJM fun m hm => mem_centralizer_singleton_iff.2 (ha m hm)))

theorem two_le_pRank_inf_centralizer_of_block {M U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hMN : M ≤ normalizer (U : Set G)) {I : Finset (Subgroup (MulAut (IntMod U hU)))}
    (hBD : BlockData (autI hU M) I) (hcard : I.card ≤ 2) {L : Subgroup (MulAut (IntMod U hU))}
    (hL : L ∈ I) {ε : IntMod U hU} (hεV : ε ∈ commV L) (hε1 : ε ≠ 1) {E : Subgroup G}
    (hEM : E ≤ M) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 27) :
    2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({ε.val} : Set G)) := by
  have hEN : E ≤ normalizer (U : Set G) := hEM.trans hMN
  refine two_le_pRank_inf_centralizer_of_few_images hEM hE hEcard hU hEN ε ?_
  have hsub : {v | ∃ x : E, convHom hU E hEN x ε = v} ⊆ (commV L : Set (IntMod U hU)) \ {1} := by
    rintro v ⟨x, rfl⟩
    have hxM : (x : G) ∈ M := hEM x.2
    have hgX : convHom hU E hEN x ∈ autI hU M := convI_mem_autI hU hxM (hMN hxM)
    have hg3 : (convHom hU E hEN x) ^ 3 = 1 := by
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
      rw [this, map_one]
    have hfix := hBD.conjAut_eq_of_card_le_two hcard hgX hg3 L hL
    refine ⟨hBD.apply_mem_commV_of_conjAut_eq hgX hL hfix ε hεV, ?_⟩
    intro h
    exact hε1 ((map_eq_one_iff _ (convHom hU E hEN x).injective).1 h)
  have hc4 : Nat.card (commV L) = 4 := (S1417.card_of_actsAsNaturalL2 (hBD.natural L hL)).2
  calc {v | ∃ x : E, convHom hU E hEN x ε = v}.ncard
      ≤ ((commV L : Set (IntMod U hU)) \ {1}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 3 := by
      rw [Set.ncard_sdiff_singleton_of_mem (commV L).one_mem, ← Nat.card_coe_set_eq]
      simp only [SetLike.coe_sort_coe, hc4]

namespace PickFacts

variable {U JM JT : Subgroup G} {hU : IsElemAbelian 2 U}
  {I : Finset (Subgroup (MulAut (IntMod U hU)))} {L : Subgroup (MulAut (IntMod U hU))} {x : G}
  {ε : IntMod U hU}

omit [Finite G] in
theorem mul_mem_inf_centralizer (hP : PickFacts hU JM JT I L x ε)
    {a b : G} (ha : a ∈ U ⊓ centralizer (JT : Set G)) (hb : b ∈ U ⊓ centralizer (JT : Set G))
    (haH : a ∉ (U ⊓ centralizer (JT : Set G)) ⊓ centralizer ({x} : Set G))
    (hbH : b ∉ (U ⊓ centralizer (JT : Set G)) ⊓ centralizer ({x} : Set G)) :
    a * b ∈ (U ⊓ centralizer (JT : Set G)) ⊓ centralizer ({x} : Set G) := by
  refine ⟨(U ⊓ centralizer (JT : Set G)).mul_mem ha hb, mem_centralizer_singleton_iff.2 ?_⟩
  refine (hP.idx a ha (fun h => haH ⟨ha, mem_centralizer_singleton_iff.2 h.symm⟩) b hb
    (fun h => hbH ⟨hb, mem_centralizer_singleton_iff.2 h.symm⟩)).symm

omit [Finite G] in
theorem three_dvd_card {M : Subgroup G} (hP : PickFacts hU JM JT I L x ε) (hJM : JM ≤ M)
    {a : G} (hxa : x * a = a * x) : 3 ∣ Nat.card ↥(M ⊓ centralizer ({a} : Set G)) := by
  have hx : x ∈ M ⊓ centralizer ({a} : Set G) :=
    ⟨hJM hP.xJ, mem_centralizer_singleton_iff.2 hxa⟩
  have h1 := Subgroup.orderOf_dvd_natCard (M ⊓ centralizer ({a} : Set G)) hx
  exact hP.x3dvd.trans h1

omit [Finite G] in
theorem eps_mem (hP : PickFacts hU JM JT I L x ε) :
    ε.val ∈ U ⊓ centralizer (JT : Set G) := ⟨ε.val_mem, hP.εA⟩

omit [Finite G] in
theorem eps_not_mem (hP : PickFacts hU JM JT I L x ε) :
    ε.val ∉ (U ⊓ centralizer (JT : Set G)) ⊓ centralizer ({x} : Set G) := fun h =>
  hP.εx ((convI_apply_eq_self_iff hU hP.xN ε).2 (mem_centralizer_singleton_iff.1 h.2).symm)

omit [Finite G] in
theorem eps_mem_other (hP : PickFacts hU JM JT I L x ε) {L' : Subgroup (MulAut (IntMod U hU))}
    {x' : G} {ε' : IntMod U hU} (hP' : PickFacts hU JM JT I L' x' ε') (hL' : L' ∈ I)
    (hLL' : L' ≠ L) :
    ε.val ∈ (U ⊓ centralizer (JT : Set G)) ⊓ centralizer ({x'} : Set G) :=
  ⟨hP.eps_mem, mem_centralizer_singleton_iff.2
    ((convI_apply_eq_self_iff hU hP'.xN ε).1 (hP.ε_other L' hL' hLL' x' hP'.xN hP'.xL)).symm⟩

end PickFacts

end CFSG.LocalAnalysis.RankThreeUC
