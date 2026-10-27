module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoHSU35
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOverModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOvergroups
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveU35
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoPairsBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.Native CFSG.AGLEmbeddingD2

private theorem map_conj_inv_map_conj {G : Type*} [Group G] (c : G) (A : Subgroup G) :
    (A.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A using 2
  ext x
  show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x
  group

private theorem hs100P_map_conj {g : Equiv.Perm (Fin 100)} (hg : g ∈ hs100P) :
    hs100P.map (MulAut.conj g).toMonoidHom = hs100P := by
  have hc : ∀ h ∈ hs100P, ∀ y ∈ hs100P, h * y * h⁻¹ ∈ hs100P := fun h hh y hy =>
    hs100P.mul_mem (hs100P.mul_mem hh hy) (hs100P.inv_mem hh)
  refine le_antisymm ?_ fun y hy => ⟨g⁻¹ * y * g⁻¹⁻¹, hc _ (hs100P.inv_mem hg) y hy, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hc g hg y hy
  · show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
    group

theorem nonempty_mulEquiv_hsOUA_of_normalizer_le
    {Y J : Subgroup (Equiv.Perm (Fin 100))}
    (hNY : hs100P ⊓ normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y) (hYP : Y ≤ hs100P)
    (hY : Y ≠ hs100P) (hJY : J ≤ Y) (hJ1 : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J Y) :
    Nonempty (↥J ≃* ↥hsOUA) := by
  have hUA : ∀ {J' : Subgroup (Equiv.Perm (Fin 100))}, J' ≤ hsOUA2 → J' ≠ ⊥ → ⁅J', J'⁆ = J' →
      IsSubnormal J' hsOUA2 → J' = hsOUA := fun hJ'Y hJ'1 hJ'p hJ's =>
    eq_of_perfect_of_isSubnormal_of_card_eq_two_mul hsOUA_le_UA2 le_rfl
      (by rw [card_hsOUA2, card_hsOUA]) hsOUA_isSimpleGroup hJ'Y hJ'1 hJ'p hJ's
  rcases hs100P_normalizer_overgroups Y hNY hYP with h | h | h | h
  ·
    exfalso
    have hcard : Nat.card ↥Y = 2 ^ 4 * 5 ^ 3 := by
      rw [h, ← hsON0_eq_normalizer, card_hsON0]
      norm_num
    haveI := Fintype.ofFinite ↥Y
    have hsol : Group.IsSolvable ↥Y :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_five (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])
    exact hJ1 (eq_bot_of_perfect_of_le_isSolvable hJY hsol hJp)
  ·
    subst h
    exact ⟨MulEquiv.subgroupCongr (hUA hJY hJ1 hJp hJs)⟩
  ·
    subst h
    rw [hsOUB2_eq_map] at hJY hJs
    set c := MulAut.conj hsOW0⁻¹ with hc
    have hinj : Function.Injective c.toMonoidHom := c.injective
    have hback : (hsOUA2.map (MulAut.conj hsOW0).toMonoidHom).map c.toMonoidHom = hsOUA2 :=
      map_conj_inv_map_conj hsOW0 hsOUA2
    have hJ' : J.map c.toMonoidHom = hsOUA := by
      refine hUA (hback ▸ Subgroup.map_mono hJY) ?_ (by rw [← Subgroup.map_commutator, hJp]) ?_
      · exact fun hb => hJ1 ((Subgroup.map_eq_bot_iff_of_injective J hinj).mp hb)
      · exact hback ▸ hJs.map c.toMonoidHom
    exact ⟨(J.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hJ')⟩
  · exact absurd h hY

theorem nonempty_mulEquiv_hsOUA_of_le
    {S H J : Subgroup ↥hs100P} (hS : Nat.card S = 5 ^ 3) (hSH : normalizer (S : Set ↥hs100P) ≤ H)
    (hH : H ≠ ⊤) (hJH : J ≤ H) (hJ1 : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J H) :
    Nonempty (↥J ≃* ↥hsOUA) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set ι := hs100P.subtype with hι
  have hιi : Function.Injective ι := hs100P.subtype_injective
  set S' := S.map ι with hS'
  have hS'P : S' ≤ hs100P := Subgroup.map_subtype_le S
  have hS'c : Nat.card S' = 5 ^ (Nat.card hs100P).factorization 5 := by
    rw [hS', Subgroup.card_map_of_injective hιi, hS, factorization_card_hs100P_five]
  have hR₀c : Nat.card hsOR0 = 5 ^ (Nat.card hs100P).factorization 5 := by
    rw [card_hsOR0, factorization_card_hs100P_five]
    norm_num
  obtain ⟨c, hcP, hc⟩ := exists_conj_eq_of_card_eq hsOR0_le_hs100P hS'P hR₀c hS'c
  set κ := (MulAut.conj c).toMonoidHom with hκ
  have hκi : Function.Injective κ := (MulAut.conj c).injective
  set Y := (H.map ι).map κ with hYdef
  have hNY : hs100P ⊓ normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y := by
    rintro n ⟨hnP, hnN⟩
    have hm : c⁻¹ * n * c⁻¹⁻¹ ∈ hs100P := by
      rw [← hs100P_map_conj (hs100P.inv_mem hcP)]
      exact ⟨n, hnP, rfl⟩
    have hmN : c⁻¹ * n * c⁻¹⁻¹ ∈ normalizer (S' : Set (Equiv.Perm (Fin 100))) := by
      have hS'eq : S' = hsOR0.map (MulAut.conj c⁻¹).toMonoidHom := by
        rw [hc, map_conj_inv_map_conj]
      rw [hS'eq, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨n, hnN, rfl⟩
    have hxN : (⟨_, hm⟩ : ↥hs100P) ∈ normalizer (S : Set ↥hs100P) := by
      have h := Subgroup.comap_normalizer_eq_of_le_range (f := ι) (H := S') (by
        rw [hι, Subgroup.range_subtype]; exact hS'P)
      rw [hS', Subgroup.comap_map_eq_self_of_injective hιi] at h
      rw [← h]
      exact hmN
    refine ⟨c⁻¹ * n * c⁻¹⁻¹, ⟨⟨_, hm⟩, hSH hxN, rfl⟩, ?_⟩
    show c * (c⁻¹ * n * c⁻¹⁻¹) * c⁻¹ = n
    group
  have hYP : Y ≤ hs100P := by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact (hs100P_map_conj hcP).le ⟨(x : Equiv.Perm (Fin 100)), x.2, rfl⟩
  have hY : Y ≠ hs100P := by
    intro hYeq
    apply hH
    apply Subgroup.map_injective hιi
    have h1 : H.map ι = Y.map (MulAut.conj c⁻¹).toMonoidHom := by
      rw [hYdef, map_conj_inv_map_conj]
    rw [h1, hYeq, hs100P_map_conj (hs100P.inv_mem hcP), Subgroup.map_top ι, hι,
      Subgroup.range_subtype]
  set J₂ := (J.map ι).map κ with hJ₂
  have hJ₂Y : J₂ ≤ Y := Subgroup.map_mono (Subgroup.map_mono hJH)
  have hJ₂1 : J₂ ≠ ⊥ := by
    intro hb
    apply hJ1
    rw [hJ₂, Subgroup.map_eq_bot_iff_of_injective _ hκi,
      Subgroup.map_eq_bot_iff_of_injective _ hιi] at hb
    exact hb
  have hJ₂p : ⁅J₂, J₂⁆ = J₂ := by
    rw [hJ₂, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hJp]
  have hJ₂s : IsSubnormal J₂ Y := (hJs.map ι).map κ
  obtain ⟨e⟩ := nonempty_mulEquiv_hsOUA_of_normalizer_le hNY hYP hY hJ₂Y hJ₂1 hJ₂p hJ₂s
  exact ⟨((J.equivMapOfInjective ι hιi).trans ((J.map ι).equivMapOfInjective κ hκi)).trans e⟩

private theorem card_center_eq_card_inf_centralizer {G : Type*} [Group G] (A : Subgroup G) :
    Nat.card (center A) = Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G) := by
  have h : (center A).map A.subtype = A ⊓ centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, mem_centralizer_iff.mpr fun b hb => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b, hb⟩)
    · rintro ⟨hxA, hxC⟩
      exact ⟨⟨x, hxA⟩, mem_center_iff.mpr fun b => Subtype.ext (mem_centralizer_iff.mp hxC b b.2),
        rfl⟩
  rw [← h, Subgroup.card_map_of_injective A.subtype_injective]

theorem threeFourTwoAt_hs100P :
    ThreeFourTwoAt 5 ↥hs100P := by
  have eP : CFSG.Blueprint.NativeSporadic.HS ≃* ↥hs100P := hs100Equiv
  haveI : IsSimpleGroup ↥hs100P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS eP.symm
  have hnab : ∃ a b : ↥hs100P, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥hs100P := { (inferInstance : Group ↥hs100P) with mul_comm := hc }
    have hq : (Nat.card ↥hs100P).Prime := IsSimpleGroup.prime_card
    rw [card_hs100P] at hq
    norm_num at hq
  have houtc : 0 < Nat.card (Outer ↥hs100P) ∧ Nat.card (Outer ↥hs100P) ≤ 2 :=
    ⟨Nat.card_pos, outer_card_hs100P⟩
  have hout : Group.IsSolvable (Outer ↥hs100P) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 (Outer ↥hs100P) := by
      rcases (by omega : Nat.card (Outer ↥hs100P) = 2 ^ 0 ∨ Nat.card (Outer ↥hs100P) = 2 ^ 1)
        with h | h
      · exact IsPGroup.of_card h
      · exact IsPGroup.of_card h
    haveI := h2.isNilpotent
    infer_instance
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  refine threeFourTwoAt_of_forall_model inferInstance hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn e hrk hC hcomp hER hE hEc hcore hRY hKY J hJ hne hJp hJs hQ
  haveI := hKn
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set H : Subgroup ↥hs100P := (Y₀.subgroupOf K).map e.toMonoidHom with hHdef
  have hH : H ≠ ⊤ := by
    intro htop
    apply hKY
    have h1 : Y₀.subgroupOf K = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [← hHdef, htop, Subgroup.map_top_of_surjective _ e.surjective]
    intro k hk
    exact Subgroup.mem_subgroupOf.mp (h1 ▸ Subgroup.mem_top (⟨k, hk⟩ : K))
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hTc, -, hTZ, -, hTexp, -⟩ := heisLocalEq_hsP e T
  have hRKc : Nat.card ((R : Subgroup Y) ⊓ K : Subgroup Y) = 5 ^ 3 := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, hTc]
  have hRKexp : ∀ x ∈ (R : Subgroup Y) ⊓ K, x ^ 5 = 1 := by
    rw [← hT]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, hTexp t ht, map_one]
  have h2 : 2 ≤ CFSG.Open.pRank 5 ((R : Subgroup Y) ⊓ K) := by
    obtain ⟨B, hB, hBe, hBc⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_card_sq_of_card_cube hRKc hRKexp
    exact CFSG.SectionRank.le_pRank (by norm_num) hB hBe hBc
  have hZT : Nat.card (center ((R : Subgroup Y) ⊓ K : Subgroup Y)) = 5 := by
    obtain ⟨φ⟩ : Nonempty (↥(T : Subgroup K) ≃* ↥((R : Subgroup Y) ⊓ K)) :=
      ⟨((T : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hT)⟩
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ,
      Subgroup.card_map_of_injective φ.injective, card_center_eq_card_inf_centralizer, hTZ]
  have hZKc : center K = ⊥ := by
    have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot ↥hs100P hnab,
      Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h
    exact h
  have hZK : K ⊓ centralizer (K : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzK, hzC⟩
    have h : (⟨z, hzK⟩ : K) ∈ center K :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hzC g g.2)
    rw [hZKc, mem_bot] at h
    exact mem_bot.mpr (congrArg Subtype.val h)
  have hout5 : ¬ 5 ∣ Nat.card (Outer K) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    intro h5
    have := Nat.le_of_dvd houtc.1 h5
    omega
  have hN := normalizer_inf_le_of_card_center_eq R hER hE hEc hcore hZK hout5 h2 hZT
  set S : Subgroup ↥hs100P := (T : Subgroup K).map e.toMonoidHom with hSdef
  have hSc : Nat.card S = 5 ^ 3 := by
    rw [hSdef, Subgroup.card_map_of_injective e.injective, hTc]
  have hSH : normalizer (S : Set ↥hs100P) ≤ H := by
    rw [hSdef, hHdef, ← Subgroup.map_equiv_normalizer_eq]
    apply Subgroup.map_mono
    intro k hk
    have h1 : (k : Y) ∈ normalizer (((T : Subgroup K).map K.subtype : Subgroup Y) : Set Y) :=
      Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hk)
    rw [hT] at h1
    exact Subgroup.mem_subgroupOf.mpr (hN h1)
  obtain ⟨g⟩ := nonempty_mulEquiv_hsOUA_of_le hSc hSH hH hJ hne hJp hJs
  obtain ⟨u⟩ := nonempty_hsOUA_mulEquiv_catU35
  refine ⟨.sporadic .HS, .lie threeFourTwoU35Index, ?_, ⟨(e.trans eP.symm).trans eC⟩,
    (g.trans u).toMonoidHom, (g.trans u).surjective⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, threeFourTwoQFive, rfl, rfl,
    threeFourTwoU35Index, rfl, rfl, rfl⟩)))))

theorem threeFourTwoAt_hs :
    ThreeFourTwoAt 5 (TauCeti.CFSGIndex.sporadic .HS).Group := by
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have eP : CFSG.Blueprint.NativeSporadic.HS ≃* ↥hs100P := hs100Equiv
  exact ThreeFourTwoAt.of_mulEquiv (eP.symm.trans eC) threeFourTwoAt_hs100P

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
