module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeSolvParabPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphQuasi
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.AGLEmbedding.SubnormalSymThreeDetermined
import CFSG.LocalAnalysis.AGLEmbedding.SUPairInvolution
public import CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphProd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.SolvParab

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus (HasLeviCensus IsWBlock IsSpTwoLeviProduct)

private theorem perm3_mem_conj :
    ∀ x b : Equiv.Perm (Fin 3), x ≠ 1 → b ^ 3 = 1 →
      ∃ g : Equiv.Perm (Fin 3), b = x * g * x⁻¹ * g⁻¹ ∨ b = x ∨ b = x⁻¹ := by
  decide

private theorem perm3_prod_two :
    ∀ x : Equiv.Perm (Fin 3), ∃ s s' : Equiv.Perm (Fin 3), s ^ 2 = 1 ∧ s' ^ 2 = 1 ∧ x = s * s' := by
  decide

private theorem le_of_forall_sq_eq_one {Λ : Type} [Group Λ] {T H : Subgroup Λ}
    (e : ↥T ≃* Equiv.Perm (Fin 3)) (h : ∀ s ∈ T, s ^ 2 = 1 → s ∈ H) : T ≤ H := by
  intro x hx
  obtain ⟨s, s', hs, hs', hxs⟩ := perm3_prod_two (e ⟨x, hx⟩)
  have hsq : ∀ u : Equiv.Perm (Fin 3), u ^ 2 = 1 → ((e.symm u : ↥T) : Λ) ^ 2 = 1 := by
    intro u hu
    have h1 : (e.symm u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
    simpa using congrArg Subtype.val h1
  have hx' : x = ((e.symm s : ↥T) : Λ) * ((e.symm s' : ↥T) : Λ) := by
    have h1 := congrArg (fun z => ((e.symm z : ↥T) : Λ)) hxs
    simpa using h1
  rw [hx']
  exact H.mul_mem (h _ (e.symm s).2 (hsq s hs)) (h _ (e.symm s').2 (hsq s' hs'))

private def BlockCond (X : Type) [Group X] : Prop :=
  CFSG.pCore 2 X = ⊥ ∧
    ∀ H : Subgroup X, IsSubnormal H ⊤ → Nonempty (↥H ≃* Equiv.Perm (Fin 3)) → H = ⊤

private theorem BlockCond.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : BlockCond X) : BlockCond X' := by
  refine ⟨?_, fun H hH ⟨f⟩ => ?_⟩
  · rw [← CFSG.pCore_map_iso 2 e, h.1, Subgroup.map_bot]
  · set K := H.comap e.toMonoidHom with hK
    have hKm : K.map e.toMonoidHom = H := map_comap_eq_self_of_surjective e.surjective H
    have hs : IsSubnormal K ⊤ := by
      have h1 := hH.comap e.toMonoidHom
      rwa [comap_top] at h1
    have hb : Nonempty (↥K ≃* Equiv.Perm (Fin 3)) :=
      ⟨((K.equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hKm)).trans f⟩
    rw [← hKm, h.2 K hs hb, map_top_of_surjective _ e.surjective]

private theorem BlockCond.of_subsingleton {X : Type} [Group X] [Subsingleton X] : BlockCond X :=
  ⟨Subgroup.eq_bot_of_subsingleton _, fun H _ _ =>
    (Subgroup.eq_bot_of_subsingleton H).trans (Subgroup.eq_bot_of_subsingleton ⊤).symm⟩

private theorem BlockCond.of_isQuasisimple {X : Type} [Group X] [Finite X]
    (hq : Open.IsQuasisimple X) (ho : Odd (Nat.card (center X))) : BlockCond X :=
  ⟨ParabCensus.eq_bot_of_normal_isPGroup_two_of_isWBlock (Or.inl ⟨hq, ho⟩)
    (CFSG.pCore_normal (p := 2) (G := X)) CFSG.pCore_isPGroup,
    fun _ hH hb => (false_of_subnormal_symThree_of_isQuasisimple hq hb hH).elim⟩

private theorem BlockCond.perm_three : BlockCond (Equiv.Perm (Fin 3)) :=
  ⟨Prod.pCore_two_perm_three, fun _ _ ⟨f⟩ =>
    SymThree.eq_top_of_card_le_six (le_of_eq SymThree.card_perm_fin_three) f⟩

open CFSG.GH74.QTGen4.Leaves.F112 KFactProofs.SUThreeTwoShape in
private theorem BlockCond.statedSU {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    BlockCond ↥(StatedSU 3 2 K) := by
  refine ⟨ParabCensus.eq_bot_of_normal_isPGroup_two_of_isWBlock
    (Or.inr (Or.inr ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩))
    (CFSG.pCore_normal (p := 2) (G := ↥(StatedSU 3 2 K))) CFSG.pCore_isPGroup,
    fun H hH ⟨e⟩ => ?_⟩
  exfalso
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω, h2⟩ := exists_omega hK
  let o : OmegaData K := ⟨ω, hω, h2⟩
  have hrel : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
    ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
  have hcard := card_SUg hK
  have hord : orderOf (OmegaData.sF o) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := OmegaData.sF o)
      (by simpa using sF_sq_ne_one o) (by simpa using sF_four o)
    simpa using this
  haveI hEn : (heisSubgroup hrel).Normal := heisSubgroup_normal hcard hrel (sZ_ne_one o)
    (hrel.F_mem_normalizer (sF_mul_sS o) (sF_mul_sD o)) hord
  have hE3 : IsPGroup 3 (heisSubgroup hrel) :=
    IsPGroup.of_card (n := 3) (by rw [card_heisSubgroup hcard hrel (sZ_ne_one o)]; norm_num)
  have hEs : IsSubnormal (heisSubgroup hrel) ⊤ := IsSubnormal.of_mathlib hEn.isSubnormal
  obtain ⟨a, haH, ha1, ha3, hHa, ⟨t, htH, ht2, ht1⟩, -⟩ := Sym.symThree_data ⟨e⟩
  obtain ⟨hta, -⟩ := hHa t htH ht2 ht1
  have hcomm := SubnormalCommute.commute_oUpperTwo_of_symThree hH ⟨e⟩ hE3 hEs a
    (SymThreeDetermined.mem_oUpperTwo_of_cube haH ha3)
  have hS := congrArg mat (hcomm _ hrel.S_mem)
  have hD := congrArg mat (hcomm _ hrel.D_mem)
  simp only [mat_mul, OmegaData.sS, OmegaData.sD, mat_suMk] at hS hD
  have hsc := SevenFourL34.scalar_of_comm hω (mat a) hS.symm hD.symm
  have hat : t * a = a * t := by
    apply su_ext
    rw [mat_mul, mat_mul, hsc]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) (mat t)).eq.symm
  rw [hat, mul_inv_cancel_right] at hta
  refine ha1 (SUPair.eq_one_of_cube_of_sq ha3 ?_)
  rw [sq]
  nth_rewrite 2 [hta]
  exact mul_inv_cancel a

private theorem BlockCond.of_isWBlock {X : Type} [Group X] [Finite X] (h : IsWBlock X) :
    BlockCond X := by
  rcases h with ⟨hq, ho⟩ | ⟨⟨e⟩⟩ | ⟨K, hKf, hKfin, hK, ⟨e⟩⟩
  · exact BlockCond.of_isQuasisimple hq ho
  · exact BlockCond.perm_three.of_mulEquiv e.symm
  · letI := hKf
    haveI := hKfin
    exact (BlockCond.statedSU hK).of_mulEquiv e.symm

private theorem exists_mulSingle_eq_of_blockCond {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] (hG : ∀ i, BlockCond (G i))
    {X : Subgroup (∀ i, G i)} (hX : Nonempty (↥X ≃* Equiv.Perm (Fin 3)))
    (hXs : IsSubnormal X ⊤) :
    ∃ i, X = (⊤ : Subgroup (G i)).map (MonoidHom.mulSingle G i) := by
  classical
  obtain ⟨e₀⟩ := hX
  obtain ⟨a, haX, ha1, ha3, hXa, ⟨s, hsX, hs2, hs1⟩, hord⟩ := Sym.symThree_data ⟨e₀⟩
  obtain ⟨hinv, hXeq⟩ := hXa s hsX hs2 hs1
  obtain ⟨i, hai⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    push Not at h
    exact ha1 (funext h)
  set φ : Equiv.Perm (Fin 3) →* G i :=
    ((Pi.evalMonoidHom G i).comp X.subtype).comp e₀.symm.toMonoidHom with hφ
  have hφa : φ (e₀ ⟨a, haX⟩) = a i := by simp [hφ]
  have hb3 : (e₀ ⟨a, haX⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨a, haX⟩ : ↥X) ^ 3 = 1 from Subtype.ext (by simpa using ha3), map_one]
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    by_contra hy1
    obtain ⟨g, hg | hg | hg⟩ := perm3_mem_conj y _ hy1 hb3
    all_goals
      apply hai
      rw [← hφa, hg]
      simp [hy]
  have hinj : Function.Injective ((Pi.evalMonoidHom G i).comp X.subtype) := by
    have hcomp : (Pi.evalMonoidHom G i).comp X.subtype = φ.comp e₀.toMonoidHom := by
      ext x
      simp [hφ]
    rw [hcomp]
    exact hφinj.comp e₀.injective
  have hsub : IsSubnormal (X.map (Pi.evalMonoidHom G i)) ⊤ := by
    have h := hXs.map (Pi.evalMonoidHom G i)
    rwa [map_top_of_surjective _ (Prod.evalMonoidHom_surjective i)] at h
  obtain ⟨f⟩ := nonempty_map_mulEquiv e₀ hinj
  have htop : X.map (Pi.evalMonoidHom G i) = ⊤ := (hG i).2 _ hsub ⟨f⟩
  have e : G i ≃* Equiv.Perm (Fin 3) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans f)
  have ha3i : a i ^ 3 = 1 := by simpa using congrFun ha3 i
  have hs2i : s i ^ 2 = 1 := by simpa using congrFun hs2 i
  have hinvi : s i * a i * (s i)⁻¹ = (a i)⁻¹ := by simpa using congrFun hinv i
  have hs1i : s i ≠ 1 := by
    intro h
    rw [h, one_mul, inv_one, mul_one] at hinvi
    refine hai (SUPair.eq_one_of_cube_of_sq ha3i ?_)
    rw [sq]
    nth_rewrite 2 [hinvi]
    exact mul_inv_cancel _
  have hconj : ∀ β : G i, β ^ 3 = 1 → β ≠ 1 → s i * β * (s i)⁻¹ = β⁻¹ := by
    intro β hβ3 hβ1
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv]
    refine Prod.perm3_invol_inv_of_order_three (e (s i)) ?_ ?_ (e β) ?_ ?_
    · rw [← map_pow, hs2i, map_one]
    · exact fun h => hs1i (e.injective (h.trans (map_one e).symm))
    · rw [← map_pow, hβ3, map_one]
    · exact fun h => hβ1 (e.injective (h.trans (map_one e).symm))
  have hpow : ∀ β : G i, β ^ 3 = 1 → (Pi.mulSingle i β : ∀ j, G j) ^ 3 = 1 := by
    intro β hβ3
    have h := (MonoidHom.mulSingle G i).map_pow β 3
    rw [hβ3, map_one] at h
    simpa using h.symm
  have hmemX : ∀ β : G i, β ^ 3 = 1 → β ≠ 1 → (Pi.mulSingle i β : ∀ j, G j) ∈ X := by
    intro β hβ3 hβ1
    refine Sym.mem_of_inv_involution ⟨e₀⟩ hXs hsX hs2 hs1 (hpow β hβ3) ?_
    rw [Prod.conj_mulSingle, hconj β hβ3 hβ1]
    exact Pi.mulSingle_inv i β
  have hm1 : (Pi.mulSingle i (a i) : ∀ j, G j) ≠ 1 := by
    intro h
    apply hai
    simpa using congrFun h i
  have hma := hord _ (hmemX (a i) ha3i hai) (hpow (a i) ha3i) hm1
  have hak : ∀ k, k ≠ i → a k = 1 := by
    intro k hk
    rcases hma with h | h <;> simpa [Pi.mulSingle_eq_of_ne hk] using (congrFun h k).symm
  have hsk : ∀ k, k ≠ i → s k = 1 := fun k hk =>
    Prod.coord_eq_one_of_pCore_two hXs hXeq hsX hs2 (hG k).1 (hak k hk)
  refine ⟨i, ?_⟩
  set A : Subgroup (∀ j, G j) := (⊤ : Subgroup (G i)).map (MonoidHom.mulSingle G i) with hA
  have hsupp : ∀ x : ∀ j, G j, (∀ k, k ≠ i → x k = 1) → x ∈ A := by
    intro x hx
    refine ⟨x i, trivial, ?_⟩
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hx j hji, Pi.mulSingle_eq_of_ne hji]
  have hle : X ≤ A := by
    rw [hXeq, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hsupp _ hak
    · exact hsupp _ hsk
  haveI : Finite X := Sym.finite_symThree ⟨e₀⟩
  have hAcard : Nat.card A = 6 := by
    rw [hA, Subgroup.card_map_of_injective (Pi.mulSingle_injective i), Subgroup.card_top,
      SymThree.card_eq_six_of_mulEquiv e]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard, Sym.card_symThree ⟨e₀⟩])

private theorem symThreePairs_pi_of_blockCond {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ i, Group (G i)] [∀ i, Finite (G i)] (hG : ∀ i, BlockCond (G i)) :
    SymThreePairs (∀ i, G i) :=
  symThreePairs_pi fun _ hXs hX => exists_mulSingle_eq_of_blockCond hG hX hXs

theorem symThreePairs_of_hasLeviCensus {R : Type} [Group R] [Finite R]
    (h : HasLeviCensus R IsWBlock) : SymThreePairs (R ⧸ CFSG.pCore 2 R) := by
  classical
  obtain ⟨Q, hQgroup, hQfin, σ, k, G, hGgroup, hGfin, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS,
    -⟩ := h
  letI : Group Q := hQgroup
  letI : Finite Q := hQfin
  letI : ∀ j, Group (G j) := hGgroup
  letI : ∀ j, Finite (G j) := hGfin
  set Λ : Subgroup (∀ j, G j) := β.range with hΛ
  set NΛ : Subgroup ↥Λ := (Subgroup.pi Set.univ S).subgroupOf Λ with hNΛ
  set D : Subgroup ↥Λ := (σ.ker).map β.rangeRestrict with hD
  set Rhat := R ⧸ CFSG.pCore 2 R
  have hodd : Odd ((Subgroup.pi Set.univ S).relIndex Λ) := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact hi (Nat.dvd_iff_mod_eq_zero.mpr (Nat.even_iff.mp he))
  have hpcΛ : CFSG.pCore 2 ↥Λ = ⊥ :=
    ParabCensus.pCore_two_eq_bot_of_le_normalizer_of_odd_relIndex hle hn hodd hS
  let φ : Q →* Rhat := (QuotientGroup.mk' (CFSG.pCore 2 R)).comp σ
  have hφsurj : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hσ
  have hβker_le : β.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hσx : σ x ∈ (β.ker).map σ := Subgroup.mem_map_of_mem σ hx
    have hle_pc : (β.ker).map σ ≤ CFSG.pCore 2 R :=
      le_sSup ⟨(inferInstance : β.ker.Normal).map σ hσ, hβ.map σ⟩
    change (QuotientGroup.mk' (CFSG.pCore 2 R)) (σ x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hle_pc hσx
  let ψbar : Q ⧸ β.ker →* Rhat := QuotientGroup.lift β.ker φ hβker_le
  let ψ : ↥Λ →* Rhat := ψbar.comp (QuotientGroup.quotientKerEquivRange β).symm.toMonoidHom
  have hψβ : ∀ q : Q, ψ ⟨β q, ⟨q, rfl⟩⟩ = φ q := by
    intro q
    have h2 : (QuotientGroup.quotientKerEquivRange β).symm ⟨β q, ⟨q, rfl⟩⟩ =
        QuotientGroup.mk q := by
      apply (QuotientGroup.quotientKerEquivRange β).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h2]
    exact QuotientGroup.lift_mk β.ker hβker_le q
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := hφsurj r
    exact ⟨⟨β q, ⟨q, rfl⟩⟩, by rw [hψβ q]; exact hq⟩
  have hpc_le : CFSG.pCore 2 Q ≤ β.ker := by
    have hnorm : ((CFSG.pCore 2 Q).map β.rangeRestrict).Normal :=
      (CFSG.pCore_normal (p := 2) (G := Q)).map β.rangeRestrict
        (MonoidHom.rangeRestrict_surjective β)
    have h2 : IsPGroup 2 ((CFSG.pCore 2 Q).map β.rangeRestrict) :=
      (CFSG.pCore_isPGroup (p := 2) (G := Q)).map β.rangeRestrict
    have hle_pc : (CFSG.pCore 2 Q).map β.rangeRestrict ≤ CFSG.pCore 2 ↥Λ :=
      le_sSup ⟨hnorm, h2⟩
    rw [hpcΛ] at hle_pc
    intro x hx
    have hxmap : β.rangeRestrict x ∈ (CFSG.pCore 2 Q).map β.rangeRestrict :=
      Subgroup.mem_map_of_mem β.rangeRestrict hx
    rw [le_bot_iff.mp hle_pc, Subgroup.mem_bot] at hxmap
    rw [MonoidHom.mem_ker]
    simpa using congrArg Subtype.val hxmap
  have hH_eq : (CFSG.pCore 2 R).comap σ ≤ σ.ker ⊔ β.ker := by
    let H : Subgroup Q := (CFSG.pCore 2 R).comap σ
    have hHN : H.Normal := (CFSG.pCore_normal (p := 2) (G := R)).comap σ
    have hZH : σ.ker ≤ H := by
      intro z hz
      rw [Subgroup.mem_comap]
      rw [MonoidHom.mem_ker] at hz
      rw [hz]
      exact (CFSG.pCore 2 R).one_mem
    haveI hZn : (σ.ker.subgroupOf H).Normal := (inferInstance : σ.ker.Normal).subgroupOf H
    have hquot : IsPGroup 2 (↥H ⧸ σ.ker.subgroupOf H) :=
      ParabCensus.isPGroup_quotient_subgroupOf_comap hσ rfl CFSG.pCore_isPGroup
    calc
      (CFSG.pCore 2 R).comap σ ≤ σ.ker ⊔ CFSG.pCore 2 Q :=
        ParabCensus.le_sup_pCore_two_of_central_odd_quotient_two hHN hZH hc ho hquot
      _ ≤ σ.ker ⊔ β.ker := sup_le le_sup_left (hpc_le.trans le_sup_right)
  have hψker : ψ.ker ≤ D := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨q, hqx⟩ := x.2
    have hxq : x = ⟨β q, ⟨q, rfl⟩⟩ := Subtype.ext hqx.symm
    have hx' : ψ ⟨β q, ⟨q, rfl⟩⟩ = 1 := by rwa [← hxq]
    have hφq : φ q = 1 := by rwa [← hψβ q]
    have hqH : q ∈ (CFSG.pCore 2 R).comap σ := by
      rw [Subgroup.mem_comap, ← QuotientGroup.eq_one_iff]
      exact hφq
    have hq : q ∈ σ.ker ⊔ β.ker := hH_eq hqH
    rw [Subgroup.mem_sup_of_normal_left] at hq
    obtain ⟨z, hz, k, hk, hzk⟩ := hq
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    apply Subtype.ext
    rw [← hqx, ← hzk, map_mul, MonoidHom.mem_ker.mp hk, mul_one]
    rfl
  have hDc : D ≤ center ↥Λ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := MonoidHom.rangeRestrict_surjective β g
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hc hz) q]
  have hDo : Odd (Nat.card D) := ho.of_dvd_nat (card_map_dvd _ _)
  have hNle : ∀ T : Subgroup ↥Λ, IsSubnormal T ⊤ → Nonempty (↥T ≃* Equiv.Perm (Fin 3)) →
      T ≤ NΛ := by
    rintro T - ⟨e⟩
    refine le_of_forall_sq_eq_one e fun u _ hu => ?_
    rw [hNΛ, mem_subgroupOf]
    exact ComponentClassification.AS76b.Lemma22Full.mem_of_pow_eq_one_of_odd_relIndex hle hn
      hodd u.2 (k := 1) (by simpa using congrArg Subtype.val hu)
  have hblock : ∀ j, BlockCond ↥(S j) := by
    intro j
    rcases hS j with hbot | hW
    · haveI : Subsingleton ↥(S j) := by rw [hbot]; infer_instance
      exact BlockCond.of_subsingleton
    · exact BlockCond.of_isWBlock hW
  have hN : SymThreePairs ↥NΛ :=
    (symThreePairs_pi_of_blockCond hblock).of_mulEquiv
      ((subgroupOfEquivOfLe hle).trans (ParabCensus.piSubgroupEquiv S)).symm
  exact (hN.of_le NΛ hNle).of_surjective ψ hψsurj (hψker.trans hDc)
    (hDo.of_dvd_nat (card_dvd_of_le hψker))

theorem symThreePairs_of_isSpTwoLeviProduct {R : Type} [Group R] [Finite R]
    (h : IsSpTwoLeviProduct R) : SymThreePairs (R ⧸ CFSG.pCore 2 R) := by
  classical
  obtain ⟨k, X, hXg, hXf, ⟨e⟩, hX⟩ := h
  letI := hXg
  letI := hXf
  refine (symThreePairs_pi fun T hT hb => ?_).of_mulEquiv e.symm
  obtain ⟨i, -, hi⟩ := Prod.exists_mulSingle_eq_of_subnormal_symThree
    (fun i => Sp.prodFactor_of_isSpTwoFactor (hX i)) hb hT
  exact ⟨i, hi⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.SolvParab
