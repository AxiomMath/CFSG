module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Reduction
public import CFSG.HardMathSupport.Dickson.Bal207.ExcG28
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28TwentySeven

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open scoped commutatorElement

section Rank

variable {X : Type} [Group X] [Finite X]

theorem su38_isElemAbelian_of_le {p : ℕ} {B E : Subgroup X} (hB : IsElemAbelian p B) (hE : E ≤ B) :
    IsElemAbelian p E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hB.2 x (hE hx)⟩
  apply Subtype.ext
  change (a : X) * b = b * a
  exact congrArg Subtype.val (hB.1.is_comm.comm ⟨a, hE a.2⟩ ⟨b, hE b.2⟩)

theorem su38_isPGroup_three {E : Subgroup X} (hE : IsElemAbelian 3 E) :
    IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem twentySeven_le_card_of_pRank {A B C : Subgroup X} (hB : IsElemAbelian 3 B) (hAB : A ≤ B)
    (hCB : C ≤ B) (hAC : A ⊓ C = ⊥) (hsup : A ⊔ C = B)
    (hpr : CFSG.Open.pRank 3 C + 3 ≤ CFSG.Open.pRank 3 B) : 27 ≤ Nat.card A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ A, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hAB hx⟩ ⟨y, hCB hy⟩)
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A C hcomm
  rw [hsup, hAC, Subgroup.card_bot, mul_one] at hprod
  have hCe : IsElemAbelian 3 C := su38_isElemAbelian_of_le hB hCB
  obtain ⟨k, hk⟩ := (su38_isPGroup_three hCe).exists_card_eq
  have hkC : k ≤ CFSG.Open.pRank 3 C := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hCe hk
  obtain ⟨E, hEB, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) B
  have h1 : 3 ^ CFSG.Open.pRank 3 B ≤ Nat.card B := by
    rw [← hEcard]
    exact Subgroup.card_le_of_le hEB
  have h2 : 3 ^ CFSG.Open.pRank 3 C * 27 ≤ 3 ^ CFSG.Open.pRank 3 B := by
    calc 3 ^ CFSG.Open.pRank 3 C * 27 = 3 ^ (CFSG.Open.pRank 3 C + 3) := by
          rw [pow_add]; norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hpr
  have h3 : Nat.card A * Nat.card C ≤ Nat.card A * 3 ^ CFSG.Open.pRank 3 C := by
    rw [hk]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hkC)
  have h4 : 3 ^ CFSG.Open.pRank 3 C * 27 ≤ 3 ^ CFSG.Open.pRank 3 C * Nat.card A := by
    calc 3 ^ CFSG.Open.pRank 3 C * 27 ≤ 3 ^ CFSG.Open.pRank 3 B := h2
      _ ≤ Nat.card B := h1
      _ = Nat.card A * Nat.card C := hprod
      _ ≤ Nat.card A * 3 ^ CFSG.Open.pRank 3 C := h3
      _ = 3 ^ CFSG.Open.pRank 3 C * Nat.card A := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

theorem exists_subgroup_card_twentySeven {A : Subgroup X} (hA : IsElemAbelian 3 A)
    (h27 : 27 ≤ Nat.card A) : ∃ A₀ : Subgroup X, A₀ ≤ A ∧ Nat.card A₀ = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (su38_isPGroup_three hA).exists_card_eq
  have hm3 : 3 ≤ m := by
    have : 3 ^ 3 ≤ 3 ^ m := by rw [← hm]; exact h27
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  obtain ⟨A₀, hA₀, -, hA₀A⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (n := 3) (H := ⊥) (L := A) (by simp) (hm ▸ pow_dvd_pow 3 hm3) bot_le
  exact ⟨A₀, hA₀A, by rw [hA₀]; norm_num⟩

theorem autImageRankThree_of_pRank {K B A : Subgroup X} (hperf : ⁅K, K⁆ = K)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hAB : A ≤ B)
    (hdisj : A ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hsup : A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B)
    (hpr : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + 3 ≤ CFSG.Open.pRank 3 B) :
    KSF4SU3.AutImageRankThree B K := by
  have hAC : A ⊓ (B ⊓ Subgroup.centralizer (K : Set X)) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left A inf_le_right).trans hdisj.le)
  have h27 := twentySeven_le_card_of_pRank hB hAB inf_le_left hAC hsup hpr
  obtain ⟨A₀, hA₀A, hA₀⟩ := exists_subgroup_card_twentySeven (su38_isElemAbelian_of_le hB hAB) h27
  have hA₀B : A₀ ≤ B := hA₀A.trans hAB
  have hA₀N : A₀ ≤ Subgroup.normalizer (K : Set X) := hA₀B.trans hBN
  let φ : ↥A₀ →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
    (actHom K).comp (Subgroup.inclusion hA₀N)
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun a ha => ?_
    have hc : (a : X) ∈ Subgroup.centralizer (K : Set X) :=
      KSF4SU3.mem_centralizer_of_actHom_eq_one hperf (hA₀N a.2) ha
    have : (a : X) ∈ A ⊓ Subgroup.centralizer (K : Set X) := ⟨hA₀A a.2, hc⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact Subtype.ext this
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact mem_autImage.2 ⟨a, hA₀N a.2, hA₀B a.2, rfl⟩
  · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      change (x : MulAut (↥K ⧸ Subgroup.center ↥K)) * y = y * x
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      have hab : (a : X) * b = b * a :=
        congrArg Subtype.val (hB.1.is_comm.comm ⟨a, hA₀B a.2⟩ ⟨b, hA₀B b.2⟩)
      exact Subtype.ext hab
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hB.2 a (hA₀B a.2))
      rw [this, map_one]
  · rw [← hA₀]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm

end Rank

section Normalizer

variable {X : Type} [Group X] [Finite X]

theorem mem_normalizer_of_normalizes_sub {K J : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hJK : J ≤ K) (hJ : ⁅J, J⁆ ≠ ⊥) {s : X}
    (hs : s ∈ Subgroup.normalizer (J : Set X)) : s ∈ Subgroup.normalizer (K : Set X) := by
  have hKc : CFSG.IsComponent K :=
    ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hK.2.2,
      CFSG.Open.IsSubnormal.top_iff.1 hK.2.1⟩
  have hK'c := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hKc
  rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with h | h
  · exact mem_normalizer_of_map_conj_eq h.symm
  · exfalso
    apply hJ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hsy : s⁻¹ * y * s ∈ J := by
      have h1 : s⁻¹ ∈ Subgroup.normalizer (J : Set X) := inv_mem hs
      have := (Subgroup.mem_normalizer_iff.1 h1 y).1 hy
      simpa using this
    have hyK' : y ∈ K.map (MulAut.conj s).toMonoidHom :=
      ⟨s⁻¹ * y * s, hJK hsy, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hc : x ∈ K := hJK hx
    have h2 : ⁅x, y⁆ ∈ ⁅K, K.map (MulAut.conj s).toMonoidHom⁆ :=
      Subgroup.commutator_mem_commutator hc hyK'
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm

theorem ne_bot_of_glaPComponent {p : ℕ} {Y J : Subgroup X} (hJ : GLAPComponent p Y J) :
    J ≠ ⊥ := by
  intro h
  have hq := hJ.2.2.1.2.2
  change CFSG.Open.IsQuasisimple ↥((J.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore p Y)))
    at hq
  rw [h, Subgroup.bot_subgroupOf, Subgroup.map_bot] at hq
  exact (Subgroup.nontrivial_iff_ne_bot _).1
    (CFSG.ComponentClassification.Quasisimple.nontrivial hq) rfl

theorem su38_map_le_normalizer_map {M M' : Type*} [Group M] [Group M'] (f : M ≃* M')
    {E Y : Subgroup M} (h : E ≤ Subgroup.normalizer (Y : Set M)) :
    E.map f.toMonoidHom ≤
      Subgroup.normalizer ((Y.map f.toMonoidHom : Subgroup M') : Set M') := by
  have key : ∀ z : M, f z ∈ Y.map f.toMonoidHom ↔ z ∈ Y := fun z =>
    ⟨fun ⟨w, hw, hwz⟩ => (f.injective hwz) ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
  rintro _ ⟨n, hn, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y'
  obtain ⟨y, rfl⟩ := f.surjective y'
  have e : (f.toMonoidHom n) * f y * (f.toMonoidHom n)⁻¹ = f (n * y * n⁻¹) := by simp
  show f y ∈ Y.map f.toMonoidHom ↔ (f.toMonoidHom n) * f y * (f.toMonoidHom n)⁻¹ ∈
    Y.map f.toMonoidHom
  rw [e, key, key]
  exact Subgroup.mem_normalizer_iff.1 (h hn) y

end Normalizer

section Kill


set_option linter.unusedSectionVars false

theorem g28K0 {Q : Type} [Group Q]
    (hQ : Nonempty (Q ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.Tag.G2 (GaloisField 2 3))))
    {E : Subgroup (MulAut Q)} (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    {Y : Subgroup (MulAut Q)} (hY3 : ¬ 3 ∣ Nat.card Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set (MulAut Q))) : Y = ⊥ := by
  obtain ⟨e⟩ := hQ
  let f : MulAut Q ≃* MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup
    CFSG.Blueprint.Chevalley.Tag.G2 (GaloisField 2 3)) := MulAut.congr e
  have hK8 : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  haveI : CharP (GaloisField 2 3) 2 := inferInstance
  obtain ⟨M'⟩ := CFSG.RankThree.PartTwo.Sec4.Item434G28.exists_model
    (K := GaloisField 2 3) hK8
  have hZK := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    (τ := CFSG.Blueprint.Chevalley.Tag.G2) (K := GaloisField 2 3)
  have hO := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.card_outer_adjointG2 hK8
  have hN : IsElemAbelian 3 (E.map f.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map hE _
  have hN27 : Nat.card (E.map f.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact hE27
  obtain ⟨E₉, hEe, hE9, hEN⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.exists_map_conj_le_of_card_27 hZK
      (by rw [hO]; norm_num) hN hN27
  have hY3' : ¬ 3 ∣ Nat.card (Y.map f.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact hY3
  have hYN := su38_map_le_normalizer_map f hEY
  have hY0 : Y.map f.toMonoidHom = ⊥ := by
    refine CFSG.RankThree.PartTwo.Sec4.Item434G28.eq_bot_of_hyperplanes hZK hO hN hN27 hEN ?_ ?_
      hY3' hYN
    · intro E' hE' hE'9 x hx
      exact M'.pow_nine_of_centralizes hK8 hE' hE'9 x hx
    · intro α hα3 hαout hαE W hW3 hαW hEW
      exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.eq_bot_of_fixed_outer M' hK8 hEe hE9 α
        hα3 hαout hαE W hW3 hαW hEW
  exact (Subgroup.map_eq_bot_iff_of_injective Y f.injective).1 hY0

theorem centralizes_of_autImageRankThree_g28 {X : Type} [Group X] [Finite X] {B K S : Subgroup X}
    (hperf : ⁅K, K⁆ = K) (hK : IsLieQuot ↥K IsG2EightIndex)
    (hE : KSF4SU3.AutImageRankThree B K) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hS3 : Nat.Coprime 3 (Nat.card S))
    (hBS : B ⊓ Subgroup.normalizer (K : Set X) ≤ Subgroup.normalizer (S : Set X)) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨E, hEA, hEel, hE27⟩ := hE
  have hEY := hEA.trans (autImage_le_normalizer_imageIn hBS)
  have h1 : imageIn K S = ⊥ :=
    g28K0 (excG28_model hK) hEel hE27 (not_three_dvd_card_imageIn hSN hS3) hEY
  exact centralizes_of_imageIn_eq_bot hperf hSN h1

theorem isStronglyLocallyOneBalanced_of_g28
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X] [Finite X]
    {K B A : Subgroup X} (ctx : Bal207PlusCtx G 3 K B A) (hq : IsLieQuot ↥K IsG2EightIndex)
    (hpr : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + 3 ≤ CFSG.Open.pRank 3 B)
    {a : X} {J : Subgroup X} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X)) : IsStronglyLocallyOneBalanced 3 B a J := by
  have hperfK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨ctx.comp.2.2.1⟩
  have hE := autImageRankThree_of_pRank hperfK ctx.scp.2.1 ctx.norm ctx.le ctx.disj ctx.sup hpr
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJab : ⁅J, J⁆ ≠ ⊥ := by
    rw [glaPComponent_perfect hJ]
    exact ne_bot_of_glaPComponent hJ
  refine KSF4Kit.isStronglyLocallyOneBalanced_of_centralizes fun S hS hcop hBS => ?_
  have hSJ : S ≤ Subgroup.normalizer (J : Set X) := hS.trans inf_le_left
  have hSK : S ≤ Subgroup.normalizer (K : Set X) := fun s hs =>
    mem_normalizer_of_normalizes_sub ctx.comp hJK hJab (hSJ hs)
  have hBS' : B ⊓ Subgroup.normalizer (K : Set X) ≤ Subgroup.normalizer (S : Set X) :=
    fun b hb => hBS ⟨hb.1, hBJ hb.1⟩
  exact (centralizes_of_autImageRankThree_g28 hperfK hq hE hSK hcop hBS').trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hJK))

end Kill

end CFSG.HardMathSupport.Dickson.Bal207

end
