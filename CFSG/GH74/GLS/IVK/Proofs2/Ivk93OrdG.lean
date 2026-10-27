module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Nu
public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.Stage2.Local.Lemma23

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

section Commute

variable {Q : Type*} [Group Q]

private theorem exists_mul_of_mem_sup_of_forall_commute {A B : Subgroup Q}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : Q} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  have hAN : A ≤ Subgroup.normalizer (B : Set Q) := fun a ha =>
    Subgroup.centralizer_le_normalizer (B : Set Q)
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (h a ha b hb).symm)
  have hg' : g ∈ (↑(A ⊔ B) : Set Q) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAN] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  exact ⟨a, ha, b, hb, rfl⟩

private theorem card_sup_mul_card_inf_of_forall_commute [Finite Q] {A B : Subgroup Q}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let φ : ↥A × ↥B →* Q := A.subtype.noncommCoprod B.subtype (fun a b => h a a.2 b b.2)
  have hφ : ∀ (a : A) (b : B), φ (a, b) = (a : Q) * b := fun a b =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hrange : φ.range = A ⊔ B := by
    refine (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : Q), k.1.1.2, by
          have h1 : (k.1.1 : Q) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          have h2 : (k.1.1 : Q) = (k.1.2 : Q)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [h2]
          exact B.inv_mem k.1.2.2⟩
        invFun := fun g => ⟨(⟨g, g.2.1⟩, ⟨(g : Q)⁻¹, B.inv_mem g.2.2⟩), by
          rw [MonoidHom.mem_ker, hφ]
          exact mul_inv_cancel _⟩
        left_inv := fun k => by
          refine Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext ?_))
          have h1 : (k.1.1 : Q) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          exact inv_eq_of_mul_eq_one_right h1
        right_inv := fun g => Subtype.ext rfl }
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker, Nat.card_prod] at h1
  rw [mul_comm]
  exact h1

private theorem sup_le_normalizer_of_forall_commute {A B : Subgroup Q}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ⊔ B ≤ Subgroup.normalizer (A : Set Q) := by
  refine sup_le Subgroup.le_normalizer ?_
  intro b hb
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact h a ha b hb

private theorem card_eq_of_hasSL2Model {K : Type} [Group K] {q : ℕ}
    (hK : HasSL2Model K (fun r => r = q)) : Nat.card K = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hK
  have hFq' : Nat.card F = q := hFq
  rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 2 F).symm).toEquiv,
    CFSG.GorensteinWalter.sl2_card_formula F, hFq']

private theorem two_le_relIndex_of_le_of_ne {X : Type*} [Group X] [Finite X] {H K : Subgroup X}
    (hHK : H ≤ K) (hne : H ≠ K) : 2 ≤ H.relIndex K := by
  have h0 : H.relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : H.relIndex K ≠ 1 := fun h => hne (le_antisymm hHK (Subgroup.relIndex_eq_one.mp h))
  omega

end Commute

section Order

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem isSylowOf_RC (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (RC S z) (LC z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ((LC z).subgroupOf (Cen z)).Normal := Stage1.Thm6.Prod.LC_normal z
  exact hS.inf_of_le_normalizer (LC_le_Cen z)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (LC_le_Cen z)).mp hN)

theorem factorization_card_LC (z : G) :
    (Nat.card ↥(LC z)).factorization 2 = (Nat.card ↥(LBar z)).factorization 2 := by
  let H : Subgroup ↥(Cen z) := (LC z).subgroupOf (Cen z)
  let φ : ↥H →* CentralizerBar z := (toBar z).comp H.subtype
  have hH : Nat.card ↥H = Nat.card ↥(LC z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (LC_le_Cen z)).toEquiv
  have hrange : φ.range = LBar z := by
    show ((toBar z).comp H.subtype).range = LBar z
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : Odd (Nat.card ↥φ.ker) := by
    have h1 : Nat.card ↥φ.ker ∣ Nat.card ↥(toBar z).ker := by
      have hc : Nat.card ↥(φ.ker.map H.subtype) = Nat.card ↥φ.ker :=
        Subgroup.card_map_of_injective H.subtype_injective
      rw [← hc]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨c, hc, rfl⟩
      exact hc
    exact Odd.of_dvd_nat (odd_card_ker_toBar z) h1
  have h2 := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hH] at h2
  have h3 : ¬ 2 ∣ Nat.card ↥φ.ker := by
    obtain ⟨k, hk⟩ := hker
    omega
  rw [← h2, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h3, zero_add]

theorem card_RC_eq_two_pow (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) :
    Nat.card ↥(RC S z) = 2 ^ (Nat.card ↥(LBar z)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(isSylowOf_RC hS).card_eq, factorization_card_LC]

theorem two_mul_card_LBar {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hprod : IsCentralProd L₁ L₂ (LBar z)) (h₁ : HasSL2Model ↥L₁ (fun r => r = q))
    (h₂ : HasSL2Model ↥L₂ (fun r => r = q)) :
    Nat.card ↥(LBar z) * 2 = (q * (q ^ 2 - 1)) ^ 2 := by
  obtain ⟨hsup, hcomm, hinf⟩ := hprod
  have h := card_sup_mul_card_inf_of_forall_commute hcomm
  rw [hsup, hinf, card_eq_of_hasSL2Model h₁, card_eq_of_hasSL2Model h₂] at h
  rw [h]
  ring

theorem card_RC_pair {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) (hp : Stage1Pair G z S q L₁ L₂) :
    Nat.card ↥(RC S z) = 2 ^ nuQ q := by
  rw [card_RC_eq_two_pow hS]
  congr 1
  unfold nuQ
  rw [← two_mul_card_LBar hp.prod hp.sl₁ hp.sl₂, Nat.mul_div_cancel _ (by norm_num)]

end Order

section L4

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

omit [Finite G] in
theorem LBar_le_normalizer {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hprod : IsCentralProd L₁ L₂ (LBar z)) :
    LBar z ≤ normalizer (L₁ : Set (CentralizerBar z)) ∧
      LBar z ≤ normalizer (L₂ : Set (CentralizerBar z)) := by
  refine ⟨?_, ?_⟩
  · rw [← hprod.1]
    exact sup_le_normalizer_of_forall_commute hprod.2.1
  · rw [← hprod.1, sup_comm]
    exact sup_le_normalizer_of_forall_commute fun b hb a ha => (hprod.2.1 a ha b hb).symm

omit [Finite G] in
theorem mem_S1_of {s : G} (hsS : s ∈ S) (hs : s ∈ Cen z)
    (h : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K ≤ LBar z →
      toBar z ⟨s, hs⟩ ∈ normalizer (K : Set (CentralizerBar z))) : s ∈ S1 S z := by
  refine ⟨hsS, ⟨s, hs⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_iInf]
  intro K
  rw [Subgroup.mem_iInf]
  intro hK
  exact h K hK.1 hK.2

omit [Finite G] in
theorem toBar_mem_normalizer_of_mem_S1 {s : G} (hs : s ∈ S1 S z) (hsC : s ∈ Cen z)
    {K : Subgroup (CentralizerBar z)} (hK : IsComponent K) (hKL : K ≤ LBar z) :
    toBar z ⟨s, hsC⟩ ∈ normalizer (K : Set (CentralizerBar z)) := by
  obtain ⟨-, c, hc, hcs⟩ := hs
  have hc' : c = ⟨s, hsC⟩ := Subtype.ext hcs
  rw [hc', SetLike.mem_coe, Subgroup.mem_iInf] at hc
  have := hc K
  rw [Subgroup.mem_iInf] at this
  exact this ⟨hK, hKL⟩

theorem RC_le_S1 {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : Stage1Pair G z S q L₁ L₂) : RC S z ≤ S1 S z := by
  intro r hr
  have hrC : r ∈ Cen z := LC_le_Cen z hr.2
  have hbar : toBar z ⟨r, hrC⟩ ∈ LBar z := ⟨⟨r, hrC⟩, hr.2, rfl⟩
  refine mem_S1_of hr.1 hrC fun K hK _ => ?_
  have hK' : K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hp.comps]
    exact hK
  rcases hK' with rfl | hK'
  · exact (LBar_le_normalizer hp.prod).1 hbar
  · rw [Set.mem_singleton_iff] at hK'
    subst hK'
    exact (LBar_le_normalizer hp.prod).2 hbar

theorem S1_ne_S {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : Stage1Pair G z S q L₁ L₂) : S1 S z ≠ S := by
  intro hEq
  obtain ⟨s, hsS, hsC, hc1, -⟩ := hp.swap
  have hsS1 : s ∈ S1 S z := hEq.symm ▸ hsS
  have hK₁ : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [hp.comps]
      exact Set.mem_insert _ _
    exact this
  have hL₁ : L₁ ≤ LBar z := hp.prod.1 ▸ le_sup_left
  have hnorm := toBar_mem_normalizer_of_mem_S1 hsS1 hsC hK₁ hL₁
  have := conjugate_eq_self_of_mem_normalizer hnorm
  rw [hc1] at this
  exact hp.ne this.symm

theorem RC_ne_S1 {ε : Bool} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : Stage1L4 G z S ε q L₁ L₂) : RC S z ≠ S1 S z := by
  intro hEq
  have hle : S1 S z ≤ RC S z := hEq.symm.le
  have hT : SBar (S1 S z) z ≤ LBar z := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, (hle (Subgroup.mem_subgroupOf.mp hc)).2, rfl⟩
  obtain ⟨hNorm, hPGL⟩ := hp.pgl.1
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := hPGL
  have hFq' : Nat.card F = q := hFq
  have hL₁Λ : L₁ ≤ LBar z := hp.pair.prod.1 ▸ le_sup_left
  have hYΛ : L₁ ⊔ SBar (S1 S z) z ≤ LBar z := sup_le hL₁Λ hT
  have hL₁Y : L₁ ≤ L₁ ⊔ SBar (S1 S z) z := le_sup_left
  have hL₂C : ∀ b ∈ L₂, b ∈ centralizer (L₁ : Set (CentralizerBar z)) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hp.pair.prod.2.1 a ha b hb
  let N : Subgroup ↥(L₁ ⊔ SBar (S1 S z) z) :=
    (centralizer (L₁ : Set (CentralizerBar z))).subgroupOf (L₁ ⊔ SBar (S1 S z) z)
  let π : ↥L₁ →* ↥(L₁ ⊔ SBar (S1 S z) z) ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion hL₁Y)
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨⟨y₀, hy₀⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_forall_commute hp.pair.prod.2.1
      (hp.pair.prod.1 ▸ hYΛ hy₀)
    refine ⟨⟨a, ha⟩, ?_⟩
    show QuotientGroup.mk (⟨a, hL₁Y ha⟩ : ↥(L₁ ⊔ SBar (S1 S z) z)) = QuotientGroup.mk ⟨y₀, hy₀⟩
    rw [QuotientGroup.eq]
    show a⁻¹ * y₀ ∈ centralizer (L₁ : Set (CentralizerBar z))
    rw [← hab, inv_mul_cancel_left]
    exact hL₂C b hb
  have hker : 2 ≤ Nat.card ↥π.ker := by
    have h2 : Nat.card ↥(L₁ ⊓ L₂) = 2 := hp.pair.prod.2.2
    have h3 : Nat.card ↥(L₁ ⊓ L₂) ≤ Nat.card ↥π.ker := by
      refine Nat.card_le_card_of_injective
        (fun w : ↥(L₁ ⊓ L₂) => (⟨⟨(w : CentralizerBar z), w.2.1⟩, ?_⟩ : ↥π.ker)) ?_
      · rw [MonoidHom.mem_ker]
        show (QuotientGroup.mk (⟨(w : CentralizerBar z), hL₁Y w.2.1⟩ :
          ↥(L₁ ⊔ SBar (S1 S z) z)) : ↥(L₁ ⊔ SBar (S1 S z) z) ⧸ N) = 1
        rw [QuotientGroup.eq_one_iff]
        show (w : CentralizerBar z) ∈ centralizer (L₁ : Set (CentralizerBar z))
        exact hL₂C _ w.2.2
      · intro u v huv
        exact Subtype.ext (congrArg (fun x : ↥π.ker => ((x : ↥L₁) : CentralizerBar z)) huv)
    omega
  have hcardQ : Nat.card (↥(L₁ ⊔ SBar (S1 S z) z) ⧸ N) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F, hFq']
  have hrange : Nat.card ↥π.range = q * (q ^ 2 - 1) := by
    rw [MonoidHom.range_eq_top.mpr hπ, ← hcardQ]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hmul := Subgroup.card_ker_mul_card_range π
  rw [hrange, card_eq_of_hasSL2Model hp.pair.sl₁] at hmul
  have hpos : 0 < q * (q ^ 2 - 1) := by
    rw [← card_eq_of_hasSL2Model hp.pair.sl₁]
    exact Nat.card_pos
  nlinarith

theorem four_le_relIndex_RC {ε : Bool} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : Stage1L4 G z S ε q L₁ L₂) : 4 ≤ (RC S z).relIndex S := by
  have hRS1 : RC S z ≤ S1 S z := RC_le_S1 hp.pair
  have hS1S : S1 S z ≤ S := inf_le_left
  have h1 : 2 ≤ (RC S z).relIndex (S1 S z) := two_le_relIndex_of_le_of_ne hRS1 (RC_ne_S1 hp)
  have h2 : 2 ≤ (S1 S z).relIndex S := two_le_relIndex_of_le_of_ne hS1S (S1_ne_S hp.pair)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hRS1 hS1S]
  nlinarith

end L4

section Main

theorem card_S_eq_relIndex_mul {G : Type} [Group G] (z : G) (S : Subgroup G) :
    Nat.card ↥S = (RC S z).relIndex S * Nat.card ↥(RC S z) := by
  have hle : RC S z ≤ S := inf_le_left
  have h := Subgroup.relIndex_mul_card (RC S z) S
  rw [inf_eq_left.mpr hle] at h
  exact h.symm

theorem card_S_psp4 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hctx : Stage2Ctx G z Kind.psp4 S)
    (hp : Stage1PSp4 G z S q L₁ L₂) : Nat.card ↥S = 2 ^ nuQ q * 2 := by
  rw [card_S_eq_relIndex_mul z S, hp.index, card_RC_pair hctx.sylow hp.pair, mul_comm]

theorem card_S_l4 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hctx : Stage2Ctx G z (Kind.l4 ε) S)
    (hp : Stage1L4 G z S ε q L₁ L₂) : Nat.card ↥S = 2 ^ nuQ q * 4 := by
  have hidx : (RC S z).relIndex S = 4 := le_antisymm hp.index_le (four_le_relIndex_RC hp)
  rw [card_S_eq_relIndex_mul z S, hidx, card_RC_pair hctx.sylow hp.pair, mul_comm]

end Main

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
