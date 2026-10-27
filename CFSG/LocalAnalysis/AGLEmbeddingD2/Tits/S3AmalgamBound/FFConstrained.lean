module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Noncyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ConstrainedQuotient

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

section Small

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_three_of_card_nine {D : Subgroup G} (hD : Nat.card D = 9)
    (hc : ¬ IsCyclic D) : IsElemAbelian 3 D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : Nat.card D = 3 ^ 2 := by rw [hD]; norm_num
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hsq, fun x hx => ?_⟩
  have hdvd : orderOf (⟨x, hx⟩ : D) ∣ 3 ^ 2 := hsq ▸ orderOf_dvd_natCard _
  obtain ⟨k, hk, hxk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk2 : k ≠ 2 := by
    rintro rfl
    exact hc (isCyclic_of_orderOf_eq_card (⟨x, hx⟩ : D) (hxk.trans hsq.symm))
  have hk1 : k ≤ 1 := by omega
  have h3 : orderOf (⟨x, hx⟩ : D) ∣ 3 := by
    rw [hxk]; exact (pow_dvd_pow 3 hk1).trans (by simp)
  have := orderOf_dvd_iff_pow_eq_one.1 h3
  exact congrArg Subtype.val this

theorem small_of_noncyclic_sylow (C : Subgroup G) (S : Sylow 3 ↥C)
    (hSc : ¬ IsCyclic ↥((S : Subgroup ↥C).map C.subtype))
    (h9 : ∀ X : Subgroup G, X ≤ C → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9) :
    ∀ E : Subgroup G, E ≤ C → IsPGroup 3 E → IsElemAbelian 3 E ∧ Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro E hEC hEp
  have hE' : IsPGroup 3 (E.subgroupOf C) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  obtain ⟨D', hED'⟩ := hE'.exists_le_sylow
  set Dm : Subgroup G := (D' : Subgroup ↥C).map C.subtype with hDm
  have hDmC : Dm ≤ C := Subgroup.map_subtype_le _
  have hDmp : IsPGroup 3 Dm := D'.isPGroup'.map _
  have hDmc : ¬ IsCyclic Dm := by
    intro hcyc
    have h1 : IsCyclic ↥(D' : Subgroup ↥C) :=
      (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).isCyclic.2 hcyc
    have h2 : IsCyclic ↥(S : Subgroup ↥C) := (Sylow.equiv S D').isCyclic.2 h1
    exact hSc ((Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).isCyclic.1 h2)
  have hcard9 : Nat.card Dm ≤ 9 := h9 Dm hDmC hDmp hDmc
  have hcard : Nat.card Dm = 9 :=
    le_antisymm hcard9 (Nat.le_of_dvd Nat.card_pos (nine_dvd_card_of_not_isCyclic hDmp hDmc))
  have hel : IsElemAbelian 3 Dm := isElemAbelian_three_of_card_nine hcard hDmc
  have hEDm : E ≤ Dm := fun x hx => ⟨⟨x, hEC hx⟩, hED' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  exact ⟨isElemAbelian_of_le hel hEDm, hcard ▸ Subgroup.card_le_of_le hEDm⟩

end Small

section Quot

theorem isPConstrained_three_of_surjective_small_ker {X Y : Type*} [Group X] [Finite X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) (hX : CFSG.ABGLocalTools.IsPConstrained 3 X)
    (hN : ∀ E : Subgroup X, E ≤ f.ker → IsPGroup 3 E →
      IsElemAbelian 3 E ∧ Nat.card E ≤ 9) :
    CFSG.ABGLocalTools.IsPConstrained 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Y := Finite.of_surjective f hf
  have h1 := isPConstrained_three_quotient_of_small_normal f.ker hX hN
  have hg : Function.Surjective (QuotientGroup.kerLift f) := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker : (QuotientGroup.kerLift f).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (QuotientGroup.kerLift_injective f)
  exact isPConstrained_of_surjective_of_coprime_ker (QuotientGroup.kerLift f) hg
    (by rw [hker, Subgroup.card_bot]; exact Nat.coprime_one_right 3) h1

variable {G : Type} [Group G] [Finite G]

noncomputable def actOnAutOn {M V : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    ↥M →* ↥(autOn M V) :=
  ((conjAct V).comp (Subgroup.inclusion hMN)).codRestrict (autOn M V) fun l =>
    Subgroup.mem_map.2 ⟨⟨l, hMN l.2⟩, by simp [Subgroup.mem_subgroupOf], rfl⟩

omit [Finite G] in
theorem actOnAutOn_surjective {M V : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (actOnAutOn hMN) := by
  rintro ⟨a, ha⟩
  obtain ⟨⟨x, hx⟩, hxM, rfl⟩ := Subgroup.mem_map.1 ha
  exact ⟨⟨x, hxM⟩, rfl⟩

omit [Finite G] in
theorem mem_ker_actOnAutOn {M V : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (l : ↥M) : l ∈ (actOnAutOn hMN).ker ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  have key : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) (v : V),
      ((conjAct V ⟨g, hg⟩ v : V) : G) = g * v * g⁻¹ := fun _ _ _ => rfl
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 : conjAct V ⟨l, hMN l.2⟩ = 1 := congrArg Subtype.val h
    have h2 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h1
    simp only [key] at h2
    change (l : G) * v * (l : G)⁻¹ = v at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  · intro h
    refine Subtype.ext (MulEquiv.ext fun v => Subtype.ext ?_)
    have := h v v.2
    change (l : G) * v * (l : G)⁻¹ = v
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm

omit [Finite G] in
theorem isElemAbelian_of_map_subtype {p : ℕ} {M : Subgroup G} {E : Subgroup ↥M}
    (h : IsElemAbelian p (E.map M.subtype)) : IsElemAbelian p E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have := h.1.is_comm.comm (⟨a.1.1, a.1, a.2, rfl⟩ : E.map M.subtype)
      (⟨b.1.1, b.1, b.2, rfl⟩ : E.map M.subtype)
    have h3 := congrArg Subtype.val this
    apply Subtype.ext
    apply Subtype.ext
    exact h3
  · exact Subtype.ext (h.2 x.1 ⟨x, hx, rfl⟩)

end Quot

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.ffQuotientConstrained3_of_small
    {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) (S : Sylow 3 ↥(ffC M T))
    (hS : ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype))
    (h9 : ∀ X : Subgroup G, X ≤ ffC M T → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9) :
    CFSG.ABGLocalTools.IsPConstrained 3
      ↥(autOn M (conjClosure (quasithinOmegaOneCenter T) M)) := by
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  have hsmall := small_of_noncyclic_sylow (ffC M T) S hS h9
  refine isPConstrained_three_of_surjective_small_ker (actOnAutOn hMN)
    (actOnAutOn_surjective hMN) hcon ?_
  intro E hE hEp
  have hEC : E.map M.subtype ≤ ffC M T := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(mem_ker_actOnAutOn hMN x).1 (hE hx), x.2⟩
  obtain ⟨hel, hcard⟩ := hsmall _ hEC (hEp.map _)
  refine ⟨isElemAbelian_of_map_subtype hel, ?_⟩
  rwa [Subgroup.card_map_of_injective M.subtype_injective] at hcard

theorem ffQuotientConstrained :
    FFQuotientConstrained := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hcon T hT hNT S hS
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  have hNZ : ¬ Subgroup.normalizer (Z : Set G) ≤ M := fun h =>
    hNT ((MsidePrelim.normalizer_le_normalizer_quasithinOmegaOneCenter T).trans h)
  have hCZ : ffC M T ≤ M ⊓ Subgroup.normalizer (Z : Set G) := by
    refine le_inf inf_le_right (inf_le_left.trans ?_)
    exact (Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z M)).trans
      (Subgroup.centralizer_le_normalizer _)
  have h9 : ∀ X : Subgroup G, X ≤ ffC M T → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9 :=
    fun X hX hXp hXc => D2L34BetaConf.card_le_nine_of_le_normalizer hc hstr hZ1 hZ2 hNZ
      (hX.trans hCZ) hXp hXc
  exact CFSG.LocalAnalysis.RankThreeTheoremC.ffQuotientConstrained3_of_small hcon S hS h9

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

