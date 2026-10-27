module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Abstract
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {S : Type} [Group S]

theorem false_of_charTwo [Finite S] {X K : Subgroup S} (hX : CharTwo X) (hKX : K ≤ X)
    (hsub : IsSubnormal K X) (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) : False := by
  rcases hK with hq | h3
  ·
    have hQX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
    have hQN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set S) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
    have hQ2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    set K' : Subgroup ↥X := K.subgroupOf X with hK'
    set R : Subgroup ↥X := (pCoreOf 2 X).subgroupOf X with hR
    have hKq : CFSG.IsQuasisimple ↥K' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm hq
    have hKsub : K'.IsSubnormal := (isSubnormal_iff_subgroupOf hKX).1 hsub
    have hRn : R.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).2 hQN
    have hRs : Group.IsSolvable ↥R := by
      have hp : IsPGroup 2 ↥R := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
      have := hp.isNilpotent
      infer_instance
    have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).1 K'
      ⟨hKq, hKsub⟩
    have hKc : K ≤ Subgroup.centralizer (pCoreOf 2 X : Set S) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro q hq'
      have h1 : ⁅(⟨k, hKX hk⟩ : ↥X), (⟨q, hQX hq'⟩ : ↥X)⁆ = 1 := by
        have : ⁅(⟨k, hKX hk⟩ : ↥X), (⟨q, hQX hq'⟩ : ↥X)⁆ ∈ ⁅K', R⁆ :=
          Subgroup.commutator_mem_commutator hk hq'
        rw [hcomm] at this
        exact Subgroup.mem_bot.1 this
      have h2 := commutatorElement_eq_one_iff_mul_comm.1 h1
      exact (congrArg Subtype.val h2).symm
    have hKQ : K ≤ pCoreOf 2 X := fun x hx => hX ⟨hKX hx, hKc hx⟩
    have hK2 : IsPGroup 2 ↥K := hQ2.to_le hKQ
    have := hK2.isNilpotent
    have : Group.IsSolvable ↥K := inferInstance
    have hper : Group.IsPerfect ↥K := hq.1
    have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  ·
    have hg : L246C127.Good2 ↥K := Or.inl h3
    have hbot := L246C127.eq_bot_of_isSubnormal_of_charTwo hX hsub hg.noTwoNormal hg.noTwoQuot
    have hnt : Nontrivial ↥K := hg.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).1 hnt hbot

@[expose] def Overgroups (S : Type) [Group S] : Prop :=
  ∀ T Y : Subgroup S, IsSylowTwoOf T ⊤ → T ≤ Y → Y ≠ ⊤ → CharTwo Y

theorem Overgroups.of_mulEquiv {S' : Type} [Group S'] (e : S ≃* S') (h : Overgroups S) :
    Overgroups S' := by
  intro T Y hT hTY hY
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T) (Y := ⊤)).2 hT
    simpa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using this
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rw [Subgroup.map_map] at this
    have h1 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' := by ext y; simp
    rwa [h1, Subgroup.map_id, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at this
  have hc := h _ _ hT' (Subgroup.map_mono hTY) hY'
  have := Ch1.charTwo_map_mulEquiv e hc
  rwa [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' by
    ext y; simp, Subgroup.map_id] at this

theorem map_map_symm' {A B : Type} [Group A] [Group B] (e : A ≃* B) (X : Subgroup A) :
    (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by ext x; simp
  rw [h, Subgroup.map_id]

theorem Overgroups.of_sylow [Finite S] (T₀ : Subgroup S) (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ Y : Subgroup S, T₀ ≤ Y → Y ≠ ⊤ → CharTwo Y) : Overgroups S := by
  intro T Y hT hTY hY
  obtain ⟨g, hg⟩ := L246C127.exists_conj_of_isSylowTwoOf' hT₀ hT
  set e : S ≃* S := MulAut.conj g with he
  have hT₀Y : T₀ ≤ Y.map e.symm.toMonoidHom := by
    rw [← map_map_symm' e T₀, hg]
    exact Subgroup.map_mono hTY
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rw [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S by
      ext y; simp, Subgroup.map_id, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      at this
    exact this
  have hc := Ch1.charTwo_map_mulEquiv e (h _ hT₀Y hY')
  rwa [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S by
    ext y; simp, Subgroup.map_id] at hc

theorem charTwo_of_le [Finite S] {Y P : Subgroup S} (hYP : Y ≤ P) (hP : CharTwo P)
    (hR : pCoreOf 2 P ≤ Y) : CharTwo Y := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hP hYP hR

theorem Overgroups.of_cover [Finite S] (T₀ : Subgroup S) (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ Y : Subgroup S, T₀ ≤ Y → Y ≠ ⊤ → ∃ P : Subgroup S, Y ≤ P ∧ P ≠ ⊤ ∧ CharTwo P) :
    Overgroups S := by
  refine Overgroups.of_sylow T₀ hT₀ fun Y hY hne => ?_
  obtain ⟨P, hYP, -, hP⟩ := h Y hY hne
  have hodd : ¬ 2 ∣ (T₀.subgroupOf P).index := by
    have h1 := Subgroup.relIndex_mul_relIndex T₀ P ⊤ (hY.trans hYP) le_top
    intro h2
    apply hT₀.2.2
    change 2 ∣ T₀.relIndex ⊤
    rw [← h1]
    exact Dvd.dvd.mul_right h2 _
  have hT₀P : IsSylowTwoOf T₀ P := ⟨hY.trans hYP, hT₀.2.1, hodd⟩
  exact charTwo_of_le hYP hP ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT₀P).trans hY)

section Center

variable {G : Type} [Group G]

theorem comm_mul_central {x y z w : G} (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  have h2 : ⁅x, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    ((Subgroup.mem_center_iff.1 hw x))
  have h3 : ⁅z, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    ((Subgroup.mem_center_iff.1 hz y).symm)
  have h4 : ⁅z, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    ((Subgroup.mem_center_iff.1 hz w).symm)
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_mul_right_eq_mul_conj, h2, h3, h4]
  simp

theorem eq_top_of_sup_center_eq_top (hp : Group.IsPerfect G) {X : Subgroup G}
    (h : X ⊔ Subgroup.center G = ⊤) : X = ⊤ := by
  have hn : X.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h]
    exact sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
  have hcomm : commutator G ≤ X := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have h1 : g₁ ∈ X ⊔ Subgroup.center G := by rw [h]; trivial
    have h2 : g₂ ∈ X ⊔ Subgroup.center G := by rw [h]; trivial
    obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 h1
    obtain ⟨x₂, hx₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 h2
    rw [comm_mul_central hz₁ hz₂]
    exact Subgroup.commutator_le_left X X (Subgroup.commutator_mem_commutator hx₁ hx₂)
  rw [Group.isPerfect_def] at hp
  rw [eq_top_iff, ← hp]
  exact hcomm

abbrev ctr (G : Type) [Group G] : G →* G ⧸ Subgroup.center G :=
  QuotientGroup.mk' (Subgroup.center G)

theorem inf_eq_bot_of_card_three {K Z : Subgroup G} [Finite K] (h3 : Nat.card ↥K = 3)
    (hKZ : ¬ K ≤ Z) : K ⊓ Z = ⊥ := by
  have hdvd : Nat.card ↥(K ⊓ Z) ∣ 3 := by
    rw [← h3]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    apply hKZ
    have : K ⊓ Z = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, h3])
    rw [← this]
    exact inf_le_right

theorem reduce_center [Finite G] (hq : CFSG.IsQuasisimple G)
    (hodd : Odd (Nat.card (Subgroup.center G))) {T X K : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hTX : T ≤ X) (hX : X ≠ ⊤) (hKX : K ≤ X) (hsub : IsSubnormal K X)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) (hKc : ¬ K ≤ Subgroup.center G) :
    IsSylowTwoOf (T.map (ctr G)) ⊤ ∧ T.map (ctr G) ≤ X.map (ctr G) ∧ X.map (ctr G) ≠ ⊤ ∧
      K.map (ctr G) ≤ X.map (ctr G) ∧ IsSubnormal (K.map (ctr G)) (X.map (ctr G)) ∧
      (CFSG.IsQuasisimple ↥(K.map (ctr G)) ∨ Nat.card ↥(K.map (ctr G)) = 3) := by
  have hker : (ctr G).ker = Subgroup.center G := QuotientGroup.ker_mk' _
  refine ⟨?_, Subgroup.map_mono hTX, ?_, Subgroup.map_mono hKX, A3.subnormal_map _ hsub, ?_⟩
  · have h1 : Odd (Nat.card (ctr G).ker) := by rw [hker]; exact hodd
    have := Setup.X3.isSylowTwoOf_map_of_odd_ker (ctr G) h1 hT
    rwa [show (ctr G).range = ⊤ from QuotientGroup.range_mk' _] at this
  · intro htop
    apply hX
    refine eq_top_of_sup_center_eq_top hq.1 ?_
    have := Subgroup.comap_map_eq (ctr G) X
    rw [htop, Subgroup.comap_top, hker] at this
    exact this.symm
  · have hKf : ¬ K ≤ (ctr G).ker := by rwa [hker]
    rcases hK with hKq | h3
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_map hKq (ctr G) hKf)
    · right
      have hfin : Finite ↥K := Finite.of_injective _ K.subtype_injective
      have hbot : K ⊓ (ctr G).ker = ⊥ := inf_eq_bot_of_card_three h3 hKf
      have hinj : Function.Injective ((ctr G).comp K.subtype) := by
        rw [← MonoidHom.ker_eq_bot_iff]
        rw [eq_bot_iff]
        intro k hk
        rw [MonoidHom.mem_ker] at hk
        have hk1 : (k : G) ∈ K ⊓ (ctr G).ker := ⟨k.2, hk⟩
        rw [hbot] at hk1
        exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hk1))
      have hrange : K.map (ctr G) = ((ctr G).comp K.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange, ← h3]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Center

end CFSG.QuasithinUnique.Bridge.Over
