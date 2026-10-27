module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H J : Subgroup G}

omit [Finite G] in
private theorem exists_subgroup_comm_mem (U T : Subgroup G)
    (hUT : U ≤ Subgroup.normalizer (T : Set G)) (S : Set G) :
    ∃ W : Subgroup G, ∀ g, g ∈ W ↔ g ∈ U ∧ ∀ s ∈ S, ⁅g, s⁆ ∈ T :=
  ⟨{ carrier := {g | g ∈ U ∧ ∀ s ∈ S, ⁅g, s⁆ ∈ T}
     mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, fun s hs => by
       rw [show ⁅a * b, s⁆ = a * ⁅b, s⁆ * a⁻¹ * ⁅a, s⁆ by
         simp only [commutatorElement_def]; group]
       exact T.mul_mem (Subgroup.le_normalizer_iff.mp hUT a ha.1 _ (hb.2 s hs)) (ha.2 s hs)⟩
     one_mem' := ⟨U.one_mem, fun s _ => by
       rw [commutatorElement_one_left]
       exact T.one_mem⟩
     inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, fun s hs => by
       rw [show ⁅a⁻¹, s⁆ = a⁻¹ * ⁅a, s⁆⁻¹ * a⁻¹⁻¹ by
         simp only [commutatorElement_def]; group]
       exact Subgroup.le_normalizer_iff.mp hUT a⁻¹ (U.inv_mem ha.1) _ (T.inv_mem (ha.2 s hs))⟩ },
   fun _ => Iff.rfl⟩

omit [Finite G] in
private theorem isPGroup_quotient_of_forall_mul {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    {P : Subgroup X} (hP : IsPGroup 2 P) (h : ∀ g : X, ∃ n ∈ N, n⁻¹ * g ∈ P) :
    IsPGroup 2 (X ⧸ N) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨n, hn, hp⟩ := h g
  obtain ⟨k, hk⟩ := hP ⟨n⁻¹ * g, hp⟩
  refine ⟨k, ?_⟩
  have hk' : (n⁻¹ * g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have e : (QuotientGroup.mk g : X ⧸ N) = QuotientGroup.mk (n⁻¹ * g) := by
    rw [QuotientGroup.eq]
    have := Subgroup.Normal.conj_mem ‹N.Normal› n⁻¹ (N.inv_mem hn) g⁻¹
    simpa [mul_assoc] using this
  rw [e, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]

private theorem exists_commutator_mem_of_isPGroup' {P U Z : Subgroup G} (hP : IsPGroup 2 P)
    (hUP : U ≤ P) (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) (hUZ : ¬ U ≤ Z) :
    ∃ u ∈ U, u ∉ Z ∧ ∀ p ∈ P, ⁅u, p⁆ ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZn : (Z.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPZ
  have hnil : Group.IsNilpotent (P ⧸ Z.subgroupOf P) := (hP.to_quotient _).isNilpotent
  have hUn : (U.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mpr hPU
  have hUbar : ((U.subgroupOf P).map (QuotientGroup.mk' (Z.subgroupOf P))).Normal :=
    hUn.map _ (QuotientGroup.mk'_surjective _)
  have hne : (U.subgroupOf P).map (QuotientGroup.mk' (Z.subgroupOf P)) ≠ ⊥ := by
    intro hbot
    apply hUZ
    intro u hu
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Z.subgroupOf P))
      (Subgroup.mem_subgroupOf.mpr hu : (⟨u, hUP hu⟩ : P) ∈ U.subgroupOf P)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨u, hUP hu⟩ : P)).mp h1)
  obtain ⟨⟨c, hcU, hcZ⟩, hc1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hcU
  refine ⟨u, Subgroup.mem_subgroupOf.mp hu, fun huZ => hc1 (Subtype.ext ?_), fun p hp => ?_⟩
  · exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr huZ)
  · have h := Subgroup.mem_center_iff.mp hcZ (QuotientGroup.mk' (Z.subgroupOf P) ⟨p, hp⟩)
    have h2 : QuotientGroup.mk' (Z.subgroupOf P) ⁅u, ⟨p, hp⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h.symm
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⁅u, (⟨p, hp⟩ : P)⁆).mp h2)

private theorem blockU_le_blockQ_aux (J : Subgroup G) : blockU J ≤ blockQ J :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (C1.le_normalizer_blockQ J)

omit [Finite G] in
private theorem le_normalizer_blockZ_aux (J : Subgroup G) :
    J ≤ Subgroup.normalizer (blockZ J : Set G) := fun _ hg =>
  C1.mem_normalizer_blockZ (Subgroup.le_normalizer hg)

omit [Finite G] in
private theorem blockZ_le_centralizer_aux (J : Subgroup G) :
    blockZ J ≤ Subgroup.centralizer (J : Set G) := inf_le_right

omit [Finite G] in
private theorem conj_eq_of_mem_blockZ {J : Subgroup G} {z : G} (hz : z ∈ blockZ J) {g : G}
    (hg : g ∈ J) : g * z * g⁻¹ = z := by
  rw [Subgroup.mem_centralizer_iff.mp (blockZ_le_centralizer_aux J hz) g hg, mul_inv_cancel_right]

omit [Finite G] in
private theorem mul_sq_eq (a b : G) : (a * b) ^ 2 = ⁅a, b⁆ * (b * a ^ 2 * b⁻¹) * b ^ 2 := by
  simp only [commutatorElement_def, pow_two]
  group

theorem IsFooteBlock.self (hJ : IsFooteBlock H J) : IsFooteBlock J J where
  le := le_rfl
  subnormal := IsSubnormal.refl J
  residual := hJ.residual
  quasisimple := hJ.quasisimple
  chief := hJ.chief

theorem IsFooteBlock.commutator_eq (hJ : IsFooteBlock H J) : ⁅J, J⁆ = J := by
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_right.1
    (Subgroup.le_normalizer (H := J))) ?_
  have hcomm : commutator ↥J = ⊤ := by
    refine hJ.residual _ (isPGroup_quotient_of_forall_mul _
      (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) fun g => ?_)
    have hmem : (QuotientGroup.mk g : ↥J ⧸ CFSG.pCore 2 ↥J) ∈
        Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) (commutator ↥J) := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def,
        hJ.quasisimple.1]
      trivial
    obtain ⟨c, hc, hcg⟩ := hmem
    exact ⟨c, hc, QuotientGroup.eq.1 hcg⟩
  have hmap : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap, hcomm, Subgroup.map_top, Subgroup.range_subtype]

theorem IsFooteBlock.commutator_blockU (hJ : IsFooteBlock H J) : ⁅blockU J, J⁆ = blockU J :=
  CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual hJ.residual
    (C1.blockQ_isPGroup J) (C1.le_normalizer_blockQ J)

theorem IsFooteBlock.commutator_blockU_blockQ_le (hJ : IsFooteBlock H J) :
    ⁅blockU J, blockQ J⁆ ≤ blockZ J := by
  have hQp : IsPGroup 2 (blockQ J) := C1.blockQ_isPGroup J
  have hJQ : J ≤ Subgroup.normalizer (blockQ J : Set G) := C1.le_normalizer_blockQ J
  have hQJ : blockQ J ≤ J := C1.blockQ_le J
  have hUQ : blockU J ≤ blockQ J := blockU_le_blockQ_aux J
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) := C1.le_normalizer_blockU J
  have hUJ : blockU J ≤ J := blockU_le_self J
  have hZU : blockZ J ≤ blockU J := blockZ_le_blockU J
  have hZJ : blockZ J ≤ Subgroup.centralizer (J : Set G) := blockZ_le_centralizer_aux J
  have hJZ : J ≤ Subgroup.normalizer (blockZ J : Set G) := le_normalizer_blockZ_aux J
  have hQc : ∀ g ∈ J, ∀ q ∈ blockQ J, g⁻¹ * q * g ∈ blockQ J := fun g hg q hq => by
    simpa using Subgroup.le_normalizer_iff.mp hJQ g⁻¹ (J.inv_mem hg) q hq
  obtain ⟨W, hW⟩ := exists_subgroup_comm_mem (blockU J) (blockZ J) (hUJ.trans hJZ)
    (blockQ J : Set G)
  have hZW : blockZ J ≤ W := fun z hz => (hW z).mpr ⟨hZU hz, fun q hq => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (hZJ hz) q (hQJ hq)).symm]
    exact (blockZ J).one_mem⟩
  have hWU : W ≤ blockU J := fun w hw => ((hW w).mp hw).1
  have hJW : J ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg w hw
    obtain ⟨hwU, hwQ⟩ := (hW w).mp hw
    refine (hW _).mpr ⟨Subgroup.le_normalizer_iff.mp hJU g hg w hwU, fun q hq => ?_⟩
    rw [show ⁅g * w * g⁻¹, q⁆ = g * ⁅w, g⁻¹ * q * g⁆ * g⁻¹ by
      simp only [commutatorElement_def]; group,
      conj_eq_of_mem_blockZ (hwQ _ (hQc g hg q hq)) hg]
    exact hwQ _ (hQc g hg q hq)
  have hne : ∃ u ∈ blockU J, u ∉ blockZ J ∧ ∀ q ∈ blockQ J, ⁅u, q⁆ ∈ blockZ J :=
    exists_commutator_mem_of_isPGroup' hQp hUQ (hQJ.trans hJU) (hQJ.trans hJZ)
      hJ.chief.1.not_ge
  refine Subgroup.commutator_le.mpr ?_
  rcases hJ.chief.2 W hZW hWU hJW with hWZ | hWU'
  · exfalso
    obtain ⟨u, hu, huZ, huQ⟩ := hne
    apply huZ
    rw [← hWZ]
    exact (hW u).mpr ⟨hu, huQ⟩
  · intro u hu
    exact ((hW u).mp (by rw [hWU']; exact hu)).2

theorem IsFooteBlock.commutator_mem_blockZ (hJ : IsFooteBlock H J) {u v : G}
    (hu : u ∈ blockU J) (hv : v ∈ blockU J) : ⁅u, v⁆ ∈ blockZ J :=
  IsFooteBlock.commutator_blockU_blockQ_le hJ
    (Subgroup.commutator_mem_commutator hu (blockU_le_blockQ_aux J hv))

theorem IsFooteBlock.sq_mem_blockZ (hJ : IsFooteBlock H J) {u : G} (hu : u ∈ blockU J) :
    u ^ 2 ∈ blockZ J := by
  have hUJ : blockU J ≤ J := blockU_le_self J
  have hZU : blockZ J ≤ blockU J := blockZ_le_blockU J
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) := C1.le_normalizer_blockU J
  have hUp : IsPGroup 2 (blockU J) :=
    (C1.blockQ_isPGroup J).to_le (blockU_le_blockQ_aux J)
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, ∀ g, g ∈ W ↔ g ∈ blockU J ∧ g ^ 2 ∈ blockZ J :=
    ⟨{ carrier := {g | g ∈ blockU J ∧ g ^ 2 ∈ blockZ J}
       mul_mem' := fun {a b} ha hb => ⟨(blockU J).mul_mem ha.1 hb.1, by
         rw [mul_sq_eq, conj_eq_of_mem_blockZ ha.2 (hUJ hb.1)]
         exact (blockZ J).mul_mem ((blockZ J).mul_mem
           (IsFooteBlock.commutator_mem_blockZ hJ ha.1 hb.1) ha.2) hb.2⟩
       one_mem' := ⟨(blockU J).one_mem, by
         rw [one_pow]
         exact (blockZ J).one_mem⟩
       inv_mem' := fun {a} ha => ⟨(blockU J).inv_mem ha.1, by
         rw [inv_pow]
         exact (blockZ J).inv_mem ha.2⟩ },
     fun _ => Iff.rfl⟩
  have hZW : blockZ J ≤ W := fun z hz => (hW z).mpr ⟨hZU hz, Subgroup.pow_mem _ hz 2⟩
  have hWU : W ≤ blockU J := fun w hw => ((hW w).mp hw).1
  have hJW : J ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg w hw
    obtain ⟨hwU, hwZ⟩ := (hW w).mp hw
    refine (hW _).mpr ⟨Subgroup.le_normalizer_iff.mp hJU g hg w hwU, ?_⟩
    rw [conj_pow, conj_eq_of_mem_blockZ hwZ hg]
    exact hwZ
  rcases hJ.chief.2 W hZW hWU hJW with hWZ | hWU'
  ·
    exfalso
    have hsq : ∀ u ∈ blockU J, u ^ 2 ∈ blockZ J → u ∈ blockZ J := fun u hu hu2 => by
      rw [← hWZ]
      exact (hW u).mpr ⟨hu, hu2⟩
    have hpow : ∀ k : ℕ, ∀ u ∈ blockU J, u ^ 2 ^ k ∈ blockZ J → u ∈ blockZ J := by
      intro k
      induction k with
      | zero =>
        intro u _ h
        simpa using h
      | succ k ih =>
        intro u hu h
        refine hsq u hu (ih (u ^ 2) (Subgroup.pow_mem _ hu 2) ?_)
        rwa [← pow_mul, ← pow_succ']
    have hUZ : blockU J ≤ blockZ J := by
      intro u hu
      obtain ⟨k, hk⟩ := hUp ⟨u, hu⟩
      have hk' : u ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      exact hpow k u hu (by rw [hk']; exact Subgroup.one_mem _)
    exact absurd (hJ.chief.1.trans_le hUZ) (lt_irrefl _)
  ·
    exact ((hW u).mp (by rw [hWU']; exact hu)).2

theorem IsFooteBlock.commutator_le_blockU (hJ : IsFooteBlock H J) {R : Subgroup G}
    (hRJ : R ≤ Subgroup.normalizer (J : Set G)) (hc : ⁅R, J⁆ ≤ blockQ J) :
    ⁅J, R⁆ ≤ blockU J := by
  have hQJ : blockQ J ≤ J := C1.blockQ_le J
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) := C1.le_normalizer_blockU J
  have key : ∀ r ∈ R, ∀ l ∈ J, r * l * r⁻¹ * l⁻¹ ∈ blockU J := fun r hr =>
    C1.commutator_mem_of_noTwoQuotient (L := J) (M := blockQ J) (N := blockU J) hJ.residual
      (C1.blockQ_isPGroup J)
      (fun m hm n hn => Subgroup.le_normalizer_iff.mp hJU m (hQJ hm) n hn)
      (fun l hl w hw => by
        rw [← commutatorElement_def, ← commutatorElement_inv]
        exact (blockU J).inv_mem (Subgroup.commutator_mem_commutator hw hl))
      (fun l hl => hc (Subgroup.commutator_mem_commutator hr hl))
  rw [Subgroup.commutator_le]
  intro j hj r hr
  rw [← commutatorElement_inv]
  exact (blockU J).inv_mem (key r hr j hj)

theorem IsFooteBlock.commutator_blockU_le_blockZ (hJ : IsFooteBlock H J) {R : Subgroup G}
    (hR : IsPGroup 2 R) (hRJ : R ≤ Subgroup.normalizer (J : Set G)) (hc : ⁅R, J⁆ ≤ blockQ J) :
    ⁅blockU J, R⁆ ≤ blockZ J := by
  have hUJ : blockU J ≤ J := blockU_le_self J
  have hZU : blockZ J ≤ blockU J := blockZ_le_blockU J
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) := C1.le_normalizer_blockU J
  have hJZ : J ≤ Subgroup.normalizer (blockZ J : Set G) := le_normalizer_blockZ_aux J
  have hUp : IsPGroup 2 (blockU J) :=
    (C1.blockQ_isPGroup J).to_le (blockU_le_blockQ_aux J)
  have hRU : R ≤ Subgroup.normalizer (blockU J : Set G) := fun r hr =>
    C1.mem_normalizer_blockU (hRJ hr)
  have hRZ : R ≤ Subgroup.normalizer (blockZ J : Set G) := fun r hr =>
    C1.mem_normalizer_blockZ (hRJ hr)
  obtain ⟨W, hW⟩ := exists_subgroup_comm_mem (blockU J) (blockZ J) (hUJ.trans hJZ) (R : Set G)
  have hZW : blockZ J ≤ W := fun z hz => (hW z).mpr ⟨hZU hz, fun r hr => by
    have h1 : r * z⁻¹ * r⁻¹ ∈ blockZ J :=
      Subgroup.le_normalizer_iff.mp hRZ r hr _ ((blockZ J).inv_mem hz)
    have e : ⁅z, r⁆ = z * (r * z⁻¹ * r⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (blockZ J).mul_mem hz h1⟩
  have hWU : W ≤ blockU J := fun w hw => ((hW w).mp hw).1
  have hJW : J ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg w hw
    obtain ⟨hwU, hwR⟩ := (hW w).mp hw
    refine (hW _).mpr ⟨Subgroup.le_normalizer_iff.mp hJU g hg w hwU, fun r hr => ?_⟩
    have hq : r⁻¹ * g⁻¹ * r * g ∈ blockQ J := by
      have := hc (Subgroup.commutator_mem_commutator (R.inv_mem hr) (J.inv_mem hg))
      simpa [commutatorElement_def] using this
    have hwq : ⁅w, r⁻¹ * g⁻¹ * r * g⁆ ∈ blockZ J :=
      IsFooteBlock.commutator_blockU_blockQ_le hJ (Subgroup.commutator_mem_commutator hwU hq)
    have e : ⁅g * w * g⁻¹, r⁆ = g * (⁅w, r⁆ * (r * ⁅w, r⁻¹ * g⁻¹ * r * g⁆ * r⁻¹)) * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, conj_eq_of_mem_blockZ ((blockZ J).mul_mem (hwR r hr)
      (Subgroup.le_normalizer_iff.mp hRZ r hr _ hwq)) hg]
    exact (blockZ J).mul_mem (hwR r hr) (Subgroup.le_normalizer_iff.mp hRZ r hr _ hwq)
  have hne : ∃ u ∈ blockU J, u ∉ blockZ J ∧ ∀ p ∈ R ⊔ blockU J, ⁅u, p⁆ ∈ blockZ J :=
    exists_commutator_mem_of_isPGroup' (hR.to_sup_of_normal_right' hUp hRU) le_sup_right
      (sup_le hRU Subgroup.le_normalizer) (sup_le hRZ (hUJ.trans hJZ)) hJ.chief.1.not_ge
  refine Subgroup.commutator_le.mpr ?_
  rcases hJ.chief.2 W hZW hWU hJW with hWZ | hWU'
  · exfalso
    obtain ⟨u, hu, huZ, huR⟩ := hne
    apply huZ
    rw [← hWZ]
    exact (hW u).mpr ⟨hu, fun r hr => huR r (Subgroup.mem_sup_left hr)⟩
  · intro u hu r hr
    exact ((hW u).mp (by rw [hWU']; exact hu)).2 r hr

theorem IsFooteBlock.le_centralizer_or_blockU_le (hJ : IsFooteBlock H J) {A : Subgroup G}
    (hAJ : A ≤ J) (hJA : J ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.centralizer (J : Set G) ∨ blockU J ≤ A := by
  have hUJ : blockU J ≤ J := blockU_le_self J
  have hZU : blockZ J ≤ blockU J := blockZ_le_blockU J
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) := C1.le_normalizer_blockU J
  have hZJ : blockZ J ≤ Subgroup.centralizer (J : Set G) := blockZ_le_centralizer_aux J
  have hAn : (A.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAJ).mpr hJA
  have hAbn : ((A.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).Normal :=
    hAn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hJ.quasisimple
    ((A.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) with hcen | htop
  ·
    have hAJQ : ⁅A, J⁆ ≤ blockQ J := by
      rw [Subgroup.commutator_le]
      intro a ha j hj
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥J) (⟨a, hAJ ha⟩ : ↥J) ∈
          (A.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
      have hc := Subgroup.mem_center_iff.mp (hcen hmem)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥J) (⟨j, hj⟩ : ↥J))
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥J) ⁅(⟨a, hAJ ha⟩ : ↥J), (⟨j, hj⟩ : ↥J)⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hc.symm
      exact Subgroup.mem_map.mpr
        ⟨⁅(⟨a, hAJ ha⟩ : ↥J), (⟨j, hj⟩ : ↥J)⁆, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    obtain ⟨W, hW⟩ := exists_subgroup_comm_mem (blockU J) A (hUJ.trans hJA) (J : Set G)
    have hZW : blockZ J ≤ W := fun z hz => (hW z).mpr ⟨hZU hz, fun j hj => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (hZJ hz) j hj).symm]
      exact A.one_mem⟩
    have hWU : W ≤ blockU J := fun w hw => ((hW w).mp hw).1
    have hJW : J ≤ Subgroup.normalizer (W : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro g hg w hw
      obtain ⟨hwU, hwA⟩ := (hW w).mp hw
      refine (hW _).mpr ⟨Subgroup.le_normalizer_iff.mp hJU g hg w hwU, fun j hj => ?_⟩
      have hj' : g⁻¹ * j * g ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hg) hj) hg
      rw [show ⁅g * w * g⁻¹, j⁆ = g * ⁅w, g⁻¹ * j * g⁆ * g⁻¹ by
        simp only [commutatorElement_def]; group]
      exact Subgroup.le_normalizer_iff.mp hJA g hg _ (hwA _ hj')
    have hAJA : ⁅A, J⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hJA
    rcases hJ.chief.2 W hZW hWU hJW with hWZ | hWU'
    ·
      left
      have hAU : A ⊓ blockU J ≤ blockZ J := fun x hx => by
        rw [← hWZ]
        exact (hW x).mpr ⟨hx.2, fun j hj => hAJA (Subgroup.commutator_mem_commutator hx.1 hj)⟩
      have hB1 : ⁅⁅A, J⁆, J⁆ ≤ blockZ J :=
        le_trans (le_inf ((Subgroup.commutator_mono hAJA le_rfl).trans hAJA)
          (Subgroup.commutator_mono hAJQ le_rfl)) hAU
      have hB2 : ⁅⁅⁅A, J⁆, J⁆, J⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hB1.trans hZJ)
      have hB3 : ⁅⁅A, J⁆, J⁆ = ⊥ :=
        CFSG.ComponentClassification.Asc76.Sec5.commutator_eq_bot_of_commutator_commutator_eq_bot
          (IsFooteBlock.commutator_eq hJ) hB2
      have hB4 : ⁅A, J⁆ = ⊥ :=
        CFSG.ComponentClassification.Asc76.Sec5.commutator_eq_bot_of_commutator_commutator_eq_bot
          (IsFooteBlock.commutator_eq hJ) hB3
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hB4
    ·
      right
      calc blockU J = ⁅blockU J, J⁆ := (IsFooteBlock.commutator_blockU hJ).symm
        _ ≤ A := Subgroup.commutator_le.mpr fun u hu j hj =>
          ((hW u).mp (by rw [hWU']; exact hu)).2 j hj
  ·
    right
    have hAJ' : A.subgroupOf J = ⊤ := by
      refine hJ.residual _ (isPGroup_quotient_of_forall_mul _
        (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) fun g => ?_)
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥J) g ∈
          (A.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) := by
        rw [htop]
        trivial
      obtain ⟨a, ha, hag⟩ := hmem
      exact ⟨a, ha, QuotientGroup.eq.1 hag⟩
    refine hUJ.trans fun x hx => ?_
    have : (⟨x, hx⟩ : ↥J) ∈ A.subgroupOf J := by
      rw [hAJ']
      trivial
    exact this

theorem IsFooteBlock.inf_centralizer_blockU_le (hJ : IsFooteBlock H J)
    (hU : ¬ ∀ u ∈ blockU J, ∀ v ∈ blockU J, u * v = v * u) :
    J ⊓ Subgroup.centralizer (blockU J : Set G) ≤ Subgroup.centralizer (J : Set G) := by
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) := C1.le_normalizer_blockU J
  have hJA : J ≤ Subgroup.normalizer ((J ⊓ Subgroup.centralizer (blockU J : Set G) :
      Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg a ha
    refine ⟨J.mul_mem (J.mul_mem hg ha.1) (J.inv_mem hg),
      Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ blockU J := by
      simpa using Subgroup.le_normalizer_iff.mp hJU g⁻¹ (J.inv_mem hg) u hu
    have h := Subgroup.mem_centralizer_iff.mp ha.2 _ hu'
    calc u * (g * a * g⁻¹) = g * ((g⁻¹ * u * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
      _ = g * a * g⁻¹ * u := by group
  rcases IsFooteBlock.le_centralizer_or_blockU_le hJ inf_le_left hJA with h | h
  · exact h
  · exfalso
    apply hU
    intro u hu v hv
    exact Subgroup.mem_centralizer_iff.mp (h hv).2 u hu

end CFSG.CGT.Foote82
