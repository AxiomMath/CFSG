module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.QuasithinUnique.I32

open CFSG.ComponentClassification CFSG.QuasithinUnique.Id2519

section Conj

variable {G : Type*} [Group G]

theorem conjugate_iSup {ι : Sort*} (H : ι → Subgroup G) (g : G) :
    CFSG.conjugate (⨆ i, H i) g = ⨆ i, CFSG.conjugate (H i) g := by
  unfold CFSG.conjugate
  exact Subgroup.map_iSup _ _

theorem map_conjugate {G' : Type*} [Group G'] (f : G →* G') (H : Subgroup G) (g : G) :
    (CFSG.conjugate H g).map f = CFSG.conjugate (H.map f) (f g) := by
  unfold CFSG.conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem conjugate_eq_map_conj {s : G} (hs : s * s = 1) (K : Subgroup G) :
    CFSG.conjugate K s = K.map (MulAut.conj s).toMonoidHom := by
  unfold CFSG.conjugate
  rw [inv_eq_of_mul_eq_one_right hs]

theorem conjugate_conjugate_self {s : G} (hs : s * s = 1) (K : Subgroup G) :
    CFSG.conjugate (CFSG.conjugate K s) s = K := by
  rw [BenderBranch.conjugate_conjugate, hs, BenderBranch.conjugate_one]

theorem conjugate_le_of_mem_normalizer {H K : Subgroup G} {g : G} (hHK : H ≤ K)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : CFSG.conjugate H g ≤ K := by
  have h := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hg
  calc CFSG.conjugate H g ≤ CFSG.conjugate K g := BenderBranch.conjugate_mono hHK g
    _ = K := h

end Conj

@[expose] noncomputable def oddLayerOf (X : Type*) [Group X] : Subgroup X :=
  (Layer.subgroup (X ⧸ CFSG.Open.componentClassificationOddCore X)).comap
    (QuotientGroup.mk' (CFSG.Open.componentClassificationOddCore X))

theorem oddLayer_eq_map {G : Type} [Group G] (H : Subgroup G) :
    oddLayer H = (oddLayerOf ↥H).map H.subtype := by
  unfold oddLayer oddLayerOf
  rw [CFSG.layer_eq_componentClassification]
  rfl

instance oddLayerOf_normal (X : Type*) [Group X] : (oddLayerOf X).Normal :=
  Subgroup.Normal.comap (Layer.normal _) _

theorem twoResidual_eq_top_of_perfect {Q : Type*} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q) :
    TwoResidual.subgroup Q = ⊤ := by
  by_contra hne
  have hchar : (TwoResidual.subgroup Q).Characteristic := TwoResidual.characteristic Q
  have hnormal : (TwoResidual.subgroup Q).Normal := inferInstance
  have hodd : Odd (Nat.card (Q ⧸ TwoResidual.subgroup Q)) := TwoResidual.odd_index Q
  have hsolv : Group.IsSolvable (Q ⧸ TwoResidual.subgroup Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hperf : Group.IsPerfect (Q ⧸ TwoResidual.subgroup Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (TwoResidual.subgroup Q))
      (QuotientGroup.mk'_surjective _)
  have hnt : Nontrivial (Q ⧸ TwoResidual.subgroup Q) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isSolvable _ hsolv

section TwoComp

variable {G : Type} [Group G] [Finite G]

theorem isTwoComponentIn_iff {L C : Subgroup G} (hLC : L ≤ C) :
    IsTwoComponentIn L C ↔ TwoComponents.IsTwoComponent (L.subgroupOf C) := by
  constructor
  · rintro ⟨hL, hq⟩
    refine (TwoComponentTransport.subgroupOf_iff L C hLC).mpr ⟨?_, ?_, ?_⟩
    · exact subgroupOf_isSubnormal_of_open (CFSG.Quasithin.subnormal_of_mem_cComp hL)
    · exact twoResidual_eq_top_of_perfect
        (Subgroup.isPerfect_iff.mpr (CFSG.Quasithin.perfect_of_mem_cComp hL))
    · exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq
  · intro h
    obtain ⟨hsub, -, hq⟩ := (TwoComponentTransport.subgroupOf_iff L C hLC).mp h
    have hperfC : Group.IsPerfect ↥(L.subgroupOf C) := ⟨TwoComponents.perfect h⟩
    have hperfL : Group.IsPerfect ↥L :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLC).surjective
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfL
    refine ⟨⟨?_, hperf, open_isSubnormal_of_subgroupOf hLC hsub, ?_⟩,
      CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq⟩
    · intro hbot
      have := Quasisimple.nontrivial hq
      have : Nontrivial ↥L :=
        (QuotientGroup.mk'_surjective (CFSG.Open.componentClassificationOddCore ↥L)).nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot L).mp this hbot
    · intro K hKL hKne hKperf hKsub
      have hKC : K ≤ C := hKL.le.trans hLC
      have hK' : CFSG.Open.IsSubnormal (K.subgroupOf C) ⊤ :=
        Components.chain_of_mathlib_subnormal (subgroupOf_isSubnormal_of_open hKsub)
      rcases TwoComponentSubnormal.contains_or_normalizes_core (L.subgroupOf C) (K.subgroupOf C)
        h hK' with hle | ⟨-, hcomm⟩
      · refine hKL.not_ge (fun x hx => ?_)
        have : (⟨x, hLC hx⟩ : C) ∈ K.subgroupOf C := hle hx
        exact this
      ·
        have hKK : K.subgroupOf C ≤ L.subgroupOf C := fun x hx => hKL.le hx
        have hmapK : (K.subgroupOf C).map C.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKC
        have hKperf' : ⁅K.subgroupOf C, K.subgroupOf C⁆ = K.subgroupOf C := by
          apply Subgroup.map_injective C.subtype_injective
          rw [Subgroup.map_commutator, hmapK, hKperf]
        have hle2 : K.subgroupOf C ≤
            (CFSG.Open.componentClassificationOddCore ↥(L.subgroupOf C)).map (L.subgroupOf C).subtype := by
          calc K.subgroupOf C = ⁅K.subgroupOf C, K.subgroupOf C⁆ := hKperf'.symm
            _ ≤ ⁅L.subgroupOf C, K.subgroupOf C⁆ := Subgroup.commutator_mono hKK le_rfl
            _ ≤ _ := hcomm
        have hoddP : Odd (Nat.card ↥((CFSG.Open.componentClassificationOddCore ↥(L.subgroupOf C)).map
            (L.subgroupOf C).subtype)) := by
          rw [Subgroup.card_map_of_injective (L.subgroupOf C).subtype_injective]
          exact OddCore.odd_card _
        have : Group.IsSolvable ↥((CFSG.Open.componentClassificationOddCore ↥(L.subgroupOf C)).map
            (L.subgroupOf C).subtype) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddP
        have : Group.IsSolvable ↥(K.subgroupOf C) :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle2)
        have : Group.IsPerfect ↥(K.subgroupOf C) := Subgroup.isPerfect_iff.mpr hKperf'
        have hbot : K.subgroupOf C = ⊥ := by
          by_contra hne
          have : Nontrivial ↥(K.subgroupOf C) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
          exact Group.IsPerfect.not_isSolvable ↥(K.subgroupOf C) inferInstance
        apply hKne
        rw [← hmapK, hbot, Subgroup.map_bot]

end TwoComp

section OddTwo

theorem map_comap_quotient_congr {A A' : Type*} [Group A] [Group A'] (N : Subgroup A)
    (N' : Subgroup A') [N.Normal] [N'.Normal] (e : A ≃* A') (hN : N.map e.toMonoidHom = N')
    (P : Subgroup (A ⧸ N)) (P' : Subgroup (A' ⧸ N'))
    (hP : P.map (QuotientGroup.congr N N' e hN).toMonoidHom = P') :
    (P.comap (QuotientGroup.mk' N)).map e.toMonoidHom = P'.comap (QuotientGroup.mk' N') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap, ← hP, Subgroup.mem_map_equiv]
  have h : (QuotientGroup.congr N N' e hN).symm (QuotientGroup.mk' N' y) =
      QuotientGroup.mk' N (e.symm y) := by
    rw [MulEquiv.symm_apply_eq]
    exact (QuotientGroup.congr_mk N N' e hN (e.symm y)).symm ▸ by simp
  rw [h]

theorem map_oddTwoCore_equiv {G G' : Type} [Group G] [Group G'] {A : Subgroup G} {A' : Subgroup G'}
    (e : ↥A ≃* ↥A') : (oddTwoCore A).map e.toMonoidHom = oddTwoCore A' := by
  have hO : (CFSG.oddCore ↥A).map e.toMonoidHom = CFSG.oddCore ↥A' := OddCore.equiv_invariant e
  exact map_comap_quotient_congr _ _ e hO _ _ (CFSG.pCore_map_iso 2 _)

theorem oddTwoIso_of_mulEquiv {G G' : Type} [Group G] [Group G'] {A B : Subgroup G}
    {A' B' : Subgroup G'} (eA : ↥A ≃* ↥A') (eB : ↥B ≃* ↥B') (h : OddTwoIso A B) :
    OddTwoIso A' B' := by
  obtain ⟨φ⟩ := h
  exact ⟨((QuotientGroup.congr (oddTwoCore A) (oddTwoCore A') eA
      (map_oddTwoCore_equiv eA)).symm.trans φ).trans
    (QuotientGroup.congr (oddTwoCore B) (oddTwoCore B') eB (map_oddTwoCore_equiv eB))⟩

variable {G : Type} [Group G] [Finite G]

theorem oddTwoCore_eq_comap_center {M : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥M ⧸ CFSG.oddCore ↥M)) :
    oddTwoCore M =
      (Subgroup.center (↥M ⧸ CFSG.oddCore ↥M)).comap (QuotientGroup.mk' (CFSG.oddCore ↥M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : CFSG.oddCore (↥M ⧸ CFSG.oddCore ↥M) = ⊥ := by
    have h1 : CFSG.oddCore ↥M = CFSG.pPrimeCore 2 ↥M :=
      (CFSG.oddCore_eq_piCore ↥M).trans (CFSG.pPrimeCore_eq_piCore ↥M 2).symm
    have h2 : CFSG.oddCore (↥M ⧸ CFSG.oddCore ↥M) = CFSG.pPrimeCore 2 (↥M ⧸ CFSG.oddCore ↥M) :=
      (CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm
    rw [h2]
    exact pPrimeCore_quotient_eq_bot_of_eq (CFSG.oddCore ↥M) h1
  have hp : CFSG.pCore 2 (↥M ⧸ CFSG.oddCore ↥M) = Subgroup.center (↥M ⧸ CFSG.oddCore ↥M) :=
    le_antisymm (pCore_le_center_of_isQuasisimple hq) (center_le_pCore_of_oddCore_eq_bot hbot)
  unfold oddTwoCore
  rw [hp]

theorem ker_eq_oddTwoCore {M : Subgroup G} (hq : CFSG.IsQuasisimple (↥M ⧸ CFSG.oddCore ↥M))
    {T : Type*} [Group T] [IsSimpleGroup T] (hT : ∃ a b : T, a * b ≠ b * a) (f : ↥M →* T)
    (hf : Function.Surjective f) : f.ker = oddTwoCore M := by
  have : Finite T := Finite.of_surjective f hf
  have hperfT : Group.IsPerfect T := ⟨ComponentClassification.Helpers.commutator_eq_top T hT⟩
  have hnt : Nontrivial T := by
    obtain ⟨a, b, hab⟩ := hT
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hO : CFSG.oddCore ↥M ≤ f.ker := by
    have hNn : ((CFSG.oddCore ↥M).map f).Normal := Subgroup.Normal.map inferInstance f hf
    rcases CFSG.eq_bot_or_eq_top_of_normal _ hNn with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).mp hbot
    · exfalso
      have hdvd : Nat.card ↥((CFSG.oddCore ↥M).map f) ∣ Nat.card (CFSG.oddCore ↥M) :=
        (CFSG.oddCore ↥M).card_map_dvd f
      have hoddT : Odd (Nat.card T) := by
        rw [htop, Subgroup.card_top] at hdvd
        exact (EscapingLocal.odd_card_oddCore ↥M).of_dvd_nat hdvd
      have hsolv : Group.IsSolvable T := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddT
      exact Group.IsPerfect.not_isSolvable T hsolv
  let fb : (↥M ⧸ CFSG.oddCore ↥M) →* T := QuotientGroup.lift (CFSG.oddCore ↥M) f hO
  have hfb : Function.Surjective fb := by
    intro t
    obtain ⟨m, hm⟩ := hf t
    exact ⟨(m : ↥M ⧸ CFSG.oddCore ↥M), by simpa [fb] using hm⟩
  have hkerfb : fb.ker = Subgroup.center (↥M ⧸ CFSG.oddCore ↥M) := by
    apply le_antisymm
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (fb.normal_ker) with htop | hle
      · exfalso
        have hone : ∀ x, fb x = 1 := fun x => MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top x)
        obtain ⟨a, b, hab⟩ := hT
        obtain ⟨a', rfl⟩ := hfb a
        obtain ⟨b', rfl⟩ := hfb b
        exact hab (by rw [hone a', hone b'])
      · exact hle
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hzc : fb z ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨q, rfl⟩ := hfb t
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz q]
      rw [ComponentClassification.Helpers.center_eq_bot T hT, Subgroup.mem_bot] at hzc
      exact hzc
  rw [oddTwoCore_eq_comap_center hq, ← hkerfb]
  ext x
  simp [fb, MonoidHom.mem_ker]

theorem oddTwoIso_of_surjective {M₁ M₂ : Subgroup G}
    (h₁ : CFSG.IsQuasisimple (↥M₁ ⧸ CFSG.oddCore ↥M₁))
    (h₂ : CFSG.IsQuasisimple (↥M₂ ⧸ CFSG.oddCore ↥M₂))
    {T : Type*} [Group T] [IsSimpleGroup T] (hT : ∃ a b : T, a * b ≠ b * a)
    (f₁ : ↥M₁ →* T) (hf₁ : Function.Surjective f₁) (f₂ : ↥M₂ →* T)
    (hf₂ : Function.Surjective f₂) : OddTwoIso M₁ M₂ := by
  have e1 := ker_eq_oddTwoCore h₁ hT f₁ hf₁
  have e2 := ker_eq_oddTwoCore h₂ hT f₂ hf₂
  exact ⟨(QuotientGroup.quotientMulEquivOfEq e1.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁).trans
      ((QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂).symm.trans
        (QuotientGroup.quotientMulEquivOfEq e2)))⟩

end OddTwo

end CFSG.QuasithinUnique.I32
