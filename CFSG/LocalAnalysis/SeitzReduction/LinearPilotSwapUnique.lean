module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotMainInputs
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGen
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped commutatorElement

section Diagonal

variable {G : Type*} [Group G] {t : G} {A : Subgroup G}

theorem range_linearSwapDiag_le_centralizer (htt : t * t = 1)
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) :
    (linearSwapDiag hA).range ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨x, rfl⟩
  rw [mem_centralizer_singleton_iff, linearSwapDiag_apply]
  have hc : (x : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * x :=
    mem_centralizer_iff.1 (hA ⟨x, x.2, rfl⟩) x x.2
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [ht] at hc ⊢
  calc (x : G) * (t * x * t) * t = x * t * x * (t * t) := by group
    _ = (t * t) * x * t * x := by rw [htt, mul_one, one_mul]
    _ = t * ((t * x * t) * x) := by group
    _ = t * ((x : G) * (t * x * t)) := by rw [hc]

theorem card_quotient_center_le_card_range_linearSwapDiag [Finite G]
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) :
    Nat.card (A ⧸ center A) ≤ Nat.card (linearSwapDiag hA).range := by
  have h1 := Subgroup.card_ker_mul_card_range (linearSwapDiag hA)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center A)
  have h3 : Nat.card (linearSwapDiag hA).ker ≤ Nat.card (center A) :=
    Subgroup.card_le_of_le (ker_linearSwapDiag_le_center hA)
  have hZ : 0 < Nat.card (center A) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hZ
  calc Nat.card (center A) * Nat.card (A ⧸ center A) = Nat.card A := by rw [h2, mul_comm]
    _ = Nat.card (linearSwapDiag hA).ker * Nat.card (linearSwapDiag hA).range := h1.symm
    _ ≤ Nat.card (center A) * Nat.card (linearSwapDiag hA).range :=
        Nat.mul_le_mul_right _ h3

theorem card_quotient_center_eq_of_linearSwapDiag {S : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hrange : (linearSwapDiag hA).range = S) (hZ : center S = ⊥) :
    Nat.card (A ⧸ center A) = Nat.card S := by
  have hker : center A = (linearSwapDiag hA).ker := by
    refine le_antisymm (fun z hz => ?_) (ker_linearSwapDiag_le_center hA)
    rw [MonoidHom.mem_ker]
    have hzS : linearSwapDiag hA z ∈ S := hrange ▸ ⟨z, rfl⟩
    have hc : (⟨_, hzS⟩ : S) ∈ center S := by
      rw [mem_center_iff]
      intro w
      obtain ⟨x, hx⟩ : (w : G) ∈ (linearSwapDiag hA).range := hrange ▸ w.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hx, ← map_mul, ← map_mul, mem_center_iff.1 hz x]
    rw [hZ, mem_bot] at hc
    exact congrArg Subtype.val hc
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (linearSwapDiag hA)).toEquiv]
  exact congrArg (fun H : Subgroup G => Nat.card H) hrange

theorem conjugate_le_centralizer_of_le_centralizer {B : Subgroup G}
    (hAB : B ≤ centralizer (A : Set G)) (h : G) :
    CFSG.conjugate B h ≤ centralizer (CFSG.conjugate A h : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hc : x * y = y * x := mem_centralizer_iff.1 (hAB hy) x hx
  calc h⁻¹ * x * h⁻¹⁻¹ * (h⁻¹ * y * h⁻¹⁻¹) = h⁻¹ * (x * y) * h⁻¹⁻¹ := by group
    _ = h⁻¹ * (y * x) * h⁻¹⁻¹ := by rw [hc]
    _ = h⁻¹ * y * h⁻¹⁻¹ * (h⁻¹ * x * h⁻¹⁻¹) := by group

theorem isQuasisimple_map_conj (hq : CFSG.Open.IsQuasisimple A) (g : G) :
    CFSG.Open.IsQuasisimple (A.map (MulAut.conj g).toMonoidHom) := by
  let e : A ≃* A.map (MulAut.conj g).toMonoidHom :=
    A.equivMapOfInjective _ (MulAut.conj g).injective
  obtain ⟨hp, hs⟩ := hq
  have hc : (center A).map (e : A →* A.map (MulAut.conj g).toMonoidHom) =
      center (A.map (MulAut.conj g).toMonoidHom) :=
    map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← map_top_of_surjective (e : A →* A.map (MulAut.conj g).toMonoidHom) e.surjective,
    ← map_commutator, hp]

theorem isQuasisimple_conjugate (hq : CFSG.Open.IsQuasisimple A) (h : G) :
    CFSG.Open.IsQuasisimple (CFSG.conjugate A h) :=
  isQuasisimple_map_conj hq h⁻¹

theorem map_conj_conjugate_eq (h t : G) :
    (CFSG.conjugate A h).map (MulAut.conj (h⁻¹ * t * h)).toMonoidHom =
      CFSG.conjugate (A.map (MulAut.conj t).toMonoidHom) h := by
  rw [CFSG.conjugate, CFSG.conjugate, F4Pilot.map_conj_map_conj_toMonoidHom,
    F4Pilot.map_conj_map_conj_toMonoidHom, show h⁻¹ * t * h * h⁻¹ = h⁻¹ * t by group]

theorem exists_surjective_conjugate_of_linearSwapDiag {S : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hδ : ∀ x ∈ A, x * (t * x * t⁻¹) ∈ S) (hsurj : ∀ y ∈ S, ∃ x ∈ A, x * (t * x * t⁻¹) = y)
    (h : G) : ∃ φ : CFSG.conjugate A h →* S, Function.Surjective φ ∧
      φ.ker ≤ center (CFSG.conjugate A h) := by
  let ψ : A ≃* CFSG.conjugate A h := A.equivMapOfInjective _ (MulAut.conj h⁻¹).injective
  let δ : A →* S := (linearSwapDiag hA).codRestrict S fun x => hδ x x.2
  refine ⟨δ.comp ψ.symm.toMonoidHom, fun y => ?_, fun z hz => ?_⟩
  · obtain ⟨x, hx, hxy⟩ := hsurj y y.2
    refine ⟨ψ ⟨x, hx⟩, Subtype.ext ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hxy
  · have h1 : ψ.symm z ∈ center A := ker_linearSwapDiag_le_center hA (by
      rw [MonoidHom.mem_ker] at hz ⊢
      exact congrArg Subtype.val hz)
    rw [mem_center_iff] at h1 ⊢
    intro w
    apply ψ.symm.injective
    rw [map_mul, map_mul]
    exact h1 (ψ.symm w)

end Diagonal

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_iSup_pieceCore_of_swap (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} {K : Type} [Field K] [Finite K]
    (hK4 : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {A : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple A)
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hcard : Nat.card L ≤ Nat.card (A ⧸ center A)) :
    A ≤ ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have : Group.IsPerfect A := ⟨hq.1⟩
  set δ := linearSwapDiag hA with hδdef
  have hperf : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map]
    exact commutator_map_eq_of_commutator_eq δ (by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top)
  have hle : δ.range ≤ L :=
    CFSG.SeitzReduction.std_perfect_le hset hOut htC ht hperf
      (range_linearSwapDiag_le_centralizer htt hA)
  have hrange : δ.range = L := Subgroup.eq_of_le_of_card_ge hle
    (hcard.trans (card_quotient_center_le_card_range_linearSwapDiag hA))
  have hmemL : ∀ x : A, δ x ∈ L := fun x => hle ⟨x, rfl⟩
  set π : A →* LinearFlag.projectiveSL (m + 1) K :=
    e.toMonoidHom.comp (δ.codRestrict L hmemL) with hπ
  have hπapp : ∀ x : A, π x = e ⟨δ x, hmemL x⟩ := fun x => rfl
  have hπs : Function.Surjective π := by
    intro z
    have hz : ((e.symm z : L) : G) ∈ δ.range := hrange ▸ (e.symm z).2
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    rw [hπapp]
    have h1 : (⟨δ x, hmemL x⟩ : L) = e.symm z := Subtype.ext hx
    rw [h1, MulEquiv.apply_symm_apply]
  have hπker : π.ker ≤ center A := by
    intro x hx
    apply ker_linearSwapDiag_le_center hA
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [hπapp] at hx
    have h1 : (⟨δ x, hmemL x⟩ : L) = 1 := by
      apply e.injective
      rw [hx, map_one]
    exact congrArg Subtype.val h1
  set I : Fin m → Finset (Fin (m + 1)) := fun i => {i.castSucc, i.succ} with hI
  set B : Fin m → Subgroup A := fun i => (blockSL (K := K) (I i)).comap π with hB
  set C : Fin m → Subgroup A := fun i => perfectCore (B i) with hC
  have hCB : ∀ i, C i ≤ B i := fun i => CFSG.Quasithin.perfectCore_le _
  have hCpiece : ∀ i, (C i).map A.subtype ≤ pieceCore e (I i) := by
    intro i
    have hperfC : ⁅(C i).map A.subtype, (C i).map A.subtype⁆ = (C i).map A.subtype := by
      rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    refine F4Pilot.le_centralizerPerfectCore hperfC ?_
    set T : Subgroup A := (blockTorus (K := K) (I i)).comap π with hT
    have hCT : (C i).map A.subtype ≤ centralizer ((T.map A.subtype : Subgroup G) : Set G) := by
      refine le_centralizer_of_commutator_le_center (M := A) (map_subtype_le _) hperfC ?_
      rw [Subgroup.commutator_le]
      rintro _ ⟨c, hc, rfl⟩ _ ⟨x, hx, rfl⟩
      have hcB : π c ∈ blockSL (K := K) (I i) := hCB i hc
      have hxT : π x ∈ blockTorus (K := K) (I i) := hx
      have hcomm : π ⁅c, x⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_centralizer_iff.1 (blockSL_le_centralizer_blockTorus (I i) hcB) _ hxT).symm
      exact ⟨⁅c, x⁆, hπker hcomm, rfl⟩
    intro w hw
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨c, hc, rfl⟩ := hw
    have hyL : y ∈ L := modelToG_le e _ hy
    obtain ⟨x, hx⟩ : y ∈ δ.range := hrange ▸ hyL
    have hxT : x ∈ T := by
      obtain ⟨z, hz, hzy⟩ := (mem_modelToG e).1 hy
      change π x ∈ blockTorus (K := K) (I i)
      have h1 : (⟨δ x, hmemL x⟩ : L) = e.symm z := Subtype.ext (hx.trans hzy.symm)
      rw [hπapp, h1, MulEquiv.apply_symm_apply]
      exact hz
    have h1 : (x : G) * c = c * x := mem_centralizer_iff.1 (hCT ⟨c, hc, rfl⟩) _ ⟨x, hxT, rfl⟩
    have h2 : (c : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * c :=
      mem_centralizer_iff.1 (hA ⟨x, x.2, rfl⟩) c c.2
    rw [← hx, hδdef, linearSwapDiag_apply]
    change (x : G) * (t * x * t⁻¹) * c = c * (x * (t * x * t⁻¹))
    calc (x : G) * (t * x * t⁻¹) * c = x * ((t * x * t⁻¹) * c) := by group
      _ = x * (c * (t * x * t⁻¹)) := by rw [h2]
      _ = (x * c) * (t * x * t⁻¹) := by group
      _ = (c * x) * (t * x * t⁻¹) := by rw [h1]
      _ = c * (x * (t * x * t⁻¹)) := by group
  have hgen : (⨆ i, C i) = ⊤ := by
    refine eq_top_of_sup_center_eq_top_of_perfect ?_
    have hi : ∀ i, (C i).map π = blockSL (K := K) (I i) := by
      intro i
      rw [hC, CFSG.Quasithin.map_perfectCore, hB, Subgroup.map_comap_eq_self_of_surjective hπs,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (commutator_blockSL_eq_of_card_two (card_nodePair i) hK4)]
    have hmap : (⨆ i, C i).map π = ⊤ := by
      rw [Subgroup.map_iSup]
      simp_rw [hi]
      rw [hI, iSup_blockSL_pair_eq_top K m]
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup A) = (⨆ i, C i) ⊔ π.ker := by
          rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
      _ ≤ (⨆ i, C i) ⊔ center A := sup_le_sup_left hπker _
  intro g hg
  have hmem : (⟨g, hg⟩ : A) ∈ ⨆ i, C i := hgen ▸ mem_top _
  have h2 : g ∈ (⨆ i, C i).map A.subtype := ⟨⟨g, hg⟩, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  exact (iSup_mono hCpiece) h2

omit [Finite G] in
theorem card_quotient_center_eq_of_swapFactors {t : G} {G₁ : Subgroup G} (hZL : center L = ⊥)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    Nat.card (G₁ ⧸ center G₁) = Nat.card L := by
  refine card_quotient_center_eq_of_linearSwapDiag h₁₂ ?_ hZL
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact hδ x x.2
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hsurj y hy
    exact ⟨⟨x, hx⟩, hxy⟩

theorem conjugate_eq_of_map_conj_eq (hset : SeitzSetting G L) {m : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL (m + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
      ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    (h : G) (hswap : (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom =
      CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h) :
    CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h =
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv (by omega) e
  have hcard₁ := card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ hsurj
  have hA : (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom ≤
      centralizer (CFSG.conjugate G₁ h : Set G) := by
    rw [hswap]
    exact conjugate_le_centralizer_of_le_centralizer h₁₂ h
  have hcardA : Nat.card L ≤ Nat.card (CFSG.conjugate G₁ h ⧸ center (CFSG.conjugate G₁ h)) := by
    rw [← Nat.card_congr (conjugateQuotientCenterEquiv G₁ h).toEquiv, hcard₁]
  have hAle := le_iSup_pieceCore_of_swap hset.standardSetting hOut hK4 e htC ht
    (isQuasisimple_conjugate hq h) hA hcardA
  rw [← hsup] at hAle
  have htG₀ : t ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
  have hBle : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h ≤
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    rw [← hswap]
    calc (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom
        ≤ (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
          map_mono hAle
      _ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom :=
          F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 htG₀
  have hle : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h ≤
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    rw [CFSG.conjugate, Subgroup.map_sup]
    exact sup_le hAle hBle
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge

theorem not_mem_centralizer_of_conj_le_centralizer (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {A : Subgroup G} (hAperf : ⁅A, A⁆ = A) (hcard : Nat.card L ≤ Nat.card A)
    (g : G) (hAB : A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G)) :
    t ∉ centralizer (A : Set G) := by
  intro htA
  have hAt : A ≤ centralizer ({t} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htA a ha)
  have hAL : A ≤ L := CFSG.SeitzReduction.std_perfect_le hset.standardSetting hOut htC ht hAperf hAt
  have hAeq : A = L := Subgroup.eq_of_le_of_card_ge hAL hcard
  obtain ⟨-, -, -, -, hnc⟩ := hset.standardSetting.standard
  apply hnc g
  rw [← hAeq, commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.2 hAB

end Swap

@[expose] def LinearSwapFactorNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (_ : L ≃* LinearFlag.projectiveSL (m + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ A : Subgroup G, CFSG.Open.IsQuasisimple A →
      (∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) →
    ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) →
      t ∈ normalizer (A : Set G) →
      t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
      t ∉ centralizer (A : Set G) →
      t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem unique_of_swapFactors (hset : SeitzSetting G L) {m : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL (m + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
      ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    (hnorm : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₁ h : Set G) →
      t ∈ normalizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      t ∉ centralizer (CFSG.conjugate G₁ h : Set G) →
      t ∉ centralizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) → False) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ i : Fin m,
        pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) : Subgroup G) : Set G) →
      g ∈ normalizer ((⨆ i : Fin m,
        pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) : Subgroup G) : Set G) := by
  rw [← hsup]
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv (by omega) e
  have hcard₁ := card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ hsurj
  refine F4Pilot.unique_of_forall_conjugate_eq fun h htM => ?_
  have hM : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h =
      CFSG.conjugate G₁ h ⊔ CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h :=
    Subgroup.map_sup _ _ _
  rw [hM] at htM
  have hqA := isQuasisimple_conjugate hq h
  have hqB := isQuasisimple_conjugate (isQuasisimple_map_conj hq t) h
  have hAB := conjugate_le_centralizer_of_le_centralizer h₁₂ h
  have hBA := le_centralizer_iff.1 hAB
  obtain ⟨hpA, hbA, hnA⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqA
  obtain ⟨hpB, hbB, hnB⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqB
  rcases F4Pilot.map_conj_eq_or_eq_of_perfect hAB hpA hbA hnA hnB htM with hAA | hswap
  ·
    rcases F4Pilot.map_conj_eq_or_eq_of_perfect hBA hpB hbB hnB hnA
        (by rw [sup_comm]; exact htM) with hBB | hBA'
    · exfalso
      have hBconj := map_conj_conjugate_eq (A := G₁) h t
      have hAconj : (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h).map
          (MulAut.conj (h⁻¹ * t * h)⁻¹).toMonoidHom = CFSG.conjugate G₁ h :=
        F4Pilot.map_conj_eq_of_map_conj_inv_eq (by rw [inv_inv]; exact hBconj)
      have hcardA : Nat.card L ≤ Nat.card (CFSG.conjugate G₁ h) := by
        rw [← hcard₁, Nat.card_congr (conjugateQuotientCenterEquiv G₁ h).toEquiv,
          Subgroup.card_eq_card_quotient_mul_card_subgroup (center (CFSG.conjugate G₁ h))]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      have hcardB : Nat.card L ≤
          Nat.card (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h) := by
        rw [← hBconj, Subgroup.card_map_of_injective (MulAut.conj _).injective]
        exact hcardA
      refine hnorm h (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hAA)
        (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hBB) ?_ ?_
      · exact not_mem_centralizer_of_conj_le_centralizer hset hOut htC ht hpA hcardA _
          (hBconj ▸ hAB)
      · exact not_mem_centralizer_of_conj_le_centralizer hset hOut htC ht hpB hcardB _
          (hAconj ▸ hBA)
    ·
      exfalso
      have hAB' : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h = CFSG.conjugate G₁ h :=
        F4Pilot.map_conj_toMonoidHom_inj.1 (hBA'.trans hAA.symm)
      rw [hAB'] at hAB
      exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hAB])
  · exact conjugate_eq_of_map_conj_eq hset hm hK4 e htC ht hq h₁₂ hsup hδ hsurj h hswap

end Unique

theorem unique_of_swapFactors_of_factorNormal (hN : LinearSwapFactorNormalInput) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L) {m f : ℕ} (hm : 3 ≤ m)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
      ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ i : Fin m,
        pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) : Subgroup G) : Set G) →
      g ∈ normalizer ((⨆ i : Fin m,
        pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) : Subgroup G) : Set G) := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hK4 : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  refine unique_of_swapFactors hset (by omega) hK4 e htC ht hq h₁₂ hsup hδ hsurj
    fun h htA htB hnA hnB => ?_
  have hBconj := map_conj_conjugate_eq (A := G₁) h t
  refine hN G L hset m f K hm hKc hf e t ht hKt (CFSG.conjugate G₁ h)
    (isQuasisimple_conjugate hq h)
    (exists_surjective_conjugate_of_linearSwapDiag h₁₂ hδ hsurj h) (h⁻¹ * t * h) ?_ htA ?_ hnA ?_
  · rw [hBconj]
    exact conjugate_le_centralizer_of_le_centralizer h₁₂ h
  · rw [hBconj]
    exact htB
  · rw [hBconj]
    exact hnB

theorem linearSwapRowUniqueInput_of_factorNormal (hN : LinearSwapFactorNormalInput) :
    LinearSwapRowUniqueInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt _ G₁ hq h₁₂ hsup hδ hsurj
  exact unique_of_swapFactors_of_factorNormal hN hset (by omega) hKc hf e ht hKt hq h₁₂ hsup hδ
    hsurj

end CFSG.SeitzReduction.LinearPilot
