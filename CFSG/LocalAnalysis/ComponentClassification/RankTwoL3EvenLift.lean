module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenKey

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial LinearFlag
  FieldFourCover CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] {F : Type} [Field F] {A : Subgroup G}

@[expose] def liftN (ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F))
    (S : Subgroup (MulAut (projectiveSL 3 F))) : Subgroup (normalizer (A : Set G)) :=
  A.subgroupOf (normalizer (A : Set G)) ⊓ S.comap ψ

@[expose] def liftIn (ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F))
    (S : Subgroup (MulAut (projectiveSL 3 F))) : Subgroup G :=
  (liftN ψ S).map (normalizer (A : Set G)).subtype

@[expose] def leviLift (ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F))
    (S : Subgroup (MulAut (projectiveSL 3 F))) : Subgroup G :=
  ⁅liftIn ψ S, liftIn ψ S⁆

variable {ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)}
  {S : Subgroup (MulAut (projectiveSL 3 F))}

theorem mem_liftIn {x : G} :
    x ∈ liftIn ψ S ↔ ∃ hx : x ∈ A, ψ ⟨x, le_normalizer hx⟩ ∈ S := by
  constructor
  · rintro ⟨⟨y, hyN⟩, ⟨hyA, hyS⟩, rfl⟩
    exact ⟨hyA, hyS⟩
  · rintro ⟨hx, hxS⟩
    exact ⟨⟨x, le_normalizer hx⟩, ⟨hx, hxS⟩, rfl⟩

theorem liftIn_le : liftIn ψ S ≤ A := fun _ hx => (mem_liftIn.1 hx).1

theorem leviLift_le_liftIn : leviLift ψ S ≤ liftIn ψ S :=
  (commutator_le).2 fun _ ha _ hb => commutatorElement_mem' ha hb

theorem leviLift_le : leviLift ψ S ≤ A :=
  leviLift_le_liftIn.trans liftIn_le

theorem leviLift_eq_map :
    leviLift ψ S = (⁅liftN ψ S, liftN ψ S⁆).map (normalizer (A : Set G)).subtype := by
  rw [leviLift, liftIn, map_commutator]

theorem map_liftN (hψ : IsActionHom A
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hS : S ≤ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) :
    (liftN ψ S).map ψ = S := by
  refine le_antisymm (map_le_iff_le_comap.2 inf_le_right) fun s hs => ?_
  obtain ⟨a, ha, has⟩ := hψ.exists_eq s (hS hs)
  exact ⟨⟨a, le_normalizer ha⟩, mem_inf.2 ⟨ha, mem_comap.2 (by rw [has]; exact hs)⟩, has⟩

theorem map_commutator_liftN (hψ : IsActionHom A
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hS : S ≤ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range)
    (hperf : ⁅S, S⁆ = S) : (⁅liftN ψ S, liftN ψ S⁆).map ψ = S := by
  rw [map_commutator, map_liftN hψ hS, hperf]

theorem psi_mem_of_mem_leviLift {l : G} (hl : l ∈ leviLift ψ S) :
    ψ ⟨l, le_normalizer (leviLift_le hl)⟩ ∈ S :=
  (mem_liftIn.1 (leviLift_le_liftIn hl)).2

theorem exists_mem_leviLift (hψ : IsActionHom A
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hS : S ≤ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range)
    (hperf : ⁅S, S⁆ = S) {s : MulAut (projectiveSL 3 F)} (hs : s ∈ S) :
    ∃ l : G, ∃ hl : l ∈ leviLift ψ S, ψ ⟨l, le_normalizer (leviLift_le hl)⟩ = s := by
  rw [← map_commutator_liftN hψ hS hperf] at hs
  obtain ⟨n, hn, rfl⟩ := hs
  refine ⟨n, ?_, rfl⟩
  rw [leviLift_eq_map]
  exact ⟨n, hn, rfl⟩

theorem leviLift_le_centralizer (hψ : IsActionHom A
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    {w : G} (hwN : w ∈ normalizer (A : Set G))
    (hw : ∀ s ∈ S, ψ ⟨w, hwN⟩ * s = s * ψ ⟨w, hwN⟩) :
    leviLift ψ S ≤ centralizer ({w} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  refine (commute_of_mem_commutator (S := liftIn ψ S) (Z := A ⊓ centralizer (A : Set G))
    (fun z hz => mem_centralizer_iff.2 fun s hs => ?_) (fun a ha b hb => ?_) (fun s hs => ?_)
    hx).symm
  · exact (mem_centralizer_iff.1 hz.2 s (liftIn_le hs))
  · exact mem_centralizer_iff.1 hb.2 a ha.1
  · obtain ⟨hsA, hsS⟩ := mem_liftIn.1 hs
    have hmem : w * s * w⁻¹ * s⁻¹ ∈ A := by
      have h1 : w * s * w⁻¹ ∈ A := (mem_normalizer_iff.1 hwN s).1 hsA
      exact mul_mem h1 (inv_mem hsA)
    refine ⟨hmem, (hψ.eq_one_iff ⟨_, le_normalizer hmem⟩).1 ?_⟩
    have hsN := le_normalizer hsA
    rw [psi_mul (mul_mem (mul_mem hwN hsN) (inv_mem hwN)) (inv_mem hsN),
      psi_mul (mul_mem hwN hsN) (inv_mem hwN), psi_mul hwN hsN, psi_inv hwN, psi_inv hsN,
      hw _ hsS]
    group

theorem mem_normalizer_liftIn {y : G} (hyN : y ∈ normalizer (A : Set G))
    (hy : ψ ⟨y, hyN⟩ ∈ normalizer (S : Set (MulAut (projectiveSL 3 F)))) :
    y ∈ normalizer (liftIn ψ S : Set G) := by
  have key : ∀ z : G, ∀ hzN : z ∈ normalizer (A : Set G),
      ψ ⟨z, hzN⟩ ∈ normalizer (S : Set (MulAut (projectiveSL 3 F))) →
        ∀ x ∈ liftIn ψ S, z * x * z⁻¹ ∈ liftIn ψ S := by
    intro z hzN hz x hx
    obtain ⟨hxA, hxS⟩ := mem_liftIn.1 hx
    have hmem : z * x * z⁻¹ ∈ A := (mem_normalizer_iff.1 hzN x).1 hxA
    refine mem_liftIn.2 ⟨hmem, ?_⟩
    have hxN := le_normalizer hxA
    have h1 : (⟨z * x * z⁻¹, le_normalizer hmem⟩ : normalizer (A : Set G)) =
        ⟨z, hzN⟩ * ⟨x, hxN⟩ * ⟨z, hzN⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hz _).1 hxS
  refine mem_normalizer_iff.2 fun x => ⟨key y hyN hy x, fun hx => ?_⟩
  have hy' : ψ ⟨y⁻¹, inv_mem hyN⟩ ∈ normalizer (S : Set (MulAut (projectiveSL 3 F))) := by
    rw [psi_inv hyN]
    exact inv_mem hy
  have := key y⁻¹ (inv_mem hyN) hy' _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_leviLift {y : G} (hyN : y ∈ normalizer (A : Set G))
    (hy : ψ ⟨y, hyN⟩ ∈ normalizer (S : Set (MulAut (projectiveSL 3 F)))) :
    y ∈ normalizer (leviLift ψ S : Set G) := by
  have h := mem_normalizer_liftIn hyN hy
  rw [mem_normalizer_iff_map_conj_eq] at h ⊢
  rw [leviLift, map_commutator, h]

theorem commutatorElement_mul_mul_of_commute {M : Type*} [Group M] {a b z w : M}
    (hzb : z * b = b * z) (hwa : w * a = a * w) (hzw : z * w = w * z) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb]; group
    _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw, mul_inv_cancel_right]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by
        have h : w * a⁻¹ = a⁻¹ * w := by
          calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
            _ = a⁻¹ * (w * a) * a⁻¹ := by rw [hwa]
            _ = a⁻¹ * w := by group
        rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

variable (ψ S) in
@[expose] def leviLiftPsi : leviLift ψ S →* S :=
  (ψ.comp (Subgroup.inclusion (leviLift_le.trans le_normalizer))).codRestrict S fun l =>
    psi_mem_of_mem_leviLift l.2

theorem leviLiftPsi_apply (l : leviLift ψ S) :
    ((leviLiftPsi ψ S l : S) : MulAut (projectiveSL 3 F)) =
      ψ ⟨l, le_normalizer (leviLift_le l.2)⟩ :=
  rfl

variable (hψ : IsActionHom A
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
  (hS : S ≤ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range)
  (hperf : ⁅S, S⁆ = S)
include hψ hS hperf

theorem exists_mem_leviLift_inv_mul_mem {a : G} (ha : a ∈ liftIn ψ S) :
    ∃ l ∈ leviLift ψ S, l⁻¹ * a ∈ A ⊓ centralizer (A : Set G) := by
  obtain ⟨haA, haS⟩ := mem_liftIn.1 ha
  obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ hS hperf haS
  exact ⟨l, hl, inv_mul_mem_of_psi_eq hψ (leviLift_le hl) haA hlψ⟩

theorem commutator_leviLift : ⁅leviLift ψ S, leviLift ψ S⁆ = leviLift ψ S := by
  refine le_antisymm ((commutator_le).2 fun a ha b hb => commutatorElement_mem' ha hb) ?_
  conv_lhs => rw [leviLift]
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨l₁, hl₁, hz₁⟩ := exists_mem_leviLift_inv_mul_mem hψ hS hperf ha
  obtain ⟨l₂, hl₂, hz₂⟩ := exists_mem_leviLift_inv_mul_mem hψ hS hperf hb
  have hcomm : ⁅a, b⁆ = ⁅l₁, l₂⁆ := by
    have e1 : a = l₁ * (l₁⁻¹ * a) := by group
    have e2 : b = l₂ * (l₂⁻¹ * b) := by group
    rw [e1, e2]
    refine commutatorElement_mul_mul_of_commute ?_ ?_ ?_
    · exact (mem_centralizer_iff.1 hz₁.2 l₂ (leviLift_le hl₂)).symm
    · exact (mem_centralizer_iff.1 hz₂.2 l₁ (leviLift_le hl₁)).symm
    · exact mem_centralizer_iff.1 hz₂.2 _ hz₁.1
  rw [hcomm]
  exact commutator_mem_commutator hl₁ hl₂

theorem mem_leviLift_of_pow [Finite G]
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G))) {a : G}
    (ha : a ∈ liftIn ψ S) {k : ℕ} (hak : a ^ 2 ^ k = 1) : a ∈ leviLift ψ S := by
  obtain ⟨l, hl, hz⟩ := exists_mem_leviLift_inv_mul_mem hψ hS hperf ha
  obtain ⟨e, -, -, he3, he4⟩ := exists_twoPartExp G
  have hcomm : Commute l (l⁻¹ * a) := mem_centralizer_iff.1 hz.2 l (leviLift_le hl)
  have h1 : a = l ^ e := by
    calc a = a ^ e := (he3 a k hak).symm
      _ = (l * (l⁻¹ * a)) ^ e := by rw [mul_inv_cancel_left]
      _ = l ^ e * (l⁻¹ * a) ^ e := hcomm.mul_pow e
      _ = l ^ e := by rw [he4 _ (odd_orderOf_of_mem hZ hz), mul_one]
  rw [h1]
  exact pow_mem hl e

theorem leviLiftPsi_surjective : Function.Surjective (leviLiftPsi ψ S) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, hl, hls⟩ := exists_mem_leviLift hψ hS hperf hs
  exact ⟨⟨l, hl⟩, Subtype.ext hls⟩

theorem ker_leviLiftPsi (hZS : center S = ⊥) : (leviLiftPsi ψ S).ker = center (leviLift ψ S) := by
  ext l
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hC : (l : G) ∈ centralizer (A : Set G) := by
      refine (hψ.eq_one_iff ⟨l, le_normalizer (leviLift_le l.2)⟩).1 ?_
      have := congrArg Subtype.val h
      rwa [leviLiftPsi_apply] at this
    rw [mem_center_iff]
    intro l'
    exact Subtype.ext (mem_centralizer_iff.1 hC l' (leviLift_le l'.2))
  · intro h
    have hc : leviLiftPsi ψ S l ∈ center S := by
      rw [mem_center_iff]
      intro s
      obtain ⟨l', rfl⟩ := leviLiftPsi_surjective hψ hS hperf s
      rw [← map_mul, ← map_mul, (mem_center_iff.1 h l')]
    rw [hZS, mem_bot] at hc
    exact hc

@[expose] def leviLiftQuotEquiv (hZS : center S = ⊥) : leviLift ψ S ⧸ center (leviLift ψ S) ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq (ker_leviLiftPsi hψ hS hperf hZS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (leviLiftPsi_surjective hψ hS hperf))

theorem isQuasisimple_leviLift (hZS : center S = ⊥) [IsSimpleGroup S] :
    CFSG.Open.IsQuasisimple (leviLift ψ S) := by
  have : Group.IsPerfect (leviLift ψ S) :=
    (Subgroup.isPerfect_iff).2 (commutator_leviLift hψ hS hperf)
  exact ⟨Group.IsPerfect.commutator_eq_top, (leviLiftQuotEquiv hψ hS hperf hZS).isSimpleGroup⟩

end Lift

end CFSG.ComponentClassification.RankTwoL3Even
