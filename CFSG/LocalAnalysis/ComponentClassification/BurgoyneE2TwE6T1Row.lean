module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Setup
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Frame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Transfer

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups


variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {L : Type} [Field L]
  [Algebra K L] [IsAlgClosure K L] [CharP L p]

omit [Finite K] in
theorem t1_preimage (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀R : g₀ ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)))
    {v : ModGL TwistTag.E6.tag L} :
    v ∈ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L))⁆ ↔
      ∃ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        g₀ * baseChangeGL (algebraMap K L) (s : ModGL TwistTag.E6.tag K) * g₀⁻¹ = v := by
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  have hH := t1_derived_eq (L := L) hp2 hf hK σ hσ
  have hRc : ∀ y ∈ R, ⁅R, R⁆.map (MulAut.conj y).toMonoidHom = ⁅R, R⁆ := by
    intro y hy
    have hRy : R.map (MulAut.conj y).toMonoidHom = R := by
      refine le_antisymm ?_ fun x hx => ⟨y⁻¹ * x * y, mul_mem (mul_mem (inv_mem hy) hx) hy, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact mul_mem (mul_mem hy hx) (inv_mem hy)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    rw [Subgroup.map_commutator, hRy]
  constructor
  · intro hv
    have h := Subgroup.mem_map_of_mem (MulAut.conj g₀⁻¹).toMonoidHom hv
    rw [hRc _ (inv_mem hg₀R), hH] at h
    obtain ⟨y, hy, hyv⟩ := h
    refine ⟨⟨y, hy⟩, ?_⟩
    change g₀ * baseChangeGL (algebraMap K L) y * g₀⁻¹ = v
    rw [hyv]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · rintro ⟨s, rfl⟩
    have h : baseChangeGL (algebraMap K L) (s : ModGL TwistTag.E6.tag K) ∈ ⁅R, R⁆ := by
      rw [hH]
      exact Subgroup.mem_map_of_mem _ s.2
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj g₀).toMonoidHom h
    rw [hRc _ hg₀R] at h2
    exact h2

theorem burgTorusFor_t1 (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀G : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hg₀F : frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) g₀ = g₀)
    (hg₀t : g₀ * baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) * g₀⁻¹ =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) :
    BurgTorusFor (MulAut.conj t) := by
  classical
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L p]; exact hp2
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L) with hι
  set a := signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20) with ha
  set d := rootDiagUnit TwistTag.E6.tag a with hd
  have hg₀R : g₀ ∈ R := mem_fixedPointsIn.2 ⟨hg₀G, hg₀F⟩
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  have hRR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hιR : ∀ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ι (s : ModGL TwistTag.E6.tag K) ∈ R := fun s => hRR ((t1_preimage hp2 hf hK σ hσ
        (one_mem R)).2 ⟨s, by rw [one_mul, inv_one, mul_one]⟩)
  obtain ⟨w, hwM, hwN⟩ := exists_e6_untwist (L := L) hp2 hf
  have hwG : w ∈ adjointGroup TwistTag.E6.tag L := (mem_toralCentralizer.1 hwM).1
  have hwd : w * d = d * w := by
    have h := (mem_toralCentralizer.1 hwM).2
    calc w * d = (d * w * d⁻¹) * d := by rw [h]
      _ = d * w := by group
  set v := w * g₀ with hv
  have hvG : v ∈ adjointGroup TwistTag.E6.tag L := mul_mem hwG hg₀G
  have hvcoc : v * (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) v)⁻¹ =
      wordWeylMatrix TwistTag.E6.tag L e6W0Word := by
    rw [hv, map_mul, hg₀F, ← hwN]
    group
  set Ψ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj v).toMonoidHom.comp
      (ι.comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype) with hΨ
  have hΨinj : Function.Injective Ψ :=
    (MulAut.conj v).injective.comp (hιinj.comp Subtype.val_injective)
  have hΨapp : ∀ s, Ψ s = w * (g₀ * ι (s : ModGL TwistTag.E6.tag K) * g₀⁻¹) * w⁻¹ := fun s => by
    change v * ι (s : ModGL TwistTag.E6.tag K) * v⁻¹ = _
    rw [hv]
    group
  have hΨv : ∀ s, v⁻¹ * Ψ s * v = ι (s : ModGL TwistTag.E6.tag K) := fun s => by
    change v⁻¹ * (v * ι (s : ModGL TwistTag.E6.tag K) * v⁻¹) * v = _
    group
  have hΨt : Ψ t = d := by
    rw [hΨapp, hg₀t, hwd]
    group
  obtain ⟨CA, hqCA, hCAH, hCAn, hCAind⟩ := exists_t1_layer hp2 hf hK σ hσ hg₀R
  obtain ⟨K', _, _, _, hK'⟩ := RankThree.PartOne.KE.exists_finite_field_into p f hf L
  have : CharP K' p := finite_field_prime_power_characteristic hp hf hK'
  have hK'2 : ringChar K' ≠ 2 := by rw [ringChar.eq K' p]; exact hp2
  obtain ⟨S', e, he1, hS'H, hS'c, hS'd, hS'χ⟩ :=
    exists_t1_sl2_frame (K := K') hp2 hK' (by omega) hvG hvcoc
  have hqK : IsQuasisimple (SL(2, K')) := by
    have : Fintype K' := Fintype.ofFinite K'
    have h4 : ∃ s : Finset K', s.card = 4 := by
      have h : 4 ≤ (Finset.univ : Finset K').card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK']
        omega
      obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq h
      exact ⟨u, hu⟩
    exact RankThree.Classical.isQuasisimple_SL2 h4
  have hvd : ∀ {c : Fin TwistTag.E6.tag.rank → Lˣ}, c (t1Node 0) = 1 → c (t1Node 1) = 1 →
      c (t1Node 3) = 1 → c (t1Node 5) = 1 → c (t1Node 2) * c (t1Node 4) = 1 →
      rootDiagUnit TwistTag.E6.tag c ∈ R → v⁻¹ * rootDiagUnit TwistTag.E6.tag c * v ∈ R := by
    intro c h0 h1 h3 h5 h24 hcR
    have hcw := rootDiagUnit_commute_toralCentralizer_d20 hL2 h0 h1 h3 h5 h24 hwM
    rw [hv, show (w * g₀)⁻¹ * rootDiagUnit TwistTag.E6.tag c * (w * g₀) =
      g₀⁻¹ * (w⁻¹ * (rootDiagUnit TwistTag.E6.tag c * w)) * g₀ by group, hcw,
      show w⁻¹ * (w * rootDiagUnit TwistTag.E6.tag c) = rootDiagUnit TwistTag.E6.tag c by group]
    exact mul_mem (mul_mem (inv_mem hg₀R) hcR) hg₀R
  have hvdR : v⁻¹ * d * v ∈ R := by
    rw [← hΨt, hΨv]
    exact hιR t
  refine burgTorusFor_of_frame_induced hΨinj (C' := CA.map (MulAut.conj w).toMonoidHom)
    (S' := S') ?_ ?_ (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CA.equivMapOfInjective _ (MulAut.conj w).injective) hqCA) hK'2 hqK e ?_ ?_ ?_ (x' := d)
    ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, hs⟩ := (t1_preimage hp2 hf hK σ hσ hg₀R).1 (hCAH hy).1
    exact ⟨s, by rw [hΨapp, hs]; rfl⟩
  · intro x hx
    obtain ⟨s, hs⟩ := (t1_preimage hp2 hf hK σ hσ (one_mem R)).1 (hS'H x hx)
    refine ⟨s, ?_⟩
    rw [one_mul, inv_one, mul_one] at hs
    calc Ψ s = v * (v⁻¹ * Ψ s * v) * v⁻¹ := by group
      _ = x := by rw [hΨv, hs]; group
  · rintro c ⟨y, hy, hyc⟩
    have hyd : y * d = d * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hCAH hy)).2
    have h : Ψ c * Ψ t = Ψ t * Ψ c := by
      rw [hΨt, ← hyc]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc w * y * w⁻¹ * d = w * (y * d) * w⁻¹ := by
            rw [show w * y * w⁻¹ * d = w * y * (w⁻¹ * d) by group,
              show w⁻¹ * d = d * w⁻¹ by
                calc w⁻¹ * d = w⁻¹ * (d * w) * w⁻¹ := by group
                  _ = w⁻¹ * (w * d) * w⁻¹ := by rw [hwd]
                  _ = d * w⁻¹ := by group]
            group
        _ = w * (d * y) * w⁻¹ := by rw [hyd]
        _ = d * (w * y * w⁻¹) := by rw [show w * (d * y) * w⁻¹ = (w * d) * y * w⁻¹ by group, hwd]
                                    group
    rw [← map_mul, ← map_mul] at h
    have hct := hΨinj h
    rw [MulAut.conj_apply, ← hct]
    group
  · intro c hc x hx
    have hct : c * t = t * c := by
      rw [MulAut.conj_apply] at hc
      calc c * t = (t * c * t⁻¹) * t := by rw [hc]
        _ = t * c := by group
    have hyR : g₀ * ι (c : ModGL TwistTag.E6.tag K) * g₀⁻¹ ∈ R ⊓
        Subgroup.centralizer {d} := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg₀R (hιR c)) (inv_mem hg₀R), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg₀t]
      have hct' : ι (c : ModGL TwistTag.E6.tag K) * ι (t : ModGL TwistTag.E6.tag K) =
          ι (t : ModGL TwistTag.E6.tag K) * ι (c : ModGL TwistTag.E6.tag K) := by
        rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hct]
      calc g₀ * ι (c : ModGL TwistTag.E6.tag K) * g₀⁻¹ *
            (g₀ * ι (t : ModGL TwistTag.E6.tag K) * g₀⁻¹) =
          g₀ * (ι (c : ModGL TwistTag.E6.tag K) * ι (t : ModGL TwistTag.E6.tag K)) * g₀⁻¹ := by
            group
        _ = g₀ * (ι (t : ModGL TwistTag.E6.tag K) * ι (c : ModGL TwistTag.E6.tag K)) * g₀⁻¹ := by
            rw [hct']
        _ = _ := by group
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨_, hCAn _ hyR x' hx', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hΨapp]
    group
  · intro c hc x hx
    refine hS'c (Ψ c) (by rw [hΨapp]; exact mul_mem (mul_mem hwG (mul_mem (mul_mem hg₀G
      (mem_fixedPointsIn.1 (hιR c)).1) (inv_mem hg₀G))) (inv_mem hwG))
      (by rw [hΨv]; exact hιR c) (by rw [← he1]; exact hc) x hx
  · intro s
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hΨt]
  · exact hS'd a hvdR
  · intro x hx
    have h := hS'd a⁻¹ (by
      rw [← rootDiagUnit_inv, show v⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ * v =
        (v⁻¹ * rootDiagUnit TwistTag.E6.tag a * v)⁻¹ by group]
      exact inv_mem hvdR) x hx
    rwa [← rootDiagUnit_inv, inv_inv] at h
  · by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have h := hS'χ a fun x hx => by
      calc d * x = d * x * d⁻¹ * d := by group
        _ = x * d := by rw [hcon x hx]
    rw [rootChar_twenty_three] at h
    have h' := congrArg (fun z : Lˣ => (z : L)) h
    simp only [Units.val_neg, Units.val_one] at h'
    exact Ring.neg_one_ne_one_of_char_ne_two hL2 h'
  · intro β hβ _ hfixQ
    obtain ⟨c, h0, h1, h3, h5, h24, hcR, hcβ⟩ := hCAind β hβ fun s hs => hfixQ s (by
      rw [hΨapp]
      exact ⟨_, hs, rfl⟩)
    have hcw := rootDiagUnit_commute_toralCentralizer_d20 hL2 h0 h1 h3 h5 h24 hwM
    have hvc := hvd h0 h1 h3 h5 h24 hcR
    refine ⟨rootDiagUnit TwistTag.E6.tag c, fun s => ?_, hS'd c hvc, fun x hx => ?_,
      fun hcS => ?_⟩
    · rw [hΨapp, hΨapp, hcβ s]
      calc w * (rootDiagUnit TwistTag.E6.tag c * (g₀ * ι (s : ModGL TwistTag.E6.tag K) * g₀⁻¹) *
            (rootDiagUnit TwistTag.E6.tag c)⁻¹) * w⁻¹ =
          (w * rootDiagUnit TwistTag.E6.tag c) * (g₀ * ι (s : ModGL TwistTag.E6.tag K) * g₀⁻¹) *
            (w * rootDiagUnit TwistTag.E6.tag c)⁻¹ := by group
        _ = _ := by rw [← hcw]; group
    · have h := hS'd c⁻¹ (by
        rw [← rootDiagUnit_inv, show v⁻¹ * (rootDiagUnit TwistTag.E6.tag c)⁻¹ * v =
          (v⁻¹ * rootDiagUnit TwistTag.E6.tag c * v)⁻¹ by group]
        exact inv_mem hvc) x hx
      rwa [← rootDiagUnit_inv, inv_inv] at h
    · have hχ := hS'χ c hcS
      rw [CFSG.ComponentClassification.CatLeafProof.rootChar_single'] at hχ
      have h4 : c (t1Node 4) = 1 := by rwa [hχ, one_mul] at h24
      have hc1 : c = 1 := by
        funext i
        obtain ⟨j, rfl⟩ : ∃ j : Fin 6, t1Node j = i := ⟨i, rfl⟩
        fin_cases j
        · exact h0
        · exact h1
        · exact hχ
        · exact h3
        · exact h4
        · exact h5
      intro s
      apply hΨinj
      rw [hΨapp, hΨapp, hcβ s, hc1, rootDiagUnit_one, one_mul, inv_one, mul_one]

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
