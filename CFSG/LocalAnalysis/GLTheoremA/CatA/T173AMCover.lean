module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.PerfectCover
open CFSG.LieType.Steinberg
open Subgroup

private theorem card_center_dvd_griess_perfect {S Q : Type} [Group S] [Group Q]
    (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv, ← hker, ← hmap]
  exact Subgroup.card_map_dvd (H := hopfMultiplier S) (hopfLift q hq hker.le)

private theorem isPerfect_commutator_of_central_quotient {G Q : Type*} [Group G] [Group Q]
    [Group.IsPerfect Q] (φ : G →* Q) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center G) : Group.IsPerfect (commutator G) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm ?_ ?_
  · exact Subgroup.commutator_le_self (commutator G)
  · have hsup : commutator G ⊔ φ.ker = ⊤ := by
      have hmap : (commutator G).map φ = ⊤ := by
        rw [_root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective φ hφ]
        exact Group.IsPerfect.commutator_eq_top
      have h := Subgroup.comap_map_eq (f := φ) (commutator G)
      rw [hmap, Subgroup.comap_top] at h
      exact h.symm
    rw [_root_.commutator_def]
    refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤)
      (H₃ := ⁅commutator G, commutator G⁆)).mpr ?_
    intro g _ h _
    have hg' : g ∈ (↑(commutator G ⊔ φ.ker) : Set G) := by rw [hsup]; trivial
    rw [Subgroup.mul_normal, Set.mem_mul] at hg'
    obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := hg'
    have hh' : h ∈ (↑(commutator G ⊔ φ.ker) : Set G) := by rw [hsup]; trivial
    rw [Subgroup.mul_normal, Set.mem_mul] at hh'
    obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := hh'
    rw [Subgroup.mem_center_iff.mp (hZ hz₁) c₁, Subgroup.mem_center_iff.mp (hZ hz₂) c₂,
      commutatorElement_mul_mul_of_mem_center (hZ hz₁) (hZ hz₂)]
    exact Subgroup.commutator_mem_commutator (H₁ := commutator G) (H₂ := commutator G) hc₁ hc₂

private theorem cover_exact_aux {S U R : Type} [Group S] [Finite S] [Group U] [Finite U]
    [Group R] (hSperf : Group.IsPerfect S) (hSodd : Odd (Nat.card (Subgroup.center S)))
    (hU : Group.IsPerfect U) (π : U →* R) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hkodd : Odd (Nat.card π.ker))
    (hR : Subgroup.center R = ⊥) (e : S ⧸ Subgroup.center S ≃* R)
    [Finite (CFSG.Open.griessHopfMultiplier R)] {k : ℕ}
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier R) ∣ Nat.card π.ker * 2 ^ k) :
    ∃ ψ : U →* S, ∀ u : U, e (QuotientGroup.mk (ψ u)) = π u := by
  have hperfS : Group.IsPerfect S := hSperf
  let qS : S →* R := centralQuotientMap e
  have hqS : Function.Surjective qS := centralQuotientMap_surjective e
  have hqSker : qS.ker = Subgroup.center S := centralQuotientMap_ker e
  haveI : Finite R := finite_of_surjective_monoidHom qS hqS
  haveI : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := qS) hqS
  let W : Subgroup (U × S) := pullback π qS
  have hWmem : ∀ x : W, π (x : U × S).1 = qS (x : U × S).2 :=
    fun x => mem_pullback.mp x.2
  let prU : W →* U := pullbackFst π qS
  let prS : W →* S := (MonoidHom.snd U S).comp W.subtype
  have hprU : Function.Surjective prU :=
    pullbackFst_surjective (β := π) (η := qS) hqS
  have hprS : Function.Surjective prS := by
    intro s
    obtain ⟨u, hu⟩ := hπ (qS s)
    exact ⟨⟨(u, s), by rw [mem_pullback]; exact hu⟩, rfl⟩
  have hZW : (π.comp prU).ker ≤ Subgroup.center W := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (x : U × S).1 ∈ π.ker := hx
    have hx2 : (x : U × S).2 ∈ Subgroup.center S := by
      rw [← hqSker, MonoidHom.mem_ker, ← hWmem x]
      exact MonoidHom.mem_ker.mp hx1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Subgroup.mem_center_iff.mp (hker hx1) (y : U × S).1
    · exact Subgroup.mem_center_iff.mp hx2 (y : U × S).2
  let M : Subgroup W := commutator W
  have hMperf : Group.IsPerfect M :=
    isPerfect_commutator_of_central_quotient (π.comp prU) (hπ.comp hprU) hZW
  let qM : M →* R := (π.comp prU).comp M.subtype
  have hqM : Function.Surjective qM := by
    have hmap : M.map (π.comp prU) = ⊤ := by
      change (commutator W).map (π.comp prU) = ⊤
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective (π.comp prU) (hπ.comp hprU)]
      exact Group.IsPerfect.commutator_eq_top
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmap
  have hker_le : qM.ker ≤ Subgroup.center M := by
    intro x hx
    have hxcen : (x : W) ∈ Subgroup.center W := hZW hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxcen (y : W))
  have hcenter_le : Subgroup.center M ≤ qM.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxR : qM x ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨m, hm⟩ := hqM r
      have hxcomm : m * x = x * m := Subgroup.mem_center_iff.mp hx m
      have h := congrArg qM hxcomm
      simpa [map_mul, hm] using h
    rw [hR] at hxR
    simpa using hxR
  have hker_eq : Subgroup.center M = qM.ker := le_antisymm hcenter_le hker_le
  have eM : M ⧸ Subgroup.center M ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective qM hqM)
  have hApvd : Nat.card (Subgroup.center M) ∣ Nat.card (CFSG.Open.griessHopfMultiplier R) :=
    card_center_dvd_griess_perfect hMperf eM
  have hAodd : Odd (Nat.card (Subgroup.center M)) := by
    let Z : Subgroup (U × S) := (Subgroup.center M).map (W.subtype.comp M.subtype)
    have hZcen : Z ≤ π.ker.prod (Subgroup.center S) := by
      rintro z ⟨x, hx, rfl⟩
      have hxker : x ∈ qM.ker := hcenter_le hx
      have hx1 : π (((x : M) : W) : U × S).1 = 1 := hxker
      have hx2 : (((x : M) : W) : U × S).2 ∈ Subgroup.center S := by
        rw [← hqSker, MonoidHom.mem_ker, ← mem_pullback.mp (x : W).2]
        exact hx1
      exact Subgroup.mem_prod.mpr ⟨hx1, hx2⟩
    have hdvd : Nat.card (Subgroup.center M) ∣ Nat.card (π.ker.prod (Subgroup.center S)) := by
      rw [← Subgroup.card_map_of_injective
        (f := W.subtype.comp M.subtype) (W.subtype_injective.comp M.subtype_injective)]
      exact Subgroup.card_dvd_of_le hZcen
    have hoddZ : Odd (Nat.card (π.ker.prod (Subgroup.center S))) := by
      rw [Nat.card_congr (Subgroup.prodEquiv π.ker (Subgroup.center S)).toEquiv, Nat.card_prod]
      exact hkodd.mul hSodd
    exact Odd.of_dvd_nat hoddZ hdvd
  have hA2 : Nat.card (Subgroup.center M) ∣ Nat.card π.ker * 2 ^ k := hApvd.trans hM
  have hA_dvd : Nat.card (Subgroup.center M) ∣ Nat.card π.ker := by
    have hcop : Nat.Coprime (Nat.card (Subgroup.center M)) (2 ^ k) :=
      Nat.Coprime.pow_right k hAodd.coprime_two_right
    exact (hcop.dvd_mul_right).mp hA2
  have hMcard : Nat.card M = Nat.card R * Nat.card (Subgroup.center M) := by
    rw [card_eq_card_mul_card_ker qM hqM, ← hker_eq]
  have hUcard : Nat.card U = Nat.card R * Nat.card π.ker :=
    card_eq_card_mul_card_ker π hπ
  have hle : Nat.card M ≤ Nat.card U := by
    rw [hMcard, hUcard]
    exact Nat.mul_le_mul_left _ (Nat.le_of_dvd Nat.card_pos hA_dvd)
  have hprUM : Function.Surjective (prU.comp M.subtype) := by
    have hmap : M.map prU = ⊤ := by
      change (commutator W).map prU = ⊤
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective prU hprU]
      exact Group.IsPerfect.commutator_eq_top
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmap
  have hbij : Function.Bijective (prU.comp M.subtype) :=
    (Nat.bijective_iff_surjective_and_card _).mpr
      ⟨hprUM, le_antisymm hle (Nat.card_le_card_of_surjective _ hprUM)⟩
  let eMU : M ≃* U := MulEquiv.ofBijective (prU.comp M.subtype) hbij
  refine ⟨(prS.comp M.subtype).comp eMU.symm.toMonoidHom, ?_⟩
  intro u
  have hm : prU ((eMU.symm u : M) : W) = u := eMU.apply_symm_apply u
  calc e (QuotientGroup.mk ((prS.comp M.subtype) (eMU.symm u)))
      = qS ((prS.comp M.subtype) (eMU.symm u)) := rfl
    _ = π (prU ((eMU.symm u : M) : W)) :=
        (mem_pullback.mp ((eMU.symm u : M) : W).2).symm
    _ = π u := by rw [hm]

theorem cover_center_dvd {S R : Type} [Group S] [Finite S] [Group R]
    (hS : CFSG.Open.IsQuasisimple S) (θ : S ⧸ Subgroup.center S ≃* R)
    [Finite (CFSG.Open.griessHopfMultiplier R)] :
    Nat.card (Subgroup.center S) ∣ Nat.card (CFSG.Open.griessHopfMultiplier R) := by
  have hperf : Group.IsPerfect S := ⟨hS.1⟩
  exact card_center_dvd_griess_perfect hperf θ

theorem cover_exact {S U R : Type} [Group S] [Finite S] [Group U] [Finite U] [Group R]
    (hS : CFSG.Open.IsQuasisimple S) (hSodd : Odd (Nat.card (Subgroup.center S)))
    (hU : Group.IsPerfect U) (π : U →* R) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center U) (hkodd : Odd (Nat.card π.ker))
    (hR : Subgroup.center R = ⊥) (θ : S ⧸ Subgroup.center S ≃* R)
    [Finite (CFSG.Open.griessHopfMultiplier R)] {k : ℕ}
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier R) ∣ Nat.card π.ker * 2 ^ k) :
    ∃ ψ : U →* S, ∀ u : U, θ (QuotientGroup.mk (ψ u)) = π u := by
  have hperf : Group.IsPerfect S := ⟨hS.1⟩
  exact cover_exact_aux hperf hSodd hU π hπ hker hkodd hR θ hM

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
