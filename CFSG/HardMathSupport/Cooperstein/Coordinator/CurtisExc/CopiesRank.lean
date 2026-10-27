module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringWts

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

theorem finrank_range_sub_one_ge_of_map_le {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] {m : ℕ} (C : Fin m → Submodule k V) (hC : iSupIndep C)
    (A : V →ₗ[k] V) (π : Fin m → Fin m) (hA : ∀ i, ∀ c ∈ C i, A c ∈ C (π i))
    (R : Finset (Fin m)) (hR : ∀ i ∈ R, π i ∉ R) :
    ∑ i ∈ R, Module.finrank k (C i) ≤ Module.finrank k (LinearMap.range (A - 1)) := by
  classical
  set D : Submodule k V := R.sup C with hD
  set E : Submodule k V := (R.image π).sup C with hE
  have hsup : (R ∪ R.image π).SupIndep C := hC.supIndep' _
  have hdisjR : Disjoint R (R.image π) := by
    rw [Finset.disjoint_left]
    intro x hxR hxim
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxim
    rw [← hix] at hxR
    exact hR i hi hxR
  have hdisj : Disjoint D E :=
    hsup.disjoint_sup_sup (Finset.subset_union_left) (Finset.subset_union_right) hdisjR
  have hmap : D.map A ≤ E := by
    rw [Submodule.map_le_iff_le_comap, hD, hE]
    refine Finset.sup_le_iff.mpr fun i hi => ?_
    exact fun c hc => Finset.le_sup (f := C) (Finset.mem_image.mpr ⟨i, hi, rfl⟩) (hA i c hc)
  have hRind : iSupIndep fun i : R => C i := hC.comp Subtype.val_injective
  have hsum : Module.finrank k D = ∑ i ∈ R, Module.finrank k (C i) := by
    have h1 : D = ⨆ i : R, C i := by
      rw [hD, Finset.sup_eq_iSup]
      exact iSup_subtype' (p := fun i => i ∈ R) (f := fun i _ => C i)
    have h2 : Module.finrank k ↥(⨆ i : R, (C i : Submodule k V)) =
        ∑ i : R, Module.finrank k (C i) :=
      TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hRind
    rw [h1, h2]
    exact Finset.sum_coe_sort R (fun i => Module.finrank k (C i))
  have hker : LinearMap.ker ((A - 1).comp D.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hAx : A (x : V) = x := by
      change A (x : V) - (x : V) = 0 at hx
      exact sub_eq_zero.mp hx
    have hxD : (x : V) ∈ D := x.2
    have hxE : (x : V) ∈ E := by
      have hm := hmap (Submodule.mem_map_of_mem hxD)
      rwa [hAx] at hm
    have hbot : (x : V) ∈ (⊥ : Submodule k V) := hdisj.le_bot ⟨hxD, hxE⟩
    apply Subtype.ext
    simpa using hbot
  have hfin : Module.finrank k D =
      Module.finrank k (LinearMap.range ((A - 1).comp D.subtype)) := by
    have h := LinearMap.finrank_range_add_finrank_ker ((A - 1).comp D.subtype)
    rw [hker, finrank_bot, add_zero] at h
    exact h.symm
  have hrange : LinearMap.range ((A - 1).comp D.subtype) ≤ LinearMap.range (A - 1) := by
    rintro y ⟨x, rfl⟩
    exact ⟨(x : V), rfl⟩
  calc ∑ i ∈ R, Module.finrank k (C i) = Module.finrank k D := hsum.symm
    _ = Module.finrank k (LinearMap.range ((A - 1).comp D.subtype)) := hfin
    _ ≤ Module.finrank k (LinearMap.range (A - 1)) := Submodule.finrank_mono hrange

section Chev


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem torus_conj_rankOne (s : Fin τ.rank) {h : adjointGroup τ K}
    (hh : h ∈ (chevDatum τ K 2 hw).H) (g : SL(2, K)) :
    ∃ g' : SL(2, K), h * rankOne τ K s g * h⁻¹ = rankOne τ K s g' := by
  have hfwd : ∀ (i : Fin τ.rank) (t : Kˣ) (x : SL(2, K)), ∃ x' : SL(2, K),
      dC τ K i t * rankOne τ K s x * (dC τ K i t)⁻¹ = rankOne τ K s x' := by
    intro i t x
    obtain ⟨z, hz⟩ := exists_sq_unit (t ^ τ.cartan i s)
    refine ⟨dElt z * x * (dElt z)⁻¹, ?_⟩
    rw [conj_rankOne_eq i s t z hz x, ← rankOne_d]
    conv_lhs => rw [← map_mul, ← map_inv, ← map_mul]
  let R : Subgroup (adjointGroup τ K) := (rankOne τ K s).range
  have hgen : ∀ p : Fin τ.rank × Kˣ,
      dC τ K p.1 p.2 ∈ Subgroup.normalizer (R : Set (adjointGroup τ K)) := by
    intro p
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := hfwd p.1 p.2 x
      exact MonoidHom.mem_range.mpr ⟨x', hx'.symm⟩
    · intro hx
      obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨x'', hx''⟩ := hfwd p.1 p.2⁻¹ x'
      refine MonoidHom.mem_range.mpr ⟨x'', ?_⟩
      calc rankOne τ K s x'' =
            dC τ K p.1 p.2⁻¹ * rankOne τ K s x' * (dC τ K p.1 p.2⁻¹)⁻¹ := hx''.symm
        _ = dC τ K p.1 p.2⁻¹ * (dC τ K p.1 p.2 * x * (dC τ K p.1 p.2)⁻¹) *
              (dC τ K p.1 p.2⁻¹)⁻¹ := by rw [hx']
        _ = x := by
          simp only [dC_inv, inv_inv]
          have h1 : dC τ K p.1 p.2⁻¹ * dC τ K p.1 p.2 = 1 := by
            rw [← dC_mul, inv_mul_cancel, dC_one]
          calc dC τ K p.1 p.2⁻¹ * (dC τ K p.1 p.2 * x * dC τ K p.1 p.2⁻¹) *
                dC τ K p.1 p.2
              = (dC τ K p.1 p.2⁻¹ * dC τ K p.1 p.2) * x *
                (dC τ K p.1 p.2⁻¹ * dC τ K p.1 p.2) := by group
            _ = x := by rw [h1, one_mul, mul_one]
  let Hgrp : Subgroup (adjointGroup τ K) :=
    Subgroup.closure (Set.range fun p : Fin τ.rank × Kˣ => dC τ K p.1 p.2)
  have hmap : Hgrp.map (adjointGroup τ K).subtype = torusGroup τ K := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro _ ⟨p, rfl⟩
      exact Subgroup.subset_closure ⟨p, rfl⟩
    · change Subgroup.closure (Set.range fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ≤
        Hgrp.map (adjointGroup τ K).subtype
      rw [Subgroup.closure_le]
      rintro _ ⟨p, rfl⟩
      exact Subgroup.mem_map.mpr ⟨dC τ K p.1 p.2, Subgroup.subset_closure ⟨p, rfl⟩, rfl⟩
  have hH : h ∈ Hgrp := by
    have hval : (h : ModGL τ K) ∈ Hgrp.map (adjointGroup τ K).subtype := by
      rw [hmap]
      exact Subgroup.mem_subgroupOf.mp hh
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hval
    have hxh : x = h := Subtype.ext hxe
    rwa [hxh] at hx
  have hle : Hgrp ≤ Subgroup.normalizer (R : Set (adjointGroup τ K)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact hgen p
  have hN : h ∈ Subgroup.normalizer (R : Set (adjointGroup τ K)) := hle hH
  have hconj := (Subgroup.mem_normalizer_iff.mp hN) (rankOne τ K s g)
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp (hconj.mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
  exact ⟨g', hg'.symm⟩

private theorem torus_stable_orbitSpan {ρ : Representation k (adjointGroup τ K) V}
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} {h : adjointGroup τ K}
    (hh : h ∈ (chevDatum τ K 2 hw).H) {w : V}
    (hworbit : w ∈ orbitSpan (ρ.comp (rankOne τ K s)) y) :
    ρ h w ∈ orbitSpan (ρ.comp (rankOne τ K s)) y := by
  classical
  set σ := ρ.comp (rankOne τ K s) with hσ
  have hhy : ρ h y = χ h • y := ht.2.2.1 h hh
  have hgen : ∀ g : SL(2, K), ρ h (σ g y) ∈ orbitSpan σ y := by
    intro g
    obtain ⟨g', hg'⟩ := torus_conj_rankOne (hw := hw) s hh g
    have hkey : h * rankOne τ K s g = rankOne τ K s g' * h := by
      rw [← hg']
      group
    have h1 : ρ h (σ g y) = σ g' (ρ h y) := by
      show ρ h (ρ (rankOne τ K s g) y) = ρ (rankOne τ K s g') (ρ h y)
      rw [act_mul, act_mul, hkey]
    rw [h1, hhy, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g', rfl⟩)
  have hle : (orbitSpan σ y).map (ρ h) ≤ orbitSpan σ y := by
    rw [orbitSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact hgen g
  exact hle (Submodule.mem_map_of_mem hworbit)

private theorem iSupIndep_copies_orbit [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} {m : ℕ}
    (u : Fin m → WeylGroup τ)
    (hu : ∀ i, u i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) :
    iSupIndep fun i => orbitSpan (ρ.comp (rankOne τ K s)) (ρ (nWC τ K (u i)) y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := ρ.comp (rankOne τ K s) with hσ
  set D := chevDatum τ K 2 hw with hD
  obtain ⟨hxN, hyN⟩ := Us_normalized (hw := hw) (K := K) s
  set v : Fin m → V := fun i => ρ (nWC τ K (u i)) y with hv
  have hcomm : ∀ i (g' : SL(2, K)) (w : V), σ g' (ρ (nWC τ K (u i)) w) =
      ρ (nWC τ K (u i)) (σ g' w) := by
    intro i g' w
    show ρ (rankOne τ K s g') (ρ (nWC τ K (u i)) w) = ρ (nWC τ K (u i)) (ρ (rankOne τ K s g') w)
    rw [act_mul, act_mul, ← nWC_commute_rankOne hw (u i) s (hu i) g']
  set Fix : Fin m → Submodule k V := fun i =>
    (fixSub ρ (D.Us s)).map (ρ (nWC τ K (u i))) with hFix
  have hyFix : y ∈ fixSub ρ (D.Us s) := fun q hq => ht.1 q (D.Us_le s hq)
  have hyu : ∀ c : K, σ (uElt c) y = y := by
    intro c
    show ρ (rankOne τ K s (uElt c)) y = y
    rw [rankOne_u]
    exact ht.1 _ (D.X_le s (xC_mem_X s c))
  have hmap_inj : ∀ i, Function.Injective (ρ (nWC τ K (u i))) :=
    fun i => (repEquiv ρ (nWC τ K (u i))).injective
  have hres := finrank_iSup_orbitSpan σ v Fix
    (fun i => Submodule.mem_map_of_mem hyFix)
    (by
      rintro i g' _ ⟨f, hf, rfl⟩
      rw [hcomm]
      exact Submodule.mem_map_of_mem (fixSub_stable_rankOne ρ s (D.Us s) hxN hyN g' hf))
    (by
      rintro i _ ⟨f0, hf0, rfl⟩ hfu
      have h1 : ∀ c : K, ρ (xC τ K s c) f0 = f0 := by
        intro c
        have := hfu c
        rw [hcomm] at this
        have h2 : σ (uElt c) f0 = f0 := hmap_inj i this
        have h3 : ρ (rankOne τ K s (uElt c)) f0 = f0 := h2
        rw [rankOne_u] at h3
        exact h3
      obtain ⟨c, hc⟩ := fix_of_highest hρ ht s hf0 h1
      exact ⟨c, by rw [hc, map_smul]⟩)
    (fun i c => by rw [hcomm, hyu c])
    Finset.univ (hli.comp (fun x : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) => (x : Fin m))
      Subtype.val_injective)
  obtain ⟨-, -, hsup⟩ := hres
  exact Finset.SupIndep.iSupIndep_of_univ hsup

theorem copies_rank_le [Module.Finite k V] {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} {m : ℕ} (u : Fin m → WeylGroup τ)
    (hu : ∀ i, u i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) (b : adjointGroup τ K)
    (π : Fin m → Fin m)
    (hb : ∀ i, ∃ h ∈ (chevDatum τ K 2 hw).H, b * nWC τ K (u i) = nWC τ K (u (π i)) * h)
    (R : Finset (Fin m)) (hR : ∀ i ∈ R, π i ∉ R) :
    R.card * Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) ≤
      Module.finrank k (LinearMap.range (ρ b - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := ρ.comp (rankOne τ K s) with hσ
  set v : Fin m → V := fun i => ρ (nWC τ K (u i)) y with hv
  have hind : iSupIndep fun i => orbitSpan σ (v i) :=
    iSupIndep_copies_orbit (hw := hw) hρ ht u hu hli
  have hcomm : ∀ i (g' : SL(2, K)) (w : V), σ g' (ρ (nWC τ K (u i)) w) =
      ρ (nWC τ K (u i)) (σ g' w) := by
    intro i g' w
    show ρ (rankOne τ K s g') (ρ (nWC τ K (u i)) w) = ρ (nWC τ K (u i)) (ρ (rankOne τ K s g') w)
    rw [act_mul, act_mul, ← nWC_commute_rankOne hw (u i) s (hu i) g']
  have hCmap : ∀ i, orbitSpan σ (v i) = (orbitSpan σ y).map (ρ (nWC τ K (u i))) := by
    intro i
    rw [orbitSpan, orbitSpan, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext w
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g', (hcomm i g' y).symm⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g', hcomm i g' y⟩
  have hdimC : ∀ i, Module.finrank k (orbitSpan σ (v i)) =
      Module.finrank k (orbitSpan σ y) := by
    intro i
    rw [hCmap i]
    exact (repEquiv ρ (nWC τ K (u i))).finrank_map_eq _
  have hmapC : ∀ i, ∀ c ∈ orbitSpan σ (v i), ρ b c ∈ orbitSpan σ (v (π i)) := by
    intro i c hc
    rw [hCmap i] at hc
    obtain ⟨w, hw, rfl⟩ := hc
    rw [hCmap (π i)]
    obtain ⟨h, hh, hbh⟩ := hb i
    refine Submodule.mem_map.mpr ⟨ρ h w, torus_stable_orbitSpan (s := s) ht hh hw, ?_⟩
    simp only [act_mul, hbh]
  have hle := finrank_range_sub_one_ge_of_map_le (fun i => orbitSpan σ (v i)) hind (ρ b) π
    hmapC R hR
  have hsumC : ∑ i ∈ R, Module.finrank k (orbitSpan σ (v i)) =
      R.card * Module.finrank k (orbitSpan σ y) := by
    rw [Finset.sum_congr rfl fun i _ => hdimC i, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [← hsumC]
  exact hle

theorem copies_rank_two_pow [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    {s : Fin τ.rank} (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC τ K s z) ^ (2 ^ g) = χ (dC τ K s z)) {m : ℕ}
    (u : Fin m → WeylGroup τ)
    (hu : ∀ i, u i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) (b : adjointGroup τ K)
    (π : Fin m → Fin m)
    (hb : ∀ i, ∃ h ∈ (chevDatum τ K 2 hw).H, b * nWC τ K (u i) = nWC τ K (u (π i)) * h)
    (R : Finset (Fin m)) (hR : ∀ i ∈ R, π i ∉ R) :
    R.card * 2 ^ (n / g) ≤ Module.finrank k (LinearMap.range (ρ b - 1)) :=
  calc R.card * 2 ^ (n / g) ≤
        R.card * Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) :=
        Nat.mul_le_mul_left _ (two_pow_le_finrank_orbitSpan hn hK hρ ht hs hg hgn hper)
    _ ≤ Module.finrank k (LinearMap.range (ρ b - 1)) :=
        copies_rank_le hρ ht u hu hli b π hb R hR

end Chev

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
