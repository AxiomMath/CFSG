module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeInter

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section TypeFree

variable {N : Type} [Group N] [Finite N]

theorem perfect_le_oddCoreLift_of_fieldComponent {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    (hschurF : ∀ (X : Type) [Group X], LieModel X .PSL 4 2 2 → OddSchurTrivial X)
    {Kc : Subgroup (N ⧸ oddCore N)} (hKc : IsComponent Kc) (hKZ : center Kc = ⊥)
    (hsN : QuotientGroup.mk' (oddCore N) s ∈ normalizer (Kc : Set (N ⧸ oddCore N)))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hKm : LieModel Kc .PSL 4 2 2) (hLK : Lb ≤ oddCoreLift Kc) {P : Subgroup N}
    (hP : ⁅P, P⁆ = P) : P ≤ oddCoreLift Kc := by
  set π := QuotientGroup.mk' (oddCore N) with hπ
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsC : π s ∉ centralizer (Kc : Set (N ⧸ oddCore N)) := by
    intro hc
    apply hout
    have h1 : (⟨_, hsN⟩ : normalizer (Kc : Set (N ⧸ oddCore N))) ∈
        Kc.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hc
    exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
  obtain ⟨hcomp, -, hmap, hsNs, ⟨ι⟩, -⟩ :=
    exists_lift_field_of_le_sup hs hLs hLq hLZ hCs hschurF hKc hsN hsC hKm
  set Ks := oddCoreLift Kc with hKsdef
  have hKsZ : center Ks = ⊥ := F4Pilot.center_eq_bot_congr ι.symm hKZ
  set C := centralizer (Ks : Set N) with hCdef
  have hsCN : s ∈ normalizer (C : Set N) := by
    rw [mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [mem_centralizer_iff] at hc ⊢
      intro k hk
      have hk' : s⁻¹ * k * s ∈ Ks := by
        have h1 := (mem_normalizer_iff.1 (inv_mem hsNs) k).1 hk
        rwa [inv_inv] at h1
      have h2 := hc _ hk'
      calc k * (s * c * s⁻¹) = s * ((s⁻¹ * k * s) * c) * s⁻¹ := by group
        _ = s * (c * (s⁻¹ * k * s)) * s⁻¹ := by rw [h2]
        _ = s * c * s⁻¹ * k := by group
    · intro hc
      rw [mem_centralizer_iff] at hc ⊢
      intro k hk
      have hk' : s * k * s⁻¹ ∈ Ks := (mem_normalizer_iff.1 hsNs k).1 hk
      have h2 := hc _ hk'
      calc k * c = s⁻¹ * ((s * k * s⁻¹) * (s * c * s⁻¹)) * s := by group
        _ = s⁻¹ * ((s * c * s⁻¹) * (s * k * s⁻¹)) * s := by rw [h2]
        _ = c * k := by group
  have hfix : ∀ c ∈ C, c * s = s * c → c = 1 := by
    intro c hcC hcs
    have hcCs : c ∈ centralizer ({s} : Set N) := mem_centralizer_singleton_iff.2 hcs
    rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs hcCs with h | h
    · have hz : (⟨c, hLK h⟩ : Ks) ∈ center Ks := by
        rw [Subgroup.mem_center_iff]
        intro k
        exact Subtype.ext ((mem_centralizer_iff.1 hcC) k k.2)
      rw [hKsZ] at hz
      exact congrArg Subtype.val ((Subgroup.mem_bot).1 hz)
    · exfalso
      apply hout
      have hkK : π (c * s) ∈ Kc := by
        rw [← hmap]
        exact mem_map_of_mem _ (hLK h)
      refine ⟨⟨π (c * s), hkK⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
      have hcy : π c * (y : N ⧸ oddCore N) = y * π c := by
        have hy : (y : N ⧸ oddCore N) ∈ Ks.map π := by
          rw [hπ, hmap]
          exact y.2
        obtain ⟨k, hk, hky⟩ := hy
        rw [← hky, ← map_mul, ← map_mul, (mem_centralizer_iff.1 hcC) k hk]
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        F4Pilot.coe_normalizerMonoidHom_mk_apply Kc hsN]
      change π (c * s) * (y : N ⧸ oddCore N) * (π (c * s))⁻¹ =
        π s * (y : N ⧸ oddCore N) * (π s)⁻¹
      rw [map_mul]
      calc π c * π s * (y : N ⧸ oddCore N) * (π c * π s)⁻¹ =
            π c * (π s * (y : N ⧸ oddCore N) * (π s)⁻¹) * (π c)⁻¹ := by group
        _ = π s * (y : N ⧸ oddCore N) * (π s)⁻¹ := by
          have hy' : π s * (y : N ⧸ oddCore N) * (π s)⁻¹ ∈ Kc :=
            (mem_normalizer_iff.1 hsN y).1 y.2
          have hc' : π c * (π s * (y : N ⧸ oddCore N) * (π s)⁻¹) =
              (π s * (y : N ⧸ oddCore N) * (π s)⁻¹) * π c := by
            have hy'' : π s * (y : N ⧸ oddCore N) * (π s)⁻¹ ∈ Ks.map π := by
              rw [hπ, hmap]
              exact hy'
            obtain ⟨k, hk, hky⟩ := hy''
            rw [← hky, ← map_mul, ← map_mul, (mem_centralizer_iff.1 hcC) k hk]
          rw [hc', mul_inv_cancel_right]
  set φ : C →* C := (C.normalizerMonoidHom ⟨s, hsCN⟩ : MulAut C).toMonoidHom with hφdef
  have hφapp : ∀ x : C, ((φ x : C) : N) = s * x * s⁻¹ :=
    F4Pilot.coe_normalizerMonoidHom_mk_apply C hsCN
  have hfpf : MonoidHom.FixedPointFree φ := by
    intro x hx
    apply Subtype.ext
    have h1 := congrArg Subtype.val hx
    rw [hφapp] at h1
    have h2 : (x : N) * s = s * x := by
      calc (x : N) * s = s * x * s⁻¹ * s := by rw [h1]
        _ = s * x := by group
    exact hfix x x.2 h2
  have hinv : Function.Involutive φ := by
    intro x
    apply Subtype.ext
    rw [hφapp, hφapp]
    calc s * (s * (x : N) * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
      _ = x := by rw [hs2]; group
  have hCcomm : ∀ x y : C, x * y = y * x := fun x y =>
    MonoidHom.FixedPointFree.commute_all_of_involutive hfpf hinv x y
  have hKsN : (⊤ : Subgroup N) ≤ normalizer (Ks : Set N) := by
    intro m _
    rw [mem_normalizer_iff_map_conj_eq]
    rcases CFSG.LocalCores.distinct_components_commute
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m) hcomp) hcomp with h | h
    · exact h
    · exfalso
      set J := Ks.map (MulAut.conj m).toMonoidHom with hJ
      have hJC : J ≤ C := commutator_eq_bot_iff_le_centralizer.mp h
      have hJp : ⁅J, J⁆ = J :=
        isPerfect_iff.mp (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m) hcomp).1.1
      have hJbot : ⁅J, J⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        have hab := hCcomm ⟨a, hJC ha⟩ ⟨b, hJC hb⟩
        have hab' : a * b = b * a := congrArg Subtype.val hab
        rw [mem_bot, commutatorElement_def, hab']
        group
      have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial
        (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m) hcomp).1
      exact (Subgroup.nontrivial_iff_ne_bot _).1 this (hJp.symm.trans hJbot)
  obtain ⟨F, _, _, -, ⟨ψ₀⟩⟩ := exists_projectiveSL_equiv_of_lieModel_PSL hKm
  have hOut : Group.IsSolvable (Outer Ks) := isSolvable_outer_of_mulEquiv (by norm_num) (ι.trans ψ₀)
  have hCsolv : Group.IsSolvable (C ⊓ ⊤ : Subgroup N) := by
    rw [inf_top_eq]
    let _ : CommGroup C := { (inferInstance : Group C) with mul_comm := hCcomm }
    infer_instance
  exact CFSG.SeitzReduction.perfect_le_of_isSolvable_outer hOut le_top hKsN hCsolv hP le_top

end TypeFree

theorem lFiveLeviXTildeInput_holds :
    LFiveLeviXTildeInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ d _
  set N := normalizer (W₁ : Set G) with hNdef
  set ν := QuotientGroup.mk' (W₁.subgroupOf N) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set s := ν ⟨t, htN⟩ with hsdef
  set Lb := (L₁.subgroupOf N).map ν with hLbdef
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hLq, hLZ, -, -, hLs⟩ := leviBar_facts e hK htC hW₁c hLN htN
  have hs : orderOf s = 2 := orderOf_mk_wOne_eq_two e hK ht hW₁c hW₁2 hW₁t htN
  have hCs := centralizer_bar_le_sup e hK ht hW₁c hW₁2 hW₁t htN hLN
    (lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c)
  obtain ⟨hKc, hLKc, -, -, hKZ, hmodel, hsN, hout⟩ := hfield
  have hLp : ⁅Lb, Lb⁆ = Lb := isPerfect_iff.mp ⟨hLq.1⟩
  have hLK : Lb ≤ oddCoreLift Kc := by
    refine F4Pilot.le_oddCoreLift_of_perfect hLp ?_
    have h1 := hLKc.le
    rw [seitzLeviHat_eq_map_map] at h1
    exact h1
  set X := seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom) with hXdef
  have hXN : X ≤ N := seitzLeviX_le_normalizer_left _ _
  have hXp : ⁅X, X⁆ = X := CFSG.Quasithin.perfectCore_perfect _
  have hXb : ⁅(X.subgroupOf N).map ν, (X.subgroupOf N).map ν⁆ = (X.subgroupOf N).map ν := by
    rw [← Subgroup.map_commutator, CFSG.SeitzReduction.commutator_subgroupOf_eq_self hXN hXp]
  have hle := perfect_le_oddCoreLift_of_fieldComponent hs hLs hLq hLZ hCs
    (fun X _ hX => oddSchurTrivial_of_lieModel_PSL_four_four hX) hKc hKZ hsN hout hmodel hLK hXb
  intro x hx
  exact mem_seitzTilde_iff.2 ⟨hXN hx, hle ⟨⟨x, hXN hx⟩, mem_subgroupOf.2 hx, rfl⟩⟩

theorem lFiveGraphLeviInput_of_fieldModule_of_leviNorm
    (h : LFiveWOneFieldModuleInput)
    (h₃ : LFiveGraphLeviNormInput) : LFiveGraphLeviInput :=
  lFiveGraphLeviInput_of_fieldModule h lFiveLeviXTildeInput_holds lFiveGraphWInterInput_holds h₃

end CFSG.SeitzReduction.LinearPilot
