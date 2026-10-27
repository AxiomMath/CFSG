module

public import CFSG.LieType.Steinberg.CurtisDatum.RankOne
public import CFSG.Quasithin.Background.SmithCurtisHecke

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.Quasithin.SmithCurtis
open scoped commutatorElement Pointwise

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

section Elementary

omit [Finite K] in
theorem inv_conj_n_mem_posUnipotentExcept (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (i : Fin D.rank) {u : K}
    (hu : u ∈ posUnipotentExcept D i) : (n i)⁻¹ * u * n i ∈ posUnipotentExcept D i := by
  have hsq : (n i * n i)⁻¹ ∈ ⨆ j, H j :=
    inv_mem (by rw [← pow_two]; exact le_iSup H i (hct.sq_mem i))
  have hTnorm : (⨆ j, H j) ≤
      Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
    le_normalizer_iSup₂ fun h hh γ hγ y hy =>
      Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ
        ((Subgroup.mem_normalizer_iff.mp (iSup_le_normalizer_rootGroup hct hγ.1.1 hh) y).mp hy))
  have e : (n i)⁻¹ * u * n i =
      (n i * n i)⁻¹ * (n i * u * (n i)⁻¹) * ((n i * n i)⁻¹)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hTnorm hsq)
    (n i * u * (n i)⁻¹)).mp (conj_n_mem_posUnipotentExcept hct i hu)

omit [Finite K] in
theorem nrep_inv_conj_mem_posUnipotent (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    {w : W} {i : Fin D.rank}
    (hw : ¬ (cs).IsLeftDescent w i) {x : K} (hx : x ∈ D.rootGroup (Pi.single i 1)) :
    (nrep hct w)⁻¹ * x * nrep hct w ∈ posUnipotent D :=
  rootGroup_le_posUnipotent (weylAction_mem_roots _ _ ((Φ).single_mem i))
    (ht_weylAction_inv_single_pos hw)
    (nrep_inv_conj_mem hct w ((Φ).single_mem i) hx)

omit [Finite K] in
theorem n_mul_posUnipotent_mul_nrep_subset (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {w : W} {i : Fin D.rank}
    (hw : ¬ (cs).IsLeftDescent w i) :
    ∀ u ∈ posUnipotent D, ∃ v ∈ posUnipotentExcept D i, ∃ u' ∈ posUnipotent D,
      n i * u * nrep hct w = v * n i * nrep hct w * u' := by
  intro u hu
  have hu' : u ∈ (posUnipotent D : Set K) := hu
  rw [coe_posUnipotent_eq_mul_rootGroup hext i] at hu'
  obtain ⟨v, hv, x, hx, rfl⟩ := hu'
  refine ⟨n i * v * (n i)⁻¹, conj_n_mem_posUnipotentExcept hct i hv,
    (nrep hct w)⁻¹ * x * nrep hct w, nrep_inv_conj_mem_posUnipotent hct hw hx, ?_⟩
  group

theorem mem_dcos_mul_simple (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {w : W} {i : Fin D.rank} (hw : ¬ (cs).IsLeftDescent w i)
    {x : K} (hx : x ∈ D.rootGroup (Pi.single i 1)) {u : K} (hu : u ∈ posUnipotent D) :
    ((x * n i * u * nrep hct w : K) : K ⧸ posUnipotent D) ∈
      dcos (posUnipotent D) (n i * nrep hct w) := by
  obtain ⟨v, hv, u', hu', he⟩ := n_mul_posUnipotent_mul_nrep_subset hct hext hw u hu
  have hxU : x * v ∈ (posUnipotent D : Set K) := by
    rw [coe_posUnipotent_eq_rootGroup_mul hext i]
    exact Set.mul_mem_mul hx hv
  refine mem_dcos.mpr ⟨x * v, hxU, ?_⟩
  have hmain : x * n i * u * nrep hct w = x * (v * n i * nrep hct w * u') := by
    calc x * n i * u * nrep hct w = x * (n i * u * nrep hct w) := by group
      _ = x * (v * n i * nrep hct w * u') := by rw [he]
  rw [hmain, QuotientGroup.eq]
  have e : (x * (v * n i * nrep hct w * u'))⁻¹ * (x * v * (n i * nrep hct w)) =
      (u')⁻¹ := by group
  rw [e]
  exact inv_mem hu'

theorem mem_dcos_mul_of_mem_dcos (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {w : W} {i : Fin D.rank} (hw : ¬ (cs).IsLeftDescent w i)
    {x : K} (hx : x ∈ D.rootGroup (Pi.single i 1))
    {c : K ⧸ posUnipotent D} (hc : c ∈ dcos (posUnipotent D) (nrep hct w)) :
    ((x * n i * c.out : K) : K ⧸ posUnipotent D) ∈
      dcos (posUnipotent D) (n i * nrep hct w) := by
  obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hc
  obtain ⟨k, hout⟩ := QuotientGroup.mk_out_eq_mul (posUnipotent D)
    (u * nrep hct w)
  rw [hout]
  have hq : ((x * n i * (u * nrep hct w * (k : K)) : K) : K ⧸ posUnipotent D) =
      ((x * n i * u * nrep hct w : K) : K ⧸ posUnipotent D) := by
    rw [QuotientGroup.eq]
    have e : (x * n i * (u * nrep hct w * (k : K)))⁻¹ *
        (x * n i * u * nrep hct w) = (k : K)⁻¹ := by group
    rw [e]
    exact inv_mem k.2
  rw [hq]
  exact mem_dcos_mul_simple hct hext hw hx hu

omit [Finite K] in
theorem borel_mul_simple_mul_borel (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {w : W} {i : Fin D.rank}
    (hw : ¬ (cs).IsLeftDescent w i) {b₁ b₂ : K} (hb₁ : b₁ ∈ borel D H)
    (hb₂ : b₂ ∈ borel D H) :
    b₁ * n i * b₂ * nrep hct w ∈ bruhatCell hct ((cs).simple i * w) := by
  obtain ⟨b', hb', x, hx, he⟩ := exists_n_mul_mul_nrep hct hext hw hb₂
  have hxU : x ∈ posUnipotent D :=
    rootGroup_le_posUnipotent (weylAction_mem_roots _ _ ((Φ).single_mem i))
      (ht_weylAction_inv_single_pos hw) hx
  refine ⟨b₁ * b', mul_mem hb₁ hb', x, posUnipotent_le_borel hxU, ?_⟩
  calc b₁ * n i * b₂ * nrep hct w = b₁ * (n i * b₂ * nrep hct w) := by group
    _ = b₁ * (b' * nrep hct ((cs).simple i * w) * x) := by rw [he]
    _ = b₁ * b' * nrep hct ((cs).simple i * w) * x := by group

end Elementary

section Degrees

theorem heckeDeg_n (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    heckeDeg (posUnipotent D) (n i) = Nat.card (D.rootGroup (Pi.single i 1)) := by
  classical
  let U := posUnipotent D
  let X := D.rootGroup (Pi.single i 1)
  have : Fintype X := Fintype.ofFinite X
  let f : X → K ⧸ U := fun x => ((x : K) * n i : K ⧸ U)
  have hf_mem : ∀ x : X, f x ∈ dcos U (n i) := fun x =>
    mem_dcos.mpr ⟨x, rootGroup_le_posUnipotent ((Φ).single_mem i) (ht_single_pos i) x.2, rfl⟩
  have hf_inj : Function.Injective f := by
    intro x x' h
    have hx : ((x : K) * n i : K ⧸ U) = ((x' : K) * n i : K ⧸ U) := h
    rw [QuotientGroup.eq] at hx
    have hmemU : (n i)⁻¹ * ((x : K)⁻¹ * x') * n i ∈ U := by
      have e : ((x : K) * n i)⁻¹ * ((x' : K) * n i) =
          (n i)⁻¹ * ((x : K)⁻¹ * x') * n i := by group
      rwa [e] at hx
    have hmemL : (n i)⁻¹ * ((x : K)⁻¹ * x') * n i ∈ negUnipotent D :=
      rootGroup_le_negUnipotent ((Φ).neg_mem _ ((Φ).single_mem i))
        (by rw [ht_neg, ht_single]; norm_num)
        (inv_conj_n_mem_rootGroup_neg hct i (mul_mem (inv_mem x.2) x'.2))
    have hone : (n i)⁻¹ * ((x : K)⁻¹ * x') * n i = 1 := by
      have hmem := Subgroup.mem_inf.2 ⟨hmemU, hmemL⟩
      rw [posUnipotent_inf_negUnipotent hext, Subgroup.mem_bot] at hmem
      exact hmem
    have hz : (x : K)⁻¹ * x' = 1 := by
      have h' : (n i)⁻¹ * ((x : K)⁻¹ * x') * n i = (n i)⁻¹ * 1 * n i := by
        rw [hone]; group
      exact mul_left_cancel (mul_right_cancel h')
    exact Subtype.ext (inv_mul_eq_one.1 hz)
  have hf_surj : ∀ c ∈ dcos U (n i), ∃ x : X, f x = c := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hc
    have hu' : u ∈ (X : Set K) * (posUnipotentExcept D i : Set K) := by
      have hu'' : u ∈ (posUnipotent D : Set K) := hu
      rw [coe_posUnipotent_eq_rootGroup_mul hext i] at hu''
      exact hu''
    obtain ⟨x, hx, v, hv, rfl⟩ := hu'
    refine ⟨⟨x, hx⟩, ?_⟩
    show ((x * n i : K) : K ⧸ U) = ((x * v) * n i : K ⧸ U)
    rw [QuotientGroup.eq]
    have hv' : (n i)⁻¹ * v * n i ∈ posUnipotentExcept D i :=
      inv_conj_n_mem_posUnipotentExcept hct i hv
    have hvU : (n i)⁻¹ * v * n i ∈ U :=
      posUnipotentExcept_le_posUnipotent i hv'
    have e2 : (x * n i)⁻¹ * (x * v * n i) = (n i)⁻¹ * v * n i := by group
    rw [e2]
    exact hvU
  have himage : (Finset.univ.image f) = dcos U (n i) := by
    ext c
    constructor
    · intro hc
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
      exact hf_mem x
    · intro hc
      obtain ⟨x, rfl⟩ := hf_surj c hc
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hcard : (dcos U (n i)).card = Nat.card X := by
    rw [← himage, Finset.card_image_of_injective _ hf_inj, Finset.card_univ,
      Nat.card_eq_fintype_card]
  change heckeDeg U (n i) = Nat.card X
  rw [← card_dcos U (n i), hcard]

theorem heckeDeg_n_mul_nrep (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (w : W) (i : Fin D.rank)
    (h : (cs).length ((cs).simple i * w) = (cs).length w + 1) :
    heckeDeg (posUnipotent D) (n i) * heckeDeg (posUnipotent D) (nrep hct w) =
      heckeDeg (posUnipotent D) (nrep hct ((cs).simple i * w)) := by
  classical
  have hw : ¬ (cs).IsLeftDescent w i := (cs).not_isLeftDescent_iff.2 h
  let U := posUnipotent D
  let X := D.rootGroup (Pi.single i 1)
  have : Fintype X := Fintype.ofFinite X
  let S : Finset (X × (K ⧸ U)) :=
    (Finset.univ : Finset X).product (dcos U (nrep hct w))
  let F : X × (K ⧸ U) → K ⧸ U := fun p =>
    ((p.1.1 * n i * p.2.out : K) : K ⧸ U)
  have hFmem : ∀ p ∈ S, F p ∈ dcos U (n i * nrep hct w) := by
    rintro ⟨x, c⟩ hp
    have hpS : (x, c) ∈ Finset.univ.product (dcos U (nrep hct w)) := hp
    have hp' : c ∈ dcos U (nrep hct w) := (Finset.mem_product.mp hpS).2
    exact mem_dcos_mul_of_mem_dcos hct hext hw (x := (x : K)) x.2 hp'
  have hFsurj : ∀ c ∈ dcos U (n i * nrep hct w), ∃ p ∈ S, F p = c := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hc
    have hu' : u ∈ (X : Set K) * (posUnipotentExcept D i : Set K) := by
      have hu'' : u ∈ (posUnipotent D : Set K) := hu
      rw [coe_posUnipotent_eq_rootGroup_mul hext i] at hu''
      exact hu''
    obtain ⟨x, hx, v, hv, rfl⟩ := hu'
    have hv' : (n i)⁻¹ * v * n i ∈ posUnipotentExcept D i :=
      inv_conj_n_mem_posUnipotentExcept hct i hv
    have hvU : (n i)⁻¹ * v * n i ∈ U :=
      posUnipotentExcept_le_posUnipotent i hv'
    let c₀ : K ⧸ U := (((n i)⁻¹ * v * n i) * nrep hct w : K)
    have hc₀ : c₀ ∈ dcos U (nrep hct w) :=
      mem_dcos.mpr ⟨(n i)⁻¹ * v * n i, hvU, rfl⟩
    have hp : (⟨x, hx⟩, c₀) ∈ S :=
      Finset.mem_product.mpr ⟨Finset.mem_univ _, hc₀⟩
    obtain ⟨k, hout⟩ := QuotientGroup.mk_out_eq_mul U
      (((n i)⁻¹ * v * n i) * nrep hct w)
    refine ⟨(⟨x, hx⟩, c₀), hp, ?_⟩
    show F (⟨x, hx⟩, c₀) = (((x * v) * (n i * nrep hct w) : K) : K ⧸ U)
    show ((x * n i * c₀.out : K) : K ⧸ U) = _
    rw [show c₀.out = (((n i)⁻¹ * v * n i) * nrep hct w * (k : K)) from hout]
    have hstep : ((x * n i * (((n i)⁻¹ * v * n i) * nrep hct w * (k : K)) : K) : K ⧸ U) =
        ((x * n i * (((n i)⁻¹ * v * n i) * nrep hct w) : K) : K ⧸ U) := by
      rw [QuotientGroup.eq]
      have e : (x * n i * (((n i)⁻¹ * v * n i) * nrep hct w * (k : K)))⁻¹ *
          (x * n i * (((n i)⁻¹ * v * n i) * nrep hct w)) = (k : K)⁻¹ := by group
      rw [e]
      exact inv_mem k.2
    rw [hstep]
    congr 1
    group
  have hFinj : ∀ p ∈ S, ∀ q ∈ S, F p = F q → p = q := by
    rintro ⟨x, c⟩ hp ⟨x', c'⟩ hq hF
    have hpS : (x, c) ∈ Finset.univ.product (dcos U (nrep hct w)) := hp
    have hqS : (x', c') ∈ Finset.univ.product (dcos U (nrep hct w)) := hq
    have hpc : c ∈ dcos U (nrep hct w) := (Finset.mem_product.mp hpS).2
    have hqc : c' ∈ dcos U (nrep hct w) := (Finset.mem_product.mp hqS).2
    obtain ⟨u, hu, hcu⟩ := mem_dcos.mp hpc
    obtain ⟨u', hu', hcu'⟩ := mem_dcos.mp hqc
    obtain ⟨k, hout⟩ := QuotientGroup.mk_out_eq_mul U (u * nrep hct w)
    obtain ⟨k', hout'⟩ := QuotientGroup.mk_out_eq_mul U (u' * nrep hct w)
    have hstep1 : ((x.1 * n i * (u * nrep hct w * (k : K)) : K) : K ⧸ U) =
        ((x.1 * n i * u * nrep hct w : K) : K ⧸ U) := by
      rw [QuotientGroup.eq]
      have e : (x.1 * n i * (u * nrep hct w * (k : K)))⁻¹ *
          (x.1 * n i * u * nrep hct w) = (k : K)⁻¹ := by group
      rw [e]
      exact inv_mem k.2
    have hstep2 : ((x'.1 * n i * (u' * nrep hct w * (k' : K)) : K) : K ⧸ U) =
        ((x'.1 * n i * u' * nrep hct w : K) : K ⧸ U) := by
      rw [QuotientGroup.eq]
      have e : (x'.1 * n i * (u' * nrep hct w * (k' : K)))⁻¹ *
          (x'.1 * n i * u' * nrep hct w) = (k' : K)⁻¹ := by group
      rw [e]
      exact inv_mem k'.2
    have hF' : ((x.1 * n i * (u * nrep hct w * (k : K)) : K) : K ⧸ U) =
        ((x'.1 * n i * (u' * nrep hct w * (k' : K)) : K) : K ⧸ U) := by
      rw [hcu, hcu'] at hF
      change ((x.1 * n i * Quotient.out (↑(u * nrep hct w) : K ⧸ U) : K) : K ⧸ U) =
        ((x'.1 * n i * Quotient.out (↑(u' * nrep hct w) : K ⧸ U) : K) : K ⧸ U) at hF
      rw [hout, hout'] at hF
      exact hF
    have hcosF : ((x.1 * n i * u * nrep hct w : K) : K ⧸ U) =
        ((x'.1 * n i * u' * nrep hct w : K) : K ⧸ U) := by
      calc
        ((x.1 * n i * u * nrep hct w : K) : K ⧸ U)
            = ((x.1 * n i * (u * nrep hct w * (k : K)) : K) : K ⧸ U) := hstep1.symm
        _ = ((x'.1 * n i * (u' * nrep hct w * (k' : K)) : K) : K ⧸ U) := hF'
        _ = ((x'.1 * n i * u' * nrep hct w : K) : K ⧸ U) := hstep2
    have hmemU : ((x.1 * n i * u * nrep hct w)⁻¹ *
        (x'.1 * n i * u' * nrep hct w)) ∈ U := by
      rwa [QuotientGroup.eq] at hcosF
    let z : K := (x.1)⁻¹ * x'.1
    let y : K := (n i)⁻¹ * z * n i
    let d : K := (u : K)⁻¹ * y * (u' : K)
    have hmemU' : (nrep hct w)⁻¹ * d * nrep hct w ∈ U := by
      have e : ((x.1 * n i * u * nrep hct w)⁻¹ * (x'.1 * n i * u' * nrep hct w)) =
          (nrep hct w)⁻¹ * d * nrep hct w := by
        simp only [d, y, z]; group
      rwa [e] at hmemU
    by_cases hz : z = 1
    · have hxK : (x : K) = x'.1 := inv_mul_eq_one.1 hz
      have hcc : ((u * nrep hct w : K) : K ⧸ U) =
          ((u' * nrep hct w : K) : K ⧸ U) := by
        rw [QuotientGroup.eq]
        have e : ((u * nrep hct w)⁻¹ * (u' * nrep hct w)) =
            (nrep hct w)⁻¹ * d * nrep hct w := by
          simp only [d, y, z, hz]; group
        rw [e]
        exact hmemU'
      have hc_eq : c = c' := by rw [hcu, hcu']; exact hcc
      exact Prod.ext (Subtype.ext hxK) hc_eq
    · exfalso
      have hy_mem : y ∈ D.rootGroup (-Pi.single i 1) :=
        inv_conj_n_mem_rootGroup_neg hct i (mul_mem (inv_mem x.2) x'.2)
      have hy1 : y ≠ 1 := by
        intro hy
        apply hz
        have e : z = n i * y * (n i)⁻¹ := by simp only [y]; group
        rw [hy] at e
        simpa using e
      obtain ⟨hY, hhY, aY, haY, cY, hcY, heY⟩ := bruhatY_of_rankOne hct hext hBU i hy_mem hy1
      have hd_cell : d ∈ bruhatCell hct ((cs).simple i) := by
        refine ⟨(u : K)⁻¹ * aY * hY, mul_mem (mul_mem (inv_mem (posUnipotent_le_borel hu))
          (rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) haY))
          (iSup_le_borel hhY), cY * (u' : K),
          mul_mem (rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) hcY)
            (posUnipotent_le_borel hu'), ?_⟩
        simp only [d]
        rw [heY, nrep_simple hct i]
        group
      have hcell_w : d * nrep hct w ∈ bruhatCell hct w := by
        refine ⟨1, one_mem _, (nrep hct w)⁻¹ * d * nrep hct w,
          posUnipotent_le_borel hmemU', ?_⟩
        group
      have hcell_sw : d * nrep hct w ∈ bruhatCell hct ((cs).simple i * w) := by
        obtain ⟨b₁, hb₁, b₂, hb₂, hd_eq⟩ := hd_cell
        rw [nrep_simple hct i] at hd_eq
        rw [hd_eq]
        exact borel_mul_simple_mul_borel hct hext hw hb₁ hb₂
      have hw_eq : w = (cs).simple i * w := eq_of_mem_bruhatCell hct hext hcell_w hcell_sw
      rw [← hw_eq] at h
      omega
  have himage : S.image F = dcos U (n i * nrep hct w) := by
    ext c
    constructor
    · intro hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
      exact hFmem p hp
    · intro hc
      obtain ⟨p, hp, hFp⟩ := hFsurj c hc
      exact Finset.mem_image.mpr ⟨p, hp, hFp⟩
  have hcardS : S.card = Nat.card X * (dcos U (nrep hct w)).card := by
    change ((Finset.univ : Finset X) ×ˢ (dcos U (nrep hct w))).card =
      Nat.card X * (dcos U (nrep hct w)).card
    rw [Finset.card_product, Finset.card_univ, Nat.card_eq_fintype_card]
  have hcard_image : (S.image F).card = S.card := Finset.card_image_of_injOn hFinj
  have htarget : (dcos U (n i * nrep hct w)).card =
      Nat.card X * (dcos U (nrep hct w)).card := by
    rw [← himage, hcard_image, hcardS]
  have hni : (dcos U (n i)).card = Nat.card X := by
    rw [card_dcos]
    exact heckeDeg_n hct hext i
  rw [nrep_simple_mul hct hw]
  rw [← card_dcos U (n i), ← card_dcos U (nrep hct w),
    ← card_dcos U (n i * nrep hct w), hni, htarget]

end Degrees

end CFSG.LieType.Steinberg
