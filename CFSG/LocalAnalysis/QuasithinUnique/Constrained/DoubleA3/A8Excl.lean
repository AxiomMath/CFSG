module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A8Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4BlockMore

public section

namespace CFSG.QuasithinUnique.DoubleA3.A8Excl

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3.A8Perm Subgroup

variable {Γ : Type} [Group Γ]

@[expose] def InO (ι : Γ →* Perm (Fin 8)) (U : Subgroup Γ) (x : Fin 8) : Prop :=
  ∃ u ∈ U, ι u 0 = x

theorem inO_zero (ι : Γ →* Perm (Fin 8)) (U : Subgroup Γ) : InO ι U 0 :=
  ⟨1, U.one_mem, by simp⟩

theorem inO_smul {ι : Γ →* Perm (Fin 8)} {U : Subgroup Γ} {u : Γ} (hu : u ∈ U) (x : Fin 8) :
    InO ι U (ι u x) ↔ InO ι U x := by
  constructor
  · rintro ⟨v, hv, hvx⟩
    refine ⟨u⁻¹ * v, U.mul_mem (U.inv_mem hu) hv, ?_⟩
    rw [map_mul, Perm.mul_apply, hvx, map_inv]
    simp
  · rintro ⟨v, hv, rfl⟩
    refine ⟨u * v, U.mul_mem hu hv, ?_⟩
    rw [map_mul, Perm.mul_apply]

@[expose] def pres (ι : Γ →* Perm (Fin 8)) (U : Subgroup Γ) : Subgroup Γ where
  carrier := {g | ∀ x, InO ι U (ι g x) ↔ InO ι U x}
  mul_mem' := by
    intro a b ha hb x
    rw [map_mul, Perm.mul_apply]
    exact (ha _).trans (hb x)
  one_mem' := fun x => by rw [map_one, Perm.one_apply]
  inv_mem' := by
    intro a ha x
    have := ha (ι a⁻¹ x)
    rw [← Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Perm.one_apply] at this
    exact this.symm

section Free

variable {ι : Γ →* Perm (Fin 8)} {L U : Subgroup Γ} (hL : IsA4Block L U)
include hL

theorem fpf_of_mem [Finite Γ] {z : Γ} (hz : z ∈ U) (hz1 : z ≠ 1) (hzfpf : ∀ ω, ι z ω ≠ ω) :
    ∀ u ∈ U, u ≠ 1 → ∀ ω, ι u ω ≠ ω := by
  intro u hu hu1 ω hω
  obtain ⟨c, -, hc3, hcN, hcfp, -⟩ := hL.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  obtain ⟨n, hn⟩ := klein_conj_transitive hL.card_U hc3' hcN hcfp hz hu hz1 hu1
  apply hzfpf (ι (c ^ n) ω)
  have h1 : ι ((c ^ n)⁻¹ * z * c ^ n) ω = ω := by rw [← hn]; exact hω
  rw [map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq] at h1
  exact h1

variable (hfpf : ∀ u ∈ U, u ≠ 1 → ∀ ω, ι u ω ≠ ω)

include hfpf in
omit hL in
theorem free_of_fpf {u v : Γ} (hu : u ∈ U) (hv : v ∈ U) {ω : Fin 8} (h : ι u ω = ι v ω) :
    u = v := by
  by_contra hne
  have h1 : v⁻¹ * u ≠ 1 := fun h' => hne (by rw [inv_mul_eq_one] at h'; exact h'.symm)
  refine hfpf (v⁻¹ * u) (U.mul_mem (U.inv_mem hv) hu) h1 ω ?_
  rw [map_mul, map_inv, Perm.mul_apply, h]
  simp

include hfpf

theorem ncard_orbit (ω : Fin 8) : Set.ncard {x : Fin 8 | ∃ u ∈ U, ι u ω = x} = 4 := by
  have hinj : Function.Injective (fun u : U => ι u ω) := fun u v h =>
    Subtype.ext (free_of_fpf hfpf u.2 v.2 h)
  have hset : {x : Fin 8 | ∃ u ∈ U, ι u ω = x} = Set.range (fun u : U => ι u ω) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
  rw [hset, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, hL.card_U]

theorem same_orbit {x y : Fin 8} (h : InO ι U x ↔ InO ι U y) : ∃ u ∈ U, ι u x = y := by
  by_cases hx : InO ι U x
  · obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := h.mp ⟨u, hu, rfl⟩
    refine ⟨v * u⁻¹, U.mul_mem hv (U.inv_mem hu), ?_⟩
    rw [map_mul, Perm.mul_apply, map_inv]
    simp
  · have hy : ¬ InO ι U y := fun hy => hx (h.mpr hy)
    set O₁ : Set (Fin 8) := {x : Fin 8 | InO ι U x} with hO₁
    have hO₁card : O₁.ncard = 4 := ncard_orbit hL hfpf 0
    have hcompl : O₁ᶜ.ncard = 4 := by
      rw [Set.ncard_compl, hO₁card]
      simp
    have hsub : {w : Fin 8 | ∃ u ∈ U, ι u x = w} ⊆ O₁ᶜ := by
      rintro _ ⟨u, hu, rfl⟩ hmem
      exact hx ((inO_smul hu x).mp hmem)
    have heq : {w : Fin 8 | ∃ u ∈ U, ι u x = w} = O₁ᶜ :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcompl, ncard_orbit hL hfpf x]) (Set.toFinite _)
    have hymem : y ∈ O₁ᶜ := hy
    rw [← heq] at hymem
    exact hymem

theorem inO_conj {g : Γ} (hg : g ∈ normalizer (U : Set Γ)) {x y : Fin 8}
    (h : InO ι U x ↔ InO ι U y) : InO ι U (ι g x) ↔ InO ι U (ι g y) := by
  obtain ⟨u, hu, hxy⟩ := same_orbit hL hfpf h
  have hgu : g * u * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have : ι g y = ι (g * u * g⁻¹) (ι g x) := by
    rw [← hxy]
    simp [map_mul, map_inv, Perm.mul_apply]
  rw [this]
  exact (inO_smul hgu _).symm

theorem c_mem_pres {c : Γ} (hc3' : c ^ 3 = 1) (hcN : c ∈ normalizer (U : Set Γ)) :
    c ∈ pres ι U := by
  have hcinv : c⁻¹ ∈ normalizer (U : Set Γ) := (normalizer (U : Set Γ)).inv_mem hcN
  have hcc : ∀ x, ι c⁻¹ (ι c x) = x := fun x => by
    rw [← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply]
  by_cases ha : InO ι U (ι c 0)
  · intro x
    by_cases hx : InO ι U x
    · have h1 := inO_conj hL hfpf hcN (x := x) (y := 0) ⟨fun _ => inO_zero ι U, fun _ => hx⟩
      exact ⟨fun _ => hx, fun _ => h1.mpr ha⟩
    · refine ⟨fun h => ?_, fun h => absurd h hx⟩
      have h1 := inO_conj hL hfpf hcinv (x := ι c x) (y := ι c 0)
        ⟨fun _ => ha, fun _ => h⟩
      rw [hcc, hcc] at h1
      exact absurd (h1.mpr (inO_zero ι U)) hx
  · exfalso
    have h1 : InO ι U (ι c (ι c 0)) := by
      by_contra h1
      have h2 := inO_conj hL hfpf hcinv (x := ι c (ι c 0)) (y := ι c 0)
        ⟨fun h => absurd h h1, fun h => absurd h ha⟩
      rw [hcc, hcc] at h2
      exact ha (h2.mpr (inO_zero ι U) )
    have h3 := inO_conj hL hfpf hcN (x := ι c (ι c 0)) (y := 0)
      ⟨fun _ => inO_zero ι U, fun _ => h1⟩
    have h4 : ι c (ι c (ι c 0)) = 0 := by
      have : ι (c ^ 3) 0 = 0 := by rw [hc3', map_one, Perm.one_apply]
      simpa [pow_succ, map_mul, Perm.mul_apply] using this
    rw [h4] at h3
    exact ha (h3.mp (inO_zero ι U))

theorem L_le_pres : L ≤ pres ι U := by
  obtain ⟨c, -, hc3, hcN, -, hLc⟩ := hL.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  rw [hLc]
  exact sup_le (fun u hu x => inO_smul hu x)
    (zpowers_le.mpr (c_mem_pres hL hfpf hc3' hcN))

omit hfpf in
theorem L_le_normalizer : L ≤ normalizer (U : Set Γ) := by
  obtain ⟨c, -, -, hcN, -, hLc⟩ := hL.exists_c
  rw [hLc]
  exact sup_le Subgroup.le_normalizer (zpowers_le.mpr hcN)

theorem faithful_on_O [Finite Γ] {l : Γ} (hl : l ∈ L) (hfix : ∀ x, InO ι U x → ι l x = x) :
    l = 1 := by
  have hlN : l ∈ normalizer (U : Set Γ) := L_le_normalizer hL hl
  have hcomm : ∀ u ∈ U, l * u = u * l := by
    intro u hu
    have hwU : l * u * l⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp hlN u).mp hu) (U.inv_mem hu)
    have hw0 : ι (l * u * l⁻¹ * u⁻¹) 0 = 0 := by
      have hx : InO ι U (ι u⁻¹ 0) := (inO_smul (U.inv_mem hu) 0).mpr (inO_zero ι U)
      have h1 : ι l (ι u⁻¹ 0) = ι u⁻¹ 0 := hfix _ hx
      have h2 : ι l⁻¹ (ι u⁻¹ 0) = ι u⁻¹ 0 := by
        calc ι l⁻¹ (ι u⁻¹ 0) = ι l⁻¹ (ι l (ι u⁻¹ 0)) := by rw [h1]
          _ = ι u⁻¹ 0 := by
            rw [← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply]
      have h3 : ι l 0 = 0 := hfix 0 (inO_zero ι U)
      have h4 : ι u (ι u⁻¹ 0) = 0 := by
        rw [← Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Perm.one_apply]
      calc ι (l * u * l⁻¹ * u⁻¹) 0 = ι l (ι u (ι l⁻¹ (ι u⁻¹ 0))) := by
            simp [map_mul, map_inv, Perm.mul_apply]
        _ = 0 := by rw [h2, h4, h3]
    have hw1 : l * u * l⁻¹ * u⁻¹ = 1 := by
      by_contra h
      exact hfpf _ hwU h 0 hw0
    calc l * u = (l * u * l⁻¹ * u⁻¹) * (u * l) := by group
      _ = u * l := by rw [hw1, one_mul]
  have hlU : l ∈ U := hL.mem_of_centralizes hl hcomm
  by_contra hl1
  exact hfpf l hlU hl1 0 (hfix 0 (inO_zero ι U))

theorem inO_of_fix {r : Γ} (hr : r ∈ normalizer (L : Set Γ)) (hr0 : ι r 0 = 0) (x : Fin 8)
    (hx : InO ι U x) : InO ι U (ι r x) := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hl' : r * u * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hr u).mp (hL.le hu)
  have hr0' : ι r⁻¹ 0 = 0 := by
    rw [map_inv, Perm.inv_eq_iff_eq]
    exact hr0.symm
  have : ι r (ι u 0) = ι (r * u * r⁻¹) 0 := by
    rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, hr0']
  rw [this]
  exact (L_le_pres hL hfpf hl' 0).mpr (inO_zero ι U)

theorem eq_one_of_fixing_O [Finite Γ] (hι : Function.Injective ι) {r : Γ}
    (hrN : r ∈ normalizer (L : Set Γ)) (hrfix : ∀ y, InO ι U y → ι r y = y) : r = 1 := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, -⟩ := hL.exists_c
  have hcinv : c⁻¹ ∈ normalizer (U : Set Γ) := (normalizer (U : Set Γ)).inv_mem hcN
  have hr0 : ι r 0 = 0 := hrfix 0 (inO_zero ι U)
  have hinv : ∀ y, ι r⁻¹ (ι r y) = y := fun y => by
    rw [← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply]
  have hrinvN : r⁻¹ ∈ normalizer (L : Set Γ) := (normalizer (L : Set Γ)).inv_mem hrN
  have hrinvfix : ∀ y, InO ι U y → ι r⁻¹ y = y := fun y hy => by
    have := hrfix y hy
    calc ι r⁻¹ y = ι r⁻¹ (ι r y) := by rw [this]
      _ = y := hinv y
  have hr0inv : ι r⁻¹ 0 = 0 := hrinvfix 0 (inO_zero ι U)
  have hpr : ∀ x, InO ι U (ι r x) ↔ InO ι U x := fun x =>
    ⟨fun h => by
      have := inO_of_fix hL hfpf hrinvN hr0inv _ h
      rwa [hinv] at this, inO_of_fix hL hfpf hrN hr0 x⟩
  have hcommL : ∀ l ∈ L, r * l = l * r := by
    intro l hl
    have hm : l⁻¹ * (r * l * r⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hrN l).mp hl)
    have hm1 : l⁻¹ * (r * l * r⁻¹) = 1 := by
      apply faithful_on_O hL hfpf hm
      intro x hx
      have h1 : ι r⁻¹ x = x := hrinvfix x hx
      have hlx : InO ι U (ι l x) := (L_le_pres hL hfpf hl x).mpr hx
      have h2 : ι r (ι l x) = ι l x := hrfix _ hlx
      have : ι (l⁻¹ * (r * l * r⁻¹)) x = ι l⁻¹ (ι r (ι l (ι r⁻¹ x))) := by
        simp [map_mul, Perm.mul_apply]
      rw [this, h1, h2, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply]
    calc r * l = l * (l⁻¹ * (r * l * r⁻¹)) * r := by group
      _ = l * r := by rw [hm1, mul_one]
  have hcomm_act : ∀ g ∈ L, ∀ y, ι r (ι g y) = ι g (ι r y) := fun g hg y => by
    have := congrArg (fun h => ι h y) (hcommL g hg)
    simpa [map_mul, Perm.mul_apply] using this
  have hfixc : ∀ x, ¬ InO ι U x → ι r x = x := by
    intro x hx
    have hrx : ¬ InO ι U (ι r x) := fun h => hx ((hpr x).mp h)
    obtain ⟨u, hu, hux⟩ := same_orbit hL hfpf
      (show InO ι U x ↔ InO ι U (ι r x) from ⟨fun h => absurd h hx, fun h => absurd h hrx⟩)
    have htrans : ∀ y, ¬ InO ι U y → ι r y = ι u y := by
      intro y hy
      obtain ⟨v, hv, hvy⟩ := same_orbit hL hfpf
        (show InO ι U x ↔ InO ι U y from ⟨fun h => absurd h hx, fun h => absurd h hy⟩)
      rw [← hvy, hcomm_act v (hL.le hv) x, ← hux]
      have huv : u * v = v * u := hL.comm_U u hu v hv
      have := congrArg (fun h => ι h x) huv
      simpa [map_mul, Perm.mul_apply] using this.symm
    have hcpres : c ∈ pres ι U := L_le_pres hL hfpf hcL
    have hcx : ¬ InO ι U (ι c x) := fun h => hx ((hcpres x).mp h)
    have e1 : ι c (ι u x) = ι u (ι c x) := by
      have h1 := htrans (ι c x) hcx
      rw [hcomm_act c hcL x, ← hux] at h1
      exact h1
    have e2 : ι (c * u) x = ι (u * c) x := by simpa [map_mul, Perm.mul_apply] using e1
    have h5 : c⁻¹ * u⁻¹ * c ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp hcinv u⁻¹).mp (U.inv_mem hu)
      simpa using this
    have hgU : (u * c)⁻¹ * (c * u) ∈ U := by
      have : (u * c)⁻¹ * (c * u) = (c⁻¹ * u⁻¹ * c) * u := by group
      rw [this]
      exact U.mul_mem h5 hu
    have hgx : ι ((u * c)⁻¹ * (c * u)) x = x := by
      rw [map_mul, Perm.mul_apply, e2, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Perm.one_apply]
    have hg1 : (u * c)⁻¹ * (c * u) = 1 := by
      by_contra h
      exact hfpf _ hgU h x hgx
    have hcu : c * u * c⁻¹ = u := by
      calc c * u * c⁻¹ = (u * c) * ((u * c)⁻¹ * (c * u)) * c⁻¹ := by group
        _ = u := by rw [hg1]; group
    have hu1 : u = 1 := by
      by_contra hne
      exact hcfp u hu hne hcu
    rw [← hux, hu1, map_one, Perm.one_apply]
  apply hι
  rw [map_one]
  apply Equiv.ext
  intro x
  by_cases hx : InO ι U x
  · exact hrfix x hx
  · exact hfixc x hx

theorem card_le_sixteen [Finite Γ] (hι : Function.Injective ι) {R : Subgroup Γ}
    (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (L : Set Γ)) : Nat.card R ≤ 16 := by
  classical
  have hRω2 : IsPGroup 2 ↥(R ⊓ fixSub ι 0) :=
    hR2.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hQ : ∀ g : ↥(R ⊓ fixSub ι 0), ∀ y : Fin 8,
      (InO ι U (ι g y) ∧ ι g y ≠ 0) ↔ (InO ι U y ∧ y ≠ 0) := by
    intro g y
    have hgN : (g : Γ) ∈ normalizer (L : Set Γ) := hRN g.2.1
    have hg0 : ι g 0 = 0 := g.2.2
    have hginvN : (g : Γ)⁻¹ ∈ normalizer (L : Set Γ) := (normalizer (L : Set Γ)).inv_mem hgN
    have hginv0 : ι (g : Γ)⁻¹ 0 = 0 := by
      rw [map_inv, Perm.inv_eq_iff_eq]
      exact hg0.symm
    have hinv : ∀ y, ι (g : Γ)⁻¹ (ι g y) = y := fun y => by
      rw [← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply]
    have hpr : InO ι U (ι g y) ↔ InO ι U y :=
      ⟨fun h => by
        have := inO_of_fix hL hfpf hginvN hginv0 _ h
        rwa [hinv] at this, inO_of_fix hL hfpf hgN hg0 y⟩
    have hne : ι g y ≠ 0 ↔ y ≠ 0 := by
      constructor
      · intro h h0
        apply h
        rw [h0, hg0]
      · intro h h0
        apply h
        apply (ι g).injective
        rw [h0, hg0]
    exact and_congr hpr hne
  let φ : ↥(R ⊓ fixSub ι 0) →* Perm {y : Fin 8 // InO ι U y ∧ y ≠ 0} :=
    { toFun := fun g => (ι g).subtypePerm (p := fun y => InO ι U y ∧ y ≠ 0) (hQ g)
      map_one' := by
        apply Equiv.ext
        intro y
        apply Subtype.ext
        simp
      map_mul' := fun g h => by
        apply Equiv.ext
        intro y
        apply Subtype.ext
        show ι ((g * h : ↥(R ⊓ fixSub ι 0)) : Γ) y.1 = ι g (ι h y.1)
        rw [Subgroup.coe_mul, map_mul]
        rfl }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfix : ∀ y, InO ι U y → ι g y = y := by
      intro y hy
      by_cases hy0 : y = 0
      · rw [hy0]
        exact g.2.2
      · have := congrArg (fun p : Perm {y : Fin 8 // InO ι U y ∧ y ≠ 0} =>
          (p ⟨y, hy, hy0⟩ : Fin 8)) hg
        simpa [φ] using this
    exact Subtype.ext (eq_one_of_fixing_O hL hfpf hι (hRN g.2.1) hfix)
  have hQcard : Nat.card {y : Fin 8 // InO ι U y ∧ y ≠ 0} = 3 := by
    have hset : {y : Fin 8 | InO ι U y ∧ y ≠ 0} = {y : Fin 8 | InO ι U y} \ {0} := by
      ext y
      simp
    have h4 : Set.ncard {y : Fin 8 | InO ι U y} = 4 := ncard_orbit hL hfpf 0
    have h3 : Set.ncard {y : Fin 8 | InO ι U y ∧ y ≠ 0} = 3 := by
      rw [hset, Set.ncard_sdiff_singleton_of_mem (s := {y : Fin 8 | InO ι U y}) (a := 0)
        (inO_zero ι U), h4]
    rw [← h3]
    exact Nat.card_coe_set_eq _
  have hle2 : Nat.card ↥(R ⊓ fixSub ι 0) ≤ 2 := by
    have := CFSG.QuasithinUnique.Id2519.Tab.Class8.card_le_of_injective hRω2 φ hφ (e := 1)
      (u := 3) (by norm_num) (by rw [Nat.card_perm, hQcard]; norm_num [Nat.factorial])
    simpa using this
  have hos := orbit_ncard_mul_stab_card ι R 0
  have horb : Set.ncard {ω' : Fin 8 | ∃ p ∈ R, ι p 0 = ω'} ≤ 8 := by
    have := Set.ncard_le_card {ω' : Fin 8 | ∃ p ∈ R, ι p 0 = ω'}
    simpa using this
  calc Nat.card R = _ := hos.symm
    _ ≤ 8 * 2 := Nat.mul_le_mul horb hle2
    _ = 16 := by norm_num

end Free


section Final

variable [Finite Γ] {ι : Γ →* Perm (Fin 8)} {L U : Subgroup Γ}

theorem false_of_big_two_group (hL : IsA4Block L U) (hι : Function.Injective ι)
    (hev : ∀ g, Perm.sign (ι g) = 1) {z : Γ} (hz : z ∈ U) (hz1 : z ≠ 1) {P : Subgroup Γ}
    (hP2 : IsPGroup 2 P) (hP64 : 64 ≤ Nat.card P) (hPz : ∀ g ∈ P, g * z = z * g)
    {R : Subgroup Γ} (hR2 : IsPGroup 2 R) (hR32 : 32 ≤ Nat.card R)
    (hRN : R ≤ normalizer (L : Set Γ)) : False := by
  have htrans := exists_mem_of_card_ge ι hι hev hP2 hP64
  have hzfpf := fixed_point_free_of_commute ι hι htrans hz1 hPz
  have hfpf := fpf_of_mem hL hz hz1 hzfpf
  have := card_le_sixteen hL hfpf hι hR2 hRN
  omega

end Final

end CFSG.QuasithinUnique.DoubleA3.A8Excl
