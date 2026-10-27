module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrbitFamily

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.RankThree.PartOne.KCUnitary (commutator_iSup_commuting commutator_self_le)
open scoped commutatorElement

@[expose] def t6orth_FactorOK (q : ℕ) {G : Type} [Group G] (F : Subgroup G) : Prop :=
  ∃ (n : ℕ) (L : Fin n → Subgroup G), (∀ j, CFSG.IsQuasisimple ↥(L j)) ∧
    (∀ j, L j ≤ ⁅F, F⁆) ∧ (∀ j, ((L j).subgroupOf ⁅F, F⁆).Normal) ∧
    (Group.IsSolvable ↥F ∨ ⁅F, F⁆ ≤ ⨆ j, L j) ∧
    (∀ j, IsTypeL2 q ↥(L j) → ∀ b ∈ F, b ^ 3 = 1 →
      ∃ s ∈ L j, ∀ m ∈ L j, b * m * b⁻¹ = s * m * s⁻¹)

section Derived

variable {G : Type*} [Group G]

@[expose] def t6orth_dsub (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅t6orth_dsub H n, t6orth_dsub H n⁆

theorem t6orth_dsub_succ_le (H : Subgroup G) (n : ℕ) : t6orth_dsub H (n + 1) ≤ t6orth_dsub H n :=
  commutator_self_le _

theorem t6orth_dsub_anti (H : Subgroup G) : Antitone (t6orth_dsub H) :=
  antitone_nat_of_succ_le (t6orth_dsub_succ_le H)

theorem t6orth_map_subtype_derivedSeries (H : Subgroup G) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype = t6orth_dsub H n := by
  induction n with
  | zero => rw [derivedSeries_zero, t6orth_dsub, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeries_succ, t6orth_dsub, Subgroup.map_commutator, ih]

theorem t6orth_dsub_iSup {ι : Type} (F : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y) (n : ℕ) :
    t6orth_dsub (⨆ i, F i) n = ⨆ i, t6orth_dsub (F i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [t6orth_dsub, ih]
    exact commutator_iSup_commuting (fun i => t6orth_dsub (F i) n)
      (fun i j hij a ha b hb => hc i j hij a (t6orth_dsub_anti (F i) (Nat.zero_le n) ha) b
        (t6orth_dsub_anti (F j) (Nat.zero_le n) hb))

theorem t6orth_dsub_eq_bot_of_solvable {H : Subgroup G} (hH : Group.IsSolvable ↥H) :
    ∃ d : ℕ, t6orth_dsub H d = ⊥ := by
  obtain ⟨d, hd⟩ := hH.solvable
  refine ⟨d, ?_⟩
  rw [← t6orth_map_subtype_derivedSeries, hd, Subgroup.map_bot]

theorem t6orth_derived_le_join {ι : Type} [Finite ι] (F : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y) (P : ι → Subgroup G)
    (htame : ∀ i, Group.IsSolvable ↥(F i) ∨ ⁅F i, F i⁆ ≤ P i) :
    ∃ k : ℕ, ∀ g ∈ derivedSeries ↥(⨆ i, F i) k, (g : G) ∈ ⨆ i, P i := by
  classical
  have hd : ∀ i, ∃ d : ℕ, t6orth_dsub (F i) d ≤ P i := by
    intro i
    rcases htame i with hs | hP
    · obtain ⟨d, hd⟩ := t6orth_dsub_eq_bot_of_solvable hs
      exact ⟨d, by rw [hd]; exact bot_le⟩
    · exact ⟨1, hP⟩
  choose d hd using hd
  cases nonempty_fintype ι
  refine ⟨Finset.univ.sup d, fun g hg => ?_⟩
  have hg' : (g : G) ∈ t6orth_dsub (⨆ i, F i) (Finset.univ.sup d) := by
    rw [← t6orth_map_subtype_derivedSeries]
    exact ⟨g, hg, rfl⟩
  rw [t6orth_dsub_iSup F hc] at hg'
  refine (iSup_le (fun i => ?_) : ⨆ i, t6orth_dsub (F i) (Finset.univ.sup d) ≤ _) hg'
  exact ((t6orth_dsub_anti (F i) (Finset.le_sup (f := d) (Finset.mem_univ i))).trans (hd i)).trans
    (le_iSup P i)

end Derived

section Decomp

variable {G : Type} [Group G] {ι : Type} (F : ι → Subgroup G)

theorem t6orth_commute_of_mem_iSup_ne
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y) (i : ι) {w : G}
    (hw : w ∈ ⨆ j, ⨆ (_ : j ≠ i), F j) {m : G} (hm : m ∈ F i) : w * m = m * w := by
  refine Subgroup.iSup_induction (fun j => ⨆ (_ : j ≠ i), F j) (C := fun w => w * m = m * w) hw
    (fun j x hx => ?_) (by simp) (fun x y hx hy => by rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc])
  refine Subgroup.iSup_induction (fun _ : j ≠ i => F j) (C := fun x => x * m = m * x) hx
    (fun hji x hx => ?_) (by simp) (fun x y hx hy => by rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc])
  exact (hc j i hji x hx m hm).eq

theorem t6orth_exists_decomp (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y)
    (hind : iSupIndep F) (i : ι) {b : G} (hb : b ∈ ⨆ j, F j) (hb3 : b ^ 3 = 1) :
    ∃ bi ∈ F i, ∃ w : G, (∀ m ∈ F i, w * m = m * w) ∧ b = bi * w ∧ bi ^ 3 = 1 := by
  have h1 : ∃ bi ∈ F i, ∃ w ∈ ⨆ j, ⨆ (_ : j ≠ i), F j, b = bi * w := by
    refine Subgroup.iSup_induction F (C := fun b => ∃ bi ∈ F i, ∃ w ∈ ⨆ j, ⨆ (_ : j ≠ i), F j,
      b = bi * w) hb ?_ ?_ ?_
    · intro j x hx
      by_cases hji : j = i
      · subst hji
        exact ⟨x, hx, 1, Subgroup.one_mem _, by simp⟩
      · exact ⟨1, Subgroup.one_mem _, x, Subgroup.mem_iSup_of_mem j
          (Subgroup.mem_iSup_of_mem hji hx), by simp⟩
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
    · rintro x y ⟨xi, hxi, wx, hwx, rfl⟩ ⟨yi, hyi, wy, hwy, rfl⟩
      refine ⟨xi * yi, (F i).mul_mem hxi hyi, wx * wy, Subgroup.mul_mem _ hwx hwy, ?_⟩
      have h : wx * yi = yi * wx := t6orth_commute_of_mem_iSup_ne F hc i hwx hyi
      calc xi * wx * (yi * wy) = xi * (wx * yi) * wy := by group
        _ = xi * (yi * wx) * wy := by rw [h]
        _ = xi * yi * (wx * wy) := by group
  obtain ⟨bi, hbi, w, hw, rfl⟩ := h1
  have hwc : ∀ m ∈ F i, w * m = m * w := fun m hm => t6orth_commute_of_mem_iSup_ne F hc i hw hm
  have hbw : bi * w = w * bi := (hwc bi hbi).symm
  have hb3' : bi ^ 3 * w ^ 3 = 1 := by
    rw [← Commute.mul_pow (show Commute bi w from hbw), hb3]
  have hbi3 : bi ^ 3 = (w ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hb3'
  refine ⟨bi, hbi, w, hwc, rfl, ?_⟩
  have hmem1 : bi ^ 3 ∈ F i := (F i).pow_mem hbi 3
  have hmem2 : bi ^ 3 ∈ ⨆ j, ⨆ (_ : j ≠ i), F j := by
    rw [hbi3]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hw 3)
  exact Subgroup.disjoint_def.mp (hind i) hmem1 hmem2

end Decomp

section Data

theorem t6orth_blocks_data {G : Type} [Group G] [Finite G] (Ω : Subgroup G) (q : ℕ) (a : ↥Ω)
    {ι : Type} [Finite ι] (F : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y) (hind : iSupIndep F)
    (hjoin : ∀ g : ↥Ω, g ∈ Subgroup.centralizer ({a} : Set ↥Ω) ↔ (g : G) ∈ ⨆ i, F i)
    (hΩ : ∀ i, ⁅F i, F i⁆ ≤ Ω) (hF : ∀ i, t6orth_FactorOK q (F i)) :
    ∃ (ι' : Type) (_ : Finite ι') (N : ι' → Subgroup ↥Ω),
      (∀ i, N i ≤ Subgroup.centralizer ({a} : Set ↥Ω)) ∧
      (∀ i, ((N i).subgroupOf (Subgroup.centralizer ({a} : Set ↥Ω))).IsSubnormal) ∧
      (∀ i, CFSG.IsQuasisimple (N i)) ∧
      (∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set ↥Ω)) k,
        (g : ↥Ω) ∈ ⨆ i, N i) ∧
      (∀ i, IsTypeL2 q (N i) → ∀ b ∈ Subgroup.centralizer ({a} : Set ↥Ω), b ^ 3 = 1 →
        ∃ s ∈ N i, ∀ m ∈ N i, b * m * b⁻¹ = s * m * s⁻¹) := by
  classical
  choose n L hLq hLF hLn htame hkey using hF
  set C : Subgroup ↥Ω := Subgroup.centralizer ({a} : Set ↥Ω) with hC
  let κ : Type := Σ i, Fin (n i)
  let L' : κ → Subgroup G := fun k => L k.1 k.2
  have hLΩ : ∀ k : κ, L' k ≤ Ω := fun k => (hLF k.1 k.2).trans (hΩ k.1)
  have hLF' : ∀ k : κ, L' k ≤ F k.1 := fun k => (hLF k.1 k.2).trans (commutator_self_le (F k.1))
  have hLM : ∀ k : κ, L' k ≤ ⨆ i, F i := fun k => (hLF' k).trans (le_iSup F k.1)
  let N : κ → Subgroup ↥Ω := fun k => (L' k).subgroupOf Ω
  have hNmem : ∀ (k : κ) (m : ↥Ω), m ∈ N k ↔ (m : G) ∈ L' k := fun k m => Subgroup.mem_subgroupOf
  have hNC : ∀ k : κ, N k ≤ C := fun k m hm => (hjoin m).2 (hLM k ((hNmem k m).1 hm))
  have hDn : ∀ i, ∀ c ∈ ⨆ j, F j, ∀ g ∈ ⁅F i, F i⁆, c * g * c⁻¹ ∈ ⁅F i, F i⁆ :=
    fun i => conj_mem_commutator_of_orbit_family F hc i
  refine ⟨κ, inferInstance, N, hNC, fun k => ?_, fun k => ?_, ?_, fun k hT b hb hb3 => ?_⟩
  ·
    let D : Subgroup ↥Ω := (⁅F k.1, F k.1⁆).subgroupOf Ω
    have hDmem : ∀ m : ↥Ω, m ∈ D ↔ (m : G) ∈ ⁅F k.1, F k.1⁆ := fun m => Subgroup.mem_subgroupOf
    have hDC : D ≤ C := fun m hm => (hjoin m).2 (((commutator_self_le (F k.1)).trans
      (le_iSup F k.1)) ((hDmem m).1 hm))
    have hND : N k ≤ D := fun m hm => (hDmem m).2 (hLF k.1 k.2 ((hNmem k m).1 hm))
    have hDnorm : (D.subgroupOf C).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hDC]
      intro g c hg hc
      rw [hDmem] at hg ⊢
      exact hDn k.1 (c : G) ((hjoin c).1 hc) (g : G) hg
    have hle : (N k).subgroupOf C ≤ D.subgroupOf C := fun m hm =>
      Subgroup.mem_subgroupOf.mpr (hND (Subgroup.mem_subgroupOf.mp hm))
    refine Subgroup.IsSubnormal.step _ (D.subgroupOf C) hle hDnorm.isSubnormal ?_
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h c hh hcm
    have hh' : ((h : ↥C) : ↥Ω) ∈ N k := Subgroup.mem_subgroupOf.mp hh
    have hcm' : (((c : ↥C) : ↥Ω) : G) ∈ ⁅F k.1, F k.1⁆ :=
      (hDmem _).1 (Subgroup.mem_subgroupOf.mp hcm)
    refine Subgroup.mem_subgroupOf.mpr ((hNmem k _).2 ?_)
    have h1 := (Subgroup.normal_subgroupOf_iff (hLF k.1 k.2)).mp (hLn k.1 k.2)
      (((h : ↥C) : ↥Ω) : G) (((c : ↥C) : ↥Ω) : G) ((hNmem k _).1 hh') hcm'
    exact h1
  ·
    have e : ↥(N k) ≃* ↥(L' k) := Subgroup.subgroupOfEquivOfLe (hLΩ k)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (hLq k.1 k.2)
  ·
    obtain ⟨k, hk⟩ := t6orth_derived_le_join F hc (fun i => ⨆ j : Fin (n i), L i j) htame
    have hle : (⨆ i, ⨆ j : Fin (n i), L i j) ≤ ⨆ k : κ, L' k :=
      iSup_le fun i => iSup_le fun j => le_iSup L' ⟨i, j⟩
    refine ⟨k, fun g hg => ?_⟩
    let ιM : ↥C →* ↥(⨆ i, F i) :=
      { toFun := fun x => ⟨((x : ↥Ω) : G), (hjoin x).1 x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hmapd : ιM g ∈ derivedSeries ↥(⨆ i, F i) k :=
      map_derivedSeries_le_derivedSeries ιM k ⟨g, hg, rfl⟩
    have h1 : (((g : ↥C) : ↥Ω) : G) ∈ ⨆ k : κ, L' k := hle (hk _ hmapd)
    have h3 : ((g : ↥C) : ↥Ω) ∈ (⨆ k : κ, L' k).subgroupOf Ω := h1
    rw [subgroupOf_iSup_eq L' hLΩ] at h3
    exact h3
  ·
    have hTi : IsTypeL2 q ↥(L k.1 k.2) := by
      have e : ↥(N k) ≃* ↥(L' k) := Subgroup.subgroupOfEquivOfLe (hLΩ k)
      exact p6_isTypeL2_of_equiv e hT
    have hbG : ((b : ↥Ω) : G) ∈ ⨆ i, F i := (hjoin b).1 hb
    have hb3G : ((b : ↥Ω) : G) ^ 3 = 1 := by
      have := congrArg Subtype.val hb3
      simpa using this
    obtain ⟨bi, hbi, w, hw, hbw, hbi3⟩ := t6orth_exists_decomp F hc hind k.1 hbG hb3G
    obtain ⟨s, hs, hsm⟩ := hkey k.1 k.2 hTi bi hbi hbi3
    have hsΩ : s ∈ Ω := hLΩ k hs
    refine ⟨⟨s, hsΩ⟩, (hNmem k ⟨s, hsΩ⟩).2 hs, fun m hm => ?_⟩
    apply Subtype.ext
    have hmL : (m : G) ∈ L' k := (hNmem k m).1 hm
    have hmF : (m : G) ∈ F k.1 := hLF' k hmL
    have hwm : w * (m : G) = (m : G) * w := hw _ hmF
    show ((b : ↥Ω) : G) * (m : G) * ((b : ↥Ω) : G)⁻¹ = s * (m : G) * s⁻¹
    rw [hbw]
    calc bi * w * (m : G) * (bi * w)⁻¹ = bi * (w * (m : G) * w⁻¹) * bi⁻¹ := by group
      _ = bi * (m : G) * bi⁻¹ := by rw [hwm]; group
      _ = s * (m : G) * s⁻¹ := hsm _ hmL

end Data

end CFSG.HardMathSupport.Dickson.Sec6.I1431
