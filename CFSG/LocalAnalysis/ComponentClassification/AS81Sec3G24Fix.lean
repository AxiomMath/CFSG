module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step33Syl
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.G2

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

omit [CharP K 2] in
theorem torus_r_conj_b [Finite K]
    (hK : Nat.card K = 4) (t : Kˣ) (s : K) :
    torusElt .G2 K g2ir t * X g2b s * (torusElt .G2 K g2ir t)⁻¹ = X g2b s := by
  rw [root_torus_conjugation g2ir isRoot_g2b t s]
  have h : ∑ j, Tag.G2.cartan g2ir j * g2b j = 3 := by decide
  have ht : t ^ (3 : ℤ) = 1 := by exact_mod_cast pow_three_eq_one_of_card hK t
  rw [h, ht, Units.val_one, one_mul]


theorem borel_r_conj_b [Finite K] (hK : Nat.card K = 4) (t : Kˣ) (b s : K) :
    (torusElt .G2 K g2ir t * X g2r b) * X g2b s * (torusElt .G2 K g2ir t * X g2r b)⁻¹ =
      X g2b s := by
  have hc : X g2r b * X g2b s = X g2b s * X g2r b := by
    have := swap_b_r (K := K) s b 1
    simpa using this.symm
  calc (torusElt .G2 K g2ir t * X g2r b) * X g2b s * (torusElt .G2 K g2ir t * X g2r b)⁻¹ =
      torusElt .G2 K g2ir t * (X g2r b * X g2b s) * (X g2r b)⁻¹ *
        (torusElt .G2 K g2ir t)⁻¹ := by group
    _ = torusElt .G2 K g2ir t * X g2b s * (torusElt .G2 K g2ir t)⁻¹ := by rw [hc]; group
    _ = X g2b s := torus_r_conj_b hK t s

theorem conj_g2N_b [Finite K] (B C D E F s : K) :
    g2N 0 B C D E F * X g2b s * (g2N 0 B C D E F)⁻¹ = g2N 0 0 0 0 s (B * s) := by
  obtain ⟨-, -, -, -, -, -, -, -, hXc, -⟩ := even_G2_highest_long_root_centralizer K
  have h1 := conj_b s 0 B C D E F
  rw [← g2N_mul_c] at h1
  have hcomm := (hXc (B * s)).2 _ (g2N_mem_g2LongRadical B C D E F)
  have hbb : X g2b s * X g2b s = 1 := pinnedX_mul_self g2b s
  have e : g2N 0 0 0 0 s (B * s) = X g2b s * X g2c (B * s) := by
    simp [g2N, pinnedX_zero]
  rw [e]
  calc g2N 0 B C D E F * X g2b s * (g2N 0 B C D E F)⁻¹ =
      (X g2b s * X g2b s) * g2N 0 B C D E F * X g2b s * (g2N 0 B C D E F)⁻¹ := by
        rw [hbb, one_mul]
    _ = X g2b s * (X g2b s * g2N 0 B C D E F * X g2b s) * (g2N 0 B C D E F)⁻¹ := by group
    _ = X g2b s * (g2N 0 B C D E F * X g2c (B * s)) * (g2N 0 B C D E F)⁻¹ := by rw [h1]
    _ = X g2b s * X g2c (B * s) := by rw [← hcomm.eq]; group

theorem conj_b_of_mem_longCent [Finite K] (hK : Nat.card K = 4) {g : ModGL .G2 K}
    (hg : g ∈ adjointGroup .G2 K ⊓ centralizer ({X g2c 1} : Set (ModGL .G2 K)))
    {y' y z : K} (hy' : y' ≠ 0) (h : g * X g2b y' * g⁻¹ = g2N 0 0 0 0 y z) :
    y = y' ∧ ∃ B : K, ∀ s : K, g * X g2b s * g⁻¹ = g2N 0 0 0 0 s (B * s) := by
  obtain ⟨-, -, -, -, hset, hLN, -, -, -, ⟨π, -, -, hπ⟩, -, -⟩ :=
    even_G2_highest_long_root_centralizer K
  have hg' : g ∈ ((adjointGroup .G2 K ⊓ centralizer ({X g2c 1} : Set (ModGL .G2 K)) :
      Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hg
  rw [hset] at hg'
  obtain ⟨q, hq, l, hl, rfl⟩ := hg'
  obtain ⟨ρ, -, -, -, -, hrange, -, hcell0, hcell⟩ := g2_rank_one (K := K) g2ir
  have hl' := hl
  rw [← hrange] at hl'
  obtain ⟨m, hm⟩ := hl'
  by_cases hc : (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  ·
    obtain ⟨t, b, e⟩ : ∃ (t : Kˣ) (b : K),
        ρ m = torusElt .G2 K g2ir t * pinnedX .G2 K g2r b :=
      ⟨_, _, by rw [hcell0 m hc, xUnit_g2ir]⟩
    have hlb : ∀ s, l * X g2b s * l⁻¹ = X g2b s := fun s => by
      rw [← hm, e]
      exact borel_r_conj_b hK t b s
    obtain ⟨B, C, D, E, F, rfl⟩ := hq
    have key : ∀ s, g2N 0 B C D E F * l * X g2b s * (g2N 0 B C D E F * l)⁻¹ =
        g2N 0 0 0 0 s (B * s) := fun s => by
      rw [show g2N 0 B C D E F * l * X g2b s * (g2N 0 B C D E F * l)⁻¹ =
        g2N 0 B C D E F * (l * X g2b s * l⁻¹) * (g2N 0 B C D E F)⁻¹ by group, hlb, conj_g2N_b]
    refine ⟨?_, B, key⟩
    obtain ⟨-, -, -, -, h5, -⟩ := g2N_injective ((key y').symm.trans h)
    exact h5.symm
  ·
    exfalso
    obtain ⟨c₁, t, c₂, e⟩ : ∃ (c₁ : K) (t : Kˣ) (c₂ : K), ρ m = pinnedX .G2 K g2r c₁ *
        torusElt .G2 K g2ir t * weylElt .G2 K g2ir 1 * pinnedX .G2 K g2r c₂ :=
      ⟨_, _, _, by rw [hcell m hc, xUnit_g2ir, xUnit_g2ir]⟩
    have hact : ActsOnRadical l (((radMr c₁ ∘ₗ radDiag t) ∘ₗ radSwap) ∘ₗ radMr c₂) := by
      rw [← hm, e]
      exact (((actsOnRadical_pinnedX_r _).mul (actsOnRadical_torusElt_r _)).mul
        actsOnRadical_weylElt_r).mul (actsOnRadical_pinnedX_r _)
    set T := ((radMr c₁ ∘ₗ radDiag t) ∘ₗ radSwap) ∘ₗ radMr c₂ with hT
    set v : Fin 4 → K := ![0, 0, 0, y'] with hv
    obtain ⟨F', hF'⟩ := hact.2 v 0
    have hxb : g2N 0 (v 0) (v 1) (v 2) (v 3) 0 = X g2b y' := by
      rw [pinnedX_b_eq_g2N]
      rfl
    rw [hxb] at hF'
    have hy := g2N_mem_g2LongRadical (0 : K) 0 0 y' 0
    rw [← pinnedX_b_eq_g2N] at hy
    have hyQ : l * X g2b y' * l⁻¹ ∈ g2LongRadical K := (mem_normalizer_iff.1 (hLN hl) _).1 hy
    have h2 : q * (l * X g2b y' * l⁻¹) * q⁻¹ = g2N 0 0 0 0 y z := by
      rw [← h]
      group
    have h3 : π ⟨q * (l * X g2b y' * l⁻¹) * q⁻¹, mul_mem (mul_mem hq hyQ) (inv_mem hq)⟩ =
        π ⟨l * X g2b y' * l⁻¹, hyQ⟩ := by
      have e3 : (⟨q * (l * X g2b y' * l⁻¹) * q⁻¹, mul_mem (mul_mem hq hyQ) (inv_mem hq)⟩ :
          g2LongRadical K) = ⟨q, hq⟩ * ⟨_, hyQ⟩ * (⟨q, hq⟩ : g2LongRadical K)⁻¹ := rfl
      rw [e3, map_mul, map_mul, map_inv, mul_comm (π ⟨q, hq⟩), mul_assoc, mul_inv_cancel, mul_one]
    have e1 : (⟨q * (l * X g2b y' * l⁻¹) * q⁻¹, mul_mem (mul_mem hq hyQ) (inv_mem hq)⟩ :
        g2LongRadical K) = ⟨_, g2N_mem_g2LongRadical 0 0 0 y z⟩ := Subtype.ext h2
    have e2 : (⟨l * X g2b y' * l⁻¹, hyQ⟩ : g2LongRadical K) =
        ⟨_, g2N_mem_g2LongRadical (T v 0) (T v 1) (T v 2) (T v 3) F'⟩ := Subtype.ext hF'
    rw [e1, e2, hπ, hπ] at h3
    have h4 := congrFun (congrArg Multiplicative.toAdd h3) 0
    simp only [toAdd_ofAdd] at h4
    have h5 : T v 0 = ((t ^ (-3 : ℤ) : Kˣ) : K) * y' := by
      simp [hT, hv, radDiag, radMr, radSwap]
    rw [h5] at h4
    exact hy' (by simpa using h4.symm)

omit
  [CharP K 2] in
theorem g2N_bc_eq (y z : K) : g2N 0 0 0 0 y z = X g2b y * X g2c z := by
  simp [g2N, pinnedX_zero]

theorem g2N_bc_mul (y z y' z' : K) :
    g2N 0 0 0 0 y z * g2N 0 0 0 0 y' z' = g2N 0 0 0 0 (y + y') (z + z') := by
  rw [g2N_zero_mul_g2N_zero]
  exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) rfl (by ring)

omit
  [CharP K 2] in
theorem entrywise_g2N_bc (σ : K ≃+* K) (y z : K) :
    Units.map (entrywiseHom σ.toRingHom) (g2N 0 0 0 0 y z) = g2N 0 0 0 0 (σ y) (σ z) := by
  rw [g2N_bc_eq, g2N_bc_eq, map_mul]
  congr 1
  · exact Units.ext (entrywise_pinnedX σ.toRingHom g2b y)
  · exact Units.ext (entrywise_pinnedX σ.toRingHom g2c z)

theorem fix_g2BCGroup_of_fix [Finite K] (hK : Nat.card K = 4) {H : Subgroup (ModGL .G2 K)}
    (hHZ : H ≤ g2BCGroup K) (hH8 : 8 ≤ Nat.card H) (hc1 : X g2c 1 ∈ H)
    (α : MulAut ↥(adjointGroup .G2 K))
    (hα : ∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ H → α z = z) :
    ∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ g2BCGroup K → α z = z := by
  have hK4 : 4 ≤ Nat.card K := hK.ge
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (even_G2_exact_automorphism_normal_form (f := 2) le_rfl K
    (by rw [hK]; norm_num)).1 α
  have hZ₀C : g2BCGroup K ≤ adjointGroup .G2 K :=
    g2BCGroup_le_g2ShortParabolicRadical.trans g2ShortParabolicRadical_le_adjointGroup
  have hαZ : ∀ (y z : K) (hm : g2N 0 0 0 0 y z ∈ adjointGroup .G2 K),
      ((α ⟨_, hm⟩ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
        (g : ModGL .G2 K) * g2N 0 0 0 0 (σ y) (σ z) * (g : ModGL .G2 K)⁻¹ := by
    intro y z hm
    rw [hgσ ⟨_, hm⟩]
    change (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (g2N 0 0 0 0 y z) *
      (g : ModGL .G2 K)⁻¹ = _
    rw [entrywise_g2N_bc]
  have hc1' : g2N 0 0 0 0 0 1 ∈ H := by
    rw [← pinnedX_c_eq_g2N]
    exact hc1
  have hm1 : g2N (0 : K) 0 0 0 0 1 ∈ adjointGroup .G2 K := hZ₀C (hHZ hc1')
  have h1 := hαZ 0 1 hm1
  rw [hα ⟨_, hm1⟩ hc1', map_zero, map_one] at h1
  change g2N 0 0 0 0 0 1 = _ at h1
  have hg : (g : ModGL .G2 K) ∈ adjointGroup .G2 K ⊓
      centralizer ({X g2c 1} : Set (ModGL .G2 K)) := by
    refine mem_inf.mpr ⟨g.2, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [pinnedX_c_eq_g2N]
    calc (g : ModGL .G2 K) * g2N (0 : K) 0 0 0 0 1 =
        (g : ModGL .G2 K) * g2N (0 : K) 0 0 0 0 1 * (g : ModGL .G2 K)⁻¹ * (g : ModGL .G2 K) := by
          group
      _ = g2N (0 : K) 0 0 0 0 1 * (g : ModGL .G2 K) := by rw [← h1]
  have hgL : (g : ModGL .G2 K) ∈ g2LongCent K := hg
  obtain ⟨-, hcent⟩ := g2Centr184 K hK4
  have hgc : ∀ s : K, (g : ModGL .G2 K) * X g2c s = X g2c s * g := by
    intro s
    have h2 : X g2c s ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
      rw [hcent]
      exact mem_rootSubgroup.mpr ⟨s, rfl⟩
    exact mem_centralizer_iff.mp (mem_inf.mp h2).2 _ hgL
  have hrel : ∀ y z : K, g2N 0 0 0 0 y z ∈ H →
      (g : ModGL .G2 K) * X g2b (σ y) * (g : ModGL .G2 K)⁻¹ = g2N 0 0 0 0 y (z + σ z) := by
    intro y z hyz
    have hm := hZ₀C (hHZ hyz)
    have h2 := hαZ y z hm
    rw [hα ⟨_, hm⟩ hyz] at h2
    change g2N 0 0 0 0 y z = _ at h2
    have hcc : X g2c (σ z) * X g2c (σ z) = 1 := pinnedX_mul_self g2c (σ z)
    have hinv : (g : ModGL .G2 K)⁻¹ * X g2c (σ z) = X g2c (σ z) * (g : ModGL .G2 K)⁻¹ :=
      (Commute.inv_left (hgc (σ z) : Commute (g : ModGL .G2 K) (X g2c (σ z)))).eq
    rw [← g2N_mul_c, h2, g2N_bc_eq]
    calc (g : ModGL .G2 K) * X g2b (σ y) * (g : ModGL .G2 K)⁻¹ =
        (g : ModGL .G2 K) * X g2b (σ y) *
          ((g : ModGL .G2 K)⁻¹ * (X g2c (σ z) * X g2c (σ z))) := by rw [hcc, mul_one]
      _ = (g : ModGL .G2 K) * X g2b (σ y) * ((g : ModGL .G2 K)⁻¹ * X g2c (σ z)) *
          X g2c (σ z) := by group
      _ = (g : ModGL .G2 K) * X g2b (σ y) * (X g2c (σ z) * (g : ModGL .G2 K)⁻¹) *
          X g2c (σ z) := by rw [hinv]
      _ = (g : ModGL .G2 K) * (X g2b (σ y) * X g2c (σ z)) * (g : ModGL .G2 K)⁻¹ *
          X g2c (σ z) := by group
  have hmain : (∀ t : K, σ t = t) ∧
      ∀ y : K, (g : ModGL .G2 K) * X g2b y * (g : ModGL .G2 K)⁻¹ = X g2b y := by
    by_cases hXc : ∀ t : K, g2N 0 0 0 0 0 t ∈ H
    ·
      have hσ : ∀ t : K, σ t = t := by
        intro t
        have h2 := hrel 0 t (hXc t)
        rw [map_zero, pinnedX_zero, mul_one, mul_inv_cancel, ← g2N_zero] at h2
        obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective h2
        exact (eq_neg_of_add_eq_zero_right h6.symm).trans (CharTwo.neg_eq t)
      obtain ⟨y₀, z₀, hy₀, hmem₀⟩ : ∃ y z : K, y ≠ 0 ∧ g2N 0 0 0 0 y z ∈ H := by
        by_contra hcon
        push Not at hcon
        have hsub : (H : Set (ModGL .G2 K)) ⊆ Set.range (fun z : K => g2N (0 : K) 0 0 0 0 z) := by
          intro h hh
          obtain ⟨y, z, rfl⟩ := hHZ hh
          by_cases hy : y = 0
          · exact ⟨z, by rw [hy]⟩
          · exact absurd hh (hcon y z hy)
        have hinj : Function.Injective (fun z : K => g2N (0 : K) 0 0 0 0 z) := fun z z' h => by
          obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective h
          exact h6
        have h2 : Nat.card H ≤ Nat.card K := by
          calc Nat.card H = Nat.card (H : Set (ModGL .G2 K)) := rfl
            _ ≤ Nat.card (Set.range (fun z : K => g2N (0 : K) 0 0 0 0 z)) :=
              Nat.card_mono (Set.finite_range _) hsub
            _ = Nat.card K := Nat.card_range_of_injective hinj
        omega
      have h2 := hrel y₀ z₀ hmem₀
      rw [hσ, hσ, CharTwo.add_self_eq_zero] at h2
      obtain ⟨-, B, hB⟩ := conj_b_of_mem_longCent hK hg hy₀ h2
      have hB0 : B = 0 := by
        obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective ((hB y₀).symm.trans h2)
        exact (mul_eq_zero.mp h6).resolve_right hy₀
      refine ⟨hσ, fun y => ?_⟩
      rw [hB y, hB0, zero_mul, pinnedX_b_eq_g2N]
    ·
      push Not at hXc
      obtain ⟨t₀, ht₀⟩ := hXc
      have hcomm : ∀ a ∈ g2BCGroup K, ∀ b ∈ g2BCGroup K, a * b = b * a := by
        rintro _ ⟨y, z, rfl⟩ _ ⟨y', z', rfl⟩
        rw [g2N_bc_mul, g2N_bc_mul, add_comm y, add_comm z]
      set Xc := rootSubgroup .G2 K g2c with hXcdef
      have hXcZ : Xc ≤ g2BCGroup K := fun w hw => by
        obtain ⟨t, rfl⟩ := mem_rootSubgroup.mp hw
        exact pinnedX_c_mem_g2BCGroup t
      have hHN : H ≤ normalizer (Xc : Set (ModGL .G2 K)) := fun h hh =>
        centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw =>
          hcomm _ (hXcZ hw) _ (hHZ hh))
      have hXcN : Xc ≤ normalizer (H : Set (ModGL .G2 K)) := fun w hw =>
        centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh =>
          hcomm _ (hHZ hh) _ (hXcZ hw))
      have hXcard : Nat.card Xc = 4 := by
        rw [← hK]
        exact (Nat.card_congr (rootSubgroupEquiv (τ := .G2) (R := K) g2c).toEquiv).symm
      have hZcard : Nat.card (g2BCGroup K) = 16 := by
        rw [card_g2BCGroup, hK]
      have hinf : Nat.card (Xc ⊓ H : Subgroup (ModGL .G2 K)) ≤ 2 := by
        have hlt : Xc ⊓ H < Xc := lt_of_le_of_ne inf_le_left fun heq => ht₀ (by
          have h3 : X g2c t₀ ∈ Xc ⊓ H := by
            rw [heq]
            exact mem_rootSubgroup.mpr ⟨t₀, rfl⟩
          rw [← pinnedX_c_eq_g2N]
          exact h3.2)
        have h3 := Subgroup.card_lt_of_lt hlt
        have h4 := Subgroup.card_dvd_of_le (inf_le_left : Xc ⊓ H ≤ Xc)
        rw [hXcard] at h3 h4
        have h5 : Nat.card (Xc ⊓ H : Subgroup (ModGL .G2 K)) ≠ 0 := Nat.card_pos.ne'
        interval_cases h : Nat.card (Xc ⊓ H : Subgroup (ModGL .G2 K)) <;> omega
      have hsup : Xc ⊔ H = g2BCGroup K := by
        have : Finite (g2BCGroup K) := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
        have h3 := card_sup_mul_card_inf hHN
        rw [hXcard] at h3
        refine Subgroup.eq_of_le_of_card_ge (sup_le hXcZ hHZ) ?_
        rw [hZcard]
        nlinarith
      have hsurj : ∀ y : K, ∃ z : K, g2N 0 0 0 0 y z ∈ H := by
        intro y
        have hy : g2N 0 0 0 0 y 0 ∈ ((Xc ⊔ H : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := by
          rw [hsup]
          exact ⟨y, 0, rfl⟩
        rw [coe_mul_of_left_le_normalizer_right Xc H hXcN, Set.mem_mul] at hy
        obtain ⟨w, hw, h, hh, hwh⟩ := hy
        obtain ⟨t, rfl⟩ := mem_rootSubgroup.mp hw
        refine ⟨t, ?_⟩
        have e : g2N 0 0 0 0 y t = X g2c t * g2N 0 0 0 0 y 0 := by
          rw [hcomm _ (pinnedX_c_mem_g2BCGroup t) _ ⟨y, 0, rfl⟩, g2N_mul_c, zero_add]
        rw [e, ← hwh, ← mul_assoc, pinnedX_mul_self, one_mul]
        exact hh
      have hσ : ∀ y : K, σ y = y := by
        intro y
        by_cases hy : y = 0
        · rw [hy, map_zero]
        obtain ⟨z, hz⟩ := hsurj y
        exact (conj_b_of_mem_longCent hK hg ((map_ne_zero σ).mpr hy) (hrel y z hz)).1.symm
      refine ⟨hσ, fun y => ?_⟩
      obtain ⟨z, hz⟩ := hsurj y
      have h2 := hrel y z hz
      rw [hσ, hσ, CharTwo.add_self_eq_zero, ← pinnedX_b_eq_g2N] at h2
      exact h2
  obtain ⟨hσ, hgb⟩ := hmain
  intro w hw
  obtain ⟨y, z, hyz⟩ := hw
  have hm : g2N 0 0 0 0 y z ∈ adjointGroup .G2 K := hyz ▸ w.2
  have e : w = ⟨g2N 0 0 0 0 y z, hm⟩ := Subtype.ext hyz
  subst e
  apply Subtype.ext
  have h2 := hαZ y z hm
  rw [hσ, hσ] at h2
  change ((α ⟨g2N 0 0 0 0 y z, hm⟩ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = g2N 0 0 0 0 y z
  rw [h2, g2N_bc_eq]
  calc (g : ModGL .G2 K) * (X g2b y * X g2c z) * (g : ModGL .G2 K)⁻¹ =
      ((g : ModGL .G2 K) * X g2b y * (g : ModGL .G2 K)⁻¹) *
        ((g : ModGL .G2 K) * X g2c z * (g : ModGL .G2 K)⁻¹) := by group
    _ = X g2b y * X g2c z := by rw [hgb, hgc z, mul_inv_cancel_right]

theorem eq_conj_of_fix [Finite K] (hK : Nat.card K = 4) {H : Subgroup (ModGL .G2 K)}
    (hHZ : H ≤ g2BCGroup K) (hH8 : 8 ≤ Nat.card H) (α : MulAut ↥(adjointGroup .G2 K))
    (hα : ∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ H → α z = z) :
    ∃ c : ↥(adjointGroup .G2 K), (c : ModGL .G2 K) ∈ g2ShortParabolicRadical K ⊔ g2TorusR K ∧
      α = MulAut.conj c := by
  obtain ⟨h₀, hh₀, hh₀1⟩ : ∃ h₀ ∈ H, h₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : H = ⊥ := eq_bot_iff.mpr fun h hh => (mem_bot).mpr (hcon h hh)
    rw [hbot, card_bot] at hH8
    omega
  have hXc1 : X g2c 1 ≠ 1 := by
    intro h
    rw [← pinnedX_zero (τ := .G2) (R := K) g2c] at h
    exact one_ne_zero (pinnedX_injective .G2 K g2c h)
  obtain ⟨l, hl, hll⟩ := exists_conj_eq_of_mem_g2BCGroup (hHZ hh₀) (pinnedX_c_mem_g2BCGroup 1)
    hh₀1 hXc1
  have hlC : l ∈ adjointGroup .G2 K := g2RankOne_le_adjointGroup g2ia hl
  set lC : ↥(adjointGroup .G2 K) := ⟨l, hlC⟩ with hlCdef
  set H' : Subgroup (ModGL .G2 K) := H.map (MulAut.conj l).toMonoidHom with hH'
  set α' : MulAut ↥(adjointGroup .G2 K) := MulAut.conj lC * α * (MulAut.conj lC)⁻¹ with hα'
  have hLZ : g2RankOne K g2ia ≤ normalizer (g2BCGroup K : Set (ModGL .G2 K)) :=
    g2RankOne_a_le_normalizer
  have hH'Z : H' ≤ g2BCGroup K := by
    rintro _ ⟨h, hh, rfl⟩
    exact (mem_normalizer_iff.mp (hLZ hl) h).mp (hHZ hh)
  have hH'8 : 8 ≤ Nat.card H' := by
    rw [hH', card_map_of_injective (MulAut.conj l).injective]
    exact hH8
  have hc1 : X g2c 1 ∈ H' := ⟨h₀, hh₀, hll⟩
  have hα'H : ∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ H' → α' z = z := by
    rintro z ⟨h, hh, hzh⟩
    have hhC : h ∈ adjointGroup .G2 K := by
      have : h = l⁻¹ * (z : ModGL .G2 K) * l := by
        rw [← hzh]
        change h = l⁻¹ * (l * h * l⁻¹) * l
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hlC) z.2) hlC
    have hz : z = lC * ⟨h, hhC⟩ * lC⁻¹ := Subtype.ext (by
      rw [← hzh]
      rfl)
    have e1 : α' z = lC * α (lC⁻¹ * z * lC) * lC⁻¹ := rfl
    have e2 : lC⁻¹ * z * lC = ⟨h, hhC⟩ := by
      rw [hz]
      group
    rw [e1, e2, hα ⟨h, hhC⟩ hh, hz]
  have hfix := fix_g2BCGroup_of_fix hK hH'Z hH'8 hc1 α' hα'H
  obtain ⟨c', hc', hα'c⟩ := eq_conj_of_forall_mem_g2BCGroup hK α' hfix
  refine ⟨lC⁻¹ * c' * lC, ?_, ?_⟩
  ·
    have hlD : l⁻¹ ∈ normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) :=
      g2Para_le_normalizer (inv_mem (show l ∈ g2Para K from mem_sup_left (mem_sup_right hl)))
    have hlT : ∀ u ∈ g2TorusR K, l⁻¹ * u * l = u := fun u hu => by
      have := mem_centralizer_iff.mp (g2TorusR_le_centralizer_g2RankOne hK hu) l hl
      calc l⁻¹ * u * l = l⁻¹ * (u * l) := by group
        _ = l⁻¹ * (l * u) := by rw [this]
        _ = u := by group
    have hmap : (g2ShortParabolicRadical K ⊔ g2TorusR K).map (MulAut.conj l⁻¹).toMonoidHom ≤
        g2ShortParabolicRadical K ⊔ g2TorusR K := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨d, hd, rfl⟩
        exact (mem_normalizer_iff.mp hlD d).mp hd
      · rintro _ ⟨u, hu, rfl⟩
        change l⁻¹ * u * l⁻¹⁻¹ ∈ _
        rw [inv_inv, hlT u hu]
        exact hu
    have h3 : ((lC⁻¹ * c' * lC : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
        (MulAut.conj l⁻¹).toMonoidHom (c' : ModGL .G2 K) := by
      change l⁻¹ * (c' : ModGL .G2 K) * l = l⁻¹ * (c' : ModGL .G2 K) * l⁻¹⁻¹
      rw [inv_inv]
    rw [h3]
    exact hmap ⟨_, hc', rfl⟩
  ·
    have e : α = (MulAut.conj lC)⁻¹ * α' * MulAut.conj lC := by
      rw [hα']
      group
    rw [e, hα'c, ← map_inv, ← map_mul, ← map_mul]

end CFSG.ComponentClassification.AS81.G2
