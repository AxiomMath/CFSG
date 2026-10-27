module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Eigen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup

variable {X : Type*} [Group X]

namespace EigenBasis

variable {Y L : Subgroup X} {σ : Multiplicative (Fin 3 → ZMod 3) →* X} {l : Fin 3 → X}

theorem card_range (E : EigenBasis Y L σ l) : Nat.card Y = 27 := by
  let f : Multiplicative (Fin 3 → ZMod 3) → Y := fun a =>
    ⟨σ a, by rw [← E.range_eq]; exact MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact E.inj (Subtype.ext_iff.mp hab)
    · intro y
      have hy : (y : X) ∈ σ.range := by rw [E.range_eq]; exact y.2
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hy
      exact ⟨a, Subtype.ext ha⟩
  calc Nat.card Y = Nat.card (Multiplicative (Fin 3 → ZMod 3)) :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = 27 := by simp [Nat.card_eq_fintype_card]

theorem le_normalizer (E : EigenBasis Y L σ l) (hL2 : ∀ s ∈ L, s * s = 1) :
    L ≤ normalizer (Y : Set X) := by
  have hcl : Subgroup.closure (Set.range l) = L := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro - ⟨i, rfl⟩
      exact E.l_mem i
    · exact E.gen
  rw [← hcl, Subgroup.closure_le]
  rintro - ⟨i, rfl⟩
  change l i ∈ normalizer (Y : Set X)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨c, hc⟩ := E.mem_iff.mp hy
    rw [← hc, E.act i c]
    exact E.mem_iff.mpr ⟨negAt i c, rfl⟩
  · intro hy
    have hsq : l i * l i = 1 := hL2 (l i) (E.l_mem i)
    obtain ⟨c, hc⟩ := E.mem_iff.mp hy
    have hforward : l i * (l i * y * (l i)⁻¹) * (l i)⁻¹ ∈ Y := by
      rw [← hc, E.act i c]
      exact E.mem_iff.mpr ⟨negAt i c, rfl⟩
    have hy' : l i * (l i * y * (l i)⁻¹) * (l i)⁻¹ = y := by
      have hlinv : (l i)⁻¹ = l i := inv_eq_of_mul_eq_one_left hsq
      rw [hlinv]
      calc l i * (l i * y * l i) * l i = (l i * l i) * y * (l i * l i) := by group
        _ = y := by rw [hsq, one_mul, mul_one]
    rwa [hy'] at hforward

theorem disjoint (E : EigenBasis Y L σ l) (hL : Nat.card L = 8)
    (hL2 : ∀ s ∈ L, s * s = 1) : Disjoint Y L := by
  rw [disjoint_iff, eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  rw [Subgroup.mem_bot]
  have h27 : orderOf y ∣ 27 := by
    simpa [E.card_range] using Subgroup.orderOf_dvd_natCard Y hy.1
  have h2 : orderOf y ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using hL2 y hy.2
  have hone : orderOf y = 1 := by
    have h : orderOf y ∣ Nat.gcd 27 2 := Nat.dvd_gcd h27 h2
    rw [show Nat.gcd 27 2 = 1 from by norm_num] at h
    exact Nat.dvd_one.mp h
  exact orderOf_eq_one_iff.mp hone

theorem card_sup (E : EigenBasis Y L σ l) (hL : Nat.card L = 8)
    (hL2 : ∀ s ∈ L, s * s = 1) : Nat.card ↥(Y ⊔ L) = 216 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y L
    (E.le_normalizer hL2) (E.disjoint hL hL2), E.card_range, hL]

theorem sigma_single_eq_pow (E : EigenBasis Y L σ l) (i : Fin 3) (s : ZMod 3) :
    σ (Multiplicative.ofAdd (Pi.single i s)) = eb σ i ^ s.val := by
  have h : (Pi.single i s : Fin 3 → ZMod 3) =
      s.val • (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) :=
    single_eq_nsmul_single i s
  calc σ (Multiplicative.ofAdd (Pi.single i s))
      = σ (Multiplicative.ofAdd
          (s.val • (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3))) := by rw [h]
    _ = σ ((Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3)) ^ s.val) := by
        rw [ofAdd_nsmul]
    _ = (σ (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3))) ^ s.val :=
        map_pow σ _ _
    _ = eb σ i ^ s.val := rfl

theorem pow_sigma_single (E : EigenBasis Y L σ l) (i : Fin 3) (s t : ZMod 3) :
    σ (Multiplicative.ofAdd (Pi.single i s)) ^ t.val =
      σ (Multiplicative.ofAdd (Pi.single i (t * s))) := by
  rw [← map_pow, ← ofAdd_nsmul]
  apply congrArg σ
  apply Multiplicative.ofAdd.injective
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ← Pi.single_smul, smul_eq_mul,
    ZMod.natCast_zmod_val]

theorem conj_l_single (E : EigenBasis Y L σ l) (i : Fin 3) (s : ZMod 3) :
    l i * σ (Multiplicative.ofAdd (Pi.single i s)) * (l i)⁻¹ =
      (σ (Multiplicative.ofAdd (Pi.single i s)))⁻¹ := by
  have hneg : negAt i (Pi.single i s) = -(Pi.single i s : Fin 3 → ZMod 3) := by
    funext j
    by_cases h : j = i
    · subst h
      rw [negAt, Function.update_self, Pi.neg_apply, Pi.single_eq_same]
      rfl
    · rw [negAt, Function.update_of_ne h, Pi.neg_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) h s]
      exact neg_zero.symm
  calc l i * σ (Multiplicative.ofAdd (Pi.single i s)) * (l i)⁻¹
      = σ (Multiplicative.ofAdd (negAt i (Pi.single i s))) := E.act i _
    _ = σ (Multiplicative.ofAdd (-(Pi.single i s : Fin 3 → ZMod 3))) := by rw [hneg]
    _ = σ ((Multiplicative.ofAdd (Pi.single i s))⁻¹) := by rw [ofAdd_neg]
    _ = (σ (Multiplicative.ofAdd (Pi.single i s)))⁻¹ := map_inv σ _

theorem conj_l_single_of_ne (E : EigenBasis Y L σ l) {i j : Fin 3} (hij : j ≠ i)
    (s : ZMod 3) :
    l i * σ (Multiplicative.ofAdd (Pi.single j s)) * (l i)⁻¹ =
      σ (Multiplicative.ofAdd (Pi.single j s)) := by
  have hfix : negAt i (Pi.single j s) = Pi.single j s := by
    funext k
    by_cases hk : k = i
    · subst hk
      rw [negAt, Function.update_self,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij) s]
      exact neg_zero
    · rw [negAt, Function.update_of_ne hk]
  calc l i * σ (Multiplicative.ofAdd (Pi.single j s)) * (l i)⁻¹
      = σ (Multiplicative.ofAdd (negAt i (Pi.single j s))) := E.act i _
    _ = σ (Multiplicative.ofAdd (Pi.single j s)) := by rw [hfix]

end EigenBasis

namespace MonomialSetup

variable {M Y L : Subgroup X}

private structure Setup (M Y L : Subgroup X) where
  σ : Multiplicative (Fin 3 → ZMod 3) →* X
  l : Fin 3 → X
  E : EigenBasis Y L σ l
  card_L : Nat.card L = 8
  sq_L : ∀ s ∈ L, s * s = 1
  le_M_Y : Y ≤ M
  le_M_L : L ≤ M
  normalizes : ∀ x ∈ M, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y
  centralizes : ∀ x ∈ M, (∀ y ∈ Y, x * y = y * x) → x ∈ Y
  F : X → Prop
  F_conj : ∀ x ∈ M, ∀ y, F y → F (x * y * x⁻¹)
  F_iff : ∀ c : Fin 3 → ZMod 3, F (σ (Multiplicative.ofAdd c)) ↔
    ∃ i, c i ≠ 0 ∧ ∀ j, j ≠ i → c j = 0

variable {S : Setup M Y L}

private theorem line_exists (S : Setup M Y L) (x : M) (i : Fin 3) :
    ∃ p : Fin 3 × ZMod 3, p.2 ≠ 0 ∧
      (x : X) * eb S.σ i * (x : X)⁻¹ =
        S.σ (Multiplicative.ofAdd (Pi.single p.1 p.2)) := by
  have hmemY : (x : X) * eb S.σ i * (x : X)⁻¹ ∈ Y :=
    S.normalizes x x.2 (eb S.σ i) (S.E.eb_mem i)
  obtain ⟨c, hc⟩ := S.E.mem_iff.mp hmemY
  have hFeb : S.F (eb S.σ i) := by
    have h := (S.F_iff (Pi.single i 1)).mpr
      ⟨i, by simp, by
        intro j hj
        exact Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj 1⟩
    simpa [eb] using h
  have hFc : S.F (S.σ (Multiplicative.ofAdd c)) := by
    rw [hc]
    exact S.F_conj x x.2 (eb S.σ i) hFeb
  obtain ⟨j, hjne, hjsupp⟩ := (S.F_iff c).mp hFc
  refine ⟨(j, c j), hjne, ?_⟩
  rw [← hc]
  have hsingle : c = Pi.single j (c j) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [hjsupp k hk, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk (c j)]
  conv_lhs => rw [hsingle]

private noncomputable def lineP (S : Setup M Y L) (x : M) (i : Fin 3) :
    Fin 3 × ZMod 3 := Classical.choose (line_exists S x i)

private noncomputable def lineIdx (S : Setup M Y L) (x : M) (i : Fin 3) : Fin 3 :=
  (lineP S x i).1

private noncomputable def lineVal (S : Setup M Y L) (x : M) (i : Fin 3) : ZMod 3 :=
  (lineP S x i).2

private theorem lineIdx_spec (S : Setup M Y L) (x : M) (i : Fin 3) :
    lineVal S x i ≠ 0 ∧
      (x : X) * eb S.σ i * (x : X)⁻¹ =
        S.σ (Multiplicative.ofAdd (Pi.single (lineIdx S x i) (lineVal S x i))) :=
  Classical.choose_spec (line_exists S x i)

private theorem line_unique (S : Setup M Y L) {j j' : Fin 3} {s s' : ZMod 3}
    (hs : s ≠ 0) (hs' : s' ≠ 0)
    (h : S.σ (Multiplicative.ofAdd (Pi.single j s)) =
      S.σ (Multiplicative.ofAdd (Pi.single j' s'))) :
    j = j' ∧ s = s' := by
  have h1 : (Pi.single j s : Fin 3 → ZMod 3) = Pi.single j' s' := by
    apply Multiplicative.ofAdd.injective
    exact S.E.inj h
  have hj := congrFun h1 j
  rw [Pi.single_eq_same] at hj
  by_cases hjj : j = j'
  · subst hjj
    exact ⟨rfl, by simpa using hj⟩
  · exfalso
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjj s'] at hj
    exact hs hj

private theorem lineIdx_unique (S : Setup M Y L) {x : M} {i j : Fin 3}
    {s : ZMod 3} (hs : s ≠ 0)
    (h : (x : X) * eb S.σ i * (x : X)⁻¹ =
      S.σ (Multiplicative.ofAdd (Pi.single j s))) :
    lineIdx S x i = j ∧ lineVal S x i = s :=
  line_unique S (lineIdx_spec S x i).1 hs ((lineIdx_spec S x i).2.symm.trans h)

private theorem conj_single (S : Setup M Y L) (x : M) (i : Fin 3) (s : ZMod 3) :
    (x : X) * S.σ (Multiplicative.ofAdd (Pi.single i s)) * (x : X)⁻¹ =
      S.σ (Multiplicative.ofAdd
        (Pi.single (lineIdx S x i) (lineVal S x i * s))) := by
  calc (x : X) * S.σ (Multiplicative.ofAdd (Pi.single i s)) * (x : X)⁻¹
      = (x : X) * (eb S.σ i ^ s.val) * (x : X)⁻¹ := by rw [S.E.sigma_single_eq_pow]
    _ = ((x : X) * eb S.σ i * (x : X)⁻¹) ^ s.val := by rw [← conj_pow]
    _ = (S.σ (Multiplicative.ofAdd
          (Pi.single (lineIdx S x i) (lineVal S x i)))) ^ s.val := by
        rw [(lineIdx_spec S x i).2]
    _ = S.σ (Multiplicative.ofAdd
          (Pi.single (lineIdx S x i) (s * lineVal S x i))) := by
        rw [S.E.pow_sigma_single]
    _ = S.σ (Multiplicative.ofAdd
          (Pi.single (lineIdx S x i) (lineVal S x i * s))) := by
        rw [mul_comm]

private theorem comm_of_eb (S : Setup M Y L) {w : X}
    (hw : ∀ i, w * eb S.σ i = eb S.σ i * w) :
    ∀ y ∈ Y, w * y = y * w := by
  intro y hy
  obtain ⟨c, hc⟩ := S.E.mem_iff.mp hy
  rw [← hc, S.E.apply_eq_eprod]
  unfold CFSG.GroupTheory.DiagonalTwentySeven.eprod
  have h0 : Commute w (eb S.σ 0) := hw 0
  have h1 : Commute w (eb S.σ 1) := hw 1
  have h2 : Commute w (eb S.σ 2) := hw 2
  exact ((h0.pow_right (c 0).val).mul_right (h1.pow_right (c 1).val)).mul_right
    (h2.pow_right (c 2).val) |>.eq

private theorem lineIdx_inv (S : Setup M Y L) (x : M) (i : Fin 3) :
    lineIdx S x⁻¹ (lineIdx S x i) = i := by
  have h1 := conj_single S x⁻¹ (lineIdx S x i) (lineVal S x i)
  have h2 : ((x⁻¹ : M) : X) * S.σ (Multiplicative.ofAdd
      (Pi.single (lineIdx S x i) (lineVal S x i))) * (((x⁻¹ : M) : X))⁻¹ = eb S.σ i := by
    rw [← (lineIdx_spec S x i).2]
    simp only [Subgroup.coe_inv]
    group
  have h3 : S.σ (Multiplicative.ofAdd
        (Pi.single (lineIdx S x⁻¹ (lineIdx S x i))
          (lineVal S x⁻¹ (lineIdx S x i) * lineVal S x i))) =
      S.σ (Multiplicative.ofAdd (Pi.single i 1)) := by
    rw [← h1, h2]
    rfl
  exact (line_unique S (mul_ne_zero (lineIdx_spec S x⁻¹ _).1 (lineIdx_spec S x i).1)
    (by decide) h3).1

private theorem lineIdx_inv' (S : Setup M Y L) (x : M) (i : Fin 3) :
    lineIdx S x (lineIdx S x⁻¹ i) = i := by
  simpa using lineIdx_inv S x⁻¹ i

private noncomputable def toPerm (S : Setup M Y L) (x : M) : Equiv.Perm (Fin 3) where
  toFun := lineIdx S x
  invFun := lineIdx S x⁻¹
  left_inv := lineIdx_inv S x
  right_inv := lineIdx_inv' S x

private theorem lineIdx_mul (S : Setup M Y L) (x y : M) (i : Fin 3) :
    lineIdx S (x * y) i = lineIdx S x (lineIdx S y i) := by
  have h1 : ((x * y : M) : X) * eb S.σ i * ((x * y : M) : X)⁻¹ =
      S.σ (Multiplicative.ofAdd (Pi.single (lineIdx S x (lineIdx S y i))
        (lineVal S x (lineIdx S y i) * lineVal S y i))) := by
    calc ((x * y : M) : X) * eb S.σ i * ((x * y : M) : X)⁻¹
        = (x : X) * ((y : X) * eb S.σ i * (y : X)⁻¹) * (x : X)⁻¹ := by
            simp only [Subgroup.coe_mul]
            group
      _ = (x : X) * S.σ (Multiplicative.ofAdd
            (Pi.single (lineIdx S y i) (lineVal S y i))) * (x : X)⁻¹ := by
            rw [(lineIdx_spec S y i).2]
      _ = S.σ (Multiplicative.ofAdd (Pi.single (lineIdx S x (lineIdx S y i))
            (lineVal S x (lineIdx S y i) * lineVal S y i))) :=
            conj_single S x (lineIdx S y i) (lineVal S y i)
  exact (lineIdx_unique S (mul_ne_zero (lineIdx_spec S x _).1
    (lineIdx_spec S y i).1) h1).1

private theorem toPerm_mul (S : Setup M Y L) (x y : M) :
    toPerm S (x * y) = toPerm S x * toPerm S y := by
  apply Equiv.ext
  intro i
  simpa [toPerm, Equiv.Perm.mul_apply] using lineIdx_mul S x y i

private noncomputable def perm (S : Setup M Y L) : M →* Equiv.Perm (Fin 3) where
  toFun := toPerm S
  map_one' := by
    apply Equiv.ext
    intro i
    have h1 : ((1 : M) : X) * eb S.σ i * ((1 : M) : X)⁻¹ = eb S.σ i := by simp
    have := (lineIdx_unique S (x := 1) (i := i) (j := i) (s := 1) (by decide)
      (by simpa [eb] using h1)).1
    simpa [toPerm] using this
  map_mul' := toPerm_mul S

private theorem perm_eq_one_of_mem_Y (S : Setup M Y L) {x : M} (hx : (x : X) ∈ Y) :
    perm S x = 1 := by
  apply Equiv.ext
  intro i
  have hcomm : (x : X) * eb S.σ i = eb S.σ i * (x : X) := S.E.comm hx (S.E.eb_mem i)
  have hconj_eq : (x : X) * eb S.σ i * (x : X)⁻¹ = eb S.σ i := by
    rw [hcomm]
    group
  have := (lineIdx_unique S (x := x) (i := i) (j := i) (s := 1) (by decide)
    (by simpa [eb] using hconj_eq)).1
  simpa [perm, toPerm] using this

private theorem perm_eq_one_of_mem_L (S : Setup M Y L) {x : M} (hx : (x : X) ∈ L) :
    perm S x = 1 := by
  obtain ⟨s, hs, hact⟩ := S.E.diag hx
  apply Equiv.ext
  intro i
  have hmul : s * (Pi.single i 1 : Fin 3 → ZMod 3) = Pi.single i (s i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [Pi.mul_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj (1 : ZMod 3),
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj (s i)]
      simp
  have hconj_eq : (x : X) * eb S.σ i * (x : X)⁻¹ =
      S.σ (Multiplicative.ofAdd (Pi.single i (s i))) := by
    have h := hact (Pi.single i 1)
    rw [hmul] at h
    simpa [eb] using h
  have hsi : s i ≠ 0 := by
    rcases hs i with h | h <;> rw [h] <;> decide
  have := (lineIdx_unique S (x := x) (i := i) (j := i) (s := s i) hsi
    (by simpa [eb] using hconj_eq)).1
  simpa [perm, toPerm] using this

private theorem perm_eq_one_of_mem_sup (S : Setup M Y L) {x : M}
    (hx : (x : X) ∈ Y ⊔ L) : perm S x = 1 := by
  have hLN : L ≤ normalizer (Y : Set X) := S.E.le_normalizer S.sq_L
  have hx' : (x : X) ∈ (↑(Y ⊔ L) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y L hLN, Set.mem_mul] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := hx'
  have hyM : y ∈ M := S.le_M_Y hy
  have hzM : z ∈ M := S.le_M_L hz
  have hxy : x = (⟨y, hyM⟩ : M) * (⟨z, hzM⟩ : M) := Subtype.ext hyz.symm
  rw [hxy, map_mul, perm_eq_one_of_mem_Y S hy, perm_eq_one_of_mem_L S hz, one_mul]

private theorem mem_sup_of_perm_eq_one (S : Setup M Y L) {x : M}
    (hx : perm S x = 1) : (x : X) ∈ Y ⊔ L := by
  have htri : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = -1 := by decide
  have hsign : ∀ i, lineVal S x i = 1 ∨ lineVal S x i = -1 := by
    intro i
    have hne : lineVal S x i ≠ 0 := (lineIdx_spec S x i).1
    rcases htri (lineVal S x i) with h0 | h1 | h1
    · exact absurd h0 hne
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨z, hzL, hzact⟩ := S.E.exists_mem_of_signs (lineVal S x) hsign
  have hzM : z ∈ M := S.le_M_L hzL
  have hxp : ∀ i, lineIdx S x i = i := by
    intro i
    have h := congrArg (fun p : Equiv.Perm (Fin 3) => p i) hx
    simpa [perm, toPerm] using h
  have hz_eq : ∀ i, z * eb S.σ i * z⁻¹ = (x : X) * eb S.σ i * (x : X)⁻¹ := by
    intro i
    have hmul : lineVal S x * (Pi.single i 1 : Fin 3 → ZMod 3) =
        Pi.single i (lineVal S x i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Pi.mul_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj (1 : ZMod 3),
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj (lineVal S x i)]
        simp
    calc z * eb S.σ i * z⁻¹
        = z * S.σ (Multiplicative.ofAdd (Pi.single i 1)) * z⁻¹ := rfl
      _ = S.σ (Multiplicative.ofAdd (lineVal S x * Pi.single i 1)) := hzact (Pi.single i 1)
      _ = S.σ (Multiplicative.ofAdd (Pi.single i (lineVal S x i))) := by rw [hmul]
      _ = (x : X) * eb S.σ i * (x : X)⁻¹ := by
          simpa [hxp i] using ((lineIdx_spec S x i).2).symm
  let wM : M := ⟨z⁻¹ * (x : X), M.mul_mem (M.inv_mem hzM) x.2⟩
  have hwconj : ∀ i, (wM : X) * eb S.σ i * (wM : X)⁻¹ = eb S.σ i := by
    intro i
    have hzi := hz_eq i
    calc (wM : X) * eb S.σ i * (wM : X)⁻¹
        = z⁻¹ * ((x : X) * eb S.σ i * (x : X)⁻¹) * z := by
            simp only [wM, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]
            group
      _ = z⁻¹ * (z * eb S.σ i * z⁻¹) * z := by rw [← hzi]
      _ = eb S.σ i := by group
  have hwcomm : ∀ i, (wM : X) * eb S.σ i = eb S.σ i * (wM : X) := by
    intro i
    have h := hwconj i
    calc (wM : X) * eb S.σ i
        = ((wM : X) * eb S.σ i * (wM : X)⁻¹) * (wM : X) := by group
      _ = eb S.σ i * (wM : X) := by rw [h]
  have hwY : (wM : X) ∈ Y := S.centralizes wM wM.2 (comm_of_eb S hwcomm)
  have hx_eq : (x : X) = z * (wM : X) := by
    simp only [wM, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hx_eq]
  exact (Y ⊔ L).mul_mem (Subgroup.mem_sup_right hzL) (Subgroup.mem_sup_left hwY)

private theorem perm_ker_eq (S : Setup M Y L) :
    (perm S).ker = (Y ⊔ L).subgroupOf M := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨mem_sup_of_perm_eq_one S, perm_eq_one_of_mem_sup S⟩

private theorem card_eq (S : Setup M Y L) :
    Nat.card M = 216 * Nat.card (perm S).range := by
  have hsupM : Y ⊔ L ≤ M := sup_le S.le_M_Y S.le_M_L
  have h1 := Subgroup.card_mul_index (perm S).ker
  rw [Subgroup.index_ker, perm_ker_eq S] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsupM).toEquiv,
    S.E.card_sup S.card_L S.sq_L] at h1
  exact h1.symm

private theorem exists_diag (S : Setup M Y L) (x : M) (i : Fin 3) :
    ∃ d : X, d ∈ Y ∧
      (∀ m : Fin 3, m ≠ lineIdx S x i → S.l m * d * (S.l m)⁻¹ = d) ∧
      (x : X) * S.l i * (x : X)⁻¹ = d * S.l (lineIdx S x i) * d⁻¹ := by
  let v : X := (x : X) * S.l i * (x : X)⁻¹
  have hv_mem : v ∈ M := by
    simp only [v]
    exact M.mul_mem (M.mul_mem x.2 (S.le_M_L (S.E.l_mem i))) (M.inv_mem x.2)
  have hv2 : v * v = 1 := by
    have hli : S.l i * S.l i = 1 := S.sq_L (S.l i) (S.E.l_mem i)
    simp only [v]
    calc ((x : X) * S.l i * (x : X)⁻¹) * ((x : X) * S.l i * (x : X)⁻¹)
        = (x : X) * (S.l i * S.l i) * (x : X)⁻¹ := by group
      _ = 1 := by rw [hli]; group
  let u : X := v * S.l (lineIdx S x i)
  have hu_mem : u ∈ M := by
    simp only [u]
    exact M.mul_mem hv_mem (S.le_M_L (S.E.l_mem _))
  have hlk2 : S.l (lineIdx S x i) * S.l (lineIdx S x i) = 1 :=
    S.sq_L _ (S.E.l_mem _)
  have hlinv : (S.l (lineIdx S x i))⁻¹ = S.l (lineIdx S x i) :=
    inv_eq_of_mul_eq_one_left hlk2
  have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hv_action : ∀ j : Fin 3, v * eb S.σ j * v⁻¹ =
      if j = lineIdx S x i then (eb S.σ j)⁻¹ else eb S.σ j := by
    intro j
    let i' : Fin 3 := lineIdx S x⁻¹ j
    let s' : ZMod 3 := lineVal S x⁻¹ j
    have hz : (x : X)⁻¹ * eb S.σ j * ((x : X)⁻¹)⁻¹ =
        S.σ (Multiplicative.ofAdd (Pi.single i' s')) := by
      simpa only [Subgroup.coe_inv] using (lineIdx_spec S x⁻¹ j).2
    by_cases hjk : j = lineIdx S x i
    · have hi' : i' = i := by
        simpa [i', hjk] using lineIdx_inv S x i
      have hzi : (x : X)⁻¹ * eb S.σ j * ((x : X)⁻¹)⁻¹ =
          S.σ (Multiplicative.ofAdd (Pi.single i s')) := by
        simpa [hi'] using hz
      have hvj : v * eb S.σ j * v⁻¹ = (eb S.σ j)⁻¹ := by
        calc v * eb S.σ j * v⁻¹
            = (x : X) * (S.l i * ((x : X)⁻¹ * eb S.σ j * ((x : X)⁻¹)⁻¹) *
                (S.l i)⁻¹) * (x : X)⁻¹ := by
                simp only [v]; group
          _ = (x : X) * (S.σ (Multiplicative.ofAdd (Pi.single i s')))⁻¹ *
                (x : X)⁻¹ := by
                rw [hzi, S.E.conj_l_single i s']
          _ = ((x : X) * S.σ (Multiplicative.ofAdd (Pi.single i s')) *
                (x : X)⁻¹)⁻¹ := by group
          _ = ((x : X) * ((x : X)⁻¹ * eb S.σ j * ((x : X)⁻¹)⁻¹) *
                (x : X)⁻¹)⁻¹ := by rw [hzi]
          _ = (eb S.σ j)⁻¹ := by group
      rw [if_pos hjk]
      exact hvj
    · have hi' : i' ≠ i := by
        intro h
        apply hjk
        calc j = lineIdx S x i' := by
              rw [show i' = lineIdx S x⁻¹ j from rfl]
              exact (lineIdx_inv' S x j).symm
          _ = lineIdx S x i := by rw [h]
      have hvj : v * eb S.σ j * v⁻¹ = eb S.σ j := by
        calc v * eb S.σ j * v⁻¹
            = (x : X) * (S.l i * ((x : X)⁻¹ * eb S.σ j * ((x : X)⁻¹)⁻¹) *
                (S.l i)⁻¹) * (x : X)⁻¹ := by
                simp only [v]; group
          _ = (x : X) * S.σ (Multiplicative.ofAdd (Pi.single i' s')) * (x : X)⁻¹ := by
                rw [hz, S.E.conj_l_single_of_ne hi' s']
          _ = (x : X) * ((x : X)⁻¹ * eb S.σ j * ((x : X)⁻¹)⁻¹) * (x : X)⁻¹ := by
                rw [hz]
          _ = eb S.σ j := by group
      rw [if_neg hjk]
      exact hvj
  have hu_conj : ∀ j : Fin 3, u * eb S.σ j * u⁻¹ = eb S.σ j := by
    intro j
    calc u * eb S.σ j * u⁻¹
        = v * (S.l (lineIdx S x i) * eb S.σ j * (S.l (lineIdx S x i))⁻¹) * v⁻¹ := by
            simp only [u]; group
      _ = eb S.σ j := by
            by_cases hjk : j = lineIdx S x i
            · have hl : S.l (lineIdx S x i) * eb S.σ j * (S.l (lineIdx S x i))⁻¹ =
                  (eb S.σ j)⁻¹ := by
                rw [← hjk]
                simpa [eb] using S.E.conj_l_single j (1 : ZMod 3)
              rw [hl]
              have hvj := hv_action j
              rw [if_pos hjk] at hvj
              calc v * (eb S.σ j)⁻¹ * v⁻¹ = (v * eb S.σ j * v⁻¹)⁻¹ := by group
                _ = ((eb S.σ j)⁻¹)⁻¹ := by rw [hvj]
                _ = eb S.σ j := inv_inv _
            · have hl : S.l (lineIdx S x i) * eb S.σ j * (S.l (lineIdx S x i))⁻¹ =
                  eb S.σ j := by
                simpa [eb] using S.E.conj_l_single_of_ne hjk (1 : ZMod 3)
              rw [hl]
              have hvj := hv_action j
              rw [if_neg hjk] at hvj
              exact hvj
  have hu_comm_eb : ∀ j : Fin 3, u * eb S.σ j = eb S.σ j * u := by
    intro j
    calc u * eb S.σ j = (u * eb S.σ j * u⁻¹) * u := by group
      _ = eb S.σ j * u := by rw [hu_conj j]
  have hu_Y : u ∈ Y := S.centralizes u hu_mem (comm_of_eb S hu_comm_eb)
  obtain ⟨c, hc⟩ := S.E.mem_iff.mp hu_Y
  have hu3 : u ^ 3 = 1 := by
    rw [← hc]
    have h3 : (3 : ℕ) • c = 0 := by
      funext j
      show (3 : ℕ) • c j = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    calc S.σ (Multiplicative.ofAdd c) ^ 3
        = S.σ ((Multiplicative.ofAdd c) ^ 3) := (map_pow _ _ _).symm
      _ = S.σ (Multiplicative.ofAdd (3 • c)) := by rw [ofAdd_nsmul]
      _ = S.σ (Multiplicative.ofAdd (0 : Fin 3 → ZMod 3)) := by rw [h3]
      _ = 1 := by simp
  have hu_inv : S.l (lineIdx S x i) * u * (S.l (lineIdx S x i))⁻¹ = u⁻¹ := by
    rw [hlinv]
    have hu_inv' : S.l (lineIdx S x i) * u * S.l (lineIdx S x i) = u⁻¹ := by
      simp only [u]
      calc S.l (lineIdx S x i) * (v * S.l (lineIdx S x i)) * S.l (lineIdx S x i)
          = S.l (lineIdx S x i) * v * (S.l (lineIdx S x i) * S.l (lineIdx S x i)) := by
              group
        _ = S.l (lineIdx S x i) * v := by rw [hlk2, mul_one]
        _ = (v * S.l (lineIdx S x i))⁻¹ := by
              rw [mul_inv_rev, hlinv, hv_inv]
    exact hu_inv'
  have hsupp : ∀ j : Fin 3, j ≠ lineIdx S x i → c j = 0 := by
    have hconj_u : S.l (lineIdx S x i) * S.σ (Multiplicative.ofAdd c) *
        (S.l (lineIdx S x i))⁻¹ = (S.σ (Multiplicative.ofAdd c))⁻¹ := by
      rw [hc]
      exact hu_inv
    exact (S.E.conj_eq_inv_iff (lineIdx S x i) c).mp hconj_u
  have hu_sq_inv : u⁻¹ * u⁻¹ = u := by
    have huu : u * u = u⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      simpa [pow_succ, pow_two, mul_assoc] using hu3
    calc u⁻¹ * u⁻¹ = (u * u) * u⁻¹ := by rw [huu]
      _ = u * (u * u⁻¹) := by group
      _ = u := by rw [mul_inv_cancel, mul_one]
  have hB : S.l (lineIdx S x i) * u = u⁻¹ * S.l (lineIdx S x i) := by
    have hu_inv'' : S.l (lineIdx S x i) * u * S.l (lineIdx S x i) = u⁻¹ := by
      rwa [hlinv] at hu_inv
    have h := congrArg (fun z => z * S.l (lineIdx S x i)) hu_inv''
    simpa [mul_assoc, hlk2] using h
  refine ⟨S.σ (Multiplicative.ofAdd (-c)), S.E.mem_iff.mpr ⟨-c, rfl⟩, ?_, ?_⟩
  · intro m hm
    have hneg_single : -c = Pi.single (lineIdx S x i) (-(c (lineIdx S x i))) := by
      funext j
      by_cases hj : j = lineIdx S x i
      · subst hj
        simp
      · rw [Pi.neg_apply, hsupp j hj,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj (-(c (lineIdx S x i)))]
        rfl
    have h1 : S.l m * S.σ (Multiplicative.ofAdd
          (Pi.single (lineIdx S x i) (-(c (lineIdx S x i))))) * (S.l m)⁻¹ =
        S.σ (Multiplicative.ofAdd (Pi.single (lineIdx S x i) (-(c (lineIdx S x i))))) :=
      S.E.conj_l_single_of_ne (Ne.symm hm) _
    simpa [hneg_single] using h1
  · have hd_eq : S.σ (Multiplicative.ofAdd (-c)) = u⁻¹ := by
      calc S.σ (Multiplicative.ofAdd (-c))
          = S.σ ((Multiplicative.ofAdd c)⁻¹) := by rw [ofAdd_neg]
        _ = (S.σ (Multiplicative.ofAdd c))⁻¹ := map_inv S.σ (Multiplicative.ofAdd c)
        _ = u⁻¹ := by rw [hc]
    have hv_eq : v = u * S.l (lineIdx S x i) := by
      simp only [u]
      rw [mul_assoc, hlk2, mul_one]
    have hv_d : v = S.σ (Multiplicative.ofAdd (-c)) * S.l (lineIdx S x i) *
        (S.σ (Multiplicative.ofAdd (-c)))⁻¹ := by
      rw [hv_eq, hd_eq, inv_inv]
      exact (calc u⁻¹ * S.l (lineIdx S x i) * u
          = u⁻¹ * (S.l (lineIdx S x i) * u) := by group
        _ = u⁻¹ * (u⁻¹ * S.l (lineIdx S x i)) := by rw [hB]
        _ = (u⁻¹ * u⁻¹) * S.l (lineIdx S x i) := by group
        _ = u * S.l (lineIdx S x i) := by rw [hu_sq_inv]).symm
    simpa only [v] using hv_d

private theorem exists_conj_l (S : Setup M Y L) (x : M) :
    ∃ c : Fin 3 → ZMod 3, ∀ i : Fin 3,
      (x : X) * S.l i * (x : X)⁻¹ =
        S.σ (Multiplicative.ofAdd c) * S.l (lineIdx S x i) *
          (S.σ (Multiplicative.ofAdd c))⁻¹ := by
  choose D hD_mem hD_fix hD_eq using exists_diag S x
  let d : X := D 0 * D 1 * D 2
  have hdY : d ∈ Y := Y.mul_mem (Y.mul_mem (hD_mem 0) (hD_mem 1)) (hD_mem 2)
  have hD_comm : ∀ i j : Fin 3, D i * D j = D j * D i :=
    fun i j => S.E.comm (hD_mem i) (hD_mem j)
  have hline_inj : ∀ {i j : Fin 3}, lineIdx S x i = lineIdx S x j → i = j := by
    intro i j h
    have := congrArg (lineIdx S x⁻¹) h
    simpa [lineIdx_inv S x i, lineIdx_inv S x j] using this
  have hline_ne : ∀ {i j : Fin 3}, i ≠ j → lineIdx S x i ≠ lineIdx S x j := by
    intro i j hij h
    exact hij (hline_inj h)
  have hD_fix' : ∀ (j m : Fin 3), m ≠ lineIdx S x j →
      D j * S.l m * (D j)⁻¹ = S.l m := by
    intro j m hm
    have hl2 : S.l m * S.l m = 1 := S.sq_L _ (S.E.l_mem m)
    have hcomm : S.l m * D j = D j * S.l m := by
      have h := hD_fix j m hm
      have := congrArg (fun z => z * S.l m) h
      simpa [mul_assoc, hl2] using this
    rw [← hcomm]
    group
  have hfix_prod : ∀ (i : Fin 3) {j k : Fin 3}, j ≠ i → k ≠ i → j ≠ k →
      (D j * D k) * S.l (lineIdx S x i) * (D j * D k)⁻¹ = S.l (lineIdx S x i) := by
    intro i j k hji hki _
    have hji' : lineIdx S x i ≠ lineIdx S x j := hline_ne (Ne.symm hji)
    have hki' : lineIdx S x i ≠ lineIdx S x k := hline_ne (Ne.symm hki)
    calc (D j * D k) * S.l (lineIdx S x i) * (D j * D k)⁻¹
        = D j * (D k * S.l (lineIdx S x i) * (D k)⁻¹) * (D j)⁻¹ := by group
      _ = D j * S.l (lineIdx S x i) * (D j)⁻¹ := by rw [hD_fix' k _ hki']
      _ = S.l (lineIdx S x i) := hD_fix' j _ hji'
  have hcombine : ∀ i : Fin 3, d * S.l (lineIdx S x i) * d⁻¹ =
      D i * S.l (lineIdx S x i) * (D i)⁻¹ := by
    intro i
    fin_cases i
    · show (D 0 * D 1 * D 2) * S.l (lineIdx S x 0) * (D 0 * D 1 * D 2)⁻¹ =
        D 0 * S.l (lineIdx S x 0) * (D 0)⁻¹
      have hp : (D 1 * D 2) * S.l (lineIdx S x 0) * (D 1 * D 2)⁻¹ =
          S.l (lineIdx S x 0) := hfix_prod 0 (by decide) (by decide) (by decide)
      calc (D 0 * D 1 * D 2) * S.l (lineIdx S x 0) * (D 0 * D 1 * D 2)⁻¹
          = D 0 * ((D 1 * D 2) * S.l (lineIdx S x 0) * (D 1 * D 2)⁻¹) * (D 0)⁻¹ := by
              group
        _ = D 0 * S.l (lineIdx S x 0) * (D 0)⁻¹ := by rw [hp]
    · show (D 0 * D 1 * D 2) * S.l (lineIdx S x 1) * (D 0 * D 1 * D 2)⁻¹ =
        D 1 * S.l (lineIdx S x 1) * (D 1)⁻¹
      have hd_eq : D 0 * D 1 * D 2 = D 1 * (D 0 * D 2) := by
        rw [hD_comm 0 1]
        group
      rw [hd_eq]
      have hp : (D 0 * D 2) * S.l (lineIdx S x 1) * (D 0 * D 2)⁻¹ =
          S.l (lineIdx S x 1) := hfix_prod 1 (by decide) (by decide) (by decide)
      calc D 1 * (D 0 * D 2) * S.l (lineIdx S x 1) * (D 1 * (D 0 * D 2))⁻¹
          = D 1 * ((D 0 * D 2) * S.l (lineIdx S x 1) * (D 0 * D 2)⁻¹) * (D 1)⁻¹ := by
              group
        _ = D 1 * S.l (lineIdx S x 1) * (D 1)⁻¹ := by rw [hp]
    · show (D 0 * D 1 * D 2) * S.l (lineIdx S x 2) * (D 0 * D 1 * D 2)⁻¹ =
        D 2 * S.l (lineIdx S x 2) * (D 2)⁻¹
      have hd_eq : D 0 * D 1 * D 2 = D 2 * (D 0 * D 1) := by
        calc D 0 * D 1 * D 2 = D 0 * (D 1 * D 2) := by group
          _ = D 0 * (D 2 * D 1) := by rw [hD_comm 1 2]
          _ = (D 0 * D 2) * D 1 := by group
          _ = (D 2 * D 0) * D 1 := by rw [hD_comm 0 2]
          _ = D 2 * (D 0 * D 1) := by group
      rw [hd_eq]
      have hp : (D 0 * D 1) * S.l (lineIdx S x 2) * (D 0 * D 1)⁻¹ =
          S.l (lineIdx S x 2) := hfix_prod 2 (by decide) (by decide) (by decide)
      calc D 2 * (D 0 * D 1) * S.l (lineIdx S x 2) * (D 2 * (D 0 * D 1))⁻¹
          = D 2 * ((D 0 * D 1) * S.l (lineIdx S x 2) * (D 0 * D 1)⁻¹) * (D 2)⁻¹ := by
              group
        _ = D 2 * S.l (lineIdx S x 2) * (D 2)⁻¹ := by rw [hp]
  obtain ⟨c, hc⟩ := S.E.mem_iff.mp hdY
  refine ⟨c, fun i => ?_⟩
  rw [hD_eq i, hc]
  exact (hcombine i).symm

end MonomialSetup

theorem exists_monomial {M Y L : Subgroup X} {σ : Multiplicative (Fin 3 → ZMod 3) →* X}
    {l : Fin 3 → X} (E : EigenBasis Y L σ l) (hL : Nat.card L = 8)
    (hL2 : ∀ s ∈ L, s * s = 1) (hYM : Y ≤ M) (hLM : L ≤ M)
    (hnorm : ∀ x ∈ M, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (hcent : ∀ x ∈ M, (∀ y ∈ Y, x * y = y * x) → x ∈ Y) {F : X → Prop}
    (hFconj : ∀ x ∈ M, ∀ y, F y → F (x * y * x⁻¹))
    (hF : ∀ c : Fin 3 → ZMod 3, F (σ (Multiplicative.ofAdd c)) ↔
      ∃ i, c i ≠ 0 ∧ ∀ j, j ≠ i → c j = 0) :
    ∃ perm : M →* Equiv.Perm (Fin 3),
      (∀ (x : M) (i : Fin 3), ∃ s : ZMod 3, s ≠ 0 ∧
        (x : X) * eb σ i * (x : X)⁻¹ =
          σ (Multiplicative.ofAdd (Pi.single (perm x i) s))) ∧
      (∀ x : M, perm x = 1 ↔ (x : X) ∈ Y ⊔ L) ∧
      (∀ x : M, ∃ c : Fin 3 → ZMod 3, ∀ i, (x : X) * l i * (x : X)⁻¹ =
        σ (Multiplicative.ofAdd c) * l (perm x i) * (σ (Multiplicative.ofAdd c))⁻¹) ∧
      Nat.card M = 216 * Nat.card perm.range := by
  classical
  let S : MonomialSetup.Setup M Y L :=
    { σ := σ, l := l, E := E, card_L := hL, sq_L := hL2, le_M_Y := hYM, le_M_L := hLM,
      normalizes := hnorm, centralizes := hcent, F := F, F_conj := hFconj, F_iff := hF }
  refine ⟨MonomialSetup.perm S, ?_, ?_, ?_, ?_⟩
  · intro x i
    exact ⟨MonomialSetup.lineVal S x i, (MonomialSetup.lineIdx_spec S x i).1,
      by
        simpa [S, MonomialSetup.perm, MonomialSetup.toPerm]
          using (MonomialSetup.lineIdx_spec S x i).2⟩
  · intro x
    rw [← MonoidHom.mem_ker, MonomialSetup.perm_ker_eq S, Subgroup.mem_subgroupOf]
  · intro x
    obtain ⟨c, hc⟩ := MonomialSetup.exists_conj_l S x
    exact ⟨c, fun i => by
      simpa [S, MonomialSetup.perm, MonomialSetup.toPerm] using hc i⟩
  · simpa [S] using MonomialSetup.card_eq S

end CFSG.GF2Type.Smith1979.TriPlus

end
