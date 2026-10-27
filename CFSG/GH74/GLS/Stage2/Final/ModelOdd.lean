module

public import CFSG.GH74.GLS.Stage2.Final.ModelCenter
public import CFSG.GH74.GLS.Stage2.Final.ModelGroupTheory
public import CFSG.GH74.GLS.Stage2.Final.ModelH2Facts

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F]

theorem det_sc2 (c : Fˣ) : ((sc2 c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (c : F) ^ 2 := by
  simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]

theorem diag_sc2_mem_K4 (M : ModelData F) {l m : Fˣ} (hl : sc2 l ∈ M.U2) (hm : sc2 m ∈ M.U2)
    (h : (l : F) ^ 2 * (m : F) ^ 2 = 1) : diagGL (sc2 l) (sc2 m) ∈ M.K4 := by
  rw [M.diagGL_mem_K4_iff]
  exact ⟨hl, hm, by rw [det_sc2, det_sc2]; exact h⟩

@[expose] def thetaEl (M : ModelData F) {l : Fˣ} (hl : sc2 l ∈ M.U2) : ↥M.K4 :=
  ⟨diagGL (sc2 l) (sc2 l⁻¹), diag_sc2_mem_K4 M hl (by rw [← sc2_inv]; exact M.U2.inv_mem hl) (by
    have : (l : F) * (l⁻¹ : Fˣ) = 1 := by simp
    calc (l : F) ^ 2 * ((l⁻¹ : Fˣ) : F) ^ 2 = ((l : F) * ((l⁻¹ : Fˣ) : F)) ^ 2 := by ring
      _ = 1 := by rw [this]; norm_num)⟩

theorem thetaEl_mul (M : ModelData F) {l m : Fˣ} (hl : sc2 l ∈ M.U2) (hm : sc2 m ∈ M.U2) :
    thetaEl M hl * thetaEl M hm = thetaEl M (l := l * m) (by
      rw [← sc2_mul]; exact M.U2.mul_mem hl hm) := by
  apply Subtype.ext
  change diagGL (sc2 l) (sc2 l⁻¹) * diagGL (sc2 m) (sc2 m⁻¹) = diagGL (sc2 (l * m)) (sc2 (l * m)⁻¹)
  rw [diagGL_mul, sc2_mul, sc2_mul, mul_inv]

theorem eq_one_of_pow_odd {G : Type*} [Group G] {u : G} {n' : ℕ} (hodd : Odd n') (h1 : u ^ n' = 1)
    (h2 : u * u = 1) : u = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have : u ^ n' = u := by
    rw [hk, pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  rw [← this, h1]

@[expose] noncomputable def theta (M : ModelData F) (n' : ℕ)
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) : ↥(rootsOfUnity n' F) →* PG M where
  toFun l := mkP M (thetaEl M (hU l.1 ((mem_rootsOfUnity _ _).1 l.2)))
  map_one' := by
    have : thetaEl M (l := 1) (hU 1 (by simp)) = 1 := by
      apply Subtype.ext
      change diagGL (sc2 (1 : Fˣ)) (sc2 (1 : Fˣ)⁻¹) = 1
      rw [inv_one, sc2_one, diagGL_one]
    exact (congrArg (mkP M) this).trans (map_one _)
  map_mul' l₁ l₂ := by
    rw [← map_mul]
    exact congrArg (mkP M) (thetaEl_mul M _ _).symm

theorem theta_apply (M : ModelData F) (n' : ℕ) (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2)
    (l : ↥(rootsOfUnity n' F)) :
    theta M n' hU l = mkP M (thetaEl M (hU l.1 ((mem_rootsOfUnity _ _).1 l.2))) := rfl

theorem theta_injective (M : ModelData F) (n' : ℕ) (hodd : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) : Function.Injective (theta M n' hU) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  rw [theta_apply] at hl
  have hZ : thetaEl M (hU l.1 ((mem_rootsOfUnity _ _).1 l.2)) ∈ Zs M :=
    (QuotientGroup.eq_one_iff _).1 hl
  obtain ⟨c, hc⟩ := mem_Zs.1 hZ
  rw [scalar4_eq] at hc
  obtain ⟨h1, h2⟩ := diagGL_inj hc
  have hcl : c = l.1 := sc2_inj h1
  have hcl' : c = l.1⁻¹ := sc2_inj h2
  have hsq : l.1 * l.1 = 1 := by
    calc l.1 * l.1 = l.1 * l.1⁻¹ := by rw [← hcl', hcl]
      _ = 1 := mul_inv_cancel _
  have hpow : (l.1) ^ n' = 1 := (mem_rootsOfUnity _ _).1 l.2
  exact Subtype.ext (eq_one_of_pow_odd hodd hpow hsq)

theorem sc2_conj_self (a : GL (Fin 2) F) (c : Fˣ) : a * sc2 c * a⁻¹ = sc2 c := by
  calc a * sc2 c * a⁻¹ = sc2 c * a * a⁻¹ := by rw [← sc2_comm c a]
    _ = sc2 c := by group

theorem conj_blockScalar (M : ModelData F) (h2 : (2 : F) ≠ 0) {g : ↥M.K4} (hg : g ∈ Nsub M)
    (l m : Fˣ) :
    (g : GL (Fin 4) F) * diagGL (sc2 l) (sc2 m) * (g : GL (Fin 4) F)⁻¹ = diagGL (sc2 l) (sc2 m) ∨
    (g : GL (Fin 4) F) * diagGL (sc2 l) (sc2 m) * (g : GL (Fin 4) F)⁻¹ = diagGL (sc2 m) (sc2 l) := by
  have hD : ∀ d : ↥M.K4, d ∈ Dsub M → (d : GL (Fin 4) F) * diagGL (sc2 l) (sc2 m) *
      (d : GL (Fin 4) F)⁻¹ = diagGL (sc2 l) (sc2 m) := by
    intro d hd
    have hc : (d : GL (Fin 4) F) * yGL F = yGL F * (d : GL (Fin 4) F) :=
      congrArg Subtype.val (mem_Dsub.1 hd)
    obtain ⟨a, b, hab, -, -, -⟩ := M.exists_diagGL_of_comm h2 d.2 hc
    rw [hab, diagGL_inv, diagGL_mul, diagGL_mul, sc2_conj_self, sc2_conj_self]
  rcases (mem_Nsub_iff_D M).1 hg with hgD | hgD
  · left
    exact hD g hgD
  · right
    have hww := swapGL_mul_self (F := F)
    have hgeq : (g : GL (Fin 4) F) = swapGL F * ((M.wK * g : ↥M.K4) : GL (Fin 4) F) := by
      show (g : GL (Fin 4) F) = swapGL F * (swapGL F * (g : GL (Fin 4) F))
      rw [← mul_assoc, hww, one_mul]
    rw [hgeq, _root_.mul_inv_rev, swapGL_inv]
    have := hD _ hgD
    calc swapGL F * (M.wK * g : ↥M.K4) * diagGL (sc2 l) (sc2 m) *
          (((M.wK * g : ↥M.K4) : GL (Fin 4) F)⁻¹ * swapGL F)
        = swapGL F * (((M.wK * g : ↥M.K4) : GL (Fin 4) F) * diagGL (sc2 l) (sc2 m) *
          ((M.wK * g : ↥M.K4) : GL (Fin 4) F)⁻¹) * swapGL F := by group
      _ = diagGL (sc2 m) (sc2 l) := by
        rw [this, swapGL_mul_diagGL_mul_swapGL]

noncomputable abbrev R0 (M : ModelData F) (n' : ℕ) (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) :
    Subgroup (PG M) := (theta M n' hU).range

theorem card_R0 (M : ModelData F) [Finite F] (n' : ℕ) (hodd : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) (hdvd : n' ∣ Nat.card F - 1) :
    Nat.card ↥(R0 M n' hU) = n' := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (theta_injective M n' hodd hU)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, Nat.gcd_eq_right hdvd]

theorem thetaEl_mem_Dsub (M : ModelData F) {l : Fˣ} (hl : sc2 l ∈ M.U2) :
    thetaEl M hl ∈ Dsub M := by
  rw [mem_Dsub]
  apply Subtype.ext
  change diagGL (sc2 l) (sc2 l⁻¹) * yGL F = yGL F * diagGL (sc2 l) (sc2 l⁻¹)
  rw [yGL, diagGL_mul, diagGL_mul, mul_one, one_mul, ← sc2_neg_one (F := F), sc2_mul, sc2_mul,
    mul_comm l (-1)]

theorem R0_le_C (M : ModelData F) (n' : ℕ) (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) :
    R0 M n' hU ≤ (Dsub M).map (mkP M) := by
  rintro _ ⟨l, rfl⟩
  exact ⟨thetaEl M _, thetaEl_mem_Dsub M _, rfl⟩

theorem R0_normalized (M : ModelData F) (h2 : (2 : F) ≠ 0) (n' : ℕ)
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) {c : PG M}
    (hc : c ∈ Subgroup.centralizer {yP M}) {x : PG M} (hx : x ∈ R0 M n' hU) :
    c * x * c⁻¹ ∈ R0 M n' hU := by
  rw [centralizer_yP] at hc
  obtain ⟨g, hg, rfl⟩ := hc
  obtain ⟨l, rfl⟩ := hx
  rw [theta_apply]
  have hl' : (l.1⁻¹) ^ n' = 1 := by
    rw [inv_pow, (mem_rootsOfUnity _ _).1 l.2, inv_one]
  have key : ∀ a : ↥M.K4, mkP M g * mkP M a * (mkP M g)⁻¹ = mkP M (g * a * g⁻¹) := by
    intro a
    simp only [map_mul, map_inv]
  rw [key]
  rcases conj_blockScalar M h2 hg l.1 l.1⁻¹ with h | h
  · refine ⟨l, ?_⟩
    rw [theta_apply]
    congr 1
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨l.1⁻¹, inv_mem l.2⟩, ?_⟩
    rw [theta_apply]
    congr 1
    apply Subtype.ext
    change diagGL (sc2 l.1⁻¹) (sc2 l.1⁻¹⁻¹) = _
    rw [inv_inv]
    exact h.symm

theorem wK_conj_mem_Dsub (M : ModelData F) {d : ↥M.K4} (hd : d ∈ Dsub M) :
    M.wK * d * M.wK⁻¹ ∈ Dsub M := by
  have hww := wK_mul_self M
  have hwinv : M.wK⁻¹ = M.wK := inv_eq_of_mul_eq_one_right hww
  rw [hwinv, mem_Dsub]
  have hy : M.yK = M.wK * M.xyK * M.wK := by
    have h := M.wK_mul_xyK_mul_inv
    rw [hwinv] at h
    exact h.symm
  have hxc := fun t : ↥M.K4 => (Subgroup.mem_center_iff.1 M.xK_mem_center t)
  have hd' := mem_Dsub.1 hd
  have hdxy : d * M.xyK = M.xyK * d := by
    rw [← M.xK_mul_yK]
    calc d * (M.xK * M.yK) = (d * M.xK) * M.yK := by group
      _ = (M.xK * d) * M.yK := by rw [hxc d]
      _ = M.xK * (d * M.yK) := by group
      _ = M.xK * (M.yK * d) := by rw [hd']
      _ = (M.xK * M.yK) * d := by group
  have e : ∀ a b : ↥M.K4, (M.wK * a * M.wK) * (M.wK * b * M.wK) = M.wK * (a * b) * M.wK := by
    intro a b
    calc (M.wK * a * M.wK) * (M.wK * b * M.wK) = M.wK * a * (M.wK * M.wK) * b * M.wK := by group
      _ = M.wK * (a * b) * M.wK := by rw [hww]; group
  calc (M.wK * d * M.wK) * M.yK = (M.wK * d * M.wK) * (M.wK * M.xyK * M.wK) := by rw [← hy]
    _ = M.wK * (d * M.xyK) * M.wK := e _ _
    _ = M.wK * (M.xyK * d) * M.wK := by rw [hdxy]
    _ = (M.wK * M.xyK * M.wK) * (M.wK * d * M.wK) := (e _ _).symm
    _ = M.yK * (M.wK * d * M.wK) := by rw [← hy]

theorem sq_mem_Dsub (M : ModelData F) {g : ↥M.K4} (hg : g ∈ Nsub M) :
    g * g ∈ Dsub M := by
  rcases (mem_Nsub_iff_D M).1 hg with h | h
  · exact (Dsub M).mul_mem h h
  · have hww := wK_mul_self M
    have hwinv : M.wK⁻¹ = M.wK := inv_eq_of_mul_eq_one_right hww
    have hconj := wK_conj_mem_Dsub M h
    have : g * g = (M.wK * (M.wK * g) * M.wK⁻¹) * (M.wK * g) := by
      rw [hwinv]
      calc g * g = (M.wK * M.wK) * g * (M.wK * M.wK) * g := by rw [hww]; group
        _ = _ := by group
    rw [this]
    exact (Dsub M).mul_mem hconj h

theorem odd_mem_C0 (M : ModelData F) {x : PG M}
    (hx : x ∈ Subgroup.centralizer {yP M}) (hodd : Odd (orderOf x)) :
    x ∈ (Dsub M).map (mkP M) := by
  rw [centralizer_yP] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  rcases (mem_Nsub_iff_D M).1 hg with h | h
  · exact ⟨g, h, rfl⟩
  · obtain ⟨k, hk⟩ := hodd
    have hsq : mkP M g ^ 2 ∈ (Dsub M).map (mkP M) :=
      ⟨g * g, sq_mem_Dsub M hg, by rw [map_mul, sq]⟩
    have hpow : mkP M g ^ (orderOf (mkP M g)) = 1 := pow_orderOf_eq_one _
    have : mkP M g = (mkP M g ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      calc mkP M g = mkP M g * mkP M g ^ orderOf (mkP M g) := by rw [hpow, mul_one]
        _ = mkP M g ^ (2 * (k + 1)) := by rw [← pow_succ']; congr 1; omega
    rw [this]
    exact Subgroup.pow_mem _ hsq _

theorem zpow_mem_of_coprime_order {G : Type*} [Group G] (H : Subgroup G) {x : G} {k : ℕ}
    (hk : Nat.Coprime k (orderOf x)) (hxk : x ^ k ∈ H) : x ∈ H := by
  have h1 : ((k : ℤ) * Nat.gcdA k (orderOf x) + (orderOf x : ℤ) * Nat.gcdB k (orderOf x)) = 1 := by
    have := Nat.gcd_eq_gcd_ab k (orderOf x)
    rw [hk] at this
    simpa using this.symm
  have : x = (x ^ k) ^ (Nat.gcdA k (orderOf x)) := by
    have hx1 : x ^ (1 : ℤ) = x := zpow_one x
    calc x = x ^ (1 : ℤ) := hx1.symm
      _ = x ^ ((k : ℤ) * Nat.gcdA k (orderOf x) + (orderOf x : ℤ) * Nat.gcdB k (orderOf x)) := by
          rw [h1]
      _ = (x ^ (k : ℤ)) ^ (Nat.gcdA k (orderOf x)) *
          (x ^ (orderOf x : ℤ)) ^ (Nat.gcdB k (orderOf x)) := by
          rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul]
      _ = (x ^ k) ^ (Nat.gcdA k (orderOf x)) := by
          rw [zpow_natCast, zpow_natCast, pow_orderOf_eq_one, _root_.one_zpow, mul_one]
  rw [this]
  exact H.zpow_mem hxk _

theorem diagGL_pow (a b : GL (Fin 2) F) (k : ℕ) : (diagGL a b) ^ k = diagGL (a ^ k) (b ^ k) :=
  (map_pow (diagGLHom F) (a, b) k).symm

theorem sc2_pow (c : Fˣ) (k : ℕ) : (sc2 c : GL (Fin 2) F) ^ k = sc2 (c ^ k) :=
  (map_pow (Matrix.GeneralLinearGroup.scalar (Fin 2)) c k).symm

theorem blockScalar_odd_mem_R0 (M : ModelData F) {n s n' : ℕ} (hn : n = 2 ^ s * n') (hs : 1 ≤ s)
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ n = 1)
    {g : ↥M.K4} {l m : Fˣ} (hg : (g : GL (Fin 4) F) = diagGL (sc2 l) (sc2 m))
    (hodd : Odd (orderOf (mkP M g))) : mkP M g ∈ R0 M n' hU := by
  have hK : diagGL (sc2 l) (sc2 m) ∈ M.K4 := hg ▸ g.2
  rw [M.diagGL_mem_K4_iff, det_sc2, det_sc2] at hK
  obtain ⟨hl, hm, hdet⟩ := hK
  have hlm : (l * m) * (l * m) = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one]
    linear_combination hdet
  have hln : l ^ n = 1 := hU2 l hl
  set a : Fˣ := l ^ (2 ^ s) with ha
  have han' : a ^ n' = 1 := by
    rw [ha, ← pow_mul, ← hn]
    exact hln
  have hma : m ^ (2 ^ s) = a⁻¹ := by
    rcases units_sq_eq_one hlm with h | h
    · have hm' : m = l⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [hm', inv_pow]
    · have hm' : m = l⁻¹ * (-1) := by
        calc m = l⁻¹ * (l * m) := by group
          _ = l⁻¹ * (-1) := by rw [h]
      rw [hm', mul_pow, inv_pow, Even.neg_one_pow (Nat.even_pow.2 ⟨even_two, by omega⟩), mul_one]
  have hpow : mkP M g ^ (2 ^ s) = theta M n' hU ⟨a, (mem_rootsOfUnity _ _).2 han'⟩ := by
    rw [theta_apply, ← map_pow]
    congr 1
    apply Subtype.ext
    change ((g : GL (Fin 4) F)) ^ (2 ^ s) = diagGL (sc2 a) (sc2 a⁻¹)
    rw [hg, diagGL_pow, sc2_pow, sc2_pow, hma]
  have hcop : Nat.Coprime (2 ^ s) (orderOf (mkP M g)) :=
    Nat.Coprime.pow_left s (Nat.coprime_two_left.2 hodd)
  exact zpow_mem_of_coprime_order _ hcop (by rw [hpow]; exact ⟨_, rfl⟩)

@[expose] noncomputable def blkHom (M : ModelData F) (blk : GL (Fin 2) F →* GL (Fin 4) F)
    (hmem : ∀ a ∈ M.H2, blk a ∈ M.K4) : ↥M.H2 →* PG M where
  toFun a := mkP M ⟨blk a, hmem a a.2⟩
  map_one' := by
    have : (⟨blk ((1 : ↥M.H2) : GL (Fin 2) F), hmem _ (1 : ↥M.H2).2⟩ : ↥M.K4) = 1 :=
      Subtype.ext (map_one blk)
    rw [this, map_one]
  map_mul' a b := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (map_mul blk _ _)

theorem blkHom_apply (M : ModelData F) (blk : GL (Fin 2) F →* GL (Fin 4) F)
    (hmem : ∀ a ∈ M.H2, blk a ∈ M.K4) (a : ↥M.H2) :
    blkHom M blk hmem a = mkP M ⟨blk a, hmem a a.2⟩ := rfl

theorem commute_of_normal_odd (M : ModelData F) (blk : GL (Fin 2) F →* GL (Fin 4) F)
    (hmem : ∀ a ∈ M.H2, blk a ∈ M.K4)
    (hnorm : ∀ g : ↥M.K4, g ∈ Dsub M → ∀ a ∈ M.H2, ∃ c ∈ M.H2,
      (g : GL (Fin 4) F) * blk a * (g : GL (Fin 4) F)⁻¹ = blk c)
    (hinj : Function.Injective (blkHom M blk hmem))
    (hqs : CFSG.IsQuasisimple ↥M.H2) (hZ : IsPGroup 2 ↥(Subgroup.center ↥M.H2))
    (hev : 2 ∣ Nat.card ↥M.H2)
    (hC : ∀ a : ↥M.H2, blkHom M blk hmem a ∈ Subgroup.centralizer {yP M})
    {N₀ : Subgroup (PG M)}
    (hnormal : ∀ c ∈ Subgroup.centralizer {yP M}, ∀ x ∈ N₀, c * x * c⁻¹ ∈ N₀)
    (hodd : Odd (Nat.card N₀)) [Finite F] {g : ↥M.K4} (hgD : g ∈ Dsub M) (hx : mkP M g ∈ N₀)
    (a : ↥M.H2) :
    mkP M g * blkHom M blk hmem a = blkHom M blk hmem a * mkP M g := by
  set ι := blkHom M blk hmem with hι
  have hc := hgD
  have hgC : g ∈ Dsub M := hgD
  obtain ⟨c, hcH, hgc⟩ := hnorm g hgD a a.2
  have e1 : mkP M g * ι a * (mkP M g)⁻¹ = ι ⟨c, hcH⟩ := by
    rw [hι, blkHom_apply, blkHom_apply]
    simp only [← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext hgc
  let W : Subgroup ↥M.H2 := N₀.comap ι
  have hWn : W.Normal := by
    refine ⟨fun c' hc' h => ?_⟩
    show ι (h * c' * h⁻¹) ∈ N₀
    rw [map_mul, map_mul, map_inv]
    exact hnormal _ (hC h) _ hc'
  have hWodd : Odd (Nat.card W) := by
    have hle : W.map ι ≤ N₀ := Subgroup.map_comap_le _ _
    have h1 : Nat.card W = Nat.card (W.map ι) :=
      (Subgroup.card_map_of_injective hinj).symm
    have h2' : Nat.card (W.map ι) ∣ Nat.card N₀ := Subgroup.card_dvd_of_le hle
    rw [h1]
    exact Odd.of_dvd_nat hodd h2'
  have hW := ModelGT.normal_odd_eq_bot hqs hZ hev W hWodd
  have hmem' : ι (⟨c, hcH⟩ * a⁻¹) ∈ N₀ := by
    rw [map_mul, map_inv, ← e1]
    have h3 : ι a * (mkP M g)⁻¹ * (ι a)⁻¹ ∈ N₀ :=
      hnormal _ (hC a) _ (N₀.inv_mem hx)
    have h4 : mkP M g * ι a * (mkP M g)⁻¹ * (ι a)⁻¹ =
        mkP M g * (ι a * (mkP M g)⁻¹ * (ι a)⁻¹) := by group
    rw [h4]
    exact N₀.mul_mem hx h3
  have hca : (⟨c, hcH⟩ * a⁻¹ : ↥M.H2) ∈ W := hmem'
  rw [hW, Subgroup.mem_bot, mul_inv_eq_one] at hca
  rw [hca] at e1
  calc mkP M g * ι a = (mkP M g * ι a * (mkP M g)⁻¹) * mkP M g := by group
    _ = ι a * mkP M g := by rw [e1]

theorem blkHom_injective (M : ModelData F) (blk : GL (Fin 2) F →* GL (Fin 4) F)
    (hmem : ∀ a ∈ M.H2, blk a ∈ M.K4)
    (hscal : ∀ (a : GL (Fin 2) F) (c : Fˣ),
      blk a = Matrix.GeneralLinearGroup.scalar (Fin 4) c → a = 1) :
    Function.Injective (blkHom M blk hmem) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [blkHom_apply] at ha
  have hZ : (⟨blk a, hmem a a.2⟩ : ↥M.K4) ∈ Zs M := (QuotientGroup.eq_one_iff _).1 ha
  obtain ⟨c, hc⟩ := mem_Zs.1 hZ
  exact Subtype.ext (hscal a c hc.symm)

theorem pPrimeCore_eq_R0 [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) {n s n' : ℕ}
    (hn : n = 2 ^ s * n') (hs : 1 ≤ s) (hodd' : Odd n')
    (hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2) (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ n = 1)
    (hdvd : n' ∣ Nat.card F - 1) (hqs : CFSG.IsQuasisimple ↥M.H2)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥M.H2)) (hev : 2 ∣ Nat.card ↥M.H2) {a b : F}
    (hab : a ^ 2 + b ^ 2 = -1) (hH : ∀ g, rhoQ hab g ∈ M.H2) :
    CFSG.pPrimeCore 2 ↥(Subgroup.centralizer {yP M}) =
      (R0 M n' hU).subgroupOf (Subgroup.centralizer {yP M}) := by
  set C : Subgroup (PG M) := Subgroup.centralizer {yP M} with hCdef
  have hDC : (Dsub M).map (mkP M) ≤ C := by
    rw [hCdef, centralizer_yP]
    exact Subgroup.map_mono (Dsub_le_Nsub M)
  have hR0C : R0 M n' hU ≤ C := (R0_le_C M n' hU).trans hDC
  have hRn : ((R0 M n' hU).subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact R0_normalized M h2 n' hU g.2 hx
  have hRodd : Odd (Nat.card ↥((R0 M n' hU).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0C).toEquiv, card_R0 M n' hodd' hU hdvd]
    exact hodd'
  refine ModelGT.pPrimeCore_eq_of_normal_odd _ hRodd ?_
  intro N₀ hN₀ hN₀odd x hx
  rw [Subgroup.mem_subgroupOf]
  set N₁ : Subgroup (PG M) := N₀.map C.subtype with hN₁
  have hN₁card : Nat.card N₁ = Nat.card N₀ := Subgroup.card_map_of_injective C.subtype_injective
  have hN₁odd : Odd (Nat.card N₁) := by rw [hN₁card]; exact hN₀odd
  have hxN₁ : (x : PG M) ∈ N₁ := ⟨x, hx, rfl⟩
  have hnormal : ∀ c ∈ C, ∀ y ∈ N₁, c * y * c⁻¹ ∈ N₁ := by
    intro c hc y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨c, hc⟩ * z * ⟨c, hc⟩⁻¹, hN₀.conj_mem z hz _, rfl⟩
  have hxodd : Odd (orderOf (x : PG M)) := by
    have : orderOf (⟨(x : PG M), hxN₁⟩ : N₁) ∣ Nat.card N₁ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hN₁odd this
  have hxC : (x : PG M) ∈ C := x.2
  obtain ⟨g, hgD, hgx⟩ := odd_mem_C0 M hxC hxodd
  have hgN : g ∈ Nsub M := Dsub_le_Nsub M hgD
  have hxg : mkP M g ∈ N₁ := by rw [hgx]; exact hxN₁
  have hDy : ∀ d : ↥M.K4, d ∈ Dsub M → mkP M d ∈ C := fun d hd => hDC ⟨d, hd, rfl⟩
  have hscalL : ∀ (a : GL (Fin 2) F) (c : Fˣ),
      blkL F a = Matrix.GeneralLinearGroup.scalar (Fin 4) c → a = 1 := by
    intro a c hc
    rw [blkL_apply, scalar4_eq] at hc
    obtain ⟨h1, h2'⟩ := diagGL_inj hc
    rw [h1, ← h2']
  have hscalR : ∀ (a : GL (Fin 2) F) (c : Fˣ),
      blkR F a = Matrix.GeneralLinearGroup.scalar (Fin 4) c → a = 1 := by
    intro a c hc
    rw [blkR_apply, scalar4_eq] at hc
    obtain ⟨h1, h2'⟩ := diagGL_inj hc
    rw [h2', ← h1]
  have hCL : ∀ a : ↥M.H2, blkHom M (blkL F) (fun a ha => M.blkL_mem_K4 ha) a ∈ C := by
    intro a
    refine hDy ⟨blkL F a, M.blkL_mem_K4 a.2⟩ ?_
    rw [mem_Dsub]
    exact Subtype.ext (ModelData.blkL_comm_yGL _)
  have hCR : ∀ a : ↥M.H2, blkHom M (blkR F) (fun a ha => M.blkR_mem_K4 ha) a ∈ C := by
    intro a
    refine hDy ⟨blkR F a, M.blkR_mem_K4 a.2⟩ ?_
    rw [mem_Dsub]
    exact Subtype.ext (ModelData.blkR_comm_yGL _)
  have hgc : (g : GL (Fin 4) F) * yGL F = yGL F * (g : GL (Fin 4) F) :=
    congrArg Subtype.val (mem_Dsub.1 hgD)
  have hcL := fun a : ↥M.H2 => commute_of_normal_odd M (blkL F) (fun a ha => M.blkL_mem_K4 ha)
    (fun g hg a ha => M.conj_blkL_of_comm h2 g.2 (congrArg Subtype.val (mem_Dsub.1 hg)) ha)
    (blkHom_injective M (blkL F) (fun a ha => M.blkL_mem_K4 ha) hscalL)
    hqs hZ hev hCL hnormal hN₁odd hgD hxg a
  have hcR := fun a : ↥M.H2 => commute_of_normal_odd M (blkR F) (fun a ha => M.blkR_mem_K4 ha)
    (fun g hg a ha => M.conj_blkR_of_comm h2 g.2 (congrArg Subtype.val (mem_Dsub.1 hg)) ha)
    (blkHom_injective M (blkR F) (fun a ha => M.blkR_mem_K4 ha) hscalR)
    hqs hZ hev hCR hnormal hN₁odd hgD hxg a
  have hcomm : ∀ c d : CFSG.GH74.Filter.ClassicalOdd.Q8,
      mkP M g * mkP M (Phi M (rhoQ hab) hH (c, d)) =
        mkP M (Phi M (rhoQ hab) hH (c, d)) * mkP M g := by
    intro c d
    have hsplit : mkP M (Phi M (rhoQ hab) hH (c, d)) =
        blkHom M (blkL F) (fun a ha => M.blkL_mem_K4 ha) ⟨rhoQ hab c, hH c⟩ *
          blkHom M (blkR F) (fun a ha => M.blkR_mem_K4 ha) ⟨rhoQ hab d, hH d⟩ := by
      rw [blkHom_apply, blkHom_apply, ← map_mul]
      congr 1
      apply Subtype.ext
      change diagGL (rhoQ hab c) (rhoQ hab d) = blkL F (rhoQ hab c) * blkR F (rhoQ hab d)
      exact diagGL_eq_blkL_mul_blkR _ _
    rw [hsplit, ← mul_assoc, hcL, mul_assoc, hcR, ← mul_assoc]
  obtain ⟨l, m, hlm⟩ := blockScalar_of_comm M h2 (rhoQ hab) hH (rhoQ_irr hab h2) (rhoQ_nc hab)
    hgN hcomm
  have hodd_g : Odd (orderOf (mkP M g)) := by rw [hgx]; exact hxodd
  have := blockScalar_odd_mem_R0 M hn hs hU hU2 hlm hodd_g
  rw [hgx] at this
  exact this

theorem card_pPrimeCore [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0)
    (hneven : 2 ∣ n) (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1) (hdvd : n ∣ Nat.card F - 1)
    (hqs : CFSG.IsQuasisimple ↥M.H2) (hZ : IsPGroup 2 ↥(Subgroup.center ↥M.H2))
    (hev : 2 ∣ Nat.card ↥M.H2) {a b : F} (hab : a ^ 2 + b ^ 2 = -1)
    (hH : ∀ g, rhoQ hab g ∈ M.H2) :
    Nat.card ↥(CFSG.pPrimeCore 2 ↥(Subgroup.centralizer {yP M})) = n / 2 ^ n.factorization 2 := by
  set s := n.factorization 2 with hs
  set n' := n / 2 ^ s with hn'
  have hn : n = 2 ^ s * n' := (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hodd' : Odd n' := Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hn0)
  have hs1 : 1 ≤ s := by
    have : 0 < n.factorization 2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 hneven
    exact this
  have hU : ∀ l : Fˣ, l ^ n' = 1 → sc2 l ∈ M.U2 := by
    intro l hl
    rw [hU2, hn, mul_comm, pow_mul, hl, one_pow]
  have hU2' : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ n = 1 := fun l hl => (hU2 l).1 hl
  have hdvd' : n' ∣ Nat.card F - 1 := (Nat.ordCompl_dvd n 2).trans hdvd
  have hC0 : (R0 M n' hU).subgroupOf (Subgroup.centralizer {yP M}) =
      CFSG.pPrimeCore 2 ↥(Subgroup.centralizer {yP M}) :=
    (pPrimeCore_eq_R0 M h2 hn hs1 hodd' hU hU2' hdvd' hqs hZ hev hab hH).symm
  have hDC : (Dsub M).map (mkP M) ≤ Subgroup.centralizer {yP M} := by
    rw [centralizer_yP]
    exact Subgroup.map_mono (Dsub_le_Nsub M)
  have hR0C : R0 M n' hU ≤ Subgroup.centralizer {yP M} := (R0_le_C M n' hU).trans hDC
  rw [← hC0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0C).toEquiv, card_R0 M n' hodd' hU hdvd']

theorem sc2_mem_uni_iff {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (l : Fˣ) :
    sc2 l ∈ (ModelData.uni hF).U2 ↔ l ^ (p ^ f + 1) = 1 := by
  show sc2 l ∈ uniGL (unitaryInvolution F p f) 2 ↔ _
  rw [mem_uniGL]
  have hσ : ∀ x, unitaryInvolution F p f x = x ^ (p ^ f) := unitaryInvolution_apply F p f
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hmat : conjTr (unitaryInvolution F p f) ((sc2 l : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((sc2 l : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) ((l : F) ^ (p ^ f) * (l : F)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply,
        Fin.sum_univ_two, iterateFrobenius_def, hp0]
  rw [hmat]
  constructor
  · intro h
    have h1 : (l : F) ^ (p ^ f) * (l : F) = 1 := by
      have := congrFun₂ h 0 0
      simpa [Matrix.scalar_apply] using this
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [pow_succ]; exact h1
  · intro h
    have h1 : (l : F) ^ (p ^ f + 1) = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) h
      simpa using this
    rw [pow_succ] at h1
    rw [h1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem modelOddCore : ModelOddCore := by
  intro Gs _ _ p f S' z' hGs hz'ord hz'c
  obtain ⟨hp, hp2, hq3, hcases⟩ := hGs
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq5 : 5 ≤ p ^ f := by obtain ⟨k, hk⟩ := hqodd; omega
  constructor
  · intro h8 hL
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    obtain ⟨a, b, hab⟩ := (CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices
      (ringChar_ne_two_of_two_ne_zero h2)).1
    have hH := rhoQ_mem_H2_lin hab
    obtain ⟨S₁, hS₁⟩ := exists_sylow_center_of_quat (ModelData.lin F) h2
      (ModelOrd.odd_index_lin F h2) hab hH
    obtain ⟨Φ, hΦ⟩ := exists_equiv_of_center (show Gs ≃* PG (ModelData.lin F) from e) S₁ (yP _)
      (orderOf_yP _ h2) ((centerIs_iff _ _).1 hS₁) S' z' hz'ord hz'c
    rw [card_pPrimeCore_centralizer_of_equiv Φ z', hΦ]
    have h5 : 5 ≤ Nat.card F := by rw [hF]; exact hq5
    have hev : 2 ∣ p ^ f - 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k, by omega⟩
    exact card_pPrimeCore (ModelData.lin F) h2 (n := p ^ f - 1) (by omega) hev
      (fun l => ⟨fun _ => by
        have h := pow_card_eq_one' (G := Fˣ) (x := l)
        rwa [Nat.card_units, hF] at h, fun _ => Subgroup.mem_top _⟩)
      (by rw [hF]) (ModelH2.h2_quasisimple_lin F h5) (ModelH2.h2_center_two_lin F)
      (ModelH2.h2_even_lin F h2) hab hH
  · intro h8 hU
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    obtain ⟨a, b, hab, hH⟩ := exists_rhoQ_uni hF hp2
    obtain ⟨S₁, hS₁⟩ := exists_sylow_center_of_quat (ModelData.uni hF) h2
      (ModelOrd.odd_index_uni hF hp2) hab hH
    obtain ⟨Φ, hΦ⟩ := exists_equiv_of_center (show Gs ≃* PG (ModelData.uni hF) from e) S₁ (yP _)
      (orderOf_yP _ h2) ((centerIs_iff _ _).1 hS₁) S' z' hz'ord hz'c
    rw [card_pPrimeCore_centralizer_of_equiv Φ z', hΦ]
    have h5 : 5 ≤ p ^ f := hq5
    have hev : 2 ∣ p ^ f + 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k + 1, by omega⟩
    have hdvd : p ^ f + 1 ∣ Nat.card F - 1 := by
      rw [hF]
      obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
      rw [hk]
      refine ⟨k, ?_⟩
      apply Nat.sub_eq_of_eq_add
      ring
    exact card_pPrimeCore (ModelData.uni hF) h2 (n := p ^ f + 1) (by omega) hev
      (sc2_mem_uni_iff hF) hdvd (ModelH2.h2_quasisimple_uni hF h5) (ModelH2.h2_center_two_uni hF)
      (ModelH2.h2_even_uni hF hp2) hab hH

end CFSG.GH74.GLS.Stage2.Final
