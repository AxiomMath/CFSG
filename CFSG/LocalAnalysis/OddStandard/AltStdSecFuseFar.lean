module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseOpen
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseSigma
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseFarDef

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem exists_decomp_of_mem_R (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hzR : z ∈ R) (hzz : z * z = 1) {r : G} (hr : r ∈ R) :
    ∃ l ∈ L, l ∈ R ∧ (r = l ∨ r = l * z) := by
  obtain ⟨l, hl, hrl⟩ := shape_one_decomp d hQ2 hE (hRC hr)
  refine ⟨l, hl, ?_, hrl⟩
  rcases hrl with rfl | rfl
  · exact hr
  · have := mul_mem hr hzR
    simpa [mul_assoc, hzz] using this

@[expose] def omegaG (L R : Subgroup G) (z : G) : Set G :=
  {p | p ∈ L ∧ p ∈ R ∧ (p = 1 ∨ p ∈ FusionSet L z)}

theorem conj_mem_R_iff (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hzR : z ∈ R) {r : G} (hr : r ∈ R) :
    (∃ g : G, g * z * g⁻¹ = r) ↔ ∃ w ∈ omegaG L R z, r = z * w := by
  have hzz := d.mul_self
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨l, hl, hlR, hrl⟩ := exists_decomp_of_mem_R d hQ2 hE hRC hzR hzz hr
    have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hl)
    rcases hrl with hrl | hrl
    · exact absurd (hrl ▸ hl) (hg ▸ not_conj_mem_L h d hQ2 g)
    · have hr' : r = z * l := by rw [hrl, hlz]
      refine ⟨l, ⟨hl, hlR, ?_⟩, hr'⟩
      by_cases hl1 : l = 1
      · exact Or.inl hl1
      · right
        have hsq : r * r = 1 := by
          rw [← hg]
          calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
            _ = 1 := by rw [hzz]; group
        have hll : l * l = 1 := by
          have : r * r = l * l := by
            calc r * r = z * l * (z * l) := by rw [hr']
              _ = z * (l * z) * l := by group
              _ = z * (z * l) * l := by rw [hlz]
              _ = (z * z) * (l * l) := by group
              _ = l * l := by rw [hzz, one_mul]
          rw [← this]
          exact hsq
        refine ⟨hl, orderOf_eq_prime (by rw [← sq] at hll; exact hll) hl1, g, ?_⟩
        rw [hg, hr']
  · rintro ⟨w, ⟨hwL, hwR, hw⟩, hrw⟩
    rcases hw with rfl | ⟨-, -, g, hg⟩
    · exact ⟨1, by simp [hrw]⟩
    · exact ⟨g, by rw [hg, hrw]⟩

theorem prodCnt_omega_eq (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hzR : z ∈ R) {x y₀ : G} (hy₀R : y₀ ∈ R)
    (hy₀c : ∀ r ∈ R, r * y₀ = y₀ * r) (hxz : x * z * x⁻¹ = y₀ * z)
    (hconj : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hconj' : ∀ r ∈ R, x⁻¹ * r * x ∈ R) :
    prodCnt {w : ↥R | (w : G) ∈ omegaG L R z} 1 =
      prodCnt {w : ↥R | (w : G) ∈ omegaG L R z} ⟨y₀, hy₀R⟩ := by
  have hzz := d.mul_self
  set zR : ↥R := ⟨z, hzR⟩ with hzR_def
  set Ω : Set ↥R := {w | (w : G) ∈ omegaG L R z} with hΩ
  set T : Set ↥R := {t | ∃ g : G, g * z * g⁻¹ = (t : G)} with hT
  let φ : ↥R ≃* ↥R :=
    { toFun := fun r => ⟨x * r * x⁻¹, hconj r r.2⟩
      invFun := fun r => ⟨x⁻¹ * r * x, hconj' r r.2⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφT : ∀ r, φ r ∈ T ↔ r ∈ T := by
    intro r
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨x⁻¹ * g, ?_⟩
      calc x⁻¹ * g * z * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * z * g⁻¹) * x := by group
        _ = r := by
            have : g * z * g⁻¹ = x * (r : G) * x⁻¹ := hg
            rw [this]; group
    · rintro ⟨g, hg⟩
      refine ⟨x * g, ?_⟩
      calc x * g * z * (x * g)⁻¹ = x * (g * z * g⁻¹) * x⁻¹ := by group
        _ = x * (r : G) * x⁻¹ := by rw [hg]
  have hTeq : T = {t | ∃ w ∈ Ω, t = zR * w} := by
    ext t
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    constructor
    · intro ht
      obtain ⟨w, hw, hwt⟩ := (conj_mem_R_iff h d hQ2 hE hRC hzR t.2).1 ht
      exact ⟨⟨w, hw.2.1⟩, hw, Subtype.ext hwt⟩
    · rintro ⟨w, hw, hwt⟩
      refine (conj_mem_R_iff h d hQ2 hE hRC hzR t.2).2 ⟨w, hw, ?_⟩
      rw [hwt]
      rfl
  have hz2 : zR * zR = 1 := Subtype.ext hzz
  have hzc : ∀ r : ↥R, r * zR = zR * r := fun r =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (hRC r.2))
  have hΩ2 : ∀ w ∈ Ω, w * w = 1 := by
    rintro ⟨w, hwR⟩ ⟨hwL, -, hw⟩
    rcases hw with rfl | ⟨-, hw2, -⟩
    · exact Subtype.ext (one_mul 1)
    · refine Subtype.ext ?_
      have : w ^ 2 = 1 := hw2 ▸ pow_orderOf_eq_one w
      rw [sq] at this
      exact this
  have e1 := tripleCnt_eq_prodCnt hz2 hzc hΩ2 (1 : ↥R)
  have e2 := tripleCnt_eq_prodCnt hz2 hzc hΩ2 (⟨y₀, hy₀R⟩ : ↥R)
  have e3 := tripleCnt_map φ hφT zR
  have e4 : φ zR = zR * ⟨y₀, hy₀R⟩ := by
    refine Subtype.ext ?_
    show x * z * x⁻¹ = z * y₀
    rw [hxz]
    exact (hy₀c z hzR).symm
  rw [← hTeq] at e1 e2
  rw [mul_one] at e1
  rw [e4] at e3
  rw [← e1, ← e2, ← e3]

section PermSide

@[expose] def embL (e : L ≃* alternatingGroup (Fin n)) : L →* Equiv.Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom

variable (e : L ≃* alternatingGroup (Fin n))

omit [Finite G] in
theorem embL_injective : Function.Injective (embL e) :=
  Subtype.coe_injective.comp e.injective

omit [Finite G] in
theorem embL_mem_alt (l : L) : embL e l ∈ alternatingGroup (Fin n) := (e l).2

omit [Finite G] in
theorem exists_embL_eq {p : Equiv.Perm (Fin n)} (hp : p ∈ alternatingGroup (Fin n)) :
    ∃ l : L, embL e l = p := ⟨e.symm ⟨p, hp⟩, by simp [embL]⟩

@[expose] def ppOf (R : Subgroup G) : Subgroup (Equiv.Perm (Fin n)) :=
  (R.subgroupOf L).map (embL e)

omit [Finite G] in
theorem mem_ppOf {R : Subgroup G} {p : Equiv.Perm (Fin n)} :
    p ∈ ppOf e R ↔ ∃ l : L, (l : G) ∈ R ∧ embL e l = p := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩

omit [Finite G] in
theorem ppOf_le_alt (R : Subgroup G) : ppOf e R ≤ alternatingGroup (Fin n) := by
  intro p hp
  obtain ⟨l, -, rfl⟩ := (mem_ppOf e).1 hp
  exact embL_mem_alt e l

omit [Finite G] in
theorem ppOf_isPGroup {R : Subgroup G} (hR : IsPGroup 2 R) : IsPGroup 2 (ppOf e R) :=
  (hR.comap_subtype (K := L)).map (embL e)

omit [Finite G] in
theorem isNear_coe_iff (l : L) :
    IsNear e (l : G) ↔ 4 ≤ Nat.card (Function.fixedPoints (embL e l)) := by
  constructor
  · rintro ⟨hy, h4⟩
    exact h4
  · intro h4
    exact ⟨l.2, h4⟩

theorem ppOf_maximal (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hzR : z ∈ R)
    (hRmax : ∀ R' : Subgroup G, R' ≤ centralizer ({z} : Set G) → IsPGroup 2 R' → R ≤ R' →
      R' = R)
    (P' : Subgroup (Equiv.Perm (Fin n))) (hP'A : P' ≤ alternatingGroup (Fin n))
    (hP' : IsPGroup 2 P') (hle : ppOf e R ≤ P') : P' = ppOf e R := by
  have hzz := d.mul_self
  set Q' : Subgroup G := (P'.comap (embL e)).map L.subtype with hQ'
  have hQ'L : Q' ≤ L := Subgroup.map_subtype_le _
  have hQ'p : IsPGroup 2 Q' :=
    (hP'.comap_of_injective (embL e) (embL_injective e)).map L.subtype
  have hmemQ : ∀ l : L, embL e l ∈ P' → (l : G) ∈ Q' := fun l hl => ⟨l, hl, rfl⟩
  have hRle : R ≤ Subgroup.zpowers z ⊔ Q' := by
    intro r hr
    obtain ⟨l, hl, hlR, hrl⟩ := exists_decomp_of_mem_R d hQ2 hE hRC hzR hzz hr
    have hlQ : l ∈ Q' := hmemQ ⟨l, hl⟩ (hle ((mem_ppOf e).2 ⟨⟨l, hl⟩, hlR, rfl⟩))
    rcases hrl with rfl | rfl
    · exact Subgroup.mem_sup_right hlQ
    · exact mul_mem (Subgroup.mem_sup_right hlQ)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.order, pow_one])
  have hnorm : Q' ≤ normalizer (Subgroup.zpowers z : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro q hq
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have := mem_centralizer_singleton_iff.1 (le_centralizer_single h d (hQ'L hq))
    exact (Commute.zpow_left (Commute.symm this) j).eq
  have hQz : IsPGroup 2 ↥(Q' ⊔ Subgroup.zpowers z) :=
    IsPGroup.to_sup_of_normal_right' hQ'p hzp hnorm
  have hsub : R ⊔ Q' ≤ Q' ⊔ Subgroup.zpowers z :=
    sup_le (hRle.trans (by rw [sup_comm])) le_sup_left
  have hRQ : IsPGroup 2 ↥(R ⊔ Q') := hQz.to_le hsub
  have hle2 : R ⊔ Q' ≤ centralizer ({z} : Set G) :=
    sup_le hRC (hQ'L.trans (le_centralizer_single h d))
  have hEq := hRmax (R ⊔ Q') hle2 hRQ le_sup_left
  have hQR : Q' ≤ R := by
    rw [← hEq]
    exact le_sup_right
  refine le_antisymm (fun p hp => ?_) hle
  obtain ⟨l, rfl⟩ := exists_embL_eq e (hP'A hp)
  exact (mem_ppOf e).2 ⟨l, hQR (hmemQ l hp), rfl⟩

theorem embL_mem_farSet_iff (h : Setting G L n) (d : Cyc L Q z) {R : Subgroup G}
    (hFC : FarClass) (hfar : ∀ y ∈ FusionSet L z, ¬ IsNear e y) {y₀ : G}
    (hy₀Y : y₀ ∈ FusionSet L z) (l : L) :
    embL e l ∈ farSet n (ppOf e R) ↔ (l : G) ∈ omegaG L R z := by
  have hfix : ∀ y ∈ FusionSet L z, ∀ hy : y ∈ L,
      Nat.card (Function.fixedPoints (embL e ⟨y, hy⟩)) ≤ 3 := fun y hy hyL => by
    have := hfar y hy
    rw [show y = ((⟨y, hyL⟩ : L) : G) from rfl, isNear_coe_iff] at this
    omega
  constructor
  · intro hl
    rcases hl with hl1 | ⟨hlP, hl2, hl1, hf, -⟩
    · have : l = 1 := embL_injective e (by simpa using hl1)
      subst this
      exact ⟨one_mem _, one_mem _, Or.inl rfl⟩
    · obtain ⟨l', hl'R, hl'⟩ := (mem_ppOf e).1 hlP
      have hll' : l' = l := embL_injective e hl'
      subst hll'
      have hll : l' * l' = 1 := embL_injective e (by rw [map_mul, map_one]; exact hl2)
      have hl'1 : l' ≠ 1 := fun h1 => hl1 (by rw [h1, map_one])
      have hl'2 : orderOf (l' : G) = 2 := by
        refine orderOf_eq_prime ?_ (fun h1 => hl'1 (Subtype.ext h1))
        rw [sq]
        exact congrArg Subtype.val hll
      refine ⟨l'.2, hl'R, Or.inr ?_⟩
      have hnear : ¬ IsNear e (l' : G) := by
        rw [isNear_coe_iff]
        omega
      obtain ⟨l₁, hl₁, hl₁y⟩ := hFC G L n e y₀ hy₀Y.1 (l' : G) l'.2 hy₀Y.2.1 hl'2
        (hfar y₀ hy₀Y) hnear
      rw [← hl₁y]
      exact FusionSet.conj h d hy₀Y hl₁
  · rintro ⟨-, hlR, hl⟩
    rcases hl with hl1 | hlY
    · have : l = 1 := Subtype.ext hl1
      subst this
      exact Or.inl (by simp)
    · right
      have hl'1 : l ≠ 1 := fun h1 => by
        have : (l : G) = 1 := by rw [h1]; rfl
        rw [this] at hlY
        exact absurd hlY.2.1 (by simp)
      have hsq : (l : G) * l = 1 := by
        rw [← sq]
        exact hlY.2.1 ▸ pow_orderOf_eq_one _
      refine ⟨(mem_ppOf e).2 ⟨l, hlR, rfl⟩, ?_, ?_, hfix _ hlY l.2, ?_⟩
      · rw [← map_mul]
        have : l * l = 1 := Subtype.ext hsq
        rw [this, map_one]
      · exact fun h1 => hl'1 (embL_injective e (by rw [h1, map_one]))
      · exact Equiv.Perm.mem_alternatingGroup.1 (embL_mem_alt e l)

end PermSide

theorem prodCnt_transport (e : L ≃* alternatingGroup (Fin n)) (h : Setting G L n)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hzR : z ∈ R) {x y₀ : G} (hy₀R : y₀ ∈ R)
    (hy₀L : y₀ ∈ L) (hy₀c : ∀ r ∈ R, r * y₀ = y₀ * r) (hxz : x * z * x⁻¹ = y₀ * z)
    (hconj : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hconj' : ∀ r ∈ R, x⁻¹ * r * x ∈ R)
    (S : Set (Equiv.Perm (Fin n)))
    (hS : ∀ l : L, embL e l ∈ S ↔ (l : G) ∈ omegaG L R z)
    (hS' : ∀ p ∈ S, ∃ l : L, embL e l = p) :
    prodCnt S 1 = prodCnt S (embL e ⟨y₀, hy₀L⟩) := by
  have h1 := prodCnt_omega_eq h d hQ2 hE hRC hzR hy₀R hy₀c hxz hconj hconj'
  have tR : ∀ g : ↥R, prodCnt {w : ↥R | (w : G) ∈ omegaG L R z} g =
      prodCnt (omegaG L R z) (g : G) := fun g =>
    (prodCnt_inj R.subtype Subtype.coe_injective (fun w => Iff.rfl)
      (fun w hw => ⟨⟨w, hw.2.1⟩, rfl⟩) g).symm
  have tL : ∀ l : ↥L, prodCnt (omegaG L R z) (l : G) =
      prodCnt {l : ↥L | (l : G) ∈ omegaG L R z} l := fun l =>
    prodCnt_inj L.subtype Subtype.coe_injective (fun w => Iff.rfl)
      (fun w hw => ⟨⟨w, hw.1⟩, rfl⟩) l
  have tP : ∀ l : ↥L, prodCnt S (embL e l) =
      prodCnt {l : ↥L | (l : G) ∈ omegaG L R z} l := fun l =>
    prodCnt_inj (embL e) (embL_injective e) hS hS' l
  have e1 := (tR 1).trans (tL ⟨1, one_mem _⟩)
  have e2 := (tR ⟨y₀, hy₀R⟩).trans (tL ⟨y₀, hy₀L⟩)
  have t1 : prodCnt S 1 = prodCnt {l : ↥L | (l : G) ∈ omegaG L R z} ⟨1, one_mem _⟩ := by
    have := tP ⟨1, one_mem _⟩
    rwa [show embL e ⟨1, one_mem L⟩ = 1 from map_one (embL e)] at this
  exact t1.trans ((e1.symm.trans (h1.trans e2)).trans (tP ⟨y₀, hy₀L⟩).symm)

theorem farOnlyFalse_of_farCount (hFC : FarClass) (hc : ∀ n, 12 ≤ n → FarCount n) :
    FarOnlyFalse := by
  intro G _ _ L n Q z h d hQ2 hE hn e hfar
  obtain ⟨R, hRC, hRp, hRmax⟩ := exists_maximal_two_subgroup (centralizer ({z} : Set G))
  obtain ⟨x, y₀, hy₀R, hy₀L, hy₀1, hy₀2, hy₀c, hxz, -, hconj, hconj'⟩ :=
    exists_common_involution_norm h d hQ2 hE hRC hRp hRmax
  have hzR : z ∈ R := mem_of_maximal d hRC hRp hRmax
  have hy₀ord : orderOf y₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hy₀2) hy₀1
  have hy₀Y : y₀ ∈ FusionSet L z := ⟨hy₀L, hy₀ord, x, by rw [hxz]; exact (hy₀c z hzR).symm⟩
  have hy₀Ω : y₀ ∈ omegaG L R z := ⟨hy₀L, hy₀R, Or.inr hy₀Y⟩
  have hS' : ∀ p ∈ farSet n (ppOf e R), ∃ l : L, embL e l = p := by
    rintro p (hp | ⟨hp, -⟩)
    · exact ⟨1, by rw [map_one, hp]⟩
    · obtain ⟨l', -, hl'⟩ := (mem_ppOf e).1 hp
      exact ⟨l', hl'⟩
  have key := prodCnt_transport e h d hQ2 hE hRC hzR hy₀R hy₀L hy₀c hxz hconj hconj'
    (farSet n (ppOf e R)) (fun l => embL_mem_farSet_iff e h d hFC hfar hy₀Y l) hS'
  refine hc n hn (ppOf e R) (ppOf_le_alt e R) (ppOf_isPGroup e hRp)
    (fun P' hP'A hP' hle => ppOf_maximal e h d hQ2 hE hRC hzR hRmax P' hP'A hP' hle)
    (embL e ⟨y₀, hy₀L⟩) ((mem_ppOf e).2 ⟨⟨y₀, hy₀L⟩, hy₀R, rfl⟩)
    ((embL_mem_farSet_iff e h d hFC hfar hy₀Y ⟨y₀, hy₀L⟩).2 hy₀Ω)
    (fun h1' => hy₀1 (congrArg Subtype.val (embL_injective e (h1'.trans (map_one _).symm))))
    ?_ key
  rintro p hp
  obtain ⟨l', hl'R, rfl⟩ := (mem_ppOf e).1 hp
  rw [← map_mul, ← map_mul]
  exact congrArg (embL e) (Subtype.ext (hy₀c l' hl'R))

end CFSG.OddStandard.AltStdSec
