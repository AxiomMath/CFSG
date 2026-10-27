module

public import CFSG.CGT.Stroth77.Section224FrameStruct
public import CFSG.CGT.Stroth77.Section225FrameExports
public import CFSG.CGT.Stroth77.Section226A
public import CFSG.CGT.Stroth77.WeakTypeFamilyOneComm
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

open Matrix

theorem StrothTypeIndex.two_le_k_of_familyOne {τ : StrothTypeIndex} (hfam : τ.m + 1 = τ.n)
    (hm : 2 ≤ τ.m) (i : Fin 3) : 2 ≤ τ.k i := by
  rw [τ.k_eq]
  fin_cases i <;> simp <;> omega

namespace DeviationGeneric

open Stroth225Frame Stroth224Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

end DeviationGeneric

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

namespace StrothFrame.IsD

open DeviationGeneric Stroth225Frame Stroth224Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

theorem stroth_2_24_frame_a (h : F.IsD D dD) (hmn : τ.m + 1 = τ.n) (hm : 2 ≤ τ.m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G),
      z * z = 1 → z ∈ omegaIn 1 D :=
  fun _ hz hz2 => h.mem_omegaIn_one_of_mul_self_familyOne hmn
    (StrothTypeIndex.two_le_k_of_familyOne hmn hm) (h.setting hns) hz hz2

omit [Finite G] in
private theorem pow_two_pow_eq_one_of_addEquiv' {B : Subgroup G} {k : ℕ}
    (e : Additive B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) {b : G}
    (hb : b ∈ B) : b ^ (2 ^ (k + 1)) = 1 := by
  have hv : ∀ v : ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)),
      (2 ^ (k + 1) : ℕ) • v = 0 := by
    intro v
    have h1 : (2 : ZMod (2 ^ k)) ^ (k + 1) = 0 := by
      rw [pow_succ, show (2 : ZMod (2 ^ k)) ^ k = 0 by exact_mod_cast ZMod.natCast_self (2 ^ k),
        zero_mul]
    have h2 : (2 : ZMod (2 ^ (k + 1))) ^ (k + 1) = 0 := by
      exact_mod_cast ZMod.natCast_self (2 ^ (k + 1))
    obtain ⟨p, q, r⟩ := v
    simp only [Prod.smul_mk, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, h1, h2, zero_mul]
    rfl
  have h := hv (e (Additive.ofMul ⟨b, hb⟩))
  rw [← map_nsmul, ← ofMul_pow] at h
  have h' : (⟨b, hb⟩ : B) ^ (2 ^ (k + 1)) = 1 := by
    apply Additive.ofMul.injective
    apply e.injective
    rw [h, ofMul_one, map_zero]
  simpa using congrArg Subtype.val h'

omit [Finite G] in
private theorem card_of_addEquiv' {B : Subgroup G} {k : ℕ}
    (e : Additive B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) :
    Nat.card B = 2 ^ (k + (k + 1) + (k + 1)) := by
  rw [← Nat.card_congr (Additive.toMul.symm.trans e.toEquiv).symm, Nat.card_prod,
    Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
  ring

theorem devMat_eq_devD_of_pow_eq_one (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n)
    (hk : ∀ i, 2 ≤ τ.k i) (hS : Local.Setting (F.S : Subgroup G) D) {x : G}
    (hx : x ∈ 𝓡[(F.S : Subgroup G), D]) (hxD : x ∉ D) (hpow : x ^ (2 ^ (τ.m + 1)) = 1) :
    devMat dD hk x hx = devD ∧ x ^ (2 ^ τ.m) ≠ 1 := by
  obtain ⟨hr, hb, hq⟩ := h.struct_familyOne hfam hk hS hx
  have hkk := familyOne_k hfam
  have hx2D := mul_self_mem_of_mem_R dD hk h.cent hx
  have hpow2 : (⟨x * x, hx2D⟩ : D) ^ (2 ^ τ.m) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← pow_two, ← pow_mul, ← pow_succ']
    exact hpow
  have h1 : barD dD hk ⟨x * x, hx2D⟩ 1 = 0 := barD_eq_zero_of_pow hk hpow2 (by rw [hkk]; simp)
  have h2 : barD dD hk ⟨x * x, hx2D⟩ 2 = 0 := barD_eq_zero_of_pow hk hpow2 (by rw [hkk]; simp)
  have hq1 := congrFun hq 1
  have hq2 := congrFun hq 2
  have hq0 := congrFun hq 0
  rw [show sqBar dD hk h.cent x hx 1 = barD dD hk ⟨x * x, hx2D⟩ 1 from rfl, h1] at hq1
  rw [show sqBar dD hk h.cent x hx 2 = barD dD hk ⟨x * x, hx2D⟩ 2 from rfl, h2] at hq2
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_zero] at hq0 hq1 hq2
  have hne : sqBar dD hk h.cent x hx ≠ 0 :=
    fun h0 => hxD (h.mem_of_sqBar_eq_zero_of_mem_familyOne hfam hk hS hx h0)
  have h11 : devMat dD hk x hx 1 1 = 1 := by
    by_contra h11
    have h11' : devMat dD hk x hx 1 1 = 0 := by
      revert h11; generalize devMat dD hk x hx 1 1 = a; intro h11; fin_cases a
      · rfl
      · exact absurd rfl h11
    apply hne
    rw [hq]
    funext i
    fin_cases i
    · exact h11'
    · exact hq1.symm
    · exact hq2.symm
  have hd : devMat dD hk x hx = devD := by
    obtain ⟨r1, r2, r3⟩ := hr
    obtain ⟨b1, b2, b3⟩ := hb
    have key : ∀ (f : Matrix (Fin 3) (Fin 3) (ZMod 2)), f 0 0 = 0 → f 0 1 = 0 → f 0 2 = 0 →
        f 1 0 = 0 → f 2 0 = 0 → f 1 2 = 0 → f 2 1 = 0 → f 1 1 = 1 → f 2 2 = 1 → f = devD := by
      intro f a1 a2 a3 a4 a5 a6 a7 a8 a9
      rw [Matrix.eta_fin_three f, a1, a2, a3, a4, a5, a6, a7, a8, a9]
      decide
    exact key _ r1 r2 r3 hq1.symm hq2.symm b1 b2 h11 (b3 ▸ h11)
  refine ⟨hd, fun hm => ?_⟩
  have hq0' : barD dD hk ⟨x * x, hx2D⟩ 0 = 1 := by
    rw [show barD dD hk ⟨x * x, hx2D⟩ 0 = sqBar dD hk h.cent x hx 0 from rfl, hq0, h11]
  have hm1 : (⟨x * x, hx2D⟩ : D) ^ (2 ^ (τ.m - 1)) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have hm0 : 1 ≤ τ.m := by have := hk 0; rw [hkk] at this; simp at this; omega
    rw [← pow_two, ← pow_mul, ← pow_succ', show τ.m - 1 + 1 = τ.m by omega]
    exact hm
  have hk0 : τ.m - 1 + 1 ≤ τ.k 0 := by
    have := hk 0; rw [hkk] at this ⊢; simp at this ⊢; omega
  have := barD_eq_zero_of_pow (dD := dD) hk hm1 (i := 0) hk0
  rw [hq0'] at this
  exact absurd this (by decide)

theorem stroth_2_24_frame_b (h : F.IsD D dD) (hmn : τ.m + 1 = τ.n) (hm : 2 ≤ τ.m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (k : ℕ) (hk : k ≤ τ.n - 1) (B : Subgroup G)
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G))
    (hB : Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1))))) :
    B ≤ D := by
  obtain ⟨e⟩ := hB
  have hkk := StrothTypeIndex.two_le_k_of_familyOne hmn hm
  have hS := h.setting hns
  have hkm : k ≤ τ.m := by omega
  have hexp : ∀ x ∈ B, x ^ (2 ^ (τ.m + 1)) = 1 := fun x hx => by
    obtain ⟨j, hj⟩ : ∃ j, τ.m + 1 = k + 1 + j := ⟨τ.m - k, by omega⟩
    rw [hj, pow_add, pow_mul, pow_two_pow_eq_one_of_addEquiv' e hx, one_pow]
  have hdev : ∀ x (hxB : x ∈ B), x ∉ D → devMat dD hkk x (hBR hxB) = devD ∧ k = τ.m := by
    intro x hxB hxD
    obtain ⟨hd, hne⟩ := h.devMat_eq_devD_of_pow_eq_one hmn hkk hS (hBR hxB) hxD (hexp x hxB)
    refine ⟨hd, ?_⟩
    by_contra hkne
    apply hne
    obtain ⟨j, hj⟩ : ∃ j, τ.m = k + 1 + j := ⟨τ.m - k - 1, by omega⟩
    rw [hj, pow_add, pow_mul, pow_two_pow_eq_one_of_addEquiv' e hxB, one_pow]
  by_contra hBD
  obtain ⟨x, hxB, hxD⟩ := Set.not_subset.mp hBD
  obtain ⟨hdx, rfl⟩ := hdev x hxB hxD
  have hBcomm : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y := fun y hy z hz => by
    have h1 := e.map_add (Additive.ofMul ⟨y, hy⟩) (Additive.ofMul ⟨z, hz⟩)
    have h2 := e.map_add (Additive.ofMul ⟨z, hz⟩) (Additive.ofMul ⟨y, hy⟩)
    rw [add_comm (e _) (e _), ← h2] at h1
    have h3 := congrArg Subtype.val (Additive.ofMul.injective (e.injective h1))
    simpa using h3
  have hcard : Nat.card B = Nat.card D := by
    rw [card_of_addEquiv' e, dD.card, familyOne_k hmn]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
  have hrel : D.relIndex B ≤ 2 := by
    let φ : ↥B →* Multiplicative (ZMod 2) :=
      MonoidHom.mk' (fun y => Multiplicative.ofAdd (devMat dD hkk y (hBR y.2) 1 1)) (fun y z => by
        have h := devMat_mul (dD := dD) hkk (hBR y.2) (hBR z.2)
        simp only [Subgroup.coe_mul]
        rw [h]
        rfl)
    have hker : φ.ker ≤ D.subgroupOf B := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      by_contra hyD
      have h11 : devMat dD hkk y (hBR y.2) 1 1 = 0 := (MonoidHom.mem_ker).mp hy
      rw [(hdev y y.2 hyD).1] at h11
      exact absurd h11 (by decide)
    have h1 : (D.subgroupOf B).index ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
    have h2 : φ.ker.index ≤ 2 := by
      rw [Subgroup.index_ker]
      refine (Subgroup.card_le_card_group φ.range).trans ?_
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have h3 : 0 < φ.ker.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    exact (Nat.le_of_dvd h3 h1).trans h2
  have hC : 2 * Nat.card ↥(D ⊓ Subgroup.centralizer ({x} : Set G)) < Nat.card D := by
    let ψ : ↥D →* Multiplicative (ZMod 2 × ZMod 2) :=
      MonoidHom.mk' (fun d => Multiplicative.ofAdd (barD dD hkk d 1, barD dD hkk d 2))
        (fun d d' => by
          rw [barD_mul, Pi.add_apply, Pi.add_apply]
          rfl)
    have hsurj : Function.Surjective ψ := by
      intro w
      obtain ⟨d, hd⟩ := barD_surjective (dD := dD) hkk ![0, (Multiplicative.toAdd w).1,
        (Multiplicative.toAdd w).2]
      refine ⟨d, ?_⟩
      show Multiplicative.ofAdd (barD dD hkk d 1, barD dD hkk d 2) = w
      rw [hd]
      rfl
    have hcardψ := Subgroup.card_ker_mul_card_range ψ
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
      Nat.card_prod, Nat.card_zmod] at hcardψ
    have hinj : Nat.card ↥(D ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Nat.card ψ.ker := by
      refine Nat.card_le_card_of_injective
        (fun g => ⟨⟨g, (Subgroup.mem_inf.mp g.2).1⟩, ?_⟩) ?_
      · rw [MonoidHom.mem_ker]
        have hgx : x * (g : G) = (g : G) * x :=
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2).symm
        have hval := devMat_val_eq (dD := dD) hkk x (hBR hxB) ⟨g, (Subgroup.mem_inf.mp g.2).1⟩
        have h1 : (⟨x * (g : G) * x⁻¹ * (g : G)⁻¹, omegaIn_le 1 D
            (commutator_mem_omegaIn_one dD (hBR hxB) (Subgroup.mem_inf.mp g.2).1)⟩ : D) = 1 :=
          Subtype.ext (by simp only [Subgroup.coe_one]; rw [hgx]; group)
        rw [h1, ofMul_one, map_zero, hdx] at hval
        have h2 := torusHalf_injective τ.k (one_le_of_two_le hkk)
          (hval.symm.trans (map_zero _).symm)
        obtain ⟨a1, a2⟩ := (devD_mulVec_eq_zero_iff _).mp h2
        show Multiplicative.ofAdd (barD dD hkk _ 1, barD dD hkk _ 2) = 1
        rw [a1, a2]
        rfl
      · intro g g' hgg
        exact Subtype.ext (congrArg (fun y : ψ.ker => ((y : D) : G)) hgg)
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    omega
  exact false_of_relIndex_mul_card_lt hBcomm hcard hxB hrel hC

end StrothFrame.IsD

end CFSG.CGT.Stroth77
