module

public import CFSG.Certificates.Kernel.L52Insp443.Cover
public import CFSG.Literature.GL52Chain
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.L52Insp443.Act

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.Misc.GLM.Ech CFSG.Literature.GL52

@[expose] noncomputable def actG (g : G) (F : ℕ) : ℕ := actK (mcode (g : Mat)) F

theorem actG_mul (g h : G) {F : ℕ} (hF : F < 2 ^ 32) : actG (g * h) F = actG g (actG h F) :=
  actK_mul g h hF

theorem actG_one {F : ℕ} (hF : F < 2 ^ 32) : actG 1 F = F := actK_one hF

theorem actG_lt (g : G) (F : ℕ) : actG g F < 2 ^ 32 := actK_lt g F

theorem actG_inv {g : G} {F F' : ℕ} (hF : F < 2 ^ 32) (h : actG g F = F') : actG g⁻¹ F' = F := by
  rw [← h, ← actG_mul _ _ hF, inv_mul_cancel, actG_one hF]

@[expose] noncomputable def stabK (F₀ : ℕ) (hF₀ : F₀ < 2 ^ 32) : Subgroup G where
  carrier := {g | actG g F₀ = F₀}
  mul_mem' {a b} ha hb := by
    change actG (a * b) F₀ = F₀
    rw [actG_mul _ _ hF₀, Set.mem_setOf_eq.mp hb, Set.mem_setOf_eq.mp ha]
  one_mem' := actG_one hF₀
  inv_mem' {a} ha := actG_inv hF₀ ha

theorem mem_stabK {F₀ : ℕ} (hF₀ : F₀ < 2 ^ 32) (g : G) : g ∈ stabK F₀ hF₀ ↔ actG g F₀ = F₀ :=
  Iff.rfl

variable {F₀ : ℕ} (hF₀ : F₀ < 2 ^ 32) {m : ℕ} (t : Fin m → G) (F : Fin m → ℕ)
  (ht : ∀ k, actG (t k) F₀ = F k)

include ht in
theorem inv_mul_mem_stabK (j : Fin m) (y : G) :
    (t j)⁻¹ * y ∈ stabK F₀ hF₀ ↔ actG y F₀ = F j := by
  rw [mem_stabK, actG_mul _ _ hF₀]
  constructor
  · intro h
    have e := congrArg (actG (t j)) h
    rw [← actG_mul _ _ (actG_lt _ _), mul_inv_cancel, actG_one (actG_lt _ _), ht j] at e
    exact e
  · intro h
    rw [h]
    exact actG_inv hF₀ (ht j)

include ht in
theorem schreier_mem_stabK {x : G} {j k : Fin m} (h : actG x (F k) = F j) :
    (t j)⁻¹ * (x * t k) ∈ stabK F₀ hF₀ := by
  rw [inv_mul_mem_stabK hF₀ t F ht, actG_mul _ _ hF₀, ht k, h]

variable {s : Set G} (hs : Subgroup.closure s = ⊤)

include hs ht in
theorem card_stabK (hinj : Function.Injective F) (hcov : ∀ x ∈ s, ∀ k, ∃ j, actG x (F k) = F j)
    (h0 : ∃ k, t k ∈ stabK F₀ hF₀) : Nat.card G = m * Nat.card (stabK F₀ hF₀) := by
  refine card_eq_mul_of_cover hs (stabK F₀ hF₀) t (fun g => actG g F₀) (fun g x hx => ?_)
    (fun j k e => hinj ?_) (fun x hx k => ?_) h0
  · change actG (g * x) F₀ = actG g F₀
    rw [actG_mul _ _ hF₀, (mem_stabK hF₀ x).mp hx]
  · change actG (t j) F₀ = actG (t k) F₀ at e
    rw [ht, ht] at e
    exact e
  · obtain ⟨j, hj⟩ := hcov x hx k
    exact ⟨j, schreier_mem_stabK hF₀ t F ht hj⟩

include hs ht in
theorem stabK_le (hinj : Function.Injective F) (P : Subgroup G)
    (hcov : ∀ x ∈ s, ∀ k, ∃ j, actG x (F k) = F j ∧ (t j)⁻¹ * (x * t k) ∈ P) {k₀ : Fin m}
    (h₀ : t k₀ = 1) : stabK F₀ hF₀ ≤ P := by
  refine le_of_schreier hs (stabK F₀ hF₀) t (fun g => actG g F₀) (fun g x hx => ?_)
    (fun j k e => hinj ?_) P (fun x hx k => ?_) h₀
  · change actG (g * x) F₀ = actG g F₀
    rw [actG_mul _ _ hF₀, (mem_stabK hF₀ x).mp hx]
  · change actG (t j) F₀ = actG (t k) F₀ at e
    rw [ht, ht] at e
    exact e
  · obtain ⟨j, hj, hP⟩ := hcov x hx k
    exact ⟨j, schreier_mem_stabK hF₀ t F ht hj, hP⟩

theorem closure_glAB :
    Subgroup.closure ({glA, glB} : Set G) = ⊤ := by
  apply Subgroup.map_injective glPerm_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← glCert_originalSubgroup_eq, glCert_original,
    MonoidHom.range_eq_map]

@[expose] noncomputable def mvG (g : G) (v : ℕ) : ℕ := mvK (mcode (g : Mat)) v

theorem mvG_mul (g h : G) {v : ℕ} (hv : v < 32) : mvG (g * h) v = mvG g (mvG h v) :=
  mvK_mul g h hv

theorem mvG_one {v : ℕ} (hv : v < 32) : mvG 1 v = v := mvK_one hv

theorem mvG_lt (g : G) {v : ℕ} (hv : v < 32) : mvG g v < 32 := mvK_lt g hv

theorem mvG_inv {g : G} {v : ℕ} (hv : v < 32) : mvG g⁻¹ (mvG g v) = v := by
  rw [← mvG_mul _ _ hv, inv_mul_cancel, mvG_one hv]

theorem mvG_zero (g : G) : mvG g 0 = 0 := by
  obtain ⟨h1, e1⟩ := mvK_mcode (g : Mat) (show 0 < 32 by norm_num)
  refine bvo5_inj h1 (by norm_num) ?_
  change bvo 5 0 (mvK (mcode (g : Mat)) 0) = bvo 5 0 0
  rw [e1, bvo_zero, Matrix.mulVec_zero]

@[expose] noncomputable def subK (bs : List ℕ) : Subgroup G := Subgroup.closure (gD '' {b | b ∈ bs})

theorem fix_of_mem_subK {bs : List ℕ} {v : ℕ} (hv : v < 32)
    (hfix : ∀ b ∈ bs, unitK b = true ∧ mvK b v = v) {g : G} (hg : g ∈ subK bs) : mvG g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    unfold mvG
    rw [mcode_gD (hfix b hb).1]
    exact (hfix b hb).2
  | one => exact mvG_one hv
  | mul x y _ _ hx hy => rw [mvG_mul _ _ hv, hy, hx]
  | inv x _ hx =>
    have e := mvG_inv (g := x) hv
    rw [hx] at e
    exact e

theorem fixK_lt (bs : List ℕ) : fixK bs < 2 ^ 32 := by
  refine Nat.lt_pow_two_of_testBit _ fun u hu => ?_
  rw [Bool.eq_false_iff]
  intro h
  have := ((fixK_testBit bs u).mp h).1
  omega

theorem mapsTo_fix {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true) {x : G}
    (hx : x ∈ Subgroup.normalizer (subK bs : Set G)) {v : ℕ} (hv : (fixK bs).testBit v = true) :
    (fixK bs).testBit (mvG x v) = true := by
  obtain ⟨hv32, hv0, hvb⟩ := (fixK_testBit bs v).mp hv
  rw [fixK_testBit]
  refine ⟨mvG_lt x hv32, fun h0 => hv0 ?_, fun b hb => ?_⟩
  · have e := mvG_inv (g := x) hv32
    rw [h0, mvG_zero] at e
    exact e.symm
  · have hb' : x⁻¹ * gD b * x ∈ subK bs := by
      have hmem : gD b ∈ subK bs := Subgroup.subset_closure ⟨b, hb, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) (gD b)).mp hmem
      rwa [inv_inv] at this
    have hf := fix_of_mem_subK hv32 (fun c hc => ⟨hu c hc, hvb c hc⟩) hb'
    rw [mvG_mul _ _ hv32, mvG_mul _ _ (mvG_lt _ hv32)] at hf
    have e := congrArg (mvG x) hf
    rw [← mvG_mul _ _ (mvG_lt _ (mvG_lt _ hv32)), mul_inv_cancel,
      mvG_one (mvG_lt _ (mvG_lt _ hv32))] at e
    have e2 : mvK b (mvG x v) = mvG (gD b) (mvG x v) := by
      unfold mvG
      rw [mcode_gD (hu b hb)]
    rw [e2]
    exact e

theorem normalizer_le_stabK {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true) :
    Subgroup.normalizer (subK bs : Set G) ≤ stabK (fixK bs) (fixK_lt bs) := by
  intro x hx
  rw [mem_stabK]
  apply Nat.eq_of_testBit_eq
  intro u
  rw [Bool.eq_iff_iff]
  unfold actG
  rw [actK_testBit]
  constructor
  · rintro ⟨v, -, hv, rfl⟩
    exact mapsTo_fix hu hx hv
  · intro h
    have hu32 := ((fixK_testBit bs u).mp h).1
    refine ⟨mvG x⁻¹ u, mvG_lt _ hu32, mapsTo_fix hu (Subgroup.inv_mem _ hx) h, ?_⟩
    change mvG x (mvG x⁻¹ u) = u
    have e := mvG_inv (g := x⁻¹) hu32
    rwa [inv_inv] at e

end CFSG.KC.L52I

end
