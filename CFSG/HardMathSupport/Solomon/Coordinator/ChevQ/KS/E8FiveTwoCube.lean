module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess

section Cube

variable {G H : Type*} [Group G] [Group H]

structure CubeBasis (a b c : G) : Prop where
  comm_ab : Commute a b
  comm_ac : Commute a c
  comm_bc : Commute b c
  pow_a : a ^ 5 = 1
  pow_b : b ^ 5 = 1
  pow_c : c ^ 5 = 1
  inj : Function.Injective fun v : Fin 5 × Fin 5 × Fin 5 =>
    a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ)

theorem CubeBasis.map (φ : G →* H) (hφ : Function.Injective φ) {a b c : G}
    (h : CubeBasis a b c) : CubeBasis (φ a) (φ b) (φ c) where
  comm_ab := h.comm_ab.map φ
  comm_ac := h.comm_ac.map φ
  comm_bc := h.comm_bc.map φ
  pow_a := by rw [← map_pow, h.pow_a, map_one]
  pow_b := by rw [← map_pow, h.pow_b, map_one]
  pow_c := by rw [← map_pow, h.pow_c, map_one]
  inj := fun v w hvw => h.inj (hφ (by
    simp only [map_pow, map_mul]
    exact hvw))

theorem CubeBasis.swap {a b c : G} (h : CubeBasis a b c) : CubeBasis b a c where
  comm_ab := h.comm_ab.symm
  comm_ac := h.comm_bc
  comm_bc := h.comm_ac
  pow_a := h.pow_b
  pow_b := h.pow_a
  pow_c := h.pow_c
  inj := fun v w hvw => by
    have e : ∀ u : Fin 5 × Fin 5 × Fin 5,
        b ^ (u.1 : ℕ) * a ^ (u.2.1 : ℕ) * c ^ (u.2.2 : ℕ) =
          a ^ (u.2.1 : ℕ) * b ^ (u.1 : ℕ) * c ^ (u.2.2 : ℕ) := fun u => by
      rw [(h.comm_ab.symm.pow_pow u.1 u.2.1).eq]
    have h2 := @h.inj (v.2.1, v.1, v.2.2) (w.2.1, w.1, w.2.2) (by
      simp only
      rw [← e v, ← e w]
      exact hvw)
    simp only [Prod.mk.injEq] at h2
    exact Prod.ext h2.2.1 (Prod.ext h2.1 h2.2.2)

theorem CubeBasis.swap' {a b c : G} (h : CubeBasis a b c) : CubeBasis a c b where
  comm_ab := h.comm_ac
  comm_ac := h.comm_ab
  comm_bc := h.comm_bc.symm
  pow_a := h.pow_a
  pow_b := h.pow_c
  pow_c := h.pow_b
  inj := fun v w hvw => by
    have e : ∀ u : Fin 5 × Fin 5 × Fin 5,
        a ^ (u.1 : ℕ) * c ^ (u.2.1 : ℕ) * b ^ (u.2.2 : ℕ) =
          a ^ (u.1 : ℕ) * b ^ (u.2.2 : ℕ) * c ^ (u.2.1 : ℕ) := fun u => by
      rw [mul_assoc, mul_assoc, (h.comm_bc.symm.pow_pow u.2.1 u.2.2).eq]
    have h2 := @h.inj (v.1, v.2.2, v.2.1) (w.1, w.2.2, w.2.1) (by
      simp only
      rw [← e v, ← e w]
      exact hvw)
    simp only [Prod.mk.injEq] at h2
    exact Prod.ext h2.1 (Prod.ext h2.2.2 h2.2.1)

theorem CubeBasis.card {a b c : G} (h : CubeBasis a b c) :
    Nat.card (Subgroup.closure ({a, b, c} : Set G)) = 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact closure_triple_facts h.comm_ab h.comm_ac h.comm_bc h.pow_a h.pow_b h.pow_c h.inj

theorem CubeBasis.line {a b c : G} (h : CubeBasis a b c) (i j : ℕ) (hij : ¬ (5 ∣ i ∧ 5 ∣ j)) :
    Subgroup.closure ({a, b ^ i * c ^ j} : Set G) ≤ Subgroup.closure ({a, b, c} : Set G) ∧
    (Subgroup.closure ({a, b ^ i * c ^ j} : Set G)).relIndex
      (Subgroup.closure ({a, b, c} : Set G)) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hle : Subgroup.closure ({a, b ^ i * c ^ j} : Set G) ≤
      Subgroup.closure ({a, b, c} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
        (pow_mem (Subgroup.subset_closure (by simp)) _)
  refine ⟨hle, relIndex_of_card hle ?_ h.card (by norm_num)⟩
  have hu : Commute a (b ^ i * c ^ j) :=
    (h.comm_ab.pow_right i).mul_right (h.comm_ac.pow_right j)
  have hu5 : (b ^ i * c ^ j) ^ 5 = 1 := by
    rw [((h.comm_bc.pow_pow i j)).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul,
      pow_mul, h.pow_b, h.pow_c]
    simp
  refine card_closure_pair hu h.pow_a hu5 ?_
  intro v w hvw
  simp only at hvw
  have hbc : ∀ t : ℕ, (b ^ i * c ^ j) ^ t = b ^ (i * t) * c ^ (j * t) := fun t => by
    rw [(h.comm_bc.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul]
  rw [hbc, hbc] at hvw
  have hmod : ∀ (x : G) (n : ℕ), x ^ 5 = 1 → x ^ n = x ^ (n % 5) := fun x n hx => by
    conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, hx, one_pow, one_mul]
  have hexp : a ^ (v.1 : ℕ) * b ^ (i * v.2 % 5) * c ^ (j * v.2 % 5) =
      a ^ (w.1 : ℕ) * b ^ (i * w.2 % 5) * c ^ (j * w.2 % 5) := by
    have e1 : a ^ (v.1 : ℕ) * (b ^ (i * (v.2 : ℕ)) * c ^ (j * (v.2 : ℕ))) =
        a ^ (v.1 : ℕ) * b ^ (i * (v.2 : ℕ) % 5) * c ^ (j * (v.2 : ℕ) % 5) := by
      rw [← mul_assoc, ← hmod b _ h.pow_b, ← hmod c _ h.pow_c]
    have e2 : a ^ (w.1 : ℕ) * (b ^ (i * (w.2 : ℕ)) * c ^ (j * (w.2 : ℕ))) =
        a ^ (w.1 : ℕ) * b ^ (i * (w.2 : ℕ) % 5) * c ^ (j * (w.2 : ℕ) % 5) := by
      rw [← mul_assoc, ← hmod b _ h.pow_b, ← hmod c _ h.pow_c]
    rw [← e1, ← e2]
    exact hvw
  have hinj := @h.inj (v.1, ⟨i * v.2 % 5, Nat.mod_lt _ (by norm_num)⟩,
    ⟨j * v.2 % 5, Nat.mod_lt _ (by norm_num)⟩) (w.1, ⟨i * w.2 % 5, Nat.mod_lt _ (by norm_num)⟩,
    ⟨j * w.2 % 5, Nat.mod_lt _ (by norm_num)⟩) hexp
  simp only [Prod.mk.injEq, Fin.mk.injEq] at hinj
  obtain ⟨h1, h2, h3⟩ := hinj
  refine Prod.ext h1 (Fin.ext ?_)
  have hv := v.2.isLt
  have hw := w.2.isLt
  have hcancel : ∀ k : ℕ, ¬ 5 ∣ k → k * (v.2 : ℕ) % 5 = k * (w.2 : ℕ) % 5 → (v.2 : ℕ) = w.2 := by
    intro k hk hkvw
    have hcop : Nat.Coprime 5 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk
    have hmodeq : (v.2 : ℕ) ≡ w.2 [MOD 5] :=
      Nat.ModEq.cancel_left_of_coprime (by simpa using hcop.gcd_eq_one) hkvw
    exact Nat.ModEq.eq_of_lt_of_lt hmodeq hv hw
  by_cases hi : 5 ∣ i
  · have hj : ¬ 5 ∣ j := fun hj => hij ⟨hi, hj⟩
    exact hcancel j hj h3
  · exact hcancel i hi h2

theorem CubeBasis.of_card {a b c : G} (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) (hc : c ^ 5 = 1)
    (hcard : Nat.card (Subgroup.closure ({a, b, c} : Set G)) = 5 ^ 3) : CubeBasis a b c where
  comm_ab := hab
  comm_ac := hac
  comm_bc := hbc
  pow_a := ha
  pow_b := hb
  pow_c := hc
  inj := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    let f : Fin 5 × Fin 5 × Fin 5 → Subgroup.closure ({a, b, c} : Set G) := fun v =>
      ⟨a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ),
        (mem_closure_triple_iff hab hac hbc ha hb hc _).2 ⟨v, rfl⟩⟩
    have hsurj : Function.Surjective f := fun ⟨g, hg⟩ => by
      obtain ⟨v, hv⟩ := (mem_closure_triple_iff hab hac hbc ha hb hc g).1 hg
      exact ⟨v, Subtype.ext hv⟩
    have hbij : Function.Bijective f :=
      hsurj.bijective_of_nat_card_le (by simp [hcard, Nat.card_eq_fintype_card])
    intro v w hvw
    exact hbij.1 (Subtype.ext hvw)

end Cube

namespace CubeCoordinates

open Matrix

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {G : Type*} [Group G] {a b c : G}

def cubeVec (a b c : G) : Fin 3 → G := ![a, b, c]

def cubeCoord (a b c : G) (v : Fin 3 → ZMod 5) : G :=
  a ^ (v 0).val * b ^ (v 1).val * c ^ (v 2).val

@[simp]
theorem cubeCoord_apply (v : Fin 3 → ZMod 5) :
    cubeCoord a b c v = a ^ (v 0).val * b ^ (v 1).val * c ^ (v 2).val := by
  simp [cubeCoord]

theorem cubeCoord_add (h : CubeBasis a b c) (v w : Fin 3 → ZMod 5) :
    cubeCoord a b c (v + w) = cubeCoord a b c v * cubeCoord a b c w := by
  have hpow {g : G} (hg : g ^ 5 = 1) (i j : ZMod 5) :
      g ^ (i + j).val = g ^ i.val * g ^ j.val := by
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]
  simp only [cubeCoord, Pi.add_apply, hpow h.pow_a, hpow h.pow_b, hpow h.pow_c]
  symm
  calc a ^ (v 0).val * b ^ (v 1).val * c ^ (v 2).val *
        (a ^ (w 0).val * b ^ (w 1).val * c ^ (w 2).val)
      = a ^ (v 0).val * b ^ (v 1).val * (c ^ (v 2).val * a ^ (w 0).val) *
        b ^ (w 1).val * c ^ (w 2).val := by simp only [mul_assoc]
    _ = a ^ (v 0).val * b ^ (v 1).val * (a ^ (w 0).val * c ^ (v 2).val) *
        b ^ (w 1).val * c ^ (w 2).val := by rw [(h.comm_ac.symm.pow_pow _ _).eq]
    _ = a ^ (v 0).val * (b ^ (v 1).val * a ^ (w 0).val) * c ^ (v 2).val *
        b ^ (w 1).val * c ^ (w 2).val := by simp only [mul_assoc]
    _ = a ^ (v 0).val * (a ^ (w 0).val * b ^ (v 1).val) * c ^ (v 2).val *
        b ^ (w 1).val * c ^ (w 2).val := by rw [(h.comm_ab.symm.pow_pow _ _).eq]
    _ = a ^ (v 0).val * a ^ (w 0).val * b ^ (v 1).val *
        (c ^ (v 2).val * b ^ (w 1).val) * c ^ (w 2).val := by simp only [mul_assoc]
    _ = a ^ (v 0).val * a ^ (w 0).val * b ^ (v 1).val *
        (b ^ (w 1).val * c ^ (v 2).val) * c ^ (w 2).val :=
      by rw [(h.comm_bc.symm.pow_pow _ _).eq]
    _ = (a ^ (v 0).val * a ^ (w 0).val) * (b ^ (v 1).val * b ^ (w 1).val) *
        (c ^ (v 2).val * c ^ (w 2).val) := by simp only [mul_assoc]

theorem cubeCoord_mem (h : CubeBasis a b c) (v : Fin 3 → ZMod 5) :
    cubeCoord a b c v ∈ Subgroup.closure ({a, b, c} : Set G) := by
  rw [mem_closure_triple_iff h.comm_ab h.comm_ac h.comm_bc h.pow_a h.pow_b h.pow_c]
  refine ⟨(⟨(v 0).val, ZMod.val_lt _⟩, ⟨(v 1).val, ZMod.val_lt _⟩,
    ⟨(v 2).val, ZMod.val_lt _⟩), ?_⟩
  simp [cubeCoord_apply]

theorem cubeCoord_injective (h : CubeBasis a b c) :
    Function.Injective (cubeCoord a b c) := by
  intro v w hvw
  let vi : Fin 5 × Fin 5 × Fin 5 :=
    (⟨(v 0).val, ZMod.val_lt _⟩, ⟨(v 1).val, ZMod.val_lt _⟩, ⟨(v 2).val, ZMod.val_lt _⟩)
  let wi : Fin 5 × Fin 5 × Fin 5 :=
    (⟨(w 0).val, ZMod.val_lt _⟩, ⟨(w 1).val, ZMod.val_lt _⟩, ⟨(w 2).val, ZMod.val_lt _⟩)
  have hvw' : a ^ (vi.1 : ℕ) * b ^ (vi.2.1 : ℕ) * c ^ (vi.2.2 : ℕ) =
      a ^ (wi.1 : ℕ) * b ^ (wi.2.1 : ℕ) * c ^ (wi.2.2 : ℕ) := by
    simpa [vi, wi, cubeCoord_apply] using hvw
  have htriple : vi = wi := h.inj hvw'
  have h0 : (vi.1 : ℕ) = (wi.1 : ℕ) := congrArg (fun p : Fin 5 × Fin 5 × Fin 5 => (p.1 : ℕ)) htriple
  have h1 : (vi.2.1 : ℕ) = (wi.2.1 : ℕ) :=
    congrArg (fun p : Fin 5 × Fin 5 × Fin 5 => (p.2.1 : ℕ)) htriple
  have h2 : (vi.2.2 : ℕ) = (wi.2.2 : ℕ) :=
    congrArg (fun p : Fin 5 × Fin 5 × Fin 5 => (p.2.2 : ℕ)) htriple
  have h0' : (v 0).val = (w 0).val := by simpa [vi, wi] using h0
  have h1' : (v 1).val = (w 1).val := by simpa [vi, wi] using h1
  have h2' : (v 2).val = (w 2).val := by simpa [vi, wi] using h2
  funext i
  fin_cases i
  · exact ZMod.val_injective 5 h0'
  · exact ZMod.val_injective 5 h1'
  · exact ZMod.val_injective 5 h2'

theorem cubeCoord_surjective (h : CubeBasis a b c) :
    Function.Surjective fun v : Fin 3 → ZMod 5 =>
      (⟨cubeCoord a b c v, cubeCoord_mem h v⟩ : Subgroup.closure ({a, b, c} : Set G)) := by
  rintro ⟨g, hg⟩
  obtain ⟨⟨i, j, k⟩, hijk⟩ :=
    (mem_closure_triple_iff h.comm_ab h.comm_ac h.comm_bc h.pow_a h.pow_b h.pow_c g).1 hg
  let v : Fin 3 → ZMod 5 := ![(i : ZMod 5), (j : ZMod 5), (k : ZMod 5)]
  refine ⟨v, Subtype.ext ?_⟩
  change a ^ (v 0).val * b ^ (v 1).val * c ^ (v 2).val = g
  have hi : (v 0).val = (i : ℕ) := by
    dsimp [v]
    rfl
  have hj : (v 1).val = (j : ℕ) := by
    dsimp [v]
    rfl
  have hk : (v 2).val = (k : ℕ) := by
    dsimp [v]
    rfl
  rw [hi, hj, hk]
  exact hijk

def cubeCoordHom (h : CubeBasis a b c) :
    Multiplicative (Fin 3 → ZMod 5) →* Subgroup.closure ({a, b, c} : Set G) where
  toFun v := ⟨cubeCoord a b c v.toAdd, cubeCoord_mem h v.toAdd⟩
  map_one' := by
    apply Subtype.ext
    simp [cubeCoord]
  map_mul' v w := by
    apply Subtype.ext
    exact cubeCoord_add h v.toAdd w.toAdd

def cubeCoordEquiv (h : CubeBasis a b c) :
    Multiplicative (Fin 3 → ZMod 5) ≃* Subgroup.closure ({a, b, c} : Set G) :=
  MulEquiv.ofBijective (cubeCoordHom h)
    ⟨fun v w hvw => cubeCoord_injective h (congrArg Subtype.val hvw),
      cubeCoord_surjective h⟩

@[simp]
theorem cubeCoordEquiv_apply (h : CubeBasis a b c) (v : Fin 3 → ZMod 5) :
    ((cubeCoordEquiv h (Multiplicative.ofAdd v) :
      Subgroup.closure ({a, b, c} : Set G)) : G) =
      a ^ (v 0).val * b ^ (v 1).val * c ^ (v 2).val := by
  change cubeCoord a b c v = _
  exact cubeCoord_apply v

theorem cubeCoordEquiv_single (h : CubeBasis a b c) (i : Fin 3) :
    ((cubeCoordEquiv h (Multiplicative.ofAdd (Pi.single i (1 : ZMod 5))) :
      Subgroup.closure ({a, b, c} : Set G)) : G) = cubeVec a b c i := by
  have h1 : (1 : ZMod 5).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
  rw [cubeCoordEquiv_apply]
  fin_cases i <;> simp [cubeVec, h1]

@[simp]
theorem cubeCoordEquiv_single_zero (h : CubeBasis a b c) :
    ((cubeCoordEquiv h (Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 5))) :
      Subgroup.closure ({a, b, c} : Set G)) : G) = a := by
  simpa [cubeVec] using cubeCoordEquiv_single h 0

@[simp]
theorem cubeCoordEquiv_single_one (h : CubeBasis a b c) :
    ((cubeCoordEquiv h (Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 5))) :
      Subgroup.closure ({a, b, c} : Set G)) : G) = b := by
  simpa [cubeVec] using cubeCoordEquiv_single h 1

@[simp]
theorem cubeCoordEquiv_single_two (h : CubeBasis a b c) :
    ((cubeCoordEquiv h (Multiplicative.ofAdd (Pi.single 2 (1 : ZMod 5))) :
      Subgroup.closure ({a, b, c} : Set G)) : G) = c := by
  simpa [cubeVec] using cubeCoordEquiv_single h 2

section MappedCube

variable {G H : Type*} [Group G] [Group H]
variable (E : Subgroup G) (f : G →* H) (hf : Function.Injective f)
  {a b c : H} (h : CubeBasis a b c)
  (hcl : Subgroup.closure ({a, b, c} : Set H) = E.map f)

@[expose] def cubeCoordEquivOfMap : E ≃* Multiplicative (Fin 3 → ZMod 5) :=
  (E.equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr hcl.symm).trans (cubeCoordEquiv h).symm)

theorem cubeCoordEquivOfMap_symm_apply (v : Fin 3 → ZMod 5) :
    f ((cubeCoordEquivOfMap E f hf h hcl).symm (Multiplicative.ofAdd v) : E) =
      a ^ (v 0).val * b ^ (v 1).val * c ^ (v 2).val := by
  let x := (cubeCoordEquivOfMap E f hf h hcl).symm (Multiplicative.ofAdd v)
  have hx : (cubeCoordEquivOfMap E f hf h hcl) x = Multiplicative.ofAdd v :=
    (cubeCoordEquivOfMap E f hf h hcl).apply_symm_apply _
  have hx' : (E.equivMapOfInjective f hf) x =
      (MulEquiv.subgroupCongr hcl.symm).symm
        (cubeCoordEquiv h (Multiplicative.ofAdd v)) := by
    apply (MulEquiv.subgroupCongr hcl.symm).injective
    apply (cubeCoordEquiv h).symm.injective
    simpa only [cubeCoordEquivOfMap, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] using hx
  have hm := congrArg (fun y : E.map f => (y : H)) hx'
  simpa only [Subgroup.coe_equivMapOfInjective_apply,
    MulEquiv.subgroupCongr_symm_apply, cubeCoordEquiv_apply] using hm

end MappedCube

end CubeCoordinates

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
