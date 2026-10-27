module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.CharacterTheory.Burnside
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Solomon.LocalBalance

section Constrained

variable {Y : Type} [Group Y] [Finite Y]

theorem pConstrainedShape_of_constraint {p : ℕ} {C : Subgroup Y}
    (h : ∀ x ∈ C, (∀ r ∈ CFSG.Open.pCoreOf p C, x * r = r * x) → x ∈ CFSG.Open.pCoreOf p C) :
    PConstrainedShape p C := by
  refine ⟨CFSG.Open.pCoreOf p C, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨q, hq, rfl⟩
    exact ⟨⟨g, hg⟩ * q * ⟨g, hg⟩⁻¹, (CFSG.pCore_normal (p := p) (G := ↥C)).conj_mem q hq ⟨g, hg⟩, rfl⟩
  · exact (CFSG.pCore_isPGroup (G := ↥C) (p := p)).map C.subtype
  · rintro x ⟨hxC, hxc⟩
    exact h x hxC (fun r hr => (Subgroup.mem_centralizer_iff.1 hxc r hr).symm)

theorem pConstrainedShape_of_solvable {p : ℕ} (hp : p.Prime) {C : Subgroup Y}
    (hsolv : Group.IsSolvable ↥C) (hO : GLAPPrimeCoreOf p C = ⊥) : PConstrainedShape p C := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO' : CFSG.pPrimeCore p ↥C = ⊥ := by
    unfold GLAPPrimeCoreOf at hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hO
  have hF : CFSG.fittingSubgroup ↥C = CFSG.pCore p ↥C := CFSG.Fitting_eq_pcore ↥C p hO'
  have hcent := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  rw [hF] at hcent
  refine pConstrainedShape_of_constraint fun x hx hxr => ?_
  have : (⟨x, hx⟩ : ↥C) ∈ CFSG.pCore p ↥C := by
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subtype.ext ((hxr (r : Y) ⟨r, hr, rfl⟩).symm)
  exact ⟨⟨x, hx⟩, this, rfl⟩

theorem pConstrainedShape_of_centralizer_solvable {p : ℕ} (hp : p.Prime) {C R : Subgroup Y}
    (hRC : R ≤ C) (hRn : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R) (hRp : IsPGroup p R)
    (hRmax : ∀ J : Subgroup Y, J ≤ C → (∀ c ∈ C, ∀ j ∈ J, c * j * c⁻¹ ∈ J) → IsPGroup p J →
      J ≤ R)
    (hO : GLAPPrimeCoreOf p C = ⊥)
    (hN : Group.IsSolvable ↥(C ⊓ Subgroup.centralizer (R : Set Y))) : PConstrainedShape p C := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨R, hRC, hRn, hRp, ?_⟩
  set N := C ⊓ Subgroup.centralizer (R : Set Y) with hNdef
  have hNC : N ≤ C := inf_le_left
  have hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    refine ⟨C.mul_mem (C.mul_mem hc hn.1) (C.inv_mem hc), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro r hr
    have hr' : c⁻¹ * r * c ∈ R := by simpa using hRn c⁻¹ (C.inv_mem hc) r hr
    have h1 := Subgroup.mem_centralizer_iff.1 hn.2 (c⁻¹ * r * c) hr'
    calc r * (c * n * c⁻¹) = c * ((c⁻¹ * r * c) * n) * c⁻¹ := by group
      _ = c * (n * (c⁻¹ * r * c)) * c⁻¹ := by rw [h1]
      _ = (c * n * c⁻¹) * r := by group
  have hnorm : (N.subgroupOf C).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hNn g.1 g.2 x hx⟩
  have hON : GLAPPrimeCoreOf p N = ⊥ := by
    have h1 := glaPPrimeCoreOf_le_of_normal_aux p hNC hnorm
    rw [hO] at h1
    exact le_bot_iff.1 h1
  have hON' : CFSG.pPrimeCore p ↥N = ⊥ := by
    unfold GLAPPrimeCoreOf at hON
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 hON
  have hF : CFSG.fittingSubgroup ↥N = CFSG.pCore p ↥N := CFSG.Fitting_eq_pcore ↥N p hON'
  have hcent := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hN
  rw [hF] at hcent
  set F : Subgroup Y := (CFSG.pCore p ↥N).map N.subtype with hFdef
  have hFC : F ≤ C := (Subgroup.map_subtype_le _).trans hNC
  have hFn : ∀ c ∈ C, ∀ f ∈ F, c * f * c⁻¹ ∈ F := by
    intro c hc f hf
    obtain ⟨f', hf', rfl⟩ := hf
    let φ : ↥N ≃* ↥N :=
      { toFun := fun n => ⟨c * n * c⁻¹, hNn c hc n n.2⟩
        invFun := fun n => ⟨c⁻¹ * n * c, by
          simpa using hNn c⁻¹ (C.inv_mem hc) n n.2⟩
        left_inv := fun n => Subtype.ext (by dsimp only; group)
        right_inv := fun n => Subtype.ext (by dsimp only; group)
        map_mul' := fun a b => Subtype.ext (by
          show c * ((a : Y) * (b : Y)) * c⁻¹ = (c * (a : Y) * c⁻¹) * (c * (b : Y) * c⁻¹)
          group) }
    have hfix := (inferInstance : (CFSG.pCore p ↥N).Characteristic).fixed φ
    have hmem : f' ∈ (CFSG.pCore p ↥N).comap φ.toMonoidHom := by rw [hfix]; exact hf'
    exact ⟨φ f', hmem, rfl⟩
  have hFp : IsPGroup p F := (CFSG.pCore_isPGroup (G := ↥N) (p := p)).map N.subtype
  have hFR : F ≤ R := hRmax F hFC hFn hFp
  rintro x ⟨hxC, hxc⟩
  have hxN : x ∈ N := ⟨hxC, hxc⟩
  have : (⟨x, hxN⟩ : ↥N) ∈ CFSG.pCore p ↥N := by
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrF : (r : Y) ∈ F := ⟨r, hr, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc (r : Y) (hFR hrF))
  exact hFR ⟨⟨x, hxN⟩, this, rfl⟩

end Constrained

section Burnside

theorem isSolvable_of_card_two_pow_mul_three_pow {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  haveI : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem isSolvable_of_card_dvd_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd₁
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd₂
  exact isSolvable_of_card_two_pow_mul_three_pow (a := i) (b := j) (by rw [← hd, hi, hj])

end Burnside

end CFSG.HardMathSupport.Dickson.I271
