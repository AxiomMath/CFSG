module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.GH74.GLS.Stage1.Main.BrRankE16

public section

open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section Abstract

variable {Γ : Type} [Group Γ]

theorem relIndex_le_two_of_involution [Finite Γ] {L : Subgroup Γ} {w : Γ} (hw2 : w * w = 1)
    (hwN : w ∈ normalizer (L : Set Γ)) : L.relIndex (L ⊔ zpowers w) ≤ 2 := by
  classical
  have hzw : zpowers w ≤ normalizer (L : Set Γ) := Subgroup.zpowers_le.2 hwN
  have hBN : L ⊔ zpowers w ≤ normalizer (L : Set Γ) := sup_le Subgroup.le_normalizer hzw
  have hLB : L ≤ L ⊔ zpowers w := le_sup_left
  have hn : (L.subgroupOf (L ⊔ zpowers w)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLB).2 hBN
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left L (zpowers w) hzw
  let f : Bool → ↥(L ⊔ zpowers w) ⧸ L.subgroupOf (L ⊔ zpowers w) := fun b =>
    if b then QuotientGroup.mk ⟨w, Subgroup.mem_sup_right (mem_zpowers w)⟩ else 1
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : (x : Γ) ∈ (L : Set Γ) * (zpowers w : Set Γ) := by
      rw [← hmul]
      exact x.2
    obtain ⟨l, hl, a, ha, hla⟩ := Set.mem_mul.1 hx
    rcases eq_one_or_eq_of_mem_zpowers_sq hw2 ha with h | h
    · refine ⟨false, ?_⟩
      show (1 : ↥(L ⊔ zpowers w) ⧸ _) = QuotientGroup.mk x
      rw [eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rw [← hla, h, mul_one]
      exact hl
    · refine ⟨true, ?_⟩
      show QuotientGroup.mk (⟨w, _⟩ : ↥(L ⊔ zpowers w)) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (w⁻¹ * (x : Γ)) ∈ L
      rw [← hla, h]
      have : w⁻¹ * (l * w) = (w⁻¹ * l * w) := by group
      rw [this]
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (L : Set Γ)).inv_mem hwN) l).1 hl
      simpa using this
  have h1 := Nat.card_le_card_of_surjective f hsurj
  have h2 : Nat.card Bool = 2 := by simp
  have h3 : Nat.card (↥(L ⊔ zpowers w) ⧸ L.subgroupOf (L ⊔ zpowers w)) =
      L.relIndex (L ⊔ zpowers w) := rfl
  omega


open CFSG.GorensteinWalter in
theorem inf_centralizer_le_Z [Finite Γ] {L B Z : Subgroup Γ} (hLB : L ≤ B) (hLperf : Group.IsPerfect ↥L)
    (hidx : L.relIndex B ≤ 2) [hZn : (Z.subgroupOf B).Normal] {Fq : Type} [Field Fq] [Finite Fq]
    (hodd : IsOddPrimePower (Nat.card Fq)) (h3 : 3 < Nat.card Fq)
    (φ : ↥B ⧸ Z.subgroupOf B ≃* PGL2 Fq) : B ⊓ centralizer (L : Set Γ) ≤ Z := by
  classical
  have : Finite (PGL2 Fq) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let ψ : ↥B →* PGL2 Fq := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf B))
  have hψsurj : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk b) = 1 ↔ b ∈ Z.subgroupOf B
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  set L' : Subgroup ↥B := L.subgroupOf B with hL'
  set R : Subgroup (PGL2 Fq) := L'.map ψ with hR
  have hL'perf : ⁅L', L'⁆ = L' := by
    have hperf' : Group.IsPerfect ↥L' :=
      Group.IsPerfect.ofSurjective (G := ↥L) (G' := ↥L')
        (f := (Subgroup.subgroupOfEquivOfLe hLB).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLB).symm.surjective
    exact Subgroup.isPerfect_iff.1 hperf'
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← Subgroup.map_commutator, hL'perf]
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three Fq hodd h3
  have hRle : R ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Fq)).range := by
    rw [← hcomm, ← hRperf, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  set P₀ : Subgroup (PGL2 Fq) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Fq)).range with hP₀
  have hP₀idx : P₀.index = 2 := pgl2_psl2Range_index_eq_two Fq hodd
  have hRidx : R.index ≤ 2 := by
    rw [hR, Subgroup.index_map, MonoidHom.range_eq_top.2 hψsurj, Subgroup.index_top, mul_one]
    have h1 : (L' ⊔ ψ.ker).index ∣ L'.index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : L'.index = L.relIndex B := rfl
    have h3' : L'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h3') h1).trans (h2 ▸ hidx)
  have hRidx2 : R.index = 2 := by
    have h1 : P₀.index ∣ R.index := Subgroup.index_dvd_of_le hRle
    rw [hP₀idx] at h1
    have h2 : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
    omega
  have hReq : R = P₀ := by
    have e1 := Subgroup.index_mul_card R
    have e2 := Subgroup.index_mul_card P₀
    rw [hRidx2] at e1
    rw [hP₀idx] at e2
    exact Subgroup.eq_of_le_of_card_ge hRle (by
      have : 2 * Nat.card P₀ ≤ 2 * Nat.card R := by rw [e2, ← e1]
      omega)
  intro b hb
  have hbB : b ∈ B := hb.1
  have hbC : b ∈ centralizer (L : Set Γ) := hb.2
  have hψb : ψ ⟨b, hbB⟩ ∈ centralizer (P₀ : Set (PGL2 Fq)) := by
    rw [← hReq, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l', hl', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hbC (l' : Γ) (Subgroup.mem_subgroupOf.1 hl'))
  rw [pgl2_psl2Range_centralizer_eq_bot Fq hodd, Subgroup.mem_bot] at hψb
  have : (⟨b, hbB⟩ : ↥B) ∈ ψ.ker := hψb
  rw [hψker, Subgroup.mem_subgroupOf] at this
  exact this

theorem inducedQuot_equiv {L B T Z : Subgroup Γ} (hBN : B ≤ normalizer (L : Set Γ))
    (hTN : T ≤ normalizer (L : Set Γ)) (hBT : B ≤ L ⊔ T)
    (hA : L ⊔ T ≤ B ⊔ centralizer (L : Set Γ)) (hBC : B ⊓ centralizer (L : Set Γ) = Z)
    [hZn : (Z.subgroupOf B).Normal] :
    ∃ _ : ((centralizer (L : Set Γ)).subgroupOf (L ⊔ T)).Normal,
      Nonempty (↥(L ⊔ T) ⧸ (centralizer (L : Set Γ)).subgroupOf (L ⊔ T) ≃*
        ↥B ⧸ Z.subgroupOf B) := by
  classical
  set A : Subgroup Γ := L ⊔ T with hAdef
  set C : Subgroup Γ := centralizer (L : Set Γ) with hCdef
  have hAN : A ≤ normalizer (L : Set Γ) := sup_le Subgroup.le_normalizer hTN
  have hBA : B ≤ A := hBT
  have hCn : (C.subgroupOf A).Normal := by
    refine ⟨fun c hc a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    have hcC : (c : Γ) ∈ C := hc
    have haN : (a : Γ) ∈ normalizer (L : Set Γ) := hAN a.2
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : (a : Γ)⁻¹ * l * (a : Γ) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (L : Set Γ)).inv_mem haN) l).1 hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hcC _ hl'
    show l * ((a : Γ) * (c : Γ) * (a : Γ)⁻¹) = ((a : Γ) * (c : Γ) * (a : Γ)⁻¹) * l
    calc l * ((a : Γ) * (c : Γ) * (a : Γ)⁻¹)
        = (a : Γ) * (((a : Γ)⁻¹ * l * (a : Γ)) * (c : Γ)) * (a : Γ)⁻¹ := by group
      _ = (a : Γ) * ((c : Γ) * ((a : Γ)⁻¹ * l * (a : Γ))) * (a : Γ)⁻¹ := by rw [← h1]
      _ = ((a : Γ) * (c : Γ) * (a : Γ)⁻¹) * l := by group
  refine ⟨hCn, ⟨?_⟩⟩
  let φ : ↥B →* ↥A ⧸ C.subgroupOf A := (QuotientGroup.mk' (C.subgroupOf A)).comp (Subgroup.inclusion hBA)
  have hker : φ.ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hBC]
    show (QuotientGroup.mk (Subgroup.inclusion hBA b) : ↥A ⧸ C.subgroupOf A) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨b.2, h⟩
    · intro h
      exact h.2
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    have hBnC : B ≤ normalizer (C : Set Γ) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro c
      have hbN : b ∈ normalizer (L : Set Γ) := hBN hb
      constructor
      · intro hc
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hl' : b⁻¹ * l * b ∈ L := by
          have := (Subgroup.mem_normalizer_iff.1 ((normalizer (L : Set Γ)).inv_mem hbN) l).1 hl
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.1 hc _ hl'
        calc l * (b * c * b⁻¹) = b * ((b⁻¹ * l * b) * c) * b⁻¹ := by group
          _ = b * (c * (b⁻¹ * l * b)) * b⁻¹ := by rw [← h1]
          _ = (b * c * b⁻¹) * l := by group
      · intro hc
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hl' : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hbN l).1 hl
        have h1 := Subgroup.mem_centralizer_iff.1 hc _ hl'
        calc l * c = b⁻¹ * ((b * l * b⁻¹) * (b * c * b⁻¹)) * b := by group
          _ = b⁻¹ * ((b * c * b⁻¹) * (b * l * b⁻¹)) * b := by rw [← h1]
          _ = c * l := by group
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left C B hBnC
    have ha : (a : Γ) ∈ (C : Set Γ) * (B : Set Γ) := by
      rw [← hmul, sup_comm]
      exact hA a.2
    obtain ⟨c, hc, b, hb, hcb⟩ := Set.mem_mul.1 ha
    have hbA : b ∈ A := hBA hb
    have hcA : c ∈ A := by
      have : c = (a : Γ) * b⁻¹ := by rw [← hcb]; group
      rw [this]
      exact A.mul_mem a.2 (A.inv_mem hbA)
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hBA ⟨b, hb⟩) : ↥A ⧸ C.subgroupOf A) = QuotientGroup.mk a
    rw [QuotientGroup.eq]
    show ((⟨b, hbA⟩ : ↥A)⁻¹ * a) ∈ C.subgroupOf A
    rw [Subgroup.mem_subgroupOf]
    show b⁻¹ * (a : Γ) ∈ C
    have : b⁻¹ * (a : Γ) = b⁻¹ * c * b := by rw [← hcb]; group
    rw [this]
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (C : Set Γ)).inv_mem (hBnC hb)) c).1 hc
    simpa using this
  exact (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)

end Abstract

end CFSG.GH74.GLS.Stage1.Main
