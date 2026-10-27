module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Ja
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Red
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Local
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Main
public import CFSG.CGT.PushingUpLit.CGT6.EmbK

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem i253_isQuasisimple_of_open {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem i253_cube_eq_one {G : Type*} [Group G] {O : Subgroup G} (hcop : Nat.Coprime 3 (Nat.card O))
    {o : G} (ho : o ∈ O) (h : o ^ 3 = 1) : o = 1 := by
  have h1 : orderOf (⟨o, ho⟩ : O) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h))
  have h2 : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

section Map

variable {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q]
variable (π : G →* Q) (hker : π.ker ≤ Subgroup.center G) (α : MulAut G) (β : MulAut Q)
  (hαβ : ∀ k, π (α k) = β (π k)) (hπ : Function.Surjective π)
include hker hαβ hπ

theorem i253_conjFix {k : G} (hk : π k ∈ fixSubgroup β) : ∃ e : ↥(fixSubgroup α) ≃* ↥(fixSubgroup α),
    ∀ f, ((e f : ↥(fixSubgroup α)) : G) = k * f * k⁻¹ := by
  have hk' : π k⁻¹ ∈ fixSubgroup β := by
    rw [map_inv]; exact (fixSubgroup β).inv_mem hk
  refine ⟨{ toFun := fun f => ⟨k * f * k⁻¹, conj_mem_fixSubgroup π hker α β hαβ hk f.2⟩
            invFun := fun f => ⟨k⁻¹ * f * k, by
              have := conj_mem_fixSubgroup π hker α β hαβ hk' f.2
              simpa using this⟩
            left_inv := fun f => Subtype.ext (by simp [mul_assoc])
            right_inv := fun f => Subtype.ext (by simp [mul_assoc])
            map_mul' := fun f g => Subtype.ext (by simp [mul_assoc]) }, fun f => rfl⟩

theorem i253_map_primeCoreOf {y : G} (hy : y ∈ GLAPPrimeCoreOf 3 (fixSubgroup α)) :
    π y ∈ GLAPPrimeCoreOf 3 (fixSubgroup β) := by
  obtain ⟨y0, hy0, rfl⟩ := hy
  let ψ : ↥(fixSubgroup α) →* ↥(fixSubgroup β) :=
    (π.comp (fixSubgroup α).subtype).codRestrict (fixSubgroup β) (fun k =>
      map_fixSubgroup_le π hker α β hαβ ⟨k, k.2, rfl⟩)
  set S : Subgroup ↥(fixSubgroup β) := (GLAPPrimeCore 3 ↥(fixSubgroup α)).map ψ with hS
  have hSn : S.Normal := by
    refine ⟨fun s hs g => ?_⟩
    obtain ⟨s0, hs0, rfl⟩ := hs
    obtain ⟨k, hk⟩ := hπ (g : Q)
    have hkF : π k ∈ fixSubgroup β := by rw [hk]; exact g.2
    obtain ⟨e, he⟩ := i253_conjFix π hker α β hαβ hπ hkF
    have hmap := CFSG.pPrimeCore_map_iso 3 e
    have hes : e s0 ∈ GLAPPrimeCore 3 ↥(fixSubgroup α) := by
      change e s0 ∈ CFSG.pPrimeCore 3 ↥(fixSubgroup α)
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hs0
    refine ⟨e s0, hes, Subtype.ext ?_⟩
    show π ((e s0 : ↥(fixSubgroup α)) : G) = (g : Q) * π (s0 : G) * (g : Q)⁻¹
    rw [he, map_mul, map_mul, map_inv, hk]
  have hcop : Nat.Coprime 3 (Nat.card S) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ ψ) CFSG.pPrimeCore_coprime_card
  have hle : S ≤ GLAPPrimeCore 3 ↥(fixSubgroup β) := le_sSup ⟨hSn, hcop⟩
  exact ⟨ψ y0, hle (Subgroup.mem_map_of_mem _ hy0), rfl⟩

end Map

theorem i253_b3_step (hB : B3Quasi) {G : Type} [Group G] [Finite G]
    (hq : CFSG.Open.IsQuasisimple G) (hK : CFSG.Open.IsKGroup G) (h3 : 3 ∣ Nat.card G)
    (α : MulAut G) (hα : α ^ 3 = 1) {x y : G} (hx : x ∈ GLAPLayer 3 (fixSubgroup α))
    (hy : y ∈ GLAPPrimeCoreOf 3 (fixSubgroup α)) (hx3 : x ^ 3 = 1) : x * y = y * x := by
  set O : Subgroup G := GLAPPrimeCore 3 G with hO
  have hOc : O ≤ Subgroup.center G := i253_primeCore_le_center hq h3
  let π : G →* G ⧸ O := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : π.ker ≤ Subgroup.center G := by
    rw [QuotientGroup.ker_mk']; exact hOc
  have hOα : O.map α.toMonoidHom = O := CFSG.pPrimeCore_map_iso 3 α
  let β : MulAut (G ⧸ O) := QuotientGroup.congr O O α hOα
  have hαβ : ∀ k, π (α k) = β (π k) := fun k => rfl
  have hQb : CFSG.Open.IsQuasisimple (G ⧸ O) := i253_isQuasisimple_of_surj hq π hπ hker
  have hOb : GLAPPrimeCore 3 (G ⧸ O) = ⊥ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    show CFSG.pPrimeCore 3 (G ⧸ O) = ⊥
    rw [pPrimeCore_eq_map_of_central 3 π hπ hker]
    exact QuotientGroup.map_mk'_self O
  have hKb : CFSG.IsKGroup (G ⧸ O) :=
    CFSG.CGT.PushingUpLit.CGT6.isKGroup_of_surjective (isKGroup_of_openIsKGroup hK) π hπ
  have hopen : CFSG.Open.IsKGroup (G ⧸ O) := fun K L _ _ hs _ => hKb K (L.subgroupOf K) hs
  have hcat := (I1420.catalog_of_quasisimple hQb hopen).2
  have hβ3 : β ^ 3 = 1 := by
    ext z
    obtain ⟨k, rfl⟩ := hπ z
    have h1 : α (α (α k)) = k := by
      have := congrArg (fun f : MulAut G => f k) hα
      simpa [pow_succ, MulAut.mul_apply] using this
    have h2 : β (β (β (π k))) = π (α (α (α k))) := by rw [← hαβ, ← hαβ, ← hαβ]
    show β (β (β (π k))) = π k
    rw [h2, h1]
  have hB3 : ⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆ = ⊥ :=
    hB (G ⧸ O) (i253_isQuasisimple_of_open hQb) hOb hcat β hβ3
  have hxπ : π x ∈ GLAPLayer 3 (fixSubgroup β) := by
    rw [← map_glaPLayer_fixSubgroup_eq π hker α β hαβ hπ Nat.prime_three]
    exact Subgroup.mem_map_of_mem _ hx
  have hyπ : π y ∈ GLAPPrimeCoreOf 3 (fixSubgroup β) :=
    i253_map_primeCoreOf π hker α β hαβ hπ hy
  have hcomm : ⁅π x, π y⁆ = 1 :=
    Subgroup.mem_bot.1 (hB3 ▸ Subgroup.commutator_mem_commutator hxπ hyπ)
  have hoO : x * y * x⁻¹ * y⁻¹ ∈ O := by
    have : π (x * y * x⁻¹ * y⁻¹) = 1 := by
      have h := hcomm
      rw [commutatorElement_def] at h
      simpa using h
    rwa [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
  set o := x * y * x⁻¹ * y⁻¹ with ho
  have hoc : ∀ g : G, g * o = o * g := fun g => (Subgroup.mem_center_iff.1 (hOc hoO) g)
  have e1 : x * y * x⁻¹ = o * y := by rw [ho]; group
  have e2 : x * (o * y) * x⁻¹ = o * (x * y * x⁻¹) := by
    calc x * (o * y) * x⁻¹ = (x * o) * y * x⁻¹ := by group
      _ = (o * x) * y * x⁻¹ := by rw [hoc x]
      _ = o * (x * y * x⁻¹) := by group
  have hx3' : x * x * x = 1 := by simpa [pow_succ] using hx3
  have e3 : y = o * o * o * y := by
    calc y = (x * x * x) * y * (x * x * x)⁻¹ := by rw [hx3']; group
      _ = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = x * (x * (o * y) * x⁻¹) * x⁻¹ := by rw [e1]
      _ = x * (o * (x * y * x⁻¹)) * x⁻¹ := by rw [e2]
      _ = x * (o * (o * y)) * x⁻¹ := by rw [e1]
      _ = o * (x * (o * y) * x⁻¹) := by
        calc x * (o * (o * y)) * x⁻¹ = (x * o) * (o * y) * x⁻¹ := by group
          _ = (o * x) * (o * y) * x⁻¹ := by rw [hoc x]
          _ = o * (x * (o * y) * x⁻¹) := by group
      _ = o * (o * (x * y * x⁻¹)) := by rw [e2]
      _ = o * (o * (o * y)) := by rw [e1]
      _ = o * o * o * y := by group
  have hcube : o ^ 3 = 1 := by
    have : o * o * o = 1 := by
      have h := e3
      have h' : o * o * o * y = 1 * y := by rw [one_mul]; exact h.symm
      exact mul_right_cancel h'
    simpa [pow_succ] using this
  have hcop : Nat.Coprime 3 (Nat.card O) := CFSG.pPrimeCore_coprime_card
  have ho1 : o = 1 := i253_cube_eq_one hcop hoO hcube
  have : x * y * x⁻¹ * y⁻¹ = 1 := ho1
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 this)

end CFSG.HardMathSupport.Solomon.Coordinator
