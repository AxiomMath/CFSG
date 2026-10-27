module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph
public import CFSG.ClassicalInvolution.SmallCases.NDBC3

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace Cover

section Big

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem inv_exists (C : Asc77.XCtx p f Ω z) {j : Fin C.D.card}
    (hsingle : FundamentalSingleClass (C.D.tag j) (compModel C.D j).D)
    {U : Subgroup (compModel C.D j).K}
    (hU : U ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) :
    ∃ x ∈ U.map (C.psi j), x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨N, hN, hNU⟩ := C.exists_member_of_fund j hsingle hU
  obtain ⟨n, hn⟩ := C.hΩ.classical N hN.1
  have hUq := C.isUniqueInvolution_modOdd hN hn
  rw [hNU] at hUq
  exact ⟨_, hUq.mem, hUq.sq, hUq.ne_one⟩

theorem inv_unique (C : Asc77.XCtx p f Ω z) {j : Fin C.D.card}
    (hsingle : FundamentalSingleClass (C.D.tag j) (compModel C.D j).D)
    {U : Subgroup (compModel C.D j).K}
    (hU : U ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) {x y : OddQuot z}
    (hx : x ∈ U.map (C.psi j)) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hy : y ∈ U.map (C.psi j))
    (hy2 : y * y = 1) (hy1 : y ≠ 1) : y = x := by
  obtain ⟨N, hN, hNU⟩ := C.exists_member_of_fund j hsingle hU
  obtain ⟨n, hn⟩ := C.hΩ.classical N hN.1
  have hUq := C.isUniqueInvolution_modOdd hN hn
  rw [hNU] at hUq
  exact ((hUq.unique y hy hy2).resolve_left hy1).trans
    ((hUq.unique x hx hx2).resolve_left hx1).symm

theorem inv_step (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4) {U V : Subgroup (compModel C.D j).K}
    (hU : U ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hV : V ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) (hc : Commutes U V)
    {x y : OddQuot z} (hx : x ∈ U.map (C.psi j)) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hy : y ∈ V.map (C.psi j)) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    y = x ∨ y = x * oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by
  have hsingle := C.single j hG2 hD4
  obtain ⟨N₁, h₁, hN₁⟩ := C.exists_member_of_fund j hsingle hU
  obtain ⟨N₂, h₂, hN₂⟩ := C.exists_member_of_fund j hsingle hV
  obtain ⟨n₁, hn₁⟩ := C.hΩ.classical N₁ h₁.1
  obtain ⟨n₂, hn₂⟩ := C.hΩ.classical N₂ h₂.1
  have hU₁ := C.isUniqueInvolution_modOdd h₁ hn₁
  have hU₂ := C.isUniqueInvolution_modOdd h₂ hn₂
  rw [hN₁] at hU₁
  rw [hN₂] at hU₂
  have ex : x = oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ :=
    (hU₁.unique x hx hx2).resolve_left hx1
  have ey : y = oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ :=
    (hU₂.unique y hy hy2).resolve_left hy1
  obtain ⟨w₁, -, hw₁⟩ := exists_not_commute C hj hU hx hx1
  obtain ⟨w₂, -, hw₂⟩ := exists_not_commute C hj hV hy hy1
  have hcomm : ∀ a ∈ modOdd z (exactCore z N₁), ∀ b ∈ modOdd z (exactCore z N₂),
      a * b = b * a := by
    rw [hN₁, hN₂]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  rcases eq_or_mul_eq C hnoF h₁ h₂ hn₁ hn₂ hcomm
    (fun h => hw₁ (by rw [ex, h]; exact zbar_comm w₁))
    (fun h => hw₂ (by rw [ey, h]; exact zbar_comm w₂)) with h | h
  · exact Or.inl (by rw [ex, ey, h])
  · right
    rw [← ex, ← ey] at h
    calc y = (x * x) * y := by rw [hx2, one_mul]
      _ = x * oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by rw [mul_assoc, h]

theorem false_of_connected (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4)
    (hconn : RouteD.CommFamilyConnected (fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)) :
    False := by
  have hsingle := C.single j hG2 hD4
  set zb := oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ with hzb
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← map_mul]
    have e : (⟨z, Asc77.XCtx.hzC z⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
        ⟨z, Asc77.XCtx.hzC z⟩ = 1 := Subtype.ext C.hKz.sq
    rw [e, map_one]
  obtain ⟨R₀, hR₀, -⟩ := exists_member_of_meets C j
  obtain ⟨x₀, hx₀, hx₀2, hx₀1⟩ := inv_exists C hsingle hR₀
  have hP : ∀ V ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D,
      ∀ y ∈ V.map (C.psi j), y * y = 1 → y ≠ 1 → y = x₀ ∨ y = x₀ * zb := by
    intro V hV
    have hpath := hconn R₀ hR₀ V hV
    clear hV
    induction hpath with
    | refl => exact fun y hy hy2 hy1 => Or.inl (inv_unique C hsingle hR₀ hx₀ hx₀2 hx₀1 hy hy2 hy1)
    | @tail U W _ hUW ih =>
      obtain ⟨hU, hW, hc⟩ := hUW
      intro y hy hy2 hy1
      obtain ⟨x, hx, hx2, hx1⟩ := inv_exists C hsingle hU
      rcases ih x hx hx2 hx1 with rfl | rfl <;>
        rcases inv_step C hnoF hj hG2 hD4 hU hW hc hx hx2 hx1 hy hy2 hy1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (by rw [mul_assoc, hzb2, mul_one])
  obtain ⟨r₀, hr₀, hr₀x⟩ := hx₀
  have hK := (ModelFacts.modelClauseZero (C.D.tag j) (C.D.rank j) p (C.D.exp j) Fact.out
    (C.D.isFundTag j) (C.D.admissible j)).1
  have hcent : ∀ y : (compModel C.D j).K,
      r₀ * y * r₀⁻¹ * y⁻¹ ∈ Subgroup.center (compModel C.D j).K := by
    intro y
    set ψ := C.psi j with hψ
    have hmem : ψ y * x₀ * (ψ y)⁻¹ ∈ (conjSub y R₀).map ψ :=
      ⟨y * r₀ * y⁻¹, conj_mem_conjSub hr₀, by rw [map_mul, map_mul, map_inv, hr₀x]⟩
    have hsq : (ψ y * x₀ * (ψ y)⁻¹) * (ψ y * x₀ * (ψ y)⁻¹) = 1 := by
      calc (ψ y * x₀ * (ψ y)⁻¹) * (ψ y * x₀ * (ψ y)⁻¹) = ψ y * (x₀ * x₀) * (ψ y)⁻¹ := by group
        _ = 1 := by rw [hx₀2]; group
    have hne1 : ψ y * x₀ * (ψ y)⁻¹ ≠ 1 := fun h => hx₀1 (by
      have e : x₀ = (ψ y)⁻¹ * (ψ y * x₀ * (ψ y)⁻¹) * ψ y := by group
      rw [e, h]
      group)
    have hc : ∀ w : OddQuot z, ψ (r₀ * y * r₀⁻¹ * y⁻¹) * w = w * ψ (r₀ * y * r₀⁻¹ * y⁻¹) := by
      have e : ψ (r₀ * y * r₀⁻¹ * y⁻¹) = x₀ * (ψ y * x₀ * (ψ y)⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hr₀x]
        group
      rcases hP _ (RouteD.conjSub_mem_fundamentalSubgroups hR₀ y) _ hmem hsq hne1 with h | h
      · intro w
        rw [e, h, mul_inv_cancel, one_mul, mul_one]
      · intro w
        have e2 : x₀ * (x₀ * zb)⁻¹ = zb⁻¹ := by
          calc x₀ * (x₀ * zb)⁻¹ = x₀ * zb⁻¹ * x₀⁻¹ := by group
            _ = zb⁻¹ * x₀ * x₀⁻¹ := by
              rw [inv_eq_of_mul_eq_one_left hzb2]
              have := zbar_comm x₀
              rw [← hzb] at this
              rw [this]
            _ = zb⁻¹ := by group
        have hzw : zb * w = w * zb := by
          have := zbar_comm (z := z) w
          rwa [← hzb] at this
        rw [e, h, e2, inv_eq_of_mul_eq_one_left hzb2, hzw]
    refine ModelFacts.mem_center_of_commutators_mem_center hK fun k => C.psi_ker j ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hψ,
      hc (ψ k)]
    group
  have h1 : r₀ = 1 := RouteD.Gaps.fundNoncentral p (C.D.tag j) (C.D.rank j) (C.D.exp j)
    (C.D.isFundTag j) (C.D.admissible j) hj R₀ hR₀ r₀ hr₀ hcent
  exact hx₀1 (by rw [← hr₀x, h1, map_one])

theorem small_of_noFrame (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4) : Asc77.SmallModel (C.D.tag j) (C.D.rank j) := by
  have hq : 5 ≤ p ^ C.D.exp j := by rw [C.exp_eq j hD4]; exact C.hq
  rcases Asc77.ih8_tag_cases C.hp hq (C.D.isFundTag j) (C.D.admissible j) hG2 hD4 with h | h
  · exact (false_of_connected C hnoF hj hG2 hD4 h).elim
  · exact h

end Big

end Cover

end CFSG.ClassicalInvolution.NDB
