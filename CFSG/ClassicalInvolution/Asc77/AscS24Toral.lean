module

public import CFSG.ClassicalInvolution.Asc77.AscS24Hyp51
public import CFSG.ClassicalInvolution.Asc77.AscS24Lie
public import CFSG.ClassicalInvolution.AschTight.S19MCenter

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


namespace Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem J_mem_tq_e0 (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    conjSub g⁻¹ K ∈ tqMembers Ω C.e0 := by
  have h := C.D.J_mem_tq C.hc hZ
  rwa [C.hJ] at h

theorem K_classical : IsClassicalMember p f K z :=
  isClassicalMember_of_twin C.hs.stand.hyp C.hs.stand.mem C.hs.hz

theorem J_classical : IsClassicalMember p f (conjSub g⁻¹ K) u := by
  have h := C.K_classical.conj g⁻¹
  rwa [inv_inv, C.hg] at h

theorem e0_isPGroup (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    IsPGroup 2 (Subgroup.zpowers C.e0) :=
  isPGroup_zpowers_of_sq_eq_one (C.e0_sq hZ)

theorem B_le_centralizer_e0 (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    C.B ≤ Subgroup.centralizer ({C.e0} : Set G) := fun _ hb =>
  Lemma52Proof.le_centralizer_of_mem (C.B_isElemAbelian hZ) C.e0_mem_B hb

theorem toral (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (D : LocalLieSystemAt p f (exactFamily Ω C.e0) C.e0) (hD1 : D.card = 1) (j : Fin D.card)
    (htag : D.tag j = .PSL ∨ D.tag j = .PSU) (hrank : D.rank j = 3) :
    FrameVertex.ToralOnComponent C.e0 C.B
      (secComponentHom (normalizesLayer_exactFamily C.hs.stand.hyp.conjInvariant) D j) := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψ
  have hc2 := C.e0_isPGroup hZ
  have hKt := C.K_mem_tq_e0 hZ
  have hJt := C.J_mem_tq_e0 hZ
  have hne : (tqMembers Ω C.e0).Nonempty := ⟨K, hKt⟩
  have hexp : D.exp j = f := by
    rcases D.exp_eq j with h | ⟨h, -⟩
    · exact h
    · rcases htag with h' | h' <;> rw [h'] at h <;> cases h
  have h5 : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
  have h4 : 4 ≤ p ^ D.exp j := by omega
  have hG2 : D.tag j ≠ .G2 := by rcases htag with h | h <;> rw [h] <;> decide
  have hD4 : D.tag j ≠ .trialityD4 := by rcases htag with h | h <;> rw [h] <;> decide
  obtain ⟨R₁, hR₁, hmod₁⟩ := exists_fund_of_mem' hΩ hc2 hne D hD1 hKt j
  obtain ⟨R₂, hR₂, hmod₂⟩ := exists_fund_of_mem' hΩ hc2 hne D hD1 hJt j
  obtain ⟨τ₁, -, hτ₁2, -, hτ₁c⟩ := exists_tau hp D j h5 hG2 hD4 hR₁
  obtain ⟨τ₂, -, hτ₂2, -, hτ₂c⟩ := exists_tau hp D j h5 hG2 hD4 hR₂
  have hz₁ := oddQuotMk_involution' hp hΩ hc2 D j h4 hKt C.K_classical hR₁ hτ₁c hmod₁.symm
  have hu₂ := oddQuotMk_involution' hp hΩ hc2 D j h4 hJt C.J_classical hR₂ hτ₂c hmod₂.symm
  set hzC := exactCore_le_centralizer C.e0 K (mem_exactCore C.K_classical hc2 hKt.2)
  set huC := exactCore_le_centralizer C.e0 (conjSub g⁻¹ K)
    (mem_exactCore C.J_classical hc2 hJt.2)
  have hodd : Odd (Nat.card (Subgroup.center (compModel D j).K)) := by
    have hT6 : AschTight.S1911.IsT6Tag (D.tag j) (D.rank j) := by
      rcases htag with h | h
      · exact Or.inl ⟨h, hrank⟩
      · exact Or.inr (Or.inl ⟨h, hrank⟩)
    exact AschTight.S19M.factM3 p (D.exp j) Fact.out hp (D.tag j) (D.rank j) hT6 (D.admissible j)
  have hfin : Finite (compModel D j).K :=
    ModelFacts.finite_modelUniv hp Fact.out (ih8_isFundTag_mf (D.isFundTag j)) (D.admissible j)
  have hzu : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({C.e0} : Set G))) * ⟨u, huC⟩ =
      ⟨u, huC⟩ * ⟨z, hzC⟩ := Subtype.ext C.comm_uz.symm
  have hτcomm : τ₁ * τ₂ = τ₂ * τ₁ := by
    refine commute_of_map_commute ψ
      (secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j) hodd
      hτ₁2 hτ₂2 ?_
    rw [← hz₁, ← hu₂, ← map_mul, ← map_mul, hzu]
  have hpair : ∀ a ∈ ({τ₁, τ₂} : Set (compModel D j).K),
      ∀ b ∈ ({τ₁, τ₂} : Set (compModel D j).K), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl)
    · rfl
    · exact hτcomm
    · exact hτcomm.symm
    · rfl
  have hcm := ChainFrame.commutes_closure hpair
  have hBC := C.B_le_centralizer_e0 hZ
  have he0C : C.e0 ∈ Subgroup.centralizer ({C.e0} : Set G) := hBC C.e0_mem_B
  refine ⟨Subgroup.closure ({τ₁, τ₂} : Set (compModel D j).K), hcm, ?_⟩
  intro b hb hbC
  have hgen : ∀ x ∈ ({u * C.e0, u, z} : Set G), ∃ hx : x ∈ Subgroup.centralizer ({C.e0} : Set G),
      ∃ y ∈ Subgroup.closure ({τ₁, τ₂} : Set (compModel D j).K), y * y = 1 ∧
        ∀ w ∈ ψ.range, oddQuotMk C.e0 ⟨x, hx⟩ * w * (oddQuotMk C.e0 ⟨x, hx⟩)⁻¹ =
          ψ y * w * (ψ y)⁻¹ := by
    rintro x (rfl | rfl | rfl)
    · refine ⟨hBC (C.B.mul_mem C.u_mem_B C.e0_mem_B), τ₂, Subgroup.subset_closure (by simp),
        hτ₂2, fun w _ => ?_⟩
      have hmul : (⟨u * C.e0, hBC (C.B.mul_mem C.u_mem_B C.e0_mem_B)⟩ :
          ↥(Subgroup.centralizer ({C.e0} : Set G))) = ⟨u, huC⟩ * ⟨C.e0, he0C⟩ := rfl
      rw [hmul, map_mul, ← hu₂]
      have hcen := oddQuotMk_central he0C w
      calc oddQuotMk C.e0 ⟨u, huC⟩ * oddQuotMk C.e0 ⟨C.e0, he0C⟩ * w *
            (oddQuotMk C.e0 ⟨u, huC⟩ * oddQuotMk C.e0 ⟨C.e0, he0C⟩)⁻¹
          = oddQuotMk C.e0 ⟨u, huC⟩ * (oddQuotMk C.e0 ⟨C.e0, he0C⟩ * w) *
              (oddQuotMk C.e0 ⟨C.e0, he0C⟩)⁻¹ * (oddQuotMk C.e0 ⟨u, huC⟩)⁻¹ := by group
        _ = oddQuotMk C.e0 ⟨u, huC⟩ * w * (oddQuotMk C.e0 ⟨u, huC⟩)⁻¹ := by
            rw [hcen]; group
    · exact ⟨huC, τ₂, Subgroup.subset_closure (by simp), hτ₂2, fun w _ => by rw [hu₂]⟩
    · exact ⟨hzC, τ₁, Subgroup.subset_closure (by simp), hτ₁2, fun w _ => by rw [hz₁]⟩
  have key : ∀ (b : G) (hb : b ∈ C.B),
      ∃ y ∈ Subgroup.closure ({τ₁, τ₂} : Set (compModel D j).K), y * y = 1 ∧
        ∀ w ∈ ψ.range, oddQuotMk C.e0 ⟨b, hBC hb⟩ * w * (oddQuotMk C.e0 ⟨b, hBC hb⟩)⁻¹ =
          ψ y * w * (ψ y)⁻¹ := by
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hx', y, hy, hy2, hact⟩ := hgen x hx
      exact ⟨y, hy, hy2, hact⟩
    | one =>
      refine ⟨1, Subgroup.one_mem _, by simp, fun w _ => ?_⟩
      have : (⟨1, hBC (Subgroup.one_mem _)⟩ : ↥(Subgroup.centralizer ({C.e0} : Set G))) = 1 :=
        rfl
      rw [this]
      simp
    | mul x y hx hy ihx ihy =>
      obtain ⟨xa, hxa, hxa2, hact⟩ := ihx
      obtain ⟨xb, hxb, hxb2, hbct⟩ := ihy
      have hxC := hBC hx
      have hyC := hBC hy
      refine ⟨xa * xb, Subgroup.mul_mem _ hxa hxb, ?_, fun w hw => ?_⟩
      · calc xa * xb * (xa * xb) = xa * (xb * xa) * xb := by group
          _ = xa * (xa * xb) * xb := by rw [hcm xb hxb xa hxa]
          _ = (xa * xa) * (xb * xb) := by group
          _ = 1 := by rw [hxa2, hxb2]; simp
      · have hmul : (⟨x * y, hBC (Subgroup.mul_mem _ hx hy)⟩ :
            ↥(Subgroup.centralizer ({C.e0} : Set G))) = ⟨x, hxC⟩ * ⟨y, hyC⟩ := rfl
        rw [hmul, map_mul]
        obtain ⟨k, rfl⟩ := hw
        have hw' : ψ xb * ψ k * (ψ xb)⁻¹ ∈ ψ.range := ⟨xb * k * xb⁻¹, by simp⟩
        have h1 := hbct (ψ k) ⟨k, rfl⟩
        have h2 := hact _ hw'
        calc oddQuotMk C.e0 ⟨x, hxC⟩ * oddQuotMk C.e0 ⟨y, hyC⟩ * ψ k *
              (oddQuotMk C.e0 ⟨x, hxC⟩ * oddQuotMk C.e0 ⟨y, hyC⟩)⁻¹
            = oddQuotMk C.e0 ⟨x, hxC⟩ * (oddQuotMk C.e0 ⟨y, hyC⟩ * ψ k *
                (oddQuotMk C.e0 ⟨y, hyC⟩)⁻¹) * (oddQuotMk C.e0 ⟨x, hxC⟩)⁻¹ := by group
          _ = ψ (xa * xb) * ψ k * (ψ (xa * xb))⁻¹ := by
            rw [h1, h2]
            simp only [map_mul]
            group
    | inv x hx ihx =>
      obtain ⟨xa, hxa, hxa2, hact⟩ := ihx
      refine ⟨xa, hxa, hxa2, fun w hw => ?_⟩
      have hxC := hBC hx
      have hinv : (⟨x⁻¹, hBC (Subgroup.inv_mem _ hx)⟩ :
          ↥(Subgroup.centralizer ({C.e0} : Set G))) = ⟨x, hxC⟩⁻¹ := rfl
      rw [hinv, map_inv, inv_inv]
      have hψ2 : ψ xa * ψ xa = 1 := by rw [← map_mul, hxa2, map_one]
      have hψinv : (ψ xa)⁻¹ = ψ xa := inv_eq_of_mul_eq_one_right hψ2
      obtain ⟨k, rfl⟩ := hw
      have hw' : ψ xa * ψ k * ψ xa ∈ ψ.range := ⟨xa * k * xa, by simp⟩
      have h2 := hact _ hw'
      rw [hψinv] at h2
      have e1 : oddQuotMk C.e0 ⟨x, hxC⟩ * (ψ xa * ψ k * ψ xa) * (oddQuotMk C.e0 ⟨x, hxC⟩)⁻¹ =
          ψ k := by
        rw [h2]
        calc ψ xa * (ψ xa * ψ k * ψ xa) * ψ xa = (ψ xa * ψ xa) * ψ k * (ψ xa * ψ xa) := by group
          _ = ψ k := by rw [hψ2]; simp
      rw [hψinv]
      calc (oddQuotMk C.e0 ⟨x, hxC⟩)⁻¹ * ψ k * oddQuotMk C.e0 ⟨x, hxC⟩
          = (oddQuotMk C.e0 ⟨x, hxC⟩)⁻¹ * (oddQuotMk C.e0 ⟨x, hxC⟩ * (ψ xa * ψ k * ψ xa) *
              (oddQuotMk C.e0 ⟨x, hxC⟩)⁻¹) * oddQuotMk C.e0 ⟨x, hxC⟩ := by rw [e1]
        _ = ψ xa * ψ k * ψ xa := by group
  exact key b hb

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
