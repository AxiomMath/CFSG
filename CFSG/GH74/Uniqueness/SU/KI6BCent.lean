module

public import CFSG.GH74.Uniqueness.SU.KI6BInner

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open scoped Pointwise commutatorElement
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

theorem exists_conj_subgroup_sylow (S : Sylow 2 H) (A : Subgroup H) (hA : IsPGroup 2 A) :
    ∃ g : H, ∀ a ∈ A, g * a * g⁻¹ ∈ (S : Subgroup H) := by
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q S
  refine ⟨g, fun a ha => ?_⟩
  have hyQ : a ∈ (Q : Subgroup H) := hQ ha
  have hmem : MulAut.conj g • a ∈ MulAut.conj g • ((Q : Subgroup H) : Set H) :=
    Set.smul_mem_smul_set hyQ
  have hcoe : ((g • Q : Sylow 2 H) : Set H) = MulAut.conj g • ((Q : Subgroup H) : Set H) :=
    Sylow.coe_smul
  rw [← hcoe, hg] at hmem
  have h3 : g * a * g⁻¹ ∈ ((S : Subgroup H) : Set H) := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hmem
  exact h3

theorem Cfg.pRank_centralizer_eq_one (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hKH : ¬ K ≤ H₀) :
    Open.pRank 2 (centralizer (K : Set H)) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFH := h.generalizedFitting_sup_eq_top F hr htc ht2
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨A, hAC, hAel, hAcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
      (H := centralizer (K : Set H)) (k := 2) hlt
    have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 2) hAcard
    obtain ⟨g, hg⟩ := exists_conj_subgroup_sylow T A hAp
    let A' : Subgroup H := A.map (MulAut.conj g).toMonoidHom
    have hA'T : A' ≤ (T : Subgroup H) := by
      rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hg a ha
    have hrankA : 2 ≤ Open.pRank 2 A := SU1.le_pRank (by norm_num) le_rfl hAel hAcard
    have hrankA' : 2 ≤ Open.pRank 2 A' := by
      rw [SU4.pRank_map_of_injective _ (MulAut.conj g).injective]; exact hrankA
    have hC := two_generated_core_subgroup_centralizer_le T H₀ h.sylow_le h.gamma A'
      (hA'T.trans h.sylow_le) hrankA'
    apply h.conj_not_le hFH hK hKH g
    intro x hx
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hax : x * a = a * x := (Subgroup.mem_centralizer_iff.mp (hAC ha) x hx)
    show (MulAut.conj g).toMonoidHom a * (g * x * g⁻¹) =
      (g * x * g⁻¹) * (MulAut.conj g).toMonoidHom a
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
      _ = g * (x * a) * g⁻¹ := by rw [hax]
      _ = g * x * g⁻¹ * (g * a * g⁻¹) := by group
  · exact one_le_two_rank_of_involution_mem _ t
      (Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp htc g) ht2


theorem isCyclic_center_of_unique_involution (T : Sylow 2 H) (t : H)
    (key : ∀ w : ↥(center ↥(T : Subgroup H)), orderOf w = 2 →
      (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) = t) :
    IsCyclic ↥(center ↥(T : Subgroup H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥(T : Subgroup H) := T.isPGroup'
  have hCp : IsPGroup 2 ↥(center ↥(T : Subgroup H)) := hTp.to_subgroup _
  obtain ⟨m, hm⟩ := hCp.exists_card_eq
  let : CommGroup ↥(center ↥(T : Subgroup H)) :=
    { (inferInstance : Group ↥(center ↥(T : Subgroup H))) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  exact
    CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    m _ hCp hm
    (fun left right hleft hright =>
      Subtype.ext (Subtype.ext ((key left hleft).trans (key right hright).symm)))

theorem Cfg.isCyclic_center (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hKH : ¬ K ≤ H₀) :
    IsCyclic ↥(center ↥(T : Subgroup H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP1 := h.pRank_centralizer_eq_one F hr htc ht2 hK hKH
  have hrk : CFSG.pRank 2 ↥K ≤ 1 := (pRank_coe_eq K).trans_le (hr K hK)
  have hZ := h.isPGroup_center_component hK
  obtain ⟨h5, -⟩ := component_sl25 F h hr htc ht2 hK hKH
  obtain ⟨S, hS⟩ := exists_sylow_component T hK
  have hinC : ∀ w : ↥(center ↥(T : Subgroup H)), orderOf w = 2 →
      (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) ∈ centralizer (K : Set H) := by
    intro w hw
    set u : H := (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) with hu
    have hu2 : u * u = 1 := by
      apply mul_self_eq_one_of_orderOf_two
      rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hw
    obtain ⟨k, hkK, hkc⟩ := h.exists_inner F hr htc ht2 hK hKH
      (w : ↥(T : Subgroup H)).2 hu2
    set c : H := u * k⁻¹ with hc
    have hkeq : k = c⁻¹ * u := by rw [hc]; group
    have hkS : (⟨k, hkK⟩ : ↥K) ∈ centralizer ((S : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsT : (s : H) ∈ (T : Subgroup H) := (hS s).mp hs
      have hus : u * (s : H) = (s : H) * u := by
        have := Subgroup.mem_center_iff.mp w.2 ⟨(s : H), hsT⟩
        exact (congrArg Subtype.val this).symm
      have hcs : (s : H) * c = c * (s : H) := Subgroup.mem_centralizer_iff.mp hkc (s : H) s.2
      apply Subtype.ext
      show (s : H) * k = k * (s : H)
      have hcs' : Commute c (s : H) := hcs.symm
      have hus' : Commute u (s : H) := hus
      have := (hcs'.inv_left.mul_left hus').eq
      rw [hkeq]
      exact this.symm
    have hkZ : (⟨k, hkK⟩ : ↥K) ∈ center ↥K := F.centralizer ↥K hK.1 hrk hZ h5 S hkS
    have hkC : k ∈ centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hkZ ⟨x, hx⟩)
    have : u = c * k := by rw [hkeq, hc]; group
    rw [this]
    exact Subgroup.mul_mem _ hkc hkC
  apply isCyclic_center_of_unique_involution T t
  intro w hw
  by_contra hne
  have hwC := hinC w hw
  have hw2 : orderOf (((w : ↥(T : Subgroup H)) : ↥(T : Subgroup H)) : H) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hw
  have htC : t ∈ centralizer (K : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp htc g
  have := two_le_pRank_of_commuting_involutions hw2 ht2 hne
    (Subgroup.mem_center_iff.mp htc _) hwC htC
  omega

theorem Cfg.closure_le (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hKH : ¬ K ≤ H₀) :
    Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ K ⊔ centralizer (K : Set H) := by
  rw [Subgroup.closure_le]
  rintro g ⟨hgT, hg2⟩
  obtain ⟨k, hkK, hkc⟩ := h.exists_inner F hr htc ht2 hK hKH hgT hg2
  have : g = (g * k⁻¹) * k := by group
  rw [SetLike.mem_coe, this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hkc) (Subgroup.mem_sup_left hkK)

end CFSG.GH74.Uniqueness.SU.K.R6
