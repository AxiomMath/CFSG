module

public import CFSG.LargeExtraspecial.S6EightB
public import CFSG.LargeExtraspecial.S6SixB
public import CFSG.LargeExtraspecial.S6SixC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

omit [Finite G] in
theorem card_eq_card_clSub {X : Subgroup G} (hX : X ≤ S.QG) (hz : S.z ∉ X) :
    Nat.card X = Nat.card (S.clSub X) := by
  let f : X → S.clSub X := fun x => ⟨S.cl x, S.cl_mem_clSub x.2 (hX x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    rcases (S.cl_eq_cl_iff (hX x.2) (hX y.2)).mp h with h1 | h1
    · exact Subtype.ext h1.symm
    · exfalso
      apply hz
      have e : S.z = (x : G)⁻¹ * y := by rw [h1]; group
      rw [e]
      exact mul_mem (inv_mem x.2) y.2
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨x, hxX, -, hx⟩ := S.mem_clSub_iff.mp v.2
    exact ⟨⟨x, hxX⟩, Subtype.ext hx⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem card_eq_card_map_mul {X : Subgroup G} (hXM : X ≤ S.M) :
    Nat.card X = Nat.card ((X.subgroupOf S.M).map S.ρ) *
      Nat.card (S.ρ.ker ⊓ X.subgroupOf S.M : Subgroup S.M) := by
  have h1 := Subgroup.relIndex_mul_card S.ρ.ker (X.subgroupOf S.M)
  rw [Subgroup.relIndex_ker] at h1
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]

theorem card_ker_inf_le {X : Subgroup G} {u : G} (hXu : X ≤ S.Qa u) :
    Nat.card (S.ρ.ker ⊓ X.subgroupOf S.M : Subgroup S.M) ≤
      Nat.card (S.QG ⊓ S.Qa u : Subgroup G) := by
  have hle : (S.ρ.ker ⊓ X.subgroupOf S.M).map S.M.subtype ≤ S.QG ⊓ S.Qa u := by
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨(S.ρ_eq_one_iff y).mp hy1, hXu (mem_subgroupOf.mp hy2)⟩
  rw [← Subgroup.card_map_of_injective S.M.subtype_injective]
  exact Subgroup.card_le_of_le hle

theorem card_le_two_mul (H : Hyp4 S g) (u : G) :
    Nat.card (S.Qa g ⊓ S.Qa u : Subgroup G) ≤
      2 * Nat.card ((S.Qa g ⊓ S.Qa u) ⊓ S.M : Subgroup G) := by
  set X0 := S.Qa g ⊓ S.Qa u with hX0
  set X := X0 ⊓ S.M with hX
  set aa := g * S.z * g⁻¹ with haa
  set Ta := S.conjBy g with hTa
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa H.conj_mem H.conj_ne
  have key : ∀ b ∈ X0, b ∉ S.M → S.z * b * S.z⁻¹ = aa * b := by
    intro b hb hbM
    rcases Ta.commutator_eq_one_or_z hzQa hb.1 with h | h
    · exfalso
      apply hbM
      rw [S.mem_M_iff]
      calc b * S.z = (S.z * b * S.z⁻¹ * b⁻¹)⁻¹ * (S.z * b) := by group
        _ = S.z * b := by rw [h, inv_one, one_mul]
    · calc S.z * b * S.z⁻¹ = (S.z * b * S.z⁻¹ * b⁻¹) * b := by group
        _ = aa * b := by rw [h]; rfl
  have hdvd : X.relIndex X0 ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hall : ∀ b ∈ X0, b ∈ S.M
    · exact ⟨1, one_mem _, fun b hb => Or.inr ⟨hb, hall b hb⟩⟩
    push Not at hall
    obtain ⟨a₀, ha₀, ha₀M⟩ := hall
    refine ⟨a₀, ha₀, fun b hb => ?_⟩
    by_cases hbM : b ∈ S.M
    · exact Or.inr ⟨hb, hbM⟩
    refine Or.inl (Subgroup.mem_inf.mpr ⟨mul_mem hb ha₀, ?_⟩)
    rw [S.mem_M_iff]
    have hab : b * aa = aa * b := Ta.z_comm_QG hb.1
    have haa2 : aa * aa = 1 := Ta.z_mul_z
    have h3 : S.z * (b * a₀) * S.z⁻¹ = b * a₀ := by
      calc S.z * (b * a₀) * S.z⁻¹ = (S.z * b * S.z⁻¹) * (S.z * a₀ * S.z⁻¹) := by group
        _ = aa * b * (aa * a₀) := by rw [key b hb hbM, key a₀ ha₀ ha₀M]
        _ = b * a₀ := by
          rw [← hab, mul_assoc b aa (aa * a₀), ← mul_assoc aa aa a₀, haa2, one_mul]
    calc b * a₀ * S.z = S.z * (b * a₀) * S.z⁻¹ * S.z := by rw [h3]
      _ = S.z * (b * a₀) := by group
  have h1 := Subgroup.relIndex_mul_card X X0
  rw [inf_eq_left.mpr (inf_le_left : X ≤ X0)] at h1
  have h2 := Nat.le_of_dvd two_pos hdvd
  rw [← h1]
  exact Nat.mul_le_mul_right _ h2

section Tau

variable (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) {τ : S.M} (hτ : S.ρ τ = t) {u : G}
  (hτu : (τ : G) = u * S.z * u⁻¹)
include H ht1 hτ hτu

theorem card_Qa_inf_Qa (C : Cons311 S g) (hF : FusionCtl S g)
    (haQt : g * S.z * g⁻¹ ∈ S.Qa u) :
    Nat.card (S.Qa g ⊓ S.Qa u : Subgroup G) = 2 ^ (S.width + 1) := by
  have hmap : S.Qa g ⊓ S.Qa u =
      (S.Qa (u⁻¹ * g) ⊓ S.QG).map (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective, ← S.Qa_eq_map, ← S.Qa_mul,
      mul_inv_cancel_left]
  rw [hmap, Subgroup.card_map_of_injective (MulAut.conj u).injective, inf_comm]
  have ha'Q : (u⁻¹ * g) * S.z * (u⁻¹ * g)⁻¹ ∈ S.QG := by
    rw [S.Qa_eq_map] at haQt
    obtain ⟨x, hx, hxa⟩ := haQt
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxa
    have e : x = (u⁻¹ * g) * S.z * (u⁻¹ * g)⁻¹ := by
      calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
        _ = (u⁻¹ * g) * S.z * (u⁻¹ * g)⁻¹ := by rw [hxa]; group
    rw [← e]
    exact hx
  have ha'z : (u⁻¹ * g) * S.z * (u⁻¹ * g)⁻¹ ≠ S.z := by
    intro h
    apply tau_not_mem_QG ht1 hτ
    have e : (τ : G) = g * S.z * g⁻¹ := by
      rw [hτu]
      calc u * S.z * u⁻¹ = u * ((u⁻¹ * g) * S.z * (u⁻¹ * g)⁻¹) * u⁻¹ := by rw [h]
        _ = g * S.z * g⁻¹ := by group
    rw [e]
    exact H.conj_mem
  obtain ⟨m, hm, hma⟩ := hF (u⁻¹ * g) ha'Q ha'z
  rw [S.Qa_eq_of_conj_eq (g := u⁻¹ * g) (h := m * g) (by rw [← hma]; group),
    S.card_QG_inf_Qa_mul hm, C.card_QG_inf_Qa]

omit H ht1 in
theorem commute_of_cl_mem_commSpace
    (hq : ∀ v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), S.q v = 0) {c : G} (hc : c ∈ S.QG)
    (hcU : S.cl c ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : c * τ = τ * c := by
  have hττ : (τ : G) * τ = 1 := by
    rw [hτu]
    exact (S.conjBy u).z_mul_z
  have hτi : (τ : G)⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hU' : S.cl c ∈ S.commQt (τ : G) := by
    rw [S.commQt_of_mem τ.2]
    exact hτ ▸ hcU
  obtain ⟨y, hyQ, hy⟩ := (S.mem_commQt_iff' τ.2).mp hU'
  set d := y * τ * y⁻¹ * (τ : G)⁻¹ with hd
  have hdQ : d ∈ S.QG := S.commutator_mem_QG' τ.2 hyQ
  have hd2 : d ^ 2 = 1 := (S.q_cl_eq_zero_iff hdQ).mp (hq _ (by rw [hy]; exact hcU))
  have hdd : d * τ = τ * d := by
    have h1 : d = d⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_two, hd2])
    calc d * τ = d⁻¹ * τ := by rw [← h1]
      _ = τ * y * (τ : G)⁻¹ * y⁻¹ * τ := by rw [hd]; group
      _ = τ * d := by rw [hd, hτi]; group
  rcases (S.cl_eq_cl_iff hdQ hc).mp hy with h | h
  · rw [h]
    exact hdd
  · rw [h]
    calc d * S.z * τ = d * (τ * S.z) := by rw [mul_assoc, S.z_comm τ.2]
      _ = τ * (d * S.z) := by rw [← mul_assoc, hdd, mul_assoc]

omit ht1 in
theorem map_le_Lbar_inf_Nbar (hNo : NoA2 S g) {ht : t ∈ S.Lbar g} (ht1 : t ≠ 1)
    (hL : LinCase S g ht)
    (hU8 : S.clSub (S.QG ⊓ S.Qa u) ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t) :
    (((S.Qa g ⊓ S.Qa u) ⊓ S.M).subgroupOf S.M).map S.ρ ≤ S.Lbar g ⊓ Nbar S g t := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨⟨hxg, hxu⟩, -⟩ := mem_subgroupOf.mp hx
  have hxL : S.ρ x ∈ S.Lbar g := ρ_mem_Lbar S ⟨hxg, x.2⟩
  refine ⟨hxL, mem_Nbar_of_apply_sub_mem_Tt H ht ht1 (Lbar_le_Rbar ht hxL) fun w hw => ?_⟩
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl w
  have hcτ := commute_of_cl_mem_commSpace hτ hτu
    (isTypeA_of_linCase H ht1 hL).2.2.2.2 hcQ hw
  have hxτ : (x : G) * τ = τ * x := commute_of_mem_Qa_tau hτu hxu
  have hmem : (x : G) * c * (x : G)⁻¹ * c⁻¹ ∈ S.QG ⊓ S.Qa u := by
    refine ⟨S.commutator_mem_QG x.2 hcQ, ?_⟩
    rw [show (x : G) * c * (x : G)⁻¹ * c⁻¹ = x * (c * (x : G)⁻¹ * c⁻¹) by group]
    exact mul_mem hxu (conj_mem_Qa_of_commute hτu (inv_mem hxu) hcτ)
  have hcl : S.cl ((x : G) * c * (x : G)⁻¹ * c⁻¹) =
      ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) - S.cl c := S.cl_commutator x.2 hcQ
  have hxt : S.ρ x * t = t * S.ρ x := by
    rw [← hτ, ← map_mul, ← map_mul]
    exact congrArg S.ρ (Subtype.ext hxτ)
  have hU : ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) - S.cl c ∈
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    sub_mem (apply_mem_commSpace_of_commute hxt hw) hw
  have hP : ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) - S.cl c ∈
      S.clSub (S.QG ⊓ S.Qa u) := by
    rw [← hcl]
    exact S.cl_mem_clSub hmem hmem.1
  exact Vt_le_Tt H hNo ht1 hL (hU8 ⟨hP, hU⟩)

end Tau

end CFSG.LargeExtraspecial.S6
