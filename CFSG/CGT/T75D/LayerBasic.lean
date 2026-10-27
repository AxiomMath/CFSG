module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary
import CFSG.Assembly.Defs

public section

namespace CFSG.CGT.T75D

open CFSG.Open

section Central

variable {H : Type*} [Group H] (O : Subgroup H) [O.Normal]

theorem mem_of_mk_mem_map [Finite H] (hO : ∀ o ∈ O, ∀ h : H, h * o = o * h)
    (hodd : Odd (Nat.card O)) {H₁ : Subgroup H} {α : H} (hα : α * α = 1)
    (h : (QuotientGroup.mk' O) α ∈ H₁.map (QuotientGroup.mk' O)) : α ∈ H₁ := by
  obtain ⟨h₁, hh₁, hπ⟩ := Subgroup.mem_map.1 h
  have hmem : h₁⁻¹ * α ∈ O := QuotientGroup.eq.1 hπ
  set o : H := h₁⁻¹ * α with ho
  have hαo : α = h₁ * o := by rw [ho]; group
  have hoo : o ^ Nat.card O = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard O hmem)
  have hcomm : Commute h₁ o := hO o hmem h₁
  have hαn : α ^ Nat.card O = α := by
    obtain ⟨j, hj⟩ := hodd
    rw [hj, pow_succ, pow_mul, pow_two, hα, one_pow, one_mul]
  have : α ^ Nat.card O = h₁ ^ Nat.card O := by
    conv_lhs => rw [hαo]
    rw [hcomm.mul_pow, hoo, mul_one]
  rw [← hαn, this]
  exact H₁.pow_mem hh₁ _

theorem eq_of_mk_eq [Finite H] (hO : ∀ o ∈ O, ∀ h : H, h * o = o * h)
    (hodd : Odd (Nat.card O)) {α β : H} (hα : α * α = 1) (hβ : β * β = 1)
    (h : (QuotientGroup.mk' O) α = (QuotientGroup.mk' O) β) : α = β := by
  have hmem : α⁻¹ * β ∈ O := QuotientGroup.eq.1 h
  set o : H := α⁻¹ * β with ho
  have hβo : β = α * o := by rw [ho]; group
  have hcomm : Commute α o := hO o hmem α
  have hoo : o ^ Nat.card O = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard O hmem)
  have ho2 : o * o = 1 := by
    have h1 : β * β = α * α * (o * o) := by
      rw [hβo]
      rw [show α * o * (α * o) = α * (o * α) * o by group, ← hcomm.eq]
      group
    rw [hβ, hα, one_mul] at h1
    exact h1.symm
  have : o = 1 := by
    obtain ⟨j, hj⟩ := hodd
    have h3 : o ^ Nat.card O = o := by
      rw [hj, pow_succ, pow_mul, pow_two, ho2, one_pow, one_mul]
    rw [← h3, hoo]
  rw [hβo, this, mul_one]

end Central

section PCore

variable {H : Type*} [Group H] [Finite H] (O : Subgroup H) [O.Normal]

theorem pCore_quotient_le_map (hO : ∀ o ∈ O, ∀ h : H, h * o = o * h) :
    CFSG.pCore 2 (H ⧸ O) ≤ (CFSG.pCore 2 H).map (QuotientGroup.mk' O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  set Q : Subgroup (H ⧸ O) := CFSG.pCore 2 (H ⧸ O) with hQ
  set N : Subgroup H := Q.comap π with hN
  have hNn : N.Normal := (inferInstance : (CFSG.pCore 2 (H ⧸ O)).Normal).comap π
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := H ⧸ O)
  let f : ↥N →* ↥Q := (π.comp N.subtype).codRestrict Q (fun x => x.2)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (q : H ⧸ O)
    exact ⟨⟨x, by
      show π x ∈ Q
      rw [hπ]
      simpa using (hx ▸ q.2)⟩, Subtype.ext hx⟩
  have hker : f.ker ≤ Subgroup.center ↥N := by
    intro x hx
    have h1 : π (x : H) = 1 := by
      have := MonoidHom.mem_ker.1 hx
      exact congrArg Subtype.val this
    have hxO : (x : H) ∈ O := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hO _ hxO y)
  have hQn : Group.IsNilpotent ↥Q := hQp.isNilpotent
  have hnil : Group.IsNilpotent ↥N := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
  have hP := Sylow.map_le_pCore hNn hnil 2 P
  have htop : (P.mapSurjective hf : Subgroup ↥Q) = ⊤ := by
    have : IsPGroup 2 (⊤ : Subgroup ↥Q) := hQp.to_subgroup _
    have h1 := this.le_sylow_of_normal (P.mapSurjective hf)
    exact top_le_iff.1 h1
  rw [Sylow.coe_mapSurjective] at htop
  intro q hq
  have hmem : (⟨q, hq⟩ : ↥Q) ∈ (P : Subgroup ↥N).map f := by rw [htop]; trivial
  obtain ⟨x, hxP, hxq⟩ := hmem
  refine ⟨(x : H), hP ⟨x, hxP, rfl⟩, ?_⟩
  exact congrArg Subtype.val hxq

end PCore

end CFSG.CGT.T75D
