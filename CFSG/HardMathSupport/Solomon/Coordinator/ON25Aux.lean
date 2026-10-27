module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Quasi
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Local

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.Native.ONTriple Subgroup CFSG.Open
open scoped commutatorElement

section


theorem on25_hKbar {Y : Type} [Group Y] [Finite Y] (q : GM →* Y) (hker : q.ker ≤ zpowers zG)
    (hq : Function.Surjective q) (n : GM) :
    CFSG.Open.IsQuasisimple ↥((K0G.map (MulAut.conj n).toMonoidHom).map q) ∧
      IsPGroup 3 (Subgroup.center ↥((K0G.map (MulAut.conj n).toMonoidHom).map q)) ∧
      3 ∣ Nat.card ((K0G.map (MulAut.conj n).toMonoidHom).map q) := by
  set K := K0G.map (MulAut.conj n).toMonoidHom with hK
  let ρ : ↥K →* ↥(K.map q) :=
    (q.domRestrict K).codRestrict (K.map q) (fun k => ⟨k, k.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    exact ⟨⟨k, hk⟩, Subtype.ext rfl⟩
  have hkerρ : ρ.ker ≤ Subgroup.center ↥K := by
    intro k hk
    have h1 : q (k : GM) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      exact this
    have h2 : (k : GM) ∈ center GM := by
      rw [center_GM]
      exact hker (MonoidHom.mem_ker.2 h1)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 g)
  have h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
    rw [on25_card_K, on25_card_center_K] at h1
    exact ⟨120, by omega⟩
  exact on25_quasi_of_central_surj (on25_K_quasisimple n) (on25_center_K_pgroup n) h3 ρ hρ hkerρ

end

theorem on25_comm_central {Y : Type*} [Group Y] {B : Subgroup Y}
    (hB : IsMulCommutative (B.map (QuotientGroup.mk' (Subgroup.center Y)))) :
    ∀ x ∈ B, ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ Subgroup.center Y := by
  intro x hx b hb
  have h := hB.is_comm.comm (⟨QuotientGroup.mk' (Subgroup.center Y) x, x, hx, rfl⟩ :
    ↥(B.map (QuotientGroup.mk' (Subgroup.center Y))))
    ⟨QuotientGroup.mk' (Subgroup.center Y) b, b, hb, rfl⟩
  have h' : QuotientGroup.mk' (Subgroup.center Y) x * QuotientGroup.mk' (Subgroup.center Y) b =
      QuotientGroup.mk' (Subgroup.center Y) b * QuotientGroup.mk' (Subgroup.center Y) x :=
    congrArg Subtype.val h
  rw [← QuotientGroup.ker_mk' (Subgroup.center Y), MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [h']
  group

theorem on25_card_subgroup {Y : Type*} [Group Y] [Finite Y] (B : Subgroup Y) :
    Nat.card B = Nat.card (B.map (QuotientGroup.mk' (Subgroup.center Y))) *
      Nat.card (B ⊓ Subgroup.center Y : Subgroup Y) := by
  let φ := (QuotientGroup.mk' (Subgroup.center Y)).domRestrict B
  have h := Subgroup.card_ker_mul_card_range φ
  have hr : φ.range = B.map (QuotientGroup.mk' (Subgroup.center Y)) := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hk : Nat.card φ.ker = Nat.card (B ⊓ Subgroup.center Y : Subgroup Y) := by
    have : φ.ker = (Subgroup.center Y).subgroupOf B := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show QuotientGroup.mk' (Subgroup.center Y) (g : Y) = 1 ↔ _
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    rw [this, ← Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hr, hk] at h
  rw [← h, mul_comm]

end CFSG.HardMathSupport.Solomon.Coordinator
