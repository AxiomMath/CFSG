module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod

open CFSG.ClassicalInvolution.Q3.AE Wr

@[expose] noncomputable def wsumHom (n : ℕ) : Wr n →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd (wsum a)
  map_one' := by simp [wsum_one]
  map_mul' a b := by simp [wsum_mul]

@[expose] noncomputable def evenVec (n : ℕ) : Subgroup (Wr n) := vecSub n ⊓ (wsumHom n).ker

theorem mem_evenVec {n : ℕ} {a : Wr n} : a ∈ evenVec n ↔ a.perm = 1 ∧ wsum a = 0 := by
  simp only [evenVec, Subgroup.mem_inf, MonoidHom.mem_ker, wsumHom, MonoidHom.coe_mk,
    OneHom.coe_mk]
  exact and_congr Iff.rfl ⟨fun h => by simpa using h, fun h => by simp [h]⟩

instance evenVec_normal (n : ℕ) : (evenVec n).Normal := by
  unfold evenVec
  infer_instance

theorem exists_mem_sylow_evenVec {Y : Type} [Group Y] [Finite Y] {n : ℕ} (ψ : Y →* AEQ n)
    (S : Sylow 2 Y) {v : Wr n} (hv : v ∈ evenVec n) (hvr : mkQ n v ∈ ψ.range) :
    ∃ s ∈ (S : Subgroup Y), ψ s = mkQ n v := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup (AEQ n) := (evenVec n).map (mkQ n)
  haveI hN : N.Normal := Subgroup.Normal.map inferInstance (mkQ n) (QuotientGroup.mk'_surjective _)
  let N' : Subgroup ψ.range := N.subgroupOf ψ.range
  haveI : N'.Normal := Subgroup.Normal.subgroupOf hN _
  have h2 : IsPGroup 2 N' := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨u, hu, hug⟩ := g.2
    have hu2 : u * u = 1 := vecSub_mul_self (mem_evenVec.mp hu).1
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, pow_one]
    have hug' : (mkQ n) u = ((g : ψ.range) : AEQ n) := hug
    rw [pow_two, ← hug', ← map_mul, hu2, map_one]
  let ψ' : Y →* ψ.range := ψ.rangeRestrict
  have hsurj : Function.Surjective ψ' := MonoidHom.rangeRestrict_surjective ψ
  have hle : N' ≤ (S.mapSurjective hsurj : Subgroup ψ.range) := h2.le_sylow_of_normal _
  have hmem : (⟨mkQ n v, hvr⟩ : ψ.range) ∈ N' := ⟨v, hv, rfl⟩
  obtain ⟨s, hs, hsv⟩ := (by simpa using hle hmem : (⟨mkQ n v, hvr⟩ : ψ.range) ∈ S.map ψ')
  exact ⟨s, hs, congrArg Subtype.val hsv⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod
