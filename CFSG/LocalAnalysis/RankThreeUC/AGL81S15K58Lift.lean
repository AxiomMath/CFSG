module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K58Section
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.Transfer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem fixed_of_sub_fixed {G : Type*} [Group G] [Finite G] (ρ : Representation (ZMod 2) G V)
    (S : Subgroup G) (hS : ¬ 2 ∣ S.index) {v : V} (hfix : ∀ g h, ρ g (ρ h v - v) = ρ h v - v)
    (hv : ∀ s ∈ S, ρ s v = v) (g : G) : ρ g v = v := by
  letI : DistribMulAction G V := DistribMulAction.compHom V (1 : G →* Module.End (ZMod 2) V)
  have hsmul : ∀ (h : G) (x : V), h • x = x := fun _ _ => rfl
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index S hS (fun h => ρ h v - v)
    (fun a b => by
      rw [hsmul, map_mul, Module.End.mul_apply]
      calc ρ a (ρ b v) - v = (ρ a (ρ b v - v) + ρ a v) - v := by rw [map_sub]; abel
        _ = (ρ a v - v) + (ρ b v - v) := by rw [hfix]; abel)
    (fun s hs => by rw [hv s hs, sub_self])
  have h := hm g
  rw [hsmul, sub_self] at h
  exact sub_eq_zero.mp h

variable {H : Type} [Group H] [Finite H]

theorem fixes_of_fixes_secW (ρ : Representation (ZMod 2) H V) (K : Subgroup H)
    {S P : Subgroup ↥K} (hSP : S ≤ P) (hS : ¬ 2 ∣ S.index)
    (hP : ∀ m : SecW ρ K, (∀ s ∈ S, secW ρ K s m = m) → ∀ p ∈ P, secW ρ K p m = m)
    {v : V} (hv : ∀ s ∈ S, ρ (s : H) v = v) : ∀ p ∈ P, ρ (p : H) v = v := by
  letI : DistribMulAction ↥K (SecW ρ K) := DistribMulAction.compHom _ (secW ρ K)
  have hsmul : ∀ (k : ↥K) (m : SecW ρ K), k • m = secW ρ K k m := fun _ _ => rfl
  let c : ↥K → SecW ρ K := fun k =>
    Submodule.Quotient.mk ⟨ρ k v - v, sub_mem_commOn k.2 Submodule.mem_top⟩
  have hc : ∀ a b : ↥K, c (a * b) = c a + a • c b := fun a b => by
    rw [hsmul, secW_mk, ← Submodule.Quotient.mk_add]
    show (Submodule.Quotient.mk ⟨ρ (a * b : ↥K) v - v, sub_mem_commOn (a * b).2 Submodule.mem_top⟩ :
      SecW ρ K) = _
    congr 1
    apply Subtype.ext
    show ρ (a * b : ↥K) v - v = (ρ a v - v) + ρ a (ρ b v - v)
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hS0 : ∀ s ∈ S, c s = 0 := fun s hs => by
    rw [secW_mk_eq_zero]
    show ρ s v - v ∈ _
    rw [hv s hs, sub_self]
    exact zero_mem _
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index S hS c hc hS0
  have hmP := hP m (fun s hs => fixed_of_coboundary_of_vanishes S c m hm hS0 s hs)
  have hPC : ∀ p ∈ P, ρ (p : H) v - v ∈ fixOn ρ K (commOn ρ K ⊤) := fun p hp => by
    have h1 : c p = 0 := by rw [hm p, hsmul, hmP p hp, sub_self]
    exact (secW_mk_eq_zero ρ K _).1 h1
  have hodd : ¬ 2 ∣ (S.subgroupOf P).index := fun h2 =>
    hS (Subgroup.relIndex_mul_index hSP ▸ Dvd.dvd.mul_right h2 _)
  intro p hp
  exact fixed_of_sub_fixed (ρ.comp (K.subtype.comp P.subtype)) (S.subgroupOf P) hodd
    (fun a b => (mem_fixOn.mp (hPC b b.2)).2 _ (a : ↥K).2)
    (fun s hs => hv s (Subgroup.mem_subgroupOf.mp hs)) ⟨p, hp⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof
