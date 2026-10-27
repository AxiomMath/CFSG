module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Def
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix

@[expose] def Nar24Mat : Prop :=
  ∀ (H D : Subgroup (GL (Fin 6) (ZMod 2))) (τ : GL (Fin 6) (ZMod 2)),
    IsSimpleGroup ↥H → (¬ ∀ x y : ↥H, x * y = y * x) → 2 ^ 6 ∣ Nat.card ↥H →
    D ≤ H → Nonempty (↥D ≃* GL (Fin 3) (ZMod 2)) →
    (∀ x ∈ D, x ^ 7 = 1 → x ≠ 1 → ∀ v : Fin 6 → ZMod 2,
      (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v → v = 0) →
    τ ^ 2 = 1 → (∀ d ∈ D, τ * d = d * τ) → (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) →
    (∀ c ∈ H, c * τ = τ * c → ∀ d ∈ D, c * d * c⁻¹ ∈ D) → False

theorem nar24_of_mat (h : Nar24Mat) : Nar24 := by
  intro M _ _ hE H D τ hs hnc h64 hDH hD hfpf hτ hcomm hnorm hcen
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEl, hcard⟩ := hE
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := M) (p := 2) (n := 6)
    (fun a b => congrArg Subtype.val
      (hEl.1.is_comm.comm (⟨a, Subgroup.mem_top a⟩ : (⊤ : Subgroup M))
        (⟨b, Subgroup.mem_top b⟩ : (⊤ : Subgroup M))))
    (fun a => hEl.2 a (Subgroup.mem_top a)) hcard
  let Φ := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  let f : MulAut M →* GL (Fin 6) (ZMod 2) := Φ.toMonoidHom
  have hf : Function.Injective f := Φ.injective
  haveI : IsSimpleGroup ↥H := hs
  refine h (H.map f) (D.map f) (f τ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (Subgroup.equivMapOfInjective H f hf).symm.isSimpleGroup
  · intro hc
    apply hnc
    intro a b
    apply (Subgroup.equivMapOfInjective H f hf).injective
    rw [map_mul, map_mul]
    exact hc _ _
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective H f hf).toEquiv.symm]
    exact h64
  · exact Subgroup.map_mono hDH
  · exact ⟨(Subgroup.equivMapOfInjective D f hf).symm.trans hD.some⟩
  ·
    intro x' hx' hx7 hx1 v hv
    obtain ⟨x, hxD, rfl⟩ := Subgroup.mem_map.1 hx'
    have hx7' : x ^ 7 = 1 := by
      apply hf
      rw [map_pow, map_one]
      exact hx7
    have hx1' : x ≠ 1 := by
      intro hx
      apply hx1
      rw [hx, map_one]
    obtain ⟨m, hm⟩ : ∃ m : M, Multiplicative.toAdd (e m) = v :=
      ⟨e.symm (Multiplicative.ofAdd v), by simp⟩
    have hmv : (f x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Multiplicative.toAdd (e m) =
        Multiplicative.toAdd (e (x m)) := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e x m
    rw [hm, hv] at hmv
    have hxm : x m = m := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [← hmv, hm]
    have hm1 : m = 1 := hfpf x hxD hx7' hx1' m hxm
    have hv0 : v = Multiplicative.toAdd (e 1) := by rw [← hm, hm1]
    rw [hv0, map_one, toAdd_one]
  · rw [← map_pow, hτ, map_one]
  · intro d' hd'
    obtain ⟨d, hdD, rfl⟩ := Subgroup.mem_map.1 hd'
    rw [← map_mul, ← map_mul, hcomm d hdD]
  · intro h' hh'
    obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.1 hh'
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem f (hnorm y hyH)
  · intro c' hc' hcτ d' hd'
    obtain ⟨c, hcH, rfl⟩ := Subgroup.mem_map.1 hc'
    obtain ⟨d, hdD, rfl⟩ := Subgroup.mem_map.1 hd'
    have hcτ' : c * τ = τ * c := by
      apply hf
      rw [map_mul, map_mul]
      exact hcτ
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem f (hcen c hcH hcτ' d hdD)

end CFSG.OddStandard.HigherRank.YamadaG23
