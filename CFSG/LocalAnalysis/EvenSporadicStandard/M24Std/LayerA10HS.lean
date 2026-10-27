module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Fix
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier

theorem card_hsP_inf_centralizer
    {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsR) (hx2 : x ^ 2 = 1) :
    Nat.card (hsP ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 3850))) : Subgroup _) ∈
        ({44352000, 7680, 2880, 40320, 1920} : Finset ℕ) ∧
      (Nat.card (hsP ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 3850))) : Subgroup _) = 40320 →
        x ∉ hsP) := by
  by_cases h1 : x = 1
  · subst h1
    have htop : hsP ⊓ centralizer ({1} : Set (Equiv.Perm (Fin 3850))) = hsP :=
      inf_eq_left.2 fun p _ => mem_centralizer_singleton_iff.2 (by rw [one_mul, mul_one])
    rw [htop, card_hsP]
    exact ⟨by simp, by omega⟩
  obtain ⟨-, -, -, hrows, hcover, -, hlist, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover _ hx (orderOf_eq_prime hx2 h1)
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows r hr
  rw [inf_centralizer_conj hsP hg, card_map_of_injective (MulAut.conj g).injective, hcent]
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320), (true, 23100, 1920)] := by
    rw [← hlist]
    exact List.mem_map_of_mem (f := fun r => (r.outer, r.classSize, r.centOrder)) hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  refine ⟨by rcases hmem with h | h | h | h <;> simp [h.2.2], fun h40 hgP => ?_⟩
  have hrP : tp 3850 r.rep ∈ hsP := by
    have h := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) hgP) hg
    rwa [show g⁻¹ * (g * tp 3850 r.rep * g⁻¹) * g = tp 3850 r.rep by group] at h
  rcases hmem with h | h | h | h <;> rw [h.2.2] at h40 <;> try omega
  exact (hout.1 h.1) hrP

theorem not_isLayerInvolutionAut_hs
    (f : MulAut hsP) :
    ¬ IsLayerInvolutionAut 20160 f := by
  rintro ⟨hf, h⟩
  obtain ⟨e, he, -, -, -⟩ := hs_full_automorphism_model
  obtain ⟨x, rfl⟩ := e.surjective f
  have hxx : x * x = 1 := e.injective (by rw [map_mul, hf, map_one])
  have hx2 : (x : Equiv.Perm (Fin 3850)) ^ 2 = 1 := by
    rw [sq, ← Subgroup.coe_mul, hxx, Subgroup.coe_one]
  have hiff : ∀ p : hsP, e x p = p ↔
      (p : Equiv.Perm (Fin 3850)) ∈ centralizer ({(x : Equiv.Perm (Fin 3850))} : Set _) := by
    intro p
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, he, Subgroup.coe_inv,
      mul_inv_eq_iff_eq_mul, eq_comm]
  have hfix : Nat.card {p : hsP // e x p = p} = Nat.card (hsP ⊓
      centralizer ({(x : Equiv.Perm (Fin 3850))} : Set _) : Subgroup _) :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.1, mem_inf.2 ⟨p.1.2, (hiff _).1 p.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩, (hiff _).2 (mem_inf.1 y.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  obtain ⟨hmem, hout⟩ := card_hsP_inf_centralizer x.2 hx2
  rw [hfix] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases h with h | ⟨h1, h2, h3⟩
  · omega
  · have h40 : Nat.card (hsP ⊓
        centralizer ({(x : Equiv.Perm (Fin 3850))} : Set _) : Subgroup _) = 40320 := by omega
    obtain ⟨s, hs⟩ := h3 h40
    have hsR' : (s : Equiv.Perm (Fin 3850)) ∈ hsR := (le_sup_left : hsP ≤ hsR) s.2
    have hes : e ⟨s, hsR'⟩ = e x := by
      ext p
      rw [he, hs, MulAut.conj_apply]
      rfl
    have hxs : x = ⟨s, hsR'⟩ := e.injective hes.symm
    exact hout h40 (by rw [hxs]; exact s.2)

theorem not_isSporadic_layer_hs
    {X : Type} [Group X] [Finite X] {z : X} {H : Subgroup X}
    (hz : orderOf z = 2) (hH : Nonempty (H ≃* alternatingGroup (Fin 8)))
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X)) :
    ¬ IsSporadic (egaLayer (X ⧸ fusionOddCore X)) .HS := by
  rintro ⟨e₀⟩
  have e : egaLayer (X ⧸ fusionOddCore X) ≃* CFSG.Blueprint.NativeSporadic.HS := e₀
  exact not_nonempty_layer_of_alt8 hz hH hC hz' not_isLayerInvolutionAut_hs ⟨e.trans hsPermEquiv⟩

end CFSG.EvenSporadicStandard.M24Std
