module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathNorm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

theorem WreathK.card_layer_inf_centralizer_outer (hK : WreathK t A K) {u : X} (hu2 : u * u = 1)
    (hn : u ∉ normalizer (K : Set X)) :
    Nat.card ↥(CFSG.layer X ⊓ centralizer ({u} : Set X)) = 20160 := by
  have hu : K.map (MulAut.conj u).toMonoidHom = conjSub t K :=
    hK.map_conj_eq_conjSub_of_notMem hn
  have hu' : (conjSub t K).map (MulAut.conj u).toMonoidHom = K :=
    hK.map_conj_conjSub_eq_of_notMem hu2 hn
  have mem_conj : ∀ k ∈ K, u * k * u⁻¹ ∈ conjSub t K := by
    intro k hk
    rw [← hu]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hk
  have mem_K : ∀ k' ∈ conjSub t K, u * k' * u⁻¹ ∈ K := by
    intro k' hk'
    rw [← hu']
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hk'
  have hconj_inv (k : X) : u * (u * k * u⁻¹) * u⁻¹ = k := by
    have huu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    rw [show u * (u * k * u⁻¹) * u⁻¹ = (u * u) * k * (u⁻¹ * u⁻¹) by group,
      hu2, huu, hu2, one_mul, mul_one]
  have mem_central (k : X) (hk : k ∈ K) :
      k * (u * k * u⁻¹) ∈ centralizer ({u} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hw : u * k * u⁻¹ ∈ conjSub t K := mem_conj k hk
    have hcomm : k * (u * k * u⁻¹) = (u * k * u⁻¹) * k := hK.commute hk hw
    have hconj : u * (k * (u * k * u⁻¹)) * u⁻¹ = k * (u * k * u⁻¹) :=
      calc u * (k * (u * k * u⁻¹)) * u⁻¹
          = (u * k * u⁻¹) * (u * (u * k * u⁻¹) * u⁻¹) := by group
        _ = (u * k * u⁻¹) * k := by rw [hconj_inv]
        _ = k * (u * k * u⁻¹) := hcomm.symm
    have := congrArg (fun x => x * u) hconj
    have hfin : u * (k * (u * k * u⁻¹)) = (k * (u * k * u⁻¹)) * u := by
      simpa [mul_assoc] using this
    exact hfin.symm
  let f : K → ↥(CFSG.layer X ⊓ centralizer ({u} : Set X)) := fun k =>
    ⟨(k : X) * (u * (k : X) * u⁻¹),
      ⟨mul_mem (hK.le_layer k.2) (hK.conjSub_le_layer (mem_conj k k.2)),
        mem_central k k.2⟩⟩
  have hinj : Function.Injective f := by
    intro k₁ k₂ h
    have hval : (k₁ : X) * (u * (k₁ : X) * u⁻¹) =
        (k₂ : X) * (u * (k₂ : X) * u⁻¹) := congrArg Subtype.val h
    exact Subtype.ext
      (hK.eq_of_mul_eq k₁.2 k₂.2 (mem_conj k₁ k₁.2) (mem_conj k₂ k₂.2) hval).1
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgE, hgC⟩ := hg
    obtain ⟨k, hk, k', hk', hgk⟩ := hK.mem_layer_iff.mp hgE
    have hcomm : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hmemKk' : u * k' * u⁻¹ ∈ K := mem_K k' hk'
    have hmemconjk : u * k * u⁻¹ ∈ conjSub t K := mem_conj k hk
    have hconj_g : u * g * u⁻¹ = g := by rw [← hcomm]; group
    have hsplit : u * g * u⁻¹ = (u * k * u⁻¹) * (u * k' * u⁻¹) := by
      rw [hgk]; group
    have hg_decomp : g = (u * k * u⁻¹) * (u * k' * u⁻¹) := hconj_g.symm.trans hsplit
    have hEq : k * k' = (u * k' * u⁻¹) * (u * k * u⁻¹) := by
      rw [← hgk, hg_decomp, (hK.commute hmemKk' hmemconjk).symm]
    obtain ⟨hk_eq, hk'_eq⟩ := hK.eq_of_mul_eq hk hmemKk' hk' hmemconjk hEq
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    show k * (u * k * u⁻¹) = g
    rw [← hk'_eq, ← hgk]
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  calc Nat.card ↥(CFSG.layer X ⊓ centralizer ({u} : Set X))
      = Nat.card K := (Nat.card_congr (Equiv.ofBijective f hbij)).symm
    _ = 20160 := hK.card_K

theorem WreathK.seven_dvd_card_centralizer_outer (hK : WreathK t A K) {u : X} (hu2 : u * u = 1)
    (hn : u ∉ normalizer (K : Set X)) : 7 ∣ Nat.card ↥(centralizer ({u} : Set X)) := by
  have h1 : 7 ∣ Nat.card ↥(CFSG.layer X ⊓ centralizer ({u} : Set X)) := by
    rw [WreathK.card_layer_inf_centralizer_outer hK hu2 hn]
    norm_num
  have h2 : Nat.card ↥(CFSG.layer X ⊓ centralizer ({u} : Set X)) ∣
      Nat.card ↥(centralizer ({u} : Set X)) :=
    Subgroup.card_dvd_of_le inf_le_right
  exact h1.trans h2

end CFSG.OddStandard.AltStdSec.SwapPattern
