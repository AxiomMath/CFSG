module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3Main

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem _root_.CFSG.QuasithinUnique.Setup.Layer.ConjFamily.reindex
    {G N A : Subgroup (V ≃ₗ[k] V)} {ι ι' : Type*} {g : ι → V ≃ₗ[k] V}
    (F : ConjFamily G N A g) (e : ι' ≃ ι) : ConjFamily G N A (g ∘ e) where
  mem i := F.mem (e i)
  inj := F.inj.comp e.injective
  all x hx := by
    obtain ⟨j, hj⟩ := F.all x hx
    exact ⟨e.symm j, by simpa [natL] using hj⟩

theorem commutator_ne_bot_of_centralizer_le {H N A : Subgroup (V ≃ₗ[k] V)} (hAH : A ≤ H)
    (hAne : A ≠ ⊥) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hodd : Odd (Nat.card N))
    (hC : H ⊓ Subgroup.centralizer (N : Set (V ≃ₗ[k] V)) ≤ N) : ⁅N, A⁆ ≠ ⊥ := by
  intro h
  have hAc : A ≤ Subgroup.centralizer (N : Set (V ≃ₗ[k] V)) := by
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hAN : A ≤ N := fun a ha => hC ⟨hAH ha, hAc ha⟩
  have h2 : 2 ∣ Nat.card ↥A := two_dvd_card_of_elem hAel hAne
  have hdvd : Nat.card ↥A ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hAN
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))

variable [CharP k 2] [Finite V]

theorem minimal_parabolic_odd_abelian_S3_wreath {H T M N E : Subgroup (V ≃ₗ[k] V)}
    (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (hNab : ∀ x y : ↥N, x * y = y * x)
    (hNodd : Odd (Nat.card N))
    (hCN : H ⊓ Subgroup.centralizer (N : Set (V ≃ₗ[k] V)) ≤ N)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 ↥E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) : S3Wreath H T N := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hO2 := pCore_trivial_of_centralizer_le hNH hNn hNodd hCN
  obtain ⟨A, hA⟩ := exists_minOffender hEH hEne hEel hEoff
  obtain ⟨hAH, hAne, hAel, hAoff, hAstrict⟩ := hA
  have hcomm := commutator_ne_bot_of_centralizer_le hAH hAne hAel hNodd hCN
  have hset : OddAbelianSetting H N A :=
    ⟨hNH, hNn, hNab, hNodd, hAH, hAel, hAne, hAoff, hAstrict, hcomm⟩
  obtain ⟨ι, hfin, g0, F0⟩ := exists_conjFamily H N A
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hF : ConjFamily H N A (g0 ∘ e) := F0.reindex e
  have hnat := hset.naturalS3Factors hF
  exact s3Wreath_of_natural hnat hF hNH hNn hNodd hAne hAel hO2 hT hTn hTM hMH hmax

end CFSG.QuasithinUnique.Setup.Wreath
