module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Count
public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMInvol
public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMFus
public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMWeak
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2B4A

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Main

variable {r : ℕ} {G : Type} [Group G] [Finite G]

theorem tightPMR_of_le_pm (hr : 4 ≤ r) {R : Subgroup G} {S : Sylow 2 R} {t : G}
    {T : Sylow 2 G} (h : StdR r R S t T) {U : Subgroup G}
    (hUS : U ≤ (S : Subgroup R).map R.subtype) (hUc : IsCyclic ↥U)
    (hUi : U.relIndex ((S : Subgroup R).map R.subtype) = 2)
    (hT : (T : Subgroup G) ≤ pmSubgroup U) :
    ∀ C : Subgroup G, C ≤ (S : Subgroup R).map R.subtype → IsCyclic ↥C →
      C.relIndex ((S : Subgroup R).map R.subtype) = 2 →
      ∀ g ∈ (T : Subgroup G), (∀ x ∈ C, g * x * g⁻¹ = x) ∨ (∀ x ∈ C, g * x * g⁻¹ = x⁻¹) := by
  intro C hCS hCc hCi g hg
  obtain ⟨e₀⟩ := h.quat
  let e : ↥((S : Subgroup R).map R.subtype) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e₀
  have hCU : C = U := eq_of_isCyclic_of_relIndex_eq_two hr e hCS hCc hCi hUS hUc hUi
  subst hCU
  exact hT hg

theorem tight_le_pm (hr : 4 ≤ r) {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}
    (h : StdR r R S t T) (hgen : TightSelfGen R) {W L : Subgroup G} {t' : G} {V : Subgroup G}
    (hd : TightSylowDataTR r (tightCore R) t T W L t' V) (hB : TightBPrimeBot (tightCore R) T W L) :
    (T : Subgroup G) ≤ pmSubgroup (tightCore R ⊓ W) := by
  by_contra hT
  obtain ⟨x, hxT, hx2, hxN⟩ := hd.exists_involution hB hr hT
  obtain ⟨w₀, hw₀, hw₀x, -, hw₀4⟩ := hd.exists_order_four hr hxT hx2 hxN
  refine TL4.LinkZ2B.false_of_transfer_tight (R := R) (R₀ := (S : Subgroup R).map R.subtype)
    hgen h.sylow_core T (N := pmSubgroup (tightCore R ⊓ W)) ?_ hxT hxN (by rw [sq]; exact hx2)
    ?_ ?_
  · intro y hy z hz
    exact commutator_mem_pmSubgroup hd.isCyclic_inf (hd.le_normalizer_inf_W hr hy)
      (hd.le_normalizer_inf_W hr hz)
  · intro g hg
    exact hd.hfus hr hxT hx2 hxN hw₀ hw₀x hw₀4 g hg
  · intro y hy hy1 g hg
    rw [← h.inf_core_eq] at hy
    exact hd.hweak hr hy hy1 hg

end Main

theorem tightPMR (r : ℕ) (IH : ℕ → Prop) : TightPMR r IH := by
  intro hr G _ _ _ hIH hnab R S t T h hcls hmu hcore hE
  obtain ⟨W, hW, hWT⟩ := h.exists_w69
  obtain ⟨L, t', V, hd⟩ := (h.sylowData hmu hW hWT).exists_dataT
  have hB : TightBPrimeBot (tightCore R) T W L := hcore G hnab R S t T W L t' V h hd
  have hle : (T : Subgroup G) ≤ pmSubgroup (tightCore R ⊓ W) :=
    tight_le_pm hr h hcls.2.1 hd hB
  have hUS : tightCore R ⊓ W ≤ (S : Subgroup R).map R.subtype := by
    rw [← h.inf_core_eq]
    exact hd.inf_le_inf_core
  have hUi : (tightCore R ⊓ W).relIndex ((S : Subgroup R).map R.subtype) = 2 := by
    rw [← h.inf_core_eq]
    exact hd.relIndex_inf
  exact tightPMR_of_le_pm hr h hUS hd.isCyclic_inf hUi hle

end CFSG.CGT.PushingUpLit.SolKNA.R4
