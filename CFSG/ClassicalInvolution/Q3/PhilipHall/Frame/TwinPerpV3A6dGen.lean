module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

section DI

variable {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u : Y)

theorem ae6E_le_ae6D : ae6E Ω u ≤ ae6D Ω W u := by
  unfold ae6D
  have := le_iSup (fun m : ↥(MGrp Ω W) => conjSub (m : Y) (ae6E Ω u))
    ⟨1, (MGrp Ω W).one_mem⟩
  simpa only [conjSub_one] using this

theorem mem_normalizer_ae6D {m : Y} (hm : m ∈ MGrp Ω W) :
    m ∈ Subgroup.normalizer (ae6D Ω W u : Set Y) := by
  have hle : ∀ m ∈ MGrp Ω W, conjSub m (ae6D Ω W u) ≤ ae6D Ω W u := by
    intro m hm
    unfold ae6D
    rw [conjSub_iSup]
    refine iSup_le fun m' => ?_
    rw [← conjSub_mul]
    exact le_iSup (fun m'' : ↥(MGrp Ω W) => conjSub (m'' : Y) (ae6E Ω u))
      ⟨m * m', (MGrp Ω W).mul_mem hm m'.2⟩
  refine Generic.mem_normalizer_of_conjSub_eq (le_antisymm (hle m hm) ?_)
  have := conjSub_mono (n := m) (hle m⁻¹ ((MGrp Ω W).inv_mem hm))
  rwa [conjSub_conjSub_inv] at this

theorem M_le_ae6I : MGrp Ω W ≤ ae6I Ω W u := le_sup_left

theorem rLayer_le_ae6I : rLayer Ω u ≤ ae6I Ω W u := le_sup_right

theorem ae6I_le_normalizer_ae6D (hN : rLayer Ω u ≤ Subgroup.normalizer (ae6D Ω W u : Set Y)) :
    ae6I Ω W u ≤ Subgroup.normalizer (ae6D Ω W u : Set Y) :=
  sup_le (fun _ hm => mem_normalizer_ae6D Ω W u hm) hN

theorem isPGroup_two_of_sq_eq_one {D : Subgroup Y} (h : ∀ d ∈ D, d * d = 1) : IsPGroup 2 ↥D :=
  fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h x x.2)⟩

end DI

section ConjIn

variable {Y : Type} [Group Y] {X K : Subgroup Y}

theorem le_of_mem_ae6ConjIn (hK : K ≤ X) {L : Subgroup Y} (hL : L ∈ ae6ConjIn X K) : L ≤ X := by
  obtain ⟨g, hg, rfl⟩ := hL
  intro x hx
  have h1 : g⁻¹ * x * g ∈ K := mem_conjSub_iff.mp hx
  have h2 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [h2]
  exact X.mul_mem (X.mul_mem hg (hK h1)) (X.inv_mem hg)

theorem pSpan_ae6ConjIn_le (hK : K ≤ X) : pSpan (ae6ConjIn X K) ≤ X :=
  pSpan_le fun _ hL => le_of_mem_ae6ConjIn hK hL

theorem mem_ae6ConjIn_self : K ∈ ae6ConjIn X K := ⟨1, X.one_mem, conjSub_one K⟩

theorem conjSub_mem_ae6ConjIn {m : Y} (hm : m ∈ X) : conjSub m K ∈ ae6ConjIn X K := ⟨m, hm, rfl⟩

theorem conjSub_mem_of_mem_ae6ConjIn {g : Y} (hg : g ∈ X) {L : Subgroup Y}
    (hL : L ∈ ae6ConjIn X K) : conjSub g L ∈ ae6ConjIn X K := by
  obtain ⟨h, hh, rfl⟩ := hL
  exact ⟨g * h, X.mul_mem hg hh, by rw [conjSub_mul]⟩

theorem exists_conj_of_mem_ae6ConjIn {L L' : Subgroup Y} (hL : L ∈ ae6ConjIn X K)
    (hL' : L' ∈ ae6ConjIn X K) : ∃ x ∈ X, conjSub x L = L' := by
  obtain ⟨g, hg, rfl⟩ := hL
  obtain ⟨g', hg', rfl⟩ := hL'
  exact ⟨g' * g⁻¹, X.mul_mem hg' (X.inv_mem hg), by rw [conjSub_mul, conjSub_inv_conjSub]⟩

theorem ae6ConjIn_subset {Ω : Set (Subgroup Y)} (hΩ : ConjInvariant Ω) (hK : K ∈ Ω) :
    ae6ConjIn X K ⊆ Ω := by
  rintro _ ⟨g, -, rfl⟩
  exact hΩ g K hK

end ConjIn

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
