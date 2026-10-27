module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups commutatorElement

theorem center_eq_bot_of_odd_central_extension
    {n : ℕ} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) {L : Type*} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (α : (L ⧸ Subgroup.center L) ≃* SL(2, F)) (hodd : Odd (Nat.card (Subgroup.center L))) :
    Subgroup.center L = ⊥ := by
  have : CharP F 2 := charP_two_of_card_eq hF
  have : Finite F := inferInstance
  let π : L →* SL(2, F) := α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := α.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext l
    rw [MonoidHom.mem_ker]
    show α (QuotientGroup.mk' (Subgroup.center L) l) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff l
  obtain ⟨s, hs, -, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting
    (K := F) (n := 2) (le_refl 2) hπ hker.le (by rw [hker]; exact hodd)
  have hdec : ∀ l : L, l * (s (π l))⁻¹ ∈ Subgroup.center L := by
    intro l
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
  have hcomm : commutator L ≤ s.range := by
    show ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ ≤ s.range
    refine Subgroup.commutator_le.mpr (fun l₁ _ l₂ _ => ?_)
    have key : ⁅l₁, l₂⁆ = ⁅s (π l₁), s (π l₂)⁆ := by
      calc ⁅l₁, l₂⁆ = ⁅(l₁ * (s (π l₁))⁻¹) * s (π l₁), (l₂ * (s (π l₂))⁻¹) * s (π l₂)⁆ := by
            rw [inv_mul_cancel_right, inv_mul_cancel_right]
        _ = ⁅s (π l₁), (l₂ * (s (π l₂))⁻¹) * s (π l₂)⁆ :=
            commutator_central_left (hdec l₁) _ _
        _ = ⁅s (π l₁), s (π l₂)⁆ := commutator_central_right (hdec l₂) _ _
    rw [key, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hRtop : s.range = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hperf]
    exact hcomm
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz1 : π z = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hz
  have hzs : z ∈ s.range := by rw [hRtop]; exact Subgroup.mem_top z
  obtain ⟨g, rfl⟩ := hzs
  have hg : g = 1 := by rw [← hs g]; exact hz1
  rw [hg, map_one]

theorem exists_pow_two_card_conj_family {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) {r : ℕ} (L : Fin r → Subgroup G) (hinj : Function.Injective L)
    (hperm : ∀ t ∈ T, ∀ i, ∃ j, (L i).map (MulAut.conj t).toMonoidHom = L j)
    (htrans : ∀ i j, ∃ t ∈ T, (L i).map (MulAut.conj t).toMonoidHom = L j) (i₀ : Fin r) :
    ∃ k : ℕ, r = 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction T (Subgroup G) :=
    { smul := fun t K => K.map (MulAut.conj (t : G)).toMonoidHom
      one_smul := fun K => by
        show K.map (MulAut.conj ((1 : T) : G)).toMonoidHom = K
        have : (MulAut.conj ((1 : T) : G)).toMonoidHom = MonoidHom.id G := by
          ext x; simp
        rw [this, Subgroup.map_id]
      mul_smul := fun a b K => by
        show K.map (MulAut.conj (((a * b : T)) : G)).toMonoidHom =
          (K.map (MulAut.conj (b : G)).toMonoidHom).map (MulAut.conj (a : G)).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [mul_assoc] }
  obtain ⟨k, hk⟩ := hT.card_orbit (α := Subgroup G) (L i₀)
  refine ⟨k, ?_⟩
  have horb : (MulAction.orbit T (L i₀) : Set (Subgroup G)) = Set.range L := by
    ext K
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨j, hj⟩ := hperm t t.2 i₀
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨t, ht, h⟩ := htrans i₀ j
      exact ⟨⟨t, ht⟩, h⟩
  have h2 : Nat.card (MulAction.orbit T (L i₀)) = r := by
    rw [horb, Nat.card_range_of_injective hinj]
    simp
  rw [← h2, hk]

end CFSG.QuasithinUnique.Setup.Lift
