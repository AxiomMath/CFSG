module

public import CFSG.CGT.PushingUpLit.BHS7.SevenNine
public import CFSG.CGT.PushingUpLit.BHS7.ModuleW
public import CFSG.CGT.PushingUpLit.BHS7.QuotInv

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem conjSub_sup' (g : Γ) (A B : Subgroup Γ) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B :=
  Subgroup.map_sup _ _ _

theorem commutator_mem_centralizer_opResidual {G T E P V W X : Subgroup Γ} (hG : CharTwo G)
    (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) (hVQ : V ≤ pCoreOf 2 G)
    (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) (hne : ⁅E, V⁆ ≠ ⊥) (hTP : IsSylowOf 2 T P)
    (hPE : G ≤ P ⊔ E) (hW : IsModuleW P T V W) (hXT : X ≤ T)
    (hXn : T ≤ Subgroup.normalizer (X : Set Γ))
    (hXE : ∀ x ∈ X, ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (V : Set Γ)) {x : Γ}
    (hx : x ∈ X ⊓ pCoreOf 2 P) {w : Γ} (hw : w ∈ W) :
    x * w * x⁻¹ * w⁻¹ ∈ V ⊓ Subgroup.centralizer (opResidual 2 G : Set Γ) := by
  have hTG : T ≤ G := hT.1
  have hXG : X ≤ G := hXT.trans hTG
  have hX2 : IsPGroup 2 ↥X := hT.2.1.to_le hXT
  have hTP' : T ≤ P := hTP.1
  have hxX : x ∈ X := hx.1
  have hxO : x ∈ pCoreOf 2 P := hx.2
  have hwV : w ∈ V := hW.le_V hw
  have hCV : G ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set Γ) : Set Γ) :=
    B6.le_normalizer_centralizer hGV
  have hy : x * w * x⁻¹ * w⁻¹ = ⁅x, w⁆ := rfl
  have hyXV : ⁅x, w⁆ ∈ (⁅X, V⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hxX hwV
  have hyV : ⁅x, w⁆ ∈ V := commutator_le_of_le_normalizer (hXG.trans hGV) hyXV
  have hyP : ⁅x, w⁆ ∈ Subgroup.centralizer (opResidual 2 P : Set Γ) := by
    have h1 : ⁅w, x⁆ ∈ (⁅W, pCoreOf 2 P⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hw hxO
    have h2 : ⁅x, w⁆ = ⁅w, x⁆⁻¹ := (commutatorElement_inv w x).symm
    rw [h2]
    exact (Subgroup.centralizer (opResidual 2 P : Set Γ)).inv_mem (hW.pCore_comm_le h1).2
  have hEt : ∀ t ∈ T, ∀ f ∈ conjSub t E, ⁅x, w⁆ * f = f * ⁅x, w⁆ := by
    intro t ht f hf
    have htG : t ∈ G := hTG ht
    have hFt : IsBTBlock G T (conjSub t E) := by
      have := isBTBlock_conj t hE
      rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer htG),
        conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer ht)] at this
    have hneF : ⁅conjSub t E, V⁆ ≠ ⊥ := by
      have h1 := commutator_conjSub t E V
      rw [conjSub_eq_of_mem_normalizer (hGV htG)] at h1
      rw [h1]
      exact fun h => hne ((conjSub_eq_bot_iff t _).mp h)
    have hXF : ∀ x' ∈ X, ∀ f' ∈ conjSub t E, ⁅x', f'⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
      intro x' hx' f' hf'
      rw [mem_conjSub_iff] at hf'
      have hx'' : t⁻¹ * x' * t ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (hXn (T.inv_mem ht)) x').mp hx'
        simpa using this
      have h1 := hXE _ hx'' _ hf'
      have e : ⁅x', f'⁆ = t * ⁅t⁻¹ * x' * t, t⁻¹ * f' * t⁆ * t⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hCV htG) _).mp h1
    have h79 := commutator_commutator_eq_bot_of_comm_mod hG hT hFt hVQ hGV hneF hX2 hXG hXF
    have hy' : ⁅x, w⁆ ∈ (⁅V, X⁆ : Subgroup Γ) := by
      rw [Subgroup.commutator_comm]; exact hyXV
    have h1 : ⁅⁅x, w⁆, f⁆ ∈ (⁅⁅V, X⁆, conjSub t E⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hy' hf
    rw [h79, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  set C' : Subgroup Γ := opResidual 2 P ⊔ ⨆ t : ↥T, conjSub (t : Γ) E with hC'
  have hC'y : C' ≤ Subgroup.centralizer ({⁅x, w⁆} : Set Γ) := by
    refine sup_le (fun k hk => ?_) (iSup_le fun t f hf => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hyP k hk
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hEt t t.2 f hf).symm
  have hEC' : E ≤ C' := by
    intro e he
    refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (1 : ↥T) ?_)
    rw [show (((1 : ↥T) : Γ)) = 1 from rfl, conjSub_one]
    exact he
  have hTn : T ≤ Subgroup.normalizer (C' : Set Γ) := by
    have key : ∀ t ∈ T, conjSub t C' ≤ C' := by
      intro t ht
      rw [hC', conjSub_sup', conjSub_iSup]
      refine sup_le ?_ (iSup_le fun s => ?_)
      · rw [conjSub_eq_of_mem_normalizer (le_normalizer_opResidual' P (hTP' ht))]
        exact le_sup_left
      · rw [← conjSub_mul]
        exact le_sup_of_le_right
          (le_iSup (fun s : ↥T => conjSub (s : Γ) E) ⟨t * s, T.mul_mem ht s.2⟩)
    intro t ht
    exact BHS.mem_normalizer_of_conjSub_le (key t ht) (key t⁻¹ (T.inv_mem ht))
  have hGC' : G ≤ T ⊔ C' := by
    refine hPE.trans (sup_le ?_ (hEC'.trans le_sup_right))
    refine (le_sup_opResidual hTP).trans (sup_le le_sup_left ?_)
    exact (le_sup_left : opResidual 2 P ≤ C').trans le_sup_right
  have hO2G : opResidual 2 G ≤ C' := opResidual_le_of_le_sup hT.2.1 hTn hGC'
  refine ⟨hyV, ?_⟩
  show ⁅x, w⁆ ∈ Subgroup.centralizer (opResidual 2 G : Set Γ)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hC'y (hO2G hk))

end CFSG.CGT.PushingUpLit.BHS7
