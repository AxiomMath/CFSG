module

public import CFSG.CGT.PushingUpLit.SYMB.SevenFamily
public import CFSG.CGT.PushingUpLit.SYMB.SevenSchur
public import CFSG.CGT.PushingUpLit.SYMB.Assembly
public import CFSG.CGT.PushingUpLit.SYMB.Reduce

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

theorem symCaseTwo_seven : SymCaseTwoAt fun m => 3 ≤ m := by
  intro Γ _ _ G T V m hm φ ψ T' S hih hno
  classical
  set E : Subgroup Γ := sSup (altBlocks G T φ) with hEdef
  have hJ : SymJoin G T V φ ψ E := symJoin_altBlocks S hm hih
  have hEG : E ≤ G := hJ.le
  have hcomm : ⁅E, pCoreOf 2 G⁆ ≤ V := altBlocks_comm_pCore_le S
  set K : Subgroup Γ := E ⊓ Subgroup.centralizer (V : Set Γ) with hK
  have hKE : K ≤ E := inf_le_left
  have hK2 : IsPGroup 2 ↥K := isPGroup_inf_centralizer_of_comm_le S.charTwo hEG hcomm
  have hKker : K ≤ kerG G φ := fun k hk => sym_mem_kerG S (hEG hk.1) hk.2
  have hQn : G ≤ Subgroup.normalizer ((T ⊓ kerG G φ : Subgroup Γ) : Set Γ) :=
    sym_Q_normal_of_no_L S hno
  have hQs := sym_Q_sylow S
  have hKQ : K ≤ T ⊓ kerG G φ :=
    le_of_isPGroup_of_normal_sylow hQs (fun g hg => hQn (mem_kerG.1 hg).1) hKker hK2
  have hQG : T ⊓ kerG G φ ≤ G := inf_le_right.trans fun _ hg => (mem_kerG.1 hg).1
  have hQW : T ⊓ kerG G φ ≤ pCoreOf 2 G := le_pCoreOf_of_normalizes hQG hQn hQs.2.1
  have hKW : K ≤ pCoreOf 2 G := hKQ.trans hQW
  have hKEV : ⁅K, E⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hKW).trans hcomm
  obtain ⟨F, hF⟩ := altBlocks_nonempty S hm hih
  obtain ⟨hFB, hFn, Ω, hΩ5, hFΩ⟩ := hF
  obtain ⟨s, hsΩ, hscard⟩ := Finset.exists_subset_card_eq (show 4 ≤ Ω.card by omega)
  let p : Fin 4 → Fin (2 * m + 1) := fun i => s.orderEmbOfFin hscard i
  have hp : Function.Injective p := (s.orderEmbOfFin hscard).injective
  have hpΩ : ∀ i, p i ∈ Ω := fun i => hsΩ (s.orderEmbOfFin_mem hscard i)
  obtain ⟨a, haF, b, hbF, ha, hb, haφ, hbφ, hab⟩ := exists_lifts_block S hFB hFn hFΩ hp hpΩ
  have hFE : F ≤ E := le_sSup ⟨hFB, hFn, Ω, hΩ5, hFΩ⟩
  have hFK : pCoreOf 2 F ≤ K := by
    rw [← sym_inf_centralizer_block S hFB hFn]
    exact inf_le_inf hFE le_rfl
  have hab' : (a * b) ^ 2 ∈ ⁅K, E⁆ := by
    have h1 : (a * b) ^ 2 ∈ ⁅pCoreOf 2 F, F⁆ := by
      rw [hFB.perfect]
      exact hab
    exact Subgroup.commutator_mono hFK hFE h1
  have hSch : K ≤ ⁅K, E⁆ :=
    hJ.ker_le_commutator S (by omega) hK2 hp (hFE haF) (hFE hbF) ha hb haφ hbφ hab'
  have hKV : K ≤ V := hSch.trans hKEV
  have hKEK : ⁅K, E⁆ ≤ K := by
    have hEK := hJ.le_normalizer_ker S.data.normal
    rw [Subgroup.commutator_le]
    intro k hk e he
    have e' : ⁅k, e⁆ = k * (e * k⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e']
    exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hEK he) k⁻¹).mp (K.inv_mem hk))
  exact ⟨E, hJ.isBTBlock (by omega) S hKV (le_antisymm hKEK hSch), hJ.img_eq_alt⟩

@[expose] def SymCaseTwoFive : Prop := SymCaseTwoAt fun m => m = 2

theorem symCaseTwo_of_five (h5 : SymCaseTwoFive) : SymCaseTwo :=
  symCaseTwo_of_five_seven h5 symCaseTwo_seven

theorem threeEightSymmIH_of_five (h5 : SymCaseTwoFive) : ThreeEightSymmIH :=
  threeEightSymmIH_of_caseTwo (symCaseTwo_of_five h5)

end CFSG.CGT.PushingUpLit.SYMB
