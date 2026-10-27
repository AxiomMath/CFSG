module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerStrict
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K57Assembly
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepOffenderJ

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement

theorem K541CountEven_holds : K541CountEven := by
  intro X _ _ T hGN Ls hL hJ n hn hEven hLiso P₀ P₁ P₂ P₃ h01 h12 h23 h3V hn0 hn1 hn2 hn3
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  have hn2' : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hEven
    omega
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hGN
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  obtain ⟨A, hA2, hAb, hAN, hLA, hAJ⟩ := exists_rep_offender_J hGN hV hL hJ
  have hinj := gnRep_injective hV
  have hfaith : ∀ a ∈ A, (∀ v, gnRep hV a v = v) → a = 1 := fun a _ h =>
    hinj (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn (gnRep hV) A ⊤ := (isBestOffender_iff_on _ A hfaith).mp ⟨hA2, hAb⟩
  have hKnt : ¬ Ls ≤ cenOn (gnRep hV) Ls ⊤ := by
    intro hle
    apply ne_bot_of_isComponentOf hL
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    apply hinj
    rw [map_one]
    exact LinearMap.ext fun v => (mem_cenOn.mp (hle hl)).2 v Submodule.mem_top
  obtain ⟨B, hBA, hinvB, hLnt, hBnt, hbestB, hquadB, hmove, -⟩ :=
    exists_strictMin_moving Ls A hA2 hAN hLA hKnt hb
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) b (hBA hb)
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc => by
    have := hA2.toIsMulCommutative.is_comm.comm ⟨b, hBA hb⟩ ⟨c, hBA hc⟩
    exact congrArg Subtype.val this
  obtain ⟨e⟩ := hLiso
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hBN : ∀ b ∈ B, ∀ l ∈ Ls, b * l * b⁻¹ ∈ Ls := fun b hb l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAN (hBA hb)) l).mp hl
  have hinn : ∀ b ∈ B, ∃ l ∈ Ls, ConjAgree Ls b l :=
    strictMin_inner (gnRep hV) Ls B hn2' hF e hL.2.2 hBN hB2 hBc hinvB hLnt hbestB hquadB hmove
  have hup := nontrivCount_le_two (gnRep hV) Ls B hn2' hF e hL.2.2.1 hL.2.2.2 hB2 hBc hinn le_rfl
    hinvB hbestB hmove hBnt
  have hlow := three_le_nontrivCount_chain hV hL.2.2.1 h01.le h12.le h23.le h3V hn0 hn1 hn2 hn3
    c1 c2 c3
  omega

theorem K57_holds : K57 :=
  K57_of_count K541CountEven_holds

end CFSG.LocalAnalysis.RankThreeUC.S15
