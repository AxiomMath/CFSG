module

public import CFSG.Quasithin.EmptyFaithful.Der6EMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Ch1
open scoped commutatorElement Pointwise

theorem stageLemma15224_of_F4 (hlist : Lemma115_3_List)
    (hA3 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], A3Orbits G)
    (h15208 : StageLemma15208_F4) (h15214 : StageLemma15214_F4) (h15216 : StageLemma15216_F4)
    (h15218 : StageLemma15218_F4) (h15220 : StageLemma15220_F4) (insp : Insp15224) :
    StageLemma15224_F4 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hImin L hL hLnot hLie
  classical
  have hI := hImin.1
  have c14 := h15214 G T Mc M hs B₀ hB₀
  have c16 := h15216 G T Mc M hs H hH B₀ hB₀ I hI
  have c18 := h15218 G T Mc M hs H hH B₀ hB₀ I hI
  have c20 := h15220 G T Mc M hs H hH B₀ hB₀ I hI
  set S := sOf152 T Mc M B₀ with hS
  set Zs := zSOf T Mc M B₀ with hZs
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hSsyl : IsSylowTwoOf S I := c18.sylow
  have hST : S ≤ T := inf_le_left

  have hZcard : 2 ≤ Nat.card (quasithinOmegaOneCenter T) := by
    rcases c14.cases with ⟨-, hZeq, hcard, -⟩ | ⟨-, hZc, -⟩
    · rw [hZeq, hcard]; norm_num
    · rw [hZc]
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨z', hz'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  set z : G := (z' : G) with hzdef
  have hzZ : z ∈ quasithinOmegaOneCenter T := z'.2
  have hz1 : z ≠ 1 := fun h => hz'1 (Subtype.ext h)
  obtain ⟨hzT, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hzZ
  have hZsT : Zs ≤ T := (zSOf_le_V154 T Mc M B₀).trans (S152N.V154_le_T hs)
  have hzS : z ∈ S := ⟨hzT, fun x hx => Subgroup.mem_centralizer_iff.mp hzC x (hZsT hx)⟩
  have hzCS : z ∈ Subgroup.centralizer (S : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hzC x (hST hx)

  have hyp := c20.hyp115 z hzZ hz1
  have hMcz : Mc ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [c14.mc_eq]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ)
  have hMi : Mc ⊓ I = I ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine le_antisymm (fun x hx => ⟨hx.2, hMcz hx.1⟩) (fun x hx => ⟨hyp.centralizer_z_le hx.2, hx.1⟩)
  have hMiI : Mc ⊓ I ≠ I := fun h => hI.not_le (h ▸ inf_le_left)
  have hO2I : pCoreOf 2 I ≠ ⊥ := hI.inH.2
  have hSQ : SQTKGroup ↥I :=
    sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hO2I

  have hSMi : S ≤ Mc ⊓ I := le_inf (hST.trans hTMc) hSsyl.1
  have hmax : ∀ J : Subgroup G, Mc ⊓ I ≤ J → J ≤ I → J = Mc ⊓ I ∨ J = I := by
    intro J hMJ hJI
    by_contra hcon
    push Not at hcon
    have hJMc : ¬ J ≤ Mc := fun h => hcon.1 (le_antisymm (le_inf h hJI) hMJ)
    have hZsC : Subgroup.centralizer (Zs : Set G) ≤ J :=
      (c16.centralizer_eq.le.trans c16.centralizer_le).trans hMJ
    have hO2 : pCoreOf 2 J ≠ ⊥ := by
      intro hbot
      have hle : pCoreOf 2 I ≤ pCoreOf 2 J :=
        le_pCoreOf_of_le_normalizer (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSsyl |>.trans
          (hSMi.trans hMJ)) (hJI.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
      exact hO2I (le_bot_iff.mp (hbot ▸ hle))
    exact hcon.2 (hImin.2 J ⟨hZsC, hO2⟩ hJMc hJI)

  have hLMi : ¬ L ≤ Mc ⊓ I := fun h => hLnot fun x hx => (h hx).1
  have := hs.qtfe.simple
  have hqtke : QTKECore G := qtkeCore_of_cat hs.qtfe.nonabelian hs.qtfe.qtke
  obtain ⟨hzN, hcomm, -, hcases⟩ :=
    Lemma115_3_List.component_cases hlist hs.qtfe.simple hs.qtfe.nonabelian hqtke hyp hL
  have hLcomp : L ∈ cComp I := Id2519.mem_cComp_of_isComponentIn hL
  obtain ⟨horb, -⟩ := hA3 G I S L hSQ hSsyl hLcomp
  have hL0I : conjClosure L S ≤ I := conjClosure_le fun s hs l hl =>
    I.mul_mem (I.mul_mem (hSsyl.1 hs) (le_of_mem_cComp hLcomp hl)) (I.inv_mem (hSsyl.1 hs))
  have hL0N : I ≤ Subgroup.normalizer (conjClosure L S : Set G) := by
    have key : ∀ g ∈ I, conjClosure L S ≤ (conjClosure L S).comap (MulAut.conj g).toMonoidHom := by
      intro g hg
      refine conjClosure_le fun s hs l hl => ?_
      have hmem : conjByElt (g * s) L ∈ conjSubgroupsBy I L := ⟨g * s, I.mul_mem hg (hSsyl.1 hs), rfl⟩
      rw [horb] at hmem
      obtain ⟨s', hs', hs'eq⟩ := hmem
      have hx : (g * s) * l * (g * s)⁻¹ ∈ conjByElt (g * s) L := ⟨l, hl, rfl⟩
      rw [hs'eq] at hx
      obtain ⟨l', hl', hl'eq⟩ := hx
      have e : g * (s * l * s⁻¹) * g⁻¹ = s' * l' * s'⁻¹ := by
        have h1 : (MulAut.conj s') l' = (g * s) * l * (g * s)⁻¹ := hl'eq
        simp only [MulAut.conj_apply] at h1
        rw [h1]
        group
      show (MulAut.conj g) (s * l * s⁻¹) ∈ conjClosure L S
      simp only [MulAut.conj_apply]
      rw [e]
      exact mem_conjClosure hs' hl'
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg hx, fun hx => ?_⟩
    have h1 := key g⁻¹ (I.inv_mem hg) hx
    simpa [MulAut.conj_apply, mul_assoc] using h1
  have hL0n : ((conjClosure L S).subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL0I).mpr hL0N
  have hIeq : I = conjClosure L S ⊔ (Mc ⊓ I) := by
    rcases hmax (conjClosure L S ⊔ (Mc ⊓ I)) le_sup_right (sup_le hL0I inf_le_right) with h | h
    · exact absurd ((le_conjClosure L S).trans (le_sup_left.trans h.le) |>.trans inf_le_left) hLnot
    · exact h.symm

  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hsylH : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hX : IsXi T (oTwoUpper H) := Der6D.xi_of_iso hsylH hH.1.2 φ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hi : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 :=
    C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hi]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ oTwoUpper H) IsPGroup.of_bot
  have hPc : Nat.card P = 9 := by rw [hX.card_sylow (by norm_num) h3 hP, hi]
  exact insp G I S (Mc ⊓ I) L (conjClosure L S) P z hSQ c20.oddCore hSsyl hzS hzCS hz2
    hz1 hMi hMiI hmax hL hLMi hcomm hcases hLie rfl hL0n hIeq
    (hP.le.trans (le_sup_left.trans c16.KS_le)) hP.isPGroup hPc
    (fun x hx => hX.pow_eq_one (by norm_num) h3 hP hx)

end CFSG.Quasithin
