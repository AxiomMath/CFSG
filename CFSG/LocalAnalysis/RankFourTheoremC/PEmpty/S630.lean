module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Inputs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wExists
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDerive
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wSylowX
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wBurnside
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wInvert
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wConjTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySylow
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankCover smallRankS smallRankR smallRankD
  smallRankF smallRankB smallRankCenter smallRankOmega Lemma628Concl Lemma629Concl Lemma630Concl
  Lemma630Iii SmallRankSBSylow KFactZAction629 sr629_ne_prime sr629_isElemAbelian_omega_center
  sr629_omega_center_ne_bot sr629_centralizer_le_normalizer_F sr629_F_le_fitting sr629_F_isPGroup
  sr629_omega_center_le sr629_mem_normalizer_smallRankCenter sr629_mem_normalizer_smallRankOmega
  sr628_centralizer_le_normalizer_zpowers sr628_card_sup_and_solvable
  sr628_exists_invariant_sylow sr628_exists_mem_normalizer_not_mem
  smallRankInvolutionRankLE_of_localRank sr630e_not_two_dvd_card_centralizer
  sr630e_zpowers_isSylowOf sr630e_normal_complement sr630e_orderOf_conj
  sr630c_mem_normalizer_centralizer sr630a_conj_eq_inv sr630a_isMulCommutative_of_conj_eq_inv
  sr630a_pRank_eq sr630a_not_dvd_index k631_tyg_dihedral k631_le_of_sylow_centralizer)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T : Subgroup G}

theorem s630_exists_sylow (c : S62Config p P M x z T) {f : ℕ} (hfp : f.Prime) (hf2 : f ≠ 2)
    (hfD : pCoreOf f (smallRankD p x) ≠ ⊥) (h28 : Lemma628Concl p M x z T)
    (h29 : Lemma629Concl p M x z T f) : ∃ E : Subgroup G, SmallRankSBSylow p f x z T E := by
  have hS := c.situation
  have hp : p.Prime := c.prime
  have hp2 : p ≠ 2 := c.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact f.Prime := ⟨hfp⟩
  have hfp' : f ≠ p := sr629_ne_prime hp hfp x hfD
  obtain ⟨hp35, -, -, hfit⟩ := h28
  obtain ⟨-, -, hlr3, hFe, hF4, -⟩ := h29
  have hFne : smallRankF p f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF p f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFM : smallRankF p f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hFD : smallRankF p f x ≤ smallRankD p x :=
    (sr629_omega_center_le f _).trans (CFSG.LieType.BorelTits.pCoreOf_le f _)
  have hDC : smallRankD p x ≤ centralizer ({x} : Set G) := sSup_le fun _ hK => hK.1
  have hxCF : x ∈ centralizer (smallRankF p f x : Set G) :=
    mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hDC (hFD ha))
  have hzx : z ∈ centralizer ({x} : Set G) := c.z_mem_centralizer
  have hCN : ∀ g ∈ centralizer ({x} : Set G),
      g ∈ normalizer (centralizer (smallRankF p f x : Set G) : Set G) := fun g hg =>
    sr630c_mem_normalizer_centralizer (sr629_centralizer_le_normalizer_F hp x hg)
  have hzCF : z ∉ centralizer (smallRankF p f x : Set G) := by
    intro hz
    apply hFne
    rw [eq_bot_iff, ← hFM]
    refine fun a ha => ⟨ha, c.centralizer_le_M ?_⟩
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz a ha)
  have hpl := plane_of_central hS c.point c.central
  have hrank : CFSG.Open.pRank p (centralizer ({x} : Set G)) ≤ 2 :=
    c.point.pRank_centralizer_le hS
  have hCx : ∀ E : Subgroup G, E ≤ centralizer ({x} : Set G) → IsElemAbelian p E →
      Nat.card E ≤ p ^ 2 := by
    intro E hE hEe
    have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk2 := CFSG.SectionRank.le_pRank hp.one_lt hE hEe hk
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hA3 : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3 := by
    obtain ⟨A, hAP, hAe, hAc⟩ := hS.exists_elemAbelian_cube
    exact ⟨A, hAP, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).1 hAe, hAc⟩
  have hsyl : IsSylowOf p (zpowers x) (centralizer (smallRankF p f x : Set G)) :=
    sr630e_zpowers_isSylowOf hp hp2 hpl c.central.centralizes (c.point.ne_one hp)
      c.point.pow_eq_one c.point.sylow hCx hA3 hxCF hzCF (hCN z hzx)
  have hodd := sr630e_not_two_dvd_card_centralizer hfp hFe hF4 hlr3
  obtain ⟨K, hKC, hcardC, hpK, hKchar⟩ :=
    sr630e_normal_complement hp hp35 (c.point.ne_one hp) c.point.pow_eq_one hsyl hodd
  have hKN : ∀ g ∈ normalizer (centralizer (smallRankF p f x : Set G) : Set G),
      g ∈ normalizer (K : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhC := hKC hh
      have hghC := (mem_normalizer_iff.mp hg h).mp hhC
      rw [hKchar _ hghC, sr630e_orderOf_conj]
      exact (hKchar h hhC).mp hh
    · intro hh
      have hghC := hKC hh
      have hhC := (mem_normalizer_iff.mp hg h).mpr hghC
      rw [hKchar h hhC]
      have h1 := (hKchar _ hghC).mp hh
      rwa [sr630e_orderOf_conj] at h1
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card hpl.card_eq
  obtain ⟨hAcard, hAsolv⟩ :=
    sr628_card_sup_and_solvable hp hp2 c.S_isPGroup hBp c.B_le_normalizer_S
  have hAC : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ centralizer ({x} : Set G) :=
    sup_le inf_le_right c.B_le_centralizer
  have hAK : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (K : Set G) := fun g hg =>
    hKN g (hCN g (hAC hg))
  have hKodd : Odd (Nat.card K) := by
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hodd ?_)
    rw [hcardC]
    exact h.mul_right p
  have hcop : Nat.Coprime (Nat.card ↥(smallRankS x T ⊔ (zpowers x ⊔ zpowers z)))
      (Nat.card K) := by
    rw [hAcard]
    obtain ⟨a, ha⟩ := c.S_isPGroup.exists_card_eq
    obtain ⟨b, hb⟩ := hBp.exists_card_eq
    rw [ha, hb]
    refine Nat.Coprime.mul_left ?_ ?_
    · exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hKodd)
    · exact Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK)
  have : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
  have : Group.IsSolvable ↥(smallRankS x T ⊔ (zpowers x ⊔ zpowers z)) := hAsolv
  obtain ⟨E, hEK, hEp, hEc, hEA⟩ := sr628_exists_invariant_sylow hAK hcop hfp
  have hv : (Nat.card (centralizer (smallRankF p f x : Set G))).factorization f =
      (Nat.card K).factorization f := by
    rw [hcardC, Nat.factorization_mul Nat.card_pos.ne' hp.ne_zero, Finsupp.add_apply,
      hp.factorization, Finsupp.single_apply, ite_eq_right (Ne.symm hfp'), add_zero]
  have hEsyl : IsSylowOf f E (centralizer (smallRankF p f x : Set G)) :=
    isSylowOf_of_card (hEK.trans hKC) (by rw [hEc, hv])
  exact ⟨E, hEK.trans hKC, hEp, (isSylowOf_iff.mp hEsyl).2.2, hEA⟩

theorem s630_evasion (h65 : S62Prop65) (c : S62Config p P M x z T)
    (hcov : SmallRankCover p M x) {f : ℕ} (hfp : f.Prime) (hf2 : f ≠ 2)
    (hfD : pCoreOf f (smallRankD p x) ≠ ⊥) (h28 : Lemma628Concl p M x z T)
    (h29 : Lemma629Concl p M x z T f) {E : Subgroup G} (hE : SmallRankSBSylow p f x z T E) :
    E ⊓ M = ⊥ := by
  have hp : p.Prime := c.prime
  have : Fact f.Prime := ⟨hfp⟩
  have hfp' : f ≠ p := sr629_ne_prime hp hfp x hfD
  obtain ⟨hp35, -, hQ8, hfit⟩ := h28
  have hp5 : p = 5 := hp35.resolve_left (by have := c.situation.p_ge; omega)
  obtain ⟨-, -, -, hFe, hF4, -⟩ := h29
  have hEp : IsPGroup f E := hE.2.1
  have hFne : smallRankF p f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF p f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFM : smallRankF p f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hFE : smallRankF p f x ≤ E :=
    k631_le_of_sylow_centralizer hfp (sr629_F_isPGroup hfp x) hFe.1 hE.1 hEp hE.2.2.1
  by_contra hne
  have hE₁p : IsPGroup f (E ⊓ M : Subgroup G) := hEp.to_le inf_le_left
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hE.2.2.2
  have hBE₁ : zpowers x ⊔ zpowers z ≤ normalizer ((E ⊓ M : Subgroup G) : Set G) :=
    fun b hb => inf_normalizer_le_normalizer_inf ⟨hBE hb, le_normalizer (c.B_le_M hb)⟩
  obtain ⟨k, hk⟩ := hE₁p.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card (E ⊓ M : Subgroup G)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp hfp).mpr hfp'.symm)
  have hodd : Odd (Nat.card (E ⊓ M : Subgroup G)) := by
    rw [hk]
    exact (hfp.eq_two_or_odd'.resolve_left hf2).pow
  have hN : normalizer ((E ⊓ M : Subgroup G) : Set G) ≤ M :=
    h65 G p P M x z c.situation c.point c.central c.prop614 T c.sylowTwo hcov hp5 (hQ8 hp5) _
      hne inf_le_right hBE₁ hcop hodd
  have hEM : E ≤ M := by
    by_contra hEM
    have hlt : E ⊓ M < E :=
      lt_of_le_of_ne inf_le_left fun heq => hEM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyE, hyN, hyY⟩ := sr628_exists_mem_normalizer_not_mem hEp hlt
    exact hyY ⟨hyE, hN hyN⟩
  exact hFne ((inf_eq_left.mpr (hFE.trans hEM)).symm.trans hFM)

theorem s630_concl_of_core (hK : KFactZAction629) (c : S62Config p P M x z T)
    {f : ℕ} (hfp : f.Prime) (hf2 : f ≠ 2) (hfD : pCoreOf f (smallRankD p x) ≠ ⊥)
    (h28 : Lemma628Concl p M x z T) (h29 : Lemma629Concl p M x z T f) {E : Subgroup G}
    (hE : SmallRankSBSylow p f x z T E) (hEM : E ⊓ M = ⊥) (hiii : Lemma630Iii p f x) :
    Lemma630Concl p x z T f := by
  have hS := c.situation
  have hp : p.Prime := c.prime
  have hp2 : p ≠ 2 := c.ne_two
  have : Fact f.Prime := ⟨hfp⟩
  have hfp' : f ≠ p := sr629_ne_prime hp hfp x hfD
  obtain ⟨hp35, hQ, hQ8, hfit⟩ := h28
  obtain ⟨⟨hi5, hi3, hcen⟩, -, hlr3, hFe, hF4, hFinv⟩ := h29
  have hp5 : p = 5 := hp35.resolve_left (by have := hS.p_ge; omega)
  have hEC : E ≤ centralizer (smallRankF p f x : Set G) := hE.1
  have hEp : IsPGroup f E := hE.2.1
  have hEs : ¬ f ∣ (E.subgroupOf (centralizer (smallRankF p f x : Set G))).index := hE.2.2.1
  have hSE : smallRankS x T ≤ normalizer (E : Set G) := le_sup_left.trans hE.2.2.2
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hE.2.2.2
  have hzE : zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hBE
  have hFne : smallRankF p f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF p f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFE : smallRankF p f x ≤ E :=
    k631_le_of_sylow_centralizer hfp (sr629_F_isPGroup hfp x) hFe.1 hEC hEp hEs
  have hFM : smallRankF p f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hzx : z ∈ centralizer ({x} : Set G) := c.z_mem_centralizer
  have hzF : z ∈ normalizer (smallRankF p f x : Set G) :=
    sr629_centralizer_le_normalizer_F hp x hzx
  have hzS : zpowers z ≤ normalizer (smallRankS x T : Set G) := c.z_le_normalizer_S
  have hSCF : smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) = ⊥ := by
    by_contra hne
    have hz0 : zpowers z ≤ normalizer
        ((smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) : Subgroup G) : Set G) := by
      rw [zpowers_le]
      exact inf_normalizer_le_normalizer_inf
        ⟨hzS (mem_zpowers z), sr630c_mem_normalizer_centralizer hzF⟩
    have hN := c.normalizer_le inf_le_left hne hz0
    have hFC : smallRankF p f x ≤ centralizer
        ((smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) : Subgroup G) : Set G) := by
      intro a ha
      rw [mem_centralizer_iff]
      intro s hs
      exact (mem_centralizer_iff.mp hs.2 a ha).symm
    refine hFne (eq_bot_iff.mpr ?_)
    calc smallRankF p f x ≤ smallRankF p f x ⊓ M :=
          le_inf le_rfl (hFC.trans ((Subgroup.centralizer_le_normalizer _).trans hN))
      _ = ⊥ := hFM
      _ ≤ ⊥ := le_rfl
  obtain ⟨-, y, -, -, -, hyZ, -, hy2, hy1, -, -⟩ : ∃ t y g : G,
      t ∈ smallRankS x T ∧ g ∈ smallRankS x T ∧ y ∈ smallRankCenter (smallRankS x T) ∧
      t ^ 2 = 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ t * y = y * t ∧ g * t * g⁻¹ = t * y := by
    obtain ⟨n, hn⟩ := hi5 hp5
    exact k631_tyg_dihedral hn
  have hyZ0 : y ∈ smallRankOmega 2 (smallRankCenter (smallRankS x T)) :=
    Subgroup.subset_closure ⟨hyZ, hy2⟩
  have hZ0S : smallRankOmega 2 (smallRankCenter (smallRankS x T)) ≤ smallRankS x T :=
    sr629_omega_center_le 2 _
  have hyS : y ∈ smallRankS x T := hZ0S hyZ0
  have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hy2)
  have hyinv : ∀ a ∈ smallRankF p f x, y * a * y⁻¹ = a⁻¹ :=
    hFinv y (by rw [hcen]; exact hyZ0) hy1
  have hZ0 : ∀ s ∈ smallRankOmega 2 (smallRankCenter (smallRankS x T)), s = 1 ∨ s = y := by
    intro s hs
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    right
    have hsinv := hFinv s (by rw [hcen]; exact hs) hs1
    have hsyC : s * y ∈ smallRankS x T ⊓ centralizer (smallRankF p f x : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (hZ0S hs) hyS, ?_⟩
      rw [mem_centralizer_iff]
      intro a ha
      have h3 : s * y * a * (s * y)⁻¹ = a := by
        calc s * y * a * (s * y)⁻¹ = s * (y * a * y⁻¹) * s⁻¹ := by group
          _ = s * a⁻¹ * s⁻¹ := by rw [hyinv a ha]
          _ = a⁻¹⁻¹ := hsinv a⁻¹ (inv_mem ha)
          _ = a := inv_inv a
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    rw [hSCF, Subgroup.mem_bot] at hsyC
    rw [eq_inv_of_mul_eq_one_left hsyC, hyy]
  have hZ0ne : smallRankOmega 2 (smallRankCenter (smallRankS x T)) ≠ ⊥ := by
    intro h
    rw [h] at hyZ0
    exact hy1 (Subgroup.mem_bot.mp hyZ0)
  have hzZ0 : zpowers z ≤
      normalizer (smallRankOmega 2 (smallRankCenter (smallRankS x T)) : Set G) := by
    rw [zpowers_le]
    exact sr629_mem_normalizer_smallRankOmega 2
      (sr629_mem_normalizer_smallRankCenter (hzS (mem_zpowers z)))
  have hNZ0 := c.normalizer_le hZ0S hZ0ne hzZ0
  have hCy : centralizer ({y} : Set G) ≤ M := by
    intro g hg
    refine hNZ0 (Subgroup.centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro s hs
    rcases hZ0 s hs with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (mem_centralizer_singleton_iff.mp hg).symm
  have hfix : ∀ e ∈ E, y * e = e * y → e = 1 := by
    intro e he hye
    have hem : e ∈ E ⊓ M := ⟨he, hCy (mem_centralizer_singleton_iff.mpr hye.symm)⟩
    rw [hEM] at hem
    exact Subgroup.mem_bot.mp hem
  have hEc : IsMulCommutative E :=
    sr630a_isMulCommutative_of_conj_eq_inv (sr630a_conj_eq_inv hy2 (hSE hyS) hfix)
  have hEcen : ∀ e ∈ E, e ∈ smallRankCenter E := by
    intro e he
    refine Subgroup.mem_inf.mpr ⟨he, ?_⟩
    rw [mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hEc.is_comm.comm ⟨h, hh⟩ ⟨e, he⟩)
  have hE₁e : IsElemAbelian f (smallRankOmega f (smallRankCenter E)) :=
    sr629_isElemAbelian_omega_center f E
  have hE₁E : smallRankOmega f (smallRankCenter E) ≤ E := sr629_omega_center_le f E
  have hall : ∀ e ∈ E, e ^ f = 1 → e ∈ smallRankOmega f (smallRankCenter E) :=
    fun e he hef => Subgroup.subset_closure ⟨hEcen e he, hef⟩
  have hFE₁ : smallRankF p f x ≤ smallRankOmega f (smallRankCenter E) :=
    fun a ha => hall a (hFE ha) (hFe.2 a ha)
  have hE₁ne : smallRankOmega f (smallRankCenter E) ≠ ⊥ := by
    intro h
    apply hFne
    rw [eq_bot_iff, ← h]
    exact hFE₁
  have hNE₁ : ∀ g ∈ normalizer (E : Set G),
      g ∈ normalizer (smallRankOmega f (smallRankCenter E) : Set G) := fun g hg =>
    sr629_mem_normalizer_smallRankOmega f (sr629_mem_normalizer_smallRankCenter hg)
  have hSzE₁ : smallRankS x T ⊔ zpowers z ≤
      normalizer (smallRankOmega f (smallRankCenter E) : Set G) :=
    sup_le (fun s hs => hNE₁ s (hSE hs)) (fun g hg => hNE₁ g (hzE hg))
  have hH2 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) →
      smallRankOmega f (smallRankCenter E) ⊓ centralizer (S₀ : Set G) = ⊥ := by
    intro S₀ hS₀S hS₀1 hzS₀
    rw [eq_bot_iff, ← hEM]
    exact inf_le_inf hE₁E ((Subgroup.centralizer_le_normalizer _).trans
      (c.normalizer_le hS₀S hS₀1 hzS₀))
  have hH3 : smallRankOmega f (smallRankCenter E) ⊓ centralizer ({z} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hEM]
    exact inf_le_inf hE₁E c.centralizer_le_M
  obtain ⟨⟨hcard, -⟩, -, -⟩ :=
    hK G p f hp hfp hp2 hf2 hfp' hp35 (smallRankS x T) (smallRankOmega f (smallRankCenter E)) z
      c.S_isPGroup hE₁e hE₁ne c.central.pow_eq_one c.central.ne_one hzS hSzE₁ hQ hQ8 hH2 hH3
      (smallRankInvolutionRankLE_of_localRank hfp _ _ hlr3)
      (fun hp3 => absurd hp3 (by have := hS.p_ge; omega))
      (fun ⟨hp3, _⟩ => absurd hp3 (by have := hS.p_ge; omega))
  have hE₁F : smallRankOmega f (smallRankCenter E) = smallRankF p f x :=
    (Subgroup.eq_of_le_of_card_ge hFE₁ (by rw [hcard, hF4])).symm
  have hFall : ∀ e ∈ E, e ^ f = 1 → e ∈ smallRankF p f x := fun e he hef =>
    hE₁F ▸ hall e he hef
  exact ⟨⟨E, hEC, hEp, hEs, hE.2.2.2, hEc, sr630a_pRank_eq hfp hFE hFe hF4 hFall,
    sr630a_not_dvd_index hfp hf2 hFE hFne hFe.2 hFall hEp hEC hEs hiii⟩, hiii⟩

theorem stepL630_of_inputs (hK : KFactZAction629) (h65 : S62Prop65) (hiii : S62L630Iii) :
    StepL630 := by
  intro G _ _ p P M x z hS hx hz h614 T hT hcov h28 f hfp hf2 hfD h29
  have c : S62Config p P M x z T := ⟨hS, hx, hz, h614, hT⟩
  obtain ⟨E, hE⟩ := s630_exists_sylow c hfp hf2 hfD h28 h29
  exact s630_concl_of_core hK c hfp hf2 hfD h28 h29 hE
    (s630_evasion h65 c hcov hfp hf2 hfD h28 h29 hE)
    (hiii G p P M x z hS hx hz h614 T hT hcov h28 f hfp hf2 hfD h29)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
