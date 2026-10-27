module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin8

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.StandardType CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint CFSG.Open
  CFSG.ComponentClassification.CatLeafProof
open scoped Pointwise

section Layer


theorem concl165_of_e8FourData {F : Type} [Field F] [Finite F] [CharP F 2] {n p q : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 4)
    (hq : q.Prime) (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    {lam : ZMod p} (hlam : lam * lam = -1)
    {ζ : (AlgebraicClosure F)ˣ} (hζo : orderOf ζ = p)
    {g : ModGL Tag.E8 (AlgebraicClosure F)}
    (hgM : g ∈ torusGroup .E8 (AlgebraicClosure F) ⊔
      rootSpan .E8 (AlgebraicClosure F) (kernelRoots d4d4Char))
    (hgN : g ∈ Subgroup.normalizer
      (rootSpan .E8 (AlgebraicClosure F) e8D4PerpRoots :
        Set (ModGL .E8 (AlgebraicClosure F))))
    {A₀ : Subgroup (adjointGroup .E8 F)} (hA₀e : IsElemAbelian p A₀)
    {x z : adjointGroup .E8 F} (hx : x ∈ A₀) (hz : z ∈ A₀) (hx1 : x ≠ 1)
    (hzx : z ∉ Subgroup.zpowers x) (hxL : x ∈ e8D4Levi F) (hzL : z ∈ e8D4Levi F)
    (hxdiag : adjEmb .E8 F (AlgebraicClosure F) x =
      g * rootDiagUnit .E8 (d6TorsionChar p ζ lam) * g⁻¹)
    (hzdiag : adjEmb .E8 F (AlgebraicClosure F) z =
      g * rootDiagUnit .E8 (d6zTorsionChar p ζ lam) * g⁻¹) :
    Concl165 (adjointGroup .E8 F) p q A₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card F ^ 2 + 1 := dvd_card_sq_add_one_of_rk2Ord_four hcard hp hrk
  have hqK : q ∣ Nat.card F - 1 ∨ Nat.card F = 2 ∧ q = 3 := by
    rcases hqdiv with h | ⟨hn1, hq3⟩
    · left
      rwa [hcard]
    · right
      refine ⟨?_, hq3⟩
      rw [hcard, hn1]
      norm_num
  have hb : rootCharKernel (d6zTorsionChar p ζ lam) = d6zRoots :=
    rootCharKernel_eq_d6zRoots_of_rootChar hp hp2 hζo hlam
      (rootChar_d6zTorsionChar p ζ lam) d6z_pair_bound
  have hxC : Subgroup.centralizer ({x} : Set (adjointGroup .E8 F)) ≤ ⨆ k, e8D8Chain F k :=
    centralizer_le_d8Chain_of_adjEmb_eq hp hp2 hζo hlam hgM hxdiag
  have hord : orderOf (e8D8Theta F ⟨x, e8D4Levi_le_e8D8Chain F hxL⟩) = p := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA₀e.2 x hx) hx1
  obtain ⟨J, hQJ, hJx, hJn, hJq, hpJ⟩ :=
    exists_layer_normal_centralizer (K := F) hp hp2 hxL hxC hord hpq
  have hQz : e8D4Perp F ≤ Subgroup.centralizer ({z} : Set (adjointGroup .E8 F)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1
      (e8D4Perp_le_centralizer_e8D4Levi F hy) z hzL).symm
  have hQn : ((e8D4Perp F).subgroupOf
      (J ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E8 F)))).Normal :=
    e8D4Perp_normal_in_inf_centralizer (K := F) (L := AlgebraicClosure F) hp hp2 hζo hlam
      hgM hgN hxdiag hzdiag hb hJx hQJ hzL
  have hQq : CFSG.Open.IsQuasisimple ↥(e8D4Perp F) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).mp (isQuasisimple_e8D4Perp F)
  have hpQ : p ∣ Nat.card (e8D4Perp F) := dvd_card_e8D4Perp F hp hpq
  obtain ⟨Fq, hFqQ, hFqe, -, hFq3⟩ := exists_elemAbelian_e8D4Perp F hq hqK
  have hFqJ : Fq ≤ J := hFqQ.trans hQJ
  have hFx : Fq ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E8 F)) :=
    hFqJ.trans hJx
  have hFJ : Fq ≤ Subgroup.normalizer (J : Set (adjointGroup .E8 F)) :=
    hFqJ.trans Subgroup.le_normalizer
  exact concl165_of_layers hp hA₀e hx hz hx1 hzx hJx hJn hJq hpJ hQJ hQz hQn hQq hpQ
    hFqe hFx hFJ hFq3

end Layer

section Assembly


theorem exists_conj_map_eq_e8Four {F : Type} [Field F] [Finite F] (n p : ℕ)
    (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 4)
    {Ã A₀ : Subgroup (adjointGroup .E8 F)} (hÃe : IsElemAbelian p Ã)
    (hA₀e : IsElemAbelian p A₀)
    (hÃmax : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E8 F)) ≤ CFSG.Open.pRank p Ã)
    (hA₀card : Nat.card A₀ = p ^ 4) :
    ∃ c : adjointGroup .E8 F, Ã.map (MulAut.conj c).toMonoidHom = A₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card F ^ 2 + 1 := dvd_card_sq_add_one_of_rk2Ord_four hcard hp hrk
  have h4Ã : 4 ≤ CFSG.Open.pRank p Ã :=
    (four_le_pRank_adjoint_e8 F hp (orderOf_card_eq_four hcard hrk)).trans hÃmax
  by_cases h5 : p = 5
  · subst h5
    have h5dvd : 5 ∣ Nat.card F * Nat.card F + 1 := by
      rw [← pow_two]
      exact hpq
    have h54Ã : 5 ^ 4 ≤ Nat.card Ã := by
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hÃe]
      exact Nat.pow_le_pow_right (by norm_num) h4Ã
    have h54A : 5 ^ 4 ≤ Nat.card A₀ := by
      rw [hA₀card]
    exact CFSG.StandardType.NoOffE8Five.exists_conj_map_eq_E8_five h5dvd hÃe hA₀e h54Ã h54A
  · have hp5 : 5 ≤ p := five_le_of_rk2Ord_four hp hp2 hrk
    have h7 : 7 ≤ p := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      omega
    have hpqF : ¬ p ∣ Nat.card F := by
      intro hd
      have h1 : p ∣ Nat.card F ^ 2 := by
        rw [pow_two]
        exact dvd_mul_of_dvd_left hd _
      exact hp.not_dvd_one ((Nat.dvd_add_right h1).mp hpq)
    have hpr : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E8 F)) = 4 :=
      pRank_adjoint_e8_four F hp h7 hpqF (orderOf_card_eq_four hcard hrk)
    have hle : CFSG.Open.pRank p Ã ≤ 4 :=
      hpr ▸ CFSG.SectionRank.pRank_mono hp.one_lt (le_top : Ã ≤ ⊤)
    have hÃcard : Nat.card Ã = p ^ 4 := by
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hÃe]
      congr 1
      omega
    exact CFSG.HardMathSupport.Lang.AnisoE6.exists_conj_eq_of_sylowTorus
      (CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E8_four F hp h7 hpqF
        (Or.inr (Or.inl (orderOf_card_eq_four hcard hrk))))
      hÃe hÃcard hA₀e hA₀card

theorem e8Model165At_four : E8Model165At 4 := by
  intro F hField hFinite hChar n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  intro Ã hÃe hΩ hÃmax hÃ3
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨lam, hlam, ζ, hζo, g, hgM, hgN, A₀, hA₀e, hA₀card, x, z, hx, hz, hx1, hzx,
    hxL, hzL, hxdiag, hzdiag⟩ := exists_e8FourPointData F hcard hn hp hp2 hrk
  have hconcl : Concl165 (adjointGroup .E8 F) p q A₀ :=
    concl165_of_e8FourData hcard hp hp2 hrk hq hqdiv hlam hζo hgM hgN hA₀e hx hz hx1 hzx
      hxL hzL hxdiag hzdiag
  obtain ⟨c, hc⟩ := exists_conj_map_eq_e8Four n p hcard hp hp2 hrk hÃe hA₀e hÃmax hA₀card
  exact concl165_of_conj hp hq c (by rw [hc]; exact hconcl)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
