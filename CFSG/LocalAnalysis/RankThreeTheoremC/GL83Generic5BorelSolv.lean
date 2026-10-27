module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section Borel

variable {p : ℕ} [Fact p.Prime] {L U : Subgroup G}

theorem inf_le_normalizer_of_mulEquiv_psl2GF {n : ℕ} (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (e : L ≃* PSL(2, GaloisField p n)) (hU : IsSylowOf p U L) {M : Subgroup G}
    (hN : normalizer (U : Set G) ≤ M) (hLM : ¬ L ≤ M) :
    M ⊓ L ≤ normalizer (U : Set G) := by
  obtain ⟨T, hT⟩ := hU
  have hes : Function.Surjective (e : L →* PSL(2, GaloisField p n)) := e.surjective
  have hB : IsCoatom (normalizer ((T : Subgroup L) : Set L)) := by
    have h := psl2GF_borelCoatom p n hp2 hn (T.mapSurjective hes)
    rw [Sylow.coe_mapSurjective, ← MulEquiv.toMonoidHom_eq_coe,
      ← Subgroup.map_equiv_normalizer_eq] at h
    exact (OrderIso.isCoatom_iff e.mapSubgroup _).mp h
  have hmap : ∀ k ∈ normalizer ((T : Subgroup L) : Set L), (k : G) ∈ normalizer (U : Set G) := by
    intro k hk
    rw [← hT]
    exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hk)
  have hNL : normalizer ((T : Subgroup L) : Set L) ≤ M.subgroupOf L :=
    fun k hk => Subgroup.mem_subgroupOf.mpr (hN (hmap k hk))
  have heq : M.subgroupOf L = normalizer ((T : Subgroup L) : Set L) :=
    (hB.le_iff.mp hNL).resolve_left fun h => hLM (Subgroup.subgroupOf_eq_top.mp h)
  rintro y ⟨hyM, hyL⟩
  exact hmap ⟨y, hyL⟩ (heq ▸ Subgroup.mem_subgroupOf.mpr hyM)

theorem inf_normalizer_le_normalizer_of_isSylowOf (hU : IsSylowOf p U L) {M : Subgroup G}
    (hUM : U ≤ M) (hML : M ⊓ L ≤ normalizer (U : Set G)) :
    M ⊓ normalizer (L : Set G) ≤ normalizer (U : Set G) := by
  have hconj : ∀ h ∈ M ⊓ normalizer (L : Set G), ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    have hVL : U.map (MulAut.conj h).toMonoidHom ≤ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact (mem_normalizer_iff.mp hh.2 v).mp (hU.le hv)
    have hVN : U.map (MulAut.conj h).toMonoidHom ≤ normalizer (U : Set G) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hML ⟨M.mul_mem (M.mul_mem hh.1 (hUM hv)) (M.inv_mem hh.1), hVL ⟨v, hv, rfl⟩⟩
    have heq := hU.eq_of_le le_sup_right (sup_le hVL hU.le)
      ((hU.isPGroup.map _).to_sup_of_normal_right' hU.isPGroup hVN)
    exact (le_sup_left.trans heq.le) ⟨u, hu, rfl⟩
  intro h hh
  rw [mem_normalizer_iff]
  refine fun u => ⟨hconj h hh u, fun hu => ?_⟩
  have h' := hconj h⁻¹ (inv_mem hh) _ hu
  rwa [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group] at h'

theorem isSolvable_of_le_normalizer_of_mulEquiv_psl2GF {n : ℕ} (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (e : L ≃* PSL(2, GaloisField p n)) (hU : IsSylowOf p U L) {H : Subgroup G}
    (hHL : H ≤ normalizer (L : Set G)) (hHU : H ≤ normalizer (U : Set G))
    [Group.IsSolvable (centralizer (L : Set G))] : Group.IsSolvable H := by
  let ρ : H →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hHL)
  have hρ : ∀ (h : H) (k : L), ((ρ h k : L) : G) = (h : G) * k * (h : G)⁻¹ := fun _ _ => rfl
  have hker : ∀ h : ρ.ker, ((h : H) : G) ∈ centralizer (L : Set G) := by
    intro h
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut L => ((φ ⟨k, hk⟩ : L) : G)) (MonoidHom.mem_ker.mp h.2)
    simp only [hρ, MulAut.one_apply] at h1
    calc k * ((h : H) : G) = ((h : H) : G) * k * ((h : H) : G)⁻¹ * ((h : H) : G) := by rw [h1]
      _ = ((h : H) : G) * k := by group
  let κ : ρ.ker →* centralizer (L : Set G) :=
    (H.subtype.comp ρ.ker.subtype).codRestrict _ hker
  have hκ : Function.Injective κ := fun a b hab => by
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have : Group.IsSolvable ρ.ker := Group.isSolvable_of_isSolvable_injective hκ
  obtain ⟨T, hT⟩ := hU
  have hmemT : ∀ k : L, k ∈ (T : Subgroup L) ↔ (k : G) ∈ U := fun k => by
    rw [← hT]
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  have hes : Function.Surjective (e : L →* PSL(2, GaloisField p n)) := e.surjective
  set T' : Sylow p (PSL2GF p n) := T.mapSurjective hes with hT'
  have hT'mem : ∀ k : L, e k ∈ (T' : Subgroup (PSL2GF p n)) ↔ k ∈ (T : Subgroup L) :=
    fun k => by
      rw [hT', Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_iff_mem (f := (e : L →* PSL(2, GaloisField p n))) e.injective
  let F : MulAut L →* MulAut (PSL2GF p n) := (MulAut.congr e).toMonoidHom
  have hF : Function.Injective F := (MulAut.congr e).injective
  have hFe : ∀ (α : MulAut L) (k : L), F α (e k) = e (α k) := fun α k => by
    simp [F, MulAut.congr]
  have hA : ∀ β ∈ ρ.range.map F,
      (T' : Subgroup (PSL2GF p n)).map (β : PSL2GF p n ≃* PSL2GF p n).toMonoidHom = T' := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) (by
      rw [Subgroup.card_map_of_injective
        (f := ((F (ρ h) : PSL2GF p n ≃* PSL2GF p n)).toMonoidHom) (F (ρ h)).injective])
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, rfl⟩ := e.surjective y
    rw [hT'mem, hmemT] at hy
    change F (ρ h) (e k) ∈ (T' : Subgroup (PSL2GF p n))
    rw [hFe, hT'mem, hmemT, hρ]
    exact (mem_normalizer_iff.mp (hHU h.2) k).mp hy
  have := kFactL2SylowNormalizerSolvable p n hp2 hn T' (ρ.range.map F) hA
  have : Group.IsSolvable ρ.range := Group.isSolvable_of_isSolvable_injective
    (f := (ρ.range.equivMapOfInjective F hF).toMonoidHom)
    (ρ.range.equivMapOfInjective F hF).injective
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

end Borel

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_solvable_inf_normalizer (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    Group.IsSolvable ↥(M ⊓ normalizer ((gen5L x : Subgroup G) : Set G)) := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  have hp2 : p ≠ 2 := by have := gen5_five_le hG hl; omega
  have hU := gen5_sylow hG hl
  have hU1 : gen5U (P : Subgroup G) x ≠ ⊥ := by
    intro h
    have hc := (gen5_U_elemAbelian hG hl).2
    rw [h, card_bot] at hc
    have := (gen5_prime hl).one_lt
    nlinarith
  have hNU := gen5_normalizer_le hG hl le_rfl hU1
  have hML := inf_le_normalizer_of_mulEquiv_psl2GF hp2 (by norm_num) e hU hNU (gen5_not_le hG hl)
  have : Group.IsSolvable (centralizer ((gen5L x : Subgroup G) : Set G)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (gen5_Z hG hl).2.1))
  exact isSolvable_of_le_normalizer_of_mulEquiv_psl2GF hp2 (by norm_num) e hU inf_le_right
    (inf_normalizer_le_normalizer_of_isSylowOf hU (le_normalizer.trans hNU) hML)

end CFSG.LocalAnalysis.RankThreeTheoremC
