module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoA5Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoAltTen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoThreeSporBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem inf_isElemAbelian_of_altTen {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (e : K ≃* alternatingGroup (Fin 10)) (R : Sylow 5 Y) (T : Sylow 5 K)
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup Y) ⊓ K) :
    IsElemAbelian 5 ((R : Subgroup Y) ⊓ K) ∧
      Nat.card ((R : Subgroup Y) ⊓ K : Subgroup Y) = 5 ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ψ, hψ⟩ := Generic41Spor.A10Perm.exists_iso_sylow e T
  have hS : ∀ x ∈ (T : Subgroup K), x ^ 5 = 1 ∧ ∀ y ∈ (T : Subgroup K), x * y = y * x := by
    intro x hx
    obtain ⟨i, j, hij⟩ := Generic41Spor.A10Perm.mem_S₀.mp ((hψ x).mp hx)
    refine ⟨ψ.injective ?_, fun y hy => ψ.injective ?_⟩
    · rw [map_pow, hij, map_one, (Generic41Spor.A10Perm.a₁₂_commute.pow_pow i j).mul_pow,
        ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul,
        Generic41Spor.A10Perm.a₁_pow, Generic41Spor.A10Perm.a₂_pow, one_pow, one_pow, one_mul]
    · obtain ⟨k, l, hkl⟩ := Generic41Spor.A10Perm.mem_S₀.mp ((hψ y).mp hy)
      rw [map_mul, map_mul, hij, hkl, Generic41Spor.A10Perm.mul_aux,
        Generic41Spor.A10Perm.mul_aux, add_comm i, add_comm j]
  rw [← hT]
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := mem_map.mp b.2
    change (a : Y) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, (hS x hx).2 y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, (hS x hx).1, map_one]
  · rw [card_map_of_injective K.subtype_injective, T.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
    exact congrArg (5 ^ ·) Generic41Spor.A10Perm.factorization_A10

private theorem threeFourTwoAt_alternatingGroup_ten :
    ThreeFourTwoAt 5 (alternatingGroup (Fin 10)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hX : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
  haveI := hX
  have hcard : Nat.card (alternatingGroup (Fin 10)) = 1814400 := Generic41Spor.A10Perm.card_A10
  have hnab : ∃ a b : alternatingGroup (Fin 10), a * b ≠ b * a :=
    exists_mul_ne_of_sq_dvd_card Nat.prime_five (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
  have hout2 : Nat.card (Outer (alternatingGroup (Fin 10))) ∣ 2 :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_outside_six
      (Or.inr (by norm_num))
  refine threeFourTwoAt_of_forall_model hX hnab
    (CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_solvable_outside_six
      (Or.inr (by norm_num))) ?_
  intro Y _ _ K Y₀ E R _ _ hKn e _ _ _ hER hE hEc hcore _ hKY J hJ hne hJp _ hQ
  haveI := hKn
  have hZK : K ⊓ centralizer (K : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxC⟩
    have h : e ⟨x, hxK⟩ ∈ center (alternatingGroup (Fin 10)) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (mem_centralizer_iff.mp hxC k k.2))
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ hnab, mem_bot,
      MulEquiv.map_eq_one_iff] at h
    exact mem_bot.mpr (congrArg Subtype.val h)
  have hout5 : ¬ 5 ∣ Nat.card (Outer K) := fun h5 => by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv] at h5
    have := Nat.le_of_dvd (by norm_num) (h5.trans hout2)
    omega
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hTe, hTc⟩ := inf_isElemAbelian_of_altTen e R T hT
  have hN : normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ Y₀ :=
    normalizer_inf_le_of_isElemAbelian R hER hE hEc hcore hZK hout5 hTe
      (CFSG.SectionRank.le_pRank Nat.prime_five.one_lt le_rfl hTe hTc)
  have hNT : normalizer ((T : Subgroup K) : Set K) ≤ Y₀.subgroupOf K := fun k hk => by
    refine mem_subgroupOf.mpr (hN ?_)
    have h := le_normalizer_map K.subtype (mem_map_of_mem K.subtype hk)
    rwa [hT] at h
  set S : Sylow 5 (alternatingGroup (Fin 10)) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hNS : normalizer ((S : Subgroup (alternatingGroup (Fin 10))) :
      Set (alternatingGroup (Fin 10))) ≤ (Y₀.subgroupOf K).map e.toMonoidHom := by
    rw [show (S : Subgroup (alternatingGroup (Fin 10))) = (T : Subgroup K).map e.toMonoidHom
      from rfl, ← map_equiv_normalizer_eq]
    exact map_mono hNT
  have hK₁ : (Y₀.subgroupOf K).map e.toMonoidHom ≠ ⊤ := fun htop => hKY fun k hk => by
    have h := congrArg (Subgroup.comap e.toMonoidHom) htop
    rw [comap_map_eq_self_of_injective e.injective, comap_top] at h
    exact mem_subgroupOf.mp (h ▸ mem_top (⟨k, hk⟩ : K))
  obtain ⟨Q, _, f, hf, hfk, hQq⟩ := hQ
  have hJc : commutator J = ⊤ := (Subgroup.isPerfect_iff.mpr hJp).commutator_eq_top
  obtain ⟨φ⟩ := TenFourteenTwo.nonempty_mulEquiv_alt5_of_altTen (MulEquiv.refl _) S hNS hK₁ hJ
    hJp hne (TenFourteenTwo.joinIrreducible_of_isQuasisimple hJc f hf hQq hfk)
  have h10 : 5 ≤ 10 := by norm_num
  have h5 : 5 ≤ 5 := le_rfl
  exact ⟨.alternating 10 h10, .alternating 5 h5,
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, h10, h5, rfl, rfl⟩, ⟨e⟩, φ.toMonoidHom,
    φ.surjective⟩

theorem threeFourTwoAltTen_holds : ThreeFourTwoAltTen := fun _ =>
  threeFourTwoAt_alternatingGroup_ten

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
