module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnRed
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
  (SU4 μ3 fieldFactor4 equivSU4 mem_range_conj_of_fieldFactor4_eq_one exists_isPrimitiveRoot_three)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48 CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)
open CFSG.ClassicalInvolution.Phan (Su blockEmb blockEmb_injective)

namespace U4InnU48

theorem perfect_le_W0_c211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (L : Subgroup SU4)
    (hLC : L ≤ Subgroup.centralizer ({c211 ζ hζ} : Set SU4)) (hL : Group.IsPerfect ↥L) :
    L ≤ W0 := by
  obtain ⟨hk2, hk3⟩ := c211_eig_ne ζ hζ
  have hd := mat_c211 ζ hζ
  have hperf := subgroupOf_perfect hLC hL
  have hk2' := le_ker_of_perfect (diagChar hd hk2) hperf
  have hk3' := le_ker_of_perfect (diagChar hd hk3) hperf
  intro x hx
  have hxC : x ∈ Subgroup.centralizer ({c211 ζ hζ} : Set SU4) := hLC hx
  have hmem : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({c211 ζ hζ} : Set SU4))) ∈
      L.subgroupOf (Subgroup.centralizer ({c211 ζ hζ} : Set SU4)) :=
    Subgroup.mem_subgroupOf.2 hx
  have e2 : mat x 2 2 = 1 := by
    have h := MonoidHom.mem_ker.1 (hk2' hmem)
    have h' := congrArg Units.val h
    exact h'
  have e3 : mat x 3 3 = 1 := by
    have h := MonoidHom.mem_ker.1 (hk3' hmem)
    have h' := congrArg Units.val h
    exact h'
  rw [mem_W0_iff]
  constructor
  · funext k
    rw [smul_single_eq, Pi.single_apply]
    by_cases hk : k = 2
    · subst hk
      rw [e2, if_pos rfl]
    · rw [entry_zero_of_mem_centralizer hd hxC (hk2 k hk), if_neg hk]
  · funext k
    rw [smul_single_eq, Pi.single_apply]
    by_cases hk : k = 3
    · subst hk
      rw [e3, if_pos rfl]
    · rw [entry_zero_of_mem_centralizer hd hxC (hk3 k hk), if_neg hk]

theorem card_perfect_c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (L : Subgroup SU4)
    (hLC : L ≤ Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) (hL : Group.IsPerfect ↥L) :
    Nat.card L ∣ 504 * 504 := by
  have hperf := subgroupOf_perfect hLC hL
  have hLKA : L ≤ KA ζ hζ := by
    intro x hx
    have hmem : (⟨x, hLC hx⟩ : ↥(Subgroup.centralizer ({c022 ζ hζ} : Set SU4))) ∈
        L.subgroupOf (Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) :=
      Subgroup.mem_subgroupOf.2 hx
    have hk := MonoidHom.mem_ker.1 (le_ker_of_perfect (detA ζ hζ) hperf hmem)
    exact ⟨hLC hx, congrArg Units.val hk⟩
  let ρ : ↥L →* SU4 := (piA ζ hζ).comp (Subgroup.inclusion hLKA)
  have hrange : Nat.card ρ.range ∣ 504 := by
    have : ρ.range ≤ W0 := by
      rintro _ ⟨x, rfl⟩
      exact piA_mem_W0 ζ hζ _
    exact (Subgroup.card_dvd_of_le this).trans (by rw [card_W0])
  have hker : Nat.card ρ.ker ∣ 504 := by
    let φ : ↥ρ.ker →* ↥W1 :=
      ((L.subtype.comp ρ.ker.subtype).codRestrict W1 fun x => by
        have hx : ρ x.1 = 1 := x.2
        exact piA_ker (Subgroup.inclusion hLKA x.1) hx)
    have hφ : Function.Injective φ := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    have h1 := Subgroup.card_dvd_of_injective φ hφ
    have h2 : Nat.card ↥W1 = 504 := by rw [Nat.card_congr W1equivW0.toEquiv, card_W0]
    rwa [h2] at h1
  rw [← Subgroup.card_ker_mul_card_range ρ]
  exact Nat.mul_dvd_mul hker hrange

theorem u4InnModel_SU4 : U4InnModel SU4 := by
  intro hS u hu3 hq
  show CFSG.pPrimeCore 3 ↥(u4Fix u) = ⊥
  by_cases hf : fieldFactor4 u = 1
  · obtain ⟨s, rfl⟩ := mem_range_conj_of_fieldFactor4_eq_one hf
    have hs : s ^ 3 = 1 := by
      have h3 : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact hu3
      have hz : s ^ 3 ∈ Subgroup.center SU4 := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut SU4 => φ g) h3
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48.center_SU4, Subgroup.mem_bot] at hz
      exact hz
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
    obtain ⟨h, hcases⟩ := normal_form s hs ζ hζ
    rw [u4Fix_conj] at hq ⊢
    have hτ : (MulAut.conj h : SU4 ≃* SU4) s = h * s * h⁻¹ := MulAut.conj_apply h s
    have hq' : HasU4Quot (Subgroup.centralizer ({h * s * h⁻¹} : Set SU4)) := by
      have := hq.map_equiv (MulAut.conj h : SU4 ≃* SU4)
      rwa [centralizer_map_equiv, hτ] at this
    refine pPrimeCore_centralizer_of_equiv (MulAut.conj h) s ?_
    rw [hτ]
    rcases hcases with h1 | h2 | h3 | h4 | h5
    · rw [h1]
      have : Subgroup.centralizer ({(1 : SU4)} : Set SU4) = ⊤ := by
        ext x
        rw [Subgroup.mem_centralizer_singleton_iff]
        simp
      rw [this]
      exact pPrimeCore_eq_bot_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup SU4) ≃* SU4)
        (pPrimeCore_eq_bot_of_simple three_dvd_card_SU4)
    · rw [h2]
      exact pPrimeCore_Cstd (zetaU_ne_one ζ hζ)
    · rw [h3]
      exact pPrimeCore_Cstd (zetaU_sq_ne_one ζ hζ)
    · exfalso
      rw [h4] at hq'
      obtain ⟨L, hLC, hLperf, hLdvd⟩ := hq'.exists_perfect
      have hLW0 := perfect_le_W0_c211 ζ hζ L hLC hLperf
      have h504 := (Subgroup.card_dvd_of_le hLW0).trans (dvd_of_eq card_W0)
      have := hLdvd.trans h504
      norm_num at this
    · exfalso
      rw [h5] at hq'
      obtain ⟨L, hLC, hLperf, hLdvd⟩ := hq'.exists_perfect
      have := hLdvd.trans (card_perfect_c022 ζ hζ L hLC hLperf)
      norm_num at this
  · obtain ⟨hcat, hcard⟩ := catalogIs_fixSub hu3 hf
    haveI := CFSG.LocalAnalysis.GLTheoremA.S10.isSimple_of_isU4two hcat
    have hH : u4Fix u = U48.fixSub u := by
      ext x
      exact Iff.rfl
    rw [hH]
    exact pPrimeCore_eq_bot_of_simple (by rw [hcard]; norm_num)

end U4InnU48

theorem u4InnAt_u4eight : U4InnAt S9.isU4eight := by
  intro S _ _ hcat
  obtain ⟨e0⟩ := bridge_u4eight hcat
  exact U4InnModel.of_mulEquiv (e0.trans equivSU4) U4InnU48.u4InnModel_SU4

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
