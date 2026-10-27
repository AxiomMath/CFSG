module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05I1416Spor
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CrossCharOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

open scoped commutatorElement

private theorem i1431_char_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;> first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

private theorem i1431_catalogIs_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs T Q) : catalogIs S Q :=
  let ⟨i, hi, ⟨f⟩⟩ := h
  ⟨i, hi, ⟨e.trans f⟩⟩

section MainCerts


theorem i1431ClAt_of_XK (hSpor : I1431SporSK) (hChev : I1431ChevTwoS) (G : Type) [Group G] [Finite G]
    (h1429 : I1429At G) : I1431ClAt G := by
  intro a x K J ha hX hxX hxo hxna hK hxN hJ hJU hnot hrk
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    omega
  have hap : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hncent : ¬ CentMod 3 K x := fun h => hnot (i1431_le_sup_of_centMod hp hK hap h hJ)
  have haK : a ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hk)
  have hRk : RkY (PQuot 3 K) := i1431_rkY ha3 ha1 haK hrk
  have hcat : IsCatalogGroup (PSimple 3 K) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hK.1).quotient _)
      (isQuasisimple_pQuot_of_glaPComponent hp hK)
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a', b', hab⟩ := (chev_pSimple_simple_nonabelian hp hK).2
    apply hab
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exfalso
    obtain ⟨m, hm5, ⟨eJ⟩⟩ := i1416AltSmall hp hp2 hK hxN hx3 hncent hJ hn e
    exact i1431_u42_not_alt hm5 hJU eJ
  | sporadic s =>
    have hKPS : CFSG.Open.IsKGroup (PSimple 3 K) := ((hX.of_le hK.1).quotient _).quotient _
    have hs : s = TauCeti.SporadicName.Co2 := by
      obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hxN hap hJ
      exact hSpor (PSimple 3 K) s ⟨e⟩ hKPS (chevAut 3 K ⟨x, hxN⟩) (chevAut_pow_eq_one 3 K hxN hx3)
        (fun h => hncent ((chevAut_eq_one_iff hp hK hxN).1 h)) (chevTransfer 3 K J)
        (glaPComponent_chevTransfer hp hxN hap hJ) (i1431_catalogIs_congr g.symm hJU)
    subst hs
    exact ⟨TauCeti.CFSGIndex.sporadic .Co2, (i1431List_iff _).2 (Or.inl rfl), ⟨e⟩⟩
  | lie d =>
    have hr : d.1.characteristic.Prime := i1431_char_prime d.1
    have hKr : IsChevSimple d.1.characteristic (PSimple 3 K) :=
      Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨e⟩⟩
    have hxN' : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.2 hxN
    have hcen : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
        Subgroup.centralizer ({x} : Set G) := by
      ext g
      simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
      constructor
      · intro h
        exact h x (Subgroup.mem_zpowers x)
      · intro h z hz
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact (Commute.zpow_left (show Commute x g from h) m).eq
    have hJr : IsChevSimple d.1.characteristic (PSimple 3 J) :=
      (chevClosureQAt_of_lieComp_lieComps (G := G) lieComp_holds
        (fun _ hq' h5 => lieCompsOn_holds hq' h5) hp hp2)
        hp hp2 d.1.characteristic hr (S9.cx a) K (Subgroup.zpowers x) hX hK hKr
        (i1431_isElemAbelian_zpowers hx3) hxN' J (by rw [hcen]; exact hJ)
    rcases i1431_char_two_or_three CFSG.LocalAnalysis.GLTheoremB.MovingAround.CrossCharOdd.input3_3_OddChar_holds
      hJr hJU with h2 | h3
    ·
      have hY : catalogIs (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K))
          (onLie fun d => d.characteristic = 2) :=
        ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using h2, ⟨e⟩⟩
      have hξ3 : barAut 3 K ⟨x, hxN⟩ ^ 3 = 1 := by
        have h : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext hx3
        rw [← map_pow, h, map_one]
      have hξ1 : barAut 3 K ⟨x, hxN⟩ ≠ 1 := fun h =>
        hncent ((chev_barAut_eq_one_iff_centMod hxN).1 h)
      obtain ⟨g⟩ := i1431_pSimple_equiv_barImage hp hxN hap hJ
      obtain ⟨i, hi, f⟩ := hChev (PQuot 3 K) (isQuasisimple_pQuot_of_glaPComponent hp hK)
        (glaPPrimeCore_quotient_eq_bot hp) hRk hY (barAut 3 K ⟨x, hxN⟩) hξ3 hξ1
        ((J.subgroupOf K).map (pQuotHom 3 K)) (glaPComponent_map_pQuotHom hp hxN hap hJ)
        (i1431_catalogIs_congr g.symm hJU)
      exact ⟨i, (i1431List_iff i).2 (Or.inr hi), f⟩
    ·
      rw [h3] at hKr
      have h6 := h1429 (S9.cx a) K J x hX hK hKr hxN hx3 hncent hJ hJU
      exact (i1431_not_five_le_twoLocalRank hRk (le_trans (by norm_num) h6)).elim

end MainCerts

end CFSG.LocalAnalysis.GLTheoremA

end
