module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up1415Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKSporDefs
public import CFSG.HardMathSupport.Dickson.BMRows.KFormBridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (kRows_of_isKGroup isKGroup_pSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section BMKBridge1415

private theorem bmk_up1415_char_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;> first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

private theorem bmk_up1415_elemAb {G : Type} [Group G] {p : ℕ} {y : G} (hyp : y ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers y) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hm, ← hn]
    exact (Commute.refl y).zpow_zpow m n |>.eq
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]

private theorem bmk_up1415_cen {G : Type} [Group G] (y : G) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h y (Subgroup.mem_zpowers y)
  · intro h z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (show Commute y g from h) m).eq

private theorem bmk_up1415_sporIs_eq (s : TauCeti.SporadicName) : S8.sporIs s = isSporIdx s := by
  funext i
  cases i <;> simp [S8.sporIs, isSporIdx]

theorem i1415At_of_sporK (h : I1415SporSK) (G : Type) [Group G] [Finite G] (p : ℕ) : I1415At G p := by
  intro hp hp2 X K J y m hX hK hyN hyp hncent hJ hm9 hJm
  have hyp' : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hα1 : chevAut p K ⟨y, hyN⟩ ≠ 1 := fun h' => hncent ((chevAut_eq_one_iff hp hK hyN).1 h')
  have hαp : chevAut p K ⟨y, hyN⟩ ^ p = 1 := chevAut_pow_eq_one p K hyN hyp
  have hL : GLAPComponent p (fixSubgroup (chevAut p K ⟨y, hyN⟩)) (chevTransfer p K J) :=
    glaPComponent_chevTransfer hp hyN hyp' hJ
  obtain ⟨eJL⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp' hJ
  have hm5 : 5 ≤ m := by omega
  obtain ⟨eJA⟩ := up1415_pSimple_alt hm5 hJm
  have hcat : IsCatalogGroup (PSimple p K) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hK.1).quotient _)
      (isQuasisimple_pQuot_of_glaPComponent hp hK)
  obtain ⟨i, ⟨eT⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨-, a, b, hab⟩ := chev_pSimple_simple_nonabelian hp hK
    apply hab
    apply eT.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    have hβ : (MulAut.congr eT) (chevAut p K ⟨y, hyN⟩) ^ p = 1 := by
      rw [← map_pow, hαp, map_one]
    have hβ1 : (MulAut.congr eT) (chevAut p K ⟨y, hyN⟩) ≠ 1 := fun h' =>
      hα1 ((MulAut.congr eT).injective (h'.trans (map_one _).symm))
    obtain ⟨hLe, ⟨eLe⟩⟩ := chevQ_transport hp eT hL
    obtain ⟨m', k, hm', hk, hnk, ⟨f⟩⟩ := up1415_altExactRoot hn hp hp2 hβ hβ1 hLe
    have hmm : m = m' := up1415_alt_index_eq hm5 hm' (eJA.symm.trans (eJL.trans (eLe.trans f)))
    refine ⟨k, hk, ?_⟩
    have h8 : 8 ≤ n := by omega
    have hiso := up1415_isAltPType_of_pSimple hp hp2 hK h8 eT
    rw [show m + k * p = n by omega]
    exact hiso
  | sporadic s =>
    obtain ⟨hKB, hKM⟩ := kRows_of_isKGroup (isKGroup_pSimple hX hK) eT
    exact (h (PSimple p K) s ⟨eT⟩ hKB hKM p hp hp2 (chevAut p K ⟨y, hyN⟩) hαp hα1 (chevTransfer p K J) hL m
      (by omega) ⟨eJL.symm.trans eJA⟩).elim
  | lie d =>
    have hr : d.1.characteristic.Prime := bmk_up1415_char_prime d.1
    have hKr : IsChevSimple d.1.characteristic (PSimple p K) :=
      Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨eT⟩⟩
    have hyN' : Subgroup.zpowers y ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.2 hyN
    have hJr : IsChevSimple d.1.characteristic (PSimple p J) :=
      (chevClosureQAt_of_lieComp_lieComps (G := G) lieComp_holds
        (fun _ hq' h5 => lieCompsOn_holds hq' h5) hp hp2) hp hp2 d.1.characteristic hr X K
        (Subgroup.zpowers y) hX hK hKr (bmk_up1415_elemAb hyp) hyN' J (by rw [bmk_up1415_cen]; exact hJ)
    exact (up1415_alt_not_chev (by omega) eJA hr hJr).elim

theorem i1415NineAt_of_sporK (h : I1415NineSporSK) (G : Type) [Group G] [Finite G] : I1415NineAt G := by
  intro X K J y hX hK hyN hy3 hJ hJA9
  have hyp' : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hy3
  by_cases hcm : CentMod 3 K y
  ·
    obtain ⟨eQ⟩ := pQuot_equiv_of_centMod Nat.prime_three hK hyp' hcm hJ
    obtain ⟨eJ⟩ := hJA9
    exact Or.inl ⟨0, ⟨eQ.symm.trans eJ⟩⟩
  · have hα1 : chevAut 3 K ⟨y, hyN⟩ ≠ 1 := fun h' =>
      hcm ((chevAut_eq_one_iff Nat.prime_three hK hyN).1 h')
    have hαp : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
    have hL : GLAPComponent 3 (fixSubgroup (chevAut 3 K ⟨y, hyN⟩)) (chevTransfer 3 K J) :=
      glaPComponent_chevTransfer Nat.prime_three hyN hyp' hJ
    obtain ⟨eJL⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hyN hyp' hJ
    obtain ⟨eJA⟩ := up1415_pSimple_alt (by norm_num) hJA9
    have hcat : IsCatalogGroup (PSimple 3 K) :=
      CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hK.1).quotient _)
        (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK)
    obtain ⟨i, ⟨eT⟩⟩ := hcat
    cases i with
    | cyclic r hr =>
      exfalso
      obtain ⟨-, a, b, hab⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
      apply hab
      apply eT.injective
      simp only [map_mul]
      exact mul_comm _ _
    | alternating n hn =>
      have hβ : (MulAut.congr eT) (chevAut 3 K ⟨y, hyN⟩) ^ 3 = 1 := by
        rw [← map_pow, hαp, map_one]
      have hβ1 : (MulAut.congr eT) (chevAut 3 K ⟨y, hyN⟩) ≠ 1 := fun h' =>
        hα1 ((MulAut.congr eT).injective (h'.trans (map_one _).symm))
      obtain ⟨hLe, ⟨eLe⟩⟩ := chevQ_transport Nat.prime_three eT hL
      obtain ⟨m', k, hm', hk, hnk, ⟨f⟩⟩ :=
        up1415_altExactRoot hn Nat.prime_three (by norm_num) hβ hβ1 hLe
      have hmm : 9 = m' :=
        up1415_alt_index_eq (by norm_num) hm' (eJA.symm.trans (eJL.trans (eLe.trans f)))
      refine Or.inl ⟨k, ?_⟩
      have h8 : 8 ≤ n := by omega
      have hiso := up1415_isAltPType_of_pSimple Nat.prime_three (by norm_num) hK h8 eT
      rw [show 9 + 3 * k = n by omega]
      exact hiso
    | sporadic s =>
      obtain ⟨hKB, hKM⟩ := kRows_of_isKGroup (isKGroup_pSimple hX hK) eT
      have hs := h (PSimple 3 K) s ⟨eT⟩ hKB hKM (chevAut 3 K ⟨y, hyN⟩) hαp hα1 (chevTransfer 3 K J) hL
        ⟨eJL.symm.trans eJA⟩
      rcases hs with rfl | rfl
      · exact Or.inr (Or.inl ⟨TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.HN, rfl, ⟨eT⟩⟩)
      · exact Or.inr (Or.inr ⟨TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Co1, rfl, ⟨eT⟩⟩)
    | lie d =>
      have hr : d.1.characteristic.Prime := bmk_up1415_char_prime d.1
      have hKr : IsChevSimple d.1.characteristic (PSimple 3 K) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨eT⟩⟩
      have hyN' : Subgroup.zpowers y ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.2 hyN
      have hJr : IsChevSimple d.1.characteristic (PSimple 3 J) :=
        (chevClosureQAt_of_lieComp_lieComps (G := G) lieComp_holds
          (fun _ hq' h5 => lieCompsOn_holds hq' h5) Nat.prime_three (by norm_num))
          Nat.prime_three (by norm_num) d.1.characteristic hr X K (Subgroup.zpowers y) hX hK hKr
          (bmk_up1415_elemAb hy3) hyN' J (by rw [bmk_up1415_cen]; exact hJ)
      exact (up1415_alt_not_chev (by norm_num) eJA hr hJr).elim

theorem l83_i1415NineAt_of_sporK (h : I1415NineSporSK) (G : Type) [Group G] [Finite G] :
    S8.L83.I1415NineAt G := by
  intro X K J d hX hK hdN hd hJ hJA9
  rcases i1415NineAt_of_sporK h G X K J d hX hK hdN hd hJ hJA9 with ⟨k, hk⟩ | hHN | hCo
  · exact Or.inl ⟨k, hk⟩
  · refine Or.inr (Or.inl ?_)
    rw [bmk_up1415_sporIs_eq]
    exact hHN
  · refine Or.inr (Or.inr ?_)
    rw [bmk_up1415_sporIs_eq]
    exact hCo

end BMKBridge1415

end CFSG.LocalAnalysis.GLTheoremA
