module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverA7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddOvergroups
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem reduce_center_gen {G : Type} [Group G] [Finite G] (hq : CFSG.IsQuasisimple G)
    {T X K : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hTX : T ≤ X) (hX : X ≠ ⊤) (hKX : K ≤ X) (hsub : IsSubnormal K X)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) (hKc : ¬ K ≤ Subgroup.center G) :
    IsSylowTwoOf (T.map (ctr G)) ⊤ ∧ T.map (ctr G) ≤ X.map (ctr G) ∧ X.map (ctr G) ≠ ⊤ ∧
      K.map (ctr G) ≤ X.map (ctr G) ∧ IsSubnormal (K.map (ctr G)) (X.map (ctr G)) ∧
      (CFSG.IsQuasisimple ↥(K.map (ctr G)) ∨ Nat.card ↥(K.map (ctr G)) = 3) := by
  have hker : (ctr G).ker = Subgroup.center G := QuotientGroup.ker_mk' _
  refine ⟨?_, Subgroup.map_mono hTX, ?_, Subgroup.map_mono hKX, A3.subnormal_map _ hsub, ?_⟩
  · have hTi : ¬ 2 ∣ T.index := by
      have h := hT.2.2
      rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
    have hmap : ¬ 2 ∣ (T.map (ctr G)).index := fun h =>
      hTi (h.trans (T.index_map_dvd (QuotientGroup.mk'_surjective (Subgroup.center G))))
    refine ⟨le_top, hT.2.1.map (ctr G), ?_⟩
    rw [show ((T.map (ctr G)).subgroupOf ⊤).index = (T.map (ctr G)).index from
      Subgroup.relIndex_top_right _]
    exact hmap
  · intro htop
    apply hX
    refine eq_top_of_sup_center_eq_top hq.1 ?_
    have := Subgroup.comap_map_eq (ctr G) X
    rw [htop, Subgroup.comap_top, hker] at this
    exact this.symm
  · have hKf : ¬ K ≤ (ctr G).ker := by rwa [hker]
    rcases hK with hKq | h3
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_map hKq (ctr G) hKf)
    · right
      have hbot : K ⊓ (ctr G).ker = ⊥ := inf_eq_bot_of_card_three h3 hKf
      have hinj : Function.Injective ((ctr G).comp K.subtype) := by
        rw [← MonoidHom.ker_eq_bot_iff]
        rw [eq_bot_iff]
        intro k hk
        rw [MonoidHom.mem_ker] at hk
        have hk1 : (k : G) ∈ K ⊓ (ctr G).ker := ⟨k.2, hk⟩
        rw [hbot] at hk1
        exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hk1))
      have hrange : K.map (ctr G) = ((ctr G).comp K.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange, ← h3]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem false_of_overgroups_gen {Ω : Type} [Group Ω] [Finite Ω] {L T X K : Subgroup Ω}
    (hLq : CFSG.IsQuasisimple ↥L) (hT : IsSylowTwoOf T L) (hTX : T ≤ X)
    (hXL : X ≤ L) (hXne : X ≠ L) (hKX : K ≤ X) (hsub : IsSubnormal K X)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3)
    (hKc : ¬ K ≤ Subgroup.centralizer (L : Set Ω))
    (hov : Overgroups (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨hT', hTX', hXne', hKX', hsub'⟩ := lift_to_subgroup hT hTX hXL hXne hKX hsub
  have hKL : K ≤ L := hKX.trans hXL
  obtain ⟨hT'', hTX'', hXne'', hKX'', hsub'', hK''⟩ :=
    reduce_center_gen hLq hT' hTX' hXne' hKX' hsub' (lift_quasisimple_or_card_three hKL hK)
      (not_le_center_of_not_le_centralizer hKL hKc)
  exact false_of_charTwo (hov _ _ hT'' hTX'' hXne'') hKX'' hsub'' hK''

end CFSG.QuasithinUnique.Bridge.Over

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

private theorem bk4_five_le {Ω : Type} [Group Ω] {L : Subgroup Ω}
    (hLq : CFSG.IsQuasisimple ↥L) {m : ℕ} (e : ↥L ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  by_contra hlt
  have hm4 : Nat.card (Fin m) ≤ 4 := by
    simp
    omega
  haveI := alternatingGroup.isSolvable hm4
  have hsolv : Group.IsSolvable ↥L :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Group.IsPerfect ↥L := hLq.1
  haveI := hLq.2.1
  haveI : Nontrivial ↥L :=
    Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center ↥L))
  exact Group.IsPerfect.not_isSolvable ↥L hsolv

private theorem bk4_center_bot {Ω : Type} [Group Ω] {L : Subgroup Ω}
    (hLq : CFSG.IsQuasisimple ↥L) {m : ℕ} (hm : 5 ≤ m)
    (e : ↥L ≃* alternatingGroup (Fin m)) : Subgroup.center ↥L = ⊥ := by
  haveI hA : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  haveI hLs : IsSimpleGroup ↥L := e.isSimpleGroup
  haveI := hLq.2.1
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥L) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hxy : (x : ↥L ⧸ Subgroup.center ↥L) = (y : ↥L ⧸ Subgroup.center ↥L) :=
      QuotientGroup.eq.mpr (by rw [h]; exact Subgroup.mem_top _)
    exact hab hxy

theorem asLieAltOvergroups_of
    (hLie : AsLieTwoOvergroups) : AsLieAltOvergroups := by
  unfold AsLieAltOvergroups
  intro Ω _ _ L T X K hLq hLA hT hTX hXL hXne hKX hsub hK hKc
  rcases hLA with h2 | ⟨m, ⟨e⟩⟩ | hHat
  · exact (CFSG.QuasithinUnique.Bridge.Over.false_of_overgroups_gen hLq hT hTX hXL hXne hKX
      hsub hK hKc (hLie _ hLq.2.1 h2.2)).elim
  · have hm5 : 5 ≤ m := bk4_five_le hLq e
    by_cases h5 : m = 5 ∨ m = 6 ∨ m = 8
    · have hc : Subgroup.center ↥L = ⊥ := bk4_center_bot hLq hm5 e
      have e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin m) :=
        ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
      exact (CFSG.QuasithinUnique.Bridge.Over.false_of_overgroups_gen hLq hT hTX hXL hXne hKX
        hsub hK hKc (CFSG.QuasithinUnique.Bridge.Over.overgroups_alt h5 e')).elim
    by_cases h7 : m = 7
    · subst h7
      rcases CFSG.QuasithinUnique.Bridge.Over.A7.concl_of_alt7 e hT hTX hXL hXne hKX hsub hK
        with h | h
      · exact ⟨7, ⟨e⟩, Or.inl h⟩
      · exact ⟨7, ⟨e⟩, Or.inr ⟨h, rfl⟩⟩
    have hm9 : 9 ≤ m := by omega
    rcases Nat.even_or_odd m with hev | hodd
    · have hm10 : 10 ≤ m := by
        obtain ⟨k, hk⟩ := hev
        omega
      obtain ⟨n, hn, hKn⟩ :=
        CFSG.QuasithinUnique.L246C127.alt_overgroups_even L T X K hm10 hev ⟨e⟩ hT hTX hXL hKX
          hsub hK
      exact ⟨m, ⟨e⟩, Or.inl ⟨n, hn, hKn⟩⟩
    · obtain ⟨n, hn, hKn⟩ :=
        CFSG.QuasithinUnique.L246C127.alt_overgroups_odd Ω L T X K m hm9 hodd ⟨e⟩ hT hTX hXL
          hKX hsub hK
      exact ⟨m, ⟨e⟩, Or.inl ⟨n, hn, hKn⟩⟩
  · obtain ⟨-, -, ⟨e6⟩⟩ := hHat
    exact (CFSG.QuasithinUnique.Bridge.Over.false_of_overgroups_gen hLq hT hTX hXL hXne hKX
      hsub hK hKc (CFSG.QuasithinUnique.Bridge.Over.Overgroups.of_mulEquiv e6.symm
        CFSG.QuasithinUnique.Bridge.Over.overgroups_alt_six)).elim

end CFSG.Quasithin
