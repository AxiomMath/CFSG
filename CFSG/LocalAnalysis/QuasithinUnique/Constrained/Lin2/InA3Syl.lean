module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Lines
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Strong

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {P K : Subgroup G} (hP : IsPGroup 2 P) (hKP : K < P) :
    ∃ y ∈ P, y ∈ Subgroup.normalizer (K : Set G) ∧ y ∉ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let KP : Subgroup P := K.subgroupOf P
  have hne : KP ≠ ⊤ := by
    intro htop
    obtain ⟨z, hzP, hzK⟩ := IsConcreteLE.exists_of_lt hKP
    have : (⟨z, hzP⟩ : P) ∈ KP := by rw [htop]; trivial
    exact hzK (Subgroup.mem_subgroupOf.mp this)
  have hlt : KP < ⊤ := lt_top_iff_ne_top.2 hne
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt' : KP < Subgroup.normalizer (KP : Set P) := hnc KP hlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨x, x.2, ?_, fun h => hxnot (Subgroup.mem_subgroupOf.mpr h)⟩
  have hxsub : x ∈ (Subgroup.normalizer (K : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq (show K ≤ P from hKP.le)]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem mem_normalizer_strongClosure {A T' : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (T' : Set G)) :
    y ∈ Subgroup.normalizer ((strongClosure A T' : Subgroup G) : Set G) := by
  rw [← conjR_eq_self_iff]
  have hle : conjR (strongClosure A T') y ≤ strongClosure A T' := by
    unfold strongClosure
    rw [conjR_def, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨z, ⟨hzT, a, ha, g, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨?_, a, ha, g * y, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (T' : Set G)).inv_mem hy) _).mp hzT
      simpa using this
    · simp [mul_assoc]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjR])

end Generic

namespace Lin2Hyp

section Syl

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem elem_le_U_s_or_V_s {s x : G} (hx : x ∈ T) (hxS : x ∉ S) {E' : Subgroup G}
    (hE'R : E' ≤ thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)) (hE' : IsElemAbelian 2 E') :
    E' ≤ blockU L ⊓ Subgroup.centralizer ({s} : Set G) ∨
      E' ≤ conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) := by
  rcases (E.elemU hcfg hx hxS).2.2 E' (hE'R.trans inf_le_left) hE' with h | h
  · exact Or.inl (le_inf h (hE'R.trans inf_le_right))
  · exact Or.inr (le_inf h (hE'R.trans inf_le_right))

omit E in
theorem blockU_ne_bot_of_cfg : blockU L ≠ ⊥ := by
  intro h
  have := hcfg.short.2.2.2.2.1
  rw [h] at this
  exact not_lt_bot this

theorem S_s_sylow {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hLs2 : twoPart (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G)) :
    IsSylowTwoOf (S ⊓ Subgroup.centralizer ({s} : Set G))
      (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) := by
  set R := thompsonJ S with hR
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set GQ := Subgroup.normalizer (pCoreOf 2 H : Set G) with hGQ
  have hGQL : GQ = Subgroup.normalizer (L : Set G) := E.GQ_eq hcfg
  have hSG : IsSylowTwoOf S GQ := by
    have hQne : pCoreOf 2 H ≠ ⊥ := by rw [← E.UQ hcfg]; exact blockU_ne_bot_of_cfg hcfg
    exact hcfg.cs.isSylowTwoOf_normalizer hQne hcfg.Q_le_S hcfg.H_le_normalizer_Q
  have hSsGQ : S ⊓ C ≤ GQ ⊓ C := inf_le_inf_right _ hSG.le
  obtain ⟨P, hSsP, hP⟩ := exists_isSylowTwoOf_of_le hSsGQ (hcfg.S_isPGroup.to_le inf_le_left)
  suffices hcard : Nat.card P ≤ Nat.card (S ⊓ C : Subgroup G) by
    have := Subgroup.eq_of_le_of_card_ge hSsP hcard
    rw [this]; exact hP
  have hPGC : P ≤ GQ ⊓ C := hP.le
  have hPL : P ≤ Subgroup.normalizer (L : Set G) := hGQL ▸ hPGC.trans inf_le_left
  have hP2 : IsPGroup 2 P := hP.isPGroup
  obtain ⟨e, he⟩ := hP2.exists_card_eq
  have hb : L.relIndex P * Nat.card (L ⊓ P : Subgroup G) = Nat.card P :=
    Subgroup.relIndex_mul_card L P
  have hbdvd : L.relIndex P ∣ 2 ^ e := he ▸ Dvd.intro _ hb
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hbdvd
  have ha : Nat.card (L ⊓ P : Subgroup G) ≤ Nat.card (R ⊓ C : Subgroup G) := by
    rw [← hLs2]
    exact card_le_twoPart (inf_le_inf_left _ (hPGC.trans inf_le_right)) (hP2.to_le inf_le_right)
  have hX := relIndex_sup_of_le_normalizer hPL
  have hcardX : Nat.card (P ⊔ L : Subgroup G) = L.relIndex P * Nat.card L := by
    have := Subgroup.relIndex_mul_card L (P ⊔ L)
    rw [inf_eq_left.mpr le_sup_right, hX] at this
    exact this.symm
  have hXGQ : P ⊔ L ≤ GQ := sup_le (hPGC.trans inf_le_left)
    (hGQL ▸ (Subgroup.le_normalizer : L ≤ Subgroup.normalizer (L : Set G)))
  have htwo : twoPart (P ⊔ L : Subgroup G) = L.relIndex P * twoPart L := by
    unfold twoPart
    rw [hcardX, hk, Nat.factorization_mul (by positivity) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, pow_add]
    simp
  have hbR : L.relIndex P * Nat.card R ≤ Nat.card S := by
    have h1 := twoPart_mono hXGQ
    rw [htwo, ← hSG.card_eq, ← (E.Rsyl hcfg).card_eq] at h1
    exact h1
  have hSRn : S ≤ Subgroup.normalizer (R : Set G) := hcfg.S_le_T.trans (E.TnR hcfg)
  have hS_eq : R ⊔ (S ⊓ C) = S := by
    obtain ⟨F, hcyc, hFS, hRF, hRFS, hfus⟩ := E.exists_F hcfg
    exact (eq_sup_centralizer_involution (thompsonJ_le_self S) le_rfl
      (Subgroup.le_normalizer) hSRn hFS hcyc hRF hRFS hfus hs hsR hs2).symm
  have hSC : Nat.card S * Nat.card (R ⊓ C : Subgroup G) =
      Nat.card R * Nat.card (S ⊓ C : Subgroup G) := by
    have h1 := card_sup_mul_card_inf (A := S ⊓ C) (B := R) (inf_le_left.trans hSRn)
    rw [sup_comm, hS_eq, inf_comm, ← inf_assoc, inf_eq_left.mpr (thompsonJ_le_self S)] at h1
    rw [mul_comm (Nat.card R)]
    exact h1
  have hRpos : 0 < Nat.card R := Nat.card_pos
  apply Nat.le_of_mul_le_mul_right _ hRpos
  calc Nat.card P * Nat.card R = (L.relIndex P * Nat.card R) * Nat.card (L ⊓ P : Subgroup G) := by
        rw [← hb]; ring
    _ ≤ Nat.card S * Nat.card (R ⊓ C : Subgroup G) := Nat.mul_le_mul hbR ha
    _ = Nat.card (S ⊓ C : Subgroup G) * Nat.card R := by rw [hSC]; ring

theorem T_s_sylow {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hOs : pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      blockU L ⊓ Subgroup.centralizer ({s} : Set G))
    (hLs2 : twoPart (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G)) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({s} : Set G)) (Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨x, hxT, hxS⟩ := E.exists_mem_T_centralizer_not_mem_S hcfg hs hsR hs2
  set R := thompsonJ S with hR
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set Ts := T ⊓ C with hTs
  set U := blockU L with hU
  set Us := U ⊓ C with hUs
  have hTs2 : IsPGroup 2 Ts := hcfg.sylowT.isPGroup.to_le inf_le_left
  obtain ⟨P, hTsP, hP⟩ := exists_isSylowTwoOf_of_le (inf_le_right : Ts ≤ C) hTs2
  suffices hPle : P ≤ Ts by
    have : Ts = P := le_antisymm hTsP hPle
    rw [this]; exact hP
  by_contra hnot
  have hlt : Ts < P := lt_of_le_of_ne hTsP (fun h => hnot (h ▸ le_rfl))
  obtain ⟨y, hyP, hyN, hyT⟩ := exists_mem_normalizer_not_mem_of_lt hP.isPGroup hlt
  have hRs := E.R_s_eq_strongClosure hcfg hs hsR hs2 hxT hxS
  have hyRs : y ∈ Subgroup.normalizer ((R ⊓ C : Subgroup G) : Set G) := by
    rw [hRs]; exact mem_normalizer_strongClosure hyN
  have hRU : R = U ⊔ conjR U x := (E.RUU hcfg hxT.1 hxS).1
  have hUR : U ≤ R := by rw [hRU]; exact le_sup_left
  have hUsR : Us ≤ R ⊓ C := inf_le_inf_right _ hUR
  have hUe : IsElemAbelian 2 U := (E.elemU hcfg hxT.1 hxS).1
  have hconjR : conjR Us y ≤ R ⊓ C := by
    calc conjR Us y ≤ conjR (R ⊓ C) y := conjR_mono hUsR y
      _ = R ⊓ C := conjR_eq_of_mem_normalizer hyRs
  have hEl : IsElemAbelian 2 (conjR Us y) :=
    (isElemAbelian_conjR_iff Us y).mpr (IsElemAbelian.mono inf_le_left hUe)
  have hVc : Nat.card (conjR U x ⊓ C : Subgroup G) = Nat.card Us :=
    E.card_conjR_U_inf_centralizer hcfg hs hsR hs2 hxT.1
  have hVeq : conjR U x ⊓ C = conjR Us x := by
    have h1 := conjR_inf_centralizer U x s
    have hxs : x * s * x⁻¹ = s := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hxT.2
      calc x * s * x⁻¹ = s * x * x⁻¹ := by rw [this]
        _ = s := by group
    rw [hxs] at h1
    rw [h1]
  obtain ⟨y', hy'P, hy'T, hy'N⟩ : ∃ y' ∈ P, y' ∉ Ts ∧ y' ∈ Subgroup.normalizer (Us : Set G) := by
    rcases E.elem_le_U_s_or_V_s hcfg hxT.1 hxS hconjR hEl with h | h
    · have heq : conjR Us y = Us :=
        Subgroup.eq_of_le_of_card_ge h (by rw [card_conjR])
      exact ⟨y, hyP, hyT, conjR_eq_self_iff.mp heq⟩
    · have heq : conjR Us y = conjR U x ⊓ C :=
        Subgroup.eq_of_le_of_card_ge h (by rw [card_conjR, hVc])
      rw [hVeq] at heq
      refine ⟨y * x⁻¹, P.mul_mem hyP (P.inv_mem (hTsP hxT)), fun h' => hyT ?_, ?_⟩
      · have := Ts.mul_mem h' hxT
        simpa using this
      · rw [← conjR_eq_self_iff, ← conjR_conjR, heq, conjR_conjR]
        simp
  have hy'U : y' ∈ Subgroup.normalizer (U : Set G) :=
    E.normalizer_U_s_le hcfg hs hsR hs2 hOs hy'N
  have hy'GQ : y' ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [← E.UQ hcfg]; exact hy'U
  have hSs := E.S_s_sylow hcfg hs hsR hs2 hLs2
  have hSsX : S ⊓ C ≤ P ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    le_inf ((inf_le_inf_right _ hcfg.S_le_T).trans hTsP)
      (inf_le_left.trans (hcfg.H_le_normalizer_Q.trans' hcfg.S_le_H))
  have hXK : P ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ C := fun z hz => ⟨hz.2, hP.le hz.1⟩
  have hX := hSs.eq_of_le hSsX hXK (hP.isPGroup.to_le inf_le_left)
  have hy'S : y' ∈ S ⊓ C := hX ▸ (⟨hy'P, hy'GQ⟩ : y' ∈ P ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G))
  exact hy'T ⟨hcfg.S_le_T hy'S.1, hy'S.2⟩

end Syl

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
