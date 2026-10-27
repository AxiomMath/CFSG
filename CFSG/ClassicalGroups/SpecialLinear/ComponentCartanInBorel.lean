module

public import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanRankFinal
public import CFSG.ClassicalGroups.SpecialLinear.DiagTorusNormalizesUnitriangular
public import CFSG.Quasithin.Background.E3Transport
public import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanRankDivisible
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCoverUncond
public import CFSG.GroupTheory.SylowTwoOfConj
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

theorem exists_elemAbelian_diagTorus_meet_ker_eq_bot
    {n : Nat} (hn : 4 <= n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {q : Nat} (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1)
    {L : Type} [Group L] [Finite L] (pi : SpecialLinearGroup (Fin n) F →* L)
    (hker : pi.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)) :
    ∃ T : Subgroup (SpecialLinearGroup (Fin n) F),
      T ≤ diagTorus n F ∧
      CFSG.Open.IsElemAbelian q T ∧ Nat.card T = q ^ 3 ∧ T ⊓ pi.ker = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd' : q ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' q hdvd'
  rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
  ·
    subst h4
    obtain ⟨T, hTle, hTelem, hTcard⟩ :=
      exists_elemAbelian_of_diagGen (n := 4) (F := F) hn hq t ht (diagTorus 4 F)
        (fun i => diagGen_mem_diagTorus (n := 4) (F := F) t hn i)
    refine ⟨T, hTle, hTelem, hTcard, ?_⟩
    have hle : T ⊓ pi.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 4) F) :=
      inf_le_right.trans hker
    rw [center_specialLinear_four_eq_bot F] at hle
    exact le_antisymm hle bot_le
  ·
    let s : Finset (Fin n) := (Finset.univ.image (threeToFin hn)) ∪ {threeIndex hn}
    have hs : s.card ≤ 4 := by
      have h1 : s.card ≤
          (Finset.univ.image (threeToFin hn)).card + ({threeIndex hn} : Finset _).card :=
        Finset.card_union_le _ _
      have h2 : (Finset.univ.image (threeToFin hn)).card ≤ 3 := by
        simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 3)))
      have h3 : ({threeIndex hn} : Finset (Fin n)).card = 1 := by simp
      omega
    have hlt : s.card < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨j, _, hjs⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ) hlt
    have hj1 : ∀ i : Fin 3, j ≠ threeToFin hn i := by
      intro i h
      exact hjs (Finset.mem_union.mpr (Or.inl
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩)))
    have hj2 : j ≠ threeIndex hn := by
      intro h
      exact hjs (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    let Hfix : Subgroup (SpecialLinearGroup (Fin n) F) :=
      { carrier := {g | SpecialLinearGroup.toLin' g (Pi.single j 1) = Pi.single j 1}
        one_mem' := by simp
        mul_mem' := by
          intro g h hg hh
          change SpecialLinearGroup.toLin' (g * h) (Pi.single j 1) = Pi.single j 1
          rw [map_mul, LinearEquiv.mul_apply, hh, hg]
        inv_mem' := by
          intro g hg
          change SpecialLinearGroup.toLin' g⁻¹ (Pi.single j 1) = Pi.single j 1
          rw [map_inv]
          have h2 : (SpecialLinearGroup.toLin' g).symm (Pi.single j 1) = Pi.single j 1 := by
            have h3 := congrArg (SpecialLinearGroup.toLin' g).symm hg
            simpa using h3.symm
          simpa using h2 }
    have hgen_fix : ∀ i : Fin 3, diagGen (n := n) (F := F) t hn i ∈ Hfix := by
      intro i
      change SpecialLinearGroup.toLin' (diagGen (n := n) (F := F) t hn i) (Pi.single j 1) =
        Pi.single j 1
      rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, coe_diagGen,
        Matrix.diagonal_mulVec_single]
      have hval : diagUnit (n := n) (F := F) t hn i j = 1 := diagUnit_of_ne t hn i (hj1 i) hj2
      rw [hval]
      simp
    obtain ⟨T, hTH, hTelem, hTcard⟩ :=
      exists_elemAbelian_of_diagGen (n := n) (F := F) hn hq t ht
        (diagTorus n F ⊓ Hfix)
        (fun i => Subgroup.mem_inf.mpr
          ⟨diagGen_mem_diagTorus (n := n) (F := F) t hn i, hgen_fix i⟩)
    refine ⟨T, hTH.trans inf_le_left, hTelem, hTcard, ?_⟩
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgT, hgker⟩ := Subgroup.mem_inf.mp hg
    have hgcen : g ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := hker hgker
    have hgfix : SpecialLinearGroup.toLin' g (Pi.single j 1) = Pi.single j 1 :=
      (hTH.trans inf_le_right) hgT
    have hsc := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hgcen j
    have hlam : (g : Matrix (Fin n) (Fin n) F) j j = 1 := by
      have h1 := congrArg (fun v : Fin n → F => v j) hgfix
      rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
        Matrix.mulVec_single_one, Matrix.col_apply] at h1
      simpa using h1
    have hone : (g : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← hsc, hlam, Matrix.scalar_apply, Matrix.diagonal_one]
    exact Subtype.ext hone

theorem exists_cartan_in_borel_of_linear_component
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : Nat) (hm : 3 <= m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : ¬ (m = 2 ∧ Q.card = 4))
    {q : Nat} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Q.card - 1)
    {U : Subgroup L} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ Hc : Subgroup L,
      IsPiSubgroup {p : Nat.Primes | (p : Nat) ≠ 2} Hc ∧
      3 <= CFSG.Open.pRank q Hc ∧ Hc ≤ Subgroup.normalizer (U : Set L) := by
  classical
  obtain ⟨F, hFld, hFfin, hFchar, π, hFcard, hπsurj, hker⟩ :=
    exists_central_cover_specialLinear_of_ne_two_four hL m (by omega) Q hQ hv e hne
  letI : Field F := hFld
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  haveI : Fintype F := Fintype.ofFinite F
  let SL := SpecialLinearGroup (Fin (m + 1)) F
  have hdvdF : q ∣ Nat.card F - 1 := by rw [hFcard]; exact hdvd
  have hn : 4 ≤ m + 1 := by omega
  obtain ⟨T, hTle, hTelem, hTcard, hTdisj⟩ :=
    exists_elemAbelian_diagTorus_meet_ker_eq_bot (n := m + 1) hn hq hdvdF π hker
  let U0 : Subgroup SL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (m + 1) F
  have hU0 : CFSG.QuasithinUnique.IsSylowTwoOf U0 ⊤ :=
    CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (n := m + 1) (by omega)
  have hTnorm : T ≤ Subgroup.normalizer (U0 : Set SL) :=
    hTle.trans (CFSG.diagTorus_le_normalizer_unitriangular (n := m + 1) (F := F))
  let Hc0 : Subgroup L := T.map π
  have hHc0card : Nat.card Hc0 = q ^ 3 := by
    have h := Subgroup.relIndex_mul_card (H := π.ker) (K := T)
    have h1 : π.ker.relIndex T = Nat.card (T.map π) := Subgroup.relIndex_ker (f := π) (K := T)
    rw [h1, inf_comm, hTdisj, Subgroup.card_bot, mul_one] at h
    exact h.trans hTcard
  have hHc0elem : CFSG.Open.IsElemAbelian q Hc0 :=
    CFSG.SectionRank.isElemAbelian_map hTelem π
  have hHc0odd : Odd (Nat.card Hc0) := by
    rw [hHc0card]
    exact (hq.odd_of_ne_two hq2).pow
  have hHc0pi : IsPiSubgroup {p : Nat.Primes | (p : Nat) ≠ 2} Hc0 := by
    intro p hp h2
    exact hHc0odd.not_two_dvd_nat (h2 ▸ hp)
  have hHc0rank : 3 ≤ CFSG.Open.pRank q Hc0 :=
    CFSG.SectionRank.le_pRank hq.one_lt le_rfl hHc0elem hHc0card
  have hU0map : CFSG.QuasithinUnique.IsSylowTwoOf (U0.map π) ⊤ :=
    CFSG.AGLEmbedding.isSylowTwoOf_map_top_of_surjective hU0 hπsurj
  have hHc0norm : Hc0 ≤ Subgroup.normalizer (U0.map π : Set L) := by
    calc Hc0 = T.map π := rfl
      _ ≤ (Subgroup.normalizer (U0 : Set SL)).map π := Subgroup.map_mono hTnorm
      _ ≤ Subgroup.normalizer (U0.map π : Set L) := Subgroup.le_normalizer_map π
  obtain ⟨g, -, hg⟩ := CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf
    (L := ⊤) (P := U0.map π) (P' := U) hU0map hU
  refine ⟨Hc0.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · exact CFSG.LocalCores.isPiSubgroup_map hHc0pi (MulAut.conj g).toMonoidHom
  · have hrank : CFSG.Open.pRank q (Hc0.map (MulAut.conj g).toMonoidHom) =
        CFSG.Open.pRank q Hc0 :=
      CFSG.Quasithin.E3.pRank_map_mulEquiv' (MulAut.conj g) hq Hc0
    rw [hrank]
    exact hHc0rank
  · rw [hg]
    calc Hc0.map (MulAut.conj g).toMonoidHom
        ≤ (Subgroup.normalizer (U0.map π : Set L)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hHc0norm
      _ = Subgroup.normalizer ((CFSG.Quasithin.conjSub g (U0.map π) : Subgroup L) : Set L) :=
          Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective

end CFSG.ClassicalGroups.SpecialLinear

end
