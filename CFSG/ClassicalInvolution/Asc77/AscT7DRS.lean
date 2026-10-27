module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenWire
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAll
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscT7AAlphaTwin
public import CFSG.ClassicalInvolution.Asc77.AscT7CSetup25

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7D

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem ctx_of_stand {K : Subgroup G} (hs : AscStand p f Ω K) (hW : W ∈ WSet Ω) :
    Thompson.Ctx p f Ω W :=
  ⟨hs.odd, hs.five, hs.hyp, hW,
    thompsonKey G Ω ⟨hs.odd, hs.five, hs.hyp, hs.aEmpty⟩ W hW, hs.aEmpty⟩

theorem exists_rep (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hRK : IsSylow2In R K) (hRD : R ∈ DSet Ω W) :
    ∃ ρ : Thompson.Rep Ω W, ρ.K = K ∧ ρ.R = R := by
  obtain ⟨-, -, -, -, hcard⟩ := Thompson.inf_W_of_mem_D hp hq hΩ hW hRD hK hRK
  have hnle : ¬ R ≤ W := by
    intro hle
    rw [inf_eq_left.mpr hle] at hcard
    have : 0 < Nat.card ↥R := Nat.card_pos
    omega
  obtain ⟨r, hr, hrW⟩ := Set.not_subset.mp hnle
  exact ⟨⟨K, R, r, hK, hRD, hRK, hr, hrW⟩, rfl, rfl⟩

omit [Finite G] in
theorem rep_img_mem (ρ : Thompson.Rep Ω W) : ρ.img ∈ muGroup Ω W :=
  Thompson.piG_mem_muGroup (Subgroup.mem_sup_left (Thompson.le_MGrp_of_mem_D ρ.hR ρ.hr))

omit [Finite G] in
theorem muGroup_comm_of_E4 (h : MuIsoE4 Ω W) (a b : ↥(muGroup Ω W)) : a * b = b * a := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem exists_sylow_frame {K K' : Subgroup G} {z : G} (hs : Hyp23Setting p f Ω K K' z)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (R R' : Subgroup G), W ≤ (S : Subgroup G) ∧ IsSylow2In R K ∧
      IsSylow2In R' K' ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ K) K :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hΩ hK hz)
  have hR' : IsSylow2In (T ⊓ K') K' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hΩ hK' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  exact ⟨S, T ⊓ K, T ⊓ K', hWT.trans hTS, hR, hR', inf_le_left.trans hTS,
    inf_le_left.trans hTS⟩

end T7D

variable {p f : ℕ} [Fact p.Prime]

theorem c25_RS_proved : C25_RS p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hE4
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := T7D.exists_sylow_frame hs hW hzW
  have hRK : K ⊓ (S : Subgroup G) = R :=
    hR.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hR.1 hRS)
  have hRK' : K' ⊓ (S : Subgroup G) = R' :=
    hR'.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hR'.1 hR'S)
  refine ⟨S, R, R', ⟨mem_RSet_of_isSylow2In hK hR, hR.1, hRS⟩,
    ⟨mem_RSet_of_isSylow2In hK' hR', hR'.1, hR'S⟩, ?_⟩
  intro X hX hXS
  obtain ⟨J, hJ, hXJ⟩ := exists_isSylow2In_of_mem_RSet hX
  by_cases hJK : J = K
  · subst hJK
    left
    have hXle : X ≤ J ⊓ (S : Subgroup G) := le_inf hXJ.1 hXS
    rw [hRK] at hXle
    exact (hXJ.eq_of_le hR.2.1 hR.1 hXle).symm
  by_cases hJK' : J = K'
  · subst hJK'
    right
    have hXle : X ≤ J ⊓ (S : Subgroup G) := le_inf hXJ.1 hXS
    rw [hRK'] at hXle
    exact (hXJ.eq_of_le hR'.2.1 hR'.1 hXle).symm
  exfalso
  have hc : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hWS (mem_RSet_of_isSylow2In hK hR) hRS
  have hXD : X ∈ DSet Ω W := Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hWS hX hXS
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hp hq hΩ hW hK hR hRD
  obtain ⟨σ, hσK, hσR⟩ := T7D.exists_rep hp hq hΩ hW hJ hXJ hXD
  have hcomm : ρ.img * σ.img = σ.img * ρ.img := by
    have := T7D.muGroup_comm_of_E4 hE4 ⟨ρ.img, T7D.rep_img_mem ρ⟩ ⟨σ.img, T7D.rep_img_mem σ⟩
    exact congrArg Subtype.val this
  have hne : ρ.K ≠ σ.K := by
    rw [hρK, hσK]
    exact fun h => hJK h.symm
  have hnbr : σ.K ∈ omegaNbr Ω ρ.K := hc.omega_of_comm ρ σ hne hcomm
  rw [hρK, hσK] at hnbr
  have hperp : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
  rw [hs.perp] at hperp
  rcases hperp with h | h
  · exact hJK h
  · exact hJK' h

end CFSG.ClassicalInvolution.Asc77
