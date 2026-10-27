module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Trans
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Glauberman

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

@[expose] def Step53' {G : Type} [Group G] (p : ℕ) (H P : Subgroup G) (g : G) (X Y : Subgroup G) :
    Prop :=
  g ∈ P ∧ g ∉ Op p H ∧ X ≤ Op p H ∧ IsChiefFactorIn H X Y ∧
    ⁅⁅X, zpowers g⁆, zpowers g⁆ ≤ Y ∧ ¬ ⁅X, zpowers g⁆ ≤ Y ∧
    (∃ h ∈ H, ∃ J : Subgroup G, J = Subgroup.closure {g, h * g * h⁻¹} ∧ J ≤ nclIn H (zpowers g) ∧
      ∃ N : Subgroup G, N ≤ J ∧ J ⊓ CV H X Y ≤ N ∧ ∃ _ : (N.subgroupOf J).Normal,
        HasSL2Model (↥J ⧸ N.subgroupOf J)
          (fun q => (∃ n : ℕ, 1 ≤ n ∧ q = p ^ n) ∨ (p = 3 ∧ q = 5))) ∧
    ¬ barIn H (zpowers g) ≤ centralizer ((layer (HBar H) : Set (HBar H)))


theorem lemma5_3_core {G : Type} [Group G] [Finite G] {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
    {z : G} {H P : Subgroup G} (hctx : Ctx51 k z S T Tstar p H P) (hnot : ¬ Concl51 k S p H P)
    (hL52 : L52 k S T Tstar p H P) : ∃ (g : G) (X Y : Subgroup G), Step53' p H P g X Y := by
  have hp : p.Prime := hctx.prime
  have hpf : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hctx.odd
  obtain ⟨hPH, hPp, -, -⟩ := hctx.maxi.1
  obtain ⟨hOP, -, hO22, -⟩ := hL52
  have hι : Function.Injective H.subtype := Subtype.val_injective
  have hOp : Op p H = (pCore p ↥H).map H.subtype := rfl
  have hF : generalizedFitting ↥H = pCore p ↥H := by
    have h1 : Fs H = Op p H := hctx.fstar
    have h2 : (generalizedFitting ↥H).map H.subtype = (pCore p ↥H).map H.subtype := h1
    exact (map_inj' H.subtype hι).mp h2
  set SH : Subgroup ↥H := P.subgroupOf H with hSH
  have hSHp : IsPGroup p ↥SH := by
    intro y
    obtain ⟨k, hk⟩ := hPp ⟨(y : G), y.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hTSH : pCore p ↥H ≤ SH := by
    intro t ht
    have : (t : G) ∈ Op p H := Subgroup.mem_map_of_mem _ ht
    exact hOP this
  have hkey : SH.map H.subtype = P := by
    rw [hSH, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hPH
  have hTn : (pCore p ↥H).Normal := CFSG.pCore_normal
  have hTp : IsPGroup p ↥(pCore p ↥H) := CFSG.pCore_isPGroup
  rcases glauberman_kinfty_thm ↥H p hp SH hSHp hTSH hF with ⟨hn1, hn2⟩ |
    ⟨g, hgS, A, hAT, hcrit, X, Y, hXn, hYn, hYX, hmin, hXA, hq, hn⟩
  ·
    exfalso
    apply hnot
    left
    have hkinf : kInfty P = (kInfty SH).map H.subtype := by
      rw [← hkey]; exact kInfty_map' H.subtype hι SH
    have hH : H ≤ normalizer (((kInfty SH).map H.subtype : Subgroup G) : Set G) := by
      have := (map_mem_normalizer_iff H.subtype hι (Q := ⊤) (B := kInfty SH)).mpr
        (normalizer_top_of_normal hn1)
      rwa [Subgroup.map_top, Subgroup.range_subtype] at this
    rw [hkinf]
    exact hH
  · have hYXlt : Y < X := by
      refine lt_of_le_of_ne hYX fun h => hn ?_
      exact (Subgroup.commutator_le_left X (zpowers g)).trans h.ge
    have hc : IsChiefPair X Y := ⟨hXn, hYn, hYXlt, hmin⟩
    have hXT : X ≤ pCore p ↥H := hXA.trans hAT
    have hTnil : Group.IsNilpotent ↥(pCore p ↥H) := hTp.isNilpotent
    have hgT : g ∉ pCore p ↥H := by
      intro hgT
      apply hn
      refine (Subgroup.commutator_mono_right ((Subgroup.zpowers_le).mpr hgT)).trans ?_
      exact comm_le_of_chief_nilp hTnil hTn hXT hc
    have hgp : IsPGroup p ↥(zpowers g) := hSHp.to_le ((Subgroup.zpowers_le).mpr hgS)
    have hq' : ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y := fun x hx =>
      hq (Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers g)) (Subgroup.mem_zpowers g))
    have hn' : ∃ x ∈ X, ⁅x, g⁆ ∉ Y := by
      by_contra hcon
      push Not at hcon
      exact hn ((comm_zpowers_le_iff hYn).mpr hcon)
    obtain ⟨m, hS⟩ := prop110_M hp2 hc (hTp.to_le hXT) hgp hq' hn'
    have hzp : zpowers (g : G) = (zpowers g).map H.subtype := (MonoidHom.map_zpowers H.subtype g).symm
    refine ⟨(g : G), X.map H.subtype, Y.map H.subtype, ?_, ?_, ?_, isChiefFactorIn_map H hc, ?_, ?_,
      step53b_of_sl2quot H hc g m hS, ?_⟩
    · exact Subgroup.mem_subgroupOf.mp hgS
    · intro hgO
      rw [hOp] at hgO
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hgO
      have : t = g := hι hte
      exact hgT (this ▸ ht)
    · rw [hOp]; exact Subgroup.map_mono hXT
    · rw [hzp, map_commutator' H.subtype, map_commutator' H.subtype]
      exact Subgroup.map_mono hq
    · rw [hzp, map_commutator' H.subtype, map_le_map_iff' H.subtype hι]
      exact hn
    · intro hc8
      have hπ : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :=
        QuotientGroup.mk'_surjective _
      have hFcent : ∀ y ∈ pCore 2 (↥H ⧸ pPrimeCore 2 ↥H),
          ⁅y, (g : ↥H ⧸ pPrimeCore 2 ↥H)⁆ = 1 := by
        intro y hy
        obtain ⟨y₀, rfl⟩ := hπ y
        have hy₀ : y₀ ∈ pPrimePCore 2 ↥H := hy
        have h1 : (y₀ : G) ∈ O22Of H := Subgroup.mem_map_of_mem _ hy₀
        have h2 : ⁅(y₀ : G), (g : G)⁆ ∈ pPrimeCoreOf 2 H :=
          hO22 (Subgroup.commutator_mem_commutator h1 (Subgroup.mem_subgroupOf.mp hgS))
        obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp h2
        have hw' : w = ⁅y₀, g⁆ := by
          apply hι
          rw [hwe]
          simp [commutatorElement_def]
        rw [hw'] at hw
        change (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ⁅y₀, g⁆ = 1
        exact (QuotientGroup.eq_one_iff _).mpr hw
      have hEcent : ∀ y ∈ layer (↥H ⧸ pPrimeCore 2 ↥H),
          ⁅y, (g : ↥H ⧸ pPrimeCore 2 ↥H)⁆ = 1 := by
        intro y hy
        have hg1 : (g : ↥H ⧸ pPrimeCore 2 ↥H) ∈ barIn H (zpowers (g : G)) :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _))
        have := (Subgroup.mem_centralizer_iff.mp (hc8 hg1)) y hy
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact this
      have hgO : g ∈ pPrimeCore 2 ↥H := fstar_central_trivial hp2 hgp hFcent hEcent
      have hOn : (pPrimeCore 2 ↥H).Normal := CFSG.pPrimeCore_normal
      have hJO : closure ({g, m * g * m⁻¹} : Set ↥H) ≤ pPrimeCore 2 ↥H := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact hgO
        · exact hOn.conj_mem g hgO m
      have heven := sl2Quot_even hp2 hS
      have hdvd := Subgroup.card_dvd_of_le hJO
      have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥H)
      have h2 : 2 ∣ Nat.card (pPrimeCore 2 ↥H) := heven.trans hdvd
      exact absurd (Nat.dvd_gcd (dvd_refl 2) h2) (by
        rw [hcop]; decide)

theorem lemma5_3_thm : Lemma5_3 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hctx hnot hL52 => lemma5_3_core hctx hnot hL52

end CFSG.GH74.GLS.Stage2.Signalizer.L53
