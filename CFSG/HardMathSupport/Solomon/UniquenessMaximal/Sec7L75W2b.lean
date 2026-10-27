module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X3a
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75W2d

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

private theorem layer_inf_le_aux {K N : Subgroup G} (hcov : Covers3 N K) :
    GLAPLayer 3 (K ⊓ N) ⊓ GLAPPrimeCoreOf 3 N ≤ GLAPPrimeCoreOf 3 K := by
  set H := K ⊓ N with hH
  have hJH : GLAPLayer 3 H ≤ H := glaPLayer_le 3 H
  have hQ : GLAPLayer 3 H ⊓ GLAPPrimeCoreOf 3 N ≤ GLAPPrimeCoreOf 3 H := by
    refine Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three (inf_le_left.trans hJH) ?_ ?_
    · intro x hx
      exact Sec7.inf_normalizer_le_normalizer_inf _ _
        ⟨Sec7.le_normalizer_glaPLayer 3 H hx,
          le_normalizer_glaPPrimeCoreOf 3 N (Subgroup.mem_inf.1 hx).2⟩
    · intro hd
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three N
        (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  rw [hH, Sec7.glaPPrimeCoreOf_inf_eq hcov] at hQ
  exact hQ.trans inf_le_right

omit [Finite G] in
private theorem not_dvd_card_barX {N P : Subgroup G} (hPN : P ≤ N)
    (h : ¬ 3 ∣ Nat.card P) : ¬ 3 ∣ Nat.card (barX 3 N P) := by
  intro hd
  have h2 : Nat.card (barX 3 N P) ∣ Nat.card (P.subgroupOf N) := Subgroup.card_map_dvd _ _
  have h3 : Nat.card (P.subgroupOf N) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  exact h (h3 ▸ hd.trans h2)

namespace Ctx75

variable {B N K : Subgroup G} {x : G}

theorem A_cent_of (c : Ctx75 B N K x)
    (hL34 : IsLThreeFour (↥(barX 3 N (GLAPLayer 3 (K ⊓ N))) ⧸
      GLAPPrimeCore 3 ↥(barX 3 N (GLAPLayer 3 (K ⊓ N)))))
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N (GLAPLayer 3 (K ⊓ N)))) :
    barX 3 N (centralizerQuot B K) ≤
      Subgroup.centralizer (barX 3 N (GLAPLayer 3 (K ⊓ N)) : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
  set K0 := GLAPLayer 3 (K ⊓ N) with hK0
  set O := GLAPPrimeCoreOf 3 K with hO
  have hK0K : K0 ≤ K := (glaPLayer_le 3 _).trans inf_le_left
  have hK0N : K0 ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hK0O : K0 ≤ Subgroup.normalizer ((K0 ⊓ O : Subgroup G) : Set G) := fun g hg =>
    Sec7.inf_normalizer_le_normalizer_inf K0 O
      ⟨Subgroup.le_normalizer hg, Sec7.layer_le_normalizerO K N hg⟩
  intro y hy
  obtain ⟨a, haN, haA, rfl⟩ := exists_mem_of_mem_barX hy
  obtain ⟨haB, hacomm⟩ := comm_of_mem_centralizerQuot' c.hf.normalizes haA
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  have hne : ¬ barX 3 N K0 ≤ GLAPPrimeCoreOf 3 (barX 3 N K0) := by
    intro hle
    have htop : GLAPPrimeCore 3 ↥(barX 3 N K0) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨y', hy', e⟩ := hle y.2
      have : y' = y := Subtype.ext e
      subst this
      exact hy'
    have hsub : Subsingleton (↥(barX 3 N K0) ⧸ GLAPPrimeCore 3 ↥(barX 3 N K0)) := by
      refine ⟨fun p q => ?_⟩
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
      exact QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _)
    have h1 := card_eq_of_isLThreeFour hL34
    rw [Nat.card_of_subsingleton 1] at h1
    exact absurd h1 (by norm_num)
  have hcomm : ∀ z ∈ barX 3 N K0, mkN N a haN * z * (mkN N a haN)⁻¹ * z⁻¹ ∈
      GLAPPrimeCoreOf 3 (barX 3 N K0) := by
    intro z hz
    obtain ⟨k0, hk0N, hk0K0, rfl⟩ := exists_mem_of_mem_barX hz
    have hk0K : k0 ∈ K := hK0K hk0K0
    have hak : a * k0 * a⁻¹ * k0⁻¹ ∈ K0 := by
      have h1 : a * k0 * a⁻¹ ∈ K0 :=
        (Subgroup.mem_normalizer_iff.1 (c.B_le_normalizer_K0 haB) k0).1 hk0K0
      exact K0.mul_mem h1 (K0.inv_mem hk0K0)
    have hmem : mkN N (a * k0 * a⁻¹ * k0⁻¹)
        (N.mul_mem (N.mul_mem (N.mul_mem haN hk0N) (N.inv_mem haN)) (N.inv_mem hk0N)) ∈
        barX 3 N (K0 ⊓ O) := mkN_mem_barX _ ⟨hak, hacomm k0 hk0K⟩
    have hle : barX 3 N (K0 ⊓ O) ≤ GLAPPrimeCoreOf 3 (barX 3 N K0) := by
      refine Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three
        (barX_mono 3 inf_le_left) (barX_le_normalizer hK0O) ?_
      refine not_dvd_card_barX (inf_le_left.trans hK0N) fun hd => ?_
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
        (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
    exact hle hmem
  have hcen := Sec7.centralizes_of_commutator_le_proper (J := barX 3 N K0)
    (P := GLAPPrimeCoreOf 3 (barX 3 N K0)) (c := mkN N a haN) hq (Subgroup.map_subtype_le _)
    (le_normalizer_glaPPrimeCoreOf 3 _) hne hcomm
  exact (hcen z hz).symm

theorem mem_centralizerQuot_of_centralizes (c : Ctx75 B N K x) {b : G} (hb : b ∈ B)
    (h : mkN N b (c.hBN hb) ∈ Subgroup.centralizer (barX 3 N (GLAPLayer 3 (K ⊓ N)) :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N))) : b ∈ centralizerQuot B K := by
  refine Subgroup.subset_closure ⟨hb, fun k hk => ?_⟩
  set K0 := GLAPLayer 3 (K ⊓ N) with hK0
  set O := GLAPPrimeCoreOf 3 K with hO
  have hK0K : K0 ≤ K := (glaPLayer_le 3 _).trans inf_le_left
  have hK0N : K0 ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hBN := c.hBN hb
  have hBO : B ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_glaPPrimeCoreOf_of_le' c.hf.normalizes
  have hk' : k ∈ ((K0 ⊔ O : Subgroup G) : Set G) := c.layer_data.2.2 hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K0 O (Sec7.layer_le_normalizerO K N)] at hk'
  obtain ⟨k0, hk0, o, ho, hko⟩ := hk'
  have hko : k0 * o = k := hko
  subst hko
  have hk0K : k0 ∈ K := hK0K hk0
  have hbk0 : b * k0 * b⁻¹ * k0⁻¹ ∈ K0 := by
    have h1 : b * k0 * b⁻¹ ∈ K0 :=
      (Subgroup.mem_normalizer_iff.1 (c.B_le_normalizer_K0 hb) k0).1 hk0
    exact K0.mul_mem h1 (K0.inv_mem hk0)
  have hbk0N : b * k0 * b⁻¹ * k0⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem hBN (hK0N hk0)) (N.inv_mem hBN)) (N.inv_mem (hK0N hk0))
  have hb1 : b * k0 * b⁻¹ * k0⁻¹ ∈ O := by
    have h1 : mkN N (b * k0 * b⁻¹ * k0⁻¹) hbk0N = 1 := by
      have h2 := Subgroup.mem_centralizer_iff.1 h (mkN N k0 (hK0N hk0)) (mkN_mem_barX _ hk0)
      show mkN N b hBN * mkN N k0 (hK0N hk0) * (mkN N b hBN)⁻¹ * (mkN N k0 (hK0N hk0))⁻¹ = 1
      rw [← h2]
      group
    have h2 : b * k0 * b⁻¹ * k0⁻¹ ∈ GLAPPrimeCoreOf 3 N :=
      ⟨⟨_, hbk0N⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
    exact layer_inf_le_aux c.cov ⟨hbk0, h2⟩
  have e : b * (k0 * o) * b⁻¹ * (k0 * o)⁻¹ =
      (b * k0 * b⁻¹ * k0⁻¹) * (k0 * (b * o * b⁻¹ * o⁻¹) * k0⁻¹) := by group
  rw [e]
  refine O.mul_mem hb1 ?_
  have h3 : b * o * b⁻¹ * o⁻¹ ∈ O :=
    O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBO hb) o).1 ho) (O.inv_mem ho)
  exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 K hk0K) _).1 h3

end Ctx75

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
