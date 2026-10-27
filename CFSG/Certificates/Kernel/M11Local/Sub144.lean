module

public import CFSG.Certificates.Kernel.M11Local.Group
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.KC.M11L

open Equiv CFSG.KC.Misc.Clos CFSG.GH74.KGroups CFSG.Blueprint Certificates.ONanSmallM11
  CFSG.Sporadic.Mathieu

theorem sub144_tail_stable {W : Subgroup (Perm (Fin 11))} (hW : Nat.card W = 144)
    (hreg : ∀ i : Fin 11, 2 ≤ (i : ℕ) → ∃ e ∈ W, e 2 = i) :
    ∀ w ∈ W, ∀ i : Fin 11, 2 ≤ (i : ℕ) → 2 ≤ ((w i : Fin 11) : ℕ) := by
  classical
  let T : Set (Fin 11) := ↑(Finset.univ.filter fun i : Fin 11 => 2 ≤ (i : ℕ))
  have hmemT : ∀ i : Fin 11, i ∈ T ↔ 2 ≤ (i : ℕ) := by
    intro i
    simp [T]
  have hTsub : T ⊆ MulAction.orbit W (2 : Fin 11) := by
    intro i hi
    obtain ⟨e, he, rfl⟩ := hreg i ((hmemT i).1 hi)
    exact ⟨⟨e, he⟩, rfl⟩
  have hTcard : T.ncard = 9 := by
    rw [Set.ncard_coe_finset]
    decide
  have hle : (MulAction.orbit W (2 : Fin 11)).ncard ≤ 11 := by
    have h := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit W (2 : Fin 11)))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hge : 9 ≤ (MulAction.orbit W (2 : Fin 11)).ncard := by
    rw [← hTcard]
    exact Set.ncard_le_ncard hTsub
  have hdvd : (MulAction.orbit W (2 : Fin 11)).ncard ∣ 144 := by
    rw [← MulAction.index_stabilizer, ← hW]
    exact Subgroup.index_dvd_card _
  have h9 : (MulAction.orbit W (2 : Fin 11)).ncard = 9 := by
    obtain ⟨n, hn⟩ : ∃ n, (MulAction.orbit W (2 : Fin 11)).ncard = n := ⟨_, rfl⟩
    rw [hn] at hle hge hdvd ⊢
    interval_cases n <;> first | rfl | norm_num at hdvd
  have hEq : T = MulAction.orbit W (2 : Fin 11) :=
    Set.eq_of_subset_of_ncard_le hTsub (by rw [h9, hTcard]) (Set.toFinite _)
  intro w hw i hi
  obtain ⟨e, he, rfl⟩ := hreg i hi
  have hmem : (⟨w * e, W.mul_mem hw he⟩ : W) • (2 : Fin 11) ∈ MulAction.orbit W (2 : Fin 11) :=
    MulAction.mem_orbit _ _
  rw [← hEq, hmemT] at hmem
  exact hmem

theorem sub144_duad {W : Subgroup (Perm (Fin 11))} (hW : Nat.card W = 144)
    (hreg : ∀ i : Fin 11, 2 ≤ (i : ℕ) → ∃ e ∈ W, e 2 = i) {w : Perm (Fin 11)} (hw : w ∈ W) :
    (w 0 = 0 ∧ w 1 = 1) ∨ (w 0 = 1 ∧ w 1 = 0) := by
  have hT := sub144_tail_stable hW hreg
  have hlt2 : ∀ j : Fin 11, ¬ 2 ≤ (j : ℕ) → j = 0 ∨ j = 1 := by decide
  have hsmall : ∀ j : Fin 11, ¬ 2 ≤ (j : ℕ) → ¬ 2 ≤ ((w j : Fin 11) : ℕ) := by
    intro j hj hwj
    apply hj
    have h := hT w⁻¹ (W.inv_mem hw) (w j) hwj
    rwa [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply] at h
  have hn01 : w 0 ≠ w 1 := fun h => absurd (w.injective h) (by decide)
  rcases hlt2 _ (hsmall 0 (by decide)) with h0 | h0 <;>
    rcases hlt2 _ (hsmall 1 (by decide)) with h1 | h1
  · exact absurd (h0.trans h1.symm) hn01
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (h0.trans h1.symm) hn01

theorem sub144_pCore_of_map {A B : Type} [Group A] [Group B] (f : A ≃* B) (U : Subgroup A)
    (h0 : CFSG.pCore 2 ↥(U.map f.toMonoidHom) = ⊥) : CFSG.pCore 2 ↥U = ⊥ := by
  let e : ↥U ≃* ↥(U.map f.toMonoidHom) := U.equivMapOfInjective f.toMonoidHom f.injective
  have h := CFSG.pCore_map_iso 2 e
  rw [← h] at h0
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have h2 : e.toMonoidHom y ∈ (CFSG.pCore 2 ↥U).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hy
  rw [h0, Subgroup.mem_bot] at h2
  apply e.injective
  rw [map_one]
  exact h2

theorem sub144_pCore_of_le (hx : m11x ∈ NativeSporadic.M11)
    (hy : m11y ∈ NativeSporadic.M11) (hs : m11s ∈ NativeSporadic.M11) (hnodup : m11E.Nodup)
    (hmul : ∀ a ∈ m11E, ∀ b ∈ m11E, a * b ∈ m11E) (hinv : ∀ a ∈ m11E, a⁻¹ ∈ m11E)
    (hxy : m11x * m11y = m11y * m11x) (hx1 : m11x ≠ 1)
    (hfix : ∀ e ∈ m11E, e ≠ 1 → e 0 = 0 ∧ e 1 = 1 ∧ ∀ i : Fin 11, 2 ≤ (i : ℕ) → e i ≠ i)
    (hreg : ∀ i : Fin 11, 2 ≤ (i : ℕ) → ∃ e ∈ m11E, e 2 = i)
    (hs8 : m11s ^ 8 = 1) (hs4 : m11s ^ 4 ≠ 1) (hsx : m11s * m11x * m11s⁻¹ ∈ m11E)
    (hsy : m11s * m11y * m11s⁻¹ ∈ m11E) {U : Subgroup ↥NativeSporadic.M11}
    (hU : Nat.card U = 144) (hEU : eT ≤ U) : CFSG.pCore 2 ↥U = ⊥ := by
  have hmemT : ∀ k : ↥NativeSporadic.M11, k ∈ eT ↔ (k : Perm (Fin 11)) ∈ m11E := fun k =>
    (Subgroup.mem_subgroupOf).trans (mem_eSub_iff hmul hinv)
  have heM : ∀ e ∈ m11E, e ∈ NativeSporadic.M11 := fun e he =>
    eSub_le hx hy ((mem_eSub_iff hmul hinv).2 he)
  let W : Subgroup (Perm (Fin 11)) := U.map NativeSporadic.M11.subtype
  have hW : Nat.card W = 144 := by
    rw [← hU]
    exact (Nat.card_congr (U.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hregW : ∀ i : Fin 11, 2 ≤ (i : ℕ) → ∃ e ∈ W, e 2 = i := by
    intro i hi
    obtain ⟨e, he, he2⟩ := hreg i hi
    exact ⟨e, Subgroup.mem_map.2 ⟨⟨e, heM e he⟩, hEU ((hmemT _).2 he), rfl⟩, he2⟩
  have hN : ∀ u ∈ U, u ∈ Subgroup.normalizer
      ((eT : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) := by
    intro u hu
    rw [normalizer_eT_eq hx hy hs hnodup hmul hinv hx1 hfix hs8 hs4 hsx hsy,
      mem_stabilizer_duad_iff]
    exact sub144_duad hW hregW (Subgroup.mem_map_of_mem _ hu)
  let EU : Subgroup U := eT.subgroupOf U
  have hEUn : EU.Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hN (g : ↥NativeSporadic.M11) g.2) _).1 hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hEUcard : Nat.card EU = 9 := by
    rw [← card_eT hx hy hnodup hmul hinv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEU).toEquiv
  have hdisj : Disjoint (CFSG.pCore 2 ↥U) EU := by
    rw [Subgroup.disjoint_def]
    intro x hx hxE
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥U)) ⟨x, hx⟩
    have h2k : x ^ (2 ^ k) = 1 := by
      have h := congrArg (fun z : CFSG.pCore 2 ↥U => (z : U)) hk
      simpa using h
    have h9 : x ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := ↥EU) (x := ⟨x, hxE⟩)
      rw [hEUcard] at h
      have := congrArg Subtype.val h
      simpa using this
    have hg : Nat.gcd (2 ^ k) 9 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have h1 : x ^ Nat.gcd (2 ^ k) 9 = 1 := pow_gcd_eq_one.mpr ⟨h2k, h9⟩
    rwa [hg, pow_one] at h1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hxO
  have hcomm : ∀ c ∈ m11E,
      ((x : ↥NativeSporadic.M11) : Perm (Fin 11)) * c = c * ((x : ↥NativeSporadic.M11) :
        Perm (Fin 11)) := by
    intro c hc
    have hcU : (⟨c, heM c hc⟩ : ↥NativeSporadic.M11) ∈ U := hEU ((hmemT _).2 hc)
    have hcE : (⟨⟨c, heM c hc⟩, hcU⟩ : U) ∈ EU :=
      Subgroup.mem_subgroupOf.2 ((hmemT _).2 hc)
    have h := Subgroup.commute_of_normal_of_disjoint _ _ inferInstance hEUn hdisj x _ hxO hcE
    have h' := congrArg (fun z : U => ((z : ↥NativeSporadic.M11) : Perm (Fin 11))) h.eq
    simpa using h'
  have hxE : ((x : ↥NativeSporadic.M11) : Perm (Fin 11)) ∈ m11E :=
    centralizer_le hx hy hmul hinv hxy hx1 hfix hreg _ (x : ↥NativeSporadic.M11).2
      (hcomm m11x (by simp [m11E])) (hcomm m11y (by simp [m11E]))
  exact Subgroup.disjoint_def.1 hdisj hxO (Subgroup.mem_subgroupOf.2 ((hmemT _).2 hxE))

theorem sub144_sylow (K : Subgroup ↥NativeSporadic.M11)
    (hK : Nat.card K = 9) : ∃ S : Sylow 3 ↥NativeSporadic.M11, S.toSubgroup = K := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨⟨K, IsPGroup.of_card (n := 2) (by rw [hK]; norm_num), ?_⟩, rfl⟩
  intro R hR hle
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card ↥NativeSporadic.M11 := Subgroup.card_subgroup_dvd_card R
  rw [hm, M11.card_M11] at hdvd
  have hm2 : m ≤ 2 := by
    by_contra hc
    have h27 : 3 ^ 3 ∣ 7920 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h27
  have hR9 : Nat.card R ≤ 9 := by
    rw [hm]
    calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 9 := by norm_num
  have hcard : Nat.card R ≤ Nat.card K := by omega
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem m11_sub144_pCore_of_check {wx wy ws : List Bool}
    (h : m11K (pcode m11x) (pcode m11y) (pcode m11s) (pcode m11gA) (pcode m11gB) wx wy ws =
      true) :
    ∀ U : Subgroup ↥NativeSporadic.M11, Nat.card U = 144 → CFSG.pCore 2 ↥U = ⊥ := by
  obtain ⟨hwx, hwy, hws, hnodup, hinv, hmul, -, -, hxy, hx1, -, hfix, hreg, -, hs8, hs4,
    hsx, hsy, -, -⟩ := m11K_sound h
  have hx : m11x ∈ NativeSporadic.M11 := hwx ▸ evalW_mem wx
  have hy : m11y ∈ NativeSporadic.M11 := hwy ▸ evalW_mem wy
  have hs : m11s ∈ NativeSporadic.M11 := hws ▸ evalW_mem ws
  intro U hU
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨K0, hK0⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) (by rw [hU]; norm_num)
  have hQcard : Nat.card (K0.map U.subtype) = 9 := by
    have h := Nat.card_congr (K0.equivMapOfInjective U.subtype (fun a b h => Subtype.ext h)).toEquiv
    rw [← h, hK0]
    norm_num
  have hQU : ∀ q ∈ K0.map U.subtype, q ∈ U := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Subgroup.mem_map.mp hq
    exact k.2
  obtain ⟨SQ, hSQ⟩ := sub144_sylow (K0.map U.subtype) hQcard
  obtain ⟨SE, hSE⟩ := sub144_sylow eT (card_eT hx hy hnodup hmul hinv)
  have : Finite (Sylow 3 ↥NativeSporadic.M11) :=
    Finite.of_injective
      (fun S : Sylow 3 ↥NativeSporadic.M11 => (S : Subgroup ↥NativeSporadic.M11))
      (fun S T h => Sylow.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M11 SQ SE
  let f : ↥NativeSporadic.M11 ≃* ↥NativeSporadic.M11 := MulAut.conj g
  have hle : eT ≤ U.map f.toMonoidHom := by
    intro x hxE
    rw [← hSE] at hxE
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxE
    obtain ⟨s, hs', hsx'⟩ := hxE
    rw [hSQ] at hs'
    exact ⟨s, hQU s hs', hsx'⟩
  have hU' : Nat.card (U.map f.toMonoidHom) = 144 := by
    rw [← hU]
    exact (Nat.card_congr (U.equivMapOfInjective f.toMonoidHom f.injective).toEquiv).symm
  exact sub144_pCore_of_map f U (sub144_pCore_of_le hx hy hs hnodup hmul hinv hxy hx1 hfix hreg
    hs8 hs4 hsx hsy hU' hle)

end CFSG.KC.M11L

end
