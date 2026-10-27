module

public import CFSG.Quasithin.H13.A6S1357
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1355
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1356

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_centralizer_V_of_odd_F4 (h13315 : Stmt13_3_15_F4) {y : G}
    (hy : y ∈ Subgroup.centralizer (S.V3 : Set G)) (hodd : ∃ m : ℕ, Odd m ∧ y ^ m = 1) :
    y ∈ Subgroup.centralizer (V : Set G) := by
  have hyN := S.centralizer_V3_le_F4 h13315 hy
  refine (S.rho_eq_one_iff ⟨y, hyN⟩).1 ?_
  rcases fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨y, hyN⟩) hy) with h | h
  · exact h
  · exfalso
    obtain ⟨m, ⟨k, rfl⟩, hm⟩ := hodd
    have h1 : S.frame.ρ (⟨y, hyN⟩ ^ (2 * k + 1)) = 1 := by
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ (2 * k + 1) = 1 :=
        Subtype.ext (by simpa using hm)
      rw [this, map_one]
    rw [map_pow, h, pow_succ, pow_mul, t_facts.2.2.2, one_pow, one_mul] at h1
    exact t_facts.2.2.1 h1

theorem coreIn_le_pCoreOf_F4
    (h13315 : Stmt13_3_15_F4) {H : Subgroup G} (hH : H ∈ S.Hz) :
    coreIn (centralizerMod (fsuV1 T V) H S.V3) H ≤ pCoreOf 2 H :=
  coreIn_le_pCoreOf_of S.uniqueM (le_sup_right.trans hH.1.1) hH.2.2
    (S.charTwo_of_inH ⟨le_sup_right.trans hH.1.1, hH.1.2⟩)
    (hH.2.1.trans S.G1_le_centralizer_V1) (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V)
    (S.V1_le_V2.trans S.V2_le_V3)
    ((Subgroup.centralizer_le_normalizer (V : Set G)).trans S.NV_le_M) S.pCoreOf_L_le_T
    (fun _ hy _ hl => S.comm_mem_pCoreOf hy hl)
    (fun _ _ hy3 hodd => S.mem_centralizer_V_of_odd_F4 h13315 hy3 hodd)

theorem weak_e_two_F4 (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two_F4)
    (h13315 : Stmt13_3_15_F4) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) :
    ∃ hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G), ∀ (a b : G)
      (ha : a ∈ conjSub g⁻¹ V) (hb : b ∈ conjSub g⁻¹ V), S.frame.ρ ⟨a, hN ha⟩ = 1 ∨
        S.frame.ρ ⟨b, hN hb⟩ = 1 ∨ S.frame.ρ ⟨a, hN ha⟩ = S.frame.ρ ⟨b, hN hb⟩ := by
  obtain ⟨hN, hR, hquad⟩ := S.weak_e_core hg h1 h2
  refine ⟨hN, fun a b ha hb => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨ha1, hb1, hab⟩ := hne

  have key : ∃ (c d : G) (hc : c ∈ conjSub g⁻¹ V) (hd : d ∈ conjSub g⁻¹ V),
      S.frame.ρ ⟨c, hN hc⟩ = swap 4 5 ∧ S.frame.ρ ⟨d, hN hd⟩ ≠ 1 ∧
        S.frame.ρ ⟨d, hN hd⟩ ≠ swap 4 5 := by
    rcases quad_R8 _ (hR a ha) _ (hR b hb) ha1 hb1 hab (hquad a b ha hb) with h | h | h
    · exact ⟨a, b, ha, hb, h, hb1, fun h' => hab (h.trans h'.symm)⟩
    · exact ⟨b, a, hb, ha, h, ha1, fun h' => hab (h'.trans h.symm)⟩
    · refine ⟨a * b, a, (conjSub g⁻¹ V).mul_mem ha hb, ha, ?_, ha1, fun h' => ?_⟩
      · rw [← h, ← map_mul]
        rfl
      · apply hb1
        rw [h'] at h
        exact mul_left_cancel (h.trans (mul_one _).symm)
  obtain ⟨c, d, hc, hd, hct, hd1, hdt⟩ := key
  obtain ⟨π, hπC, hπ⟩ := synWit _ (hR d hd) hd1 hdt
  obtain ⟨l, -, hl⟩ := (S.frame.image_L π).2 (Perm.mem_alternatingGroup.2 (C3_sign π hπC))

  have hV2 : S.V2 ≤ V ⊓ conjSub (g * l)⁻¹ V := by
    intro w hw
    obtain ⟨hwV, hwW2⟩ := S.mem_pre.1 hw
    refine Subgroup.mem_inf.2 ⟨hwV, ?_⟩
    obtain ⟨x, hx, hxe⟩ := hπ _ hwW2
    set v : ↥V := S.frame.ψ.symm ⟨x, hx⟩
    have hdv : (d : G) * v * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hN hd) v).mp v.2

    have heq : (l : G) * w * (l : G)⁻¹ = v * d * (v : G)⁻¹ * d⁻¹ := by
      have h1' := S.psi_conj l ⟨w, hwV⟩
      rw [hl] at h1'
      have h2' : S.frame.ψ ⟨v * d * (v : G)⁻¹ * d⁻¹, by
          have e : (v : G) * d * (v : G)⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
          rw [e]
          exact V.mul_mem v.2 (V.inv_mem hdv)⟩ =
          S.frame.ψ v * (act4 (S.frame.ρ ⟨d, hN hd⟩) (S.frame.ψ v))⁻¹ := by
        rw [← S.psi_conj ⟨d, hN hd⟩ v, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have h3' : S.frame.ψ ⟨(l : G) * w * (l : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp l.2 w).mp hwV⟩ = S.frame.ψ ⟨v * d * (v : G)⁻¹ * d⁻¹,
          by
            have e : (v : G) * d * (v : G)⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
            rw [e]
            exact V.mul_mem v.2 (V.inv_mem hdv)⟩ := by
        rw [h1', h2', MulEquiv.apply_symm_apply]
        exact Subtype.ext hxe
      exact congrArg Subtype.val (S.frame.ψ.injective h3')
    have hmemA : (l : G) * w * (l : G)⁻¹ ∈ conjSub g⁻¹ V := by
      rw [heq]
      exact (h1 (Subgroup.commutator_mem_commutator v.2 hd)).2
    rw [mem_conjSub, inv_inv] at hmemA ⊢
    have e : g * l * w * (g * l)⁻¹ = g * ((l : G) * w * (l : G)⁻¹) * g⁻¹ := by group
    rw [e]
    exact hmemA

  have hcN : (l : G)⁻¹ * c * l ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ l.2) (hN hc)) l.2
  have hc' : (l : G)⁻¹ * c * l ∈ conjSub (g * l)⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have hcA := hc
    rw [mem_conjSub, inv_inv] at hcA
    have e : g * l * ((l : G)⁻¹ * c * l) * (g * l)⁻¹ = g * c * g⁻¹ := by group
    rw [e]
    exact hcA
  have hρc' : S.frame.ρ ⟨(l : G)⁻¹ * c * l, hcN⟩ = π⁻¹ * swap 4 5 * π := by
    have e : (⟨(l : G)⁻¹ * c * l, hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        l⁻¹ * ⟨c, hN hc⟩ * l := rfl
    rw [e, map_mul, map_mul, map_inv, hct, hl]
  have hsign : Perm.sign (π⁻¹ * swap 4 5 * π) = -1 := by
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, t_facts.2.1, C3_sign π hπC]
    simp
  rcases S.lemma13_5_6_three_F4 hNS h1356two h13315 (g * l) hV2 with h0 | ⟨-, -, hauto⟩
  ·
    have hcC : (l : G)⁻¹ * c * l ∈ Subgroup.centralizer (V : Set G) := by
      have : conjSub (g * l)⁻¹ V ≤ Subgroup.centralizer (V : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h0
      exact this hc'
    have h1c := (S.rho_eq_one_iff ⟨_, hcN⟩).2 hcC
    rw [hρc'] at h1c
    rw [h1c, Perm.sign_one] at hsign
    exact absurd hsign (by decide)
  ·
    have hmem : conjAct V ⟨_, hcN⟩ ∈ autOn (conjSub (g * l)⁻¹ V) V := ⟨⟨_, hcN⟩, hc', rfl⟩
    obtain ⟨x, hxL2, hx⟩ := hauto hmem
    have hxL : (x : G) ∈ L := ((oTwoRes_le _).trans inf_le_left) hxL2
    have hρx := S.rho_eq_of_conjAct_eq hx
    have hev := (S.frame.image_L _).1 ⟨x, hxL, rfl⟩
    rw [hρx, hρc', Perm.mem_alternatingGroup] at hev
    rw [hev] at hsign
    exact absurd hsign (by decide)

theorem weak_e_card_F4 (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two_F4)
    (h13315 : Stmt13_3_15_F4) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) :
    Nat.card (conjSub g⁻¹ V) ≤
      2 * Nat.card ↥(conjSub g⁻¹ V ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨hN, hσ⟩ := S.weak_e_two_F4 hNS h1356two h13315 hg h1 h2
  set A := conjSub g⁻¹ V
  let φ : ↥A →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hN)
  have hker : ∀ a : ↥A, φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := fun a =>
    S.rho_eq_one_iff _
  have hrange : Nat.card φ.range ≤ 2 := by
    by_cases hex : ∃ a : ↥A, φ a ≠ 1
    · obtain ⟨a₀, ha₀⟩ := hex
      have hsub : (φ.range : Set (Perm (Fin 6))) ⊆ {1, φ a₀} := by
        rintro _ ⟨b, rfl⟩
        rcases hσ a₀ b a₀.2 b.2 with h | h | h
        · exact absurd h ha₀
        · exact Or.inl h
        · exact Or.inr h.symm
      calc Nat.card φ.range = Nat.card ((φ.range : Set (Perm (Fin 6)))) := rfl
        _ ≤ Nat.card (({1, φ a₀} : Set (Perm (Fin 6)))) :=
          Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
    · push Not at hex
      have : φ.range = ⊥ := by
        ext σ
        constructor
        · rintro ⟨b, rfl⟩
          exact hex b
        · intro h
          rw [Subgroup.mem_bot] at h
          exact ⟨1, by rw [h, map_one]⟩
      rw [this, Subgroup.card_bot]
      norm_num
  have hkcard : Nat.card φ.ker = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_congr ⟨fun a => ⟨a.1, a.1.2, (hker a.1).1 a.2⟩,
      fun b => ⟨⟨b.1, b.2.1⟩, (hker ⟨b.1, b.2.1⟩).2 b.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  have h := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hkcard] at h
  calc Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * Nat.card φ.range :=
        h.symm
    _ ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring

theorem rho_one_or_t_F4 (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two_F4)
    (h13315 : Stmt13_3_15_F4) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) (h3 : ⁅conjSub g⁻¹ S.V3, V⁆ ≤ fsuV1 T V) :
    ∃ hN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G), ∀ (a : G) (ha : a ∈ conjSub g⁻¹ V),
      S.frame.ρ ⟨a, hN ha⟩ = 1 ∨ S.frame.ρ ⟨a, hN ha⟩ = swap 4 5 := by
  obtain ⟨hN, hR, -⟩ := S.weak_e_core hg h1 h2
  refine ⟨hN, fun a ha => ?_⟩
  by_contra hne
  push Not at hne
  have h4 := S.card_inf_centralizer_le_four (hN ha) (hR a ha) hne.1 hne.2 ha
  have hginv : g⁻¹ ∈ S.G1 := S.G1.inv_mem hg
  have hgN1 : g ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.G1_le_normalizer_V1 hg
  have h1' : ⁅V, conjSub g⁻¹⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹⁻¹ V := by
    rw [inv_inv]
    have := conjSub_mono g h1
    rw [← conjSub_commutator, conjSub_inv_conjSub, conjSub_inf, conjSub_inv_conjSub,
      Subgroup.commutator_comm] at this
    rwa [inf_comm]
  have h2' : ⁅S.V3, conjSub g⁻¹⁻¹ V⁆ ≤ fsuV1 T V := by
    rw [inv_inv]
    have := conjSub_mono g h3
    rwa [← conjSub_commutator, conjSub_inv_conjSub, A5.conjSub_self_of_mem hgN1] at this
  have hF1 := S.weak_e_card_F4 hNS h1356two h13315 hginv h1' h2'
  rw [inv_inv, A5.card_conjSub', S.card_V] at hF1
  have htrans : Nat.card ↥(conjSub g V ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G)) := by
    have e : conjSub g⁻¹ (conjSub g V ⊓ Subgroup.centralizer (V : Set G)) =
        V ⊓ Subgroup.centralizer (conjSub g⁻¹ V : Set G) := by
      rw [conjSub_inf, conjSub_conjSub_inv, conjSub_centralizer]
    rw [← e, A5.card_conjSub']
  rw [htrans] at hF1
  omega

theorem weak_e_F4 (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two_F4)
    (h13315 : Stmt13_3_15_F4) {g : G}
    (hg : g ∈ S.G1) (h1 : ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V)
    (h2 : ⁅S.V3, conjSub g⁻¹ V⁆ ≤ fsuV1 T V) (h3 : ⁅conjSub g⁻¹ S.V3, V⁆ ≤ fsuV1 T V) :
    ⁅S.V3, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ S.V3, V⁆ = ⊥ := by
  have hginv : g⁻¹ ∈ S.G1 := S.G1.inv_mem hg
  have hgN1 : g ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.G1_le_normalizer_V1 hg
  have h1' : ⁅V, conjSub g⁻¹⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹⁻¹ V := by
    rw [inv_inv]
    have := conjSub_mono g h1
    rw [← conjSub_commutator, conjSub_inv_conjSub, conjSub_inf, conjSub_inv_conjSub,
      Subgroup.commutator_comm] at this
    rwa [inf_comm]
  have h2' : ⁅S.V3, conjSub g⁻¹⁻¹ V⁆ ≤ fsuV1 T V := by
    rw [inv_inv]
    have := conjSub_mono g h3
    rwa [← conjSub_commutator, conjSub_inv_conjSub, A5.conjSub_self_of_mem hgN1] at this
  have h3' : ⁅conjSub g⁻¹⁻¹ S.V3, V⁆ ≤ fsuV1 T V := by
    rw [inv_inv]
    have := conjSub_mono g h2
    rwa [← conjSub_commutator, conjSub_inv_conjSub, A5.conjSub_self_of_mem hgN1] at this

  have hcen : ∀ k : G, k ∈ S.G1 → ⁅V, conjSub k⁻¹ V⁆ ≤ V ⊓ conjSub k⁻¹ V →
      ⁅S.V3, conjSub k⁻¹ V⁆ ≤ fsuV1 T V → ⁅conjSub k⁻¹ S.V3, V⁆ ≤ fsuV1 T V →
      conjSub k⁻¹ V ≤ Subgroup.centralizer (S.V3 : Set G) := by
    intro k hk h1k h2k h3k a ha
    obtain ⟨hN, hσ⟩ := S.rho_one_or_t_F4 hNS h1356two h13315 hk h1k h2k h3k
    refine S.centralizer_of_fixW3 (x := ⟨a, hN ha⟩) ?_
    rcases hσ a ha with h | h <;> rw [h]
    · exact fun x hx => act4f_one x hx.1
    · exact t_facts.1
  have hA := hcen g hg h1 h2 h3
  have hA' : conjSub g V ≤ Subgroup.centralizer (S.V3 : Set G) := by
    have := hcen g⁻¹ hginv h1' h2' h3'
    rwa [inv_inv] at this
  constructor
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hA
  · have h0 : ⁅conjSub g V, S.V3⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hA'
    have := congrArg (conjSub g⁻¹) h0
    rw [← conjSub_commutator, conjSub_conjSub_inv, conjSub_bot, Subgroup.commutator_comm] at this
    exact this

theorem hypF91_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz) :
    HypF91 T V L (fsuV1 T V) S.V3 H :=
  hypF91_of S.h13.sylow S.h13.faithful S.h13.qtke.2.1 S.T_le_NL S.reduced S.cT S.uniqueM
    S.card_V1 S.V1_lt_V3 S.V3_le_V S.T_le_NV1 hH.1 (hH.2.1.trans S.G1_le_centralizer_V1)
    hH.2.2 (S.coreIn_le_pCoreOf_F4 h13315 hH) S.L1T_le_NV3 S.irred_V3
    (fun _ hx => S.G1_inf_G3_le_F4 h13315 ⟨hH.2.1 hx.1, hx.2⟩)
    (fun _ hg h1 h2 h3 => S.weak_e_F4 hNS h1356two h13315 (hH.2.1 hg) h1 h2 h3)

end Setting4

end CFSG.Quasithin.H13.A6
