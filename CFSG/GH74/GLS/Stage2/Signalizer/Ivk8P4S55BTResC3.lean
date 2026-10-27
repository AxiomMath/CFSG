module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResC2
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupInner

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
  CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_inner_of_card_outer_le_two {Y : Type*} [Group Y] [Finite Y]
    (hO : Nat.card (Outer Y) ≤ 2) (W : Subgroup (MulAut Y)) (hW4 : Nat.card W = 4) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ inner Y := by
  set f : ↥W →* Outer Y := (QuotientGroup.mk' (inner Y)).comp W.subtype with hf
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hW4] at h1
  have h2 : Nat.card f.range ≤ 2 := (Subgroup.card_le_card_group f.range).trans hO
  have h3 : 2 ≤ Nat.card f.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card f.range * Nat.card f.ker ≤ 2 * 1 := Nat.mul_le_mul h2 (by omega)
    omega
  have hne : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at h3
    omega
  obtain ⟨⟨w, hwk⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨w, w.2, fun h => hw1 (Subtype.ext (Subtype.ext h)), ?_⟩
  have : QuotientGroup.mk' (inner Y) (w : MulAut Y) = 1 := hwk
  exact (QuotientGroup.eq_one_iff _).mp this

theorem exists_inner_of_type {Y : Type} [Group Y] [Finite Y]
    (hY : Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 Y Odd) (W : Subgroup (MulAut Y))
    (hW2 : ∀ w ∈ W, w * w = 1) (hW4 : Nat.card W = 4) : ∃ w ∈ W, w ≠ 1 ∧ w ∈ inner Y := by
  rcases hY with he | ⟨F, _, _, hodd, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    refine exists_inner_of_card_outer_le_two ?_ W hW4
    rw [CFSG.ProperTwoGeneratedCore.BenderFacts.card_outer_eq_two_of_mulEquiv_alternatingGroup
      (by norm_num) (by norm_num) e]
  · set e' := e.trans (IVK.L2.equivPSL F) with he'
    set Φ := CFSG.ComponentClassification.AutL2Facts.autEquiv e' with hΦ
    obtain ⟨_, ⟨w, hwW, rfl⟩, hw1, hwL⟩ :=
      CFSG.ComponentClassification.AutL2Facts.fourgroup_meets_psl
        (CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of_odd_card F hodd)
        (W.map Φ.toMonoidHom)
        (by
          rintro _ ⟨w, hw, rfl⟩
          change Φ w * Φ w = 1
          rw [← map_mul, hW2 w hw, map_one])
        (by rw [Subgroup.card_map_of_injective Φ.injective, hW4])
    refine ⟨w, hwW, fun h => hw1 (by rw [h]; exact map_one _), ?_⟩
    rw [← CFSG.ComponentClassification.AutL2Facts.map_autEquiv_innAut e'] at hwL
    obtain ⟨β, hβ, hβw⟩ := hwL
    rwa [← Φ.injective hβw]

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem exists_U_mem_J (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) :
    ∃ u : ↥H, (u : G) ∈ L52Two.U4 z t ∧ QuotientGroup.mk' (pPrimeCore 2 ↥H) u ≠ 1 ∧
      QuotientGroup.mk' (pPrimeCore 2 ↥H) u ∈ J := by
  obtain ⟨φ, hφ, hφa⟩ := exists_actU hL31 h hd hJ hIJ
  have := hd.u.four.1
  have hsq : ∀ u : ↥(L52Two.U4 z t), u * u = 1 := fun u => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← sq]
    exact elemPow_eq_one_of_isElementaryAbelian (u : G) u.2
  have hW4 : Nat.card φ.range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hd.u.four.2]
  have hW2 : ∀ w ∈ φ.range, w * w = 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← map_mul, hsq, map_one]
  obtain ⟨_, ⟨u, rfl⟩, hw1, hwin⟩ := exists_inner_of_type (quot_type hL31 h hd hJ hIJ) φ.range
    hW2 hW4
  obtain ⟨hN, hφu⟩ := hφa u
  have hUH := U_le_H h hd.u
  have hu2 : (⟨(u : G), hUH u.2⟩ : ↥H) * ⟨(u : G), hUH u.2⟩ = 1 := by
    have h0 : ((u * u : ↥(L52Two.U4 z t)) : G) = 1 := congrArg Subtype.val (hsq u)
    exact Subtype.ext h0
  refine ⟨⟨u, hUH u.2⟩, u.2, ?_, ?_⟩
  · intro h1
    apply hw1
    have h2 := eq_one_of_mk_eq_one hu2 h1
    have h3 : (u : G) = 1 := congrArg Subtype.val h2
    have hu1 : u = 1 := Subtype.ext h3
    rw [hu1, map_one]
  · refine mem_of_actJ_mem_inner hL31 h hd hJ hIJ hN
      (barIn_U_le_centralizer hd ⟨⟨u, hUH u.2⟩, u.2, rfl⟩) ?_ (hφu ▸ hwin)
    rw [← map_mul, hu2, map_one]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
