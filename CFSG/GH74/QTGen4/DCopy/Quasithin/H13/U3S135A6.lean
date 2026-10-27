module

public import CFSG.Quasithin.H13.U3S135A6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135Gen

public section

namespace CFSG.Quasithin.H13.U3

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 (P6 InW4 act4f e0123 e45 InW1)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem setting4_not_centralizer_le_F4 (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    (S : A6.Setting4 G T L V) : ¬ centralizer ({S.z} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v, hv, hv1, hvM⟩ := exists_centralizer_not_le_F4 h12213 S.h13
    (hyp1223_of_fsu S.h13 S.T_le_NL S.maximal S.fsu S.irr)
  obtain ⟨l, hl, hlv⟩ := setting4_exists_conj_eq_z S hv hv1
  exact not_centralizer_le_of_conj (le_normalizer hl) hlv hvM

theorem setting134_exists_v1_F4 (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    (S : A6.Setting134 G T L V) (hc2 : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2) :
    ∃ v ∈ fsuV1 T V, v ∉ centralizer (L : Set G) ∧
      ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv, hv1, hvM⟩ := exists_centralizer_not_le_F4 h12213 S.h13
    (hyp1223_of_fsu S.h13 S.T_le_NL S.maximal S.fsu S.irr)
  have huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → L ⊔ T ≤ M →
      M = normalizer (L : Set G) := fun M h1 h2 => S.uniqueM.2 M ⟨h1, h2⟩

  have hvL : v ∉ centralizer (L : Set G) := by
    intro hvC
    apply hvM
    have hvX : v ∈ V ⊓ centralizer (L : Set G) := ⟨hv, hvC⟩
    have hov : orderOf v = 2 := orderOf_eq_prime (sq_of_irr S.irr hv) hv1
    have hXv : zpowers v = V ⊓ centralizer (L : Set G) :=
      eq_of_le_of_card_ge (zpowers_le.2 hvX) (le_of_eq (by rw [hc2, Nat.card_zpowers, hov]))
    have hX2 : IsPGroup 2 ↥(V ⊓ centralizer (L : Set G)) :=
      IsPGroup.of_card (n := 1) (by rw [hc2, pow_one])
    have hLT : L ⊔ T ≤ normalizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
      sup_le (fun l hl => mem_normalizer_inf (S.frame.L_le hl)
          (mem_normalizer_centralizer (le_normalizer hl)))
        (fun t ht => mem_normalizer_inf (S.frame.T_le ht)
          (mem_normalizer_centralizer (S.T_le_NL ht)))
    refine (centralizer_le_normalizer_zpowers v).trans ?_
    rw [hXv]
    exact normalizer_le_of_uniq S.zv hX2 hLT huniq

  have hx0 : ∑ i, Multiplicative.toAdd (S.frame.ψ ⟨v, hv⟩ : P6) i = 0 :=
    G6.mem_coreMod.1 (S.frame.ψ ⟨v, hv⟩).2
  have hx1 : (S.frame.ψ ⟨v, hv⟩ : P6) ≠ 1 := by
    intro h
    apply hv1
    have h1 : S.frame.ψ ⟨v, hv⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hxΩ : (S.frame.ψ ⟨v, hv⟩ : P6) ≠ G6.allOnes 6 := by
    intro h
    apply hvL
    rw [mem_centralizer_iff]
    intro l hl
    have hc : l * v * l⁻¹ = v := (S.conj_eq_iff ⟨l, S.frame.L_le hl⟩ ⟨v, hv⟩).2
      (Subtype.ext (by rw [G6.coreAct_coe, h, A6.permAct_allOnes]))
    calc l * v = l * v * l⁻¹ * l := by group
      _ = v * l := by rw [hc]

  obtain ⟨a, b, c, d, hab, hcd, he⟩ := core_trans _ hx0 hx1 hxΩ
  obtain ⟨g, hgL, hρ⟩ := (S.frame.image_L _).2 (swap_mul_swap_mem hab hcd)
  have hwV : (g : G) * v * (g : G)⁻¹ ∈ V := (mem_normalizer_iff.mp g.2 v).mp hv
  have hψw : (S.frame.ψ ⟨(g : G) * v * (g : G)⁻¹, hwV⟩ : P6) =
      G6.permAct 6 (swap a b * swap c d) (S.frame.ψ ⟨v, hv⟩) := by
    rw [S.psi_conj g ⟨v, hv⟩, hρ, G6.coreAct_coe]
  refine ⟨(g : G) * v * (g : G)⁻¹, S.mem_V1_iff.2 ⟨hwV, ?_⟩, fun hw => hvL ?_,
    not_centralizer_le_of_conj (le_normalizer hgL) rfl hvM⟩
  · rw [hψw]
    rcases he with he | he <;> rw [he]
    · exact inW1_e0123
    · exact inW1_e45
  · have h1 := (mem_normalizer_iff.mp
      (mem_normalizer_centralizer (le_normalizer (inv_mem hgL))) _).1 hw
    rwa [show (g : G)⁻¹ * ((g : G) * v * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = v by group] at h1

end CFSG.Quasithin.H13.U3
