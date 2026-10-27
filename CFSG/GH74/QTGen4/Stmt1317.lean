module

public import CFSG.GH74.QTGen4.Statements
public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.GH74.QTGen4.Perfect.Final

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin

theorem pCore_two_quotient_eq_bot_1317 {H : Type} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore 2 H with hN
  set M : Subgroup H := (CFSG.pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMp : IsPGroup 2 M := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hMN : M ≤ N := le_sSup ⟨inferInstance, hMp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hMN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem isSolvable_of_normal_ne_top {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : K ∈ cComp X) (P : Subgroup ↥K) [P.Normal] (hP : P ≠ ⊤) :
    Group.IsSolvable ↥P := by
  rcases normal_eq_top_or_map_le_solvRad hK P with h | h
  · exact absurd h hP
  · have hmem : ∀ x : ↥P, (x.1.1 : G) ∈ solvRad K := fun x =>
      h (Subgroup.mem_map.2 ⟨x.1, x.2, rfl⟩)
    let f : ↥P →* ↥(solvRad K) :=
      { toFun := fun x => ⟨x.1.1, hmem x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b hab
      have hval := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext hval)
    have : Group.IsSolvable ↥(solvRad K) := solvRad_isSolvable K
    exact Group.isSolvable_of_isSolvable_injective hf

theorem isQuasisimple_quot_of_cComp {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : K ∈ cComp X) (hcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 20160) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hPK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  have hPQ : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hnt : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have htop : CFSG.pCore 2 ↥K = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).1 hx
    have hp : IsPGroup 2 ↥K := by
      intro g
      have hg : g ∈ CFSG.pCore 2 ↥K := by
        rw [htop]
        exact Subgroup.mem_top g
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨g, hg⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := IsPGroup.isNilpotent hp
    exact not_isSolvable_of_mem_cComp hK inferInstance
  have := hnt
  have hO2 : CFSG.pCore 2 (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := pCore_two_quotient_eq_bot_1317
  have hsol : ∀ N : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), N.Normal → N ≠ ⊤ →
      Group.IsSolvable ↥N := by
    intro N hN hNtop
    have hMtop : N.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ≠ ⊤ := by
      intro h
      apply hNtop
      rw [eq_top_iff]
      intro y _
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
      have hk : k ∈ N.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
        rw [h]
        exact Subgroup.mem_top k
      exact hk
    have := isSolvable_of_normal_ne_top hK (N.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
      hMtop
    let f : ↥(N.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) →* ↥N :=
      { toFun := fun x => ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥K) x.1, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
      exact ⟨⟨k, hy⟩, rfl⟩
    exact Group.isSolvable_of_surjective hf
  exact isQuasisimple_of_perfect_card_dvd_20160 (Group.isPerfect_def.1 hPQ) hO2 hsol hcard

theorem stmt13_1_7_GH : Stmt13_1_7_GH :=
  fun G _ _ hc T _ _ hqtke hT _ K hK => by
    obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
    have hKc : K ∈ cComp (K ⊔ (S : Subgroup G)) := mem_cComp_iff.2 hK.1.2.1
    have hInH : CFSG.Quasithin.InH (S : Subgroup G) (K ⊔ (S : Subgroup G)) :=
      ⟨le_sup_right, hK.1.2.2.2⟩
    have hd := modO2_dvd_of_inH hc.1 hqtke.2.1 S hInH (le_sup_left : K ≤ K ⊔ (S : Subgroup G))
    exact isQuasisimple_quot_of_cComp hKc hd

end CFSG.GH74.QTGen4
