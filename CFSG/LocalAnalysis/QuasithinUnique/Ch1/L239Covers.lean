module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM23
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239.Covers

theorem exists_noncomm_of_simple_card {Q : Type*} [Group Q] (hs : IsSimpleGroup Q) {N : ℕ}
    (hN : Nat.card Q = N) (h2 : 2 ∣ N) (h3 : 2 < N) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : IsMulCommutative Q := ⟨⟨fun a b => hc a b⟩⟩
  have hp : (Nat.card Q).Prime := Group.is_simple_iff_prime_card.mp hs
  rw [hN] at hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2) with h | h <;> omega

theorem center_eq_bot_of_exp2 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.IsQuasisimple ↥L) {C : Type} [Group C]
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* C) (hs : IsSimpleGroup C) (hnc : ∃ a b : C, a * b ≠ b * a)
    (hexp2 : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* C), Function.Surjective π' →
      (∀ z, π' z = 1 → z ∈ Subgroup.center E') → (∀ z, π' z = 1 → z * z = 1) →
      commutator E' = ⊤ → π'.ker = ⊥) :
    Subgroup.center ↥L = ⊥ := by
  have hs' : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
  have hnc' : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hpc : CFSG.pCore 2 ↥L = Subgroup.center ↥L :=
    Id2519.pCore_eq_center_of_simple_quotient hL hs' hnc'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* C := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = CFSG.pCore 2 ↥L := by
    ext z
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk z) = 1 ↔ z ∈ CFSG.pCore 2 ↥L
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff z
  have hz : ∀ z, π z = 1 → z ∈ Subgroup.center ↥L := fun z hz1 => by
    have : z ∈ CFSG.pCore 2 ↥L := hker ▸ (MonoidHom.mem_ker.mpr hz1)
    rw [← hpc]
    exact this
  have hp2 : IsPGroup 2 ↥π.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hbot := ker_eq_bot_of_exp2 hexp2 π hz hp2 hL.1.commutator_eq_top hπ
  rw [← hpc, ← hker]
  exact hbot

theorem l239Covers
    : L239Covers := by
  intro G _ _ L hL hcase
  rcases hcase with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hfin := CFSG.Sporadic.Mathieu.fam_m11_simplicity
    have hs : IsSimpleGroup ↥NativeSporadic.M11 := hfin.2.2
    exact center_eq_bot_of_exp2 hL e hs
      (exists_noncomm_of_simple_card hs CFSG.Sporadic.Mathieu.card_M11 (by norm_num)
        (by norm_num))
      (fun E' _ _ π' h1 h2 h3 h4 => m11_cover_exp2 π' h1 h2 h3 h4)
  · have hfin := CFSG.Sporadic.Mathieu.fam_m23_simplicity
    have hs : IsSimpleGroup ↥NativeSporadic.M23 := hfin.2.2
    exact center_eq_bot_of_exp2 hL e hs
      (exists_noncomm_of_simple_card hs CFSG.Sporadic.Schreier.m23_card (by norm_num)
        (by norm_num))
      (fun E' _ _ π' h1 h2 h3 h4 => m23_cover_exp2 π' h1 h2 h3 h4)

end CFSG.QuasithinUnique.Vol2Native.L239
