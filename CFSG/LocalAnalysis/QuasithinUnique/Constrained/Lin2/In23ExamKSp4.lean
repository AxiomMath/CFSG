module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4Core
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour

@[expose] def Sp4OddMultiplierTrivial : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], 4 ≤ Nat.card F →
    ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → ∀ η : E →* StatedSp 2 F,
      Function.Surjective η → η.ker ≤ Subgroup.center E → Odd (Nat.card η.ker) → η.ker = ⊥

section Positive

variable {G : Type} [Group G] [Finite G] {K B B' P R : Subgroup G} {m : ℕ}

theorem examSp4 (hodd : Sp4OddMultiplierTrivial) : ExamSp4 := by
  intro G _ _ K B B' P R m h ⟨f, hf2, hmodel⟩
  have hmodel' := hmodel
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFfin : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hcp : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have habs := h.toAbs
  have hperf : Group.IsPerfect ↥K := h.quasisimple.1
  have hJ : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .PSp 2 2 f :=
    Or.inl ⟨by decide, hmodel⟩
  have hcover : ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E →
      ∀ η : E →* (↥K ⧸ Subgroup.center ↥K), Function.Surjective η → η.ker ≤ Subgroup.center E →
        IsPGroup 2 η.ker → η.ker = ⊥ := by
    intro E _ _ hp η hη hC h2
    have := hp
    exact (SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial
      η hη hC h2 hf2 hJ).1
  have hZ : ∀ z ∈ Subgroup.center ↥K, z ^ 2 = 1 → z = 1 :=
    center_no_involution_of_cover hperf (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hcover
  let ε : StatedProj (StatedSp 2 F) ≃* StatedSp 2 F :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot 2)).trans
      QuotientGroup.quotientBot
  let ψ : (↥K ⧸ Subgroup.center ↥K) ≃* StatedSp 2 F := e.trans ε
  let θ : ↥K →* StatedSp 2 F := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  obtain ⟨-, ⟨S, hSU⟩, hUcard, -⟩ :=
    SymplecticFour.unique_symplectic_four_Sylow_center (K := F) (Nat.card F) rfl
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent 2 F) ⊤ :=
    hSU ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨R₀, A₀, hR₀U, hnorm, hcardR, hnea, -, -, -⟩ :=
    habs.exists_Rprime θ hθsurj hθker.le (unipotent 2 F) hU
  have hReq : R₀ = unipotent 2 F := Sp4Core.eq_unipotent_of_normalized hF4 hR₀U hnorm hnea
  have hm : m = f := by
    rw [hReq, hUcard, hF, ← pow_mul] at hcardR
    have := Nat.pow_right_injective (le_refl 2) hcardR
    omega
  have hodd' : Odd (Nat.card θ.ker) := by
    rw [hθker]
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 2
      (even_iff_two_dvd.mp hev)
    have hz2 : ((z : ↥K)) ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    have hz1 : (z : ↥K) = 1 := hZ z z.2 hz2
    have hz1' : z = 1 := Subtype.ext hz1
    rw [hz1', orderOf_one] at hz
    omega
  have hbot : θ.ker = ⊥ := hodd F hF4 ↥K hperf θ hθsurj hθker.le hodd'
  rw [hθker] at hbot
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hbot
  let eK : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥K))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  refine ⟨F, ‹Field F›, hFfin, ?_, ?_⟩
  · rw [hFcard, hm]
  · exact ⟨eK.trans e⟩

end Positive

end CFSG.QuasithinUnique.Lin2
