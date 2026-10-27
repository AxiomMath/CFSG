module

public import CFSG.GH74.GLS.Stage1.Thm4.L98a

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

section Bar

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_Oz_iff {c : ↥(Cz z)} : (c : G) ∈ Oz z ↔ c ∈ pPrimeCore 2 ↥(Cz z) := by
  constructor
  · rintro ⟨y, hy, hyc⟩
    have : y = c := Subtype.ext hyc
    rwa [this] at hy
  · intro h
    exact ⟨c, h, rfl⟩

omit [Finite G] in
theorem Oz_conj {c : G} (hc : c ∈ Cz z) {x : G} (hx : x ∈ Oz z) : c * x * c⁻¹ ∈ Oz z := by
  obtain ⟨y, hy, rfl⟩ := hx
  have := (pPrimeCore_normal (p := 2) (G := ↥(Cz z))).conj_mem y hy ⟨c, hc⟩
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, this, rfl⟩

theorem card_Oz_coprime : Nat.Coprime 2 (Nat.card (Oz z)) := by
  unfold Oz pPrimeCoreOf
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact pPrimeCore_coprime_card

omit [Finite G] in
theorem mem_barOf_iff {K : Subgroup G} {y : CentralizerBar z} :
    y ∈ barOf z K ↔ ∃ c : ↥(Cz z), (c : G) ∈ K ∧ toBar z c = y := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

end Bar

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem Oz_inf_K : Oz z ⊓ K = pPrimeCoreOf 2 K := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxO, hxK⟩ := hx
    have hnorm : ((Oz z ⊓ K).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ Oz z ⊓ K := hn
      refine ⟨?_, (g * n * g⁻¹).2⟩
      have := Oz_conj (h.K_le g.2) hn'.1
      simpa using this
    have hcop : Nat.Coprime 2 (Nat.card ((Oz z ⊓ K).subgroupOf K)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Oz z ⊓ K ≤ K)).toEquiv]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) card_Oz_coprime
    have hle : (Oz z ⊓ K).subgroupOf K ≤ pPrimeCore 2 ↥K := le_sSup ⟨hnorm, hcop⟩
    exact ⟨⟨x, hxK⟩, hle ⟨hxO, hxK⟩, rfl⟩
  · intro x hx
    exact ⟨h.pPrimeCoreOf_le_Oz hx, (Subgroup.map_subtype_le _) hx⟩

end Ctx98

section Hat

variable {G : Type} [Group G] [Finite G] {z : G} {K : Subgroup G}

noncomputable def phiK (hK : K ≤ Cz z) : ↥K →* ↥(barOf z K) where
  toFun x := ⟨toBar z ⟨(x : G), hK x.2⟩, ⟨⟨(x : G), hK x.2⟩, x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (toBar z)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (toBar z) ⟨(x : G), hK x.2⟩ ⟨(y : G), hK y.2⟩

omit [Finite G] in
theorem phiK_surjective (hK : K ≤ Cz z) : Function.Surjective (phiK hK) := by
  rintro ⟨_, c, hc, rfl⟩
  exact ⟨⟨(c : G), hc⟩, rfl⟩

theorem mem_ker_phiK (hK : K ≤ Cz z) {x : ↥K} :
    x ∈ (phiK hK).ker ↔ ((x : G) ∈ Oz z) := by
  rw [MonoidHom.mem_ker, mem_Oz_iff (c := ⟨(x : G), hK x.2⟩), ← QuotientGroup.eq_one_iff]
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    exact this
  · intro h1
    exact Subtype.ext h1

end Hat

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem phiK_ker : (phiK h.K_le).ker = pPrimeCore 2 ↥K := by
  ext x
  rw [mem_ker_phiK]
  constructor
  · intro hx
    have : (x : G) ∈ pPrimeCoreOf 2 K := by
      rw [← h.Oz_inf_K]; exact ⟨hx, x.2⟩
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact h.pPrimeCoreOf_le_Oz ⟨x, hx, rfl⟩

noncomputable def hatEquivBar : HatT K ≃* ↥(barOf z K) :=
  (QuotientGroup.quotientMulEquivOfEq (h.phiK_ker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (phiK h.K_le) (phiK_surjective h.K_le))

end Ctx98

end CFSG.GH74.GLS.Stage1.Thm4
