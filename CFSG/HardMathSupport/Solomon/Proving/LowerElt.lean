module

public import CFSG.HardMathSupport.Solomon.Proving.LowerPair

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance.Alt
open Subgroup

theorem exists_twoLocal_lower_elt {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X B L : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian p B)
    (hL : GLAPComponent p X L) (C : Subgroup G) (hCB : C ≤ B)
    (hCN : C ≤ Subgroup.normalizer (L : Set G))
    (E : Subgroup (barOf p L)) (hE : IsElemAbelian p E)
    (hEZ : E ⊓ Subgroup.center (barOf p L) = ⊥)
    (hCE : ∀ c (hc : c ∈ C), ∀ x ∈ E, barAut p L ⟨c, hCN hc⟩ x = x)
    (hCinn : ∀ c (hc : c ∈ C), barAut p L ⟨c, hCN hc⟩ ∈ innerAut (barOf p L) →
      barAut p L ⟨c, hCN hc⟩ = 1)
    {t : G} (htX : t ∈ X) (htN : t ∈ Subgroup.normalizer (L : Set G))
    (ht1 : barAut p L ⟨t, htN⟩ = 1) (htC : ∀ c ∈ C, c * t = t * c) (ht2 : t ^ 2 = 1)
    (htO : (⟨t, htX⟩ : ↥X) ∉ GLAPPrimeCore p ↥X) :
    ∃ P S : Subgroup ↥X, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card C * Nat.card E ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      P ≤ Subgroup.normalizer (S : Set ↥X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCX : C ≤ X := (hCB.trans hBX)
  have hO : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) :=
    coprime_card_gLAPPrimeCore_aux p ↥X
  set O := GLAPPrimeCore p ↥X with hOdef
  set θ := barTheta p hL.1 hL.2.1 with hθdef
  have hθinj : Function.Injective θ := barTheta_injective p hL.1 hL.2.1
  have conjX : ∀ x : ↥X, ∀ hx : (x : G) ∈ C, ∀ e : barOf p L,
      (QuotientGroup.mk x : ↥X ⧸ O) * θ e * (QuotientGroup.mk x : ↥X ⧸ O)⁻¹ =
        θ (barAut p L ⟨(x : G), hCN hx⟩ e) := by
    intro x hx e
    obtain ⟨x, hxX⟩ := x
    exact conj_barTheta_X hL (hCN hx) hxX e
  have hcommXE : ∀ x : ↥X, ∀ hx : (x : G) ∈ C, ∀ e ∈ E,
      θ e * (QuotientGroup.mk x : ↥X ⧸ O) = (QuotientGroup.mk x : ↥X ⧸ O) * θ e := by
    intro x hx e he
    have h := conjX x hx e
    rw [hCE _ hx e he] at h
    have h2 : θ e * (QuotientGroup.mk x : ↥X ⧸ O) =
        (QuotientGroup.mk x : ↥X ⧸ O) * θ e * (QuotientGroup.mk x : ↥X ⧸ O)⁻¹ *
          (QuotientGroup.mk x : ↥X ⧸ O) := by
      rw [h]
    rw [h2, inv_mul_cancel_right]
  have hCxmem : ∀ y : ↥(C.subgroupOf X), ((y : ↥X) : G) ∈ C :=
    fun y => Subgroup.mem_subgroupOf.1 y.2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(C.subgroupOf X) →* ↥X ⧸ O,
      ∀ y, ψ y = QuotientGroup.mk (y : ↥X) :=
    ⟨(QuotientGroup.mk' O).comp (C.subgroupOf X).subtype, fun y => rfl⟩
  have hpowB : ∀ z ∈ C, z ^ p = 1 := fun z hz => hB.2 z (hCB hz)
  have hkerC : ∀ z : ↥X, z ∈ O → (z : G) ∈ C → z = 1 := by
    intro z hzO hzC
    apply eq_one_of_mem_coprime hp O hO hzO
    apply Subtype.ext
    simpa using hpowB _ hzC
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hψ] at hy
    have hyO : (y : ↥X) ∈ O := (QuotientGroup.eq_one_iff _).1 hy
    exact Subtype.ext (by simpa using hkerC (y : ↥X) hyO (hCxmem y))
  have hCxcomm : IsMulCommutative ↥(C.subgroupOf X) :=
    ⟨⟨fun y z => Subtype.ext (Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact hB.1.is_comm.comm ⟨_, hCB (hCxmem y)⟩ ⟨_, hCB (hCxmem z)⟩ |> congrArg Subtype.val))⟩⟩
  have hCxpow : ∀ y : ↥(C.subgroupOf X), y ^ p = 1 := fun y =>
    Subtype.ext (Subtype.ext (by simpa using hpowB _ (hCxmem y)))
  set Cbar := ψ.range with hCbar
  set Ebar := E.map θ with hEbar
  have hmemC : ∀ g ∈ Cbar, ∃ x : ↥X, (x : G) ∈ C ∧ g = QuotientGroup.mk x := by
    intro g hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hg
    exact ⟨(y : ↥X), hCxmem y, hψ y⟩
  have hCbar_el : IsElemAbelian p Cbar := isElemAbelian_range' ψ hCxcomm hCxpow
  have hEbar_el : IsElemAbelian p Ebar := isElemAbelian_map' θ hE
  have hcomm_CE : Cbar ≤ Subgroup.centralizer (Ebar : Set (↥X ⧸ O)) := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hmemC g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hh
    exact hcommXE x hx e he
  have hdisj : Cbar ⊓ Ebar = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgC, hgE⟩
    obtain ⟨x, hx, rfl⟩ := hmemC _ hgC
    obtain ⟨e, he, hex⟩ := Subgroup.mem_map.1 hgE
    have hconj : barAut p L ⟨(x : G), hCN hx⟩ = MulAut.conj e := by
      ext w
      show barAut p L ⟨(x : G), hCN hx⟩ w = e * w * e⁻¹
      have h := conjX x hx w
      rw [← hex] at h
      apply hθinj
      rw [← h]
      simp [map_mul, map_inv]
    have hinn : barAut p L ⟨(x : G), hCN hx⟩ ∈ innerAut (barOf p L) := ⟨e, hconj.symm⟩
    have h1 := hCinn (x : G) hx hinn
    have hcen : e ∈ Subgroup.center (barOf p L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw : e * w * e⁻¹ = w := by
        simpa using congrArg (fun φ : MulAut (barOf p L) => φ w) (hconj.symm.trans h1)
      have h3 : e * w = w * e := by simpa using congrArg (· * e) hw
      exact h3.symm
    have he1 : e = 1 := by
      have hm : e ∈ E ⊓ Subgroup.center (barOf p L) := ⟨he, hcen⟩
      rw [hEZ] at hm
      exact Subgroup.mem_bot.1 hm
    rw [he1, map_one] at hex
    exact Subgroup.mem_bot.2 hex.symm
  have hCardC : Nat.card Cbar = Nat.card C := by
    show Nat.card ψ.range = Nat.card C
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv)
  have hCardE : Nat.card Ebar = Nat.card E := Subgroup.card_map_of_injective hθinj
  obtain ⟨hJc, hJcard⟩ := isElemAbelian_sup_card hcomm_CE hdisj hCbar_el hEbar_el
  set xt : ↥X ⧸ O := QuotientGroup.mk' O ⟨t, htX⟩ with hxtdef
  have htL : t ∈ centB p (Subgroup.zpowers t) L :=
    mem_centB.2 ⟨htN, Subgroup.mem_zpowers t, ht1⟩
  have hxtE : ∀ g ∈ Ebar, Commute xt g := by
    intro g hg
    obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hg
    exact commute_theta_of_centB hL htL htX e
  have hxtC : ∀ g ∈ Cbar, Commute xt g := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hmemC g hg
    have hxy : (⟨t, htX⟩ : ↥X) * y = y * ⟨t, htX⟩ := Subtype.ext (htC _ hy).symm
    show xt * QuotientGroup.mk y = QuotientGroup.mk y * xt
    rw [hxtdef, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  have hPx : (Cbar ⊔ Ebar) ≤ Subgroup.centralizer ({xt} : Set (↥X ⧸ O)) :=
    sup_le
      (fun g hg => Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (hxtC g hg).eq)
      (fun g hg => Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (hxtE g hg).eq)
  have hPT : (Cbar ⊔ Ebar) ≤ Subgroup.centralizer ((Subgroup.zpowers xt : Subgroup (↥X ⧸ O)) : Set (↥X ⧸ O)) := by
    intro g hg
    have hg' : Commute xt g := Subgroup.mem_centralizer_iff.1 (hPx hg) xt (Set.mem_singleton xt)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hg'.zpow_left k).eq
  have hPnorm := hPT.trans (Subgroup.centralizer_le_normalizer _)
  have hxt2 : xt ^ 2 = 1 := by
    have h2 : (⟨t, htX⟩ : ↥X) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [hxtdef, ← map_pow, h2, map_one]
  have hxtne : xt ≠ 1 := by
    intro h
    apply htO
    rw [hxtdef] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  have hTne : Subgroup.zpowers xt ≠ ⊥ := by
    intro hbot
    apply hxtne
    have hm : xt ∈ Subgroup.zpowers xt := Subgroup.mem_zpowers xt
    rw [hbot, Subgroup.mem_bot] at hm
    exact hm
  have hTp : IsPGroup 2 (Subgroup.zpowers xt) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, orderOf_eq_prime hxt2 hxtne]; norm_num⟩
  obtain ⟨P, S, hPc, hPp, hPcard, hS1, hS2, hPS⟩ :=
    exists_lift_twoLocal_of_le_normalizer hp hp2 O hO (Cbar ⊔ Ebar) (Subgroup.zpowers xt)
      hJc ⟨hTne, hTp⟩ hPnorm
  refine ⟨P, S, hPc, hPp, ?_, hS1, hS2, hPS⟩
  rw [hPcard, hJcard, hCardC, hCardE]

end CFSG.HardMathSupport.Solomon.Proving
