module

public import CFSG.HardMathSupport.Solomon.Proving.CentralizerLift
public import CFSG.HardMathSupport.Solomon.Proving.LowerFixed

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance.Alt
open Subgroup

theorem exists_elemAbelian_centralizer_fixed {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (_hp2 : p ≠ 2) {X B L : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian p B)
    (hL : GLAPComponent p X L) (C : Subgroup G) (hCB : C ≤ B)
    (hCN : C ≤ Subgroup.normalizer (L : Set G))
    (E : Subgroup (barOf p L)) (hE : IsElemAbelian p E)
    (hEZ : E ⊓ Subgroup.center (barOf p L) = ⊥)
    (hCE : ∀ c (hc : c ∈ C), ∀ x ∈ E, barAut p L ⟨c, hCN hc⟩ x = x)
    (hCinn : ∀ c (hc : c ∈ C), barAut p L ⟨c, hCN hc⟩ ∈ innerAut (barOf p L) →
      barAut p L ⟨c, hCN hc⟩ = 1) :
    ∃ P : Subgroup ↥X, IsElemAbelian p P ∧ Nat.card P = Nat.card C * Nat.card E ∧
      P ≤ Subgroup.centralizer ((C.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hCX : C ≤ X := hCB.trans hBX
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
  have hCbar_el : IsElemAbelian p Cbar :=
    isElemAbelian_range' ψ hCxcomm hCxpow
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
  have hQmap : (C.subgroupOf X).map (QuotientGroup.mk' O) = Cbar := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
      exact MonoidHom.mem_range.2 ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, by rw [hψ]; rfl⟩
    · intro hg
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hg
      exact Subgroup.mem_map.2 ⟨(y : ↥X), Subgroup.mem_subgroupOf.2 (hCxmem y), by rw [hψ]; rfl⟩
  have hCC : Cbar ≤ Subgroup.centralizer (Cbar : Set (↥X ⧸ O)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hCbar_el.1.is_comm.comm ⟨h, hh⟩ ⟨g, hg⟩)
  have hEC : Ebar ≤ Subgroup.centralizer (Cbar : Set (↥X ⧸ O)) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.1 (hcomm_CE hh) e he).symm
  have hQJ : Cbar ⊔ Ebar ≤ Subgroup.centralizer
      (((C.subgroupOf X).map (QuotientGroup.mk' O) : Subgroup (↥X ⧸ O)) : Set (↥X ⧸ O)) := by
    rw [hQmap]
    exact sup_le hCC hEC
  have hQp : IsPGroup p (C.subgroupOf X) :=
    isPGroup_of_pow_eq_one hp (fun x hx => by
      simpa using congrArg Subtype.val (hCxpow ⟨x, hx⟩))
  obtain ⟨P, hPE, hPcard, hPc⟩ :=
    exists_elemAbelian_centralizer_lift hp O hO (C.subgroupOf X) hQp (Cbar ⊔ Ebar) hJc hQJ
  refine ⟨P, hPE, ?_, hPc⟩
  rw [hPcard, hJcard, hCardC, hCardE]

end CFSG.HardMathSupport.Solomon.Proving
