module

public import CFSG.HardMathSupport.Solomon.Proving.LiftTwoLocalNormalizer
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance.Alt
open Subgroup

theorem conj_barTheta_X {G : Type*} [Group G] [Finite G] {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L)
    {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G)) (hcX : c ∈ X) (x : barOf p L) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩ *
        barTheta p hL.1 hL.2.1 x *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩)⁻¹ =
      barTheta p hL.1 hL.2.1 (barAut p L ⟨c, hc⟩ x) := by
  induction x using QuotientGroup.induction_on with
  | H ℓ =>
    have key : Subgroup.inclusion hL.1 (L.normalizerMonoidHom ⟨c, hc⟩ ℓ) =
        ⟨c, hcX⟩ * Subgroup.inclusion hL.1 ℓ * ⟨c, hcX⟩⁻¹ := by
      apply Subtype.ext
      simp
    rw [barAut_mk, barTheta_mk, barTheta_mk, key]
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem isElemAbelian_map' {p : ℕ} {K N : Type*} [Group K] [Group N] {E : Subgroup K}
    (f : K →* N) (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_range' {p : ℕ} {K N : Type*} [Group K] [Group N] (f : K →* N)
    (hK : IsMulCommutative K) (hKp : ∀ x : K, x ^ p = 1) : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hxa⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hyb⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hK.is_comm.comm x y]
  · intro z hz
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hz
    rw [← map_pow, hKp x, map_one]

theorem eq_one_of_mem_coprime {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    (O : Subgroup H) (hO : Nat.Coprime p (Nat.card O)) {x : H} (hxO : x ∈ O) (hx : x ^ p = 1) :
    x = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have h1 : orderOf x = p := orderOf_eq_prime hx hne
  have h2 : orderOf (⟨x, hxO⟩ : O) = p := by
    rw [← Subgroup.orderOf_coe]
    exact h1
  have h3 : p ∣ Nat.card O := h2 ▸ orderOf_dvd_natCard (⟨x, hxO⟩ : O)
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hO h3)

theorem isElemAbelian_sup_card {M : Type*} [Group M] {p : ℕ} {A B : Subgroup M}
    (h : A ≤ centralizer (B : Set M)) (hAB : A ⊓ B = ⊥) (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) :
    IsElemAbelian p (A ⊔ B : Subgroup M) ∧
      Nat.card (A ⊔ B : Subgroup M) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n =>
    (h m.2 n n.2).symm
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm with hφ
  have hrange : φ.range = A ⊔ B := by
    have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hAB
  obtain ⟨hAc, hAe⟩ := hA
  obtain ⟨hBc, hBe⟩ := hB
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    rw [← hrange] at hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    apply Subtype.ext
    show φ u * φ v = φ v * φ u
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (congrArg Subtype.val (hAc.is_comm.comm u.1 v.1))
    · exact Subtype.ext (congrArg Subtype.val (hBc.is_comm.comm u.2 v.2))
  · intro x hx
    rw [← hrange] at hx
    obtain ⟨u, rfl⟩ := hx
    rw [← map_pow]
    have : u ^ p = 1 := Prod.ext (Subtype.ext (hAe _ u.1.2 |> fun h' => by simpa using h'))
      (Subtype.ext (hBe _ u.2.2 |> fun h' => by simpa using h'))
    rw [this, map_one]
  · have e : (A × B) ≃ (A ⊔ B : Subgroup M) :=
      (MonoidHom.ofInjective hinj).toEquiv.trans (MulEquiv.subgroupCongr hrange).toEquiv
    rw [← Nat.card_prod, Nat.card_congr e]


theorem exists_twoLocal_lower_fixed {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X B L : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian p B)
    (hL : GLAPComponent p X L) (C : Subgroup G) (hCB : C ≤ B)
    (hCN : C ≤ Subgroup.normalizer (L : Set G))
    (E U : Subgroup (barOf p L)) (hE : IsElemAbelian p E)
    (hEZ : E ⊓ Subgroup.center (barOf p L) = ⊥) (hU : U ≠ ⊥ ∧ IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set (barOf p L)))
    (hCE : ∀ c (hc : c ∈ C), ∀ x ∈ E, barAut p L ⟨c, hCN hc⟩ x = x)
    (hCU : ∀ c (hc : c ∈ C), ∀ u ∈ U, barAut p L ⟨c, hCN hc⟩ u ∈ U)
    (hCinn : ∀ c (hc : c ∈ C), barAut p L ⟨c, hCN hc⟩ ∈ innerAut (barOf p L) →
      barAut p L ⟨c, hCN hc⟩ = 1) :
    ∃ P S : Subgroup ↥X, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card C * Nat.card E ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      P ≤ Subgroup.normalizer (S : Set ↥X) := by
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
  set Tbar := U.map θ with hTbar
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
  have hfwC : ∀ g ∈ Cbar, ∀ h ∈ Tbar, g * h * g⁻¹ ∈ Tbar := by
    intro g hg h hh
    obtain ⟨x, hx, rfl⟩ := hmemC g hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hh
    rw [conjX x hx u]
    exact Subgroup.mem_map_of_mem θ (hCU (x : G) hx u hu)
  have hfwE : ∀ g ∈ Ebar, ∀ h ∈ Tbar, g * h * g⁻¹ ∈ Tbar := by
    intro g hg h hh
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hh
    rw [Subgroup.mem_map]
    exact ⟨e * u * e⁻¹, (Subgroup.mem_normalizer_iff.1 (hEU he) u).1 hu, by simp [map_mul, map_inv]⟩
  have hnormC : Cbar ≤ Subgroup.normalizer (Tbar : Set (↥X ⧸ O)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwC g hg h, fun hh => ?_⟩
    have := hfwC g⁻¹ (Subgroup.inv_mem _ hg) _ hh
    simpa [mul_assoc] using this
  have hnormE : Ebar ≤ Subgroup.normalizer (Tbar : Set (↥X ⧸ O)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwE g hg h, fun hh => ?_⟩
    have := hfwE g⁻¹ (Subgroup.inv_mem _ hg) _ hh
    simpa [mul_assoc] using this
  have hPnorm : Cbar ⊔ Ebar ≤ Subgroup.normalizer (Tbar : Set (↥X ⧸ O)) :=
    sup_le hnormC hnormE
  have hTne : Tbar ≠ ⊥ := by
    intro hbot
    apply hU.1
    rw [eq_bot_iff]
    intro u hu
    have hmem : θ u ∈ Tbar := Subgroup.mem_map_of_mem θ hu
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact hθinj (by rw [hmem, map_one])
  have hTp : IsPGroup 2 Tbar := hU.2.map θ
  have hCardC : Nat.card Cbar = Nat.card C := by
    show Nat.card ψ.range = Nat.card C
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv)
  have hCardE : Nat.card Ebar = Nat.card E := Subgroup.card_map_of_injective hθinj
  obtain ⟨hJc, hJcard⟩ := isElemAbelian_sup_card hcomm_CE hdisj hCbar_el hEbar_el
  obtain ⟨P, S, hPc, hPp, hPcard, hS1, hS2, hPS⟩ :=
    exists_lift_twoLocal_of_le_normalizer hp hp2 O hO (Cbar ⊔ Ebar) Tbar hJc ⟨hTne, hTp⟩ hPnorm
  refine ⟨P, S, hPc, hPp, ?_, hS1, hS2, hPS⟩
  rw [hPcard, hJcard, hCardC, hCardE]

end CFSG.HardMathSupport.Solomon.Proving
