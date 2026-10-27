module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Orbit
public import CFSG.HardMathSupport.Timmesfeld.Balance.Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.HardMathSupport.Timmesfeld.Balance (eq_bot_of_centralizes_pCore_of_centralizes_components_p)
open scoped commutatorElement

theorem thompson_step {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P R B : Subgroup G)
    (hP : IsPGroup p P) (hR : Nat.Coprime (Nat.card R) p) (hB : IsPGroup p B)
    (hRP : R ≤ Subgroup.normalizer (P : Set G)) (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hRB : ⁅R, B⁆ = ⊥)
    (hfix : P ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (R : Set G)) :
    P ≤ Subgroup.centralizer (R : Set G) := by
  have hRB' : R ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB
  let α : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRP)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (r : R) (x : P), ((α r x : P) : G) = r * x * (r : G)⁻¹ := fun r x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRP r) x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : G) = b * x * (b : G)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hBP b) x
  have hcomm : ∀ r b, α r * β b = β b * α r := by
    intro r b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hrb : (b : G) * r = r * b := Subgroup.mem_centralizer_iff.mp (hRB' r.2) b b.2
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
    calc (r : G) * (b * x * (b : G)⁻¹) * (r : G)⁻¹ = (r * b) * x * ((r : G) * b)⁻¹ := by
          group
      _ = (b * r) * x * ((b : G) * r)⁻¹ := by rw [hrb]
      _ = b * (r * x * (r : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ r x, (∀ b, β b x = x) → α r x = x := by
    intro r x hx
    have hxB : (x : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hx ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (x : G) = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [h]
    have hrx : (r : G) * x = x * r :=
      Subgroup.mem_centralizer_iff.mp (hfix ⟨x.2, hxB⟩) r r.2
    apply Subtype.ext
    rw [hα, hrx, mul_inv_cancel_right]
  have hR' : ¬ p ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hR.symm
  have key := CFSG.GroupTheory.thompson_A_times_B hP hR' hB α β hcomm hfix'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : G)) (key ⟨r, hr⟩)
  simp only [hα, MulAut.one_apply] at h
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [h]

theorem centralizes_pCore_of_glaPPrimeCoreOf_centralizer {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {A : Subgroup Y} (hA : IsPGroup p ↥A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set Y)) ≤
      Subgroup.centralizer (CFSG.pCore p Y : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set W := GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set Y)) with hW
  set P : Subgroup Y := CFSG.pCore p Y with hPdef
  have hWC : W ≤ Subgroup.centralizer (A : Set Y) := by
    rintro x hx
    have hx' : x ∈ (GLAPPrimeCore p ↥(Subgroup.centralizer (A : Set Y))).map
        (Subgroup.centralizer (A : Set Y)).subtype := hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx'
    exact y.2
  have hWnorm : ∀ g ∈ Subgroup.centralizer (A : Set Y), ∀ t ∈ W, g * t * g⁻¹ ∈ W := by
    intro g hg t ht
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p _ hg) t).1 ht
  have hWcop : Nat.Coprime p (Nat.card W) := coprime_card_GLAPPrimeCoreOf hp _
  have hPp : IsPGroup p ↥P := CFSG.pCore_isPGroup
  have hPn : P.Normal := CFSG.pCore_normal
  have hNtop : ∀ g : Y, g ∈ Subgroup.normalizer (P : Set Y) := fun g =>
    Subgroup.mem_normalizer_iff.2 fun h => by
      constructor
      · intro hh
        exact hPn.conj_mem h hh g
      · intro hh
        have h1 := hPn.conj_mem _ hh g⁻¹
        have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
        rw [e] at h1
        exact h1
  have hRB : ⁅W, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWC
  have hfix : P ⊓ Subgroup.centralizer (A : Set Y) ≤ Subgroup.centralizer (W : Set Y) := by
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨c, hcdef⟩ : ∃ c : Y, c = x * w * x⁻¹ * w⁻¹ := ⟨_, rfl⟩
    have hcW : c ∈ W := by
      have h1 : x * w * x⁻¹ ∈ W := hWnorm x hxC w hw
      have h2 : (w⁻¹ : Y) ∈ W := W.inv_mem hw
      have : c = (x * w * x⁻¹) * w⁻¹ := by rw [hcdef]
      rw [this]
      exact W.mul_mem h1 h2
    have hcK : c ∈ P ⊓ Subgroup.centralizer (A : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h1 : w * x⁻¹ * w⁻¹ ∈ P := hPn.conj_mem _ (P.inv_mem hxP) w
        have : c = x * (w * x⁻¹ * w⁻¹) := by rw [hcdef]; group
        rw [this]
        exact P.mul_mem hxP h1
      · have hwC : w ∈ Subgroup.centralizer (A : Set Y) := hWC hw
        rw [hcdef]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxC hwC)
          (Subgroup.inv_mem _ hxC)) (Subgroup.inv_mem _ hwC)
    have hK0 : IsPGroup p ↥(P ⊓ Subgroup.centralizer (A : Set Y)) := hPp.to_le inf_le_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hK0
    have hdisj : Disjoint W (P ⊓ Subgroup.centralizer (A : Set Y)) :=
      Subgroup.disjoint_of_coprime_natCard (by
        rw [hn]
        exact Nat.Coprime.pow_right n hWcop.symm)
    have hc1 : c = 1 := by
      have hmem : c ∈ W ⊓ (P ⊓ Subgroup.centralizer (A : Set Y)) := Subgroup.mem_inf.2 ⟨hcW, hcK⟩
      rw [disjoint_iff.1 hdisj] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hxw : x * w = w * x := by
      have : x * w * x⁻¹ * w⁻¹ = 1 := hcdef ▸ hc1
      have h2 : x * w = (x * w * x⁻¹ * w⁻¹) * (w * x) := by group
      rw [h2, this, one_mul]
    exact hxw.symm
  have hPC := thompson_step P W A hPp hWcop.symm hA (fun g _ => hNtop g)
    (fun g _ => hNtop g) hRB hfix
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.1 (hPC hx)) w hw).symm

theorem i194_reduced {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) {B A : Subgroup Y} (hB : IsElemAbelian p B) (hAB : A ≤ B)
    (hcf : ∀ L : Subgroup Y, IsComponent L → IsCompCoreFreeLocalType p B L) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set Y)) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAp : IsPGroup p ↥A := isPGroup_of_le_elemAbelian hB hAB
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨a, hAB ha⟩ ⟨b, hAB hb⟩)
  refine eq_bot_of_centralizes_pCore_of_centralizes_components_p hp hO
    (fun d hd => orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hd)
    (centralizes_pCore_of_glaPPrimeCoreOf_centralizer hp hAp hAc) ?_
  intro L hL d hd
  exact Subgroup.mem_centralizer_iff.2 fun y hy =>
    (orbit_centralizes hp hO hB hAB hcf hL hd y hy).symm

end CFSG.LocalAnalysis.GLTheoremA
