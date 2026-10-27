module

public import CFSG.GroupTheory.AltSevenModule.Faithful
public import CFSG.GroupTheory.AltSevenModule.Irreducible
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourMain
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.HA7
public import CFSG.Quasithin.Background.FLc3Tr

public section

namespace CFSG.GroupTheory.AltSevenModule

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

theorem exists_conj_kleinRegular7_le {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (ρ : ↥(alternatingGroup (Fin 7)) →* MulAut V)
    (hρ : Function.Injective ρ) (h16 : Nat.card (commV ρ.range) = 16)
    {A : Subgroup ↥(alternatingGroup (Fin 7))} (hA1 : A ≠ ⊥) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV (A.map ρ))) :
    ∃ c ∈ alternatingGroup (Fin 7),
      kleinRegular7.map (MulAut.conj c).toMonoidHom ≤ A.map (alternatingGroup (Fin 7)).subtype := by
  classical
  have hA7nonab : ∃ a b : ↥(alternatingGroup (Fin 7)), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact CFSG.Quasithin.H.A7.not_comm_A7 h
  let K : Subgroup (MulAut V) := ρ.range
  let W : Subgroup V := commV K
  have hW16 : Nat.card ↥W = 16 := h16
  let κ : ↥(alternatingGroup (Fin 7)) ≃* ↥K := MonoidHom.ofInjective hρ
  haveI hKsimple : IsSimpleGroup ↥K := κ.symm.isSimpleGroup
  have hKnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hA7nonab
    exact ⟨κ a, κ b, fun h => hab (by simpa using congrArg κ.symm h)⟩
  let r : ↥K →* MulAut ↥W := (restrictW W).comp (Subgroup.inclusion (le_stabW_commV K))
  have hr : Function.Injective r := injective_restrictW_commV hKnonab
  let φ : ↥(alternatingGroup (Fin 7)) →* MulAut ↥W := r.comp ρ.rangeRestrict
  have hρr : Function.Injective ρ.rangeRestrict :=
    fun x y h => hρ (by simpa using congrArg Subtype.val h)
  have hφ : Function.Injective φ := hr.comp hρr
  let L' : Subgroup (MulAut ↥W) := φ.range
  let π : ↥(alternatingGroup (Fin 7)) ≃* ↥L' := MonoidHom.ofInjective hφ
  haveI hL'simple : IsSimpleGroup ↥L' := π.symm.isSimpleGroup
  have hL'nonab : ∃ a b : ↥L', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hA7nonab
    exact ⟨π a, π b, fun h => hab (by simpa using congrArg π.symm h)⟩
  have hq : CFSG.IsQuasisimple ↥L' :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hL'nonab).1
  have hF : L' = CFSG.Open.quasithinGenFitting L' := by
    refine le_antisymm ?_ (CFSG.Quasithin.quasithinGenFitting_le L')
    exact CFSG.Quasithin.InternalSec.le_quasithinGenFitting_of_normal le_rfl
      (fun x hx k hk => L'.mul_mem (L'.mul_mem hx hk) (L'.inv_mem hx)) hq
  have hW2 : ∀ s : ↥W, s ^ 2 = 1 := fun s => Subtype.ext (by simpa using hV (s : V))
  have hCtx : CFSG.QuasithinUnique.Bridge.Alt57.Ctx L' L' 7 :=
    ⟨Or.inr rfl, ⟨π.symm⟩, hF, fun y hy => Subgroup.pow_mem L' hy 2⟩
  have hirr : XMod.IsIrrSec ↥L' (⊥ : Subgroup ↥W) ⊤ := isIrrSec_of_card_sixteen hW16 π
  let A' : Subgroup (MulAut ↥W) := A.map φ
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hab : (a * b) * (a * b) = 1 := by
      simpa [pow_two] using hA2 (a * b) (A.mul_mem ha hb)
    have ha2 : a * a = 1 := by simpa [pow_two] using hA2 a ha
    have hb2 : b * b = 1 := by simpa [pow_two] using hA2 b hb
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]
  have hA'le : A' ≤ L' := Subgroup.map_le_range φ A
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have hmem : φ a ∈ A' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (hφ (by rw [hmem, map_one]))
  have hA'abel : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcommA a ha b hb]
  have hA'sq : ∀ x ∈ A', x ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA2 a ha, map_one]
  have hIsA2 : IsA2 L' A' := ⟨hA'le, hA'ne, hA'abel, hA'sq⟩
  have hmem : ∀ w : ↥W, w ∈ fixV A' ↔ (w : V) ∈ fixV (A.map ρ) := by
    intro w
    constructor
    · intro hw
      rw [mem_fixV]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      exact congrArg Subtype.val
        ((mem_fixV.mp hw) (φ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
    · intro hw
      rw [mem_fixV]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      apply Subtype.ext
      exact mem_fixV.mp hw (ρ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  have hfix : (fixV A').map W.subtype = fixV (A.map ρ) ⊓ W := by
    ext v
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨(hmem w).mp hw, w.2⟩
    · intro hv
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hv
      exact ⟨⟨v, h2⟩, (hmem ⟨v, h2⟩).mpr h1, rfl⟩
  have hmapcard : Nat.card ↥((fixV A').map W.subtype) = Nat.card ↥(fixV A') :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hfixcard : Nat.card ↥(fixV A') = Nat.card ↥(fixV (A.map ρ) ⊓ W) := by
    rw [← hmapcard, hfix]
  have hA'card : Nat.card ↥A' = Nat.card ↥A := Subgroup.card_map_of_injective hφ
  have hCpos : 0 < Nat.card ↥(fixV (A.map ρ)) := by
    haveI : Nonempty ↥(fixV (A.map ρ)) := ⟨⟨1, (fixV (A.map ρ)).one_mem⟩⟩
    exact Nat.card_pos
  have hWle : Nat.card ↥W ≤ Nat.card ↥A' * Nat.card ↥(fixV A') := by
    refine Nat.le_of_mul_le_mul_right ?_ hCpos
    rw [hfixcard]
    calc Nat.card ↥W * Nat.card ↥(fixV (A.map ρ))
        ≤ Nat.card V * Nat.card ↥(fixV (A.map ρ) ⊓ W) :=
          CFSG.Quasithin.FLc.card_mul_card_le_inf W (fixV (A.map ρ))
      _ ≤ Nat.card A * Nat.card ↥(fixV (A.map ρ)) *
            Nat.card ↥(fixV (A.map ρ) ⊓ W) := Nat.mul_le_mul_right _ hoff
      _ = Nat.card ↥A' * Nat.card ↥(fixV (A.map ρ) ⊓ W) *
            Nat.card ↥(fixV (A.map ρ)) := by
          rw [hA'card]
          ring
  obtain ⟨B, hBA, hB, -⟩ :=
    CFSG.Quasithin.B1.exists_offender_below (X := L') hIsA2 0 (by simpa using hWle)
  have hconj := CFSG.QuasithinUnique.B42A57.asB42A7Four_holds (S := ↥W) hW2 L' L' B hCtx hirr hB
    (by rw [hW16]; norm_num) π
  unfold AltConjTo at hconj
  obtain ⟨c, hc, hEq⟩ := hconj
  have hpre : (B.subgroupOf L').comap π.toMonoidHom ≤ A := by
    intro x hx
    have hxB : (π x : MulAut ↥W) ∈ B := Subgroup.mem_subgroupOf.mp hx
    have hxφ : φ x ∈ B := by
      have h := MonoidHom.ofInjective_apply (f := φ) hφ (x := x)
      rw [← h]
      exact hxB
    obtain ⟨a, ha, hEqax⟩ := Subgroup.mem_map.mp (hBA hxφ)
    have hax : a = x := hφ hEqax
    rwa [← hax]
  refine ⟨c, hc, ?_⟩
  rw [← hEq]
  exact Subgroup.map_mono hpre

end CFSG.GroupTheory.AltSevenModule
