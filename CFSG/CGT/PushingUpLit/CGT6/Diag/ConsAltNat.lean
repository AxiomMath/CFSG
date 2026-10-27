module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

theorem natSection_alt_of_classX (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hcen : Subgroup.center ↥Y = ⊥) (hX : InClassX ↥(yuHol Y)) {m : ℕ}
    (hm : 7 ≤ m) (eY : ↥Y ≃* alternatingGroup (Fin m)) :
    IsNatSectionBy (altAct m) Y (commV Y) (commV Y ⊓ fixV Y) := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨hshort, halt | hsl⟩ := hX
  · obtain ⟨n, hn1, φ, ψ, hsum, hsurj, hker, hequiv⟩ := halt
    have hθs := yuTheta_surjective Y φ hV
    have hRc := yuTheta_ker_le_center Y φ hV hshort
    have hker1 : (yuTheta Y φ).ker = ⊥ := by
      rw [eq_bot_iff]
      exact hRc.trans hcen.le
    have hθi : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hker1
    let θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)) :=
      MulEquiv.ofBijective (yuTheta Y φ) ⟨hθi, hθs⟩
    have hcard := Nat.card_congr (eY.symm.trans θ).toEquiv
    rw [natCard_alt m (by omega), natCard_alt (2 * n + 1) (by omega)] at hcard
    have hmn : m = 2 * n + 1 := by
      have h2m : 2 ∣ Nat.factorial m := Nat.dvd_factorial (by norm_num) (by omega)
      have h2n : 2 ∣ Nat.factorial (2 * n + 1) := Nat.dvd_factorial (by norm_num) (by omega)
      have hfac : Nat.factorial m = Nat.factorial (2 * n + 1) := by omega
      exact (Nat.factorial_inj (by omega : 1 < m)).mp hfac
    subst hmn
    let ρ : ↥Y →* MulAut V := Y.subtype
    let θ' : ↥Y →* Equiv.Perm (Fin (2 * n + 1)) :=
      (alternatingGroup (Fin (2 * n + 1))).subtype.comp (yuTheta Y φ)
    let A₀ : Subgroup V := commV Y ⊓ fixV Y
    have hB : ∀ g : ↥Y, ∀ b ∈ commV Y, ρ g b ∈ commV Y := fun g b hb =>
      apply_mem_commV_self Y g.2 hb
    have hshortU := shortU_eq_range Y φ hV hshort
    let ι : ↥(commV Y) →* ↥(shortU ↥(yuHol Y)) :=
      (yuInc Y).codRestrict (shortU ↥(yuHol Y)) (yuInc_mem_shortU Y hV)
    let β : ↥(commV Y) →* ↥(G6.coreMod (2 * n + 1)) :=
      (ψ.comp ι).codRestrict (G6.coreMod (2 * n + 1)) (fun u => (G6.mem_coreMod).2 (hsum _))
    have hβs : Function.Surjective β := by
      intro w
      obtain ⟨x, hx⟩ := hsurj (Multiplicative.toAdd (w : G6.PermMod (2 * n + 1)))
        (G6.mem_coreMod.mp w.2)
      obtain ⟨u, hu⟩ : (x : ↥(yuHol Y)) ∈ (yuInc Y).range := hshortU ▸ x.2
      refine ⟨u, Subtype.ext ?_⟩
      show ψ (ι u) = (w : G6.PermMod (2 * n + 1))
      have : ι u = x := Subtype.ext hu
      rw [this, hx]
      rfl
    have hβk : β.ker = A₀.subgroupOf (commV Y) := by
      ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h1 : (ψ.comp ι) u = 1 := congrArg Subtype.val h
        have h2 : ι u ∈ ψ.ker := h1
        rw [hker, Subgroup.mem_subgroupOf] at h2
        have h3 : yuInc Y u ∈ Subgroup.center ↥(yuHol Y) := h2.2
        refine ⟨u.2, fun g hg => ?_⟩
        exact apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) h3
      · rintro ⟨-, hu⟩
        apply Subtype.ext
        show ψ (ι u) = 1
        have h2 : ι u ∈ ψ.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          refine ⟨yuInc_mem_shortU Y hV u, Subgroup.mem_center_iff.mpr ?_⟩
          intro x
          have h4 := conj_yuInc Y x u
          have h5 : (⟨x.1.right u, apply_mem_commV_self Y x.2.2 u.2⟩ : ↥(commV Y)) = u :=
            Subtype.ext (hu x.1.right x.2.2)
          rw [h5] at h4
          exact mul_inv_eq_iff_eq_mul.mp h4
        exact h2
    have hβe : ∀ (g : ↥Y) (b : ↥(commV Y)), β ⟨ρ g b, hB g b b.2⟩ =
        G6.coreAct (2 * n + 1) (θ' g) (β b) := by
      intro g b
      have hu : yuInc Y b ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV b
      have hu' : yuSec Y g * yuInc Y b * (yuSec Y g)⁻¹ ∈ shortU ↥(yuHol Y) :=
        (shortU_normal (L := ↥(yuHol Y))).conj_mem _ hu _
      have h1 := hequiv (yuSec Y g : ↥(yuHol Y)) (yuInc Y b) hu hu'
      have h2 : (⟨yuSec Y g * yuInc Y b * (yuSec Y g)⁻¹, hu'⟩ : ↥(shortU ↥(yuHol Y))) =
          ι ⟨ρ g b, hB g b b.2⟩ := by
        apply Subtype.ext
        exact conj_yuInc Y (yuSec Y g) b
      rw [h2] at h1
      apply Subtype.ext
      show ψ (ι ⟨ρ g b, hB g b b.2⟩) = G6.permAct (2 * n + 1) (θ' g) (ψ (ι b))
      rw [h1]
      apply Multiplicative.toAdd.injective
      funext i
      rfl
    refine ⟨fun x hx p hp => apply_mem_commV_self Y hx hp, θ, β, hβs, hβk, ?_⟩
    intro x p hp
    exact hβe x p
  · exfalso
    obtain ⟨n, hn1, φ, ψ, hsurj, hker, hequiv⟩ := hsl
    have hθs := yuTheta_surjective Y φ hV
    have hRc := yuTheta_ker_le_center Y φ hV hshort
    have hker1 : (yuTheta Y φ).ker = ⊥ := by
      rw [eq_bot_iff]
      exact hRc.trans hcen.le
    have hθi : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hker1
    let θ : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
      MulEquiv.ofBijective (yuTheta Y φ) ⟨hθi, hθs⟩
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn : n = 1 := by omega
      subst hn
      have hcard := Nat.card_congr (eY.symm.trans θ).toEquiv
      rw [natCard_alt m (by omega), card_sl2_fq le_rfl] at hcard
      have h7 : Nat.factorial 7 ≤ Nat.factorial m := Nat.factorial_le hm
      have h7' : Nat.factorial 7 = 5040 := by decide
      norm_num at hcard
      omega
    · have := (alt_sl2_iso (by omega) hn2 (eY.symm.trans θ)).1
      omega

end CFSG.CGT.PushingUpLit.CGT6.Diag.Cons
