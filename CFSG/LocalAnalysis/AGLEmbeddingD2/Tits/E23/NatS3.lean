module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SymBaumComp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SymThreeAgree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SylowIndep
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixGen
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open Equiv CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.Open CFSG.QuasithinUnique
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.RankThree.PartOne

variable {V : Type} [CommGroup V] [Finite V]
  {P M E : Subgroup (MulAut V)} {m : ℕ} {θ : ↥E ≃* Perm (Fin m)} {β : ↥(commV E) →* coreMod m}
  {i₀ : Fin m}

theorem SymComp.commV_inf_fixV_eq_bot (hc : SymComp P M E m θ β i₀) : commV E ⊓ fixV E = ⊥ := by
  refine eq_bot_iff.2 fun w hw => ?_
  have := hc.commV_inf_fixV (w := ⟨w, hw.1⟩) fun g => hw.2 g g.2
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)

theorem SymComp.eq_one (hc : SymComp P M E m θ β i₀) {e : MulAut V} (he : e ∈ E)
    (htriv : ∀ w ∈ commV E, e w * w⁻¹ ∈ fixV E) : e = 1 := by
  have hbot := hc.commV_inf_fixV_eq_bot
  have hfix : ∀ w ∈ commV E, e w = w := by
    intro w hw
    have h1 : e w * w⁻¹ ∈ commV E ⊓ fixV E :=
      ⟨(commV E).mul_mem (hc.inv e he w hw) ((commV E).inv_mem hw), htriv w hw⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hθ : θ ⟨e, he⟩ = 1 := by
    apply CFSG.CGT.PushingUpLit.BHS.coreAct_injective hc.three
    rw [map_one]
    ext d : 1
    obtain ⟨p, rfl⟩ := hc.surj d
    have h1 := hc.equiv ⟨e, he⟩ p (hc.inv e he p p.2)
    rw [MulAut.one_apply, ← h1]
    congr 1
    exact Subtype.ext (hfix p p.2)
  exact congrArg Subtype.val (θ.injective (hθ.trans (map_one θ).symm))

omit [Finite V] in
theorem SymComp.card_le_two (hc : SymComp P M E m θ β i₀) {B : Subgroup (MulAut V)}
    (hB : B ∈ dInter (Hyp51.offSet P) E) : Nat.card B ≤ 2 := by
  classical
  obtain ⟨i, j, -, hb⟩ := hc.dsw B hB
  let S : Finset (Perm (Fin m)) := {1, swap i j}
  let f : ↥B → ↥S := fun b => ⟨θ ⟨b, hB.2 b.2⟩, by
    rcases hb ⟨b, hB.2 b.2⟩ b.2 with h | h <;> simp [S, h]⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (⟨a, hB.2 a.2⟩ : ↥E) = ⟨b, hB.2 b.2⟩ := θ.injective (Subtype.ext_iff.1 hab)
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  calc Nat.card B ≤ Nat.card ↥S := Nat.card_le_card_of_injective f hf
    _ = S.card := Nat.card_eq_finsetCard S
    _ ≤ 2 := Finset.card_le_two

omit [Finite V] in
theorem SymComp.eq_three_of_six (hc : SymComp P M E m θ β i₀) (h6 : Nat.card E = 6) : m = 3 := by
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin] at h6
  have h3 := hc.three
  by_contra hne
  have h4 : 4 ≤ m := by omega
  have := Nat.factorial_le h4
  have h24 : Nat.factorial 4 = 24 := by decide
  omega

variable {T : Subgroup (MulAut V)}

theorem SymComp.isSylowOf_of_six (hc : SymComp P M E m θ β i₀) (h6 : Nat.card E = 6)
    (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hB : B ∈ Hyp51.offSet P) (hBE : B ≤ E) : Nat.card B = 2 ∧ IsSylowOf 2 B E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := hc.card_le_two ⟨hB, hBE⟩
  have hne : B ≠ ⊥ := (h.hyp43 hV).ne_bot B hB
  have h2 : Nat.card B = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot B).2 hne
    omega
  refine ⟨h2, hBE, IsPGroup.of_card (n := 1) (by rw [h2, pow_one]), ?_⟩
  have hri := relIndex_mul_card_of_le_sylowIndep hBE
  rw [h2, h6] at hri
  have : B.relIndex E = 3 := by omega
  rw [this]
  decide

theorem SymComp.exists_fixed_of_six (hc : SymComp P M E m θ β i₀) (h6 : Nat.card E = 6)
    {R : Subgroup (MulAut V)} (hR : R ∈ Hyp51.offSet P) (hRE : R ≤ E) :
    ∃ w ∈ commV E, w ∈ fixV R ∧ w ∉ fixV E := by
  classical
  have hm := hc.eq_three_of_six h6
  subst hm
  obtain ⟨i, j, hij, hb⟩ := hc.dsw R ⟨hR, hRE⟩
  have hτ1 : swap i j ≠ 1 := fun h1 => hij (Equiv.swap_eq_one_iff.1 h1)
  obtain ⟨w₀, hw₀, hw₀1, hfix₀⟩ := perm_fix_exists_core3 (swap i j) hτ1 (Equiv.swap_mul_self i j)
  obtain ⟨p, hp⟩ := hc.surj ⟨w₀, hw₀⟩
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hc.ker
  refine ⟨p, p.2, fun r hr => ?_, fun hpE => ?_⟩
  · have hrp : r p ∈ commV E := hc.inv r (hRE hr) p p.2
    have h1 := hc.equiv ⟨r, hRE hr⟩ p hrp
    have h2 : β ⟨r p, hrp⟩ = β p := by
      rw [h1, hp]
      rcases hb ⟨r, hRE hr⟩ hr with h | h
      · rw [h, map_one, MulAut.one_apply]
      · rw [h]
        exact Subtype.ext hfix₀
    exact congrArg Subtype.val (hinj h2)
  · have hbot := hc.commV_inf_fixV_eq_bot
    have h1 : (p : V) ∈ commV E ⊓ fixV E := ⟨p.2, hpE⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : p = 1 := Subtype.ext h1
    rw [h2, map_one] at hp
    exact hw₀1 (congrArg Subtype.val hp).symm

theorem SymComp.exists_agree_of_six (hc : SymComp P M E m θ β i₀) (h6 : Nat.card E = 6)
    (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) {R : Subgroup (MulAut V)}
    (hR : R ∈ Hyp51.offSet P) (hRE : R ≤ E) {x : MulAut V} (hxE : conjSub x E = E)
    (hxfix : ∀ w ∈ commV E, w ∈ fixV R → x w = w) :
    ∃ u ∈ R, ∀ w ∈ commV E, x w * (u w)⁻¹ ∈ fixV E := by
  have hR2 := (hc.isSylowOf_of_six h6 h hV hR hRE).1
  have hm := hc.eq_three_of_six h6
  subst hm
  have hxE' : ∀ p ∈ commV E, x p ∈ commV E := fun p hp => by
    have := map_mem_commV_conj E x hp
    rwa [hxE] at this
  obtain ⟨u, huR, hu⟩ := exists_mem_agree_of_symData_three hV θ β hc.inv hc.surj hc.ker hc.equiv
    hRE hR2 hxE' fun w hw hwR => hxfix w hw hwR
  refine ⟨u, huR, fun w hw => ?_⟩
  rw [hu w hw, mul_inv_cancel]
  exact (fixV E).one_mem

theorem isSylowOf_of_nat {ℰ : Set (Subgroup (MulAut V))} (h : Hyp51 P T M)
    (hV : ∀ v : V, v ^ 2 = 1)
    (hnat : ∀ E ∈ ℰ, SLType2 (Hyp51.offSet P) E ∨
      (SymType (genD P ⊓ M) (Hyp51.offSet P) E ∧ Nat.card E = 6)) :
    ∀ E ∈ ℰ, ∀ B ∈ Hyp51.offSet P, B ≤ E → IsSylowOf 2 B E := by
  intro E hE B hB hBE
  rcases hnat E hE with hSL | ⟨hSym, h6⟩
  · obtain ⟨n, -, -, -, hsyl⟩ := hSL
    exact (hsyl B).1 ⟨hB, hBE⟩
  · obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType hSym
    exact (hc.isSylowOf_of_six h6 h hV hB hBE).2

end CFSG.AGLEmbeddingD2.Tits.E23
