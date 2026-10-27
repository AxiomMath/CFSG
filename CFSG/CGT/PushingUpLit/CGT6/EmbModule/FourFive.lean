module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.YuBasic
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.AltSplit
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

theorem false_of_perfect_small {Γ A : Type*} [Group Γ] [Group.IsPerfect Γ] [Group A] [Finite A]
    [Nontrivial A] (hA : Nat.card A < 60) (f : Γ →* A) (hf : Function.Surjective f) : False := by
  have : Group.IsPerfect A := Group.IsPerfect.ofSurjective hf
  have : Group.IsSolvable A := CFSG.GroupTheory.groups_order_below_sixty_solvable hA
  exact Group.IsPerfect.not_isSolvable A inferInstance

theorem eq_top_of_perfect_two_quotient {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (I : Subgroup E) [I.Normal] (h : ∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ I) : I = ⊤ := by
  have hp : IsPGroup 2 (E ⧸ I) := fun x => by
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := h e
    exact ⟨n, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hn⟩
  have : Group.IsNilpotent (E ⧸ I) := hp.isNilpotent
  have : Group.IsSolvable (E ⧸ I) := inferInstance
  by_contra hne
  have hnt : Nontrivial (E ⧸ I) := by
    have h1 : 1 < I.index := Subgroup.one_lt_index_of_ne_top hne
    rw [Subgroup.index_eq_card] at h1
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  exact Group.IsPerfect.not_isSolvable (E ⧸ I) inferInstance

section Yu

variable {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))

theorem central_comm_mem {z : ↥Y} (hz : z ∈ Subgroup.center ↥Y)
    (hzfix : ∀ u : ↥(commV Y), (z : MulAut V) (u : V) = u) (v : V) :
    (z : MulAut V) v * v⁻¹ ∈ commV Y ⊓ fixV Y := by
  refine ⟨commV_mem_of_apply Y z v, fun y hy => ?_⟩
  have hcomm : (y : MulAut V) ((z : MulAut V) v) = (z : MulAut V) ((y : MulAut V) v) := by
    have h1 := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
    have h2 := congrArg (fun g : ↥Y => (g : MulAut V) v) h1
    simpa [map_mul] using h2
  let w : ↥(commV Y) := ⟨(y : MulAut V) v * v⁻¹, commV_mem_of_apply Y ⟨y, hy⟩ v⟩
  have hwv : (y : MulAut V) v = (w : V) * v := by
    show _ = ((y : MulAut V) v * v⁻¹) * v
    rw [inv_mul_cancel_right]
  have hzw : (z : MulAut V) (w : V) = w := hzfix w
  show y ((z : MulAut V) v * v⁻¹) = (z : MulAut V) v * v⁻¹
  have h4 : (z : MulAut V) ((y : MulAut V) v) = (w : V) * (z : MulAut V) v := by
    rw [hwv, map_mul, hzw]
  rw [map_mul, map_inv, hcomm, h4]
  have hwdef : (w : V) = (y : MulAut V) v * v⁻¹ := rfl
  rw [hwdef]
  calc ((y : MulAut V) v * v⁻¹) * (z : MulAut V) v * ((y : MulAut V) v)⁻¹
      = ((y : MulAut V) v * ((y : MulAut V) v)⁻¹) * ((z : MulAut V) v * v⁻¹) := by ac_rfl
    _ = (z : MulAut V) v * v⁻¹ := by rw [mul_inv_cancel, one_mul]

theorem commV_center_le
    (hfix : ∀ z ∈ Subgroup.center ↥Y, ∀ u : ↥(commV Y), (z : MulAut V) (u : V) = u) :
    commV ((Subgroup.center ↥Y).map Y.subtype) ≤ commV Y ⊓ fixV Y := by
  unfold commV
  rw [Subgroup.closure_le]
  rintro _ ⟨x, ⟨z, hz, rfl⟩, v, rfl⟩
  exact central_comm_mem Y hz (hfix z hz) v

variable [Finite V]

theorem center_eq_bot_of_alt [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) {n : ℕ} (hn1 : 1 ≤ n) (hnat : IsNaturalAltModule ↥(yuHol Y) n) :
    Subgroup.center ↥Y = ⊥ := by
  classical
  obtain ⟨φ, ψ, hsum, hsurj, hker, hequiv⟩ := hnat
  have hθs := yuTheta_surjective Y φ hV
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn : n = 1 := by omega
    subst hn
    have hcard : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have : Nontrivial (alternatingGroup (Fin (2 * 1 + 1))) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact false_of_perfect_small (Γ := ↥Y) (A := alternatingGroup (Fin (2 * 1 + 1)))
      (by omega) (yuTheta Y φ) hθs
  have hcenter : Subgroup.center (alternatingGroup (Fin (2 * n + 1))) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hZ := yuTheta_center_le_ker Y φ hV hcenter
  have hRc := yuTheta_ker_le_center Y φ hV hX
  have hRfix := fun {r : ↥Y} (hr : r ∈ (yuTheta Y φ).ker) (u : ↥(commV Y)) =>
    yuTheta_ker_fixes Y φ hV hX hr u
  let ρ : ↥Y →* MulAut V := Y.subtype
  let θ' : ↥Y →* Perm (Fin (2 * n + 1)) := (alternatingGroup (Fin (2 * n + 1))).subtype.comp
    (yuTheta Y φ)
  have hev : ∀ g, θ' g ∈ alternatingGroup (Fin (2 * n + 1)) := fun g => (yuTheta Y φ g).2
  have hsurjθ : ∀ σ ∈ alternatingGroup (Fin (2 * n + 1)), ∃ g, θ' g = σ := by
    intro σ hσ
    obtain ⟨g, hg⟩ := hθs ⟨σ, hσ⟩
    exact ⟨g, by simp [θ', hg]⟩
  let A₀ : Subgroup V := commV Y ⊓ fixV Y
  have hAB : A₀ ≤ commV Y := inf_le_left
  have hB : ∀ g : ↥Y, ∀ b ∈ commV Y, ρ g b ∈ commV Y := fun g b hb =>
    apply_mem_commV_self Y g.2 hb
  have hAt : ∀ g : ↥Y, ∀ a ∈ A₀, ρ g a = a := fun g a ha => ha.2 g g.2
  have hshortU := shortU_eq_range Y φ hV hX
  let ι : ↥(commV Y) →* ↥(shortU ↥(yuHol Y)) :=
    (yuInc Y).codRestrict (shortU ↥(yuHol Y)) (yuInc_mem_shortU Y hV)
  let β : ↥(commV Y) →* ↥(coreMod (2 * n + 1)) :=
    (ψ.comp ι).codRestrict (coreMod (2 * n + 1)) (fun u => (mem_coreMod).2 (hsum _))
  have hβs : Function.Surjective β := by
    intro w
    obtain ⟨x, hx⟩ := hsurj (Multiplicative.toAdd (w : PermMod (2 * n + 1))) (mem_coreMod.mp w.2)
    obtain ⟨u, hu⟩ : (x : ↥(yuHol Y)) ∈ (yuInc Y).range := hshortU ▸ x.2
    refine ⟨u, Subtype.ext ?_⟩
    show ψ (ι u) = (w : PermMod (2 * n + 1))
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
      coreAct (2 * n + 1) (θ' g) (β b) := by
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
    show ψ (ι ⟨ρ g b, hB g b b.2⟩) = permAct (2 * n + 1) (θ' g) (ψ (ι b))
    rw [h1]
    apply Multiplicative.toAdd.injective
    funext i
    rfl
  have hker' : ∀ k : ↥Y, θ' k = 1 → ∀ b ∈ commV Y, ρ k b = b := by
    intro k hk b hb
    have : yuTheta Y φ k = 1 := Subtype.ext hk
    exact hRfix ((MonoidHom.mem_ker).mpr this) ⟨b, hb⟩
  obtain ⟨r, hrA, hr1, hrg⟩ := alt_retraction ρ ⟨n, rfl⟩ θ' hev hsurjθ hV A₀ (commV Y) hAB hB hAt β
    hβs hβk hβe hker'
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzR : z ∈ (yuTheta Y φ).ker := hZ hz
  have hzV : ∀ v : V, ρ z v = v := by
    intro v
    let u : ↥Y → ↥(commV Y) := fun g => ⟨ρ g v * v⁻¹, commV_mem_of_apply Y g v⟩
    have hu : ∀ g h, u (g * h) = ⟨ρ g (u h : V), hB g _ (u h).2⟩ * u g := by
      intro g h
      apply Subtype.ext
      show ρ (g * h) v * v⁻¹ = ρ g (ρ h v * v⁻¹) * (ρ g v * v⁻¹)
      rw [map_mul, MulAut.mul_apply, map_mul, map_inv]
      group
    have hχ := mult_trivial_of_perfect (M := V) (fun g => r (u g)) (fun g h => by
      show r (u (g * h)) = r (u g) * r (u h)
      rw [hu, map_mul, hrg g (u h)]
      exact mul_comm _ _) z
    have huA : (u z : V) ∈ A₀ := central_comm_mem Y hz (hRfix hzR) v
    have h4 := hr1 (u z : V) huA
    have h5 : r ⟨(u z : V), hAB huA⟩ = (u z : V) := h4
    have h6 : r (u z) = 1 := hχ
    have h7 : (u z : V) = 1 := by rw [← h5]; exact h6
    exact mul_inv_eq_one.mp h7
  apply Subtype.ext
  exact MulEquiv.ext hzV

theorem center_cases_of_sl (hM4 : SchurMultL2Two) [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) {n : ℕ} (hn1 : 1 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥(yuHol Y) n) :
    Subgroup.center ↥Y = ⊥ ∨ (n = 2 ∧ Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      Nat.card ↥(Subgroup.center ↥Y) = 2 ∧
      ∀ z ∈ Subgroup.center ↥Y, ∀ u : ↥(commV Y), (z : MulAut V) (u : V) = u) := by
  classical
  obtain ⟨φ, ψ, -, -, -⟩ := hnat
  have hθs := yuTheta_surjective Y φ hV
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn : n = 1 := by omega
    subst hn
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        GaloisField.card 2 1 (by norm_num)]
      norm_num
    have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact false_of_perfect_small (Γ := ↥Y) (by omega) (yuTheta Y φ) hθs
  have hcenter := sl2_center_eq_bot (GaloisField 2 n)
  have hZ := yuTheta_center_le_ker Y φ hV hcenter
  have hRc := yuTheta_ker_le_center Y φ hV hX
  have hcR : Subgroup.center ↥Y = (yuTheta Y φ).ker := le_antisymm hZ hRc
  have hfix : ∀ z ∈ Subgroup.center ↥Y, ∀ u : ↥(commV Y), (z : MulAut V) (u : V) = u :=
    fun z hz u => yuTheta_ker_fixes Y φ hV hX (hcR ▸ hz) u
  by_cases hn3 : 3 ≤ n
  · left
    have h := hM4 n hn3 ↥Y inferInstance ((yuTheta Y φ).ker) hRc (yuTheta_ker_isPGroup Y φ)
      ⟨QuotientGroup.quotientKerEquivOfSurjective (yuTheta Y φ) hθs⟩
    rw [hcR]
    exact h
  · have hn2' : n = 2 := by omega
    subst hn2'
    obtain ⟨e⟩ := sl2_four_equiv_alt5
    let ρ : ↥Y →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (yuTheta Y φ)
    have hkerρ : ρ.ker = (yuTheta Y φ).ker := by
      ext y
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      show e (yuTheta Y φ y) = 1 ↔ _
      exact e.map_eq_one_iff
    have hno2 : ∀ I : Subgroup ↥Y, I.Normal → (∀ y : ↥Y, ∃ n : ℕ, y ^ 2 ^ n ∈ I) → I = ⊤ :=
      fun I hI h => by
        have := hI
        exact eq_top_of_perfect_two_quotient I h
    rcases alt5_cover_cases' ρ (e.surjective.comp hθs) (by rw [hkerρ]; exact hRc)
      (by rw [hkerρ]; exact yuTheta_ker_isPGroup Y φ) hno2 with hinj | ⟨hiso, hcard⟩
    · left
      rw [hcR, ← hkerρ]
      exact (MonoidHom.ker_eq_bot_iff ρ).mpr hinj
    · right
      refine ⟨rfl, hiso, ?_, hfix⟩
      rw [hcR, ← hkerρ]
      exact hcard

theorem emb_four_five_core (hM4 : SchurMultL2Two) (hV : ∀ v : V, v ^ 2 = 1)
    (hY : ⁅Y, Y⁆ = Y) (hX : InClassX ↥(yuHol Y)) :
    Subgroup.center ↥Y = ⊥ ∨
      (Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
        Nat.card ↥(Subgroup.center ↥Y) = 2 ∧ IsNaturalSLTwoModule ↥(yuHol Y) 2 ∧
        Nat.card ↥(commV ((Subgroup.center ↥Y).map Y.subtype)) ≤
          Nat.card ↥(commV Y ⊓ fixV Y)) := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  obtain ⟨hshort, hnat⟩ := hX
  rcases hnat with ⟨n, hn, halt⟩ | ⟨n, hn, hsl⟩
  · exact Or.inl (center_eq_bot_of_alt Y hV hshort hn halt)
  · rcases center_cases_of_sl Y hM4 hV hshort hn hsl with h | ⟨rfl, hiso, hcard, hfix⟩
    · exact Or.inl h
    · refine Or.inr ⟨hiso, hcard, hsl, ?_⟩
      exact Subgroup.card_le_of_le (commV_center_le Y hfix)

end Yu

end CFSG.CGT.PushingUpLit.CGT6
