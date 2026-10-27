module

public import CFSG.LocalAnalysis.GLTheoremB.BaseCase
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools
public import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i116n_isComponentOf_of_glaPComponent {X : Type} [Group X] {p : ℕ} (hO : GLAPPrimeCore p X = ⊥)
    {L : Subgroup X} (hL : GLAPComponent p ⊤ L) : IsComponentOf L ⊤ := by
  have hcore : GLAPPrimeCore p ↥(⊤ : Subgroup X) = ⊥ := by
    have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)
    rw [hO] at h
    exact Subgroup.map_injective (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).injective
      (by simpa using h)
  have hker : GLAPPrimeCore p ↥(⊤ : Subgroup X) ≤ (⊤ : Subgroup X).subtype.ker := by
    rw [hcore]; exact bot_le
  let ψ : (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X)) →* X :=
    QuotientGroup.lift _ (⊤ : Subgroup X).subtype hker
  have hψc : ψ.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X))) =
      (⊤ : Subgroup X).subtype := by
    ext t; simp [ψ]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have ht : (t : X) = 1 := by
      have := congrArg (fun f => f t) hψc
      simp only [MonoidHom.comp_apply] at this
      rw [MonoidHom.mem_ker] at hq
      exact this.symm.trans hq
    have : t = 1 := Subtype.ext ht
    simp [this]
  have hsurj : Function.Surjective ψ := by
    intro x
    exact ⟨QuotientGroup.mk' _ ⟨x, trivial⟩, by
      have := congrArg (fun f => f ⟨x, trivial⟩) hψc
      simpa using this⟩
  let e := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hL.2.2.1
  have htop : (⊤ : Subgroup (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X))).map
      (e : _ →* X) = ⊤ := Subgroup.map_top_of_surjective _ e.surjective
  rw [htop, Subgroup.map_map] at h1
  have h2 : (e : _ →* X).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X))) =
      (⊤ : Subgroup X).subtype := hψc
  rw [h2, Subgroup.subgroupOf_map_subtype, inf_top_eq] at h1
  exact h1

theorem normalizes_of_noncentral_elt {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p X = ⊥) {L : Subgroup X} (hL : GLAPComponent p ⊤ L)
    {Y : Subgroup X} (hYc : Nat.Coprime p (Nat.card Y)) {x : X} (hxL : x ∈ L)
    (hxY : x ∈ Subgroup.normalizer (Y : Set X)) (hxord : orderOf x = p)
    (hxnc : ∃ l ∈ L, x * l ≠ l * x) : Y ≤ Subgroup.normalizer (L : Set X) := by
  intro y hy
  have _ := hp
  by_contra hyn
  have hLc := i116n_isComponentOf_of_glaPComponent hO hL
  have hL' : IsComponentOf (GLBConj y L) ⊤ :=
    CFSG.Quasithin.F918V5G.isComponentOf_map_conj hLc (m := y⁻¹) trivial
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hLc hL' with h | hcomm
  · exact hyn (mem_normalizer_iff_gLBConj_eq.2 h.symm)
  · set x' : X := y⁻¹ * x * y with hx'
    have hx'L' : x' ∈ GLBConj y L := by
      rw [mem_gLBConj]; simpa [hx', mul_assoc] using hxL
    have hxx' : x * x' = x' * x := hcomm x hxL x' hx'L'
    have hx'p : x' ^ p = 1 := by
      have : x' = MulAut.conj y⁻¹ x := by simp [hx']
      rw [this, ← map_pow, ← hxord, pow_orderOf_eq_one, map_one]
    have hxp : x ^ p = 1 := by rw [← hxord, pow_orderOf_eq_one]
    have hzY : x⁻¹ * x' ∈ Y := by
      have h1 : x⁻¹ * y⁻¹ * x ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hxY) y⁻¹).1 (inv_mem hy)
        simpa using this
      have := mul_mem h1 hy
      simpa [hx', mul_assoc] using this
    have hzp : (x⁻¹ * x') ^ p = 1 := by
      rw [((Commute.inv_left (hxx')).mul_pow p)]
      rw [inv_pow, hxp, hx'p]; simp
    have hz1 : x⁻¹ * x' = 1 := by
      set z : Y := ⟨x⁻¹ * x', hzY⟩
      have hzp' : z ^ p = 1 := Subtype.ext hzp
      have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp'
      have h2 : orderOf z ∣ Nat.card Y := orderOf_dvd_natCard z
      have h3 : orderOf z = 1 :=
        Nat.eq_one_of_dvd_coprimes hYc h1 h2
      have : z = 1 := orderOf_eq_one_iff.1 h3
      exact congrArg Subtype.val this
    have hxx : x' = x := by
      have := hz1
      rw [inv_mul_eq_one] at this
      exact this.symm
    obtain ⟨l, hl, hne⟩ := hxnc
    have hxL' : x ∈ GLBConj y L := hxx ▸ hx'L'
    exact hne (hcomm l hl x hxL').symm

theorem normalizes_pPrimeCore_centralizer_of_noncentral_elt {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥) {L : Subgroup X}
    (hL : GLAPComponent p ⊤ L) {B : Subgroup X} {x : X} (hxL : x ∈ L)
    (hxB : x ∈ Subgroup.normalizer (B : Set X)) (hxord : orderOf x = p)
    (hxnc : ∃ l ∈ L, x * l ≠ l * x) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (L : Set X) := by
  have hxY : x ∈ Subgroup.normalizer
      ((GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, gLBConj_centralizer,
      mem_normalizer_iff_gLBConj_eq.1 hxB]
  refine normalizes_of_noncentral_elt hp hO hL ?_ hxL hxY hxord hxnc
  exact (Nat.Prime.coprime_iff_not_dvd hp).2
    (not_dvd_card_glaPPrimeCoreOf hp (Subgroup.centralizer (B : Set X)))

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
