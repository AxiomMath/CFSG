module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93WO2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUMuRest
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3T6.Mu CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section W

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem wUnique_conj (hΩ : HypOmegaGen Φ) {V : Subgroup X} (hV : WSet Φ = {V}) (x : X) :
    conjSub x V = V := by
  have hVW : V ∈ WSet Φ := by rw [hV]; exact Set.mem_singleton V
  have hinv : (MulAut.conj x).symm = MulAut.conj x⁻¹ := by
    ext y
    simp [MulAut.conj_symm_apply]
  have h := Pf93.map_mem_WSet_equiv (MulAut.conj x) (Ω := Φ)
    (fun J hJ => hΩ.conjInvariant x J hJ)
    (fun J hJ => by rw [hinv]; exact hΩ.conjInvariant x⁻¹ J hJ) hVW
  rw [hV] at h
  exact h

theorem exists_rep_member (hP : Q3CL.PartIHypG Φ) {V : Subgroup X} (hVW : V ∈ WSet Φ)
    (hVn : ∀ x : X, conjSub x V = V) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) {K : Subgroup X} (hK : K ∈ Φ) :
    ∃ ρ : Rep Φ V, ρ.K = K := by
  have hRK : IsSylow2In K K := TL4.Vtx.isSylow2In_self (h2 K hK)
  have hR : K ∈ DSet Φ V := by
    refine ⟨mem_RSet_of_isSylow2In hK hRK, fun x hx => ?_⟩
    exact mem_normalizer_iff_conjSub_eq.mpr (hVn x)
  exact ⟨Q3CL.T8.mkRep hP hVW hK hR hRK, rfl⟩

theorem wUnique_card_le (hP : Q3CL.PartIHypG Φ) {V : Subgroup X} (hV : WSet Φ = {V})
    (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hTO : TwinOnlyNbr Φ)
    {A A' B : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hB : B ∈ Φ) (hAB : B ≠ A) (hA'B : B ≠ A')
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A') (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A) :
    Φ.ncard ≤ 6 := by
  classical
  have hΩ := hP.hyp
  have hVW : V ∈ WSet Φ := by rw [hV]; exact Set.mem_singleton V
  have hVn := wUnique_conj hΩ hV
  have repOf : ∀ K ∈ Φ, ∃ ρ : Rep Φ V, ρ.K = K := fun K hK =>
    exists_rep_member hP hVW hVn h2 hK
  obtain ⟨ρA, hρA⟩ := repOf A hA
  obtain ⟨ρB, hρB⟩ := repOf B hB
  haveI : Nonempty (Rep Φ V) := ⟨ρA⟩
  choose! ρ hρ using repOf
  have hne : ρA.K ≠ ρB.K := by rw [hρA, hρB]; exact hAB.symm
  have hstar : ρB.K ∈ omegaStarNbr Φ ρA.K := muTab_omegaStar hP hVW ρA ρB hne
  rw [hρA, hρB] at hstar
  have hcomp : dComp Φ A ≠ dstarComp Φ A := by
    intro heq
    have hBd : B ∈ dstarComp Φ A := Relation.ReflTransGen.single ⟨hB, Or.inl hstar⟩
    rw [← heq] at hBd
    rcases Sec.dComp_subset_pair hΩ hA hA' hnb hnb' hBd with h | h
    · exact hAB h
    · exact hA'B h
  have hnc : ¬ DbarConnected Φ V := not_dbarConnected_of_shape hP hVW hA hcomp
  obtain ⟨a, ha, hconn⟩ := exists_not_conn_at hP hVW hnc (muTabElt ρA)
  have hpl : Star3T.IsPlane (muDelta Φ V) (muTabElt ρA) a (muTabElt ρA * a * muTabElt ρA) :=
    ⟨muTabElt_mem ρA, ha, hconn, rfl⟩
  have h3 := (isTT_muDelta hP hVW).ncard_eq_three_mul (isStar_muDelta (Q3CL.T8.ctxOf hP hVW)) hpl
  have hcent := ncard_cent_le hP hVW ρA (n := 1) (by
    rw [Set.ncard_le_one_iff]
    intro a b ha hb
    rw [hρA] at ha hb
    exact hTO A hA a ha b hb)
  have hD : (muDelta Φ V).ncard ≤ 6 := by omega
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun K => muTabElt (ρ K))
    (fun K _ => muTabElt_mem (ρ K)) (fun K hK L hL h => ?_) (Set.toFinite _)) hD
  have := (muTabElt_eq_iff hP hVW (ρ K) (ρ L)).mp h
  rwa [hρ K hK, hρ L hL] at this

theorem two_mul_conjugates_le (hΩ : HypOmegaGen Φ) {A A' : Subgroup X} {z : X} (hA : A ∈ Φ)
    (hA' : A' ∈ Φ) (hne : A ≠ A') (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z) :
    2 * (conjugatesOf z).ncard ≤ Φ.ncard := by
  classical
  have hc : ∀ w ∈ conjugatesOf z, ∃ c : X, c * z * c⁻¹ = w := fun w hw => isConj_iff.mp hw
  choose! c hc using hc
  have hinv₁ : ∀ w ∈ conjugatesOf z, IsUniqueInvolution (conjSub (c w) A) w := fun w hw => by
    have := hzA.conj (c w)
    rwa [hc w hw] at this
  have hinv₂ : ∀ w ∈ conjugatesOf z, IsUniqueInvolution (conjSub (c w) A') w := fun w hw => by
    have := hzA'.conj (c w)
    rwa [hc w hw] at this
  have hinj₁ : Set.InjOn (fun w => conjSub (c w) A) (conjugatesOf z) := by
    intro w hw w' hw' h
    have h1 := hinv₁ w hw
    have h2 := hinv₁ w' hw'
    simp only at h
    rw [h] at h1
    exact h1.eq h2
  have hinj₂ : Set.InjOn (fun w => conjSub (c w) A') (conjugatesOf z) := by
    intro w hw w' hw' h
    have h1 := hinv₂ w hw
    have h2 := hinv₂ w' hw'
    simp only at h
    rw [h] at h1
    exact h1.eq h2
  have hdisj : Disjoint ((fun w => conjSub (c w) A) '' conjugatesOf z)
      ((fun w => conjSub (c w) A') '' conjugatesOf z) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', h⟩
    have h1 := hinv₁ w hw
    have h2 := hinv₂ w' hw'
    simp only at h
    rw [← h] at h1
    have hww : w = w' := h1.eq h2
    subst hww
    exact hne ((conjSub_inj (c w)).mp h).symm
  have hsub : (fun w => conjSub (c w) A) '' conjugatesOf z ∪
      (fun w => conjSub (c w) A') '' conjugatesOf z ⊆ Φ := by
    rintro _ (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact hΩ.conjInvariant (c w) A hA
    · exact hΩ.conjInvariant (c w) A' hA'
  calc 2 * (conjugatesOf z).ncard
      = ((fun w => conjSub (c w) A) '' conjugatesOf z).ncard +
          ((fun w => conjSub (c w) A') '' conjugatesOf z).ncard := by
        rw [hinj₁.ncard_image, hinj₂.ncard_image]; ring
    _ = (((fun w => conjSub (c w) A) '' conjugatesOf z) ∪
          ((fun w => conjSub (c w) A') '' conjugatesOf z)).ncard :=
        (Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)).symm
    _ ≤ Φ.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem exists_mem_centralizer_not (hS : Q8Section X Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J)
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (F : Asc77.TwinFrame Φ A A' B z u₁ u₂ τ ε)
    (hAA' : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) :
    ∃ r : X, r ∈ Subgroup.centralizer ({z} : Set X) ∧ r ∉ Subgroup.centralizer ({τ} : Set X) := by
  classical
  obtain ⟨e⟩ := hS.q8 A F.hA A (TL4.Vtx.isSylow2In_self (h2 A F.hA))
  have key : ∀ x : QuaternionGroup 2, x * x ≠ 1 → ∃ y : QuaternionGroup 2, y * x * y⁻¹ = x⁻¹ := by
    decide
  have hsq : e ⟨u₁, F.h₁⟩ * e ⟨u₁, F.h₁⟩ ≠ 1 := by
    intro h
    have h1 : (⟨u₁, F.h₁⟩ * ⟨u₁, F.h₁⟩ : ↥A) = 1 := e.injective (by rw [← map_mul, ← map_one e] at h; exact h)
    have h' : u₁ * u₁ = 1 := congrArg Subtype.val h1
    exact F.hzA.ne_one (F.o₁ ▸ h')
  obtain ⟨y, hy⟩ := key _ hsq
  set r : ↥A := e.symm y with hr
  have hrinv : r * ⟨u₁, F.h₁⟩ * r⁻¹ = ⟨u₁, F.h₁⟩⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv, hr, MulEquiv.apply_symm_apply, hy]
  have hrinv' : (r : X) * u₁ * (r : X)⁻¹ = u₁⁻¹ := congrArg Subtype.val hrinv
  have hrA : (r : X) ∈ A := r.2
  refine ⟨r, Subgroup.mem_centralizer_singleton_iff.mpr (F.hzA.commute_of_mem hrA).symm, ?_⟩
  intro hrτ
  have hτ : (r : X) * τ = τ * (r : X) := Subgroup.mem_centralizer_singleton_iff.mp hrτ
  have hu₂ : (r : X) * u₂ = u₂ * (r : X) := hAA' _ hrA u₂ F.h₂
  have hε : (r : X) * ε = ε * (r : X) := Subgroup.mem_center_iff.mp F.he r
  have h1 : (r : X) * τ * (r : X)⁻¹ = u₁⁻¹ * u₂ * ε := by
    rw [F.hrel]
    calc (r : X) * (u₁ * u₂ * ε) * (r : X)⁻¹
        = ((r : X) * u₁ * (r : X)⁻¹) * ((r : X) * u₂ * (r : X)⁻¹) * ((r : X) * ε * (r : X)⁻¹) := by
          group
      _ = u₁⁻¹ * u₂ * ε := by
          rw [hrinv', hu₂, hε]; group
  have h3 : (r : X) * τ * (r : X)⁻¹ = τ := by
    rw [hτ]; group
  rw [h3, F.hrel] at h1
  have h4 : u₁ * (u₂ * ε) = u₁⁻¹ * (u₂ * ε) := by
    calc u₁ * (u₂ * ε) = u₁ * u₂ * ε := by group
      _ = u₁⁻¹ * u₂ * ε := h1
      _ = u₁⁻¹ * (u₂ * ε) := by group
  have h5 : u₁ = u₁⁻¹ := mul_right_cancel h4
  have h6 : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = u₁ * u₁⁻¹ := by rw [← h5]
      _ = 1 := mul_inv_cancel u₁
  exact F.hzA.ne_one (F.o₁ ▸ h6)

theorem gen_of_wUnique (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hTO : TwinOnlyNbr Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J)
    {V : Subgroup X} (hV : WSet Φ = {V})
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (F : Asc77.TwinFrame Φ A A' B z u₁ u₂ τ ε)
    (hAA' : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A) (hτz : τ ≠ z) :
    ∀ g : X, g ∈ Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({τ} : Set X) := by
  classical
  have hΩ := hS.hyp
  have hPΦ : Q3CL.PartIHypG Φ := ⟨hΩ, TC.Thin.classicalClause_of_two hΩ h2, hS.aEmpty⟩
  have hBA : B ≠ A := fun h => hτz (F.htB.eq (h ▸ F.hzA))
  have hBA' : B ≠ A' := fun h => hτz (F.htB.eq (h ▸ F.hzA'))
  have hcard := wUnique_card_le hPΦ hV h2 hTO F.hA F.hA' F.hB hBA hBA' hnb hnb'
  have h2I := two_mul_conjugates_le hΩ F.hA F.hA' F.hne F.hzA F.hzA'
  obtain ⟨x, hx⟩ := htrans A F.hA B F.hB
  have hτx : x * z * x⁻¹ = τ := by
    have := F.hzA.conj x
    rw [hx] at this
    exact this.eq F.htB
  have hconjτ : IsConj z τ := isConj_iff.mpr ⟨x, hτx⟩
  have hzmem : z ∈ conjugatesOf z := IsConj.refl z
  have hτmem : τ ∈ conjugatesOf z := hconjτ
  have hI2 : 2 ≤ (conjugatesOf z).ncard := by
    have h := Set.ncard_le_ncard (show ({z, τ} : Set X) ⊆ conjugatesOf z from by
      intro w hw
      rcases hw with rfl | rfl
      · exact hzmem
      · exact hτmem) (Set.toFinite _)
    rwa [Set.ncard_pair (Ne.symm hτz)] at h
  have hI3 : (conjugatesOf z).ncard ≤ 3 := by omega
  have hidx : (Subgroup.centralizer ({τ} : Set X)).index = (conjugatesOf z).ncard := by
    rw [Subgroup.index_centralizer_eq_ncard, ← hconjτ.conjugatesOf_eq]
  have hprime : Nat.Prime (conjugatesOf z).ncard := by
    have : (conjugatesOf z).ncard = 2 ∨ (conjugatesOf z).ncard = 3 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  obtain ⟨r, hrC, hrτ⟩ := exists_mem_centralizer_not hS h2 F hAA'
  intro g
  have hle : Subgroup.centralizer ({τ} : Set X) ≤
      Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({τ} : Set X) := le_sup_right
  have h1 := Subgroup.relIndex_mul_index hle
  rw [hidx] at h1
  rcases (Nat.dvd_prime hprime).mp (Dvd.intro_left _ h1) with h | h
  · have := Subgroup.index_eq_one.mp h
    rw [this]
    exact Subgroup.mem_top g
  · exfalso
    rw [h] at h1
    have hrel : (Subgroup.centralizer ({τ} : Set X)).relIndex
        (Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({τ} : Set X)) = 1 :=
      Nat.eq_of_mul_eq_mul_right hprime.pos (by rw [one_mul]; exact h1)
    have hle' := Subgroup.relIndex_eq_one.mp hrel
    exact hrτ (hle' (Subgroup.mem_sup_left hrC))

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX
