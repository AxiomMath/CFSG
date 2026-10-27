module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.One
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.FourClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Action
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover

theorem exists_covering_of_check {Q : RawSchreierDatum 24} (hQ : ValidSchreier Q)
    {gs reps : List (Equiv.Perm (Fin 24))}
    (hgs : Q.originalSubgroup = Subgroup.closure {g | g ∈ gs})
    (hreps : ∀ r ∈ reps, ∃ w, r = evalCodes gs w)
    (hok : repsOK 24 (listTables gs) (listTables (gs.map (·⁻¹))) (cosetOrderTables Q 1 4)
      (reps.map toTable) 1000 = true)
    (hord : (reps.map toTable).all (ordTest 24 4) = true) :
    ∀ x ∈ Q.originalSubgroup, orderOf x = 4 →
      ∃ r ∈ reps, ∃ c ∈ Q.originalSubgroup, x = c * r * c⁻¹ := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hgs' : ∀ g ∈ gs, g ∈ Q.originalSubgroup := fun g hg => by
    rw [hgs]
    exact Subgroup.subset_closure hg
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn Q hQ (listTables_spec hn hgs') 1
    (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh) (by norm_num) reps
    (fun r hr => ⟨by
      obtain ⟨w, rfl⟩ := hreps r hr
      simpa using evalCodes_mem _ hgs' w,
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
        (List.all_eq_true.1 hord _ (List.mem_map_of_mem hr))⟩) 1000 hok
  intro x hx h4
  exact hcov x (by simpa using hx) h4

theorem q5Q_orderOf_ne_four :
    ∀ x ∈ q5Q.originalSubgroup, orderOf x ≠ 4 := by
  have h := checkQ5_eq
  simp only [checkQ5, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hc, ho⟩, hcomm⟩, hok⟩ := h
  intro x hx h4
  obtain ⟨r, hr, -⟩ := exists_covering_of_check (reps := []) hc
    (by rw [q5Q, certificate_originalSubgroup]) (by simp) (by simpa using hok) (by simp) x hx h4
  simp at hr

theorem fewFour_q4Q : FewFour 3 q4Q.originalSubgroup := by
  have h := checkQ4_eq
  simp only [checkQ4, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hc, ho⟩, hcomm⟩, hok⟩, hsz⟩, hord⟩ := h
  refine ⟨q4Reps.toFinset, (List.toFinset_card_le _).trans (by simp [q4Reps]), ?_⟩
  intro x hx h4
  obtain ⟨r, hr, c, hcQ, hxr⟩ := exists_covering_of_check hc
    (by rw [q4Q, certificate_originalSubgroup]) (fun r hr => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
      exact ⟨w, rfl⟩) hok hord x hx h4
  exact ⟨r, List.mem_toFinset.2 hr, c, hcQ, hxr⟩

@[expose] noncomputable def m12Rho
    {G : Type} [Group G] (S : Subgroup G) [S.Normal]
    (ψ : ↥S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) : G →* ↥autModel :=
  CFSG.EvenSporadicStandard.HSStd.HL34.rho S ψ autModelEquiv

theorem m12Rho_injective
    {G : Type} [Group G] (S : Subgroup G) [S.Normal]
    (ψ : ↥S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) (hcent : centralizer (S : Set G) = ⊥) :
    Function.Injective (m12Rho S ψ) :=
  CFSG.EvenSporadicStandard.HSStd.HL34.rho_injective S ψ autModelEquiv hcent

theorem m12Rho_bijective_of_ne_top
    {G : Type} [Group G] [Finite G] (S : Subgroup G) [S.Normal]
    (ψ : ↥S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) (hcent : centralizer (S : Set G) = ⊥)
    (hne : S ≠ ⊤) : Function.Bijective (m12Rho S ψ) := by
  refine (m12Rho_injective S ψ hcent).bijective_of_nat_card_le ?_
  have hS : Nat.card ↥S = 95040 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have h1 : S.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have h0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : 2 ≤ S.index := by omega
  rw [card_autModel, ← S.card_mul_index, hS]
  calc 190080 = 95040 * 2 := by norm_num
    _ ≤ 95040 * S.index := Nat.mul_le_mul_left _ h2

theorem exists_rep_map
    {G : Type} [Group G] (S : Subgroup G) [S.Normal]
    (ψ : ↥S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) (hcent : centralizer (S : Set G) = ⊥)
    {t : G} (ht : orderOf t = 2) :
    ∃ r ∈ [m12A1, blockHom (permZ, permZ), m12Sigma],
      ∃ κ : ↥(centralizer ({t} : Set G)) →* ↥(centralizerIn autModel r),
        Function.Injective κ ∧ (Function.Surjective (m12Rho S ψ) → Function.Surjective κ) := by
  set ρ := m12Rho S ψ with hρ
  have hinj : Function.Injective ρ := m12Rho_injective S ψ hcent
  have h2 : orderOf ((ρ t : ↥autModel) : Equiv.Perm (Fin 24)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_injective ρ hinj, ht]
  obtain ⟨r, hr, c, hc, hδ⟩ := autModel_involution_cover (ρ t).2 h2
  refine ⟨r, hr, ?_⟩
  let f : ↥(centralizer ({t} : Set G)) →* Equiv.Perm (Fin 24) :=
    ((MulAut.conj c⁻¹).toMonoidHom.comp autModel.subtype).comp
      (ρ.comp (centralizer ({t} : Set G)).subtype)
  have hfapply : ∀ g : ↥(centralizer ({t} : Set G)),
      f g = c⁻¹ * ((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24)) * c := by
    intro g
    simp [f, MulAut.conj_apply]
  have hf : ∀ g : ↥(centralizer ({t} : Set G)), f g ∈ centralizerIn autModel r := by
    intro g
    rw [mem_centralizerIn, hfapply]
    refine ⟨autModel.mul_mem (autModel.mul_mem (autModel.inv_mem hc) (ρ (g : G)).2) hc, ?_⟩
    have hg : (g : G) * t = t * (g : G) := mem_centralizer_singleton_iff.1 g.2
    have key : ((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24)) * (c * r * c⁻¹) =
        (c * r * c⁻¹) * ((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24)) := by
      rw [← hδ]
      have := congrArg (fun z => ((ρ z : ↥autModel) : Equiv.Perm (Fin 24))) hg
      simpa using this
    calc c⁻¹ * ((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24)) * c * r
        = c⁻¹ * (((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24)) * (c * r * c⁻¹)) * c := by
          group
      _ = c⁻¹ * ((c * r * c⁻¹) * ((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24))) * c := by
          rw [key]
      _ = r * (c⁻¹ * ((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24)) * c) := by group
  refine ⟨f.codRestrict (centralizerIn autModel r) hf, ?_, ?_⟩
  · intro g g' hgg
    have h1 : f g = f g' := congrArg Subtype.val hgg
    rw [hfapply, hfapply] at h1
    have h3 : ((ρ (g : G) : ↥autModel) : Equiv.Perm (Fin 24)) =
        ((ρ (g' : G) : ↥autModel) : Equiv.Perm (Fin 24)) := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    exact Subtype.ext (hinj (Subtype.ext h3))
  · intro hsurj y
    have hy := y.2
    rw [mem_centralizerIn] at hy
    obtain ⟨hyA, hyr⟩ := hy
    have hzA : c * (y : Equiv.Perm (Fin 24)) * c⁻¹ ∈ autModel :=
      autModel.mul_mem (autModel.mul_mem hc hyA) (autModel.inv_mem hc)
    obtain ⟨g, hg⟩ := hsurj ⟨_, hzA⟩
    have hgt : g * t = t * g := by
      apply hinj
      rw [map_mul, map_mul, hg]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hδ]
      calc c * (y : Equiv.Perm (Fin 24)) * c⁻¹ * (c * r * c⁻¹)
          = c * ((y : Equiv.Perm (Fin 24)) * r) * c⁻¹ := by group
        _ = c * (r * (y : Equiv.Perm (Fin 24))) * c⁻¹ := by rw [hyr]
        _ = c * r * c⁻¹ * (c * (y : Equiv.Perm (Fin 24)) * c⁻¹) := by group
    refine ⟨⟨g, mem_centralizer_singleton_iff.2 hgt⟩, ?_⟩
    apply Subtype.ext
    show f ⟨g, _⟩ = (y : Equiv.Perm (Fin 24))
    rw [hfapply]
    simp only
    rw [hg]
    show c⁻¹ * (c * (y : Equiv.Perm (Fin 24)) * c⁻¹) * c = _
    group

theorem haradaM12_holds :
    HaradaM12 := by
  intro G _ _ S hSn ⟨ψ₀⟩ hcent t ht ⟨ζ⟩
  haveI := hSn
  by_contra hne
  let ψ : ↥S ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := ψ₀
  have hbij := m12Rho_bijective_of_ne_top S ψ hcent hne
  obtain ⟨r, hr, κ, hκi, hκs⟩ := exists_rep_map S ψ hcent ht
  have hκb : Function.Bijective κ := ⟨hκi, hκs hbij.2⟩
  have hcard : Nat.card ↥(centralizer ({t} : Set G)) = Nat.card ↥(centralizerIn autModel r) :=
    Nat.card_congr (Equiv.ofBijective κ hκb)
  have h240 := card_centralizer_of_equiv ζ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · obtain ⟨h1, h2, -⟩ := q2Q_spec
    rw [← h1, h2] at hcard
    omega
  · obtain ⟨h1, h2, -⟩ := q4Q_spec
    rw [← h1, h2] at hcard
    omega
  · obtain ⟨h1, -, -⟩ := q5Q_spec
    obtain ⟨x, hx⟩ := exists_orderOf_four_z2s5
    have hz : orderOf (ζ.symm x) = 4 := by rw [MulEquiv.orderOf_eq, hx]
    have hκz : orderOf ((κ (ζ.symm x) : ↥(centralizerIn autModel m12Sigma)) :
        Equiv.Perm (Fin 24)) = 4 := by
      rw [Subgroup.orderOf_coe, orderOf_injective κ hκi, hz]
    exact q5Q_orderOf_ne_four _ (by rw [h1]; exact (κ (ζ.symm x)).2) hκz

theorem noTwoCfgM12_holds :
    NoTwoCfgM12 := by
  intro G _ _ S hSn ⟨ψ₀⟩ hcent t v J h _
  haveI := hSn
  let ψ : ↥S ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := ψ₀
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  have h480 := h.card_centralizer htop
  obtain ⟨r, hr, κ, hκi, -⟩ := exists_rep_map S ψ hcent h.ht
  have hle : 480 ≤ Nat.card ↥(centralizerIn autModel r) := by
    rw [← h480]
    exact Nat.card_le_card_of_injective κ hκi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · obtain ⟨h1, h2, -⟩ := q2Q_spec
    rw [← h1, h2] at hle
    omega
  · obtain ⟨h1, h2, -⟩ := q4Q_spec
    have hcardQ : Nat.card ↥(centralizerIn autModel (blockHom (permZ, permZ))) = 480 := by
      rw [← h1, h2]
    have hκb : Function.Bijective κ :=
      hκi.bijective_of_nat_card_le (by rw [hcardQ, h480])
    have hF : FewFour 3 (centralizerIn autModel (blockHom (permZ, permZ))) := by
      rw [← h1]
      exact fewFour_q4Q
    exact h.false_of_fewFour htop (MulEquiv.ofBijective κ hκb) hF
  · obtain ⟨h1, h2, -⟩ := q5Q_spec
    rw [← h1, h2] at hle
    omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
