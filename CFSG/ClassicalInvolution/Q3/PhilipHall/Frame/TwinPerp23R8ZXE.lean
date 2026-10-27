module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZXThm2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Members
import CFSG.ClassicalInvolution.Sp62Rec.I1.KappaCount
import CFSG.ClassicalInvolution.Sp62Rec.I1.WsubMembersE64
import CFSG.ClassicalInvolution.Sp62Rec.SylowOfHat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance

section Count


theorem ncard_members_eq_six_of_labels {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {z e : G} {E B : Subgroup G} {f : ↥E →* AE.Wr 6}
    {Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Solomon73.Yamaki.Hhat} {φ : ↥B →* ↥Solomon73.Yamaki.Hhat}
    (D : Sp62Rec.I1Action z e E B f Θ φ) (ML : Sp62Rec.MemberLabels Ω E f)
    (hOe : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥)
    (hΩE : ∀ J ∈ Ω, J ≤ E ↔ J ≤ Subgroup.centralizer ({e} : Set G)) {T A : Subgroup G}
    (hTB : T ≤ B) (hT : Nat.card T = 512) (hAT : A ≤ T) (hA : Solomon73.IsE64 A)
    (huniq : ∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) :
    {J | J ∈ Ω ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
      J ≤ Subgroup.centralizer ({e} : Set G)}.ncard = 6 := by
  have hOE : oddCoreIn E = ⊥ := D.oddCoreIn_eq_bot hOe
  have hfi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, D.f_ker, hOE, Subgroup.bot_subgroupOf]
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, D.φ_ker, hOE, Subgroup.bot_subgroupOf]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥B →* ↥Sp62Rec.I1.Wsub, Ψ = Θ.symm.toMonoidHom.comp φ := ⟨_, rfl⟩
  have hΨi : Function.Injective Ψ := by
    rw [hΨ]
    exact Θ.symm.injective.comp hφi
  have hΨs : Function.Surjective Ψ := by
    rw [hΨ]
    exact Θ.symm.surjective.comp D.φ_surj
  have hmem : ∀ {J : Subgroup G}, J ≤ E → ∀ {M : Subgroup (AE.Wr 6)},
      (J.subgroupOf E).map f = M → (J.subgroupOf B).map Ψ = M.subgroupOf Sp62Rec.I1.Wsub := by
    intro J hJE M hM
    rw [hΨ]
    exact D.map_member_wsub hJE hM
  have hAB : A ≤ B := hAT.trans hTB
  have hT' : Nat.card ((T.subgroupOf B).map Ψ) = 512 := by
    rw [Subgroup.card_map_of_injective hΨi,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv, hT]
  have hAT' : (A.subgroupOf B).map Ψ ≤ (T.subgroupOf B).map Ψ :=
    Subgroup.map_mono fun b hb => hAT hb
  have hA' : Solomon73.IsE64 ((A.subgroupOf B).map Ψ) :=
    Sp62Rec.isE64_map_of_injective hΨi (Sp62Rec.isE64_comap_of_injective B.subtype_injective hA
      (by rw [Subgroup.range_subtype]; exact hAB))
  have huniq' : ∀ A' ≤ (T.subgroupOf B).map Ψ, Solomon73.IsE64 A' →
      A' = (A.subgroupOf B).map Ψ := by
    intro A' hA'T hA'
    have h1 : A'.comap Ψ ≤ T.subgroupOf B := by
      intro b hb
      obtain ⟨b', hb', hbb'⟩ := hA'T (Subgroup.mem_comap.mp hb)
      rw [← hΨi hbb']
      exact hb'
    have h2 : Solomon73.IsE64 (A'.comap Ψ) := Sp62Rec.isE64_comap_of_injective hΨi hA'
      (by rw [MonoidHom.range_eq_top_of_surjective _ hΨs]; exact le_top)
    have h3 := huniq _ (show (A'.comap Ψ).map B.subtype ≤ T by
        rintro _ ⟨b, hb, rfl⟩
        exact Subgroup.mem_subgroupOf.mp (h1 hb))
      (Sp62Rec.isE64_map_of_injective B.subtype_injective h2)
    have h4 : A'.comap Ψ = A.subgroupOf B := by
      rw [← Subgroup.comap_map_eq_self_of_injective B.subtype_injective (A'.comap Ψ), h3]
      rfl
    rw [← Subgroup.map_comap_eq_self_of_surjective hΨs A', h4]
  have hsix := Sp62Rec.I1.card_members_normalizing_e64 _ _ hT' hAT' hA' huniq'
  have key : ∀ J : Subgroup G, J ≤ B →
      ((J.subgroupOf B).map Ψ ≤ Subgroup.normalizer (((A.subgroupOf B).map Ψ :
        Subgroup ↥Sp62Rec.I1.Wsub) : Set ↥Sp62Rec.I1.Wsub) ↔
        J ≤ Subgroup.normalizer (A : Set G)) := by
    intro J hJB
    rw [← Subgroup.map_normalizer_eq_of_bijective _ ⟨hΨi, hΨs⟩,
      Subgroup.map_le_map_iff_of_injective hΨi]
    exact ⟨ZX.le_normalizer_of_subgroupOf hJB hAB,
      fun h => (Subgroup.comap_mono (f := B.subtype) h).trans
        (Subgroup.le_normalizer_comap B.subtype)⟩
  have hEC : E ≤ Subgroup.centralizer ({e} : Set G) := D.E_le_B.trans D.B_le
  have hsub : {J | J ∈ Ω ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
      J ≤ Subgroup.centralizer ({e} : Set G)} ⊆ {J | J ∈ Ω ∧ J ≤ E} :=
    fun J hJ => ⟨hJ.1, (hΩE J hJ.1).mpr hJ.2.2⟩
  have hFi : Set.InjOn (fun J : Subgroup G => (J.subgroupOf E).map f)
      {J | J ∈ Ω ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
        J ≤ Subgroup.centralizer ({e} : Set G)} :=
    (ML.bijOn hfi).injOn.mono hsub
  have hGi : Set.InjOn (fun L : Finset (Fin 6) × Bool =>
      if h : L.1.card = 4 then AE.memAt L.1 h L.2 else ⊥)
      {L : Finset (Fin 6) × Bool | ∃ h : L.1.card = 4,
        (AE.memAt L.1 h L.2).subgroupOf Sp62Rec.I1.Wsub ≤ Subgroup.normalizer
          (((A.subgroupOf B).map Ψ : Subgroup ↥Sp62Rec.I1.Wsub) : Set ↥Sp62Rec.I1.Wsub)} := by
    rintro L₁ ⟨h₁, -⟩ L₂ ⟨h₂, -⟩ h12
    have h12' : AE.memAt L₁.1 h₁ L₁.2 = AE.memAt L₂.1 h₂ L₂.2 := by
      simpa only [dif_pos h₁, dif_pos h₂] using h12
    refine Sp62Rec.I1.eq_of_forall_mem_iff h₁ h₂ fun x => ?_
    rw [← Sp62Rec.I1.mem_memAt_iff_mem_memAtL L₁.1 h₁ L₁.2 x,
      ← Sp62Rec.I1.mem_memAt_iff_mem_memAtL L₂.1 h₂ L₂.2 x, h12']
  have himg : (fun J : Subgroup G => (J.subgroupOf E).map f) ''
      {J | J ∈ Ω ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
        J ≤ Subgroup.centralizer ({e} : Set G)} =
      (fun L : Finset (Fin 6) × Bool => if h : L.1.card = 4 then AE.memAt L.1 h L.2 else ⊥) ''
      {L : Finset (Fin 6) × Bool | ∃ h : L.1.card = 4,
        (AE.memAt L.1 h L.2).subgroupOf Sp62Rec.I1.Wsub ≤ Subgroup.normalizer
          (((A.subgroupOf B).map Ψ : Subgroup ↥Sp62Rec.I1.Wsub) : Set ↥Sp62Rec.I1.Wsub)} := by
    ext M
    constructor
    · rintro ⟨J, ⟨hJ, hJN, hJC⟩, rfl⟩
      have hJE : J ≤ E := (hΩE J hJ).mpr hJC
      obtain ⟨α, h, b, hb⟩ := ML.label J hJ hJE
      refine ⟨(α, b), ⟨h, ?_⟩, ?_⟩
      · show (AE.memAt α h b).subgroupOf Sp62Rec.I1.Wsub ≤ _
        rw [← hmem hJE hb]
        exact (key J (hJE.trans D.E_le_B)).mpr hJN
      · show (if h : α.card = 4 then AE.memAt α h b else ⊥) = (J.subgroupOf E).map f
        rw [dif_pos h, hb]
    · rintro ⟨L, ⟨h, hLN⟩, rfl⟩
      obtain ⟨J, hJ, hJE, hb⟩ := ML.surj L.1 h L.2
      refine ⟨J, ⟨hJ, (key J (hJE.trans D.E_le_B)).mp ?_, hJE.trans hEC⟩, ?_⟩
      · rw [hmem hJE hb]
        exact hLN
      · show (J.subgroupOf E).map f = if h : L.1.card = 4 then AE.memAt L.1 h L.2 else ⊥
        rw [dif_pos h, hb]
  have hcount := hFi.ncard_image
  rw [himg, hGi.ncard_image] at hcount
  exact hcount.symm.trans hsix

end Count

section Leaf



variable {n : ℕ}

theorem ncard_members_normalizer_eq_six {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t e : Y} {Z : Subgroup Y} (hP : PerpHypS n Y R S t) (hAE : SecAE R e 6)
    (hI : I1In R t e Z) (hodd : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hOe : oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥) {T A : Subgroup Y}
    (hTB : T ≤ Z ⊔ rLayer (Om R) e) (hT : Nat.card T = 512) (hAT : A ≤ T)
    (hA : Solomon73.IsE64 A) (huniq : ∀ A' ≤ T, Solomon73.IsE64 A' → A' = A) :
    {J | J ∈ Om R ∧ J ≤ Subgroup.normalizer (A : Set Y) ∧
      J ≤ Subgroup.centralizer ({e} : Set Y)}.ncard = 6 := by
  obtain ⟨f, Θ, φ, D, ML⟩ := i1_action_memberLabels_final hP hAE hI hodd
  exact ncard_members_eq_six_of_labels D ML hOe
    (fun J hJ => le_rLayer_iff_le_centralizer hP (hI.Z_elem e hI.e_mem e hI.e_mem).2 hJ)
    hTB hT hAT hA huniq

section O2


theorem p23E8ZXE_proved (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) : P23E8ZXE n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZ hA6 Z hI _ hOe T A hTB hT512 hAT hA64 huniq
  have h6 := ncard_members_normalizer_eq_six hc.std.perp hA6 hI
    (p23E8Z_oddC_of_normT hE hT hα hN hcit hP hc hno hZ hA6).1 hOe hTB hT512 hAT hA64 huniq
  exact ⟨(show (3 : ℕ) ≤ 6 by norm_num).trans h6.ge, h6.le.trans (show (6 : ℕ) ≤ 9 by norm_num)⟩

end O2

end Leaf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
