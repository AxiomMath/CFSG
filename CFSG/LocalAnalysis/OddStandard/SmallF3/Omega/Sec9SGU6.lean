module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGT0
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

theorem sec9u_exists_E16_commute (hT6 : Asc82Tab6M) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsOm6M L) {B : Subgroup G} (hBL : B ≤ L) (hB : IsElemAb2 B 4) {s : G}
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) {α : ℤˣ}
    (hs : InducesTypeSome L s 6 (-1) 3 α) :
    ∃ B' : Subgroup G, B' ≤ L ∧ IsElemAb2 B' 4 ∧ ∀ b ∈ B', s * b = b * s := by
  have hBp : IsPGroup 2 B := IsPGroup.of_card (n := 4) hB.2
  obtain ⟨P, hP, hBP⟩ := sec68_exists_sylow_ge hBp hBL
  obtain ⟨V, _, _, _, Q, hQ, e, hm, F, hF16, hlift, hFB, hBF⟩ :=
    sec9g_model_E16 hT6 G L hL P hP B hBP hB
  have hLperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  let hBN : B ≤ Subgroup.normalizer (L : Set G) :=
    hBP.trans (hP.1.trans Subgroup.le_normalizer)
  have hx : SimHasDim (ffInducesHom hm e ⟨s, hsN⟩) 3 :=
    simHasDim_of_inducesTypeSome hm e hsN hs
  obtain ⟨δ, hδ⟩ := sec9u_exists_conj_cent hQ hm.1 F hF16 hlift hx
  let F'' : Subgroup (ProjSim Q) := F.map (MulAut.conj δ).toMonoidHom
  have hFΩ : ∀ f ∈ F, SimInOmegaStar hQ f := by
    intro f hf
    obtain ⟨b, hb, hbf⟩ := hBF f hf
    rw [← hbf, ffInducesHom_of_mem hm e ⟨b, hBL hb⟩ (hBN hb)]
    exact ⟨(e (QuotientGroup.mk (⟨b, hBL hb⟩ : ↥L)) : omegaProj hQ),
      (e (QuotientGroup.mk (⟨b, hBL hb⟩ : ↥L))).2, rfl⟩
  have hFcomm : ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ * f₂ = f₂ * f₁ := by
    intro f₁ h₁ f₂ h₂
    obtain ⟨b₁, hb₁, hbf₁⟩ := hBF f₁ h₁
    obtain ⟨b₂, hb₂, hbf₂⟩ := hBF f₂ h₂
    have hbb : b₁ * b₂ = b₂ * b₁ := by
      have hcommB : (⟨b₁, hb₁⟩ : ↥B) * ⟨b₂, hb₂⟩ = ⟨b₂, hb₂⟩ * ⟨b₁, hb₁⟩ := by
        haveI : IsMulCommutative ↥B := hB.1.1
        exact mul_comm' _ _
      simpa using congrArg Subtype.val hcommB
    calc f₁ * f₂
        = ffInducesHom hm e ⟨b₁, hBN hb₁⟩ * ffInducesHom hm e ⟨b₂, hBN hb₂⟩ := by
          rw [← hbf₁, ← hbf₂]
      _ = ffInducesHom hm e (⟨b₁, hBN hb₁⟩ * ⟨b₂, hBN hb₂⟩) := (map_mul _ _ _).symm
      _ = ffInducesHom hm e (⟨b₂, hBN hb₂⟩ * ⟨b₁, hBN hb₁⟩) := by
          apply congrArg (ffInducesHom hm e)
          apply Subtype.ext
          simpa using hbb
      _ = ffInducesHom hm e ⟨b₂, hBN hb₂⟩ * ffInducesHom hm e ⟨b₁, hBN hb₁⟩ :=
          map_mul _ _ _
      _ = f₂ * f₁ := by rw [hbf₂, hbf₁]
  have hFsq : ∀ f ∈ F, f * f = 1 := by
    intro f hf
    obtain ⟨b, hb, hbf⟩ := hBF f hf
    have hb2 : (⟨b, hBN hb⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨b, hBN hb⟩ = 1 := by
      apply Subtype.ext
      have h := hB.1.2 b hb
      simpa [pow_two] using h
    calc f * f
        = ffInducesHom hm e ⟨b, hBN hb⟩ * ffInducesHom hm e ⟨b, hBN hb⟩ := by rw [← hbf]
      _ = ffInducesHom hm e (⟨b, hBN hb⟩ * ⟨b, hBN hb⟩) := (map_mul _ _ _).symm
      _ = ffInducesHom hm e 1 := by rw [hb2]
      _ = 1 := map_one _
  have hF''16 : Nat.card F'' = 2 ^ 4 := by
    change Nat.card (F.map (MulAut.conj δ).toMonoidHom) = 2 ^ 4
    have hinj : Function.Injective (MulAut.conj δ).toMonoidHom :=
      fun _ _ h => (MulAut.conj δ).injective h
    rw [Subgroup.card_map_of_injective hinj, hF16]
  have hF''c : ∀ f₁ ∈ F'', ∀ f₂ ∈ F'', f₁ * f₂ = f₂ * f₁ := by
    intro f₁ h₁ f₂ h₂
    obtain ⟨g₁, hg₁, hg₁eq⟩ := Subgroup.mem_map.mp h₁
    obtain ⟨g₂, hg₂, hg₂eq⟩ := Subgroup.mem_map.mp h₂
    rw [← hg₁eq, ← hg₂eq, ← map_mul, ← map_mul, hFcomm g₁ hg₁ g₂ hg₂]
  have hF''sq : ∀ f ∈ F'', f * f = 1 := by
    intro f hf
    obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp hf
    rw [← hgeq, ← map_mul, hFsq g hg, map_one]
  have hF''Ω : ∀ f ∈ F'', SimInOmegaStar hQ f := by
    intro f hf
    obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp hf
    rw [← hgeq]
    have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hm.1]; norm_num
    have h := sec9u_simInOmegaStar_conj hQ h2 δ (hFΩ g hg)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  obtain ⟨B', hB'L, hB'E, hB'F⟩ :=
    sec9u_lift_E16 hL hm e F'' hF''16 hF''c hF''sq hF''Ω
  refine ⟨B', hB'L, hB'E, ?_⟩
  intro b hb
  have hbL : b ∈ L := hB'L hb
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hbL
  have hfF'' : ffInducesHom hm e ⟨b, hbN⟩ ∈ F'' := hB'F b hb
  obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp hfF''
  have hxf : ffInducesHom hm e ⟨s, hsN⟩ * ffInducesHom hm e ⟨b, hbN⟩ =
      ffInducesHom hm e ⟨b, hbN⟩ * ffInducesHom hm e ⟨s, hsN⟩ := by
    have h := hδ g hg
    rw [← hgeq]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  set c : G := s * b * s⁻¹ * b⁻¹ with hcdef
  have hcL : c ∈ L := by
    have hsb : s * b * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN b).mp hbL
    rw [hcdef]
    exact L.mul_mem hsb (L.inv_mem hbL)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hcL
  have hΦc : ffInducesHom hm e ⟨c, hcN⟩ = 1 := by
    have hceq : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨s, hsN⟩ * ⟨b, hbN⟩ * ⟨s, hsN⟩⁻¹ * ⟨b, hbN⟩⁻¹ := Subtype.ext rfl
    rw [hceq]
    simp only [map_mul, map_inv]
    rw [hxf]
    group
  have hcCent : c ∈ Subgroup.centralizer (L : Set G) :=
    (ffInducesHom_eq_one_iff hm e hLperf ⟨c, hcN⟩).mp hΦc
  have hcCenterIn : c ∈ centerIn L :=
    (sec4_mem_centerIn_iff c).mpr ⟨hcL, fun k hk =>
      (Subgroup.mem_centralizer_iff.mp hcCent k hk).symm⟩
  rw [hcdef] at hcCenterIn
  have hb2 : b * b = 1 := by
    have h := hB'E.1.2 b hb
    rwa [pow_two] at h
  exact sec9g_commute_of_commutator_central hL hsN hbL hb2 hcCenterIn

end CFSG.OddStandard.SmallF3.Omega
