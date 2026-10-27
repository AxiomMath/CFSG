module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ1
public import CFSG.Walter.J1Props.Aut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Walter.J1Props

section Janko

theorem involutionCentralizerComponent_of_janko {X : Type} [Group X] [Finite X]
    (h : JankoHyp₀ X) (hconj : ∀ s t : X, orderOf s = 2 → orderOf t = 2 → IsConj s t) :
    InvolutionCentralizerComponent X := by
  intro t' ht1 ht2
  have hord' : orderOf t' = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj h.t t' h.orderOf_t hord')
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hFsimple : IsSimpleGroup h.F := h.iso.isSimpleGroup
  have hFperf : Group.IsPerfect h.F := by
    have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.ofSurjective (f := h.iso.symm.toMonoidHom) h.iso.symm.surjective
  have hFcomm : ⁅h.F, h.F⁆ = h.F := Subgroup.commutator_eq_self
  have hFcard : Nat.card h.F = 60 := by
    rw [Nat.card_congr h.iso.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hFne : h.F ≠ ⊥ := by
    intro hbot
    have : Nat.card h.F = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hFt : ∀ f ∈ h.F, f * h.t = h.t * f := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hf)
  have htN : h.t ∈ Subgroup.normalizer (h.F : Set X) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hFt)
  have hcen : ∀ z : X, z * h.t = h.t * z → z ∈ Subgroup.normalizer (h.F : Set X) := by
    intro z hz
    have hz' : z ∈ Subgroup.zpowers h.t ⊔ h.F := by
      rw [← h.centralizer_eq]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hz
    have hle : Subgroup.zpowers h.t ⊔ h.F ≤ Subgroup.normalizer (h.F : Set X) :=
      sup_le (Subgroup.zpowers_le.mpr htN) Subgroup.le_normalizer
    exact hle hz'
  let f : X →* X := (MulAut.conj c).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.conj c).injective
  refine ⟨h.F.map f, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hFne ((Subgroup.map_eq_bot_iff_of_injective (f := f) _ hfinj).mp hbot)
  · rw [← Subgroup.map_commutator, hFcomm]
  · rintro _ ⟨a, ha, rfl⟩
    have h1 := hFt a ha
    have h2 : f a * t' = t' * f a := by
      rw [← hc]
      show c * a * c⁻¹ * (c * h.t * c⁻¹) = c * h.t * c⁻¹ * (c * a * c⁻¹)
      calc c * a * c⁻¹ * (c * h.t * c⁻¹) = c * (a * h.t) * c⁻¹ := by group
        _ = c * (h.t * a) * c⁻¹ := by rw [h1]
        _ = c * h.t * c⁻¹ * (c * a * c⁻¹) := by group
    exact h2
  · rintro z hz _ ⟨a, ha, rfl⟩
    have hz' : (c⁻¹ * z * c) * h.t = h.t * (c⁻¹ * z * c) := by
      rw [← hc] at hz
      calc c⁻¹ * z * c * h.t = c⁻¹ * (z * (c * h.t * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * h.t * c⁻¹) * z) * c := by rw [hz]
        _ = h.t * (c⁻¹ * z * c) := by group
    have hN := hcen _ hz'
    have h3 : (c⁻¹ * z * c)⁻¹ * a * (c⁻¹ * z * c) ∈ h.F := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (h.F : Set X)).inv_mem hN) a).mp ha
      simpa using this
    refine ⟨(c⁻¹ * z * c)⁻¹ * a * (c⁻¹ * z * c), h3, ?_⟩
    show c * ((c⁻¹ * z * c)⁻¹ * a * (c⁻¹ * z * c)) * c⁻¹ = z⁻¹ * (c * a * c⁻¹) * z
    group
  · intro M hMA hMn hMp
    let g : X →* X := (MulAut.conj c⁻¹).toMonoidHom
    have hMF : ∀ m ∈ M, c⁻¹ * m * c ∈ h.F := by
      intro m hm
      obtain ⟨a, ha, hma⟩ := hMA hm
      have : c⁻¹ * m * c = a := by
        rw [← hma]
        show c⁻¹ * (c * a * c⁻¹) * c = a
        group
      rw [this]
      exact ha
    have hMp' : IsPGroup 2 (M.map g) := hMp.map g
    have hginj : Function.Injective g := (MulAut.conj c⁻¹).injective
    let N : Subgroup h.F := (M.map g).subgroupOf h.F
    have hNn : N.Normal := by
      refine ⟨fun n hn y => ?_⟩
      obtain ⟨m, hm, hmn⟩ := (show (n : X) ∈ M.map g from hn)
      have hy : f (y : X) ∈ h.F.map f := ⟨y, y.2, rfl⟩
      have hym : f (y : X) * m * (f (y : X))⁻¹ ∈ M := by
        have := hMn _ ((h.F.map f).inv_mem hy) m hm
        simpa using this
      show (y : X) * (n : X) * (y : X)⁻¹ ∈ M.map g
      refine ⟨f y * m * (f y)⁻¹, hym, ?_⟩
      rw [← hmn]
      simp only [g, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
      group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
    · rw [eq_bot_iff]
      intro m hm
      have hgm : g m ∈ M.map g := ⟨m, hm, rfl⟩
      have hgmF : g m ∈ h.F := by
        have := hMF m hm
        simpa [g, MulAut.conj_apply] using this
      have h4 : (⟨g m, hgmF⟩ : h.F) ∈ N := hgm
      rw [hN, Subgroup.mem_bot] at h4
      have h1 : g m = 1 := congrArg Subtype.val h4
      exact Subgroup.mem_bot.mpr (hginj (h1.trans (map_one g).symm))
    · exfalso
      have hle : h.F ≤ M.map g := fun y hy => by
        have h4 : (⟨y, hy⟩ : h.F) ∈ N := by rw [hN]; exact Subgroup.mem_top _
        exact h4
      have hpF : IsPGroup 2 h.F := IsPGroup.to_le hMp' hle
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpF
      have h3 : 3 ∣ 2 ^ n := by rw [← hn, hFcard]; norm_num
      have h5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega

end Janko

section Model

theorem autInner_walterJ1 :
    ∀ β : walterJ1 ≃* walterJ1, ∃ x : walterJ1, ∀ y, β y = x⁻¹ * y * x := by
  intro β
  obtain ⟨g, hg⟩ := J3_aut β
  refine ⟨g⁻¹, fun y => ?_⟩
  rw [hg]
  simp [MulAut.conj_apply]

theorem involutionCentralizerComponent_walterJ1
    : InvolutionCentralizerComponent walterJ1 :=
  involutionCentralizerComponent_of_janko jankoHyp₀ fun _ _ hs ht => J1_isConj_involutions hs ht

theorem autInner_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ β : Y ≃* Y, ∃ x : Y, ∀ y, β y = x⁻¹ * y * x) :
    ∀ β : X ≃* X, ∃ x : X, ∀ y, β y = x⁻¹ * y * x := by
  intro β
  obtain ⟨x, hx⟩ := h (e.symm.trans (β.trans e))
  refine ⟨e.symm x, fun y => ?_⟩
  have h1 := hx (e y)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  apply e.injective
  rw [h1]
  simp

theorem false_of_J1_component
    {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) (e : (L ⧸ Subgroup.center L) ≃* walterJ1)
    {w : G} (hwU : w ∈ U) (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G))
    (hchar : CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G))) : False :=
  false_of_charTwo_inner h.elem (Subgroup.isPerfect_iff.mpr h.perfect) h.normalizes
    (autInner_of_mulEquiv e autInner_walterJ1)
    (InvolutionCentralizerComponent.of_mulEquiv e involutionCentralizerComponent_walterJ1)
    hwU hnc hchar

end Model

end CFSG.QuasithinUnique.K1
