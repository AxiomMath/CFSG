module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Assemble
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Purity
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section Generic

variable {G : Type*} [Group G]

theorem not_le_normalizer_of_simple_centralizer {F : Subgroup G} [IsSimpleGroup F]
    (hnc : ∃ x y : F, x * y ≠ y * x) (X : Subgroup G) {t : G} (htF : t ∈ F) (ht1 : t ≠ 1)
    (hXC : X ≤ Subgroup.centralizer ({t} : Set G))
    (hsolv : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (X : Set G) →
      Group.IsSolvable ↥(P ⊓ X) → Group.IsSolvable ↥P) :
    ¬ F ≤ Subgroup.normalizer (X : Set G) := by
  intro hFN
  haveI hnorm : ((F ⊓ X).subgroupOf F).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ F ⊓ X := Subgroup.mem_subgroupOf.1 hn
    rw [Subgroup.mem_inf] at hn'
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨F.mul_mem (F.mul_mem g.2 hn'.1) (F.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.1 (hFN g.2) (n : G)).1 hn'.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((F ⊓ X).subgroupOf F) with hbot | htop
  ·
    have hsub : ∀ x : G, x ∈ F ⊓ X → x = 1 := by
      intro x hx
      have hxmem : (⟨x, (Subgroup.mem_inf.1 hx).1⟩ : F) ∈ (F ⊓ X).subgroupOf F :=
        Subgroup.mem_subgroupOf.2 hx
      rw [hbot, Subgroup.mem_bot] at hxmem
      exact congrArg Subtype.val hxmem
    haveI : Subsingleton ↥(F ⊓ X) :=
      ⟨fun a b => Subtype.ext ((hsub a a.2).trans (hsub b b.2).symm)⟩
    have hFsolv : Group.IsSolvable ↥F := hsolv F hFN inferInstance
    have hcomm : ∀ a b : F, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.2 hFsolv
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (hcomm x y)
  ·
    have hFX : ∀ f : F, (f : G) ∈ X := by
      intro f
      have hf : f ∈ (F ⊓ X).subgroupOf F := by rw [htop]; exact Subgroup.mem_top f
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hf)).2
    have hcentral : ∀ f : F, f * ⟨t, htF⟩ = ⟨t, htF⟩ * f := by
      intro f
      apply Subtype.ext
      have hc := Subgroup.mem_centralizer_singleton_iff.1 (hXC (hFX f))
      simpa using hc
    have hZ : (⟨t, htF⟩ : F) ∈ Subgroup.center F := Subgroup.mem_center_iff.2 hcentral
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center F) with hZb | hZt
    · have h1 : (⟨t, htF⟩ : F) = 1 := by
        rw [hZb] at hZ
        exact Subgroup.mem_bot.1 hZ
      exact ht1 (congrArg Subtype.val h1)
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hx : x ∈ Subgroup.center F := by rw [hZt]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.1 hx y).symm

theorem closing_map_conj (X : Subgroup G) (k : G)
    (hX : ∀ H : Subgroup G, X ≤ H → ¬ H ≤ Subgroup.normalizer (X : Set G) → H = ⊤) :
    ∀ H : Subgroup G, X.map (MulAut.conj k).toMonoidHom ≤ H →
      ¬ H ≤ Subgroup.normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) →
        H = ⊤ := by
  intro H hXH hHN
  have hmem : ∀ w : G, w ∈ X.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * w * k ∈ X := by
    intro w
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hnorm : ∀ n ∈ Subgroup.normalizer (X : Set G),
      k * n * k⁻¹ ∈ Subgroup.normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro w
    simp only [hmem]
    have h1 := Subgroup.mem_normalizer_iff.1 hn (k⁻¹ * w * k)
    have e1 : k⁻¹ * (k * n * k⁻¹ * w * (k * n * k⁻¹)⁻¹) * k = n * (k⁻¹ * w * k) * n⁻¹ := by
      group
    rw [e1]
    exact h1
  have hH' : X ≤ H.comap (MulAut.conj k).toMonoidHom := fun x hx => hXH (Subgroup.mem_map_of_mem _ hx)
  have hnot : ¬ H.comap (MulAut.conj k).toMonoidHom ≤ Subgroup.normalizer (X : Set G) := by
    intro hN
    apply hHN
    intro g hg
    have hn : k⁻¹ * g * k ∈ Subgroup.normalizer (X : Set G) := by
      apply hN
      show k * (k⁻¹ * g * k) * k⁻¹ ∈ H
      have hgeq : k * (k⁻¹ * g * k) * k⁻¹ = g := by group
      rw [hgeq]
      exact hg
    have h2 := hnorm _ hn
    have hgeq : k * (k⁻¹ * g * k) * k⁻¹ = g := by group
    rwa [hgeq] at h2
  have hHtop : H.comap (MulAut.conj k).toMonoidHom = ⊤ := hX _ hH' hnot
  rw [eq_top_iff]
  intro g _
  have hg : (MulAut.conj k).symm g ∈ H.comap (MulAut.conj k).toMonoidHom := by
    rw [hHtop]
    exact Subgroup.mem_top _
  have h3 : (MulAut.conj k) ((MulAut.conj k).symm g) ∈ H := Subgroup.mem_comap.1 hg
  rwa [MulEquiv.apply_symm_apply] at h3

theorem normalizer_le_of_map_conj (X : Subgroup G) (k : G) (F : Subgroup G) (hk : k ∈ F)
    (hF : F ≤ Subgroup.normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G)) :
    F ≤ Subgroup.normalizer (X : Set G) := by
  have hmem : ∀ w : G, w ∈ X.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * w * k ∈ X := by
    intro w
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  intro f hf
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hf' : k * f * k⁻¹ ∈ F := F.mul_mem (F.mul_mem hk hf) (F.inv_mem hk)
  have h1 := Subgroup.mem_normalizer_iff.1 (hF hf') (k * y * k⁻¹)
  simp only [hmem] at h1
  have e1 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  have e2 : k⁻¹ * (k * f * k⁻¹ * (k * y * k⁻¹) * (k * f * k⁻¹)⁻¹) * k = f * y * f⁻¹ := by
    group
  rw [e1, e2] at h1
  exact h1

end Generic

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

theorem e6Frame_le (K : Type) [Field K] [Finite K] (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D ≤ adjointGroup TwClass.e6Six.tag K :=
  sup_le inf_le_left inf_le_left

theorem e6Frame_closing (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    ∀ H : Subgroup (adjointGroup TwClass.e6Six.tag K),
      frameIn (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) ≤ H →
        ¬ H ≤ Subgroup.normalizer
          ((frameIn (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) : Subgroup (adjointGroup TwClass.e6Six.tag K)) :
            Set (adjointGroup TwClass.e6Six.tag K)) →
        H = ⊤ :=
  closing_of_twFrameClosing (e6Frame_le K D) (twClosing_e6Six K h3 D)

theorem e6Frame_normalizerSolvable (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    ∀ P : Subgroup (adjointGroup TwClass.e6Six.tag K),
      P ≤ Subgroup.normalizer
          ((frameIn (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) : Subgroup (adjointGroup TwClass.e6Six.tag K)) :
            Set (adjointGroup TwClass.e6Six.tag K)) →
        Group.IsSolvable ↥(P ⊓ frameIn (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D)) →
          Group.IsSolvable ↥P :=
  normalizerSolvable_of_twFrame (e6Frame_le K D)
    (twNormalizer_e6Six K (show TwClass.e6Six.minQ ≤ Nat.card K from h3) D)

theorem e6Frame_centralizes (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (z : adjointGroup .E6 K)
    (hz : TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D ≤
      Subgroup.centralizer ({((z : ModGL Tag.E6 K))} : Set (ModGL Tag.E6 K))) :
    frameIn (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) ≤
      Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) := by
  intro y hy
  apply Subgroup.mem_centralizer_singleton_iff.2
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hz (Subgroup.mem_subgroupOf.1 hy)))

theorem hReg2_of_NR (hNR : LangPlaneKillsRoot Tag.F4) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ D : LangPlaneData .F4 K E₃, ∀ α, IsRoot .F4 α → ¬ D.Kills α := by
  intro K _ _ hK E₃ hexp hcard hnF
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  have hor : Nonempty (LangPlaneData .F4 K E₃) ∨ NormalizesRNative .F4 K E₃ :=
    langToralOrParabolic_of_langToralPlane
      CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three K hnd E₃ hexp hcard
  rcases hor with hD | hN
  · obtain ⟨D⟩ := hD
    refine ⟨D, fun α hα hk => ?_⟩
    obtain ⟨u, hu1, ⟨n, hn⟩, hcomm⟩ := hNR K E₃ D α hα hk
    apply hnF
    show NormalizesRIn (ringChar K) E₃
    refine ⟨Subgroup.zpowers u, fun h => hu1 (Subgroup.zpowers_eq_bot.mp h), ?_, ?_⟩
    · intro g
      obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨n, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hk', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn,
        one_zpow]
      rfl
    · intro x hx
      have hxu : x * u * x⁻¹ = u := by
        rw [mul_inv_eq_iff_eq_mul]
        exact ((hcomm x hx).eq).symm
      have hconj : ∀ k : ℤ, x * u ^ k * x⁻¹ = u ^ k := by
        intro k
        rw [← conj_zpow, hxu]
      have hconj' : ∀ k : ℤ, x⁻¹ * u ^ k * x = u ^ k := by
        intro k
        calc x⁻¹ * u ^ k * x = x⁻¹ * (x * u ^ k * x⁻¹) * x := by rw [hconj k]
          _ = u ^ k := by group
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        rw [← hk, hconj k]
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        have hh' : h = x⁻¹ * (x * h * x⁻¹) * x := by group
        rw [hh', ← hk, hconj']
  · exact absurd hN hnF

theorem f4_twisted_element (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (h3 : 3 ≤ Nat.card K) (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ)
    (hω3 : orderOf ω = 3) :
    ∃ z : adjointGroup .F4 K, z ≠ 1 ∧
      baseChangeGL (algebraMap K D.L) (z : ModGL Tag.F4 K) =
        D.g * rootDiagUnit TwClass.f4Six.tag
          (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D.g⁻¹ := by
  obtain ⟨z, hzbc, hz1, -, -⟩ := f4TwistedFrame_of K hK h3 D ω hω3
  exact ⟨z, hz1, hzbc⟩

@[expose] def E6TwistedTransport : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → 3 ≤ Nat.card K →
    ∀ (D₁ : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D₁.Lˣ), orderOf ω = 3 →
    ∀ z : adjointGroup TwClass.f4Six.tag K,
      baseChangeGL (algebraMap K D₁.L) (z : ModGL TwClass.f4Six.tag K) =
        D₁.g * rootDiagUnit TwClass.f4Six.tag
          (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D₁.g⁻¹ →
      ∃ (D₆ : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (ω₆ : D₆.Lˣ), orderOf ω₆ = 3 ∧
        baseChangeGL (algebraMap K D₆.L)
            ((embE6F4 K z : adjointGroup .E6 K) : ModGL Tag.E6 K) =
          D₆.g * rootDiagUnit TwClass.e6Six.tag
            (Pi.mulSingle (⟨3, by decide⟩ : Fin TwClass.e6Six.tag.rank) ω₆) * D₆.g⁻¹

@[expose] def E6FrameCentral : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
    ∀ (D₆ : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (ω₆ : D₆.Lˣ), orderOf ω₆ = 3 →
    ∀ z₆ : ModGL TwClass.e6Six.tag K,
      baseChangeGL (algebraMap K D₆.L) z₆ =
        D₆.g * rootDiagUnit TwClass.e6Six.tag
          (Pi.mulSingle (⟨3, by decide⟩ : Fin TwClass.e6Six.tag.rank) ω₆) * D₆.g⁻¹ →
      TwClass.e6Six.X₁ D₆ ⊔ TwClass.e6Six.X₂ D₆ ≤
        Subgroup.centralizer ({z₆} : Set (ModGL TwClass.e6Six.tag K))

theorem frame_two_of_three_le (hNR : LangPlaneKillsRoot Tag.F4) (hT : E6TwistedTransport)
    (hC : E6FrameCentral) (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (h3 : 3 ≤ Nat.card K) (E₃ : Subgroup (adjointGroup .F4 K)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1)
    (hcard : Nat.card E₃ = 3 ^ 2) (hnF : ¬ NormalizesRNative .F4 K E₃) :
    ∃ e ∈ E₃, e ≠ 1 ∧ ∃ X : Subgroup (adjointGroup .E6 K),
      X ≤ Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) ∧
      (∀ H : Subgroup (adjointGroup .E6 K), X ≤ H →
        ¬ H ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K)) → H = ⊤) ∧
      ¬ (fixE6 K ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K))) := by
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨P, hreg⟩ := hReg2_of_NR hNR K hK E₃ hexp hcard hnF
  obtain ⟨x, hx⟩ : ∃ x : E₃, x ≠ 1 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    have hsub : Subsingleton E₃ := ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h1 : Nat.card E₃ = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    rw [hcard] at h1
    norm_num at h1
  have he : (x : adjointGroup .F4 K) ∈ E₃ := x.2
  have he1 : (x : adjointGroup .F4 K) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag K TwClass.f4Six.w (TwClass.w_theta TwClass.f4Six)
  obtain ⟨ω, hω⟩ := exists_cube_root_langLevi K hnd D₁
  obtain ⟨z, hz1, hzbc⟩ := f4_twisted_element K hK h3 D₁ ω hω
  obtain ⟨g, hg⟩ := f4PureTwisted_holds K hK h3 D₁ ω hω z hzbc E₃ hexp hcard P hreg _ he he1
  obtain ⟨D₆, ω₆, hω₆, hbc⟩ := hT K hK h3 D₁ ω hω z hzbc
  have hC' := hC K h3 D₆ ω₆ hω₆ ((embE6F4 K z : adjointGroup .E6 K) : ModGL Tag.E6 K) hbc
  have hcent := e6Frame_centralizes K D₆ (embE6F4 K z) hC'
  haveI hsimpleF4 : IsSimpleGroup (adjointGroup .F4 K) :=
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type
      (τ := Tag.F4) (K := K) (Or.inr (Or.inr (Or.inr rfl)))
  haveI hsimpleF : IsSimpleGroup ↥(fixE6 K) := MulEquiv.isSimpleGroup (isoE6F4 K).symm
  have hnc : ∃ a b : ↥(fixE6 K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (opposite_simple_root_noncommutativity Tag.F4 K).2.2.1
    refine ⟨isoE6F4 K a, isoE6F4 K b, fun h => hab ?_⟩
    apply (isoE6F4 K).injective
    simpa [map_mul] using h
  have hιzF : embE6F4 K z ∈ fixE6 K := by
    rw [← range_embE6F4 K]
    exact MonoidHom.mem_range.2 ⟨z, rfl⟩
  have hιz1 : embE6F4 K z ≠ 1 := fun h => hz1 (embE6F4_injective K (h.trans (map_one _).symm))
  have hnotX₀ : ¬ fixE6 K ≤ Subgroup.normalizer
      ((frameIn (TwClass.e6Six.X₁ D₆ ⊔ TwClass.e6Six.X₂ D₆) :
        Subgroup (adjointGroup TwClass.e6Six.tag K)) : Set (adjointGroup TwClass.e6Six.tag K)) :=
    not_le_normalizer_of_simple_centralizer (F := fixE6 K) hnc _ hιzF hιz1 hcent
      (e6Frame_normalizerSolvable K h3 D₆)
  have hxz : (x : adjointGroup .F4 K) = g⁻¹ * (z : adjointGroup .F4 K) * g := by
    rw [← hg]
    group
  have hkF : embE6F4 K g⁻¹ ∈ fixE6 K := by
    rw [← range_embE6F4 K]
    exact MonoidHom.mem_range.2 ⟨g⁻¹, rfl⟩
  have hιe : embE6F4 K (x : adjointGroup .F4 K) =
      embE6F4 K g⁻¹ * embE6F4 K z * (embE6F4 K g⁻¹)⁻¹ := by
    rw [hxz]
    simp only [map_mul, map_inv, inv_inv]
  refine ⟨(x : adjointGroup .F4 K), he, he1,
    (frameIn (TwClass.e6Six.X₁ D₆ ⊔ TwClass.e6Six.X₂ D₆)).map (MulAut.conj (embE6F4 K g⁻¹)).toMonoidHom,
    ?_, ?_, ?_⟩
  ·
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, hιe]
    have hw : (embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹ ∈
        frameIn (TwClass.e6Six.X₁ D₆ ⊔ TwClass.e6Six.X₂ D₆) := by
      have h0 := (Subgroup.mem_map_equiv (f := MulAut.conj (embE6F4 K g⁻¹))).1 hy
      rwa [MulAut.conj_symm_apply] at h0
    have hcw : (embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹ * embE6F4 K z =
        embE6F4 K z * ((embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hcent hw)
    calc y * (embE6F4 K g⁻¹ * embE6F4 K z * (embE6F4 K g⁻¹)⁻¹)
        = embE6F4 K g⁻¹ * ((embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹ * embE6F4 K z) *
            (embE6F4 K g⁻¹)⁻¹ := by group
      _ = embE6F4 K g⁻¹ * (embE6F4 K z * ((embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹)) *
            (embE6F4 K g⁻¹)⁻¹ := by rw [hcw]
      _ = embE6F4 K g⁻¹ * embE6F4 K z * (embE6F4 K g⁻¹)⁻¹ * y := by group
  ·
    exact closing_map_conj _ _ (e6Frame_closing K h3 D₆)
  ·
    intro hF
    exact hnotX₀ (normalizer_le_of_map_conj _ _ (fixE6 K) hkF hF)

@[expose] def E6FrameAtTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
      ¬ NormalizesRNative .F4 K E₃ →
      ∃ e ∈ E₃, e ≠ 1 ∧ ∃ X : Subgroup (adjointGroup .E6 K),
        X ≤ Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) ∧
        (∀ H : Subgroup (adjointGroup .E6 K), X ≤ H →
          ¬ H ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K)) → H = ⊤) ∧
        ¬ (fixE6 K ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K)))

theorem twistedFrameTwo_of (hNR : LangPlaneKillsRoot Tag.F4) (hT : E6TwistedTransport)
    (hC : E6FrameCentral) (hTwo : E6FrameAtTwo) :
    TwistedFrameTwo := by
  unfold TwistedFrameTwo
  intro K _ _ hK E₃ hexp hcard hnF
  by_cases h2 : Nat.card K = 2
  · exact hTwo K h2 E₃ hexp hcard hnF
  · have h1 : 1 < Nat.card K := Finite.one_lt_card
    exact frame_two_of_three_le hNR hT hC K hK (by omega) E₃ hexp hcard hnF

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
