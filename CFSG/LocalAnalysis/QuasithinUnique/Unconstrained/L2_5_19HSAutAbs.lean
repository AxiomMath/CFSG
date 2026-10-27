module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut

open CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem perfectResidualOf_eq_ambientDerived {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    ∃ i, perfectResidualOf H = ambientDerived H i := by
  obtain ⟨i, hi⟩ := finite_perfectResidual_eq_derivedSeries (G := ↥H)
  refine ⟨i, ?_⟩
  unfold perfectResidualOf
  rw [hi, map_derivedSeries]

theorem le_ambientDerived {G : Type*} [Group G] {H F : Subgroup G} (hFH : F ≤ H)
    (hFc : ⁅F, F⁆ = F) (k : ℕ) : F ≤ ambientDerived H k := by
  induction k with
  | zero => exact hFH
  | succ k ih =>
    show F ≤ ⁅ambientDerived H k, ambientDerived H k⁆
    calc F = ⁅F, F⁆ := hFc.symm
      _ ≤ _ := Subgroup.commutator_mono ih ih

theorem le_perfectResidualOf {G : Type*} [Group G] [Finite G] {H F : Subgroup G} (hFH : F ≤ H)
    (hF : Group.IsPerfect F) : F ≤ perfectResidualOf H := by
  obtain ⟨i, hi⟩ := perfectResidualOf_eq_ambientDerived H
  rw [hi]
  exact le_ambientDerived hFH (Subgroup.isPerfect_iff.mp hF) i

theorem perfectResidualOf_le' {G : Type*} [Group G] (H : Subgroup G) : perfectResidualOf H ≤ H :=
  Subgroup.map_subtype_le _

theorem commutator_perfectResidualOf {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    ⁅perfectResidualOf H, perfectResidualOf H⁆ = perfectResidualOf H :=
  Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect H)

theorem perfectResidualOf_eq_of_commutator_le {G : Type*} [Group G] [Finite G] {H N : Subgroup G}
    (hNH : N ≤ H) (hc : ⁅H, H⁆ ≤ N) : perfectResidualOf N = perfectResidualOf H := by
  apply le_antisymm
  · exact le_perfectResidualOf ((perfectResidualOf_le' N).trans hNH)
      (finite_perfectResidualOf_isPerfect N)
  · have hle : perfectResidualOf H ≤ N := by
      calc perfectResidualOf H = ⁅perfectResidualOf H, perfectResidualOf H⁆ :=
            (commutator_perfectResidualOf H).symm
        _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono (perfectResidualOf_le' H) (perfectResidualOf_le' H)
        _ ≤ N := hc
    exact le_perfectResidualOf hle (finite_perfectResidualOf_isPerfect H)

theorem perfectResidualOf_map_equiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (φ : G ≃* G') (H : Subgroup G) :
    perfectResidualOf (H.map φ.toMonoidHom) = (perfectResidualOf H).map φ.toMonoidHom := by
  apply le_antisymm
  · have h1 : (perfectResidualOf (H.map φ.toMonoidHom)).map φ.symm.toMonoidHom ≤
        perfectResidualOf H := by
      refine le_perfectResidualOf ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, rfl⟩ := perfectResidualOf_le' _ hx
        simpa using hy
      · have := finite_perfectResidualOf_isPerfect (H.map φ.toMonoidHom)
        exact Group.IsPerfect.map (φ.symm.toMonoidHom)
          (H := perfectResidualOf (H.map φ.toMonoidHom))
    intro x hx
    have := h1 ⟨x, hx, rfl⟩
    exact ⟨_, this, by simp⟩
  · refine le_perfectResidualOf ?_ ?_
    · exact Subgroup.map_mono (perfectResidualOf_le' H)
    · have := finite_perfectResidualOf_isPerfect H
      exact Group.IsPerfect.map (φ.toMonoidHom) (H := perfectResidualOf H)

theorem perfectResidualOf_subgroupOf {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) :
    (perfectResidualOf (H.subgroupOf K)).map K.subtype = perfectResidualOf H := by
  apply le_antisymm
  · refine le_perfectResidualOf ?_ ?_
    · have h1 : (perfectResidualOf (H.subgroupOf K)).map K.subtype ≤
          (H.subgroupOf K).map K.subtype :=
        Subgroup.map_mono (perfectResidualOf_le' _)
      rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hHK] at h1
    · have := finite_perfectResidualOf_isPerfect (H.subgroupOf K)
      exact Group.IsPerfect.map K.subtype (H := perfectResidualOf (H.subgroupOf K))
  · set F := perfectResidualOf H with hF
    have hFK : F ≤ K := (perfectResidualOf_le' H).trans hHK
    have hFH : F.subgroupOf K ≤ H.subgroupOf K := by
      intro x hx
      exact (perfectResidualOf_le' H) hx
    have hperf : Group.IsPerfect (F.subgroupOf K) := by
      rw [Subgroup.isPerfect_iff]
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hFK,
        commutator_perfectResidualOf]
    have h2 := le_perfectResidualOf hFH hperf
    intro x hx
    have hxK : x ∈ K := hFK hx
    exact ⟨⟨x, hxK⟩, h2 (show (⟨x, hxK⟩ : ↥K) ∈ F.subgroupOf K from hx), rfl⟩

theorem exists_perfect_lift {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (F : Subgroup B) (hF : Group.IsPerfect F) (hFr : F ≤ f.range) :
    ∃ F' : Subgroup A, Group.IsPerfect F' ∧ F' ≤ F.comap f ∧ F'.map f = F := by
  classical
  set F₀ : Subgroup A := F.comap f with hF₀
  let g : ↥F₀ →* ↥F := (f.comp F₀.subtype).codRestrict F (fun x => x.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, ha⟩ := hFr y.2
    refine ⟨⟨a, show f a ∈ F by rw [ha]; exact y.2⟩, ?_⟩
    apply Subtype.ext
    exact ha
  have hmap := finite_perfectResidual_surjects_to_perfect_image g hg
  refine ⟨perfectResidualOf F₀, finite_perfectResidualOf_isPerfect F₀,
    perfectResidualOf_le' F₀, ?_⟩
  have hcomp : f.comp F₀.subtype = F.subtype.comp g := by
    ext x
    rfl
  calc (perfectResidualOf F₀).map f
      = (Helpers.perfectResidual ↥F₀).map (f.comp F₀.subtype) := by
        unfold perfectResidualOf
        rw [Subgroup.map_map]
    _ = ((Helpers.perfectResidual ↥F₀).map g).map F.subtype := by
        rw [hcomp, ← Subgroup.map_map]
    _ = F := by
        rw [hmap, Subgroup.map_top, Subgroup.range_subtype]

theorem isQuasisimple_of_central_cover {N S : Type*} [Group N] [Group S] (f : N →* S)
    (hf : Function.Surjective f) (hNperf : Group.IsPerfect N) (hS : IsSimpleGroup S)
    (hker : f.ker ≤ Subgroup.center N) : CFSG.IsQuasisimple N := by
  have : IsSimpleGroup S := hS
  have : Group.IsPerfect N := hNperf
  have hSperf : Group.IsPerfect S := Group.IsPerfect.ofSurjective hf
  have hScenter : Subgroup.center S = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hbot | htop
    · exact hbot
    · exfalso
      exact Group.IsPerfect.not_isMulCommutative S (Subgroup.center_eq_top_iff.mp htop)
  have hcenter_ker : Subgroup.center N ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hfz : f z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hf y
      simpa using congrArg f (Subgroup.mem_center_iff.mp hz x)
    rw [hScenter] at hfz
    exact Subgroup.mem_bot.mp hfz
  have hker_eq : f.ker = Subgroup.center N := le_antisymm hker hcenter_ker
  let eRangeTop : f.range ≃* (⊤ : Subgroup S) :=
    MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hf)
  let eQuot : N ⧸ f.ker ≃* S :=
    ((QuotientGroup.quotientKerEquivRange f).trans eRangeTop).trans Subgroup.topEquiv
  let eCenterKer : N ⧸ Subgroup.center N ≃* N ⧸ f.ker :=
    QuotientGroup.quotientMulEquivOfEq (M := Subgroup.center N) (N := f.ker) hker_eq.symm
  have hquotSimple : IsSimpleGroup (N ⧸ Subgroup.center N) :=
    (MulEquiv.isSimpleGroup_congr (eCenterKer.trans eQuot)).mpr hS
  refine ⟨hNperf, hquotSimple, ?_⟩
  by_contra hcon
  have hcomm : IsMulCommutative (N ⧸ Subgroup.center N) :=
    ⟨⟨fun a b => by by_contra hab; exact hcon ⟨a, b, hab⟩⟩⟩
  have : Nontrivial (N ⧸ Subgroup.center N) := hquotSimple.toNontrivial
  have : Group.IsPerfect (N ⧸ Subgroup.center N) := inferInstance
  exact Group.IsPerfect.not_isMulCommutative _ hcomm

theorem commutatorElement_central_mul {Γ : Type*} [Group Γ] {z : Γ} (hz : ∀ x, z * x = x * z)
    (a b : Γ) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  calc ⁅z * a, b⁆ = (z * (a * b * a⁻¹) * z⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = (a * b * a⁻¹) * b⁻¹ := by rw [hz (a * b * a⁻¹), mul_inv_cancel_right]
    _ = ⁅a, b⁆ := rfl

theorem commutatorElement_mul_central {Γ : Type*} [Group Γ] {z : Γ} (hz : ∀ x, z * x = x * z)
    (a b : Γ) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  calc ⁅a, z * b⁆ = (a * z) * (b * a⁻¹ * b⁻¹) * z⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = (z * a) * (b * a⁻¹ * b⁻¹) * z⁻¹ := by rw [← hz a]
    _ = (z * (a * b * a⁻¹ * b⁻¹)) * z⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [hz (a * b * a⁻¹ * b⁻¹)]
    _ = ⁅a, b⁆ := by rw [mul_inv_cancel_right]; rfl

section Residual

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {M : Type*} [Group M] [Finite M]
  (π : ↥X →* M) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center ↥X)
  (W : Subgroup G) (hWn : W ≤ Subgroup.normalizer (X : Set G))

theorem residual_centralizer_image (Fm : Subgroup M)
    (hFm : ∀ m : M, m ∈ Fm ↔ ∀ w : ↥W, Tab.actHom π hπ hker W hWn w m = m) :
    ((perfectResidualOf (X ⊓ Subgroup.centralizer (W : Set G))).subgroupOf X).map π =
      perfectResidualOf Fm := by
  classical
  set C : Subgroup G := X ⊓ Subgroup.centralizer (W : Set G) with hC
  set A : Subgroup G := perfectResidualOf C with hA
  let cj : ↥W → MulAut ↥X := fun w => X.normalizerMonoidHom (Subgroup.inclusion hWn w)
  have hcjc : ∀ (w : ↥W) (x : ↥X), (((cj w) x : ↥X) : G) = (w : G) * (x : G) * (w : G)⁻¹ :=
    fun w x => Tab.coe_actHom_conj W hWn w x
  have hact : ∀ (w : ↥W) (x : ↥X), Tab.actHom π hπ hker W hWn w (π x) = π ((cj w) x) :=
    fun w x => Tab.actHom_apply π hπ hker W hWn w x
  set D : Subgroup ↥X := Fm.comap π with hD
  set D' : Subgroup G := D.map X.subtype with hD'
  have hDmem : ∀ x : ↥X, x ∈ D ↔ ∀ w : ↥W, π ((cj w) x) = π x := by
    intro x
    rw [hD, Subgroup.mem_comap, hFm]
    refine forall_congr' fun w => ?_
    rw [hact]
  have hCD : C ≤ D' := by
    rintro x ⟨hxX, hxC⟩
    refine ⟨⟨x, hxX⟩, (hDmem _).2 ?_, rfl⟩
    intro w
    have hcomm : (w : G) * x = x * (w : G) := Subgroup.mem_centralizer_iff.mp hxC w w.2
    have : (cj w) ⟨x, hxX⟩ = ⟨x, hxX⟩ := by
      apply Subtype.ext
      rw [hcjc]
      calc (w : G) * x * (w : G)⁻¹ = (x * (w : G)) * (w : G)⁻¹ := by rw [hcomm]
        _ = x := by group
    rw [this]
  have hcommC : ⁅D', D'⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩
    have hcoe : ((⁅a', b'⁆ : ↥X) : G) = ⁅(a' : G), (b' : G)⁆ := by
      simp [commutatorElement_def]
    show ⁅(a' : G), (b' : G)⁆ ∈ C
    rw [← hcoe]
    refine ⟨(⁅a', b'⁆ : ↥X).2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    set w' : ↥W := ⟨w, hw⟩ with hw'
    have haD := (hDmem a').1 ha' w'
    have hbD := (hDmem b').1 hb' w'
    have hza : (cj w') a' * a'⁻¹ ∈ Subgroup.center ↥X := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, haD, mul_inv_cancel]
    have hzb : (cj w') b' * b'⁻¹ ∈ Subgroup.center ↥X := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hbD, mul_inv_cancel]
    obtain ⟨za, hzac, hzaeq⟩ : ∃ za : ↥X, (∀ x, za * x = x * za) ∧ (cj w') a' = za * a' :=
      ⟨(cj w') a' * a'⁻¹, fun x => (Subgroup.mem_center_iff.mp hza x).symm, by group⟩
    obtain ⟨zb, hzbc, hzbeq⟩ : ∃ zb : ↥X, (∀ x, zb * x = x * zb) ∧ (cj w') b' = zb * b' :=
      ⟨(cj w') b' * b'⁻¹, fun x => (Subgroup.mem_center_iff.mp hzb x).symm, by group⟩
    have hfix : (cj w') ⁅a', b'⁆ = ⁅a', b'⁆ := by
      rw [map_commutatorElement, hzaeq, hzbeq, commutatorElement_central_mul hzac,
        commutatorElement_mul_central hzbc]
    have h1 := hcjc w' ⁅a', b'⁆
    rw [hfix, hcoe] at h1
    calc (w : G) * ⁅(a' : G), (b' : G)⁆
        = ((w : G) * ⁅(a' : G), (b' : G)⁆ * (w : G)⁻¹) * (w : G) := by
          group
      _ = ⁅(a' : G), (b' : G)⁆ * (w : G) := by rw [← h1]
  have hAeq : A = perfectResidualOf D' := perfectResidualOf_eq_of_commutator_le hCD hcommC
  have hAX : A ≤ X := (perfectResidualOf_le' C).trans inf_le_left
  have hAD' : A ≤ D' := by rw [hAeq]; exact perfectResidualOf_le' D'
  have hAperf : Group.IsPerfect ↥A := finite_perfectResidualOf_isPerfect C
  have hAc : ⁅A, A⁆ = A := commutator_perfectResidualOf C
  set AX : Subgroup ↥X := A.subgroupOf X with hAX'
  have hAXmap : AX.map X.subtype = A := by
    rw [hAX', Subgroup.subgroupOf_map_subtype, inf_of_le_left hAX]
  have hAXD : AX ≤ D := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hAD' (show (x : G) ∈ A from hx)
    have : d = x := Subtype.ext hdx
    rw [← this]
    exact hd
  have hAXperf : Group.IsPerfect AX := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hAXmap, hAc]
  set F : Subgroup M := perfectResidualOf Fm with hF
  have hFperf : Group.IsPerfect ↥F := finite_perfectResidualOf_isPerfect Fm
  have hSF : AX.map π ≤ F := by
    refine le_perfectResidualOf ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hAXD hx
    · have := hAXperf
      exact Group.IsPerfect.map π (H := AX)
  have hFS : F ≤ AX.map π := by
    obtain ⟨F', hF'perf, hF'le, hF'map⟩ := exists_perfect_lift π F hFperf (by
      rw [MonoidHom.range_eq_top.mpr hπ]; exact le_top)
    have hF'D : F' ≤ D := fun x hx => (perfectResidualOf_le' Fm) (hF'le hx)
    have hF''perf : Group.IsPerfect (F'.map X.subtype) := by
      have := hF'perf
      exact Group.IsPerfect.map X.subtype (H := F')
    have hF''le : F'.map X.subtype ≤ A := by
      rw [hAeq]
      exact le_perfectResidualOf (Subgroup.map_mono hF'D) hF''perf
    intro m hm
    rw [← hF'map] at hm
    obtain ⟨f', hf', rfl⟩ := hm
    exact ⟨f', hF''le ⟨f', hf', rfl⟩, rfl⟩
  exact le_antisymm hSF hFS

theorem residual_centralizer (Fm : Subgroup M)
    (hFm : ∀ m : M, m ∈ Fm ↔ ∀ w : ↥W, Tab.actHom π hπ hker W hWn w m = m)
    (hS : IsSimpleGroup ↥(perfectResidualOf Fm)) :
    CFSG.IsQuasisimple ↥(perfectResidualOf (X ⊓ Subgroup.centralizer (W : Set G))) ∧
      Nat.card ↥(perfectResidualOf Fm) ≤
        Nat.card ↥(perfectResidualOf (X ⊓ Subgroup.centralizer (W : Set G))) := by
  classical
  have himg := residual_centralizer_image π hπ hker W hWn Fm hFm
  set C : Subgroup G := X ⊓ Subgroup.centralizer (W : Set G) with hC
  set A : Subgroup G := perfectResidualOf C with hA
  have hAX : A ≤ X := (perfectResidualOf_le' C).trans inf_le_left
  have hAperf : Group.IsPerfect ↥A := finite_perfectResidualOf_isPerfect C
  set AX : Subgroup ↥X := A.subgroupOf X with hAX'
  set F : Subgroup M := perfectResidualOf Fm with hF
  have hSF : AX.map π ≤ F := himg.le
  have hFS : F ≤ AX.map π := himg.ge
  let f : ↥A →* ↥F := (π.comp (Subgroup.inclusion hAX)).codRestrict F (fun a => by
    apply hSF
    exact ⟨Subgroup.inclusion hAX a, show (Subgroup.inclusion hAX a) ∈ AX from a.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro m
    obtain ⟨x, hx, hxm⟩ := hFS m.2
    refine ⟨⟨(x : G), show (x : G) ∈ A from hx⟩, ?_⟩
    apply Subtype.ext
    exact hxm
  have hfker : f.ker ≤ Subgroup.center ↥A := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : π (Subgroup.inclusion hAX a) = 1 := congrArg Subtype.val ha
    have h2 : Subgroup.inclusion hAX a ∈ Subgroup.center ↥X := by
      rw [← hker]; exact h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro a'
    apply Subtype.ext
    exact congrArg (Subtype.val : ↥X → G) (h2 (Subgroup.inclusion hAX a'))
  exact ⟨isQuasisimple_of_central_cover f hf hAperf hS hfker, Nat.card_le_card_of_surjective f hf⟩

end Residual

end CFSG.QuasithinUnique.Id2519.HSAut
