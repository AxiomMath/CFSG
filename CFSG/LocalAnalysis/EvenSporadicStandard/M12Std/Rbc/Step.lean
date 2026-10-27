module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Layer
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.OddStandardExact
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Composite
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.InnCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Quasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Thm21Lemma15
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.Walter.JRFacts
public import Certificates.Certificate3120

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

variable {G : Type} [Group G]

section Fold

variable {L K : Subgroup G} {s : G}

theorem foldHom_ker_le_center
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) :
    (Zassenhaus.foldHom s L hc).ker ≤ center ↥L := by
  intro a ha
  rw [MonoidHom.mem_ker, Zassenhaus.foldHom_apply] at ha
  have hinv : s * (a : G) * s⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right ha
  have hmem : (a : G)⁻¹ ∈ L.map (MulAut.conj s).toMonoidHom :=
    ⟨a, a.2, by simp [MulAut.conj_apply, hinv]⟩
  rw [mem_center_iff]
  intro x
  apply Subtype.ext
  have h1 := hc x x.2 _ hmem
  simp only [Subgroup.coe_mul]
  calc (x : G) * a = (a : G) * ((a : G)⁻¹ * x) * a := by group
    _ = (a : G) * (x * (a : G)⁻¹) * a := by rw [h1]
    _ = a * x := by group

theorem exists_eq_mul_foldHom_of_sq (hs : ∀ a ∈ L, s * s * a = a * (s * s))
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) {k : G}
    (hks : s * k = k * s) (hk : k ∈ L ⊔ L.map (MulAut.conj s).toMonoidHom) :
    ∃ ζ ∈ L, ζ ∈ L.map (MulAut.conj s).toMonoidHom ∧
      ∃ b : ↥L, k = ζ * Zassenhaus.foldHom s L hc b := by
  obtain ⟨a, ha, b', hb', rfl⟩ := Zassenhaus.exists_mul_of_mem_sup_of_commute hc hk
  obtain ⟨b, hb, rfl⟩ := hb'
  have hbs : (MulAut.conj s).toMonoidHom b = s * b * s⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hbs] at hks ⊢
  set a₁ := s * a * s⁻¹ with ha₁
  set b' := s * b * s⁻¹ with hb'
  have hb'L : b' ∈ L.map (MulAut.conj s).toMonoidHom := ⟨b, hb, hbs⟩
  have ha₁L : a₁ ∈ L.map (MulAut.conj s).toMonoidHom :=
    ⟨a, ha, by simp [MulAut.conj_apply, ha₁]⟩
  have hsb : s * b' * s⁻¹ = b := by
    rw [hb']
    rw [show s * (s * b * s⁻¹) * s⁻¹ = (s * s) * b * (s * s)⁻¹ by group]
    rw [hs b hb]
    group
  have h1 : a₁ * b = a * b' := by
    calc a₁ * b = a₁ * (s * b' * s⁻¹) := by rw [hsb]
      _ = s * (a * b') * s⁻¹ := by simp only [ha₁, hb']; group
      _ = a * b' := by rw [hks]; group
  have hba : b * a₁ = a₁ * b := hc b hb a₁ ha₁L
  have hζ' : b⁻¹ * a ∈ L.map (MulAut.conj s).toMonoidHom := by
    have : b⁻¹ * a = a₁ * b'⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a₁ * b) * b'⁻¹ := by rw [h1]; group
        _ = a₁ * b'⁻¹ := by rw [← hba]; group
    rw [this]
    exact Subgroup.mul_mem _ ha₁L (Subgroup.inv_mem _ hb'L)
  have hζ : b⁻¹ * a ∈ L := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha
  refine ⟨b⁻¹ * a, hζ, hζ', ⟨b, hb⟩, ?_⟩
  have hbζ : b * (b⁻¹ * a) = (b⁻¹ * a) * b := hc b hb _ hζ'
  rw [Zassenhaus.foldHom_apply]
  calc a * b' = b * (b⁻¹ * a) * b' := by group
    _ = (b⁻¹ * a) * b * b' := by rw [hbζ]
    _ = _ := by simp only [hb']; group

theorem le_range_foldHom_of_sq (hs : ∀ a ∈ L, s * s * a = a * (s * s))
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a)
    (hKs : K ≤ centralizer ({s} : Set G)) (hKp : Group.IsPerfect ↥K)
    (hKL : K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom) :
    K ≤ (Zassenhaus.foldHom s L hc).range := by
  have hper : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hKp
  calc K = ⁅K, K⁆ := hper.symm
    _ ≤ _ := by
      rw [Subgroup.commutator_le]
      intro k₁ hk₁ k₂ hk₂
      obtain ⟨ζ₁, hζ₁, hζ₁', b₁, rfl⟩ := exists_eq_mul_foldHom_of_sq hs hc
        (mem_centralizer_singleton_iff.1 (hKs hk₁)).symm (hKL hk₁)
      obtain ⟨ζ₂, hζ₂, hζ₂', b₂, rfl⟩ := exists_eq_mul_foldHom_of_sq hs hc
        (mem_centralizer_singleton_iff.1 (hKs hk₂)).symm (hKL hk₂)
      rw [Zassenhaus.commutator_mul_mul_of_commute (hc ζ₁ hζ₁ ζ₂ hζ₂')
        (Zassenhaus.commute_foldHom hc hζ₁ hζ₁' b₁) (Zassenhaus.commute_foldHom hc hζ₁ hζ₁' b₂)
        (Zassenhaus.commute_foldHom hc hζ₂ hζ₂' b₁) (Zassenhaus.commute_foldHom hc hζ₂ hζ₂' b₂),
        ← map_commutatorElement]
      exact ⟨_, rfl⟩

theorem range_foldHom_le_centralizer_of_sq (hs : ∀ a ∈ L, s * s * a = a * (s * s))
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) :
    (Zassenhaus.foldHom s L hc).range ≤ centralizer ({s} : Set G) := by
  rintro _ ⟨a, rfl⟩
  rw [mem_centralizer_singleton_iff, Zassenhaus.foldHom_apply]
  have h1 : (a : G) * (s * a * s⁻¹) = (s * a * s⁻¹) * a :=
    hc a a.2 (s * a * s⁻¹) ⟨a, a.2, by simp [MulAut.conj_apply]⟩
  have h2 : s * (s * a * s⁻¹) = (a : G) * s := by
    calc s * (s * a * s⁻¹) = (s * s * a) * s⁻¹ := by group
      _ = (a * (s * s)) * s⁻¹ := by rw [hs a a.2]
      _ = a * s := by group
  have h3 : s * ((a : G) * (s * a * s⁻¹)) = ((a : G) * (s * a * s⁻¹)) * s := by
    calc s * ((a : G) * (s * a * s⁻¹))
        = (s * a) * (s * a * s⁻¹) := by group
      _ = ((s * a * s⁻¹) * s) * (s * a * s⁻¹) := by group
      _ = (s * a * s⁻¹) * (s * (s * a * s⁻¹)) := by group
      _ = (s * a * s⁻¹) * ((a : G) * s) := by rw [h2]
      _ = ((s * a * s⁻¹) * (a : G)) * s := by group
      _ = ((a : G) * (s * a * s⁻¹)) * s := by rw [← h1]
  exact h3.symm

theorem range_foldHom_le_sup
    (hc : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj s).toMonoidHom, a * b = b * a) :
    (Zassenhaus.foldHom s L hc).range ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom := by
  rintro _ ⟨a, rfl⟩
  rw [Zassenhaus.foldHom_apply]
  exact Subgroup.mul_mem_sup a.2 ⟨a, a.2, by simp [MulAut.conj_apply]⟩

end Fold

namespace Step

theorem eq_of_le_of_isSubnormal_of_isQuasisimple {K R : Subgroup G} (hKR : K ≤ R)
    (hK : CFSG.IsQuasisimple ↥K) (hR : CFSG.IsQuasisimple ↥R)
    (hsub : (K.subgroupOf R).IsSubnormal) : K = R := by
  have htop : K.subgroupOf R = ⊤ := by
    refine Zassenhaus.eq_top_of_isSubnormal_of_perfect hR hsub ?_ ?_
    · have := hK.1
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hKR).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKR).symm.surjective
    · intro hbot
      obtain ⟨-, -, a, b, hab⟩ := hK
      have hK1 : Subsingleton ↥K := by
        refine ⟨fun x y => ?_⟩
        have hx : (⟨x, hKR x.2⟩ : ↥R) ∈ K.subgroupOf R := x.2
        have hy : (⟨y, hKR y.2⟩ : ↥R) ∈ K.subgroupOf R := y.2
        rw [hbot, mem_bot] at hx hy
        apply Subtype.ext
        have hx' := congrArg Subtype.val hx
        have hy' := congrArg Subtype.val hy
        simp only [OneMemClass.coe_one] at hx' hy'
        rw [hx', hy']
      have h1 : ∀ q : ↥K ⧸ center ↥K, q = 1 := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H x => rw [Subsingleton.elim x 1]; rfl
      exact hab (by rw [h1 a, h1 b])
  refine le_antisymm hKR fun x hx => ?_
  have : (⟨x, hx⟩ : ↥R) ∈ K.subgroupOf R := htop ▸ mem_top _
  exact this

theorem map_conj_eq_of_commute {M : Subgroup G} {g : G} (h : ∀ m ∈ M, g * m = m * g) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [h m hm, mul_assoc, mul_inv_cancel, mul_one]
    exact hm
  · intro hx
    exact ⟨x, hx, by rw [h x hx, mul_assoc, mul_inv_cancel, mul_one]⟩

end Step

theorem conjClosure_zpowers_eq_of_sq (M : Subgroup G) {u : G}
    (h : ∀ m ∈ M, u ^ 2 * m = m * u ^ 2) :
    conjClosure M (zpowers u) = M ⊔ M.map (MulAut.conj u).toMonoidHom := by
  have hsq : (M.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u).toMonoidHom = M := by
    rw [Induction.map_conj_map_conj, ← pow_two u]
    exact Step.map_conj_eq_of_commute h
  apply le_antisymm
  · refine Junction.conjClosure_le_of_le_normalizer le_sup_left ?_
    rw [Subgroup.zpowers_le, Solomon78.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, hsq]
    exact sup_comm _ _
  · exact sup_le (Junction.le_conjClosure M _) (Junction.map_conj_le_conjClosure (mem_zpowers u))

namespace Step

theorem centralizer_sup_zpowers (T : Subgroup G) (u : G) :
    centralizer ((T ⊔ zpowers u : Subgroup G) : Set G) =
      centralizer (T : Set G) ⊓ centralizer ({u} : Set G) := by
  ext x
  rw [Junction.mem_centralizer_sup, Subgroup.mem_inf]
  have h : centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [h]

end Step

section Alternatives

variable [Finite G]

theorem conjClosure_layerIn_eq_of_le {K M X : Subgroup G} (hM : IsCompIn M X) (hKM : K ≤ M)
    (hK : CFSG.IsQuasisimple ↥K) : conjClosure K (layerIn X) = M := by
  refine le_antisymm ?_ ?_
  ·
    exact Junction.conjClosure_le_of_le_normalizer hKM (layerIn_le_normalizer hM)
  ·
    have hN0M : conjClosure K M ≤ M :=
      Junction.conjClosure_le_of_le_normalizer hKM Subgroup.le_normalizer
    have hMN0 : M ≤ normalizer (conjClosure K M : Set G) :=
      Junction.le_normalizer_conjClosure K M
    have hnormal : ((conjClosure K M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN0M).2 hMN0
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hM.isQuasisimple hnormal with
      htop | hcent
    · exact (Subgroup.subgroupOf_eq_top.1 htop).trans
        (Junction.conjClosure_mono le_rfl (Junction.le_layerIn_of_isCompIn hM))
    · exfalso
      refine not_forall_commute_of_isQuasisimple hK fun a ha b hb => ?_
      have h1 : (⟨a, hKM ha⟩ : ↥M) ∈ (conjClosure K M).subgroupOf M :=
        Junction.le_conjClosure K M ha
      have h2 := Subgroup.mem_center_iff.1 (hcent h1) (⟨b, hKM hb⟩ : ↥M)
      exact congrArg Subtype.val h2.symm

theorem diagonal_of_le_sup {T K M : Subgroup G} {u : G}
    (hu : u ∈ normalizer (T : Set G)) (hu2 : u ^ 2 ∈ T)
    (hKc : IsCompIn K (centralizer ((T ⊔ zpowers u : Subgroup G) : Set G)))
    (hM : IsCompIn M (centralizer (T : Set G)))
    (hle : K ≤ M ⊔ M.map (MulAut.conj u).toMonoidHom)
    (hne : M ≠ M.map (MulAut.conj u).toMonoidHom) :
    Sol78Link5a M K u ∧
      M ⊔ M.map (MulAut.conj u).toMonoidHom =
        conjClosure K (layerIn (centralizer (T : Set G))) := by
  have hMu : IsCompIn (M.map (MulAut.conj u).toMonoidHom) (centralizer (T : Set G)) :=
    isCompIn_map_conj_of_mem_normalizer hM (mem_normalizer_centralizer_of_mem_normalizer hu)
  have hc : ∀ a ∈ M, ∀ b ∈ M.map (MulAut.conj u).toMonoidHom, a * b = b * a :=
    hM.commute_of_ne hMu hne
  have hsq : ∀ a ∈ M, u * u * a = a * (u * u) := by
    intro a ha
    have := mem_centralizer_iff.1 (hM.1 ha) (u ^ 2) hu2
    simpa [pow_two] using this
  have hKq := hKc.isQuasisimple
  set φ := Zassenhaus.foldHom u M hc with hφ
  have hker : φ.ker ≤ center ↥M := foldHom_ker_le_center hc
  have hR : CFSG.IsQuasisimple ↥φ.range :=
    Zassenhaus.isQuasisimple_range_of_ker_le_center hM.isQuasisimple φ hker
  have hKC : K ≤ centralizer ({u} : Set G) := by
    intro x hx
    have := hKc.1 hx
    rw [Step.centralizer_sup_zpowers] at this
    exact this.2
  have hKR : K ≤ φ.range := le_range_foldHom_of_sq hsq hc hKC hKq.1 hle
  have hRC : φ.range ≤ centralizer ((T ⊔ zpowers u : Subgroup G) : Set G) := by
    rw [Step.centralizer_sup_zpowers]
    exact le_inf ((range_foldHom_le_sup hc).trans (sup_le hM.1 hMu.1))
      (range_foldHom_le_centralizer_of_sq hsq hc)
  have hsub : (K.subgroupOf φ.range).IsSubnormal :=
    Zassenhaus.isSubnormal_subgroupOf_of_le hRC hKc.2.2
  have hKeq : K = φ.range :=
    Step.eq_of_le_of_isSubnormal_of_isQuasisimple hKR hKq hR hsub
  have hφK : ∀ m ∈ M, m * (u * m * u⁻¹) ∈ K := by
    intro m hm
    have : m * (u * m * u⁻¹) ∈ φ.range := ⟨⟨m, hm⟩, rfl⟩
    rwa [← hKeq] at this
  have hNM : M ≤ conjClosure K (layerIn (centralizer (T : Set G))) := by
    have hcomm : ⁅M, M⁆ ≤ conjClosure K (layerIn (centralizer (T : Set G))) := by
      rw [Subgroup.commutator_le]
      intro a ha m hm
      have hy : u * m * u⁻¹ ∈ M.map (MulAut.conj u).toMonoidHom :=
        ⟨m, hm, by simp [MulAut.conj_apply]⟩
      have hay : Commute a (u * m * u⁻¹) := hc a ha _ hy
      have h1 : a * (m * (u * m * u⁻¹)) * a⁻¹ ∈
          conjClosure K (layerIn (centralizer (T : Set G))) :=
        Junction.map_conj_le_conjClosure (Junction.le_layerIn_of_isCompIn hM ha)
          ⟨_, hφK m hm, by simp [MulAut.conj_apply]⟩
      have h2 : m * (u * m * u⁻¹) ∈ conjClosure K (layerIn (centralizer (T : Set G))) :=
        Junction.le_conjClosure _ _ (hφK m hm)
      have h3 : ⁅a, m⁆ = a * (m * (u * m * u⁻¹)) * a⁻¹ * (m * (u * m * u⁻¹))⁻¹ := by
        have h4 : (u * m * u⁻¹) * a⁻¹ = a⁻¹ * (u * m * u⁻¹) := hay.inv_left.eq.symm
        calc ⁅a, m⁆ = a * m * (a⁻¹ * (u * m * u⁻¹)) * (u * m * u⁻¹)⁻¹ * m⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = a * m * ((u * m * u⁻¹) * a⁻¹) * (u * m * u⁻¹)⁻¹ * m⁻¹ := by rw [h4]
          _ = _ := by group
      rw [h3]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    rwa [Subgroup.isPerfect_iff.1 hM.isQuasisimple.1] at hcomm
  have hNM' : M.map (MulAut.conj u).toMonoidHom ≤
      conjClosure K (layerIn (centralizer (T : Set G))) := by
    rintro _ ⟨m, hm, rfl⟩
    have h1 : (MulAut.conj u).toMonoidHom m = m⁻¹ * (m * (u * m * u⁻¹)) := by
      simp [MulAut.conj_apply]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hNM hm)) (Junction.le_conjClosure _ _ (hφK m hm))
  refine ⟨⟨hne, ?_⟩, le_antisymm (sup_le hNM hNM') ?_⟩
  · obtain ⟨e⟩ := Zassenhaus.nonempty_quotient_center_equiv_range hM.isQuasisimple φ hker
    subst hKeq
    exact ⟨e⟩
  · refine Junction.conjClosure_le_of_le_normalizer hle fun g hg => ?_
    exact Junction.mem_normalizer_sup (layerIn_le_normalizer hM hg)
      (layerIn_le_normalizer hMu hg)

theorem link_of_le_sup {T K M : Subgroup G} {u : G}
    (hu : u ∈ normalizer (T : Set G)) (hu2 : u ^ 2 ∈ T)
    (hKc : IsCompIn K (centralizer ((T ⊔ zpowers u : Subgroup G) : Set G)))
    (hM : IsCompIn M (centralizer (T : Set G)))
    (hle : K ≤ M ⊔ M.map (MulAut.conj u).toMonoidHom) :
    (M = M.map (MulAut.conj u).toMonoidHom ∨ Sol78Link5a M K u) ∧
      M ⊔ M.map (MulAut.conj u).toMonoidHom =
        conjClosure K (layerIn (centralizer (T : Set G))) := by
  by_cases h : M = M.map (MulAut.conj u).toMonoidHom
  · refine ⟨Or.inl h, ?_⟩
    have hKM : K ≤ M := by rwa [← h, sup_idem] at hle
    rw [← h, sup_idem]
    exact (conjClosure_layerIn_eq_of_le hM hKM hKc.isQuasisimple).symm
  · obtain ⟨h5a, hcl⟩ := diagonal_of_le_sup hu hu2 hKc hM hle h
    exact ⟨Or.inr h5a, hcl⟩

theorem pumpUp_trichotomy {T K : Subgroup G} {u : G}
    (hu : u ∈ normalizer (T : Set G)) (hu2 : u ^ 2 ∈ T)
    (hKc : IsCompIn K (centralizer ((T ⊔ zpowers u : Subgroup G) : Set G)))
    (hKL : K ≤ layerIn (centralizer (T : Set G))) :
    IsCompIn K (centralizer (T : Set G)) ∨
    ∃ M : Subgroup G, IsCompIn M (centralizer (T : Set G)) ∧ M ≠ K ∧
      (M = M.map (MulAut.conj u).toMonoidHom ∨ Sol78Link5a M K u) ∧
      K ≤ M ⊔ M.map (MulAut.conj u).toMonoidHom ∧
      M ⊔ M.map (MulAut.conj u).toMonoidHom =
        conjClosure K (layerIn (centralizer (T : Set G))) := by
  by_cases hK : IsCompIn K (centralizer (T : Set G))
  · exact Or.inl hK
  · right
    have hsq : ∀ m ∈ centralizer (T : Set G), u ^ 2 * m = m * u ^ 2 := fun m hm =>
      mem_centralizer_iff.1 hm (u ^ 2) hu2
    have hWT : zpowers u ≤ normalizer (T : Set G) := Subgroup.zpowers_le.2 hu
    obtain ⟨M, hM, hKM⟩ := Junction.exists_isCompIn_le_conjClosure hWT
      (by rwa [sup_comm] at hKc) hKL
    rw [conjClosure_zpowers_eq_of_sq M fun m hm => hsq m (hM.1 hm)] at hKM
    obtain ⟨hlink, hcl⟩ := link_of_le_sup hu hu2 hKc hM hKM
    refine ⟨M, hM, ?_, hlink, hKM, hcl⟩
    rintro rfl
    exact hK hM

theorem tLinks_single {T K M : Subgroup G} {u : G} (hT : IsPGroup 2 T)
    (hu : u ∈ normalizer (T : Set G)) (hu2 : u ^ 2 ∈ T)
    (hKc : IsCompIn K (centralizer ((T ⊔ zpowers u : Subgroup G) : Set G)))
    (hM : IsCompIn M (centralizer (T : Set G)))
    (hlink : M = M.map (MulAut.conj u).toMonoidHom ∨ Sol78Link5a M K u)
    (hle : K ≤ M ⊔ M.map (MulAut.conj u).toMonoidHom)
    (hcl : M ⊔ M.map (MulAut.conj u).toMonoidHom =
      conjClosure K (layerIn (centralizer (T : Set G)))) :
    TLinks G 1 (seq2 K M) (seq2 (T ⊔ zpowers u) T) (seq2 1 u) := by
  have hTu : IsPGroup 2 ↥(T ⊔ zpowers u) := isPGroup_sup_zpowers hT hu hu2
  have hu' : IsPGroup 2 ↥(zpowers u) := hTu.to_le le_sup_right
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · simpa [seq2] using ⟨hTu, hKc⟩
    · simpa [seq2] using ⟨hT, hM⟩
  · intro i h1 hi
    obtain rfl : i = 1 := le_antisymm hi h1
    simpa [seq2] using ⟨hu', hu, hu2, hKc⟩
  · intro i h1 hi
    obtain rfl : i = 1 := le_antisymm hi h1
    simpa [seq2] using ⟨hle, hcl⟩
  · intro i h1 hi
    obtain rfl : i = 1 := le_antisymm hi h1
    simpa [seq2] using hlink.symm

theorem tLinks_of_ltF {K M : Subgroup G} (hlt : LtF K M) :
    ∃ (T₀ T₁ : Subgroup G) (u : G), T₀ ≠ ⊥ ∧ T₁ ≠ ⊥ ∧
      TLinks G 1 (seq2 K M) (seq2 T₀ T₁) (seq2 1 u) := by
  obtain ⟨s, t, hs, ht, hst, hK, hM, hKM⟩ := hlt
  have hCT : centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hT2 : IsPGroup 2 ↥(zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hsN : s ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [hCT]
    exact mem_centralizer_singleton_iff.2 hst
  have hs2 : s ^ 2 ∈ zpowers t := by
    rw [pow_two, Zassenhaus.mul_self_eq_one_of_orderOf_eq_two hs]
    exact one_mem _
  have hMT : IsCompIn M (centralizer ((zpowers t : Subgroup G) : Set G)) := by rwa [hCT]
  have hMs : IsCompIn (M.map (MulAut.conj s).toMonoidHom) (centralizer ({t} : Set G)) :=
    Zassenhaus.isCompIn_conj_of_commute hst hM
  have hKt : K ≤ centralizer ({t} : Set G) := hKM.trans (sup_le hM.1 hMs.1)
  have hKc : IsCompIn K (centralizer ((zpowers t ⊔ zpowers s : Subgroup G) : Set G)) := by
    have hle : K ≤ centralizer ((zpowers t ⊔ zpowers s : Subgroup G) : Set G) := by
      rw [Step.centralizer_sup_zpowers, hCT]
      exact le_inf hKt hK.1
    refine isCompIn_of_le hK hle ?_
    rw [Step.centralizer_sup_zpowers]
    exact inf_le_right
  obtain ⟨hlink, hcl⟩ := link_of_le_sup hsN hs2 hKc hMT hKM
  have ht1 : zpowers t ≠ ⊥ := by
    intro h
    have h1 := Subgroup.zpowers_eq_bot.1 h
    rw [h1, orderOf_one] at ht
    omega
  exact ⟨zpowers t ⊔ zpowers s, zpowers t, s,
    fun h => ht1 (le_bot_iff.1 (h ▸ le_sup_left)), ht1,
    tLinks_single hT2 hsN hs2 hKc hMT hlink hKM hcl⟩

end Alternatives

end CFSG.EvenSporadicStandard.M12Std.Rbc
