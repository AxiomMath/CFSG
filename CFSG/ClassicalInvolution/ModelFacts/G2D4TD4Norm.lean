module

public import CFSG.LieType.Steinberg.TwistedD4.Fixed
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralFixedBruhat
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LieType.Chevalley.HeightSeries
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley

section Orbit

@[expose] def td4Orb (γ : Fin d4.rank → ℤ) : Set (Fin d4.rank → ℤ) :=
  {γ, rho γ, rho (rho γ)}

theorem self_mem_td4Orb (γ : Fin d4.rank → ℤ) : γ ∈ td4Orb γ := Set.mem_insert _ _

theorem td4Orb_rho (γ : Fin d4.rank → ℤ) : td4Orb (rho γ) = td4Orb γ := by
  ext x
  simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff, rho_rho_rho]
  tauto

theorem td4Orb_eq_of_mem {γ δ : Fin d4.rank → ℤ} (h : δ ∈ td4Orb γ) : td4Orb δ = td4Orb γ := by
  simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl
  · rfl
  · exact td4Orb_rho γ
  · rw [td4Orb_rho, td4Orb_rho]

theorem isRoot_of_mem_td4Orb {γ δ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (h : δ ∈ td4Orb γ) :
    IsRoot d4 δ := by
  simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl
  · exact hγ
  · exact isRoot_rho hγ
  · exact isRoot_rho (isRoot_rho hγ)

theorem proj_eq_of_mem_td4Orb {γ δ : Fin d4.rank → ℤ} (h : δ ∈ td4Orb γ) : proj δ = proj γ := by
  simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl
  · rfl
  · exact proj_rho γ
  · rw [proj_rho, proj_rho]

theorem rho_mem_td4Orb_of_mem {γ δ : Fin d4.rank → ℤ} (h : δ ∈ td4Orb γ) :
    rho δ ∈ td4Orb γ := by
  rw [← td4Orb_eq_of_mem h]
  exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem rho_neg (v : Fin d4.rank → ℤ) : rho (-v) = -rho v := by
  funext l
  simp [rho, permLattice]

end Orbit

section Translate

variable {K : Type} [Field K]

theorem map_rootGroup_td4 {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    (rootGroup (rootOperatorFamily d4) K γ).map (adjointGroup d4 K).subtype =
      CFSG.Blueprint.Chevalley.rootSubgroup d4 K γ := by
  have h : (CFSG.Blueprint.Chevalley.rootSubgroup d4 K γ).subgroupOf (adjointGroup d4 K) =
      rootGroup (rootOperatorFamily d4) K γ := by
    rw [rootGroup_of_isRoot hγ]
    exact (rootOperatorFamily d4).subgroupOf_rootSubgroup_eq K ⟨γ, hγ⟩
  rw [← h]
  exact Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup γ)

theorem map_iSup_rootGroup_td4 {Ψ : Set (Fin d4.rank → ℤ)} (hΨ : ∀ α ∈ Ψ, IsRoot d4 α) :
    (⨆ α ∈ Ψ, rootGroup (rootOperatorFamily d4) K α).map (adjointGroup d4 K).subtype =
      rootSpan d4 K Ψ := by
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun α => iSup_congr fun hα => map_rootGroup_td4 (hΨ α hα)

theorem rootSpan_td4Orb (γ : Fin d4.rank → ℤ) :
    rootSpan d4 K (td4Orb γ) = CFSG.Blueprint.Chevalley.rootSubgroup d4 K γ ⊔
      CFSG.Blueprint.Chevalley.rootSubgroup d4 K (rho γ) ⊔
        CFSG.Blueprint.Chevalley.rootSubgroup d4 K (rho (rho γ)) := by
  simp only [rootSpan, td4Orb, iSup_insert, iSup_singleton, sup_assoc]

theorem map_twistedRootSubgroupD4_eq (σ : K →+* K) {α₀ : Fin d4.rank → ℤ} (hα₀ : IsRoot d4 α₀) :
    (twistedRootSubgroupD4 σ (proj α₀)).map (adjointGroup d4 K).subtype =
      rootSpan d4 K (td4Orb α₀) ⊓ twistedFixedGroup TwistTag.D4 K σ := by
  have hsp : (rootGroup (rootOperatorFamily d4) K α₀ ⊔
      rootGroup (rootOperatorFamily d4) K (rho α₀) ⊔
        rootGroup (rootOperatorFamily d4) K (rho (rho α₀))).map (adjointGroup d4 K).subtype =
      rootSpan d4 K (td4Orb α₀) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, map_rootGroup_td4 hα₀,
      map_rootGroup_td4 (isRoot_rho hα₀), map_rootGroup_td4 (isRoot_rho (isRoot_rho hα₀)),
      rootSpan_td4Orb]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxP, hxF⟩ := (mem_twistedRootSubgroupD4_iff σ hα₀ rfl x).1 hx
    refine ⟨?_, (coe_mem_twistedFixedGroup_iff TwistTag.D4 K σ x).2 hxF⟩
    rw [← hsp]
    exact Subgroup.mem_map_of_mem _ hxP
  · rintro ⟨hyP, hyF⟩
    rw [← hsp] at hyP
    obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.1 hyP
    exact ⟨x, (mem_twistedRootSubgroupD4_iff σ hα₀ rfl x).2
      ⟨hxP, (coe_mem_twistedFixedGroup_iff TwistTag.D4 K σ x).1 hyF⟩, rfl⟩

theorem htHom_rho (v : Fin d4.rank → ℤ) : htHom (rho v) = htHom v := by
  rw [htHom_apply, htHom_apply, ← ht_proj, proj_rho, ht_proj]

theorem rootSpan_inf_twistedFixed_le (σ : K →+* K) {Ψ : Set (Fin d4.rank → ℤ)}
    (hΨ : ∀ α ∈ Ψ, IsRoot d4 α ∧ 0 < height α)
    (hclosed : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot d4 (α + β) → α + β ∈ Ψ)
    (hρ : ∀ α ∈ Ψ, rho α ∈ Ψ) :
    rootSpan d4 K Ψ ⊓ twistedFixedGroup TwistTag.D4 K σ ≤
      ⨆ β ∈ proj '' Ψ, (twistedRootSubgroupD4 σ β).map (adjointGroup d4 K).subtype := by
  rintro u ⟨huS, huF⟩
  rw [← map_iSup_rootGroup_td4 fun α hα => (hΨ α hα).1] at huS
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 huS
  have hxF : twistC TwistTag.D4 K σ x = x :=
    (coe_mem_twistedFixedGroup_iff TwistTag.D4 K σ x).1 huF
  have h62 := iSup_rootGroup_inf_twistFixed_le σ (f := htHom) htHom_rho
    (fun α hα => ⟨(hΨ α hα).1, by rw [htHom_apply]; exact (hΨ α hα).2⟩) hclosed hρ
  have hxm := h62 (Subgroup.mem_inf.2 ⟨hx, (mem_twistFixed TwistTag.D4 K σ).2 hxF⟩)
  have := Subgroup.mem_map_of_mem (adjointGroup d4 K).subtype hxm
  simpa only [Subgroup.map_iSup] using this

end Translate

section Commute

variable {K : Type} [Field K]

theorem subgroupOf_rootSubgroup_td4 {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    (CFSG.Blueprint.Chevalley.rootSubgroup d4 K γ).subgroupOf (adjointGroup d4 K) =
      rootGroup (rootOperatorFamily d4) K γ := by
  rw [rootGroup_of_isRoot hγ]
  exact (rootOperatorFamily d4).subgroupOf_rootSubgroup_eq K ⟨γ, hγ⟩

theorem commute_rootSubgroup_td4 {γ δ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hδ : IsRoot d4 δ)
    (hne : γ ≠ δ) (hne' : γ ≠ -δ) (hsum : ¬IsRoot d4 (γ + δ))
    {x y : ModGL d4 K} (hx : x ∈ CFSG.Blueprint.Chevalley.rootSubgroup d4 K γ)
    (hy : y ∈ CFSG.Blueprint.Chevalley.rootSubgroup d4 K δ) : x * y = y * x := by
  have hxG : x ∈ adjointGroup d4 K := rootSubgroup_le_adjointGroup γ hx
  have hyG : y ∈ adjointGroup d4 K := rootSubgroup_le_adjointGroup δ hy
  have hx' : (⟨x, hxG⟩ : adjointGroup d4 K) ∈ rootGroup (rootOperatorFamily d4) K γ := by
    rw [← subgroupOf_rootSubgroup_td4 hγ]
    exact hx
  have hy' : (⟨y, hyG⟩ : adjointGroup d4 K) ∈ rootGroup (rootOperatorFamily d4) K δ := by
    rw [← subgroupOf_rootSubgroup_td4 hδ]
    exact hy
  have h := commute_of_mem_rootGroup hγ hδ hne hne' hsum hx' hy'
  exact congrArg Subtype.val h.eq

theorem commute_rootSpan_td4 {S T : Set (Fin d4.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot d4 γ)
    (hT : ∀ δ ∈ T, IsRoot d4 δ)
    (h : ∀ γ ∈ S, ∀ δ ∈ T, γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ))
    {x y : ModGL d4 K} (hx : x ∈ rootSpan d4 K S) (hy : y ∈ rootSpan d4 K T) :
    x * y = y * x := by
  have h1 : ∀ γ ∈ S, ∀ z ∈ CFSG.Blueprint.Chevalley.rootSubgroup d4 K γ,
      rootSpan d4 K T ≤ Subgroup.centralizer ({z} : Set (ModGL d4 K)) := by
    intro γ hγ z hz
    refine iSup₂_le fun δ hδ => fun y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨h1, h2, h3⟩ := h γ hγ δ hδ
    exact (commute_rootSubgroup_td4 (hS γ hγ) (hT δ hδ) h1 h2 h3 hz hy).symm
  have h2 : ∀ γ ∈ S, CFSG.Blueprint.Chevalley.rootSubgroup d4 K γ ≤
      Subgroup.centralizer ({y} : Set (ModGL d4 K)) := by
    intro γ hγ z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (h1 γ hγ z hz hy)).symm
  have h3 : rootSpan d4 K S ≤ Subgroup.centralizer ({y} : Set (ModGL d4 K)) :=
    iSup₂_le fun γ hγ => h2 γ hγ
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h3 hx))

end Commute

section Main

variable {K : Type} [Field K]

@[expose] def psiTD4 (a : Fin d4.rank → Kˣ) : Set (Fin d4.rank → ℤ) :=
  rootCharKernel a ∩ {α | IsRoot d4 α ∧ 0 < height α}

@[expose] def nodeGroupTD4 (σ : K →+* K) (α₀ : Fin d4.rank → ℤ) : Subgroup (ModGL d4 K) :=
  (rootSpan d4 K (td4Orb α₀) ⊓ twistedFixedGroup TwistTag.D4 K σ) ⊔
    (rootSpan d4 K (td4Orb (-α₀)) ⊓ twistedFixedGroup TwistTag.D4 K σ)

theorem neg_mem_td4Orb_neg {γ δ : Fin d4.rank → ℤ} (h : δ ∈ td4Orb γ) : -δ ∈ td4Orb (-γ) := by
  simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (rho_neg γ).symm)
  · exact Or.inr (Or.inr (by rw [rho_neg, rho_neg]))

theorem smul_rho_td4 {w : WeylGroup d4} (hw : weylTwist TwistTag.D4 w = w)
    (v : Fin d4.rank → ℤ) : w • rho v = rho (w • v) := by
  have := weylTwist_smul_permLattice TwistTag.D4 w v
  rw [hw] at this
  exact this

theorem image_td4Orb {w : WeylGroup d4} (hw : weylTwist TwistTag.D4 w = w)
    (γ : Fin d4.rank → ℤ) : (fun α => w • α) '' td4Orb γ = td4Orb (w • γ) := by
  simp only [td4Orb, Set.image_insert_eq, Set.image_singleton, smul_rho_td4 hw]

theorem map_conj_nodeGroup {σ : K →+* K} {α₀ : Fin d4.rank → ℤ} {x : ModGL d4 K}
    (hx : x ∈ twistedFixedGroup TwistTag.D4 K σ) {P Q : Subgroup (ModGL d4 K)}
    (hP : (rootSpan d4 K (td4Orb α₀)).map (MulAut.conj x).toMonoidHom = P)
    (hQ : (rootSpan d4 K (td4Orb (-α₀))).map (MulAut.conj x).toMonoidHom = Q) :
    (nodeGroupTD4 σ α₀).map (MulAut.conj x).toMonoidHom =
      (P ⊓ twistedFixedGroup TwistTag.D4 K σ) ⊔ (Q ⊓ twistedFixedGroup TwistTag.D4 K σ) := by
  have hΓ : (twistedFixedGroup TwistTag.D4 K σ).map (MulAut.conj x).toMonoidHom =
      twistedFixedGroup TwistTag.D4 K σ :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)
  rw [nodeGroupTD4, Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, hP, hQ, hΓ]

end Main

section Theorem

variable {K : Type} [Field K]

theorem mem_normalizer_of_commute_td4 {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (h : ∀ y ∈ H, x * y = y * x) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ = y := by rw [h y hy]; group
    rwa [this]
  · intro hz
    have h1 : x * (x * y * x⁻¹) = x * y := by rw [h _ hz]; group
    exact (mul_left_cancel h1) ▸ hz

theorem nodeGroupTD4_le_rootSpan (σ : K →+* K) (α₀ : Fin d4.rank → ℤ) :
    nodeGroupTD4 σ α₀ ≤ rootSpan d4 K (td4Orb α₀ ∪ td4Orb (-α₀)) :=
  sup_le (inf_le_left.trans (rootSpan_mono Set.subset_union_left))
    (inf_le_left.trans (rootSpan_mono Set.subset_union_right))

theorem mem_normalizer_nodeGroup_of_centralizes (σ : K ≃+* K) (a : Fin d4.rank → Kˣ)
    {α₀ : Fin d4.rank → ℤ} (hα₀ : IsRoot d4 α₀)
    (hWeyl : ∀ w : WeylGroup d4, weylTwist TwistTag.D4 w = w →
      (∀ v, rootChar a (w • v) = rootChar a v) →
        w • α₀ ∈ td4Orb α₀ ∨ w • α₀ ∈ td4Orb (-α₀))
    (hclosed : ∀ α ∈ psiTD4 a, ∀ β ∈ psiTD4 a, IsRoot d4 (α + β) → α + β ∈ psiTD4 a)
    (hρ : ∀ α ∈ psiTD4 a, rho α ∈ psiTD4 a)
    (hnode : ∀ γ ∈ psiTD4 a, γ ∉ td4Orb α₀ → ∀ δ ∈ td4Orb α₀ ∪ td4Orb (-α₀),
      γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ))
    {g : ModGL d4 K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hga : g ∈ Subgroup.centralizer ({rootDiagUnit d4 a} : Set (ModGL d4 K))) :
    g ∈ Subgroup.normalizer (nodeGroupTD4 σ.toRingHom α₀ : Set (ModGL d4 K)) := by
  set Γ := twistedFixedGroup TwistTag.D4 K σ.toRingHom with hΓ
  have hα₀' : IsRoot d4 (-α₀) := IsRoot.neg hα₀
  obtain ⟨w, hw1, hwa, h, hh, u, hu, v, hv, hgeq⟩ :=
    graphFixed_toral_centralizer_Bruhat_factors TwistTag.D4 K σ a hg hga
  have hwρ : weylTwist TwistTag.D4 w = w := hw1
  have hgΓ : g ∈ Γ := graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hg
  have hhm := Subgroup.mem_inf.1 hh
  have hhT : h ∈ torusGroup d4 K := (Subgroup.mem_inf.1 hhm.1).1
  have hhΓ : h ∈ Γ := (Subgroup.mem_inf.1 hhm.1).2
  have huΓ : u ∈ Γ := (Subgroup.mem_inf.1 hu).2
  have hvΓ : v ∈ Γ := (Subgroup.mem_inf.1 hv).2
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K w with hn
  have hnΓ : n ∈ Γ := by
    have e : n = (h * u)⁻¹ * g * v⁻¹ := by rw [hgeq]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (mul_mem hhΓ huΓ)) hgΓ) (inv_mem hvΓ)
  have hNh : h ∈ Subgroup.normalizer (nodeGroupTD4 σ.toRingHom α₀ : Set (ModGL d4 K)) := by
    have hPp : h ∈ Subgroup.normalizer (rootSpan d4 K (td4Orb α₀) : Set (ModGL d4 K)) :=
      torusGroup_le_normalizer_rootSpan (fun γ hγ => isRoot_of_mem_td4Orb hα₀ hγ) hhT
    have hPn : h ∈ Subgroup.normalizer (rootSpan d4 K (td4Orb (-α₀)) : Set (ModGL d4 K)) :=
      torusGroup_le_normalizer_rootSpan (fun γ hγ => isRoot_of_mem_td4Orb hα₀' hγ) hhT
    exact mem_normalizer_of_map_eq (map_conj_nodeGroup hhΓ (map_conj_eq_of_mem_normalizer hPp)
      (map_conj_eq_of_mem_normalizer hPn))
  have hNn : n ∈ Subgroup.normalizer (nodeGroupTD4 σ.toRingHom α₀ : Set (ModGL d4 K)) := by
    have hT := (canonical_weyl_root_transport TwistTag.D4.tag K).1 w
    have hmapP : (rootSpan d4 K (td4Orb α₀)).map (MulAut.conj n).toMonoidHom =
        rootSpan d4 K (td4Orb (w • α₀)) := by
      rw [hT _ (fun γ hγ => isRoot_of_mem_td4Orb hα₀ hγ), image_td4Orb hwρ]
    have hmapQ : (rootSpan d4 K (td4Orb (-α₀))).map (MulAut.conj n).toMonoidHom =
        rootSpan d4 K (td4Orb (w • (-α₀))) := by
      rw [hT _ (fun γ hγ => isRoot_of_mem_td4Orb hα₀' hγ), image_td4Orb hwρ]
    have hwa' : ∀ v, rootChar a (w • v) = rootChar a v := hwa
    rcases hWeyl w hwρ hwa' with h1 | h1
    · have e1 : td4Orb (w • α₀) = td4Orb α₀ := td4Orb_eq_of_mem h1
      have e2 : td4Orb (w • (-α₀)) = td4Orb (-α₀) := by
        rw [smul_neg]
        exact td4Orb_eq_of_mem (neg_mem_td4Orb_neg h1)
      rw [e1] at hmapP
      rw [e2] at hmapQ
      exact mem_normalizer_of_map_eq (map_conj_nodeGroup hnΓ hmapP hmapQ)
    · have e1 : td4Orb (w • α₀) = td4Orb (-α₀) := td4Orb_eq_of_mem h1
      have e2 : td4Orb (w • (-α₀)) = td4Orb α₀ := by
        rw [smul_neg]
        have := neg_mem_td4Orb_neg h1
        rw [neg_neg] at this
        exact td4Orb_eq_of_mem this
      rw [e1] at hmapP
      rw [e2] at hmapQ
      refine mem_normalizer_of_map_eq ?_
      rw [map_conj_nodeGroup hnΓ hmapP hmapQ, sup_comm]
      rfl
  have hΨN : rootSpan d4 K (psiTD4 a) ⊓ Γ ≤
      Subgroup.normalizer (nodeGroupTD4 σ.toRingHom α₀ : Set (ModGL d4 K)) := by
    refine (rootSpan_inf_twistedFixed_le σ.toRingHom (fun α hα => hα.2) hclosed hρ).trans ?_
    refine iSup₂_le fun β hβ => ?_
    obtain ⟨α, hαΨ, rfl⟩ := hβ
    by_cases hαo : α ∈ td4Orb α₀
    · rw [proj_eq_of_mem_td4Orb hαo, map_twistedRootSubgroupD4_eq σ.toRingHom hα₀]
      exact le_sup_left.trans Subgroup.le_normalizer
    · rw [map_twistedRootSubgroupD4_eq σ.toRingHom hαΨ.2.1]
      refine inf_le_left.trans ?_
      intro x hx
      refine mem_normalizer_of_commute_td4 fun y hy => ?_
      have hyL := nodeGroupTD4_le_rootSpan σ.toRingHom α₀ hy
      have hmemΨ : ∀ γ ∈ td4Orb α, γ ∈ psiTD4 a := by
        intro γ hγ
        simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
        rcases hγ with rfl | rfl | rfl
        · exact hαΨ
        · exact hρ _ hαΨ
        · exact hρ _ (hρ _ hαΨ)
      have hcond : ∀ γ ∈ td4Orb α, ∀ δ ∈ td4Orb α₀ ∪ td4Orb (-α₀),
          γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ) := by
        intro γ hγ δ hδ
        refine hnode γ (hmemΨ γ hγ) (fun hγo => hαo ?_) δ hδ
        have e1 := td4Orb_eq_of_mem hγ
        have e2 := td4Orb_eq_of_mem hγo
        have hself := self_mem_td4Orb α
        rw [← e1, e2] at hself
        exact hself
      exact commute_rootSpan_td4 (fun γ hγ => isRoot_of_mem_td4Orb hαΨ.2.1 hγ)
        (fun δ hδ => hδ.elim (fun h => isRoot_of_mem_td4Orb hα₀ h)
          (fun h => isRoot_of_mem_td4Orb hα₀' h)) hcond hx hyL
  have hNu := hΨN hu
  have hsub : rootCharKernel a ∩ inversionSet w ⊆ psiTD4 a :=
    fun α hα => ⟨hα.1, hα.2.1, hα.2.2.1⟩
  have hNv : v ∈ Subgroup.normalizer (nodeGroupTD4 σ.toRingHom α₀ : Set (ModGL d4 K)) :=
    hΨN (Subgroup.mem_inf.2 ⟨rootSpan_mono hsub (Subgroup.mem_inf.1 hv).1, hvΓ⟩)
  rw [hgeq]
  exact mul_mem (mul_mem (mul_mem hNh hNu) hNn) hNv

end Theorem

end CFSG.ClassicalInvolution.G2D4Models
