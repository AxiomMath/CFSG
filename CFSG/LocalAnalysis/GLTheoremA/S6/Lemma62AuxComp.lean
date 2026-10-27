module

public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

namespace L62

variable {G : Type} [Group G] [Finite G] {p : ℕ}

noncomputable def phiC (p : ℕ) (C : Subgroup G) :
    ↥(Subgroup.normalizer (C : Set G)) →* MulAut (PSimple p C) :=
  (centerQuotientHom (PQuot p C)).comp (barAut p C)

theorem phiC_apply_mk (p : ℕ) (C : Subgroup G) (γ : ↥(Subgroup.normalizer (C : Set G))) (x : ↥C) :
    phiC p C γ (QuotientGroup.mk (QuotientGroup.mk x)) =
      QuotientGroup.mk (QuotientGroup.mk (C.normalizerMonoidHom γ x)) := by
  show onCenterQuotient (barAut p C γ) ((QuotientGroup.mk' (Subgroup.center (PQuot p C))) (QuotientGroup.mk x)) = _
  rw [onCenterQuotient_apply_mk]
  show QuotientGroup.mk (barAut p C γ (QuotientGroup.mk x)) = _
  rw [barAut_mk]

theorem phiC_inner (p : ℕ) {C : Subgroup G} (c : ↥C) (hc : (c : G) ∈ Subgroup.normalizer (C : Set G)) :
    phiC p C ⟨c, hc⟩ = MulAut.conj (QuotientGroup.mk (QuotientGroup.mk c) : PSimple p C) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [phiC_apply_mk, MulAut.conj_apply]
      have : (C.normalizerMonoidHom ⟨c, hc⟩) y = c * y * c⁻¹ := by
        apply Subtype.ext
        rfl
      rw [this]
      simp [map_mul, map_inv]

theorem phiC_eq_one_iff (hp : p.Prime) {X C : Subgroup G} (hC : GLAPComponent p X C) {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) : phiC p C ⟨g, hg⟩ = 1 ↔ CentMod p C g := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hC
  haveI : Group.IsPerfect (PQuot p C) := ⟨hq.1⟩
  rw [centMod_iff]
  constructor
  · intro h
    have h1 : barAut p C ⟨g, hg⟩ = 1 :=
      centerQuotientHom_injective (PQuot p C) (by
        rw [map_one]
        exact h)
    refine ⟨hg, fun l hl => ?_⟩
    have h2 := congrArg (fun σ : MulAut (PQuot p C) => σ (QuotientGroup.mk ⟨l⁻¹, C.inv_mem hl⟩)) h1
    simp only [barAut_mk, MulAut.one_apply] at h2
    have h3 := QuotientGroup.eq.1 h2
    have h4 : ((g * l⁻¹ * g⁻¹)⁻¹ * l⁻¹ : G) ∈ GLAPPrimeCoreOf p C :=
      Subgroup.mem_map_of_mem C.subtype h3
    have h5 : (⁅l, g⁆ : G) = ((g * l⁻¹ * g⁻¹)⁻¹ * l⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h5]
    exact Subgroup.inv_mem _ h4
  · intro h
    have h1 : barAut p C ⟨g, hg⟩ = 1 := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H x =>
        simp only [barAut_mk, MulAut.one_apply]
        rw [QuotientGroup.eq]
        have hc := h.2 ((x⁻¹ : ↥C) : G) (C.inv_mem x.2)
        obtain ⟨o', ho', hoe⟩ := Subgroup.mem_map.1 hc
        have : o' = x⁻¹ * (C.normalizerMonoidHom ⟨g, hg⟩) x := by
          apply Subtype.ext
          rw [Subgroup.coe_mul]
          refine hoe.trans ?_
          show ⁅((x⁻¹ : ↥C) : G), g⁆ = ((x⁻¹ : ↥C) : G) * (g * (x : G) * g⁻¹)
          simp only [commutatorElement_def, Subgroup.coe_inv]
          group
        have h6 : ((C.normalizerMonoidHom ⟨g, hg⟩) x)⁻¹ * x = o'⁻¹ := by
          rw [this]; group
        rw [h6]
        exact Subgroup.inv_mem _ ho'
    show centerQuotientHom (PQuot p C) (barAut p C ⟨g, hg⟩) = 1
    rw [h1, map_one]


theorem aut_two_group_trivial {P : Type*} [Group P] [Finite P] (hP : IsSimpleGroup P)
    (hnonab : ∃ a b : P, a * b ≠ b * a) (Sg : Subgroup (MulAut P)) (hSg : IsPGroup 2 Sg)
    (hnorm : ∀ x : P, (MulAut.conj x : MulAut P) ∈ Subgroup.normalizer (Sg : Set (MulAut P))) :
    Sg = ⊥ := by
  let M : Subgroup P := Sg.comap (MulAut.conj : P →* MulAut P)
  haveI hMn : M.Normal := ⟨fun m hm x => by
    show MulAut.conj (x * m * x⁻¹) ∈ Sg
    have h1 : (MulAut.conj x : MulAut P) * MulAut.conj m * (MulAut.conj x)⁻¹ ∈ Sg :=
      (Subgroup.mem_normalizer_iff.1 (hnorm x) _).1 hm
    simpa [map_mul, map_inv] using h1⟩
  rcases hP.eq_bot_or_eq_top_of_normal M with hM | hM
  · refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => ?_
    ext x
    have e : (MulAut.conj (σ x) : MulAut P) = σ * MulAut.conj x * σ⁻¹ := by
      ext y
      simp [MulAut.conj_apply]
    have hmem : (MulAut.conj (σ x * x⁻¹) : MulAut P) ∈ Sg := by
      have h2 : (MulAut.conj x : MulAut P) * σ⁻¹ * (MulAut.conj x)⁻¹ ∈ Sg :=
        (Subgroup.mem_normalizer_iff.1 (hnorm x) _).1 (Sg.inv_mem hσ)
      have h3 : σ * ((MulAut.conj x : MulAut P) * σ⁻¹ * (MulAut.conj x)⁻¹) ∈ Sg := Sg.mul_mem hσ h2
      have e2 : (MulAut.conj (σ x * x⁻¹) : MulAut P) =
          σ * ((MulAut.conj x : MulAut P) * σ⁻¹ * (MulAut.conj x)⁻¹) := by
        rw [map_mul, map_inv, e]
        group
      rw [e2]
      exact h3
    have h4 : σ x * x⁻¹ ∈ M := hmem
    rw [hM, Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.1 h4
  · exfalso
    have hall : ∀ x : P, (MulAut.conj x : MulAut P) ∈ Sg := fun x => by
      have : x ∈ M := hM ▸ Subgroup.mem_top x
      exact this
    haveI : Nontrivial P := hP.toNontrivial
    have hcen : Subgroup.center P = ⊥ := by
      rcases hP.eq_bot_or_eq_top_of_normal (Subgroup.center P) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        apply hab
        have ha : a ∈ Subgroup.center P := h ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.1 ha b).symm
    let f : P →* Sg := (MulAut.conj : P →* MulAut P).codRestrict Sg hall
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 : (MulAut.conj x : MulAut P) = MulAut.conj y := congrArg Subtype.val hxy
      have h5 : ∀ z : P, x * z * x⁻¹ = y * z * y⁻¹ := fun z => by
        have := congrArg (fun φ : MulAut P => φ z) h1
        simpa [MulAut.conj_apply] using this
      have h2 : y⁻¹ * x ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro g
        calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
          _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [h5 g]
          _ = y⁻¹ * x * g := by group
      rw [hcen, Subgroup.mem_bot] at h2
      exact (inv_mul_eq_one.1 h2).symm
    have hP2 : IsPGroup 2 P := IsPGroup.of_injective hSg f hf
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hP2.center_nontrivial
    rw [hcen] at this
    exact (not_subsingleton_iff_nontrivial.2 inferInstance) (inferInstance : Subsingleton (⊥ : Subgroup P))


theorem centralizes_component (hp : p.Prime) {X C J S : Subgroup G} (hC : GLAPComponent p X C)
    (hJC : J ≤ Subgroup.normalizer (C : Set G)) (hSC : S ≤ Subgroup.normalizer (C : Set G))
    (hS2 : IsPGroup 2 S)
    (hJS : J ≤ Subgroup.normalizer ((S ⊔ centModSubgroup p C : Subgroup G) : Set G))
    (hcov : C ≤ J ⊔ centModSubgroup p C) : S ≤ centModSubgroup p C := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hC
  have hsimple : IsSimpleGroup (PSimple p C) := hq.2
  have hnonab : ∃ a b : PSimple p C, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (PQuot p C) hq
  set Nn : Subgroup G := Subgroup.normalizer (C : Set G) with hNn
  set cm := centModSubgroup p C with hcm
  have hcmN : cm ≤ Nn := fun g hg => hg.1
  have hCN : C ≤ Nn := Subgroup.le_normalizer
  set Φ := phiC p C with hΦ
  set Sg : Subgroup (MulAut (PSimple p C)) := (S.subgroupOf Nn).map Φ with hSg
  have hSg2 : IsPGroup 2 Sg := hS2.comap_subtype.map Φ
  have hcm1 : (cm.subgroupOf Nn).map Φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro γ hγ
    have hγ' : (γ : G) ∈ cm := hγ
    exact (phiC_eq_one_iff hp hC γ.2).2 (centMod_iff.2 hγ')
  have hSS : ∀ (y : G) (hy : y ∈ S ⊔ cm) (hyN : y ∈ Nn), Φ ⟨y, hyN⟩ ∈ Sg := by
    intro y hy hyN
    have hmem : (⟨y, hyN⟩ : ↥Nn) ∈ (S ⊔ cm).subgroupOf Nn := hy
    rw [Subgroup.subgroupOf_sup hSC hcmN] at hmem
    have h1 : Φ ⟨y, hyN⟩ ∈ (S.subgroupOf Nn).map Φ ⊔ (cm.subgroupOf Nn).map Φ := by
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem Φ hmem
    rwa [hcm1, sup_bot_eq] at h1
  have hA : ∀ (j : G) (hj : j ∈ J), ∀ σ ∈ Sg, Φ ⟨j, hJC hj⟩ * σ * (Φ ⟨j, hJC hj⟩)⁻¹ ∈ Sg := by
    intro j hj σ hσ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hσ
    have htS : (t : G) ∈ S := ht
    have hyS : j * (t : G) * j⁻¹ ∈ S ⊔ cm :=
      (Subgroup.mem_normalizer_iff.1 (hJS hj) _).1 (Subgroup.mem_sup_left htS)
    have hyN : j * (t : G) * j⁻¹ ∈ Nn :=
      Nn.mul_mem (Nn.mul_mem (hJC hj) t.2) (Nn.inv_mem (hJC hj))
    have := hSS _ hyS hyN
    convert this using 1
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hJn : ∀ (j : G) (hj : j ∈ J),
      Φ ⟨j, hJC hj⟩ ∈ Subgroup.normalizer (Sg : Set (MulAut (PSimple p C))) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hA j hj h hh, fun hh => ?_⟩
    have h1 := hA j⁻¹ (J.inv_mem hj) _ hh
    have e : Φ ⟨j⁻¹, hJC (J.inv_mem hj)⟩ = (Φ ⟨j, hJC hj⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e] at h1
    have e2 : (Φ ⟨j, hJC hj⟩)⁻¹ * (Φ ⟨j, hJC hj⟩ * h * (Φ ⟨j, hJC hj⟩)⁻¹) *
        ((Φ ⟨j, hJC hj⟩)⁻¹)⁻¹ = h := by group
    rwa [e2] at h1
  have hnorm : ∀ x : PSimple p C,
      (MulAut.conj x : MulAut (PSimple p C)) ∈ Subgroup.normalizer (Sg : Set (MulAut (PSimple p C))) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    have hcN : (c : G) ∈ Nn := hCN c.2
    rw [← phiC_inner p c hcN]
    have hmem : (⟨c, hcN⟩ : ↥Nn) ∈ (J ⊔ cm).subgroupOf Nn := hcov c.2
    rw [Subgroup.subgroupOf_sup hJC hcmN] at hmem
    have h1 : Φ ⟨c, hcN⟩ ∈ (J.subgroupOf Nn).map Φ ⊔ (cm.subgroupOf Nn).map Φ := by
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem Φ hmem
    rw [hcm1, sup_bot_eq] at h1
    obtain ⟨jj, hjj, hΦjj⟩ := Subgroup.mem_map.1 h1
    have hjjJ : (jj : G) ∈ J := hjj
    rw [← hΦjj]
    exact hJn jj hjjJ
  have hSg0 : Sg = ⊥ := aut_two_group_trivial hsimple hnonab Sg hSg2 hnorm
  intro s hs
  have hsN : s ∈ Nn := hSC hs
  have h1 : Φ ⟨s, hsN⟩ ∈ Sg :=
    Subgroup.mem_map_of_mem Φ (show (⟨s, hsN⟩ : ↥Nn) ∈ S.subgroupOf Nn from hs)
  rw [hSg0, Subgroup.mem_bot] at h1
  exact centMod_iff.1 ((phiC_eq_one_iff hp hC hsN).1 h1)

theorem conj_mem_centModSubgroup {C : Subgroup G} {g m : G} (hg : g ∈ Subgroup.normalizer (C : Set G))
    (hm : m ∈ centModSubgroup p C) : g * m * g⁻¹ ∈ centModSubgroup p C := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hm.1) (Subgroup.inv_mem _ hg), fun l hl => ?_⟩
  have h1 : g⁻¹ * l * g ∈ C := (Subgroup.mem_normalizer_iff''.1 hg l).1 hl
  have h2 : ⁅g⁻¹ * l * g, m⁆ ∈ GLAPPrimeCoreOf p C := hm.2 _ h1
  have e : ⁅l, g * m * g⁻¹⁆ = g * ⁅g⁻¹ * l * g, m⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p C hg) _).1 h2

theorem normalizer_le_normalizer_centModSubgroup (p : ℕ) (C : Subgroup G) :
    Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (centModSubgroup p C : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_centModSubgroup hg hh, fun hh => ?_⟩
  have := conj_mem_centModSubgroup (Subgroup.inv_mem _ hg) hh
  simpa [mul_assoc] using this

theorem comm_mem_of_forall_component {K S O : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hK : (⨆ C ∈ 𝒞, C) = K) (hO : K ≤ Subgroup.normalizer (O : Set G))
    (h : ∀ C ∈ 𝒞, ∀ c ∈ C, ∀ s ∈ S, ⁅c, s⁆ ∈ O) : ∀ k ∈ K, ∀ s ∈ S, ⁅k, s⁆ ∈ O := by
  let Z : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∀ s ∈ S, ⁅k, s⁆ ∈ O}
      mul_mem' := by
        rintro a b ⟨ha, haS⟩ ⟨hb, hbS⟩
        refine ⟨K.mul_mem ha hb, fun s hs => ?_⟩
        have e : ⁅a * b, s⁆ = a * ⁅b, s⁆ * a⁻¹ * ⁅a, s⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hO ha) _).1 (hbS s hs)
          |> fun h => by simpa [mul_assoc] using h) (haS s hs)
      one_mem' := ⟨K.one_mem, fun s _ => by
        rw [commutatorElement_one_left]
        exact O.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, haS⟩
        refine ⟨K.inv_mem ha, fun s hs => ?_⟩
        have e : ⁅a⁻¹, s⁆ = a⁻¹ * ⁅a, s⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 : ⁅a, s⁆⁻¹ ∈ O := O.inv_mem (haS s hs)
        have h2 := (Subgroup.mem_normalizer_iff.1 (hO (K.inv_mem ha)) _).1 h1
        simpa [mul_assoc] using h2 }
  have hZ : K ≤ Z := by
    rw [← hK]
    exact iSup₂_le fun C hC c hc => ⟨(hK ▸ le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) C hC) hc, h C hC c hc⟩
  intro k hk s hs
  exact (hZ hk).2 s hs

theorem claim_of_projection (hp : p.Prime) {X K J S : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hK : (⨆ C ∈ 𝒞, C) = K) (hKX : IsSubnormal K X)
    (hJK : J ≤ K) (hS2 : IsPGroup 2 S) (hSK : S ≤ K)
    (hJS : J ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G))
    (hproj : ∀ C ∈ 𝒞, C ≤ J ⊔ centModSubgroup p C) :
    ⁅S, J⁆ ≤ GLAPPrimeCoreOf p K := by
  have hKL : K ≤ GLAPLayer p X := by
    rw [← hK]
    exact iSup₂_le fun C hC => le_sSup (hcomp C hC)
  have hKN : ∀ C ∈ 𝒞, K ≤ Subgroup.normalizer (C : Set G) := fun C hC =>
    hKL.trans (i183_glaPLayer_le_normalizer hp (hcomp C hC))
  have hCK : ∀ C ∈ 𝒞, C ≤ K := fun C hC =>
    hK ▸ le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) C hC
  have hKXle : K ≤ X := isSubnormal_le' hKX
  have hCsub : ∀ C ∈ 𝒞, IsSubnormal C K := fun C hC =>
    isSubnormal_of_le_of_le (hcomp C hC).2.1 (hCK C hC) hKXle
  have hOC : ∀ C ∈ 𝒞, GLAPPrimeCoreOf p C ≤ GLAPPrimeCoreOf p K := fun C hC =>
    glaPPrimeCoreOf_le_of_isSubnormal hp (hCsub C hC)
  have hKO : K ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) := le_normalizer_glaPPrimeCoreOf p K
  have hOcm : ∀ C ∈ 𝒞, GLAPPrimeCoreOf p K ≤ centModSubgroup p C := by
    intro C hC o ho
    have hoN : o ∈ Subgroup.normalizer (C : Set G) :=
      hKN C hC (Subgroup.map_subtype_le _ ho)
    refine ⟨hoN, fun l hl => ?_⟩
    have h1 : ⁅l, o⁆ ∈ GLAPPrimeCoreOf p K := by
      rw [commutatorElement_def]
      have : l * o * l⁻¹ ∈ GLAPPrimeCoreOf p K :=
        (Subgroup.mem_normalizer_iff.1 (hKO (hCK C hC hl)) o).1 ho
      exact (GLAPPrimeCoreOf p K).mul_mem this ((GLAPPrimeCoreOf p K).inv_mem ho)
    have h2 : ⁅l, o⁆ ∈ C := by
      have h3 : o * l⁻¹ * o⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 hoN _).1 (C.inv_mem hl)
      have e : ⁅l, o⁆ = l * (o * l⁻¹ * o⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [e]
      exact C.mul_mem hl h3
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp (hCsub C hC)]
    exact ⟨h2, h1⟩
  have hJC : ∀ C ∈ 𝒞, J ≤ Subgroup.normalizer (C : Set G) := fun C hC => hJK.trans (hKN C hC)
  have hSC : ∀ C ∈ 𝒞, S ≤ Subgroup.normalizer (C : Set G) := fun C hC => hSK.trans (hKN C hC)
  have hJS' : ∀ C ∈ 𝒞, J ≤ Subgroup.normalizer ((S ⊔ centModSubgroup p C : Subgroup G) : Set G) := by
    intro C hC j hj
    have h1 : j ∈ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p K ⊔ centModSubgroup p C : Subgroup G) : Set G) :=
      i183_mem_normalizer_sup (hJS hj) (normalizer_le_normalizer_centModSubgroup p C (hJC C hC hj))
    have e : S ⊔ GLAPPrimeCoreOf p K ⊔ centModSubgroup p C = S ⊔ centModSubgroup p C := by
      rw [sup_assoc, sup_eq_right.2 (hOcm C hC)]
    rwa [e] at h1
  have hScm : ∀ C ∈ 𝒞, S ≤ centModSubgroup p C := fun C hC =>
    centralizes_component hp (hcomp C hC) (hJC C hC) (hSC C hC) hS2 (hJS' C hC) (hproj C hC)
  have hcomm : ∀ k ∈ K, ∀ s ∈ S, ⁅k, s⁆ ∈ GLAPPrimeCoreOf p K := by
    refine comm_mem_of_forall_component hK hKO fun C hC c hc s hs => ?_
    exact hOC C hC ((hScm C hC hs).2 c hc)
  refine Subgroup.commutator_le.2 fun s hs j hj => ?_
  have := (GLAPPrimeCoreOf p K).inv_mem (hcomm j (hJK hj) s hs)
  rwa [commutatorElement_inv] at this

end L62

end CFSG.LocalAnalysis.GLTheoremA
