module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XHyp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.S172X
open scoped commutatorElement

variable {Ω : Type} [Group Ω] {S B N D K : Subgroup Ω} {x : Ω}
  {Γ : Type} [Group Γ] {G₀ Ghat : Subgroup Γ}

namespace S172DModel

variable (M : S172DModel S B G₀ Ghat)

private theorem mem_img {X : Subgroup Ω} {y : Γ} :
    y ∈ M.img X ↔ ∃ b : ↥B, (b : Ω) ∈ X ∧ ((M.β b : ↥Ghat) : Γ) = y := by
  rw [S172DModel.img, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hya⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨b, hb, hya⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨M.β b, Subgroup.mem_map.2 ⟨b, hb, rfl⟩, rfl⟩

private lemma img_le_barB : M.img D ≤ M.barB := by
  rw [S172DModel.img, S172DModel.barB]
  exact Subgroup.map_mono (Subgroup.map_le_range M.β (D.subgroupOf B))

private lemma pi_mem_piImg {X : Subgroup Ω} (hX : X ≤ S) {t : ↥S} (ht : (t : Ω) ∈ X) :
    ((M.π t : ↥G₀) : Γ) ∈ M.piImg X := by
  rw [S172DModel.piImg, Subgroup.map_map]
  exact Subgroup.mem_map_of_mem (G₀.subtype.comp M.π) (Subgroup.mem_subgroupOf.2 ht)

private lemma inf_centralizer_eq_zpowers_of_cent (hcent : ∀ b ∈ B,
    b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x) (hmem : x ∈ B)
    {D' : Subgroup Ω} (hD'B : D' ≤ B) (hxD' : x ∈ D') :
    D' ⊓ Subgroup.centralizer (S : Set Ω) = Subgroup.zpowers x := by
  apply le_antisymm
  · intro b hb
    exact (hcent b (hD'B hb.1)).1 hb.2
  · rw [le_inf_iff]
    exact ⟨Subgroup.zpowers_le.2 hxD',
      Subgroup.zpowers_le.2 ((hcent x hmem).2 (Subgroup.mem_zpowers x))⟩

private theorem card_img_eq_prime [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {D' : Subgroup Ω} (hD'B : D' ≤ B) (hxD' : x ∈ D')
    (hcard : Nat.card D' = p ^ 2) : Nat.card (M.img D') = p := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hD'c : D' ⊓ Subgroup.centralizer (S : Set Ω) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_cent hcfg.cent hcfg.mem hD'B hxD'
  let ρ : ↥D' →* ↥Ghat := M.β.comp (Subgroup.inclusion hD'B)
  have hρker : ρ.ker = (D' ⊓ Subgroup.centralizer (S : Set Ω)).subgroupOf D' := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hb
      have h1 : Subgroup.inclusion hD'B b ∈ M.β.ker := hb
      rw [M.ker_β hcfg, Subgroup.mem_subgroupOf] at h1
      exact ⟨b.2, (hcfg.cent b (hD'B b.2)).2 h1⟩
    · rintro ⟨-, hbC⟩
      have h1 : (b : Ω) ∈ Subgroup.zpowers x := (hcfg.cent b (hD'B b.2)).1 hbC
      have h2 : Subgroup.inclusion hD'B b ∈ (Subgroup.zpowers x).subgroupOf B := by
        rw [Subgroup.mem_subgroupOf]
        exact h1
      have h3 : Subgroup.inclusion hD'B b ∈ M.β.ker := by
        rw [M.ker_β hcfg]
        exact h2
      exact h3
  have hker_card : Nat.card ↥ρ.ker = p := by
    rw [hρker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : D' ⊓ Subgroup.centralizer (S : Set Ω) ≤ D')).toEquiv,
      hD'c, Nat.card_zpowers,
      orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one]
  have hrange_card : Nat.card ↥ρ.range = Nat.card (M.img D') := by
    have hr : ρ.range = (D'.subgroupOf B).map M.β := by
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hD'B b,
          Subgroup.mem_subgroupOf.2 b.2, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨(b : Ω), Subgroup.mem_subgroupOf.1 hb⟩, rfl⟩
    rw [hr, S172DModel.img]
    exact (Subgroup.card_map_of_injective Ghat.subtype_injective).symm
  have h := Subgroup.card_ker_mul_card_range ρ
  rw [hker_card, hrange_card, hcard] at h
  exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h, pow_two])

private lemma csIn_le_comap_centralizer [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {d : Γ} {b : ↥B} (hbD : (b : Ω) ∈ D)
    (hbd : ((M.β b : ↥Ghat) : Γ) = d) :
    S172X.csIn S D ≤
      (G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)).comap (G₀.subtype.comp M.π) := by
  have hN : B ≤ Subgroup.normalizer (S : Set Ω) :=
    le_normalizer_of_splitInnerDiagMarking16 hcfg.split
  intro a ha
  rw [Subgroup.mem_comap]
  refine ⟨(M.π a).2, ?_⟩
  change ((M.π a : ↥G₀) : Γ) ∈ Subgroup.centralizer ({d} : Set Γ)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  have hmem : (b : Ω) * (a : Ω) * (b : Ω)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hN b.2) (a : Ω)).mp a.2
  have hfix : (b : Ω) * (a : Ω) * (b : Ω)⁻¹ = (a : Ω) := by
    have h := S172X.mem_csIn.1 ha (b : Ω) hbD
    calc (b : Ω) * (a : Ω) * (b : Ω)⁻¹ = ((a : Ω) * (b : Ω)) * (b : Ω)⁻¹ := by rw [h]
      _ = (a : Ω) := by group
  have hconj := M.conj b ⟨(b : Ω) * (a : Ω) * (b : Ω)⁻¹, hmem⟩ a (by
    show (a : Ω) = (b : Ω)⁻¹ * ((b : Ω) * (a : Ω) * (b : Ω)⁻¹) * (b : Ω)
    group)
  have hsa : (⟨(b : Ω) * (a : Ω) * (b : Ω)⁻¹, hmem⟩ : ↥S) = a := Subtype.ext hfix
  have hconj' : ((M.π a : ↥G₀) : Γ) =
      ((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π a : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) := by
    simpa only [hsa] using hconj
  rw [← hbd]
  calc ((M.β b : ↥Ghat) : Γ) * ((M.π a : ↥G₀) : Γ)
      = ((M.β b : ↥Ghat) : Γ) *
          (((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π a : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ)) :=
        congrArg (fun x => ((M.β b : ↥Ghat) : Γ) * x) hconj'
    _ = ((M.π a : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) := by group

private lemma pi_conj_eq_of_mem_centralizer [Finite Ω] {p : ℕ} {N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {d : Γ} (hd : M.img D = Subgroup.zpowers d)
    {b : Ω} (hbD : b ∈ D) {a : ↥S}
    (ha : ((M.π a : ↥G₀) : Γ) ∈ Subgroup.centralizer ({d} : Set Γ))
    (hmem : b * (a : Ω) * b⁻¹ ∈ S) :
    M.π (⟨b * (a : Ω) * b⁻¹, hmem⟩ : ↥S) = M.π a := by
  obtain ⟨hDB, -, -, -, -, -, -⟩ := hcfg.std
  have hN : B ≤ Subgroup.normalizer (S : Set Ω) :=
    le_normalizer_of_splitInnerDiagMarking16 hcfg.split
  have hbB : b ∈ B := hDB hbD
  have hbimg : ((M.β ⟨b, hbB⟩ : ↥Ghat) : Γ) ∈ Subgroup.zpowers d := by
    rw [← hd]
    exact (M.mem_img).2 ⟨⟨b, hbB⟩, hbD, rfl⟩
  have hcentZ : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer ({d} : Set Γ) := S172X.centralizer_zpowers_eq d
  have haZ : ((M.π a : ↥G₀) : Γ) ∈
      Subgroup.centralizer ((Subgroup.zpowers d : Subgroup Γ) : Set Γ) := by
    rwa [hcentZ]
  have hβa : ((M.β ⟨b, hbB⟩ : ↥Ghat) : Γ) * ((M.π a : ↥G₀) : Γ) =
      ((M.π a : ↥G₀) : Γ) * ((M.β ⟨b, hbB⟩ : ↥Ghat) : Γ) :=
    Subgroup.mem_centralizer_iff.1 haZ _ hbimg
  apply Subtype.ext
  have hconj := M.conj ⟨b, hbB⟩ ⟨b * (a : Ω) * b⁻¹, hmem⟩ a (by
    show (a : Ω) = (b : Ω)⁻¹ * (b * (a : Ω) * b⁻¹) * (b : Ω)
    group)
  have h1 : ((M.β ⟨b, hbB⟩ : ↥Ghat) : Γ) * ((M.π a : ↥G₀) : Γ) =
      ((M.π (⟨b * (a : Ω) * b⁻¹, hmem⟩ : ↥S) : ↥G₀) : Γ) *
        ((M.β ⟨b, hbB⟩ : ↥Ghat) : Γ) := by
    rw [hconj]
    group
  exact mul_right_cancel (h1.symm.trans hβa)

private lemma exists_central_factor_of_pi_conj_eq {b : Ω} {a : ↥S}
    (hmem : b * (a : Ω) * b⁻¹ ∈ S)
    (hπ : M.π (⟨b * (a : Ω) * b⁻¹, hmem⟩ : ↥S) = M.π a) :
    ∃ z ∈ Subgroup.center ↥S, (⟨b * (a : Ω) * b⁻¹, hmem⟩ : ↥S) = z * a := by
  have hza : (⟨b * (a : Ω) * b⁻¹, hmem⟩ : ↥S) * a⁻¹ ∈ Subgroup.center ↥S := by
    rw [← M.ker_π, MonoidHom.mem_ker, map_mul, map_inv, hπ]
    simp
  exact ⟨_, hza, by group⟩

private lemma commutator_eq_of_central_factors {a c z w : ↥S}
    (hz : z ∈ Subgroup.center ↥S) (hw : w ∈ Subgroup.center ↥S) {u v : ↥S}
    (hu : u = z * a) (hv : v = w * c) : ⁅u, v⁆ = ⁅a, c⁆ := by
  rw [hu, hv]
  calc ⁅z * a, w * c⁆ = ⁅a * z, c * w⁆ := by
        rw [(Subgroup.mem_center_iff.1 hz a).symm,
          (Subgroup.mem_center_iff.1 hw c).symm]
    _ = ⁅a, c⁆ := by
        rw [CFSG.LocalAnalysis.GLTheoremA.I142N.comm_mul_central_left hz,
          CFSG.LocalAnalysis.GLTheoremA.I142N.comm_mul_central_right hw]

private lemma conj_commutator_eq {b : Ω} {a c u v : ↥S}
    (hu : (u : Ω) = b * (a : Ω) * b⁻¹) (hv : (v : Ω) = b * (c : Ω) * b⁻¹) :
    b * ((⁅a, c⁆ : ↥S) : Ω) * b⁻¹ = ((⁅u, v⁆ : ↥S) : Ω) := by
  have hsub : ∀ z : ↥S, S.subtype z = (z : Ω) := fun z => rfl
  rw [← hsub (⁅a, c⁆), ← hsub (⁅u, v⁆), map_commutatorElement S.subtype,
    map_commutatorElement S.subtype]
  simp only [hsub]
  rw [hu, hv]
  simp only [commutatorElement_def]
  group

private lemma commutator_mem_csIn [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {d : Γ} (hd : M.img D = Subgroup.zpowers d) {a c : ↥S}
    (ha : ((M.π a : ↥G₀) : Γ) ∈ Subgroup.centralizer ({d} : Set Γ))
    (hc : ((M.π c : ↥G₀) : Γ) ∈ Subgroup.centralizer ({d} : Set Γ)) :
    ⁅a, c⁆ ∈ S172X.csIn S D := by
  obtain ⟨hDB, -, -, -, -, -, -⟩ := hcfg.std
  have hN : B ≤ Subgroup.normalizer (S : Set Ω) :=
    le_normalizer_of_splitInnerDiagMarking16 hcfg.split
  rw [S172X.mem_csIn]
  intro b hbD
  have hbB : b ∈ B := hDB hbD
  have hmema : b * (a : Ω) * b⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hN hbB) (a : Ω)).mp a.2
  have hmemc : b * (c : Ω) * b⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hN hbB) (c : Ω)).mp c.2
  have hπa : M.π (⟨b * (a : Ω) * b⁻¹, hmema⟩ : ↥S) = M.π a :=
    pi_conj_eq_of_mem_centralizer (M := M) hcfg hd hbD ha hmema
  have hπc : M.π (⟨b * (c : Ω) * b⁻¹, hmemc⟩ : ↥S) = M.π c :=
    pi_conj_eq_of_mem_centralizer (M := M) hcfg hd hbD hc hmemc
  obtain ⟨za, hzaS, hzaeq⟩ :=
    exists_central_factor_of_pi_conj_eq (M := M) hmema hπa
  obtain ⟨zc, hzcS, hzceq⟩ :=
    exists_central_factor_of_pi_conj_eq (M := M) hmemc hπc
  have hcommS : ⁅(⟨b * (a : Ω) * b⁻¹, hmema⟩ : ↥S),
      (⟨b * (c : Ω) * b⁻¹, hmemc⟩ : ↥S)⁆ = ⁅a, c⁆ :=
    commutator_eq_of_central_factors hzaS hzcS hzaeq hzceq
  have hconj : (b : Ω) * ((⁅a, c⁆ : ↥S) : Ω) * (b : Ω)⁻¹ =
      ((⁅a, c⁆ : ↥S) : Ω) := by
    rw [conj_commutator_eq (u := ⟨b * (a : Ω) * b⁻¹, hmema⟩)
      (v := ⟨b * (c : Ω) * b⁻¹, hmemc⟩) rfl rfl, hcommS]
  calc (b : Ω) * ((⁅a, c⁆ : ↥S) : Ω)
      = (b * ((⁅a, c⁆ : ↥S) : Ω) * (b : Ω)⁻¹) * b := by group
    _ = ((⁅a, c⁆ : ↥S) : Ω) * b := by rw [hconj]

private lemma conj_mem_csIn [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {d : Γ} (hd : M.img D = Subgroup.zpowers d)
    {b0 : ↥B} (hb0D : (b0 : Ω) ∈ D) (hb0d : ((M.β b0 : ↥Ghat) : Γ) = d) {a : ↥S}
    (ha : ((M.π a : ↥G₀) : Γ) ∈ Subgroup.centralizer ({d} : Set Γ))
    {y : ↥S} (hy : y ∈ S172X.csIn S D) : a * y * a⁻¹ ∈ S172X.csIn S D := by
  have hle := csIn_le_comap_centralizer (M := M) hcfg hb0D hb0d
  have hyC : ((M.π y : ↥G₀) : Γ) ∈ Subgroup.centralizer ({d} : Set Γ) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 (hle hy))).2
  have hcomm : ⁅a, y⁆ ∈ S172X.csIn S D :=
    commutator_mem_csIn (M := M) hcfg hd ha hyC
  have he : a * y * a⁻¹ = ⁅a, y⁆ * y := by
    rw [commutatorElement_def]
    group
  rw [he]
  exact Subgroup.mul_mem _ hcomm hy

private lemma csIn_layer_component_of_img_eq_zpowers [Finite Ω] {p : ℕ}
    {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x) {d : Γ}
    (hd : M.img D = Subgroup.zpowers d) (f : ↥S →* Γ) (C : Subgroup ↥S)
    (hf : f = G₀.subtype.comp M.π)
    (hC : C = (G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)).comap f) :
    GLALayer (S172X.csIn S D) = GLALayer C ∧ IsComponentOf (GLALayer C) C := by
  subst f
  subst C
  obtain ⟨-, -, -, -, hKeq, hKc, -⟩ := hcfg.std
  obtain ⟨b0, hb0D, hb0d⟩ := (M.mem_img).1 (hd.symm ▸ Subgroup.mem_zpowers d)
  have hYX : S172X.csIn S D ≤
      (G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)).comap (G₀.subtype.comp M.π) :=
    csIn_le_comap_centralizer (M := M) hcfg hb0D hb0d
  have hnormal : ((S172X.csIn S D).subgroupOf
      ((G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)).comap (G₀.subtype.comp M.π))).Normal := by
    refine ⟨fun x hx a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have haH : (G₀.subtype.comp M.π) (a : ↥S) ∈
        G₀ ⊓ Subgroup.centralizer ({d} : Set Γ) := Subgroup.mem_comap.1 a.2
    exact conj_mem_csIn (M := M) hcfg hd hb0D hb0d (Subgroup.mem_inf.1 haH).2 hx
  have hcomm_le : ⁅(G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)).comap (G₀.subtype.comp M.π),
      (G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)).comap (G₀.subtype.comp M.π)⁆ ≤
      S172X.csIn S D := by
    rw [Subgroup.commutator_le]
    intro a ha c hc
    have haC : (G₀.subtype.comp M.π) (a : ↥S) ∈
        Subgroup.centralizer ({d} : Set Γ) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 ha)).2
    have hcC : (G₀.subtype.comp M.π) (c : ↥S) ∈
        Subgroup.centralizer ({d} : Set Γ) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hc)).2
    exact commutator_mem_csIn (M := M) hcfg hd haC hcC
  have hY : IsComponentOf (GLALayer (S172X.csIn S D)) (S172X.csIn S D) := by
    refine (S172X.isComponentOf_glaLayer_csIn_iff S D).2 ?_
    rw [← hKeq]
    exact hKc
  exact ⟨S172X.glaLayer_eq_of_commutator_le hYX hnormal hcomm_le,
    (S172X.isComponentOf_glaLayer_iff_of_commutator_le hYX hnormal hcomm_le).1 hY⟩

private lemma piImg_eq_stdLayerD_of_img_eq_zpowers [Finite Ω] {p : ℕ} {N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {d : Γ}
    (hd : M.img D = Subgroup.zpowers d) :
    M.piImg K = stdLayerD G₀ d ∧
      IsComponentOf (stdLayerD G₀ d) (G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)) := by
  obtain ⟨-, -, -, -, hKeq, -, -⟩ := hcfg.std
  have hKS : K ≤ S := CFSG.LocalAnalysis.GLTheoremA.T173X.K_le_of_cfg173 hcfg
  let f : ↥S →* Γ := G₀.subtype.comp M.π
  let H : Subgroup Γ := G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)
  let C : Subgroup ↥S := H.comap f
  obtain ⟨hlayer_cs, hcomp_cs⟩ :=
    csIn_layer_component_of_img_eq_zpowers (M := M) hcfg hd f C rfl rfl
  have hfker : f.ker = Subgroup.center ↥S := by
    rw [show f.ker = M.π.ker from
      MonoidHom.ker_comp_of_injective M.π G₀.subtype G₀.subtype_injective]
    exact M.ker_π
  have hfcentral : ∀ a : ↥S, f a = 1 → a ∈ Subgroup.center ↥S := by
    intro a ha
    rw [← MonoidHom.mem_ker, hfker] at ha
    exact ha
  have hfrange : f.range = G₀ := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact (M.π s).2
    · intro hy
      obtain ⟨s, hs⟩ := M.surj ⟨y, hy⟩
      exact ⟨s, congrArg Subtype.val hs⟩
  have hCmap : C.map f = H :=
    Subgroup.map_comap_eq_self (by rw [hfrange]; exact inf_le_left)
  have hHlayer : GLALayer H = (GLALayer C).map f := by
    rw [← hCmap]
    exact S172X.glaLayer_map_eq f hfcentral C
  have hHcomp : IsComponentOf (GLALayer H) H := by
    have h := (S172X.isComponentOf_glaLayer_map_iff f hfcentral C).2 hcomp_cs
    rwa [hCmap] at h
  have hKsub : K.subgroupOf S = GLALayer (S172X.csIn S D) := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKS, hKeq, S172X.glaLayer_csIn_map]
  refine ⟨?_, ?_⟩
  · calc M.piImg K = (K.subgroupOf S).map f := by
          rw [S172DModel.piImg, Subgroup.map_map]
      _ = (GLALayer (S172X.csIn S D)).map f := by rw [hKsub]
      _ = (GLALayer C).map f := by rw [hlayer_cs]
      _ = GLALayer H := hHlayer.symm
      _ = stdLayerD G₀ d := rfl
  · simpa only [stdLayerD, H] using hHcomp

private lemma coe_β_mem_centralizer_piImg [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {b : ↥B}
    (hb : (b : Ω) ∈ Subgroup.centralizer (K : Set Ω)) :
    ((M.β b : ↥Ghat) : Γ) ∈ Subgroup.centralizer (M.piImg K : Set Γ) := by
  have hKS : K ≤ S := CFSG.LocalAnalysis.GLTheoremA.T173X.K_le_of_cfg173 hcfg
  have hN : B ≤ Subgroup.normalizer (S : Set Ω) :=
    le_normalizer_of_splitInnerDiagMarking16 hcfg.split
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [S172DModel.piImg] at hy
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
  obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.1 hz
  have hkK : (k : Ω) ∈ K := Subgroup.mem_subgroupOf.1 hk
  have hyk : y = ((M.π k : ↥G₀) : Γ) := by
    rw [← hzy, ← hkz]
    rfl
  rw [hyk]
  have hmem : (b : Ω) * (k : Ω) * (b : Ω)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hN b.2) (k : Ω)).mp (hKS hkK)
  have hbcomm : (k : Ω) * (b : Ω) = (b : Ω) * (k : Ω) :=
    Subgroup.mem_centralizer_iff.1 hb (k : Ω) hkK
  have hfix : (b : Ω) * (k : Ω) * (b : Ω)⁻¹ = (k : Ω) := by
    calc (b : Ω) * (k : Ω) * (b : Ω)⁻¹ = ((k : Ω) * (b : Ω)) * (b : Ω)⁻¹ := by rw [hbcomm]
      _ = (k : Ω) := by group
  have hconj := M.conj b ⟨(b : Ω) * (k : Ω) * (b : Ω)⁻¹, hmem⟩ k (by
    show (k : Ω) = (b : Ω)⁻¹ * ((b : Ω) * (k : Ω) * (b : Ω)⁻¹) * (b : Ω)
    group)
  have hπs : M.π (⟨(b : Ω) * (k : Ω) * (b : Ω)⁻¹, hmem⟩ : ↥S) = M.π k :=
    congrArg M.π (Subtype.ext hfix)
  have hfix' : ((M.π k : ↥G₀) : Γ) =
      ((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π k : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) := by
    simpa only [hπs] using hconj
  have hcomm' : ((M.β b : ↥Ghat) : Γ) * ((M.π k : ↥G₀) : Γ) =
      ((M.π k : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) := by
    calc ((M.β b : ↥Ghat) : Γ) * ((M.π k : ↥G₀) : Γ)
        = ((M.β b : ↥Ghat) : Γ) *
            (((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π k : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ)) :=
          congrArg (fun x => ((M.β b : ↥Ghat) : Γ) * x) hfix'
      _ = ((M.π k : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) := by group
  exact hcomm'.symm

private lemma mem_centralizer_of_centralizes_piImg [Finite Ω] {p : ℕ} {N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {b : ↥B}
    (hb : ((M.β b : ↥Ghat) : Γ) ∈ Subgroup.centralizer (M.piImg K : Set Γ)) :
    (b : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
  obtain ⟨-, -, -, -, -, hKc, -⟩ := hcfg.std
  have hKS : K ≤ S := CFSG.LocalAnalysis.GLTheoremA.T173X.K_le_of_cfg173 hcfg
  have hN : B ≤ Subgroup.normalizer (S : Set Ω) :=
    le_normalizer_of_splitInnerDiagMarking16 hcfg.split
  haveI : Group.IsPerfect ↥K := ⟨hKc.2.2.1⟩
  let φ : ↥K →* ↥S :=
    { toFun := fun k => ⟨(b : Ω)⁻¹ * (k : Ω) * (b : Ω), by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN b.2)) (k : Ω)).mp
          (hKS k.2)⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp only [Subgroup.coe_mul]; group }
  let ψ : ↥K →* ↥S := Subgroup.inclusion hKS
  have hφψ : ∀ k : ↥K, M.π (φ k) = M.π (ψ k) := by
    intro k
    apply Subtype.ext
    have hcomm : ((M.π (ψ k) : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) =
        ((M.β b : ↥Ghat) : Γ) * ((M.π (ψ k) : ↥G₀) : Γ) :=
      Subgroup.mem_centralizer_iff.1 hb _ (pi_mem_piImg M hKS k.2)
    have hc := M.conj b (ψ k) (φ k) rfl
    rw [hc]
    calc ((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π (ψ k) : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ)
        = ((M.β b : ↥Ghat) : Γ)⁻¹ *
            (((M.π (ψ k) : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ)) := by group
      _ = ((M.β b : ↥Ghat) : Γ)⁻¹ *
            (((M.β b : ↥Ghat) : Γ) * ((M.π (ψ k) : ↥G₀) : Γ)) := by rw [hcomm]
      _ = ((M.π (ψ k) : ↥G₀) : Γ) := by group
  have hrigid : φ = ψ :=
    CFSG.SeitzReduction.LinearPilot.eq_of_comp_eq_of_ker_le_center (p := M.π)
      (by rw [M.ker_π]) (φ := φ) (ψ := ψ) hφψ
  rw [Subgroup.mem_centralizer_iff]
  intro k hkK
  have h := congrArg (fun f : ↥K →* ↥S => ((f ⟨k, hkK⟩ : ↥S) : Ω)) hrigid
  have h' : (b : Ω)⁻¹ * (k : Ω) * (b : Ω) = (k : Ω) := h
  calc (k : Ω) * (b : Ω) = (b : Ω) * ((b : Ω)⁻¹ * (k : Ω) * (b : Ω)) := by group
    _ = (b : Ω) * (k : Ω) := by rw [h']

theorem exists_stdD [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) :
    ∃ d ∈ M.barB, d ≠ 1 ∧ d ^ p = 1 ∧ M.img D = Subgroup.zpowers d ∧
      M.piImg K = stdLayerD G₀ d ∧
      IsComponentOf (stdLayerD G₀ d) (G₀ ⊓ Subgroup.centralizer ({d} : Set Γ)) ∧
      M.barB ⊓ Subgroup.centralizer (M.piImg K : Set Γ) = Subgroup.zpowers d := by
  obtain ⟨hDB, -, hDc, hxmem, -, -, hDK⟩ := hcfg.std
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardD : Nat.card (M.img D) = p :=
    card_img_eq_prime (M := M) hcfg hDB hxmem hDc
  obtain ⟨d, hd⟩ := S172X.exists_zpowers_eq_of_card_eq_prime (p := p) hcardD
  have hd' : M.img D = Subgroup.zpowers d := hd.symm
  have hord : orderOf d = p := by rw [← Nat.card_zpowers, ← hd', hcardD]
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.ne_one hord.symm
  have hdp : d ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one d
  obtain ⟨b0, hb0D, hb0d⟩ := (M.mem_img).1 (hd'.symm ▸ Subgroup.mem_zpowers d)
  have hb0cent : (b0 : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
    have h := hb0D
    rw [hDK] at h
    exact h.2
  obtain ⟨hpi, hcomp⟩ := piImg_eq_stdLayerD_of_img_eq_zpowers (M := M) hcfg hd'
  refine ⟨d, (M.mem_barB).2 ⟨b0, hb0d⟩, hd1, hdp, hd', hpi, hcomp, ?_⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨hyB, hyC⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨b, hby⟩ := (M.mem_barB).1 hyB
    have hyC' : ((M.β b : ↥Ghat) : Γ) ∈ Subgroup.centralizer (M.piImg K : Set Γ) := by
      rwa [hby]
    have hbcent : (b : Ω) ∈ Subgroup.centralizer (K : Set Ω) :=
      mem_centralizer_of_centralizes_piImg (M := M) hcfg hyC'
    have hbD : (b : Ω) ∈ D := by
      rw [hDK]
      exact ⟨b.2, hbcent⟩
    have hmem : ((M.β b : ↥Ghat) : Γ) ∈ Subgroup.zpowers d := by
      rw [← hd']
      exact (M.mem_img).2 ⟨b, hbD, rfl⟩
    rwa [← hby]
  · refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact img_le_barB (M := M) (hd'.symm ▸ Subgroup.mem_zpowers d)
    · rw [← hb0d]
      exact coe_β_mem_centralizer_piImg (M := M) hcfg hb0cent
