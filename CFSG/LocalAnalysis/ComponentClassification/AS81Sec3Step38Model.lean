module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Move
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Tau
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2NQ0

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec3

section General

variable {G : Type} [Group G]

theorem mem_normalizer_sec3B_of_inv {A₁ : Subgroup G} {x τ : G}
    (hA : τ ∈ normalizer (A₁ : Set G)) (hx : τ * x * τ⁻¹ = x⁻¹) :
    τ ∈ normalizer (sec3B A₁ x : Set G) := by
  have key : ∀ {σ : G}, σ ∈ normalizer (A₁ : Set G) → σ * x * σ⁻¹ = x⁻¹ →
      ∀ b ∈ sec3B A₁ x, σ * b * σ⁻¹ ∈ sec3B A₁ x := by
    intro σ hσA hσx
    have hσx' : σ⁻¹ * x * σ = x⁻¹ := by
      calc σ⁻¹ * x * σ = (σ⁻¹ * x⁻¹ * σ)⁻¹ := by group
        _ = (σ⁻¹ * (σ * x * σ⁻¹) * σ)⁻¹ := by rw [hσx]
        _ = x⁻¹ := by group
    have hC : ∀ c ∈ centralizer ({x} : Set G), σ * c * σ⁻¹ ∈ centralizer ({x} : Set G) := by
      intro c hc
      rw [mem_centralizer_singleton_iff] at hc ⊢
      calc σ * c * σ⁻¹ * x = σ * c * (σ⁻¹ * x * σ) * σ⁻¹ := by group
        _ = σ * (c * x⁻¹) * σ⁻¹ := by rw [hσx']; group
        _ = σ * (x⁻¹ * c) * σ⁻¹ := by
          rw [show c * x⁻¹ = x⁻¹ * c by
            calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
              _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hc]
              _ = x⁻¹ * c := by group]
        _ = (σ * x⁻¹ * σ⁻¹) * (σ * c * σ⁻¹) := by group
        _ = x * (σ * c * σ⁻¹) := by
          rw [show σ * x⁻¹ * σ⁻¹ = x by
            rw [show σ * x⁻¹ * σ⁻¹ = (σ * x * σ⁻¹)⁻¹ by group, hσx, inv_inv]]
    let φ : ↥(centralizer ({x} : Set G)) →* ↥(centralizer ({x} : Set G)) :=
      { toFun := fun c => ⟨σ * c * σ⁻¹, hC c c.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hle : normalClosure ((A₁.subgroupOf (centralizer ({x} : Set G)) :
        Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G))) ≤
        (normalClosure ((A₁.subgroupOf (centralizer ({x} : Set G)) :
          Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G)))).comap φ := by
      have : ((normalClosure ((A₁.subgroupOf (centralizer ({x} : Set G)) :
          Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G)))).comap
            φ).Normal := Subgroup.Normal.comap normalClosure_normal φ
      refine normalClosure_le_normal fun c hc => ?_
      refine subset_normalClosure ?_
      have hcA : (c : G) ∈ A₁ := mem_subgroupOf.mp hc
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hσA _).mp hcA)
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨φ b, hle hb, rfl⟩
  refine G2.mem_normalizer_of_conj (key hA hx) fun b hb => ?_
  have hx' : τ⁻¹ * x * τ⁻¹⁻¹ = x⁻¹ := by
    rw [inv_inv]
    calc τ⁻¹ * x * τ = (τ⁻¹ * x⁻¹ * τ)⁻¹ := by group
      _ = (τ⁻¹ * (τ * x * τ⁻¹) * τ)⁻¹ := by rw [hx]
      _ = x⁻¹ := by group
  have h := key (inv_mem hA) hx' b hb
  rwa [inv_inv] at h

end General

theorem eq_zero_or_one_or_of_card_four {K : Type} [Field K] [CharP K 2] [Finite K]
    (hK : Nat.card K = 4) {t : Kˣ} (ht : t ≠ 1) (c : K) :
    c = 0 ∨ c = 1 ∨ c = t ∨ c = ((t⁻¹ : Kˣ) : K) := by
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  by_cases hc1 : c = 1
  · exact Or.inr (Or.inl hc1)
  right; right
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have ht1 : (t : K) ≠ 1 := fun h => ht (Units.ext h)
  have hc2 := G2.sq_add_self_add_one_of_ne hK hc0 hc1
  have ht2 := G2.sq_add_self_add_one_of_ne hK ht0 ht1
  have e : (c - t) * (c - (t + 1)) = 0 := by
    linear_combination (norm := char2_ring) hc2 - ht2
  rcases mul_eq_zero.mp e with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    rw [sub_eq_zero.mp h]
    have h1 : (t : K) * (t + 1) = 1 := by linear_combination (norm := char2_ring) ht2
    rw [Units.val_inv_eq_inv_val, eq_inv_of_mul_eq_one_right h1]

@[expose] noncomputable def nrElt
    {K : Type} [Field K] : ↥(adjointGroup .G2 K) :=
  ⟨weylElt .G2 K g2ir 1, weylElt_mem_adjointGroup g2ir 1⟩

theorem coe_nrElt {K : Type} [Field K] :
    ((nrElt : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = weylElt .G2 K g2ir 1 := rfl

theorem nrElt_mul_self {K : Type}
    [Field K] [CharP K 2] : (nrElt : ↥(adjointGroup .G2 K)) * nrElt = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_nrElt, OneMemClass.coe_one]
  exact weylElt_mul_self g2ir

theorem nrElt_inv {K : Type}
    [Field K] [CharP K 2] : (nrElt : ↥(adjointGroup .G2 K))⁻¹ = nrElt := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, coe_nrElt]
  exact weylElt_inv g2ir

theorem nrElt_conj_torus {K : Type}
    [Field K] (t : Kˣ) {h : ↥(adjointGroup .G2 K)}
    (ht : torusElt .G2 K g2ir t = (h : ModGL .G2 K)) : nrElt * h * nrElt⁻¹ = h⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_nrElt, ← ht,
    weylElt_mul_torusElt_mul_inv, eq_inv_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel,
    torusElt_one]

section VElt

variable
  {K : Type} [Field K] [CharP K 2]

theorem g2V_le_adjointGroup : G2.g2V K ≤ adjointGroup .G2 K :=
  G2.g2V_le_g2V0.trans (G2.g2V0_le_g2ShortParabolicRadical.trans
    G2.g2ShortParabolicRadical_le_adjointGroup)

@[expose] noncomputable def vElt (C D F : K) : ↥(adjointGroup .G2 K) :=
  ⟨g2N 0 0 C D 0 F, g2V_le_adjointGroup ⟨C, D, F, rfl⟩⟩

theorem coe_vElt (C D F : K) : (vElt C D F : ModGL .G2 K) = g2N 0 0 C D 0 F := rfl

theorem vElt_mul (C D F C' D' F' : K) :
    vElt C D F * vElt C' D' F' = vElt (C + C') (D + D') (F + F' + C' * D) :=
  Subtype.ext ((G2.g2N_uv_mul C D 0 F C' D' 0 F').trans
    (g2N_eq_g2N rfl rfl rfl rfl (add_zero 0) rfl))

theorem vElt_inv (C D F : K) : (vElt C D F)⁻¹ = vElt C D (F + C * D) :=
  Subtype.ext (G2.g2N_uv_inv C D 0 F)

theorem vElt_congr {C D F C' D' F' : K} (h1 : C = C') (h2 : D = D') (h3 : F = F') :
    vElt C D F = vElt C' D' F' := by
  rw [h1, h2, h3]

theorem vElt_injective {C D F C' D' F' : K} (h : vElt C D F = vElt C' D' F') :
    C = C' ∧ D = D' ∧ F = F' := by
  have h' := congrArg Subtype.val h
  rw [coe_vElt, coe_vElt] at h'
  obtain ⟨-, -, h1, h2, -, h3⟩ := g2N_injective h'
  exact ⟨h1, h2, h3⟩

theorem torus_conj_vElt (t : Kˣ) {h : ↥(adjointGroup .G2 K)}
    (ht : torusElt .G2 K g2ir t = (h : ModGL .G2 K)) (C D F : K) :
    h * vElt C D F * h⁻¹ = vElt (((t⁻¹ : Kˣ) : K) * C) ((t : K) * D) F := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_vElt, coe_vElt, ← ht,
    G2.torus_r_conj_g2N_uv, zpow_neg_one, zpow_one]
  exact g2N_eq_g2N rfl rfl rfl rfl (mul_zero _) rfl

theorem nrElt_conj_vElt (C D F : K) :
    nrElt * vElt C D F * nrElt⁻¹ = vElt D C (D * C + F) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_nrElt, coe_vElt, coe_vElt,
    weylElt_r_conj_g2N]
  exact g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)

theorem nrElt_comm_vElt (F : K) : nrElt * vElt 0 0 F = vElt 0 0 F * nrElt := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_nrElt, coe_vElt,
    show g2N (0 : K) 0 0 0 0 F = pinnedX .G2 K g2c F from (pinnedX_c_eq_g2N F).symm]
  exact (commute_weylElt_r_pinnedX_c F).eq

end VElt

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem exists_tau_sec38V
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
    (hTV : T ≤ normalizer (V : Set G)) (hTC : Nat.card ↥(T ⊓ centralizer (Q : Set G)) ≤ 2) :
    ∃ τ v₀ : G, IsTau A₁ V x z τ ∧ Sec38V T Q Zs V Q₀ x z v₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSz := hQ.dData.suz
  have hS := hSz.setting
  obtain ⟨hEA, -, -, -, -, -, -, -, hS64⟩ := frame_inf_A₁ hS
  obtain ⟨K, _, _, _, hK, f, hM, l, t₀, h₀, hl0, ht₀1, ht₀, hfh₀, -, hQm⟩ :=
    exists_sec3Q0_model hQ.dData
  have hfinj := hM.inj
  have hD₀C : g2ShortParabolicRadical K ≤ adjointGroup .G2 K :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hZ₀C : g2BCGroup K ≤ adjointGroup .G2 K :=
    G2.g2BCGroup_le_g2ShortParabolicRadical.trans hD₀C
  have hV0C : G2.g2V0 K ≤ adjointGroup .G2 K := G2.g2V0_le_g2ShortParabolicRadical.trans hD₀C
  have hVC : G2.g2V K ≤ adjointGroup .G2 K := g2V_le_adjointGroup
  have hLPC : G2.g2LongPos K ≤ adjointGroup .G2 K :=
    G2.g2LongPos_le_g2LongA2.trans g2LongA2_le_adjointGroup
  have hACC : G2.g2ACGroup K ≤ adjointGroup .G2 K := G2.g2ACGroup_le_g2LongPos.trans hLPC
  have hQ0C : G2.g2Q0 K l ≤ adjointGroup .G2 K := (G2.g2Q0_le_g2V l).trans hVC
  have hV₀ : V₀ = ((G2.g2V0 K).subgroupOf (adjointGroup .G2 K)).map f :=
    SetLike.coe_injective (hQ.V₀_eq.trans hQm.V₀_eq.symm)
  have hV : V = ((G2.g2V K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hQ.V_eq, hQm.V_eq, hV₀]
  have hQ₀ : Q₀ = ((G2.g2Q0 K l).subgroupOf (adjointGroup .G2 K)).map f :=
    (hQ.unique _ (hV ▸ hQm.Q₀_le) hQm.x_Q₀ hQm.Q₀_iso hQm.center_Q₀).symm
  have hfinj' : ∀ {C D F' C' D' F'' : K}, f (vElt C D F') = f (vElt C' D' F'') →
      C = C' ∧ D = D' ∧ F' = F'' := fun h => vElt_injective (hfinj h)
  have hmemV : ∀ {w : G}, w ∈ V ↔ ∃ C D F' : K, f (vElt C D F') = w := by
    intro w
    rw [hV]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨C, D, F', hc'⟩ := mem_subgroupOf.mp hc
      exact ⟨C, D, F', congrArg f (Subtype.ext ((coe_vElt C D F').trans hc'.symm))⟩
    · rintro ⟨C, D, F', rfl⟩
      exact ⟨vElt C D F', mem_subgroupOf.mpr ⟨C, D, F', coe_vElt C D F'⟩, rfl⟩
  have hx_vE : ∀ C D F' : K, x * f (vElt C D F') * x⁻¹ =
      f (vElt (((t₀⁻¹ : Kˣ) : K) * C) ((t₀ : K) * D) F') := by
    intro C D F'
    rw [← hfh₀, ← map_inv, ← map_mul, ← map_mul, torus_conj_vElt t₀ ht₀]
  have hxinv_vE : ∀ D : K, x⁻¹ * f (vElt 0 D 0) * x = f (vElt 0 (((t₀⁻¹ : Kˣ) : K) * D) 0) := by
    intro D
    have h := hx_vE 0 (((t₀⁻¹ : Kˣ) : K) * D) 0
    rw [mul_zero, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    rw [← h]
    group
  let Xc : Subgroup (ModGL .G2 K) :=
    { carrier := {w | ∃ F' : K, w = g2N 0 0 0 0 0 F'}
      mul_mem' := by
        rintro _ _ ⟨F', rfl⟩ ⟨F'', rfl⟩
        exact ⟨F' + F'', (G2.g2N_uv_mul 0 0 0 F' 0 0 0 F'').trans
          (g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring))⟩
      one_mem' := ⟨0, g2N_zero.symm⟩
      inv_mem' := by
        rintro _ ⟨F', rfl⟩
        exact ⟨F', (G2.g2N_uv_inv 0 0 0 F').trans
          (g2N_eq_g2N rfl rfl rfl rfl rfl (by ring))⟩ }
  have hXcC : Xc ≤ adjointGroup .G2 K := by
    rintro _ ⟨F', rfl⟩
    exact hVC ⟨0, 0, F', rfl⟩
  have hcardXc : Nat.card Xc = 4 := by
    rw [← hK]
    refine (Nat.card_congr (Equiv.ofBijective (fun F' : K => (⟨g2N 0 0 0 0 0 F', F', rfl⟩ : Xc))
      ⟨fun F' F'' h => ?_, fun w => ?_⟩)).symm
    · obtain ⟨-, -, -, -, -, h1⟩ := g2N_injective (Subtype.mk.inj h)
      exact h1
    · obtain ⟨F', hF⟩ := w.2
      exact ⟨F', Subtype.ext hF.symm⟩
  have hZc : ∀ F' : K, f (vElt 0 0 F') ∈ (Xc.subgroupOf (adjointGroup .G2 K)).map f := fun F' =>
    ⟨vElt 0 0 F', mem_subgroupOf.mpr ⟨F', coe_vElt 0 0 F'⟩, rfl⟩
  have hUL : ((G2.g2LongPos K).subgroupOf (adjointGroup .G2 K)).map f = (E ⊔ F) ⊓ A₁ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · have h1 : G2.g2LongPos K ≤ g2BCGroup K ⊔ G2.g2ACGroup K := by
        rintro _ ⟨B, E', F', rfl⟩
        rw [show g2N 0 B 0 0 E' F' = g2N 0 0 0 0 E' 0 * g2N 0 B 0 0 0 (F' + B * E') by
          rw [g2N_zero_mul_g2N_zero]
          exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by char2_ring)]
        exact mul_mem_sup ⟨E', 0, rfl⟩ ⟨B, F' + B * E', rfl⟩
      refine (tr_mono h1).trans ?_
      rw [tr_sup hZ₀C hACC, hM.E_eq, hM.F_eq, hEA]
      exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)
    · rw [hS64, card_map_of_injective hfinj, Nat.card_congr (subgroupOfEquivOfLe hLPC).toEquiv,
        G2.card_g2LongPos, hK]
      norm_num
  have hZsc : ∀ s ∈ Zs, ∃ F' : K, s = f (vElt 0 0 F') := by
    intro s hs
    have hs' : s ∈ A₁ ⊓ ((E ⊔ F) ⊓ centralizer ((E ⊔ F : Subgroup G) : Set G)) := by
      rw [hSz.Zs_eq] at hs
      exact hs
    obtain ⟨hsA₁, hsEF, hsc⟩ := hs'
    have hsUL : s ∈ ((G2.g2LongPos K).subgroupOf (adjointGroup .G2 K)).map f := by
      rw [hUL]
      exact ⟨hsEF, hsA₁⟩
    obtain ⟨b, hb, hfb⟩ := hsUL
    have hXa1 : g2N 0 1 0 0 0 0 ∈ adjointGroup .G2 K := hACC ⟨1, 0, rfl⟩
    have hXb1 : g2N 0 0 0 0 1 0 ∈ adjointGroup .G2 K := hZ₀C ⟨1, 0, rfl⟩
    have hfa : f ⟨_, hXa1⟩ ∈ E ⊔ F := by
      have h1 : f ⟨_, hXa1⟩ ∈ F ⊓ A₁ := by
        rw [← hM.F_eq]
        exact ⟨⟨_, hXa1⟩, mem_subgroupOf.mpr ⟨1, 0, rfl⟩, rfl⟩
      exact mem_sup_right h1.1
    have hfb' : f ⟨_, hXb1⟩ ∈ E ⊔ F := by
      have h1 : f ⟨_, hXb1⟩ ∈ E ⊓ A := by
        rw [← hM.E_eq]
        exact ⟨⟨_, hXb1⟩, mem_subgroupOf.mpr ⟨1, 0, rfl⟩, rfl⟩
      exact mem_sup_left h1.1
    have hcomm : ∀ {w : ↥(adjointGroup .G2 K)}, f w ∈ E ⊔ F →
        (b : ModGL .G2 K) * w = w * b := by
      intro w hw
      have h1 := mem_centralizer_iff.mp hsc _ hw
      rw [← hfb, ← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hfinj h1).symm
    obtain ⟨F', hF'⟩ := G2.eq_g2N_c_of_mem_g2LongPos (mem_subgroupOf.mp hb)
      (hcomm (w := ⟨_, hXa1⟩) hfa) (hcomm (w := ⟨_, hXb1⟩) hfb')
    exact ⟨F', by rw [← hfb]; exact congrArg f (Subtype.ext (hF'.trans (coe_vElt 0 0 F').symm))⟩
  have hZsXc : Zs = (Xc.subgroupOf (adjointGroup .G2 K)).map f := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro s hs
      obtain ⟨F', rfl⟩ := hZsc s hs
      exact hZc F'
    · rw [hSz.Zs_card, card_map_of_injective hfinj,
        Nat.card_congr (subgroupOfEquivOfLe hXcC).toEquiv, hcardXc]
  have hZsF : ∀ F' : K, f (vElt 0 0 F') ∈ Zs := fun F' => hZsXc ▸ hZc F'
  have hZs_eq : Zs = V ⊓ centralizer ({x} : Set G) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨F', rfl⟩ := hZsc s hs
      refine mem_inf.mpr ⟨hmemV.mpr ⟨0, 0, F', rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
      have h := hx_vE 0 0 F'
      rw [mul_zero, mul_zero] at h
      calc f (vElt 0 0 F') * x = x * f (vElt 0 0 F') * x⁻¹ * x := by rw [h]
        _ = x * f (vElt 0 0 F') := by group
    · intro w hw
      obtain ⟨hwV, hwx⟩ := mem_inf.mp hw
      obtain ⟨C, D, F', rfl⟩ := hmemV.mp hwV
      have h1 : x * f (vElt C D F') * x⁻¹ = f (vElt C D F') := by
        rw [← mem_centralizer_singleton_iff.mp hwx, mul_inv_cancel_right]
      rw [hx_vE] at h1
      obtain ⟨hC, hD, -⟩ := hfinj' h1
      have hC0 : C = 0 := by
        by_contra hC0
        apply ht₀1
        have h2 : ((t₀⁻¹ : Kˣ) : K) = 1 :=
          mul_right_cancel₀ hC0 (hC.trans (one_mul C).symm)
        exact inv_eq_one.mp (Units.ext h2)
      have hD0 : D = 0 := by
        by_contra hD0
        apply ht₀1
        exact Units.ext (mul_right_cancel₀ hD0 (hD.trans (one_mul D).symm))
      rw [hC0, hD0]
      exact hZsF F'
  obtain ⟨lz, hlz⟩ := hZsc z hSz.z_mem
  let S' : Subgroup (ModGL .G2 K) :=
    { carrier := {w | ∃ C E' F' : K, w = g2N 0 0 C (l * C ^ 2) E' F'}
      mul_mem' := by
        rintro _ _ ⟨C, E', F', rfl⟩ ⟨C', E'', F'', rfl⟩
        exact ⟨C + C', E' + E'', F' + F'' + C' * (l * C ^ 2),
          (G2.g2N_uv_mul _ _ _ _ _ _ _ _).trans
            (g2N_eq_g2N rfl rfl rfl (by char2_ring) rfl rfl)⟩
      one_mem' := ⟨0, 0, 0, by rw [show l * (0 : K) ^ 2 = 0 by ring, g2N_zero]⟩
      inv_mem' := by
        rintro _ ⟨C, E', F', rfl⟩
        exact ⟨C, E', F' + C * (l * C ^ 2), G2.g2N_uv_inv _ _ _ _⟩ }
  have hQ₀S' : Q₀ ⊔ Zs ≤ (S'.subgroupOf (adjointGroup .G2 K)).map f := by
    refine sup_le ?_ ?_
    · rw [hQ₀]
      refine tr_mono ?_
      rintro _ ⟨C, F', _, _, rfl⟩
      exact ⟨C, 0, F', rfl⟩
    · rw [hZsXc]
      refine tr_mono ?_
      rintro _ ⟨F', rfl⟩
      exact ⟨0, 0, F', g2N_eq_g2N rfl rfl rfl (by ring) rfl rfl⟩
  have hnotS : ∀ D : K, D ≠ 0 → f (vElt 0 D 0) ∉ Q₀ ⊔ Zs := by
    intro D hD hmem
    have h1 := hQ₀S' hmem
    rw [mem_map_iff_mem hfinj, mem_subgroupOf] at h1
    obtain ⟨C, E', F', hw⟩ := h1
    rw [coe_vElt] at hw
    obtain ⟨-, -, h2, h3, -⟩ := g2N_injective hw
    rw [← h2] at h3
    exact hD (h3.trans (by ring))
  have hinS : ∀ C F' : K, f (vElt C (l * C ^ 2) F') ∈ Q₀ ⊔ Zs := by
    intro C F'
    obtain ⟨ω, hω0, hω1⟩ := G2.exists_ne_zero_ne_one hK
    obtain ⟨r, hr⟩ := G2.exists_root_g2Q0 (l := l) hK (G2.sq_add_self_add_one_of_ne hK hω0 hω1) C
    have hq : g2N 0 0 C (l * C ^ 2) 0 r ∈ G2.g2Q0 K l :=
      ⟨C, r, G2.pow_four_eq_self hK C, by linear_combination (norm := char2_ring) hr, rfl⟩
    have e : vElt C (l * C ^ 2) F' = vElt C (l * C ^ 2) r * vElt 0 0 (F' + r) := by
      rw [vElt_mul]
      exact vElt_congr (by ring) (by ring) (by char2_ring)
    rw [e, map_mul]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right (hZsF _))
    rw [hQ₀]
    exact ⟨vElt C (l * C ^ 2) r, mem_subgroupOf.mpr ((coe_vElt C (l * C ^ 2) r).symm ▸ hq), rfl⟩
  have hτV : ∀ w ∈ V, f nrElt * w * (f nrElt)⁻¹ ∈ V := by
    intro w hw
    obtain ⟨C, D, F', rfl⟩ := hmemV.mp hw
    rw [← map_inv, ← map_mul, ← map_mul, nrElt_conj_vElt (K := K)]
    exact hmemV.mpr ⟨_, _, _, rfl⟩
  have hτinv : (f nrElt)⁻¹ = f nrElt := by rw [← map_inv, nrElt_inv (K := K)]
  have hτA₁ : f nrElt ∈ normalizer (A₁ : Set G) := by
    have h1 : f nrElt ∈ ((adjointGroup .G2 K ⊓
        normalizer (g2LongA2 K : Set (ModGL .G2 K))).subgroupOf (adjointGroup .G2 K)).map f := by
      refine ⟨nrElt, mem_subgroupOf.mpr ⟨nrElt.2, ?_⟩, rfl⟩
      rw [coe_nrElt (K := K)]
      exact G2.weylElt_r_mem_normalizer_g2LongA2
    rw [← tr_normalizer hfinj g2LongA2_le_adjointGroup, hM.A₁_eq] at h1
    exact h1.2
  have hτx : f nrElt * x * (f nrElt)⁻¹ = x⁻¹ := by
    rw [← hfh₀, ← map_inv, ← map_mul, ← map_mul, ← map_inv, nrElt_conj_torus t₀ ht₀]
  refine ⟨f nrElt, f (vElt 0 1 0), ⟨mem_normalizer_sec3B_of_inv hτA₁ hτx,
    G2.mem_normalizer_of_conj hτV (fun w hw => by
      have h := hτV w hw
      rw [hτinv] at h ⊢
      exact h), hτx, ?_, ?_⟩,
    ⟨hTV, hZs_eq, ?_, ?_, hTC, hmemV.mpr ⟨0, 1, 0, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    rw [hlz, ← map_mul, ← map_mul, nrElt_comm_vElt (K := K)]
  ·
    rw [← map_mul, nrElt_mul_self (K := K), map_one]
  ·
    intro b hb
    obtain ⟨C, D, F', rfl⟩ := hmemV.mp hb
    rw [hlz, ← map_mul, ← map_mul, vElt_mul, vElt_mul]
    exact congrArg f (vElt_congr (by ring) (by ring) (by ring))
  ·
    intro a ha b hb
    obtain ⟨C, D, F', rfl⟩ := hmemV.mp ha
    obtain ⟨C', D', F'', rfl⟩ := hmemV.mp hb
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, vElt_inv, vElt_inv, vElt_mul,
      vElt_mul, vElt_mul, vElt_congr (C' := 0) (D' := 0) (by char2_ring) (by char2_ring) rfl]
    exact hZsF _
  ·
    intro hN
    have h1 : f (vElt 0 1 0) ∈ f.range ⊓ normalizer (Q₀ : Set G) := ⟨⟨_, rfl⟩, hN⟩
    rw [hQ₀, tr_normalizer hfinj hQ0C, mem_map_iff_mem hfinj, mem_subgroupOf] at h1
    have h2 : g2N 0 0 0 1 0 0 ∈ g2ShortParabolicRadical K ⊓
        normalizer (G2.g2Q0 K l : Set (ModGL .G2 K)) := ⟨⟨0, 0, 1, 0, 0, rfl⟩, h1.2⟩
    have h3 := G2.g2ShortParabolicRadical_inf_normalizer_g2Q0_le hK hl0 h2
    have h4 : G2.g2Q0 K l ⊔ g2BCGroup K ≤ S' := by
      refine sup_le ?_ ?_
      · rintro _ ⟨C, F', _, _, rfl⟩
        exact ⟨C, 0, F', rfl⟩
      · rintro _ ⟨E', F', rfl⟩
        exact ⟨0, E', F', g2N_eq_g2N rfl rfl rfl (by ring) rfl rfl⟩
    obtain ⟨C, E', F', hw⟩ := h4 h3
    obtain ⟨-, -, h5, h6, -⟩ := g2N_injective hw
    rw [← h5] at h6
    exact one_ne_zero (h6.trans (by ring))
  ·
    exact hnotS 1 one_ne_zero
  ·
    rw [hx_vE, mul_zero, mul_one, ← map_inv, ← map_mul, vElt_inv, vElt_mul,
      vElt_congr (C' := 0) (D' := 1 + (t₀ : K)) (F' := 0) (by ring) rfl (by ring)]
    refine hnotS _ fun h => ht₀1 (Units.ext ?_)
    rw [Units.val_one]
    linear_combination (norm := char2_ring) h
  ·
    rw [hxinv_vE, mul_one, ← map_inv, ← map_mul, vElt_inv, vElt_mul,
      vElt_congr (C' := 0) (D' := 1 + ((t₀⁻¹ : Kˣ) : K)) (F' := 0) (by ring) rfl (by ring)]
    refine hnotS _ fun h => ht₀1 (inv_eq_one.mp (Units.ext ?_))
    rw [Units.val_one]
    linear_combination (norm := char2_ring) h
  ·
    intro w hw
    obtain ⟨C, D, F', rfl⟩ := hmemV.mp hw
    have hrep : ∀ D' : K, D + D' = l * C ^ 2 →
        f (vElt C D F') * (f (vElt 0 D' 0))⁻¹ ∈ Q₀ ⊔ Zs := by
      intro D' hD'
      rw [← map_inv, ← map_mul, vElt_inv, vElt_mul,
        vElt_congr (C' := C) (D' := l * C ^ 2) (F' := F') (by ring) hD' (by ring)]
      exact hinS C F'
    rcases eq_zero_or_one_or_of_card_four hK ht₀1 (D + l * C ^ 2) with h | h | h | h
    · left
      have h1 := hinS C F'
      rwa [vElt_congr (C' := C) (D' := D) (F' := F') rfl
        (by linear_combination (norm := char2_ring) -h) rfl] at h1
    · right; left
      exact hrep 1 (by linear_combination (norm := char2_ring) h)
    · right; right; left
      rw [hx_vE, mul_zero, mul_one]
      exact hrep _ (by linear_combination (norm := char2_ring) h)
    · right; right; right
      rw [hxinv_vE, mul_one]
      exact hrep _ (by linear_combination (norm := char2_ring) h)

end CFSG.ComponentClassification.AS81
