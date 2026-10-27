module

public import CFSG.Quasithin.H13.L32AL2p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2f

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable {X : TopCtx T L V K W t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem fix_W_of_index_le_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (Wd : WrData (X.img (A6.g1 T V)) (X.img K) (X.img (K.map (MulAut.conj t₀ : G →* G))))
    {t : ↥(A6.g1 T V)} (ht2 : t * t = 1) (ht1 : X.top.act t ≠ 1)
    (hidx : ((Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf
      (conjClosure V (A6.g1 T V))).index ≤ 4) :
    ∀ c ∈ modO2Image (A6.g1 T V) K ⊔ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)),
      ∀ (w : G) (hw : w ∈ W), rhoDot X.top.hF.toHypF91 c (clsU X.top.hF.toHypF91
        (X.top.hWU.le hw)) = clsU X.top.hF.toHypF91 (X.top.hWU.le hw) := by
  obtain ⟨hsw, hcW⟩ := X.comm_eq_of_index_le Wd ht2 ht1 hidx
  set h := X.top.hF.toHypF91 with hh
  have hinj := X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  set c := QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) t with hc

  let N : Subgroup (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) :=
    { carrier := {x | ∀ (w : G) (hw : w ∈ W), rhoDot h x (clsU h (X.top.hWU.le hw)) =
        clsU h (X.top.hWU.le hw)}
      mul_mem' := fun {a b} ha hb w hw => by
        rw [map_mul, MulAut.mul_apply, hb w hw, ha w hw]
      one_mem' := fun w hw => by rw [map_one, MulAut.one_apply]
      inv_mem' := fun {a} ha w hw => by
        rw [map_inv]
        conv_lhs => rw [← ha w hw]
        exact MulAut.inv_apply_self _ _ _ }
  have hNn : N.Normal := by
    refine ⟨fun n hn g w hw => ?_⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(A6.g1 T V)) g
    have hwU := X.top.hWU.le hw
    have hw' : ((g'⁻¹ : ↥(A6.g1 T V)) : G) * w * ((g'⁻¹ : ↥(A6.g1 T V)) : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (X.top.hHW (g'⁻¹).2) w).mp hw
    have e1 : (rhoDot h (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) g'))⁻¹ (clsU h hwU) =
        clsU h (X.top.hWU.le hw') := by
      rw [← map_inv, ← map_inv, rhoDot_mk_clsU]
    show rhoDot h (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) g' * n *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) g')⁻¹) (clsU h hwU) = clsU h hwU
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv, e1, hn _ hw',
      rhoDot_mk_clsU]
    exact clsU_congr h _ _ (by simp [mul_assoc])
  have hcN : c ∈ N := fun w hw => by
    rw [hc, rhoDot_mk_clsU]
    exact clsU_congr h _ _ (hcW w hw)

  have hcK : ∀ a ∈ modO2Image (A6.g1 T V) K,
      c * a * c⁻¹ ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) := by
    intro a ha
    have h1 : X.actDot (c * a * c⁻¹) ∈ X.img (K.map (MulAut.conj t₀ : G →* G)) := by
      rw [map_mul, map_mul, map_inv, hc, actDot_mk]
      exact hsw _ (by rw [img_eq_map]; exact ⟨a, ha, rfl⟩)
    rw [img_eq_map] at h1
    obtain ⟨b, hb, hbe⟩ := h1
    rw [← hinj hbe]
    exact hb
  have hcKt : ∀ b ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)),
      c * b * c⁻¹ ∈ modO2Image (A6.g1 T V) K := by
    rcases L2.CtxL2.conj_cases X.C c with ⟨h1, -⟩ | ⟨-, h2⟩
    · exfalso
      obtain ⟨⟨a, ha⟩, ha1⟩ := @exists_ne _ X.C.isSimpleGroup_kb.toNontrivial 1
      apply ha1
      apply Subtype.ext
      have h3 := X.C.eq_one_of_mem_kb_kt hA37 (h1 a ha) (hcK a ha)
      show a = 1
      calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
        _ = 1 := by rw [h3]; group
    · exact h2

  have key : ∀ (A B : Subgroup (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V))), IsSimpleGroup ↥A →
      (∃ y ∈ A, ∃ z ∈ A, y * z ≠ z * y) → (∀ a ∈ A, c * a * c⁻¹ ∈ B) →
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → A ≤ N := by
    intro A B hA hnc hAB hcomm
    obtain ⟨y, hy, z, hz, hyz⟩ := hnc
    have hn : c * y * c⁻¹ * y⁻¹ ∈ N := by
      have := mul_mem hcN (hNn.conj_mem _ (inv_mem hcN) y)
      simpa [mul_assoc] using this
    have hnz : (c * y * c⁻¹ * y⁻¹) * z * (c * y * c⁻¹ * y⁻¹)⁻¹ * z⁻¹ ∈ N := by
      have := mul_mem hn (hNn.conj_mem _ (inv_mem hn) z)
      simpa [mul_assoc] using this
    have hyzy : y⁻¹ * z * y ∈ A := mul_mem (mul_mem (inv_mem hy) hz) hy
    have hcm := hcomm _ hyzy _ (hAB y hy)
    have heq : (c * y * c⁻¹ * y⁻¹) * z * (c * y * c⁻¹ * y⁻¹)⁻¹ * z⁻¹ = y⁻¹ * z * y * z⁻¹ := by
      calc (c * y * c⁻¹ * y⁻¹) * z * (c * y * c⁻¹ * y⁻¹)⁻¹ * z⁻¹
          = (c * y * c⁻¹) * (y⁻¹ * z * y) * (c * y * c⁻¹)⁻¹ * z⁻¹ := by group
        _ = (y⁻¹ * z * y) * (c * y * c⁻¹) * (c * y * c⁻¹)⁻¹ * z⁻¹ := by rw [← hcm]
        _ = y⁻¹ * z * y * z⁻¹ := by group
    rw [heq] at hnz
    have hmem : y⁻¹ * z * y * z⁻¹ ∈ A := mul_mem hyzy (inv_mem hz)
    have hne : y⁻¹ * z * y * z⁻¹ ≠ 1 := fun h1 => hyz (by
      have h2 : z * y = y * z := by
        calc z * y = y * (y⁻¹ * z * y * z⁻¹) * z := by group
          _ = y * z := by rw [h1, mul_one]
      exact h2.symm)
    have : (N.subgroupOf A).Normal := hNn.subgroupOf A
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h1 | h1
    · exfalso
      have h2 : (⟨_, hmem⟩ : ↥A) ∈ N.subgroupOf A := Subgroup.mem_subgroupOf.mpr hnz
      rw [h1, Subgroup.mem_bot] at h2
      exact hne (congrArg Subtype.val h2)
    · intro a ha
      have h2 : (⟨a, ha⟩ : ↥A) ∈ N.subgroupOf A := h1 ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h2

  obtain ⟨e₁⟩ := X.R.hA5
  obtain ⟨e₂⟩ := X.C.nonempty_equiv
  set φ₁ : ↥(modO2Image (A6.g1 T V) K) ≃* alternatingGroup (Fin 5) := e₂.symm.trans e₁ with hφ₁
  obtain ⟨a, b, hab⟩ := alt5_noncomm
  have hnc₁ : ∃ y ∈ modO2Image (A6.g1 T V) K, ∃ z ∈ modO2Image (A6.g1 T V) K, y * z ≠ z * y :=
    ⟨φ₁.symm a, (φ₁.symm a).2, φ₁.symm b, (φ₁.symm b).2, fun h1 => hab (by
      have h2 : φ₁.symm a * φ₁.symm b = φ₁.symm b * φ₁.symm a := Subtype.ext h1
      simpa using congrArg φ₁ h2)⟩
  have hnc₂ : ∃ y ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)),
      ∃ z ∈ modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)), y * z ≠ z * y :=
    ⟨X.C.equivKt (φ₁.symm a), (X.C.equivKt _).2, X.C.equivKt (φ₁.symm b), (X.C.equivKt _).2,
      fun h1 => hab (by
        have h2 : X.C.equivKt (φ₁.symm a * φ₁.symm b) = X.C.equivKt (φ₁.symm b * φ₁.symm a) := by
          rw [map_mul, map_mul]
          exact Subtype.ext h1
        simpa using congrArg φ₁ (X.C.equivKt.injective h2))⟩
  have hs₂ : IsSimpleGroup ↥(modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G))) :=
    (MulEquiv.isSimpleGroup_congr X.C.equivKt).mp X.C.isSimpleGroup_kb
  have hK₁ := key _ _ X.C.isSimpleGroup_kb hnc₁ hcK fun a ha b hb => X.C.commute_kb hA37 ha hb
  have hK₂ := key _ _ hs₂ hnc₂ hcKt fun a ha b hb => (X.C.commute_kb hA37 hb ha).symm
  intro c' hc' w hw
  exact sup_le hK₁ hK₂ hc' w hw

theorem eq_fsuV1_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (Wd : WrData (X.img (A6.g1 T V)) (X.img K) (X.img (K.map (MulAut.conj t₀ : G →* G))))
    {t : ↥(A6.g1 T V)} (ht2 : t * t = 1) (ht1 : X.top.act t ≠ 1)
    (hidx : ((Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf
      (conjClosure V (A6.g1 T V))).index ≤ 4) :
    W = fsuV1 T V := by
  have hfix := X.fix_W_of_index_le_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 Wd ht2 ht1 hidx
  set h := X.top.hF.toHypF91 with hh
  set Kb := modO2Image (A6.g1 T V) K with hKb
  set Kt := modO2Image (A6.g1 T V) (K.map (MulAut.conj t₀ : G →* G)) with hKt
  have hinj := X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hV : ∀ w : UMod h, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hUt : ∀ {w : G}, w ∈ W → w ∈ conjClosure V (A6.g1 T V) := fun hw => X.top.hWU.le hw

  let Wt : Subgroup (UMod h) :=
    { carrier := {x | ∃ (w : G) (hw : w ∈ W), clsU h (hUt hw) = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, W.mul_mem ha hb, by rw [clsU_mul]⟩
      one_mem' := ⟨1, W.one_mem, clsU_one _⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, W.inv_mem ha, by rw [clsU_inv]⟩ }
  have hsupK : ∀ {y}, y ∈ Kb ∨ y ∈ Kt → y ∈ Kb ⊔ Kt := fun hy =>
    hy.elim (fun h1 => Subgroup.mem_sup_left h1) (fun h1 => Subgroup.mem_sup_right h1)

  have hfixeq : ∀ y, y ∈ Kb ∨ y ∈ Kt → y ≠ 1 → y ^ 5 = 1 →
      fixV (Subgroup.zpowers (rhoDot h y)) = Wt := by
    intro y hy hy1 hy5
    apply le_antisymm
    · intro x hx
      have hx' : rhoDot h y x = x := hx _ (Subgroup.mem_zpowers _)
      obtain ⟨u, hu, rfl⟩ := exists_clsU h x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(A6.g1 T V)) y
      have h1 : (g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ fsuV1 T V := (rhoH_clsU_eq_iff h g hu).mp hx'
      have h2 : X.top.act g (InternalSec.secMk (W.subgroupOf (conjClosure V (A6.g1 T V)))
          ⟨u, hu⟩) = InternalSec.secMk (W.subgroupOf (conjClosure V (A6.g1 T V))) ⟨u, hu⟩ := by
        rw [X.top.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
        exact X.top.hV₁W h1
      have hg1 : X.top.act g ≠ 1 := fun h0 => hy1 (hinj (by rw [X.actDot_mk g, h0, map_one]))
      have hg5 : X.top.act g ^ 5 = 1 := by rw [← X.actDot_mk g, ← map_pow, hy5, map_one]
      have h3 : InternalSec.secMk (W.subgroupOf (conjClosure V (A6.g1 T V))) ⟨u, hu⟩ = 1 := by
        rcases hy with hy | hy
        · exact Wd.fpf₁ _ (by rw [img_eq_map]; exact ⟨_, hy, X.actDot_mk g⟩) hg1 5 (by decide)
            hg5 _ h2
        · exact Wd.fpf₂ _ (by rw [img_eq_map]; exact ⟨_, hy, X.actDot_mk g⟩) hg1 5 (by decide)
            hg5 _ h2
      rw [A6.A6Mod.secMk_eq_one_iff] at h3
      exact ⟨u, h3, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩ z hz
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← map_zpow]
      exact hfix _ (zpow_mem (hsupK hy) j) w hw

  obtain ⟨e₁⟩ := X.R.hA5
  obtain ⟨e₂⟩ := X.C.nonempty_equiv
  set φ₁ : ↥Kb ≃* alternatingGroup (Fin 5) := e₂.symm.trans e₁ with hφ₁
  set y₁ := ((φ₁.symm cycle5 : ↥Kb) : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) with hy₁
  set y₂ := ((X.C.equivKt (φ₁.symm cycle5) : ↥Kt) : ↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V))
    with hy₂
  have hy₁K : y₁ ∈ Kb := (φ₁.symm cycle5).2
  have hy₂K : y₂ ∈ Kt := (X.C.equivKt _).2
  have hy₁5 : y₁ ^ 5 = 1 := by
    rw [hy₁, ← Subgroup.coe_pow, ← map_pow, cycle5_pow_five, map_one, Subgroup.coe_one]
  have hy₂5 : y₂ ^ 5 = 1 := by
    rw [hy₂, ← Subgroup.coe_pow, ← map_pow, ← map_pow, cycle5_pow_five, map_one, map_one,
      Subgroup.coe_one]
  have hy₁1 : y₁ ≠ 1 := fun h1 => cycle5_ne_one (by
    have h2 : φ₁.symm cycle5 = 1 := Subtype.ext h1
    simpa using congrArg φ₁ h2)
  have hy₂1 : y₂ ≠ 1 := fun h1 => cycle5_ne_one (by
    have h2 : X.C.equivKt (φ₁.symm cycle5) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    simpa using congrArg φ₁ h2)
  have hρ5 : ∀ {y}, y ^ 5 = 1 → rhoDot h y ^ 5 = 1 := fun hy => by rw [← map_pow, hy, map_one]
  set Xc := commSub ⊤ (Subgroup.zpowers (rhoDot h y₁)) with hXc
  have hX12 : Xc = commSub ⊤ (Subgroup.zpowers (rhoDot h y₂)) :=
    commSub_eq_of_fixV_eq hV (by decide) (by decide) (hρ5 hy₁5) (hρ5 hy₂5)
      (by rw [← map_mul, ← map_mul, X.C.commute_kb hA37 hy₁K hy₂K])
      (by rw [hfixeq _ (Or.inl hy₁K) hy₁1 hy₁5, hfixeq _ (Or.inr hy₂K) hy₂1 hy₂5])

  have hXany : ∀ y, y ∈ Kb ∨ y ∈ Kt → y ≠ 1 → y ^ 5 = 1 →
      commSub ⊤ (Subgroup.zpowers (rhoDot h y)) = Xc := by
    intro y hy hy1 hy5
    rcases hy with hy' | hy'
    · rw [hX12]
      exact commSub_eq_of_fixV_eq hV (by decide) (by decide) (hρ5 hy5) (hρ5 hy₂5)
        (by rw [← map_mul, ← map_mul, X.C.commute_kb hA37 hy' hy₂K])
        (by rw [hfixeq _ (Or.inl hy') hy1 hy5, hfixeq _ (Or.inr hy₂K) hy₂1 hy₂5])
    · exact (commSub_eq_of_fixV_eq hV (by decide) (by decide) (hρ5 hy₁5) (hρ5 hy5)
        (by rw [← map_mul, ← map_mul, X.C.commute_kb hA37 hy₁K hy'])
        (by rw [hfixeq _ (Or.inl hy₁K) hy₁1 hy₁5, hfixeq _ (Or.inr hy') hy1 hy5])).symm

  have hXinv : ∀ c x, x ∈ Xc → rhoDot h c x ∈ Xc := by
    intro c x hx
    have hcy : c * y₁ * c⁻¹ ∈ Kb ∨ c * y₁ * c⁻¹ ∈ Kt := by
      rcases L2.CtxL2.conj_cases X.C c with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (h1 y₁ hy₁K)
      · exact Or.inr (h1 y₁ hy₁K)
    have hne : c * y₁ * c⁻¹ ≠ 1 := fun h0 => hy₁1 (by
      calc y₁ = c⁻¹ * (c * y₁ * c⁻¹) * c := by group
        _ = 1 := by rw [h0]; group)
    have h5 : (c * y₁ * c⁻¹) ^ 5 = 1 := by rw [conj_pow, hy₁5, mul_one, mul_inv_cancel]
    rw [← hXany _ hcy hne h5]
    refine B1.commSub_smul_mem (rhoDot h c) (fun z hz => ?_) (fun _ _ => Subgroup.mem_top _) x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [map_mul, map_mul, map_inv, conj_zpow]

  obtain ⟨hsup, hinf, -, -⟩ := B1.zpowers_decomp hV (r := 5) (by decide) (hρ5 hy₁5)
  rw [hfixeq _ (Or.inl hy₁K) hy₁1 hy₁5] at hsup hinf

  have hcommK : ∀ k ∈ Kb ⊔ Kt, ∀ x : UMod h, rhoDot h k x * x⁻¹ ∈ Xc := by
    intro k hk x
    have hx : x ∈ Wt ⊔ Xc := hsup ▸ Subgroup.mem_top x
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨w, hw, rfl⟩ := ha
    rw [map_mul, hfix k hk w hw]
    have e : clsU h (hUt hw) * rhoDot h k b * (clsU h (hUt hw) * b)⁻¹ =
        rhoDot h k b * b⁻¹ := by
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    rw [e]
    exact mul_mem (hXinv k b hb) (inv_mem hb)

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨y, hyL, hy3, hfpfy⟩ := exists_l1_fpf_F4 X.C.S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
  have hyH : y ∈ A6.g1 T V := Setting147.l1H' X.C.S hy
  obtain ⟨k₁, hk₁K, k₂, hk₂K, he, -, -, -, -⟩ := X.C.decomp hA37 hy hy3
  have he' : QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) (⟨y, hyH⟩ : ↥(A6.g1 T V)) =
      k₁ * k₂ := he
  set yb := QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) (⟨y, hyH⟩ : ↥(A6.g1 T V)) with hyb
  have hybK : yb ∈ Kb ⊔ Kt := by
    rw [he']
    exact mul_mem (Subgroup.mem_sup_left hk₁K) (Subgroup.mem_sup_right hk₂K)
  have hyN : ∀ j : ℤ, y ^ j ∈ Subgroup.normalizer (V : Set G) := fun j =>
    zpow_mem (h.L₁T_normalizes_Vp (Subgroup.mem_sup_left hyL)) j
  let P : Subgroup (UMod h) :=
    { carrier := {x | ∃ (v : G) (hv : v ∈ V), clsU h (le_conjClosure V _ hv) = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, V.mul_mem ha hb, by rw [clsU_mul]⟩
      one_mem' := ⟨1, V.one_mem, clsU_one _⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, V.inv_mem ha, by rw [clsU_inv]⟩ }
  have hyb3 : rhoDot h yb ^ 3 = 1 := by
    have : yb ^ 3 = 1 := by
      rw [hyb, ← map_pow]
      have e : (⟨y, hyH⟩ : ↥(A6.g1 T V)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [e, map_one]
    rw [← map_pow, this, map_one]
  have hPinv : ∀ z ∈ Subgroup.zpowers (rhoDot h yb), ∀ p ∈ P, z p ∈ P := by
    intro z hz p hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨v, hv, rfl⟩ := hp
    rw [← map_zpow, hyb, ← map_zpow, rhoDot_mk_clsU]
    have hvm : (((⟨y, hyH⟩ : ↥(A6.g1 T V)) ^ j : ↥(A6.g1 T V)) : G) * v *
        (((⟨y, hyH⟩ : ↥(A6.g1 T V)) ^ j : ↥(A6.g1 T V)) : G)⁻¹ ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hyN j) v).mp hv
      simpa using this
    exact ⟨_, hvm, rfl⟩
  have hPfix : P ⊓ fixV (Subgroup.zpowers (rhoDot h yb)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨v, hv, rfl⟩, hfx⟩
    rw [Subgroup.mem_bot, clsU_eq_one_iff]
    have h1 : rhoDot h yb (clsU h (le_conjClosure V _ hv)) = clsU h (le_conjClosure V _ hv) :=
      hfx _ (Subgroup.mem_zpowers _)
    exact hfpfy v hv ((rhoH_clsU_eq_iff h ⟨y, hyH⟩ _).mp h1)
  have hYodd : Odd (Nat.card (Subgroup.zpowers (rhoDot h yb))) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hyb3)
  obtain ⟨hsupP, -⟩ := B1.coprime_decomp hV hYodd hPinv
  rw [hPfix, bot_sup_eq] at hsupP
  have hPX : P ≤ Xc := by
    rw [← hsupP, commSub, Subgroup.closure_le]
    rintro _ ⟨z, hz, p, -, rfl⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← map_zpow]
    exact hcommK _ (zpow_mem hybK j) p

  let S : Subgroup G :=
    { carrier := {u | ∃ hu : u ∈ conjClosure V (A6.g1 T V), clsU h hu ∈ Xc}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        have := mul_mem ha' hb'
        rw [clsU_mul] at this
        exact ⟨mul_mem ha hb, this⟩
      one_mem' := ⟨one_mem _, by rw [clsU_one]; exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        have := inv_mem ha'
        rw [clsU_inv] at this
        exact ⟨inv_mem ha, this⟩ }
  have hUS : conjClosure V (A6.g1 T V) ≤ S := conjClosure_le fun g hg v hv =>
    ⟨conj_mem_UH hg (le_conjClosure V _ hv), by
      have := hXinv (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) ⟨g, hg⟩) _
        (hPX ⟨v, hv, rfl⟩)
      rwa [rhoDot_mk_clsU] at this⟩
  refine le_antisymm (fun w hw => ?_) X.top.hV₁W
  obtain ⟨hwU, hwX⟩ := hUS (hUt hw)
  have hm : clsU h hwU ∈ Wt ⊓ Xc := Subgroup.mem_inf.mpr ⟨⟨w, hw, rfl⟩, hwX⟩
  rw [hinf, Subgroup.mem_bot, clsU_eq_one_iff] at hm
  exact hm

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
