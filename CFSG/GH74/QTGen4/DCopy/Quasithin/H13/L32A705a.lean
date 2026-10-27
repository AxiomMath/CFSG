module

public import CFSG.Quasithin.H13.L32A705a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A515a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_x_cube_F4 {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S : L32NSet14.Setting_F4 G T L V V₂) {z a c : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (hc : c ∈ V) (hcV : c ∉ V₂) :
    ∃ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 ∧ x * z * x⁻¹ = z ∧ x * a * x⁻¹ = c ∧
      x * c * x⁻¹ = a * c := by
  have hzV₂ : z ∈ V₂ := S.hV2.1 hz
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have haV' : a ∈ V := S.hV2.2.1 ha
  obtain ⟨x, hxL, hx3, hxz, hxa, hxc⟩ := S.exists_rot_F4 hzV haV' hc
    (fun h => haV (h ▸ one_mem _)) (fun h => hcV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz)) (fun h => hcV (h ▸ hzV₂)) (fun h => hcV (h ▸ ha))
    (fun h => hcV (h ▸ mul_mem hzV₂ ha))
  exact ⟨x, Subgroup.subset_closure ⟨⟨hxL, S.mem_g1_F4 hz hz1 hxz⟩, 3, ⟨1, by norm_num⟩, hx3⟩, hx3,
    hxz, hxa, hxc⟩

namespace Setting147

variable {T L V H : Subgroup G}

theorem T_le_N_l1_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4) :
    T ≤ Subgroup.normalizer (l1 T L V : Set G) := fun t ht => by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful).2.1.1
  have htV : t ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.hz.2.1 ((Setting147.TH' S) ht)
  exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hTL ht, Subgroup.le_normalizer htV⟩)

theorem H_le_N_l1_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4)
    (hN : (modO2Image H (l1 T L V)).Normal) : H ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp (Setting147.TH' S)

  have hLQ : H ≤ Subgroup.normalizer ((l1 T L V ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨l, hl, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      ((hQT.trans (Setting147.T_le_N_l1_F4 S h1332)))).mp hx
    have hlH := (Setting147.l1H' S) hl
    have hlstar : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨h, hh⟩ * ⟨l, hlH⟩ * ⟨h, hh⟩⁻¹) ∈
        modO2Image H (l1 T L V) := by
      rw [map_mul, map_mul, map_inv]
      exact hN.conj_mem _ (mem_modO2Image'.mpr ⟨⟨l, hlH⟩, hl, rfl⟩) _
    obtain ⟨l', hl', he⟩ := mem_modO2Image'.mp hlstar
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at he
    have hq' : h * q * h⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
    have e : h * (l * q) * h⁻¹ = (l' : G) * (((l' : G))⁻¹ * (h * l * h⁻¹)) * (h * q * h⁻¹) := by
      group
    rw [e]
    refine mul_mem (mul_mem (Subgroup.mem_sup_left hl') (Subgroup.mem_sup_right ?_))
      (Subgroup.mem_sup_right hq')
    simpa using he

  have hO : oTwoUpper (l1 T L V ⊔ pCoreOf 2 H) = l1 T L V :=
    le_antisymm (oTwoUpper_sup_le_two' (pCoreOf_isPGroup 2 H)
      (hQT.trans (Setting147.T_le_N_l1_F4 S h1332)))
      (calc l1 T L V = oTwoUpper (l1 T L V) := (oTwoUpper_oTwoUpper _).symm
        _ ≤ _ := oTwoUpper_mono le_sup_left)
  rw [← hO]
  exact hLQ.trans (normalizer_le_normalizer_oTwoUpper _)

theorem card_l1_star_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) :
    Nat.card ↥(modO2Image H (l1 T L V)) = 3 := by
  rw [card_modO2Image' (Setting147.l1H' S), ← Subgroup.inf_relIndex_right, Setting147.inf_O2H S hHL]
  exact (lemma14_5_15_three_of_F4 h1222 h1332 h1334 G T L V H S hHL).2.1

theorem comm_R1_l1_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {r l : G}
    (hr : r ∈ pCoreOf 2 (l1 T L V ⊔ T)) (hl : l ∈ l1 T L V) :
    r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLT : l1 T L V ⊔ T ≤ Subgroup.normalizer (l1 T L V : Set G) :=
    sup_le Subgroup.le_normalizer (Setting147.T_le_N_l1_F4 S h1332)
  have hrN := hLT (pCoreOf_le 2 _ hr)
  have h1 : r * l * r⁻¹ * l⁻¹ ∈ l1 T L V :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hrN l).mp hl) (inv_mem hl)
  have h2 : r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) := by
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl)) r⁻¹).mp (inv_mem hr)
    rw [show r * l * r⁻¹ * l⁻¹ = r * (l * r⁻¹ * l⁻¹) by group]
    exact mul_mem hr this
  have h3 : r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (l1 T L V) := by
    refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : l1 T L V ⊓ pCoreOf 2 (l1 T L V ⊔ T) ≤ _)
      (fun l' hl' => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl',
        le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl')⟩)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right) ⟨h1, h2⟩
  rw [← Setting147.inf_O2H S hHL] at h3
  exact h3.1

theorem fix_z_of_N_F4 {V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting_F4 G T L V V₂) {z y : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hyN : y ∈ Subgroup.normalizer (fsuV1 T V : Set G)) : y * z * y⁻¹ = z := by
  have hm : y * z * y⁻¹ ∈ fsuV1 T V := (Subgroup.mem_normalizer_iff.mp hyN z).mp hz
  rcases S14.eq_of_mem_V1_F4 hz hz1 hm with h | h
  · exfalso
    apply hz1
    have := congrArg (fun u => y⁻¹ * u * y) h
    simpa [mul_assoc] using this
  · exact h

theorem mem_V1_of_fix_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {y u : G}
    (hy : y ∈ l1 T L V) (hyO : y ∉ pCoreOf 2 (l1 T L V)) (hu : u ∈ conjClosure V H)
    (hyu : y * u * y⁻¹ * u⁻¹ ∈ fsuV1 T V) : u ∈ fsuV1 T V := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hUab := Setting147.UH_comm S
  have hV1U : fsuV1 T V ≤ conjClosure V H :=
    (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V H)
  obtain ⟨z, a, b, hz, hz1, -, -, -, -⟩ := S14.exists_basis_F4
  have hp := Setting147.p3_mem_F4 S h1222 h1332 h1334 hHL hy hyO u hu
  set w := y * u * y⁻¹ * u⁻¹ with hw
  have hyw : y * w * y⁻¹ = w := fix_V1_F4 S14 hz hz1
    (Setting147.fix_z_of_N_F4 S14 hz hz1 (S.hz.2.1 (Setting147.l1H' S hy))) hyu
  have hyu' : y * u * y⁻¹ = w * u := by rw [hw]; group
  have hww : w * w = 1 := S14.mul_self_V_F4 (Subgroup.mem_inf.mp hyu).1
  have huu : u * u = 1 := Setting147.sq_fsuU S (fun v hv => S14.mul_self_V_F4 hv) u
    (conjClosure_mono le_rfl S.hz.2.1 hu)
  have hwu : w * u = u * w := hUab _ (hV1U hyu) _ hu
  have hy2 : y * (y * u * y⁻¹) * y⁻¹ = u := by
    rw [hyu', show y * (w * u) * y⁻¹ = (y * w * y⁻¹) * (y * u * y⁻¹) by group, hyw, hyu',
      ← mul_assoc, hww, one_mul]
  have he : p3 y u = w * u := by
    simp only [p3]
    rw [hy2, hyu']
    calc u * (w * u) * u = u * (u * w) * u := by rw [hwu]
      _ = w * u := by rw [← mul_assoc, huu, one_mul, hwu]
  rw [he] at hp
  rw [show u = w⁻¹ * (w * u) by group]
  exact mul_mem (inv_mem hyu) hp

theorem UH_eq_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) :
    ⁅conjClosure V H, l1 T L V⁆ ⊔ fsuV1 T V = conjClosure V H := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hUab := Setting147.UH_comm S
  have hV1U : fsuV1 T V ≤ conjClosure V H :=
    (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V H)
  have hN : ∀ l ∈ l1 T L V, ∀ u ∈ conjClosure V H, l * u * l⁻¹ ∈ conjClosure V H :=
    fun l hl u hu => (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure V H (Setting147.l1H' S hl)) u).mp hu
  refine le_antisymm (sup_le ?_ hV1U) (fun u hu => ?_)
  · rw [Subgroup.commutator_le]
    intro u hu l hl
    rw [commutatorElement_def, show u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) by group]
    exact mul_mem hu (hN l hl _ (inv_mem hu))
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨x, hx, -, -, hxa, -⟩ := exists_x_cube_F4 S14 hz hz1 ha haV hb hbV
  have hxl : x ∈ l1 T L V := hl1eq ▸ hx
  have hxO : x ∉ pCoreOf 2 (l1 T L V) := fun h => by
    have h1 := (S14.pCoreOf_L1_le_F4 (hl1eq ▸ h)).2.2 a (S14.hV2.2.1 ha)
    rw [hxa] at h1
    apply hbV
    rw [show b = b * a⁻¹ * a by group]
    exact mul_mem (S14.hV2.1 h1) ha
  have hp := Setting147.p3_mem_F4 S h1222 h1332 h1334 hHL hxl hxO u hu
  set a' := x * u * x⁻¹ with ha'
  have ha'U : a' ∈ conjClosure V H := hN x hxl u hu
  set b' := x * a' * x⁻¹ with hb'
  have hb'U : b' ∈ conjClosure V H := hN x hxl a' ha'U
  have ha'a' : a' * a' = 1 := Setting147.sq_fsuU S (fun v hv => S14.mul_self_V_F4 hv) a'
    (conjClosure_mono le_rfl S.hz.2.1 ha'U)

  have hc1 : a' * b' = b' * a' := hUab _ ha'U _ hb'U
  have hcomm' : ⁅a', x⁆ = a' * b'⁻¹ := by
    rw [commutatorElement_def, hb']
    group
  have hp3 : p3 x u = u * a' * b' := rfl
  have he : u = p3 x u * ⁅a', x⁆ :=
    calc u = u * (a' * a') * (b' * b'⁻¹) := by rw [ha'a', mul_inv_cancel, mul_one, mul_one]
      _ = u * a' * (a' * b') * b'⁻¹ := by group
      _ = u * a' * (b' * a') * b'⁻¹ := by rw [hc1]
      _ = (u * a' * b') * (a' * b'⁻¹) := by group
      _ = p3 x u * ⁅a', x⁆ := by rw [hp3, hcomm']
  rw [he]
  exact mul_mem (Subgroup.mem_sup_right hp)
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha'U hxl))

theorem T_trivSub_eq_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
    T ⊓ L32NSet14.trivSub V (fsuV1 T V) = pCoreOf 2 (l1 T L V ⊔ T) := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hle : pCoreOf 2 (l1 T L V ⊔ T) ≤ T ⊓ L32NSet14.trivSub V (fsuV1 T V) :=
    le_inf (Setting147.R1_le_T S) (hl1eq ▸ S14.pCoreOf_L1T_le_F4)
  have h2 : (pCoreOf 2 (l1 T L V ⊔ T)).relIndex T = 2 := hl1eq ▸ S14.index2_eq_F4
  have hm := Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_left
  rw [h2] at hm
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hm) with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hle
  · exfalso
    rw [h] at hm
    have h1 : (T ⊓ L32NSet14.trivSub V (fsuV1 T V)).relIndex T = 1 := by omega
    obtain ⟨t, ht, htn⟩ := S14.exists_T_not_triv_F4
    exact htn (Subgroup.relIndex_eq_one.mp h1 ht).2

theorem R1_star_eq_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) :
    modO2Image H (pCoreOf 2 (l1 T L V ⊔ T)) =
      modO2Image H T ⊓ Subgroup.centralizer (modO2Image H (l1 T L V) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _

  have hcomm : ∀ a b : ↥H, (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H →
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) b * QuotientGroup.mk' (CFSG.pCore 2 ↥H) a =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) b := by
    intro a b hab
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf]
    have e : (((b * a)⁻¹ * (a * b) : ↥H) : G) =
        ((b : G) * a)⁻¹ * ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * a)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (inv_mem (mul_mem b.2 a.2))) _).mp hab
  have hcomm' : ∀ a b : ↥H,
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) b * QuotientGroup.mk' (CFSG.pCore 2 ↥H) a =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) b →
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H := by
    intro a b hab
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hab
    have e : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ =
        ((b : G) * a) * ((((b * a)⁻¹ * (a * b) : ↥H) : G)) * ((b : G) * a)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (mul_mem b.2 a.2)) _).mp hab
  apply le_antisymm
  · rintro x hx
    obtain ⟨r, hr, rfl⟩ := mem_modO2Image'.mp hx
    refine ⟨mem_modO2Image'.mpr ⟨r, Setting147.R1_le_T S hr, rfl⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨l, hl, rfl⟩ := mem_modO2Image'.mp hy
    exact hcomm r l (Setting147.comm_R1_l1_F4 S h1332 hHL hr hl)
  · rintro x ⟨hxT, hxC⟩
    obtain ⟨t, ht, rfl⟩ := mem_modO2Image'.mp hxT
    refine mem_modO2Image'.mpr ⟨t, ?_, rfl⟩
    rw [← Setting147.T_trivSub_eq_F4 S h1222 h1332 h1334]
    refine ⟨ht, ?_⟩

    obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
    obtain ⟨x, hx, hx3, -, hxa, -⟩ := exists_x_cube_F4 S14 hz hz1 ha haV hb hbV
    have hxl : x ∈ l1 T L V := hl1eq ▸ hx
    obtain ⟨ψ, hψ⟩ := S14.exists_rep_F4
    have htX := S14.T_le_X_F4 ht
    have hxX := S14.L1_le_X_F4 hx
    have hxH := Setting147.l1H' S hxl
    have hc := hcomm' ⟨x, hxH⟩ t (Subgroup.mem_centralizer_iff.mp hxC _
      (mem_modO2Image'.mpr ⟨⟨x, hxH⟩, hxl, rfl⟩)).symm

    have hcT : (x : G) * t * x⁻¹ * (t : G)⁻¹ ∈ L32NSet14.trivSub V (fsuV1 T V) :=
      (hl1eq ▸ S14.pCoreOf_L1T_le_F4) (Setting147.O2H_le_R1 S hc)
    have hψc : ψ ⟨x, hxX⟩ * ψ ⟨t, htX⟩ = ψ ⟨t, htX⟩ * ψ ⟨x, hxX⟩ := by
      have h1 : ψ (⟨x, hxX⟩ * ⟨t, htX⟩ * ⟨x, hxX⟩⁻¹ * ⟨t, htX⟩⁻¹) = 1 :=
        (hψ _).mpr (by simpa using hcT)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc ψ ⟨x, hxX⟩ * ψ ⟨t, htX⟩ =
          ψ ⟨x, hxX⟩ * ψ ⟨t, htX⟩ * (ψ ⟨x, hxX⟩)⁻¹ * (ψ ⟨t, htX⟩)⁻¹ *
            (ψ ⟨t, htX⟩ * ψ ⟨x, hxX⟩) := by group
        _ = ψ ⟨t, htX⟩ * ψ ⟨x, hxX⟩ := by rw [h1, one_mul]
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨t, ht⟩
    have hk' : ((t : G)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hψt2 : ψ ⟨t, htX⟩ ^ 2 = 1 := by
      apply L32NSet14.sl2_sq_of_two (k := k)
      rw [← map_pow]
      have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    rcases sl2_comm_cases _ _ hψt2 hψx3 hψc.symm with h | h
    · exact (hψ _).mp h
    · exfalso
      have h1 := ((hψ _).mp h).2.2 a (S14.hV2.2.1 ha)
      rw [hxa] at h1
      apply hbV
      rw [show b = b * a⁻¹ * a by group]
      exact mul_mem (S14.hV2.1 h1) ha

theorem relIndex_R1_star_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
    (modO2Image H (pCoreOf 2 (l1 T L V ⊔ T))).relIndex (modO2Image H T) = 2 := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  rw [relIndex_modO2Image' (Setting147.TH' S) (Setting147.O2H_le_R1 S)]
  exact hl1eq ▸ S14.index2_eq_F4

end Setting147

end CFSG.Quasithin.H13.L32A
