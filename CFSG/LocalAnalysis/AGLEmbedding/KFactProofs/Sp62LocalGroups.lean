module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTab
public import CFSG.LocalAnalysis.AGLEmbedding.KlingenRoute
public import Certificates.Certificate9440
public import Certificates.Certificate9441

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13 CFSG.KGroups.Sp6 CFSG.Quasithin.G2U CFSG.Open CFSG.SectionRank.Ccomm
open CFSG.Assembly.LowTwoRank

@[expose] def T0 : Subgroup H6 := Hgen gensT

@[expose] def B0 : Subgroup H6 := Hgen gensB

@[expose] def E0 : Subgroup H6 := Hgen gensE

@[expose] def D0 : Subgroup H6 := Hgen gensD

@[expose] def W0 : Subgroup H6 := Hgen gensWD

@[expose] def V0 : Subgroup H6 := Hgen gensV

theorem sp62_tables_small :
    chkT = true ∧ chkB = true ∧ chkE = true ∧ chkD = true :=
  Certificates.certificate9440

theorem tabCheck_T :
    tabCheck gensT 81 (fun _ => true) = true := sp62_tables_small.1

theorem tabCheck_B : tabCheck gensB 27 propB = true :=
  sp62_tables_small.2.1

theorem tabCheck_E : tabCheck gensE 27 propE = true :=
  sp62_tables_small.2.2.1

theorem tabCheck_D : tabCheck gensD 9 propD = true :=
  sp62_tables_small.2.2.2

theorem card_T0 : Nat.card T0 = 3 ^ 4 :=
  (tabCheck_spec tabCheck_T).2.2.1.trans (by norm_num)

theorem isPGroup_T0 : IsPGroup 3 T0 :=
  IsPGroup.of_card card_T0

theorem not_dvd_index_T0 : ¬ 3 ∣ T0.index := by
  have h := Subgroup.card_mul_index T0
  rw [card_T0, card_H6] at h
  omega

@[expose] noncomputable def T0S : Sylow 3 H6 :=
  isPGroup_T0.toSylow not_dvd_index_T0

theorem coe_T0S : (T0S : Subgroup H6) = T0 :=
  IsPGroup.toSylow_coe _ _

theorem B0_spec :
    propB1 (tabOf gensB 27) = true ∧ propB2 (tabOf gensB 27) = true ∧
      propB3 (tabOf gensB 27) = true ∧ propB4 (tabOf gensB 27) = true := by
  simpa only [propB, Bool.and_eq_true] using (tabCheck_spec tabCheck_B).2.2.2.1

theorem B0_le_T0 : B0 ≤ T0 := by
  have h := B0_spec.1
  simp only [propB1, List.all_eq_true] at h
  exact Hgen_le_of_inTab tabCheck_T (tabCheck_spec tabCheck_B).2.2.2.2
    (fun c hc => inTab_iff.1 (h c hc))

theorem card_B0 : Nat.card B0 = 3 ^ 3 :=
  (tabCheck_spec tabCheck_B).2.2.1.trans (by norm_num)

theorem pow_three_B0 : ∀ x ∈ B0, x ^ 3 = 1 :=
  pow_three_Hgen tabCheck_B B0_spec.2.1

theorem B0_elemAbelian : IsElemAbelian 3 B0 :=
  ⟨isMulCommutative_Hgen tabCheck_B B0_spec.2.2.1, pow_three_B0⟩

theorem elt_mem_normalizer_B0 {c : List ℕ} (hc : c ∈ gensN) :
    elt c ∈ Subgroup.normalizer (B0 : Set H6) := by
  have h := B0_spec.2.2.2
  simp only [propB4, List.all_eq_true, Bool.and_eq_true] at h
  exact elt_mem_normalizer_Hgen tabCheck_B (h c hc).1
    fun x hx => inTab_iff.1 ((h c hc).2 x hx)

theorem E0_spec :
    propE1 (tabOf gensE 27) = true ∧ propE2 (tabOf gensE 27) = true ∧
      propE3 (tabOf gensE 27) = true ∧ propE4 (tabOf gensE 27) = true ∧
      propE5 (tabOf gensE 27) = true ∧ propE6 (tabOf gensE 27) = true ∧
      propE7 (tabOf gensE 27) = true ∧ propE8 (tabOf gensE 27) = true ∧
      propE9 (tabOf gensE 27) = true ∧ propE10 (tabOf gensE 27) = true ∧
      propE11 (tabOf gensE 27) = true ∧ propE12 (tabOf gensE 27) = true ∧
      propE13 (tabOf gensE 27) = true ∧ propE14 (tabOf gensE 27) = true := by
  simpa only [propE, Bool.and_eq_true] using (tabCheck_spec tabCheck_E).2.2.2.1

theorem E0_le_T0 : E0 ≤ T0 := by
  have h := E0_spec.1
  simp only [propE1, List.all_eq_true] at h
  exact Hgen_le_of_inTab tabCheck_T (tabCheck_spec tabCheck_E).2.2.2.2
    (fun c hc => inTab_iff.1 (h c hc))

theorem card_E0 : Nat.card E0 = 3 ^ 3 :=
  (tabCheck_spec tabCheck_E).2.2.1.trans (by norm_num)

theorem pow_three_E0 : ∀ x ∈ E0, x ^ 3 = 1 :=
  pow_three_Hgen tabCheck_E E0_spec.2.1

@[expose] noncomputable def z0 : H6 := elt cZ

theorem genB_cZ : genB cZ = true := by
  have h := E0_spec.2.2.2.2.1
  simp only [propE5, Bool.and_eq_true] at h
  exact h.2

theorem rep_z0 : Rep z0 cZ := rep_elt (genB_isoB genB_cZ)

theorem z0_mem_E0 : z0 ∈ E0 := by
  have h := E0_spec.2.2.2.2.1
  simp only [propE5, Bool.and_eq_true] at h
  exact mem_Hgen_of_rep tabCheck_E (inTab_iff.1 h.1) rep_z0

theorem z0_comm_E0 : ∀ y ∈ E0, z0 * y = y * z0 := by
  have h := E0_spec.2.2.2.1
  simp only [propE4, List.all_eq_true] at h
  exact comm_Hgen_of_gens rep_z0 (tabCheck_spec tabCheck_E).2.2.2.2 h

theorem z0_pow_three : z0 ^ 3 = 1 :=
  rep_z0.pow_three.2 (beq_iff_eq.1 E0_spec.2.2.2.2.2.1)

theorem z0_ne_one : z0 ≠ 1 := fun h => by
  have h7 : (cZ != oneC) = true := E0_spec.2.2.2.2.2.2.1
  exact bne_iff_ne.1 h7 (rep_z0.eq_one_iff.1 h)

theorem orderOf_z0 : orderOf z0 = 3 :=
  orderOf_eq_prime z0_pow_three z0_ne_one

theorem rep_z0_sq : Rep (z0 * z0) cZ2 := by
  have h := beq_iff_eq.1 E0_spec.2.2.2.2.2.2.2.1
  rw [h]
  exact rep_z0.mul rep_z0

theorem mem_zpowers_z0 {s : H6} {t : List ℕ} (hs : Rep s t)
    (ht : inZ t = true) : s ∈ Subgroup.zpowers z0 := by
  simp only [inZ, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with (rfl | rfl) | rfl
  · rw [hs.eq Rep.one]
    exact Subgroup.one_mem _
  · rw [hs.eq rep_z0]
    exact Subgroup.mem_zpowers z0
  · rw [hs.eq rep_z0_sq, ← sq]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z0) 2

theorem center_E0_map :
    (Subgroup.center E0).map E0.subtype = Subgroup.zpowers z0 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_E x.2
    have hcomm : ∀ c ∈ gensE, commB t c = true := by
      intro c hc
      have hxc : elt c ∈ E0 := elt_mem_Hgen hc
      have := Subgroup.mem_center_iff.1 hx ⟨elt c, hxc⟩
      have hh := congrArg Subtype.val this
      exact beq_iff_eq.2 ((hrep.comm_iff (rep_elt (genB_isoB
        ((tabCheck_spec tabCheck_E).2.2.2.2 c hc)))).1 (by simpa using hh.symm))
    have h9 := forall_of_allCheck E0_spec.2.2.2.2.2.2.2.2.1 t ht
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h9
    rcases h9 with h9 | h9
    · exact absurd (List.all_eq_true.2 hcomm) (by simp [h9])
    · exact mem_zpowers_z0 hrep h9
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨z0, z0_mem_E0⟩, Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (z0_comm_E0 y y.2).symm, rfl⟩

theorem card_center_E0 : Nat.card (Subgroup.center E0) = 3 := by
  have h : Nat.card ((Subgroup.center E0).map E0.subtype) = Nat.card (Subgroup.center E0) :=
    Subgroup.card_map_of_injective E0.subtype_injective
  rw [center_E0_map, Nat.card_zpowers, orderOf_z0] at h
  exact h.symm

theorem D0_spec :
    propD1 (tabOf gensD 9) = true ∧ propD2 (tabOf gensD 9) = true ∧
      propD3 (tabOf gensD 9) = true ∧ propD4 (tabOf gensD 9) = true ∧
      propD5 (tabOf gensD 9) = true := by
  simpa only [propD, Bool.and_eq_true] using (tabCheck_spec tabCheck_D).2.2.2.1

theorem D0_le_E0 : D0 ≤ E0 := by
  have h := D0_spec.1
  simp only [propD1, List.all_eq_true] at h
  exact Hgen_le_of_inTab tabCheck_E (tabCheck_spec tabCheck_D).2.2.2.2
    (fun c hc => inTab_iff.1 (h c hc))

theorem card_D0 : Nat.card D0 = 3 ^ 2 :=
  (tabCheck_spec tabCheck_D).2.2.1.trans (by norm_num)

theorem D0_elemAbelian : IsElemAbelian 3 D0 :=
  ⟨isMulCommutative_Hgen tabCheck_D D0_spec.2.2.1,
    pow_three_Hgen tabCheck_D D0_spec.2.1⟩

theorem D0_centralizes_T0 :
    ∀ y ∈ D0, y ∈ Subgroup.centralizer (T0 : Set H6) →
      y ∈ (Subgroup.center E0).map E0.subtype := by
  intro y hy hyc
  rw [center_E0_map]
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_D hy
  have hcomm : ∀ c ∈ gensT, commB t c = true := by
    intro c hc
    have hxc : elt c ∈ T0 := elt_mem_Hgen hc
    have := Subgroup.mem_centralizer_iff.1 hyc (elt c) hxc
    exact beq_iff_eq.2 ((hrep.comm_iff (rep_elt (genB_isoB
      ((tabCheck_spec tabCheck_T).2.2.2.2 c hc)))).1 this.symm)
  have h4 := forall_of_allCheck D0_spec.2.2.2.1 t ht
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h4
  rcases h4 with h4 | h4
  · exact absurd (List.all_eq_true.2 hcomm) (by simp [h4])
  · exact mem_zpowers_z0 hrep h4

theorem elt_gD_mem_normalizer_D0 :
    elt cGD ∈ Subgroup.normalizer (D0 : Set H6) := by
  have h := D0_spec.2.2.2.2
  simp only [propD5, Bool.and_eq_true, List.all_eq_true] at h
  exact elt_mem_normalizer_Hgen tabCheck_D h.1 fun x hx => inTab_iff.1 (h.2 x hx)

@[expose] def L0 : Subgroup H6 := Hgen [cW0, cGu]

theorem genB_cW0 : genB cW0 = true :=
  (tabCheck_spec tabCheck_T).2.2.2.2 cW0 (by simp [gensT])

theorem E10_spec :
    ∀ g ∈ [cW0, cGu], genB g = true ∧ (∀ x ∈ gensE, inTab (tabOf gensE 27) (conjC g x) = true) ∧
      commB g cZ = true ∧ cubeB g = true := by
  intro g hg
  have h := E0_spec.2.2.2.2.2.2.2.2.2.1
  simp only [propE10, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h g hg
  exact ⟨h1, h2, h3, h4⟩

theorem genB_cGu : genB cGu = true :=
  (E10_spec cGu (by simp)).1

theorem elt_mem_normalizer_E0 {g : List ℕ}
    (hg : g ∈ [cW0, cGu]) : elt g ∈ Subgroup.normalizer (E0 : Set H6) :=
  elt_mem_normalizer_Hgen tabCheck_E (E10_spec g hg).1 fun x hx =>
    inTab_iff.1 ((E10_spec g hg).2.1 x hx)

theorem elt_comm_z0 {g : List ℕ} (hg : g ∈ [cW0, cGu]) :
    Commute (elt g) z0 :=
  (rep_elt (genB_isoB (E10_spec g hg).1)).comm_iff rep_z0 |>.2 (beq_iff_eq.1 (E10_spec g hg).2.2.1)

theorem pow_three_elt {g : List ℕ} (hg : g ∈ [cW0, cGu]) :
    elt g ^ 3 = 1 :=
  (rep_elt (genB_isoB (E10_spec g hg).1)).pow_three.2 (beq_iff_eq.1 (E10_spec g hg).2.2.2)

theorem L0_le_centralizer :
    L0 ≤ Subgroup.centralizer (((Subgroup.center E0).map E0.subtype : Subgroup H6) : Set H6) := by
  rw [center_E0_map]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((elt_comm_z0 hg).zpow_right k).symm.eq

theorem zpowers_z0_cases {s : H6} (hs : s ∈ Subgroup.zpowers z0) :
    s = 1 ∨ s = z0 ∨ s = z0 * z0 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  have h3 : z0 ^ (3 : ℤ) = 1 := by exact_mod_cast z0_pow_three
  have hk : z0 ^ k = z0 ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rw [hk]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; rw [zpow_two]

theorem act_eq_of_eq
    (e : E0 ⧸ Subgroup.center E0 ≃* Multiplicative (Fin 2 → ZMod 3))
    {g h : Subgroup.normalizer (E0 : Set H6)}
    (hgh : centerQuotientAction E0 e g = centerQuotientAction E0 e h) (x : E0) :
    ∃ s : H6, (s = 1 ∨ s = z0 ∨ s = z0 * z0) ∧
      (g : H6) * x * (g : H6)⁻¹ = (h : H6) * x * (h : H6)⁻¹ * s := by
  have h1 : autQuotient (Subgroup.center E0) (E0.normalizerMonoidHom g) =
      autQuotient (Subgroup.center E0) (E0.normalizerMonoidHom h) :=
    (elemAutEquivGL e).injective hgh
  have h2 := congrArg (fun β : MulAut (E0 ⧸ Subgroup.center E0) =>
    β (x : E0 ⧸ Subgroup.center E0)) h1
  simp only [autQuotient_mk] at h2
  have h3 := QuotientGroup.eq.1 h2
  set a := E0.normalizerMonoidHom g x with ha
  set b := E0.normalizerMonoidHom h x with hb
  have h4 : ((a⁻¹ * b)⁻¹ : E0) ∈ Subgroup.center E0 := inv_mem h3
  have h5 : (((a⁻¹ * b)⁻¹ : E0) : H6) ∈ Subgroup.zpowers z0 := by
    rw [← center_E0_map]
    exact ⟨_, h4, rfl⟩
  refine ⟨_, zpowers_z0_cases h5, ?_⟩
  have ha' : ((a : E0) : H6) = (g : H6) * x * (g : H6)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe E0 g x
  have hb' : ((b : E0) : H6) = (h : H6) * x * (h : H6)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe E0 h x
  rw [← ha', ← hb']
  simp

theorem act_ne
    (e : E0 ⧸ Subgroup.center E0 ≃* Multiplicative (Fin 2 → ZMod 3))
    {g h : Subgroup.normalizer (E0 : Set H6)} {c d : List ℕ} (hc : genB c = true)
    (hd : genB d = true) (hg : (g : H6) = elt c) (hh : (h : H6) = elt d)
    (hne : actNe (tabOf gensE 27) c d = true) :
    centerQuotientAction E0 e g ≠ centerQuotientAction E0 e h := by
  intro hgh
  simp only [actNe, List.any_eq_true, Bool.not_eq_true'] at hne
  obtain ⟨x, hx, hnot⟩ := hne
  obtain ⟨x', hx'E, hx'⟩ := (tabCheck_spec tabCheck_E).2.1 x (Array.mem_toList_iff.1 hx)
  obtain ⟨s, hs, hsE⟩ := act_eq_of_eq e hgh ⟨x', hx'E⟩
  have hcg : Rep (g : H6) c := hg ▸ rep_elt (genB_isoB hc)
  have hdh : Rep (h : H6) d := hh ▸ rep_elt (genB_isoB hd)
  have hgi : Rep (g : H6)⁻¹ (invC c) := hg ▸ rep_elt_inv hc
  have hhi : Rep (h : H6)⁻¹ (invC d) := hh ▸ rep_elt_inv hd
  have hL : Rep ((g : H6) * x' * (g : H6)⁻¹) (conjC c x) := by
    unfold conjC
    rw [mul_assoc]
    exact hcg.mul (hx'.mul hgi)
  have hR : Rep ((h : H6) * x' * (h : H6)⁻¹) (conjC d x) := by
    unfold conjC
    rw [mul_assoc]
    exact hdh.mul (hx'.mul hhi)
  simp only [inZc, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hnot
  obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
  rcases hs with rfl | rfl | rfl
  · rw [mul_one] at hsE
    exact h1 ((hL.eq_iff hR).1 hsE)
  · exact h2 ((hL.eq_iff (hR.mul rep_z0)).1 hsE)
  · exact h3 ((hL.eq_iff (hR.mul rep_z0_sq)).1 hsE)

theorem genB_oneC : genB oneC = true := by decide

theorem one_eq_elt_oneC : (1 : H6) = elt oneC :=
  Rep.one.eq (rep_elt (genB_isoB genB_oneC))

theorem zpow_cases_of_pow_three {G : Type*} [Group G] {u : G} (h : u ^ 3 = 1) (k : ℤ) :
    u ^ k = 1 ∨ u ^ k = u ∨ u ^ k = u⁻¹ := by
  have h3 : u ^ (3 : ℤ) = 1 := by exact_mod_cast h
  have hk : u ^ k = u ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rw [hk]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · left; rw [hr]; simp
  · right; left; rw [hr]; simp
  · right; right
    rw [hr, show (2 : ℤ) = -1 + 3 by norm_num, zpow_add, h3, mul_one, zpow_neg_one]

theorem exists_e_SL :
    ∃ e : E0 ⧸ Subgroup.center E0 ≃* Multiplicative (Fin 2 → ZMod 3),
      StatedSL 2 (ZMod 3) ≤
        (L0.subgroupOf (Subgroup.normalizer (E0 : Set H6))).map (centerQuotientAction E0 e) := by
  have hgenE := (tabCheck_spec tabCheck_E).2.2.2.2
  have hsgE : cSg ∈ gensE := by simp [gensE]
  have hbeE : cBeta ∈ gensE := by simp [gensE]
  have hnc : ∃ a b : E0, a * b ≠ b * a := by
    refine ⟨⟨elt cSg, elt_mem_Hgen hsgE⟩, ⟨elt cBeta, elt_mem_Hgen hbeE⟩, fun h => ?_⟩
    have h' : elt cSg * elt cBeta = elt cBeta * elt cSg := congrArg Subtype.val h
    have h3 : (!(commB cSg cBeta)) = true := E0_spec.2.2.1
    have h4 := ((rep_elt (genB_isoB (hgenE _ hsgE))).comm_iff
      (rep_elt (genB_isoB (hgenE _ hbeE)))).1 h'
    simp [commB, h4] at h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, ⟨e⟩⟩ := center_structure_of_card_eq_pow_three (p := 3)
    (card_E0 : Nat.card E0 = 3 ^ 3) hnc
  refine ⟨e, ?_⟩
  have hwmem : cW0 ∈ [cW0, cGu] := by simp
  have humem : cGu ∈ [cW0, cGu] := by simp
  let wN : Subgroup.normalizer (E0 : Set H6) := ⟨elt cW0, elt_mem_normalizer_E0 hwmem⟩
  let uN : Subgroup.normalizer (E0 : Set H6) := ⟨elt cGu, elt_mem_normalizer_E0 humem⟩
  have hwL : elt cW0 ∈ L0 := elt_mem_Hgen (c := cW0) hwmem
  have huL : elt cGu ∈ L0 := elt_mem_Hgen (c := cGu) humem
  have hu3 : centerQuotientAction E0 e uN ^ 3 = 1 := by
    rw [← map_pow]
    have : uN ^ 3 = 1 := Subtype.ext (by simpa using pow_three_elt humem)
    rw [this, map_one]
  have hw3 : centerQuotientAction E0 e wN ^ 3 = 1 := by
    rw [← map_pow]
    have : wN ^ 3 = 1 := Subtype.ext (by simpa using pow_three_elt hwmem)
    rw [this, map_one]
  have hspec := E0_spec
  have h11 : actNe (tabOf gensE 27) cGu oneC = true := hspec.2.2.2.2.2.2.2.2.2.2.1
  have h12 : actNe (tabOf gensE 27) cW0 oneC = true := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  have h13 : actNe (tabOf gensE 27) cW0 cGu = true := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h14 : (genB (invC cGu) && actNe (tabOf gensE 27) cW0 (invC cGu)) = true :=
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.2
  simp only [Bool.and_eq_true] at h14
  have h1 : (1 : Subgroup.normalizer (E0 : Set H6)).1 = elt oneC := one_eq_elt_oneC
  have hu1 : centerQuotientAction E0 e uN ≠ 1 := by
    rw [← map_one (centerQuotientAction E0 e)]
    exact act_ne e genB_cGu genB_oneC rfl h1 h11
  have hui : (uN⁻¹ : Subgroup.normalizer (E0 : Set H6)).1 = elt (invC cGu) :=
    (rep_elt_inv genB_cGu).eq (rep_elt (genB_isoB h14.1))
  have huw : centerQuotientAction E0 e wN ∉ Subgroup.zpowers (centerQuotientAction E0 e uN) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rcases zpow_cases_of_pow_three hu3 k with h | h | h
    · rw [h] at hk
      rw [← map_one (centerQuotientAction E0 e)] at hk
      exact act_ne e genB_cW0 genB_oneC rfl h1 h12 hk.symm
    · rw [h] at hk
      exact act_ne e genB_cW0 genB_cGu rfl rfl h13 hk.symm
    · rw [h, ← map_inv] at hk
      exact act_ne e genB_cW0 h14.1 rfl hui h14.2 hk.symm
  have hclos : Subgroup.closure ({centerQuotientAction E0 e uN, centerQuotientAction E0 e wN} :
      Set (GL (Fin 2) (ZMod 3))) = StatedSL 2 (ZMod 3) :=
    CFSG.RankThree.SubgroupLists.closure_pair_eq_statedSL _ _ hu3 hu1 hw3 huw
  rw [← hclos, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨uN, Subgroup.mem_subgroupOf.2 huL, rfl⟩
  · exact ⟨wN, Subgroup.mem_subgroupOf.2 hwL, rfl⟩

theorem hasKlingenData_of_not_le [Fact (Nat.Prime 3)]
    {X₀ : Subgroup H6} (hD : ¬ Subgroup.normalizer (D0 : Set H6) ≤ X₀) (hL : ¬ L0 ≤ X₀) :
    HasKlingenData 3 T0S X₀ := by
  obtain ⟨e, he⟩ := exists_e_SL
  refine ⟨E0, D0, L0, ?_, card_E0, pow_three_E0, card_center_E0, D0_le_E0, D0_elemAbelian,
    card_D0, ?_, hD, L0_le_centralizer, hL, e, he⟩
  · rw [coe_T0S]
    exact E0_le_T0
  · have hset : ((T0S : Set H6)) = (T0 : Set H6) := by rw [← coe_T0S]; rfl
    rw [hset]
    exact D0_centralizes_T0

theorem sp62_tables_large :
    chkWD = true ∧ chkWL = true ∧ chkV = true :=
  Certificates.certificate9441

theorem tabCheck_WD : tabCheck gensWD 51840 propWD = true :=
  sp62_tables_large.1

theorem tabCheck_WL : tabCheck gensWL 51840 propWL = true :=
  sp62_tables_large.2.1

theorem tabCheck_V : tabCheck gensV 25920 propV = true :=
  sp62_tables_large.2.2

theorem WD_spec :
    propWD1 (tabOf gensWD 51840) = true ∧ propWD2 (tabOf gensWD 51840) = true ∧
      propWD3 (tabOf gensWD 51840) = true ∧ propWD4 (tabOf gensWD 51840) = true := by
  simpa only [propWD, Bool.and_eq_true] using (tabCheck_spec tabCheck_WD).2.2.2.1

theorem V_spec :
    propV1 (tabOf gensV 25920) = true ∧ propV2 (tabOf gensV 25920) = true := by
  simpa only [propV, Bool.and_eq_true] using (tabCheck_spec tabCheck_V).2.2.2.1

theorem card_W0 : Nat.card W0 = 51840 :=
  (tabCheck_spec tabCheck_WD).2.2.1

theorem card_V0 : Nat.card V0 = 25920 :=
  (tabCheck_spec tabCheck_V).2.2.1

theorem V0_le_W0 : V0 ≤ W0 := by
  have h := WD_spec.1
  simp only [propWD1, List.all_eq_true] at h
  exact Hgen_le_of_inTab tabCheck_WD (tabCheck_spec tabCheck_V).2.2.2.2
    (fun c hc => inTab_iff.1 (h c hc))

theorem W0_le_Hgen_WL : W0 ≤ Hgen gensWL := by
  have h := (tabCheck_spec tabCheck_WL).2.2.2.1
  simp only [propWL, List.all_eq_true] at h
  exact Hgen_le_of_inTab tabCheck_WL (tabCheck_spec tabCheck_WD).2.2.2.2
    (fun c hc => inTab_iff.1 (h c hc))

theorem T0_le_V0 : T0 ≤ V0 := by
  have h := V_spec.1
  simp only [propV1, List.all_eq_true] at h
  exact Hgen_le_of_inTab tabCheck_V (tabCheck_spec tabCheck_T).2.2.2.2
    (fun c hc => inTab_iff.1 (h c hc))

theorem W0_le_normalizer_V0 :
    W0 ≤ Subgroup.normalizer (V0 : Set H6) := by
  have h := V_spec.2
  simp only [propV2, List.all_eq_true, Bool.and_eq_true] at h
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, rfl⟩
  exact elt_mem_normalizer_Hgen tabCheck_V (h c hc).1 fun x hx => inTab_iff.1 ((h c hc).2 x hx)

theorem W0_inf_centralizer_V0 :
    W0 ⊓ Subgroup.centralizer (V0 : Set H6) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxW, hxC⟩
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_WD hxW
  have h3 := forall_of_allCheck WD_spec.2.2.1 t ht
  have hcomm := commB_gens_of_centralizes (tabCheck_spec tabCheck_V).2.2.2.2 hrep hxC
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h3
  rcases h3 with h3 | h3
  · exact absurd hcomm (by simp [h3])
  · rw [Subgroup.mem_bot]
    exact hrep.eq_one_iff.2 h3

theorem W0_inf_centralizer_T0_le :
    W0 ⊓ Subgroup.centralizer (T0 : Set H6) ≤ T0 := by
  rintro x ⟨hxW, hxC⟩
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_WD hxW
  have h4 := forall_of_allCheck WD_spec.2.2.2 t ht
  have hcomm := commB_gens_of_centralizes (tabCheck_spec tabCheck_T).2.2.2.2 hrep hxC
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h4
  rcases h4 with h4 | h4
  · exact absurd hcomm (by simp [h4])
  · exact mem_Hgen_of_rep tabCheck_T (inTab_iff.1 h4) hrep

theorem W0_le_of_not_klingen
    [Fact (Nat.Prime 3)] {X₀ : Subgroup H6}
    (hN : Subgroup.normalizer (B0 : Set H6) ≤ X₀) (hK : ¬ HasKlingenData 3 T0S X₀) :
    W0 ≤ X₀ := by
  have hgensN : ∀ c ∈ gensN, elt c ∈ X₀ := fun c hc => hN (elt_mem_normalizer_B0 hc)
  have hWD : gensWD = gensN ++ [cGD] := rfl
  have hWL : gensWL = gensN ++ [cGu] := rfl
  by_cases hD : Subgroup.normalizer (D0 : Set H6) ≤ X₀
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [hWD, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hgensN c hc
    · exact hD elt_gD_mem_normalizer_D0
  · by_cases hL : L0 ≤ X₀
    · refine W0_le_Hgen_WL.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨c, hc, rfl⟩
      rw [hWL, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hgensN c hc
      · exact hL (elt_mem_Hgen (c := cGu) (by simp))
    · exact absurd (hasKlingenData_of_not_le hD hL) hK

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
