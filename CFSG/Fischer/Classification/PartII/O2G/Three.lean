module

public import CFSG.Fischer.Classification.PartII.O2G.ThreeMono
public import CFSG.Fischer.Classification.PartII.O2G.Two
public import CFSG.Fischer.Classification.SRG.Pair

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin LocalR3

namespace O2G

variable {G : Type} [Group G] {D : Set G}

theorem hasNormalPSubgroup_of_mulEquiv {A B : Type} [Group A] [Group B] (φ : A ≃* B) {p : ℕ}
    (h : HasNormalPSubgroup p B) : HasNormalPSubgroup p A := by
  obtain ⟨N, hN, hne, hp⟩ := h
  refine ⟨N.comap φ.toMonoidHom, hN.comap _, fun hbot => hne ?_,
    hp.comap_of_injective _ φ.injective⟩
  rw [eq_bot_iff]
  intro x hx
  have hmem : φ.symm x ∈ N.comap φ.toMonoidHom := by
    show φ (φ.symm x) ∈ N
    rwa [MulEquiv.apply_symm_apply]
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply φ x, hmem, map_one]

theorem hasNormalPSubgroup_localQuotient (hP : Pair G D) {d m : G} (hd : d ∈ D) (hm : m ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) :
    HasNormalPSubgroup 2 (LocalQuotient D m) := by
  obtain ⟨φ, hφE, hφm⟩ := Pair.exists_mulEquiv hP hm hd
  exact hasNormalPSubgroup_of_mulEquiv (localQuotientCongr φ hφE hφm) h2

theorem twinClass_conj_eq (hP : Pair G D) (g m x : G) :
    twinClass (LocalClass D (g * m * g⁻¹)) (g * x * g⁻¹) =
      (fun y => g * y * g⁻¹) '' twinClass (LocalClass D m) x := by
  ext y
  refine ⟨fun hy => ⟨g⁻¹ * y * g, ?_, by group⟩, ?_⟩
  · have h := LocalU.isTwin_conj hP g⁻¹ hy
    rwa [show g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m by group,
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group,
      show g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g by group] at h
  · rintro ⟨z, hz, rfl⟩
    exact LocalU.isTwin_conj hP g hz

theorem ncard_twinClass_eq_of_mem (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d m a x : G} (hd : d ∈ D) (hm : m ∈ D)
    (ha : a ∈ LocalClass D d) (hx : x ∈ LocalClass D m) :
    (twinClass (LocalClass D m) x).ncard = (twinClass (LocalClass D d) a).ncard := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hm hd)
  have hx' : g * x * g⁻¹ ∈ LocalClass D d := by
    rw [← hg]
    exact (Pair.conj_mem_localClass_iff hP g).2 hx
  rw [← ncard_twinClass_eq hP hZ hS hd hx' ha, ← hg, twinClass_conj_eq hP,
    Set.ncard_image_of_injective _ (conj_injective g)]

theorem ncard_twinClass_sdiff {H : Type} [Group H] [Finite H] {E μ : Set H}
    (hμ : O2Mod.IsTwinSection E μ) {a : H} (ha : a ∈ E) :
    (twinClass E a \ μ).ncard = (twinClass E a).ncard - 1 := by
  have hint : twinClass E a ∩ μ = {O2Mod.sec E μ a} := by
    ext s
    refine ⟨fun hs => hμ.eq_sec hs.2 hs.1, fun hs => ?_⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨hμ.isTwin_sec ha, hμ.sec_mem ha⟩
  rw [← Set.sdiff_self_inter, Set.ncard_sdiff Set.inter_subset_left, hint, Set.ncard_singleton]

theorem three_dvd_of_affine_star (hH : Hyp G D) (hna : NonabelianCommutator G) {d a m u v w : G}
    (hd : d ∈ D) (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) (ha : a ∈ LocalClass D d)
    (hm : m ∈ D) (hu : u ∈ LocalClass D m) (hv : v ∈ LocalClass D m) (hw : w ∈ LocalClass D m)
    (huv : u * v ≠ v * u) (hvw : v * w ≠ w * v) (huw : u * w ≠ w * u)
    (hc : w * (u * v * u) ≠ u * v * u * w) :
    3 ∣ (twinClass (LocalClass D d) a).ncard - 1 := by
  have hP := hH.pair
  have hZ := hH.center
  have hS := hH.simple
  have h2m := hasNormalPSubgroup_localQuotient hP hd hm h2
  have hPH := Pair.pair_localQuotient hP hZ hS hna hm
  have := Pair.finite hPH
  have hι := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hm)
  obtain ⟨y, hy, hym⟩ := O2Twin.exists_not_commute_of_mem hP hZ hm
  have hO := o2_O1 hH hna hm h2m hy fun e => hym e.symm
  have hμ := O2Bridge.isTwinSection_image hP hZ hS hm hO.1 hO.2
  have huvu : u * v * u ∈ LocalClass D m := Pair.mul_mul_mem_localClass_of_mem hP hu hv
  have hmain := hμ.three_dvd_ncard_of_affine hPH (hι.mem hu) (hι.mem hv) (hι.mem hw)
    (fun e => huv ((hι.comm_iff u hu v hv).2 e)) (fun e => hvw ((hι.comm_iff v hv w hw).2 e))
    (fun e => huw ((hι.comm_iff u hu w hw).2 e))
    (by
      rw [← LocalU.lqMap_mul_mul hu hv]
      exact fun e => hc ((hι.comm_iff w hw _ huvu).2 e))
  rwa [ncard_twinClass_sdiff hμ (hι.mem hu), ncard_twinClass_lqMap hP hZ hS hm hu,
    ncard_twinClass_eq_of_mem hP hZ hS hd hm ha hu] at hmain

theorem four_or_three_dvd_of_coclique (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hs : ¬ IsSymplecticType D) {d a x : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) (ha : a ∈ LocalClass D d) (hx : x ∈ D)
    (hxd : x * d ≠ d * x) (h3 : (muSet D d x).ncard = 3)
    (hcoc : ∀ s ∈ muSet D d x, ∀ t ∈ muSet D d x, s * t = t * s → s = t) :
    (twinClass (LocalClass D d) a).ncard = 4 ∨ 3 ∣ (twinClass (LocalClass D d) a).ncard - 1 := by
  have hP := hH.pair
  have hZ := hH.center
  have hS := hH.simple
  have := Pair.finite hP
  have hne2 := o2_r_ne_two hH hna hs hd h2 ha
  obtain ⟨r, hr⟩ : ∃ r, (twinClass (LocalClass D d) a).ncard = r := ⟨_, rfl⟩
  rw [hr]
  change (twinClass (LocalClass D d) a).ncard ≠ 2 at hne2
  rw [hr] at hne2
  have hO := o2_O1 hH hna hd h2 hx hxd
  have hμ : O2Mod.IsTwinSection (LocalClass D d) (muSet D d x) :=
    ⟨fun s hs => hs.1, fun s hs t ht => ⟨Pair.mul_mul_mem_localClass_of_mem hP hs.1 ht.1,
      Pair.mul_mul_mem_localClass_of_mem hP hs.2 ht.2⟩, hO.2, hO.1⟩
  have hrall : ∀ b ∈ LocalClass D d, (twinClass (LocalClass D d) b).ncard = r := fun b hb => by
    rw [← hr]
    exact ncard_twinClass_eq hP hZ hS hd hb ha
  have hr1 : 1 ≤ r := by
    rw [← hr]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨a, self_mem_twinClass ha⟩
  have hk : (LocalClass D d).ncard = r * 3 := by
    rw [← h3]
    refine O2Bridge.ncard_eq_mul_of_fibres (Set.toFinite _) (Set.toFinite _)
      (f := O2Mod.sec (LocalClass D d) (muSet D d x)) (fun b hb => hμ.sec_mem hb)
      fun s hs => ?_
    rw [← hrall s (hμ.subset hs)]
    congr 1
    ext b
    refine ⟨fun hb => ?_, fun hb => ⟨hb.2.1, ?_⟩⟩
    · rw [mem_twinClass, ← hb.2]
      exact isTwin_symm (hμ.isTwin_sec hb.1)
    · rw [hμ.sec_eq_sec (isTwin_symm hb), hμ.sec_eq_self hs]
  have hlam : LocalClass D d ∩ LocalClass D a = twinClass (LocalClass D d) a \ {a} := by
    ext y
    constructor
    · rintro ⟨hy, hya⟩
      refine ⟨?_, hya.2.1⟩
      have hsy := hμ.isTwin_sec hy
      have hsa := hμ.isTwin_sec ha
      have h1 := (hsy.2.2.2 a ha).1 hya.2.2.symm
      have h1' := (hsa.2.2.2 _ hsy.2.1).1 h1.symm
      have heq := hcoc _ (hμ.sec_mem hy) _ (hμ.sec_mem ha) h1'
      exact isTwin_trans hsa (heq ▸ isTwin_symm hsy)
    · rintro ⟨hy, hya⟩
      exact ⟨hy.2.1, hy.2.1.1, hya, hy.2.2.1.symm⟩
  have hℓ : (LocalClass D d ∩ LocalClass D a).ncard = r - 1 := by
    rw [hlam, Set.ncard_sdiff_singleton_of_mem (self_mem_twinClass ha), hr]
  have hfar : {f | f ∈ LocalClass D d ∧ f * a ≠ a * f}.ncard = 2 * r := by
    have h := O2Bridge.ncard_localClass_eq_ncard_inter_add hP ha
    rw [hk, hℓ] at h
    omega
  have hA : {c | c ∈ D ∧ c * d ≠ d * c}.ncard = 2 * r * r := by
    have h := O2Bridge.ncard_far_mul_ncard_muSet hH hna hd ha hx hxd
    rw [h3, hk, hfar] at h
    have h' : {c | c ∈ D ∧ c * d ≠ d * c}.ncard * 3 = 2 * r * r * 3 := by rw [h]; ring
    omega
  have hD : D.ncard = r * 3 + 1 + 2 * r * r := by
    rw [O2Bridge.ncard_eq_ncard_localClass_add hP hd, hk, hA]
  obtain ⟨f, g, hfg, hmult⟩ := Pair.exists_multiplicities_of_roots hH hna hd ha hx hxd hk hℓ h3
    (r := (r : ℤ) - 1) (s := -3) (by omega) (by rw [Nat.cast_sub hr1]; push_cast; ring)
    (by push_cast; ring)
  rw [hD] at hfg
  have hfgZ : (f : ℤ) + g = 3 * r + 2 * r * r := by
    have h' : f + g = r * 3 + 2 * r * r := by omega
    have h'' : ((f + g : ℕ) : ℤ) = ((r * 3 + 2 * r * r : ℕ) : ℤ) := by rw [h']
    push_cast at h''
    linarith
  push_cast at hmult
  have hkey : (f : ℤ) * (r + 2) = 6 * r * (r + 1) := by linear_combination hmult + 3 * hfgZ
  have hdvd : (r + 2 : ℤ) ∣ 12 :=
    ⟨f - 6 * r + 6, by linear_combination (-1 : ℤ) * hkey⟩
  have hle : (r : ℤ) + 2 ≤ 12 := Int.le_of_dvd (by norm_num) hdvd
  have hr10 : r ≤ 10 := by omega
  interval_cases r <;> omega

end O2G

open O2G

theorem o2_four_or_three_dvd {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : NonabelianCommutator G) (hs : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) {a : G} (ha : a ∈ LocalClass D d) :
    {b | LocalU.IsTwin (LocalClass D d) a b}.ncard = 4 ∨
      3 ∣ {b | LocalU.IsTwin (LocalClass D d) a b}.ncard - 1 := by
  have hP := hH.pair
  have hZ := hH.center
  have hS := hH.simple
  have := Pair.finite hP
  show (twinClass (LocalClass D d) a).ncard = 4 ∨ 3 ∣ (twinClass (LocalClass D d) a).ncard - 1
  have hs' := hs
  simp only [IsSymplecticType, not_forall, not_or] at hs'
  obtain ⟨a₀, ha₀, b₀, hb₀, z₀, hz₀, hab₀, hza₀, hzb₀, hzl₀⟩ := hs'
  have hza₀' : a₀ * z₀ ≠ z₀ * a₀ := fun e => hza₀ e.symm
  have hzb₀' : b₀ * z₀ ≠ z₀ * b₀ := fun e => hzb₀ e.symm
  set M := muSet D a₀ b₀ with hM
  have hMa : ∀ m ∈ M, m ∈ LocalClass D a₀ := fun m hm => hm.1
  by_cases hA : ∃ m ∈ M, m * z₀ = z₀ * m
  ·
    obtain ⟨m, hm, hmz⟩ := hA
    have hmD : m ∈ D := hm.1.1
    have ha₀m : a₀ ∈ LocalClass D m := ⟨ha₀, hm.1.2.1.symm, hm.1.2.2.symm⟩
    have hb₀m : b₀ ∈ LocalClass D m := ⟨hb₀, hm.2.2.1.symm, hm.2.2.2.symm⟩
    have hz₀m : z₀ ∈ LocalClass D m :=
      ⟨hz₀, fun e => hza₀ (by rw [e]; exact hm.1.2.2), hmz.symm⟩
    exact Or.inr (three_dvd_of_affine_star hH hna hd h2 ha hmD ha₀m hb₀m hz₀m hab₀ hzb₀'
      hza₀' hzl₀)
  simp only [not_exists, not_and] at hA
  have hcoc : ∀ s ∈ M, ∀ t ∈ M, s * t = t * s → s = t := by
    intro s hs t ht hst
    by_contra hne
    have hsD : s ∈ D := hs.1.1
    have h2s := hasNormalPSubgroup_localQuotient hP hd hsD h2
    have hzs : z₀ * s ≠ s * z₀ := fun e => hA s hs e.symm
    have hts : t ∈ LocalClass D s := ⟨ht.1.1, fun e => hne e.symm, hst.symm⟩
    obtain ⟨b, hb, htw⟩ := (o2_O1 hH hna hsD h2s hz₀ hzs).2 t hts
    have hbz : b * z₀ = z₀ * b := hb.2.2.2
    have hbM : b ∈ M := by
      have ha₀s : a₀ ∈ LocalClass D s := ⟨ha₀, hs.1.2.1.symm, hs.1.2.2.symm⟩
      have hb₀s : b₀ ∈ LocalClass D s := ⟨hb₀, hs.2.2.1.symm, hs.2.2.2.symm⟩
      refine ⟨⟨hb.1.1, fun e => hza₀ (by rw [← e]; exact hbz.symm), ?_⟩,
        ⟨hb.1.1, fun e => hzb₀ (by rw [← e]; exact hbz.symm), ?_⟩⟩
      · exact ((htw.2.2.2 a₀ ha₀s).1 ht.1.2.2.symm).symm
      · exact ((htw.2.2.2 b₀ hb₀s).1 ht.2.2.2.symm).symm
    exact hA b hbM hbz
  have hτ : ∀ s ∈ M, ∀ t ∈ M, s * t * s ∈ M := fun s hs t ht =>
    ⟨Pair.mul_mul_mem_localClass_of_mem hP hs.1 ht.1,
      Pair.mul_mul_mem_localClass_of_mem hP hs.2 ht.2⟩
  have h2a := hasNormalPSubgroup_localQuotient hP hd ha₀ h2
  have hOa := o2_O1 hH hna ha₀ h2a hb₀ fun e => hab₀ e.symm
  obtain ⟨f₀, hf₀⟩ : (LocalClass D a₀).Nonempty := by
    have hpos : 0 < (LocalClass D a₀).ncard := by
      rw [Pair.ncard_localClass_eq hP ha₀ hd]
      exact (Set.ncard_pos (Set.toFinite _)).2 ⟨a, ha⟩
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨m₁, hm₁, -⟩ := hOa.2 f₀ hf₀
  obtain ⟨g₀, hg₀, hg₀m⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS ha₀ (hMa m₁ hm₁)
  obtain ⟨m₂, hm₂, htw₂⟩ := hOa.2 g₀ hg₀
  have hm₁₂ : m₂ * m₁ ≠ m₁ * m₂ := fun e => hg₀m ((htw₂.2.2.2 m₁ (hMa m₁ hm₁)).2 e.symm).symm
  have hne₁₂ : m₁ ≠ m₂ := fun e => hm₁₂ (by rw [e])
  by_cases h4 : 4 ≤ M.ncard
  ·
    have hlt : ({m₁, m₂, m₁ * m₂ * m₁} : Set G).ncard < M.ncard := by
      have h1 := Set.ncard_insert_le m₁ ({m₂, m₁ * m₂ * m₁} : Set G)
      have h2' := Set.ncard_insert_le m₂ ({m₁ * m₂ * m₁} : Set G)
      have h3 := Set.ncard_singleton (m₁ * m₂ * m₁)
      omega
    obtain ⟨m₃, hm₃, hm₃n⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hm₃n
    obtain ⟨h31, h32, h33⟩ := hm₃n
    have hc13 : m₁ * m₃ ≠ m₃ * m₁ := fun e => h31 (hcoc _ hm₁ _ hm₃ e).symm
    have hc23 : m₂ * m₃ ≠ m₃ * m₂ := fun e => h32 (hcoc _ hm₂ _ hm₃ e).symm
    have hc3l : m₃ * (m₁ * m₂ * m₁) ≠ m₁ * m₂ * m₁ * m₃ := fun e =>
      h33 (hcoc _ hm₃ _ (hτ _ hm₁ _ hm₂) e)
    exact Or.inr (three_dvd_of_affine_star hH hna hd h2 ha ha₀ (hMa m₁ hm₁) (hMa m₂ hm₂)
      (hMa m₃ hm₃) (fun e => hm₁₂ e.symm) hc23 hc13 hc3l)
  ·
    have hM3 : M.ncard = 3 := by
      have hsub : ({m₁, m₂, m₁ * m₂ * m₁} : Set G) ⊆ M := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hm₁
        · exact hm₂
        · exact hτ _ hm₁ _ hm₂
      have hl := Pair.line_ne hP (hMa m₁ hm₁).1 (hMa m₂ hm₂).1 fun e => hm₁₂ e.symm
      have h3' : ({m₁, m₂, m₁ * m₂ * m₁} : Set G).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨hne₁₂, hl.2.1.symm⟩),
          Set.ncard_pair hl.2.2.1.symm]
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    obtain ⟨x, hx, hxd⟩ := O2Twin.exists_not_commute_of_mem hP hZ hd
    obtain ⟨g, hga, hgb⟩ := Pair.exists_conj_pair_of_not_commute hP hZ hS hna ha₀ hb₀ hd hx
      hab₀ hxd
    have himg : (fun s => g * s * g⁻¹) '' M = muSet D d x := by
      rw [hM, Pair.image_conj_muSet hP, hga, hgb]
    refine four_or_three_dvd_of_coclique hH hna hs hd h2 ha hx (fun e => hxd e.symm) ?_ ?_
    · rw [← himg, Set.ncard_image_of_injective _ (conj_injective g), hM3]
    · rw [← himg]
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
      rw [conj_commute_iff] at hst
      rw [hcoc s hs t ht hst]

end CFSG.Fischer.Classification
