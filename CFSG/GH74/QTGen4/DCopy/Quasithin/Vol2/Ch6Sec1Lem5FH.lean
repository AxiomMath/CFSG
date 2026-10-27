module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FG
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FH
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FGS432

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Family CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

namespace Cx615C

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

theorem false_of_b56Case5_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h5 : B56Case5 (ffJ (autI hU (borelL T L ⊔ H)))) : False := by
  classical
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, hdir, ⟨e₁⟩, -, -, h5ab⟩ := h5
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  set e : ↥G₁ ≃* GL32 := e₁.trans statedSLThreeTwoEquiv_ch615 with he
  have hsimple := isSimpleGroup_l32_ch615 e
  have hZ₁ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1 := fun g hg h =>
    eq_one_of_commute_l32_ch615 e hg h
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hBN : borelL T L ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_left.trans hXN
  have hTN : T ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    (c.hH.1.1.trans le_sup_right).trans hXN
  have hTsX : autI hU T ≤ autI hU (borelL T L ⊔ H) := autI_mono hU (c.hH.1.1.trans le_sup_right)
  have hTsY : autI hU T ≤ autI hU (borelL T L ⊔ T) := autI_mono hU le_sup_right
  have hDsY : autI hU D ≤ autI hU (borelL T L ⊔ T) := autI_mono hU (hD.1.trans le_sup_left)
  have hDsB : autI hU D ≤ autI hU (borelL T L) := autI_mono hU hD.1
  have hYsX : autI hU (borelL T L ⊔ T) ≤ autI hU (borelL T L ⊔ H) :=
    autI_mono hU (sup_le le_sup_left (c.hH.1.1.trans le_sup_right))
  have hYD : autI hU (borelL T L ⊔ T) ≤ autI hU D ⊔ autI hU T := by
    rw [autI_sup hU hBN hTN, ← c.hyp.toHyp5_0_1.borelL_eq_sup hD,
      autI_sup hU (hD.1.trans hBN) ((Hyp5_0_1.inf_le_borel T L).trans hBN)]
    exact sup_le (sup_le le_sup_left ((autI_mono hU inf_le_left).trans le_sup_right)) le_sup_right
  have hGsX : G₁ ⊔ G₂ ≤ autI hU (borelL T L ⊔ H) := hsup ▸ B6.ffJ_le _
  have hnorm : ∀ x ∈ autI hU (borelL T L ⊔ H),
      x ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup _) : Set (MulAut _)) := fun x hx =>
    hsup ▸ B6.le_normalizer_ffJ _ hx
  have hKG : autI hU (oTwoUpper H) ≤ G₁ ⊔ G₂ := hsup ▸ (c.le_ffJ_ch615 hU).2
  have hJG : autI hU (thompsonJ T) ≤ G₁ ⊔ G₂ := hsup ▸ (c.le_ffJ_ch615 hU).1
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have h3 : ∀ x ∈ autI hU (borelL T L), ∀ y ∈ autI hU (borelL T L), x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x → x ≠ 1 → y ∈ Subgroup.zpowers x :=
    fun x hx y hy hx3 hy3 hxy hx1 => c.mem_zpowers_of_autI_borelL_ch615 hU hx hy hx3 hy3 hxy hx1
  have hYB : ∀ y ∈ autI hU (borelL T L ⊔ T), Odd (orderOf y) → y ∈ autI hU (borelL T L) :=
    fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho
  have hYsolv := c.isSolvable_autI_ch615 hU
  have hGsn : ((G₁ ⊔ G₂).subgroupOf (autI hU (borelL T L ⊔ H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hGsX).mpr fun x hx => hnorm x hx
  have hP : IsSylowTwoOf (autI hU T ⊓ (G₁ ⊔ G₂)) (G₁ ⊔ G₂) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (c.isSylowTwoOf_autI_ch615 hU) hGsX
      hGsn.isSubnormal
  have hn₁ : (G₁.subgroupOf (G₁ ⊔ G₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le_normalizer_ch615 hcomm)
  have hn₂ : (G₂.subgroupOf (G₁ ⊔ G₂)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
    rw [sup_comm]
    exact sup_le_normalizer_ch615 hc'
  have hS : ∀ Gi : Subgroup (MulAut (IntMod (UX615 T L H) hU)), Gi ≤ G₁ ⊔ G₂ →
      (Gi.subgroupOf (G₁ ⊔ G₂)).Normal → IsSylowTwoOf (autI hU T ⊓ Gi) Gi := by
    intro Gi hGi hn
    have := RankOneRecog.isSylowTwoOf_inf_of_subnormal hP hGi hn.isSubnormal
    rwa [inf_assoc, inf_eq_right.mpr hGi] at this
  have hS₁ := hS G₁ le_sup_left hn₁
  have hnotc : ¬ (autI hU D ≤ Subgroup.centralizer (G₁ : Set (MulAut _)) ∧
      autI hU D ≤ Subgroup.centralizer (G₂ : Set (MulAut _))) := by
    rintro ⟨h1, h2⟩
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute_ch615 hcomm).mp (hKG hk)
    have hya := Subgroup.mem_centralizer_iff.mp (h1 hy) a ha
    have hyb := Subgroup.mem_centralizer_iff.mp (h2 hy) b hb
    have : y * (a * b) * y⁻¹ = a * b := by
      calc y * (a * b) * y⁻¹ = (y * a) * b * y⁻¹ := by group
        _ = (a * y) * b * y⁻¹ := by rw [hya]
        _ = a * (y * b) * y⁻¹ := by group
        _ = a * (b * y) * y⁻¹ := by rw [hyb]
        _ = a * b := by group
    rw [this]
    exact hk
  set g₄ : MulAut (IntMod (UX615 T L H) hU) := (e.symm (unitriGL 1 0 1)).1 with hg₄
  have hg₄G : g₄ ∈ G₁ := (e.symm (unitriGL 1 0 1)).2
  have hg₄4 : g₄ ^ 4 = 1 := by
    rw [hg₄, ← Subgroup.coe_pow, ← map_pow, unitriGL_pow_ch615.1, map_one, Subgroup.coe_one]
  have hg₄2 : g₄ ^ 2 ≠ 1 := fun h => unitriGL_pow_ch615.2 (by
    have h' : (e.symm (unitriGL 1 0 1) ^ 2 : ↥G₁) = 1 := Subtype.ext (by simpa [hg₄] using h)
    rw [← map_pow] at h'
    exact e.symm.injective (h'.trans (map_one _).symm))
  have hcase : (∃ e₂ : ↥G₂ ≃* GL32, True) ∨
      ∀ x ∈ autI hU (borelL T L ⊔ H), x ∈ Subgroup.normalizer (G₁ : Set (MulAut _)) := by
    rcases h5ab with ⟨⟨e₂⟩, -⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨e₂.trans statedSLThreeTwoEquiv_ch615, trivial⟩
    · right
      intro x hx
      rcases map_conj_eq_or_le_ch615 hcomm hsimple hZ₁ (hnorm x hx) with h | h
      · exact mem_normalizer_of_map_eq_ch615 h
      · exfalso
        refine not_pow_four_of_binaryNaturalSL_ch615 hm (h ⟨g₄, hg₄G, rfl⟩) ?_ ?_
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [conj_pow, hg₄4, mul_one, mul_inv_cancel]
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [conj_pow]
          intro h'
          apply hg₄2
          have := congrArg (fun y => x⁻¹ * y * x) h'
          simpa [mul_assoc] using this
  have hodd₁ : ∀ x ∈ autI hU (borelL T L ⊔ H), Odd (orderOf x) →
      x ∈ Subgroup.normalizer (G₁ : Set (MulAut _)) := by
    intro x hx hxo
    rcases hcase with ⟨e₂, -⟩ | hb
    · have hZ₂ : ∀ g ∈ G₂, (∀ y ∈ G₂, g * y = y * g) → g = 1 := fun g hg h =>
        eq_one_of_commute_l32_ch615 e₂ hg h
      rcases map_conj_eq_or_le_ch615 hcomm hsimple hZ₁ (hnorm x hx) with h | h
      · exact mem_normalizer_of_map_eq_ch615 h
      · have hcard : Nat.card G₂ ≤ Nat.card (G₁.map (MulAut.conj x).toMonoidHom) := by
          rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, card_l32_ch615 e,
            card_l32_ch615 e₂]
        have hmap : G₁.map (MulAut.conj x).toMonoidHom = G₂ := Subgroup.eq_of_le_of_card_ge h hcard
        have hmap2 := map_conj_le_of_swap_ch615 hcomm hZ₂ (hnorm x hx) hmap
        have hx2 : x ^ 2 ∈ Subgroup.normalizer (G₁ : Set (MulAut _)) := by
          refine mem_normalizer_of_conj_mem_l32_ch615 fun g hg => ?_
          have h1 : x * g * x⁻¹ ∈ G₂ := by
            rw [← hmap]
            exact ⟨g, hg, rfl⟩
          have h2 : x * (x * g * x⁻¹) * x⁻¹ ∈ G₁ := hmap2 ⟨_, h1, rfl⟩
          have e2 : x ^ 2 * g * (x ^ 2)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by
            rw [pow_two, mul_inv_rev]
            group
          rw [e2]
          exact h2
        obtain ⟨k, hk⟩ := hxo
        have ex : x = (x ^ 2) ^ (k + 1) := by
          rw [← pow_mul]
          calc x = x ^ orderOf x * x := by rw [pow_orderOf_eq_one, one_mul]
            _ = x ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
        rw [ex]
        exact Subgroup.pow_mem _ hx2 _
    · exact hb x hx
  have hDs₁ : autI hU D ≤ Subgroup.normalizer (G₁ : Set (MulAut _)) := fun d hd =>
    hodd₁ d (hYsX (hDsY hd)) (hDsodd d hd)
  have hDs₂ : autI hU D ≤ Subgroup.normalizer (G₂ : Set (MulAut _)) := fun d hd =>
    mem_normalizer_right_ch615 hcomm hZ₁ (hnorm d (hYsX (hDsY hd))) (hDs₁ hd)
  by_cases hsw : autI hU T ≤ Subgroup.normalizer (G₁ : Set (MulAut _))
  ·
    have hTs₂ : autI hU T ≤ Subgroup.normalizer (G₂ : Set (MulAut _)) := fun t ht =>
      mem_normalizer_right_ch615 hcomm hZ₁ (hnorm t (hTsX ht)) (hsw ht)
    have hTK : autI hU T ≤ Subgroup.normalizer (autI hU (oTwoUpper H) : Set (MulAut _)) := by
      have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
        c.hH.1.1.trans (le_normalizer_oTwoUpper H)
      intro y hy
      refine Subgroup.mem_normalizer_iff.mpr fun a =>
        ⟨fun ha => C124.autI_conj_mem hU hTK' y hy a ha, fun ha => ?_⟩
      have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy) _ ha
      simpa [mul_assoc] using this
    have hsplit : autI hU (oTwoUpper H) ≤
        (autI hU (oTwoUpper H) ⊓ G₁) ⊔ (autI hU (oTwoUpper H) ⊓ G₂) := by
      refine (c.le_commutator_ch615 hU).trans
        (commutator_le_sup_inf_ch615 hcomm (P := autI hU T ⊓ (G₁ ⊔ G₂)) hKG ?_
          (inf_le_left.trans hTK))
      exact (le_inf (autI_mono hU (thompsonJ_le_self T)) hJG).trans
        (le_sup_inf_of_isSylowTwoOf_ch615 hcomm hinf hP)
    have hor := c.le_or_le_ch615_F4 h331 hU (A := autI hU (oTwoUpper H) ⊓ G₁)
      (B := autI hU (oTwoUpper H) ⊓ G₂) inf_le_left inf_le_left
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK ht, hsw ht⟩)
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK ht, hTs₂ ht⟩)
      (fun k hk => (mem_sup_iff_of_commute_ch615 (fun a ha b hb =>
        hcomm a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)).mp (hsplit hk))
    have hK₁ : autI hU (oTwoUpper H) ≤ G₁ := by
      rcases hor with h | h
      · exact h.trans inf_le_right
      · exfalso
        apply not_isSolvable_l32_ch615 e
        refine c.isSolvable_of_centralizes_ch615 hU (le_sup_left.trans hGsX) ?_ ?_
        · exact hYD.trans (sup_le hDs₁ hsw)
        · intro k hk
          exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
            hcomm a ha k (Subgroup.mem_inf.mp (h hk)).2
    have hDc : ¬ autI hU D ≤ Subgroup.centralizer (G₁ : Set (MulAut _)) := fun h1 => by
      apply c.not_hall_normalizes_ch615 hU hD hN
      intro y hy k hk
      have := Subgroup.mem_centralizer_iff.mp (h1 hy) k (hK₁ hk)
      rw [← this, mul_inv_cancel_right]
      exact hk
    obtain ⟨d₃, hd₃D, hd₃G, hd₃1, -⟩ := exists_mem_of_not_le_centralizer_l32_ch615 e hS₁
      (inf_le_left.trans hTsY) hDsY hYsolv hDs₁ hDsodd hYB h3 hDc
    have hW₂ : commV G₂ ≠ ⊥ := by
      rcases h5ab with ⟨⟨e₂⟩, -⟩ | ⟨m, hm⟩
      · refine commV_ne_bot_ch615 fun hb => ?_
        have := card_l32_ch615 (e₂.trans statedSLThreeTwoEquiv_ch615)
        rw [hb, Subgroup.card_bot] at this
        omega
      · exact commV_ne_bot_of_binaryNaturalSL_ch615 hm
    obtain ⟨w, hwW, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU)
      hW₂ fun t ht w hw => mem_commV_of_conj_ch615
        (fun x hx => (Subgroup.mem_normalizer_iff.mp (hTs₂ ht) x).mp hx) hw
    have hG₁W : ∀ g ∈ G₁, g w = w := by
      intro g hg
      have h1 : g w * w⁻¹ ∈ commV G₁ := Subgroup.subset_closure ⟨g, hg, w, rfl⟩
      have h2 : g w * w⁻¹ ∈ commV G₂ :=
        (commV G₂).mul_mem (mem_commV_of_conj_ch615 (fun x hx => by
          rw [hcomm g hg x hx, mul_inv_cancel_right]; exact hx) hwW) ((commV G₂).inv_mem hwW)
      have h12 : g w * w⁻¹ ∈ commV G₁ ⊓ commV G₂ := ⟨h1, h2⟩
      rw [hdir.2, Subgroup.mem_bot, mul_inv_eq_one] at h12
      exact h12
    exact c.false_of_fix_ch615_F4 h432 hU hD hw1 hwT (fun k hk => hG₁W k (hK₁ hk)) hd₃D hd₃1
      (hG₁W d₃ hd₃G)
  ·
    obtain ⟨t, htT, htn⟩ := IsConcreteLE.not_le_iff_exists.mp hsw
    rcases hcase with ⟨e₂, -⟩ | hb
    · have hmap : G₁.map (MulAut.conj t).toMonoidHom = G₂ := by
        rcases map_conj_eq_or_le_ch615 hcomm hsimple hZ₁ (hnorm t (hTsX htT)) with h | h
        · exact absurd (mem_normalizer_of_map_eq_ch615 h) htn
        · refine Subgroup.eq_of_le_of_card_ge h ?_
          rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, card_l32_ch615 e,
            card_l32_ch615 e₂]
      have key : ∀ (Gi Gj : Subgroup (MulAut (IntMod (UX615 T L H) hU)))
          (s : MulAut (IntMod (UX615 T L H) hU)), s ∈ autI hU T → Gi ⊓ Gj = ⊥ →
          (∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a) → ∀ d ∈ autI hU D, d ∈ Gi → d ≠ 1 →
          d ^ 3 = 1 → s * d * s⁻¹ ∈ Gj → False := by
        intro Gi Gj s hs hij hcij d hdD hdG hd1 hd3 hsd
        have hsdY : s * d * s⁻¹ ∈ autI hU (borelL T L ⊔ T) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTsY hs) (hDsY hdD))
            (Subgroup.inv_mem _ (hTsY hs))
        have hsd3 : (s * d * s⁻¹) ^ 3 = 1 := by rw [conj_pow, hd3, mul_one, mul_inv_cancel]
        have hsdo : Odd (orderOf (s * d * s⁻¹)) :=
          Odd.of_dvd_nat (by norm_num) (orderOf_dvd_of_pow_eq_one hsd3)
        have hz := h3 d (hDsB hdD) _ (hYB _ hsdY hsdo) hd3 hsd3 (hcij d hdG _ hsd) hd1
        have hzG : s * d * s⁻¹ ∈ Gi := (Subgroup.zpowers_le.mpr hdG) hz
        have h1 : s * d * s⁻¹ = 1 := by
          have : s * d * s⁻¹ ∈ Gi ⊓ Gj := ⟨hzG, hsd⟩
          rwa [hij, Subgroup.mem_bot] at this
        apply hd1
        have := congrArg (fun y => s⁻¹ * y * s) h1
        simpa [mul_assoc] using this
      by_cases hc1 : autI hU D ≤ Subgroup.centralizer (G₁ : Set (MulAut _))
      · have hc2 : ¬ autI hU D ≤ Subgroup.centralizer (G₂ : Set (MulAut _)) := fun hc2 =>
          hnotc ⟨hc1, hc2⟩
        obtain ⟨d₃, hd₃D, hd₃G, hd₃1, hd₃3⟩ := exists_mem_of_not_le_centralizer_l32_ch615 e₂
          (hS G₂ le_sup_right hn₂) (inf_le_left.trans hTsY) hDsY hYsolv hDs₂ hDsodd hYB h3 hc2
        refine key G₂ G₁ t⁻¹ ((autI hU T).inv_mem htT) (by rw [inf_comm]; exact hinf) hc' d₃
          hd₃D hd₃G hd₃1 hd₃3 ?_
        have hd₃G' := hd₃G
        rw [← hmap] at hd₃G'
        obtain ⟨a, ha, hae⟩ := hd₃G'
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae
        rw [← hae, inv_inv]
        simpa [mul_assoc] using ha
      · obtain ⟨d₃, hd₃D, hd₃G, hd₃1, hd₃3⟩ := exists_mem_of_not_le_centralizer_l32_ch615 e hS₁
          (inf_le_left.trans hTsY) hDsY hYsolv hDs₁ hDsodd hYB h3 hc1
        refine key G₁ G₂ t htT hinf hcomm d₃ hd₃D hd₃G hd₃1 hd₃3 ?_
        rw [← hmap]
        exact ⟨d₃, hd₃G, rfl⟩
    · exact htn (hb t (hTsX htT))

end Cx615C

theorem res615EFF_of_cases134_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (hB56 : AsB56)
    (hcases : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H : Subgroup G) (n : ℕ),
      Cx615C G T M L V H n → ∀ hU : IsElemAbelian 2 (UX615 T L H),
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) →
      (B56Case1 (ffJ (autI hU (borelL T L ⊔ H))) ∨ B56Case3 (ffJ (autI hU (borelL T L ⊔ H))) ∨
        B56Case4 (ffJ (autI hU (borelL T L ⊔ H)))) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)) :
    Res615EFF_F4 :=
  res615EFF_of_cases_F4 hB56 fun G _ _ T M L V H n c hU hN h => by
    rcases h with h1 | h3 | h4 | h5
    · exact hcases G T M L V H n c hU hN (Or.inl h1)
    · exact hcases G T M L V H n c hU hN (Or.inr (Or.inl h3))
    · exact hcases G T M L V H n c hU hN (Or.inr (Or.inr h4))
    · exact (c.false_of_b56Case5_ch615_F4 h331 h432 hU hN h5).elim

end CFSG.Quasithin.H13
