module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenBlocks

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2
  CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}
  {H T M : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem autI_baum_gen (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    autI hV (baum T) = autI hV (thompsonJ T) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hT := h.isSylow
  refine le_antisymm (fun x hx => ?_) (autI_mono hV (thompsonJ_le_baum T))
  have hxH : x ∈ autI hV H := autI_mono hV (inf_le_left.trans hT.1) hx
  have hex : ∀ L, ∃ t : MulAut (IntMod V hV), L ∈ I →
      t ∈ L ∧ t ∈ autI hV (thompsonJ T) ∧ orderOf t = 2 := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨t, htL, -, htJ, ht2⟩ := B.exists_orderOf_eq_two hred hT hL
      exact ⟨t, fun _ => ⟨htL, htJ, ht2⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose t ht using hex
  have hexc : ∀ L, ∃ c : IntMod V hV, L ∈ I → c ∈ commSub ⊤ L ∧ c ≠ 1 ∧ t L c = c := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨c, hc, hc1, htc⟩ := B.exists_fix hL (ht L hL).1 (ht L hL).2.2
      exact ⟨c, fun _ => ⟨hc, hc1, htc⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose c hc using hexc
  have hJTeq := B.autI_thompsonJ_eq hT hsolv hred hJ t (fun L hL => ht L hL)
  have hcfix : ∀ L ∈ I, c L ∈ fixV (autI hV (thompsonJ T)) := by
    intro L hL y hy
    rw [hJTeq] at hy
    have hle : (⨆ L' ∈ I, Subgroup.zpowers (t L')) ≤
        MulAction.stabilizer (MulAut (IntMod V hV)) (c L) := by
      refine iSup₂_le fun L' hL' => Subgroup.zpowers_le.2 ?_
      rw [MulAction.mem_stabilizer_iff]
      by_cases hLL : L' = L
      · subst hLL
        exact (hc L' hL).2.2
      · exact B.hb.triv L' (B.sub hL') L (B.sub hL) hLL (t L') (ht L' hL').1 (c L) (hc L hL).1
    exact hle hy
  have hxc : ∀ L ∈ I, x (c L) = c L := fun L hL => baum_fix hred hT hx (hcfix L hL)
  have hloc : ∀ L ∈ I, ∃ l ∈ Subgroup.zpowers (t L),
      ∀ u ∈ commSub (⊤ : Subgroup (IntMod V hV)) L, x u = l u := fun L hL =>
    B.exists_local hL hxH (ht L hL).1 (ht L hL).2.2 (hc L hL).1 (hc L hL).2.1 (hc L hL).2.2
      (hxc L hL)
  have hJTJH : autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
    autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
  have hxC : ∀ u ∈ fixV (autI hV (thompsonJ H)), x u = u := fun u hu =>
    baum_fix hred hT hx (B1.fixV_le_fixV hJTJH hu)
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq] at hdec
  have key : ∀ J : Finset (Subgroup (MulAut (IntMod V hV))), J ⊆ I →
      ∃ l ∈ ⨆ L ∈ J, Subgroup.zpowers (t L),
        ∀ u ∈ ⨆ L ∈ J, commSub (⊤ : Subgroup (IntMod V hV)) L, x u = l u := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, Subgroup.one_mem _, fun u hu => ?_⟩
      have hu1 : u = 1 := by simpa using hu
      subst hu1
      simp
    | insert L₀ J hL₀J ih =>
      intro hJI
      have hL₀I : L₀ ∈ I := hJI (Finset.mem_insert_self _ _)
      have hJI' : J ⊆ I := fun y hy => hJI (Finset.mem_insert_of_mem hy)
      obtain ⟨l, hl, hxl⟩ := ih hJI'
      obtain ⟨l₀, hl₀, hxl₀⟩ := hloc L₀ hL₀I
      have hl₀L : l₀ ∈ L₀ := Subgroup.zpowers_le.2 (ht L₀ hL₀I).1 hl₀
      have hlfix : ∀ v ∈ commSub (⊤ : Subgroup (IntMod V hV)) L₀, l v = v := by
        have hle : (⨆ L ∈ J, Subgroup.zpowers (t L)) ≤
            fixPt (commSub (⊤ : Subgroup (IntMod V hV)) L₀) := by
          refine iSup₂_le fun L hL => Subgroup.zpowers_le.2 fun v hv => ?_
          exact B.hb.triv L (B.sub (hJI' hL)) L₀ (B.sub hL₀I) (fun he => hL₀J (he ▸ hL)) (t L)
            (ht L (hJI' hL)).1 v hv
        exact hle hl
      have hl₀fix : ∀ u ∈ ⨆ L ∈ J, commSub (⊤ : Subgroup (IntMod V hV)) L, l₀ u = u := by
        have hle : (⨆ L ∈ J, commSub (⊤ : Subgroup (IntMod V hV)) L) ≤
            fixV (Subgroup.zpowers l₀) := by
          refine iSup₂_le fun L hL v hv y hy => ?_
          exact B.hb.triv L₀ (B.sub hL₀I) L (B.sub (hJI' hL)) (fun he => hL₀J (he ▸ hL)) y
            (Subgroup.zpowers_le.2 hl₀L hy) v hv
        exact fun u hu => hle hu l₀ (Subgroup.mem_zpowers l₀)
      rw [Finset.iSup_insert, Finset.iSup_insert]
      refine ⟨l * l₀, Subgroup.mul_mem _ (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left hl₀),
        fun u hu => ?_⟩
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hu
      rw [map_mul, hxl₀ u₁ hu₁, hxl u₂ hu₂, MulAut.mul_apply, map_mul, map_mul,
        hl₀fix u₂ hu₂, hlfix (l₀ u₁) (B.hb.stab L₀ (B.sub hL₀I) l₀ hl₀L u₁ hu₁)]
  obtain ⟨l, hl, hxl⟩ := key I le_rfl
  rw [← hJTeq] at hl
  have hlJ : l ∈ autI hV (thompsonJ H) := hJTJH hl
  have hxeq : x = l := by
    refine MulEquiv.ext fun u => ?_
    have hu : u ∈ fixV (autI hV (thompsonJ H)) ⊔ ⨆ L ∈ I, commSub ⊤ L := by
      rw [hdec.1]
      exact Subgroup.mem_top u
    obtain ⟨c', hc', w, hw, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [map_mul, map_mul, hxC c' hc', hxl w hw, hc' l hlJ]
  rw [hxeq]
  exact hl

theorem exists_twoResidual_le_gen (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set G) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T) := by
  classical
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  obtain ⟨gs, hgsK, hgsL⟩ : ∃ gs ∈ autI hV (twoResidual H), ∀ L ∈ I,
      L ≤ autI hV (thompsonJ T) ⊔ (autI hV (thompsonJ T)).map (MulAut.conj gs).toMonoidHom := by
    have hloc : ∀ {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) {t f : MulAut (IntMod V hV)},
        t ∈ L → t ∈ autI hV (thompsonJ T) → orderOf t = 2 → f ∈ L → orderOf f = 3 →
        ∀ gs : MulAut (IntMod V hV), gs * t * gs⁻¹ = f * t * f⁻¹ →
          L ≤ autI hV (thompsonJ T) ⊔
            (autI hV (thompsonJ T)).map (MulAut.conj gs).toMonoidHom := by
      intro L hL t f htL htJ ht2 hfL hf3 gs hgs
      obtain ⟨hcL, hc2, hne⟩ := B.conj_ne hL htL hfL ht2 hf3
      refine (B.le_sup_zpowers hL htL hcL ht2 hc2 hne).trans (sup_le_sup
        (Subgroup.zpowers_le.2 htJ) (Subgroup.zpowers_le.2 ?_))
      rw [← hgs]
      exact ⟨t, htJ, rfl⟩
    have hex2 : ∀ L, ∃ t : MulAut (IntMod V hV), L ∈ I →
        t ∈ L ∧ t ∈ autI hV (thompsonJ T) ∧ orderOf t = 2 := by
      intro L
      by_cases hL : L ∈ I
      · obtain ⟨t, htL, -, htJ, ht2⟩ := B.exists_orderOf_eq_two hred hT hL
        exact ⟨t, fun _ => ⟨htL, htJ, ht2⟩⟩
      · exact ⟨1, fun h' => absurd h' hL⟩
    choose t ht using hex2
    have hex3 : ∀ L, ∃ f : MulAut (IntMod V hV), L ∈ I →
        f ∈ L ∧ f ∈ autI hV (twoResidual H) ∧ orderOf f = 3 := by
      intro L
      by_cases hL : L ∈ I
      · obtain ⟨f, hfL, hfK, hf3⟩ := B.exists_orderOf_eq_three hL
        exact ⟨f, fun _ => ⟨hfL, hfK, hf3⟩⟩
      · exact ⟨1, fun h' => absurd h' hL⟩
    choose f hf using hex3
    have key : ∀ J : Finset (Subgroup (MulAut (IntMod V hV))), J ⊆ I →
        ∃ gs ∈ ⨆ L ∈ J, (L ⊓ autI hV (twoResidual H)),
          ∀ L ∈ J, gs * t L * gs⁻¹ = f L * t L * (f L)⁻¹ := by
      intro J
      induction J using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨1, Subgroup.one_mem _, fun L hL => absurd hL (Finset.notMem_empty L)⟩
      | insert L₀ J hL₀J ih =>
        intro hJI
        have hL₀I : L₀ ∈ I := hJI (Finset.mem_insert_self _ _)
        have hJI' : J ⊆ I := fun y hy => hJI (Finset.mem_insert_of_mem hy)
        obtain ⟨gs, hgs, hgse⟩ := ih hJI'
        have hcentr : gs ∈ Subgroup.centralizer (L₀ : Set (MulAut (IntMod V hV))) := by
          have hle : (⨆ L ∈ J, (L ⊓ autI hV (twoResidual H))) ≤
              Subgroup.centralizer (L₀ : Set (MulAut (IntMod V hV))) := by
            refine iSup₂_le fun L hL => inf_le_left.trans fun a ha => ?_
            have hne : L₀ ≠ L := fun he => hL₀J (he ▸ hL)
            exact Subgroup.mem_centralizer_iff.2 fun b hb =>
              (B.comm hL₀I (hJI' hL) hne hb ha)
          exact hle hgs
        rw [Finset.iSup_insert]
        refine ⟨gs * f L₀, Subgroup.mul_mem _ (Subgroup.mem_sup_right hgs)
          (Subgroup.mem_sup_left ⟨(hf L₀ hL₀I).1, (hf L₀ hL₀I).2.1⟩), fun L hL => ?_⟩
        rcases Finset.mem_insert.1 hL with rfl | hLJ
        · have hmem : f L * t L * (f L)⁻¹ ∈ L :=
            L.mul_mem (L.mul_mem (hf L hL₀I).1 (ht L hL₀I).1) (L.inv_mem (hf L hL₀I).1)
          have hc := Subgroup.mem_centralizer_iff.1 hcentr _ hmem
          calc gs * f L * t L * (gs * f L)⁻¹ = gs * (f L * t L * (f L)⁻¹) * gs⁻¹ := by group
            _ = (f L * t L * (f L)⁻¹) * gs * gs⁻¹ := by rw [← hc]
            _ = f L * t L * (f L)⁻¹ := by group
        · have hne : L₀ ≠ L := fun he => hL₀J (he ▸ hLJ)
          have hcomm : f L₀ * t L = t L * f L₀ :=
            B.comm hL₀I (hJI' hLJ) hne (hf L₀ hL₀I).1 (ht L (hJI' hLJ)).1
          calc gs * f L₀ * t L * (gs * f L₀)⁻¹ = gs * (f L₀ * t L) * (f L₀)⁻¹ * gs⁻¹ := by group
            _ = gs * (t L * f L₀) * (f L₀)⁻¹ * gs⁻¹ := by rw [hcomm]
            _ = gs * t L * gs⁻¹ := by group
            _ = f L * t L * (f L)⁻¹ := hgse L hLJ
    obtain ⟨gs, hgs, hgse⟩ := key I le_rfl
    refine ⟨gs, (iSup₂_le fun L _ => inf_le_right : (⨆ L ∈ I, (L ⊓ autI hV (twoResidual H))) ≤
      autI hV (twoResidual H)) hgs, fun L hL => ?_⟩
    exact hloc hL (ht L hL).1 (ht L hL).2.1 (ht L hL).2.2 (hf L hL).1 (hf L hL).2.2 gs (hgse L hL)
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hgsK
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := g.2
  set I₀ := thompsonJ T ⊔ cjSub (g : G) (thompsonJ T) with hI₀
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hT.1
  have hI₀H : I₀ ≤ H := by
    refine sup_le hJTH fun z hz => ?_
    rw [mem_cjSub] at hz
    have := H.mul_mem (H.mul_mem (hKH hgK) (hJTH hz)) (H.inv_mem (hKH hgK))
    simpa [mul_assoc] using this
  have hKI : autI hV (twoResidual H) ≤ autI hV I₀ := by
    rw [hI₀, autI_sup hV ((thompsonJ_le_self T).trans (hT.1.trans hHN))
      (fun z hz => hHN (hI₀H (Subgroup.mem_sup_right hz))), ← autI_cjSub hV hgN]
    calc autI hV (twoResidual H) ≤ autI hV (thompsonJ H) :=
          autI_mono hV (twoResidual_le_thompsonJ h hred hJ)
      _ = ⨆ L ∈ I, L := B.eq
      _ ≤ _ := iSup₂_le fun L hL => hgsL L hL
  have hKIJ : twoResidual H ≤ I₀ ⊔ kerIn M H := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := hHN (hKH hk)
    obtain ⟨i, hiI, hik⟩ := (mem_autI hV).1 (hKI (convI_mem_autI hV hk hkN))
    have hc : (i : G)⁻¹ * k ∈ Subgroup.centralizer (V : Set G) := by
      have := (convI_eq_one_iff hV (i⁻¹ * ⟨k, hkN⟩)).1 (by rw [map_mul, map_inv, hik,
        inv_mul_cancel])
      simpa using this
    have hiH : (i : G) ∈ H := hI₀H hiI
    have hcJ : (i : G)⁻¹ * k ∈ kerIn M H :=
      h.inf_centralizer_le_kerIn hred (not_le_centralizer h hJ)
        ⟨H.mul_mem (H.inv_mem hiH) (hKH hk), hc⟩
    have : k = (i : G) * ((i : G)⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hiI) (Subgroup.mem_sup_right hcJ)
  have hKIQ := h.twoResidual_le_sup_pCoreOf hsolv hI₀H hKIJ
  have hI₀N : I₀ ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hI₀H.trans (le_normalizer_pCoreOf 2 H)
  have hcl : conjClosure (thompsonJ T) H ≤ I₀ := by
    refine conjClosure_le fun y hy z hz => ?_
    have hH : H = twoResidual H ⊔ T := by rw [sup_comm]; exact (sup_twoResidual_eq hT).symm
    have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
      hT.1.trans (le_normalizer_twoResidual H)
    have hy' : y ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by rw [← hH]; exact hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hy'
    obtain ⟨k, hk, t, ht, rfl⟩ := hy'
    have hk' : k ∈ ((I₀ ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hKIQ hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hI₀N] at hk'
    obtain ⟨i, hi, q, hq, rfl⟩ := hk'
    have hqT : q ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT hq
    have hJTN : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    have hz' : (q * t) * z * (q * t)⁻¹ ∈ thompsonJ T :=
      (Subgroup.mem_normalizer_iff.mp (hJTN (T.mul_mem hqT ht)) z).mp hz
    have e : i * q * t * z * (i * q * t)⁻¹ = i * ((q * t) * z * (q * t)⁻¹) * i⁻¹ := by group
    rw [e]
    exact I₀.mul_mem (I₀.mul_mem hi (Subgroup.mem_sup_left hz')) (I₀.inv_mem hi)
  have hclJ : ¬ conjClosure (thompsonJ T) H ≤ kerIn M H := by
    intro hle
    apply hJ
    have h1 : thompsonJ T ≤ pCoreOf 2 H :=
      h.le_pCoreOf_of_isPGroup_of_le_kerIn (hT.2.1.to_le (thompsonJ_le_self T))
        ((le_conjClosure _ _).trans hle)
    exact h1.trans (MinParabolic.pCoreOf_le_centralizer hred)
  have hclH : conjClosure (thompsonJ T) H ≤ H :=
    conjClosure_le fun y hy z hz => H.mul_mem (H.mul_mem hy (hJTH hz)) (H.inv_mem hy)
  have hKcl := (h.le_kerIn_or_twoResidual_le hclH (le_normalizer_conjClosure _ _)).resolve_left
    hclJ
  exact ⟨g, hgK, hgN, hKcl.trans hcl⟩

end CFSG.AGLEmbeddingD2.GN
