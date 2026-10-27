module

public import CFSG.CGT.PushingUpLit.BHS6.SymOffender
public import CFSG.CGT.PushingUpLit.BHS7.OmegaMaxSwapCore
public import CFSG.CGT.PushingUpLit.BHS6.SymLocalBlock

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem sym_imgG_thompsonJ_eq {G T V : Subgroup Γ} {m : ℕ} (hm : 2 ≤ m)
    (hT : IsSylowTwoOf T G) (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ))
    {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))} {ψ : ↥V →* ↥(coreMod (2 * m + 1))}
    (hnat : SymNatData G V (2 * m + 1) φ ψ) :
    imgG G φ (thompsonJ T) = imgG G φ (baum T) := by
  classical
  obtain ⟨hVn, hVe, hφs, hφk, hψs, hψk, hψe⟩ := hnat
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have h5 : 5 ≤ 2 * m + 1 := by omega
  have h3 : 3 ≤ 2 * m + 1 := by omega
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hOT : pCoreOf 2 G ≤ T := hT.pCoreOf_le
  have hVT : V ≤ T := (hVQ.trans (C1GN.omegaOneCenterOf_le_self _)).trans hOT
  obtain ⟨W, hWV, hWG, hWψ, hperf⟩ := exists_perfectCore hVn h3 φ hφs ψ hψs hψe
  obtain ⟨hφ's, hφ'k, hψ's, hψ'k, hψ'e⟩ :=
    natAlt_data_core hodd h3 φ hφs hφk ψ hψk hψe hWV hWψ
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_le' hWV hVe
  have hEG : evenSub G φ ≤ G := evenSub_le G φ
  have hGE : G ≤ Subgroup.normalizer (evenSub G φ : Set Γ) := le_normalizer_evenSub G φ
  have hEW : evenSub G φ ≤ Subgroup.normalizer (W : Set Γ) := hEG.trans hWG
  have hWT : W ≤ T := hWV.trans hVT
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  obtain ⟨D, hDβ⟩ := exists_altNatData_of_data hWe hEW hperf (evenHom G φ)
    (ψ.comp (Subgroup.inclusion hWV)) hφ's hφ'k hψ's hψ'k hψ'e
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le hBT
  have hJB : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hJG : thompsonJ T ≤ G := hJT.trans hT.1
  have hBG : baum T ≤ G := hBT.trans hT.1
  have hJW : thompsonJ T ≤ Subgroup.normalizer (W : Set Γ) := hJG.trans hWG
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) := hBG.trans hWG
  have hJE : thompsonJ T ≤ Subgroup.normalizer (evenSub G φ : Set Γ) := hJG.trans hGE
  have hBE : baum T ≤ Subgroup.normalizer (evenSub G φ : Set Γ) := hBG.trans hGE
  have hQ : IsPGroup 2 ↥(autOn (thompsonJ T) W) := isPGroup_autOn hJ2 hJW
  have hQN : autOn (thompsonJ T) W ≤ Subgroup.normalizer (autOn (evenSub G φ) W : Set _) :=
    autOn_le_normalizer_autOn hJW hJE
  have hB : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) := by
    by_contra hcon
    apply hJ
    have hAc : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.centralizer (W : Set Γ) := fun A hA => by
      by_contra hA'
      exact hcon ⟨A, hA, hA'⟩
    have hJC : thompsonJ T ≤ Subgroup.centralizer (W : Set Γ) :=
      iSup_le fun A => iSup_le fun hA => hAc A hA
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨w, hwW, hwv⟩ := hWψ (ψ ⟨v, hv⟩)
    have hc : (⟨v, hv⟩ : ↥V) * w⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv]
      exact mul_inv_cancel _
    rw [hψk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hc
    have hcG : (((⟨v, hv⟩ : ↥V) * w⁻¹ : ↥V) : Γ) ∈ Subgroup.centralizer (G : Set Γ) := hc.2
    have h1 : (j : Γ) * (v * (w : Γ)⁻¹) = (v * (w : Γ)⁻¹) * j :=
      Subgroup.mem_centralizer_iff.mp hcG j (hJG hj)
    have h2 : (w : Γ) * j = j * w := Subgroup.mem_centralizer_iff.mp (hJC hj) w hwW
    calc v * j = (v * (w : Γ)⁻¹) * ((w : Γ) * j) := by group
      _ = (v * (w : Γ)⁻¹) * (j * w) := by rw [h2]
      _ = ((v * (w : Γ)⁻¹) * j) * w := by group
      _ = (j * (v * (w : Γ)⁻¹)) * w := by rw [h1]
      _ = j * v := by group
  let 𝒜 : Set (Subgroup (MulAut ↥W)) :=
    {B | ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) ∧ B = autOn A W}
  have hne : 𝒜.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hB
    exact ⟨autOn A W, A, hA, hAc, rfl⟩
  have h𝒜 : ∀ B ∈ 𝒜, B ≤ autOn (thompsonJ T) W ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥W ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
    have hAN : A ≤ Subgroup.normalizer (W : Set Γ) := hAJ.trans hJW
    refine ⟨autOn_le_autOn W hAJ, isElemAbelian2_autOn hWe hA.2.1 hAN,
      autOn_ne_bot_of_not_le_centralizer hAN hAc, ?_⟩
    rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hWe hAN]
    exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA hWe hWT hAN
  obtain ⟨-, -, -, -, -, hfixed⟩ := alt_family hW2 hodd h5 D hQ hQN hne h𝒜
  have hJU : autOn (thompsonJ T) W = ⨆ B ∈ 𝒜, B := by
    refine le_antisymm ?_ (iSup₂_le fun B hB' => ?_)
    · refine autOn_iSup_le (P := fun A => IsMaxElemAbelian T A) (fun A hA => ?_) fun A hA => ?_
      · exact (B6.le_thompsonJ hA).trans hJW
      · by_cases hAc : A ≤ Subgroup.centralizer (W : Set Γ)
        · rw [autOn_eq_bot_of_le_centralizer hAc]
          exact bot_le
        · exact le_iSup₂_of_le (autOn A W) ⟨A, hA, hAc, rfl⟩ le_rfl
    · obtain ⟨A, hA, -, rfl⟩ := hB'
      exact autOn_le_autOn W (B6.le_thompsonJ hA)
  have hfix : fixV (⨆ B ∈ 𝒜, B) ≤ fixV (autOn (baum T) W) := by
    intro w hw b hb
    obtain ⟨x, hxB, rfl⟩ := mem_autOn_iff.mp hb
    rw [← hJU, ← fixOn, fixOn_eq hWe hJW] at hw
    have hwJ : ∀ j ∈ thompsonJ T, j * (w : Γ) = (w : Γ) * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hw) j hj
    have hwΩ : (w : Γ) ∈ omegaOneCenterOf (thompsonJ T) :=
      mem_omegaOneCenter_thompsonJ_of_centralizes (hWT w.2) (hWe.2 w w.2)
        fun A hA a ha => hwJ a (B6.le_thompsonJ hA ha)
    have hxw : (w : Γ) * (x : Γ) = (x : Γ) * (w : Γ) :=
      Subgroup.mem_centralizer_iff.mp hxB.2 w hwΩ
    apply Subtype.ext
    rw [conjAct_apply']
    calc (x : Γ) * (w : Γ) * (x : Γ)⁻¹ = ((w : Γ) * x) * (x : Γ)⁻¹ := by rw [hxw]
      _ = w := by group
  have hQB : IsPGroup 2 ↥(autOn (baum T) W) := isPGroup_autOn hB2 hBW
  have hQBN : autOn (baum T) W ≤ Subgroup.normalizer (autOn (evenSub G φ) W : Set _) :=
    autOn_le_normalizer_autOn hBW hBE
  have hBJ : autOn (baum T) W ≤ ⨆ B ∈ 𝒜, B := hfixed _ hQB hQBN hfix
  have hJeq : autOn (thompsonJ T) W = autOn (baum T) W :=
    le_antisymm (autOn_le_autOn W hJB) (hJU ▸ hBJ)
  have hGN : ∀ g : ↥G, conjAct W ⟨g, hWG g.2⟩ ∈
      Subgroup.normalizer (autOn (evenSub G φ) W : Set (MulAut ↥W)) := fun g =>
    autOn_le_normalizer_autOn hWG hGE (mem_autOn_iff.mpr ⟨⟨g, hWG g.2⟩, g.2, rfl⟩)
  have link : ∀ g : ↥G, D.psi hodd h5 ⟨conjAct W ⟨g, hWG g.2⟩, hGN g⟩ = φ g := by
    intro g
    apply coreAct_injective h3
    refine MulEquiv.ext fun u => ?_
    obtain ⟨w, hw⟩ := D.surj u
    have h1 := D.psi_spec hodd h5 ⟨conjAct W ⟨g, hWG g.2⟩, hGN g⟩ w
    have hv : (g : Γ) * (w : Γ) * (g : Γ)⁻¹ ∈ V := by
      rw [← conjAct_apply' W ⟨g, hWG g.2⟩ w]
      exact hWV ((conjAct W ⟨g, hWG g.2⟩) w).2
    have key : D.β ((conjAct W ⟨g, hWG g.2⟩) w) = coreAct (2 * m + 1) (φ g) (D.β w) := by
      rw [hDβ, hDβ]
      have e : Subgroup.inclusion hWV ((conjAct W ⟨g, hWG g.2⟩) w) =
          ⟨(g : Γ) * (w : Γ) * (g : Γ)⁻¹, hv⟩ :=
        Subtype.ext (conjAct_apply' W ⟨g, hWG g.2⟩ w)
      show ψ (Subgroup.inclusion hWV ((conjAct W ⟨g, hWG g.2⟩) w)) =
        coreAct (2 * m + 1) (φ g) (ψ (Subgroup.inclusion hWV w))
      rw [e]
      exact hψe g (Subgroup.inclusion hWV w) hv
    rw [hw] at h1 key
    exact h1.symm.trans key
  refine le_antisymm (imgG_mono G φ hJB) ?_
  intro σ hσ
  obtain ⟨b, hbG, hbB, rfl⟩ := mem_imgG.1 hσ
  have hmem : conjAct W ⟨b, hWG hbG⟩ ∈ autOn (thompsonJ T) W := by
    rw [hJeq]
    exact mem_autOn_iff.mpr ⟨⟨b, hWG hbG⟩, hbB, rfl⟩
  obtain ⟨x, hxJ, hxy⟩ := mem_autOn_iff.mp hmem
  have hxG : (x : Γ) ∈ G := hJG hxJ
  refine mem_imgG.2 ⟨x, hxG, hxJ, ?_⟩
  rw [← link ⟨x, hxG⟩, ← link ⟨b, hbG⟩]
  congr 1
  exact Subtype.ext hxy

theorem sym_thompsonJ_not_le {G T V : Subgroup Γ} {n : ℕ} {φ : ↥G →* Equiv.Perm (Fin n)}
    {ψ : ↥V →* ↥(coreMod n)} {T' : Set (Equiv.Perm (Fin n))}
    (S : SymSetting G T V n φ ψ T') : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) := by
  have hT : IsSylowTwoOf T G := S.sylow
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    apply S.ne
    refine le_antisymm (cStarIn_le G ⊥) fun g hg => ?_
    have hΩ : omegaOneCenterOf (⊥ : Subgroup Γ) = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.closure_le _).mpr fun x hx => ?_)
      exact hx.1.1
    refine centralizer_le_cStarIn G ⊥ ⟨hg, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have h1 : h = 1 := Subgroup.mem_bot.mp (hΩ ▸ hh)
    simp [h1]
  have hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T :=
    (inf_le_inf_left G (Subgroup.centralizer_le fun x hx => S.vT hx)).trans
      (centralizer_le_cStarIn G T)
  have hOT : pCoreOf 2 G ≤ T := hT.pCoreOf_le
  have hVQ' : V ≤ pCoreOf 2 G := S.vQ.trans (C1GN.omegaOneCenterOf_le_self _)
  have hVT' : V ≤ T := hVQ'.trans hOT
  have hbaum : ¬ baum T ≤ Subgroup.centralizer (V : Set Γ) :=
    baum_not_le_centralizer hT hT0 S.data.normal hC S.ne
  exact thompsonJ_not_le_centralizer hVT' S.data.elemAbelian hbaum

theorem symSetting_ncard {G T V : Subgroup Γ} {m : ℕ} (hm : 2 ≤ m)
    {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))} {ψ : ↥V →* ↥(coreMod (2 * m + 1))}
    {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}
    (S : SymSetting G T V (2 * m + 1) φ ψ T') : T'.ncard = m := by
  classical
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hT : IsSylowTwoOf T G := S.sylow
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hJ := sym_thompsonJ_not_le S
  have hJB : imgG G φ (thompsonJ T) = imgG G φ (baum T) :=
    sym_imgG_thompsonJ_eq hm hT S.vQ hJ S.data
  set Bbar : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := Subgroup.closure T' with hBbar
  have hBimg : imgG G φ (baum T) = Bbar := S.baum
  have hsurj := S.data.φ_surj
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJG : thompsonJ T ≤ G := hJT.trans hT.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
  set P : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := imgG G φ T with hPdef
  have hP2 : IsPGroup 2 ↥P := isPGroup_imgG hT.1 hT2
  have hPidx : ¬ 2 ∣ P.index := fun hd => hT.2.2 (hd.trans (Subgroup.index_map_dvd _ hsurj))
  have hY : ∃ Y ≤ P, IsMaxSwapGroup Y := exists_isMaxSwapGroup_le_of_isSylow hodd hP2 hPidx
  have hstar : ∀ π : Equiv.Perm (Fin (2 * m + 1)),
      A1b.conjSub π Bbar ≤ P → A1b.conjSub π Bbar = Bbar := by
    intro π hπ
    obtain ⟨g, rfl⟩ := hsurj π
    have hgG : (g : Γ) ∈ G := g.2
    have hKG : kerG G φ ≤ G := fun x hx => (mem_kerG.1 hx).1
    set M : Subgroup Γ := T ⊔ kerG G φ with hM
    have hMG : M ≤ G := sup_le hT.1 hKG
    have hTM : IsSylowTwoOf T M := B6.isSylowTwoOf_mono hT le_sup_left hMG
    have hX : A1b.conjSub (g : Γ) (thompsonJ T) ≤ M := by
      intro x hx
      have hj : (g : Γ)⁻¹ * x * g ∈ thompsonJ T := A1b.mem_conjSub_iff.mp hx
      have hxj : x = (g : Γ) * ((g : Γ)⁻¹ * x * g) * (g : Γ)⁻¹ := by group
      have hxG : x ∈ G := by
        have h' : (g : Γ) * ((g : Γ)⁻¹ * x * g) * (g : Γ)⁻¹ ∈ G :=
          G.mul_mem (G.mul_mem hgG (hJG hj)) (G.inv_mem hgG)
        rwa [← hxj] at h'
      have hmem : φ ⟨x, hxG⟩ ∈ P := by
        have hφj : φ ⟨(g : Γ)⁻¹ * x * g, hJG hj⟩ ∈ Bbar := by
          rw [← hBimg, ← hJB]
          exact mem_imgG.2 ⟨_, hJG hj, hj, rfl⟩
        have hconj := hπ (A1b.mem_conjSub_of_mem hφj)
        have e : φ ⟨x, hxG⟩ = φ g * φ ⟨(g : Γ)⁻¹ * x * g, hJG hj⟩ * (φ g)⁻¹ := by
          have e' : (⟨x, hxG⟩ : ↥G) = g * ⟨(g : Γ)⁻¹ * x * g, hJG hj⟩ * g⁻¹ := Subtype.ext hxj
          rw [e', map_mul, map_mul, map_inv]
        rwa [e]
      obtain ⟨s, hsG, hsT, hsx⟩ := mem_imgG.1 hmem
      have hker : x * s⁻¹ ∈ kerG G φ := by
        refine mem_kerG.2 ⟨G.mul_mem hxG (G.inv_mem hsG), ?_⟩
        have e' : (⟨x * s⁻¹, G.mul_mem hxG (G.inv_mem hsG)⟩ : ↥G) =
            ⟨x, hxG⟩ * ⟨s, hsG⟩⁻¹ := rfl
        rw [e', map_mul, map_inv, ← hsx, mul_inv_cancel]
      have e2 : x = (x * s⁻¹) * s := by group
      rw [e2]
      exact M.mul_mem (Subgroup.mem_sup_right hker) (Subgroup.mem_sup_left hsT)
    have hX2 : IsPGroup 2 ↥(A1b.conjSub (g : Γ) (thompsonJ T)) :=
      hJ2.of_equiv (Subgroup.equivMapOfInjective (thompsonJ T) (MulAut.conj (g : Γ)).toMonoidHom
        (MulAut.conj (g : Γ)).injective)
    obtain ⟨S₁, hS₁, hXS⟩ := B6.exists_isSylowTwoOf_ge hX2 hX
    obtain ⟨y, hyM, hy⟩ := B6.isSylowTwoOf_exists_conj hTM hS₁
    have hTn : T ≤ Subgroup.normalizer (kerG G φ : Set Γ) := hT.1.trans (le_normalizer_kerG G φ)
    have hyM' : y ∈ (T : Set Γ) * (kerG G φ : Set Γ) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T (kerG G φ) hTn]
      exact hyM
    obtain ⟨t, ht, r, hr, rfl⟩ := hyM'
    have htG : t ∈ G := hT.1 ht
    have hr'K : t * r * t⁻¹ ∈ kerG G φ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerG G φ htG) r).mp hr
    have hr'G : t * r * t⁻¹ ∈ G := hKG hr'K
    have huG : (t * r * t⁻¹)⁻¹ * (g : Γ) ∈ G := G.mul_mem (G.inv_mem hr'G) hgG
    have hφu : φ ⟨(t * r * t⁻¹)⁻¹ * (g : Γ), huG⟩ = φ g := by
      have e' : (⟨(t * r * t⁻¹)⁻¹ * (g : Γ), huG⟩ : ↥G) = ⟨t * r * t⁻¹, hr'G⟩⁻¹ * g := rfl
      rw [e', map_mul, map_inv, (mem_kerG.1 hr'K).2, inv_one, one_mul]
    have hJu : ∀ j ∈ thompsonJ T, ((t * r * t⁻¹)⁻¹ * (g : Γ)) * j * ((t * r * t⁻¹)⁻¹ * (g : Γ))⁻¹ ∈ T := by
      intro j hj
      have hx : (g : Γ) * j * (g : Γ)⁻¹ ∈ S₁ := hXS (A1b.mem_conjSub_of_mem hj)
      rw [hy, B6.mem_conjSub] at hx
      have e3 : ((t * r * t⁻¹)⁻¹ * (g : Γ)) * j * ((t * r * t⁻¹)⁻¹ * (g : Γ))⁻¹ =
          t * ((t * r)⁻¹ * ((g : Γ) * j * (g : Γ)⁻¹) * (t * r)) * t⁻¹ := by group
      rw [e3]
      exact T.mul_mem (T.mul_mem ht hx) (T.inv_mem ht)
    have hJu' : A1b.conjSub ((t * r * t⁻¹)⁻¹ * (g : Γ)) (thompsonJ T) ≤ T := by
      intro x hx
      have hj := A1b.mem_conjSub_iff.mp hx
      have := hJu _ hj
      have e : ((t * r * t⁻¹)⁻¹ * (g : Γ)) *
          (((t * r * t⁻¹)⁻¹ * (g : Γ))⁻¹ * x * ((t * r * t⁻¹)⁻¹ * (g : Γ))) *
          ((t * r * t⁻¹)⁻¹ * (g : Γ))⁻¹ = x := by group
      rwa [e] at this
    have hJu'' : A1b.conjSub ((t * r * t⁻¹)⁻¹ * (g : Γ)) (thompsonJ T) ≤ thompsonJ T :=
      OMS.conjSub_thompsonJ_le hJu'
    have h3 : A1b.conjSub (φ g) Bbar ≤ Bbar := by
      intro σ hσ
      have hσ' : (φ g)⁻¹ * σ * φ g ∈ Bbar := A1b.mem_conjSub_iff.mp hσ
      rw [← hBimg, ← hJB] at hσ'
      obtain ⟨j, hjG, hjJ, hjσ⟩ := mem_imgG.1 hσ'
      have hmem : ((t * r * t⁻¹)⁻¹ * (g : Γ)) * j * ((t * r * t⁻¹)⁻¹ * (g : Γ))⁻¹ ∈
          thompsonJ T := hJu'' (A1b.mem_conjSub_of_mem hjJ)
      rw [← hBimg, ← hJB]
      refine mem_imgG.2 ⟨_, hJG hmem, hmem, ?_⟩
      have e' : (⟨((t * r * t⁻¹)⁻¹ * (g : Γ)) * j * ((t * r * t⁻¹)⁻¹ * (g : Γ))⁻¹, hJG hmem⟩ :
          ↥G) = ⟨(t * r * t⁻¹)⁻¹ * (g : Γ), huG⟩ * ⟨j, hjG⟩ *
            ⟨(t * r * t⁻¹)⁻¹ * (g : Γ), huG⟩⁻¹ := rfl
      rw [e', map_mul, map_mul, map_inv, hφu, hjσ]
      group
    exact Subgroup.eq_of_le_of_card_ge h3 (OMS.card_conjSub_eq (φ g) Bbar).ge
  have hk1 : 1 ≤ T'.ncard := (Set.ncard_pos (Set.toFinite T')).2 S.nonempty
  have hswap : IsSwapGroupOfSize Bbar T'.ncard := ⟨T', S.swaps, S.comm, rfl, rfl⟩
  have hk : T'.ncard = (2 * m + 1 - 1) / 2 := swap_rank_eq_of_unique_conj hodd hswap hk1 hY hstar
  omega

end CFSG.CGT.PushingUpLit.SYMB
