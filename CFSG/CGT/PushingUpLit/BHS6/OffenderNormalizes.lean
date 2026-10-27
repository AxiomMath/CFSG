module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge
public import CFSG.CGT.PushingUpLit.BHS6.SixSevenWeak
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenSL
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenThree
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

omit [Group Γ] in
theorem autOn_isSubnormal [Group Γ] {V E G : Subgroup Γ} (h : CFSG.Open.IsSubnormal E G) :
    CFSG.Open.IsSubnormal (autOn E V) (autOn G V) := by
  have h1 := Quasithin.A3.subnormal_comap (Subgroup.normalizer (V : Set Γ)).subtype h
  exact Quasithin.A3.subnormal_map (conjAct V) h1

section Finite

variable [Finite Γ] {G T E S A : Subgroup Γ}

omit [Finite Γ] in
theorem conj_mem_mul_centralizer_of_autOn_normalizes {V X Y : Subgroup Γ}
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) (hY : Y ≤ Subgroup.normalizer (V : Set Γ))
    (h : autOn Y V ≤ Subgroup.normalizer (autOn X V : Set (MulAut ↥V))) :
    ∀ y ∈ Y, ∀ x ∈ X, ∃ x' ∈ X, (y * x * y⁻¹) * x'⁻¹ ∈ Subgroup.centralizer (V : Set Γ) := by
  intro y hy x hx
  have hyN : y ∈ Subgroup.normalizer (V : Set Γ) := hY hy
  have hxN : x ∈ Subgroup.normalizer (V : Set Γ) := hX hx
  have hyb : conjAct V ⟨y, hyN⟩ ∈ autOn Y V := mem_autOn_iff.mpr ⟨⟨y, hyN⟩, hy, rfl⟩
  have hxb : conjAct V ⟨x, hxN⟩ ∈ autOn X V := mem_autOn_iff.mpr ⟨⟨x, hxN⟩, hx, rfl⟩
  have hmem := (Subgroup.mem_normalizer_iff.mp (h hyb) _).mp hxb
  obtain ⟨x', hx'X, hx'⟩ := mem_autOn_iff.mp hmem
  refine ⟨(x' : Γ), hx'X, ?_⟩
  let m : ↥(Subgroup.normalizer (V : Set Γ)) := ⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹
  have hm : conjAct V m =
      conjAct V ⟨y, hyN⟩ * conjAct V ⟨x, hxN⟩ * (conjAct V ⟨y, hyN⟩)⁻¹ := by
    show conjAct V (⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hxm : conjAct V x' = conjAct V m := by rw [hx', hm]
  have key : ∀ u : ↥V, (x' : Γ) * u * (x' : Γ)⁻¹ = (m : Γ) * u * (m : Γ)⁻¹ := fun u => by
    rw [← conjAct_apply' V x' u, ← conjAct_apply' V m u, hxm]
  have hmcoe : (m : Γ) = y * x * y⁻¹ := rfl
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hu : (x' : Γ)⁻¹ * v * (x' : Γ) ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set Γ)).inv_mem x'.2) v).mp
      hv
    simpa using this
  have h3 : (x' : Γ) * ((x' : Γ)⁻¹ * v * (x' : Γ)) * (x' : Γ)⁻¹ =
      (m : Γ) * ((x' : Γ)⁻¹ * v * (x' : Γ)) * (m : Γ)⁻¹ := key ⟨_, hu⟩
  have h3' : v = (m : Γ) * ((x' : Γ)⁻¹ * v * (x' : Γ)) * (m : Γ)⁻¹ := by
    rw [← h3]; group
  rw [← hmcoe]
  calc v * ((m : Γ) * (x' : Γ)⁻¹)
      = ((m : Γ) * ((x' : Γ)⁻¹ * v * (x' : Γ)) * (m : Γ)⁻¹) * ((m : Γ) * (x' : Γ)⁻¹) := by
        rw [← h3']
    _ = (m : Γ) * (x' : Γ)⁻¹ * v := by group

theorem offender_le_normalizer_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) (hsub : CFSG.Open.IsSubnormal E G) (hS : IsSylowOf 2 S G)
    (hA : IsMaxElemAbelian S A) : A ≤ Subgroup.normalizer (E : Set Γ) := by
  classical
  set V₀ : Subgroup Γ := omegaOneCenterOf (pCoreOf 2 G) with hV₀def
  have hV₀e : IsElemAbelian 2 V₀ := isElemAbelian_omegaOneCenter_pCoreOf G
  have hGV : G ≤ Subgroup.normalizer (V₀ : Set Γ) := le_normalizer_omegaOneCenter_pCoreOf G
  have hV₀Q : V₀ ≤ pCoreOf 2 G := omegaOneCenter_le_pCoreOf G
  have hSG : S ≤ G := hS.1
  have hAS : A ≤ S := hA.1
  have hAG : A ≤ G := hAS.trans hSG
  have hEG : E ≤ G := hE.le
  have hWV : blockW E ≤ V₀ := (six_four_a hG hT hE).2
  have hEV : E ≤ Subgroup.normalizer (V₀ : Set Γ) := hEG.trans hGV
  have hAV : A ≤ Subgroup.normalizer (V₀ : Set Γ) := hAG.trans hGV
  have hneEV : ⁅E, V₀⁆ ≠ ⊥ := commutator_omegaOneCenter_ne_bot hG hT hE
  have hcentW : G ⊓ Subgroup.centralizer (V₀ : Set Γ) ≤
      G ⊓ Subgroup.centralizer (blockW E : Set Γ) :=
    inf_le_inf_left G (Subgroup.centralizer_le hWV)
  have hCN : G ⊓ Subgroup.centralizer (V₀ : Set Γ) ≤ Subgroup.normalizer (E : Set Γ) :=
    hcentW.trans (six_six hG hT hE)
  by_cases hAc : A ≤ Subgroup.centralizer (V₀ : Set Γ)
  · exact fun a ha => hCN ⟨hAG ha, hAc ha⟩
  have hS' : IsSylowTwoOf S G := isSylowTwoOf_of_isSylowOf hS
  have hOff : IsOffG V₀ A :=
    isOffG_of_isMaxElemAbelian hV₀e (hV₀Q.trans hS'.pCoreOf_le) (hSG.trans hGV) hA hAc
  have hOffA : @IsOff ↥V₀ (commGroupOfElemAbelian hV₀e) (autOn A V₀) :=
    (isOffG_iff_isOff_autOn hV₀e hAV).mp hOff
  have hAN : autOn A V₀ ≤ Subgroup.normalizer (autOn E V₀ : Set (MulAut ↥V₀)) := by
    by_cases hcomm : ⁅autOn E V₀, autOn A V₀⁆ = ⊥
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr (hcomm ▸ bot_le)
    · let _ : CommGroup ↥V₀ := commGroupOfElemAbelian hV₀e
      have hV2 : ∀ v : ↥V₀, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hV₀e.2 v v.2)
      rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm1, hm⟩
      · have hnat := isSLNatSection_autOn_of_isBTBlock hG hT hE hn hV₀e hV₀Q hEV hneEV
        exact (two_sixteen_sl hV2 hn2 hOffA (autOn_le_autOn V₀ hAG) (autOn_le_autOn V₀ hEG)
          (autOn_isSubnormal hsub) hnat hcomm).1
      · have hnat := isAltNatSection_autOn_of_isBTBlock hG hT hE hm hV₀e hV₀Q hEV hneEV
        rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · have hm1' : m = 1 := by omega
          subst hm1'
          exact (two_sixteen_three hV2 hOffA (autOn_le_autOn V₀ hAG) (autOn_isSubnormal hsub)
            hnat hcomm).1
        · exact (two_sixteen_alt hV2 hm2 hOffA (autOn_le_autOn V₀ hAG) (autOn_le_autOn V₀ hEG)
            (autOn_isSubnormal hsub) hnat hcomm).1
  have hR : ∀ a ∈ A, ∀ e ∈ E, ∃ e' ∈ E, (a * e * a⁻¹) * e'⁻¹ ∈
      G ⊓ Subgroup.centralizer (V₀ : Set Γ) := by
    intro a ha e he
    obtain ⟨e', he', hc⟩ := conj_mem_mul_centralizer_of_autOn_normalizes hEV hAV hAN a ha e he
    exact ⟨e', he', ⟨G.mul_mem (G.mul_mem (G.mul_mem (hAG ha) (hEG he)) (G.inv_mem (hAG ha)))
      (G.inv_mem (hEG he')), hc⟩⟩
  have hdecomp : ∀ a ∈ A, ∀ f ∈ conjSub a E, ∃ c ∈ G ⊓ Subgroup.centralizer (V₀ : Set Γ),
      ∃ e' ∈ E, f = c * e' := by
    intro a ha f hf
    rw [mem_conjSub_iff] at hf
    obtain ⟨e', he', hc⟩ := hR a ha _ hf
    refine ⟨f * e'⁻¹, ?_, e', he', by group⟩
    have : a * (a⁻¹ * f * a) * a⁻¹ * e'⁻¹ = f * e'⁻¹ := by group
    rwa [this] at hc
  have key : ∀ a ∈ A, conjSub a E ≤ E := by
    intro a ha
    have hF : conjSub a E ∈ btBlocksG G T :=
      conjSub_mem_btBlocksG (mem_btBlocksG_of_isBTBlock hE) (hAG ha)
    have hFN : conjSub a E ≤ Subgroup.normalizer (E : Set Γ) := fun f hf => by
      obtain ⟨c, hc, e', he', rfl⟩ := hdecomp a ha f hf
      exact (Subgroup.normalizer (E : Set Γ)).mul_mem (hCN hc) (Subgroup.le_normalizer he')
    have hFR : conjSub a E ≤ (G ⊓ Subgroup.centralizer (blockW E : Set Γ)) ⊔ E := fun f hf => by
      obtain ⟨c, hc, e', he', rfl⟩ := hdecomp a ha f hf
      exact mul_mem ((le_sup_left : G ⊓ Subgroup.centralizer (blockW E : Set Γ) ≤ _) (hcentW hc))
        ((le_sup_right : E ≤ _) he')
    rcases six_seven_of_le_R hG hT hE hF hFN hFR with h | ⟨hFE, -⟩
    · exfalso
      have hWE : blockW E = pCoreOf 2 E := blockW_eq_pCoreOf hE
      have hle : ⁅E, V₀⁆ ≤ (blockW E).comap (MulAut.conj a).toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro e he v hv
        obtain ⟨e', he', hc⟩ := hR a ha e he
        obtain ⟨c, hcdef⟩ : ∃ c, c = (a * e * a⁻¹) * e'⁻¹ := ⟨_, rfl⟩
        rw [← hcdef] at hc
        have hcv : ∀ u ∈ V₀, c * u = u * c := fun u hu =>
          (Subgroup.mem_centralizer_iff.mp hc.2 u hu).symm
        have hv' : a * v * a⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.mp (hGV (hAG ha)) v).mp hv
        have hu : e' * (a * v * a⁻¹) * e'⁻¹ ∈ V₀ :=
          (Subgroup.mem_normalizer_iff.mp (hEV he') _).mp hv'
        have h1 := hcv _ hu
        have hW : ⁅e', a * v * a⁻¹⁆ ∈ blockW E := by
          rw [← commutator_omegaOneCenter_eq hG hT hE]
          exact Subgroup.commutator_mem_commutator he' hv'
        have hce : a * e * a⁻¹ = c * e' := by rw [hcdef]; group
        have h2 : a * ⁅e, v⁆ * a⁻¹ = ⁅e', a * v * a⁻¹⁆ := by
          calc a * ⁅e, v⁆ * a⁻¹ = ⁅a * e * a⁻¹, a * v * a⁻¹⁆ := by
                simp only [commutatorElement_def]; group
            _ = ⁅c * e', a * v * a⁻¹⁆ := by rw [hce]
            _ = (c * (e' * (a * v * a⁻¹) * e'⁻¹)) * c⁻¹ * (a * v * a⁻¹)⁻¹ := by
                simp only [commutatorElement_def]; group
            _ = ((e' * (a * v * a⁻¹) * e'⁻¹) * c) * c⁻¹ * (a * v * a⁻¹)⁻¹ := by rw [h1]
            _ = ⁅e', a * v * a⁻¹⁆ := by simp only [commutatorElement_def]; group
        show a * ⁅e, v⁆ * a⁻¹ ∈ blockW E
        rw [h2]
        exact hW
      have hWa : conjSub a (blockW E) ≤ blockW E := by
        intro x hx
        rw [mem_conjSub_iff] at hx
        have h3 := hle ((commutator_omegaOneCenter_eq hG hT hE).symm ▸ hx)
        have h4 : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
        simpa [h4] using h3
      have hWE' : blockW E ≤ E := by
        rw [hWE]
        exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E
      have hperf : ⁅blockW E, E⁆ = blockW E := by rw [hWE]; exact hE.perfect
      have h5 : conjSub a (blockW E) = ⁅conjSub a (blockW E), conjSub a E⁆ := by
        rw [commutator_conjSub, hperf]
      have h6 : ⁅conjSub a (blockW E), conjSub a E⁆ ≤ ⁅E, conjSub a E⁆ :=
        Subgroup.commutator_mono (hWa.trans hWE') le_rfl
      rw [h] at h6
      have h7 : conjSub a (blockW E) = ⊥ := by
        rw [h5]; exact le_bot_iff.mp h6
      rw [conjSub_eq_bot_iff, hWE] at h7
      exact pCoreOf_ne_bot hE (charTwo_of_isBTBlock hG hT hE) h7
    · exact hFE
  intro a ha
  exact mem_normalizer_of_conjSub_le (key a ha) (key a⁻¹ (A.inv_mem ha))

theorem thompsonJ_le_normalizer_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) (hsub : CFSG.Open.IsSubnormal E G) (hS : IsSylowOf 2 S G) :
    thompsonJ S ≤ Subgroup.normalizer (E : Set Γ) :=
  iSup_le fun _ => iSup_le fun hA =>
    offender_le_normalizer_of_isBTBlock hG hT hE hsub hS hA

end Finite

end CFSG.CGT.PushingUpLit.BHS6
