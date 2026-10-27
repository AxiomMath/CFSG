module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs523
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem centralizer_Z₁_le_normalizer_K_F4 (h5114 : Stmt5_1_14_first_F4) :
    Subgroup.centralizer (Z₁ : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)).trans
    ((h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.2 z
      (s.Z₁_le_Z hz) hz1)

theorem tildeOf_pCoreOf_K_le_centralizer_F4 (h5114 : Stmt5_1_14_first_F4) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    tildeOf Z₁ (pCoreOf 2 (oTwoUpper H)) ≤ Subgroup.centralizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))) :
        Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHG₁ := s.H_le_centralizer_F4 h5114
  have h21 := (h521 G T M L V H B D D₃ Z₁ (Subgroup.centralizer (Z₁ : Set G)) n s.hyp.hyp
    s.hyp.notation59 s.hyp.module s.hyp.l34 hnot s.le_D s.card_D₃ s.z1 hHG₁ le_rfl).1
  have hOK : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans ((oTwoUpper_le H).trans hHG₁))
      ((s.centralizer_Z₁_le_normalizer_K_F4 h5114).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
  have hc : (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ ∈ Z₁ :=
    h21 (Subgroup.commutator_mem_commutator hu (hOK hx))
  have h1 : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ (u * x * u⁻¹ * x⁻¹) = 1 := by
    rw [secMk_eq_one_iff]; simpa using hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ x) h1
  simp only [one_mul, inv_mul_cancel_right] at this
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ u) this
  simpa [mul_assoc] using this

theorem false_of_qhatInt_lt_F4
    (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h510 : Stmt5_1_10_F4)
    (h521 : Stmt5_1_21_F4) (hD : D310L34Fact) (hB : B45L34Fact) (hfaith : Stmt5_1_23_faithful_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n)
    (hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G)))))
    (hlt : qhatInt (tildeOf Z₁ (Subgroup.centralizer (Z₁ : Set G)))
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) hU <
      2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hAnot0 := hfaith G T M L V H B D D₃ Z₁ n s.hyp.hyp s.hyp.notation59 s.hyp.module
    s.hyp.l34 hnot s.le_D s.card_D₃ s.z1 hU
  have hHN := s.H_le_normalizer_Z₁_F4 h5114
  have hHG₁ : H ≤ Subgroup.centralizer (Z₁ : Set G) := s.H_le_centralizer_F4 h5114
  have hG₁N : Subgroup.centralizer (Z₁ : Set G) ≤ Subgroup.normalizer (Z₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hG₁K := s.centralizer_Z₁_le_normalizer_K_F4 h5114
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (Z₁ : Set G) := hKH.trans hHN
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hO2K := s.tildeOf_pCoreOf_K_le_centralizer_F4 h5114 h521 hnot
  set G₁ := Subgroup.centralizer (Z₁ : Set G) with hG₁def
  set U₁ := conjClosure (conjClosure Z₁ D₃) G₁ with hU₁def
  set UH := conjClosure (conjClosure Z₁ D₃) H with hUHdef
  set Ut := tildeOf Z₁ U₁ with hUtdef
  set UHt := tildeOf Z₁ UH with hUHtdef
  set G₁t := tildeOf Z₁ G₁ with hG₁tdef
  set Ht := tildeOf Z₁ H with hHtdef
  set Kt := tildeOf Z₁ (oTwoUpper H) with hKtdef
  set Tt := tildeOf Z₁ T with hTtdef

  have hUHU : UH ≤ U₁ := conjClosure_mono le_rfl hHG₁
  have hUHtU : UHt ≤ Ut := tildeOf_mono hUHU
  have hUHab : IsElemAbelian 2 UHt := isElemAbelian_mono hU hUHtU
  have hHtUH : Ht ≤ Subgroup.normalizer (UHt : Set _) :=
    tildeOf_le_normalizer_tildeOf (le_normalizer_conjClosure _ H)
  have hG₁tU : G₁t ≤ Subgroup.normalizer (Ut : Set _) :=
    tildeOf_le_normalizer_tildeOf (le_normalizer_conjClosure _ G₁)
  have hHtG₁t : Ht ≤ G₁t := tildeOf_mono hHG₁
  have hKtHt : Kt ≤ Ht := tildeOf_mono hKH
  have hTtHt : Tt ≤ Ht := tildeOf_mono hTH
  have hG₁tKt : G₁t ≤ Subgroup.normalizer (Kt : Set _) := tildeOf_le_normalizer_tildeOf hG₁K
  have hKtUH : Kt ≤ Subgroup.normalizer (UHt : Set _) := hKtHt.trans hHtUH
  have hTsyl : IsSylowTwoOf T G₁ := hh.isSylowTwoOf (hTH.trans hHG₁)
  have hTtsyl : IsSylowTwoOf Tt G₁t := isSylowTwoOf_secImg hTsyl hG₁N s.Z₁_le_T

  have hqhat := s.two_lt_qhatInt_F4 h5114 hF h510 h521 hD hB hnot hUHab

  have hKtW : ¬ Kt ≤ Subgroup.centralizer (UHt : Set _) := s.not_tildeOf_K_le_centralizer_F4 h5114 hF
  have hker := s.ker_tildeAct_K_F4 le_rfl hHtUH hKtW h5114 h521 hnot

  let := commGroupOfElemAbelian hU
  have hV : ∀ v : ↥Ut, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hU.2 v v.2)
  have hlt' : qhatOf (autOn G₁t Ut) < (2 : WithTop ℚ) := hlt
  obtain ⟨r, hr'⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt')
  have hr : qhatOf (autOn G₁t Ut) = (r : WithTop ℚ) := hr'.symm
  have hr2 : r < 2 := by
    rw [hr] at hlt'
    have : ((r : ℚ) : WithTop ℚ) < ((2 : ℚ) : WithTop ℚ) := by simpa using hlt'
    exact WithTop.coe_lt_coe.mp this
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2.le
  have hAnot := hAnot0 A hA hlt
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA

  set ρ : ↥G₁t →* MulAut ↥Ut := Setup.rho Ut G₁t hG₁tU with hρ
  have hρrange : ρ.range = autOn G₁t Ut := Setup.range_rho hG₁tU
  have hρT : (Tt.subgroupOf G₁t).map ρ = autOn Tt Ut := by
    apply le_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨t, hG₁tU t.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    · intro φ hφ
      obtain ⟨⟨y, hyN⟩, hyT, rfl⟩ := Subgroup.mem_map.mp hφ
      rw [Subgroup.mem_subgroupOf] at hyT
      exact ⟨⟨y, (tildeOf_mono (hTH.trans hHG₁)) hyT⟩, hyT, rfl⟩
  have hTs : IsSylowTwoOf (autOn Tt Ut) (autOn G₁t Ut) := by
    have := isSylowTwoOf_map_hom' hTtsyl ρ
    rwa [hρT, hρrange] at this
  obtain ⟨g, hgX, hAg⟩ := F7.isSylowTwoOf_exists_conj_le hTs hA2.1 hA2.2.2.isPGroup

  set A' := A.map (congrHom g⁻¹) with hA'def
  have hA' : A' ∈ QhatStar (autOn G₁t Ut) := mem_QhatStar_map_conj hA ((autOn G₁t Ut).inv_mem hgX)
  have hA'T : A' ≤ autOn Tt Ut := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hAg ha
    rw [mem_conjSub] at h1
    rw [congrHom_eq_conj, inv_inv]
    exact h1
  have hA'H : A' ≤ autOn Ht Ut := hA'T.trans (autOn_le_autOn _ hTtHt)

  have hLnorm : ∀ x ∈ autOn G₁t Ut, ∀ l ∈ autOn Kt Ut, x * l * x⁻¹ ∈ autOn Kt Ut := by
    intro x hx l hl
    obtain ⟨⟨y, hyN⟩, hyG, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨⟨k, hkN⟩, hkK, rfl⟩ := Subgroup.mem_map.mp hl
    rw [Subgroup.mem_subgroupOf] at hyG hkK
    rw [← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hG₁tKt hyG) k).mp hkK
  have hA'not : ¬ A' ≤ Subgroup.centralizer (autOn Kt Ut : Set (MulAut ↥Ut)) := by
    intro hc
    apply hAnot
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have ha' : congrHom g⁻¹ a ∈ A' := ⟨a, ha, rfl⟩
    have hl' : g⁻¹ * l * g ∈ autOn Kt Ut := by
      have := hLnorm g⁻¹ ((autOn G₁t Ut).inv_mem hgX) l hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hc ha') _ hl'
    rw [congrHom_eq_conj, inv_inv] at h1

    have h2 : g⁻¹ * (l * a) * g = g⁻¹ * (a * l) * g := by
      calc g⁻¹ * (l * a) * g = (g⁻¹ * l * g) * (g⁻¹ * a * g) := by group
        _ = (g⁻¹ * a * g) * (g⁻¹ * l * g) := h1
        _ = g⁻¹ * (a * l) * g := by group
    have h3 := congrArg (fun y => g * y * g⁻¹) h2
    simpa [mul_assoc] using h3

  have hY : autOn Ht Ut ≤ stabSub (UHt.subgroupOf Ut) := by
    intro x hx u
    obtain ⟨g', hgY, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hgY
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAct_coe_apply]
    have h1 := Subgroup.mem_normalizer_iff.mp (hHtUH hgY) (u : SecQuot _ _)
    exact ⟨fun h => h1.mpr h, fun h => h1.mp h⟩
  have hLstab : autOn Kt Ut ≤ stabSub (UHt.subgroupOf Ut) := (autOn_le_autOn _ hKtHt).trans hY
  have hcomm : commSub (UHt.subgroupOf Ut) A' ≠ ⊥ := by
    rw [Ne, commSub_eq_bot_iff]
    intro hfix
    apply hA'not
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro l hl

    have hc : a * l * a⁻¹ * l⁻¹ ∈ autOn Kt Ut :=
      (autOn Kt Ut).mul_mem (hLnorm a ((hA'H.trans (autOn_le_autOn _ hHtG₁t)) ha) l hl)
        ((autOn Kt Ut).inv_mem hl)
    have hcfix : ∀ u ∈ UHt.subgroupOf Ut, (a * l * a⁻¹ * l⁻¹) u = u := by
      intro u hu
      have hlu : l⁻¹ u ∈ UHt.subgroupOf Ut := ((hLstab ((autOn Kt Ut).inv_mem hl)) u).mpr hu
      have h1 : a⁻¹ (l⁻¹ u) = l⁻¹ u := by
        have := hfix hlu a ha
        rw [← this, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply, this]
      have h2 : l (l⁻¹ u) = u := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      simp only [MulAut.mul_apply]
      rw [h1, h2]
      exact hfix hu a ha
    have hc1 : a * l * a⁻¹ * l⁻¹ = 1 := by
      obtain ⟨⟨y, hyN⟩, hyK, hye⟩ := Subgroup.mem_map.mp hc
      rw [Subgroup.mem_subgroupOf] at hyK
      obtain ⟨k, hk, rfl⟩ := mem_secImg.mp hyK

      have hkC : tmk Z₁ k ∈ Subgroup.centralizer (UHt : Set _) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h1 := congrArg Subtype.val (hcfix ⟨w, hUHtU hw⟩ hw)
        rw [← hye, conjAct_coe_apply] at h1
        have h2 := congrArg (· * tmk Z₁ k) h1
        simpa [mul_assoc] using h2.symm
      have hkO : (⟨k, hk⟩ : ↥(oTwoUpper H)) ∈ CFSG.pCore 2 ↥(oTwoUpper H) := by
        rw [← hker, mem_ker_tildeAct]
        exact hkC
      have hkO' : (k : G) ∈ pCoreOf 2 (oTwoUpper H) := ⟨_, by assumption, rfl⟩
      have hcU := hO2K (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := k) hkO')
      rw [← hye]
      ext u
      rw [conjAct_coe_apply, MulAut.one_apply]
      have hcu := Subgroup.mem_centralizer_iff.mp hcU (u : SecQuot _ _) u.2
      rw [← hcu, mul_inv_cancel_right]
    calc l * a = (a * l * a⁻¹ * l⁻¹)⁻¹ * (a * l) := by group
      _ = a * l := by rw [hc1, inv_one, one_mul]

  have h27 := qhatOf_autSub_le_of_mem_QhatStar' hV hr hA' hA'H (hA'H.trans hY) hcomm
  have htrans := qhatInt_le_qhatOf_autSub hU hUHtU hHtUH
  have hlt2 : (2 : WithTop ℚ) < (r : WithTop ℚ) := lt_of_lt_of_le hqhat (htrans.trans h27)
  have hr2' : (r : WithTop ℚ) ≤ (2 : WithTop ℚ) := by
    have : ((r : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := WithTop.coe_le_coe.mpr hr2.le
    simpa using this
  exact absurd hlt2 (not_lt.mpr hr2')

end Setup521

theorem stmt5_1_23_of_inputs_F4
    (h5114 : Stmt5_1_14_first_F4) (h510 : Stmt5_1_10_F4) (h520 : Stmt5_1_20_F4)
    (h521 : Stmt5_1_21_F4) (hF : L2TorusFact) (hD : D310L34Fact) (hB : B45L34Fact)
    (hoff : Stmt5_1_23_offender_F4) (hfaith : Stmt5_1_23_faithful_F4) : Stmt5_1_23_F4 := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨⟨hyp, not59, hmod, hl34⟩, hD₃, h3,
      (h520 G T M L V H B D n hyp not59 hmod hl34 hnot D₃ hD₃ h3).1, hz1⟩
  by_contra hab
  obtain ⟨hU, hlt⟩ := hoff G T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1 hab
  exact s.false_of_qhatInt_lt_F4 h5114 hF h510 h521 hD hB hfaith hnot hU hlt

end CFSG.Quasithin.H13
