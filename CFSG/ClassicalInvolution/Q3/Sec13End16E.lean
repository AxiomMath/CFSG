module

public import CFSG.ClassicalInvolution.Q3.Sec13End16A
public import CFSG.ClassicalInvolution.Q3.Sec13End15F
public import CFSG.ClassicalInvolution.Q3.Sec13EndPolar16
import CFSG.ClassicalInvolution.Q3.Sec13L94
import CFSG.ClassicalInvolution.Q3.Sec13PerpPair
import CFSG.ClassicalInvolution.Q3.Sec13End15H
public import CFSG.ClassicalInvolution.Q3.Q3T6DConj

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

theorem TwinSit.conj {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G} (s : TwinSit Ω K K' z)
    (hΩ : ConjInvariant Ω) (n : G) :
    TwinSit Ω (conjSub n K) (conjSub n K') (n * z * n⁻¹) := by
  have hK' : K' ∈ twinSet Ω K := by
    rw [s.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  refine ⟨hΩ n K s.mem, s.isInv.conj n, ?_, ?_⟩
  · ext L
    constructor
    · intro hL
      have h1 := twinSet_conj hΩ hL n⁻¹
      rw [conjSub_inv_conjSub, s.twin] at h1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
      rcases h1 with h1 | h1
      · left
        rw [← conjSub_conjSub_inv n L, h1]
      · right
        rw [← conjSub_conjSub_inv n L, h1]
    · intro hL
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
      rcases hL with rfl | rfl
      · exact ⟨hΩ n K s.mem, n * z * n⁻¹, s.isInv.conj n, s.isInv.conj n⟩
      · exact twinSet_conj hΩ hK' n
  · intro heq
    exact s.ne ((conjSub_inv_conjSub n K).symm.trans
      ((congrArg (conjSub n⁻¹) heq).trans (conjSub_inv_conjSub n K')))

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

private theorem e16e1_mem_conj_sup {K K' : Subgroup G} (n : G) {x : G} (hx : x ∈ K ⊔ K') :
    n * x * n⁻¹ ∈ conjSub n K ⊔ conjSub n K' := by
  have h1 : conjSub n (K ⊔ K') = conjSub n K ⊔ conjSub n K' := Subgroup.map_sup _ _ _
  rw [← h1]
  exact conj_mem_conjSub hx

private theorem e16e1_comm_normalizer {W : Subgroup G} {e : G}
    (he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G))) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) : x * e = e * x := by
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp he.2
  have hyc := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
  have h1 : x * (y : G) = (y : G) * x := congrArg Subtype.val hyc
  rw [show (y : G) = e from hye] at h1
  exact h1

private theorem e16e1_MGrp_le_normalizer (h : EndHyp Ω) {W : Subgroup G} {n : G}
    (hn : n ∈ MGrp Ω W) : n ∈ Subgroup.normalizer (W : Set G) :=
  (iSup₂_le fun R hR => (h.mem_dSet_iff.mp hR).2 : MGrp Ω W ≤ Subgroup.normalizer (W : Set G)) hn

private theorem e16e1_dSet_conj (h : EndHyp Ω) {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    conjSub n R ∈ DSet Ω W := by
  obtain ⟨hRΩ, hRN⟩ := h.mem_dSet_iff.mp hR
  refine h.mem_dSet_iff.mpr ⟨h.thmD.hyp.conjInvariant n R hRΩ, fun x hx => ?_⟩
  have h1 := hRN (mem_conjSub_iff.mp hx)
  have e : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn h1) (Subgroup.inv_mem _ hn)

private theorem e16e1_MGrp_conj (h : EndHyp Ω) {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) {g : G} (hg : g ∈ MGrp Ω W) :
    n * g * n⁻¹ ∈ MGrp Ω W := by
  have key : MGrp Ω W ≤ (MGrp Ω W).comap (MulAut.conj n).toMonoidHom := by
    unfold MGrp
    refine iSup₂_le fun R hR => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    exact (le_iSup₂ (f := fun (R' : Subgroup G) (_ : R' ∈ DSet Ω W) => R') (conjSub n R)
      (e16e1_dSet_conj h hn hR)) (conj_mem_conjSub hx)
  exact key hg

private theorem e16e1_conj_e {n e : G} (hnc : n * e = e * n) : n * e * n⁻¹ = e := by
  rw [hnc]
  group

private theorem e16e1_e_not_mem_conj (c : Sit16 Ω K K' W z u e g) {n : G}
    (hnc : n * e = e * n) : e ∉ conjSub n K ⊔ conjSub n K' := by
  intro hmem
  have h1 : conjSub n (K ⊔ K') = conjSub n K ⊔ conjSub n K' := Subgroup.map_sup _ _ _
  rw [← h1] at hmem
  have h2 := mem_conjSub_iff.mp hmem
  have h3 : n⁻¹ * e * n = e := by
    rw [show n⁻¹ * e * n = n⁻¹ * (e * n) by group, ← hnc]
    group
  exact c.e_not_mem (h3 ▸ h2)

theorem conj (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) {n : G} (hn : n ∈ MGrp Ω W) :
    Sit16 Ω (conjSub n K) (conjSub n K') W (n * z * n⁻¹) (n * u * n⁻¹) e (n * g * n⁻¹) := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hnN : n ∈ Subgroup.normalizer (W : Set G) := e16e1_MGrp_le_normalizer h hn
  have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← hd.he]
    exact Subgroup.subset_closure rfl
  have hnc : n * e = e * n := e16e1_comm_normalizer he hnN
  have hzW : n * z * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hnN z).mp hd.hzW
  have huW : n * u * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hnN u).mp hd.huW
  refine ⟨c.twin.conj h.thmD.hyp.conjInvariant n, ⟨hd.hW, hd.hS4, hzW,
    e16e1_mem_conj_sup n hd.hu, huW, ?_, ?_, ?_, hd.he, hd.he1, hd.he2,
    e16e1_MGrp_conj h hnN hd.hg, ?_⟩, e16e1_e_not_mem_conj c hnc⟩
  · calc n * u * n⁻¹ * (n * u * n⁻¹) = n * (u * u) * n⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group
  · intro h1
    apply hd.hu1
    calc u = n⁻¹ * (n * u * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    apply hd.huz
    calc u = n⁻¹ * (n * u * n⁻¹) * n := by group
      _ = n⁻¹ * (n * z * n⁻¹) * n := by rw [h1]
      _ = z := by group
  · calc n * g * n⁻¹ * (n * z * n⁻¹) * (n * g * n⁻¹)⁻¹ = n * (g * z * g⁻¹) * n⁻¹ := by group
      _ = n * (u * e) * n⁻¹ := by rw [hd.hgt]
      _ = (n * u * n⁻¹) * (n * e * n⁻¹) := by group
      _ = (n * u * n⁻¹) * e := by rw [e16e1_conj_e hnc]

private theorem e16e1_comm_W (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {x y : G}
    (hx : x ∈ W) (hy : y ∈ W) : x * y = y * x :=
  CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.commutes_of_mem_WSet h.thmD.hyp hW x hx y hy

private theorem e16e1_he (c : Sit16 Ω K K' W z u e g) :
    e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
  rw [← c.data.he]
  exact Subgroup.subset_closure rfl

private theorem e16e1_seven_false {W : Subgroup G} (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (c : Q3CL.Thompson.Ctx Ω W) (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4))
    (hφ : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (φ x).IsSwap) (Xs : Fin 7 → Subgroup G)
    (hΩX : ∀ i, Xs i ∈ Ω) (hXD : ∀ i, Xs i ∈ DSet Ω W) (h2 : ∀ i, IsPGroup 2 (Xs i))
    (hinj : Function.Injective Xs) : False := by
  choose r hrX hrW using fun i => Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW (hXD i)
  let ρ : Fin 7 → Thompson.Rep Ω W := fun i =>
    ⟨Xs i, Xs i, r i, hΩX i, hXD i, ⟨le_rfl, h2 i, fun _ hV _ hV' => le_antisymm hV hV'⟩,
      hrX i, hrW i⟩
  let T : Finset (Equiv.Perm (Fin 4)) := {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3,
    Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3}
  have hT' : ∀ x y : Fin 4, x ≠ y → Equiv.swap x y ∈ T := by decide
  have hT6 : T.card = 6 := by decide
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin 7)), φ (Asc77.T7D.imgQ (ρ i)) ∈ T := by
    intro i _
    obtain ⟨x, y, hxy, hσ⟩ := (hφ _).mp (Asc77.T7D.imgQ_mem (ρ i))
    rw [hσ]
    exact hT' x y hxy
  have hFinj : Set.InjOn (fun i => φ (Asc77.T7D.imgQ (ρ i))) (Finset.univ : Finset (Fin 7)) := by
    intro i _ j _ hij
    have h1 : Asc77.T7D.imgQ (ρ i) = Asc77.T7D.imgQ (ρ j) := φ.injective hij
    have h3 : (ρ i).K = (ρ j).K := c.K_eq_of_img_eq (ρ i) (ρ j) (congrArg Subtype.val h1)
    exact hinj h3
  have hcard := Finset.card_le_card_of_injOn (fun i => φ (Asc77.T7D.imgQ (ρ i))) hF hFinj
  rw [Finset.card_univ, Fintype.card_fin, hT6] at hcard
  omega

private theorem e16e1_exists_r0 (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    ∃ r ∈ K, r ∉ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) ∧
      r * (u * e) * r⁻¹ = (u * e) * z := by
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ := h.thmD.hyp
  obtain ⟨-, hJOm, hJtw, hJu⟩ := conjSub_mem c h h9
  have hJΩ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hs.mem
  have hJn : conjSub g K ∉ omegaNbr Ω K := by
    intro hJn
    apply hJtw
    rw [← h.kPerp_eq_twinSet_of_perp9 h9 hs.mem]
    exact Set.mem_insert_of_mem _ hJn
  obtain ⟨-, hcard, -⟩ := pair_structure h hs.mem hJOm hJn
  obtain ⟨r, hrK, hrN⟩ : ∃ r ∈ K,
      r ∉ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
    by_contra hcon
    push Not at hcon
    have hinf : K ⊓ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) = K :=
      inf_eq_left.mpr (fun x hx => hcon x hx)
    rw [hinf, h.card_eq_eight hs.mem] at hcard
    norm_num at hcard
  have hKn : K ∉ omegaNbr Ω (conjSub g K) := by
    intro hK
    exact hrN (((TC.mem_omegaNbr_iff hΩ h.thmD.two).mp hK).2.2 hrK)
  have hJK : K ∈ omegaStarNbr Ω (conjSub g K) :=
    CFSG.ClassicalInvolution.Q3.Q3T6.Mu.omegaStarNbr_symm hΩ hs.mem hJΩ hJOm
  exact ⟨r, hrK, hrN, conj_involution_eq_mul h hJΩ hJK hKn hJu hs.isInv hrK hrN⟩

theorem zValues (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    ∀ R ∈ DSet Ω W, ∀ r : G, IsUniqueInvolution R r → r = z ∨ r = u * e ∨ r = z * (u * e) := by
  intro R hR r hr
  by_contra hcon
  push Not at hcon
  obtain ⟨hr1, hr2, hr3⟩ := hcon
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ := h.thmD.hyp
  have hW := hd.hW
  have hΩc := hΩ.conjInvariant
  have he_W : e ∈ W := (e16e1_he c).1
  have ht_W : u * e ∈ W := Subgroup.mul_mem _ hd.huW he_W
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem hW hs.mem hs.isInv hd.hzW
  have hK'D : K' ∈ DSet Ω W := h.mem_dSet_of_mem hW hs.mem_twin.1 hs.mem_twin.2 hd.hzW
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := e16e1_MGrp_le_normalizer h hd.hg
  obtain ⟨hJD, -, -, hJu⟩ := conjSub_mem c h h9
  have hJ'u : IsUniqueInvolution (conjSub g K') (u * e) := by
    have := (hs.conj hΩc g).mem_twin.2
    rwa [hd.hgt] at this
  have hJ'D : conjSub g K' ∈ DSet Ω W := e16e1_dSet_conj h hgN hK'D
  obtain ⟨r₀, hr₀K, hr₀N, hinv⟩ := e16e1_exists_r0 c h h9
  have hr₀NW : r₀ ∈ Subgroup.normalizer (W : Set G) := (h.mem_dSet_iff.mp hKD).2 hr₀K
  have hID : conjSub r₀ (conjSub g K) ∈ DSet Ω W := e16e1_dSet_conj h hr₀NW hJD
  have hI'D : conjSub r₀ (conjSub g K') ∈ DSet Ω W := e16e1_dSet_conj h hr₀NW hJ'D
  have hzt : u * e * z = z * (u * e) := e16e1_comm_W h hW ht_W hd.hzW
  have hIu : IsUniqueInvolution (conjSub r₀ (conjSub g K)) (z * (u * e)) := by
    have := hJu.conj r₀
    rw [hinv, hzt] at this
    exact this
  have hI'u : IsUniqueInvolution (conjSub r₀ (conjSub g K')) (z * (u * e)) := by
    have := hJ'u.conj r₀
    rw [hinv, hzt] at this
    exact this
  let Xs : Fin 7 → Subgroup G := ![K, K', conjSub g K, conjSub g K', conjSub r₀ (conjSub g K),
    conjSub r₀ (conjSub g K'), R]
  let ι : Fin 7 → G := ![z, z, u * e, u * e, z * (u * e), z * (u * e), r]
  have hXsD : ∀ i, Xs i ∈ DSet Ω W := by
    intro i
    fin_cases i <;> first
      | exact hKD | exact hK'D | exact hJD | exact hJ'D | exact hID | exact hI'D | exact hR
  have hIU : ∀ i, IsUniqueInvolution (Xs i) (ι i) := by
    intro i
    fin_cases i <;> first
      | exact hs.isInv | exact hs.mem_twin.2 | exact hJu | exact hJ'u | exact hIu | exact hI'u
      | exact hr
  have hzt1 : z ≠ u * e := by
    intro h1
    apply c.e_not_mem
    have he' : e = u * z := by rw [h1, ← mul_assoc, hd.hu2, one_mul]
    rw [he']
    exact Subgroup.mul_mem _ hd.hu (Subgroup.mem_sup_left hs.isInv.mem)
  have hzt2 : z ≠ z * (u * e) := by
    intro h1
    have h3 : (1 : G) = u * e := mul_left_cancel (a := z) (b := 1) (c := u * e)
      (by rw [mul_one]; exact h1)
    apply c.e_not_mem
    have he' : e = u := by
      calc e = u * (u * e) := by rw [← mul_assoc, hd.hu2, one_mul]
        _ = u * 1 := by rw [← h3]
        _ = u := mul_one u
    rw [he']
    exact hd.hu
  have ht_zt : u * e ≠ z * (u * e) := by
    intro h1
    apply hs.isInv.ne_one
    exact (mul_right_cancel (a := 1) (b := u * e) (c := z) (by rw [one_mul]; exact h1)).symm
  have hKK : K ≠ K' := hs.ne
  have hJJ : conjSub g K ≠ conjSub g K' := fun heq => hs.ne
    ((conjSub_inv_conjSub g K).symm.trans ((congrArg (conjSub g⁻¹) heq).trans
      (conjSub_inv_conjSub g K')))
  have hII : conjSub r₀ (conjSub g K) ≠ conjSub r₀ (conjSub g K') := fun heq => hJJ
    ((conjSub_inv_conjSub r₀ _).symm.trans ((congrArg (conjSub r₀⁻¹) heq).trans
      (conjSub_inv_conjSub r₀ _)))
  have hinj : Function.Injective Xs := by
    intro i j hij
    have hιij : ι i = ι j := (hIU i).eq (by rw [hij]; exact hIU j)
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact (hzt1 hιij).elim | exact (hzt1 hιij.symm).elim
      | exact (hzt2 hιij).elim | exact (hzt2 hιij.symm).elim
      | exact (ht_zt hιij).elim | exact (ht_zt hιij.symm).elim
      | exact (hr1 hιij).elim | exact (hr1 hιij.symm).elim
      | exact (hr2 hιij).elim | exact (hr2 hιij.symm).elim
      | exact (hr3 hιij).elim | exact (hr3 hιij.symm).elim
      | exact (hKK hij).elim | exact (hKK hij.symm).elim
      | exact (hJJ hij).elim | exact (hJJ hij.symm).elim
      | exact (hII hij).elim | exact (hII hij.symm).elim
  have hP : Q3CL.PartIHypG Ω := ⟨hΩ, h.cls, h.thmD.aEmpty⟩
  have hK'tw : K' ∈ twinSet Ω K := by
    rw [hs.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hperp : KPerp Ω K = {K, K'} := (h.kPerp_eq_twinSet_of_perp9 h9 hs.mem).trans hs.twin
  have hS4 : MuIsoS4 Ω W :=
    h.muIsoS4_of_twinSet_pair (fun L hL => h.kPerp_eq_twinSet_of_perp9 h9 hL) hW hKD hs.twin
      hs.ne
  obtain ⟨φ, hφ⟩ := L94.exists_swap_equiv hP hW hs.mem
    (fun J hJ => h.thmD.trans K hs.mem J hJ) hs.isInv hK'tw hs.ne.symm hperp hS4
  have hΩX : ∀ i, Xs i ∈ Ω := fun i => (h.mem_dSet_iff.mp (hXsD i)).1
  have h2 : ∀ i, IsPGroup 2 (Xs i) := fun i => h.thmD.two (Xs i) (hΩX i)
  exact e16e1_seven_false hΩ hW (Q3CL.T8.ctxOf hP hW) φ hφ Xs hΩX hXsD h2 hinj

theorem exists_dSet_zt (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    ∃ R ∈ DSet Ω W, IsUniqueInvolution R (z * (u * e)) := by
  obtain ⟨r, hrK, hrN, hinv⟩ := e16e1_exists_r0 c h h9
  obtain ⟨hJD, -, -, hJu⟩ := conjSub_mem c h h9
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem hd.hW c.twin.mem c.twin.isInv hd.hzW
  have hrNW : r ∈ Subgroup.normalizer (W : Set G) := (h.mem_dSet_iff.mp hKD).2 hrK
  refine ⟨conjSub r (conjSub g K), e16e1_dSet_conj h hrNW hJD, ?_⟩
  have := hJu.conj r
  rw [hinv, e16e1_comm_W h hd.hW (Subgroup.mul_mem _ hd.huW (e16e1_he c).1) hd.hzW] at this
  exact this

theorem exists_frame_mul_z (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    ∃ g₂ : G, Sit16 Ω K K' W z (u * z) e g₂ := by
  obtain ⟨I, hID, hIu⟩ := exists_dSet_zt c h h9
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ := h.thmD.hyp
  have hW := hd.hW
  have hP : Q3CL.PartIHypG Ω := ⟨hΩ, h.cls, h.thmD.aEmpty⟩
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem hW hs.mem hs.isInv hd.hzW
  have hK'tw : K' ∈ twinSet Ω K := by
    rw [hs.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hperp : KPerp Ω K = {K, K'} := (h.kPerp_eq_twinSet_of_perp9 h9 hs.mem).trans hs.twin
  have hS4 : MuIsoS4 Ω W :=
    h.muIsoS4_of_twinSet_pair (fun L hL => h.kPerp_eq_twinSet_of_perp9 h9 hL) hW hKD hs.twin
      hs.ne
  obtain ⟨g₂, hg₂, hg₂z⟩ := L94.exists_mGrp_conj hP (fun L hL => h.thmD.two L hL) hW hs.mem
    (fun J hJ => h.thmD.trans K hs.mem J hJ) hs.isInv hK'tw hs.ne.symm hperp hS4 hKD
    (h.mem_dSet_iff.mp hID).1 hID hIu
  have hcomm : u * z = z * u := e16e1_comm_W h hW hd.huW hd.hzW
  refine ⟨g₂, hs, ⟨hW, hd.hS4, hd.hzW,
    Subgroup.mul_mem _ hd.hu (Subgroup.mem_sup_left hs.isInv.mem),
    Subgroup.mul_mem _ hd.huW hd.hzW, ?_, ?_, ?_, hd.he, hd.he1, hd.he2, hg₂, ?_⟩, c.e_not_mem⟩
  · calc (u * z) * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [← hcomm]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [hd.hu2, hs.isInv.sq, mul_one]
  · intro h1
    apply hd.huz
    calc u = u * z * z := by rw [mul_assoc, hs.isInv.sq, mul_one]
      _ = 1 * z := by rw [h1]
      _ = z := one_mul z
  · intro h1
    apply hd.hu1
    calc u = u * z * z := by rw [mul_assoc, hs.isInv.sq, mul_one]
      _ = z * z := by rw [h1]
      _ = 1 := hs.isInv.sq
  · calc g₂ * z * g₂⁻¹ = z * (u * e) := hg₂z
      _ = (z * u) * e := by group
      _ = (u * z) * e := by rw [hcomm]

theorem mul_mem_sup_conj (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    e * z ∈ conjSub g K ⊔ conjSub g K' := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := e16e1_he c
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := e16e1_MGrp_le_normalizer h hd.hg
  have hzN : z ∈ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer hd.hzW
  have hge : g * e = e * g := e16e1_comm_normalizer he hgN
  have hez : e * z = z * e := (e16e1_comm_normalizer he hzN).symm
  obtain ⟨hJD, -, -, hJu⟩ := conjSub_mem c h h9
  have hgJD : conjSub g (conjSub g K) ∈ DSet Ω W := e16e1_dSet_conj h hgN hJD
  have hgJu : IsUniqueInvolution (conjSub g (conjSub g K)) (g * (u * e) * g⁻¹) := hJu.conj g
  have hcases := zValues c h h9 _ hgJD _ hgJu
  have hne_t : g * (u * e) * g⁻¹ ≠ u * e := by
    intro hs'
    apply c.e_not_mem
    have hzt : z = u * e := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * (u * e) * g := by rw [hd.hgt]
        _ = g⁻¹ * (g * (u * e) * g⁻¹) * g := by rw [hs']
        _ = u * e := by group
    have he' : e = u * z := by rw [hzt, ← mul_assoc, hd.hu2, one_mul]
    rw [he']
    exact Subgroup.mul_mem _ hd.hu (Subgroup.mem_sup_left hs.isInv.mem)
  rcases hcases with hA | hA | hA
  ·
    have h1 : g * u * g⁻¹ * e = z := by
      calc g * u * g⁻¹ * e = g * u * g⁻¹ * (g * e * g⁻¹) := by rw [e16e1_conj_e hge]
        _ = g * (u * e) * g⁻¹ := by group
        _ = z := hA
    have h2 : g * u * g⁻¹ = z * e := by
      calc g * u * g⁻¹ = (g * u * g⁻¹ * e) * e := by
            rw [mul_assoc (g * u * g⁻¹) e e, hd.he2, mul_one]
        _ = z * e := by rw [h1]
    rw [hez, ← h2]
    exact e16e1_mem_conj_sup g hd.hu
  · exact absurd hA hne_t
  ·
    have h1 : g * u * g⁻¹ * e = z * (u * e) := by
      calc g * u * g⁻¹ * e = g * u * g⁻¹ * (g * e * g⁻¹) := by rw [e16e1_conj_e hge]
        _ = g * (u * e) * g⁻¹ := by group
        _ = z * (u * e) := hA
    have h2 : g * u * g⁻¹ = z * u := by
      calc g * u * g⁻¹ = (g * u * g⁻¹ * e) * e := by
            rw [mul_assoc (g * u * g⁻¹) e e, hd.he2, mul_one]
        _ = z * (u * e) * e := by rw [h1]
        _ = z * u := by rw [mul_assoc z (u * e) e, mul_assoc u e e, hd.he2, mul_one]
    have h3 : e * z = (z * u) * (u * e) := by
      calc e * z = z * e := hez
        _ = z * ((u * u) * e) := by rw [hd.hu2, one_mul]
        _ = (z * u) * (u * e) := by group
    rw [h3, ← h2]
    exact Subgroup.mul_mem _ (e16e1_mem_conj_sup g hd.hu) (Subgroup.mem_sup_left hJu.mem)

theorem conj_frame (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) :
    Sit16 Ω (conjSub g K) (conjSub g K') W (u * e) (e * z) e g⁻¹ := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ := h.thmD.hyp
  have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := e16e1_he c
  have he_W : e ∈ W := he.1
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := e16e1_MGrp_le_normalizer h hd.hg
  have hge : g * e = e * g := e16e1_comm_normalizer he hgN
  have hzN : z ∈ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer hd.hzW
  have hez : e * z = z * e := (e16e1_comm_normalizer he hzN).symm
  have huN : u ∈ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer hd.huW
  have heu : e * u = u * e := (e16e1_comm_normalizer he huN).symm
  have htw : TwinSit Ω (conjSub g K) (conjSub g K') (u * e) := by
    have := hs.conj hΩ.conjInvariant g
    rwa [hd.hgt] at this
  have hu : e * z ∈ conjSub g K ⊔ conjSub g K' := mul_mem_sup_conj c h h9
  refine ⟨htw, ⟨hd.hW, hd.hS4, Subgroup.mul_mem _ hd.huW he_W, hu,
    Subgroup.mul_mem _ he_W hd.hzW, ?_, ?_, ?_, hd.he, hd.he1, hd.he2, ?_, ?_⟩,
    e16e1_e_not_mem_conj c hge⟩
  · calc e * z * (e * z) = e * (z * e) * z := by group
      _ = e * (e * z) * z := by rw [← hez]
      _ = (e * e) * (z * z) := by group
      _ = 1 := by rw [hd.he2, hs.isInv.sq, mul_one]
  · intro h1
    apply c.e_not_mem
    have hez' : e = z := by
      calc e = e * z * z := by rw [mul_assoc, hs.isInv.sq, mul_one]
        _ = 1 * z := by rw [h1]
        _ = z := one_mul z
    rw [hez']
    exact Subgroup.mem_sup_left hs.isInv.mem
  · intro h1
    apply hd.huz
    have hzu : z = u := by
      calc z = e * (e * z) := by rw [← mul_assoc, hd.he2, one_mul]
        _ = e * (u * e) := by rw [h1]
        _ = (e * u) * e := by rw [mul_assoc]
        _ = (u * e) * e := by rw [heu]
        _ = u := by rw [mul_assoc, hd.he2, mul_one]
    exact hzu.symm
  · exact Subgroup.inv_mem (MGrp Ω W) hd.hg
  · calc g⁻¹ * (u * e) * g⁻¹⁻¹ = g⁻¹ * (g * z * g⁻¹) * g := by rw [← hd.hgt, inv_inv]
      _ = z := by group
      _ = e * z * e := by rw [hez, mul_assoc, hd.he2, mul_one]

theorem dSet_subset_centMembers (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) :
    DSet Ω W ⊆ centMembers Ω e := by
  intro R hR
  obtain ⟨J, hJ, hRJ, -, hmax⟩ := Asc77.mem_RSet_iff.mp hR.1
  have hJR : J = R := hmax J le_rfl (h.thmD.two J hJ) hRJ
  exact Generic.mem_centMembers.mpr ⟨hJR ▸ hJ, dSet_le_centralizer c R hR⟩

end Sit16

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem zGroup_ne_eGroup_conj (h : EndHyp Ω) (hK : K ∈ Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    (n : G) : zGroup Ω ≠ eGroup Ω (conjSub n K) := by
  intro heq
  apply h13
  rw [h.eGroup_conj hK n] at heq
  have h1 : conjSub n⁻¹ (zGroup Ω) = eGroup Ω K := by
    rw [heq, conjSub_inv_conjSub]
  have hN := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hfix : conjSub n⁻¹ (zGroup Ω) = zGroup Ω := by
    ext x
    rw [mem_conjSub_iff, inv_inv]
    constructor
    · intro hx
      have h2 := hN.conj_mem _ hx n⁻¹
      have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
      rwa [e] at h2
    · intro hx
      exact hN.conj_mem x hx n
  rw [hfix] at h1
  exact h1

omit [Finite G] in
private def e16e1_conjEquiv (Y : Subgroup G) (g : G) (h1 : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (h2 : ∀ y ∈ Y, g⁻¹ * y * g⁻¹⁻¹ ∈ Y) : ↥Y ≃* ↥Y where
  toFun y := ⟨g * (y : G) * g⁻¹, h1 _ y.2⟩
  invFun y := ⟨g⁻¹ * (y : G) * g⁻¹⁻¹, h2 _ y.2⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem oddCore_centMembers_eq_bot (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {a : G} (ha : a ∈ zGroup Ω) (ha1 : a ≠ 1) :
    classicalInvolutionOddCore ↥(pSpan (centMembers Ω a)) = ⊥ := by
  have hΩc := h.thmD.hyp.conjInvariant
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant hΩc
  generalize hY : pSpan (centMembers Ω a) = Y
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hcomm : ∀ d ∈ zGroup Ω, ∀ L ∈ centMembers Ω a, conjSub d L ∈ centMembers Ω a := by
    intro d hd L hL
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩc (n := d) hL
    have hda : d * a * d⁻¹ = a := by
      rw [h.zGroup_comm h9 d hd a ha, mul_inv_cancel_right]
    rwa [hda] at h1
  have hYle : ∀ d ∈ zGroup Ω, Y ≤ Y.comap (MulAut.conj d).toMonoidHom := by
    intro d hd
    rw [← hY]
    refine pSpan_le fun L hL => ?_
    intro m hm
    rw [Subgroup.mem_comap]
    exact le_pSpan (hcomm d hd L hL) (Subgroup.mem_map_of_mem (MulAut.conj d).toMonoidHom hm)
  have hconj : ∀ d ∈ zGroup Ω, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y := fun d hd y hy =>
    Subgroup.mem_comap.mp (hYle d hd hy)
  have hOconj : ∀ d ∈ zGroup Ω, ∀ c : ↥Y, c ∈ classicalInvolutionOddCore ↥Y →
      ∃ c' ∈ classicalInvolutionOddCore ↥Y, (c' : G) = d * (c : G) * d⁻¹ := by
    intro d hd c hc
    refine ⟨(e16e1_conjEquiv Y d (hconj d hd) (hconj d⁻¹ (inv_mem hd))) c, ?_, rfl⟩
    have hchar : (classicalInvolutionOddCore ↥Y).map
        (e16e1_conjEquiv Y d (hconj d hd) (hconj d⁻¹ (inv_mem hd))).toMonoidHom =
          classicalInvolutionOddCore ↥Y :=
      CFSG.ComponentClassification.OddCore.char_invariant _
    rw [← hchar]
    exact Subgroup.mem_map_of_mem _ hc
  have hcomm2 : ∀ c ∈ classicalInvolutionOddCore ↥Y, ∀ d ∈ zGroup Ω, (c : G) * d = d * c := by
    intro c hc d hd
    obtain ⟨u, huO, hu⟩ := hOconj d hd c⁻¹ (inv_mem hc)
    have hu' : (u : G) = d * (c : G)⁻¹ * d⁻¹ := by rw [hu, Subgroup.coe_inv]
    have hwO : c * u ∈ classicalInvolutionOddCore ↥Y := mul_mem hc huO
    have hwG : ((c * u : ↥Y) : G) = (c : G) * (d * (c : G)⁻¹ * d⁻¹) := by
      rw [Subgroup.coe_mul, hu']
    have hwD : ((c * u : ↥Y) : G) ∈ zGroup Ω := by
      have h1 : (c : G) * d * (c : G)⁻¹ ∈ zGroup Ω := hD.conj_mem d hd (c : G)
      have e : (c : G) * (d * (c : G)⁻¹ * d⁻¹) = (c : G) * d * (c : G)⁻¹ * d⁻¹ := by group
      rw [hwG, e]
      exact mul_mem h1 (inv_mem hd)
    have hodd : Odd (orderOf ((c * u : ↥Y) : G)) := by
      rw [Subgroup.orderOf_coe]
      exact hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hwO)
    have hcent : ((c * u : ↥Y) : G) ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => h.zGroup_comm h9 x hx _ hwD
    have hw1 := h.eq_one_of_odd_mem_centralizer_zGroup h9 s h13 hcent hodd
    rw [hwG] at hw1
    calc (c : G) * d = (c : G) * (d * (c : G)⁻¹ * d⁻¹) * (d * c) := by group
      _ = d * c := by rw [hw1, one_mul]
  rw [eq_bot_iff]
  intro c hc
  have hcent : (c : G) ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun d hd => (hcomm2 c hc d hd).symm
  have hodd : Odd (orderOf (c : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hc)
  have hc1 := h.eq_one_of_odd_mem_centralizer_zGroup h9 s h13 hcent hodd
  rw [Subgroup.mem_bot]
  exact Subtype.ext hc1

end EndHyp

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem natCard_zGroup_eq_four_pow (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) : ∃ m : ℕ, Nat.card (zGroup Ω) = 4 ^ m := by
  obtain ⟨bf, hbf⟩ := h.exists_endForm h9 s h13
  haveI : Fact (EndHyp Ω) := ⟨h⟩
  haveI : Fact (Perp9 Ω) := ⟨h9⟩
  exact Polar.SympForm.exists_natCard_eq_four_pow hbf.sympForm

theorem sixtyFour_le_natCard_zGroup (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : ¬ eGroup Ω K ≤ K ⊔ K') : 64 ≤ Nat.card (zGroup Ω) := by
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := by
    have hcomm' : Commutes K' K := fun x hx y hy => (s.commutes h y hy x hx).symm
    exact AscL62.le_normalizer_of_commutes hcomm'
  have hKN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK'N
  have hD16 : Nat.card (zGroup Ω) ≠ 16 := by
    intro h16
    have h2 := h.natCard_zGroup_eq_two_mul h9 s h13
    have hI := h.natCard_zGroup_inf_sup_twin h9 s h13
    have hle : zGroup Ω ⊓ (K ⊔ K') ≤ zGroup Ω ⊓ Subgroup.normalizer (K : Set G) :=
      inf_le_inf_left _ hKN
    have heq : zGroup Ω ⊓ (K ⊔ K') = zGroup Ω ⊓ Subgroup.normalizer (K : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by omega)
    have hE' : eGroup Ω K ≤ zGroup Ω ⊓ (K ⊔ K') := by
      rw [heq]
      exact le_inf (h.eGroup_le_zGroup s.mem) (h.eGroup_le_normalizer s.mem)
    exact hE (fun x hx => (hE' hx).2)
  obtain ⟨m, hm⟩ := h.natCard_zGroup_eq_four_pow h9 s h13
  have h8 : 8 ∣ Nat.card (zGroup Ω) := by
    rw [h.natCard_zGroup_eq_eight_mul h9 s h13]
    exact dvd_mul_right 8 _
  rw [hm] at h8 hD16 ⊢
  rcases m with _ | _ | _ | m
  · norm_num at h8
  · norm_num at h8
  · norm_num at hD16
  · calc (64 : ℕ) = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ (m + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem involution_eq_of_le_centralizer (h : EndHyp Ω) (h9 : Perp9 Ω) {R M : Subgroup G}
    (hR : R ∈ Ω) (hM : M ∈ Ω) {r : G} (hr : IsUniqueInvolution R r)
    (hMr : M ≤ Subgroup.centralizer ({r} : Set G)) : IsUniqueInvolution M r := by
  by_cases hRM : R = M
  · subst hRM
    exact hr
  have hN : M ≤ Subgroup.normalizer (R : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer h.thmD.hyp hR hM hRM hr le_rfl
      (h.thmD.two M hM) (by rw [h.card_eq_eight hM]; norm_num) hMr
  have hMnbr : M ∈ omegaNbr Ω R :=
    (TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two).mpr ⟨hM, Ne.symm hRM, hN⟩
  have hMtw : M ∈ twinSet Ω R := by
    rw [← h.kPerp_eq_twinSet_of_perp9 h9 hR]
    exact Set.mem_insert_of_mem _ hMnbr
  obtain ⟨-, z', hz', hMz'⟩ := hMtw
  have e : r = z' := hr.eq hz'
  rw [e]
  exact hMz'

theorem closure_zPoints (Ω : Set (Subgroup G)) :
    Subgroup.closure (zPoints Ω : Set (zGroup Ω)) = ⊤ :=
  Subgroup.closure_closure_coe_preimage (k := zSet Ω)

private theorem e16e2_even_card_of_invol {α : Type*} [DecidableEq α] (f : α → α)
    (hff : ∀ x, f (f x) = x) : ∀ (n : ℕ) (X : Finset α), X.card = n →
      (∀ x ∈ X, f x ≠ x) → (∀ x ∈ X, f x ∈ X) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hX hne hinv
  rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [Finset.card_empty] at hX
    rw [← hX]
    exact ⟨0, rfl⟩
  · have hfx : f x ∈ X := hinv x hx
    have hxfx : f x ≠ x := hne x hx
    have hfx' : f x ∈ X.erase x := Finset.mem_erase.2 ⟨hxfx, hfx⟩
    have hcard : ((X.erase x).erase (f x)).card + 2 = X.card := by
      have h1 : (X.erase x).card = X.card - 1 := Finset.card_erase_of_mem hx
      have h2 : ((X.erase x).erase (f x)).card = (X.erase x).card - 1 :=
        Finset.card_erase_of_mem hfx'
      have h4 : 0 < (X.erase x).card := Finset.card_pos.2 ⟨f x, hfx'⟩
      omega
    have hYX : ∀ y ∈ (X.erase x).erase (f x), y ∈ X := fun y hy =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
    have hYinv : ∀ y ∈ (X.erase x).erase (f x), f y ∈ (X.erase x).erase (f x) := by
      intro y hy
      rw [Finset.mem_erase, Finset.mem_erase] at hy
      obtain ⟨h1, h2, h3⟩ := hy
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨fun h => h2 (by have := congrArg f h; rwa [hff, hff] at this),
        fun h => h1 (by have := congrArg f h; rwa [hff] at this), hinv y h3⟩
    obtain ⟨k, hk⟩ := ih ((X.erase x).erase (f x)).card (by omega) _ rfl
      (fun y hy => hne y (hYX y hy)) hYinv
    rw [← hX]
    exact ⟨k + 1, by omega⟩

private theorem e16e2_even_ncard {α : Type*} [Finite α] (f : α → α) (hff : ∀ x, f (f x) = x)
    (S : Set α) (hfix : ∀ x ∈ S, f x ≠ x) (hmem : ∀ x ∈ S, f x ∈ S) : Even S.ncard := by
  classical
  have hfin : S.Finite := Set.toFinite S
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact e16e2_even_card_of_invol f hff _ hfin.toFinset rfl
    (fun x hx => hfix x (hfin.mem_toFinset.mp hx))
    (fun x hx => hfin.mem_toFinset.mpr (hmem x (hfin.mem_toFinset.mp hx)))

theorem exists_pointSet [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)] (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) :
    ∃ a : ℕ, Polar.PointSet bf (zPoints Ω) a := by
  classical
  have h : EndHyp Ω := hh.out
  have h9' : Perp9 Ω := h9.out
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hDn : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant hΩ.conjInvariant
  have hDc : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9'
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩
  let cj : G → zGroup Ω → zGroup Ω := fun g x => ⟨g * x.1 * g⁻¹, hDn.conj_mem x.1 x.2 g⟩
  have cj_inv : ∀ g x, cj g (cj g⁻¹ x) = x := by
    intro g x
    exact Subtype.ext (by show g * (g⁻¹ * x.1 * g⁻¹⁻¹) * g⁻¹ = x.1; group)
  have cj_inv2 : ∀ g x, cj g⁻¹ (cj g x) = x := by
    intro g x
    exact Subtype.ext (by show g⁻¹ * (g * x.1 * g⁻¹) * g⁻¹⁻¹ = x.1; group)
  have cj_inj : ∀ g, Function.Injective (cj g) := by
    intro g x y hxy
    have := congrArg (cj g⁻¹) hxy
    rwa [cj_inv2, cj_inv2] at this
  have cj_pts : ∀ g x, x ∈ zPoints Ω → cj g x ∈ zPoints Ω := by
    rintro g x ⟨M, hM, hx⟩
    exact ⟨conjSub g M, hΩ.conjInvariant g M hM, hx.conj g⟩
  have cj_bf : ∀ g a b, bf (cj g a) (cj g b) = bf a b := fun g a b => hbf.conj g a b _ _ rfl rfl
  have trans : ∀ p q : zGroup Ω, p ∈ zPoints Ω → q ∈ zPoints Ω → ∃ g : G, cj g p = q := by
    rintro p q ⟨Mp, hMp, hp⟩ ⟨Mq, hMq, hq⟩
    obtain ⟨g, hg⟩ := h.thmD.trans Mp hMp Mq hMq
    refine ⟨g, Subtype.ext ?_⟩
    have hc : IsUniqueInvolution Mq (g * p.1 * g⁻¹) := by
      have := hp.conj g
      rwa [hg] at this
    exact hc.eq hq
  have mul_mem : ∀ x ∈ zPoints Ω, ∀ y ∈ zPoints Ω, x ≠ y → bf x y = 0 → x * y ∈ zPoints Ω := by
    rintro x ⟨Mx, hMx, hx⟩ y ⟨My, hMy, hy⟩ hxy hb
    have hxN : x.1 ∈ Subgroup.normalizer (My : Set G) := (hbf.spec My hMy y hy x).mp hb
    have hst := h.mem_omegaStarNbr_or_twinSet h9' hMy hMx hx hxN
    have hT : Mx ∉ twinSet Ω My := by
      rintro ⟨-, z', hz'y, hz'x⟩
      exact hxy (Subtype.ext ((hx.eq hz'x).trans (hy.eq hz'y).symm))
    have hstar := hst.resolve_right hT
    have hnot := h.notMem_omegaNbr_of_notMem_twinSet h9' hMy hT
    obtain ⟨r, -, -, hr2⟩ := Q3T6D.exists_mem_conj_eq_mul hΩ hMy hMx hy hx hstar hnot
    have hinv : IsUniqueInvolution (conjSub r Mx) (y.1 * x.1) := by
      have := hx.conj r
      rwa [hr2] at this
    refine ⟨conjSub r Mx, hΩ.conjInvariant r Mx hMx, ?_⟩
    rw [show (x * y).1 = y.1 * x.1 from (h.zGroup_comm h9' x.1 x.2 y.1 y.2)]
    exact hinv
  have one_notMem : (1 : zGroup Ω) ∉ zPoints Ω := by
    rintro ⟨M, -, hu⟩
    exact hu.ne_one rfl
  have nbr_mul : ∀ p x : zGroup Ω, p ∈ zPoints Ω → x ∈ Polar.nbr bf (zPoints Ω) p →
      p * x ∈ Polar.nbr bf (zPoints Ω) p := by
    rintro p x hp ⟨hxS, hxp, hb⟩
    have hx1 : x ≠ 1 := fun e => one_notMem (by rw [← e]; exact hxS)
    refine ⟨mul_mem p hp x hxS (Ne.symm hxp) hb, ?_, ?_⟩
    · intro e
      exact hx1 (mul_eq_left.1 e)
    · rw [hbf.mul_right, hbf.alt, hb, add_zero]
  have nbr_transport : ∀ (g : G) (p : zGroup Ω), p ∈ zPoints Ω →
      (Polar.nbr bf (zPoints Ω) (cj g p)).ncard = (Polar.nbr bf (zPoints Ω) p).ncard := by
    intro g p hp
    have himg : Polar.nbr bf (zPoints Ω) (cj g p) = cj g '' Polar.nbr bf (zPoints Ω) p := by
      ext y
      constructor
      · rintro ⟨hyS, hyp, hb⟩
        refine ⟨cj g⁻¹ y, ⟨cj_pts g⁻¹ y hyS, ?_, ?_⟩, cj_inv g y⟩
        · intro e
          apply hyp
          rw [← cj_inv g y, e]
        · rw [← cj_bf g p (cj g⁻¹ y), cj_inv g y]
          exact hb
      · rintro ⟨x, ⟨hxS, hxp, hb⟩, rfl⟩
        refine ⟨cj_pts g x hxS, fun e => hxp (cj_inj g e), ?_⟩
        rw [cj_bf]
        exact hb
    rw [himg]
    exact Set.ncard_image_of_injective _ (cj_inj g)
  have nbr_even : ∀ p ∈ zPoints Ω, Even (Polar.nbr bf (zPoints Ω) p).ncard := by
    intro p hp
    have hp1 : p ≠ 1 := fun e => one_notMem (by rw [← e]; exact hp)
    have hpp : ∀ x : zGroup Ω, p * (p * x) = x := fun x => by
      rw [← mul_assoc, show p * p = 1 from Subtype.ext (h.zGroup_mul_self h9' p.1 p.2), one_mul]
    exact e16e2_even_ncard (fun x => p * x) hpp _ (fun x _ e => hp1 (mul_eq_right.1 e))
      (fun x hx => nbr_mul p x hp hx)
  have hp₀ : (⟨z, hzD⟩ : zGroup Ω) ∈ zPoints Ω := ⟨K, s.mem, s.isInv⟩
  refine ⟨(Polar.nbr bf (zPoints Ω) ⟨z, hzD⟩).ncard / 2, one_notMem, ?_, ?_⟩
  · intro x hx y hy hxy hb
    exact mul_mem x hx y hy hxy hb
  · intro p hp
    obtain ⟨g, hg⟩ := trans ⟨z, hzD⟩ p hp₀ hp
    rw [← hg, nbr_transport g _ hp₀]
    exact (Nat.two_mul_div_two_of_even (nbr_even _ hp₀)).symm

private theorem e16e2_cent_twinSet (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {I : Subgroup G} (hI : I ∈ Ω) {x d : G}
    (hx : IsUniqueInvolution I x) (hd : d ∈ zGroup Ω)
    (hdI : d ∈ Subgroup.centralizer (I : Set G)) {R : Subgroup G} (hR : R ∈ twinSet Ω I) :
    d ∈ Subgroup.centralizer (R : Set G) := by
  obtain ⟨I', hne, hT⟩ := h.twinSet_pair s hI
  have hIne : zGroup Ω ≠ eGroup Ω I := by
    obtain ⟨n, hn⟩ := h.thmD.trans K s.mem I hI
    rw [← hn]
    exact h.zGroup_ne_eGroup_conj s.mem h13 n
  have hsI : TwinSit Ω I I' x := ⟨hI, hx, hT, hne.symm⟩
  have hinf := h.inf_centralizer_twin_eq h9 hsI hIne
  rw [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hR
  rcases hR with hR | hR
  · rw [hR]
    exact hdI
  · rw [hR]
    have hmem : d ∈ zGroup Ω ⊓ Subgroup.centralizer (I' : Set G) := by
      rw [hinf]
      exact Subgroup.mem_inf.mpr ⟨hd, hdI⟩
    exact (Subgroup.mem_inf.mp hmem).2

private theorem e16e2_eq_or_inv {v x : G} (hv4 : orderOf v = 4) (hx : x ∈ Subgroup.zpowers v)
    (hx2 : x * x ≠ 1) : x = v ∨ x = v⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h4 : (orderOf v : ℤ) = 4 := by rw [hv4]; norm_num
  have hk : v ^ k = v ^ (k % 4) := by
    rw [← h4]
    exact (zpow_mod_orderOf v k).symm
  have hv4' : v ^ (4 : ℤ) = 1 := by
    have h1 := pow_orderOf_eq_one v
    rw [hv4] at h1
    exact_mod_cast h1
  rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h0 | h1 | h2 | h3
  · exfalso
    apply hx2
    rw [hk, h0, zpow_zero, one_mul]
  · left
    rw [hk, h1, zpow_one]
  · exfalso
    apply hx2
    rw [hk, h2, ← zpow_add, show (2 : ℤ) + 2 = 4 by norm_num, hv4']
  · right
    rw [hk, h3]
    apply eq_inv_of_mul_eq_one_left
    rw [← zpow_add_one, show (3 : ℤ) + 1 = 4 by norm_num, hv4']

private theorem e16e2_sup_zpowers_eq {M V : Subgroup G} (hVM : V ≤ M) (hM8 : Nat.card M = 8)
    (hV4 : Nat.card V = 4) {x : G} (hxM : x ∈ M) (hxV : x ∉ V) :
    V ⊔ Subgroup.zpowers x = M := by
  have hS : V ⊔ Subgroup.zpowers x ≤ M := sup_le hVM (Subgroup.zpowers_le.mpr hxM)
  have hxS : x ∈ V ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hdvd1 : Nat.card V ∣ Nat.card ↥(V ⊔ Subgroup.zpowers x) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(V ⊔ Subgroup.zpowers x) ∣ Nat.card M := Subgroup.card_dvd_of_le hS
  have hge : Nat.card V ≤ Nat.card ↥(V ⊔ Subgroup.zpowers x) :=
    Subgroup.card_le_of_le le_sup_left
  have hne : Nat.card ↥(V ⊔ Subgroup.zpowers x) ≠ 4 := by
    intro h4
    have heq : V = V ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    exact hxV (by rw [heq]; exact hxS)
  have hle8 : Nat.card ↥(V ⊔ Subgroup.zpowers x) ≤ 8 := by
    rw [← hM8]
    exact Nat.le_of_dvd Nat.card_pos hdvd2
  have h8 : Nat.card ↥(V ⊔ Subgroup.zpowers x) = 8 := by
    rw [hV4] at hdvd1 hge
    omega
  exact Subgroup.eq_of_le_of_card_ge hS (by omega)

theorem centralizer_or_mul (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {R M : Subgroup G} {r p c : G} (hR : R ∈ Ω) (hM : M ∈ Ω)
    (hr : IsUniqueInvolution R r) (hp : IsUniqueInvolution M p) (hc : c ∈ zGroup Ω)
    (hcR : R ≤ Subgroup.centralizer ({c} : Set G))
    (hrM : r ∈ Subgroup.normalizer (M : Set G)) (hcM : c ∈ Subgroup.normalizer (M : Set G)) :
    M ≤ Subgroup.centralizer ({c} : Set G) ∨ M ≤ Subgroup.centralizer ({c * r} : Set G) := by
  have hDc : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have hDsq : ∀ a ∈ zGroup Ω, a * a = 1 := h.zGroup_mul_self h9
  have hDn : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hrD : r ∈ zGroup Ω := Subgroup.subset_closure ⟨R, hR, hr⟩
  have hpD : p ∈ zGroup Ω := Subgroup.subset_closure ⟨M, hM, hp⟩
  have hcRc : ∀ x ∈ R, x * c = c * x :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hcR hx)
  have hcN : c ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer (R : Set G) (Subgroup.mem_centralizer_iff.mpr hcRc)
  by_cases hT : R ∈ twinSet Ω M
  ·
    left
    obtain ⟨-, z', hz'M, hz'R⟩ := hT
    have hcM' := e16e2_cent_twinSet h h9 s h13 hR hr hc (Subgroup.mem_centralizer_iff.mpr hcRc)
      (⟨hM, z', hz'R, hz'M⟩ : M ∈ twinSet Ω R)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcM' x hx)
  ·
    have hRstar : R ∈ omegaStarNbr Ω M :=
      (h.mem_omegaStarNbr_or_twinSet h9 hM hR hr hrM).resolve_right hT
    have hRn : R ∉ omegaNbr Ω M := h.notMem_omegaNbr_of_notMem_twinSet h9 hM hT
    obtain ⟨hcV, hV4, hcU, hU4, hcomm, -⟩ := pair_structure h hM hRstar hRn
    obtain ⟨v, hvV, hv4, hVle⟩ := perpP_gen hcV hV4
    obtain ⟨u, huU, hu4, -⟩ := perpP_gen hcU hU4
    obtain ⟨r', hr'R, hr'N⟩ : ∃ r' ∈ R, r' ∉ Subgroup.normalizer (M : Set G) := by
      by_contra hcon
      push Not at hcon
      have hRle : R ⊓ Subgroup.normalizer (M : Set G) = R :=
        inf_eq_left.mpr (fun x hx => hcon x hx)
      rw [hRle, h.card_eq_eight hR] at hU4
      omega
    have hMstar : M ∈ omegaStarNbr Ω R := Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hM hR hRstar
    have hMn : M ∉ omegaNbr Ω R := fun hMN =>
      hRn (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.thmD.hyp hR hM hMN)
    obtain ⟨n, hnodd, hvr⟩ := h.pair_action hR hMstar hMn huU hu4 hvV hv4 hr'R hr'N
    have huv : v * u = u * v := hcomm v hvV u huU
    have hrv : v * r = r * v := hcomm v hvV r ⟨hr.mem, hrM⟩
    have hcr' : r' * c = c * r' := hcRc r' hr'R
    have hcu : u * c = c * u := hcRc u huU.1
    have hcun : ∀ k : ℤ, c * u ^ k * c⁻¹ = u ^ k := fun k => by
      have hcm : Commute c u := hcu.symm
      rw [(hcm.zpow_right k).eq]
      group
    have hcvV : c * v * c⁻¹ ∈ M ⊓ Subgroup.normalizer (R : Set G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hcM v).mp hvV.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hvV.2) (Subgroup.inv_mem _ hcN)⟩
    have hvv : v * v ≠ 1 := by
      intro h1
      have h2 : v ^ 2 = 1 := by rw [pow_two]; exact h1
      have hd := orderOf_dvd_of_pow_eq_one h2
      rw [hv4] at hd
      omega
    have hx2 : c * v * c⁻¹ * (c * v * c⁻¹) ≠ 1 := by
      intro h1
      apply hvv
      have e : c * v * c⁻¹ * (c * v * c⁻¹) = c * (v * v) * c⁻¹ := by group
      rw [e] at h1
      calc v * v = c⁻¹ * (c * (v * v) * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have hcvv : c * v * c⁻¹ = v := by
      rcases e16e2_eq_or_inv hv4 (hVle hcvV) hx2 with h1 | h1
      · exact h1
      · exfalso
        have hcr'' : c * r' * c⁻¹ = r' := by rw [← hcr']; group
        have hcvi : c * v⁻¹ * c⁻¹ = v := by
          rw [show c * v⁻¹ * c⁻¹ = (c * v * c⁻¹)⁻¹ by group, h1, inv_inv]
        have hE1 : v⁻¹ * r' * v = r' * u ^ n := by
          have e1 : c * (v * r' * v⁻¹) * c⁻¹ = c * (r' * u ^ n) * c⁻¹ := by rw [hvr]
          have hL : c * (v * r' * v⁻¹) * c⁻¹ = v⁻¹ * r' * v := by
            calc c * (v * r' * v⁻¹) * c⁻¹
                = (c * v * c⁻¹) * (c * r' * c⁻¹) * (c * v⁻¹ * c⁻¹) := by group
              _ = v⁻¹ * r' * v := by rw [h1, hcr'', hcvi]
          have hR' : c * (r' * u ^ n) * c⁻¹ = r' * u ^ n := by
            calc c * (r' * u ^ n) * c⁻¹ = (c * r' * c⁻¹) * (c * u ^ n * c⁻¹) := by group
              _ = r' * u ^ n := by rw [hcr'', hcun n]
          rw [← hL, e1, hR']
        have hvu : Commute v u := huv
        have hvun : v⁻¹ * u ^ n * v = u ^ n := by
          have hc' : Commute v (u ^ n) := hvu.zpow_right n
          calc v⁻¹ * u ^ n * v = v⁻¹ * (u ^ n * v) := by group
            _ = v⁻¹ * (v * u ^ n) := by rw [← hc'.eq]
            _ = u ^ n := by group
        have hrr : r' = r' * u ^ (2 * n) := by
          calc r' = v⁻¹ * (v * r' * v⁻¹) * v := by group
            _ = v⁻¹ * (r' * u ^ n) * v := by rw [hvr]
            _ = (v⁻¹ * r' * v) * (v⁻¹ * u ^ n * v) := by group
            _ = (r' * u ^ n) * u ^ n := by rw [hE1, hvun]
            _ = r' * u ^ (2 * n) := by rw [mul_assoc, ← zpow_add, two_mul]
        have hu2n : u ^ (2 * n) = 1 := mul_eq_left.mp hrr.symm
        have hdvd : (orderOf u : ℤ) ∣ 2 * n := orderOf_dvd_iff_zpow_eq_one.mpr hu2n
        rw [hu4] at hdvd
        norm_num at hdvd
        obtain ⟨m, hm⟩ := hnodd
        omega
    have hcvc : Commute c v := by
      show c * v = v * c
      calc c * v = c * v * c⁻¹ * c := by group
        _ = v * c := by rw [hcvv]
    have hcVc : ∀ x ∈ M ⊓ Subgroup.normalizer (R : Set G), x * c = c * x := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hVle hx)
      exact (hcvc.zpow_right k).eq.symm
    have hrVc : ∀ x ∈ M ⊓ Subgroup.normalizer (R : Set G), x * r = r * x := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hVle hx)
      have hrv' : Commute r v := hrv.symm
      exact (hrv'.zpow_right k).eq.symm
    have hdich : ∀ a ∈ zGroup Ω, a ∈ Subgroup.normalizer (M : Set G) → ∀ x ∈ M,
        a * x * a⁻¹ = x ∨ a * x * a⁻¹ = p * x := by
      intro a ha haN x hx
      have hd1 : a * x * a⁻¹ * x⁻¹ ∈ M :=
        M.mul_mem ((Subgroup.mem_normalizer_iff.mp haN x).mp hx) (M.inv_mem hx)
      have hd2 : a * x * a⁻¹ * x⁻¹ ∈ zGroup Ω := by
        rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
        exact (zGroup Ω).mul_mem ha (Subgroup.Normal.conj_mem hDn a⁻¹ ((zGroup Ω).inv_mem ha) x)
      rcases hp.unique _ hd1 (hDsq _ hd2) with h1 | h1
      · exact Or.inl (mul_inv_eq_one.mp h1)
      · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h1)
    have hdichc := hdich c hc hcM
    have hdichr := hdich r hrD hrM
    have hrnc : ∃ x ∈ M, x * r ≠ r * x := by
      by_contra hcon
      push Not at hcon
      have hMr : M ≤ Subgroup.centralizer ({r} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hcon x hx)
      exact hT ⟨hR, r, h.involution_eq_of_le_centralizer h9 hR hM hr hMr, hr⟩
    have hM8 : Nat.card M = 8 := h.card_eq_eight hM
    by_cases hcM' : ∀ x ∈ M, x * c = c * x
    · left
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcM' x hx)
    · right
      have hcx : ∀ x ∈ M, x ∉ M ⊓ Subgroup.normalizer (R : Set G) →
          c * x * c⁻¹ = p * x := by
        intro x hx hxV
        rcases hdichc x hx with h1 | h1
        · exfalso
          have hxc : c * x = x * c := by
            calc c * x = c * x * c⁻¹ * c := by group
              _ = x * c := by rw [h1]
          have hsup := e16e2_sup_zpowers_eq inf_le_left hM8 hV4 hx hxV
          have hCle : M ≤ Subgroup.centralizer ({c} : Set G) := by
            rw [← hsup]
            refine sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcVc y hy))
              ?_
            rw [Subgroup.zpowers_le]
            exact Subgroup.mem_centralizer_singleton_iff.mpr hxc.symm
          exact hcM' fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hCle hy)
        · exact h1
      have hrx : ∀ x ∈ M, x ∉ M ⊓ Subgroup.normalizer (R : Set G) →
          r * x * r⁻¹ = p * x := by
        intro x hx hxV
        rcases hdichr x hx with h1 | h1
        · exfalso
          obtain ⟨y, hy, hyr⟩ := hrnc
          apply hyr
          have hxr : x * r = r * x := by
            calc x * r = (r * x * r⁻¹) * r := by rw [h1]
              _ = r * x := by group
          have hsup := e16e2_sup_zpowers_eq inf_le_left hM8 hV4 hx hxV
          have hCle : M ≤ Subgroup.centralizer ({r} : Set G) := by
            rw [← hsup]
            refine sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hrVc y hy))
              ?_
            rw [Subgroup.zpowers_le]
            exact Subgroup.mem_centralizer_singleton_iff.mpr hxr
          exact (Subgroup.mem_centralizer_singleton_iff.mp (hCle hy))
        · exact h1
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hxV : x ∈ M ⊓ Subgroup.normalizer (R : Set G)
      · have hxc : x * c = c * x := hcVc x hxV
        have hxr : x * r = r * x := hrVc x hxV
        calc x * (c * r) = (x * c) * r := by group
          _ = (c * x) * r := by rw [hxc]
          _ = c * (x * r) := by group
          _ = c * (r * x) := by rw [hxr]
          _ = c * r * x := by group
      · have e1 : c * x = p * x * c := by
          calc c * x = c * x * c⁻¹ * c := by group
            _ = p * x * c := by rw [hcx x hx hxV]
        have e2 : r * x = p * x * r := by
          calc r * x = r * x * r⁻¹ * r := by group
            _ = p * x * r := by rw [hrx x hx hxV]
        have hpc : c * p = p * c := hDc c hc p hpD
        have hpp : p * p = 1 := hDsq p hpD
        symm
        calc c * r * x = c * (r * x) := by group
          _ = c * (p * x * r) := by rw [e2]
          _ = (c * p) * x * r := by group
          _ = (p * c) * x * r := by rw [hpc]
          _ = p * (c * x) * r := by group
          _ = p * (p * x * c) * r := by rw [e1]
          _ = (p * p) * x * c * r := by group
          _ = x * c * r := by rw [hpp, one_mul]
          _ = x * (c * r) := by group

end EndHyp

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

@[expose] def lambdaW (Ω : Set (Subgroup G)) (W : Subgroup G) : Subgroup G :=
  zGroup Ω ⊓ Subgroup.centralizer ((MGrp Ω W : Subgroup G) : Set G)

theorem e_mem_lambdaW (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) : e ∈ lambdaW Ω W := by
  refine Subgroup.mem_inf.mpr ⟨(u_mem_zGroup c h h9 h13).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
  have hM : MGrp Ω W ≤ Subgroup.centralizer ({e} : Set G) :=
    iSup₂_le fun R hR => dSet_le_centralizer c R hR
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hM hy)

private theorem e16e2_mGrp_le_normalizer (h : EndHyp Ω) {W : Subgroup G} :
    MGrp Ω W ≤ Subgroup.normalizer (W : Set G) :=
  iSup₂_le fun R hR => (h.mem_dSet_iff.mp hR).2

private theorem e16e2_le_mGrp {W A : Subgroup G} (hA : A ∈ DSet Ω W) : A ≤ MGrp Ω W :=
  le_iSup₂ (f := fun (R : Subgroup G) (_ : R ∈ DSet Ω W) => R) A hA

private theorem e16e2_conj_mem_dSet (h : EndHyp Ω) {W A : Subgroup G} {n : G}
    (hA : A ∈ DSet Ω W) (hn : n ∈ Subgroup.normalizer (W : Set G)) :
    conjSub n A ∈ DSet Ω W := by
  obtain ⟨hAΩ, hAN⟩ := h.mem_dSet_iff.mp hA
  refine h.mem_dSet_iff.mpr ⟨h.thmD.hyp.conjInvariant n A hAΩ, fun y hy => ?_⟩
  have hyW := hAN (mem_conjSub_iff.mp hy)
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hyW) (Subgroup.inv_mem _ hn)
  convert this using 1
  group

private theorem e16e2_mem_normalizer_conjSub {n x : G} {X : Subgroup G} :
    x ∈ Subgroup.normalizer ((conjSub n X : Subgroup G) : Set G) ↔
      n⁻¹ * x * n ∈ Subgroup.normalizer (X : Set G) := by
  have key : ∀ y : G, conjSub (n⁻¹ * y * n) X = conjSub n⁻¹ (conjSub y (conjSub n X)) := by
    intro y
    rw [conjSub_mul, conjSub_mul]
  rw [mem_normalizer_iff_conjSub_eq, mem_normalizer_iff_conjSub_eq]
  constructor
  · intro hx
    rw [key, hx, conjSub_inv_conjSub]
  · intro hX
    calc conjSub x (conjSub n X) = conjSub n (conjSub (n⁻¹ * x * n) X) := by
          rw [key, conjSub_conjSub_inv]
      _ = conjSub n X := by rw [hX]

private theorem e16e2_S_normalizes_K (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) {x : G}
    (hx : x = z ∨ x = u * e ∨ x = z * (u * e)) : x ∈ Subgroup.normalizer (K : Set G) := by
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW
  have hKK : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (fun y hy => Subgroup.le_normalizer hy)
      (Asc77.AscL62.le_normalizer_of_commutes (c.twin.commutes h).symm)
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer c.twin.isInv.mem
  have hu : u ∈ Subgroup.normalizer (K : Set G) := hKK c.data.hu
  have he : e ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) (Subgroup.mem_centralizer_iff.mpr
      fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (dSet_le_centralizer c K hKD hy))
  rcases hx with rfl | rfl | rfl
  · exact hzN
  · exact (Subgroup.normalizer (K : Set G)).mul_mem hu he
  · exact (Subgroup.normalizer (K : Set G)).mul_mem hzN
      ((Subgroup.normalizer (K : Set G)).mul_mem hu he)

private theorem e16e2_conj_S (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    {n x : G} (hn : n ∈ MGrp Ω W) (hx : x = z ∨ x = u * e ∨ x = z * (u * e)) :
    n⁻¹ * x * n = z ∨ n⁻¹ * x * n = u * e ∨ n⁻¹ * x * n = z * (u * e) := by
  have hnW : n⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inv_mem _ (e16e2_mGrp_le_normalizer h hn)
  obtain ⟨A, hA, hAx⟩ : ∃ A ∈ DSet Ω W, IsUniqueInvolution A x := by
    rcases hx with rfl | rfl | rfl
    · exact ⟨K, h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW, c.twin.isInv⟩
    · have hgN : g ∈ Subgroup.normalizer (W : Set G) := e16e2_mGrp_le_normalizer h c.data.hg
      have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW
      have hJi : IsUniqueInvolution (conjSub g K) (u * e) := by
        have := c.twin.isInv.conj g
        rwa [c.data.hgt] at this
      exact ⟨conjSub g K, e16e2_conj_mem_dSet h hKD hgN, hJi⟩
    · obtain ⟨I, hI, hIx⟩ := c.exists_dSet_zt h h9
      exact ⟨I, hI, hIx⟩
  have hconj := e16e2_conj_mem_dSet h hA hnW
  have hinv := hAx.conj n⁻¹
  rw [inv_inv] at hinv
  exact c.zValues h h9 (conjSub n⁻¹ A) hconj (n⁻¹ * x * n) hinv

private theorem e16e2_S_normalizes (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) {A : Subgroup G} (hA : A ∈ DSet Ω W) {x : G}
    (hx : x = z ∨ x = u * e ∨ x = z * (u * e)) : x ∈ Subgroup.normalizer (A : Set G) := by
  have hAΩ : A ∈ Ω := (h.mem_dSet_iff.mp hA).1
  obtain ⟨a, ha⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hAΩ
  have hperp : KPerp Ω K = {K, K'} := by
    rw [h.kPerp_eq_twinSet_of_perp9 h9 c.twin.mem, c.twin.twin]
  have hK'tw : K' ∈ twinSet Ω K := by
    rw [c.twin.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨n, hn, hnz⟩ := L94.exists_mGrp_conj ⟨h.thmD.hyp, h.cls, h.thmD.aEmpty⟩ h.thmD.two
    c.data.hW c.twin.mem (fun J hJ => h.thmD.trans K c.twin.mem J hJ) c.twin.isInv hK'tw
    c.twin.ne.symm hperp c.data.hS4
    (h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW) hAΩ hA ha
  have hcinv : IsUniqueInvolution (conjSub n⁻¹ A) z := by
    have e : n⁻¹ * a * n⁻¹⁻¹ = z := by rw [← hnz]; group
    have := ha.conj n⁻¹
    rwa [e] at this
  have hmem : conjSub n⁻¹ A ∈ twinSet Ω K :=
    ⟨h.thmD.hyp.conjInvariant n⁻¹ A hAΩ, z, c.twin.isInv, hcinv⟩
  rw [c.twin.twin, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hxN := e16e2_conj_S c h h9 hn hx
  rcases hmem with hmem | hmem
  · have hA' : A = conjSub n K := by
      rw [← hmem, conjSub_conjSub_inv]
    rw [hA']
    exact e16e2_mem_normalizer_conjSub.mpr (e16e2_S_normalizes_K c h hxN)
  · have hA' : A = conjSub n K' := by
      rw [← hmem, conjSub_conjSub_inv]
    rw [hA']
    refine e16e2_mem_normalizer_conjSub.mpr ?_
    rw [← (h.normalizer_twin c.twin).1]
    exact e16e2_S_normalizes_K c h hxN

private theorem e16e2_cover3 {X : Type*} {p q r a b c x : X} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ha : a = p ∨ a = q ∨ a = r) (hb : b = p ∨ b = q ∨ b = r)
    (hc : c = p ∨ c = q ∨ c = r) (hx : x = p ∨ x = q ∨ x = r) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : x = a ∨ x = b ∨ x = c := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> simp_all

private theorem e16e2_zt_ne (c : Sit16 Ω K K' W z u e g) :
    z ≠ u * e ∧ z ≠ z * (u * e) ∧ u * e ≠ z * (u * e) := by
  have hu : u ∈ K ⊔ K' := c.data.hu
  have hzKK : z ∈ K ⊔ K' := Subgroup.mem_sup_left c.twin.isInv.mem
  refine ⟨fun hzue => c.e_not_mem ?_, fun hzz => c.e_not_mem ?_, fun huz => c.twin.isInv.ne_one ?_⟩
  · have e1 : e = u⁻¹ * z := by rw [hzue]; group
    rw [e1]
    exact (K ⊔ K').mul_mem ((K ⊔ K').inv_mem hu) hzKK
  · have h1 : u * e = 1 := mul_left_cancel (a := z) (by rw [mul_one]; exact hzz.symm)
    have e1 : e = u⁻¹ := by
      calc e = u⁻¹ * (u * e) := by group
        _ = u⁻¹ := by rw [h1, mul_one]
    rw [e1]
    exact (K ⊔ K').inv_mem hu
  · exact mul_right_cancel (a := z) (b := u * e) (c := 1) (by rw [one_mul]; exact huz.symm)

private theorem e16e2_lambda_of_pair (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) {A B : Subgroup G} (hA : A ∈ DSet Ω W) (hB : B ∈ DSet Ω W)
    (hAB : B ∉ twinSet Ω A) {d : G} (hd : d ∈ zGroup Ω)
    (hdA : d ∈ Subgroup.centralizer (A : Set G)) (hdB : d ∈ Subgroup.centralizer (B : Set G)) :
    d ∈ lambdaW Ω W := by
  have hAΩ : A ∈ Ω := (h.mem_dSet_iff.mp hA).1
  have hBΩ : B ∈ Ω := (h.mem_dSet_iff.mp hB).1
  have hAN : A ≤ Subgroup.normalizer (W : Set G) := (h.mem_dSet_iff.mp hA).2
  obtain ⟨a, ha⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hAΩ
  obtain ⟨b, hb⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hBΩ
  have hSa := c.zValues h h9 A hA a ha
  have hSb := c.zValues h h9 B hB b hb
  have hbN : b ∈ Subgroup.normalizer (A : Set G) := e16e2_S_normalizes c h h9 h13 hA hSb
  have hBst : B ∈ omegaStarNbr Ω A :=
    (h.mem_omegaStarNbr_or_twinSet h9 hAΩ hBΩ hb hbN).resolve_right hAB
  have hBn : B ∉ omegaNbr Ω A := h.notMem_omegaNbr_of_notMem_twinSet h9 hAΩ hAB
  obtain ⟨-, hcA, -, -, -, -⟩ := pair_structure h hAΩ hBst hBn
  obtain ⟨r, hrA, hrB⟩ : ∃ r ∈ A, r ∉ Subgroup.normalizer (B : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : A ⊓ Subgroup.normalizer (B : Set G) = A :=
      inf_eq_left.mpr (fun x hx => hcon x hx)
    rw [hle, h.card_eq_eight hAΩ] at hcA
    omega
  have hAB' : A ∈ omegaStarNbr Ω B := Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hAΩ hBΩ hBst
  have hBA' : A ∉ omegaNbr Ω B := fun hh =>
    hBn (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.thmD.hyp hBΩ hAΩ hh)
  have hconj : r * b * r⁻¹ = b * a := conj_involution_eq_mul h hBΩ hAB' hBA' hb ha hrA hrB
  have hCΩ : conjSub r B ∈ Ω := h.thmD.hyp.conjInvariant r B hBΩ
  have hCinv : IsUniqueInvolution (conjSub r B) (b * a) := by
    have := hb.conj r
    rwa [hconj] at this
  have hrW : r ∈ Subgroup.normalizer (W : Set G) := hAN hrA
  have hCD : conjSub r B ∈ DSet Ω W := by
    refine h.mem_dSet_iff.mpr ⟨hCΩ, fun y hy => ?_⟩
    have hyW := (h.mem_dSet_iff.mp hB).2 (mem_conjSub_iff.mp hy)
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hrW hyW) (Subgroup.inv_mem _ hrW)
    convert this using 1
    group
  have hSc := c.zValues h h9 (conjSub r B) hCD (b * a) hCinv
  have hab : a ≠ b := fun hab => hAB ⟨hBΩ, a, ha, by rw [hab]; exact hb⟩
  have hac : a ≠ b * a := fun e1 => hb.ne_one (mul_right_cancel (a := b) (b := a) (c := 1)
    (by rw [one_mul]; exact e1.symm))
  have hbc : b ≠ b * a := fun e1 => ha.ne_one (mul_left_cancel (a := b) (b := 1) (c := a)
    (by rw [mul_one]; exact e1)).symm
  obtain ⟨hzt1, hzt2, hzt3⟩ := e16e2_zt_ne c
  have hcov : ∀ y, (y = z ∨ y = u * e ∨ y = z * (u * e)) → y = a ∨ y = b ∨ y = b * a :=
    fun y hy => e16e2_cover3 hzt1 hzt2 hzt3 hSa hSb hSc hy hab hac hbc
  have hdr : d * r = r * d := by
    have := Subgroup.mem_centralizer_iff.mp hdA r hrA
    exact this.symm
  have hdC : d ∈ Subgroup.centralizer ((conjSub r B : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : r⁻¹ * y * r ∈ B := mem_conjSub_iff.mp hy
    have h1 : (r⁻¹ * y * r) * d = d * (r⁻¹ * y * r) :=
      Subgroup.mem_centralizer_iff.mp hdB _ hy'
    have hrinv : r⁻¹ * d = d * r⁻¹ := by
      calc r⁻¹ * d = r⁻¹ * d * r * r⁻¹ := by group
        _ = r⁻¹ * (d * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * d) * r⁻¹ := by rw [hdr]
        _ = d * r⁻¹ := by group
    calc y * d = r * (r⁻¹ * y * r) * r⁻¹ * d := by group
      _ = r * (r⁻¹ * y * r) * (r⁻¹ * d) := by group
      _ = r * (r⁻¹ * y * r) * (d * r⁻¹) := by rw [hrinv]
      _ = r * ((r⁻¹ * y * r) * d) * r⁻¹ := by group
      _ = r * (d * (r⁻¹ * y * r)) * r⁻¹ := by rw [h1]
      _ = (r * d) * (r⁻¹ * y * r) * r⁻¹ := by group
      _ = (d * r) * (r⁻¹ * y * r) * r⁻¹ := by rw [hdr]
      _ = d * y := by group
  have hcent : ∀ R ∈ DSet Ω W, d ∈ Subgroup.centralizer (R : Set G) := by
    intro R hR
    obtain ⟨hRΩ, -⟩ := h.mem_dSet_iff.mp hR
    obtain ⟨x, hx⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hRΩ
    rcases hcov x (c.zValues h h9 R hR x hx) with hxa | hxb | hxc
    · exact EndHyp.e16e2_cent_twinSet h h9 c.twin h13 hAΩ ha hd hdA
        ⟨hRΩ, a, ha, by rw [← hxa]; exact hx⟩
    · exact EndHyp.e16e2_cent_twinSet h h9 c.twin h13 hBΩ hb hd hdB
        ⟨hRΩ, b, hb, by rw [← hxb]; exact hx⟩
    · exact EndHyp.e16e2_cent_twinSet h h9 c.twin h13 hCΩ hCinv hd hdC
        ⟨hRΩ, b * a, hCinv, by rw [← hxc]; exact hx⟩
  have hM : MGrp Ω W ≤ Subgroup.centralizer ({d} : Set G) := iSup₂_le fun R hR => fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hcent R hR) w hw)
  unfold lambdaW
  refine Subgroup.mem_inf.mpr ⟨hd, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hM hy)

private theorem e16e2_cent_of_lambda {d : G} {A : Subgroup G} {Ω' : Set (Subgroup G)}
    {W' : Subgroup G} (hd : d ∈ lambdaW Ω' W') (hA : A ∈ DSet Ω' W') :
    d ∈ Subgroup.centralizer (A : Set G) := by
  unfold lambdaW at hd
  have hC := (Subgroup.mem_inf.mp hd).2
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_iff.mp hC y (e16e2_le_mGrp hA hy)

theorem lambdaW_eq (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    lambdaW Ω W = zGroup Ω ⊓ Subgroup.centralizer (K : Set G) ⊓
      Subgroup.centralizer ((conjSub g K : Subgroup G) : Set G) := by
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW
  have hJD : conjSub g K ∈ DSet Ω W :=
    e16e2_conj_mem_dSet h hKD (e16e2_mGrp_le_normalizer h c.data.hg)
  have hJu : IsUniqueInvolution (conjSub g K) (u * e) := by
    have := c.twin.isInv.conj g
    rwa [c.data.hgt] at this
  have hJt : conjSub g K ∉ twinSet Ω K := by
    intro hJtw
    obtain ⟨-, z', hz'K, hz'J⟩ := hJtw
    exact (e16e2_zt_ne c).1 ((c.twin.isInv.eq hz'K).trans (hJu.eq hz'J).symm)
  ext d
  constructor
  · intro hd
    unfold lambdaW at hd
    obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hdD, Subgroup.mem_centralizer_iff.mpr
      fun y hy => Subgroup.mem_centralizer_iff.mp hdC y (e16e2_le_mGrp hKD hy)⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hdC y (e16e2_le_mGrp hJD hy)⟩
  · intro hd
    obtain ⟨hdDK, hdJ⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨hdD, hdK⟩ := Subgroup.mem_inf.mp hdDK
    exact e16e2_lambda_of_pair c h h9 h13 hKD hJD hJt hdD hdK hdJ

theorem lambdaW_eq_of_mem (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ DSet Ω W)
    (hJ₂ : J₂ ∈ DSet Ω W) (hne : J₂ ∉ twinSet Ω J₁) :
    lambdaW Ω W = zGroup Ω ⊓ Subgroup.centralizer (J₁ : Set G) ⊓
      Subgroup.centralizer (J₂ : Set G) := by
  ext d
  constructor
  · intro hd
    unfold lambdaW at hd
    obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hdD, Subgroup.mem_centralizer_iff.mpr
      fun y hy => Subgroup.mem_centralizer_iff.mp hdC y (e16e2_le_mGrp hJ₁ hy)⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hdC y (e16e2_le_mGrp hJ₂ hy)⟩
  · intro hd
    obtain ⟨hdDJ, hdJ₂⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨hdD, hdJ₁⟩ := Subgroup.mem_inf.mp hdDJ
    exact e16e2_lambda_of_pair c h h9 h13 hJ₁ hJ₂ hne hdD hdJ₁ hdJ₂

private theorem e16e2_J_facts (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) :
    K ∈ DSet Ω W ∧ conjSub g K ∈ DSet Ω W ∧ IsUniqueInvolution (conjSub g K) (u * e) ∧
      conjSub g K ∉ twinSet Ω K := by
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW
  have hJD : conjSub g K ∈ DSet Ω W :=
    e16e2_conj_mem_dSet h hKD (e16e2_mGrp_le_normalizer h c.data.hg)
  have hJu : IsUniqueInvolution (conjSub g K) (u * e) := by
    have := c.twin.isInv.conj g
    rwa [c.data.hgt] at this
  refine ⟨hKD, hJD, hJu, ?_⟩
  intro hJtw
  obtain ⟨-, z', hz'K, hz'J⟩ := hJtw
  exact (e16e2_zt_ne c).1 ((c.twin.isInv.eq hz'K).trans (hJu.eq hz'J).symm)

theorem inf_normalizer_eq_lambdaW (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) :
    zGroup Ω ⊓ Subgroup.centralizer (K : Set G) ⊓
        Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) =
      lambdaW Ω W ⊔ Subgroup.zpowers z := by
  obtain ⟨hKD, hJD, hJu, hJt⟩ := e16e2_J_facts c h
  have hKΩ : K ∈ Ω := c.twin.mem
  have hJΩ : conjSub g K ∈ Ω := (h.mem_dSet_iff.mp hJD).1
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp
      ((h.normalizer_twin c.twin).2 (Subgroup.le_normalizer hy))
  have hzJ : z ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
    have hJst : conjSub g K ∈ omegaStarNbr Ω K :=
      (h.mem_omegaStarNbr_or_twinSet h9 hKΩ hJΩ hJu
        (e16e2_S_normalizes_K c h (Or.inr (Or.inl rfl)))).resolve_right hJt
    have hJn : conjSub g K ∉ omegaNbr Ω K := h.notMem_omegaNbr_of_notMem_twinSet h9 hKΩ hJt
    obtain ⟨hcU, hU4, -, -, -, -⟩ := pair_structure h hKΩ hJst hJn
    obtain ⟨u₀, hu₀U, hu₀4, -⟩ := perpP_gen hcU hU4
    have h4 : u₀ ^ 4 = 1 := by rw [← hu₀4]; exact pow_orderOf_eq_one u₀
    have hw : u₀ ^ 2 ∈ K := K.pow_mem hu₀U.1 2
    have hww : u₀ ^ 2 * u₀ ^ 2 = 1 := by
      calc u₀ ^ 2 * u₀ ^ 2 = u₀ ^ 4 := by group
        _ = 1 := h4
    have hw1 : u₀ ^ 2 ≠ 1 := fun h1 => by
      have hd := orderOf_dvd_of_pow_eq_one h1
      rw [hu₀4] at hd
      omega
    have hsq : u₀ ^ 2 = z := (c.twin.isInv.unique _ hw hww).resolve_left hw1
    have hmem := (Subgroup.pow_mem (K ⊓ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G))
      hu₀U 2).2
    rwa [hsq] at hmem
  ext x
  constructor
  · intro hx
    obtain ⟨hxZK, hxJ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxD, hxK⟩ := Subgroup.mem_inf.mp hxZK
    have hcR : K ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxK y hy)
    rcases EndHyp.centralizer_or_mul h h9 c.twin h13 hKΩ hJΩ c.twin.isInv hJu hxD hcR hzJ hxJ
      with h1 | h2
    ·
      have hxC : x ∈ Subgroup.centralizer ((conjSub g K : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy =>
          Subgroup.mem_centralizer_singleton_iff.mp (h1 hy)
      exact Subgroup.mem_sup_left (e16e2_lambda_of_pair c h h9 h13 hKD hJD hJt hxD hxK hxC)
    ·
      have hxzC : x * z ∈ Subgroup.centralizer ((conjSub g K : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy =>
          Subgroup.mem_centralizer_singleton_iff.mp (h2 hy)
      have hxzL := e16e2_lambda_of_pair c h h9 h13 hKD hJD hJt ((zGroup Ω).mul_mem hxD hzD)
        (Subgroup.mul_mem _ hxK hzK) hxzC
      have key : x * z * z ∈ lambdaW Ω W ⊔ Subgroup.zpowers z :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hxzL) (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers z))
      rwa [mul_assoc, c.twin.isInv.sq, mul_one] at key
  · intro hx
    have hle : lambdaW Ω W ⊔ Subgroup.zpowers z ≤
        zGroup Ω ⊓ Subgroup.centralizer (K : Set G) ⊓
          Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
      refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
      ·
        unfold lambdaW at hy
        obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.mp hy
        have hyK : y ∈ Subgroup.centralizer (K : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun w hw =>
            Subgroup.mem_centralizer_iff.mp hyC w (e16e2_le_mGrp hKD hw)
        have hyJ : y ∈ Subgroup.centralizer ((conjSub g K : Subgroup G) : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun w hw =>
            Subgroup.mem_centralizer_iff.mp hyC w (e16e2_le_mGrp hJD hw)
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyD, hyK⟩,
          Subgroup.centralizer_le_normalizer _ hyJ⟩
      · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzD, hzK⟩, hzJ⟩
    exact hle hx

theorem lambdaW_inf_zpowers (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) : lambdaW Ω W ⊓ Subgroup.zpowers z = ⊥ := by
  obtain ⟨hKD, hJD, hJu, -⟩ := e16e2_J_facts c h
  have hJΩ : conjSub g K ∈ Ω := (h.mem_dSet_iff.mp hJD).1
  have hzL : z ∉ lambdaW Ω W := by
    intro hz
    have hzJ := e16e2_cent_of_lambda hz hJD
    have hJz : IsUniqueInvolution (conjSub g K) z :=
      h.involution_eq_of_le_centralizer h9 c.twin.mem hJΩ c.twin.isInv
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hzJ y hy))
    exact (e16e2_zt_ne c).1 (hJz.eq hJu)
  have hzo : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact c.twin.isInv.sq) c.twin.isInv.ne_one
  have hzo' : (orderOf z : ℤ) = 2 := by rw [hzo]; norm_num
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxZ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxZ
  have hk : z ^ k = z ^ (k % 2) := by
    rw [← hzo']
    exact (zpow_mod_orderOf z k).symm
  rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with h0 | h1
  · rw [Subgroup.mem_bot, hk, h0, zpow_zero]
  · exfalso
    apply hzL
    rw [hk, h1, zpow_one] at hxL
    exact hxL

private theorem e16e2_betaPt_zero_iff (h : EndHyp Ω) (h9 : Perp9 Ω)
    (s : TwinSit Ω K K' z) {J : Subgroup G} (hJ : J ∈ Ω) {b : G}
    (hb : IsUniqueInvolution J b) (x : G) :
    betaPt Ω b x = 0 ↔ x ∈ Subgroup.normalizer (J : Set G) := by
  rw [h.betaPt_eq h9 s hJ hb x]
  unfold bnorm
  by_cases hx : x ∈ Subgroup.normalizer (J : Set G) <;> simp [hx]

theorem natCard_zGroup_eq_sixteen_mul (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ ε : ℕ, ε ∈ ({1, 2} : Set ℕ) ∧ Nat.card (zGroup Ω) = 16 * ε * Nat.card (lambdaW Ω W) ∧
      (ε = 2 ↔ ∃ d ∈ zGroup Ω ⊓ Subgroup.centralizer (K : Set G),
        d ∉ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G)) := by
  obtain ⟨hKD, hJD, hJu, hJt⟩ := e16e2_J_facts c h
  have hKΩ : K ∈ Ω := c.twin.mem
  have hJΩ : conjSub g K ∈ Ω := (h.mem_dSet_iff.mp hJD).1
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hKΩ, c.twin.isInv⟩
  have hDc : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have hzo : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact c.twin.isInv.sq) c.twin.isInv.ne_one
  have hΛD : lambdaW Ω W ≤ zGroup Ω := fun y hy => by
    unfold lambdaW at hy
    exact (Subgroup.mem_inf.mp hy).1
  have hzC : z ∈ Subgroup.centralizer ((lambdaW Ω W : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => hDc y (hΛD hy) z hzD
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer ((lambdaW Ω W : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hzC)
  have hcardZ : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  have hinfZ : Subgroup.zpowers z ⊓ lambdaW Ω W = ⊥ := by
    rw [inf_comm]
    exact lambdaW_inf_zpowers c h h9 h13
  have hcardL : Nat.card ↥(lambdaW Ω W ⊔ Subgroup.zpowers z) = 2 * Nat.card (lambdaW Ω W) := by
    have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hzN
    rw [hinfZ, hcardZ, Subgroup.card_bot, sup_comm] at hprod
    omega
  have hD8 := h.natCard_zGroup_eq_eight_mul h9 c.twin h13
  have hH : Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) ⊓
      (zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) = lambdaW Ω W ⊔ Subgroup.zpowers z := by
    rw [inf_comm]
    exact inf_normalizer_eq_lambdaW c h h9 h13
  have hrel := Subgroup.relIndex_mul_card (H := Subgroup.normalizer
    ((conjSub g K : Subgroup G) : Set G)) (K := zGroup Ω ⊓ Subgroup.centralizer (K : Set G))
  rw [hH, hcardL] at hrel
  by_cases hcase : ∃ d ∈ zGroup Ω ⊓ Subgroup.centralizer (K : Set G),
      d ∉ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G)
  · obtain ⟨d, hdF, hdN⟩ := hcase
    have hdD : d ∈ zGroup Ω := (Subgroup.mem_inf.mp hdF).1
    have hbetaZ := e16e2_betaPt_zero_iff h h9 c.twin hJΩ hJu
    have hβd : betaPt Ω (u * e) d = 1 := by
      have hne : betaPt Ω (u * e) d ≠ 0 := fun h0 => hdN ((hbetaZ d).mp h0)
      exact (show ∀ y : ZMod 2, y ≠ 0 → y = 1 by decide) _ hne
    have hbz : u * e ∈ zSet Ω := ⟨conjSub g K, hJΩ, hJu⟩
    have hidx : (Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G)).relIndex
        (zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) = 2 := by
      unfold Subgroup.relIndex
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨d, hdF⟩, fun b => ?_⟩
      have hbD : (b : G) ∈ zGroup Ω := (Subgroup.mem_inf.mp b.2).1
      have hmul : betaPt Ω (u * e) ((b : G) * d) = betaPt Ω (u * e) (b : G) + 1 := by
        rw [h.betaPt_mul h9 c.twin h13 hbz hbD hdD, hβd]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        ← hbetaZ, ← hbetaZ, hmul]
      generalize betaPt Ω (u * e) (b : G) = y
      revert y
      decide
    refine ⟨2, by simp, ?_, ⟨fun _ => ⟨d, hdF, hdN⟩, fun _ => rfl⟩⟩
    rw [hD8, ← hrel, hidx]
    ring
  · push Not at hcase
    have hidx : (Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G)).relIndex
        (zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) = 1 :=
      Subgroup.relIndex_eq_one.mpr (fun x hx => hcase x hx)
    refine ⟨1, by simp, ?_, ⟨fun h1 => absurd h1 (by norm_num), fun ⟨d, hdF, hdN⟩ =>
      absurd (hcase d hdF) hdN⟩⟩
    rw [hD8, ← hrel, hidx]
    ring

theorem le_centralizer_of_mem_lambdaW (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) {M : Subgroup G} (hM : M ∈ Ω) {d : G} (hd : d ∈ lambdaW Ω W)
    (hz : z ∈ Subgroup.normalizer (M : Set G)) (ht : u * e ∈ Subgroup.normalizer (M : Set G))
    (hdM : d ∈ Subgroup.normalizer (M : Set G)) : M ≤ Subgroup.centralizer ({d} : Set G) := by
  obtain ⟨hKD, hJD, hJu, -⟩ := e16e2_J_facts c h
  have hKΩ : K ∈ Ω := c.twin.mem
  have hJΩ : conjSub g K ∈ Ω := (h.mem_dSet_iff.mp hJD).1
  obtain ⟨I, hI, hIx⟩ := c.exists_dSet_zt h h9
  have hIΩ : I ∈ Ω := (h.mem_dSet_iff.mp hI).1
  have hdD : d ∈ zGroup Ω := by
    unfold lambdaW at hd
    exact (Subgroup.mem_inf.mp hd).1
  have hdK := e16e2_cent_of_lambda hd hKD
  have hdJ := e16e2_cent_of_lambda hd hJD
  have hdI := e16e2_cent_of_lambda hd hI
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hKΩ, c.twin.isInv⟩
  have htD : u * e ∈ zGroup Ω := (zGroup Ω).mul_mem (c.u_mem_zGroup h h9 h13).1
    (c.u_mem_zGroup h h9 h13).2
  have hzt : z * (u * e) ∈ Subgroup.normalizer (M : Set G) := Subgroup.mul_mem _ hz ht
  have hDc : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have hDsq : ∀ a ∈ zGroup Ω, a * a = 1 := h.zGroup_mul_self h9
  have hz2 : z * z = 1 := c.twin.isInv.sq
  obtain ⟨p, hp⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hM
  by_contra hcon
  have hA1 := EndHyp.centralizer_or_mul h h9 c.twin h13 hKΩ hM c.twin.isInv hp hdD
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hdK y hy))
    hz hdM
  have hA2 := EndHyp.centralizer_or_mul h h9 c.twin h13 hJΩ hM hJu hp hdD
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hdJ y hy))
    ht hdM
  have hA3 := EndHyp.centralizer_or_mul h h9 c.twin h13 hIΩ hM hIx hp hdD
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hdI y hy))
    hzt hdM
  have m1 : d * z ∈ Subgroup.centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp ((hA1.resolve_left hcon) hy)
  have m2 : d * (u * e) ∈ Subgroup.centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp ((hA2.resolve_left hcon) hy)
  have m3 : d * (z * (u * e)) ∈ Subgroup.centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp ((hA3.resolve_left hcon) hy)
  have hzd : z * d = d * z := hDc z hzD d hdD
  have e1 : (d * z) * (d * (u * e)) = z * (u * e) := by
    calc (d * z) * (d * (u * e)) = d * (z * d) * (u * e) := by group
      _ = d * (d * z) * (u * e) := by rw [hzd]
      _ = (d * d) * z * (u * e) := by group
      _ = z * (u * e) := by rw [hDsq d hdD, one_mul]
  have e2 : (d * z) * (d * (z * (u * e))) = u * e := by
    calc (d * z) * (d * (z * (u * e))) = d * (z * d) * (z * (u * e)) := by group
      _ = d * (d * z) * (z * (u * e)) := by rw [hzd]
      _ = (d * d) * (z * z) * (u * e) := by group
      _ = u * e := by rw [hDsq d hdD, hz2, one_mul, one_mul]
  have hzt' : z * (u * e) ∈ Subgroup.centralizer (M : Set G) := by
    rw [← e1]
    exact Subgroup.mul_mem _ m1 m2
  have ht' : u * e ∈ Subgroup.centralizer (M : Set G) := by
    rw [← e2]
    exact Subgroup.mul_mem _ m1 m3
  have hz' : z ∈ Subgroup.centralizer (M : Set G) := by
    have eq : z = z * (u * e) * (u * e)⁻¹ := by group
    rw [eq]
    exact Subgroup.mul_mem _ hzt' (Subgroup.inv_mem _ ht')
  have hd' : d ∈ Subgroup.centralizer (M : Set G) := by
    have eq : d = d * z * z⁻¹ := by group
    rw [eq]
    exact Subgroup.mul_mem _ m1 (Subgroup.inv_mem _ hz')
  exact hcon (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hd' m hm))

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
