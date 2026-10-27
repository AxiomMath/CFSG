module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6P1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Bst
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6G2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Syl
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Eig
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Enl
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem main_cfg (hMin : MinIndexL34) (hInv : InvSec)
    (hstar : KStarL34) (hno3L : KNoOrder3L34) (hkb : KB813) (h171 : Prop17_1)
    (hL31 : Lemma31Narrow) (hB12 : Bender12) (h183 : Lemma18_3a) (h184 : Lemma18_4ac)
    (hKA : IVK_8_13_lift) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) (hZE : omega1Z p (Op p M) ≤ E) {X : Subgroup G}
    (hXv : ∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) (hXM : ¬ X ≤ M) (hXG : X ≠ ⊤)
    {J : Subgroup G} (hJ : IsCompIn X J) (hLie : IsL34Quotient ↥J) : False := by
  obtain ⟨hMz, hz2', hz2, hp, hp2, hMc, hsimple, hzV, hVle, hZP, hZV, hZodd, hMZ, hZbot, hNZ, hEO,
    hZO⟩ := P2S4.CtxFacts.of_ctx h171 hctx
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hF := S5Facts.of_ctx h171 hctx
  have hq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  obtain ⟨hJz, hzN, hJZ, hVN⟩ := cfg_basic h171 hL31 h183 hctx hXv hXM hXG hJ
  have hZc := cfg_odd_center hMin hInv hS2 hq hLie
  obtain ⟨-, hp3, -, -, -, -⟩ := cfg_star hMin hInv hstar h171 hL31 h183 hctx hXv hXM hXG hJ hLie
  obtain ⟨hZN, hZnc⟩ := cfg_Z_facts h171 hL31 h183 hctx hXv hXM hXG hJ
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2'
    omega
  obtain ⟨g, hwJ, hwz⟩ := exists_central_conj_mem_comm hS2.central hS2.std.rank.2 hzN
    (exists_elem_four hkb hLie hZc).choose_spec.1 (exists_elem_four hkb hLie hZc).choose_spec.2.1
    (exists_elem_four hkb hLie hZc).choose_spec.2.2
  set w : G := g * z * g⁻¹ with hw
  have hw2 : w * w = 1 := by
    calc w * w = g * (z * z) * g⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hz2]; group
  have hw1 : w ≠ 1 := fun h => hz1 (by
    have : g⁻¹ * w * g = z := by rw [hw]; group
    rw [← this, h]
    group)
  obtain ⟨e, heE, he1, heJ⟩ :=
    exists_cent_elem hMin hInv hstar h171 hL31 h183 hctx hXv hXM hXG hJ hLie
  obtain ⟨I, hI, hJI, hLieI⟩ := part1 hMin hInv hstar hkb h171 hL31 hB12 h183 h184 hKA hctx hZE
    hXv hXM hXG hJ hLie heE he1 heJ
  have hIq : IsQuasisimple ↥I := P2S3.quasisimple_of_isCompIn hI
  have hZI : Odd (Nat.card (center ↥I)) := cfg_odd_center hMin hInv hS2 hIq hLieI
  have hwI : w ∈ I := hJI hwJ
  have hKM : ¬ centralizer ({e} : Set G) ≤ M := fun h =>
    not_le_of_comm hq hJz (hMz ▸ heJ.trans h)
  have hKG : centralizer ({e} : Set G) ≠ ⊤ := centralizer_ne_top hF.hkps he1
  obtain ⟨hzC, hVC, -, -⟩ := centralizer_facts hB12 h171 hctx heE
  have hno3H : ∀ K₁ K₂ K₃ : Subgroup ↥(centralizer ({e} : Set G)), IsComponent K₁ →
      IsComponent K₂ → IsComponent K₃ → K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun K₁ K₂ K₃ h₁ h₂ h₃ =>
    P2S3.comps_le_two hL31 hS2 hKG hzC h₁ h₂ h₃
  set Z : Subgroup G := omega1Z p (Op p M) with hZdef
  set U : Subgroup G := cj g Z with hU
  have hMw : centralizer ({w} : Set G) = cj g M := by
    rw [hMz, cj_centralizer]
  have hMwN : ∀ y ∈ centralizer ({w} : Set G), y ∈ normalizer (U : Set G) := by
    intro y hy
    rw [hMw, mem_cj] at hy
    exact mem_normalizer_cj (hMZ hy)
  have hew : e ∈ centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (heJ hwJ)).symm
  have hzw : z ∈ centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hwz.symm
  have hUp : IsPGroup p ↥U := isPGroup_cj g ((isPGroup_Op p hp M).to_le hZP)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    rw [hU, mem_cj] at ha hb
    have h1 := hZP ha
    have h2 := (ha.2.1 _ (hZP hb))
    have : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) := h2
    calc a * b = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group
  have hU1 : U ≠ ⊥ := fun h => hZbot ((Subgroup.map_eq_bot_iff_of_injective _
    (MulAut.conj g).injective).mp h)
  have hEel : IsElementaryAbelian p ↥E := hctx.E_elem
  have hep : e ^ p = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e heE
  have hez : e * z = z * e :=
    Subgroup.mem_centralizer_singleton_iff.1
      (hMz ▸ Op_le p M (hctx.E_le heE) : e ∈ centralizer ({z} : Set G))
  obtain ⟨u, huU, hu1, heu, hzu⟩ := exists_fixed_eigen hp hUp hUab hU1 (hMwN e hew) (hMwN z hzw)
    hez hz2 hep hp2
  have huZ : g⁻¹ * u * g ∈ Z := mem_cj.mp huU
  have huC : u ∈ centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact heu.symm
  have hMc' : ∀ c : G, c * z = z * c → c ∈ M := fun c hc => by
    rw [hMz]
    exact Subgroup.mem_centralizer_singleton_iff.2 hc
  have huodd : Odd (orderOf u) := by
    have hu2 : (g⁻¹ * u * g) ^ p = 1 := huZ.2.2
    have hup : u ^ p = 1 := by
      have e : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      calc u ^ p = (g * (g⁻¹ * u * g) * g⁻¹) ^ p := by rw [← e]
        _ = g * (g⁻¹ * u * g) ^ p * g⁻¹ := conj_pow
        _ = 1 := by rw [hu2]; group
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hup)
  have huI : u ∈ normalizer (I : Set G) := P2S3.mem_normalizer_of_odd hno3H hI huC huodd
  have hOw : cj g (Op p M) ≤ cj g M := Subgroup.map_mono (Op_le p M)
  have huO : u ∈ cj g (Op p M) := Subgroup.map_mono hZP huU
  have hQ : cj g (Op p M) ⊓ normalizer (I : Set G) ≤ centralizer (I : Set G) :=
    g2_J hstar hIq hLieI hZI hwI hw2 hw1 hp hp2 inf_le_right
      ((isPGroup_cj g (isPGroup_Op p hp M)).to_le inf_le_left)
      (fun x hx => (Subgroup.mem_centralizer_singleton_iff.1
        (show x ∈ centralizer ({w} : Set G) by rw [hMw]; exact hOw hx.1)).symm)
      (fun y hy hyw => by
        have hyw' : y ∈ centralizer ({w} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hyw
        rw [hMw, mem_cj] at hyw'
        exact mem_normalizer_inf' (mem_normalizer_cj (le_normalizer_Op p M hyw'))
          (Subgroup.le_normalizer (Subgroup.le_normalizer hy)))
  have huIC : u ∈ centralizer (I : Set G) := hQ ⟨huO, huI⟩
  have hIC : I ≤ centralizer ({u} : Set G) := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.mp huIC j hj)
  by_cases hcase : centralizer ({u} : Set G) ≤ centralizer ({w} : Set G)
  ·
    apply invol_not_mem_center hZI hwI hw2 hw1
    rw [Subgroup.mem_center_iff]
    intro j
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hcase (hIC j.2)))
  ·
    set u₂ : G := g⁻¹ * u * g with hu₂
    have hu₂Z : u₂ ∈ Z := huZ
    have hu₂E : u₂ ∈ E := hZE hu₂Z
    have hgu : g * u₂ * g⁻¹ = u := by rw [hu₂]; group
    have hu₂1 : u₂ ≠ 1 := fun h => hu1 (by rw [← hgu, h]; group)
    set X₂ : Subgroup G := centralizer ({u₂} : Set G) with hX₂
    have hX₂cj : cj g X₂ = centralizer ({u} : Set G) := by rw [hX₂, cj_centralizer, hgu]
    have hX₂M : ¬ X₂ ≤ M := by
      intro h
      apply hcase
      have h1 : cj g X₂ ≤ cj g M := Subgroup.map_mono h
      rw [hX₂cj] at h1
      rw [hMw]
      exact h1
    have hX₂G : X₂ ≠ ⊤ := centralizer_ne_top hF.hkps hu₂1
    obtain ⟨hz₂C, hVC₂, -, -⟩ := centralizer_facts hB12 h171 hctx hu₂E
    have hX₂v : ∀ v ∈ Vof M E, v ∈ normalizer (X₂ : Set G) := fun v hv =>
      Subgroup.le_normalizer (hVC₂ hv)
    set J₂ : Subgroup G := cj g⁻¹ J with hJ₂
    have hJ₂q : IsQuasisimple ↥J₂ := quasisimple_cj g⁻¹ hq
    have hJ₂Lie : IsL34Quotient ↥J₂ := isL34_cj g⁻¹ hLie
    have hZ₂ : Odd (Nat.card (center ↥J₂)) := cfg_odd_center hMin hInv hS2 hJ₂q hJ₂Lie
    have hzJ₂ : z ∈ J₂ := by
      rw [hJ₂, mem_cj]
      simpa [hw] using hwJ
    have hJ₂X₂ : J₂ ≤ X₂ := by
      have h1 : cj g⁻¹ J ≤ cj g⁻¹ (centralizer ({u} : Set G)) :=
        Subgroup.map_mono (hJI.trans hIC)
      rw [cj_centralizer] at h1
      have : g⁻¹ * u * g⁻¹⁻¹ = u₂ := by rw [hu₂]; group
      rw [this] at h1
      exact h1
    have hJ₂z : ⁅J₂, zpowers z⁆ = J₂ := comm_eq_of_invol hJ₂q hZ₂ hzJ₂ hz2 hz1
    have hJ₂E : J₂ ≤ Em X₂ := J_le_Em_cent hB12 h184 h171 hctx hu₂E hu₂1 hX₂M
      (Subgroup.isPerfect_iff.mp hJ₂q.1) hJ₂X₂ hJ₂z
    have hno3₂ := comps_no3 h183 hctx hX₂v hX₂M hX₂G
    obtain ⟨I₂, hI₂, hJ₂I₂⟩ := exists_comp_of_le_Em hJ₂q hZ₂ (exists_elem_four hkb hJ₂Lie hZ₂)
      (no_involution_cent hMin hInv hS2 hJ₂q hJ₂Lie) hS2.std.rank.2 hno3₂ hJ₂E
    set I' : Subgroup G := cj g I₂ with hI'
    have hI'c : IsCompIn (centralizer ({u} : Set G)) I' := by
      have := isCompIn_cj hI₂ g
      rwa [hX₂cj] at this
    have hJI' : J ≤ I' := by
      have h1 : cj g J₂ ≤ cj g I₂ := Subgroup.map_mono hJ₂I₂
      have h2 : cj g J₂ = J := by
        have := cj_cj_inv g⁻¹ J
        simpa [hJ₂] using this
      rwa [h2] at h1
    have hI'q : IsQuasisimple ↥I' := quasisimple_cj g (P2S3.quasisimple_of_isCompIn hI₂)
    have hJC : J ≤ centralizer ({u} : Set G) := hJI.trans hIC
    set H₀ : Subgroup G := normalizer ((centralizer ({u} : Set G) : Subgroup G) : Set G) with hH₀
    have hH₀top : H₀ ≠ ⊤ := by
      intro h
      have hn : (centralizer ({u} : Set G)).Normal := by
        rw [← Subgroup.normalizer_eq_top_iff]
        exact h
      rcases hsimple.eq_bot_or_eq_top_of_normal (centralizer ({u} : Set G)) with h0 | h0
      · have hmem : u ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
        rw [h0] at hmem
        exact hu1 (Subgroup.mem_bot.1 hmem)
      · exact centralizer_ne_top hF.hkps hu1 h0
    have hzH₀ : z ∈ H₀ := by
      have h1 : z ∈ normalizer ((zpowers u : Subgroup G) : Set G) := by
        refine mem_normalizer_of_forall_conj fun y hy => ?_
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        rw [← conj_zpow]
        rcases hzu with h | h
        · rw [h]
          exact Subgroup.zpow_mem_zpowers u n
        · rw [h, inv_zpow]
          exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers u n)
      exact normalizer_zpowers_le_normalizer_centralizer u h1
    have hI'H₀ : IsCompIn H₀ I' := P2S4.isCompIn_of_normal Subgroup.le_normalizer le_rfl hI'c
    have hzI' : z ∈ normalizer (I' : Set G) := normalizer_of_le_comp hI'H₀ hzH₀ hq hJI' hzN
    have hI'z : ⁅I', zpowers z⁆ = I' := by
      refine commutator_eq_of_not_le_centralizer hI'q (Subgroup.zpowers_le.mpr hzI') ?_
      intro h
      have h1 : ⁅J, zpowers z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (fun j hj => Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (Subgroup.mem_centralizer_iff.mp (h hy) j (hJI' hj)).symm)
      rw [hJz] at h1
      have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hq
      exact (Subgroup.nontrivial_iff_ne_bot J).mp this h1
    have hnc : ¬ IsCyclic ↥(Pbar J (Op p M ⊓ J)) :=
      bst_noncyclic hstar hkb hno3L hq hLie hZc hzN hz2 hJz hp hp2 (isPGroup_Op p hp M)
        (fun x hx => (Subgroup.mem_centralizer_singleton_iff.1
          (hMz ▸ Op_le p M hx : x ∈ centralizer ({z} : Set G))).symm)
        (fun y _ hyz => le_normalizer_Op p M (hMc' y hyz))
        (fun hle => hZnc fun x hx => hle ⟨hZP hx, hZN hx⟩) hwJ hw2 hwz hw1
    have hLieI' : IsL34Quotient ↥I' :=
      isL34_of_noncyclic hKA hS2 hMz hz2' hp hp2 hH₀top hI'H₀ hI'q hq hzI' hI'z hJI'
        (Q := Op p M ⊓ J)
        (fun x hx => ⟨⟨⟨hx.1, Subgroup.le_normalizer (hJC hx.2)⟩,
          Subgroup.le_normalizer (hJI' hx.2)⟩, Subgroup.le_normalizer hx.2⟩) hnc
    have hLieI₂ : IsL34Quotient ↥I₂ := by
      have h1 := isL34_cj g⁻¹ hLieI'
      have e : cj g⁻¹ I' = I₂ := by rw [hI']; exact cj_cj_inv g I₂
      rwa [e] at h1
    obtain ⟨hzN₂, -, -, hninn, -, -⟩ := cfg_star hMin hInv hstar h171 hL31 h183 hctx hX₂v hX₂M
      hX₂G hI₂ hLieI₂
    exact hninn (alphaZ_mem_innSub (hJ₂I₂ hzJ₂))

theorem lemma18_6_of (hMin : MinIndexL34) (hInv : InvSec)
    (hstar : KStarL34) (hno3L : KNoOrder3L34) (hkb : KB813) (h171 : Prop17_1)
    (hL31 : Lemma31Narrow) (hB12 : Bender12) (h183 : Lemma18_3a) (h184 : Lemma18_4ac)
    (hKA : IVK_8_13_lift) : Lemma18_6 := by
  intro G _ _ z k S M p E t hctx X hXv hXM hXG J hJ hLie
  have hp : p.Prime := hctx.prime
  have hV : Vof M (E ⊔ omega1Z p (Op p M)) = Vof M E := Vof_sup_omega1Z M E hp
  exact main_cfg hMin hInv hstar hno3L hkb h171 hL31 hB12 h183 h184 hKA hctx.sup_omega1Z
    le_sup_right (fun v hv => hXv v (hV ▸ hv)) hXM hXG hJ hLie

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
