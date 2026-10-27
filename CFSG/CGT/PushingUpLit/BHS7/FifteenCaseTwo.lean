module

public import CFSG.CGT.PushingUpLit.BHS7.FifteenSub
public import CFSG.CGT.PushingUpLit.BHS7.FifteenSym
public import CFSG.CGT.PushingUpLit.BHS7.FifteenJ
public import CFSG.CGT.PushingUpLit.BHS7.FiveCaseTwo

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem isNat_of_eq_comp {V : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hGN : G ≤ Subgroup.normalizer (V : Set Γ)) {E : Subgroup (MulAut ↥V)} (hEq : autOn G V = E)
    (htype : @IsCompType ↥V (commGroupOfElemAbelian hV) E) :
    (∃ n : ℕ, 1 ≤ n ∧ IsNatSL G V n) ∨ (∃ m : ℕ, 1 ≤ m ∧ IsNatSym G V (2 * m + 1)) := by
  classical
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hGW : G ≤ Subgroup.normalizer ((⁅V, G⁆ : Subgroup Γ) : Set Γ) :=
    le_normalizer_commutator hGN (fun g hg => Subgroup.le_normalizer hg)
  have hWV : (⁅V, G⁆ : Subgroup Γ) ≤ V :=
    (Subgroup.commutator_comm V G).le.trans (commutator_le_of_le_normalizer hGN)
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => isElemAbelian_comm' hV hx hy
  have hker : ∀ (_ : ∀ v ∈ V, ∃ w ∈ (⁅V, G⁆ : Subgroup Γ),
      ∃ c ∈ V ⊓ Subgroup.centralizer (G : Set Γ), v = w * c),
      G ⊓ Subgroup.centralizer (V : Set Γ) =
        G ⊓ Subgroup.centralizer ((⁅V, G⁆ : Subgroup Γ) : Set Γ) := by
    intro hdec
    refine le_antisymm (inf_le_inf_left G (Subgroup.centralizer_le hWV)) fun g hg => ?_
    obtain ⟨hgG, hgW⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_inf.mpr ⟨hgG, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv'
    obtain ⟨w, hw, c, hc, rfl⟩ := hdec v hv'
    have h1 : w * g = g * w := Subgroup.mem_centralizer_iff.mp hgW w hw
    have h2 : g * c = c * g :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 g hgG)
    calc w * c * g = w * (c * g) := by group
      _ = w * (g * c) := by rw [h2]
      _ = (w * g) * c := by group
      _ = (g * w) * c := by rw [h1]
      _ = g * (w * c) := by group
  rcases htype with ⟨D, n, hn, hnat, htop, -⟩ | ⟨M, D, m, θ, β, hm, h3, hinv, hsurj, hker', hequiv,
    htop, -, -⟩
  · left
    refine ⟨n, by omega, ?_⟩
    have hnatG := isNatSL_of_slType hV hGN hEq hnat htop
    have hdec := exists_decomp_of_top hV hGN (hEq ▸ htop)
    exact isNatSL_iff.mpr (isNatBy_of_decomp (isNatSL_iff.mp hnatG) hWV hGW hVab hdec (hker hdec))
  · right
    let D' : SymDat E m := ⟨θ, β, hm, h3, hinv, hsurj, hker', hequiv, htop⟩
    obtain ⟨k, hk⟩ := hm
    have hnatG := isNatSym_of_symDat hV hGN hEq D'
    have hdec := exists_decomp_of_top hV hGN (hEq ▸ htop)
    refine ⟨k, by omega, ?_⟩
    rw [← hk]
    exact isNatSym_iff.mpr (isNatBy_of_decomp (isNatSym_iff.mp hnatG) hWV hGW hVab hdec
      (hker hdec))

theorem faithful_of_decomp (hG : CharTwo G) (hT : IsSylowTwoOf T G)
    {E : Subgroup (MulAut ↥(vSub G T))}
    (htop : @commV ↥(vSub G T) (commGroupOfElemAbelian (isElemAbelian_vSub hG hT)) E ⊔
      @fixV ↥(vSub G T) (commGroupOfElemAbelian (isElemAbelian_vSub hG hT)) E = ⊤)
    (hGE : ∀ y ∈ autOn G (vSub G T), y ∈ Subgroup.normalizer (E : Set (MulAut ↥(vSub G T))))
    (hdec : ∀ y ∈ autOn G (vSub G T), ∃ x ∈ E, ∃ b ∈ autOn (baum T) (vSub G T), y = x * b) :
    ∀ y ∈ autOn G (vSub G T),
      (∀ w ∈ @commV ↥(vSub G T) (commGroupOfElemAbelian (isElemAbelian_vSub hG hT)) E,
        y w = w) → y = 1 := by
  classical
  have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub hG hT
  let _ : CommGroup ↥(vSub G T) := commGroupOfElemAbelian hV
  have hTG : T ≤ G := hT.1
  have hGN : G ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := le_normalizer_vSub G T
  have hBT : baum T ≤ T := inf_le_left
  have hBN : baum T ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) :=
    hBT.trans (hTG.trans hGN)
  set W : Subgroup ↥(vSub G T) := commV E with hW
  set R : Subgroup (MulAut ↥(vSub G T)) := autOn G (vSub G T) ⊓ centSub W with hR
  have hstab : ∀ y ∈ autOn G (vSub G T), y ∈ stabSub W := fun y hy =>
    normalizer_commV_le_stabSub E (hGE y hy)
  have hRinv : ∀ y ∈ autOn G (vSub G T), ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    refine ⟨(autOn G (vSub G T)).mul_mem ((autOn G (vSub G T)).mul_mem hy hr.1)
      ((autOn G (vSub G T)).inv_mem hy), fun w hw => ?_⟩
    have h1 : y⁻¹ w ∈ W := (hstab y⁻¹ ((autOn G (vSub G T)).inv_mem hy) w).2 hw
    have h2 : r (y⁻¹ w) = y⁻¹ w := hr.2 _ h1
    show y (r (y⁻¹ w)) = w
    rw [h2]
    simp
  have hRE : ∀ x ∈ E, x ∈ R → x = 1 := by
    intro x hxE hxR
    ext v
    have hv : v ∈ W ⊔ fixV E := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨w, hwW, c, hcF, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, hxR.2 w hwW, hcF x hxE]
    rfl
  have hB2 : IsPGroup 2 ↥(autOn (baum T) (vSub G T)) :=
    CFSG.CGT.PushingUpLit.BHS6.isPGroup_autOn (hT.2.1.to_le hBT) hBN
  have hBE : autOn (baum T) (vSub G T) ≤ Subgroup.normalizer (E : Set (MulAut ↥(vSub G T))) :=
    fun b hb => hGE b (autOn_le_autOn (vSub G T) (hBT.trans hTG) hb)
  have hR2 : IsPGroup 2 ↥R := by
    intro r
    obtain ⟨x, hx, b, hb, hrxb⟩ := hdec r.1 r.2.1
    obtain ⟨k, hk⟩ := hB2 ⟨b, hb⟩
    obtain ⟨y', hy', hpow⟩ := CFSG.CGT.PushingUpLit.SubTwo.exists_pow_mul_eq hBE hx hb (2 ^ k)
    have hb1 : b ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : ((r ^ 2 ^ k : ↥R) : MulAut ↥(vSub G T)) = y' := by
      rw [Subgroup.coe_pow, hrxb, hpow, hb1, mul_one]
    have h2 : ((r ^ 2 ^ k : ↥R) : MulAut ↥(vSub G T)) ∈ E := h1 ▸ hy'
    exact hRE _ h2 (r ^ 2 ^ k).2
  have hRG : R ≤ autOn G (vSub G T) := inf_le_left
  have hRΓ : liftSub (vSub G T) G R ≤ Subgroup.centralizer ((vSub G T : Subgroup Γ) : Set Γ) := by
    refine le_centralizer_vSub_of_isPGroup_autOn hT (liftSub_le G R) ?_ ?_
    · intro g hg
      refine mem_normalizer_liftSub (hGN hg) hg ?_
      rw [Subgroup.mem_normalizer_iff]
      have hy : conjAct (vSub G T) ⟨g, hGN hg⟩ ∈ autOn G (vSub G T) :=
        mem_autOn_iff.2 ⟨⟨g, hGN hg⟩, hg, rfl⟩
      intro x
      refine ⟨fun hx => hRinv _ hy x hx, fun hx => ?_⟩
      have := hRinv _ ((autOn G (vSub G T)).inv_mem hy) _ hx
      simpa [mul_assoc] using this
    · rw [autOn_liftSub hRG]
      exact hR2
  have hRbot : R = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun r hr => ?_
    have h1 : r ∈ autOn (liftSub (vSub G T) G R) (vSub G T) := by
      rw [autOn_liftSub hRG]
      exact hr
    have h2 := CFSG.CGT.PushingUpLit.BHS.autOn_eq_bot_of_le_centralizer hRΓ
    rw [h2] at h1
    exact h1
  intro y hy hyw
  have : y ∈ R := ⟨hy, hyw⟩
  rw [hRbot] at this
  exact this

theorem caseTwo_natural (h : MinCex G T) {E : Subgroup (MulAut ↥(vSub G T))}
    (hE : @IsCompType ↥(vSub G T)
      (commGroupOfElemAbelian (isElemAbelian_vSub h.charTwo h.sylow)) E)
    (hEG : E ≤ autOn G (vSub G T))
    (hBN : ∀ b ∈ baum T, ∀ hb : b ∈ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ),
      A1b.conjSub (conjAct (vSub G T) ⟨b, hb⟩) E = E)
    (hH : baum T ⊔ liftSub (vSub G T) G E = G) :
    (∃ n : ℕ, 1 ≤ n ∧ IsNatSL G (vSub G T) n) ∨
      (∃ m : ℕ, 1 ≤ m ∧ IsNatSym G (vSub G T) (2 * m + 1)) := by
  classical
  have hG := h.charTwo
  have hT : IsSylowTwoOf T G := h.sylow
  have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub hG hT
  let _ : CommGroup ↥(vSub G T) := commGroupOfElemAbelian hV
  have hTG : T ≤ G := hT.1
  have hGN : G ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := le_normalizer_vSub G T
  have hTN : T ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := hTG.trans hGN
  have hVT : vSub G T ≤ T := (vSub_le_pCoreOf hG hT).trans hT.pCoreOf_le
  have hV2 : ∀ v : ↥(vSub G T), v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hV.2 v v.2)
  have hBT : baum T ≤ T := inf_le_left
  have hBNV : baum T ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) :=
    hBT.trans hTN
  have htop : commV E ⊔ fixV E = ⊤ :=
    hE.elim (fun ⟨_, hD⟩ => SLType2.commV_sup_fixV hD) (fun ⟨_, _, hD⟩ => SymType.commV_sup_fixV hD)
  have hbarN : ∀ b ∈ baum T, ∀ hb : b ∈ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ),
      conjAct (vSub G T) ⟨b, hb⟩ ∈ Subgroup.normalizer (E : Set (MulAut ↥(vSub G T))) :=
    fun b hb hbN => mem_normalizer_of_conjSub_eq (hBN b hb hbN)
  have hBTÊ : baum T ≤ Subgroup.normalizer ((liftSub (vSub G T) G E : Subgroup Γ) : Set Γ) :=
    fun b hb => mem_normalizer_liftSub (hBNV hb) (hTG (hBT hb)) (hbarN b hb (hBNV hb))
  have hdecG : ∀ g ∈ G, ∃ x ∈ liftSub (vSub G T) G E, ∃ b ∈ baum T, g = x * b := by
    intro g hg
    have : g ∈ liftSub (vSub G T) G E ⊔ baum T := by
      rw [sup_comm, hH]
      exact hg
    exact exists_mul_of_mem_sup hBTÊ this
  have hdec : ∀ y ∈ autOn G (vSub G T), ∃ x ∈ E, ∃ b ∈ autOn (baum T) (vSub G T), y = x * b := by
    intro y hy
    obtain ⟨a, haG, rfl⟩ := mem_autOn_iff.1 hy
    obtain ⟨x, hxÊ, b, hb, hab⟩ := hdecG a haG
    obtain ⟨-, hxN, hxE⟩ := mem_liftSub_iff.1 hxÊ
    have hbN : b ∈ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := hBNV hb
    refine ⟨conjAct (vSub G T) ⟨x, hxN⟩, hxE, conjAct (vSub G T) ⟨b, hbN⟩,
      mem_autOn_iff.2 ⟨⟨b, hbN⟩, hb, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hab
  have hBbarN : autOn (baum T) (vSub G T) ≤
      Subgroup.normalizer (E : Set (MulAut ↥(vSub G T))) := by
    intro b hb
    obtain ⟨b', hb'B, rfl⟩ := mem_autOn_iff.1 hb
    exact hbarN _ hb'B b'.2
  have hGE : ∀ y ∈ autOn G (vSub G T),
      y ∈ Subgroup.normalizer (E : Set (MulAut ↥(vSub G T))) := by
    intro y hy
    obtain ⟨x, hx, b, hb, rfl⟩ := hdec y hy
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hx) (hBbarN hb)
  have hfaith := faithful_of_decomp hG hT htop hGE hdec
  have hstab : ∀ y ∈ autOn G (vSub G T), y ∈ stabSub (commV E) := fun y hy =>
    normalizer_commV_le_stabSub E (hGE y hy)
  have hres_of : ∀ (y : MulAut ↥(vSub G T)) (hy : y ∈ autOn G (vSub G T)),
      resHom (commV E) ⟨y, hstab y hy⟩ ∈ autSub E (commV E) → y ∈ E := by
    intro y hy hmem
    obtain ⟨g, hgE, hg⟩ := mem_autSub.1 hmem
    have h1 : (g : MulAut ↥(vSub G T))⁻¹ * y = 1 := hfaith _
      ((autOn G (vSub G T)).mul_mem ((autOn G (vSub G T)).inv_mem (hEG hgE)) hy) (fun w hw => by
        have h2 := congrArg (fun φ : MulAut ↥(commV E) => ((φ ⟨w, hw⟩ : ↥(commV E)) :
          ↥(vSub G T))) hg
        simp only [resHom_apply] at h2
        show (g : MulAut ↥(vSub G T))⁻¹ (y w) = w
        rw [← h2]
        simp)
    have : y = g := by
      have h3 := congrArg ((g : MulAut ↥(vSub G T)) * ·) h1
      simpa using h3
    rw [this]
    exact hgE
  have hGle : autOn G (vSub G T) ≤ E := by
    rcases hE with ⟨D, hSL⟩ | ⟨M, D, hSym⟩
    ·
      obtain ⟨n, hn, hnat, -, -⟩ := hSL
      have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
      have hXdef := autOn_thompsonJ_eq_iSup (V := vSub G T) hTN
      have hoff := jFamily_isOff hV hVT hTN
      have hX2 : IsPGroup 2 ↥(autOn (thompsonJ T) (vSub G T)) :=
        CFSG.CGT.PushingUpLit.BHS6.isPGroup_autOn (hT.2.1.to_le hJT) (hJT.trans hTN)
      have hXG : autOn (thompsonJ T) (vSub G T) ≤ autOn G (vSub G T) :=
        autOn_le_autOn (vSub G T) (hJT.trans hTG)
      have hXQ : autOn (thompsonJ T) (vSub G T) ≤ autOn (baum T) (vSub G T) :=
        autOn_le_autOn (vSub G T) (B6.thompsonJ_le_baum T)
      have hfix := fixV_autOn_thompsonJ_le hV hVT hTN
      have hQ2 : IsPGroup 2 ↥(autOn (baum T) (vSub G T)) :=
        CFSG.CGT.PushingUpLit.BHS6.isPGroup_autOn (hT.2.1.to_le hBT) hBNV
      have hQG : autOn (baum T) (vSub G T) ≤ autOn G (vSub G T) :=
        autOn_le_autOn (vSub G T) (hBT.trans hTG)
      by_cases hX0 : autOn (thompsonJ T) (vSub G T) = ⊥
      ·
        have hQbot : autOn (baum T) (vSub G T) = ⊥ := by
          refine (Subgroup.eq_bot_iff_forall _).2 fun q hq => ?_
          refine MulEquiv.ext fun v => ?_
          have hv : v ∈ fixV (autOn (thompsonJ T) (vSub G T)) := by
            rw [hX0]
            intro x hx
            rw [Subgroup.mem_bot.1 hx]
            rfl
          exact (mem_fixV.mp (hfix hv)) q hq
        intro y hy
        obtain ⟨x, hx, b, hb, rfl⟩ := hdec y hy
        rw [hQbot, Subgroup.mem_bot] at hb
        rw [hb, mul_one]
        exact hx
      · have hne : ∃ A ∈ jFamily T (vSub G T), ¬ A ≤ centSub (commV E) := by
          by_contra hcon
          push Not at hcon
          apply hX0
          have hle : autOn (thompsonJ T) (vSub G T) ≤ centSub (commV E) := by
            rw [hXdef]
            exact iSup₂_le fun A hA => hcon A hA
          exact (Subgroup.eq_bot_iff_forall _).2 fun x hx => hfaith x (hXG hx) (hle hx)
        obtain ⟨-, hQ, hXE⟩ := sl_fix_baum hn hnat hXdef hoff hX2 (hXQ.trans hBbarN) hne
        have hQres := hQ _ hQ2 hBbarN hXQ hfix
        have hQleE : ∀ q ∈ autOn (baum T) (vSub G T), q ∈ E := fun q hq =>
          hres_of q (hQG hq) (hXE (hQres (mem_autSub.2 ⟨⟨q, hstab q (hQG hq)⟩, hq, rfl⟩)))
        intro y hy
        obtain ⟨x, hx, b, hb, rfl⟩ := hdec y hy
        exact E.mul_mem hx (hQleE b hb)
    ·
      obtain ⟨m, θ, β, hm, h3, hinv, hsurj, hker', hequiv, htop', -, -⟩ := hSym
      let D' : SymDat E m := ⟨θ, β, hm, h3, hinv, hsurj, hker', hequiv, htop'⟩
      intro y hy
      exact hres_of y hy (sym_normalizer_le hV2 D' (fun z hz => hGE z hz)
        (mem_autSub.2 ⟨⟨y, hstab y hy⟩, hy, rfl⟩))
  exact isNat_of_eq_comp hV hGN (le_antisymm hGle hEG) hE

end CFSG.CGT.PushingUpLit.BHS7
