module

public import CFSG.CGT.PushingUpLit.BHS7.FiveAmb
public import CFSG.CGT.PushingUpLit.BHS7.FiveBase
public import CFSG.CGT.PushingUpLit.BHS7.FiveTransport
public import CFSG.CGT.PushingUpLit.BHS5.TransferNat
public import CFSG.CGT.PushingUpLit.BHS7.AltAssembly
public import CFSG.CGT.PushingUpLit.BHS7.NatTail

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem le_normalizer_commutator {A B C : Subgroup Γ} (hB : A ≤ Subgroup.normalizer (B : Set Γ))
    (hC : A ≤ Subgroup.normalizer (C : Set Γ)) :
    A ≤ Subgroup.normalizer ((⁅B, C⁆ : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ A, ∀ x ∈ (⁅B, C⁆ : Subgroup Γ), g * x * g⁻¹ ∈ (⁅B, C⁆ : Subgroup Γ) := by
    intro g hg x hx
    have hmap : ∀ K : Subgroup Γ, g ∈ Subgroup.normalizer (K : Set Γ) →
        K.map (MulAut.conj g).toMonoidHom = K := by
      intro K hK
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hK z).mp hz
      · intro hy
        refine ⟨g⁻¹ * y * g, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hK) y).mp hy
        simpa using this
    have h1 : (⁅B, C⁆ : Subgroup Γ).map (MulAut.conj g).toMonoidHom =
        ⁅B.map (MulAut.conj g).toMonoidHom, C.map (MulAut.conj g).toMonoidHom⁆ :=
      Subgroup.map_commutator _ _ _
    rw [hmap B (hB hg), hmap C (hC hg)] at h1
    have : g * x * g⁻¹ ∈ (⁅B, C⁆ : Subgroup Γ).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h1] at this
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (A.inv_mem hg) _ hx
  simpa [mul_assoc] using this

variable {G T M V : Subgroup Γ}

omit [Finite Γ] in
theorem conjSub_liftSub_thompsonJ (hv : VHyp G T M V) {t : Γ} (htG : t ∈ G) :
    A1b.conjSub t (liftSub V G (autOn (thompsonJ G) V)) =
      liftSub V G (autOn (thompsonJ G) V) := by
  have htN : t ∈ Subgroup.normalizer (V : Set Γ) := hv.normalized htG
  rw [liftSub_conjSub htN htG, ← autOn_conjSub htN,
    conjSub_eq_of_mem_normalizer' (normalizer_le_normalizer_thompsonJ G
      (Subgroup.le_normalizer htG))]

omit [Finite Γ] in
theorem le_normalizer_liftSub_thompsonJ (hv : VHyp G T M V) :
    G ≤ Subgroup.normalizer (liftSub V G (autOn (thompsonJ G) V) : Set Γ) := fun _ ht =>
  CFSG.Quasithin.B6.mem_normalizer_of_conjSub_le (conjSub_liftSub_thompsonJ hv ht).le
    (conjSub_liftSub_thompsonJ hv (G.inv_mem ht)).le

theorem baum_le_liftSub (hv : VHyp G T M V) :
    baum T ≤ liftSub V G (autOn (thompsonJ G) V) := by
  intro b hb
  have hbT : b ∈ T := (inf_le_left : baum T ≤ T) hb
  have hbG : b ∈ G := hv.minpar.T_le hbT
  have hbN : b ∈ Subgroup.normalizer (V : Set Γ) := hv.normalized hbG
  refine mem_liftSub_iff.2 ⟨hbG, hbN, ?_⟩
  exact autOn_baum_le_autOn_thompsonJ hv (mem_autOn_iff.2 ⟨⟨b, hbN⟩, hb, rfl⟩)

theorem le_liftSub_sup (hv : VHyp G T M V) :
    G ≤ liftSub V G (autOn (thompsonJ G) V) ⊔ T := by
  classical
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  have hsym := bhsSymType
  have hGN : G ≤ Subgroup.normalizer (V : Set Γ) := hv.normalized
  have hTG : T ≤ G := hv.minpar.T_le
  have hTN : T ≤ Subgroup.normalizer (V : Set Γ) := hTG.trans hGN
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hv.elem.2 v v.2)
  have h51 := hv.hyp51
  have hF := five_five hsym h51 hV2
  have hJeq : autOn (thompsonJ G) V = genD (autOn G V) :=
    le_antisymm (hv.autOn_thompsonJ_le hsym) (hv.genD_le_autOn_thompsonJ hsym)
  have hTbar : autOn T V ≤ Subgroup.normalizer ((genD (autOn G V) : Subgroup (MulAut ↥V)) :
      Set (MulAut ↥V)) := (autOn_le_autOn V hTG).trans (le_normalizer_genD h51 hV2)
  intro g hg
  have hgbar : conjAct V ⟨g, hGN hg⟩ ∈ genD (autOn G V) ⊔ autOn T V := by
    rw [hF.sup_eq]
    exact mem_autOn_iff.2 ⟨⟨g, hGN hg⟩, hg, rfl⟩
  obtain ⟨a, ha, tb, htb, hat⟩ := exists_mul_of_mem_sup hTbar hgbar
  obtain ⟨t, htT, rfl⟩ := mem_autOn_iff.1 htb
  have hg' : g * (t : Γ)⁻¹ ∈ liftSub V G (autOn (thompsonJ G) V) := by
    have htG : (t : Γ) ∈ G := hTG htT
    refine mem_liftSub_iff.2 ⟨G.mul_mem hg (G.inv_mem htG), ?_, ?_⟩
    · exact Subgroup.mul_mem _ (hGN hg) (Subgroup.inv_mem _ t.2)
    · rw [hJeq]
      have : conjAct V ⟨g * (t : Γ)⁻¹, Subgroup.mul_mem _ (hGN hg) (Subgroup.inv_mem _ t.2)⟩ =
          conjAct V ⟨g, hGN hg⟩ * (conjAct V t)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [this, hat]
      simpa using ha
  have : g = g * (t : Γ)⁻¹ * (t : Γ) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hg' htT

omit [Finite Γ] in
theorem exists_decomp_of_top (hV : IsElemAbelian 2 V) {E : Subgroup Γ}
    (hE : E ≤ Subgroup.normalizer (V : Set Γ))
    (htop : @commV ↥V (commGroupOfElemAbelian hV) (autOn E V) ⊔
      @fixV ↥V (commGroupOfElemAbelian hV) (autOn E V) = ⊤) :
    ∀ v ∈ V, ∃ w ∈ (⁅V, E⁆ : Subgroup Γ), ∃ c ∈ V ⊓ Subgroup.centralizer (E : Set Γ),
      v = w * c := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  intro v hv
  have hmem : (⟨v, hv⟩ : ↥V) ∈ commV (autOn E V) ⊔ fixV (autOn E V) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
  refine ⟨(y : Γ), ?_, (z : Γ), ⟨z.2, (mem_fixV_autOn_iff hV hE z).1 hz⟩, ?_⟩
  · rw [← map_commV_autOn hV hE]
    exact ⟨y, hy, rfl⟩
  · exact (congrArg Subtype.val hyz).symm

theorem isNat_of_liftSub_eq (hv : VHyp G T M V)
    (hEq : liftSub V G (autOn (thompsonJ G) V) = G) :
    (∃ n : ℕ, 1 ≤ n ∧ IsNatSL G V n) ∨ (∃ m : ℕ, 1 ≤ m ∧ IsNatSym G V (2 * m + 1)) := by
  classical
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  have hsym := bhsSymType
  have hGN : G ≤ Subgroup.normalizer (V : Set Γ) := hv.normalized
  have hTG : T ≤ G := hv.minpar.T_le
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hv.elem.2 v v.2)
  have h51 := hv.hyp51
  have hF := five_five hsym h51 hV2
  have hJeq : autOn (thompsonJ G) V = genD (autOn G V) :=
    le_antisymm (hv.autOn_thompsonJ_le hsym) (hv.genD_le_autOn_thompsonJ hsym)
  have hJle : thompsonJ G ≤ G := iSup₂_le fun A hA => hA.1
  have hGbar : autOn G V = genD (autOn G V) := by
    rw [← hJeq]
    have h1 := autOn_liftSub (A := G) (V := V) (Y := autOn (thompsonJ G) V)
      (autOn_le_autOn V hJle)
    rw [hEq] at h1
    exact h1
  generalize @compSet ↥V (commGroupOfElemAbelian hv.elem) (autOn G V) (autOn M V) = ℰ at hF
  obtain ⟨E₀, hE₀⟩ := hF.nonempty
  have hall : ∀ E ∈ ℰ, E = E₀ := by
    intro E hE
    obtain ⟨t, htT, htE⟩ := hF.trans E₀ hE₀ E hE
    have htP : t ∈ ⨆ E' ∈ ℰ, E' := by
      rw [hF.iSup_eq, ← hGbar]
      exact autOn_le_autOn V hTG htT
    have := mem_normalizer_of_le_iSup hF hE₀ htP
    rw [← htE, conjSub_eq_of_mem_normalizer' this]
  have hgen : genD (autOn G V) = E₀ := by
    rw [← hF.iSup_eq]
    exact le_antisymm (iSup₂_le fun E hE => (hall E hE).le) (le_iSup₂_of_le E₀ hE₀ le_rfl)
  have hEq₀ : autOn G V = E₀ := hGbar.trans hgen
  have hGW : G ≤ Subgroup.normalizer ((⁅V, G⁆ : Subgroup Γ) : Set Γ) :=
    le_normalizer_commutator hGN (fun g hg => Subgroup.le_normalizer hg)
  have hWV : (⁅V, G⁆ : Subgroup Γ) ≤ V :=
    (Subgroup.commutator_comm V G).le.trans (commutator_le_of_le_normalizer hGN)
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => isElemAbelian_comm' hv.elem hx hy
  have hker : ∀ (hdec : ∀ v ∈ V, ∃ w ∈ (⁅V, G⁆ : Subgroup Γ),
      ∃ c ∈ V ⊓ Subgroup.centralizer (G : Set Γ), v = w * c),
      G ⊓ Subgroup.centralizer (V : Set Γ) = G ⊓ Subgroup.centralizer ((⁅V, G⁆ : Subgroup Γ) :
        Set Γ) := by
    intro hdec
    refine le_antisymm (inf_le_inf_left G (Subgroup.centralizer_le hWV)) fun g hg => ?_
    obtain ⟨hgG, hgW⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_inf.mpr ⟨hgG, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv'
    obtain ⟨w, hw, c, hc, rfl⟩ := hdec v hv'
    have h1 : w * g = g * w := Subgroup.mem_centralizer_iff.mp hgW w hw
    have h2 : g * c = c * g := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 g hgG)
    calc w * c * g = w * (c * g) := by group
      _ = w * (g * c) := by rw [h2]
      _ = (w * g) * c := by group
      _ = (g * w) * c := by rw [h1]
      _ = g * (w * c) := by group
  rcases hF.type E₀ hE₀ with hSL | hSym
  · obtain ⟨n, hn, hnat, htop, -⟩ := hSL
    left
    refine ⟨n, by omega, ?_⟩
    have hnatG := isNatSL_of_slType hv.elem hGN hEq₀ hnat htop
    have hdec := exists_decomp_of_top hv.elem hGN (hEq₀ ▸ htop)
    exact isNatSL_iff.mpr (isNatBy_of_decomp (isNatSL_iff.mp hnatG) hWV hGW hVab hdec (hker hdec))
  · obtain ⟨m, θ, β, hm, h3, hinv, hsurj, hker', hequiv, htop, -, -⟩ := hSym
    right
    let D : SymDat E₀ m := ⟨θ, β, hm, h3, hinv, hsurj, hker', hequiv, htop⟩
    obtain ⟨k, hk⟩ := hm
    have hnatG := isNatSym_of_symDat hv.elem hGN hEq₀ D
    have hdec := exists_decomp_of_top hv.elem hGN (hEq₀ ▸ htop)
    refine ⟨k, by omega, ?_⟩
    rw [← hk]
    exact isNatSym_iff.mpr (isNatBy_of_decomp (isNatSym_iff.mp hnatG) hWV hGW hVab hdec
      (hker hdec))

theorem five_of_certificate {G T : Subgroup Γ} (h : MinCex G T)
    (hmin : IsMinParabolic2 T G) : ∃ Ê : Subgroup Γ, NatTailData G T Ê := by
  classical
  have hT2 : IsPGroup 2 ↥T := h.sylow.2.1
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hT0 : T ≠ ⊥ := fun h0 => hb0 (le_bot_iff.mp ((inf_le_left : baum T ≤ T).trans h0.le))
  have hne : cStarStarIn G T ≠ G := fun heq =>
    h.ne (le_antisymm (cStarIn_le G T) (by
      have h1 := cStarStarIn_le_cStarIn (G := G) hT2 hT0
      rwa [heq] at h1))
  obtain ⟨hsyl, hnn, M, hTM, hMlt, hmax⟩ := hmin
  have hAmb : AmbHyp G T M := ⟨h.charTwo, ⟨hsyl, hnn, hTM, hMlt, hmax⟩, hne⟩
  have hv := hAmb.vHyp
  have hTC : T ≤ cStarIn G T := le_cStarIn_of_minCex h
  refine ⟨liftSub (omegaOneCenterOf (pCoreOf 2 G)) G
    (autOn (thompsonJ G) (omegaOneCenterOf (pCoreOf 2 G))), ?_, ?_, ?_, ?_⟩
  · exact isSubnormal_of_le_of_le_normalizer (liftSub_le G _) (le_normalizer_liftSub_thompsonJ hv)
  · intro hle
    apply h.ne
    refine le_antisymm (cStarIn_le G T) fun g hg => ?_
    have := le_liftSub_sup hv hg
    exact (sup_le hle hTC) this
  · exact (inf_le_left : baum T ≤ T).trans (hv.minpar.T_le.trans
      (le_normalizer_liftSub_thompsonJ hv))
  · intro hH
    have hBE := baum_le_liftSub hv
    have hEq : liftSub (omegaOneCenterOf (pCoreOf 2 G)) G
        (autOn (thompsonJ G) (omegaOneCenterOf (pCoreOf 2 G))) = G := by
      refine le_antisymm (liftSub_le G _) ?_
      calc G = baum T ⊔ liftSub (omegaOneCenterOf (pCoreOf 2 G)) G
            (autOn (thompsonJ G) (omegaOneCenterOf (pCoreOf 2 G))) := hH.symm
        _ ≤ _ := sup_le hBE le_rfl
    refine ⟨omegaOneCenterOf (pCoreOf 2 G), ?_⟩
    exact ⟨h.charTwo, h.sylow, h.ne, hv.normalized, hv.omega_le, le_rfl,
      by
        rcases isNat_of_liftSub_eq hv hEq with ⟨n, hn, hnat⟩ | ⟨m, hm, hnat⟩
        · exact Or.inl ⟨n, hn, hnat⟩
        · exact Or.inr ⟨m, hm, hnat⟩⟩

end CFSG.CGT.PushingUpLit.BHS7
