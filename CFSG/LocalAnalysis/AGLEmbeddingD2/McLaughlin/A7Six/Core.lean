module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.SubS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixBlock
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Escape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.BlockQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.C126Over
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Parabolic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open Equiv Equiv.Perm CFSG.AGLEmbeddingD2.GN
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

namespace SixCtx

variable (c : SixCtx T L)

theorem le_of_closure {K : Subgroup (X ⧸ gnC T)} {Sig : Set (Perm (Fin 7))}
    (hgen : alternatingGroup (Fin 7) ≤ Subgroup.closure Sig)
    (hSig : ∀ σ ∈ Sig, ∃ l : ↥L, (l : X ⧸ gnC T) ∈ K ∧ (c.eL l : Perm (Fin 7)) = σ) : L ≤ K := by
  set K₀ : Subgroup (Perm (Fin 7)) :=
    (K.comap L.subtype).map ((alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom)
  have hle : Subgroup.closure Sig ≤ K₀ := by
    refine (Subgroup.closure_le _).2 fun σ hσ => ?_
    obtain ⟨l, hlK, hl⟩ := hSig σ hσ
    exact ⟨l, hlK, hl⟩
  intro x hx
  have h1 : ((c.eL ⟨x, hx⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ K₀ :=
    hle (hgen (c.eL ⟨x, hx⟩).2)
  obtain ⟨k, hkK, hk⟩ := h1
  have h2 : c.eL k = c.eL ⟨x, hx⟩ := Subtype.ext hk
  have h3 := c.eL.injective h2
  have h4 : (k : X ⧸ gnC T) = x := congrArg Subtype.val h3
  rw [← h4]
  exact hkK

omit [Finite X] in
theorem mem_of_wP_le {K : Subgroup (X ⧸ gnC T)} {P : Subgroup (Perm (Fin 7))} (hW : c.wP P ≤ K)
    {σ : Perm (Fin 7)} (hσ : σ ∈ (P ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7)))) :
    ∃ l : ↥L, (l : X ⧸ gnC T) ∈ K ∧ (c.eL l : Perm (Fin 7)) = σ := by
  refine ⟨c.eL.symm ⟨σ, hσ.2⟩, hW ((c.mem_wP).2 ⟨(c.eL.symm ⟨σ, hσ.2⟩).2, ?_⟩), ?_⟩
  · rw [show (⟨((c.eL.symm ⟨σ, hσ.2⟩ : ↥L) : X ⧸ gnC T), (c.eL.symm ⟨σ, hσ.2⟩).2⟩ : ↥L) =
      c.eL.symm ⟨σ, hσ.2⟩ from rfl, MulEquiv.apply_symm_apply]
    exact hσ.1
  · rw [MulEquiv.apply_symm_apply]

theorem step (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    (hTL : T ≤ nL T L) (hDL : gnD T ⊓ lT T L ≤ gnC T)
    {R : Subgroup X} (hRT : R ≤ T) (hCR : T ⊓ gnC T ≤ R)
    (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) (hbR : baum R = baum T)
    (h1R : C₁ ≤ omegaOneCenterOf R) {P : Subgroup (Perm (Fin 7))} (hQP : c.img R ≤ P)
    (hcard : Nat.card P = 3 * Nat.card (c.img R))
    (hodd : ∃ q ∈ c.img R, q ∉ alternatingGroup (Fin 7))
    (hnn : ∃ g ∈ P ⊓ alternatingGroup (Fin 7), ∃ e ∈ c.img R, g * e * g⁻¹ ∉ c.img R)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hTL (hRT ht)⟩ = σ)
    (hsolvP : Group.IsSolvable ↥P) :
    c.wP P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c.wP P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π
  have hRL : Rs ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hTL (hRT hr)
  have hRp : IsPGroup 2 Rs := (hX.sylow.2.1.to_le hRT).map π
  have hQ : c.imgS Rs = c.img R := c.imgS_map R (hRT.trans hTL)
  have hQL' : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (y : X ⧸ gnC T) (hy : y ∈ Rs ⊓ L),
      c.θs ⟨y, hRL hy.1⟩ = σ := by
    intro σ hσ
    obtain ⟨t, ht, htL, htσ⟩ := hQL σ hσ
    exact ⟨π t, ⟨⟨t, ht, rfl⟩, htL⟩, htσ⟩
  obtain ⟨hmins, himg, hker⟩ := c.minParabolic_wP hRL hRp hQ hQP hcard hodd hnn hQL'
  set W := c.wP P
  obtain ⟨H, M, hmin, hF, hRH, hmap⟩ := exists_minParabolic_lift hX hRT hCR hQR hmins
  have hWL : W ≤ nLs T L := (c.wP_le_L P).trans Subgroup.le_normalizer
  have hHL : W ⊔ Rs ≤ nLs T L := sup_le hWL hRL
  have hne : W ⊔ Rs ≠ Rs := by
    intro h
    have h1 : c.imgS (W ⊔ Rs) = c.imgS Rs := by rw [h]
    rw [himg, hQ] at h1
    have h2 : Nat.card P = Nat.card (c.img R) := by rw [h1]
    have hpos : 0 < Nat.card (c.img R) := Nat.card_pos
    omega
  have hsolvs : Group.IsSolvable ↥(W ⊔ Rs) := by
    let g : ↥(W ⊔ Rs) →* ↥P :=
      (c.θs.comp (Subgroup.inclusion hHL)).codRestrict P (fun h => by
        rw [← himg]; exact ⟨⟨h, hHL h.2⟩, h.2, rfl⟩)
    let f : ↥(Rs.subgroupOf (W ⊔ Rs)) →* ↥(W ⊔ Rs) := (Rs.subgroupOf (W ⊔ Rs)).subtype
    have hRs2 : IsPGroup 2 ↥(Rs.subgroupOf (W ⊔ Rs)) :=
      hRp.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
    have := hRs2.isNilpotent
    refine Group.isSolvable_of_ker_le_range f g fun h hh => ?_
    have h1 : c.θs ⟨h, hHL h.2⟩ = 1 := congrArg Subtype.val hh
    exact ⟨⟨h, hker h h.2 h1⟩, rfl⟩
  have hsolv : Group.IsSolvable ↥H :=
    isSolvable_of_minParabolic hmin (hmap ▸ hsolvs) (by rw [hmap]; exact hne)
  have hpc : perfectCore H ≤ Subgroup.centralizer (VZ R H : Set X) := by
    rw [(isSolvable_iff_perfectCore_eq_bot H).1 hsolv]
    exact bot_le
  have hWH : W ≤ gnImg T H := by
    show W ≤ H.map π
    rw [hmap]
    exact le_sup_left
  rcases concl1_over hP hbR h1R hmin hF hpc with h1 | h2 | h3
  · exact Tits.GN516.escape_of_le_gnImg hWH (Or.inl h1)
  · exact Tits.GN516.escape_of_le_gnImg hWH (Or.inr h2)
  · exfalso
    obtain ⟨K, hKχ, -, hHK⟩ := h3
    have hKb : IsBlock2 H K := hKχ.1
    have hKC : ¬ K ≤ gnC T := by
      intro hKC
      apply hne
      apply le_antisymm _ le_sup_right
      rw [← hmap, hHK, Subgroup.map_sup]
      refine sup_le le_rfl ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxC : x ∈ gnC T := by
        refine (conjClosure_le fun t _ k hk => ?_) hx
        exact (gnC_normal T).conj_mem k (hKC hk) t
      rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hxC]
      exact Rs.one_mem
    have hKD : K ≤ gnD T := le_gnD_of_isBlock2' hX (hQR.trans hRH) hKb hKC
    have hodd' : ∀ h ∈ W ⊔ Rs, Odd (orderOf h) → h ∈ L := by
      intro h hh hho
      have hmul : ((W : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) =
          ((W ⊔ Rs : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := by
        have hRW : Rs ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) := by
          intro r hr
          rw [Subgroup.mem_normalizer_iff]
          have key : ∀ g ∈ Rs, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
            intro g hg w hw
            obtain ⟨hwL, hwP⟩ := (c.mem_wP).1 hw
            have hgw : g * w * g⁻¹ ∈ L :=
              (Subgroup.mem_normalizer_iff.1 (hRL hg) w).1 hwL
            refine (c.mem_wP).2 ⟨hgw, ?_⟩
            rw [c.hθs ⟨g, hRL hg⟩ ⟨w, hwL⟩ ⟨_, hgw⟩ rfl]
            have hgQ : c.θs ⟨g, hRL hg⟩ ∈ c.img R := hQ ▸ ⟨⟨g, hRL hg⟩, hg, rfl⟩
            exact P.mul_mem (P.mul_mem (hQP hgQ) hwP) (P.inv_mem (hQP hgQ))
          intro w
          constructor
          · exact key r hr w
          · intro h
            have := key r⁻¹ (Rs.inv_mem hr) _ h
            simpa [mul_assoc] using this
        exact (Subgroup.coe_mul_of_right_le_normalizer_left W Rs hRW).symm
      have : h ∈ ((W : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) := by rw [hmul]; exact hh
      obtain ⟨w, hw, r, hr, rfl⟩ := this
      obtain ⟨hwL, -⟩ := (c.mem_wP).1 hw
      have hθ : c.θs ⟨w * r, hHL hh⟩ = c.θs ⟨w, hWL hw⟩ * c.θs ⟨r, hRL hr⟩ := by
        rw [← map_mul]; rfl
      have hsign : Equiv.Perm.sign (c.θs ⟨w * r, hHL hh⟩) = 1 := by
        have hord : Odd (orderOf (c.θs ⟨w * r, hHL hh⟩)) := by
          refine Odd.of_dvd_nat hho ?_
          refine orderOf_map_dvd c.θs ⟨w * r, hHL hh⟩ |>.trans ?_
          rw [Subgroup.orderOf_mk]
        have h1 := pow_orderOf_eq_one (c.θs ⟨w * r, hHL hh⟩)
        have h2 := congrArg Equiv.Perm.sign h1
        rw [map_pow, map_one] at h2
        rcases Int.units_eq_one_or (Equiv.Perm.sign (c.θs ⟨w * r, hHL hh⟩)) with h | h
        · exact h
        · rw [h] at h2
          obtain ⟨k, hk⟩ := hord
          rw [hk, pow_succ, pow_mul] at h2
          simp at h2
      have hθw : c.θs ⟨w, hWL hw⟩ = c.eL ⟨w, hwL⟩ := c.θs_of_mem_L hwL
      have hrA : c.θs ⟨r, hRL hr⟩ ∈ c.img R ⊓ alternatingGroup (Fin 7) := by
        refine ⟨hQ ▸ ⟨⟨r, hRL hr⟩, hr, rfl⟩, Equiv.Perm.mem_alternatingGroup.mpr ?_⟩
        have h1 := hsign
        rw [hθ, map_mul, hθw, Equiv.Perm.mem_alternatingGroup.mp (c.eL ⟨w, hwL⟩).2,
          one_mul] at h1
        exact h1
      obtain ⟨y, hy, hyθ⟩ := hQL' _ hrA
      set k := y⁻¹ * r with hk
      have hkR : k ∈ Rs := Rs.mul_mem (Rs.inv_mem hy.1) hr
      have hkθ : c.θs ⟨k, hRL hkR⟩ = 1 := by
        have e : (⟨k, hRL hkR⟩ : ↥(nLs T L)) = (⟨y, hRL hy.1⟩)⁻¹ * ⟨r, hRL hr⟩ := rfl
        rw [e, map_mul, map_inv, hyθ, inv_mul_cancel]
      have hkc0 := (c.hθs1 ⟨k, hRL hkR⟩).1 hkθ
      have hkc : ∀ l ∈ L, k * l * k⁻¹ = l := fun l hl => hkc0 l hl
      set m := w * y with hm
      have hmL : m ∈ L := L.mul_mem hwL hy.2
      have hmk : m * k = k * m := by
        have h := hkc m hmL
        calc m * k = (k * m * k⁻¹) * k := by rw [h]
          _ = k * m := by group
      have hwr : w * r = m * k := by rw [hm, hk]; group
      obtain ⟨n, hn⟩ := hho
      have hpow : (m * k) ^ (2 * n + 1) = 1 := by
        rw [← hwr, ← hn]; exact pow_orderOf_eq_one _
      have hpow' : m ^ (2 * n + 1) * k ^ (2 * n + 1) = 1 := by
        rw [← (Commute.mul_pow hmk)]; exact hpow
      have hkn : k ^ (2 * n + 1) ∈ L := by
        have : k ^ (2 * n + 1) = (m ^ (2 * n + 1))⁻¹ := eq_inv_of_mul_eq_one_right hpow'
        rw [this]
        exact L.inv_mem (L.pow_mem hmL _)
      have hkn1 : k ^ (2 * n + 1) = 1 := by
        refine c.eq_one_of_mem_center hkn fun l hl => ?_
        have h1 : ∀ j : ℕ, k ^ j * l * (k ^ j)⁻¹ = l := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            calc k ^ (j + 1) * l * (k ^ (j + 1))⁻¹ = k ^ j * (k * l * k⁻¹) * (k ^ j)⁻¹ := by
                  group
              _ = l := by rw [hkc l hl, ih]
        have := h1 (2 * n + 1)
        calc k ^ (2 * n + 1) * l = k ^ (2 * n + 1) * l * (k ^ (2 * n + 1))⁻¹ *
            k ^ (2 * n + 1) := by group
          _ = l * k ^ (2 * n + 1) := by rw [this]
      have hk1 : k = 1 := by
        obtain ⟨j, hj⟩ := hRp ⟨k, hkR⟩
        have hj' : k ^ 2 ^ j = 1 := congrArg Subtype.val hj
        have hcop : Nat.Coprime (2 ^ j) (2 * n + 1) :=
          Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
        have : k ^ Nat.gcd (2 ^ j) (2 * n + 1) = 1 := pow_gcd_eq_one.2 ⟨hj', hkn1⟩
        rwa [hcop.gcd_eq_one, pow_one] at this
      show w * r ∈ L
      rw [hwr, hk1, mul_one]
      exact hmL
    have hKL : K ≤ lT T L := by
      refine (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.le_closure_odd_of_isShort2 hKb.1).trans
        ((Subgroup.closure_le _).2 fun x hx => ?_)
      show π x ∈ L
      have hxH : π x ∈ W ⊔ Rs := by
        rw [← hmap]
        exact ⟨x, hKb.2.1 hx.1, rfl⟩
      refine hodd' _ hxH (Odd.of_dvd_nat hx.2 (orderOf_map_dvd π x))
    exact hKC ((le_inf hKD hKL).trans hDL)

theorem false_of_sixCtx (pd : PermData) (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    (hP : IsC118Pair T C₁ C₂) (hY : GNYComponent T C₁ C₂ L)
    (hTN : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T))) (hD : c.img T = pd.D)
    (hC : nV T L ⊓ Subgroup.centralizer (lT T L : Set X) = ⊥) : False := by
  set π := QuotientGroup.mk' (gnC T)
  have hTL : T ≤ nL T L := fun t ht => hTN ⟨t, ht, rfl⟩
  obtain ⟨-, h1Z, -, -, -, -, -⟩ := id hP
  have hL := hY.1
  have hDL : gnD T ⊓ lT T L ≤ gnC T := by
    by_contra hcon
    refine FiveThreeAlt.false_of_gnD_alt7 hX hL c.eL hC c.φ c.hφ (fun l hl u v huv => ?_) hcon
    have hlN : l ∈ nL T L := Subgroup.le_normalizer hl
    rw [c.hφe' ⟨l, hlN⟩ u v huv, c.hθL ⟨l, hlN⟩ ⟨_, hl⟩ rfl]
  set S := c.subS pd
  have hSimg := c.img_subS pd hTL hD
  have hE8 : Nat.card (c.img S) = 8 := by rw [hSimg, pd.card_E]
  have hodd02 : swap (0 : Fin 7) 2 ∉ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)]; decide
  have hQLS : ∀ σ ∈ c.img S ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ S),
      π t ∈ L ∧ c.θ ⟨t, hTL (c.subS_le pd ht)⟩ = σ := by
    rintro σ ⟨hσE, hσA⟩
    rw [hSimg] at hσE
    obtain ⟨t, ht, htL, htσ⟩ := c.exists_preimage_of_mem_D pd hX hTL hL hD ⟨pd.E_le_D hσE, hσA⟩
    exact ⟨t, (c.mem_subS pd hTL).2 ⟨ht, htσ ▸ hσE⟩, htL, htσ⟩
  have hQLT : ∀ σ ∈ c.img T ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ T),
      π t ∈ L ∧ c.θ ⟨t, hTL ((le_refl T) ht)⟩ = σ := by
    rintro σ ⟨hσD, hσA⟩
    rw [hD] at hσD
    exact c.exists_preimage_of_mem_D pd hX hTL hL hD ⟨hσD, hσA⟩
  set CC := gnImg T (Subgroup.centralizer (C₁ : Set X))
  set NN := gnImg T (Subgroup.normalizer (C₂ : Set X))
  have hstepS : ∀ i, c.wP (pd.P i) ≤ CC ∨ c.wP (pd.P i) ≤ NN := by
    intro i
    refine c.step hX hP hTL hDL (c.subS_le pd) (c.inf_gnC_le_subS pd hTL)
      (c.pCoreOf_le_subS pd hX hTL) (c.baum_subS pd hX hTL hD)
      (h1Z.trans (c.omegaOneCenterOf_le_subS pd hX hTL hD)) ?_ ?_
      ⟨swap 0 2, by rw [hSimg]; exact pd.swap_mem_E, hodd02⟩ ?_ hQLS (pd.solv_P i)
    · rw [hSimg]; exact pd.E_le_P i
    · rw [pd.card_P i, hE8]
    · rw [hSimg]; exact pd.P_notNormal i
  have hstepN : c.wP pd.PN ≤ CC ∨ c.wP pd.PN ≤ NN := by
    refine c.step hX hP hTL hDL le_rfl inf_le_left
      (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow) rfl h1Z ?_ ?_
      ⟨swap 0 2, by rw [hD]; exact pd.E_le_D pd.swap_mem_E, hodd02⟩ ?_ hQLT pd.solv_PN
    · rw [hD]; exact pd.D_le_PN
    · rw [pd.card_PN, hD, pd.card_D]
    · rw [hD]; exact pd.PN_notNormal
  have hL_le : ∀ K : Subgroup (X ⧸ gnC T), (∀ i, c.wP (pd.P i) ≤ K) → L ≤ K := by
    intro K hK
    refine c.le_of_closure pd.gen_P fun σ hσ => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hσ
    exact c.mem_of_wP_le (hK i) hi
  have hL_le' : ∀ (K : Subgroup (X ⧸ gnC T)) (i : Fin 3), c.wP pd.PN ≤ K →
      c.wP (pd.P i) ≤ K → L ≤ K := by
    intro K i hN hi
    refine c.le_of_closure (pd.gen_PN i) fun σ hσ => ?_
    rcases hσ with h | h
    · exact c.mem_of_wP_le hN h
    · exact c.mem_of_wP_le hi h
  rcases hstepN with hNC | hNN
  · by_cases hex : ∃ i, c.wP (pd.P i) ≤ CC
    · obtain ⟨i, hi⟩ := hex
      exact hY.2.1 (hL_le' _ i hNC hi)
    · push Not at hex
      exact hY.2.2 (hL_le _ fun i => (hstepS i).resolve_left (hex i))
  · by_cases hex : ∃ i, c.wP (pd.P i) ≤ NN
    · obtain ⟨i, hi⟩ := hex
      exact hY.2.2 (hL_le' _ i hNN hi)
    · push Not at hex
      exact hY.2.1 (hL_le _ fun i => (hstepS i).resolve_right (hex i))

end SixCtx

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
