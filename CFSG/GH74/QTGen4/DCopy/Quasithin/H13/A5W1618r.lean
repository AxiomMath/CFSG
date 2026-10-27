module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5W1618r
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model B2F E2
open scoped IsMulCommutative

local notation "StSL" => Assembly.LowTwoRank.StatedSL

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_a5Case_of_natural_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type}
    [Field F] [Finite F] (hF4 : Nat.card F = 4) (e : ↥(S.plus K) ≃* ↥(StSL 2 F))
    {K₀ : Subgroup G} (hK₀K : K₀ ≤ K) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G)) (hK₀im : autOn K₀ (S.WK K) = S.plus K)
    (hV : IsElemAbelian 2 (conjClosure S.V1 (K₀ ⊔ S.Tv)))
    (hn : C126.A5Case (K₀ ⊔ S.Tv) S.Tv (conjClosure S.V1 (K₀ ⊔ S.Tv)) hV)
    {G₂ : Subgroup (MulAut ↥(S.WK K))} (hsup : S.plus K ⊔ G₂ = jStar (S.HK K) S.Tv (S.WK K))
    (hc : ∀ a ∈ S.plus K, ∀ b ∈ G₂, a * b = b * a) : False := by
  classical
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hK hT
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hHKW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hHKW
  have hK₀W := hK₀K.trans hKW
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
  have hsimp : IsSimpleGroup ↥(S.plus K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo hF4.ge) e
  have h60 : Nat.card ↥(S.plus K) = 60 := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 2) (by rw [hF4]; norm_num)]
    norm_num

  have hHK : K₀ ⊔ S.Tv ≤ S.HK K :=
    sup_le (hK₀K.trans (le_sup_left.trans le_sup_left)) (S.Tv_le_HK K)
  have hVW : conjClosure S.V1 (K₀ ⊔ S.Tv) ≤ S.WK K := by
    rw [S.WK_eq hT]
    exact conjClosure_mono le_rfl hHK
  have hHV : K₀ ⊔ S.Tv ≤ Subgroup.normalizer
      ((conjClosure S.V1 (K₀ ⊔ S.Tv) : Subgroup G) : Set G) := le_normalizer_conjClosure _ _
  have hHK₀ : K₀ ⊔ S.Tv ≤ Subgroup.normalizer (K₀ : Set G) := sup_le Subgroup.le_normalizer hTK₀
  set V' := conjClosure S.V1 (K₀ ⊔ S.Tv) with hV'def
  have hK₀V' : K₀ ≤ Subgroup.normalizer (V' : Set G) := le_sup_left.trans hHV
  have hz := S.not_le_centralizer_z_of_plus_eq_F4 h1222 h517 hF hK hT hK₀im
  have hzV : S.z ∈ V' := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hK₀V : ¬ K₀ ≤ Subgroup.centralizer (V' : Set G) := fun h =>
    hz fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h hk) _ hzV).symm
  have hCWV : Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) ≤
      Subgroup.centralizer (V' : Set G) := Subgroup.centralizer_le hVW

  have hCVW : K₀ ⊓ Subgroup.centralizer (V' : Set G) ≤
      Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
    have hle : K₀ ⊓ Subgroup.centralizer (V' : Set G) ≤ K₀ := inf_le_left
    rw [← autOn_eq_bot_iff (hle.trans hK₀W)]
    have hle' : autOn (K₀ ⊓ Subgroup.centralizer (V' : Set G)) (S.WK K) ≤ S.plus K :=
      hK₀im ▸ A4.autOn_mono hle
    have hnorm : ((autOn (K₀ ⊓ Subgroup.centralizer (V' : Set G)) (S.WK K)).subgroupOf
        (S.plus K)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle', ← hK₀im]
      exact autOn_le_normalizer_autOn fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, mem_normalizer_centralizer_of_mem_normalizer (hK₀V' hk)⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((autOn (K₀ ⊓ Subgroup.centralizer (V' : Set G)) (S.WK K)).subgroupOf (S.plus K)) with
      h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact Disjoint.eq_bot_of_le h hle'
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      apply hK₀V
      intro k hk
      have hkp : conjAct (S.WK K) ⟨k, hK₀W hk⟩ ∈
          autOn (K₀ ⊓ Subgroup.centralizer (V' : Set G)) (S.WK K) :=
        h (hK₀im ▸ Setup.mem_autOn_iff.2 ⟨⟨k, hK₀W hk⟩, hk, rfl⟩)
      obtain ⟨⟨c, hcN⟩, hc, hce⟩ := Setup.mem_autOn_iff.1 hkp
      have hcW : c⁻¹ * k ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
        have h1 : conjAct (S.WK K) ((⟨c, hcN⟩ :
            ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G)))⁻¹ * ⟨k, hK₀W hk⟩) = 1 := by
          rw [map_mul, map_inv, hce, inv_mul_cancel]
        exact A4.conjAct_eq_one_iff.mp h1
      have e : k = c * (c⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem _ hc.2 (hCWV hcW)

  set φ₁ := InternalSec.autOnHom hK₀W with hφ₁
  set φ₂ := InternalSec.autOnHom hK₀V' with hφ₂
  have hker : φ₁.ker = φ₂.ker := by
    ext k
    rw [InternalSec.mem_ker_autOnHom, InternalSec.mem_ker_autOnHom]
    exact ⟨fun h => hCWV h, fun h => hCVW ⟨k.2, h⟩⟩
  let eK : ↥(autOn K₀ (S.WK K)) ≃* ↥(autOn K₀ V') :=
    ((QuotientGroup.quotientKerEquivOfSurjective φ₁
      (InternalSec.autOnHom_surjective hK₀W)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ₂ (InternalSec.autOnHom_surjective hK₀V'))
  have hq' : CFSG.IsQuasisimple ↥(autOn K₀ (S.WK K)) := by rw [hK₀im]; exact hq
  have hq₀ : CFSG.IsQuasisimple ↥(autI hV K₀) := A36B.isQuasisimple_of_mulEquiv eK hq'
  have h60₀ : Nat.card ↥(autI hV K₀) = 60 := by
    rw [← h60, ← hK₀im]
    exact (Nat.card_congr eK.toEquiv).symm
  have hp₀ : ⁅autI hV K₀, autI hV K₀⁆ = autI hV K₀ := (qs_perfect_ne_bot hq₀).1

  obtain ⟨hJH, I, hfam, hall⟩ := hn
  obtain ⟨hcard, hJeq, hcomm, -, -, -, -, -, -, h3⟩ := hfam
  have hK₀J : autI hV K₀ ≤ ⨆ L ∈ I, L := by
    rw [← hJeq]
    exact autI_mono hV ((le_twoResidual_of_perfect hK₀p le_sup_left).trans hJH)
  have hNn : ∀ y ∈ autI hV (thompsonJ (K₀ ⊔ S.Tv)), ∀ m ∈ autI hV K₀,
      y * m * y⁻¹ ∈ autI hV K₀ := by
    intro y hy m hm
    have hyH : y ∈ autI hV (K₀ ⊔ S.Tv) := autI_mono hV (B6.thompsonJ_le _) hy
    exact (Subgroup.mem_normalizer_iff.mp (autOn_le_normalizer_autOn hHK₀ hyH) m).mp hm
  obtain ⟨L₀, hL₀I, hK₀L⟩ : ∃ L₀ ∈ I, autI hV K₀ ≤ L₀ := by
    rcases hcard with h1 | h2
    · obtain ⟨L₀, rfl⟩ := Finset.card_eq_one.mp h1
      refine ⟨L₀, Finset.mem_singleton_self L₀, ?_⟩
      simpa using hK₀J
    · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
      have hs : (⨆ L ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V' hV)))), L) = L₁ ⊔ L₂ := by
        rw [Finset.iSup_insert, Finset.iSup_singleton]
      rw [hs] at hK₀J
      have hNn' : ∀ y ∈ L₁ ⊔ L₂, ∀ m ∈ autI hV K₀, y * m * y⁻¹ ∈ autI hV K₀ := by
        intro y hy m hm
        refine hNn y ?_ m hm
        rw [hJeq, hs]
        exact hy
      rcases le_or_le_of_qs_normal rfl (hcomm L₁ (by simp) L₂ (by simp) hne) hK₀J hNn' hq₀ with
        h | h
      · exact ⟨L₁, by simp, h⟩
      · exact ⟨L₂, by simp, h⟩

  obtain ⟨-, -, h3L⟩ := h3 hall
  obtain ⟨hcard4, θ, hθ⟩ := h3L L₀ hL₀I
  obtain ⟨x, hxL, hxT, hxswap⟩ : ∃ x, ∃ hx : x ∈ L₀, x ∈ autI hV S.Tv ∧ (θ ⟨x, hx⟩).IsSwap := by
    by_contra hne
    have hbot : Subgroup.closure {x | ∃ hx : x ∈ L₀, x ∈ autI hV S.Tv ∧ (θ ⟨x, hx⟩).IsSwap} = ⊥ :=
      by
      rw [Subgroup.closure_eq_bot_iff]
      rintro y ⟨hy, hyT, hys⟩
      exact absurd ⟨y, hy, hyT, hys⟩ hne
    rw [hθ, hbot, Subgroup.card_bot] at hcard4
    omega
  have hxJ : x ∈ autI hV (thompsonJ S.Tv) := by
    have : x ∈ L₀ ⊓ autI hV (thompsonJ S.Tv) := by
      rw [hθ]
      exact Subgroup.subset_closure ⟨hxL, hxT, hxswap⟩
    exact this.2
  obtain ⟨⟨t, htN⟩, htJ, hte⟩ := (mem_autI hV).1 hxJ

  have htT : t ∈ S.Tv := B6.thompsonJ_le S.Tv htJ
  have htW : t ∈ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hHKW (S.Tv_le_HK K htT)
  have htJ' : conjAct (S.WK K) ⟨t, htW⟩ ∈ S.plus K ⊔ G₂ := by
    rw [hsup]
    exact autOn_thompsonJ_le_jStar (S.Tv_le_HK K) hHKW
      (Setup.mem_autOn_iff.2 ⟨⟨t, htW⟩, htJ, rfl⟩)
  obtain ⟨n, hnK, g₂, hg₂, hng⟩ := S1417.exists_mul_of_mem_sup_of_commute hc htJ'
  obtain ⟨⟨k₁, hk₁N⟩, hk₁, hk₁e⟩ := Setup.mem_autOn_iff.1 (hK₀im ▸ hnK)

  have hk₁V : k₁ ∈ Subgroup.normalizer (V' : Set G) := hK₀V' hk₁
  have hsame : ∀ k ∈ K₀, (t * k * t⁻¹)⁻¹ * (k₁ * k * k₁⁻¹) ∈
      Subgroup.centralizer (V' : Set G) := by
    intro k hk
    have hkW := hK₀W hk
    have hkp : conjAct (S.WK K) ⟨k, hkW⟩ ∈ S.plus K :=
      hK₀im ▸ Setup.mem_autOn_iff.2 ⟨⟨k, hkW⟩, hk, rfl⟩
    have hg₂k := hc _ hkp g₂ hg₂
    have h1 : conjAct (S.WK K) ((⟨t, htW⟩ * ⟨k, hkW⟩ * (⟨t, htW⟩)⁻¹ :
        ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G)))⁻¹ *
        (⟨k₁, hk₁N⟩ * ⟨k, hkW⟩ * (⟨k₁, hk₁N⟩)⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hng, hk₁e]
      calc ((n * g₂) * conjAct (S.WK K) ⟨k, hkW⟩ * (n * g₂)⁻¹)⁻¹ *
            (n * conjAct (S.WK K) ⟨k, hkW⟩ * n⁻¹)
          = (n * (g₂ * conjAct (S.WK K) ⟨k, hkW⟩) * g₂⁻¹ * n⁻¹)⁻¹ *
            (n * conjAct (S.WK K) ⟨k, hkW⟩ * n⁻¹) := by group
        _ = 1 := by rw [← hg₂k]; group
    exact hCWV (A4.conjAct_eq_one_iff.mp h1)

  set g₁ : ↥(Subgroup.normalizer (V' : Set G)) := ⟨k₁, hk₁V⟩ with hg₁
  have hk₁A : convI hV g₁ ∈ autI hV K₀ := convI_mem_autI hV hk₁ hk₁V
  have hcent : ∀ m ∈ autI hV K₀, ((convI hV g₁)⁻¹ * x) * m * ((convI hV g₁)⁻¹ * x)⁻¹ = m := by
    intro m hm
    obtain ⟨gk, hk, rfl⟩ := (mem_autI hV).1 hm
    have h1 : convI hV ((⟨t, htN⟩ * gk * (⟨t, htN⟩)⁻¹)⁻¹ * (g₁ * gk * g₁⁻¹)) = 1 :=
      (convI_eq_one_iff hV _).mpr (hsame _ hk)
    simp only [map_mul, map_inv, hte] at h1
    have h2 := inv_mul_eq_one.mp h1
    calc ((convI hV g₁)⁻¹ * x) * convI hV gk * ((convI hV g₁)⁻¹ * x)⁻¹
        = (convI hV g₁)⁻¹ * (x * convI hV gk * x⁻¹) * convI hV g₁ := by group
      _ = (convI hV g₁)⁻¹ * (convI hV g₁ * convI hV gk * (convI hV g₁)⁻¹) * convI hV g₁ := by
          rw [h2]
      _ = convI hV gk := by group

  set φθ : Equiv.Perm (Fin 5) →* MulAut (IntMod V' hV) := L₀.subtype.comp θ.symm.toMonoidHom
    with hφθ
  have hφθi : Function.Injective φθ := L₀.subtype_injective.comp θ.symm.injective
  have hK₀r : autI hV K₀ ≤ φθ.range := fun m hm =>
    ⟨θ ⟨m, hK₀L hm⟩, by simp [hφθ]⟩
  have hA := comap_eq_alternatingGroup hφθi hK₀r hp₀ h60₀
  have hAm : ∀ σ, φθ σ ∈ autI hV K₀ ↔ σ ∈ alternatingGroup (Fin 5) := fun σ => by
    rw [← hA, Subgroup.mem_comap]
  have hcL : (convI hV g₁)⁻¹ * x ∈ L₀ := L₀.mul_mem (L₀.inv_mem (hK₀L hk₁A)) hxL
  have hσc : ∀ τ ∈ alternatingGroup (Fin 5),
      θ ⟨_, hcL⟩ * τ = τ * θ ⟨_, hcL⟩ := by
    intro τ hτ
    have h1 := hcent (φθ τ) ((hAm τ).mpr hτ)
    have h2 : (⟨_, hcL⟩ : ↥L₀) * θ.symm τ * (⟨_, hcL⟩ : ↥L₀)⁻¹ = θ.symm τ := Subtype.ext h1
    have h3 := congrArg θ h2
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h3
    calc θ ⟨_, hcL⟩ * τ = θ ⟨_, hcL⟩ * τ * (θ ⟨_, hcL⟩)⁻¹ * θ ⟨_, hcL⟩ := by group
      _ = τ * θ ⟨_, hcL⟩ := by rw [h3]
  have hσc1 : θ ⟨_, hcL⟩ = 1 := eq_one_of_commute_c3p_c234 _
    (hσc c3p (Equiv.Perm.mem_alternatingGroup.2 c3p_sign))
    (hσc c234 (Equiv.Perm.mem_alternatingGroup.2 c234_sign))

  have hx1 : (⟨x, hxL⟩ : ↥L₀) = ⟨_, hK₀L hk₁A⟩ * ⟨_, hcL⟩ := Subtype.ext (by
    show x = convI hV g₁ * ((convI hV g₁)⁻¹ * x)
    group)
  have hk₁θ : θ ⟨_, hK₀L hk₁A⟩ ∈ alternatingGroup (Fin 5) := by
    rw [← hAm]
    simpa [hφθ] using hk₁A
  have hxA : θ ⟨x, hxL⟩ ∈ alternatingGroup (Fin 5) := by
    rw [hx1, map_mul, hσc1, mul_one]
    exact hk₁θ
  rw [Equiv.Perm.mem_alternatingGroup, hxswap.sign_eq] at hxA
  exact absurd hxA (by decide)

end Setting

end CFSG.Quasithin.H13.A5
