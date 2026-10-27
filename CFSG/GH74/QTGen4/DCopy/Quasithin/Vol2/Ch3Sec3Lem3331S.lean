module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3331
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331S

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace Lem3331S

variable {G : Type} [Group G]

theorem card_C_Z_F4 [CFSG.GH74.QTGen4.Finite4 G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4)
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β u)))
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sylowS6)
    (hH : (ρ.comp (Subgroup.inclusion hLTN)).range = alternatingGroup (Fin 6) ∨
      (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤)
    (h27 : Stmt3_3_27_F4) {d : G} (hdD : d ∈ D) (hdM : d ∉ M)
    (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T) :
    Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
  obtain ⟨hshort, -⟩ := hA6
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hMp := Hyp331.mPlus_eq_of_le hTL
  obtain ⟨-, -, -, ⟨-, hV4⟩⟩ := stmt3_3_7_of h38 h39 G T M L D h
  rw [hMp] at hV4
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L :=
    (Subgroup.commutator_mono hVQ le_rfl).trans (Hyp331.commutator_qL_le_blockU hshort hTL)
  have hZV : quasithinOmegaOneCenter T ≤ vPlus L T := le_conjClosure _ _
  have hUL : blockU L ≤ L := commutator_le_right_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
  have hCZU : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer (blockU L : Set G) :=
    fun c hc => Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUL hc.2)
  have hZdec : ∀ z ∈ quasithinOmegaOneCenter T, ∃ u ∈ quasithinOmegaOneCenter T ⊓ blockU L,
      ∃ c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G), z = u * c := by
    intro z hz
    have h1 : z ∈ blockU L ⊔ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
      have h2 := hZV hz
      rw [hV4] at h2
      exact (sup_le_sup_right hVL _) h2
    obtain ⟨u, hu, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCZU).mp h1
    refine ⟨u, ⟨?_, hu⟩, c, hc, rfl⟩
    have := (quasithinOmegaOneCenter T).mul_mem hz ((quasithinOmegaOneCenter T).inv_mem hc.1)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨t₁, ht₁, e₁⟩ := CZA6.mem_image_sylow ρ hLTN hTidx (fun t ht => hρT t ht) hH
    CZA6.b1_mem_sylowS6 b1_mem_alt
  obtain ⟨t₂, ht₂, e₂⟩ := CZA6.mem_image_sylow ρ hLTN hTidx (fun t ht => hρT t ht) hH
    CZA6.s1_mem_sylowS6 s1_mem_alt
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hfixZ : ∀ u : ↥(blockU L), (u : G) ∈ quasithinOmegaOneCenter T →
      Multiplicative.toAdd (β u) = 0 ∨ Multiplicative.toAdd (β u) = CZA6.w0 := by
    intro u huZ
    have hfix : ∀ t (ht : t ∈ T), A6Coc.act (ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩)
        (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β u) := by
      intro t ht
      have e := hβe ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ u u (by
        have h1 := Subgroup.mem_centralizer_iff.mp (hTZ ht) u huZ
        show (u : G) = t * u * t⁻¹
        rw [← h1]
        group)
      exact e.symm
    apply CZA6.fix_D8
    · rw [← e₁]
      exact hfix t₁ ht₁
    · rw [← e₂]
      exact hfix t₂ ht₂
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le _).mpr fun z hz => hz.1.1
  have hAC : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤ tC L T :=
    fun z hz => ⟨hZT hz.1, hz.2⟩
  have hAd : CFSG.conjugate (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) d ≤
      quasithinOmegaOneCenter T := fun x hx => by
    have h1 := (mem_conjugate_iff.mp hx).1
    have := conj_mem_omegaOneCenter (Subgroup.inv_mem _ hdT) h1
    simpa [mul_assoc] using this
  have hAAd : (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) d = ⊥ := by
    have h1 := (h27 G T M L D h d hdD hdM hdV hTC).1
    rw [eq_bot_iff] at h1 ⊢
    intro x hx
    exact h1 ⟨hAC hx.1, mem_conjugate_iff.mpr (hAC (mem_conjugate_iff.mp hx.2))⟩
  have hcardAd : Nat.card (CFSG.conjugate
      (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) d) =
      Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective
  obtain ⟨z, hzZ, hz1, -, hzL, -⟩ := h.exists_involution_tC hTL hTC
  have hA1 : 1 < Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hz : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzL⟩
    rw [hbot, Subgroup.mem_bot] at hz
    exact hz1 hz
  exact card_inf_centralizer_eq_two β hβk hZdec hfixZ hAd hAAd hcardAd hA1

theorem step3_3_31S_aux_F4 [CFSG.GH74.QTGen4.Finite4 G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25_F4) (h27 : Stmt3_3_27_F4)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥) {d : G} (hdD : d ∈ D)
    (hdM : d ∉ M) (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T) :
    (qL L T).relIndex (qL L T ⊔ CFSG.conjugate (vPlus L T) d) = 2 ∧
      d ∈ Subgroup.normalizer ((qL L T ⊔ CFSG.conjugate (vPlus L T) d : Subgroup G) : Set G) ∧
      CFSG.conjugate (vPlus L T) d ≤ Subgroup.centralizer (tC L T : Set G) ∧
      qL L T = vPlus L T ⊔
        (qL L T ⊓ Subgroup.centralizer (CFSG.conjugate (vPlus L T) d : Set G)) ∧
      T = T ⊓ L ⊔ qL L T ⊔ CFSG.conjugate (vPlus L T) d ∧
      Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hshort, α, hA⟩ := id hA6
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := vPlus L T with hVdef
  set Q := qL L T with hQdef
  set C := tC L T with hCdef
  set U := blockU L with hUdef
  set Vd := CFSG.conjugate V d with hVddef
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hQLT : Q ≤ L ⊔ T := hQT.trans le_sup_right
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hred.2.1.1
    exact setLike_mul_comm ha hb
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hUV : U ≤ V := h.blockU_le_vPlus h38 h39 hshort hTL
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hVT : V ≤ T := hVQ.trans hQT
  have hQU : ⁅Q, L⁆ ≤ U := Hyp331.commutator_qL_le_blockU hshort hTL
  obtain ⟨ρ, β, hβs, hβk, hβe, hρT, hρL, -, hker, hK, hX⟩ :=
    CZA6.exists_rho_cZ h38 h39 h hA6 hTL
  have hρ1 : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 ↔ g ∈ Q := fun g hg =>
    ⟨hK g hg _, fun hgQ => (hker g hg _).mpr (hQV hgQ)⟩
  have hH := eq_alternatingGroup_or_eq_top (H := (ρ.comp (Subgroup.inclusion hLTN)).range)
    (fun s hs => by
      obtain ⟨ℓ, hℓ, e⟩ := hρL s hs
      exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩)
  obtain ⟨-, -, hYT, -, hRP, -⟩ := parabolic ρ hLTN hT2 hTidx
    (fun g hg h1 => hK g hg (hLTN hg) h1) (fun t ht => hρT t ht) hρL hH
    sylowS6_le_p1 r1_le_p1 p1_le_normalizer (fun x hx => sq_eq_one_of_mem_r1 hx) card_p1 card_r1
    c45_mem_r1 s1_mem_alt t1_mem_alt s1_mem_p1 t1_mem_p1 comm_not_mem_r1
  have hPSL : ¬ IsPSL 3 2 1 ↥(autOn L V) := by
    intro hP
    have h1 := h.card_autOn_dvd hTL
    have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
      obtain ⟨hαs, hαk, -⟩ := hA
      rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [Vol2.Ch11.SecA.card_of_isPSL (by norm_num) hP, h2] at h1
    revert h1
    decide
  obtain ⟨-, h25b, -⟩ := h25 G T M L D h
  obtain ⟨hDY, hDR, -⟩ := h25b hTC hPSL
  have hYP : oTwoUpper (L ⊓ Subgroup.centralizer (Z : Set G)) ⊔ T = pre ρ hLTN p1 := by
    rw [hX, hYT]
  have hdR : d ∈ Subgroup.normalizer (pre ρ hLTN r1 : Set G) := by
    have := hDR hdD
    rwa [hYP, hRP] at this
  have hdP : d ∈ Subgroup.normalizer (pre ρ hLTN p1 : Set G) := by
    rw [← hYP]
    exact C1.mem_normalizer_sup (hDY hdD) hdT
  have hdinv : ∀ {H : Subgroup G}, d ∈ Subgroup.normalizer (H : Set G) → ∀ x,
      d * x * d⁻¹ ∈ H → x ∈ H := by
    intro H hd x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) _).mp hx
    simpa [mul_assoc] using this
  have hQR : Q ≤ pre ρ hLTN r1 := fun g hg => (mem_pre ρ hLTN).mpr ⟨hQLT hg, by
    rw [(hρ1 g (hQLT hg)).mpr hg]
    exact Subgroup.one_mem _⟩
  have hVdT : Vd ≤ T := fun x hx => hdinv hdT x (hVT (mem_conjugate_iff.mp hx))
  have hVdR : Vd ≤ pre ρ hLTN r1 := fun x hx => hdinv hdR x (hQR (hVQ (mem_conjugate_iff.mp hx)))
  have hVdLT : Vd ≤ L ⊔ T := hVdT.trans le_sup_right
  have hconjVd : ∀ g, d * g * d⁻¹ ∈ Subgroup.normalizer (V : Set G) → ∀ x ∈ Vd,
      g * x * g⁻¹ ∈ Vd := by
    intro g hg x hx
    rw [mem_conjugate_iff] at hx ⊢
    have e : d * (g * x * g⁻¹) * d⁻¹ = (d * g * d⁻¹) * (d * x * d⁻¹) * (d * g * d⁻¹)⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hx
  have hTVd : ∀ g ∈ T, ∀ x ∈ Vd, g * x * g⁻¹ ∈ Vd := fun g hg =>
    hconjVd g (hLTV (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hdT g).mp hg)))
  have hPVd : ∀ g ∈ pre ρ hLTN p1, ∀ x ∈ Vd, g * x * g⁻¹ ∈ Vd := fun g hg =>
    hconjVd g (hLTV (pre_le_sup ρ hLTN p1 ((Subgroup.mem_normalizer_iff.mp hdP g).mp hg)))
  have hVdab : ∀ a ∈ Vd, ∀ b ∈ Vd, a * b = b * a := by
    intro a ha b hb
    have h1 := hVab _ (mem_conjugate_iff.mp ha) _ (mem_conjugate_iff.mp hb)
    have e : d * (a * b) * d⁻¹ = d * (b * a) * d⁻¹ := by
      calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
        _ = (d * b * d⁻¹) * (d * a * d⁻¹) := h1
        _ = d * (b * a) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨ℓc, hℓc, hρℓc⟩ := hρL CZA6.c012 CZA6.c012_mem_alt
  have hℓcP : ℓc ∈ pre ρ hLTN p1 := (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓc, by
    rw [hρℓc]
    exact CZA6.c012_mem_p1⟩
  have hρVd := rho_eq_of_quad ρ hLTN β hβs hβe hVdLT
    (fun x hx => ((mem_pre ρ hLTN).mp (hVdR hx)).2) hVdab
    (fun u hu x hx => hTVd u (hVT (hUV hu)) x hx) hℓc hρℓc (fun x hx => hPVd ℓc hℓcP x hx)
  obtain ⟨w₀, hw₀Vd, hw₀Q⟩ := Set.not_subset.mp hdV
  have hw₀ρ : ρ ⟨w₀, hLTN (hVdLT hw₀Vd)⟩ = c45 := by
    rcases hρVd w₀ hw₀Vd with h1 | h1
    · exact absurd ((hρ1 w₀ (hVdLT hw₀Vd)).mp h1) hw₀Q
    · exact h1
  have htop : (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤ := by
    rcases hH with hA' | hT'
    · exfalso
      have h1 : c45 ∈ (ρ.comp (Subgroup.inclusion hLTN)).range :=
        ⟨⟨w₀, hVdLT hw₀Vd⟩, hw₀ρ⟩
      rw [hA'] at h1
      exact c45_not_mem_alt h1
    · exact hT'
  have hrel := relIndex_sup_eq_two ρ hLTN hQLT hVdLT (hVdLT.trans hLTQ) hρ1 hρVd hw₀Vd hw₀ρ
  have hT5 := eq_inf_sup_sup ρ hLTN hTL hρL hρ1 hQT hVdT hw₀Vd hw₀ρ
  have hZ2 := card_C_Z_F4 h38 h39 h hA6 hTL hTC ρ hLTN β hβk hβe hρT hH h27 hdD hdM hdV
  obtain ⟨hdS, hVdC, hQ4⟩ := rest_S h38 h39 h hA6 hTL ρ hLTN β hβs hβk hβe hρT hρ1 hdT hdP
    hdR hRP (fun g hg hgV => (hρ1 g hg).mp ((hker g hg _).mpr hgV)) hVdLT hρVd htop hdV hℓc hρℓc
    hℓcP
  exact ⟨hrel, hdS, hVdC, hQ4, hT5, hZ2⟩

theorem step3_3_31S_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25_F4) (h27 : Stmt3_3_27_F4) : Step3_3_31S_F4 := by
  intro G _ _ T M L D h hA6 hTL hTC d hdD hdM hdV
  exact step3_3_31S_aux_F4 h38 h39 h25 h27 h hA6 hTL hTC hdD hdM hdV

end Lem3331S

end CFSG.Quasithin.H13
