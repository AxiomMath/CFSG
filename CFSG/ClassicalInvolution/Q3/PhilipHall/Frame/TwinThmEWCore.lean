module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3OddStand
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189a

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Core



variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem inf_W_mem_USet_of_card (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (h2 : 2 < Nat.card ↥(M ⊓ (S : Subgroup G))) : M ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, hWη⟩ := hW
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  have hAW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂_of_le V hV le_rfl
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hAW V hV).trans hWS
  have hmem := Q3T8.Asc77.l6_11_proved G Ω hΩ S η ⟨S₁, hS₁, hinv⟩ hηS M hMΩ h2
  rw [← hWη] at hmem
  exact (hS₁.1 hmem).1

theorem inf_W_mem_USet' (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) {M R' : Subgroup G} (hMΩ : M ∈ Ω)
    (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M) (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ W ∈ USet Ω := by
  have h8 := hΩ.eight_le_of_mem_RSet hR'
  refine inf_W_mem_USet_of_card hΩ hW hWS hMΩ ?_
  have := Subgroup.card_le_of_le (le_inf hR'M hR'S)
  omega

theorem commutes_or_eq_of_le_sylow (hΩ : HypOmegaGen Ω) {S₂ : Sylow 2 G} {R₁ R₂ : Subgroup G}
    (hR₁ : R₁ ∈ RSet Ω) (hR₂ : R₂ ∈ RSet Ω) (h₁ : R₁ ≤ (S₂ : Subgroup G))
    (h₂ : R₂ ≤ (S₂ : Subgroup G)) : Commutes R₁ R₂ ∨ R₂ = R₁ := by
  by_cases h : R₂ = R₁
  · exact Or.inr h
  · exact Or.inl (Q3CP.l67Gen G Ω hΩ S₂ R₁ hR₁ R₂ hR₂ h₁ h₂ (Ne.symm h))

theorem exists_zW' (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {R : Subgroup G} (hRR : R ∈ RSet Ω)
    (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) : ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  refine ⟨z, hz, ?_⟩
  have hU := inf_W_mem_USet' hΩ hW hWS hK hRR hRK hRS
  obtain ⟨R', -, J', -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
  have hzV : z ∈ K ⊓ W :=
    mem_of_isUniqueInvolution_of_isPGroup hz inf_le_left (hΩ.isPGroup_of_mem_USet hU) (by omega)
  exact hzV.2

theorem centralizer_le_of_hyp (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {R : Subgroup G}
    (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hWS : W ≤ (S : Subgroup G)) (hE : CentPairs Ω (S : Subgroup G) W H) {z : G}
    (hz : IsUniqueInvolution K z) : Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z', hz', hz'W⟩ := exists_zW' hΩ hK hRR hRK hRS hW hWS
  have hzz : z' = z := hz'.eq hz
  subst hzz
  have hzR : z' ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz' hRK
    (Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK).2.1 (by have := hΩ.eight_le_of_mem_RSet hRR; omega)
  exact hE K hK (inf_W_mem_USet' hΩ hW hWS hK hRR hRK hRS) K (Set.mem_insert _ _) R R hRR hRK hRS
    hRR hRK hRS (Or.inr rfl) z' (Subgroup.mem_sup_left hzR) hz'W hz'.ne_one hz'.sq

theorem mem_of_conjSub_mem_dstarComp {K H : Subgroup G}
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) {z : G}
    (hz : IsUniqueInvolution K z) (hcz : Subgroup.centralizer ({z} : Set G) ≤ H) {g : G}
    (hg : conjSub g K ∈ dstarComp Ω K) : g ∈ H := by
  obtain ⟨h, hhH, hh⟩ := htrans _ hg
  have hn : conjSub (h⁻¹ * g) K = K := by
    rw [conjSub_mul, ← hh, conjSub_inv_conjSub]
  have hcent : h⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (hz.conj_eq hn)
  have hg' : g = h * (h⁻¹ * g) := by group
  rw [hg']
  exact H.mul_mem hhH (hcz hcent)

theorem mem_of_conjSub_eq_W' (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω)
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) {z : G}
    (hz : IsUniqueInvolution K z) (hcz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K : R' ≤ K) (hR'S : R' ≤ (S : Subgroup G))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hWS : W ≤ (S : Subgroup G)) {n : G}
    (hn : conjSub n W = W) : n ∈ H := by
  have hU := inf_W_mem_USet' hΩ hW hWS hK hR' hR'K hR'S
  have habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    obtain ⟨η, hη, hWη⟩ := hW
    obtain ⟨S₁, hS₁, hinv⟩ := hη
    have := etaAbelian_of_gen hΩ S₁ η hS₁ hinv
    rwa [← hWη] at this
  have hmem : conjSub n K ∈ dstarComp Ω K :=
    mem_dstarComp_of_mem_USet_le_W hΩ hK (hΩ.conjInvariant n K hK) hU inf_le_left inf_le_right
      (USet.conj hΩ.conjInvariant hU n) (conjSub_mono (n := n) inf_le_left)
      (by have := conjSub_mono (n := n) (inf_le_right : K ⊓ W ≤ W); rwa [hn] at this) habel
  exact mem_of_conjSub_mem_dstarComp htrans hz hcz hmem

theorem exists_conj_of_sylow_le {S S₂ : Sylow 2 G} {H : Subgroup G}
    (hS : (S : Subgroup G) ≤ H) (hS₂ : (S₂ : Subgroup G) ≤ H) :
    ∃ x ∈ H, conjSub x (S : Subgroup G) = (S₂ : Subgroup G) := by
  obtain ⟨h, hh⟩ := exists_conjSub_eq_of_sylow (G := ↥H) (S.subtype hS) (S₂.subtype hS₂)
  refine ⟨(h : G), h.2, ?_⟩
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have hxH : x ∈ H := by
      have := H.mul_mem (H.mul_mem h.2 (hS hx)) (H.inv_mem h.2)
      simpa [mul_assoc] using this
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ conjSub h (S.subtype hS : Subgroup ↥H) := by
      rw [mem_conjSub_iff]
      simpa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hx
    rw [hh] at hmem
    simpa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hmem
  · intro hx
    have hxH := hS₂ hx
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ ((S₂.subtype hS₂ : Sylow 2 ↥H) : Subgroup ↥H) := by
      simpa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hx
    rw [← hh, mem_conjSub_iff] at hmem
    simpa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hmem

theorem exists_W_of_sylow (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {H : Subgroup G}
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) {z : G}
    (hz : IsUniqueInvolution K z) (hcz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {R : Subgroup G} (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hWS : W ≤ (S : Subgroup G))
    (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W) (hCW : CentPairs Ω (S : Subgroup G) W H)
    {S₂ : Sylow 2 G} {R₂ : Subgroup G} (hR₂ : R₂ ∈ RSet Ω) (hR₂K : R₂ ≤ K)
    (hR₂S₂ : R₂ ≤ (S₂ : Subgroup G)) :
    ∃ x ∈ H, conjSub x (S : Subgroup G) = (S₂ : Subgroup G) ∧ conjSub x W ∈ WSet Ω ∧
      conjSub x W ≤ (S₂ : Subgroup G) ∧ (∀ s ∈ (S₂ : Subgroup G), conjSub s (conjSub x W) = conjSub x W) ∧
      CentPairs Ω (S₂ : Subgroup G) (conjSub x W) H := by
  have hSH : (S : Subgroup G) ≤ H := fun s hs =>
    mem_of_conjSub_eq_W' hΩ hK htrans hz hcz hRR hRK hRS hW hWS (hWn s hs)
  obtain ⟨W₂, hW₂, hW₂S, hW₂n⟩ := exists_W_of_hypOmega hΩ S₂
  have hS₂H : (S₂ : Subgroup G) ≤ H := fun s hs =>
    mem_of_conjSub_eq_W' hΩ hK htrans hz hcz hR₂ hR₂K hR₂S₂ hW₂ hW₂S (hW₂n s hs)
  obtain ⟨x, hxH, hx⟩ := exists_conj_of_sylow_le hSH hS₂H
  refine ⟨x, hxH, hx, WSet.conj hΩ.conjInvariant hW x, ?_, ?_,
    hx ▸ hCW.conj_of_mem hΩ.conjInvariant hxH⟩
  · rw [← hx]
    exact conjSub_mono hWS
  · intro s hs
    rw [← hx, mem_conjSub_iff] at hs
    calc conjSub s (conjSub x W) = conjSub x (conjSub (x⁻¹ * s * x) W) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub x W := by rw [hWn _ hs]

theorem mem_W_of_isUniqueInvolution (hΩ : HypOmegaGen Ω) {S₂ : Sylow 2 G} {W₂ : Subgroup G}
    (hW : W₂ ∈ WSet Ω) (hWS : W₂ ≤ (S₂ : Subgroup G)) {M R' : Subgroup G} (hM : M ∈ Ω)
    (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M) (hR'S : R' ≤ (S₂ : Subgroup G)) {t : G}
    (ht : IsUniqueInvolution M t) : t ∈ W₂ := by
  have hU := inf_W_mem_USet' hΩ hW hWS hM hR' hR'M hR'S
  obtain ⟨R'', -, J', -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
  have hzV : t ∈ M ⊓ W₂ :=
    mem_of_isUniqueInvolution_of_isPGroup ht inf_le_left (hΩ.isPGroup_of_mem_USet hU) (by omega)
  exact hzV.2

theorem centralizer_le_mul_of_omegaNbr (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {H : Subgroup G}
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) {z : G}
    (hz : IsUniqueInvolution K z) (hcz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {R : Subgroup G} (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hWS : W ≤ (S : Subgroup G))
    (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W) (hCW : CentPairs Ω (S : Subgroup G) W H)
    {J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) {t : G} (ht : IsUniqueInvolution J t)
    (ha1 : z * t ≠ 1) (ha2 : (z * t) * (z * t) = 1) :
    Subgroup.centralizer ({z * t} : Set G) ≤ H := by
  obtain ⟨R₁, T, hR₁, hTsyl, -, hRT⟩ := exists_commuting_sylow_pair hΩ hK hJ
  have hJΩ : J ∈ Ω := hJ.1
  have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR₁
  have hTΩ : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hTsyl
  have hP : IsPGroup 2 ↥(R₁ ⊔ T) :=
    hR₁.2.1.to_sup_of_normal_left' hTsyl.2.1 fun y hy =>
      mem_normalizer_iff_conjSub_eq.mpr
        (conjSub_eq_of_mem_of_commutes hy fun a ha b hb => (hRT b hb a ha).symm)
  obtain ⟨S₂, hS₂⟩ := hP.exists_le_sylow
  have hR₁S₂ : R₁ ≤ (S₂ : Subgroup G) := le_sup_left.trans hS₂
  have hTS₂ : T ≤ (S₂ : Subgroup G) := le_sup_right.trans hS₂
  obtain ⟨x, -, -, hW₂, hW₂S, -, hCW₂⟩ :=
    exists_W_of_sylow hΩ hK htrans hz hcz hRR hRK hRS hW hWS hWn hCW hR₁Ω hR₁.1 hR₁S₂
  have hzW₂ : z ∈ conjSub x W := mem_W_of_isUniqueInvolution hΩ hW₂ hW₂S hK hR₁Ω hR₁.1 hR₁S₂ hz
  have htW₂ : t ∈ conjSub x W := mem_W_of_isUniqueInvolution hΩ hW₂ hW₂S hJΩ hTΩ hTsyl.1 hTS₂ ht
  exact hCW₂ K hK (inf_W_mem_USet' hΩ hW₂ hW₂S hK hR₁Ω hR₁.1 hR₁S₂) J
    (Set.mem_insert_of_mem _ hJ) R₁ T hR₁Ω hR₁.1 hR₁S₂ hTΩ hTsyl.1 hTS₂ (Or.inl hRT) (z * t)
    (Subgroup.mul_mem_sup (mem_of_isUniqueInvolution_of_isPGroup hz hR₁.1 hR₁.2.1
        (by have := hΩ.eight_le_of_mem_RSet hR₁Ω; omega))
      (mem_of_isUniqueInvolution_of_isPGroup ht hTsyl.1 hTsyl.2.1
        (by have := hΩ.eight_le_of_mem_RSet hTΩ; omega)))
    ((conjSub x W).mul_mem hzW₂ htW₂) ha1 ha2

theorem mem_kPerp_of_twin_gen' (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) : K ∈ KPerp Ω L := by
  by_cases hKL : K = L
  · exact Set.mem_insert_iff.mpr (Or.inl hKL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hK, hKL, ?_⟩)
    obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
    exact ⟨R, hR, hRK.1, fun x hx =>
      Sec6Gen.le_normalizer_of_twin hΩ hK hL hKL hzK hzL (hRK.1 hx)⟩

theorem exists_order_four_inf_W (hΩ : HypOmegaGen Ω) {S₂ : Sylow 2 G} {W₂ : Subgroup G}
    (hW : W₂ ∈ WSet Ω) (hWS : W₂ ≤ (S₂ : Subgroup G)) {M R' : Subgroup G} (hM : M ∈ Ω)
    (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M) (hR'S : R' ≤ (S₂ : Subgroup G)) :
    ∃ u ∈ M ⊓ W₂, orderOf u = 4 ∧ u ∈ R' := by
  have hU := inf_W_mem_USet' hΩ hW hWS hM hR' hR'M hR'S
  obtain ⟨R'', -, J, -, hRJ, hUR, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
  obtain ⟨u, hu, hu4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic
    (hΩ.isPGroup_of_mem_USet hU) hcyc h4
  refine ⟨u, hu, hu4, ?_⟩
  have hsyl : IsSylow2In R' M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hM hR' hR'M
  have heq : M ⊓ (S₂ : Subgroup G) = R' :=
    hsyl.eq_of_le (S₂.isPGroup'.to_le inf_le_right) inf_le_left (le_inf hR'M hR'S)
  rw [← heq]
  exact ⟨hu.1, hWS hu.2⟩

theorem centralizer_le_of_fusion (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {H : Subgroup G}
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) {z : G}
    (hz : IsUniqueInvolution K z) (hcz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {R : Subgroup G} (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hWS : W ≤ (S : Subgroup G))
    (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W) (hCW : CentPairs Ω (S : Subgroup G) W H)
    {K'' R₁ R₂ : Subgroup G} (hK'' : K'' ∈ Ω) (hz'' : IsUniqueInvolution K'' z)
    (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K'') (hRc : Commutes R₁ R₂) {u : G}
    (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hF : (∃ e ∈ H, e * u * e⁻¹ = z) ∨ ∀ a ∈ R₁, ∀ b ∈ R₂, orderOf a = 4 → orderOf b = 4 →
      ∃ e ∈ H, e * u * e⁻¹ = a * b) : Subgroup.centralizer ({u} : Set G) ≤ H := by
  rcases hF with ⟨e, heH, he⟩ | hF
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hg' : e * g * e⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← he]
      calc e * g * e⁻¹ * (e * u * e⁻¹) = e * (g * u) * e⁻¹ := by group
        _ = e * (u * g) * e⁻¹ := by rw [hg]
        _ = e * u * e⁻¹ * (e * g * e⁻¹) := by group
    have h2 : e⁻¹ * (e * g * e⁻¹) * e ∈ H := H.mul_mem (H.mul_mem (H.inv_mem heH) (hcz hg')) heH
    simpa [mul_assoc] using h2
  have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR₁
  have hR₂Ω : R₂ ∈ RSet Ω := mem_RSet_of_isSylow2In hK'' hR₂
  have hP : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    hR₁.2.1.to_sup_of_normal_left' hR₂.2.1 fun y hy =>
      mem_normalizer_iff_conjSub_eq.mpr
        (conjSub_eq_of_mem_of_commutes hy fun a ha b hb => (hRc b hb a ha).symm)
  obtain ⟨S₂, hS₂⟩ := hP.exists_le_sylow
  have hR₁S₂ : R₁ ≤ (S₂ : Subgroup G) := le_sup_left.trans hS₂
  have hR₂S₂ : R₂ ≤ (S₂ : Subgroup G) := le_sup_right.trans hS₂
  obtain ⟨x, -, -, hW₂, hW₂S, -, hCW₂⟩ :=
    exists_W_of_sylow hΩ hK htrans hz hcz hRR hRK hRS hW hWS hWn hCW hR₁Ω hR₁.1 hR₁S₂
  obtain ⟨x₀, hx₀, hx₀4, hx₀R⟩ := exists_order_four_inf_W hΩ hW₂ hW₂S hK hR₁Ω hR₁.1 hR₁S₂
  obtain ⟨y₀, hy₀, hy₀4, hy₀R⟩ := exists_order_four_inf_W hΩ hW₂ hW₂S hK'' hR₂Ω hR₂.1 hR₂S₂
  obtain ⟨e, heH, he⟩ := hF x₀ hx₀R y₀ hy₀R hx₀4 hy₀4
  have ha1 : x₀ * y₀ ≠ 1 := by
    intro h
    apply hu1
    rw [h] at he
    have : u = e⁻¹ * (e * u * e⁻¹) * e := by group
    rw [this, he]
    group
  have ha2 : (x₀ * y₀) * (x₀ * y₀) = 1 := by
    rw [← he]
    calc e * u * e⁻¹ * (e * u * e⁻¹) = e * (u * u) * e⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hCa := hCW₂ K hK (inf_W_mem_USet' hΩ hW₂ hW₂S hK hR₁Ω hR₁.1 hR₁S₂) K''
    (mem_kPerp_of_twin_gen' hΩ hK'' hK hz'' hz) R₁ R₂ hR₁Ω hR₁.1 hR₁S₂ hR₂Ω hR₂.1 hR₂S₂ (Or.inl hRc)
    (x₀ * y₀) (Subgroup.mul_mem_sup hx₀R hy₀R) ((conjSub x W).mul_mem hx₀.2 hy₀.2) ha1 ha2
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hg' : e * g * e⁻¹ ∈ Subgroup.centralizer ({x₀ * y₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← he]
    calc e * g * e⁻¹ * (e * u * e⁻¹) = e * (g * u) * e⁻¹ := by group
      _ = e * (u * g) * e⁻¹ := by rw [hg]
      _ = e * u * e⁻¹ * (e * g * e⁻¹) := by group
  have := hCa hg'
  have h2 : e⁻¹ * (e * g * e⁻¹) * e ∈ H := H.mul_mem (H.mul_mem (H.inv_mem heH) this) heH
  simpa [mul_assoc] using h2

end Core

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
