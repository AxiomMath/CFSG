module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.inf_le_of_l34 (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hHM : H ⊓ M ≤ H₁) (hne : H₁ ≠ H) :
    H ⊓ H₁ ≤ M := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE (Or.inl ⟨hp3, hL⟩)
  obtain ⟨T, hT, -, -, -, -, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  have hRKp : IsPGroup p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) := Rbar.isPGroup'.to_le inf_le_left
  have h2 : 2 ≤ Open.pRank p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hp hd.cfg.red.ne_two hRKp
      hd.noncyclic
  have hN : Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H :=
    hd.cfg.red.normalizer_le_of_mem_centralizer hzbR (fun h => hzbK h.2) hzbp
      (Subgroup.centralizer_le inf_le_right hzbc) inf_le_left h2
  have htop : Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ⊔ K = ⊤ := by
    rw [← hT₁]
    exact Sylow.normalizer_sup_eq_top T₁
  set Y := ((H ⊓ H₁).subgroupOf H).map π with hYdef
  have hXY : d1X0 p M H ≤ Y := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp hx).1,
      hHM (Subgroup.mem_subgroupOf.mp hx)⟩
  have hΓY : GLBCore p 1 (T₁ : Subgroup K) ≤ Y.subgroupOf K := by
    rw [← hY]
    exact Subgroup.comap_mono hXY
  have hcoreM : ∀ h : H, π h = 1 → (h : G) ∈ M := fun h h1 =>
    hd.cfg.ext.primeCore_le ((mk'_primeComplementCore_eq_one_iff p h).mp h1)
  rcases (hUE K p (Or.inl ⟨hp3, hL⟩) T₁ hΓT).1 (Y.subgroupOf K) hΓY with hYK | hYK
  ·
    intro j hj
    have hjY : π ⟨j, hj.1⟩ ∈ Y := ⟨⟨j, hj.1⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    have hjt : π ⟨j, hj.1⟩ ∈ K ⊔ Subgroup.normalizer
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
      rw [sup_comm, htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, n, hn, hkn⟩ := Subgroup.mem_sup_of_normal_left.mp hjt
    have hnX : n ∈ d1X0 p M H := hN hn
    have hkY : k ∈ Y := by
      have e : k = π ⟨j, hj.1⟩ * n⁻¹ := by rw [← hkn]; group
      rw [e]
      exact Y.mul_mem hjY (Y.inv_mem (hXY hnX))
    have hkX : k ∈ d1X0 p M H := by
      have h1 : (⟨k, hk⟩ : K) ∈ Y.subgroupOf K := Subgroup.mem_subgroupOf.mpr hkY
      rw [hYK, ← hY] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have hjX : π ⟨j, hj.1⟩ ∈ d1X0 p M H := hkn ▸ (d1X0 p M H).mul_mem hkX hnX
    obtain ⟨m, hm, hmj⟩ := hjX
    have hm' : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
    have h1 : π (m⁻¹ * ⟨j, hj.1⟩) = 1 := by rw [map_mul, map_inv, hmj, inv_mul_cancel]
    have := hcoreM _ h1
    have e : j = (m : G) * ((m⁻¹ * ⟨j, hj.1⟩ : H) : G) := by simp
    rw [e]
    exact M.mul_mem hm' this
  ·
    exfalso
    have hKY : K ≤ Y := fun k hk => by
      have h1 : (⟨k, hk⟩ : K) ∈ Y.subgroupOf K := hYK ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
    have hYtop : Y = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact sup_le (hN.trans hXY) hKY
    have hHH₁ : H ≤ H₁ := by
      intro h hh
      have hmem : π ⟨h, hh⟩ ∈ Y := hYtop ▸ Subgroup.mem_top _
      obtain ⟨j, hj, hjh⟩ := hmem
      have h1 : π (j⁻¹ * ⟨h, hh⟩) = 1 := by rw [map_mul, map_inv, hjh, inv_mul_cancel]
      have hjH₁ : (j : G) ∈ H₁ := (Subgroup.mem_subgroupOf.mp hj).2
      have hOH₁ : ((j⁻¹ * ⟨h, hh⟩ : H) : G) ∈ H₁ :=
        hHM ⟨(j⁻¹ * ⟨h, hh⟩ : H).2, hcoreM _ h1⟩
      have e : h = (j : G) * ((j⁻¹ * ⟨h, hh⟩ : H) : G) := by simp
      rw [e]
      exact H₁.mul_mem hjH₁ hOH₁
    exact hne (hd.cfg.ext.maxTwoLocal_H.2 H₁ hH₁.1 hHH₁)

theorem D1OneSmallData.false_of_l34_third (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hI : D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hHM : H ⊓ M ≤ H₁) (hne : H₁ ≠ H)
    (hneM : H₁ ≠ M) : False := by
  have hH₁M : ¬ H₁ ≤ M := fun h => hneM (hH₁.2 M hd.cfg.ext.maxTwoLocal_M.1 h).symm
  have hinf := hd.inf_le_of_l34 hUE hp3 hL hH₁ hHM hne
  subst hp3
  have hE : (3 = 3 ∧ IsLinThreeFour K) ∨ (3 = 5 ∧ IsFi22 K) := Or.inl ⟨rfl, hL⟩
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE hE
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hsolv := hΓ3 K hs hn hc T₁ hTnc hΓT hd.small (Or.inr (Or.inr hL))
  refine hd.false_of_l34_escape hβ hα h2 h3 hOut hExp hOrb hSh3 hO hz hB0 rfl hL hOR hCz hH₁
    hH₁M hHM fun U hU hUp => ?_
  have hUH : U ≤ H := hU.trans (inf_le_right.trans hCz)
  have hUM : U ≤ M := (le_inf hUH (hU.trans inf_le_left)).trans hinf
  exact D1OneSmallData.coprime_card_of_perfect_of_eq hd hI hY (hSch K hs hn hc) hsolv
    (le_inf hUH hUM) hUp

@[expose] def D1SmallGEVNormalL34Ph3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K → D1SmallU2Fails p M H K →
    GLBPrimeCore p (H ⊓ M) ≠ GLBPrimeCore p H → pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p H →
    (∀ hzH : z ∈ H,
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal) →
    (∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → H ⊓ M ≤ H₁ → H₁ = H ∨ H₁ = M) →
    False

theorem d1SmallGEVNormalL34Ph2_of_ph3 (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hPh3 : D1SmallGEVNormalL34Ph3) :
    D1SmallGEVNormalL34Ph2 := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV hCz
    hcore hA
  refine hPh3 G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV hCz
    hcore hA fun H₁ hH₁ hHM => ?_
  by_contra hcon
  push Not at hcon
  exact hd.false_of_l34_third hβ hα h2 h3 hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hz hI hB0 hp3 hL
    hOR hCz hH₁ hHM hcon.1 hcon.2

end CFSG.AGLEmbedding
