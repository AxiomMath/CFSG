module

public import CFSG.ClassicalInvolution.AschTight.S1916HalfA
public import CFSG.ClassicalInvolution.AschTight.Sec7L612B
public import CFSG.ClassicalInvolution.AschTight.Sec7L76C

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G}

theorem Ctx12.weaklyClosed [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    Sec7.WeaklyClosedIn W (S : Subgroup G) := by
  have hd := c.hd
  have ht := hd.tight
  have hp := ht.branch.odd
  have hq := ht.branch.five
  have hΩ := hypOmegaMod_of_tightD ht
  obtain ⟨η, hη, hinv, hWη⟩ := c.eta
  have htr : ∀ K₁ ∈ CoreAssembly.conjClass K, ∀ K₂ ∈ CoreAssembly.conjClass K,
      ∃ g : G, conjSub g K₁ = K₂ := by
    rintro K₁ ⟨g₁, rfl⟩ K₂ ⟨g₂, rfl⟩
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have h612 := Sec7.l6_12_on hp hq hΩ (fun S => (l6_9_proved p f hp hq G _ hΩ S).1)
    (fun η ⟨S, hS, hinv⟩ => ((l6_9_proved p f hp hq G _ hΩ S).2 η hS hinv).1)
    (l6_11_proved p f hp hq G _ hΩ) htr S
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  · have hMS : (⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG (CoreAssembly.conjClass K), U ∈ η) ∧
        U ≤ (S : Subgroup G)}, U) ≤ (S : Subgroup G) := iSup₂_le fun U hU => hU.2
    have heq : η = η₀ := huniq η hη fun m hm U hU => hinv m (hMS hm) U hU
    subst heq
    intro g hg
    rw [hWη] at hg ⊢
    refine Sec7.conjSub_iSup_eq_of_forall_mem (hwc g fun U hU => ?_)
    exact (conjSub_mono (le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) U hU le_rfl)).trans hg
  · exfalso
    have hV4 := c.four_le_card_V
    obtain ⟨M, hM, hLSM⟩ := exists_isSylow2In_of_mem_RSet (h2 L c.data.memL c.two_lt_card_L_inf_S)
    have h1 := c.isSylow2In_V.natCard_le hLSM.2.1
      (inf_le_inf_left L hd.hSz : L ⊓ (S : Subgroup G) ≤ L ⊓ Subgroup.centralizer ({z} : Set G))
    rw [hΩ.natCard_isSylow2In hM hLSM, ← hΩ.natCard_isSylow2In
      (CoreAssembly.mem_conjClass_self K) (sd_isSylow2In_R hd), c.card_R] at h1
    omega

theorem Ctx12.exists_conj_eq [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    ∃ h : G, conjSub h W = W ∧ h * z * h⁻¹ = t := by
  have hd := c.hd
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨g, hg⟩ := c.data.memL
  change conjSub g K = L at hg
  have e : t = g * z * g⁻¹ := c.data.invL.eq (hg ▸ hzK.conj g)
  have hzW : z ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_centralizer_iff.mpr fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz (hd.hWS hw))
  have htW : g * z * g⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    rw [← e]
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => c.ab w hw t (c.data.leW c.data.memT)
  obtain ⟨n, hn, hnz⟩ := Sec7.control_centralizer_of_weaklyClosed (S.isPGroup'.to_le hd.hWS)
    c.weaklyClosed hzW htW
  exact ⟨n, mem_normalizer_iff_conjSub_eq.mp hn, hnz.trans e.symm⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
