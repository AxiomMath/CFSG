module

public import CFSG.ClassicalInvolution.AschTight.S19BCtl
public import CFSG.ClassicalInvolution.AschTight.S1911C11

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_mem_V_mul_inv_mem_centralizer (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hxW : x ∈ Subgroup.centralizer (W : Set G)) :
    ∃ c ∈ V, x * c⁻¹ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hd0 := hd.toSec19Data
  have hNK : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
    exact hd.hSz
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun u hu => ⟨hd.hWS hu.2, hu.1⟩
  have hcard := S1911.card_inf_eq hd0
  obtain ⟨b, hbR, hbU⟩ := S1911.exists_mem_not_mem hcard
  have hcomm := S1911.comm_of_mem hd0
  have hxR := mem_normalizer_inf hxS (hNK hxS)
  have hxU : ∀ u ∈ K ⊓ W, x * u = u * x := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp hxW u hu.2).symm
  have hVR : V ≤ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    fun v hv => mem_normalizer_inf (hd.hWS (hd.leW hv)) (hNK (hd.hWS (hd.leW hv)))
  have hVU : ∀ c ∈ V, ∀ u ∈ K ⊓ W, c * u = u * c := fun c hc u hu =>
    hcomm c (hd.leW hc) u hu.2
  have hdisj : V ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun v hv => ?_
    have h1 : v ∈ W ⊓ sec19Y K z := by
      rw [S1911.inf_sec19Y_eq hd0]
      exact ⟨hd.leW hv.1, hv.2⟩
    have h2 : v ∈ V ⊓ sec19Y K z := ⟨hv.1, h1.2⟩
    rw [S1911.inf_sec19Y_eq_bot hd] at h2
    exact h2
  obtain ⟨c, hcV, hcdef⟩ := S1911.exists_defect_eq hUR hcard hVR hVU hdisj
    (S1911.card_inf_eq_card hd).le hbR hbU (S1911.inv_mul_conj_mem hUR hcard hbR hxR hxU)
  exact ⟨c, hcV, S1911.mem_centralizer_of_defect_eq hUR hcard hbR hbU (hVR hcV) hxU
    (hVU c hcV) hcdef.symm⟩

theorem centralizer_W_le_sup (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) ≤ W ⊔ sec19BPrime K S W L := by
  rintro x ⟨hxS, hxW⟩
  have hd0 := hd.toSec19Data
  have hcomm := S1911.comm_of_mem hd0
  have htW := S1911.mem_W hd
  obtain ⟨c, hcV, hc⟩ := exists_mem_V_mul_inv_mem_centralizer hd hxS hxW
  have hcS : c ∈ (S : Subgroup G) := hd.hWS (hd.leW hcV)
  have haS : x * c⁻¹ ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem hxS ((S : Subgroup G).inv_mem hcS)
  have hct : c⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    refine Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    exact hcomm c (hd.leW hcV) t htW
  have hxt : x ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxW t htW).symm
  have hat : x * c⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mul_mem _ hxt hct
  obtain ⟨RL, hRL, w, hw, haw⟩ := S1911.exists_mul_eq_of_mem_A hd haS hc hat
  have hwS : w ∈ (S : Subgroup G) := hd.hWS hw.1
  have hwt : w⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm w hw.1 t htW))
  have hbS : x * c⁻¹ * w⁻¹ ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem haS ((S : Subgroup G).inv_mem hwS)
  have hbL : x * c⁻¹ * w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    S1911.centralizer_le_normalizer_member hd.tight.toTightBranch hd.memL hd.invL
      (Subgroup.mul_mem _ hat hwt)
  have hbR : x * c⁻¹ * w⁻¹ ∈
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hw.2)
  have hb : x * c⁻¹ * w⁻¹ ∈ sec19BPrime K S W L :=
    (mem_sec19BPrime_iff hd).mpr ⟨hbS, mem_centralizerModOdd_K hd hbS hbR,
      S1911.mem_centralizerModOdd_of_mem_centralizer hd hbS hbL hRL haw⟩
  have e : x = x * c⁻¹ * w⁻¹ * (w * c) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb)
    (Subgroup.mem_sup_left (W.mul_mem hw.1 (hd.leW hcV)))

theorem centralizer_W_eq_sup (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) = W ⊔ sec19BPrime K S W L := by
  refine le_antisymm (centralizer_W_le_sup hd) (sup_le (fun w hw => Subgroup.mem_inf.mpr
    ⟨hd.hWS hw, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      S1911.comm_of_mem hd.toSec19Data v hv w hw⟩) fun b hb => ⟨hb.1.1.1, hb.1.2⟩)

theorem inf_sec19BPrime_eq_bot (hd : Sec19DataT p f K z S W L t V) :
    W ⊓ sec19BPrime K S W L = ⊥ := by
  obtain ⟨RL, hRL, hWRL, -, -⟩ := S1911.exists_sylow_member hd
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxN : x ∈ Subgroup.normalizer (RL : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.1)
  have hxRL : x ∈ Subgroup.centralizer (RL : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (S1916.commute_of_mem_centralizerModOdd hx.2.2 hRL.1 hRL.2.1 hxN hy).symm
  have h := S1911.inf_centralizer_inf_eq_bot hd hRL
  have hmem : x ∈ W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (RL : Set G) := ⟨⟨hx.1, hx.2.1.1.2⟩, hxRL⟩
  rw [h] at hmem
  exact hmem

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
