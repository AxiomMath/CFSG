module

public import CFSG.ClassicalInvolution.AschTight.S19BFus
public import CFSG.ClassicalInvolution.AschTight.S19BEnd
public import CFSG.ClassicalInvolution.AschTight.S1911C11
public import CFSG.ClassicalInvolution.AschTight.S19BCtl

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

omit [IsSimpleGroup G] in
theorem mem_centralizer_R_of_mem_T (hd : Sec19DataT p f K z S W L t V) {a : G}
    (ha : a ∈ sec19T K z S) :
    a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact S1911.mem_centralizer_of_mem_centralizerModOdd ha.1 ha.2 hr.1
    (S1911.inf_le_sec19X hd.toSec19Data hr)

omit [IsSimpleGroup G] in
theorem mem_centralizer_W_of_mem_T (hd : Sec19DataT p f K z S W L t V) {a : G}
    (ha : a ∈ sec19T K z S) : a ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact S1911.mem_centralizer_of_mem_centralizerModOdd ha.1 ha.2 (hd.hWS hw)
    (S1911.le_sec19X hd.toSec19Data hw)

theorem mem_cStarK_of_mem_T (hd : Sec19DataT p f K z S W L t V) {a : G}
    (ha : a ∈ sec19T K z S) : a ∈ centralizerModOdd ⊤ K :=
  mem_centralizerModOdd_K hd ha.1 (mem_centralizer_R_of_mem_T hd ha)

omit [IsSimpleGroup G] in
theorem conj_mem_T {a c : G} (ha : a ∈ sec19T K z S)
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hcS : c * a * c⁻¹ ∈ (S : Subgroup G)) :
    c * a * c⁻¹ ∈ sec19T K z S := by
  have htop : conjSub c (⊤ : Subgroup G) = ⊤ :=
    eq_top_iff.mpr fun x _ => mem_conjSub_iff.mpr (Subgroup.mem_top _)
  have hle := Hall196.conjSub_centralizerModOdd_le (H := ⊤) (L := sec19X K z)
    (Hall196.centralizer_le_normalizer_sec19X K z hc) htop
  exact ⟨hcS, hle (conj_mem_conjSub ha.2)⟩

theorem exists_not_isolated (hd : Sec19DataT p f K z S W L t V) {b c : G}
    (hb : b ∈ sec19T K z S ⊓ centralizerModOdd ⊤ L)
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ h : G, h * (c * b * c⁻¹) = (c * b * c⁻¹) * h ∧ h * z * h⁻¹ ≠ z ∧
      h * z * h⁻¹ * z = z * (h * z * h⁻¹) := by
  obtain ⟨g, hgb, hgz⟩ := exists_conj_eq_t_of_centralizes hd hb.1.1
    (mem_centralizer_R_of_mem_T hd hb.1) (mem_centralizer_W_of_mem_T hd hb.1) hb.2
  have hcz : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have htz : t * z = z * t :=
    S1911.comm_of_mem hd.toSec19Data t (S1911.mem_W hd) z (Hall196.mem_W_of_sec19DataT hd)
  have e : c * g * c⁻¹ * z * (c * g * c⁻¹)⁻¹ = c * t * c⁻¹ := by
    calc c * g * c⁻¹ * z * (c * g * c⁻¹)⁻¹ = c * (g * (c⁻¹ * z * c) * g⁻¹) * c⁻¹ := by group
      _ = c * (g * z * g⁻¹) * c⁻¹ := by
          rw [show c⁻¹ * z * c = z by
            calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
              _ = z := by group]
      _ = c * t * c⁻¹ := by rw [hgz]
  refine ⟨c * g * c⁻¹, ?_, ?_, ?_⟩
  · calc c * g * c⁻¹ * (c * b * c⁻¹) = c * (g * b) * c⁻¹ := by group
      _ = c * (b * g) * c⁻¹ := by rw [hgb]
      _ = c * b * c⁻¹ * (c * g * c⁻¹) := by group
  · rw [e]
    intro h
    apply hd.ne
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [h]
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
      _ = z := by group
  · rw [e]
    calc c * t * c⁻¹ * z = c * t * c⁻¹ * (c * z * c⁻¹) := by rw [hcz]
      _ = c * (t * z) * c⁻¹ := by group
      _ = c * (z * t) * c⁻¹ := by rw [htz]
      _ = (c * z * c⁻¹) * (c * t * c⁻¹) := by group
      _ = z * (c * t * c⁻¹) := by rw [hcz]

theorem conj_mem_B (hd : Sec19DataT p f K z S W L t V) (h93 : C19_9s3Tmp p f)
    (h92 : C19_9s2Tmp p f) {b c : G} (hb : b ∈ sec19T K z S ⊓ centralizerModOdd ⊤ L)
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hcS : c * b * c⁻¹ ∈ (S : Subgroup G)) :
    c * b * c⁻¹ ∈ sec19T K z S ⊓ centralizerModOdd ⊤ L := by
  have haT := conj_mem_T hb.1 hc hcS
  obtain ⟨h', hh'a, hne, hcomm, u, huK, hu4, hu⟩ :=
    h92 G K z S W L t V hd _ haT (exists_not_isolated hd hb hc)
  obtain ⟨g', hg'a, hg'z⟩ := h93 G K z S W L t V hd _ haT h' hh'a hne hcomm ⟨u, huK, hu4, hu⟩
  have ht := hd.tight.toTightBranch
  have hgK : conjSub g' K = L := by
    have h1 := (isUniqueInvolution_of_tight ht).conj g'
    rw [hg'z] at h1
    exact S1911.eq_of_isUniqueInvolution_member ht
      (conjInvariant_conjClass K g' K (CoreAssembly.mem_conjClass_self K)) hd.memL h1 hd.invL
  have h2 := conj_mem_centralizerModOdd_top (mem_cStarK_of_mem_T hd haT) g'
  have e : g' * (c * b * c⁻¹) * g'⁻¹ = c * b * c⁻¹ := by
    rw [hg'a]
    group
  rw [hgK, e] at h2
  exact ⟨haT, h2⟩

theorem c19_11c_of (hB1 : GoldschmidtB1Tmp) (h93 : C19_9s3Tmp p f) (h92 : C19_9s2Tmp p f)
    (h91 : C19_9s1Tmp p f) : C19_11cTmp p f := by
  intro G _ _ _ K z S W L t V hd
  by_contra hne
  have hsc : fusionStronglyClosed
      ((sec19T K z S ⊓ centralizerModOdd ⊤ L : Subgroup G) : Set G) (S : Subgroup G) := by
    intro b hb g hg
    by_cases hb1 : b = 1
    · subst hb1
      rw [mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    have hxz : g⁻¹ * b * g * z = z * (g⁻¹ * b * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hg)
    have hcomm : g * z * g⁻¹ * b = b * (g * z * g⁻¹) := by
      calc g * z * g⁻¹ * b = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * b * g * z) * g⁻¹ := by rw [hxz]
        _ = b * (g * z * g⁻¹) := by group
    obtain ⟨h, hhb, hh⟩ := h91 G K z S W L t V hd b hb hb1 g hcomm
    obtain ⟨k, hkb, hkz⟩ := exists_conj_eq_t_of_centralizes hd hb.1.1
      (mem_centralizer_R_of_mem_T hd hb.1) (mem_centralizer_W_of_mem_T hd hb.1) hb.2
    have hhb' : h * b * h⁻¹ = b := by
      rw [hhb]
      group
    have hkb' : k * b * k⁻¹ = b := by
      rw [hkb]
      group
    obtain ⟨c, hcz, hcb⟩ : ∃ c : G, c ∈ Subgroup.centralizer ({z} : Set G) ∧
        c * b * c⁻¹ = g⁻¹ * b * g := by
      rcases hh with hh | hh
      · refine ⟨g⁻¹ * h, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
        · calc g⁻¹ * h * z = g⁻¹ * (h * z * h⁻¹) * h := by group
            _ = g⁻¹ * (g * z * g⁻¹) * h := by rw [hh]
            _ = z * (g⁻¹ * h) := by group
        · calc g⁻¹ * h * b * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * b * h⁻¹) * g := by group
            _ = g⁻¹ * b * g := by rw [hhb']
      · refine ⟨g⁻¹ * h * k, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
        · calc g⁻¹ * h * k * z = g⁻¹ * (h * (k * z * k⁻¹) * h⁻¹) * (h * k) := by group
            _ = g⁻¹ * (h * t * h⁻¹) * (h * k) := by rw [hkz]
            _ = g⁻¹ * (g * z * g⁻¹) * (h * k) := by rw [hh]
            _ = z * (g⁻¹ * h * k) := by group
        · calc g⁻¹ * h * k * b * (g⁻¹ * h * k)⁻¹ = g⁻¹ * (h * (k * b * k⁻¹) * h⁻¹) * g := by
                group
            _ = g⁻¹ * (h * b * h⁻¹) * g := by rw [hkb']
            _ = g⁻¹ * b * g := by rw [hhb']
    rw [← hcb] at hg ⊢
    exact conj_mem_B hd h93 h92 hb hcz hg
  exact false_of_stronglyClosed (B := sec19T K z S ⊓ centralizerModOdd ⊤ L) (L := K) hB1
    hd.tight.branch.nonabelian S (fun x hx => hx.1.1) hne hsc
    (fun x hx => mem_cStarK_of_mem_T hd hx.1)
    (not_isSolvable_quotient_of_isClassicalMember hd.tight.branch.five hd.tight.branch.member)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
