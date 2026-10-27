module

public import CFSG.ClassicalInvolution.AschTight.S19BWC
public import CFSG.ClassicalInvolution.AschTight.Hall196QD
public import CFSG.ClassicalInvolution.AschTight.S19BStmt

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_normalizer_conjSub {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) (g : G) :
    g * x * g⁻¹ ∈ Subgroup.normalizer ((conjSub g A : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hx ⊢
  rw [← conjSub_mul, show g * x * g⁻¹ * g = g * x by group, conjSub_mul, hx]

omit [Finite G] in
theorem conj_mem_centralizerModOdd_top {J : Subgroup G} {x : G}
    (hx : x ∈ centralizerModOdd ⊤ J) (g : G) :
    g * x * g⁻¹ ∈ centralizerModOdd ⊤ (conjSub g J) := by
  obtain ⟨-, hxN, hxO, hx⟩ := hx
  refine ⟨Subgroup.mem_top _, conj_mem_normalizer_conjSub hxN g, ?_, fun l hl => ?_⟩
  · rw [S1916.oddCoreOf_conjSub]
    exact conj_mem_normalizer_conjSub hxO g
  · rw [mem_conjSub_iff] at hl
    rw [S1916.oddCoreOf_conjSub]
    have e : ⁅g * x * g⁻¹, l⁆ = g * ⁅x, g⁻¹ * l * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_conjSub (hx _ hl)

theorem mem_normalizer_inf {S J : Subgroup G} {x : G} (hxS : x ∈ S)
    (hxJ : x ∈ Subgroup.normalizer (J : Set G)) :
    x ∈ Subgroup.normalizer ((S ⊓ J : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hxJ ⊢
  refine Sec7.conjSub_eq_of_le_self fun y hy => ?_
  rw [mem_conjSub_iff] at hy
  refine ⟨?_, ?_⟩
  · have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact S.mul_mem (S.mul_mem hxS hy.1) (S.inv_mem hxS)
  · rw [← hxJ]
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact conj_mem_conjSub hy.2

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem mem_centralizerModOdd_K (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hxS : x ∈ (S : Subgroup G))
    (hxR : x ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) :
    x ∈ centralizerModOdd ⊤ K := by
  have ht := hd.tight
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight ht.toTightBranch]
    exact hd.hSz hxS
  refine ⟨Subgroup.mem_top x, hxN, mem_normalizer_oddCoreOf_of_mem_normalizer hxN,
    fun k hk => ?_⟩
  exact S1916.commutator_mem_oddCoreOf_of_centralizes ht (S1916.sd_isSylow2In_R hd.toSec19Data)
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)) hxN
    (fun r hr => Subgroup.mem_centralizer_iff.mp hxR r hr) hk

omit [IsSimpleGroup G] in
theorem mem_centralizer_inf_of_mem (S : Sylow 2 G) {J : Subgroup G} {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hxJ : x ∈ centralizerModOdd ⊤ J) :
    x ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ J : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (S1916.commute_of_mem_centralizerModOdd hxJ inf_le_right (S.isPGroup'.to_le inf_le_left)
    (mem_normalizer_inf hxS hxJ.2.1) hr).symm

theorem mem_centralizer_W (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hxK : x ∈ centralizerModOdd ⊤ K)
    (hxL : x ∈ centralizerModOdd ⊤ L) : x ∈ Subgroup.centralizer (W : Set G) := by
  have hR := mem_centralizer_inf_of_mem S hxS hxK
  have hV := mem_centralizer_inf_of_mem S hxS hxL
  rw [S1911.inf_member_eq hd] at hV
  have hle : W ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [S1911.sup_eq_inf_sup hd]
    refine sup_le (fun u hu => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hR u ⟨hd.hWS hu.2, hu.1⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hV v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem mem_sec19BPrime_iff (hd : Sec19DataT p f K z S W L t V) {x : G} :
    x ∈ sec19BPrime K S W L ↔
      x ∈ (S : Subgroup G) ∧ x ∈ centralizerModOdd ⊤ K ∧ x ∈ centralizerModOdd ⊤ L := by
  constructor
  · rintro ⟨⟨⟨hxS, hxR⟩, -⟩, hxL⟩
    exact ⟨hxS, mem_centralizerModOdd_K hd hxS hxR, hxL⟩
  · rintro ⟨hxS, hxK, hxL⟩
    exact ⟨⟨⟨hxS, mem_centralizer_inf_of_mem S hxS hxK⟩, mem_centralizer_W hd hxS hxK hxL⟩, hxL⟩

omit [Finite G] [IsSimpleGroup G] in
theorem mem_centralizerModOdd_conj_of_mem {b : G} (hb : b ∈ sec19BPrime K S W L) {r : G}
    (hr : r ∈ (S : Subgroup G) ⊓ K) : b ∈ centralizerModOdd ⊤ (conjSub r L) := by
  have h1 := conj_mem_centralizerModOdd_top hb.2 r
  have hrb : r * b * r⁻¹ = b := by
    rw [Subgroup.mem_centralizer_iff.mp hb.1.1.2 r hr]
    group
  rwa [hrb] at h1

theorem conjSub_mem_three (hd : Sec19DataT p f K z S W L t V) {r : G}
    (hrt : IsUniqueInvolution (conjSub r L) (t * z)) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) {J : Subgroup G}
    (hJ : J = K ∨ J = L ∨ J = conjSub r L) :
    conjSub n J = K ∨ conjSub n J = L ∨ conjSub n J = conjSub r L := by
  have ht := hd.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight ht
  have hzW : z ∈ W := Hall196.mem_W_of_sec19DataT hd
  have htW : t ∈ W := S1911.mem_W hd
  have hcl : ConjInvariant (CoreAssembly.conjClass K) := conjInvariant_conjClass K
  have hL' : conjSub r L ∈ CoreAssembly.conjClass K := hcl r L hd.memL
  obtain ⟨u, hJu, huW, hJmem⟩ : ∃ u, IsUniqueInvolution J u ∧ u ∈ W ∧
      J ∈ CoreAssembly.conjClass K := by
    rcases hJ with rfl | rfl | rfl
    · exact ⟨z, hI, hzW, CoreAssembly.mem_conjClass_self _⟩
    · exact ⟨t, hd.invL, htW, hd.memL⟩
    · exact ⟨t * z, hrt, W.mul_mem htW hzW, hL'⟩
  have hnu := hJu.conj n
  have hnuW : n * u * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hn u).mp huW
  have hmem : conjSub n J ∈ CoreAssembly.conjClass K := hcl n J hJmem
  rcases S1911.invol_mem_W hd hnuW hnu.sq hnu.ne_one with h | h | h
  · exact Or.inl (S1911.eq_of_isUniqueInvolution_member ht hmem
      (CoreAssembly.mem_conjClass_self K) hnu (h ▸ hI))
  · exact Or.inr (Or.inl (S1911.eq_of_isUniqueInvolution_member ht hmem hd.memL hnu
      (h ▸ hd.invL)))
  · exact Or.inr (Or.inr (S1911.eq_of_isUniqueInvolution_member ht hmem hL' hnu (h ▸ hrt)))

theorem mem_sec19BPrime_of_conj_mem (hd : Sec19DataT p f K z S W L t V) {b g : G}
    (hb : b ∈ sec19BPrime K S W L) (hgS : g * b * g⁻¹ ∈ (S : Subgroup G))
    (hgW : g * b * g⁻¹ ∈ Subgroup.centralizer (W : Set G)) :
    g * b * g⁻¹ ∈ sec19BPrime K S W L := by
  obtain ⟨n, hn, hnb⟩ := exists_normalizer_conj_eq hd hb.1.2 hgW
  obtain ⟨r, hr, hrt⟩ := S1911.exists_conj_eq_mul hd
  have hrt' : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hd.invL.conj r
  have hbJ : ∀ J : Subgroup G, (J = K ∨ J = L ∨ J = conjSub r L) → b ∈ centralizerModOdd ⊤ J := by
    rintro J (rfl | rfl | rfl)
    · exact ((mem_sec19BPrime_iff hd).mp hb).2.1
    · exact hb.2
    · exact mem_centralizerModOdd_conj_of_mem hb hr
  have key : ∀ J : Subgroup G, (J = K ∨ J = L ∨ J = conjSub r L) →
      n * b * n⁻¹ ∈ centralizerModOdd ⊤ J := by
    intro J hJ
    have h1 := conjSub_mem_three hd hrt' (Subgroup.inv_mem _ hn) hJ
    have h2 := conj_mem_centralizerModOdd_top (hbJ _ h1) n
    rwa [conjSub_conjSub_inv] at h2
  rw [← hnb] at hgS ⊢
  exact (mem_sec19BPrime_iff hd).mpr ⟨hgS, key K (Or.inl rfl), key L (Or.inr (Or.inl rfl))⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
