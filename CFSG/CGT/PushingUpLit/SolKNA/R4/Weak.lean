module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.E11
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenE612
public import CFSG.ClassicalInvolution.AschTight.S19BCtl

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section BP

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataR

variable (hd : TightSylowDataR r K z S W)
include hd

theorem inf_mem_USet : K ⊓ W ∈ USet (CoreAssembly.conjClass K) := by
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := hd.exists_eta
  exact (hη.1 (hd.inf_mem_eta hη hinv hWη hηS)).1

end TightSylowDataR

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem mem_W_z : z ∈ W := by
  have hI := hd.tight.isUniqueInvolution
  have h2 : IsPGroup 2 ↥(K ⊓ W) := S.isPGroup'.to_le (inf_le_right.trans hd.hWS)
  have hz := S1911.mem_of_le_member hI inf_le_left h2
    (by rw [hd.card_inf_eq_card]; have := hd.four_le_card_V; omega)
  exact hz.2

theorem forall_conjSub_mem_of_mem_iSup {η : Set (Subgroup G)}
    (hη : η ∈ etaG (CoreAssembly.conjClass K)) (hηS : ∀ U ∈ η, U ≤ (S : Subgroup G)) {m : G}
    (hm : m ∈ ⨆ U ∈ {U : Subgroup G | (∃ η' ∈ etaG (CoreAssembly.conjClass K), U ∈ η') ∧
      U ≤ (S : Subgroup G)}, U) :
    ∀ U ∈ η, conjSub m U ∈ η := by
  have h610 := (Sec6Gen.l6_10Gen G _ hd.tight.hypGen S η hη hηS).2
  refine S19B.mem_permSub_iff.mp ((iSup₂_le fun U hU => ?_ : _ ≤ S19B.permSub η) hm)
  obtain ⟨⟨η', ⟨S', hη'S', -⟩, hUη'⟩, hUS⟩ := hU
  have hUU : U ∈ USet (CoreAssembly.conjClass K) := (hη'S'.1 hUη').1
  exact fun u hu => S19B.mem_permSub_iff.mpr (h610 U hUU hUS u hu)

theorem weaklyClosedIn_W : Sec7.WeaklyClosedIn W (S : Subgroup G) := by
  have hd0 := hd.toTightSylowDataR
  have hΩ := hd.tight.hypGen
  obtain ⟨η, hη, hWη⟩ := hd.hW
  have hηS : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU =>
    (hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) U hU le_rfl).trans hd.hWS
  have htr : ∀ K₁ ∈ CoreAssembly.conjClass K, ∀ K₂ ∈ CoreAssembly.conjClass K,
      ∃ g : G, conjSub g K₁ = K₂ := by
    rintro K₁ ⟨g₁, rfl⟩ K₂ ⟨g₂, rfl⟩
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have h612 := Q3T6.Gen612.l6_12_on hΩ (fun S => Sec6Gen.exists_invariant_mem_etaSet hΩ S)
    (fun η ⟨S, hS, hinv⟩ => (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hS hinv).1)
    (Sec6Gen.l6_11Gen G _ hΩ) htr S
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  · have heq : η = η₀ := huniq η hη fun m hm U hU =>
      hd.forall_conjSub_mem_of_mem_iSup hη hηS hm U hU
    subst heq
    intro g hg
    rw [hWη] at hg ⊢
    refine Sec7.conjSub_iSup_eq_of_forall_mem (hwc g fun U hU => ?_)
    exact (conjSub_mono (le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) U hU le_rfl)).trans hg
  · exfalso
    have hV4 := hd.four_le_card_V
    have hLS : L ⊓ (S : Subgroup G) = V := by rw [inf_comm]; exact hd.inf_member_eq
    obtain ⟨M, hM, hVM⟩ :=
      exists_isSylow2In_of_mem_RSet (hLS ▸ h2 L hd.memL (by rw [hLS]; omega))
    have h1 := Sec6Gen.natCard_isSylow2In_eq hΩ hM (CoreAssembly.mem_conjClass_self K) hVM
      hd0.isSylow2In_inf
    rw [hd0.card_inf_eq, hd.card_inf_eq_card] at h1
    omega

theorem le_normalizer_W : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  intro s hs
  refine mem_normalizer_iff_conjSub_eq.mpr (hd.weaklyClosedIn_W s ?_)
  refine (conjSub_mono hd.hWS).trans fun x hx => ?_
  rw [mem_conjSub_iff] at hx
  have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
  rw [e]
  exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hx) ((S : Subgroup G).inv_mem hs)

theorem exists_normalizer_conj_eq {x g : G} (hx : x ∈ Subgroup.centralizer (W : Set G))
    (hgx : g * x * g⁻¹ ∈ Subgroup.centralizer (W : Set G)) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * x * n⁻¹ = g * x * g⁻¹ :=
  Sec7.control_centralizer_of_weaklyClosed (S.isPGroup'.to_le hd.hWS) hd.weaklyClosedIn_W hx hgx

end TightSylowDataTR

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem mem_centralizerModOdd_K {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxR : x ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) :
    x ∈ centralizerModOdd ⊤ K := by
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hd.hSN hxS
  refine ⟨Subgroup.mem_top x, hxN, mem_normalizer_oddCoreOf_of_mem_normalizer hxN,
    fun k hk => ?_⟩
  exact Sec6Gen.centSylow hd.tight.hypGen (CoreAssembly.mem_conjClass_self K) hd.isSylow2In_inf
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS))
    (fun y hy => mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr hxN) hy))
    (fun r hr v hv => Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hxR) hv) r hr)
    k hk x (Subgroup.mem_zpowers x)

theorem mem_centralizer_W {x : G} (hxS : x ∈ (S : Subgroup G)) (hxK : x ∈ centralizerModOdd ⊤ K)
    (hxL : x ∈ centralizerModOdd ⊤ L) : x ∈ Subgroup.centralizer (W : Set G) := by
  have hR := S19B.mem_centralizer_inf_of_mem S hxS hxK
  have hV := S19B.mem_centralizer_inf_of_mem S hxS hxL
  rw [hd.inf_member_eq] at hV
  have hle : W ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hd.sup_eq_inf_sup]
    refine sup_le (fun u hu => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hR u ⟨hd.hWS hu.2, hu.1⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hV v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem mem_sec19BPrime_iff {x : G} :
    x ∈ S19B.sec19BPrime K S W L ↔
      x ∈ (S : Subgroup G) ∧ x ∈ centralizerModOdd ⊤ K ∧ x ∈ centralizerModOdd ⊤ L := by
  constructor
  · rintro ⟨⟨⟨hxS, hxR⟩, -⟩, hxL⟩
    exact ⟨hxS, hd.mem_centralizerModOdd_K hxS hxR, hxL⟩
  · rintro ⟨hxS, hxK, hxL⟩
    exact ⟨⟨⟨hxS, S19B.mem_centralizer_inf_of_mem S hxS hxK⟩,
      hd.mem_centralizer_W hxS hxK hxL⟩, hxL⟩

theorem conjSub_mem_three {r : G} (hrt : IsUniqueInvolution (conjSub r L) (t * z)) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) {J : Subgroup G}
    (hJ : J = K ∨ J = L ∨ J = conjSub r L) :
    conjSub n J = K ∨ conjSub n J = L ∨ conjSub n J = conjSub r L := by
  have hI := hd.tight.isUniqueInvolution
  have hzW : z ∈ W := hd.mem_W_z
  have htW : t ∈ W := hd.mem_W
  have hcl : ConjInvariant (CoreAssembly.conjClass K) := hd.tight.hypGen.conjInvariant
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
  rcases hd.invol_mem_W hnuW hnu.sq hnu.ne_one with h | h | h
  · exact Or.inl (hd.tight.eq_of_isUniqueInvolution_member hmem
      (CoreAssembly.mem_conjClass_self K) hnu (h ▸ hI))
  · exact Or.inr (Or.inl (hd.tight.eq_of_isUniqueInvolution_member hmem hd.memL hnu
      (h ▸ hd.invL)))
  · exact Or.inr (Or.inr (hd.tight.eq_of_isUniqueInvolution_member hmem hL' hnu (h ▸ hrt)))

theorem mem_sec19BPrime_of_conj_mem {b g : G} (hb : b ∈ S19B.sec19BPrime K S W L)
    (hgS : g * b * g⁻¹ ∈ (S : Subgroup G))
    (hgW : g * b * g⁻¹ ∈ Subgroup.centralizer (W : Set G)) :
    g * b * g⁻¹ ∈ S19B.sec19BPrime K S W L := by
  obtain ⟨n, hn, hnb⟩ := hd.exists_normalizer_conj_eq hb.1.2 hgW
  obtain ⟨r, hr, hrt⟩ := hd.exists_conj_eq_mul
  have hrt' : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hd.invL.conj r
  have hbJ : ∀ J : Subgroup G, (J = K ∨ J = L ∨ J = conjSub r L) →
      b ∈ centralizerModOdd ⊤ J := by
    rintro J (rfl | rfl | rfl)
    · exact (hd.mem_sec19BPrime_iff.mp hb).2.1
    · exact hb.2
    · exact S19B.mem_centralizerModOdd_conj_of_mem hb hr
  have key : ∀ J : Subgroup G, (J = K ∨ J = L ∨ J = conjSub r L) →
      n * b * n⁻¹ ∈ centralizerModOdd ⊤ J := by
    intro J hJ
    have h1 := hd.conjSub_mem_three hrt' (Subgroup.inv_mem _ hn) hJ
    have h2 := S19B.conj_mem_centralizerModOdd_top (hbJ _ h1) n
    rwa [conjSub_conjSub_inv] at h2
  rw [← hnb] at hgS ⊢
  exact hd.mem_sec19BPrime_iff.mpr ⟨hgS, key K (Or.inl rfl), key L (Or.inr (Or.inl rfl))⟩

theorem inf_sec19BPrime_eq_bot : W ⊓ S19B.sec19BPrime K S W L = ⊥ := by
  obtain ⟨RL, hRL, hWRL, -, -⟩ := hd.exists_sylow_member
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxN : x ∈ Subgroup.normalizer (RL : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.1)
  have hxRL : x ∈ Subgroup.centralizer (RL : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (S1916.commute_of_mem_centralizerModOdd hx.2.2 hRL.1 hRL.2.1 hxN hy).symm
  have h := hd.inf_centralizer_inf_eq_bot hRL
  have hmem : x ∈ W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (RL : Set G) := ⟨⟨hx.1, hx.2.1.1.2⟩, hxRL⟩
  rw [h] at hmem
  exact hmem

theorem le_centralizer_W_of_mem_A :
    (S : Subgroup G) ⊓
        Subgroup.centralizer (((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤
      Subgroup.centralizer (W : Set G) := by
  rintro a ⟨haS, ha⟩
  have haR : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    S1911.mem_centralizer_inf_of_mem_A ha
  have hat : a ∈ Subgroup.centralizer ({t} : Set G) := S1911.mem_centralizer_t_of_mem_A ha
  obtain ⟨RL, hRL, w, hw, hc⟩ := hd.exists_mul_eq_of_mem_A haS haR hat
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (hd.le_centralizer_of_mem hd.mem_W).trans
      (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL)
  have hcS : a * w⁻¹ ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem haS ((S : Subgroup G).inv_mem (hd.hWS hw.1))
  have hcL : a * w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hat)
      (Subgroup.inv_mem _ (hWL hw.1))
  have hcR : a * w⁻¹ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ haR (Subgroup.inv_mem _ hw.2)
  have hcW : a * w⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
    hd.mem_centralizer_W hcS (hd.mem_centralizerModOdd_K hcS hcR)
      (hd.mem_centralizerModOdd_of_mem_centralizer hcS hcL hRL hc)
  have hwW : w ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hd.comm_of_mem x hx w hw.1
  have e : a = a * w⁻¹ * w := by group
  rw [e]
  exact Subgroup.mul_mem _ hcW hwW

end TightSylowDataTR


end BP

end CFSG.CGT.PushingUpLit.SolKNA.R4
