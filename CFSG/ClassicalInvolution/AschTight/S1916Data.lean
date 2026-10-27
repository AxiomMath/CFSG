module

public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.AschTight.S1916Eta
public import CFSG.ClassicalInvolution.AschTight.S1916Omega2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem l6_2ModTmp_proved : L6_2ModTmp p f := l6_2 p f

omit [Finite G] in
theorem conjSub_centralizer (c x : G) :
    conjSub c (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({c * x * c⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub_iff, conj_mem_centralizer_iff]

theorem le_of_mem_USet_of_isUniqueInvolution (ht : S19R.TightStd p f K z) {V L : Subgroup G}
    {t : G} (hV : V ∈ USet (CoreAssembly.conjClass K)) (hL : L ∈ CoreAssembly.conjClass K)
    (htL : IsUniqueInvolution L t) (htV : t ∈ V) : V ≤ L := by
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hCK := (normalizer_eq_centralizer_of_tight ht.toTightBranch).ge
  obtain ⟨M, ⟨g, rfl⟩, hVM⟩ := exists_member_of_mem_USet' hV
  obtain ⟨g', hg'⟩ := hL
  change conjSub g' K = L at hg'
  subst hg'
  have h1 : t = g * z * g⁻¹ :=
    ((hzK.conj g).unique t (hVM htV) htL.sq).resolve_left htL.ne_one
  have h2 : t = g' * z * g'⁻¹ := htL.eq (hzK.conj g')
  have h3 : conjSub g K = conjSub g' K := conjSub_eq_of_conj_eq hCK (h1.symm.trans h2)
  rw [← h3]
  exact hVM

theorem exists_invariant_W [IsSimpleGroup G] (hd : Sec19Data p f K z S W) :
    ∃ W₀ : Subgroup G, Sec19Data p f K z S W₀ ∧ (∀ s ∈ (S : Subgroup G), conjSub s W₀ = W₀) ∧
      (∀ x ∈ W₀, ∀ y ∈ W₀, x * y = y * x) ∧
      ∃ η ∈ etaG (CoreAssembly.conjClass K), (∀ U ∈ η, U ≤ (S : Subgroup G)) ∧
        (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧ W₀ = ⨆ U ∈ η, U := by
  have hΩ := hypOmegaMod_of_tightD hd.tight
  obtain ⟨⟨η, hη, hinv⟩, h2⟩ :=
    l6_9_proved p f hd.tight.branch.odd hd.tight.branch.five G _ hΩ S
  have hηS : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU => (hη.1 hU).2
  set W₀ : Subgroup G := ⨆ U ∈ η, U with hW₀
  have hW₀S : W₀ ≤ (S : Subgroup G) := iSup₂_le hηS
  have hinvW : ∀ s ∈ (S : Subgroup G), conjSub s W₀ ≤ W₀ := by
    intro s hs
    rw [conjSub_le_iff]
    refine iSup₂_le fun U hU => ?_
    rw [← conjSub_le_iff]
    exact le_iSup₂ (f := fun V (_ : V ∈ η) => V) (conjSub s U) (hinv s hs U hU)
  refine ⟨W₀, { hd with hW := ⟨η, ⟨S, hη, hinv⟩, rfl⟩, hWS := hW₀S }, fun s hs => ?_,
    (h2 η hη hinv).1, η, ⟨S, hη, hinv⟩, hηS, hinv, rfl⟩
  refine le_antisymm (hinvW s hs) ?_
  have h := hinvW s⁻¹ ((S : Subgroup G).inv_mem hs)
  have h3 := (conjSub_le_iff s⁻¹).mp h
  rwa [inv_inv] at h3

theorem exists_good_data [IsSimpleGroup G] {W₀ : Subgroup G} (hd : Sec19Data p f K z S W₀)
    {η : Set (Subgroup G)} (hη : η ∈ etaG (CoreAssembly.conjClass K))
    (hηS : ∀ U ∈ η, U ≤ (S : Subgroup G)) (hW₀ : W₀ = ⨆ U ∈ η, U) :
    ∃ (L : Subgroup G) (t : G), Sec19DataT p f K z S W₀ L t (L ⊓ W₀) ∧
      ∃ Sig : Subgroup G, IsSylow2In Sig (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({t} : Set G)) ∧ Sig ≤ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.tight
  have hΩ := hypOmegaMod_of_tightD ht
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hCK := (normalizer_eq_centralizer_of_tight ht.toTightBranch).ge
  obtain ⟨L₀, hL₀, t₀, ht₀, ht₀z, V₀, hV₀, hV₀S, ht₀V₀⟩ :=
    exists_data_of_not_allTypeTwo l6_2ModTmp_proved ht hd.mu S hd.hSz
  set C := Subgroup.centralizer ({z} : Set G) with hC
  obtain ⟨Sig₀, hSig₀, -⟩ := IsSylow2In.exists_ge (P := C ⊓ Subgroup.centralizer ({t₀} : Set G))
    (T := ⊥) IsPGroup.of_bot bot_le
  obtain ⟨c, hcC, hcSig⟩ := exists_conj_le_of_sylow_le S hd.hSz (hSig₀.1.trans inf_le_left)
    hSig₀.2.1
  have hczc : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hcC
    calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [hcC]
      _ = z := by group
  set t := c * t₀ * c⁻¹ with htdef
  set L := conjSub c L₀ with hLdef
  have hL : L ∈ CoreAssembly.conjClass K := hΩ.conjInvariant c L₀ hL₀
  have htL : IsUniqueInvolution L t := ht₀.conj c
  have htz : t ≠ z := by
    intro h
    apply ht₀z
    calc t₀ = c⁻¹ * t * c := by rw [htdef]; group
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [h, hczc]
      _ = z := by group
  have hSig : IsSylow2In (conjSub c Sig₀) (C ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have h1 := hSig₀.conj c
    rwa [conjSub_inf, hC, conjSub_centralizer, conjSub_centralizer, hczc] at h1
  have hV₀L₀ : V₀ ≤ L₀ := le_of_mem_USet_of_isUniqueInvolution ht hV₀ hL₀ ht₀ ht₀V₀
  have hLt : L ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_isUniqueInvolution htL hx)
  have hLtN : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨g, hg⟩ := hL
    change conjSub g K = L at hg
    have e : t = g * z * g⁻¹ := htL.eq (hg ▸ hzK.conj g)
    rw [e, ← hg]
    exact centralizer_le_normalizer_conjSub hCK g
  have hH : IsSylow2In (conjSub c Sig₀ ⊓ (L ⊓ C)) (L ⊓ C) :=
    isSylow2In_inf_of_le_normalizer hSig (le_inf inf_le_right (inf_le_left.trans hLt))
      (fun x hx => mem_normalizer_inf (hLtN hx.2) (Subgroup.le_normalizer hx.1))
  have hV₀c : conjSub c V₀ ≤ L ⊓ C := by
    refine le_inf (conjSub_mono hV₀L₀) ?_
    have := conjSub_le_centralizer (c := c) (hV₀S.trans hd.hSz)
    rwa [hczc] at this
  have hV₀2 : IsPGroup 2 V₀ := HypOmegaMod.isPGroup_of_mem_USet ht.branch.odd hΩ hV₀
  have hV₀4 : 4 ≤ Nat.card V₀ := by
    obtain ⟨R, hR, hVR, -, hidx⟩ := hV₀
    have h8 := hΩ.eight_le_of_mem_RSet ht.branch.odd hR
    have h1 := Subgroup.relIndex_mul_card (H := V₀) (K := R)
    rw [hidx, inf_eq_left.mpr hVR] at h1
    omega
  have hle4 : 4 ≤ Nat.card ↥(conjSub c Sig₀ ⊓ (L ⊓ C)) := by
    have h1 := hH.natCard_le (isPGroup_conjSub c hV₀2) hV₀c
    rw [natCard_conjSub] at h1
    omega
  have hLS : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
    have h1 : conjSub c Sig₀ ⊓ (L ⊓ C) ≤ L ⊓ (S : Subgroup G) :=
      le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans hcSig)
    have := Subgroup.card_le_of_le h1
    omega
  have hVη : L ⊓ W₀ ∈ η := by
    rw [hW₀]
    exact l6_11_proved p f ht.branch.odd ht.branch.five G _ hΩ S η hη hηS L hL hLS
  obtain ⟨S', hη', -⟩ := hη
  have hVU : L ⊓ W₀ ∈ USet (CoreAssembly.conjClass K) := (hη'.1 hVη).1
  have hV2 : IsPGroup 2 ↥(L ⊓ W₀) := HypOmegaMod.isPGroup_of_mem_USet ht.branch.odd hΩ hVU
  have hV4 : 4 ≤ Nat.card ↥(L ⊓ W₀) := by
    obtain ⟨R, hR, hVR, -, hidx⟩ := hVU
    have h8 := hΩ.eight_le_of_mem_RSet ht.branch.odd hR
    have h1 := Subgroup.relIndex_mul_card (H := L ⊓ W₀) (K := R)
    rw [hidx, inf_eq_left.mpr hVR] at h1
    omega
  have htV : t ∈ L ⊓ W₀ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup htL inf_le_left hV2 (by omega)
  exact ⟨L, t, ⟨hd, hL, htL, htz, hVU, inf_le_right, htV⟩, conjSub c Sig₀, hSig, hcSig⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
