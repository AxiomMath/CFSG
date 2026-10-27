module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Asc77.AscSixEta

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conjSub_le_centralizer {z c : G} {A : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({z} : Set G)) :
    conjSub c A ≤ Subgroup.centralizer ({c * z * c⁻¹} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hA hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (c * z * c⁻¹) = c * ((c⁻¹ * x * c) * z) * c⁻¹ := by group
    _ = c * (z * (c⁻¹ * x * c)) * c⁻¹ := by rw [h1]
    _ = c * z * c⁻¹ * x := by group

theorem conjSub_gammaGen_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (c z : G) :
    conjSub c (gammaGen Ω z) ≤ gammaGen Ω (c * z * c⁻¹) := by
  rw [conjSub_le_iff]
  refine iSup₂_le fun A hA => ?_
  refine (conjSub_le_iff c).mp ?_
  have hmem : conjSub c A ∈ {A : Subgroup G | (A ∈ USet Ω ∨ A ∈ RSet Ω) ∧
      A ≤ Subgroup.centralizer ({c * z * c⁻¹} : Set G)} := by
    refine ⟨?_, conjSub_le_centralizer hA.2⟩
    rcases hA.1 with h | h
    · exact Or.inl (USet.conj hΩ h c)
    · exact Or.inr (RSet.conj hΩ h c)
  exact le_iSup₂ (f := fun B (_ : B ∈ {A : Subgroup G | (A ∈ USet Ω ∨ A ∈ RSet Ω) ∧
      A ≤ Subgroup.centralizer ({c * z * c⁻¹} : Set G)}) => B) (conjSub c A) hmem

theorem conjSub_gammaGen {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (c z : G) :
    conjSub c (gammaGen Ω z) = gammaGen Ω (c * z * c⁻¹) := by
  refine le_antisymm (conjSub_gammaGen_le hΩ c z) ?_
  have h := conjSub_gammaGen_le hΩ c⁻¹ (c * z * c⁻¹)
  rw [show c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z by group] at h
  have h2 := (conjSub_le_iff c⁻¹).mp h
  rwa [inv_inv] at h2

theorem gammaGen_le_centralizer (Ω : Set (Subgroup G)) (z : G) :
    gammaGen Ω z ≤ Subgroup.centralizer ({z} : Set G) :=
  iSup₂_le fun _ hA => hA.2

theorem conjSub_sec19X (K : Subgroup G) {z c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : conjSub c (sec19X K z) = sec19X K z := by
  rw [sec19X, conjSub_gammaGen (conjInvariant_conjClass K) c z]
  have h1 : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [hc]
      _ = z := by group
  rw [h1]

theorem sec19X_le_centralizer (K : Subgroup G) (z : G) :
    sec19X K z ≤ Subgroup.centralizer ({z} : Set G) :=
  gammaGen_le_centralizer _ z

theorem sec19Y_le_sec19X (K : Subgroup G) (z : G) : sec19Y K z ≤ sec19X K z :=
  fun _ hx => hx.1

theorem le_sec19X [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) : K ≤ sec19X K z := by
  refine le_of_forall_isSylow2In_of_isPerfect hz.perfect fun V hV => ?_
  have hVR : V ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hV
  have hVz : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans (isSubnormal_le hz.subnormal)
  have hmem : V ∈ {A : Subgroup G | (A ∈ USet (CoreAssembly.conjClass K) ∨
      A ∈ RSet (CoreAssembly.conjClass K)) ∧ A ≤ Subgroup.centralizer ({z} : Set G)} :=
    ⟨Or.inr hVR, hVz⟩
  exact le_iSup₂ (f := fun B (_ : B ∈ {A : Subgroup G | (A ∈ USet (CoreAssembly.conjClass K) ∨
      A ∈ RSet (CoreAssembly.conjClass K)) ∧ A ≤ Subgroup.centralizer ({z} : Set G)}) => B) V hmem

theorem conj_mem_sec19Y [Finite G] {K : Subgroup G} {z c x : G}
    (hcz : c ∈ Subgroup.centralizer ({z} : Set G)) (hcK : c ∈ Subgroup.normalizer (K : Set G))
    (hx : x ∈ sec19Y K z) : c * x * c⁻¹ ∈ sec19Y K z := by
  obtain ⟨hxX, hxN, hxO, hxc⟩ := hx
  have hcO := mem_normalizer_oddCoreOf_of_mem_normalizer hcK
  refine ⟨?_, ?_, ?_, fun l hl => ?_⟩
  · have := conj_mem_conjSub (n := c) hxX
    rwa [conjSub_sec19X K hcz] at this
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcK hxN) (Subgroup.inv_mem _ hcK)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcO hxO) (Subgroup.inv_mem _ hcO)
  · have hl' : c⁻¹ * l * c ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcK) l).mp hl
      rwa [inv_inv] at this
    have h1 := hxc _ hl'
    have h2 : c * ⁅x, c⁻¹ * l * c⁆ * c⁻¹ ∈ oddCoreOf K :=
      (Subgroup.mem_normalizer_iff.mp hcO _).mp h1
    have e : ⁅c * x * c⁻¹, l⁆ = c * ⁅x, c⁻¹ * l * c⁆ * c⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h2

theorem conjSub_sec19Y [Finite G] {K : Subgroup G} {z c : G}
    (hcz : c ∈ Subgroup.centralizer ({z} : Set G)) (hcK : c ∈ Subgroup.normalizer (K : Set G)) :
    conjSub c (sec19Y K z) = sec19Y K z := by
  refine mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx =>
    conj_mem_sec19Y hcz hcK hx, fun hx => ?_⟩)
  have := conj_mem_sec19Y (Subgroup.inv_mem _ hcz) (Subgroup.inv_mem _ hcK) hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this

theorem isSylow2In_of_le [Finite G] (S : Sylow 2 G) {C : Subgroup G}
    (hSC : (S : Subgroup G) ≤ C) : IsSylow2In (S : Subgroup G) C :=
  ⟨hSC, S.isPGroup', fun _ _ hV2 hle => S.is_maximal' hV2 hle⟩

@[expose] noncomputable def sylowOf {V C : Subgroup G} (h : IsSylow2In V C) : Sylow 2 ↥C where
  toSubgroup := V.subgroupOf C
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map C.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map C.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective C.subtype_injective Q, this]
    rfl

theorem coe_sylowOf {V C : Subgroup G} (h : IsSylow2In V C) :
    ((sylowOf h : Sylow 2 ↥C) : Subgroup ↥C) = V.subgroupOf C := rfl

theorem isSylow2In_inf_of_le_normalizer [Finite G] {V C H : Subgroup G} (hV : IsSylow2In V C)
    (hHC : H ≤ C) (hn : C ≤ Subgroup.normalizer (H : Set G)) : IsSylow2In (V ⊓ H) H := by
  refine ⟨inf_le_right, hV.2.1.to_le inf_le_left, ?_⟩
  intro T hTH hT2 hle
  obtain ⟨V', hV', hTV'⟩ := IsSylow2In.exists_ge hT2 (hTH.trans hHC)
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥C) (sylowOf hV) (sylowOf hV')
  rw [coe_sylowOf, coe_sylowOf] at hx
  have hVx : conjSub (x : G) V ≤ C := by
    have := conjSub_mono (n := (x : G)) hV.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have hV'eq : V' = conjSub (x : G) V := by
    have h1 : (conjSub (x : G) V).subgroupOf C = V'.subgroupOf C := by
      have e : (conjSub (x : G) V).subgroupOf C = conjSub x (V.subgroupOf C) := by
        ext y
        rw [Subgroup.mem_subgroupOf, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_subgroupOf]
        simp
      rw [e]
      exact hx
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hVx, inf_eq_left.mpr hV'.1, eq_comm] at h2
  have hxH : conjSub (x : G)⁻¹ H = H :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (H : Set G)).inv_mem (hn x.2))
  have hTV : conjSub (x : G)⁻¹ T ≤ V ⊓ H := by
    refine le_inf ?_ ?_
    · have := conjSub_mono (n := (x : G)⁻¹) (hTV'.trans hV'eq.le)
      rwa [conjSub_inv_conjSub] at this
    · have := conjSub_mono (n := (x : G)⁻¹) hTH
      rwa [hxH] at this
  have hcard : Nat.card T ≤ Nat.card ↥(V ⊓ H) := by
    have h1 : Nat.card ↥(conjSub (x : G)⁻¹ T) = Nat.card T :=
      (Nat.card_congr (Subgroup.equivMapOfInjective T (MulAut.conj (x : G)⁻¹).toMonoidHom
        (MulAut.conj (x : G)⁻¹).injective).toEquiv).symm
    rw [← h1]
    exact Subgroup.card_le_of_le hTV
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem isSylow2In_inf [Finite G] (S : Sylow 2 G) {C H : Subgroup G} (hSC : (S : Subgroup G) ≤ C)
    (hHC : H ≤ C) (hn : C ≤ Subgroup.normalizer (H : Set G)) :
    IsSylow2In ((S : Subgroup G) ⊓ H) H :=
  isSylow2In_inf_of_le_normalizer (isSylow2In_of_le S hSC) hHC hn

theorem inf_oddCoreOf_eq_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (L : Subgroup G) :
    P ⊓ oddCoreOf L = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) hx.2
    (hP.to_le (Subgroup.zpowers_le.mpr hx.1))

theorem commute_of_mem_centralizerModOdd [Finite G] {H L P : Subgroup G} {x : G}
    (hx : x ∈ centralizerModOdd H L) (hPL : P ≤ L) (hP : IsPGroup 2 P)
    (hxP : x ∈ Subgroup.normalizer (P : Set G)) {y : G} (hy : y ∈ P) : x * y = y * x := by
  have h1 : ⁅x, y⁆ ∈ oddCoreOf L := hx.2.2.2 y (hPL hy)
  have h2 : ⁅x, y⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp hxP y).mp hy) (P.inv_mem hy)
  have h3 : ⁅x, y⁆ ∈ P ⊓ oddCoreOf L := ⟨h2, h1⟩
  rw [inf_oddCoreOf_eq_bot hP L, Subgroup.mem_bot, commutatorElement_def] at h3
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

variable {p f : ℕ} [Fact p.Prime]

theorem commutator_mem_oddCoreOf_of_centralizes [Finite G] [IsSimpleGroup G] {K : Subgroup G}
    {z : G} (ht : S19R.TightStd p f K z) {R : Subgroup G} (hR : IsSylow2In R K) {x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hxR : ∀ r ∈ R, r * x = x * r) {k : G} (hk : k ∈ K) : ⁅x, k⁆ ∈ oddCoreOf K := by
  refine AscL62.centSylow ht.branch.odd ht.branch.five (hypOmegaMod_of_tightD ht)
    (CoreAssembly.mem_conjClass_self K) hR hx2 (fun y hy => ?_) (fun r hr v hv => ?_) k hk x
    (Subgroup.mem_zpowers x)
  · exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpowers_le.mpr hxN hy)
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute r x from hxR r hr) i).eq

theorem mem_sec19Y_of_centralizes [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (ht : S19R.TightStd p f K z) {R : Subgroup G} (hR : IsSylow2In R K) {x : G}
    (hxX : x ∈ sec19X K z) (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (hxR : ∀ r ∈ R, r * x = x * r) : x ∈ sec19Y K z := by
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight ht.toTightBranch]
    exact sec19X_le_centralizer K z hxX
  exact ⟨hxX, hxN, mem_normalizer_oddCoreOf_of_mem_normalizer hxN,
    fun k hk => commutator_mem_oddCoreOf_of_centralizes ht hR hx2 hxN hxR hk⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
