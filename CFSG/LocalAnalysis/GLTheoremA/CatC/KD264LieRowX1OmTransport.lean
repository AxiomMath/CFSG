module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

@[expose] def OmCoreShape (T : Type) [Group T] [Finite T] : Prop :=
  ∀ E : Subgroup T, IsElemAbelian 3 E →
    (∀ E' : Subgroup T, IsElemAbelian 3 E' → CFSG.Open.pRank 3 E' ≤ CFSG.Open.pRank 3 E) →
      ∃ F : Subgroup T, F ≤ E ∧ IsElemAbelian 3 F ∧
        min 2 (CFSG.Open.pRank 3 E - 1) ≤ CFSG.Open.pRank 3 F ∧
        ∃ L : Subgroup T, CFSG.Open.IsSubnormal L (Subgroup.centralizer (F : Set T)) ∧
          CFSG.Open.IsQuasisimple ↥L ∧ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)

section Generic

variable {G : Type*} [Group G]

theorem om_pRank_eq_of_card [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    CFSG.Open.pRank p E = k := by
  apply le_antisymm
  · apply CFSG.SectionRank.pRank_le hp.one_lt
    intro E' hE'le _
    have h1 : Nat.card E' ≤ Nat.card E := Subgroup.card_le_of_le hE'le
    rw [hk] at h1
    exact h1
  · exact CFSG.SectionRank.le_pRank hp.one_lt (le_refl E) hE hk

theorem om_exists_card_eq_pow [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    exact hE.2 g.1 g.2
  exact hP.exists_card_eq

theorem om_isElemAbelian_of_le {p : ℕ} {E E' : Subgroup G} (h : E' ≤ E)
    (hE : IsElemAbelian p E) : IsElemAbelian p E' := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hexp x (h hx)⟩
  have hc : a.1 * b.1 = b.1 * a.1 :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨a.1, h a.2⟩ : E) ⟨b.1, h b.2⟩)
  exact Subtype.ext hc

theorem om_isElemAbelian_of_map_injective {H : Type*} [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) {E : Subgroup G} (h : IsElemAbelian p (E.map f)) :
    IsElemAbelian p E := by
  obtain ⟨hcomm, hexp⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    have hc : f a.1 * f b.1 = f b.1 * f a.1 := by
      have := hcomm.is_comm.comm (⟨f a.1, Subgroup.mem_map_of_mem f a.2⟩ :
        ↥(E.map f)) ⟨f b.1, Subgroup.mem_map_of_mem f b.2⟩
      exact congrArg Subtype.val this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hc
  · apply hf
    rw [map_pow, map_one]
    exact hexp (f x) (Subgroup.mem_map_of_mem f hx)

theorem om_centralizer_map_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (F : Subgroup G) :
    (Subgroup.centralizer (F : Set G)).map (e : G →* H) =
      Subgroup.centralizer ((F.map (e : G →* H) : Subgroup H) : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have := hx z hz
    simp only [← map_mul, this]
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hy (e z) ⟨z, hz, rfl⟩
    apply e.injective
    simp only [map_mul]
    simpa using h1

theorem om_card_quotient_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (K : Subgroup A) :
    Nat.card (↥K ⧸ Subgroup.center ↥K) =
      Nat.card (↥(K.map (e : A →* B)) ⧸ Subgroup.center ↥(K.map (e : A →* B))) := by
  have hc := Subgroup.map_center_eq (MulEquiv.subgroupMap e K)
  exact Nat.card_congr (QuotientGroup.congr _ _ (MulEquiv.subgroupMap e K) hc).toEquiv

theorem om_mulAut_pow_apply {S : Type*} [Group S] (f : MulAut S) (n : ℕ) (x : S) :
    (f ^ n) x = (⇑f)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

end Generic

section Centre

theorem om_center_eq_bot_of_simple_not_prime {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (hnp : ¬ (Nat.card H).Prime) : Subgroup.center H = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center H) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative H := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center H := by
        rw [h]
        exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.1 ha) b).symm⟩⟩
    exact hnp ((Group.is_simple_iff_prime_card (α := H)).1 inferInstance)

theorem om_not_prime_card_of_two_le_pRank {H : Type*} [Group H] [Finite H]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H)) : ¬ (Nat.card H).Prime := by
  intro hpr
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup H)
  have h9 : 3 ^ 2 ∣ Nat.card E := by
    rw [hE]
    exact pow_dvd_pow 3 h
  have h9H : 3 ^ 2 ∣ Nat.card H := h9.trans (Subgroup.card_subgroup_dvd_card E)
  have h3 : 3 ∣ Nat.card H := dvd_trans (by norm_num) h9H
  have h3eq : 3 = Nat.card H := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3
  rw [← h3eq] at h9H
  norm_num at h9H

theorem om_center_eq_bot_of_simple_pRank {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H)) : Subgroup.center H = ⊥ :=
  om_center_eq_bot_of_simple_not_prime (om_not_prime_card_of_two_le_pRank h)

theorem om_charP_two_of_card_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 := by
  apply CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
  have h := addOrderOf_dvd_natCard (1 : K)
  rw [hK] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
  · rw [AddMonoid.addOrderOf_eq_one_iff] at h1
    exact absurd h1 one_ne_zero
  · have h2 := addOrderOf_nsmul_eq_zero (1 : K)
    rw [h1] at h2
    simpa using h2

end Centre

theorem good_of_core_transport {S T : Type} [Group S] [Finite S] [Group T] [Finite T]
    (ψ : S ≃* T) (hZS : Subgroup.center S = ⊥)
    (hinner : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AutThreePowInner S)
    (hcore : OmCoreShape T)
    (A : Subgroup (MulAut S)) (hA : IsElemAbelian 3 A)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ CFSG.Open.pRank 3 A) :
    ∃ F : Subgroup (MulAut S), F ≤ A ∧ IsElemAbelian 3 F ∧
      min 2 (CFSG.Open.pRank 3 A - 1) ≤ CFSG.Open.pRank 3 F ∧ IsGood 3 F := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hψinj : Function.Injective (ψ : S →* T) := ψ.injective
  have hψ'inj : Function.Injective (ψ.symm : T →* S) := ψ.symm.injective
  let ρ : S →* MulAut S := MulAut.conj
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hc : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut S => φ g) hs
      simp only [ρ, MulAut.conj_apply, MulAut.one_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hZS, Subgroup.mem_bot] at hc
    exact hc
  have hsurj : ∀ f ∈ A, ∃ s : S, ρ s = f := by
    intro f hf
    have hf3 : f ^ 3 = 1 := hA.2 f hf
    obtain ⟨a, ha⟩ := hinner f 1 (fun x => by
      have h1 := congrArg (fun φ : MulAut S => φ x) hf3
      simp only [MulAut.one_apply] at h1
      rw [om_mulAut_pow_apply] at h1
      exact h1)
    refine ⟨a, MulEquiv.ext fun x => ?_⟩
    show MulAut.conj a x = f x
    rw [MulAut.conj_apply]
    exact (ha x).symm
  let E : Subgroup S := A.comap ρ
  have hEmap : E.map ρ = A := by
    ext f
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_comap.1 hs
    · intro hf
      obtain ⟨s, rfl⟩ := hsurj f hf
      exact ⟨s, Subgroup.mem_comap.2 hf, rfl⟩
  have hEel : IsElemAbelian 3 E :=
    om_isElemAbelian_of_map_injective ρ hρinj (by rw [hEmap]; exact hA)
  have hEcard : Nat.card E = Nat.card A := by
    have h1 := Subgroup.card_map_of_injective (K := E) hρinj
    rw [hEmap] at h1
    exact h1.symm
  obtain ⟨kA, hkA⟩ := om_exists_card_eq_pow hp hA
  have hpA : CFSG.Open.pRank 3 A = kA := om_pRank_eq_of_card hp hA hkA
  let ET : Subgroup T := E.map (ψ : S →* T)
  have hETel : IsElemAbelian 3 ET := isElemAbelian_of_map 3 ψ hEel
  have hETcard : Nat.card ET = 3 ^ kA := by
    rw [Subgroup.card_map_of_injective hψinj, hEcard, hkA]
  have hpET : CFSG.Open.pRank 3 ET = kA := om_pRank_eq_of_card hp hETel hETcard
  have hTtop : CFSG.Open.pRank 3 (⊤ : Subgroup T) = CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt ψ).symm
  have hmax : ∀ E' : Subgroup T, IsElemAbelian 3 E' →
      CFSG.Open.pRank 3 E' ≤ CFSG.Open.pRank 3 ET := by
    intro E' _
    calc CFSG.Open.pRank 3 E'
        ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T) :=
          CFSG.SectionRank.pRank_mono hp.one_lt le_top
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup S) := hTtop
      _ ≤ CFSG.Open.pRank 3 A := hrank
      _ = kA := hpA
      _ = CFSG.Open.pRank 3 ET := hpET.symm
  obtain ⟨FT, hFTle, hFTel, hFTrank, LT, hLsub, hLq, hLdvd⟩ := hcore ET hETel hmax
  let FS : Subgroup S := FT.map (ψ.symm : T →* S)
  have hFS_le : FS ≤ E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hFTle hy)
    have h1 : ψ.symm y = z := by
      rw [← hzy]
      exact ψ.symm_apply_apply z
    show ψ.symm y ∈ E
    rw [h1]
    exact hz
  have hFS_card : Nat.card FS = Nat.card FT :=
    Subgroup.card_map_of_injective hψ'inj
  have hFA_le : FS.map (MulAut.conj : S →* MulAut S) ≤ A := by
    calc FS.map (MulAut.conj : S →* MulAut S)
        ≤ E.map (MulAut.conj : S →* MulAut S) := Subgroup.map_mono hFS_le
      _ = A := hEmap
  have hFA_el : IsElemAbelian 3 (FS.map (MulAut.conj : S →* MulAut S)) :=
    om_isElemAbelian_of_le hFA_le hA
  have hFA_card : Nat.card (FS.map (MulAut.conj : S →* MulAut S)) = Nat.card FT := by
    rw [Subgroup.card_map_of_injective hρinj, hFS_card]
  obtain ⟨j, hjFT⟩ := om_exists_card_eq_pow hp hFTel
  have hpFT : CFSG.Open.pRank 3 FT = j := om_pRank_eq_of_card hp hFTel hjFT
  have hFA_pRank : CFSG.Open.pRank 3 (FS.map (MulAut.conj : S →* MulAut S)) = j :=
    om_pRank_eq_of_card hp hFA_el (by rw [hFA_card, hjFT])
  have hLS_sub : CFSG.Open.IsSubnormal (LT.map (ψ.symm : T →* S))
      ((Subgroup.centralizer (FT : Set T)).map (ψ.symm : T →* S)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map ψ.symm hLsub
  rw [om_centralizer_map_mulEquiv ψ.symm FT, ← iInf_fixSubgroup_conj] at hLS_sub
  have hLS_q : CFSG.Open.IsQuasisimple ↥(LT.map (ψ.symm : T →* S)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupMap ψ.symm LT) hLq
  have hLS_d : 3 ∣ Nat.card (↥(LT.map (ψ.symm : T →* S)) ⧸
      Subgroup.center ↥(LT.map (ψ.symm : T →* S))) := by
    rw [← om_card_quotient_center_mulEquiv ψ.symm LT]
    exact hLdvd
  have hgood : IsGood 3 (FS.map (MulAut.conj : S →* MulAut S)) :=
    isGood_of_subnormal_quasisimple hp hLS_sub hLS_q hLS_d
  refine ⟨FS.map (MulAut.conj : S →* MulAut S), hFA_le, hFA_el, ?_, hgood⟩
  rw [hpA, hFA_pRank]
  have hrk : min 2 (kA - 1) ≤ CFSG.Open.pRank 3 FT := by
    rw [← hpET]
    exact hFTrank
  rw [hpFT] at hrk
  exact hrk

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
