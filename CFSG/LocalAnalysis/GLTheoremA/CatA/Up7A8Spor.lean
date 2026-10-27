module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.GLTheoremA.AltDown

@[expose] def SporAltNoComp (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → IsAltPType 3 J m → False

@[expose] def I1415SevenSporS : Prop := SporAltNoComp 7

theorem up7a8_exists_conjAut {Q : Type} [Group Q] {K : Subgroup Q} {y : Q}
    (hyN : y ∈ Subgroup.normalizer (K : Set Q)) {n : ℕ} (hy : y ^ n = 1) :
    ∃ β : MulAut ↥K, β ^ n = 1 ∧
      fixSubgroup β = (K ⊓ Subgroup.centralizer ({y} : Set Q)).subgroupOf K := by
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut ↥K, β = Subgroup.normalizerMonoidHom K ⟨y, hyN⟩ :=
    ⟨_, rfl⟩
  have hβapp : ∀ k : ↥K, ((β k : ↥K) : Q) = y * (k : Q) * y⁻¹ := by
    intro k
    rw [hβdef]
    rfl
  refine ⟨β, ?_, ?_⟩
  · have h3 : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set Q)) ^ n = 1 := Subtype.ext hy
    rw [hβdef, ← map_pow, h3, map_one]
  · ext k
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : ((β k : ↥K) : Q) = (k : Q) := congrArg Subtype.val hk
      rw [hβapp] at h1
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [hβapp]
      exact mul_inv_eq_iff_eq_mul.2 hk.symm

theorem up7a8_central_inj {T : Type} [Group T] [Finite T] {H : Subgroup T} {m : ℕ} (hm : 5 ≤ m)
    (e : PQuot 3 H ≃* alternatingGroup (Fin m)) (hT : CFSG.pPrimeCore 3 T = ⊥) {x : T} (hxH : x ∈ H)
    (hxZ : x ∈ Subgroup.center T) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (PQuot 3 H) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have h1 : e q ∈ Subgroup.center (alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff] at hq ⊢
      intro g
      obtain ⟨u, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hq u]
    have hcA : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    rw [hcA, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  set w : ↥H := ⟨x, hxH⟩ with hw
  have hwc : (QuotientGroup.mk w : PQuot 3 H) ∈ Subgroup.center (PQuot 3 H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    have hu := Subgroup.mem_center_iff.1 hxZ (u : T)
    simp only [Subgroup.coe_mul, hw]
    exact hu
  have hw1 : (QuotientGroup.mk w : PQuot 3 H) = 1 := by
    rw [hZ, Subgroup.mem_bot] at hwc
    exact hwc
  have hwO : w ∈ GLAPPrimeCore 3 ↥H := QuotientGroup.eq_one_iff _ |>.1 hw1
  have hcop1 : Nat.Coprime 3 (orderOf w) := by
    have hle : Subgroup.zpowers w ≤ GLAPPrimeCore 3 ↥H := Subgroup.zpowers_le.2 hwO
    have hd := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers] at hd
    exact Nat.Coprime.coprime_dvd_left (dvd_refl 3) (Nat.Coprime.coprime_dvd_right hd
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)))
  have hxo : orderOf x = orderOf w := Subgroup.orderOf_coe w
  have hNnorm : (Subgroup.zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute g x := Subgroup.mem_center_iff.1 hxZ g
    have hgx : g * x ^ j * g⁻¹ = x ^ j := by
      rw [(hcomm.zpow_right j).eq, mul_inv_cancel_right]
    rw [hgx]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
  have hNcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hxo]
    exact hcop1
  have hNle : Subgroup.zpowers x ≤ CFSG.pPrimeCore 3 T := by
    unfold CFSG.pPrimeCore
    exact le_sSup ⟨hNnorm, hNcop⟩
  rw [hT, le_bot_iff] at hNle
  have hx1 : x ∈ (⊥ : Subgroup T) := hNle ▸ Subgroup.mem_zpowers x
  exact Subgroup.mem_bot.1 hx1

theorem up7a8_pQuot_map_equiv {T S : Type} [Group T] [Group S] [Finite T] [Finite S] (p : ℕ) [Fact p.Prime]
    (H : Subgroup T) (f : T →* S) (hf : ∀ x : T, x ∈ H → f x = 1 → x = 1) :
    Nonempty (PQuot p H ≃* PQuot p (H.map f)) := by
  let g : ↥H →* ↥(H.map f) := (f.comp H.subtype).codRestrict (H.map f)
    (fun h => Subgroup.mem_map.2 ⟨h.1, h.2, rfl⟩)
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfa : f a = 1 := by
      have := congrArg Subtype.val ha
      simpa [g] using this
    exact Subtype.ext (hf a a.2 hfa)
  have hgsurj : Function.Surjective g := by
    intro b
    obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.1 b.2
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  have hker : g.ker = ⊥ := (MonoidHom.ker_eq_bot_iff g).2 hginj
  let ψ : ↥H ≃* ↥(H.map f) := MulEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hcop : Nat.Coprime p (Nat.card g.ker) := by
    rw [hker, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hmap := CFSG.Semidihedral.Local.pPrimeCore_map_eq_of_coprime_ker p g hgsurj hcop
  have hcore : (GLAPPrimeCore p ↥H).map ψ.toMonoidHom = GLAPPrimeCore p ↥(H.map f) := hmap
  exact ⟨QuotientGroup.congr (GLAPPrimeCore p ↥H) (GLAPPrimeCore p ↥(H.map f)) ψ hcore⟩

end CFSG.LocalAnalysis.GLTheoremA
