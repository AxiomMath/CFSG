module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralizerSemiregular
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHModuleAut.BCHModuleAut
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.NormalCoprimeFixedControl.NormalCoprimeFixedControl

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ProofSupport

namespace PPartAnnihilation

open scoped commutatorElement

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHModuleAut

variable {G : Type} [Group G] [Finite G]

theorem comm_central {P : Subgroup G}
    (hcl : ⁅⁅P, P⁆, P⁆ = ⊥) (x y : P) : ⁅x, y⁆ ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : ((⁅x, y⁆ : P) : G) ∈ ⁅P, P⁆ := by
    have := Subgroup.commutator_mem_commutator x.2 y.2
    exact this
  have h2 : ⁅((⁅x, y⁆ : P) : G), (g : G)⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hcl]; exact Subgroup.commutator_mem_commutator h1 g.2
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  exact Subtype.ext h2.symm

theorem exp_sub {p : ℕ} {P : Subgroup G} (hexp : Monoid.exponent P = p) (x : P) : x ^ p = 1 := by
  rw [← hexp]; exact Monoid.pow_exponent_eq_one x

theorem actual_pPart_annihilation {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {A : Subgroup G} (hAB : A ≤ B)
    (Acard : Nat.card A = p) :
    ⁅P, ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), A⁆⁆ = ⊥ := by
  classical
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : p ≠ 2 := by
    have := h.oddPrimeClassTwoAction.setting.odd
    rintro rfl; exact absurd this (by decide)
  have hexp := h.oddPrimeClassTwoAction.setting.exponent
  have hcl := h.oddPrimeClassTwoAction.setting.class_le_two
  set O := CFSG.Open.pCoreOf 2 (B ⊔ T) with hO
  set N : Subgroup G := Subgroup.normalizer (P : Set G) with hN
  have hBT : B ⊔ T ≤ N := sup_le h.oddPrimeClassTwoAction.setting.normB h.oddPrimeClassTwoAction.setting.normT
  have hOle : O ≤ B ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hAle : A ≤ B ⊔ T := hAB.trans le_sup_left
  have hAnO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAle.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hAN : A ≤ N := hAle.trans hBT
  set R : Subgroup G := ⁅O, A⁆ with hR
  have hRO : R ≤ O := by
    refine Subgroup.commutator_le.2 fun o ho a ha => ?_
    have := (Subgroup.mem_normalizer_iff.1 (hAnO ha) o⁻¹).1 (O.inv_mem ho)
    have h2 := O.mul_mem ho this
    convert h2 using 1
    simp [commutatorElement_def, mul_assoc]
  have hRN : R ≤ N := hRO.trans (hOle.trans hBT)
  have hRX : R ≤ twoCoreCommutator T B := Subgroup.commutator_mono le_rfl hAB
  have hodd' : p ≠ 2 := hne
  have hexp' : ∀ x : P, x ^ p = 1 := exp_sub hexp
  have hc' : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P := comm_central hcl
  let tau : N →* (Lin p P hp hodd' hexp' hc' ≃ₗ[ZMod p] Lin p P hp hodd' hexp' hc') :=
    (linearizeAut hp hodd' hexp' hc').comp (Subgroup.normalizerMonoidHom P)
  have htau : ∀ (g : N) (w : Lin p P hp hodd' hexp' hc'),
      ((Lin.val hp hodd' hexp' hc' (tau g w) : P) : G) =
        (g : G) * ((Lin.val hp hodd' hexp' hc' w : P) : G) * (g : G)⁻¹ := fun g w => rfl
  have h9 := commutator_actorTwoCore_sup_actor_center_eq_bot h
  have hcent : twoCoreCommutator T B ⊔ B ≤ Subgroup.centralizer (centerP P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h9
  have hR2 : IsPGroup 2 R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ : IsPGroup 2 O).to_le hRO
  have hcop : Nat.Coprime (Nat.card (R.subgroupOf N)) p := by
    have h2 : IsPGroup 2 (R.subgroupOf N) := hR2.comap_subtype
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hne))
  have hDp : IsPGroup p (A.subgroupOf N) := by
    refine IsPGroup.of_card (n := 1) ?_
    have : Nat.card (A.subgroupOf N) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    rw [this, Acard, pow_one]
  have hnorm : ∀ d ∈ A.subgroupOf N, ∀ r ∈ R.subgroupOf N, d * r * d⁻¹ ∈ R.subgroupOf N := by
    intro d hd r hr
    rw [Subgroup.mem_subgroupOf] at hd hr ⊢
    have hmap : R.map (MulAut.conj (d : G)).toMonoidHom ≤ R := by
      rw [hR, Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (hAnO hd) x).1 hx
      · rintro _ ⟨x, hx, rfl⟩
        exact A.mul_mem (A.mul_mem hd hx) (A.inv_mem hd)
    exact hmap ⟨r, hr, rfl⟩
  have hfix : ∀ w : Lin p P hp hodd' hexp' hc', (∀ d : A.subgroupOf N, tau d w = w) →
      ∀ r : R.subgroupOf N, tau r w = w := by
    intro w hw r
    have hA1 : A ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at Acard
      exact hp.one_lt.ne Acard
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
    set x : P := Lin.val hp hodd' hexp' hc' w with hx
    have h1 := hw ⟨⟨a, hAN a.2⟩, a.2⟩
    have h2 := congrArg (fun w => ((Lin.val hp hodd' hexp' hc' w : P) : G)) h1
    rw [htau] at h2
    have hxc : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have : (a : G) * (x : G) * (a : G)⁻¹ = x := h2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hxZ : (x : G) ∈ centerP P := by
      rw [← centralizer_nonidentity_actor_eq_center h (a : G) (hAB a.2) (fun h0 => ha1 (Subtype.ext h0))]
      exact ⟨x.2, hxc⟩
    have hrR : ((r : N) : G) ∈ R := r.2
    have hrc := Subgroup.mem_centralizer_iff.1 (hcent (Subgroup.mem_sup_left (hRX hrR)))
      (x : G) hxZ
    apply Lin.val_injective hp hodd' hexp' hc'
    apply Subtype.ext
    rw [htau]
    have : (x : G) * ((r : N) : G) = ((r : N) : G) * (x : G) := hrc
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  haveI : Finite (Lin p P hp hodd' hexp' hc') :=
    Finite.of_injective (Lin.val hp hodd' hexp' hc') (Lin.val_injective hp hodd' hexp' hc')
  have key := NormalCoprimeFixedControl.fixed_of_normalizing_pGroup_fixed tau
    (R.subgroupOf N) (A.subgroupOf N) hnorm hcop hDp hfix
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h1 := key ⟨r, hRN hr⟩ hr (Lin.mk hp hodd' hexp' hc' ⟨x, hx⟩)
  have h2 := congrArg (fun w => ((Lin.val hp hodd' hexp' hc' w : P) : G)) h1
  rw [htau] at h2
  have h3 : r * x * r⁻¹ = x := h2
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

end PPartAnnihilation
end ProofSupport
end CFSG.LocalAnalysis.RankThreeUC
