module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoNtwo
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreShape
public import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.SignalizerFunctor.Helpers

open scoped commutatorElement

@[expose] def W1V {X : Type} [Group X] (V U : Subgroup X) : Subgroup X :=
  ⨆ u ∈ U, ⨆ (_ : u ≠ 1), theta V u

section OddCore

variable {G : Type} [Group G] [Finite G]

private theorem odd_card_sup_of_le_normalizer' {H N : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

theorem inf_oddCoreOf_cen_le_oddCoreOf {b : G} (hb2 : b * b = 1) {R N₀ : Subgroup G}
    (hN₀R : N₀ ≤ R) (hRN : R ≤ normalizer (N₀ : Set G)) (hodd : Odd (Nat.card N₀))
    (hbN : b ∈ normalizer (N₀ : Set G)) (hbR : ∀ r ∈ R, ⁅b, r⁆ ∈ N₀) :
    oddCoreOf (centralizer ({b} : Set G)) ⊓ R ≤ oddCoreOf R := by
  set Q := oddCoreOf (centralizer ({b} : Set G)) with hQ
  set P := Q ⊓ R with hP
  have hPR : P ≤ R := inf_le_right
  have hPodd : Odd (Nat.card P) :=
    (odd_card_oddCoreOf (centralizer ({b} : Set G))).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have hNodd : Odd (Nat.card (P ⊔ N₀ : Subgroup G)) :=
    odd_card_sup_of_le_normalizer' (hPR.trans hRN) hPodd hodd
  have hNR : (P ⊔ N₀ : Subgroup G) ≤ R := sup_le hPR hN₀R
  have hb2' : b ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hb2
  have hnorm : R ≤ normalizer ((P ⊔ N₀ : Subgroup G) : Set G) := by
    intro r hr
    have hy : r⁻¹ * (b * r * b⁻¹) ∈ N₀ := by
      have e : r⁻¹ * (b * r * b⁻¹) = r⁻¹ * ⁅b, r⁆ * (r⁻¹)⁻¹ := by
        simp only [commutatorElement_def, inv_inv]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hRN (R.inv_mem hr)) _).1 (hbR r hr)
    obtain ⟨p, hp, hcen⟩ := exists_mul_mem_centralizer_of_fixes_coset hodd hb2' hbN hy
    have hkR : r * p ∈ R := R.mul_mem hr (hN₀R hp)
    have hkQ : r * p ∈ normalizer (Q : Set G) := le_normalizer_oddCoreOf _ hcen
    have hkP : r * p ∈ normalizer (P : Set G) :=
      mem_normalizer_inf hkQ (Subgroup.le_normalizer hkR)
    have hk : r * p ∈ normalizer ((P ⊔ N₀ : Subgroup G) : Set G) :=
      mem_normalizer_sup hkP (hRN hkR)
    have hpN : p ∈ normalizer ((P ⊔ N₀ : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_sup_right hp)
    have e : r = (r * p) * p⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hpN)
  exact le_sup_left.trans (le_oddCoreOf_of_normalized hNR hnorm hNodd)

theorem le_oddCoreOf_cen_of_decomp {c : G} {H N : Subgroup G}
    (hcen : centralizer ({c} : Set G) = H ⊔ oddCoreOf (centralizer ({c} : Set G)))
    (hHc : H ≤ centralizer ({c} : Set G)) (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G))
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf (centralizer ({c} : Set G)) := by
  set Oc := oddCoreOf (centralizer ({c} : Set G)) with hOc
  have hOcn : centralizer ({c} : Set G) ≤ normalizer (Oc : Set G) := le_normalizer_oddCoreOf _
  have hNc : N ≤ centralizer ({c} : Set G) := hNH.trans hHc
  have hoddsup : Odd (Nat.card (N ⊔ Oc : Subgroup G)) :=
    odd_card_sup_of_le_normalizer' (hNc.trans hOcn) hodd (odd_card_oddCoreOf _)
  have hle : (N ⊔ Oc : Subgroup G) ≤ centralizer ({c} : Set G) := sup_le hNc (oddCoreOf_le _)
  have hnorm : centralizer ({c} : Set G) ≤ normalizer ((N ⊔ Oc : Subgroup G) : Set G) := by
    rw [hcen]
    exact sup_le (fun w hw => mem_normalizer_sup (hHN hw) (hOcn (hHc hw)))
      (fun o ho => Subgroup.le_normalizer (Subgroup.mem_sup_right ho))
  exact le_sup_left.trans (le_oddCoreOf_of_normalized hle hnorm hoddsup)

theorem commutator_le_oddCoreOf_cen_of_decomp {b c : G} (hb2 : b * b = 1) (hbc : b * c = c * b)
    {V L H T : Subgroup G}
    (hcen : centralizer ({c} : Set G) = H ⊔ oddCoreOf (centralizer ({c} : Set G)))
    (hHc : H ≤ centralizer ({c} : Set G)) (hHL : H ≤ normalizer (L : Set G))
    (hVL : V ≤ L) (hVc : V ≤ centralizer ({c} : Set G))
    (hbL : ∀ l ∈ L, l ∈ centralizer ({c} : Set G) →
      ⁅b, l⁆ ∈ oddCoreOf (centralizer ({c} : Set G)))
    (hT : T ≤ oddCoreOf (centralizer ({b} : Set G)) ⊓ centralizer ({c} : Set G))
    (hTV : V ≤ normalizer (T : Set G)) :
    ⁅T, V⁆ ≤ oddCoreOf (centralizer ({c} : Set G)) := by
  set Oc := oddCoreOf (centralizer ({c} : Set G)) with hOc
  set Lc : Subgroup G := L ⊓ centralizer ({c} : Set G) with hLc
  set R : Subgroup G := Lc ⊔ Oc with hR
  have hOcn : centralizer ({c} : Set G) ≤ normalizer (Oc : Set G) := le_normalizer_oddCoreOf _
  have hLcn : Lc ≤ normalizer (Oc : Set G) := inf_le_right.trans hOcn
  have hRc : R ≤ centralizer ({c} : Set G) := sup_le inf_le_right (oddCoreOf_le _)
  have hRn : R ≤ normalizer (Oc : Set G) := hRc.trans hOcn
  have hOcR : Oc ≤ R := le_sup_right
  have hbc' : b ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2 hbc
  have hbN : b ∈ normalizer (Oc : Set G) := hOcn hbc'
  have hbR : ∀ r ∈ R, ⁅b, r⁆ ∈ Oc := by
    intro r hr
    obtain ⟨l, hl, o, ho, rfl⟩ := Sec5Two.exists_mul_of_mem_sup hLcn hr
    have e : ⁅b, l * o⁆ = ⁅b, l⁆ * (l * ⁅b, o⁆ * l⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine Oc.mul_mem (hbL l hl.1 hl.2) ?_
    have hbo : ⁅b, o⁆ ∈ Oc := by
      have e' : ⁅b, o⁆ = (b * o * b⁻¹) * o⁻¹ := by simp only [commutatorElement_def]
      rw [e']
      exact Oc.mul_mem ((Subgroup.mem_normalizer_iff.1 hbN o).1 ho) (Oc.inv_mem ho)
    exact (Subgroup.mem_normalizer_iff.1 (hLcn hl) _).1 hbo
  have hRnorm : centralizer ({c} : Set G) ≤ normalizer (R : Set G) := by
    have hH : H ≤ normalizer (R : Set G) := fun w hw =>
      mem_normalizer_sup (mem_normalizer_inf (hHL hw) (Subgroup.le_normalizer (hHc hw)))
        (hOcn (hHc hw))
    have hO : Oc ≤ normalizer (R : Set G) := fun o ho => Subgroup.le_normalizer (hOcR ho)
    rw [hcen]
    exact sup_le hH hO
  have hOR : oddCoreOf R ≤ Oc :=
    le_oddCoreOf_of_normalized ((oddCoreOf_le R).trans hRc)
      (fun g hg => mem_normalizer_oddCoreOf_of_mem_normalizer (hRnorm hg)) (odd_card_oddCoreOf R)
  have hTV1 : ⁅T, V⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro t ht u hu
    have htc : t ∈ centralizer ({c} : Set G) := (hT ht).2
    have htHO : t ∈ H ⊔ Oc := by rw [← hcen]; exact htc
    obtain ⟨w, hw, o, ho, rfl⟩ := Sec5Two.exists_mul_of_mem_sup (hHc.trans hOcn) htHO
    have hu' : u ∈ centralizer ({c} : Set G) := hVc hu
    have e : ⁅w * o, u⁆ = (w * ⁅o, u⁆ * w⁻¹) * ⁅w, u⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine R.mul_mem ?_ ?_
    · apply hOcR
      have h1 : ⁅o, u⁆ ∈ Oc := by
        have e' : ⁅o, u⁆ = o * (u * o⁻¹ * u⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e']
        exact Oc.mul_mem ho
          ((Subgroup.mem_normalizer_iff.1 (hOcn hu') o⁻¹).1 (Oc.inv_mem ho))
      exact (Subgroup.mem_normalizer_iff.1 (hOcn (hHc hw)) _).1 h1
    · apply (le_sup_left : Lc ≤ R)
      refine ⟨?_, ?_⟩
      · have e' : ⁅w, u⁆ = (w * u * w⁻¹) * u⁻¹ := by simp only [commutatorElement_def]
        rw [e']
        exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hHL hw) u).1 (hVL hu))
          (L.inv_mem (hVL hu))
      · exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHc hw) hu') (Subgroup.inv_mem _ (hHc hw)))
          (Subgroup.inv_mem _ hu')
  have hTb : ⁅T, V⁆ ≤ oddCoreOf (centralizer ({b} : Set G)) :=
    (commutator_le_of_normalizing T V hTV).trans (hT.trans inf_le_left)
  have hAL := inf_oddCoreOf_cen_le_oddCoreOf hb2 hOcR hRn (odd_card_oddCoreOf _) hbN hbR
  exact fun x hx => hOR (hAL ⟨hTb hx, hTV1 hx⟩)

end OddCore

section Theta

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

theorem theta_le_cen_of_le {b : G} (hVb : V ≤ centralizer ({b} : Set G)) :
    theta V b ≤ cen b := by
  have hS : ⁅oddCoreOf (cen b), V⁆ ≤ oddCoreOf (cen b) :=
    commutator_le_of_normalizing _ _ (fun x hx => le_normalizer_oddCoreOf (cen b) (hVb hx))
  exact sup_le (hS.trans (oddCoreOf_le _)) inf_le_right

theorem normalizer_theta_of_le {E : Subgroup G} {b : G} (hEb : E ≤ cen b)
    (hEV : E ≤ centralizer (V : Set G)) : E ≤ normalizer ((theta V b : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_sup
  · apply mem_normalizer_commutator
    · exact le_normalizer_oddCoreOf (cen b) (hEb hx)
    · exact centralizer_le_normalizer _ (hEV hx)
  · apply mem_normalizer_inf
    · exact le_normalizer_oddCoreOf _ (hEV hx)
    · exact Subgroup.le_normalizer (hEb hx)

theorem odd_card_theta_of_le {b : G} (hVb : V ≤ cen b) : Odd (Nat.card (theta V b)) := by
  set S := ⁅oddCoreOf (cen b), V⁆ with hSdef
  set N := oddCoreOf (centralizer (V : Set G)) ⊓ cen b with hNdef
  have hSX : S ≤ oddCoreOf (cen b) :=
    commutator_le_of_normalizing _ _ (fun x hx => le_normalizer_oddCoreOf (cen b) (hVb hx))
  have hodS : Odd (Nat.card S) :=
    (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le hSX)
  have hodN : Odd (Nat.card N) :=
    (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hwhole : ∀ e ∈ theta V b, ∃ s ∈ S, ∃ n ∈ N, s * n = e := fun e he =>
    (mem_sup_of_normalizing S N N_le_normalizer_S e).mp he
  have hcard := subgroup_product_cardinality_of_subgroup_whole (theta V b) S N le_sup_left
    le_sup_right hwhole
  have : Odd (Nat.card (theta V b) * Nat.card (S ⊓ N : Subgroup G)) := by
    rw [← hcard]
    exact hodS.mul hodN
  exact (Nat.odd_mul.mp this).1

theorem comm_theta_le_of_le {b : G} (hVb : V ≤ cen b) :
    ⁅theta V b, V⁆ ≤ ⁅oddCoreOf (cen b), V⁆ := by
  have hAS : V ≤ normalizer ((⁅oddCoreOf (cen b), V⁆ : Subgroup G) : Set G) :=
    normalized_commutator_normalized V _ (fun x hx => le_normalizer_oddCoreOf (cen b) (hVb hx))
  rw [commutator_le]
  intro g hg a ha
  obtain ⟨s, hs, n, hn, rfl⟩ := (mem_sup_of_normalizing _ _ N_le_normalizer_S g).mp hg
  have hna : n * a * n⁻¹ = a := by
    have hc : a * n = n * a := (mem_centralizer_iff.mp (oddCoreOf_le _ hn.1)) a ha
    rw [← hc]
    simp
  have key : ⁅s * n, a⁆ = ⁅s, a⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc s * n * a * (s * n)⁻¹ * a⁻¹ = s * (n * a * n⁻¹) * s⁻¹ * a⁻¹ := by group
      _ = s * a * s⁻¹ * a⁻¹ := by rw [hna]
  rw [key]
  have hle : ⁅⁅oddCoreOf (cen b), V⁆, V⁆ ≤ ⁅oddCoreOf (cen b), V⁆ :=
    commutator_le_of_normalizing _ _ hAS
  exact hle (Subgroup.commutator_mem_commutator hs ha)

theorem inf_theta_le_of_key (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV4 : 4 ≤ Nat.card V) {b : G}
    (hVb : V ≤ cen b)
    (hkey : ∀ a ∈ V, a ≠ 1 → ∀ T : Subgroup G, T ≤ oddCoreOf (cen b) ⊓ cen a →
      V ≤ normalizer (T : Set G) → ⁅T, V⁆ ≤ oddCoreOf (cen a)) :
    centralizer (V : Set G) ⊓ theta V b ≤ oddCoreOf (centralizer (V : Set G)) := by
  have hpA : IsPGroup 2 V := isPGroup_two_of_sq hV2
  set X := oddCoreOf (cen b) with hXdef
  have hAX : V ≤ normalizer (X : Set G) := fun x hx => le_normalizer_oddCoreOf (cen b) (hVb hx)
  have hXodd : Odd (Nat.card X) := odd_card_oddCoreOf _
  set S := ⁅X, V⁆ with hSdef
  have hSS : ⁅S, V⁆ = S :=
    coprime_normalized_commutator_idempotent 2 Nat.prime_two V X hpA hAX
      (Nat.coprime_two_left.mpr hXodd)
  have hAS : V ≤ normalizer (S : Set G) := normalized_commutator_normalized V X hAX
  have hSX : S ≤ X := commutator_le_of_normalizing X V hAX
  have hSodd : Odd (Nat.card S) := hXodd.of_dvd_nat (Subgroup.card_dvd_of_le hSX)
  have hSO : S ⊓ centralizer (V : Set G) ≤ oddCoreOf (centralizer (V : Set G)) := by
    rw [goldschmidt72_thm23 G V S hV2 hV4 hAS hSodd hSS]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    set T := S ⊓ cen a with hTdef
    have hAT : V ≤ normalizer (T : Set G) := fun x hx =>
      mem_normalizer_inf (hAS hx) (Subgroup.le_normalizer (mem_cen_of_mem hV2 ha hx))
    have hYa : ⁅T, V⁆ ≤ oddCoreOf (cen a) :=
      hkey a ha ha1 T (le_inf (inf_le_left.trans hSX) inf_le_right) hAT
    intro g hg
    exact cen_inf_oddCore_le ha ⟨hg.1, hYa hg.2⟩
  intro x hx
  obtain ⟨s, hs, n, hn, rfl⟩ :=
    (mem_sup_of_normalizing _ _ N_le_normalizer_S x).mp hx.2
  have hnC : n ∈ centralizer (V : Set G) := oddCoreOf_le _ hn.1
  have hsC : s ∈ centralizer (V : Set G) := by
    have := (centralizer (V : Set G)).mul_mem hx.1 ((centralizer (V : Set G)).inv_mem hnC)
    simpa using this
  exact (oddCoreOf (centralizer (V : Set G))).mul_mem (hSO ⟨hs, hsC⟩) hn.1

theorem theta_balance_of_key (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV4 : 4 ≤ Nat.card V) {b b' : G}
    (hVb : V ≤ cen b) (hVb' : V ≤ cen b')
    (hkeyV : ∀ a ∈ V, a ≠ 1 → ∀ T : Subgroup G, T ≤ oddCoreOf (cen b) ⊓ cen a →
      V ≤ normalizer (T : Set G) → ⁅T, V⁆ ≤ oddCoreOf (cen a))
    (hkeyB : ∀ T : Subgroup G, T ≤ oddCoreOf (cen b) ⊓ cen b' →
      V ≤ normalizer (T : Set G) → ⁅T, V⁆ ≤ oddCoreOf (cen b')) :
    theta V b ⊓ cen b' ≤ theta V b' := by
  have hpV : IsPGroup 2 V := isPGroup_two_of_sq hV2
  set J := theta V b ⊓ cen b' with hJ
  have hVJ : V ≤ normalizer (J : Set G) := fun x hx =>
    mem_normalizer_inf (normalizer_theta_of_le hVb (fun y hy => by
      rw [mem_centralizer_iff]
      intro v hv
      exact comm_of_sq_eq_one hV2 hv hy) hx) (Subgroup.le_normalizer (hVb' hx))
  have hJodd : Odd (Nat.card J) :=
    (odd_card_theta_of_le hVb).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hfact := coprime_normalized_commutator_factorization 2 Nat.prime_two V J hpV hVJ
    (Nat.coprime_two_left.mpr hJodd)
  have hcomm : ⁅J, V⁆ ≤ theta V b' := by
    set Y := ⁅J, V⁆ with hYdef
    have hYJ : Y ≤ J := commutator_le_of_normalizing J V hVJ
    have hYY : ⁅Y, V⁆ = Y :=
      coprime_normalized_commutator_idempotent 2 Nat.prime_two V J hpV hVJ
        (Nat.coprime_two_left.mpr hJodd)
    have hVX : V ≤ normalizer (oddCoreOf (cen b) : Set G) := fun x hx =>
      le_normalizer_oddCoreOf (cen b) (hVb hx)
    have hYS : Y ≤ ⁅oddCoreOf (cen b), V⁆ :=
      (Subgroup.commutator_mono_left inf_le_left).trans (comm_theta_le_of_le hVb)
    have hYX : Y ≤ oddCoreOf (cen b) := hYS.trans (commutator_le_of_normalizing _ _ hVX)
    have hYn : V ≤ normalizer (Y : Set G) := normalized_commutator_normalized V J hVJ
    have hY1 : Y ≤ oddCoreOf (cen b') :=
      calc Y = ⁅Y, V⁆ := hYY.symm
        _ ≤ oddCoreOf (cen b') := hkeyB Y (le_inf hYX (hYJ.trans inf_le_right)) hYn
    calc Y = ⁅Y, V⁆ := hYY.symm
      _ ≤ ⁅oddCoreOf (cen b'), V⁆ := Subgroup.commutator_mono_left hY1
      _ ≤ theta V b' := le_sup_left
  have hcen : J ⊓ centralizer (V : Set G) ≤ theta V b' := by
    intro x hx
    exact le_sup_right (a := ⁅oddCoreOf (cen b'), V⁆)
      (show x ∈ oddCoreOf (centralizer (V : Set G)) ⊓ cen b' from
        ⟨inf_theta_le_of_key hV2 hV4 hVb hkeyV ⟨hx.2, hx.1.1⟩, hx.1.2⟩)
  calc J = ⁅J, V⁆ ⊔ (J ⊓ centralizer (V : Set G)) := hfact.symm
    _ ≤ theta V b' := sup_le hcomm hcen

theorem W1V_odd_and_cen_le_of_balance {B : Subgroup G} (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hB8 : 8 ≤ Nat.card B) (hBV : B ≤ centralizer (V : Set G))
    (hbal : ∀ a ∈ B, a ≠ 1 → ∀ b ∈ B, b ≠ 1 → theta V a ⊓ cen b ≤ theta V b) :
    Odd (Nat.card (W1V V B)) ∧
      ∀ b ∈ B, b ≠ 1 → W1V V B ⊓ centralizer ({b} : Set G) ≤ theta V b := by
  have hVa : ∀ a ∈ B, V ≤ centralizer ({a} : Set G) := fun a ha v hv =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hBV ha) v hv)
  let _ : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun x y => Subtype.ext (comm_of_sq_eq_one hB2 x.2 y.2) }
  have hexp : ∀ a : B, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hB2 a a.2)
  have hodd : ∀ a : B, a ≠ 1 → Odd (Nat.card (theta V (a : G))) := fun a _ =>
    odd_card_theta_of_le (hVa a a.2)
  have key := CFSG.Milestones.sg_two_signalizer_completeness G B hexp hB8
    ((MulAut.conj : G →* MulAut G).comp B.subtype) (fun b => theta V (b : G))
    (fun a _ b => map_conj_eq_of_mem_normalizer
      (normalizer_theta_of_le (fun x hx => mem_cen_of_mem hB2 a.2 hx) hBV b.2))
    (fun a ha => CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hodd a ha))
    hodd
    (fun a _ g hg => by
      have hga : g ∈ cen (a : G) := theta_le_cen_of_le (hVa a a.2) hg
      have hc : (a : G) * g = g * a := (mem_centralizer_iff.mp hga) (a : G) rfl
      show (a : G) * g * (a : G)⁻¹ = g
      rw [hc]
      simp)
    (fun a b ha hb g hg hgb => by
      have ha' : (a : G) ≠ 1 := fun h1 => ha (Subtype.ext h1)
      have hb' : (b : G) ≠ 1 := fun h1 => hb (Subtype.ext h1)
      have hgb' : (b : G) * g * (b : G)⁻¹ = g := hgb
      have hcb : g ∈ cen (b : G) := by
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        calc (b : G) * g = (b : G) * g * (b : G)⁻¹ * (b : G) := by simp
          _ = g * (b : G) := by rw [hgb']
      exact hbal a a.2 ha' b b.2 hb' ⟨hg, hcb⟩)
  obtain ⟨-, -, hodd', hcomp⟩ := key
  have hW : W1V V B = ⨆ (a : B) (_ : a ≠ 1), theta V (a : G) := by
    apply le_antisymm
    · refine iSup₂_le fun u hu => iSup_le fun hu1 => ?_
      exact le_iSup₂_of_le ⟨u, hu⟩ (fun h => hu1 (congrArg Subtype.val h)) le_rfl
    · refine iSup₂_le fun a ha => ?_
      exact le_iSup₂_of_le (a : G) a.2 (le_iSup_of_le (fun h => ha (Subtype.ext h)) le_rfl)
  rw [hW]
  refine ⟨hodd', fun b hb hb1 g hg => ?_⟩
  have hb1' : (⟨b, hb⟩ : B) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  refine (hcomp ⟨b, hb⟩ hb1' g).mp ⟨hg.1, ?_⟩
  have hgb : b * g = g * b := (mem_centralizer_singleton_iff.mp hg.2).symm
  show b * g * b⁻¹ = g
  rw [hgb]
  simp

end Theta

namespace Sec5Two

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem eq_z_of_mem_comp_inf (h : Sec5Data X n z (zpowers z) S) {A A' : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A)
    (hA' : Sec5Comp X n (centralizer ({z} : Set X)) A') (hne : A ≠ A') {c : X} (hcA : c ∈ A)
    (hcA' : c ∈ A') (hc2 : orderOf c = 2) : c = z := by
  refine eq_z_of_mem_zStar h (comp_le_K0 hA) hA.2 ?_ hc2 (comp_le hA hcA)
  refine ⟨hcA, Subgroup.le_normalizer hcA, mem_normalizer_pPrimeCoreOf_of_mem hcA, fun k hk => ?_⟩
  rw [← inf_core_eq hA]
  refine ⟨?_, comm_mem_of_ne hA hA' hne k hk c hcA'⟩
  have e : ⁅k, c⁆ = k * c * k⁻¹ * c⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact A.mul_mem (A.mul_mem (A.mul_mem hk hcA) (A.inv_mem hk)) (A.inv_mem hcA)

theorem mem_normalizer_comp_of_mem_cen (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {c : X} (hcA : c ∈ A) (hc2 : orderOf c = 2)
    (hcz : c ≠ z) {y : X} (hyC : y ∈ centralizer ({z} : Set X))
    (hyc : y ∈ centralizer ({c} : Set X)) : y ∈ normalizer (A : Set X) := by
  have hA' := Sec5Comp.map_conj hA (Subgroup.le_normalizer hyC)
  by_cases heq : A.map (MulAut.conj y).toMonoidHom = A
  · exact mem_normalizer_of_map_conj_eq heq
  · exfalso
    refine hcz (eq_z_of_mem_comp_inf h hA hA' (Ne.symm heq) hcA ?_ hc2)
    refine ⟨c, hcA, ?_⟩
    have hcy : y * c = c * y := mem_centralizer_singleton_iff.1 hyc
    show y * c * y⁻¹ = c
    rw [hcy]
    group

theorem conj_mem_NA' {D A : Subgroup X} {y c : X} (hyD : y ∈ normalizer (D : Set X))
    (hyA : y ∈ normalizer (A : Set X)) (hc : c ∈ NA D A) : y * c * y⁻¹ ∈ NA D A := by
  obtain ⟨⟨hcA, hcO, hcom⟩, hcD⟩ := mem_NA.1 hc
  have hyO : y ∈ normalizer (pPrimeCoreOf 2 D : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hyD
  refine mem_NA.2 ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyA hcA) (Subgroup.inv_mem _ hyA)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyO hcO) (Subgroup.inv_mem _ hyO)
  · intro a ha
    have ha' : y⁻¹ * a * y ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyA) a).1 ha
      simpa using this
    have e : ⁅a, y * c * y⁻¹⁆ = y * ⁅y⁻¹ * a * y, c⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hyO _).1 (hcom _ ha')
  · exact (Subgroup.mem_normalizer_iff.1 hyD c).1 hcD

theorem mem_normalizer_NA {D A : Subgroup X} {y : X} (hyD : y ∈ normalizer (D : Set X))
    (hyA : y ∈ normalizer (A : Set X)) : y ∈ normalizer ((NA D A : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact conj_mem_NA' hyD hyA
  · intro hc
    have := conj_mem_NA' (Subgroup.inv_mem _ hyD) (Subgroup.inv_mem _ hyA) hc
    simpa [mul_assoc] using this

theorem K0_le_normalizer_NA {H A : Subgroup X} (hA : Sec5Comp X n H A) :
    K0 X n H ≤ normalizer ((NA (K0 X n H) A : Subgroup X) : Set X) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact NA_conj_mem hA hd hc
  · intro hc
    have := NA_conj_mem hA ((K0 X n H).inv_mem hd) hc
    simpa [mul_assoc] using this

theorem commutator_le_oddCoreOf_cen_of_decomp_K0 {b c : X} (hb2 : b * b = 1) (hbc : b * c = c * b)
    (hcen : centralizer ({c} : Set X) =
      oddCoreOf (centralizer ({c} : Set X)) ⊔
        (centralizer ({z} : Set X) ⊓ centralizer ({c} : Set X)))
    {V L T : Subgroup X}
    (hHL : ∀ w ∈ centralizer ({z} : Set X) ⊓ centralizer ({c} : Set X), w ∈ normalizer (L : Set X))
    (hVL : V ≤ L) (hVc : V ≤ centralizer ({c} : Set X))
    (hbL : ∀ l ∈ L, ⁅b, l⁆ ∈ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))))
    (hT : T ≤ oddCoreOf (centralizer ({b} : Set X)) ⊓ centralizer ({c} : Set X))
    (hTV : V ≤ normalizer (T : Set X)) :
    ⁅T, V⁆ ≤ oddCoreOf (centralizer ({c} : Set X)) := by
  set C := centralizer ({z} : Set X) with hC
  set D := K0 X n C with hD
  set H : Subgroup X := C ⊓ centralizer ({c} : Set X) with hH
  have hcen' : centralizer ({c} : Set X) = H ⊔ oddCoreOf (centralizer ({c} : Set X)) :=
    hcen.trans (sup_comm _ _)
  have hHc : H ≤ centralizer ({c} : Set X) := inf_le_right
  have hOD : pPrimeCoreOf 2 D ⊓ centralizer ({c} : Set X) ≤
      oddCoreOf (centralizer ({c} : Set X)) := by
    refine le_oddCoreOf_cen_of_decomp hcen' hHc ?_ ?_ ?_
    · exact le_inf ((inf_le_left.trans (oddCoreOf_le D)).trans (K0_le n C)) inf_le_right
    · intro w hw
      exact mem_normalizer_inf
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Sec5Data.le_normalizer_K0 X n C hw.1))
        (Subgroup.le_normalizer hw.2)
    · exact (odd_card_oddCoreOf D).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  refine commutator_le_oddCoreOf_cen_of_decomp hb2 hbc hcen' hHc (fun w hw => hHL w hw) hVL hVc ?_
    hT hTV
  intro l hl hlc
  refine hOD ⟨hbL l hl, ?_⟩
  have hbc' : b ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.2 hbc
  have e : ⁅b, l⁆ = b * l * b⁻¹ * l⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbc' hlc)
    (Subgroup.inv_mem _ hbc')) (Subgroup.inv_mem _ hlc)

end Sec5Two

section Sec5

open Sec5Two

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem keyBal (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V T : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hV : Open.IsElemAbelian 2 V) (hVA : V ≤ A₂)
    {b c : X} (hb : b ∈ A₁) (hb2 : orderOf b = 2) (hbV : b ∈ centralizer (V : Set X))
    (hc2 : orderOf c = 2) (hc : (c ∈ A₁ ∧ c ∈ centralizer (V : Set X)) ∨ c ∈ V)
    (hbc : b * c = c * b)
    (hT : T ≤ oddCoreOf (centralizer ({b} : Set X)) ⊓ centralizer ({c} : Set X))
    (hTV : V ≤ normalizer (T : Set X)) :
    ⁅T, V⁆ ≤ oddCoreOf (centralizer ({c} : Set X)) := by
  set C := centralizer ({z} : Set X) with hC
  set D := K0 X n C with hD
  have hb2' : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb2, pow_two] at this
  have hbC : b ∈ C := comp_le hA₁ hb
  have hVN₁ : V ≤ NA D A₁ := hVA.trans (comp_le_NA hA₁ hA₂ (Ne.symm h12))
  have hVcomm := (CoreAux.isElemAbelian_iff.mp hV).1
  by_cases hcz : c = z
  ·
    rw [hcz] at hT ⊢
    by_cases hbz : b = z
    · rw [hbz] at hT
      exact (commutator_le_of_normalizing T V hTV).trans (hT.trans inf_le_left)
    · set N₁ := NA D A₁ with hN₁
      have hbD : b ∈ D := comp_le_K0 hA₁ hb
      have hAL : oddCoreOf (centralizer ({b} : Set X)) ⊓ N₁ ≤ oddCoreOf N₁ :=
        inf_oddCoreOf_cen_le_oddCoreOf hb2' (core_le_NA hA₁)
          (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (NA_le hx))
          (odd_card_oddCoreOf D) (mem_normalizer_pPrimeCoreOf_of_mem hbD)
          (fun r hr => (mem_NA.1 hr).1.2.2 b hb)
      have hTV1 : ⁅T, V⁆ ≤ N₁ := by
        rw [Subgroup.commutator_le]
        intro t ht u hu
        have htb : t ∈ centralizer ({b} : Set X) := oddCoreOf_le _ (hT ht).1
        have htz : t ∈ C := (hT ht).2
        have htA : t ∈ normalizer (A₁ : Set X) :=
          mem_normalizer_comp_of_mem_cen h hA₁ hb hb2 hbz htz htb
        have htN : t ∈ normalizer (N₁ : Set X) :=
          mem_normalizer_NA (Sec5Data.le_normalizer_K0 X n C htz) htA
        have e : ⁅t, u⁆ = (t * u * t⁻¹) * u⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact N₁.mul_mem ((Subgroup.mem_normalizer_iff.1 htN u).1 (hVN₁ hu))
          (N₁.inv_mem (hVN₁ hu))
      have hOND : oddCoreOf N₁ ≤ pPrimeCoreOf 2 D :=
        le_oddCoreOf_of_normalized (H := D) ((oddCoreOf_le N₁).trans NA_le)
          (fun d hd => mem_normalizer_oddCoreOf_of_mem_normalizer (K0_le_normalizer_NA hA₁ hd))
          (odd_card_oddCoreOf N₁)
      have hODC : pPrimeCoreOf 2 D ≤ oddCoreOf C := (core_K0_eq (n := n) C).le.trans inf_le_right
      have hTb : ⁅T, V⁆ ≤ oddCoreOf (centralizer ({b} : Set X)) :=
        (commutator_le_of_normalizing T V hTV).trans (hT.trans inf_le_left)
      exact fun x hx => hODC (hOND (hAL ⟨hTb hx, hTV1 hx⟩))
  ·
    rcases hc with ⟨hcA₁, hcV⟩ | hcV
    ·
      have hcC : c ∈ C := comp_le hA₁ hcA₁
      have hVc : V ≤ centralizer ({c} : Set X) := fun v hv =>
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hcV v hv)
      have hcomm : ∀ a ∈ A₂, ⁅a, c⁆ ∈ oddCoreOf A₂ :=
        (normalizes_of_comm hA₂ (Subgroup.le_normalizer hcC) fun a ha =>
          comm_mem_of_ne hA₂ hA₁ (Ne.symm h12) a ha c hcA₁).2
      have hcen := cen_eq_oddCoreOf_sup_of_comm h hA₂ hc2 hcC hcomm
      refine commutator_le_oddCoreOf_cen_of_decomp_K0 hb2' hbc hcen (L := NA D A₁) ?_ hVN₁ hVc
        (fun l hl => (mem_NA.1 hl).1.2.2 b hb) hT hTV
      intro w hw
      exact mem_normalizer_NA (Sec5Data.le_normalizer_K0 X n C hw.1)
        (mem_normalizer_comp_of_mem_cen h hA₁ hcA₁ hc2 hcz hw.1 hw.2)
    ·
      have hcA₂ : c ∈ A₂ := hVA hcV
      have hcC : c ∈ C := comp_le hA₂ hcA₂
      have hVc : V ≤ centralizer ({c} : Set X) := fun v hv =>
        mem_centralizer_singleton_iff.2 (hVcomm v hv c hcV)
      have hbc' : b * c = c * b := (mem_centralizer_iff.1 hbV c hcV).symm
      have hcomm : ∀ a ∈ A₁, ⁅a, c⁆ ∈ oddCoreOf A₁ :=
        (normalizes_of_comm hA₁ (Subgroup.le_normalizer hcC) fun a ha =>
          comm_mem_of_ne hA₁ hA₂ h12 a ha c hcA₂).2
      have hcen := cen_eq_oddCoreOf_sup_of_comm h hA₁ hc2 hcC hcomm
      refine commutator_le_oddCoreOf_cen_of_decomp_K0 hb2' hbc' hcen (L := A₂) ?_ hVA hVc
        (fun l hl => comm_mem_of_ne hA₁ hA₂ h12 b hb l hl) hT hTV
      intro w hw
      exact mem_normalizer_comp_of_mem_cen h hA₂ hcA₂ hc2 hcz hw.1 hw.2

theorem thetaV_balance (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hV : Open.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) (hVA : V ≤ A₂) {b b' : X}
    (hb : b ∈ A₁) (hb2 : orderOf b = 2) (hbV : b ∈ centralizer (V : Set X))
    (hb' : b' ∈ A₁) (hb'2 : orderOf b' = 2) (hb'V : b' ∈ centralizer (V : Set X))
    (hbb' : b * b' = b' * b) :
    theta V b ⊓ centralizer ({b'} : Set X) ≤ theta V b' := by
  obtain ⟨-, hV2⟩ := CoreAux.isElemAbelian_iff.mp hV
  have hVa : ∀ {d : X}, d ∈ centralizer (V : Set X) → V ≤ centralizer ({d} : Set X) :=
    fun hd v hv => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hd v hv)
  refine theta_balance_of_key hV2 hV4.ge (hVa hbV) (hVa hb'V) ?_ ?_
  · intro a ha ha1 T hT hTV
    exact keyBal h hA₁ hA₂ h12 hV hVA hb hb2 hbV
      (CoreAux.orderOf_eq_two_of_isElemAbelian hV ha ha1) (Or.inr ha)
      (mem_centralizer_iff.1 hbV a ha).symm hT hTV
  · intro T hT hTV
    exact keyBal h hA₁ hA₂ h12 hV hVA hb hb2 hbV hb'2 (Or.inl ⟨hb', hb'V⟩) hbb' hT hTV

theorem thetaV_complete (h : Sec5Data X n z (zpowers z) S) {A₁ A₂ V B : Subgroup X}
    (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁)
    (hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) A₂) (h12 : A₁ ≠ A₂)
    (hV : Open.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) (hVA : V ≤ A₂)
    (hB : Open.IsElemAbelian 2 B) (hB8 : 8 ≤ Nat.card B) (hBA : B ≤ A₁)
    (hBV : B ≤ centralizer (V : Set X)) :
    Odd (Nat.card (W1V V B)) ∧
      ∀ b ∈ B, b ≠ 1 → W1V V B ⊓ centralizer ({b} : Set X) ≤ theta V b := by
  obtain ⟨hBcomm, hB2⟩ := CoreAux.isElemAbelian_iff.mp hB
  refine W1V_odd_and_cen_le_of_balance hB2 hB8 hBV ?_
  intro a ha ha1 b hb hb1
  exact thetaV_balance h hA₁ hA₂ h12 hV hV4 hVA (hBA ha)
    (CoreAux.orderOf_eq_two_of_isElemAbelian hB ha ha1) (hBV ha) (hBA hb)
    (CoreAux.orderOf_eq_two_of_isElemAbelian hB hb hb1) (hBV hb) (hBcomm a ha b hb)

end Sec5

end CFSG.OddStandard.Solomon75
