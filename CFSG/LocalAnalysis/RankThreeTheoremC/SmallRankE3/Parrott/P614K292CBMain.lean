module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292

namespace P614K292CB

section Groups

variable {X : Type} [Group X]

theorem exists_involution [Finite X] {T L : Subgroup X} (hT : IsPGroup 2 T)
    (hTL : T ⊓ L ≠ ⊥) : ∃ t : X, t ∈ T ⊓ L ∧ t ^ 2 = 1 ∧ t ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(T ⊓ L) := hT.to_inf_left
  have hdvd : 2 ∣ Nat.card ↥(T ⊓ L) :=
    hp.card_eq_or_dvd.resolve_left fun h1 => hTL (Subgroup.card_eq_one.1 h1)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨t, t.2, ?_, ?_⟩
  · rw [← ht, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  · intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem conj_mem_of_iff {E L H : Subgroup X}
    (hE : ∀ g, g ∈ E ↔ g ∈ L ∧ (∀ r ∈ H, g * r = r * g) ∧ g ^ 3 = 1) {a : X}
    (haL : a ∈ normalizer (L : Set X)) (haH : a ∈ normalizer (H : Set X)) {g : X}
    (hg : g ∈ E) : a * g * a⁻¹ ∈ E := by
  obtain ⟨hgL, hgH, hg3⟩ := (hE g).1 hg
  refine (hE _).2 ⟨(mem_normalizer_iff.1 haL g).1 hgL, fun r hr => ?_, ?_⟩
  · have hr' : a⁻¹ * r * a ∈ H := (mem_normalizer_iff''.1 haH r).1 hr
    have hc := hgH _ hr'
    calc a * g * a⁻¹ * r = a * (g * (a⁻¹ * r * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * r * a) * g) * a⁻¹ := by rw [hc]
      _ = r * (a * g * a⁻¹) := by group
  · rw [conj_pow, hg3, mul_one, mul_inv_cancel]

theorem mem_normalizer_of_iff {E L H : Subgroup X}
    (hE : ∀ g, g ∈ E ↔ g ∈ L ∧ (∀ r ∈ H, g * r = r * g) ∧ g ^ 3 = 1) {a : X}
    (haL : a ∈ normalizer (L : Set X)) (haH : a ∈ normalizer (H : Set X)) :
    a ∈ normalizer (E : Set X) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_of_iff hE haL haH, fun hg => ?_⟩
  have h := conj_mem_of_iff hE (inv_mem haL) (inv_mem haH) hg
  have e : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
  rwa [e] at h

end Groups

section Preimage

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

@[expose] def preIm (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (H : Subgroup X) :
    Subgroup (GL (Fin 3) K) :=
  (H.comap (L.subtype.comp ν)).map (slPi π 3 (p ^ f) K).subtype

theorem mem_preIm {H : Subgroup X} {r : GL (Fin 3) K} :
    r ∈ preIm ν H ↔
      ∃ s : ↥(slPi π 3 (p ^ f) K), ((ν s : ↥L) : X) ∈ H ∧ (s : GL (Fin 3) K) = r :=
  Iff.rfl

theorem preIm_le_slPi (H : Subgroup X) : preIm ν H ≤ slPi π 3 (p ^ f) K := by
  intro r hr
  obtain ⟨s, -, rfl⟩ := mem_preIm.1 hr
  exact s.2

theorem isPGroup_preIm (hinj : Function.Injective ν) {q : ℕ} {H : Subgroup X}
    (hH : IsPGroup q H) : IsPGroup q (preIm ν H) :=
  (hH.comap_of_injective _ fun _ _ h => hinj (Subtype.ext h)).map _

theorem preIm_ne_bot (hsurj : Function.Surjective ν) {H : Subgroup X} (hHL : H ≤ L)
    (hH : H ≠ ⊥) : preIm ν H ≠ ⊥ := by
  obtain ⟨h, hh, h1⟩ := (Subgroup.bot_or_exists_ne_one H).resolve_left hH
  obtain ⟨s, hs⟩ := hsurj ⟨h, hHL hh⟩
  have hsh : ((ν s : ↥L) : X) = h := congrArg Subtype.val hs
  intro hbot
  have hmem : (s : GL (Fin 3) K) ∈ preIm ν H := mem_preIm.2 ⟨s, by rw [hsh]; exact hh, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hs1 : s = 1 := Subtype.ext hmem
  rw [hs1, map_one] at hsh
  exact h1 hsh.symm

theorem preIm_closure_eq (hinj : Function.Injective ν) (hsurj : Function.Surjective ν)
    {A : Set X} (hAL : A ⊆ L) (hA2 : ∀ t ∈ A, t ^ 2 = 1) :
    preIm ν (closure A) = closure {r | r ∈ preIm ν (closure A) ∧ r ^ 2 = 1} := by
  set φ : ↥(slPi π 3 (p ^ f) K) →* X := L.subtype.comp ν with hφdef
  have hφ : Function.Injective φ := fun _ _ h => hinj (Subtype.ext h)
  have hrange : A ⊆ Set.range φ := by
    intro t ht
    obtain ⟨s, hs⟩ := hsurj ⟨t, hAL ht⟩
    exact ⟨s, congrArg Subtype.val hs⟩
  have hcomap : (closure A).comap φ = closure (φ ⁻¹' A) := by
    conv_lhs => rw [← Set.image_preimage_eq_of_subset hrange, ← MonoidHom.map_closure]
    exact Subgroup.comap_map_eq_self_of_injective hφ _
  refine le_antisymm ?_ ((closure_le _).2 fun r hr => hr.1)
  change ((closure A).comap φ).map (slPi π 3 (p ^ f) K).subtype ≤ _
  rw [hcomap, MonoidHom.map_closure]
  refine closure_mono ?_
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨mem_preIm.2 ⟨s, subset_closure hs, rfl⟩, ?_⟩
  have h1 : φ (s ^ 2) = φ 1 := by
    rw [map_pow, map_one]
    exact hA2 _ hs
  have h2 : s ^ 2 = 1 := hφ h1
  change (s : GL (Fin 3) K) ^ 2 = 1
  rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]

theorem conj_mem_preIm (M : LModel L π p f K ν) {g : X} {c : GL (Fin 3) K}
    (hg : IsLiftAt ν g c) {H : Subgroup X} (hgH : g ∈ normalizer (H : Set X))
    {r : GL (Fin 3) K} (hr : r ∈ preIm ν H) : c * r * c⁻¹ ∈ preIm ν H := by
  obtain ⟨s, hsH, rfl⟩ := mem_preIm.1 hr
  refine mem_preIm.2 ⟨M.conjBy hg.mem s, ?_, M.coe_conjBy hg.mem s⟩
  rw [← hg.act s (M.conjBy hg.mem s) (M.coe_conjBy hg.mem s)]
  exact (mem_normalizer_iff.1 hgH _).1 hsH

theorem mem_threeFrameIn_iff (hinj : Function.Injective ν) (hsurj : Function.Surjective ν)
    {y : GL (Fin 3) K} {v : Fin 3 → K} {H : Subgroup X} (hHL : H ≤ L)
    (hR : preIm ν H = twoFrame y v)
    (hd : ∀ g : GL (Fin 3) K, g ∈ threeFrame y v ↔
      g ∈ slPi π 3 (p ^ f) K ∧ (∀ r ∈ twoFrame y v, g * r = r * g) ∧ g ^ 3 = 1)
    (g : X) : g ∈ threeFrameIn ν y v ↔ g ∈ L ∧ (∀ r ∈ H, g * r = r * g) ∧ g ^ 3 = 1 := by
  rw [mem_threeFrameIn]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨-, hsc, hs3⟩ := (hd _).1 hs
    refine ⟨(ν s).2, fun r hr => ?_, ?_⟩
    · obtain ⟨s', hs'⟩ := hsurj ⟨r, hHL hr⟩
      have hs'r : ((ν s' : ↥L) : X) = r := congrArg Subtype.val hs'
      have hr' : (s' : GL (Fin 3) K) ∈ twoFrame y v := by
        rw [← hR]
        exact mem_preIm.2 ⟨s', by rw [hs'r]; exact hr, rfl⟩
      have hc : s * s' = s' * s := Subtype.ext (hsc _ hr')
      have h := congrArg (fun u => ((ν u : ↥L) : X)) hc
      simp only [map_mul, Subgroup.coe_mul, hs'r] at h
      exact h
    · have h3 : s ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hs3, Subgroup.coe_one])
      have h := congrArg (fun u => ((ν u : ↥L) : X)) h3
      simp only [map_pow, Subgroup.coe_pow, map_one, Subgroup.coe_one] at h
      exact h
  · rintro ⟨hgL, hgH, hg3⟩
    obtain ⟨s, hs⟩ := hsurj ⟨g, hgL⟩
    have hsg : ((ν s : ↥L) : X) = g := congrArg Subtype.val hs
    refine ⟨s, (hd _).2 ⟨s.2, fun r hr => ?_, ?_⟩, hsg⟩
    · rw [← hR] at hr
      obtain ⟨s', hs'H, rfl⟩ := mem_preIm.1 hr
      have h1 : ν (s * s') = ν (s' * s) := by
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul, hsg]
        exact hgH _ hs'H
      exact congrArg Subtype.val (hinj h1)
    · have h1 : ν (s ^ 3) = ν 1 := by
        apply Subtype.ext
        simp only [map_pow, Subgroup.coe_pow, hsg, hg3, map_one, Subgroup.coe_one]
      have h2 := congrArg Subtype.val (hinj h1)
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2

end Preimage

end P614K292CB

open P614K292CB
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (omegaOneTwo I292.mem_normalizer_omegaOneTwo)

theorem kD292CaseB3_holds : KD292CaseB3 := by
  intro h2 h5 X _ _ L x Px B π p f K _ ν y cfg S T hT hxT hTL
  haveI : L.Normal := cfg.setup.normal
  have M := S.model
  have hgen : {t : X | t ∈ T ⊓ L ∧ t ^ 2 = 1} ⊆ L := fun t ht => (mem_inf.1 ht.1).2
  have hRXL : omegaOneTwo T L ≤ L := (closure_le _).2 hgen
  have hRXT : omegaOneTwo T L ≤ T := (closure_le _).2 fun t ht => (mem_inf.1 ht.1).1
  have hRX1 : omegaOneTwo T L ≠ ⊥ := by
    obtain ⟨t, htTL, ht2, ht1⟩ := exists_involution hT hTL
    intro hbot
    have hmem : t ∈ omegaOneTwo T L :=
      Subgroup.mem_closure_of_mem (s := {t : X | t ∈ T ⊓ L ∧ t ^ 2 = 1}) ⟨htTL, ht2⟩
    rw [hbot, mem_bot] at hmem
    exact ht1 hmem
  have hRcl : preIm ν (omegaOneTwo T L) =
      closure {r | r ∈ preIm ν (omegaOneTwo T L) ∧ r ^ 2 = 1} :=
    preIm_closure_eq S.inj M.surj hgen fun t ht => ht.2
  have hRy : ∀ r ∈ preIm ν (omegaOneTwo T L), y * r * y⁻¹ ∈ preIm ν (omegaOneTwo T L) :=
    fun r hr => conj_mem_preIm M S.lift (I292.mem_normalizer_omegaOneTwo hxT) hr
  obtain ⟨h2K, v, hv, hRv, horth⟩ := h2 π p f K y M.piField M.modThree M.two_lt S.typeThree
    (preIm ν (omegaOneTwo T L)) (preIm_le_slPi _) (isPGroup_preIm S.inj (hT.to_le hRXT))
    (preIm_ne_bot M.surj hRXL hRX1) hRcl hRy
  obtain ⟨-, -, -, -, hd⟩ := h5 π p f K y M.piField M.modThree M.two_lt S.typeThree v hv horth
  have hE := mem_threeFrameIn_iff S.inj M.surj hRXL hRv (hd h2K)
  refine ⟨v, hv, horth, fun t ht => mem_normalizer_of_iff hE ?_ ?_⟩
  · rw [normalizer_eq_top L]
    exact mem_top t
  · exact I292.mem_normalizer_omegaOneTwo (le_normalizer ht)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
