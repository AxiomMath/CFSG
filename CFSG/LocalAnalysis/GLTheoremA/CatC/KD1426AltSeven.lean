module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Common
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Klein7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Lift

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD1426Common

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltSeven

variable {Y : Type} [Group Y] [Finite Y]

theorem card_le_nine {H : Subgroup (alternatingGroup (Fin 7))} (hH : ∀ g ∈ H, g ^ 3 = 1) :
    Nat.card H ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 H := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hH g.1 g.2⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
  have hdvd : Nat.card H ∣ Nat.card (alternatingGroup (Fin 7)) := Subgroup.card_subgroup_dvd_card H
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [hm, hA7] at hdvd
  have hm2 : m ≤ 2 := by
    by_contra h
    push_neg at h
    have h27 : 3 ^ 3 ∣ 3 ^ m := pow_dvd_pow 3 h
    have := dvd_trans h27 hdvd
    norm_num at this
  rw [hm]
  calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 9 := by norm_num

theorem card_three_pow {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : ∀ g ∈ H, g ^ 3 = 1) :
    ∃ m : ℕ, Nat.card H = 3 ^ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 H := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hH g.1 g.2⟩
  exact IsPGroup.iff_card.1 hp

theorem alt7_core (K B : Subgroup Y) (hK : K.Normal) (hq : CFSG.Open.IsQuasisimple ↥K)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7))
    (hcore : GLAPPrimeCore 3 ↥K = ⊥) (hB : IsElemAbelian 3 B) (hKB : K ⊔ B = ⊤)
    (hcard : 3 ^ 4 ≤ Nat.card B)
    (hH : ∀ E : Subgroup Y, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) = ⊥) :
    Nat.card B = 3 ^ 4 ∧ ∃ A T : Subgroup Y, A ≤ B ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ∧
      catalogIs (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)))) k3NoA10 ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer
          ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) : Subgroup Y) : Set Y) ↔ b ∈ A) ∧
      T ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) ∧ IsElemAbelian 2 T ∧
      Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧ ⁅B, T⁆ = T ∧
      GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) = ⊥ := by
  classical
  have hn : 5 ≤ 7 := by norm_num
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  have hlayer : GLAPLayer 3 K = K := KD1426Common.glaPLayer_eq_self hq hcore
  have hcompK : GLAPComponent 3 K K := KD1426Common.glaPComponent_self hq hcore
  set ψ : B →* alternatingGroup (Fin 7) := KD1426Psi.psiB K hK eK hn B hB3 with hψ
  set π : ↥K →* alternatingGroup (Fin 7) := KD1426Psi.piK K eK with hπ
  set B0 : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hB0
  have hkerB : ∀ b : B, ψ b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y) := by
    intro b
    rw [hψ, KD1426Psi.psiB_apply]
    exact KD1426Psi.psiFun_eq_one_iff K hK eK hn hq _ _
  have hkermap : ψ.ker.map B.subtype = B0 := by
    ext y
    constructor
    · intro hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
      rw [MonoidHom.mem_ker, hkerB] at hb
      exact Subgroup.mem_inf.2 ⟨b.2, hb⟩
    · intro hy
      rw [hB0, Subgroup.mem_inf] at hy
      refine Subgroup.mem_map.2 ⟨⟨y, hy.1⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hkerB]
      exact hy.2
  have hcardker : Nat.card ψ.ker = Nat.card B0 := by
    rw [← hkermap, Subgroup.card_map_of_injective B.subtype_injective]
  have hmulB : Nat.card B0 * Nat.card ψ.range = Nat.card B := by
    rw [← hcardker]
    exact Subgroup.card_ker_mul_card_range ψ
  have hR9 : Nat.card ψ.range ≤ 9 := by
    apply card_le_nine
    intro g hg
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hg
    rw [← map_pow]
    have hb : b ^ 3 = 1 := Subtype.ext (by simpa using hB3 b.1 b.2)
    rw [hb, map_one]
  have hB0le : Nat.card B0 ≤ 9 := by
    by_contra hlt
    push_neg at hlt
    have hB0el : ∀ g ∈ B0, g ^ 3 = 1 := fun g hg => hB3 g (Subgroup.mem_inf.1 hg).1
    obtain ⟨m, hm⟩ := card_three_pow hB0el
    have hm3 : 3 ≤ m := by
      by_contra h
      push_neg at h
      interval_cases m <;> simp_all
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E0, hE0⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3)
      (by rw [hm]; exact pow_dvd_pow 3 hm3)
    set E : Subgroup Y := E0.map B0.subtype with hEdef
    have hEB0 : E ≤ B0 := by
      intro y hy
      obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hy
      exact e.2
    have hEB : E ≤ B := hEB0.trans inf_le_left
    have hEcard : Nat.card E = 3 ^ 3 := by
      rw [hEdef, Subgroup.card_map_of_injective B0.subtype_injective, hE0]
    have hEel : IsElemAbelian 3 E := isElemAbelian_of_le hEB hB
    have hEC : ∀ e ∈ E, e ∈ Subgroup.centralizer (K : Set Y) := fun e he =>
      (Subgroup.mem_inf.1 (hEB0 he)).2
    have hKE : K ⊓ Subgroup.centralizer (E : Set Y) = K := by
      apply inf_eq_left.2
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.1 (hEC e he) k hk).symm
    have h1 := hH E hEB hEel hEcard
    rw [hKE, hlayer] at h1
    have hKbot : K = ⊥ := h1
    have hnt := isQuasisimple_nontrivial hq
    exact not_nontrivial_iff_subsingleton.2 (by rw [hKbot]; exact inferInstance) hnt
  have hc81 : 81 ≤ Nat.card B := by norm_num at hcard; exact hcard
  have hB0ge : 9 ≤ Nat.card B0 := by
    by_contra hlt
    push_neg at hlt
    have h8 : Nat.card B0 ≤ 8 := by omega
    have := Nat.mul_le_mul h8 hR9
    omega
  have hB0eq : Nat.card B0 = 9 := le_antisymm hB0le hB0ge
  have hReq : Nat.card ψ.range = 9 := by
    rw [hB0eq] at hmulB
    omega
  have hBcard : Nat.card B = 3 ^ 4 := by
    rw [← hmulB, hB0eq, hReq]
    norm_num
  have hA_le : B0 ≤ B := inf_le_left
  have hA_el : IsElemAbelian 3 B0 := isElemAbelian_of_le hA_le hB
  have hA_card : Nat.card B0 = 9 := hB0eq
  have hAC : ∀ a ∈ B0, a ∈ Subgroup.centralizer (K : Set Y) := fun a ha =>
    (Subgroup.mem_inf.1 ha).2
  have hKA : K ⊓ Subgroup.centralizer (B0 : Set Y) = K := by
    apply inf_eq_left.2
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (hAC a ha) k hk).symm
  have hDel : IsElemAbelian 3 ψ.range := isElemAbelian_range hB ψ
  obtain ⟨T0, hT0el, hT0card, hT0norm, hT0cov⟩ := KD1426Klein.klein7 ψ.range hDel hReq
  obtain ⟨TK, hTKcard, hTKbot, hsup⟩ := KD1426Lift.exists_lift hK hq hcore eK T0 hT0card
  set Z : Subgroup ↥K := Subgroup.center ↥K with hZ
  have hZc : Nat.card Z = 1 ∨ Nat.card Z = 3 :=
    KD1426Lift.card_center_dvd_three hK hq hcore (by norm_num) rfl eK
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    rcases hZc with h | h
    · have hbot : Z = ⊥ := Subgroup.eq_bot_of_card_eq _ h
      rw [hbot, Subgroup.mem_bot] at hz
      rw [hz, one_pow]
    · have hd := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
      rw [h] at hd
      have := orderOf_dvd_iff_pow_eq_one.1 hd
      simpa using congrArg Subtype.val this
  have hTKQ : ∀ t ∈ TK, π t ∈ T0 := by
    intro t ht
    have hmem : t ∈ TK ⊔ Z := Subgroup.mem_sup_left ht
    rw [hsup] at hmem
    exact Subgroup.mem_comap.1 hmem
  have hTKinj : ∀ t ∈ TK, π t = 1 → t = 1 := by
    intro t ht h1
    have hZt : t ∈ Z := (KD1426Psi.piK_eq_one_iff K eK t).1 h1
    have hbot : t ∈ TK ⊓ Z := ⟨ht, hZt⟩
    rw [hTKbot, Subgroup.mem_bot] at hbot
    exact hbot
  have hsurj : ∀ s ∈ T0, ∃ t ∈ TK, π t = s := by
    let φ : ↥TK → ↥T0 := fun t => ⟨π t, hTKQ t t.2⟩
    have hφinj : Function.Injective φ := by
      intro t t' h
      have h1 : π t = π t' := congrArg Subtype.val h
      apply Subtype.ext
      have h2 : (t : ↥K) * (t' : ↥K)⁻¹ ∈ TK := TK.mul_mem t.2 (TK.inv_mem t'.2)
      have h3 : π ((t : ↥K) * (t' : ↥K)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      exact mul_inv_eq_one.1 (hTKinj _ h2 h3)
    have hcardeq : Nat.card ↥TK = Nat.card ↥T0 := by rw [hTKcard, hT0card]
    have hbij := (Nat.bijective_iff_injective_and_card φ).2 ⟨hφinj, hcardeq⟩
    intro s hs
    obtain ⟨⟨t, ht⟩, hteq⟩ := hbij.2 ⟨s, hs⟩
    exact ⟨t, ht, congrArg Subtype.val hteq⟩
  have hTKexp : ∀ t ∈ TK, t ^ 2 = 1 := by
    intro t ht
    have h1 : π (t ^ 2) = 1 := by
      rw [map_pow]
      exact hT0el.2 (π t) (hTKQ t ht)
    exact hTKinj _ (TK.pow_mem ht 2) h1
  have hTKcomm : ∀ t ∈ TK, ∀ s ∈ TK, t * s = s * t := by
    intro t ht s hs
    have hc := hT0el.1.is_comm.comm (⟨π t, hTKQ t ht⟩ : ↥T0) ⟨π s, hTKQ s hs⟩
    have hc' : π t * π s = π s * π t := congrArg Subtype.val hc
    have h2 : (s * t)⁻¹ * (t * s) ∈ TK :=
      TK.mul_mem (TK.inv_mem (TK.mul_mem hs ht)) (TK.mul_mem ht hs)
    have h3 : π ((s * t)⁻¹ * (t * s)) = 1 := by
      calc π ((s * t)⁻¹ * (t * s)) = (π s * π t)⁻¹ * (π t * π s) := by simp [map_mul, map_inv]
        _ = 1 := by rw [hc', inv_mul_cancel]
    have := hTKinj _ h2 h3
    exact (inv_mul_eq_one.1 this).symm
  have hTKel : IsElemAbelian 2 TK :=
    ⟨⟨⟨fun a b => Subtype.ext (hTKcomm a a.2 b b.2)⟩⟩, fun a ha => hTKexp a ha⟩
  have hP2 : ∀ q : ↥K, q ∈ T0.comap π → q ^ 2 = 1 → q ∈ TK := by
    intro q hq0 hq2
    have hqs : q ∈ TK ⊔ Z := by
      rw [hsup]
      exact hq0
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hqs
    have hc : Commute y z := Subgroup.mem_center_iff.1 hz y
    have hz2 : z ^ 2 = 1 := by
      rw [← hyz, hc.mul_pow, hTKexp y hy, one_mul] at hq2
      exact hq2
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz3 z hz, hz2]; simp
    rw [← hyz, hz1, mul_one]
    exact hy
  have hπconj : ∀ (b : B) (q : ↥K), π (KD264Inner.conjKequiv K hK (b : Y) q) =
      ψ b * π q * (ψ b)⁻¹ := by
    intro b q
    rw [hψ, KD1426Psi.psiB_apply]
    exact KD1426Psi.psiFun_equiv K hK eK hn (b : Y) (hB3 b b.2) q
  have hconjQ : ∀ b : B, ∀ q : ↥K, q ∈ T0.comap π →
      KD264Inner.conjKequiv K hK (b : Y) q ∈ T0.comap π := by
    intro b q hq0
    rw [Subgroup.mem_comap, hπconj b q]
    exact hT0norm (ψ b) (MonoidHom.mem_range.2 ⟨b, rfl⟩) (π q) (Subgroup.mem_comap.1 hq0)
  have hconjT : ∀ b : B, ∀ t ∈ TK, KD264Inner.conjKequiv K hK (b : Y) t ∈ TK := by
    intro b t ht
    apply hP2
    · exact hconjQ b t (Subgroup.mem_comap.2 (hTKQ t ht))
    · rw [← map_pow, hTKexp t ht, map_one]
  set TY : Subgroup Y := TK.map K.subtype with hTYdef
  have hTYmem : ∀ y : Y, y ∈ TY ↔ ∃ t ∈ TK, (t : Y) = y := fun y => by
    rw [hTYdef]
    constructor
    · intro h
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 h
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact Subgroup.mem_map.2 ⟨t, ht, rfl⟩
  have hTYle : TY ≤ K := by
    intro y hy
    obtain ⟨t, _, rfl⟩ := (hTYmem y).1 hy
    exact t.2
  have hTYel : IsElemAbelian 2 TY := KD264Rank.isElemAbelian_map K.subtype_injective hTKel
  have hTYcard : Nat.card TY = 4 := by
    rw [hTYdef, Subgroup.card_map_of_injective K.subtype_injective, hTKcard]
  have hnormY : ∀ b ∈ B, ∀ y ∈ TY, b * y * b⁻¹ ∈ TY := by
    intro b hb y hy
    obtain ⟨t, ht, rfl⟩ := (hTYmem y).1 hy
    rw [hTYmem]
    refine ⟨KD264Inner.conjKequiv K hK b t, hconjT ⟨b, hb⟩ t ht, ?_⟩
    exact KD264Inner.conjKequiv_apply K hK b t
  have hBnorm : B ≤ Subgroup.normalizer (TY : Set Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hnormY b hb y hy
    · intro hy
      have := hnormY b⁻¹ (B.inv_mem hb) _ hy
      have key : b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y := by group
      rw [key] at this
      exact this
  have hcomm_eq : ⁅B, TY⁆ = TY := by
    apply le_antisymm
    · apply Subgroup.commutator_le.2
      intro b hb y hy
      rw [commutatorElement_def]
      exact TY.mul_mem (hnormY b hb y hy) (TY.inv_mem hy)
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := (hTYmem t).1 ht
      obtain ⟨d, hd, s0, hs0, hds⟩ := hT0cov (π t') (hTKQ t' ht')
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hd
      obtain ⟨s, hs, hsπ⟩ := hsurj s0 hs0
      have hc_mem : KD264Inner.conjKequiv K hK (b : Y) s * s⁻¹ ∈ TK :=
        TK.mul_mem (hconjT b s hs) (TK.inv_mem hs)
      have hc_π : π (KD264Inner.conjKequiv K hK (b : Y) s * s⁻¹) = π t' := by
        rw [map_mul, map_inv, hπconj b s, hsπ]
        exact hds
      have hct : KD264Inner.conjKequiv K hK (b : Y) s * s⁻¹ = t' := by
        have := hTKinj _ (TK.mul_mem hc_mem (TK.inv_mem ht'))
          (by rw [map_mul, map_inv, hc_π, mul_inv_cancel])
        exact mul_inv_eq_one.1 this
      have hcm : ⁅(b : Y), (s : Y)⁆ ∈ ⁅B, TY⁆ :=
        Subgroup.commutator_mem_commutator b.2 ((hTYmem _).2 ⟨s, hs, rfl⟩)
      have heq : ⁅(b : Y), (s : Y)⁆ = (t' : Y) := by
        rw [← hct, commutatorElement_def]
        simp [KD264Inner.conjKequiv_apply, mul_assoc]
      rw [heq] at hcm
      exact hcm
  refine ⟨hBcard, B0, TY, hA_le, hA_el, hA_card, ?_, ?_, ?_, ?_, hTYel, hTYcard, hBnorm,
    hcomm_eq, ?_⟩
  · rw [hKA, hlayer]
    exact hcompK
  · rw [hKA, hlayer]
    have h57 : 5 ≤ 7 := by norm_num
    exact ⟨TauCeti.CFSGIndex.alternating 7 h57, rfl, pSimple_mulEquiv hcore eK⟩
  · rw [hKA, hlayer]
    intro b hb
    constructor
    · intro h
      exact Subgroup.mem_inf.2 ⟨hb, h⟩
    · intro h
      exact (Subgroup.mem_inf.1 h).2
  · rw [hKA, hlayer]
    exact hTYle
  · rw [hKA, hlayer]
    exact hcore

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltSeven

end
