module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Dedekind

variable {Y : Type} [Group Y]

theorem szh1a_mem_sup_mul {Pb N : Subgroup Y} (hPN : ∀ p ∈ Pb, ∀ n ∈ N, p * n * p⁻¹ ∈ N) :
    ∀ q ∈ Pb ⊔ N, ∃ p ∈ Pb, ∃ n ∈ N, q = p * n := by
  let S : Subgroup Y :=
    { carrier := {q | ∃ p ∈ Pb, ∃ n ∈ N, q = p * n}
      mul_mem' := by
        rintro _ _ ⟨p, hp, n, hn, rfl⟩ ⟨p', hp', n', hn', rfl⟩
        refine ⟨p * p', mul_mem hp hp', (p'⁻¹ * n * p'⁻¹⁻¹) * n', mul_mem ?_ hn', ?_⟩
        · exact hPN p'⁻¹ (inv_mem hp') n hn
        · group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨p, hp, n, hn, rfl⟩
        refine ⟨p⁻¹, inv_mem hp, p * n⁻¹ * p⁻¹, ?_, ?_⟩
        · exact hPN p hp n⁻¹ (inv_mem hn)
        · group }
  have hle : Pb ⊔ N ≤ S := by
    apply sup_le
    · intro p hp
      exact ⟨p, hp, 1, one_mem _, by simp⟩
    · intro n hn
      exact ⟨1, one_mem _, n, hn, by simp⟩
  intro q hq
  exact hle hq

theorem szh1a_dedekind {Pb N C : Subgroup Y}
    (hPC : Pb ≤ C) (hPN : ∀ p ∈ Pb, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (hNC : N ⊓ C = ⊥)
    (hCnorm : ∀ g ∈ C, ∀ q ∈ Pb ⊔ N, g * q * g⁻¹ ∈ Pb ⊔ N) :
    ∀ g ∈ C, ∀ x ∈ Pb, g * x * g⁻¹ ∈ Pb := by
  intro g hg x hx
  have hq : g * x * g⁻¹ ∈ Pb ⊔ N := hCnorm g hg x (Subgroup.mem_sup_left hx)
  have hqC : g * x * g⁻¹ ∈ C := mul_mem (mul_mem hg (hPC hx)) (inv_mem hg)
  obtain ⟨p, hp, n, hn, hpn⟩ := szh1a_mem_sup_mul hPN _ hq
  have hnC : n ∈ C := by
    have : n = p⁻¹ * (g * x * g⁻¹) := by rw [hpn]; group
    rw [this]
    exact mul_mem (inv_mem (hPC hp)) hqC
  have hn1 : n = 1 := by
    have : n ∈ N ⊓ C := ⟨hn, hnC⟩
    rw [hNC] at this
    exact Subgroup.mem_bot.mp this
  rw [hpn, hn1, mul_one]
  exact hp

end Dedekind

section Fin

variable {Y : Type} [Group Y] [Finite Y]

theorem szh1a_centralizer_pCore_le
    (hcore : primeComplementCore (G := Y) 5 = ⊥) (hno : ∀ L : Subgroup Y, ¬ IsComponentOf L ⊤) :
    Subgroup.centralizer (CFSG.pCore 5 Y : Set Y) ≤ CFSG.pCore 5 Y := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hlayer : CFSG.layer Y = ⊥ :=
    CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => hno K ((CFSG.isComponent_iff_open K).mp hK)
  intro g hg
  have h1 : g ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) := by
    rw [hlayer, Subgroup.mem_centralizer_iff]
    intro h hh
    have h2 : h = 1 := Subgroup.mem_bot.mp hh
    subst h2
    simp
  exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.centralizer_layer_inf_centralizer_pCore_le
    hcore (Subgroup.mem_inf.mpr ⟨h1, hg⟩)

theorem szh1a_exists_central {Pb R : Subgroup Y} [R.Normal]
    (hPb : IsPGroup 5 Pb) (hRP : R ≤ Pb) (hR : R ≠ ⊥) :
    ∃ z ∈ R, z ≠ 1 ∧ ∀ q ∈ Pb, q * z = z * q := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (IsPGroup 5 Pb) := ⟨hPb⟩
  have hN : (R.subgroupOf Pb).Normal := Subgroup.Normal.subgroupOf inferInstance Pb
  haveI : (R.subgroupOf Pb).Normal := hN
  have hnt : Nontrivial (R.subgroupOf Pb) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hR
    rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
    intro r hr
    have := hbot ⟨r, hRP hr⟩ (by simpa [Subgroup.mem_subgroupOf] using hr)
    simpa using congrArg Subtype.val this
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal (R.subgroupOf Pb) (p := 5)
  refine ⟨((x : Pb) : Y), ?_, ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.mp x.2)
  · intro h
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · intro q hq
    have := Subgroup.mem_center_iff.mp hxc ⟨q, hq⟩
    simpa using congrArg Subtype.val this

theorem szh1a_coprime_eq_bot
    (hcore : primeComplementCore (G := Y) 5 = ⊥) {C K : Subgroup Y} [C.Normal]
    (hKC : K ≤ C) (hKn : ∀ g ∈ C, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hcop : ∀ k ∈ K, Nat.Coprime 5 (orderOf k)) : K = ⊥ := by
  have hKnorm : (K.subgroupOf C).Normal := by
    refine ⟨?_⟩
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hKn g.1 g.2 n.1 hn
  have hCnorm : (C.subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf inferInstance ⊤
  have hsub : IsSubnormal K ⊤ :=
    IsSubnormal.step hKC hKnorm (IsSubnormal.step le_top hCnorm (IsSubnormal.refl ⊤))
  have hbot := cfsg_subnormal_primeComplementCore_eq_bot 5 K hsub hcore
  have hcard : Nat.Coprime 5 (Nat.card K) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
    have := hcop x.1 x.2
    rw [Subgroup.orderOf_coe, hx] at this
    simp at this
  have hle : (⊤ : Subgroup K) ≤ primeComplementCore 5 :=
    normal_coprime_le_primeComplementCore 5 ⊤ inferInstance (by simpa using hcard)
  rw [hbot] at hle
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have := hle (Subgroup.mem_top (⟨k, hk⟩ : K))
  have h2 : (⟨k, hk⟩ : K) = 1 := Subgroup.mem_bot.mp this
  simpa using congrArg Subtype.val h2

theorem szh1a_conj_mem_sylow (S : Sylow 5 Y) {C : Subgroup Y} [C.Normal]
    (hSC : (S : Subgroup Y) ≤ C) (hCS : C ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y)) :
    ∀ g : Y, ∀ t ∈ (S : Subgroup Y), g * t * g⁻¹ ∈ (S : Subgroup Y) := by
  intro g t ht
  let T : Subgroup Y := (S : Subgroup Y).map (MulAut.conj g).toMonoidHom
  have hT : IsPGroup 5 T := S.isPGroup'.map _
  have hTC : T ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    have := Subgroup.Normal.conj_mem inferInstance s (hSC hs) g
    simpa using this
  have hsup : IsPGroup 5 ↥(T ⊔ (S : Subgroup Y)) :=
    IsPGroup.to_sup_of_normal_right' hT S.isPGroup' (hTC.trans hCS)
  have heq : T ⊔ (S : Subgroup Y) = S := S.is_maximal' hsup le_sup_right
  have hmem : g * t * g⁻¹ ∈ T := ⟨t, ht, by simp⟩
  have : g * t * g⁻¹ ∈ T ⊔ (S : Subgroup Y) := Subgroup.mem_sup_left hmem
  rwa [heq] at this

end Fin

section Main

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1_caseA (hY : Sz32Case2Data Pb a c y) (hno : ∀ L : Subgroup Y, ¬ IsComponentOf L ⊤) :
    ∀ g : Y, ∀ t ∈ Pb, g * t * g⁻¹ ∈ Pb := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S, hS⟩ := hY.sylow
  have hPb5 : IsPGroup 5 Pb := by rw [← hS]; exact S.isPGroup'
  haveI hRn : (CFSG.pCore 5 Y).Normal := CFSG.pCore_normal
  have hRP : CFSG.pCore 5 Y ≤ Pb := by
    rw [← hS]; exact CFSG.pCore_isPGroup.le_sylow_of_normal S
  have hcent := szh1a_centralizer_pCore_le hY.core hno
  have hR : CFSG.pCore 5 Y ≠ ⊥ := by
    intro hbot
    have h1 : Pb = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      have hx : x ∈ Subgroup.centralizer (CFSG.pCore 5 Y : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [hbot] at hh
        have h2 : h = 1 := Subgroup.mem_bot.mp hh
        subst h2
        simp
      have h3 := hcent hx
      rw [hbot] at h3
      exact Subgroup.mem_bot.mp h3
    have h4 := hY.facts.card
    rw [h1, Subgroup.card_bot] at h4
    norm_num at h4
  have hZP : sz32Z a c ≤ Pb := by
    refine le_trans ?_ hY.facts.Om_le
    exact le_sup_left
  obtain ⟨z, hzR, hz1, hzc⟩ := szh1a_exists_central hPb5 hRP hR
  have hzZ : z ∈ sz32Z a c := (hY.facts.center z (hRP hzR)).mp hzc
  have hne : CFSG.pCore 5 Y ⊓ sz32Z a c ≠ ⊥ := by
    intro hbot
    have hz : z ∈ CFSG.pCore 5 Y ⊓ sz32Z a c := ⟨hzR, hzZ⟩
    rw [hbot] at hz
    exact hz1 (Subgroup.mem_bot.mp hz)
  have hZR : sz32Z a c ≤ CFSG.pCore 5 Y := by
    have hnorm : Subgroup.normalizer (sz32Z a c : Set Y) ≤
        Subgroup.normalizer ((CFSG.pCore 5 Y ⊓ sz32Z a c : Subgroup Y) : Set Y) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff] at hg ⊢
      intro h
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hRn.conj_mem h h1 g, (hg h).mp h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, (hg h).mpr h2⟩
        have := hRn.conj_mem _ h1 g⁻¹
        simpa [mul_assoc] using this
    rcases hY.irr (CFSG.pCore 5 Y ⊓ sz32Z a c) inf_le_right hnorm with h | h
    · exact absurd h hne
    · exact inf_eq_right.mp h
  have hZnorm : ∀ g : Y, ∀ w ∈ sz32Z a c, g * w * g⁻¹ ∈ sz32Z a c := by
    intro g w hw
    have hle : (sz32Z a c).map (MulAut.conj g).toMonoidHom ≤ Pb := by
      rintro _ ⟨v, hv, rfl⟩
      exact hRP (by simpa using hRn.conj_mem v (hZR hv) g)
    have heq := hY.wc g hle
    have hmem : g * w * g⁻¹ ∈ (sz32Z a c).map (MulAut.conj g).toMonoidHom := ⟨w, hw, by simp⟩
    rwa [heq] at hmem
  haveI hZn : (sz32Z a c).Normal := ⟨fun w hw g => hZnorm g w hw⟩
  obtain ⟨C, hC⟩ : ∃ C : Subgroup Y, C = Subgroup.centralizer (sz32Z a c : Set Y) := ⟨_, rfl⟩
  haveI hCn : C.Normal := by rw [hC]; infer_instance
  have hCmem : ∀ g : Y, g ∈ C ↔ ∀ w ∈ sz32Z a c, w * g = g * w := by
    intro g; rw [hC, Subgroup.mem_centralizer_iff]; rfl
  have hPC : Pb ≤ C := by
    intro q hq
    rw [hCmem]
    intro w hw
    exact ((hY.facts.center w (hZP hw)).mpr hw q hq).symm
  have hcmem : c ^ 5 ∈ sz32Z a c := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hCW : C ≤ Subgroup.centralizer ({c ^ 5} : Set Y) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hCmem g).mp hg _ hcmem
  obtain ⟨N, hser⟩ := hY.series
  have hNC : N ⊓ C = ⊥ := by
    apply szh1a_coprime_eq_bot hY.core (K := N ⊓ C) (C := C) inf_le_right
    · intro g hg k hk
      rw [Subgroup.mem_inf] at hk ⊢
      exact ⟨hser.N_norm g (hCW hg) k hk.1, C.mul_mem (C.mul_mem hg hk.2) (C.inv_mem hg)⟩
    · intro k hk
      exact hser.N_cop k (Subgroup.mem_inf.mp hk).1
  have hPN : ∀ p ∈ Pb, ∀ n ∈ N, p * n * p⁻¹ ∈ N :=
    fun p hp n hn => hser.N_norm p (hser.P_le hp) n hn
  have hCPN : ∀ g ∈ C, ∀ q ∈ Pb ⊔ N, g * q * g⁻¹ ∈ Pb ⊔ N :=
    fun g hg q hq => hser.PN_norm g (hCW hg) q hq
  have hCnormP := szh1a_dedekind hPC hPN hNC hCPN
  have hCS : C ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
    rw [hS, Subgroup.le_normalizer_iff]
    exact hCnormP
  have hSC : (S : Subgroup Y) ≤ C := by rw [hS]; exact hPC
  intro g t ht
  have := szh1a_conj_mem_sylow S hSC hCS g t (by rw [hS]; exact ht)
  rwa [hS] at this

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
