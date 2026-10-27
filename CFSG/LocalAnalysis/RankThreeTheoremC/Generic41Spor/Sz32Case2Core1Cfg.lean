module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1K6
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1One
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Cfg

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1d_mem_map_conj {L : Subgroup Y} {g x : Y} :
    x ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hl
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem szh1d_isComponent_conj (g : Y) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL

theorem szh1d_comm_of_ne {L L' : Subgroup Y} (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤)
    (hne : L ≠ L') {u v : Y} (hu : u ∈ L) (hv : v ∈ L') : u * v = v * u := by
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne
  have h2 : L ≤ Subgroup.centralizer (L' : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  exact (Subgroup.mem_centralizer_iff.mp (h2 hu) v hv).symm

theorem szh1d_inf_eq_bot {L L' : Subgroup Y} (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤)
    (hne : L ≠ L') (hc : Subgroup.center ↥L = ⊥) : L ⊓ L' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxc : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (szh1d_comm_of_ne hL hL' hne w.2 hx.2)
  rw [hc, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)

theorem szh1d_sup_eq {Z A B : Subgroup Y} (hZ : Nat.card Z = 25) (hA : A ≤ Z) (hB : B ≤ Z)
    (hA0 : A ≠ ⊥) (hB0 : B ≠ ⊥) (hAB : A ⊓ B = ⊥) : A ⊔ B = Z := by
  have hS : A ⊔ B ≤ Z := sup_le hA hB
  have hdvdZ : Nat.card (A ⊔ B : Subgroup Y) ∣ 5 ^ 2 := by
    have := Subgroup.card_dvd_of_le hS
    rw [hZ] at this
    simpa using this
  have hdA : Nat.card A ∣ Nat.card (A ⊔ B : Subgroup Y) := Subgroup.card_dvd_of_le le_sup_left
  have hdB : Nat.card B ∣ Nat.card (A ⊔ B : Subgroup Y) := Subgroup.card_dvd_of_le le_sup_right
  have hA1 : Nat.card A ≠ 1 := fun h => hA0 (Subgroup.eq_bot_of_card_eq A h)
  have hB1 : Nat.card B ≠ 1 := fun h => hB0 (Subgroup.eq_bot_of_card_eq B h)
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvdZ
  interval_cases m
  · exfalso
    rw [pow_zero] at hm'
    rw [hm'] at hdA
    exact hA1 (Nat.dvd_one.mp hdA)
  · exfalso
    have hA5 : Nat.card A = 5 := by
      rw [hm'] at hdA
      rcases (Nat.dvd_prime Nat.prime_five).mp (by simpa using hdA) with h | h
      · exact absurd h hA1
      · exact h
    have hB5 : Nat.card B = 5 := by
      rw [hm'] at hdB
      rcases (Nat.dvd_prime Nat.prime_five).mp (by simpa using hdB) with h | h
      · exact absurd h hB1
      · exact h
    have hAe : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm', hA5]; simp)
    have hBe : B = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hm', hB5]; simp)
    have hABe : A = B := hAe.trans hBe.symm
    rw [← hABe, inf_idem] at hAB
    exact hA0 hAB
  · exact Subgroup.eq_of_le_of_card_ge hS (by rw [hZ, hm']; simp)

theorem szh1d_isSylowOf (hY : Sz32Case2Data Pb a c y) : CFSG.ABGLocalTools.IsSylowOf 5 Pb ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  obtain ⟨S, hS⟩ := hY.sylow
  subst hS
  refine ⟨le_top, S.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact S.not_dvd_index

theorem szh1d_inf_Z_ne_bot (hY : Sz32Case2Data Pb a c y) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hn : ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L : Set Y)) : sz32Z a c ⊓ L ≠ ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card L := by
    by_contra hnd
    have hcop : Nat.Coprime 5 (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hnd
    have hcoreL : primeComplementCore (G := ↥L) 5 = ⊥ :=
      cfsg_subnormal_primeComplementCore_eq_bot 5 L hL.2.1 hY.core
    have htop : (⊤ : Subgroup ↥L) ≤ primeComplementCore (G := ↥L) 5 :=
      normal_coprime_le_primeComplementCore 5 ⊤ inferInstance (by simpa using hcop)
    rw [hcoreL] at htop
    haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
    exact hx (Subgroup.mem_bot.mp (htop (Subgroup.mem_top x)))
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 5 Pb (Subgroup.normalizer (L : Set Y)) :=
    (szh1d_isSylowOf hY).of_le (fun g hg => hn g hg) le_top
  have hsyl' := hsyl.inf_of_le_normalizer (N := L) Subgroup.le_normalizer le_rfl
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl'
  obtain ⟨_, _, hdvd⟩ := hsyl'
  have hbot : Pb ⊓ L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.relIndex_bot_left] at hdvd
    exact hdvd h5
  have hnormPb : ∀ q ∈ Pb, ∀ n ∈ Pb ⊓ L, q * n * q⁻¹ ∈ Pb ⊓ L := by
    intro q hq n hn'
    refine ⟨Pb.mul_mem (Pb.mul_mem hq hn'.1) (Pb.inv_mem hq), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hn q hq) n).mp hn'.2
  have hne := szh1_inf_Z_ne_bot hY inf_le_left hnormPb hbot
  intro hZL
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ sz32Z a c ⊓ L := ⟨hx.2, hx.1.2⟩
  rw [hZL] at hx'
  exact hx'

theorem szh1d_Z_le_sup (hY : Sz32Case2Data Pb a c y) {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂) (hc₁ : Subgroup.center ↥L₁ = ⊥)
    (hn₁ : ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L₁ : Set Y))
    (hn₂ : ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L₂ : Set Y)) :
    sz32Z a c ≤ L₁ ⊔ L₂ := by
  have hA0 := szh1d_inf_Z_ne_bot hY h₁ hn₁
  have hB0 := szh1d_inf_Z_ne_bot hY h₂ hn₂
  have hAB : (sz32Z a c ⊓ L₁) ⊓ (sz32Z a c ⊓ L₂) = ⊥ := by
    have h12 := szh1d_inf_eq_bot h₁ h₂ hne hc₁
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ L₁ ⊓ L₂ := ⟨hx.1.2, hx.2.2⟩
    rw [h12] at hx'
    exact hx'
  have hsup := szh1d_sup_eq (szh1_Z_card hY) inf_le_left inf_le_left hA0 hB0 hAB
  rw [← hsup]
  exact sup_le_sup inf_le_right inf_le_right

theorem szh1d_all (hY : Sz32Case2Data Pb a c y)
    (hcen : ∀ {L : Subgroup Y}, IsComponentOf L ⊤ → Subgroup.center ↥L = ⊥)
    (hnorm : ∀ {L : Subgroup Y}, IsComponentOf L ⊤ → ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L : Set Y))
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : L = L₁ ∨ L = L₂ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hL1, hL2⟩ := hcon
  have hZle := szh1d_Z_le_sup hY h₁ h₂ hne (hcen h₁) (hnorm h₁) (hnorm h₂)
  have h0 := szh1d_inf_Z_ne_bot hY hL (hnorm hL)
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp h0)
  have hzL : z ∈ L := hzmem.2
  have hzZ : z ∈ sz32Z a c := hzmem.1
  have hcentr : L₁ ⊔ L₂ ≤ Subgroup.centralizer (L : Set Y) := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => szh1d_comm_of_ne hL h₁ hL1 hw hu
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => szh1d_comm_of_ne hL h₂ hL2 hw hu
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentr (hZle hzZ)) w w.2)
  rw [hcen hL, Subgroup.mem_bot] at hzc
  apply hz1
  have hz : z = 1 := congrArg Subtype.val hzc
  exact Subtype.ext hz

theorem szh1d_centralizer_eq_bot (hY : Sz32Case2Data Pb a c y) (hpC : CFSG.pCore 5 Y = ⊥)
    {L₁ L₂ : Subgroup Y} (hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₁ ∨ L = L₂)
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) :
    Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hlayer : CFSG.layer Y = L₁ ⊔ L₂ := by
    rw [CFSG.layer_eq_componentClassification, CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    apply le_antisymm
    · apply sSup_le
      intro L hL
      rcases hall L hL with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_sSup h₁) (le_sSup h₂)
  have hb := Generic49U3.centralizer_layer_inf_centralizer_pCore_le (Y := Y) (p := 5) hY.core
  rw [hlayer, hpC] at hb
  rw [eq_bot_iff]
  intro g hg
  refine hb ⟨hg, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
  have : h = 1 := hh
  subst this
  simp

def szh1d_compKernel (Y : Type) [Group Y] : Subgroup Y where
  carrier := {g | ∀ L : Subgroup Y, IsComponentOf L ⊤ → g ∈ Subgroup.normalizer (L : Set Y)}
  mul_mem' := fun ha hb L hL => (Subgroup.normalizer (L : Set Y)).mul_mem (ha L hL) (hb L hL)
  one_mem' := fun L _ => (Subgroup.normalizer (L : Set Y)).one_mem
  inv_mem' := fun ha L hL => (Subgroup.normalizer (L : Set Y)).inv_mem (ha L hL)

instance szh1d_compKernel_normal : (szh1d_compKernel Y).Normal := by
  refine ⟨fun n hn g L hL => ?_⟩
  have hL' := szh1d_isComponent_conj g⁻¹ hL
  have h1 := hn _ hL'
  rw [Subgroup.mem_normalizer_iff] at h1 ⊢
  intro x
  have h2 := h1 (g⁻¹ * x * g)
  rw [szh1d_mem_map_conj, szh1d_mem_map_conj] at h2
  simpa [mul_assoc] using h2

theorem szh1d_exists_conj (hY : Sz32Case2Data Pb a c y)
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤)
    (hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₁ ∨ L = L₂) (hinf : L₁ ⊓ L₂ = ⊥)
    (hA0 : sz32Z a c ⊓ L₁ ≠ ⊥) (hB0 : sz32Z a c ⊓ L₂ ≠ ⊥) :
    ∃ n : Y, L₁.map (MulAut.conj n).toMonoidHom = L₂ := by
  by_contra hcon
  push_neg at hcon
  have hfix : ∀ n : Y, L₁.map (MulAut.conj n).toMonoidHom = L₁ := by
    intro n
    rcases hall _ (szh1d_isComponent_conj n h₁) with h | h
    · exact h
    · exact absurd h (hcon n)
  have hnormA : Subgroup.normalizer (sz32Z a c : Set Y) ≤
      Subgroup.normalizer ((sz32Z a c ⊓ L₁ : Subgroup Y) : Set Y) := by
    intro g hg
    have hgL : g ∈ Subgroup.normalizer (L₁ : Set Y) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix g)
    rw [Subgroup.mem_normalizer_iff] at hg hgL ⊢
    intro x
    exact and_congr (hg x) (hgL x)
  rcases hY.irr (sz32Z a c ⊓ L₁) inf_le_left hnormA with h | h
  · exact hA0 h
  · have hZL : sz32Z a c ≤ L₁ := by
      rw [← h]; exact inf_le_right
    apply hB0
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ L₁ ⊓ L₂ := ⟨hZL hx.1, hx.2⟩
    rw [hinf] at hx'
    exact hx'

theorem szh1d_swap (hY : Sz32Case2Data Pb a c y)
    (hnorm : ∀ {L : Subgroup Y}, IsComponentOf L ⊤ → ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L : Set Y))
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₁ ∨ L = L₂)
    {n : Y} (hn : L₁.map (MulAut.conj n).toMonoidHom = L₂) :
    ∃ t ∈ Subgroup.normalizer (Pb : Set Y), L₁.map (MulAut.conj t).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj t).toMonoidHom = L₁ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hS⟩ := hY.sylow
  have hSK : (S : Subgroup Y) ≤ szh1d_compKernel Y := by
    rw [hS]
    intro g hg L hL
    exact hnorm hL g hg
  have hfrat := Sylow.normalizer_sup_eq_top' S hSK
  have hmem : n ∈ (⊤ : Subgroup Y) := Subgroup.mem_top n
  rw [← hfrat] at hmem
  obtain ⟨t, ht, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  have ht1 : L₁.map (MulAut.conj t).toMonoidHom = L₂ := by
    rw [← hn]
    ext x
    rw [szh1d_mem_map_conj, szh1d_mem_map_conj]
    have hk1 := (Subgroup.mem_normalizer_iff''.mp (hk L₁ h₁)) (t⁻¹ * x * t)
    rw [hk1]
    simp [mul_assoc]
  refine ⟨t, ?_, ht1, ?_⟩
  · rw [← hS]; exact ht
  · rcases hall _ (szh1d_isComponent_conj t h₂) with h | h
    · exact h
    · exfalso
      apply hne
      exact Subgroup.map_injective (MulAut.conj t).injective (ht1.trans h.symm)

theorem szh1_exists_two_config (hY : Sz32Case2Data Pb a c y) (hI6103 : KFactI6103Five)
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂) :
    ∃ t : Y, Szh1Two Pb L₁ L₂ t := by
  obtain ⟨S, hS⟩ := hY.sylow
  have hnorm : ∀ {L : Subgroup Y}, IsComponentOf L ⊤ → ∀ g ∈ Pb,
      g ∈ Subgroup.normalizer (L : Set Y) := fun hL g hg =>
    szh1_mem_normalizer_of_pElement hY.core hY.rank (szh1_pow_pElement hY hg) hL
  have hcen : ∀ {L : Subgroup Y}, IsComponentOf L ⊤ → Subgroup.center ↥L = ⊥ := fun hL =>
    szh1_center_bot hI6103 hY.catalog hY.core hY.rank S
      (by rw [hS]; exact fun g hg h hh g5 h5 => szh1_Om_comm hY hg hh g5 h5) hL
  have hall := fun {L : Subgroup Y} (hL : IsComponentOf L ⊤) => szh1d_all hY hcen hnorm h₁ h₂ hne hL
  have hinf := szh1d_inf_eq_bot h₁ h₂ hne (hcen h₁)
  obtain ⟨n, hn⟩ := szh1d_exists_conj hY h₁ h₂ (fun L hL => hall hL) hinf
    (szh1d_inf_Z_ne_bot hY h₁ (hnorm h₁)) (szh1d_inf_Z_ne_bot hY h₂ (hnorm h₂))
  obtain ⟨t, ht, ht1, ht2⟩ := szh1d_swap hY hnorm h₁ h₂ hne (fun L hL => hall hL) hn
  refine ⟨t, ?_⟩
  exact
    { comp₁ := h₁
      comp₂ := h₂
      ne := hne
      cen₁ := hcen h₁
      cen₂ := hcen h₂
      all := fun L hL => hall hL
      norm₁ := hnorm h₁
      norm₂ := hnorm h₂
      cent := szh1d_centralizer_eq_bot hY (szh1_pCore_bot hY hI6103 h₁) (fun L hL => hall hL) h₁ h₂
      t_norm := ht
      t₁ := ht1
      t₂ := ht2 }

end Cfg

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
